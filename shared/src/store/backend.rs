//! A file, as the store sees one: bytes read and written at offsets, and
//! made durable when asked.
//!
//! Reads and writes are asked for in batches, because that is how the
//! store works (a block names everything it will touch before it touches
//! anything) and because a batch is what a backend can do well: the file
//! backend here reads one on several threads; one over `io_uring` could
//! hand the kernel the whole of it.
//!
//! Nothing here is mapped into memory. What is read is read into the
//! caller's buffers, and what the process holds of a file is what its
//! callers hold.

use std::fs::{File, OpenOptions};
use std::io;
use std::path::Path;

/// One read of a batch: `buf.len()` bytes at `offset`.
pub struct ReadReq<'a> {
    pub offset: u64,
    pub buf: &'a mut [u8],
}

/// One write of a batch.
pub struct WriteReq<'a> {
    pub offset: u64,
    pub data: &'a [u8],
}

/// A file read and written at offsets. A read past the end is an error;
/// a write past the end extends the file. What is written is durable
/// only once [`Backend::sync`] has returned.
pub trait Backend: Send + Sync {
    fn read_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()>;
    fn write_at(&self, offset: u64, data: &[u8]) -> io::Result<()>;
    /// Makes everything written so far durable.
    fn sync(&self) -> io::Result<()>;
    fn len(&self) -> io::Result<u64>;

    fn is_empty(&self) -> io::Result<bool> {
        Ok(self.len()? == 0)
    }

    /// Every read of `reads`, in any order.
    fn read_many(&self, reads: &mut [ReadReq<'_>]) -> io::Result<()> {
        reads.iter_mut().try_for_each(|r| self.read_at(r.offset, r.buf))
    }

    /// Every write of `writes`, in any order: they do not overlap.
    fn write_many(&self, writes: &[WriteReq<'_>]) -> io::Result<()> {
        writes.iter().try_for_each(|w| self.write_at(w.offset, w.data))
    }
}

/// Threads a batch of reads is spread over at most: these wait on the
/// disk, not on a core, so there may be more of them than cores.
const IO_THREADS: usize = 16;
/// A batch smaller than this is read on the calling thread.
const MIN_BATCH: usize = 8;

/// A file on disk.
pub struct FileBackend {
    file: File,
}

impl FileBackend {
    /// Opens the file at `path` for reading and writing, creating it
    /// empty if there is none.
    pub fn open(path: &Path) -> io::Result<FileBackend> {
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)?;
        Ok(FileBackend { file })
    }
}

#[cfg(unix)]
fn read_exact_at(file: &File, offset: u64, buf: &mut [u8]) -> io::Result<()> {
    std::os::unix::fs::FileExt::read_exact_at(file, buf, offset)
}

#[cfg(unix)]
fn write_all_at(file: &File, offset: u64, data: &[u8]) -> io::Result<()> {
    std::os::unix::fs::FileExt::write_all_at(file, data, offset)
}

#[cfg(windows)]
fn read_exact_at(file: &File, mut offset: u64, mut buf: &mut [u8]) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !buf.is_empty() {
        match file.seek_read(buf, offset) {
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => {
                buf = &mut buf[n..];
                offset += n as u64;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

#[cfg(windows)]
fn write_all_at(file: &File, mut offset: u64, mut data: &[u8]) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !data.is_empty() {
        match file.seek_write(data, offset) {
            Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
            Ok(n) => {
                data = &data[n..];
                offset += n as u64;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

impl Backend for FileBackend {
    fn read_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        read_exact_at(&self.file, offset, buf)
    }

    fn write_at(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        write_all_at(&self.file, offset, data)
    }

    fn sync(&self) -> io::Result<()> {
        self.file.sync_data()
    }

    fn len(&self) -> io::Result<u64> {
        Ok(self.file.metadata()?.len())
    }

    /// A batch is split among threads, each reading its share: the reads
    /// wait on the disk side by side.
    fn read_many(&self, reads: &mut [ReadReq<'_>]) -> io::Result<()> {
        let threads = IO_THREADS.min(reads.len() / (MIN_BATCH / 2));
        if reads.len() < MIN_BATCH || threads < 2 {
            return reads.iter_mut().try_for_each(|r| self.read_at(r.offset, r.buf));
        }
        let per = reads.len().div_ceil(threads);
        std::thread::scope(|s| {
            let handles: Vec<_> = reads
                .chunks_mut(per)
                .map(|part| s.spawn(move || part.iter_mut().try_for_each(|r| self.read_at(r.offset, r.buf))))
                .collect();
            handles.into_iter().try_for_each(|h| h.join().expect("a reading thread does not panic"))
        })
    }
}

/// Makes the creation or removal of a file in `dir` durable. (On Windows
/// a directory cannot be opened to be synced, and need not be.)
pub fn sync_dir(dir: &Path) -> io::Result<()> {
    #[cfg(unix)]
    File::open(dir)?.sync_all()?;
    #[cfg(not(unix))]
    let _ = dir;
    Ok(())
}

/// The one process that has a store's directory: held for as long as the
/// store is open, and let go when dropped (or when the process ends,
/// however it ends).
pub struct DirLock {
    _file: File,
}

impl DirLock {
    /// Takes the directory at `dir`, creating it if there is none. If
    /// another process (or another handle in this one) has it, the error
    /// is [`io::ErrorKind::ResourceBusy`].
    pub fn acquire(dir: &Path) -> io::Result<DirLock> {
        std::fs::create_dir_all(dir)?;
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(dir.join("LOCK"))?;
        match file.try_lock() {
            Ok(()) => Ok(DirLock { _file: file }),
            Err(std::fs::TryLockError::WouldBlock) => Err(io::ErrorKind::ResourceBusy.into()),
            Err(std::fs::TryLockError::Error(e)) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::temp_dir;

    #[test]
    fn a_file_is_read_as_it_was_written() {
        let dir = temp_dir("backend-file");
        let path = dir.join("f");
        let f = FileBackend::open(&path).unwrap();
        assert!(f.is_empty().unwrap());
        // Written out of order, and past the end.
        f.write_at(5000, b"later").unwrap();
        f.write_at(0, b"first").unwrap();
        f.write_many(&[WriteReq { offset: 100, data: b"aa" }, WriteReq { offset: 200, data: b"bbb" }]).unwrap();
        f.sync().unwrap();
        assert_eq!(f.len().unwrap(), 5005);
        let mut buf = [0u8; 5];
        f.read_at(5000, &mut buf).unwrap();
        assert_eq!(&buf, b"later");
        f.read_at(0, &mut buf).unwrap();
        assert_eq!(&buf, b"first");
        // A hole reads as zeros; past the end is an error.
        f.read_at(1000, &mut buf).unwrap();
        assert_eq!(buf, [0; 5]);
        assert_eq!(f.read_at(5001, &mut buf).unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
        // Reopened, it is all there.
        drop(f);
        let f = FileBackend::open(&path).unwrap();
        assert_eq!(f.len().unwrap(), 5005);
        f.read_at(200, &mut buf[..3]).unwrap();
        assert_eq!(&buf[..3], b"bbb");
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// A batch of reads large enough to be spread over threads gives each
    /// its own bytes; one read past the end fails the batch.
    #[test]
    fn a_batch_is_read_on_several_threads() {
        let dir = temp_dir("backend-batch");
        let f = FileBackend::open(&dir.join("f")).unwrap();
        let data: Vec<u8> = (0..200_000u32).map(|i| (i * 7 + i / 251) as u8).collect();
        f.write_at(0, &data).unwrap();
        let mut bufs = vec![[0u8; 97]; 500];
        let offset = |i: usize| (i * 389 % 1900) as u64 * 100;
        let mut reads: Vec<ReadReq<'_>> =
            bufs.iter_mut().enumerate().map(|(i, b)| ReadReq { offset: offset(i), buf: b }).collect();
        f.read_many(&mut reads).unwrap();
        for (i, b) in bufs.iter().enumerate() {
            let at = offset(i) as usize;
            assert_eq!(b[..], data[at..at + 97], "{i}");
        }
        let mut reads: Vec<ReadReq<'_>> = bufs
            .iter_mut()
            .enumerate()
            .map(|(i, b)| ReadReq { offset: if i == 333 { 199_990 } else { offset(i) }, buf: b })
            .collect();
        assert_eq!(f.read_many(&mut reads).unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_directory_has_one_holder() {
        let dir = temp_dir("backend-lock");
        let held = DirLock::acquire(&dir).unwrap();
        assert_eq!(DirLock::acquire(&dir).err().map(|e| e.kind()), Some(io::ErrorKind::ResourceBusy));
        drop(held);
        let again = DirLock::acquire(&dir).unwrap();
        sync_dir(&dir).unwrap();
        drop(again);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
