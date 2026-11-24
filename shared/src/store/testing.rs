//! Tests' tools: a directory to work in, and a file held in memory that
//! can lose power.

use std::io;
use std::path::PathBuf;
use std::sync::Mutex;

use super::backend::Backend;

/// A fresh directory for one test, under the system's temporary one.
pub(crate) fn temp_dir(name: &str) -> PathBuf {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tabminer-store-{name}-{}-{n}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// What a crash does to the writes not yet made durable.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Lost {
    /// None of them reached the disk.
    All,
    /// All of them did.
    None,
    /// Each 512-byte sector of each did or did not, by this seed: writes
    /// reordered, and writes of several sectors torn.
    Some(u64),
}

struct Mem {
    /// What the disk holds for certain: everything up to the last sync.
    durable: Vec<u8>,
    /// What a read sees: every write so far.
    current: Vec<u8>,
    /// Writes since the last sync, in order.
    pending: Vec<(u64, Vec<u8>)>,
    /// Writes and syncs so far.
    ops: u64,
    /// Reads so far.
    reads: u64,
    /// The operation at which power is lost.
    crash_at: u64,
    crashed: bool,
}

/// A file in memory, as an operating system holds one: writes are seen
/// at once and durable only after a sync. Power can be set to fail at
/// any write or sync, which then returns an error, as does everything
/// after; [`MemBackend::image`] is what a disk might then hold.
pub(crate) struct MemBackend {
    inner: Mutex<Mem>,
}

fn apply(file: &mut Vec<u8>, offset: u64, data: &[u8]) {
    let end = offset as usize + data.len();
    if file.len() < end {
        file.resize(end, 0);
    }
    file[offset as usize..end].copy_from_slice(data);
}

impl MemBackend {
    pub(crate) fn new() -> MemBackend {
        MemBackend::from_image(Vec::new())
    }

    /// A file holding `image`, all of it durable.
    pub(crate) fn from_image(image: Vec<u8>) -> MemBackend {
        let mem = Mem {
            durable: image.clone(),
            current: image,
            pending: Vec::new(),
            ops: 0,
            reads: 0,
            crash_at: u64::MAX,
            crashed: false,
        };
        MemBackend { inner: Mutex::new(mem) }
    }

    /// Power fails at the `n`-th write or sync from now (1 is the next).
    pub(crate) fn crash_at(&self, n: u64) {
        let mut m = self.inner.lock().unwrap();
        m.crash_at = m.ops + n;
    }

    /// Reads so far.
    pub(crate) fn reads(&self) -> u64 {
        self.inner.lock().unwrap().reads
    }

    /// Writes and syncs so far.
    pub(crate) fn ops(&self) -> u64 {
        self.inner.lock().unwrap().ops
    }

    pub(crate) fn crashed(&self) -> bool {
        self.inner.lock().unwrap().crashed
    }

    /// What the disk holds if power is lost now, the writes since the
    /// last sync surviving as `lost` says.
    pub(crate) fn image(&self, lost: Lost) -> Vec<u8> {
        let m = self.inner.lock().unwrap();
        let mut out = m.durable.clone();
        let mut rng = crate::test_util::Rng::new(match lost {
            Lost::Some(seed) => seed,
            _ => 0,
        });
        for (offset, data) in &m.pending {
            for (k, sector) in data.chunks(512).enumerate() {
                let kept = match lost {
                    Lost::All => false,
                    Lost::None => true,
                    Lost::Some(_) => rng.next_u64().is_multiple_of(2),
                };
                if kept {
                    apply(&mut out, offset + 512 * k as u64, sector);
                }
            }
        }
        out
    }
}

fn power() -> io::Error {
    io::Error::other("power lost")
}

impl Backend for MemBackend {
    fn read_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        let mut m = self.inner.lock().unwrap();
        m.reads += 1;
        let end = offset as usize + buf.len();
        let from = m.current.get(offset as usize..end).ok_or(io::ErrorKind::UnexpectedEof)?;
        buf.copy_from_slice(from);
        Ok(())
    }

    fn write_at(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        let mut m = self.inner.lock().unwrap();
        if m.crashed {
            return Err(power());
        }
        m.ops += 1;
        apply(&mut m.current, offset, data);
        m.pending.push((offset, data.to_vec()));
        if m.ops == m.crash_at {
            // The write was on its way: any part of it may have landed.
            m.crashed = true;
            return Err(power());
        }
        Ok(())
    }

    fn sync(&self) -> io::Result<()> {
        let mut m = self.inner.lock().unwrap();
        if m.crashed {
            return Err(power());
        }
        m.ops += 1;
        if m.ops == m.crash_at {
            m.crashed = true;
            return Err(power());
        }
        let m = &mut *m;
        for (offset, data) in m.pending.drain(..) {
            apply(&mut m.durable, offset, &data);
        }
        Ok(())
    }

    fn len(&self) -> io::Result<u64> {
        Ok(self.inner.lock().unwrap().current.len() as u64)
    }
}

/// A file on disk that counts what is asked of it.
pub(crate) struct Counting {
    pub(crate) file: super::backend::FileBackend,
    pub(crate) reads: std::sync::atomic::AtomicU64,
    pub(crate) read_bytes: std::sync::atomic::AtomicU64,
    pub(crate) writes: std::sync::atomic::AtomicU64,
    pub(crate) written: std::sync::atomic::AtomicU64,
}

impl Counting {
    pub(crate) fn open(path: &std::path::Path) -> Counting {
        Counting {
            file: super::backend::FileBackend::open(path).unwrap(),
            reads: 0.into(),
            read_bytes: 0.into(),
            writes: 0.into(),
            written: 0.into(),
        }
    }

    /// Reads, bytes read, writes and bytes written since the last call.
    pub(crate) fn take(&self) -> [u64; 4] {
        use std::sync::atomic::Ordering::Relaxed;
        [
            self.reads.swap(0, Relaxed),
            self.read_bytes.swap(0, Relaxed),
            self.writes.swap(0, Relaxed),
            self.written.swap(0, Relaxed),
        ]
    }
}

impl Backend for Counting {
    fn read_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        self.reads.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.read_bytes.fetch_add(buf.len() as u64, std::sync::atomic::Ordering::Relaxed);
        self.file.read_at(offset, buf)
    }

    fn write_at(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.writes.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.written.fetch_add(data.len() as u64, std::sync::atomic::Ordering::Relaxed);
        self.file.write_at(offset, data)
    }

    fn sync(&self) -> io::Result<()> {
        self.file.sync()
    }

    fn len(&self) -> io::Result<u64> {
        self.file.len()
    }

    /// A batch goes to the file as a batch, to be read as it reads one.
    fn read_many(&self, reads: &mut [super::backend::ReadReq<'_>]) -> io::Result<()> {
        use std::sync::atomic::Ordering::Relaxed;
        self.reads.fetch_add(reads.len() as u64, Relaxed);
        self.read_bytes.fetch_add(reads.iter().map(|r| r.buf.len() as u64).sum(), Relaxed);
        self.file.read_many(reads)
    }
}

/// A backend whose bytes can be taken as they would be after a crash.
pub(crate) trait Imaged {
    fn bytes(&self) -> Vec<u8>;
}

impl Imaged for MemBackend {
    fn bytes(&self) -> Vec<u8> {
        self.image(Lost::All)
    }
}
