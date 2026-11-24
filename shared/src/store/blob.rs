//! Bytes too many for one page: pages, and a list of them.
//!
//! A block's body is megabytes and a page holds 64 KB, so what is long
//! is cut into pages, and where they are is written in a list: a page
//! of its own, or a chain of them if one does not hold it. A [`Blob`]
//! is where the first page is and how many bytes there are in all; it
//! is what a record elsewhere holds of the bytes. Bytes that fit one
//! page are that page, and have no list.
//!
//! ```text
//! blob := first page (6) | length (4)
//! first page := the bytes, if they fit one page; else a list
//! list := next list (6) | page (6) ...
//! ```
//!
//! Where the bytes are is known from the lists alone: a file opened
//! finds the pages in use without reading megabytes of every block,
//! at one page read for every 700 MB or so.
//!
//! The pages are pages of the state's file like any others: written in a
//! transaction, in place when it commits, freed in another.

use std::io;

use super::backend::Backend;
use super::pagefile::{Extent, MAX_UNITS, PageFile, ReadPages, Txn, UNIT};

/// Bytes a page holds.
const CHUNK: usize = Extent::capacity(MAX_UNITS);
/// Pages a list names, after the next list's place: some 700 MB of
/// them. (A few, where this is tested: megabytes then have lists.)
const LISTED: usize = if cfg!(test) { 4 } else { (CHUNK - 6) / 6 };
const NONE: Extent = Extent { start: 0, units: 0 };

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// Bytes kept as pages.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Blob {
    first: Extent,
    /// Bytes in all.
    pub len: u32,
}

impl Blob {
    /// Serialized size.
    pub const BYTES: usize = 10;

    /// Writes `bytes` as pages of `txn`.
    pub fn write<B: Backend>(txn: &Txn<'_, B>, bytes: &[u8]) -> io::Result<Blob> {
        assert!(!bytes.is_empty() && bytes.len() <= u32::MAX as usize);
        let len = bytes.len() as u32;
        if bytes.len() <= CHUNK {
            return Ok(Blob { first: txn.write(bytes)?, len });
        }
        let pages = bytes.chunks(CHUNK).map(|chunk| txn.write(chunk)).collect::<io::Result<Vec<Extent>>>()?;
        // The last list first: each names the one after it.
        let mut next = NONE;
        let mut list = Vec::with_capacity(6 + 6 * LISTED.min(pages.len()));
        for listed in pages.chunks(LISTED).rev() {
            list.clear();
            put_extent(&mut list, next);
            listed.iter().for_each(|e| put_extent(&mut list, *e));
            next = txn.write(&list)?;
        }
        Ok(Blob { first: next, len })
    }

    /// The bytes.
    pub fn read(&self, pages: &impl ReadPages) -> io::Result<Vec<u8>> {
        let mut buf = vec![0u8; MAX_UNITS as usize * UNIT];
        let mut out = Vec::with_capacity(self.len as usize);
        for page in self.places(pages)?.1 {
            out.extend_from_slice(pages.read_page(page, &mut buf)?);
        }
        match out.len() == self.len as usize {
            true => Ok(out),
            false => Err(corrupt("a blob is not as long as it says")),
        }
    }

    /// Frees the pages.
    pub fn free<B: Backend>(&self, txn: &Txn<'_, B>) -> io::Result<()> {
        let (lists, pages) = self.places(txn)?;
        lists.into_iter().chain(pages).for_each(|e| txn.free(e));
        Ok(())
    }

    /// Marks the pages in `file`'s map of free space: its lists are
    /// read, and none of its bytes.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        let (lists, pages) = self.places(file)?;
        lists.into_iter().chain(pages).try_for_each(|e| file.mark(e))
    }

    pub fn put(&self, out: &mut Vec<u8>) {
        put_extent(out, self.first);
        out.extend_from_slice(&self.len.to_le_bytes());
    }

    /// Reads an optional blob as [`Blob::put_option`] wrote it.
    pub fn get_option(b: &[u8]) -> io::Result<Option<Blob>> {
        let blob = Blob { first: get_extent(&b[..6]), len: u32::from_le_bytes(b[6..10].try_into().unwrap()) };
        match (blob.first.units, blob.len) {
            (0, 0) => Ok(None),
            (1..=MAX_UNITS, 1..) => Ok(Some(blob)),
            _ => Err(corrupt("a blob's place is not one")),
        }
    }

    /// Writes an optional blob: all zero for none.
    pub fn put_option(blob: &Option<Blob>, out: &mut Vec<u8>) {
        match blob {
            Some(b) => b.put(out),
            None => out.extend_from_slice(&[0; Blob::BYTES]),
        }
    }

    /// Where its lists are, and where its bytes are, in their order.
    fn places(&self, pages: &impl ReadPages) -> io::Result<(Vec<Extent>, Vec<Extent>)> {
        // No more pages than the length needs: a list that goes on is
        // not this blob's.
        let need = (self.len as usize).div_ceil(CHUNK);
        if need <= 1 {
            return Ok((Vec::new(), vec![self.first]));
        }
        let mut buf = vec![0u8; MAX_UNITS as usize * UNIT];
        let (mut lists, mut found) = (Vec::new(), Vec::with_capacity(need));
        let mut at = self.first;
        while found.len() < need {
            if at.units == 0 || at.units > MAX_UNITS {
                return Err(corrupt("a blob's list ends early"));
            }
            let list = pages.read_page(at, &mut buf)?;
            let listed = (need - found.len()).min(LISTED);
            if list.len() != 6 + 6 * listed {
                return Err(corrupt("a blob's list is not one"));
            }
            lists.push(at);
            at = get_extent(&list[..6]);
            for place in list[6..].chunks_exact(6).map(get_extent) {
                if place.units == 0 || place.units > MAX_UNITS {
                    return Err(corrupt("a blob's page is not one"));
                }
                found.push(place);
            }
        }
        match at.units {
            0 => Ok((lists, found)),
            _ => Err(corrupt("a blob's list does not end")),
        }
    }
}

fn put_extent(out: &mut Vec<u8>, e: Extent) {
    out.extend_from_slice(&e.start.to_le_bytes()[..5]);
    out.push(e.units as u8);
}

fn get_extent(b: &[u8]) -> Extent {
    let mut start = [0u8; 8];
    start[..5].copy_from_slice(&b[..5]);
    Extent { start: u64::from_le_bytes(start), units: b[5] as u32 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;

    /// Bytes of any length come back as written, their pages are found
    /// by a fresh opening, and freed they are space again.
    #[test]
    fn bytes_of_any_length() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let empty = file.space().0;
        let mut rng = Rng::new(0xb10b);
        let mut kept = Vec::new();
        for len in [1, 5, CHUNK - 1, CHUNK, CHUNK + 1, 3 * CHUNK, 2_000_000, 2 * CHUNK + 77] {
            let bytes: Vec<u8> = (0..len).map(|_| rng.next_u64() as u8).collect();
            let txn = file.begin().unwrap();
            let blob = Blob::write(&txn, &bytes).unwrap();
            // Read back within the transaction, and after it.
            assert_eq!(blob.read(&txn).unwrap(), bytes);
            txn.commit(&[]).unwrap();
            assert_eq!(blob.read(&file).unwrap(), bytes);
            let mut coded = Vec::new();
            Blob::put_option(&Some(blob), &mut coded);
            assert_eq!((coded.len(), Blob::get_option(&coded).unwrap()), (Blob::BYTES, Some(blob)));
            kept.push((blob, bytes));
        }
        assert_eq!(Blob::get_option(&[0; 10]).unwrap(), None);
        assert!(Blob::get_option(&[0, 0, 0, 0, 0, 0, 1, 0, 0, 0]).is_err());

        // A fresh opening that marks them has the same space in use.
        let again = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        for (blob, bytes) in &kept {
            blob.mark(&again).unwrap();
            assert_eq!(blob.read(&again).unwrap(), *bytes);
        }
        again.seal();
        assert_eq!(again.space().0, file.space().0);
        // A length that is not the chain's is found out.
        let (blob, _) = kept[5];
        assert!(Blob { len: blob.len + CHUNK as u32, ..blob }.read(&file).is_err());
        assert!(Blob { len: blob.len - CHUNK as u32, ..blob }.read(&file).is_err());
        assert!(Blob { len: blob.len - 1, ..blob }.read(&file).is_err());
        let (blob, _) = kept[3];
        assert!(Blob { len: blob.len - 1, ..blob }.read(&file).is_err());
        assert!(Blob { len: blob.len + 1, ..blob }.read(&file).is_err());

        let txn = file.begin().unwrap();
        kept.iter().for_each(|(blob, _)| blob.free(&txn).unwrap());
        txn.commit(&[]).unwrap();
        assert_eq!(file.space().0, empty);
    }

    /// A file opened finds where bytes are without reading them: of
    /// what fits one page nothing is read, and of what is long its
    /// list, however many megabytes there are.
    #[test]
    fn the_pages_are_found_without_reading_the_bytes() {
        use crate::store::testing::{Counting, temp_dir};
        let dir = temp_dir("blob-marked");
        let file = PageFile::create(Counting::open(&dir.join("state"))).unwrap();
        let txn = file.begin().unwrap();
        let blobs = [1, CHUNK, CHUNK + 1, LISTED * CHUNK, LISTED * CHUNK + 1, 2_000_000]
            .map(|len| (len, Blob::write(&txn, &vec![7u8; len]).unwrap()));
        txn.commit(&[]).unwrap();
        let used = file.space().0;
        drop(file);
        let again = PageFile::open(Counting::open(&dir.join("state"))).unwrap();
        again.backend().take();
        for (len, blob) in blobs {
            blob.mark(&again).unwrap();
            let [reads, bytes, ..] = again.backend().take();
            let lists = if len > CHUNK { len.div_ceil(CHUNK).div_ceil(LISTED) as u64 } else { 0 };
            assert_eq!(reads, lists, "{len}");
            assert!(bytes <= lists * (MAX_UNITS as usize * UNIT) as u64, "{len}: {bytes}");
        }
        again.seal();
        assert_eq!(again.space().0, used);
        let _ = std::fs::remove_dir_all(dir);
    }
}
