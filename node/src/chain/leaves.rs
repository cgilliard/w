//! What a header's auxiliary bytes commit to, and the votes they cast.
//!
//! A header has 32 bytes of the miner's own, under the proof of work
//! and unread by the chain's rules. By convention they are the SHA-256
//! Merkle root of sixteen leaves of 32 bytes ([`aux_merkle_root`]), all
//! zero for a miner with nothing to say. Leaf 0 is a vote: the SHA-256
//! of the consensus file the miner favours ([`crate::consensus`]).
//!
//! A block's leaves are not in the block. A node asks for them, checks
//! them against the header's bytes, and keeps them as long as the body
//! ([`Chain::put_aux_leaves`]); from them it counts the votes of a
//! window of the chain ([`Chain::consensus_votes`]).
//!
//! The files voted for are kept by their hash. They are not kept for
//! good: [`Chain::keep_consensus_files`] lets go of every file but those
//! named, which are the one in force, the one before it while a change
//! lasts, and those the window's votes name.

use crate::consensus::{Hash, MAX_CONSENSUS, Votes, file_id};
use crate::error::Error;
use crate::hash::Digest;
use crate::sha256::{Sha256, sha256};
use crate::store::backend::Backend;

use super::Chain;

/// Leaves a header's auxiliary bytes commit to.
pub const AUX_LEAVES: usize = 16;
/// A block's leaves, or a node's own.
pub type Leaves = [[u8; 32]; AUX_LEAVES];
const LEAVES_BYTES: usize = 32 * AUX_LEAVES;

/// The SHA-256 Merkle root of sixteen leaves, a node the hash of its
/// two halves, or all zero while every leaf is zero: the auxiliary
/// bytes of a header whose miner says nothing.
pub fn aux_merkle_root(leaves: &Leaves) -> [u8; 32] {
    if leaves.iter().all(|l| *l == [0u8; 32]) {
        return [0u8; 32];
    }
    let mut level = *leaves;
    let mut n = AUX_LEAVES;
    while n > 1 {
        for i in 0..n / 2 {
            let mut h = Sha256::new();
            h.update(&level[2 * i]);
            h.update(&level[2 * i + 1]);
            level[i] = h.finish();
        }
        n /= 2;
    }
    level[0]
}

fn leaves_of(bytes: &[u8]) -> Result<Leaves, Error> {
    if bytes.len() != LEAVES_BYTES {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "leaves kept are not sixteen").into());
    }
    Ok(core::array::from_fn(|i| bytes[32 * i..32 * i + 32].try_into().unwrap()))
}

impl<B: Backend + 'static, V> Chain<B, V> {
    /// The node's own leaves: all zero until set. Their root goes in the
    /// headers it mines.
    pub fn aux_leaves(&self) -> Result<Leaves, Error> {
        let store = self.store();
        let snap = store.view()?;
        match snap.blocks().note(snap.pages())? {
            Some(bytes) => leaves_of(&bytes),
            None => Ok([[0u8; 32]; AUX_LEAVES]),
        }
    }

    /// Sets the node's own leaf `index` (0 to 15). Returns the new root.
    pub fn set_aux_leaf(&self, index: usize, value: [u8; 32]) -> Result<[u8; 32], Error> {
        assert!(index < AUX_LEAVES, "a leaf's index is below sixteen");
        self.write_blocks(|txn, blocks| {
            let mut leaves = match blocks.note(txn)? {
                Some(bytes) => leaves_of(&bytes)?,
                None => [[0u8; 32]; AUX_LEAVES],
            };
            leaves[index] = value;
            blocks.set_note(txn, Some(leaves.as_flattened()))?;
            Ok(aux_merkle_root(&leaves))
        })
        .inspect(|_| self.votes_changed())
    }

    /// The auxiliary bytes this node mines with: the root of its leaves.
    pub fn aux_root(&self) -> Result<[u8; 32], Error> {
        Ok(aux_merkle_root(&self.aux_leaves()?))
    }

    /// The leaves of the block of id `id`, if they are kept: checked
    /// against its header when they were.
    pub fn aux_leaves_of(&self, id: &Digest) -> Result<Option<Leaves>, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let Some(known) = self.known_in(pages, blocks, id)? else { return Ok(None) };
        blocks.aux(pages, known.header.height, id)?.map(|bytes| leaves_of(&bytes)).transpose()
    }

    /// Keeps the leaves of the block of id `id`, checked against its
    /// header: [`Error::AuxMismatch`] if their root is not the header's
    /// auxiliary bytes, or the header is not known. A header whose bytes
    /// are zero has no leaves to keep.
    pub fn put_aux_leaves(&self, id: &Digest, leaves: &Leaves) -> Result<(), Error> {
        self.write_blocks(|txn, blocks| {
            let Some(known) = self.known_in(txn, blocks, id)? else { return Err(Error::AuxMismatch) };
            if known.header.aux == [0u8; 32] || aux_merkle_root(leaves) != known.header.aux {
                return Err(Error::AuxMismatch);
            }
            blocks.put_aux(txn, known.header.height, id, leaves.as_flattened())
        })?;
        self.votes_changed();
        Ok(())
    }

    /// How many times the leaves and files kept have changed: whoever
    /// counted the votes need not count them again while this and the
    /// chain's last block are what they were.
    pub fn votes_epoch(&self) -> u64 {
        self.votes_epoch.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn votes_changed(&self) {
        self.votes_epoch.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// The votes of the last `window` blocks of the chain: each block's
    /// leaf 0 where its leaves are kept, and which blocks' are missing.
    pub fn consensus_votes(&self, window: u32) -> Result<Votes, Error> {
        let tip = self.store().view()?.tip().0;
        self.consensus_votes_at(tip, window)
    }

    /// The votes of the `window` blocks of the chain ending at `end`.
    pub fn consensus_votes_at(&self, end: u32, window: u32) -> Result<Votes, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let first = (end + 1).saturating_sub(window);
        let mut all = Vec::with_capacity((end + 1 - first) as usize);
        for height in first..=end {
            let Some(header) = self.header_at_in(pages, blocks, height)? else {
                return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "the chain lacks a height").into());
            };
            let id = header.hash();
            let vote = match header.aux == [0u8; 32] {
                true => Some([0u8; 32]),
                false => blocks.aux(pages, height, &id)?.map(|bytes| leaves_of(&bytes)).transpose()?.map(|l| l[0]),
            };
            all.push((id, height, vote));
        }
        Ok(Votes::tally((first, end), all.into_iter()))
    }

    /// The consensus file in force: what the votes of the window ending
    /// at the last boundary at or under the chain's last block decided
    /// ([`crate::consensus::boundary`]), of the files held. It changes
    /// only at a boundary; until the first, or while nothing that
    /// counts was voted for, the mode is init. With the votes it was
    /// decided from.
    pub fn consensus(&self) -> Result<(crate::consensus::Current, Votes), Error> {
        let tip = self.store().view()?.tip().0;
        let end = crate::consensus::boundary(tip);
        let votes = match end {
            // (Before the first boundary nothing has been decided.)
            0 => Votes::default(),
            _ => self.consensus_votes_at(end, crate::consensus::WINDOW)?,
        };
        let mut failed = None;
        let of = crate::consensus::WINDOW;
        let current = crate::consensus::Current::decide(&votes, of, |hash| match self.consensus_file(hash) {
            Ok(file) => file,
            Err(e) => {
                failed = Some(e);
                None
            }
        });
        match failed {
            Some(e) => Err(e),
            None => Ok((current, votes)),
        }
    }

    /// Holds a consensus file; returns its SHA-256, the value that votes
    /// for it. [`Error::TooLarge`] for one larger than a file may be.
    pub fn put_consensus_file(&self, bytes: &[u8]) -> Result<Hash, Error> {
        if bytes.len() > MAX_CONSENSUS {
            return Err(Error::TooLarge(bytes.len()));
        }
        let hash = sha256(bytes);
        self.write_blocks(|txn, blocks| blocks.put_file(txn, &hash, bytes))?;
        self.votes_changed();
        Ok(hash)
    }

    /// The output that was unspent at `position` as of the block at
    /// `height` on this chain, and its path to that block's state
    /// root: what shows that the block made it, where `height` is the
    /// height it was made at ([`crate::proofs`]). None if there was no
    /// such output; [`Error::NoUndoRecord`] of a block further back
    /// than the chain can still be taken to.
    pub fn output_proof_at(
        &self,
        position: u64,
        height: u32,
    ) -> Result<Option<(crate::store::outputs::Record, [Digest; crate::store::state::STATE_HEIGHT])>, Error> {
        let state = self.whole()?;
        let past = state.past(height)?;
        Ok(past.prove(position)?)
    }

    /// A consensus file held, by its SHA-256.
    pub fn consensus_file(&self, hash: &Hash) -> Result<Option<Vec<u8>>, Error> {
        let store = self.store();
        let snap = store.view()?;
        Ok(snap.blocks().file(snap.pages(), hash)?)
    }

    /// A consensus file held, by its transfer id
    /// ([`crate::consensus::file_id`]): what a peer asks for.
    pub fn consensus_file_by_id(&self, id: &Digest) -> Result<Option<Vec<u8>>, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        match blocks.files(pages)?.into_iter().find(|hash| file_id(hash) == *id) {
            Some(hash) => Ok(blocks.file(pages, &hash)?),
            None => Ok(None),
        }
    }

    /// The hashes of the consensus files held.
    pub fn consensus_files(&self) -> Result<Vec<Hash>, Error> {
        let store = self.store();
        let snap = store.view()?;
        Ok(snap.blocks().files(snap.pages())?)
    }

    /// Lets go of every consensus file but those of `keep`: the one in
    /// force, the one before it while a change lasts, and those the
    /// window's votes name. Returns how many went.
    pub fn keep_consensus_files(&self, keep: &[Hash]) -> Result<usize, Error> {
        // (Looked at before anything is taken to be written: this is
        // asked again and again, there is seldom anything to let go
        // of, and whoever waits to write holds up everyone who comes
        // to read after.)
        {
            let store = self.store();
            let snap = store.view()?;
            if snap.blocks().files(snap.pages())?.iter().all(|hash| keep.contains(hash)) {
                return Ok(0);
            }
        }
        let gone = self.write_blocks(|txn, blocks| {
            let mut gone = 0;
            for hash in blocks.files(txn)? {
                if !keep.contains(&hash) {
                    blocks.drop_file(txn, &hash)?;
                    gone += 1;
                }
            }
            Ok(gone)
        })?;
        self.votes_changed();
        Ok(gone)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::{Block, BlockRef, Body, BodyRef, Header};
    use crate::chain::apply::Applied;
    use crate::chain::headers::tests::{NOW, easy, seed, table};
    use crate::chain::params::COIN;
    use crate::chain::verify::AcceptAllProofs;
    use crate::pow::hashimoto;
    use crate::store::testing::{Lost, MemBackend};

    type TestChain = Chain<MemBackend, AcceptAllProofs>;

    fn open_on(backend: MemBackend, keep: usize) -> TestChain {
        let chain = Chain::open(backend, keep, easy(), seed(), AcceptAllProofs).unwrap();
        chain.set_dataset(table());
        chain
    }

    fn leaves(vote: u8, other: u8) -> Leaves {
        let mut l = [[0u8; 32]; AUX_LEAVES];
        l[0] = [vote; 32];
        l[9] = [other; 32];
        l
    }

    /// The next block of the chain, its header's auxiliary bytes `aux`,
    /// applied.
    fn extend(chain: &TestChain, aux: [u8; 32]) -> Header {
        let parent = chain.tip().unwrap();
        let out =
            crate::block::BlockOutput { commitment: [parent.height as u8 + 1; 32], memo: [0; 20], amount: 1500 * COIN };
        let body = Body { outputs: vec![out], ..Body::default() };
        let bytes = body.to_bytes();
        let (state_root, statement) = chain.header_after(&BodyRef::from_bytes(&bytes).unwrap()).unwrap();
        let mut header = Header {
            prev_hash: parent.hash(),
            height: parent.height + 1,
            timestamp: parent.timestamp + 600,
            body_commitment: body.commitment(),
            state_root,
            statement: statement.digest(),
            aux,
            mix: [0; 32],
            nonce: [0; 32],
        };
        header.mix = hashimoto(&*table(), &header.pow_hash(), &header.nonce).mix;
        let block = Block { header, body }.to_bytes();
        assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
        header
    }

    /// The root is the tree's: by the definition, and zero for nothing.
    #[test]
    fn the_root_of_sixteen_leaves() {
        assert_eq!(aux_merkle_root(&[[0u8; 32]; AUX_LEAVES]), [0u8; 32]);
        let l: Leaves = core::array::from_fn(|i| [i as u8 + 1; 32]);
        let pair = |a: &[u8; 32], b: &[u8; 32]| sha256(&[&a[..], &b[..]].concat());
        let mut level: Vec<[u8; 32]> = l.to_vec();
        while level.len() > 1 {
            level = level.chunks(2).map(|p| pair(&p[0], &p[1])).collect();
        }
        assert_eq!(aux_merkle_root(&l), level[0]);
        // Every leaf counts, and so does its place.
        let mut other = l;
        other.swap(3, 4);
        assert_ne!(aux_merkle_root(&other), level[0]);
        let mut one = [[0u8; 32]; AUX_LEAVES];
        one[15][31] = 1;
        assert_ne!(aux_merkle_root(&one), [0u8; 32]);
    }

    /// A node's own leaves are kept, and their root is what it mines
    /// with.
    #[test]
    fn a_nodes_own_leaves() {
        let chain = open_on(MemBackend::new(), 8);
        assert_eq!((chain.aux_leaves().unwrap(), chain.aux_root().unwrap()), ([[0u8; 32]; AUX_LEAVES], [0u8; 32]));
        let root = chain.set_aux_leaf(0, [7; 32]).unwrap();
        assert_eq!(chain.set_aux_leaf(9, [3; 32]).unwrap(), aux_merkle_root(&leaves(7, 3)));
        assert_ne!(root, chain.aux_root().unwrap());
        assert_eq!(chain.aux_leaves().unwrap(), leaves(7, 3));
        let again = open_on(MemBackend::from_image(chain.state().file().backend().image(Lost::All)), 8);
        assert_eq!(again.aux_leaves().unwrap(), leaves(7, 3));
        again.state().wait_ready().unwrap();
        assert_eq!(again.state().file().space().0, chain.state().file().space().0);
        // Set back to nothing, the root is zero again.
        chain.set_aux_leaf(0, [0; 32]).unwrap();
        assert_eq!(chain.set_aux_leaf(9, [0; 32]).unwrap(), [0u8; 32]);
    }

    /// A block's leaves are kept if they are its header's, the votes of
    /// a window are counted from them, and they go when the body does.
    #[test]
    fn votes_are_counted_from_the_leaves_kept() {
        let chain = open_on(MemBackend::new(), 4);
        let (a, b) = (leaves(1, 0), leaves(2, 5));
        // Heights 1 to 6: a, b, nothing, b, a, b.
        let said = [Some(a), Some(b), None, Some(b), Some(a), Some(b)];
        let headers: Vec<Header> =
            said.iter().map(|l| extend(&chain, l.map_or([0; 32], |l| aux_merkle_root(&l)))).collect();
        let id = |h: usize| headers[h - 1].hash();
        // Nothing fetched yet: the blocks that said something are missing.
        let votes = chain.consensus_votes(4).unwrap();
        assert_eq!((votes.range, votes.blocks, votes.cast()), ((3, 6), 4, 0));
        assert_eq!(votes.missing, vec![(id(4), 4), (id(5), 5), (id(6), 6)]);
        // Leaves that are not the header's, or of a header that has
        // none, or of no header.
        assert_eq!(chain.put_aux_leaves(&id(4), &a), Err(Error::AuxMismatch));
        assert_eq!(chain.put_aux_leaves(&id(3), &a), Err(Error::AuxMismatch));
        assert_eq!(chain.put_aux_leaves(&id(3), &[[0; 32]; AUX_LEAVES]), Err(Error::AuxMismatch));
        assert_eq!(chain.put_aux_leaves(&[9; 32], &a), Err(Error::AuxMismatch));
        assert_eq!(chain.aux_leaves_of(&id(4)).unwrap(), None);
        for h in [4, 5, 6] {
            chain.put_aux_leaves(&id(h), &said[h - 1].unwrap()).unwrap();
        }
        assert_eq!(chain.aux_leaves_of(&id(4)).unwrap(), Some(b));
        let votes = chain.consensus_votes(4).unwrap();
        assert_eq!(votes.counts, vec![([2; 32], 2, 6), ([1; 32], 1, 5)]);
        assert!(votes.missing.is_empty());
        // A window that ends earlier, and one longer than the chain.
        assert_eq!(chain.consensus_votes_at(5, 2).unwrap().counts, vec![([1; 32], 1, 5), ([2; 32], 1, 4)]);
        let all = chain.consensus_votes(100).unwrap();
        assert_eq!((all.range, all.blocks), ((0, 6), 7));
        assert_eq!(all.missing, vec![(id(1), 1), (id(2), 2)]);
        // Two blocks on: the leaves of block 4 went with its body.
        extend(&chain, [0; 32]);
        extend(&chain, [0; 32]);
        assert_eq!(chain.aux_leaves_of(&id(4)).unwrap(), None);
        assert_eq!(chain.aux_leaves_of(&id(5)).unwrap(), Some(a));
    }

    /// Consensus files are held by their hash, found by their id, and
    /// let go when they are no longer wanted.
    #[test]
    fn consensus_files_are_held_while_wanted() {
        let chain = open_on(MemBackend::new(), 8);
        let files: Vec<Vec<u8>> = vec![b"mode init\n".to_vec(), vec![b'x'; 70_000], vec![b'#'; MAX_CONSENSUS]];
        let hashes: Vec<Hash> = files.iter().map(|f| chain.put_consensus_file(f).unwrap()).collect();
        assert_eq!(hashes[0], sha256(b"mode init\n"));
        assert_eq!(chain.put_consensus_file(&files[1]), Ok(hashes[1]));
        assert_eq!(chain.put_consensus_file(&vec![0; MAX_CONSENSUS + 1]), Err(Error::TooLarge(MAX_CONSENSUS + 1)));
        for (hash, file) in hashes.iter().zip(&files) {
            assert_eq!(chain.consensus_file(hash).unwrap().as_ref(), Some(file));
            assert_eq!(chain.consensus_file_by_id(&file_id(hash)).unwrap().as_ref(), Some(file));
        }
        assert_eq!(chain.consensus_file(&[9; 32]).unwrap(), None);
        assert_eq!(chain.consensus_file_by_id(&file_id(&[9; 32])).unwrap(), None);
        assert_eq!(chain.consensus_files().unwrap().len(), 3);
        // All but the first and one not held: two go, and their space.
        let used = chain.state().file().space().0;
        assert_eq!(chain.keep_consensus_files(&[hashes[0], [9; 32]]).unwrap(), 2);
        assert_eq!(chain.consensus_files().unwrap(), vec![hashes[0]]);
        assert_eq!(chain.consensus_file(&hashes[2]).unwrap(), None);
        assert!(chain.state().file().space().0 + 2000 < used);
        assert_eq!(chain.keep_consensus_files(&[hashes[0]]).unwrap(), 0);
        assert_eq!(chain.keep_consensus_files(&[]).unwrap(), 1);
    }
}
