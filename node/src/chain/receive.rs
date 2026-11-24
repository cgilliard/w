//! Taking the state whole from other nodes, in place of applying every
//! block there has been.
//!
//! A node keeps the bodies of the blocks it can undo and no others, so
//! a node further behind than that cannot be given the blocks it lacks:
//! nobody has them. It is given the state instead, as of a block not
//! long past, and applies the blocks from there on.
//!
//! # What is trusted
//!
//! The headers, which the node has checked for itself: so the block the
//! state is taken as of has the work of the chain behind it, and its
//! header says what the state's root is. Then that block's own proof
//! ([`Chain::check_state_block`]), which on a network whose blocks carry
//! a proof of the whole chain shows every block before it valid.
//! Everything else that is handed over is checked against the root, a
//! part at a time, by the store ([`crate::store::receive`]).
//!
//! # While it is being received
//!
//! The chain has headers and no state ([`super::Store`]). Headers are
//! taken as ever, and the best of them goes on being followed; nothing
//! that needs the state can be done, and says so
//! ([`Error::Receiving`]). When the last part is in the chain is whole
//! again, its last block the one the state is of
//! ([`Chain::finish_receiving`]), and the blocks after it are fetched
//! and applied in the ordinary way.
//!
//! If the taking outlasts what the nodes that serve it can still go
//! back to, it is gone on with as of a later block
//! ([`Chain::begin_receiving`], again): the parts that are the same
//! are kept.

use crate::block::{BlockRef, BodyRef, Header};
use crate::error::Error;
use crate::hash::Digest;
use crate::name::Record as NameRecord;
use crate::store::backend::Backend;
use crate::store::outputs::Record;
use crate::store::receive::{Receiving, Target};
use crate::store::trie::Part;

use super::headers::{Known, Status};
use super::verify::{BlockStatement, ProofVerifier};
use super::{Chain, Store};

fn corrupt(what: &'static str) -> Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, what).into()
}

impl<B: Backend + 'static, V: ProofVerifier + Sync> Chain<B, V> {
    /// Checks the block a state is to be taken as of, before any of
    /// that state is: its header is one kept here, its body is that
    /// header's, and its proof is accepted, given that the position
    /// after its last output is `next` and that the outputs' root and
    /// the names' after it are `roots` (which whoever hands the state
    /// over says, and the header and the proof hold them to).
    pub fn check_state_block(&self, block: &BlockRef<'_>, next: u64, roots: &(Digest, Digest)) -> Result<(), Error> {
        let (header, body) = (block.header(), block.body());
        let (known, target) = {
            let store = self.store();
            let snap = store.view()?;
            let (pages, blocks) = (snap.pages(), snap.blocks());
            let known = self.known_in(pages, blocks, &header.hash())?.ok_or(Error::UnknownParent)?;
            // (What its work is held to, if its work was never looked
            // at in full.)
            let target = match known.status {
                Status::WorkPending => {
                    let parent = self.known_in(pages, blocks, &header.prev_hash)?.ok_or(Error::UnknownParent)?;
                    let first = self.anchor_in(pages, blocks, &parent.header)?;
                    Some(self.target_from(&parent.header, first.as_ref()))
                }
                _ => None,
            };
            (known, target)
        };
        if known.invalid() {
            return Err(Error::KnownInvalid);
        }
        // Its proof attests the work of the headers before it, and not
        // its own: that is checked here, whoever calls, if it was left
        // to a proof.
        if target.is_some_and(|target| !self.full_pow(header, &target)) {
            return Err(Error::BadProofOfWork);
        }
        self.check_body(header, &body)?;
        if crate::registry::state_root(&roots.0, &roots.1) != header.state_root {
            return Err(Error::PartRoot);
        }
        let chain = self.statement(header.height, &header.prev_hash, &body, roots, next);
        let digest = chain.digest();
        if digest != header.statement {
            return Err(Error::BadProof);
        }
        match self.verifier.verify(&BlockStatement { chain, digest, body }, body.proof()) {
            true => Ok(()),
            false => Err(Error::BadProof),
        }
    }

    /// Begins to receive the state as of the block of `header`, or goes
    /// on with it as of that block in place of another. `next` is the
    /// position after the block's last output, and `parts` and
    /// `name_parts` the roots of the state's parts, as another node
    /// gave them: [`Error::PartRoot`], with nothing changed, if they
    /// are not those of the header's state root.
    ///
    /// The roots are held to the header. `next` is not, by anything
    /// here: it is the block's proof that holds it
    /// ([`Chain::check_state_block`]), which is to be asked first.
    ///
    /// The state there was is given up, and from here until
    /// [`Chain::finish_receiving`] the chain has none.
    pub fn begin_receiving(
        &self,
        header: &Header,
        next: u64,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
    ) -> Result<(), Error> {
        let target = Target { height: header.height, block: header.hash(), state_root: header.state_root, next };
        let best = self.best_header()?.header;
        let mut store = self.store_mut();
        let began = match std::mem::replace(&mut *store, Store::Gone) {
            Store::Whole(state) => {
                let old_tip = state.tip().0;
                // (Checked before the state is given up: refused, the
                // state is still the store's.)
                match Receiving::<B>::check_roots(&target, parts, name_parts) {
                    Err(e) => {
                        *store = Store::Whole(state);
                        return Err(e);
                    }
                    // The chain has no blocks but its first while it
                    // has no state: what it had is the best header's
                    // branch to fetch, or not. Said in the step the
                    // state is given up in: a node that stopped between
                    // the two would have a chain of blocks and no state
                    // they were the blocks of.
                    Ok(()) => Receiving::replace_with(state, target, parts, name_parts, |txn, blocks| {
                        if old_tip > 0 {
                            blocks.clear_heights(txn, 1, old_tip.saturating_add(1))?;
                            self.plan(txn, blocks, &best)?;
                        }
                        Ok(())
                    }),
                }
            }
            Store::Receiving(receiving) => match receiving.retarget(target, parts, name_parts) {
                Ok(r) => Ok(r),
                Err((r, Error::PartRoot)) => {
                    *store = Store::Receiving(r);
                    return Err(Error::PartRoot);
                }
                Err((_, e)) => Err(e),
            },
            Store::Gone => Err(Error::Receiving),
        };
        // (A failure past the checks is the file's: the store is gone,
        // and is to be opened again.)
        *store = Store::Receiving(began?);
        Ok(())
    }

    /// The block the state is being received as of: its height and id.
    pub fn receiving_as_of(&self) -> Option<(u32, Digest)> {
        match &*self.store() {
            Store::Receiving(r) => Some((r.target().height, r.target().block)),
            _ => None,
        }
    }

    /// The first `most` parts of the outputs still to be put, how many
    /// there are in all, and the parts of the names still to be put:
    /// [`Chain::missing_parts`], at a cost that does not grow with the
    /// state.
    pub fn missing_parts_first(&self, most: usize) -> Result<(Vec<u64>, usize, Vec<u32>), Error> {
        match &*self.store() {
            Store::Receiving(r) if !r.roots_known() => Err(Error::PartsMissing),
            Store::Receiving(r) => {
                let (first, all) = r.missing_first(most);
                Ok((first, all, r.missing_names()))
            }
            _ => Err(Error::Receiving),
        }
    }

    /// The parts of the outputs, and of the names, still to be put.
    pub fn missing_parts(&self) -> Result<(Vec<u64>, Vec<u32>), Error> {
        match &*self.store() {
            // (Not known, of a state opened again after its receiving
            // was cut short, until it is begun again.)
            Store::Receiving(r) if !r.roots_known() => Err(Error::PartsMissing),
            Store::Receiving(r) => Ok((r.missing(), r.missing_names())),
            _ => Err(Error::Receiving),
        }
    }

    /// Puts a part of the outputs of the state being received: its
    /// unspent outputs, and which of them are commits of names.
    /// [`Error::PartRoot`], with nothing changed, if they are not that
    /// part.
    pub fn put_part(&self, index: u64, outputs: &[(u64, Record)], commits: &[(u64, Digest)]) -> Result<(), Error> {
        match &mut *self.store_mut() {
            Store::Receiving(r) => r.put_with(index, outputs, commits),
            _ => Err(Error::Receiving),
        }
    }

    /// Several parts of the outputs put at once, ascending by index:
    /// all of them, or, if any is not its part, none
    /// ([`crate::store::receive::Receiving::put_many`]).
    #[allow(clippy::type_complexity)]
    pub fn put_parts(&self, parts: &[(u64, &[(u64, Record)], &[(u64, Digest)])]) -> Result<(), Error> {
        match &mut *self.store_mut() {
            Store::Receiving(r) => r.put_many(parts),
            _ => Err(Error::Receiving),
        }
    }

    /// Puts a part of the names of the state being received.
    pub fn put_names(&self, index: u32, records: &[NameRecord]) -> Result<(), Error> {
        match &mut *self.store_mut() {
            Store::Receiving(r) => r.put_names(index, records),
            _ => Err(Error::Receiving),
        }
    }

    /// Every part is in: the chain is whole again, its last block the
    /// one the state is of. `body` is that block's body, kept so that
    /// it can be served and, if the chain goes over to another branch
    /// above it, need not be fetched again. [`Error::PartsMissing`],
    /// with nothing changed, if parts are still to be put.
    pub fn finish_receiving(&self, body: &[u8]) -> Result<(), Error> {
        let mut store = self.store_mut();
        let receiving = match std::mem::replace(&mut *store, Store::Gone) {
            Store::Receiving(r) => r,
            other => {
                *store = other;
                return Err(Error::Receiving);
            }
        };
        let (missing, missing_names) = (receiving.missing(), receiving.missing_names());
        if !receiving.roots_known() || !missing.is_empty() || !missing_names.is_empty() {
            *store = Store::Receiving(receiving);
            return Err(Error::PartsMissing);
        }
        let target = *receiving.target();
        // The chain is the block's branch, from the first block up: said
        // of each height, and planned no more. In the step the state
        // becomes whole in: a node that stopped between the two would
        // have a state at a block its chain did not have.
        let finished = receiving.finish_with(self.keep, |txn, blocks| {
            let known = self.known_in(txn, blocks, &target.block)?.ok_or_else(|| corrupt("the block is not kept"))?;
            // (The body is that block's, whoever hands it over.)
            if BodyRef::from_bytes(body)?.commitment() != known.header.body_commitment {
                return Err(Error::BadBodyCommitment);
            }
            // (All of them at once: a chain is as many heights as it
            // has blocks.)
            let mut h = known.header;
            let mut heights = Vec::with_capacity(h.height as usize);
            while h.height > 0 {
                heights.push((h.height, h.hash()));
                h = self
                    .known_in(txn, blocks, &h.prev_hash)?
                    .ok_or_else(|| corrupt("a header's ancestor is missing"))?
                    .header;
            }
            heights.reverse();
            blocks.set_many(txn, &heights)?;
            blocks.drop_planned(txn, 0, target.height.saturating_add(1))?;
            blocks.put_entry(txn, &Known { status: Status::Valid, ..known }.entry())?;
            blocks.put_body(txn, target.height, &target.block, body)
        });
        match finished {
            Ok(state) => {
                *store = Store::Whole(state);
                Ok(())
            }
            // (Refused before anything was the file's: it goes on
            // being received.)
            Err((Some(receiving), e)) => {
                *store = Store::Receiving(*receiving);
                Err(e)
            }
            Err((None, e)) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::apply::Applied;
    use crate::chain::apply::tests::grow;
    use crate::chain::headers::tests::{NOW, easy, seed, table};
    use crate::chain::verify::AcceptAllProofs;
    use crate::store::testing::MemBackend;

    type TestChain = Chain<MemBackend, AcceptAllProofs>;

    fn open(keep: usize) -> TestChain {
        let chain = Chain::open(MemBackend::new(), keep, easy(), seed(), AcceptAllProofs).unwrap();
        chain.set_dataset(table());
        chain
    }

    fn headers_of(blocks: &[Vec<u8>]) -> Vec<Header> {
        blocks.iter().map(|b| *BlockRef::from_bytes(b).unwrap().header()).collect()
    }

    /// A part of the outputs, as it is handed over: which part, its
    /// outputs by position, and hashes by position.
    type OutputsPart = (u64, Vec<(u64, Record)>, Vec<(u64, Digest)>);

    /// What a node that has the state hands over, as of `height`.
    struct Handed {
        next: u64,
        parts: Vec<(u64, Digest)>,
        name_parts: Vec<(u32, Part)>,
        /// The outputs' root and the names'.
        roots: (Digest, Digest),
        outputs: Vec<OutputsPart>,
    }

    fn hand_over(from: &TestChain, height: u32) -> Handed {
        let state = from.state();
        let past = state.past(height).unwrap();
        let parts = past.parts().to_vec();
        let outputs = parts.iter().map(|(i, _)| (*i, past.part(*i).unwrap(), past.commits(*i).unwrap())).collect();
        let roots = (crate::store::outputs::parts_root(crate::store::outputs::PART_LEVEL, &parts), past.names_root());
        Handed { next: past.next(), parts, name_parts: past.name_parts().to_vec(), roots, outputs }
    }

    /// Gives `chain` everything of `handed` and makes it whole.
    fn take(chain: &TestChain, handed: &Handed, block: &[u8]) {
        let (missing, names) = chain.missing_parts().unwrap();
        assert!(names.is_empty());
        for index in missing {
            let (_, outputs, commits) = handed.outputs.iter().find(|o| o.0 == index).unwrap();
            chain.put_part(index, outputs, commits).unwrap();
        }
        chain.finish_receiving(&block[crate::block::HEADER_SIZE..]).unwrap();
    }

    /// A node with the headers takes the state as of a block, and from
    /// there is as a node that applied every block: the same chain, the
    /// same state, and the blocks after join it as they would.
    #[test]
    fn a_state_taken_is_the_state_of_its_block() {
        let ahead = open(64);
        let blocks = grow(&ahead, 30, 1);
        let headers = headers_of(&blocks);
        let node = open(64);
        assert_eq!(node.accept_headers(&headers, NOW, false), (30, None));
        let (at, block) = (headers[19], &blocks[19]);
        let handed = hand_over(&ahead, 20);
        // The block's own proof first, held to the position after it.
        let view = BlockRef::from_bytes(block).unwrap();
        assert_eq!(node.check_state_block(&view, handed.next, &handed.roots), Ok(()));
        // Roots that are not the state's are refused, and the chain is
        // as it was.
        let mut wrong = handed.parts.clone();
        wrong[0].1[0] ^= 1;
        assert_eq!(node.begin_receiving(&at, handed.next, &wrong, &handed.name_parts), Err(Error::PartRoot));
        assert!(!node.receiving() && node.state().tip().0 == 0);
        node.begin_receiving(&at, handed.next, &handed.parts, &handed.name_parts).unwrap();
        assert!(node.receiving());
        assert_eq!(node.receiving_as_of(), Some((20, at.hash())));
        // While it is being received: no state, and no block joins.
        assert_eq!(node.whole().err(), Some(Error::Receiving));
        assert_eq!(node.apply_block(&view, NOW).err(), Some(Error::Receiving));
        assert_eq!(node.finish_receiving(&[]).err(), Some(Error::PartsMissing));
        // The headers are there as ever, and the bodies they call for.
        assert_eq!(node.tip().unwrap().height, 0);
        assert_eq!(node.best_header().unwrap().header, headers[29]);
        assert_eq!(node.known(&headers[5].hash()).unwrap().unwrap().header, headers[5]);
        let mut need = [at; 4];
        assert_eq!(node.missing_bodies(&mut need).unwrap(), 4);
        // A part that is not the part is refused.
        let (index, outputs, commits) = &handed.outputs[0];
        let mut tampered = outputs.clone();
        tampered[2].1.amount += 1;
        assert_eq!(node.put_part(*index, &tampered, commits), Err(Error::PartRoot));
        take(&node, &handed, block);
        // Whole: the block is the chain's last, and the chain is its
        // branch from the first block up.
        assert!(!node.receiving());
        assert_eq!(node.tip().unwrap(), at);
        let root = node.state().root();
        assert_eq!((root, node.state().tip()), (at.state_root, (20, at.hash())));
        for h in [1u32, 7, 20] {
            assert_eq!(node.header_at(h).unwrap(), Some(headers[h as usize - 1]));
        }
        assert_eq!(node.header_at(21).unwrap(), None);
        assert_eq!(node.tip_work().unwrap(), ahead.known(&at.hash()).unwrap().unwrap().work);
        assert_eq!(node.body(&at.hash()).unwrap().unwrap(), block[crate::block::HEADER_SIZE..]);
        // What it lacks now is the blocks after, and they join.
        let mut need = [at; 16];
        assert_eq!(node.missing_bodies(&mut need).unwrap(), 10);
        assert_eq!(need[0], headers[20]);
        for b in &blocks[20..] {
            assert_eq!(node.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW), Ok(Applied::Extended));
        }
        assert_eq!((node.tip().unwrap(), node.state().root()), (ahead.tip().unwrap(), ahead.state().root()));
        // And it goes on as any node: more blocks, made on either.
        let more = grow(&ahead, 3, 2);
        for b in &more {
            assert_eq!(node.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW), Ok(Applied::Extended));
        }
        assert_eq!(node.state().root(), ahead.state().root());
        let own = grow(&node, 2, 3);
        assert_eq!(node.tip().unwrap().height, 35);
        assert_eq!(headers_of(&own)[1], node.tip().unwrap());
    }

    /// Headers go on being taken while a state is received, and the
    /// state can be gone on with as of a later block: what is the same
    /// is kept.
    #[test]
    fn headers_are_taken_and_the_block_moved_while_receiving() {
        let ahead = open(64);
        let blocks = grow(&ahead, 20, 1);
        let headers = headers_of(&blocks);
        let node = open(64);
        assert_eq!(node.accept_headers(&headers, NOW, false), (20, None));
        let handed = hand_over(&ahead, 10);
        node.begin_receiving(&headers[9], handed.next, &handed.parts, &handed.name_parts).unwrap();
        // New blocks are made meanwhile; their headers are taken.
        let more = grow(&ahead, 5, 2);
        let more_headers = headers_of(&more);
        assert_eq!(node.accept_headers(&more_headers, NOW, false), (5, None));
        assert_eq!(node.accept_header(&more_headers[4], NOW), Ok(false));
        assert_eq!(node.best_header().unwrap().header, more_headers[4]);
        assert!(node.receiving());
        // On to a later block: the part it had is asked for again, its
        // root being another now.
        let (index, outputs, commits) = &handed.outputs[0];
        node.put_part(*index, outputs, commits).unwrap();
        assert_eq!(node.missing_parts().unwrap().0, [] as [u64; 0]);
        let later = hand_over(&ahead, 22);
        node.begin_receiving(&more_headers[1], later.next, &later.parts, &later.name_parts).unwrap();
        assert_eq!(node.receiving_as_of(), Some((22, more_headers[1].hash())));
        assert_eq!(node.missing_parts().unwrap().0, [0]);
        take(&node, &later, &more[1]);
        assert_eq!(node.tip().unwrap(), more_headers[1]);
        for b in &more[2..] {
            assert_eq!(node.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW), Ok(Applied::Extended));
        }
        assert_eq!(node.state().root(), ahead.state().root());
    }

    /// A node that has a state, too old to be caught up from, gives it
    /// up for one taken whole.
    #[test]
    fn an_old_state_is_given_up_for_one_taken() {
        let ahead = open(8);
        let early = grow(&ahead, 5, 1);
        let node = open(8);
        for b in &early {
            node.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW).unwrap();
        }
        // The others go on, past what their bodies reach back to.
        let blocks = grow(&ahead, 30, 2);
        let headers = headers_of(&blocks);
        assert_eq!(node.accept_headers(&headers, NOW, false), (30, None));
        assert_eq!(node.tip().unwrap().height, 5);
        let handed = hand_over(&ahead, 30);
        node.begin_receiving(&headers[24], handed.next, &handed.parts, &handed.name_parts).unwrap();
        // No chain but its first block until the state is in.
        assert_eq!((node.tip().unwrap().height, node.header_at(3).unwrap()), (0, None));
        take(&node, &handed, &blocks[24]);
        assert_eq!(node.tip().unwrap(), headers[24]);
        assert_eq!(node.header_at(3).unwrap(), Some(headers_of(&early)[2]));
        for b in &blocks[25..] {
            assert_eq!(node.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW), Ok(Applied::Extended));
        }
        assert_eq!((node.tip().unwrap(), node.state().root()), (ahead.tip().unwrap(), ahead.state().root()));
    }

    /// The block a state is taken as of is held to its proof.
    #[test]
    fn the_block_a_state_is_taken_of_is_checked() {
        #[derive(Clone, Copy)]
        struct OnlyFrom(u64);
        impl ProofVerifier for OnlyFrom {
            fn verify(&self, statement: &BlockStatement<'_>, _: &[u8]) -> bool {
                statement.chain.next == self.0
            }
        }
        let ahead = open(64);
        let blocks = grow(&ahead, 6, 1);
        let headers = headers_of(&blocks);
        // (A verifier that takes the sixth block's statement only if it
        // says the block's one output is the sixth.)
        let roots = hand_over(&ahead, 6).roots;
        let node = Chain::open(MemBackend::new(), 64, easy(), seed(), OnlyFrom(6)).unwrap();
        node.set_dataset(table());
        assert_eq!(node.accept_headers(&headers, NOW, false), (6, None));
        let view = BlockRef::from_bytes(&blocks[5]).unwrap();
        assert_eq!(node.check_state_block(&view, 6, &roots), Ok(()));
        // Another position after it is another statement; a position
        // before its own outputs is none.
        assert_eq!(node.check_state_block(&view, 7, &roots), Err(Error::BadProof));
        assert_eq!(node.check_state_block(&view, 0, &roots), Err(Error::BadProof));
        // A body that is not the header's; a block whose header is not
        // kept.
        let mut other = blocks[5][..crate::block::HEADER_SIZE].to_vec();
        other.extend_from_slice(&blocks[4][crate::block::HEADER_SIZE..]);
        assert_eq!(
            node.check_state_block(&BlockRef::from_bytes(&other).unwrap(), 6, &roots),
            Err(Error::BadBodyCommitment)
        );
        let stranger = grow(&ahead, 1, 9);
        assert_eq!(
            node.check_state_block(&BlockRef::from_bytes(&stranger[0]).unwrap(), 7, &roots),
            Err(Error::UnknownParent)
        );
        // A branch is weighed without being kept: its work is what the
        // chain that holds it says, nothing is written, and headers
        // that do not follow, or that break a rule, are refused.
        let fresh = Chain::open(MemBackend::new(), 64, easy(), seed(), OnlyFrom(6)).unwrap();
        let genesis = fresh.tip().unwrap().hash();
        let mut weighed = fresh.weigh_from(&genesis).unwrap();
        fresh.weigh(&mut weighed, &headers[..4], NOW).unwrap();
        fresh.weigh(&mut weighed, &headers[4..], NOW).unwrap();
        assert_eq!(weighed.work(), ahead.known(&headers[5].hash()).unwrap().unwrap().work);
        assert_eq!(weighed.last().hash(), headers[5].hash());
        assert_eq!(fresh.best_header().unwrap().header.hash(), genesis);
        assert!(fresh.known(&headers[0].hash()).unwrap().is_none());
        let mut again = fresh.weigh_from(&genesis).unwrap();
        assert_eq!(fresh.weigh(&mut again, &headers[1..], NOW).err(), Some(Error::UnknownParent));
        let mut late = headers[0];
        late.timestamp = NOW + easy().max_future_drift + 1;
        assert!(matches!(fresh.weigh(&mut again, &[late], NOW), Err(Error::TimestampTooNew { .. })));
        assert_eq!(fresh.weigh_from(&headers[0].hash()).err(), Some(Error::UnknownParent));
        // A block whose header's work was left to a proof has it
        // looked at in full here: its own proof says nothing of it.
        let late = Chain::open(MemBackend::new(), 64, easy(), seed(), OnlyFrom(6)).unwrap();
        late.set_dataset(table());
        assert_eq!(late.accept_headers(&headers, NOW, true), (6, None));
        assert_eq!(late.known(&headers[5].hash()).unwrap().unwrap().status, Status::WorkPending);
        assert!(late.full_pow_heights.lock().unwrap().is_empty());
        assert_eq!(late.check_state_block(&view, 6, &roots), Ok(()));
        assert_eq!(*late.full_pow_heights.lock().unwrap(), [6]);
    }

    /// A node that stops while it is taking a state is, when it starts
    /// again, where it was: its headers, what it had received, and no
    /// state until it has gone on to the end.
    #[test]
    fn a_state_being_received_survives_a_restart() {
        let ahead = open(64);
        let blocks = crate::chain::apply::tests::grow_wide(&ahead, 12, 2500, 1);
        let headers = headers_of(&blocks);
        let node = open(64);
        assert_eq!(node.accept_headers(&headers, NOW, false), (12, None));
        let handed = hand_over(&ahead, 10);
        assert_eq!(handed.parts.len(), 4);
        node.begin_receiving(&headers[9], handed.next, &handed.parts, &handed.name_parts).unwrap();
        // Two of the four parts, and then it stops.
        for (index, outputs, commits) in &handed.outputs[..2] {
            node.put_part(*index, outputs, commits).unwrap();
        }
        let again = Chain::open(MemBackend::from_image(node.image()), 64, easy(), seed(), AcceptAllProofs).unwrap();
        again.set_dataset(table());
        // Receiving still, as of the same block; the headers are there.
        assert!(again.receiving());
        assert_eq!(again.receiving_as_of(), Some((10, headers[9].hash())));
        assert_eq!(again.best_header().unwrap().header, headers[11]);
        assert_eq!((again.tip().unwrap().height, again.whole().err()), (0, Some(Error::Receiving)));
        // Headers go on being taken.
        let more = headers_of(&grow(&ahead, 2, 2));
        assert_eq!(again.accept_headers(&more, NOW, false), (2, None));
        // What the parts' roots are is not kept: until they are had
        // again, nothing can be put and it cannot be finished.
        assert_eq!(again.missing_parts().err(), Some(Error::PartsMissing));
        let (index, outputs, commits) = &handed.outputs[2];
        assert_eq!(again.put_part(*index, outputs, commits), Err(Error::PartsMissing));
        assert_eq!(again.finish_receiving(&[]).err(), Some(Error::PartsMissing));
        assert!(again.receiving());
        // Begun again with the roots: only what it had not got is
        // wanted.
        again.begin_receiving(&headers[9], handed.next, &handed.parts, &handed.name_parts).unwrap();
        assert_eq!(again.missing_parts().unwrap().0, [handed.parts[2].0, handed.parts[3].0]);
        take(&again, &handed, &blocks[9]);
        assert_eq!((again.tip().unwrap(), again.state().root()), (headers[9], headers[9].state_root));
        // And opened once more it is a chain like any other.
        let whole = Chain::open(MemBackend::from_image(again.image()), 64, easy(), seed(), AcceptAllProofs).unwrap();
        assert!(!whole.receiving());
        assert_eq!(whole.tip().unwrap(), headers[9]);
        // A store that was receiving another network's chain is not
        // this one's.
        let other = crate::chain::params::ChainParams { genesis_timestamp: easy().genesis_timestamp + 1, ..easy() };
        let refused = Chain::open(MemBackend::from_image(node.image()), 64, other, seed(), AcceptAllProofs);
        assert_eq!(refused.err(), Some(Error::WrongGenesis));
    }
}
