//! Tests of the pool, against a state that is three tables in memory;
//! and what it costs to take the transactions of full blocks.

use std::time::Instant;

use super::*;
use crate::output::{Output, commitment};
use crate::transaction::UnsignedTransaction;
use crate::xmss::{PublicKey, SecretKey};

/// A state: what the pool asks of one, from tables.
#[derive(Default)]
struct Fake {
    outputs: HashMap<u64, (Commitment, u32, bool)>,
    commits: HashMap<u64, (Digest, u32)>,
    names: HashMap<Key, Record>,
}

impl Ledger for Fake {
    fn output(&self, position: u64) -> Result<Option<(Commitment, u32, bool)>, Error> {
        Ok(self.outputs.get(&position).copied())
    }

    fn commit(&self, position: u64) -> Result<Option<(Digest, u32)>, Error> {
        Ok(self.commits.get(&position).copied())
    }

    fn name(&self, key: Key) -> Result<Option<Record>, Error> {
        Ok(self.names.get(&key).copied())
    }

    fn commits_up_to(&self, height: u32) -> Result<Vec<u64>, Error> {
        let mut found: Vec<u64> = self.commits.iter().filter(|(_, c)| c.1 <= height).map(|(p, _)| *p).collect();
        found.sort_unstable();
        Ok(found)
    }
}

impl Fake {
    /// An unspent output of `amount` to key `tag`, at `position`.
    fn fund(&mut self, position: u64, tag: u32, amount: u64) {
        self.outputs.insert(position, (commitment(&pk(tag), amount), 0, true));
    }
}

fn key(tag: u32) -> SecretKey {
    let mut seed = [0u8; 32];
    seed[..4].copy_from_slice(&tag.to_le_bytes());
    SecretKey::generate(&seed)
}

fn pk(tag: u32) -> PublicKey {
    key(tag).public_key()
}

fn d(n: u32) -> Digest {
    core::array::from_fn(|i| ((n >> (8 * (i % 4))) as u8).wrapping_add(i as u8))
}

/// A transaction of key `tag` spending an output of `amount` at each of
/// `positions`, all but `fee` paid to key `to`.
fn spend_at(tag: u32, positions: &[u64], amount: u64, fee: u64, to: u32) -> Vec<u8> {
    let mut k = key(tag);
    let inputs = positions.iter().map(|_| (k.public_key(), amount)).collect();
    let total = amount * positions.len() as u64;
    let tx = UnsignedTransaction::new(inputs, vec![Output::new(&pk(to), total - fee)])
        .at(positions)
        .sign(|_, _, m| k.sign(m))
        .unwrap();
    tx.to_bytes()
}

/// A transaction spending `amount` from key `tag` to key 100 with `fee`,
/// the output of key `tag` being at position `tag - 1`.
fn spend(tag: u32, amount: u64, fee: u64) -> Vec<u8> {
    spend_at(tag, &[u64::from(tag) - 1], amount, fee, 100)
}

fn none() -> (HashMap<Commitment, Vec<u64>>, HashMap<Commitment, u64>) {
    (HashMap::new(), HashMap::new())
}

/// A node that makes no blocks holds whole the most recent of what
/// its pool knows of, and of the older ones as many as fit the room it
/// gives them, which are its own: those its secret draws lowest,
/// whichever came first. Of the rest it keeps what they spend and pay. What is only known
/// of still keeps another from spending the same, counts towards what
/// the pool holds, and goes when a block spends what it spends; it is
/// not given to whoever asks, not put in a block, and not kept from
/// one run to the next. A node that makes blocks holds everything.
#[test]
fn of_what_is_known_some_is_held_whole() {
    let mut state = Fake::default();
    let txs: Vec<Vec<u8>> = (1..=40u32)
        .map(|tag| {
            state.fund(u64::from(tag) - 1, tag, 100_000_000);
            spend(tag, 100_000_000, 1_000_000 + u64::from(tag))
        })
        .collect();
    let size = txs[0].len();
    // The four most recent, and of the older: none; room for half; all.
    for room in [0usize, 18, usize::MAX] {
        let policy = Policy::NONE.holding(4 * size, room.saturating_mul(size));
        let mut pool = Mempool::with_policy(1 << 30, policy);
        let ids: Vec<Digest> = txs.iter().map(|tx| pool.insert(tx, &state, 1, 10).unwrap()).collect();
        // All are known, and count as before.
        assert_eq!((pool.len(), pool.bytes()), (40, 40 * size));
        let whole: Vec<bool> = ids.iter().map(|id| pool.entry(id).unwrap().whole()).collect();
        // The last four are whole, whatever the room.
        assert!(whole[36..].iter().all(|w| *w), "{room}");
        let older = whole[..36].iter().filter(|w| **w).count();
        assert_eq!(older, room.min(36), "{room}");
        assert_eq!((pool.whole(), pool.held()), (4 + older, (4 + older) * size));
        // Which of the older, where they are not all: those of the
        // lowest draws, and no other.
        if room == 18 {
            let draws =
                |is: bool| ids[..36].iter().zip(&whole).filter(move |(_, w)| **w == is).map(|(id, _)| pool.draw(id));
            assert!(draws(true).max() < draws(false).min());
            assert_eq!((pool.older.len(), pool.older_bytes), (18, 18 * size));
        }
        // What is whole is given and what is not is not; either way it
        // is known, with what it is and pays.
        for (id, is) in ids.iter().zip(&whole) {
            let e = pool.entry(id).unwrap();
            assert_eq!((e.bytes().is_some(), e.tx().is_some(), pool.get(id).is_some()), (*is, *is, *is));
            assert_eq!((e.size(), e.spent().len(), pool.contains(id)), (size, 1, true));
        }
        // Another that spends the same is refused as paying too little
        // to take its place, known whole or not; and takes it, paying
        // enough.
        let (first, tag) = (ids[0], 1u32);
        assert!(matches!(
            pool.insert(&spend(tag, 100_000_000, 1_000_000), &state, 1, 11),
            Err(Reject::ReplacementFee { .. })
        ));
        let better = pool.insert(&spend(tag, 100_000_000, 90_000_000), &state, 1, 11).unwrap();
        assert!(!pool.contains(&first) && pool.entry(&better).unwrap().whole());
        // A block is made of what is whole.
        let chosen = pool.select(&state, 1, 1, 0, |_| true);
        assert_eq!(chosen.len(), pool.whole(), "{room}");
        // Kept from one run to the next: what is whole.
        let mut again = Mempool::with_policy(1 << 30, Policy::NONE.holding_all());
        assert_eq!(again.load(&pool.saved(), &state, 1, 12), pool.whole());
        // A block spends what the second spent: it goes, whole or not,
        // and the rest stay.
        state.outputs.get_mut(&1).unwrap().2 = false;
        let (moved, created) = none();
        let (gone, back) = pool.revalidate(&state, 2, &moved, &created, 13).unwrap();
        assert_eq!((gone, back, pool.contains(&ids[1]), pool.len()), (1, 0, false, 39));
        state.outputs.get_mut(&1).unwrap().2 = true;
        // The counts are those of what is there.
        let held: usize = pool.entries().filter(|e| e.whole()).map(Entry::size).sum();
        assert_eq!((pool.held(), pool.whole()), (held, pool.entries().filter(|e| e.whole()).count()));
        for id in pool.ids() {
            pool.remove(&id);
        }
        assert_eq!((pool.len(), pool.bytes(), pool.held(), pool.whole()), (0, 0, 0, 0));
        assert_eq!((pool.older.len(), pool.older_bytes, pool.recent_bytes), (0, 0, 0));
    }
    // Two nodes hold different ones: each its own. And a node holds
    // the same ones in whatever order they came: so that what it holds
    // is no more of what came first, when there is no room for all.
    let share = |seed: u8, backwards: bool| {
        let mut pool = Mempool::with_policy(1 << 30, Policy::NONE.holding(0, 18 * size));
        pool.secret = [seed; 32];
        let mut order: Vec<&Vec<u8>> = txs.iter().collect();
        if backwards {
            order.reverse();
        }
        for tx in order {
            pool.insert(tx, &state, 1, 10).unwrap();
        }
        let mut whole: Vec<Digest> = pool.entries().filter(|e| e.whole()).map(|e| e.txid).collect();
        whole.sort_unstable();
        assert_eq!((whole.len(), pool.held()), (18, 18 * size));
        whole
    };
    assert_ne!(share(1, false), share(2, false));
    assert_eq!(share(1, false), share(1, true));
    // One too large for the older ones' room is not held, and lets
    // none of them go for it; and a seed, with no room, holds none.
    let large = spend_at(41, &[100, 101, 102], 100_000_000, 3_000_000, 100);
    for position in 100..103 {
        state.fund(position, 41, 100_000_000);
    }
    let mut pool = Mempool::with_policy(1 << 30, Policy::NONE.holding(0, 2 * size));
    for tx in txs.iter().chain([&large]) {
        pool.insert(tx, &state, 1, 10).unwrap();
    }
    assert!(large.len() > 2 * size);
    assert_eq!((pool.len(), pool.whole(), pool.held()), (41, 2, 2 * size));
    let mut seed = Mempool::with_policy(1 << 30, Policy::NONE.holding(4 * size, 0));
    for tx in &txs {
        seed.insert(tx, &state, 1, 10).unwrap();
    }
    assert_eq!((seed.len(), seed.whole(), seed.older.len()), (40, 4, 0));
}

/// A pool knows of so many transactions and no more, whatever their
/// bytes: with as many as it may know of it is full, and takes what
/// pays more than its lowest and drops that, as a pool full by its
/// bytes does. One that takes another's place is not one more.
#[test]
fn a_pool_knows_of_so_many_and_no_more() {
    let mut state = Fake::default();
    for tag in 1..=8 {
        state.fund(u64::from(tag) - 1, tag, 10_000_000);
    }
    assert_eq!(Mempool::new(1 << 30).most(), DEFAULT_COUNT);
    // Room for any number by their bytes; three, by their number; and
    // nothing spared.
    let mut pool = Mempool::with_policy(1 << 30, Policy { protect_bytes: 0, ..Policy::NONE }).knowing(3);
    let a = pool.insert(&spend(1, 10_000_000, 1000), &state, 1, 0).unwrap();
    let b = pool.insert(&spend(2, 10_000_000, 2000), &state, 1, 0).unwrap();
    let c = pool.insert(&spend(3, 10_000_000, 3000), &state, 1, 0).unwrap();
    assert_eq!((pool.len(), pool.admission_fee(0)), (3, 0));
    // What pays less than the lowest is not worth dropping it for.
    assert_eq!(pool.insert(&spend(4, 10_000_000, 500), &state, 1, 0), Err(Reject::Full));
    // What takes the place of one of them is no more than there were.
    let b2 = pool.insert(&spend(2, 10_000_000, 500_000), &state, 1, 0).unwrap();
    assert!(!pool.contains(&b) && pool.contains(&b2) && pool.len() == 3 && pool.admission_fee(0) == 0);
    // What pays more than the lowest takes its place, and the minimum
    // is up past what that one paid.
    let e = pool.insert(&spend(5, 10_000_000, 5000), &state, 1, 0).unwrap();
    assert!(!pool.contains(&a) && pool.contains(&c) && pool.contains(&e) && pool.len() == 3);
    assert!(pool.admission_fee(0) > 0);
    assert!(matches!(pool.insert(&spend(6, 10_000_000, 1), &state, 1, 0), Err(Reject::FeeTooLow { .. })));
    // And down again with time, and sooner for a pool that is not
    // half full: of its number, as of its bytes.
    let asked = pool.admission_fee(HALF_LIFE_SECS / 2);
    pool.remove(&c);
    pool.remove(&e);
    assert!(pool.admission_fee(HALF_LIFE_SECS / 2) < asked);

    // The oldest are spared, and no more of them than half of what
    // the pool may know of, whatever their bytes.
    let mut pool = Mempool::with_policy(1 << 30, Policy::NONE).knowing(4);
    let ids: Vec<Digest> = (1..=4u32)
        .map(|tag| pool.insert(&spend(tag, 10_000_000, 1000 * u64::from(tag)), &state, 1, 0).unwrap())
        .collect();
    let spared: Vec<bool> = ids.iter().map(|id| pool.is_protected(id)).collect();
    assert_eq!(spared, [true, true, false, false]);
    // (The third pays least of those not spared, and goes.)
    let more = pool.insert(&spend(5, 10_000_000, 50_000), &state, 1, 0).unwrap();
    assert!(pool.contains(&ids[0]) && pool.contains(&ids[1]) && !pool.contains(&ids[2]) && pool.contains(&more));
    // A pool that may know of none takes none.
    let mut none = Mempool::with_policy(1 << 30, Policy::NONE).knowing(0);
    assert_eq!(none.insert(&spend(7, 10_000_000, 5000), &state, 1, 0), Err(Reject::Full));
}

/// Two unspent outputs with one commitment (one key hash, one amount)
/// are two outputs: spending one does not conflict with spending the
/// other, a transaction may spend both, and a conflict is a second
/// spend of the same position.
#[test]
fn outputs_sharing_a_commitment_are_told_apart() {
    let mut state = Fake::default();
    state.fund(0, 1, 500);
    state.fund(1, 1, 500);
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    // (Paid to a key by its first position: the id covers neither
    // positions nor signatures, so these differ only by output.)
    pool.insert(&spend_at(1, &[0], 500, 5, 100), &state, 1, 0).unwrap();
    pool.insert(&spend_at(1, &[1], 500, 5, 101), &state, 1, 0).unwrap();
    assert_eq!(pool.len(), 2);
    // A second spend of position 0 conflicts with the first.
    let again = spend_at(1, &[0], 500, 6, 100);
    assert!(matches!(pool.insert(&again, &state, 1, 0), Err(Reject::ReplacementFee { .. })));
    // Both at once is no duplicate; the same position twice is.
    let mut other = Mempool::with_policy(1 << 20, Policy::NONE);
    other.insert(&spend_at(1, &[0, 1], 500, 5, 100), &state, 1, 0).unwrap();
    assert_eq!(other.insert(&spend_at(1, &[1, 1], 500, 5, 101), &state, 1, 0), Err(Reject::Malformed));
}

/// A reorganization that takes an output away: the transaction
/// spending it leaves the pool for the shelf. It comes back when the
/// output is where it was again, and not for the same output made
/// somewhere else: what was signed is of the place.
#[test]
fn shelved_transactions_come_back_with_their_outputs() {
    let mut state = Fake::default();
    state.fund(0, 1, 1000);
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    let id = pool.insert(&spend(1, 1000, 5), &state, 1, 0).unwrap();
    // The block that made it is replaced: the output is gone from
    // position 0.
    let made = state.outputs.remove(&0).unwrap();
    let (moved, created) = none();
    assert_eq!(pool.revalidate(&state, 1, &moved, &created, 0), Ok((1, 0)));
    assert!(pool.is_empty());
    // The new branch makes it again at position 2: another output, to
    // what was signed.
    state.outputs.insert(2, made);
    let elsewhere = HashMap::from([(made.0, vec![2u64])]);
    assert_eq!(pool.revalidate(&state, 1, &elsewhere, &created, 0), Ok((0, 0)));
    assert!(pool.is_empty() && pool.take_returned().is_empty());
    // And at position 0: the same.
    state.outputs.insert(0, made);
    assert_eq!(pool.revalidate(&state, 1, &moved, &created, 0), Ok((0, 1)));
    // What comes back is said, once, for whoever is to tell of it.
    assert_eq!(pool.take_returned(), [(id, pool.entry(&id).unwrap().size())]);
    assert!(pool.take_returned().is_empty());
    let back: Vec<u64> = pool.get(&id).unwrap().spent_positions().collect();
    assert_eq!(back, [0]);
    assert!(pool.get(&id).unwrap().verify_signatures());
    assert_eq!(pool.get(&id).unwrap().txid(), id);
}

/// What a transaction pays to take another's place is looked at before
/// its signatures: one that pays too little is turned away for that,
/// whatever its signatures are. And what is set aside when its outputs
/// go is no more, by its size, than a part of what the pool may hold.
#[test]
fn a_replacement_s_fee_comes_before_its_signatures_and_the_shelf_is_bounded() {
    let mut state = Fake::default();
    state.fund(0, 1, 5_000_000);
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    pool.insert(&spend_at(1, &[0], 5_000_000, 50, 100), &state, 1, 0).unwrap();
    // Another spend of the same output, paying less, its signature
    // spoiled: refused for what it pays.
    let mut other = spend_at(1, &[0], 5_000_000, 10, 101);
    let at = other.len() - 40;
    other[at] ^= 1;
    assert!(TransactionRef::from_bytes(&other).is_ok_and(|tx| !tx.verify_signatures()));
    assert!(matches!(pool.insert(&other, &state, 1, 0), Err(Reject::ReplacementFee { .. })));
    // (Paying enough, it is refused for its signature.)
    let mut other = spend_at(1, &[0], 5_000_000, 4_000_000, 101);
    let at = other.len() - 40;
    other[at] ^= 1;
    assert_eq!(pool.insert(&other, &state, 1, 0), Err(Reject::BadSignature));

    // Twelve transactions, in a pool that holds twelve of them and no
    // more: their outputs go, and a quarter of that is set aside.
    let mut state = Fake::default();
    for tag in 1..=12 {
        state.fund(u64::from(tag) - 1, tag, 100_000);
    }
    let size = spend(1, 100_000, 10).len();
    let mut pool = Mempool::with_policy(12 * size, Policy::NONE);
    for tag in 1..=12 {
        pool.insert(&spend(tag, 100_000, 10), &state, 1, 0).unwrap();
    }
    state.outputs.clear();
    let (moved, created) = none();
    assert_eq!(pool.revalidate(&state, 1, &moved, &created, 0), Ok((12, 0)));
    assert!(pool.is_empty());
    assert_eq!(pool.shelf.len(), 3);
}

/// Why the pool refuses a transaction is said in words, each its own.
#[test]
fn a_refusal_says_why() {
    let all = [
        Reject::Known,
        Reject::Expired,
        Reject::NoInputs,
        Reject::TooLarge(9),
        Reject::NegativeFee,
        Reject::FeeTooLow { min: 7 },
        Reject::Dust { min: 5 },
        Reject::Malformed,
        Reject::BadSignature,
        Reject::Policy(Error::Malformed("policy")),
        Reject::TooManyRows(70_000),
        Reject::UnknownInput(3),
        Reject::ReplacementFee { min: 11 },
        Reject::Full,
        Reject::Name(NameReject::NoCommit),
        Reject::NameConflict,
        Reject::Store(Error::Receiving),
    ];
    let said: Vec<String> = all.iter().map(Reject::to_string).collect();
    let mut once = said.clone();
    once.sort();
    once.dedup();
    assert_eq!(once.len(), all.len());
    assert!(said.iter().all(|why| !why.is_empty() && !why.ends_with('.')));
    assert_eq!(said[3], "9 bytes exceeds the transaction size limit");
    assert_eq!(said[10], "a policy's input of 70000 rows is more than a run of a proof holds");
    assert_eq!(said[11], "spends an output that is not unspent (position 3)");
    // And why the registry refuses what a transaction does to a name.
    let names = [
        NameReject::NoCommit,
        NameReject::Expired(4),
        NameReject::Registered,
        NameReject::NotRegistered,
        NameReject::BadOwner,
    ];
    let said: Vec<String> = names.iter().map(NameReject::to_string).collect();
    assert_eq!((said[0].as_str(), said[1].as_str()), ("no such commit", "the commit at height 4 is past its window"));
    assert!(said.iter().enumerate().all(|(i, why)| said[..i].iter().all(|other| other != why)));
}

/// A transaction that has waited its time is dropped, and its id is
/// refused for as long again.
#[test]
fn transactions_expire_and_stay_refused() {
    let mut state = Fake::default();
    state.fund(0, 1, 1000);
    let mut pool = Mempool::with_policy(1 << 20, Policy { expiry_secs: 100, ..Policy::NONE });
    let tx = spend(1, 1000, 5);
    let id = pool.insert(&tx, &state, 1, 1000).unwrap();
    assert!(pool.expire(1050).is_empty());
    assert_eq!(pool.expire(1100), [id]);
    assert!(pool.is_empty());
    assert_eq!(pool.expired().count(), 1);
    assert_eq!(pool.insert(&tx, &state, 1, 1150), Err(Reject::Expired));
    assert_eq!(pool.insert(&tx, &state, 1, 1200), Ok(id));
    // And what the pool forgets with time.
    pool.expire(1201);
    assert_eq!(pool.expired().count(), 0);
}

/// A pool is kept from one run to the next: its transactions with
/// their ages, what it remembers of those that waited too long, and
/// what it has seen confirm. One whose output the chain no longer has
/// is not taken again; and what is no saved pool is nothing.
#[test]
fn a_pool_is_kept_and_taken_again() {
    let mut state = Fake::default();
    state.fund(0, 1, 1000);
    state.fund(1, 2, 2000);
    state.fund(2, 3, 3000);
    let policy = Policy { expiry_secs: 100, ..Policy::NONE };
    let mut pool = Mempool::with_policy(1 << 20, policy);
    let gone = pool.insert(&spend_at(3, &[2], 3000, 7, 9), &state, 1, 900).unwrap();
    assert_eq!(pool.expire(1000), [gone]);
    let first = pool.insert(&spend(1, 1000, 5), &state, 1, 1000).unwrap();
    let second = pool.insert(&spend_at(2, &[1], 2000, 9, 9), &state, 1, 1010).unwrap();
    pool.remember_confirmed(50, 600, 990);
    let saved = pool.saved();
    // Taken again, by a pool that has nothing: all of it.
    let mut again = Mempool::with_policy(1 << 20, policy);
    assert_eq!(again.load(&saved, &state, 1, 1020), 2);
    assert_eq!((again.len(), again.bytes()), (pool.len(), pool.bytes()));
    assert_eq!(again.entry(&first).unwrap().arrived, 1000);
    assert_eq!(again.entry(&second).unwrap().arrived, 1010);
    assert_eq!(again.expired().collect::<Vec<_>>(), pool.expired().collect::<Vec<_>>());
    assert_eq!(again.confirmed().collect::<Vec<_>>(), [&(50, 600, 990)]);
    assert_eq!(again.saved(), saved);
    // By one whose chain has since spent what the first spends: the
    // other only.
    state.outputs.remove(&0);
    let mut later = Mempool::with_policy(1 << 20, policy);
    assert_eq!(later.load(&saved, &state, 1, 1020), 1);
    assert!(later.contains(&second) && !later.contains(&first));
    // Cut short, what is whole of it is taken; and anything else is
    // no pool at all.
    let mut short = Mempool::with_policy(1 << 20, policy);
    assert_eq!(short.load(&saved[..saved.len() / 2], &state, 1, 1020), 0);
    assert_eq!(short.load(b"not a pool", &state, 1, 1020), 0);
    assert_eq!(short.load(&[], &state, 1, 1020), 0);
}

/// A full pool takes what pays more than its lowest and drops that; what
/// it then asks rises past what it dropped, and falls back with time.
/// The oldest are spared.
#[test]
fn the_admission_minimum_rises_decays_and_spares_the_oldest() {
    let mut state = Fake::default();
    for tag in 1..=8 {
        state.fund(u64::from(tag) - 1, tag, 100_000);
    }
    let size = spend(1, 100_000, 1000).len();
    // Room for three, and nothing spared.
    let mut pool = Mempool::with_policy(3 * size + size / 2, Policy { protect_bytes: 0, ..Policy::NONE });
    let a = pool.insert(&spend(1, 100_000, 1000), &state, 1, 0).unwrap();
    let b = pool.insert(&spend(2, 100_000, 2000), &state, 1, 0).unwrap();
    let c = pool.insert(&spend(3, 100_000, 3000), &state, 1, 0).unwrap();
    assert_eq!(pool.admission_fee(0), 0);
    // What pays less than the lowest is not worth dropping it for.
    assert_eq!(pool.insert(&spend(4, 100_000, 500), &state, 1, 0), Err(Reject::Full));
    let e = pool.insert(&spend(5, 100_000, 5000), &state, 1, 0).unwrap();
    assert!(!pool.contains(&a) && pool.contains(&b) && pool.contains(&c) && pool.contains(&e));
    // The minimum is up: past what the dropped one paid.
    let asked = pool.admission_fee(0);
    assert!(asked > 0 && u128::from(asked) * size as u128 > 1000, "{asked}");
    assert!(matches!(pool.insert(&spend(6, 100_000, 1), &state, 1, 0), Err(Reject::FeeTooLow { .. })));
    // And down again, with time.
    assert!(pool.admission_fee(HALF_LIFE_SECS) < asked);
    assert_eq!(pool.admission_fee(1000 * HALF_LIFE_SECS), 0);

    // With the oldest spared: the first stays though it pays the least.
    let mut pool = Mempool::with_policy(3 * size + size / 2, Policy { protect_bytes: size, ..Policy::NONE });
    let a = pool.insert(&spend(1, 100_000, 1), &state, 1, 0).unwrap();
    let b = pool.insert(&spend(2, 100_000, 2000), &state, 1, 0).unwrap();
    let c = pool.insert(&spend(3, 100_000, 3000), &state, 1, 0).unwrap();
    assert!(pool.is_protected(&a) && !pool.is_protected(&b));
    let e = pool.insert(&spend(5, 100_000, 5000), &state, 1, 0).unwrap();
    assert!(pool.contains(&a) && !pool.contains(&b) && pool.contains(&c) && pool.contains(&e));
}

/// A block's reserve goes to the longest-waiting, whatever they pay;
/// the rest by what they pay a byte, the most first.
#[test]
fn the_aged_reserve_goes_to_the_longest_waiting() {
    let mut state = Fake::default();
    for tag in 1..=3 {
        state.fund(u64::from(tag) - 1, tag, 100_000);
    }
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    let old = pool.insert(&spend(1, 100_000, 10), &state, 1, 1).unwrap();
    let low = pool.insert(&spend(2, 100_000, 5000), &state, 1, 2).unwrap();
    let high = pool.insert(&spend(3, 100_000, 9000), &state, 1, 3).unwrap();
    let size = pool.entry(&old).unwrap().size();
    let ids = |chosen: Vec<TransactionRef<'_>>| chosen.iter().map(|tx| tx.txid()).collect::<Vec<_>>();
    assert_eq!(ids(pool.select(&state, 2, 0, size, |_| true)), [old, high, low]);
    assert_eq!(ids(pool.select(&state, 2, 0, 0, |_| true)), [high, low, old]);
    // Only while they fit.
    assert_eq!(ids(pool.select(&state, 2, 0, size, |chosen| chosen.len() <= 2)), [old, high]);
    // One that no block has room for keeps out none of the others: not
    // the best paying, and not the longest waiting.
    for unfit in [high, old] {
        let fits = |chosen: &[TransactionRef<'_>]| chosen.iter().all(|tx| tx.txid() != unfit);
        let chosen = ids(pool.select(&state, 2, 0, size, fits));
        assert_eq!(chosen.len(), 2, "without {unfit:?}");
        assert!(!chosen.contains(&unfit) && chosen.contains(&low));
    }
    assert_eq!(pool.reserve_wait(0), Some(1));
    // With no reserve nothing is promised to what waits.
    let none = Mempool::with_policy(1 << 20, Policy { reserve_percent: 0, ..Policy::NONE });
    assert_eq!(none.reserve_wait(0), None);
}

/// An operator's policy is what it sets, and what follows from it: the
/// dust limit from the floor, what is kept from eviction from the
/// reserve; and what it does not set is the default.
#[test]
fn an_operators_policy_is_what_it_sets() {
    assert_eq!(Policy::set(MIN_FEE_PER_UNIT, 12, 14, RESERVE_PERCENT), Policy::MAINNET);
    let set = Policy::set(50, 6, 3, 25);
    assert_eq!((set.min_fee_per_unit, set.dust), (50, 50));
    assert_eq!((set.half_life_secs, set.expiry_secs, set.reserve_percent), (6 * 3600, 3 * 86400, 25));
    assert_eq!(set.protect_bytes, PROTECT_BYTES / 10 * 25);
    assert_eq!(Policy::set(0, 1, 1, 0).protect_bytes, 0);
    // The floor is what the pool refuses below.
    let mut state = Fake::default();
    state.fund(0, 1, 1_000_000);
    let mut pool = Mempool::with_policy(1 << 20, set);
    // (One input and one output: a weight of four.)
    let below = spend(1, 1_000_000, 50 * 4 - 1);
    assert_eq!(pool.insert(&below, &state, 1, 0), Err(Reject::FeeTooLow { min: 200 }));
    assert!(pool.insert(&spend(1, 1_000_000, 50 * 4), &state, 1, 0).is_ok());
}

/// A fee is by weight: an output weighs three inputs, so that what
/// leaves fewer outputs than it spends is the cheap transaction; and an
/// operator may weigh them otherwise.
#[test]
fn a_fee_is_by_weight() {
    let w = Weights::DEFAULT;
    assert_eq!((w.of(2, 2), w.of(500, 1), w.of(1, 500)), (8, 503, 1501));
    let policy = Policy::MAINNET;
    assert_eq!(policy.min_fee(2, 2), 8 * MIN_FEE_PER_UNIT);
    assert_eq!((policy.dust, policy.max_tx_size), (MIN_FEE_PER_UNIT, MAX_TX_SIZE));
    let mut state = Fake::default();
    state.fund(0, 1, 10_000_000);
    state.fund(1, 1, 10_000_000);
    // Two inputs into one output weigh five; one input, four.
    let two = spend_at(1, &[0, 1], 10_000_000, 0, 100);
    assert_eq!(w.weigh(&TransactionRef::from_bytes(&two).unwrap()), 5);
    let mut pool = Mempool::new(1 << 20);
    let short = spend_at(1, &[0, 1], 10_000_000, 5 * MIN_FEE_PER_UNIT - 1, 100);
    assert_eq!(pool.insert(&short, &state, 1, 0), Err(Reject::FeeTooLow { min: 5 * MIN_FEE_PER_UNIT }));
    let id = pool.insert(&spend_at(1, &[0, 1], 10_000_000, 5 * MIN_FEE_PER_UNIT, 100), &state, 1, 0).unwrap();
    assert_eq!(pool.entry(&id).unwrap().weight, 5);
    // Other weights, another floor's worth.
    let even = Policy::MAINNET.with_weights(Weights { output: 1, ..w });
    assert_eq!((even.min_fee(2, 2), even.dust), (4 * MIN_FEE_PER_UNIT, MIN_FEE_PER_UNIT));
}

/// What is not a spend the state allows is refused, each for its reason;
/// one that pays enough more replaces what it conflicts with; and the
/// pool follows the chain.
#[test]
fn pool_validates_replaces_and_revalidates() {
    let mut state = Fake::default();
    for tag in 1..=6 {
        state.fund(u64::from(tag) - 1, tag, 1_000_000);
    }
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    assert_eq!(pool.insert(b"not a transaction", &state, 1, 0), Err(Reject::Malformed));
    assert_eq!(pool.insert(&vec![0u8; MAX_TX_SIZE + 1], &state, 1, 0), Err(Reject::TooLarge(MAX_TX_SIZE + 1)));
    // The size is the operator's to set; under it, the fee decides.
    let mut small = Mempool::with_policy(1 << 20, Policy::NONE.with_max_tx_size(100));
    assert_eq!(small.insert(&[0u8; 101], &state, 1, 0), Err(Reject::TooLarge(101)));
    assert_eq!(small.insert(&[0u8; 100], &state, 1, 0), Err(Reject::Malformed));
    // Outputs of more than the inputs.
    let mut k = key(1);
    let over = UnsignedTransaction::new(vec![(k.public_key(), 1_000_000)], vec![Output::new(&pk(100), 2_000_000)])
        .sign(|_, _, m| k.sign(m))
        .unwrap();
    assert_eq!(pool.insert(&over.to_bytes(), &state, 1, 0), Err(Reject::NegativeFee));
    // An output that is not there, one of another amount, one spent.
    assert_eq!(pool.insert(&spend(50, 1_000_000, 5), &state, 1, 0), Err(Reject::UnknownInput(49)));
    assert_eq!(pool.insert(&spend(1, 2_000_000, 5), &state, 1, 0), Err(Reject::UnknownInput(0)));
    state.outputs.get_mut(&5).unwrap().2 = false;
    assert_eq!(pool.insert(&spend(6, 1_000_000, 5), &state, 1, 0), Err(Reject::UnknownInput(5)));
    // Signed by a key that is not the output's.
    let mut other = key(2);
    let forged = UnsignedTransaction::new(vec![(pk(1), 1_000_000)], vec![Output::new(&pk(100), 999_000)])
        .sign(|_, _, m| other.sign(m))
        .unwrap();
    assert_eq!(pool.insert(&forged.to_bytes(), &state, 1, 0), Err(Reject::BadSignature));
    assert!(pool.is_empty());

    // What the main network's policy asks besides.
    let mut strict = Mempool::new(1 << 20);
    assert!(matches!(strict.insert(&spend(1, 1_000_000, 0), &state, 1, 0), Err(Reject::FeeTooLow { .. })));
    assert_eq!(strict.insert(&spend(1, 1_000_000, 999_999), &state, 1, 0), Err(Reject::Dust { min: DUST }));

    // Taken once; and replaced by what pays enough more.
    let first = spend(1, 1_000_000, 100);
    let id = pool.insert(&first, &state, 1, 0).unwrap();
    assert_eq!(pool.insert(&first, &state, 1, 0), Err(Reject::Known));
    let weight = Weights::DEFAULT.weigh(&TransactionRef::from_bytes(&first).unwrap());
    let min = 100 + REPLACEMENT_FEE_PER_UNIT * weight;
    assert_eq!(pool.insert(&spend(1, 1_000_000, min - 1), &state, 1, 0), Err(Reject::ReplacementFee { min }));
    let second = pool.insert(&spend(1, 1_000_000, min), &state, 1, 0).unwrap();
    assert!(!pool.contains(&id) && pool.contains(&second));
    assert_eq!((pool.len(), pool.ids()), (1, vec![second]));

    // Its input spent by a block that makes its output: it has confirmed.
    let paid = pool.get(&second).unwrap().outputs().get(0).commitment;
    state.outputs.get_mut(&0).unwrap().2 = false;
    let (moved, _) = none();
    let created = HashMap::from([(paid, 600u64)]);
    assert_eq!(pool.revalidate(&state, 2, &moved, &created, 700), Ok((1, 0)));
    assert!(pool.is_empty() && pool.bytes() == 0);
    assert_eq!(pool.confirmed().count(), 1);
    // That block undone: it is back.
    state.outputs.get_mut(&0).unwrap().2 = true;
    let (moved, created) = none();
    assert_eq!(pool.revalidate(&state, 1, &moved, &created, 700), Ok((0, 1)));
    assert!(pool.contains(&second));
}

/// A reveal is pooled for the commit it names, while the name is free
/// and the commit not past its time; a name is one transaction's; and a
/// block takes a reveal only in its window.
#[test]
fn name_operations_are_checked_claimed_and_selected() {
    let mut state = Fake::default();
    state.fund(0, 1, 1_000_000);
    state.fund(1, 2, 1_000_000);
    let record = Record::new(b"alice", d(10), d(20), d(30)).unwrap();
    let salt = d(40);
    let hash = commit_hash(&record.name.hash(), &salt, &record.owner);
    state.commits.insert(50, (hash, 10));
    let reveal = |tag: u32, salt: Digest, commit: u64| {
        let mut k = key(tag);
        let ops = vec![NameOp::Reveal { record, salt, commit }];
        let outputs = vec![Output::new(&pk(100), 999_000)];
        let tx = UnsignedTransaction::with_ops(vec![(k.public_key(), 1_000_000)], outputs, ops)
            .at(&[u64::from(tag) - 1])
            .sign(|_, _, m| k.sign(m))
            .unwrap();
        tx.to_bytes()
    };
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    assert_eq!(pool.insert(&reveal(1, d(41), 50), &state, 20, 0), Err(Reject::Name(NameReject::NoCommit)));
    assert_eq!(pool.insert(&reveal(1, salt, 51), &state, 20, 0), Err(Reject::Name(NameReject::NoCommit)));
    let past = 10 + MAX_REVEAL + 1;
    assert_eq!(pool.insert(&reveal(1, salt, 50), &state, past, 0), Err(Reject::Name(NameReject::Expired(10))));
    let id = pool.insert(&reveal(1, salt, 50), &state, 20, 0).unwrap();
    assert_eq!(pool.entry(&id).unwrap().claims[..], [Claim::Name(record.key()), Claim::Commit(50)]);
    // The name and the commit are that transaction's.
    assert_eq!(pool.insert(&reveal(2, salt, 50), &state, 20, 0), Err(Reject::NameConflict));
    // A block takes it once its commit has waited.
    assert!(pool.select(&state, 15, 12, 0, |_| true).is_empty());
    assert_eq!(pool.select(&state, 22, 12, 0, |_| true).len(), 1);
    // What may be swept: commits past their time.
    assert!(Mempool::sweeps(&state, 100).is_empty());
    assert_eq!(Mempool::sweeps(&state, past), [50]);
    // The name registered by another: the reveal leaves the pool.
    state.names.insert(record.key(), record);
    let (moved, created) = none();
    assert_eq!(pool.revalidate(&state, 23, &moved, &created, 0), Ok((1, 0)));
    assert!(pool.is_empty());
    assert_eq!(pool.insert(&reveal(2, salt, 50), &state, 23, 0), Err(Reject::Name(NameReject::Registered)));
}

/// The estimate is the lowest rate at which nearly all confirmed in
/// time; and there is none until enough have been seen.
#[test]
fn estimates_follow_what_confirmed() {
    let mut pool = Mempool::with_policy(1 << 20, Policy::NONE);
    assert_eq!(pool.estimate(TARGET_BLOCK, 1000), None);
    for _ in 0..30 {
        pool.remember_confirmed(50, 100, 1000);
    }
    assert_eq!(pool.estimate(TARGET_BLOCK, 1000), Some(50));
    // A lower rate that did not make it in time is not suggested.
    for _ in 0..30 {
        pool.remember_confirmed(20, 5000, 1000);
    }
    assert_eq!(pool.estimate(TARGET_BLOCK, 1000), Some(50));
    // Given longer, it did.
    assert_eq!(pool.estimate(TARGET_DAY, 1000), Some(20));
    // An empty pool asks only its minimum.
    assert_eq!(pool.suggest(TARGET_BLOCK, 5000, 1000), 0);
}

/// What the pool costs, for the transactions of full blocks: a block of
/// the main network holds some 10,900 of them (two and a half inputs and
/// as many outputs each), so a node sees about 18 a second and, with
/// what it refuses, perhaps 40.
/// `cargo test --release --lib mempool::tests::throughput -- --ignored --nocapture`
/// (`TABMINER_MEMPOOL_TXS` sets how many are made, 2,000 unless given.)
#[test]
#[ignore = "a benchmark: run with --release"]
fn throughput() {
    /// What a node sees a second with full blocks, the refused included.
    const SEEN: f64 = 40.0;
    let n: usize = std::env::var("TABMINER_MEMPOOL_TXS").ok().and_then(|s| s.parse().ok()).unwrap_or(2000);
    let policy = Policy::MAINNET;
    let mut state = Fake::default();
    let to = pk(u32::MAX);
    // Transactions of two or three inputs and three or two outputs, each
    // of a key of its own, paying from twice to fifty times the floor;
    // and for every tenth another, signed by a key that is not its
    // outputs'.
    let t = Instant::now();
    let mut txs: Vec<Vec<u8>> = Vec::with_capacity(n);
    let mut forged: Vec<Vec<u8>> = Vec::new();
    let made = |state: &mut Fake, i: usize, signer: u32| {
        let k = key(i as u32 + 1);
        let mut signer = key(signer);
        let (ins, outs) = (2 + i % 2, 3 - i % 2);
        let amount = 1_000_000_000u64;
        let positions: Vec<u64> = (0..ins).map(|j| (4 * i + j) as u64).collect();
        for p in &positions {
            state.outputs.insert(*p, (commitment(&k.public_key(), amount), 0, true));
        }
        let fee = policy.min_fee(ins, outs) * (2 + i as u64 % 49);
        let each = (amount * ins as u64 - fee) / outs as u64;
        let outputs = (0..outs).map(|_| Output::new(&to, each)).collect();
        let tx = UnsignedTransaction::new(vec![(k.public_key(), amount); ins], outputs)
            .at(&positions)
            .sign(|_, _, m| signer.sign(m))
            .unwrap();
        tx.to_bytes()
    };
    for i in 0..n {
        txs.push(made(&mut state, i, i as u32 + 1));
    }
    for i in (0..n).step_by(10) {
        forged.push(made(&mut state, n + i, 1));
    }
    let bytes: usize = txs.iter().map(Vec::len).sum();
    println!("\n  {n} transactions made in {:.1?}: {} bytes each on average", t.elapsed(), bytes / n);
    let line = |what: &str, count: usize, took: std::time::Duration| {
        let rate = count as f64 / took.as_secs_f64();
        println!(
            "  {what:<34} {rate:>10.0} a second ({:>7.1} us each): {:>6.0} times what is seen, {:.2}% of a core for it",
            took.as_secs_f64() * 1e6 / count as f64,
            rate / SEEN,
            100.0 * SEEN / rate
        );
    };

    // Taken: read, looked up, their signatures checked, and pooled.
    // (A pool that holds all it knows of, as a node that makes blocks does.)
    let mut pool = Mempool::with_policy(DEFAULT_CAPACITY, policy.holding_all());
    let t = Instant::now();
    for tx in &txs {
        pool.insert(tx, &state, 1, 0).unwrap();
    }
    line("taken", n, t.elapsed());
    assert_eq!((pool.len(), pool.bytes()), (n, bytes));
    // Refused: already there; spending what is not there; badly signed.
    let t = Instant::now();
    for tx in &txs {
        assert_eq!(pool.insert(tx, &state, 1, 0), Err(Reject::Known));
    }
    line("refused: already pooled", n, t.elapsed());
    let (nothing, mut empty) = (Fake::default(), Mempool::with_policy(DEFAULT_CAPACITY, policy));
    let t = Instant::now();
    for tx in &txs {
        assert!(matches!(empty.insert(tx, &nothing, 1, 0), Err(Reject::UnknownInput(_))));
    }
    line("refused: nothing to spend", n, t.elapsed());
    let t = Instant::now();
    for tx in &forged {
        assert_eq!(empty.insert(tx, &state, 1, 0), Err(Reject::BadSignature));
    }
    line("refused: badly signed", forged.len(), t.elapsed());

    // A pool with room for a quarter of them, given the least paying
    // first: all but the first quarter push another out.
    let mut order: Vec<&Vec<u8>> = txs.iter().collect();
    let paying = |tx: &Vec<u8>| {
        let tx = TransactionRef::from_bytes(tx).unwrap();
        rate(tx.balance() as u64, Weights::DEFAULT.weigh(&tx))
    };
    order.sort_by_key(|tx| paying(tx));
    let mut small = Mempool::with_policy(bytes / 4, Policy { protect_bytes: 0, ..policy });
    let t = Instant::now();
    let mut taken = 0;
    for tx in &order {
        taken += usize::from(small.insert(tx, &state, 1, 0).is_ok());
    }
    line("taken by a full pool", n, t.elapsed());
    println!("    ({taken} taken, {} held at the end; it asks {} a byte)", small.len(), small.admission_fee(0));

    // A block: a tenth of them confirmed, the pool looked over; and the
    // next block's chosen.
    let created: HashMap<Commitment, u64> = HashMap::new();
    let moved: HashMap<Commitment, Vec<u64>> = HashMap::new();
    for tx in txs.iter().step_by(10) {
        for p in TransactionRef::from_bytes(tx).unwrap().spent_positions() {
            state.outputs.get_mut(&p).unwrap().2 = false;
        }
    }
    let t = Instant::now();
    let (gone, back) = pool.revalidate(&state, 2, &moved, &created, 600).unwrap();
    let took = t.elapsed();
    println!("  after a block, a pool of {n} looked over in {took:.1?}: {gone} gone, {back} back");
    assert_eq!((gone, back), (n.div_ceil(10), 0));
    let t = Instant::now();
    let chosen = pool.select(&state, 2, 0, RESERVE_BYTES, |chosen| chosen.len() <= 10_878);
    println!("  a block's transactions chosen in {:.1?}: {} of {}", t.elapsed(), chosen.len(), pool.len());
    assert_eq!(chosen.len(), pool.len().min(10_878));
}

/// What the pool keeps of a transaction it does not hold whole: the
/// record, and its part of the tables beside it, in bytes asked of the
/// heap. As many transactions as fill the tables as full as the most a
/// pool knows of does (a table of hashes is as full at 25,000 as at
/// 200,000, eight times as many).
#[test]
#[ignore = "a count; run with --release --nocapture, and alone: it reads what the pool holds of the heap"]
fn what_a_record_weighs() {
    let n = 25_000u32;
    let mut state = Fake::default();
    for tag in 1..=n {
        state.fund(u64::from(tag) - 1, tag, 100_000_000);
    }
    let txs: Vec<Vec<u8>> =
        crate::parallel::par_map(n as usize, |i| spend(i as u32 + 1, 100_000_000, 1_000_001 + i as u64));
    let before = crate::heap::held(crate::heap::Part::Pool);
    let mut pool = Mempool::with_policy(1 << 30, Policy::NONE.holding(0, 0));
    for tx in &txs {
        pool.insert(tx, &state, 1, 10).unwrap();
    }
    let held = crate::heap::held(crate::heap::Part::Pool) - before;
    assert_eq!((pool.len(), pool.whole()), (n as usize, 0));
    println!(
        "{n} records of {} bytes each as transactions: {held} bytes of heap, {} a record ({} the record itself)",
        txs[0].len(),
        held / n as usize,
        std::mem::size_of::<Entry>()
    );
}
