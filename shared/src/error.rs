//! The crate's one error type.
//!
//! Every fallible function here returns [`Error`], so a failure passes up
//! through any number of layers with `?` and is never wrapped or
//! converted on the way. It is `Copy` and holds no heap: a variant carries
//! at most a few words that say where the fault is.
//!
//! This module depends on nothing in the crate, and everything may depend
//! on it.
//!
//! # What an error is not
//!
//! Which error a block, a transaction or a proof is refused with is not
//! part of consensus: only that it is refused. Two implementations check
//! the same things in different orders and name the first fault they
//! meet, so the same invalid bytes may be refused under two names. Tests
//! shared between implementations compare acceptance, not errors.
//!
//! Failures of the operating system (a file, memory, the random source)
//! are reported by `std::io::Result` where nothing else can fail. Where a
//! function both reads the store and checks what it is given (applying a
//! block to the state), a failure of the store is [`Error::Io`]: the
//! kind of the failure, without its message.

use core::fmt;

use crate::hash::Digest;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The bytes are not the encoding of the thing named.
    Malformed(&'static str),

    // -- Keys and signing
    /// All of a key's one-time leaves have been used.
    KeyExhausted,
    /// The input at this index belongs to a different key.
    WrongKey(usize),

    // -- Block bodies
    /// The same position is spent twice by inputs.
    DuplicateInput(u64),
    /// An input position is not below the tree's capacity.
    InputOutOfRange(u64),
    /// A position spent by a reveal or a sweep is repeated or also spent.
    DuplicateSpend(u64),
    /// A position spent by a reveal or a sweep is not below the tree's
    /// capacity.
    SpendOutOfRange(u64),
    /// More name operations of a kind than its cap.
    TooManyOps { kind: &'static str, cap: usize },

    // -- Spend policies
    /// A witness does not match its condition's kind, or is missing.
    PolicyWitness,
    /// Fewer valid signatures than the threshold, a key not listed, a key
    /// listed twice, or a wrong leaf index for a rebindable signature.
    PolicySignatures,
    /// The preimage is not the hash lock's.
    PolicyPreimage,
    /// A timelock has not passed.
    PolicyLocked,
    /// The state number does not exceed the output's.
    PolicyState,
    /// The covered outputs are not the covenant's.
    PolicyCovenant,
    /// The covered outputs run past the transaction's outputs.
    PolicyCovered,

    // -- Proofs
    /// A proof's parts do not number or measure what its statement and
    /// parameters say they must.
    ProofShape,
    /// A witness ground before a challenge of the proof's commit phase is
    /// wrong.
    Grinding,
    /// A witness ground before a FRI challenge, or before the queries, is
    /// wrong.
    FriGrinding,
    /// The constraints do not hold at the out-of-domain point.
    ConstraintIdentity,
    /// The tables' lookup totals do not cancel.
    LookupSum,
    /// An opening of a table's trace tree is not the tree's.
    InvalidTraceOpening { table: usize },
    /// An opening of a table's auxiliary tree is not the tree's.
    InvalidAuxOpening { table: usize },
    /// An opening of a table's preprocessed tree is not the tree's.
    InvalidPreprocessedOpening { table: usize },
    /// An opening of a table's quotient tree is not the tree's.
    InvalidQuotientOpening { table: usize },
    /// An opening of a FRI round's tree is not the tree's.
    InvalidFriOpening { round: usize },
    /// A query's fold does not match the value the next round opens.
    FoldMismatch { query: usize, round: usize },
    /// A query's last fold is not the final value.
    FinalMismatch { query: usize },
    /// The prover was told to stop.
    Cancelled,

    // -- The verifier machine's programs, run on a witness
    /// The assertion at this instruction does not hold.
    VmAssertion(usize),
    /// An instruction reads a word nothing has written.
    VmUninitialized { pc: usize, addr: u32 },
    /// An instruction writes a word already written.
    VmDoubleWrite { pc: usize, addr: u32 },
    /// A hashing instruction reads a word that is not a base-field value.
    VmNotScalar { pc: usize, addr: u32 },
    /// The witness has fewer values than the program takes.
    VmInputs,
    /// A sibling taken from the witness at this instruction is not a
    /// base-field value.
    VmNotScalarInput(usize),
    /// An absorb at this instruction with no sponge to continue, or a
    /// compress before any hash.
    VmHashOrder(usize),

    // -- The state
    /// A position that is spent holds no unspent output.
    NoSuchOutput(u64),
    /// A name to register is registered already.
    NameTaken,
    /// A name to update is not registered.
    NoSuchName,
    /// The state after a block is not the one its header commits to.
    StateRoot,
    /// A part of a state received is not the part its root says, or the
    /// parts' roots are not the state's.
    PartRoot,
    /// A state received is not whole yet.
    PartsMissing,
    /// The block to undo is older than the window of blocks whose
    /// records are kept.
    NoUndoRecord,

    // -- The chain
    /// The header's parent is not known: it is to be fetched first.
    UnknownParent,
    /// The header's parent is a block found invalid.
    InvalidParent,
    /// The block is one this node can never connect, though it may be
    /// valid: its branch leaves the chain below what can be undone.
    SetAside,
    /// The header is one found invalid before.
    KnownInvalid,
    /// The header's height is not its parent's and one.
    BadHeight { expected: u32, got: u32 },
    /// The header is above the last block the chain can have.
    ChainEnded,
    /// The header's time is not after the median of the blocks before.
    TimestampTooOld { median: u64, got: u64 },
    /// The header's time is further ahead of the clock than is allowed.
    TimestampTooNew { limit: u64, got: u64 },
    /// The header's work does not meet its target, or is not its work.
    BadProofOfWork,
    /// The store holds the chain of another genesis.
    WrongGenesis,
    /// The body is not the one the header commits to.
    BadBodyCommitment,
    /// The block is larger than a block may be: its size.
    TooLarge(usize),
    /// The outputs a block makes do not sum to what it spends and its
    /// subsidy.
    Supply,
    /// A block makes an output of no coins: an output of none is a
    /// commitment to a name, which is made as one.
    EmptyOutput,
    /// The block's proof is not accepted.
    BadProof,
    /// The body of a block of the branch is not kept.
    MissingBody,
    /// A block kept before this one on its branch came with a proof
    /// that is not accepted: that copy of it is dropped, and this block
    /// waits for another. The block is named by the first half of its
    /// id ([`Error::id_half`]), which is all an error has room for and
    /// enough to tell one block of a node's side branches from another.
    BadProofBefore([u8; 16]),
    /// Leaves offered for a block are not the ones its header's
    /// auxiliary bytes commit to, or its header is not known.
    AuxMismatch,
    /// An update of a name is not signed by the name's owner.
    NameOwner,
    /// A reveal or a sweep spends an output that is no commit: its
    /// position.
    NotACommit(u64),
    /// A commit is revealed outside its window, or swept before it is
    /// past: the height it was made at.
    CommitAge(u32),
    /// The state is being received from other nodes: there is none to
    /// read or to join a block to yet.
    Receiving,

    // -- The network
    /// A setting a node cannot run with: which, and why.
    Setting(&'static str),

    /// The operating system failed a read or a write of the store, or
    /// what was read is not what was written (`InvalidData`). Only the
    /// kind is kept: this type holds no heap.
    Io(std::io::ErrorKind),
}

/// A failure of the store's files, carried up through code that also
/// checks: its kind is kept, its message is not.
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error::Io(e.kind())
    }
}

impl Error {
    /// The half of a block's id that [`Error::BadProofBefore`] names it by.
    pub fn id_half(id: &Digest) -> [u8; 16] {
        id[..16].try_into().unwrap()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Malformed(what) => write!(f, "malformed {what}"),
            Error::KeyExhausted => f.write_str("XMSS key exhausted: all one-time leaves have been used"),
            Error::WrongKey(i) => write!(f, "input {i} is not owned by the signing key"),
            Error::DuplicateInput(p) => write!(f, "input position {p} appears twice"),
            Error::InputOutOfRange(p) => write!(f, "input position {p} exceeds the state tree"),
            Error::DuplicateSpend(p) => write!(f, "position {p} is spent twice"),
            Error::SpendOutOfRange(p) => write!(f, "spent position {p} exceeds the state tree"),
            Error::TooManyOps { kind, cap } => write!(f, "more than {cap} {kind} operations"),
            Error::PolicyWitness => f.write_str("witness does not fit the condition"),
            Error::PolicySignatures => f.write_str("threshold signatures do not verify"),
            Error::PolicyPreimage => f.write_str("wrong hash lock preimage"),
            Error::PolicyLocked => f.write_str("timelock has not passed"),
            Error::PolicyState => f.write_str("state number does not exceed the output's"),
            Error::PolicyCovenant => f.write_str("covered outputs are not the covenant's"),
            Error::PolicyCovered => f.write_str("covered outputs run past the transaction's"),
            Error::ProofShape => f.write_str("proof has the wrong shape"),
            Error::Grinding => f.write_str("wrong proof of work before a challenge"),
            Error::FriGrinding => f.write_str("wrong proof of work before a fri challenge"),
            Error::ConstraintIdentity => f.write_str("constraints do not hold at the out-of-domain point"),
            Error::LookupSum => f.write_str("lookup totals of the tables do not cancel"),
            Error::InvalidTraceOpening { table } => write!(f, "table {table}: invalid trace opening"),
            Error::InvalidAuxOpening { table } => write!(f, "table {table}: invalid auxiliary opening"),
            Error::InvalidPreprocessedOpening { table } => write!(f, "table {table}: invalid preprocessed opening"),
            Error::InvalidQuotientOpening { table } => write!(f, "table {table}: invalid quotient opening"),
            Error::InvalidFriOpening { round } => write!(f, "fri round {round}: invalid merkle opening"),
            Error::FoldMismatch { query, round } => {
                write!(f, "fri query {query} round {round}: fold does not match opened value")
            }
            Error::FinalMismatch { query } => write!(f, "fri query {query}: last fold does not match final value"),
            Error::Cancelled => f.write_str("proving was cancelled"),
            Error::VmAssertion(pc) => write!(f, "instruction {pc}: assertion failed"),
            Error::VmUninitialized { pc, addr } => write!(f, "instruction {pc}: word {addr} read before it is written"),
            Error::VmDoubleWrite { pc, addr } => write!(f, "instruction {pc}: word {addr} written twice"),
            Error::VmNotScalar { pc, addr } => write!(f, "instruction {pc}: word {addr} is not a scalar"),
            Error::VmInputs => f.write_str("the program takes more witness values than were given"),
            Error::VmNotScalarInput(pc) => write!(f, "instruction {pc}: a witness sibling is not a scalar"),
            Error::VmHashOrder(pc) => write!(f, "instruction {pc}: no hash to continue"),
            Error::NoSuchOutput(p) => write!(f, "position {p} holds no unspent output"),
            Error::NameTaken => f.write_str("the name is already registered"),
            Error::NoSuchName => f.write_str("the name is not registered"),
            Error::StateRoot => f.write_str("the state after the block is not its header's"),
            Error::PartRoot => f.write_str("a part of the state received is not what its root says"),
            Error::PartsMissing => f.write_str("the state received is not whole yet"),
            Error::NoUndoRecord => f.write_str("no record is kept to undo the block with"),
            Error::UnknownParent => f.write_str("the header's parent is not known"),
            Error::InvalidParent => f.write_str("the header's parent is invalid"),
            Error::SetAside => f.write_str("the block's branch cannot be connected here"),
            Error::KnownInvalid => f.write_str("the header was found invalid before"),
            Error::BadHeight { expected, got } => write!(f, "height {got} where {expected} follows the parent"),
            Error::ChainEnded => f.write_str("the chain has ended"),
            Error::TimestampTooOld { median, got } => write!(f, "time {got} is not after the median {median}"),
            Error::TimestampTooNew { limit, got } => write!(f, "time {got} is past the limit {limit}"),
            Error::BadProofOfWork => f.write_str("the proof of work does not hold"),
            Error::WrongGenesis => f.write_str("the store holds another network's chain"),
            Error::BadBodyCommitment => f.write_str("the body is not the header's"),
            Error::TooLarge(size) => write!(f, "a block of {size} bytes is too large"),
            Error::Supply => f.write_str("the block makes coins it may not"),
            Error::EmptyOutput => f.write_str("the block makes an output of no coins"),
            Error::BadProof => f.write_str("the block's proof is not accepted"),
            Error::MissingBody => f.write_str("a block of the branch has no body kept"),
            Error::BadProofBefore(_) => {
                f.write_str("a block before it on its branch came with a proof that is not accepted")
            }
            Error::AuxMismatch => f.write_str("the leaves are not the header's"),
            Error::NameOwner => f.write_str("the name's owner did not sign the update"),
            Error::NotACommit(p) => write!(f, "position {p} holds no commit"),
            Error::CommitAge(made) => write!(f, "a commit made at height {made} is not of an age for this"),
            Error::Receiving => f.write_str("the state is being received, and is not whole yet"),
            Error::Setting(what) => write!(f, "a setting cannot be run with: {what}"),
            Error::Io(kind) => write!(f, "the store failed: {kind}"),
        }
    }
}

impl std::error::Error for Error {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every error says what it is, in words of its own, and is small
    /// enough to hand up by value.
    #[test]
    fn every_error_has_its_own_words() {
        let all = [
            Error::Malformed("block"),
            Error::KeyExhausted,
            Error::WrongKey(3),
            Error::DuplicateInput(7),
            Error::InputOutOfRange(7),
            Error::DuplicateSpend(7),
            Error::SpendOutOfRange(7),
            Error::TooManyOps { kind: "sweep", cap: 16 },
            Error::PolicyWitness,
            Error::PolicySignatures,
            Error::PolicyPreimage,
            Error::PolicyLocked,
            Error::PolicyState,
            Error::PolicyCovenant,
            Error::PolicyCovered,
            Error::ProofShape,
            Error::Grinding,
            Error::FriGrinding,
            Error::ConstraintIdentity,
            Error::LookupSum,
            Error::InvalidTraceOpening { table: 1 },
            Error::InvalidAuxOpening { table: 1 },
            Error::InvalidPreprocessedOpening { table: 1 },
            Error::InvalidQuotientOpening { table: 1 },
            Error::InvalidFriOpening { round: 2 },
            Error::FoldMismatch { query: 4, round: 2 },
            Error::FinalMismatch { query: 4 },
            Error::Cancelled,
            Error::VmAssertion(9),
            Error::VmUninitialized { pc: 9, addr: 5 },
            Error::VmDoubleWrite { pc: 9, addr: 5 },
            Error::VmNotScalar { pc: 9, addr: 5 },
            Error::VmInputs,
            Error::VmNotScalarInput(9),
            Error::VmHashOrder(9),
            Error::NoSuchOutput(7),
            Error::NameTaken,
            Error::NoSuchName,
            Error::StateRoot,
            Error::PartRoot,
            Error::PartsMissing,
            Error::NoUndoRecord,
            Error::UnknownParent,
            Error::InvalidParent,
            Error::SetAside,
            Error::KnownInvalid,
            Error::BadHeight { expected: 2, got: 3 },
            Error::ChainEnded,
            Error::TimestampTooOld { median: 5, got: 4 },
            Error::TimestampTooNew { limit: 5, got: 6 },
            Error::BadProofOfWork,
            Error::WrongGenesis,
            Error::BadBodyCommitment,
            Error::TooLarge(9),
            Error::Supply,
            Error::EmptyOutput,
            Error::BadProof,
            Error::MissingBody,
            Error::BadProofBefore([0; 16]),
            Error::AuxMismatch,
            Error::NameOwner,
            Error::NotACommit(4),
            Error::CommitAge(4),
            Error::Io(std::io::ErrorKind::InvalidData),
        ];
        let words: Vec<String> = all.iter().map(|e| e.to_string()).collect();
        for (i, w) in words.iter().enumerate() {
            assert!(!w.is_empty());
            assert!(words[..i].iter().all(|o| o != w), "{w}");
        }
        assert_eq!(Error::Malformed("block").to_string(), "malformed block");
        assert_eq!(Error::TooManyOps { kind: "sweep", cap: 16 }.to_string(), "more than 16 sweep operations");
        assert!(Error::FoldMismatch { query: 4, round: 2 }.to_string().contains("query 4 round 2"));
        assert!(size_of::<Error>() <= 32);
        let boxed: Box<dyn std::error::Error> = Box::new(Error::Cancelled);
        assert_eq!(boxed.to_string(), "proving was cancelled");
    }
}
