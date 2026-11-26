# Work: what a node gives out, and what it takes back

A node makes a block in five steps, and two of them are not its own.

| Step | Who | What |
|---|---|---|
| 1 | node | Chooses transactions from its pool, takes from its state the paths of all they spend, and builds the block's body without its proof. |
| 2 | **a prover** | Proves the signatures of the transactions, and then the block. |
| 3 | node | Checks the proof, and builds the header. |
| 4 | **miners** | Find a nonce for the header. |
| 5 | node | Puts the block together, applies it, and tells its peers. |

Steps 2 and 4 are given out as *jobs*. A job says everything whoever
does it needs: a prover or a miner keeps no chain, asks the node
nothing more, and may be any program that reads the job and answers
it. The ones in this repository (`tabprover`, `tabminer`) are the
first; one that proves on other hardware, or stands between a node
and a pool's miners, speaks the same two formats.

This document is those formats. The code is `tabshared::job`
(`shared/src/job.rs`), which reads and writes both and which a program
in Rust may link; the node's side is `node/src/miner.rs` (`draft`,
`Draft::proven`, `Proven::block`).

**What is built, and what is not.** The formats, and the node's three
steps, are built and tested. The port they are served at (the requests,
held open until there is work) is not built yet: section 6 of
`docs/SPLIT.md` says what it is to be.

## What the node takes on trust: nothing

Whatever comes back from a job is checked as anything from outside is.

- A proof handed back is checked as the chain will check the block's
  (`Draft::proven`). One that is no proof of that block is refused, and
  so is one that would make the block larger than a block may be.
- A nonce handed back is taken only if it is for the header the node
  gave out, and its mix claims work that meets the target
  (`Proven::block`). Whether the work is as claimed is found when the
  node applies its own block, as it is of any block.
- Bytes that are not a job, or not an answer, are refused whole, and
  nothing of them is used. A length is never taken on trust for an
  allocation.

A prover, for its part, trusts its node: a job is not a proof of
anything. What a job reader does check is that the job is whole and
agrees with itself, so that proving it does not look for a path that
is not there.

## How large a block is

The node chooses a block's transactions, so how many signatures a
block made here checks is the node's setting (`--max-block-signatures`,
256 unless told otherwise). That default is what a machine with nothing
but its processor proves in good time. It is not a limit of anything
here: a node set higher gives out larger jobs, up to what the network's
proofs hold and what a block may be (2 MB).

What the main network's proofs hold is rows: a block's proof joins up
to 32 runs of 65,536 rows, an input a key signs for takes some 110 of
them, and an output some 8. So a block spends some 19,000 outputs at
the most, whatever its size, and the 32,768 signatures its proofs of
signatures have room for are not reached by inputs. Which a block of
ordinary payments reaches first, its rows or its 2 MB, is by what the
payments are: many inputs to an output, the rows.

Measured (2026-11-25, `a_full_block_is_begun_and_its_job_written`): of
13,000 payments in the pool, half of one input and half of two, each
making two outputs, a block took 10,810, which spend 17,310 outputs.
It was 1,851,376 bytes with 450,000 of them left for its proof, and
was full by its rows. Its job to prove was 66.6 MB. The node chose
its transactions in 74 ms, began the block in a second, wrote the job
in 0.1 s, and read it back in 0.3 s.

(Choosing took 189 seconds as the reference has it, asking of the
whole block again for each transaction tried, and copying every
signature to count them. `choose` now keeps what the block has taken
of its proof as it goes, `Level::filled_with`, and chooses the same
block.)

## A job to prove

Bytes (`application/octet-stream`). Numbers are little-endian; a
digest is 32 bytes; a list is its count as four bytes and then its
items.

| Bytes | What |
|---|---|
| 1 | The version: 1. |
| 32 | The program of the chain's step. A prover whose setup has another is of another network or another build, and refuses the job. |
| 236 | The header of the block before: `prev_hash` (32), `height` (4), `timestamp` (8), `body_commitment` (32), `state_root` (32), `statement` (32), `aux` (32), `mix` (32), `nonce` (32). The block to prove is at its height and one. |
| 1 | 0 where the chain begins, and the block is its first: nothing more of this row. 1 otherwise, and then: |
| 284 | What the chain's proof stated with the block before in (below). |
| 4 + n | The proof the block before carried: its length, and it. |
| 32 | The root of the outputs' tree, before the block. |
| 32 | The root of the names' tree, before the block. |
| 8 | The next position: the one the block's first output takes. |
| 8 | The subsidy: what the block may make, before its transactions' fees. |
| 4 + 1,384 each | The outputs the block spends, ascending by position, each once (below). |
| 32 + 1,312 | The leaf at the next position, and its path: 41 siblings, the lowest first. |
| 4 + each | The names the block touches, ascending by key, each once (below). |
| 4 + each | The transactions, in the block's order: each its length as four bytes, and the transaction as it is sent between nodes. |
| 4 + 8 each | The positions of the commitments of names past their time that the block sweeps. |
| 60 | The output that pays the block's maker, which is the block's first: key hash (32), amount (8), memo (20). |

An output spent, 1,384 bytes:

| Bytes | What |
|---|---|
| 8 | Its position. |
| 32, 20, 8, 4 | What the state keeps of it: commitment, memo, amount, and the height of the block that made it. Its leaf is the hash of these. |
| 1,312 | Its path in the outputs' tree: 41 siblings, the lowest first. |

The outputs spent are every input of every transaction, the commitment
every reveal of a name spends, and every position swept.

A name touched, 4,145 bytes and its record:

| Bytes | What |
|---|---|
| 16 | Its key. |
| 32 | Its leaf, as the tree has it before the block. |
| 4,096 | Its path in the names' tree: 128 siblings, the lowest first. |
| 1 | 0 if the name is not taken. 1 if it is, and then its record as the tree holds it: the name's length (1), the name, its owner (32), its value (32), its memo (32). |

The names touched are those of every reveal and every update the
transactions carry.

What the chain's proof states, 284 bytes, in this order: `program`
(32), `height` (4), `root` (32), `next` (8), `inputs` (32), `outputs`
(32), `sum_in` (16), `sum_out` (16), `era` (4), `left` (4), `names`
(32), `tip` (32), `ops` (32), `table` (4), `grows` (4).

A reader refuses a job (`ProveJob::from_bytes`) that is of another
version, is cut short, has anything after it, names a position or a
key twice, has a path that does not lead to the root the job names,
spends a position it has no path of, or has a name's path its
transactions do not touch.

### What proving it takes

`ProveJob::prove` is all of it: the proof before is read
(`Setup::carried`, or where a chain begins `Setup::beginning`), the
signatures are proven (`Setup::sign`), and then the block
(`Setup::block`).

- **The proving setup**, which a prover makes or loads when it starts,
  and which takes time: so a prover stays up, and is not started for
  each job.
- **The seed text of the proof of work**, which is in the program. A
  block's proof shows the work of the header before, from the text,
  and makes the 128 items that work read as it does so. A table of
  the proof of work (1 GB, and twice as much each year, to 32 GB) is
  not needed, and saves nothing that can be measured: four blocks
  proven with one took 25.7 to 25.9 seconds each, and the same four
  without 24.5 to 25.7 (measured 2026-11-25, on the dev network, whose
  items cost what the main network's do).
- **Memory**: `docs/MEMORY.md`.

### What comes back

The proof, as the bytes that go in the block's body; or that there is
none to make (`Proof::Refused`: the job is of another setup, or the
block is not one a chain takes); or that it was given up when told to.

## A job to find a nonce

JSON, since it is three fields and a script may want to read it.

```json
{ "height": 812345, "hash": "…64 hex digits…", "target": "…64 hex digits…" }
```

| Field | What |
|---|---|
| `height` | The header's height: which table of the proof of work its work is of. |
| `hash` | The hash the work is of: the header's, without its mix and its nonce. It names the job. |
| `target` | What the work's result is to meet, as the 32 bytes of a header's target. |

What is found:

```json
{ "hash": "…", "nonce": "…64 hex digits…", "mix": "…64 hex digits…" }
```

- **The nonce is 32 bytes, and whoever hashes chooses all of them.**
  Nothing in the chain's rules reads a nonce but to hash it. The search
  here counts in the first eight; the other twenty-four are a miner's
  to set as it likes, at random or as whatever it hashes for tells it,
  so that no two of its machines try the same. The node hands out no
  ranges.
- **A miner needs the table** of the proof of work for the job's
  height, which it makes from the seed text. A hash costs three
  compressions with the table and some 32,000 without.
- **A job goes stale** when the chain has another last block. Its
  header's time is the time the node made it, and is not under the
  block's proof: so the port, when it is built, can give the job out
  again with the time renewed, and needs no new proof to do so.
- There are no shares here, no accounts and no payouts. A node serves
  one owner's machines. A pool is another program, which takes jobs
  from a node as a miner does and deals them out as it sees fit.

## What is tested

- A job to prove is read back from its bytes, with and without a proof
  before; every part of one, one with something after it, one of
  another version and one with a path that leads elsewhere are refused
  (`tabshared::job`).
- A node begins a block of transactions, gives out the job, takes back
  a proof and a nonce, and the chain takes the block; a job that lacks
  a path or misstates an output is refused; a proof too large, and a
  nonce for another header, are refused (`a_block_is_made_in_steps`).
- A chain that checks proofs refuses whatever bytes are handed back
  for one (`a_proof_that_is_none_is_refused`).
- Every block the node's tests prove is proven from its job's bytes
  (`mine_with` writes the job and reads it back before proving it).
- A full block, of 2 MB of ordinary payments, is chosen, begun, its
  job written and read back, and with a stand-in for its proof the
  chain takes it (`a_full_block_is_begun_and_its_job_written`). It is
  not proven: the chain's proofs go unchecked there.
