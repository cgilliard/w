# Memory: what each module of `shared` asks for

What each module asks of the heap, and which program that is in:
the **prover** (making proofs), the **node** (checking them, and
keeping the chain), the **miner** (hashing) and the **wallet**.

Measured, not reckoned. How, and what the numbers are worth, is at the
end.

## The whole of it, by program

| Program | Heap that matters | Where it comes from |
|---|---|---|
| Prover | 4.4 GB at the most for a block of a reward alone; 8.2 GB for a block of 1 to 64 signatures (the reference's own measure) | `ntt`, `circuit`, `argument`, `pcs`, `merkle`: nine tenths of it |
| Node | A few megabytes for each block checked | `hidden`, `pcs`, `structure`, and what the page file writes from |
| Miner | The table of the proof of work: 1,074 MB now, twice as much each year, to 32 GB | `pow`, in one allocation |
| Wallet | Not measured | Its own tables, which are not in `shared` |

Neither the node nor the prover needs the table of the proof of work:
both make the few items they read from the seed text.

## Modules that use memory that matters

One block of a reward alone, at the main network's sizes. "Proving" is
what the module asks for while the prover makes the block's proof;
"checking" is what it asks for while the node checks the block and
applies it.

| Module | Used by | Proving: asked for | Proving: most at once | Checking: asked for |
|---|---|---|---|---|
| `argument` | prover, node | 8.4 GB | 816 MB | 0.2 MB |
| `pcs` | prover, node | 5.9 GB | 649 MB | 2.3 MB |
| `ntt` | prover | 5.5 GB | 2,049 MB | nothing |
| `circuit` | prover | 3.4 GB | 1,483 MB | nothing |
| `grand` | prover, node | 1.7 GB | 272 MB | 0.1 MB |
| `merkle` | prover, node | 1.4 GB | 530 MB | 0.3 MB |
| `machine` | prover | 645 MB | 196 MB | nothing |
| `recursion` | prover | 111 MB | 30 MB | nothing |
| `hidden` | prover, node | 81 MB | 48 MB | 4.8 MB |
| `proof` | prover | 72 MB | 32 MB | nothing |
| `reading` | prover | 63 MB | 17 MB | nothing |
| `parallel` | prover, node, miner | 42 MB | 2 MB | nothing |
| `segment` | prover | 41 MB | 3 MB | nothing |
| `work` | prover | 27 MB | 15 MB | nothing |
| `structure` | prover, node | 17 MB | 3 MB | 1.9 MB |
| `alg` | prover, node | 14 MB | 1 MB | 1.1 MB |
| `sym` | prover | 13 MB | 2 MB | nothing |
| `challenger` | prover, node | 2 MB | under 1 MB | under 0.1 MB |
| `codec` | all four | 1 MB | under 1 MB | 1.2 MB |
| `store` (the page file, the backend) | node, wallet | nothing | nothing | 2.6 MB |
| **All** | | **27.4 GB** | **4.4 GB** | **14.5 MB** |

- `ntt` holds the most at once, in few allocations: a codeword of
  1 GB, and what it is folded to.
- `circuit` and `machine` make most of the small allocations, over a
  million each: the witness's tables, made a row at a time, and the
  machine's values as a verifier is made into rows.
- The modules' "most at once" come to 6 GB between them, and the proof
  to 4.4 GB: they are not at their most at the same moment.
- The node has the code of `ntt`, `circuit`, `machine` and the others
  that say "nothing" under checking, and never asks for their memory.
- `segment` and `work` are small because this block has no
  transactions. With transactions `segment` makes a run's tables, and
  `wots`, `signature` and `signed` come into it. Not measured.
- Loading the setup, when the prover starts, is a proof of its own:
  11.7 GB asked for, the same modules in the same shares.

## Modules that use little, or none

Each under its own tests, which are small: so what these say is
whether a module asks for memory at all, and of what size, not how
much it will in a program.

### No heap at all

| Module | Used by |
|---|---|
| `blake3`, `hash`, `field` | all four |
| `sha256`, `random`, `u256`, `difficulty` | node, wallet; `difficulty` and `u256` the miner too |
| `keccak`, `mldsa`, `mlkem` | node, wallet (the message layer) |
| `store::crc32c`, `store::sparse` | node, wallet |
| `address`, `challenger` | a few bytes |

### A little, and for a moment

The most any of these held at once was 141 KB.

| Module | Used by | Most at once | What for |
|---|---|---|---|
| `msg` | node, wallet | 141 KB | a message being sealed or opened: a message is 64 KB at the most |
| `transaction` | node, wallet, prover | 78 KB | a transaction as bytes, and read back |
| `store::partial` | node, prover | 74 KB | the paths a block's proof takes from the state |
| `policy` | node, wallet, prover | 71 KB | a spending policy as bytes |
| `proofs` | node, wallet | 62 KB | a proof of payment as text |
| `registry` | node, prover | 53 KB | the names a block touches |
| `subnames` | node, wallet | 52 KB | a certificate |
| `bip39` | node, wallet | 32 KB | the word list, split for each phrase read |
| `onion` | node, wallet | 25 KB | a message's layers |
| `merkle` | prover, node | 23 KB | (under its own tests; see above for proving) |
| `xmss` | node, wallet, prover | 5 KB | a signature |
| `ledger`, `conditions`, `consensus`, `chacha20poly1305`, `codec`, `error`, `store::backend`, `terminal`, `logger` | | under 5 KB each | |

Two that are larger under their tests, by what the tests give them:
`store::blob` (2 MB: it is given 2 MB to keep) and `ntt` (2 MB: a
small codeword).

`bip39` asks 49,617 times in three tests: it splits the list of 2,048
words every time a phrase is read. It could keep the list split.

Not measured: `block`, `name`, `output`, `store::pagefile`,
`store::freemap`, and what is new in `shared` (`http`, `json`,
`options`, `fees`, `base64`, `listed`, `sym` under its own tests).

## What has been done about it

All of it is the prover's, and is in `shared`:

| | What | What it gives |
|---|---|---|
| `heap::pool` | The allocator keeps one part's blocks of a megabyte or more, and hands them out again | The block proves in about 19.5 s where it took about 31. A fixed size: 6.5 GB kept, always, for 4.4 GB used |
| `parallel` | The threads are begun once | 33,530 fewer threads begun for the block. About a second sooner, which is no more than one run differs from the next |
| Scratch of a thread's own | Three loops no longer make their scratch space for every item | Allocations of 4 KB to 1 MB from 136,307 (8.1 GB) to 25,462 (1.0 GB). No sooner |

`docs/SPLIT.md`, section 12, has those measures in full.

Not done:

- A larger block of the pool's that is idle, given for a smaller one:
  it would bring the 6.5 GB nearer the 4.4 GB.
- The 8.2 GB proof of a block of 1 to 64 signatures has tables of
  twice the size any other proof has. Were it made the size of the
  others, the most a prover holds would be under 6 GB; but that is a
  change to a circuit, and the setups made again.
- `bip39`'s list, kept split.

## How it was measured

In a copy of the reference, outside this repository, with the
allocator changed to put every allocation down to the innermost
function of the crate on the stack that asked for it. With the threads
standing and the scratch space of a thread's own, as `shared` has
them, and without the pool: so that what is counted is what is asked
for.

- One machine, six cores. The block is `main_network_block_memory` of
  the reference's tests: a block of a reward alone, proven and then
  taken by a chain.
- "Asked for" is every byte asked of the allocator, added up. "Most at
  once" is the most of a module's bytes that were held at one moment.
- Every allocation of 4 KB or more was counted. Of the smaller, one in
  sixteen was, and counted for sixteen: so the counts of small
  allocations are near, and not exact.
- The build that was measured is without link-time optimisation, which
  makes more small allocations than the usual build does. The bytes,
  which are nearly all large blocks, are the same.
- "Used by" is from what each program is to be built of, not measured.

### Something not explained

The first build for this, with link-time optimisation, stopped with an
illegal instruction in the middle of proving, in
`chain_proof::Plan::node`: the compiler had marked what follows a
hashing call there as never reached. The same source built without
link-time optimisation ran, and is what was measured. The cause was
not found. It may be the compiler, set off by the measuring; or
something in the code that is undefined and goes unnoticed otherwise.
It is to be looked into.
