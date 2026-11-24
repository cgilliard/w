# Splitting the reference into four programs

Status: **draft for review**. Nothing has been moved yet. This records
what was agreed in discussion, what the reference code says about each
boundary, and what is still open.

The reference is `tmp/v/tabminer`: one crate, one binary, about 95,000
lines, no dependencies, 648 tests. It builds cleanly in release mode.

Statements below are marked where they are not yet confirmed in the
code. Everything else was read in the reference.

## 1. The shape

```
                      UDP, as now
        other nodes <-------------> tabnode
                                     |  |
                    API port (HTTP)  |  |  work port (HTTP)
                  +------------------+  +------------------+
                  |                                         |
              tabwallet                          tabprover     tabminer
              (CLI; holds keys)                  (proves)      (hashes)
```

| Program | What it is | Started by |
|---|---|---|
| `tabnode` | The chain, the network, the pool. Builds every block. Serves the API port and the work port. | the script |
| `tabprover` | A worker. Connects to the node's work port, takes a proving job, returns a proof. | the script |
| `tabminer` | A worker. Connects to the node's work port, takes a header and a range of nonces, returns a nonce. | the script |
| `tabwallet` | A command-line program, and the one front end for every command. Holds the wallet file. Talks to the node's API port. | a person |

Decisions behind this:

- **The node builds blocks; the miner only hashes.** As with a stratum
  server, any number of hashing machines can be pointed at one node
  and hold nothing of value.
- **Workers connect to the node**, not the other way round. They need
  no ports of their own and no configuration beyond the node's
  address. What they are doing is asked of the node.
- **The wallet is always a client.** Nothing connects to it, so it has
  no port.
- **Node-to-node traffic is unchanged**: the reference's datagram
  transport, on the same port.

## 2. Repository layout

A Cargo workspace at the root, with five members:

```
Cargo.toml        workspace; the release profile lives here
shared/           tabshared: the shared library
node/             tabnode
prover/           tabprover
miner/            tabminer
wallet/           tabwallet
scripts/node.sh   starts and watches node, prover, miner
resources/        seed text, word list, proving setups
docs/
```

- All four binaries are built into `target/release/` at the root.
- Each binary depends on `tabshared` by path and on nothing else. "No
  dependencies" becomes "no dependencies from outside this
  repository".
- `[profile.release]` moves to the root `Cargo.toml` (Cargo ignores it
  in workspace members). `.gitignore` gains `/target`.
- `resources/` here lacks `setup-dev.bin` and `setup-mainnet.bin`,
  which the reference has in `tmp/v/resources/`. They need to be
  added.
- `scripts/tabminer.sh` (empty) is renamed `scripts/node.sh`.

The shared library exists (`shared/`), and holds `blake3` so far. The
workspace does not yet: each crate is built on its own for now.

## 3. Which module goes where

### `tabshared`, the shared library

One library to begin with. It can be divided later, once the real
dependencies between modules are known (the list this was drawn from
counted mentions in comments as well as uses).

| Group | Modules | Who uses it |
|---|---|---|
| Primitives | `blake3`, `sha256`, `keccak`, `chacha20poly1305`, `field`, `u256`, `hash`, `codec`, `random`, `parallel`, `heap`, `error` | all |
| Keys and signatures | `xmss`, `wots`, `mldsa`, `mlkem`, `address`, `bip39` | node, wallet |
| What a chain is made of | `block`, `header`, `transaction`, `output`, `ledger`, `name`, `registry`, `policy`, `conditions`, `difficulty`, `consensus`, `subnames`, `chain::params` | node, wallet, prover |
| Messages between wallets | `msg`, `onion` | node, wallet |
| Proof of work | `pow` | node, miner, prover |
| The proof system | `alg`, `argument`, `arith`, `challenger`, `circuit`, `grand`, `hidden`, `machine`, `merkle`, `ntt`, `pcs`, `proof`, `reading`, `recursion`, `segment`, `signature`, `signed`, `structure`, `work`, `block_proof`, `chain_proof`, `prover` | node (to verify), prover |
| Files | `store::{backend, pagefile, freemap, crc32c, blob, sparse, partial}` | node (its store), wallet (its file), prover (a job's witness) |
| Running a program | `logger`, the option parser of `configuration`, and new: `http`, `json` | all |

Two things to know about this:

- **Most of the proof system is shared, so `tabprover` itself is
  small.** The node verifies with the same modules the prover proves
  with. The prover binary is the proving setup, the job loop and
  little else. Link-time optimisation already drops the proving code
  from the node's binary.
- **A few shared constants move out of node-only modules.** The wallet
  uses the pool's fee rules (`mempool::{Policy, Weights,
  MIN_FEE_PER_UNIT, …}`) and `chain::params::COIN`. Those types go to
  `tabshared`; the pool stays in the node.

### `tabnode`

- `net`, `transport`, `chain` (less `params`), `mempool`
- `store::{state, trie, outputs, names, window, blocks, commits, receive}`
- From `miner.rs`: choosing a block's transactions (`choose`), what it
  pays (`reward_due`), building the body and header, and when not to
  mine (`HoldOff`)
- `prover::Witness::collect`, which reads the node's store
- From `console.rs`: the commands that need no wallet, as API handlers
- New: the API server, the work server, deriving reward keys from the
  mining phrase

### `tabprover`

- Making or loading the proving setup (`Setup::new`, `from_parts`)
- New: the job loop, decoding a job, reporting how long each part took
  (`parts_timed`)

### `tabminer`

- `miner::solve` (the search for a nonce) and `miner::fill_table`
- The table of the proof of work: making, keeping and growing it
  (`LazyDataset`, with `--pow-table` and `--prebuild-table`)
- New: the job loop

### `tabwallet`

- `wallet/*`, `proofs`
- From `console.rs`: the wallet's commands, parsing, the help text
- `terminal` (the prompt, recall, completion)
- The wallet's side of `net/sessions.rs` (`Participant`): see 7.3
- New: the client of the node's API

### What `main.rs` becomes

`main.rs` today starts everything and holds the threads that join the
parts: the wallet following the chain, the loop that makes blocks, the
prompt, the messages for the wallet. Each of those threads becomes one
side of a protocol below, and `main.rs` is divided among the four
programs' own `main.rs`.

## 4. The two ports

Both are served by one small HTTP implementation in `tabshared`, written
here like everything else.

| | API port | Work port |
|---|---|---|
| For | `tabwallet`, and other tools | `tabprover`, `tabminer` |
| Listens on | this machine only, unless told otherwise | this machine only, unless told otherwise |
| Secret | required | see open question 3 |
| Proposed default | TCP 3738 | TCP 3739 |

### What the HTTP is, and is not

- HTTP/1.1, `Content-Length` only. No chunked bodies, no compression,
  no redirects.
- Limits on the size of headers, the size of a body, and the number of
  open connections.
- JSON for anything a person or a script reads. Amounts are strings
  (they are 64 and 128 bits, more than a JSON number holds); hashes
  are hex.
- Raw bytes (`application/octet-stream`) for anything large or already
  encoded: a transaction, a proving job, a proof, a block's outputs.
- **Waiting is by a request held open.** A worker asks for a job and
  the node answers when there is one, or when the last block changes.
  The wallet waits for messages the same way.
- **No TLS.** On one machine it is not needed. From another machine,
  use an SSH tunnel or a proxy in front. The work port sent over an
  open network unprotected lets anyone feed a miner jobs: the
  documentation must say so.

### The secret

The node writes a random secret to `api.secret` in its data directory
when first started, readable by its owner alone. `tabwallet` reads the
file and sends the secret with each request. Another user of the same
machine cannot then stop the node or read its pool.

## 5. The API port

Paths are a first draft. Every one begins `/v1`.

### Commands that need no wallet

| Command today | Request |
|---|---|
| `status` | `GET /status` (the wallet adds its own total) |
| `supply` | `GET /supply` |
| `peers` | `GET /peers` |
| `fees` | `GET /fees` |
| `mempool` | `GET /mempool` |
| `leaves`, `set-leaf`, `set-leaf-value` | `GET /leaves`, `PUT /leaves/{index}` |
| `consensus` | `GET /consensus` |
| `relays` | `GET /relays` |
| `name NAME` | `GET /names/{name}` |
| `verify-proof FILE` | `POST /proofs/verify` |
| `quit` | `POST /stop` |
| new: `workers` | `GET /workers`: provers and miners connected, what each is doing, the hash rate each reports |
| new, replacing the wallet's `mining` | `GET /mining`: blocks won of late, and those of them undone |

### What the wallet needs of the chain

`wallet/follow.rs` reads the node's store directly today. These are
the reads it makes, as requests:

| What the wallet does | Request | Body |
|---|---|---|
| Where is the chain? | `GET /tip` | JSON |
| Is the block I last saw still in the chain? | `GET /headers/{height}` | JSON |
| The outputs a block made, and where they begin | `GET /blocks/{id}/outputs` | bytes |
| Is my output unspent, and how deep? | `GET /outputs/{position}` | JSON |
| Every unspent output (a wallet made again from its words) | `GET /outputs?from=&limit=` | bytes, a page at a time |
| The path that proves a payment | `GET /outputs/{position}/path?at={height}` | bytes |
| A name's record | `GET /names/{name}` | JSON |
| The pool's rules, for working out a fee | `GET /policy` | JSON |
| Pool a transaction | `POST /transactions` | bytes |
| Is my transaction still pooled? | `GET /transactions/{id}` | JSON |

The wallet's `Unspent` trait already stands between it and the store,
so this is a second implementation of that trait and a rewrite of
`follow`, not of the wallet.

Looking through every unspent output is the slow path, as it is today.
It is used when a wallet is made again from its words, or has been
away for longer than the node keeps blocks' bodies (1,008 blocks by
default, a week).

### The wallet's commands

These run in `tabwallet` against its own file, using the requests
above. None of them is a request to the node in itself.

| Needs only the wallet file | Needs the node too |
|---|---|
| `address`, `seed`, `password`, `outputs`, `txs`, `payments`, `subnames`, new: `mining-phrase` | `balance`, `send`, `send-file`, `receive`, `finalize`, `cancel`, `bump`, `resend`, `burn`, `burn-proof`, `payment-proof`, `names`, `name-commit`, `name-reveal`, `name-update`, `name-offer`, `name-transfer`, `subname …`, `scan` |

Every command also takes `--json`, to print its answer as JSON for
scripts.

## 6. The work port

### How a block is made

Today `miner::mine_with` does all of this in one call. It divides at
two points:

| Step | Who | What |
|---|---|---|
| 1 | node | Choose transactions from the pool. Derive the reward's key from the mining phrase. Collect the witness from the state. Build the body without its proof. |
| 2 | prover | Prove the signatures of the transactions, then the block. |
| 3 | node | Check the proof. Build the header. |
| 4 | miners | Find a nonce. |
| 5 | node | Put the block together, apply it, announce it. |

When the chain has a new last block, the node drops what is in
progress and begins again at step 1.

### A proving job

What `Setup::block` and `Setup::sign` take, sent as bytes:

- the header of the block before, and the proof that block carried
- the record the block starts from (the roots, the next position, the
  height)
- the witness: the paths in the state of everything the block spends
- the transactions, the sweeps, and the reward's output

The prover needs nothing of the chain beyond the job. It does need, at
startup, the proving setup and the table of the proof of work (a
block's proof includes a proof of the work of the block before). Both
take time to make ready, so a prover stays connected and is not
started for each job.

The witness has no encoding as bytes today. That is new code.

| Request | Does |
|---|---|
| `POST /prove/job` | Held open until there is a job. Answers with the job. |
| `GET /prove/wanted?job=` | Held open while the job is still wanted. Answers when it is not: the prover gives it up. |
| `POST /prove/done?job=` | The proof, or that it could not be made. With how long each part took. |

One job goes to one prover. A second prover connected waits its turn.
Dividing one proof among several provers is a later question (entry 19
of `NODE_ENHANCEMENTS.md`).

### A hashing job

| Request | Does |
|---|---|
| `POST /hash/job` | Held open until there is a job, or a newer one than the miner has. Answers with the hash of the header, the target, the height, and the nonces that miner is to try. The miner says here what hash rate it has. |
| `POST /hash/found?job=` | A nonce and its mix. |

- The nonce is 32 bytes, and the reference only counts in the first
  eight. The node gives each miner its own prefix in the rest, so no
  two search the same nonces. *To confirm: that nothing in the rules
  reads the nonce's other bytes.*
- A miner needs the table of the proof of work, which it makes or
  reads from a file at startup, and grows when the chain's height asks
  for a larger one. The job carries the height for that reason.
- The header's time is set when the job is made. In ten minutes it
  goes stale, so the node gives out the job again with the time
  renewed. *To confirm: that the time is not under the block's proof,
  so that this takes no new proof. `mine_with` sets it after proving,
  which suggests so.*
- The node checks what a miner sends, as it checks any block. There
  are no shares, no accounts and no payouts: this serves one person's
  machines, not a pool. A hash rate is what a miner says of itself.

## 7. Keys and secrets

### 7.1 The mining phrase

Today every block mined calls `wallet.reward(…)`, which makes a key
from the wallet's master secret. With the wallet in another program,
the node cannot. Instead:

- The wallet derives a **mining secret** from its master secret, one
  way: `mining = H(master, "mining", n)`, where `n` counts from zero.
- `tabwallet mining-phrase` shows it, as words. `tabwallet
  mining-phrase --new` makes the next one (after a leak, say); the
  wallet then watches for rewards under each it has made.
- A node that is to make blocks is started with `--mine` and **reads
  the phrase from standard input**, without showing it. It is not
  given as an argument, an environment variable or a file. Where
  standard input is not a terminal, one line is read from it.
- For each block the node makes a fresh key, exactly as the wallet
  does for an output of its own, with the mining secret in the place
  of the master secret: a random nonce `r`, the key from `H(mining,
  r)`, and a memo of `r` and a tag.
- The node keeps the phrase in memory only. It writes it to no log and
  no file.

What this gives:

| | |
|---|---|
| A key of its own for every block | Rewards are not linked to each other on the chain |
| The node never runs out of keys | Nothing to top up |
| The wallet need not be running | A node mines unattended |
| Taking the mining phrase takes the rewards not yet moved, and no more | The master secret cannot be worked back from it |
| XMSS state is untouched | The node signs nothing. Only spending signs, and only the wallet spends |

Still to design:

- **The phrase's form.** It must not be mistaken for the recovery
  phrase. Proposed: twenty-four words where the recovery phrase has
  twelve, each refused where the other is wanted, with a message that
  says which it is. `bip39.rs` handles twelve words only today.
- **Sweeping.** The wallet should move rewards that have matured to
  outputs of its own, so that little is ever exposed (entry 35).

### 7.2 Rewards in the wallet

The wallet shows a reward once its block is in the chain, and not
before.

- `follow` today only places outputs the wallet already knows of. It
  is extended to hold the memo of each block's first output (the
  reward's is always first) against the mining secrets. A block lists
  each output's memo, so this takes nothing more from the node.
- A reward found this way is treated as an output found by a scan: it
  signs from leaves 8 to 15, as the reference does for any output the
  wallet did not itself record at its making.
- The table of rewards awaited goes, with `reward`, `reward_found`,
  `forget` and `reward_settled`, and the pass at startup that clears
  rewards of blocks never found.
- A reorganization needs nothing new: a reward of a block undone is an
  output of a block undone.
- Blocks won and then undone are the node's to list (`GET /mining`).

### 7.3 The wallet on the message layer

This is the least settled part.

Payments are agreed in slates passed between wallets over the message
layer. To be reached, a wallet announces itself at certain nodes and
keeps doing so. Today the node does this on the wallet's behalf: it
holds the wallet's identity key and its Kyber keys
(`net::sessions::Participant`), signs the announcements, and opens
what arrives.

That key is not a spending key, but whoever holds it can answer a
payment meant for the wallet with an output of their own. It should
not live in the node. So:

- `Participant` moves to `tabwallet`. The wallet signs its own
  announcements and opens its own messages.
- The node carries bytes: it sends an announcement it is handed, posts
  a sealed message, and hands over sealed messages that arrive.
- **A wallet is reached only while it runs.** `tabwallet listen` stays
  connected and answers payments as they come; so does a wallet at its
  prompt. A wallet that is not running cannot be paid over the message
  layer, and the payer is told it is not there, as today when a node
  is down. Slates passed as files (`send-file`, `receive`, `finalize`)
  work whenever.
- `listen` can receive and cannot spend.

Not yet read closely enough to draft the requests: how announcements
are bound to each node's token, and how much of the ways through
relays (`net/circuits.rs`, `onion`) must move with `Participant`.

### 7.4 What else the wallet did in the background

The wallet's thread in `main.rs` also pools again a payment that fell
out of the pool, takes account of reorganizations, and reveals names
when their commits mature. In `tabwallet` these happen when it starts
and while it runs. A reveal that is late is the one that may cost
something: `wallet/names.rs` is to be read for what.

## 8. The script

`scripts/node.sh`:

1. If the node is to mine, asks for the mining phrase once, without
   showing it, and keeps it in memory.
2. Starts `tabnode`, and gives it the phrase on standard input.
3. Starts `tabprover` and `tabminer`, pointed at the node's work port.
4. Watches all three. One that ends is started again. The node is
   given the phrase again without anyone being asked.
5. A program that keeps failing is given up after a few tries, and the
   script says so.
6. Told to stop, it stops all three.

The phrase is handed over by a shell builtin through a pipe, so that
it is never an argument of a process or in a temporary file. After the
machine restarts, a person must give it again: that is the price of
keeping it off the disk.

The binaries are taken from `target/release/` unless the script is
told where else they are.

## 9. Order of work

Proposed. Each step ends with the tests passing.

| Step | What | Checked by |
|---|---|---|
| 0 | The workspace. The reference whole, in `tabshared`, with its one binary still built from it. | The reference's 648 tests, unchanged |
| 1 | `http` and `json` in `tabshared`. | New tests |
| 2 | The API server in the node, with the commands that need no wallet. `tabwallet` as a client of those. | New tests; the same answers as the prompt gives |
| 3 | The wallet out of the node: `follow` over the API, then each wallet command. | The wallet's tests, against a node |
| 4 | The message layer divided; `tabwallet listen`. | The reference's tests of payments between two wallets |
| 5 | The mining phrase. The node builds blocks; the work port; `tabminer`. | A dev network mined by a separate miner |
| 6 | `tabprover`. | The same, proven by a separate prover |
| 7 | `scripts/node.sh`. `tests/binary.rs` rewritten to drive the four programs. What is left of the one binary removed. | The whole, on the dev network |
| 8 | Enhancements. | |

Step 0 keeps a working program at every later step: modules leave the
one binary for the four as each boundary is made, and at no point is
there a half that does not run.

## 10. Enhancements

The split is to change nothing a user sees beyond what this document
says. Enhancements come after, with these exceptions, which are
cheaper done as the code is moved.

### What the split does of itself

- **The wallet's lock.** One `Arc<Mutex<Wallet>>` is shared by four
  threads today. It goes.
- **The wait for the setup.** `main.rs` polls every 50 ms for the
  proving setup to be ready. A prover that connects when it is ready
  takes the place of that.
- **Blocks given up.** `make_blocks` keeps a queue of threads still
  letting go of blocks no longer wanted. A job that is cancelled takes
  the place of that.
- **Commands as text.** `Console::run` takes a line and gives back
  text. Requests with fields take the place of that for everything
  the node answers.

### Entries of `NODE_ENHANCEMENTS.md` the split touches

Matched by their titles and the plan at the head of that file. Each is
to be read in full when it is taken up.

| Entry | How |
|---|---|
| 6. A mining node starts with twenty or thirty seconds of nothing | The setup and the table are the prover's and miner's to make ready. The node answers at once. |
| 10. What `status` says of memory | Memory is counted by part today (setup, table, pool, wallet, node). Those parts are now programs. |
| 19. How long a block takes to prove | The prover reports its timings with each proof. Several provers on one block becomes possible to ask. |
| 7, 23, 25–27, 29–32, 34, 35 (the wallet's commands and their wording) | All of this code moves to `tabwallet`. Best done as it is moved, in step 3. |
| 36. A miner's wallet, at the size it grows to | The table of rewards goes (7.2); sweeping (7.1) keeps the outputs few. |

### Found while reading for this document

- `resources/` lacks the two setup files (section 2).
- The default data directory is `~/.tabernacle/tabminer`, for a
  program now called `tabnode`.
- The wallet's `Cargo.toml` has no `dev` feature. That is right: the
  wallet should learn which network it is on from the node it
  connects to (`GET /status`), and refuse a wallet file of another.

A review of the code for further enhancements, module by module, has
not been done. It is better done at step 0, when the whole builds here
and its tests run.

## 11. Open questions

1. **Names.** The two ports' numbers.
2. **Data directories.** One for all four programs, or one each? The
   wallet file is today beside the chain, in the node's.
3. **A secret on the work port.** Without one, another user of the
   machine could take proving jobs and not return them. Proposed: the
   same kind of secret file as the API's, given to each worker, and
   required whenever the port listens beyond this machine.
4. **The mining phrase's form** (7.1): twenty-four words, or a string
   with a prefix?
5. **How a restored wallet learns how many mining phrases it made.**
   Proposed: it tries the first few counts when it looks through the
   chain.
6. **The message layer** (7.3): the requests are not drafted.
7. **A late reveal of a name** (7.4): what it costs.
8. **Other tools on the API.** If explorers or exchanges are to use
   it, some requests want to be read without the secret. Which?
