#!/usr/bin/env bash
# The checks CI makes, to be made here before a commit.
#
#   scripts/ci.sh                 all of them, of every crate
#   scripts/ci.sh lint            formatting, Clippy, and no dependencies
#   scripts/ci.sh debug           the tests, unoptimised
#   scripts/ci.sh release         the tests, optimised: the slow ones too
#   scripts/ci.sh lint debug node    some of them, of one crate
#
# Built for this machine's own processor, as .cargo/config.toml has it.
# CI makes every check a second time built for any x86-64 at all, which
# is the only way the code without AVX2 and without carry-less
# multiplication is run on a machine that has them:
#
#   RUSTFLAGS="-C target-cpu=x86-64" scripts/ci.sh
#
# A crate is added below, and to .github/workflows/ci.yml, when it has
# code. miner, prover and wallet have none yet.
set -euo pipefail
cd "$(dirname "$0")/.."

CRATES="shared node"

# The sets of features a crate is linted under, one to a line: each set
# compiles code the others leave out.
features_of() {
    case "$1" in
        shared) printf '%s\n' "" "dev" "testing" "dev testing" ;;
        node) printf '%s\n' "" "dev" ;;
    esac
}

# The features a crate is tested under: every one that adds tests. None
# takes a test away.
tested_with() {
    case "$1" in
        shared | node) echo "dev" ;;
    esac
}

say() {
    if [ -n "${GITHUB_ACTIONS:-}" ]; then echo "::endgroup::"; echo "::group::$*"; else echo "== $*"; fi
}

lint() {
    local crate=$1 features
    say "$crate: no dependencies"
    if grep -q '^source = ' "$crate/Cargo.lock"; then
        echo "$crate/Cargo.lock names a package from outside this repository" >&2
        exit 1
    fi
    say "$crate: formatting"
    (cd "$crate" && cargo fmt --check)
    while IFS= read -r features; do
        say "$crate: clippy [$features]"
        (cd "$crate" && cargo clippy --locked --all-targets --features "$features" -- -D warnings)
    done < <(features_of "$crate")
}

# Unoptimised: with the checks for overflow and the debug assertions.
# The tests marked "slow unoptimized" are left out of these.
debug() {
    say "$1: tests, unoptimised"
    (cd "$1" && cargo test --locked --features "$(tested_with "$1")")
}

# Optimised, as the programs are built: every test but the timings and
# the ones that write a setup.
release() {
    say "$1: tests, optimised"
    (cd "$1" && cargo test --locked --release --features "$(tested_with "$1")")
}

stages=""
crates=""
for word in "$@"; do
    case " lint debug release " in *" $word "*) stages="$stages $word" && continue ;; esac
    case " $CRATES " in *" $word "*) crates="$crates $word" && continue ;; esac
    echo "usage: scripts/ci.sh [lint] [debug] [release] [${CRATES// /] [}]" >&2
    exit 2
done

for stage in ${stages:-lint debug release}; do
    for crate in ${crates:-$CRATES}; do
        "$stage" "$crate"
    done
done
[ -z "${GITHUB_ACTIONS:-}" ] || echo "::endgroup::"
