# `lean-ledger-bitcoin` — Worker Contract (`WORKER.md`)

Every worker mission in this campaign MUST obey these rules strictly:

## 1. Plain Lean 4 Formal Specifications (`formal-specs`)
- Write **plain, idiomatic Lean 4** (`def`, `structure`, `inductive`, `theorem` over standard domain types `ByteArray`, `Array`, `List`, `BitVec`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Nat`, `Option`, `Except`).
- **NEVER** import `Th0rgal/lean-specs` or create wrapper DSLs (`SpecM`, `ObsQuotient`, `SpecBlock`, `SubSpec`, etc.).
- **Zero axioms / zero `sorry` / zero `native_decide`** in `Spec/` and `Proofs/`: every theorem must depend solely on `{propext, Quot.sound}` (or `{}`).
- **Implementation-independent contracts**:
  - Deduce specifications from **both** official Ledger reference codebases (`LedgerHQ/app-bitcoin` at `f010982d3050e02813cd7129bebd68cf2d1f2099` and `LedgerHQ/vanadium` `apps/bitcoin` at `ace8e96982408959dea9e7fbc59ee36e8c54e645`) plus the underlying BIPs (BIP-32, BIP-143, BIP-173/350, BIP-174/370, BIP-322, BIP-327, BIP-340/341/342, BIP-352/374/375, BIP-380..388).
  - Where `app-bitcoin` (BOLOS) and `vanadium` (`apps/bitcoin`) differ in transport or feature surface (e.g., BOLOS merkleized streaming vs Vanadium FastPSBT/Silent Payments), factor the **canonical Bitcoin wallet domain spec** cleanly and parameterize or isolate target-specific wire/protocol surfaces explicitly, documenting every discovered discrepancy!
  - Never define a spec by calling an implementation function (`def spec := impl`).
  - Specify **atomic error rollback** (`step cmd s = .error e -> persistent state unchanged`, modulo explicit MuSig2 nonce invalidation rules) and **read-only purity** (`s' = s` for read-only queries).
  - Include sanity/non-vacuity theorems (`∃` witness tests, roundtrip lemmas, and negative security rejection theorems proving malformed/attack inputs are rejected).

## 2. File Ownership & Git Discipline
- Touch **ONLY** the files/directories explicitly listed in your mission prompt's `OWNED PATHS`.
- Do **NOT** edit `lakefile.lean`, `lean-toolchain`, `plan.md`, `campaign-state.json`, or another shard's files unless explicitly assigned.
- Work on your assigned git branch (`git checkout -b <branch>`), verify compilation with `lake build` (or `lean` / `turbo-lean`), commit cleanly, and **`git push -u origin <branch>` before ending your turn**.
- Never disable tests, weaken assertions, or timebox failing checks into `PASS`.
- Do not invoke `maxwell record` in your shell.

## 3. Persistent Paths on Boat VMs
- On Boat VMs, keep durable caches/worktrees under `/var/lib/orb-node/work/...` (`$HOME/work/...`), **never** `/tmp` or `~/.cache` when preparing snapshots.
- End your final message with:
  1. Branch name & exact pushed commit SHA (`git rev-parse HEAD`)
  2. Exact verification commands executed and exit codes
  3. Discovered reference discrepancies or edge cases between `LedgerHQ/app-bitcoin` and `LedgerHQ/vanadium`
  4. Status: `DONE`, `BLOCKED`, or `NOT_FEASIBLE`.
