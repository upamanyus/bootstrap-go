# bootstrap-go (Lean): Go checkers whose answers Lean trusts

Two checkers for Go code, as translated by [Goose](https://github.com/goose-lang/goose)
to GooseLang, and the Lean development that lets a Lean proof rely on one of
their runs (OBSERVE-EXECUTION): run the Go checker on real hardware, and
turn "it returned `true` on these inputs" into a separation-logic
specification in Perennial.

- [`checker/`](checker/README.md) — a CSL symbolic-execution checker for
  loop-free functions over integers, booleans and pointers. Its soundness is
  **proved** (`Checkers/Checker/Soundness.lean`, `check_sound`; adequacy in
  `Checkers/Checker/Adequacy.lean`), so the only assumption a client adds is
  the observation of one run (`Checkers/Checker/Examples/Observed/Median3.lean`).
  Its algorithm also exists as Lean functions, proved sound with no
  observation at all ([`Checkers/Native/`](Checkers/Native/README.md),
  `lcheck_sound`), so a proof can run it by `native_decide` or in the kernel;
  `LCheck/` holds it, precompiled to native code.
- [`tcheck/`](gocheck/tcheck/README.md) — a table-driven checker whose
  knowledge of a program is a table of rules, each linked to a lemma already
  proved in Lean. Its soundness is stated, not yet proved
  (`check_adequate`, `Checkers/TCheck/Observe.lean`). Its client is etcd
  raft's `becomeFollower`: its specification, from the Lean raft election
  proof, follows from one observed run.

This is branch `lean`; the Rocq version is on `main`. It depends on
[Perennial's Lean port](https://github.com/mit-pdos/perennial/tree/lean) and on
the Lean raft election proof (`upamanyus/etcd-grove`, branch `lean`), both
Lake dependencies pinned in `lake-manifest.json`.

## Building

```
export PATH=$HOME/.elan/bin:$PATH     # elan; the toolchain is in lean-toolchain
lake build                            # all of Checkers/
go build ./... && go test ./...       # needs .lake/packages/perennial (goose)
bash gocheck/demo.sh                  # the checker on six examples, and Lean timings
bash gocheck/observe.sh               # re-observe Median3's run
bash gocheck/native.sh                # regenerate the Lean-native checker's inputs
bash gocheck/native_bench.sh          # time it against the hand-written proofs
bash gocheck/tcheck/observe.sh        # recheck and regenerate tcheck's observations
```

See [CLAUDE.md](CLAUDE.md) for the layout and [notes/STATUS.md](notes/STATUS.md)
for where things stand.
