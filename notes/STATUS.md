# Status

**Last updated:** 2026-10-07

## Where things stand

The whole Rocq side of both checkers on `main` is ported to Lean, except the
pieces listed under "Not ported" in [decisions.md](decisions.md) (`wp_symex`
and the Rocq goal exporter, neither of them a checker). `lake build` builds
all of it (680 jobs); no file of this repository has a `sorry`.

### checker/ (proved sound)

- `check_sound` (`Checkers/Checker/Soundness.lean`) and `check_adequate`
  (`Checkers/Checker/Adequacy.lean`) are theorems; `#print axioms`:
  `propext, Classical.choice, Quot.sound`.
- `Checkers.Checker.wp_Median3` (`Examples/Observed/Median3.lean`) adds
  exactly one axiom, the observation `median3_check_run`;
  `bash gocheck/observe.sh` re-observes it.
- `check_adequate` takes `{GF} [GooseGpreS ffi GF]` as a premise (Perennial
  Lean's `FfiInterpAdequacy` cannot build that instance for an arbitrary FFI,
  unlike Rocq's `ffi_interp_adequacy`), and `median3_check_run`'s existential
  names `GF` as part of the model. Drop both if Perennial Lean grows an
  `ffiΣ`-style field.
- The six hand-written example proofs (`Examples/*.lean`) are ported;
  `gocheck/demo.sh` times them against the checker.

### tcheck/ (soundness stated)

- `Perennial.TCheck.raft.becomeFollower.wp_proof` proves etcdGrove's own
  `raft.becomeFollower.spec`, given `raft.reset.spec` and
  `traceBecomeFollower.spec`, from one observed run. Axioms it adds:
  `TCheck.check_adequate` (the checker's soundness, unproved, as on `main`)
  and `TCheck.becomeFollower_check_run` (the observation). The rest of its
  `#print axioms` is inherited: etcdGrove's trust boundary (`isLogger`,
  `Logger.wp_logf`, `ownStorage`) and Perennial's opaque types of other
  packages (`fmt.pp`, `os.*`, `sync.Map`, …).
- `raft.tbl` is written against the Lean election proof's lemmas (see
  [decisions.md](decisions.md)); `bash gocheck/tcheck/observe.sh` rechecks it.

## Known issues

- **The dependencies' pins are not on GitHub yet.** Perennial `8c75a3dd4`
  (local `lean`, 5 commits ahead of GitHub's `f3b8ef80f`) and etcd-grove
  `51d6df02d` (branch `lean`, not pushed). Until both are pushed, Lake can
  only use an already-populated `.lake/packages`; a fresh clone cannot
  resolve them.

## Next

- Prove tcheck's `check_adequate`, the way `Checkers/Checker/` proves the
  checker's soundness.
- When etcdGrove gains a hand-written proof of `raft.becomeFollower`, compare
  costs with tcheck's (`gocheck/tcheck/README.md` has the tcheck numbers).
