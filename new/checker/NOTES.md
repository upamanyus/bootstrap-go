# Checker soundness proof — working notes

Running log of the proof of `check_sound` (see `SOUNDNESS_PLAN.md` in
`checker/` for the design). Newest entries at the bottom.

## Layout

    new/checker/defs.v         definitions the statement is over (was the top
                               of soundness.v; split out so that the proof
                               files can depend on them without depending on
                               the statement file)
    new/checker/soundness.v    `Axiom check_sound`, unchanged text, now
                               `Export`ing defs.v

## Build

Everything is behind the opam switch `perennial` (Rocq 9.4+alpha):

    eval $(opam env --switch=perennial --set-switch)
    make -j7 TIMED=false new/checker/<file>.vos     # fast, no proof checking
    make -j7 TIMED=false new/checker/<file>.vok     # checks proofs against .vos deps

`~/rocq-warm` keeps a warm `rocq repl` per file for the edit loop:

    rocq-warm check new/checker/<file>.v

## Log

### 2026-09-22

- Split `soundness.v` into `defs.v` (definitions) + `soundness.v` (the axiom).
  The axiom's text is character-identical to before, so the statement cannot
  have drifted. Nothing else in the tree required `soundness.v`.

### Build gotchas

- **Delete the `.vos`/`.vok` files.** `make ... .vos` (what `SOUNDNESS_PLAN.md`
  suggests for dependencies) leaves a `.vos` next to every `.vo`, and a
  `Require` then loads a mixture: a file compiled against `proof_prelude.vos`
  cannot be loaded next to `proof_prelude.vo`, and Rocq reports

      Compiled library New.checker.term_lemmas makes inconsistent assumptions
      over library New.proof.proof_prelude

  which looks like a proof error and is not one. Build the whole closure as
  `.vo` and keep it that way:

      find src new \( -name '*.vos' -o -name '*.vok' \) -delete

- `rocq-warm` needs real `.vo` dependencies, so the `.vo` closure of
  `new/checker/defs.v` (~150 files, about half an hour on 8 cores) has to be
  built once. After that the edit loop is a few seconds per check.
- `Set Default Proof Using "Type"` does not work in these sections (the
  section variables are all instances); use `"All"`.
- Error line numbers from `rocq-warm` are 0-based: an error "at line N" is at
  line N+1 of the file.

### Tactic notes

- `case_decide` is unreliable here: it silently fails (`No matching clauses
  for match`) when `destruct` cannot abstract the `decide` out of a
  hypothesis. Use `destruct (decide P)` with `P` written out, or
  `rewrite decide_True/decide_False/decide_ext`.
- `destruct (decide P)` already reduces an `if decide P then _ else _` in the
  goal, so a following `rewrite decide_True` has nothing to rewrite and
  fails. Do one or the other.
- `rewrite /Lam` is a notation, not a definition: it cannot be unfolded.
  `cbn [lams]` unfolds the `lams` fixpoint without reducing the `decide`s.

### Bugs found in the checker while proving it

1. **`is_term`/`is_assn` were not injective** (fixed in `defs.v`). `TVar n`
   with `n : nat` is represented as `W64 n`, so `TVar 0` and `TVar (2^64)`
   have the *same* heap representation while `teval` gives them different
   meanings. `check_sound` as written was therefore false: take
   `vars = [SBool]`, `pre = ⌜TVar 0⌝`, `post = ⌜TVar (2^64)⌝`; the checker
   sees the same term twice and answers `true`, but the triple it is then
   claimed to establish relates two unrelated values. The representation
   predicates now carry `idx_wf n := n < 2^64`.

2. **Unary minus at an unsigned type** (fixed in `checker/exec.go`).
   `applyUnOp` accepted `OpNeg` whenever the type's sort was `SortInt`, which
   includes `uint` and `uint64`. GooseLang has no `GoUnOp GoNeg` at those
   types -- `new/golang/defn/predeclared.v` defines `neg_int`, `neg_int64`,
   `neg_int32/16/8` and `neg_untyped_int` and nothing else -- so `-x` on a
   `uint64` is *stuck*, and the checker was calling a stuck program safe.
   This is a real soundness bug, reachable from ordinary Go (`-x` on a
   `uint64` is legal Go). `applyUnOp` now also requires `typeSigned(t)`.
   Regression test in `TestIllSorted`.
