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
- Error line numbers from `rocq-warm` are sometimes 0-based and sometimes
  1-based (it depends on which layer reports the error). Check the character
  offsets against the line to be sure which tactic is at fault.

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

### More tactic notes

- Perennial has **no `wp_bind_inv`** (it is commented out in both
  `weakestpre.v` and `crash_weakestpre.v`). So a lemma about a WP under an
  evaluation context has to be *built* with `wp_bind`, not taken apart. That
  is why `wp_lams` carries "the rest of the application" in its
  postcondition instead of being stated as a transformation of
  `WP apply_vals_e ... {{Φ}}`.
- `iApply (wp_wand with "H")` and bare `iApply wp_wand_r` fail with "Cannot
  find witness"; `iApply (wp_wand_r _ _ _ <the Φ>)` works.
- `iApply wp_value'` fails when the value was introduced by `wp_wand_r`,
  because its type prints as `goose_lang.(language.val)` rather than `val`;
  `wp_pures` closes the same goal.
- To beta-reduce exactly once without `wp_pures` running away into the body,
  prove the step lemma with the body abstract (`wp_beta_recv`,
  `wp_beta_func`, `wp_beta_anon` in steps.v) and apply it.
- `#x` is opaque (`into_val` is a field of `GoGlobalContext`), so `#x` and
  `LitV (LitInt x)` are *not* convertible. A `GoOp` step needs the `#` form,
  and `teval`'s `match` needs the `LitV` form, so the order is: put the
  operands in `#` form, `wp_pures`, then `rewrite go.into_val_unfold` and
  `simpl` (`op_operands` / `op_finish` in steps.v).

### Writing a per-function proof

Layout: `new/checker/prelude.v` exports everything; one file per Go function
under `new/checker/fn/`. `new/checker/fn/TypeEq.v` is the worked example.

- **Never name a Rocq variable after a Go local.** `wp_auto`'s
  `wp_alloc_auto` derives a Rocq identifier (`x_ptr`) and an Iris name (`x`)
  from the Go variable name, and if a Rocq variable of a clashing name is in
  scope the whole of `wp_auto` silently fails with "Failed to progress" --
  not at the allocation, at the very first step, with no hint why. `TypeEq`'s
  Go locals are `a` and `b`, so its proof calls the types `ta`/`tb` and the
  locations `la`/`lb`.
- `wp_if_destruct` ends with `try wp_auto`, so a following `wp_auto` usually
  has nothing to do and fails; write `try wp_auto`.
- `wp_if_destruct` on `if: c ≠ d` gives the *equal* case first (the `else`
  branch of the Go `if`).
- It also runs `cleanup_bool_decide`, which silently discharges
  `bool_decide` of a hypothesis already in scope -- so the goal may be
  further along than expected.
- Recursion: `iLöb as "IH" forall (...)` before `wp_start`, then
  `wp_apply ("IH" $! args with "[$]")`. The specification's postcondition
  being `True` means `wp_apply` leaves no continuation to introduce.
- A recursive Go function that recurses into a possibly-nil field needs its
  specification over an *option* of the mirror type (`is_otype` in repr.v),
  since the nil child is a real call.

### Arithmetic on w64 kind codes

- `word` does **not** prove `W64 13 ≠ W64 14`, and its failure message is the
  unhelpful "Cannot find witness". For a disequality between two *literal*
  kind codes use `by vm_compute`.
- `word` also does not see through `W64 a = W64 b` on its own; first
  `apply (f_equal uint.Z) in H`.
- `idx_wf n` is `uint.nat (W64 n) = n` rather than `n < 2^64`, because the
  round-trip form is what every proof actually needs (`lia` struggles with
  `(2 ^ 64)%nat`, which it has to evaluate).

### More per-function lessons

- **`wp_auto` cannot do an anonymous `GoAlloc`.** It handles
  `let: "x" := GoAlloc t v in ...` (that is `wp_alloc_auto`), but a Go
  `&T{...}` in return position is a bare `GoAlloc t #v` and `wp_auto` just
  stops with the same useless "Failed to progress" as the name-clash trap.
  Use `wp_alloc l as "Hl"` for it. There is no plain `wp_alloc` without the
  `ident as constr` arguments.
- **Allocating a node that a representation predicate wants persistent**:
  `iApply wp_fupd.` first, then `wp_alloc l as "Hl"`, `wp_auto`,
  `iPersist "Hl"`, `iModIntro`, `iApply "HΦ"`. (`iPersist` often works
  without the `wp_fupd` because the `ElimModal` instance for `wp` absorbs the
  update, but only while the goal is still a `WP`.)
- **Case-split on the Gallina value, not with `wp_if_destruct`, for kind
  dispatch.** Once the mirror value is destructed, the node's kind code is a
  literal and `wp_auto` evaluates the whole chain of `=⟨Kind⟩` tests and `||`s
  by computation -- which also avoids the `word` problems with literal `W64`
  disequalities.
- After a recursive call in non-tail position, `wp_auto` often has nothing
  left to do (the goal is already `Φ v`); write `try wp_auto` or go straight
  to `by iApply "HΦ"`.
- `term`'s `TLt`/`TLe` binder is called `signed`, which matters for
  `destruct`.
- `rewrite lem; last tac` silently applies `tac` to the *main* goal when the
  rewrite produced no side condition, and the failure then surfaces as a
  confusing error on the `rewrite` line.
- `copy` and `make` are library calls with ready-made specs
  (`wp_slice_make2`, `wp_slice_copy`), not inlined loops -- `copySorts` needs
  no loop invariant.

### Working with several agents in one checkout

`git add -A` will sweep up another agent's half-finished file. Commit named
paths, and `git grep Admitted HEAD -- new/checker/` after every commit.

### Lessons from the parallel wave

- **The naming trap covers the lemma statement, not just the proof.** Rename
  the universally quantified variables in the specification itself; the
  statements stay alpha-equivalent to the "official" spelling.
- **Induction rather than Löb** for a function that recurses down a Gallina
  list: state a helper with `∀ le` *inside* the statement, `induction ρ`,
  then `wp_start`. Derive the public form by plain `apply`, not `iApply` --
  a Hoare triple is a `∀ Φ`, not an entailment.
- **After a tail call, `wp_apply` still leaves a WP.** Goose compiles
  `return f(...)` as `let: ("$ret0", "$ret1") := ... in return: (...)`, so a
  `wp_auto` is still needed before `iApply "HΦ"`.
- **`iApply "HΦ"` sometimes fails where `iSpecialize ("HΦ" with "[//]");
  iExact "HΦ"` works** (the same `language.val` vs `val` mismatch as with
  `wp_value'`).
- **A specification's postcondition gets delta-unfolded** by the `simpl` in
  `wp_auto`, so after `wp_apply ("IH" ...)` the returned boolean appears in
  its expanded form and `destruct (f x) eqn:...` abstracts nothing. Fold it
  back first: `fold (f x)`.
- **Case analysis over a pair of 18-constructor mirrors must not do a
  `vm_compute` per case** -- 324 of them exhaust memory. Route the kind codes
  through a `nat` mirror proved equal once per constructor, then
  `discriminate`.
- `uint.nat` is a notation, so `f_equal uint.nat` is rejected
  ("Abbreviation is not applied enough"); wrap it in a `Definition`.
- Numeric literals in the branches of an `if` inside a `nat`-returning
  definition elaborate in `Z_scope`; annotate with `%nat`.
- `wp_apply (spec with "[$]")` on a specification whose precondition has two
  same-shaped resources can frame them in the wrong order and instantiate the
  arguments wrongly; pass the arguments explicitly.
- `wp_slice_append` needs its arguments pinned positionally for the same
  reason, and shelves `IntoValTyped` side goals -- close them with
  `Unshelve. all: apply _.` before `Qed`.
- `wp_slice_literal` leaves the contents in insert form; normalize with
  `replace (Z.to_nat (word.signed (W64 0))) with 0%nat by word` then
  `iSimpl in "Hsl"`.

- **Rocq comments nest**, so a `(*T)` inside a doc comment (as in writing the
  Go receiver `(*State).clone`) opens a comment that is never closed. The
  error is "Syntax error: end of file inside an unterminated sentence" and
  points at nothing useful.
- `make` and `copy` are `wp_slice_make2` and `wp_slice_copy`; both end with a
  `wp_auto`, so the next `wp_auto` usually has nothing to do. After a copy,
  `rewrite length_replicate take_ge; last lia. rewrite drop_ge; last (rewrite
  length_replicate; lia). rewrite app_nil_r.` normalises the result.
