# Plan: proving `check_sound` for the Go checker

> **Status (updated as the proof goes).** The plan below is the original
> design; this box records what has actually been established.
>
> Done, all checked in Rocq:
>
> - `new/checker/defs.v` -- the definitions the statement is over, split out
>   of `soundness.v` so the proof can depend on them without depending on the
>   statement. The axiom's text is unchanged.
> - §1 `term_lemmas.v`, §2 `subst.v`, §3 `steps.v`, §4 `interp.v`,
>   §5 `repr.v` (+ `nodes.v` for `Expr`/`Assn` nodes and `sortEnv`),
>   `prelude.v`.
> - `exec_spec.v`: `exec_sound`, its monotonicity in the path list (which is
>   what lets the loops in `exec.go` concatenate results), and the cases that
>   neither fork nor touch the heap.
> - `exec_spec.v` also has the semantic composition lemma for every
>   compound case of `exec` except the store: `let`, sequencing, `if` (the
>   forking one), load, allocation (the one that extends the valuation), and
>   the three exception-monad cases. Each says "if the pieces are sound, so
>   is the whole", independently of the Go code.
> - §6a, one file per Go function under `new/checker/fn/`: `TypeEq`,
>   `TypeSort`, `typeSigned`, `typeZero`, `termEq`, `TermEq`, `negate`,
>   `copySorts`, `envLookup`, `envBind`, `onePath`, `hasPat`, `heapLookup`,
>   `heapUpdate`, `(*State).clone`, `assnHasOr`, `assnHasExists`, `assnHeap`,
>   `assnPure`, `condHolds`, `findCell`, `instantiate`, `applyBinOp`,
>   `applyUnOp`, `growPats`, `flatten`, `collectDisjuncts`, and
>   `atomWellSorted`.
> - `disjunct.v` gives the postcondition matcher's `disjunct` a
>   representation predicate carrying the `pats`/`patOk` length invariant.
>
> Not done:
>
> - `sortOfEnv` and `SortOf` are parked as `*__nobuild.v`: the script is
>   essentially complete but the single Löb induction over all eighteen term
>   shapes produces a proof term too large to check. Splitting it per shape
>   is the fix. Three finished files assume it as a section hypothesis until
>   then: `applyBinOp` and `applyUnOp` assume `wp_SortOf`, and
>   `atomWellSorted` assumes `wp_sortOfEnv`. `new/checker/NOTES.md` has the
>   grep that lists every outstanding assumption.
> - The store case of `exec_sound`, `matchTerm`, `checkDisjunct`,
>   `parseDisjunct`, `parseDisjuncts`, `firstUnresolved`, `assnWellSorted`,
>   and then §6b `exec`/`execIf` themselves and §6c `Analyze`/`Verify`/`Check`.
>
> Two bugs found while proving, both fixed:
>
> 1. **The statement was not provable.** `is_term` represented `TVar n`
>    (`n : nat`) as `W64 n`, so terms whose indices differ by 2^64 had the
>    same heap representation while `teval` gave them different meanings: a
>    precondition mentioning `TVar 0` and a postcondition mentioning
>    `TVar (2^64)` are indistinguishable to the checker but not to
>    `pre_interp`/`post_interp`. The representation predicates now carry an
>    in-range side condition (`idx_wf`), which every tree the frontend builds
>    satisfies.
> 2. **A soundness bug in the checker.** `applyUnOp` accepted unary minus at
>    `uint`/`uint64`, but GooseLang has no `GoUnOp GoNeg` at those types
>    (`new/golang/defn/predeclared.v` defines `neg_int`, `neg_int64`,
>    `neg_int32/16/8` and `neg_untyped_int` and nothing else), so the
>    translated program is *stuck* and the checker was calling a stuck
>    program safe. Reachable from ordinary Go, since `-x` on a `uint64` is
>    legal Go. Fixed in `checker/exec.go` with a regression test.
>
> Three further findings about the Go code, none of them soundness bugs, all
> recorded in `new/checker/NOTES.md`: `growPats` does not terminate for an
> input-controlled large `∃`-index; `findCell` indexes `used` without
> requiring it to be as long as the heap; and `instantiate` can build a node
> with a nil child if `ret` is nil, which no `term` describes. Also, `exec`
> skipped the `let` binding for an empty name while the denotation always
> binds -- that divergence is fixed.
>
> `new/checker/NOTES.md` is the running log, and is worth reading before
> adding to this development: it records the Perennial-side traps that cost
> the most time.

Target: turn `Axiom check_sound` in `new/checker/soundness.v` into a `Lemma`,
proved in Perennial about the Goose translation of `checker.Check`
(`new/code/github_com/mit_pdos/perennial/checker.v`). Nothing about the Go code or
the statement should need to change for this; where a small change would make
the proof markedly easier it is called out in §9.

The statement (recalled):

```
{{{ is_pkg_init checker ∗ is_func lf f ∗ is_sorts svars vars ∗ is_assn lpre pre ∗ is_assn lpost post }}}
  @! checker.Check #lf #svars #lpre #lpost
{{{ (b : bool), RET #b; ⌜ b = true → ∀ θ, vars_sat θ vars →
      {{{ pre_interp θ pre }}} apply_vals (func_val f) (arg_vals f θ) {{{ v, RET v; post_interp θ v post }}} ⌝ }}}
```

Two logics are interleaved: the *outer* WP is about the checker's own execution
(Go heap of `Type`/`Expr`/`Term`/`Assn` nodes, slices of paths and cells); the
*inner* triple is about the analyzed GooseLang program. The proof of every Go
function therefore has a "semantic postcondition" describing what its result
means for the inner program. There is no Gallina reference implementation of
the checker; the only Gallina functions introduced are *specification devices*
(typing of terms/types, `subst_map`) that are needed to state what the Go
functions return.

## 0. Layout of the proof development

```
new/checker/soundness.v     statement (unchanged); Axiom → Lemma at the very end (§8)
new/checker/term_lemmas.v   §1  semantics of terms: sorts, agreement, substitution, negation
new/checker/subst.v         §2  subst_map metatheory for the fragment
new/checker/steps.v         §3  per-instruction WP lemmas at the supported types
new/checker/interp.v        §4  heap/env/state interpretation and well-formedness invariants
new/checker/repr.v          §5  lemmas about is_type/is_term/is_expr/is_assn/is_func
new/checker/proof_helpers.v §6a specs+proofs of the pure Go helpers (sorts.go, termEq, heap ops)
new/checker/proof_exec.v    §6b the exec theorem
new/checker/proof_check.v   §6c Analyze, Verify/checkDisjunct, Check
new/checker/adequacy.v      §8  end-to-end: adequacy + a concrete instantiation (Double)
```

Build with `.vos` for dependencies and `.vok` for the file being worked on
(`make TIMED=false new/checker/foo.vok` checks that file's proofs against `.vos`
dependencies). Keep each file under a few hundred lines; the Iris proof-term
size problem the whole project is about bites hardest in long files.

## 1. Term semantics (`term_lemmas.v`)

Pure Gallina lemmas about `teval`, `has_sort`, `vars_sat` from `soundness.v`.

- **Specification function** `sort_of (vs : list sort) (pats : list sort) (ret : option sort) : term → option sort`
  mirroring `sortOfEnv` in `checker/sorts.go` (with `TExec`/`TRet` → `None`).
  Lemma `sort_of_sound`: `vars_sat (vvar V) vs → pats_sat (vpat V) pats → ret_sat → sort_of … t = Some s → has_sort (teval V t) s`.
  This is the key fact that lets `if:` step and `GoOp` fire.
- `vars_below k t` (all `TVar n` have `n < k`) and `teval_agree`: valuations
  agreeing below `k` give equal values; `vars_below_mono`.
- Pattern substitution: `teval V (subst_pat σ t) = teval (V with vpat := σ') t`
  for the substitution the matcher builds, and `teval V (subst_ret r t) = teval (V with vret := teval V r) t`.
- `negate`: `teval V (negate c) = bval (negb b)` when `teval V c = bval b`
  (covers the double-negation cancellation because `c` is boolean-sorted).
- Injectivity facts: `ival`, `bval`, `lval` injective; `bool_decide (ival x = ival y) = bool_decide (x = y)`.
- `pc_sat V pc := ∀ t ∈ pc, teval V t = bval true`, with cons/app lemmas.

Effort: small (the earlier deleted `term.v` had most of this).

## 2. Substitution (`subst.v`)

The reference semantics substitutes; the checker uses an environment.

- `subst_map (m : gmap string val) : expr → expr`, defined on the fragment's
  constructors (`Val`, `Var`, `Rec`, `App`, `If`, `Pair`, `Fst`, `Snd`) and the
  identity elsewhere.
- Boolean `frag : expr → bool` for the fragment; `frag (expr_of e) = true`.
- Lemmas (Iris `metatheory.v` style, restricted to `frag e = true`):
  `subst_map_empty`, `subst_map_insert : subst_map (<[x:=v]> m) e = subst x v (subst_map (delete x m) e)`,
  and the unfolding equations for each constructor, including
  `subst_map m (Rec BAnon (BNamed x) e) = Rec BAnon (BNamed x) (subst_map (delete x m) e)`.
- Environments: `env_interp V (ρ : list (string * term)) : gmap string val` by
  `foldr insert` (head binding wins, matching the linked list in `exec.go`),
  and `env_interp_bind`.

Effort: moderate; the only induction over `expr`, kept small by `frag`.

## 3. Instruction steps (`steps.v`)

Concrete WP/PureWp lemmas derived from the typeclass semantics
(`go.PreSemantics`, `IsGoStepPureDet`, `under`/`internal` tags), one per
supported combination, with right-hand sides phrased through `ival`/`bval`/… :

- `into_val_unfold` corollaries: `#w = ival w`, `#b = bval b`, `#l = lval l`, `#() = uval`.
- For every `t` with `type_sort t = Some _` (int, int64, uint64, bool, `PointerType _`):
  `{{{ heap_pointsto l q v }}} ![type_of t] #l {{{ RET v; heap_pointsto l q v }}}`,
  `{{{ heap_pointsto l 1 v }}} #l <-[type_of t] w {{{ RET #(); heap_pointsto l 1 w }}}`,
  `{{{ True }}} GoAlloc (type_of t) v {{{ l, RET #l; heap_pointsto l 1 v }}}`,
  `GoZeroVal (type_of t) #()` steps to `ival 0` / `bval false` / `lval null`.
  Derivation: `load_underlying` + `load_predeclared`/`load_primitive` give
  `⟦GoLoad t, l⟧ ⤳ Read l`, then `_internal_wp_untyped_read`; untyped
  `heap_pointsto` is uniform across all supported types, which is why the
  statement uses it.
- Arithmetic and comparisons at each int type: `GoOp GoPlus t (ival x, ival y) ⤳ ival (word.add x y)` (same for sub, mul);
  `GoLt`/`GoLe`/`GoGt`/`GoGe` produce `bval (cmp_lt signed …)` with `signed`
  exactly `type_signed t` (int, int64 signed; uint64, uint unsigned);
  `GoEquals` at int, bool, pointer types produces `bval (bool_decide (v1 = v2))`
  (via `IsStrictlyComparable`); `GoUnOp GoNeg`, `GoUnOp GoNot`; `Convert t t ⤳ id`.
- Exception monad: the `PureWp` instances of `new/golang/theory/exception.v`
  restated with `exec_v`/`ret_v`: `do: v ⤳ exec_v`, `return: v ⤳ ret_v v`,
  `exec_v ;;; e2 ⤳ e2`, `ret_v v ;;; e2 ⤳ ret_v v`, `exception_do exec_v ⤳ #()`,
  `exception_do (ret_v v) ⤳ v`. (Needs `execute_val_unseal` etc. and
  `into_val_unfold_string`.)
- Application of the curried function: `apply_vals (func_val f) args` reduces
  by pure steps to `subst_map (params ↦ args) (expr_of body)`; for duplicate
  parameter names the later parameter wins, matching `envBind` order in
  `Analyze`.

Effort: moderate and mechanical; ~40 lemmas, each a few lines with `tc_solve`
after `pose proof (go.tagged_steps internal)`.

## 4. Interpretation and invariants (`interp.v`)

Gallina mirrors of the checker's *internal* data are needed only to state
specs (they never appear in the final statement):

```
Record sstate := { sheap : list (term*term); spc : list term; svars : list sort }.
Record path := { pret : term; pst : sstate }.
heap_interp V H := [∗ list] (l,v) ∈ H, ∃ lo, ⌜teval V l = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V v)
st_sat V st := vars_sat (vvar V) st.svars ∧ pc_sat V st.spc
wf_state st := all terms in sheap/spc are vars_below (length svars)
wf_env k ρ := all env terms vars_below k
```

Lemmas: `heap_interp_lookup` (a cell with a given location term yields a
points-to), `heap_interp_update`, `heap_interp_alloc` (prepend/append a fresh
`TVar k` cell under `upd_var V k (lval l)`), `heap_interp_agree` (valuations
agreeing below `k` give equal interpretation for `wf_state`), `heap_interp_app`
for path concatenation is not needed (paths are disjuncts, not conjuncts).

The **path postcondition** used by every exec-level spec:

```
paths_post (k : nat) (V : valuation) (ps : list path) : val → iProp :=
  λ v, ∃ p V', ⌜p ∈ ps⌝ ∗ ⌜∀ n, n < k → vvar V' n = vvar V n⌝ ∗ ⌜vpat V' = vpat V ∧ vret V' = vret V⌝ ∗
       ⌜v = teval V' p.pret⌝ ∗ ⌜st_sat V' p.pst⌝ ∗ heap_interp V' p.pst.sheap
```

and the **semantic soundness of a result list**:

```
exec_sound (e : cexpr) (ρ : env) (st : sstate) (ps : list path) : Prop :=
  wf_state st → wf_env (length st.svars) ρ →
  ∀ V, st_sat V st → ⊢ heap_interp V st.sheap -∗
        WP subst_map (env_interp V ρ) (expr_of e) {{ paths_post (length st.svars) V ps }}
```

plus `paths_wf k ps` (every result state is `wf_state`, `length svars ≥ k`,
`pret` below the new length).

## 5. Representation lemmas (`repr.v`)

`is_type`, `is_term`, `is_expr`, `is_assn`, `is_func`, `is_sorts` are already
defined in `soundness.v`. Needed:

- `Persistent` instances for all of them (by induction; `↦□` and `↦*□` are persistent).
- "Decoding" lemmas used after loading a node's `Kind` field: e.g.
  `is_expr l e -∗ ∃ n, l ↦□ n ∗ ⌜kind_of_expr e = n.(Kind')⌝ ∗ (children described by e)`,
  and, per constructor, the field equations (`e = CELet x e1 e2 → n.(Name') = x ∧ is_expr n.(A') e1 ∧ …`).
  These make the `switch e.Kind` in `exec` resolve to the right `cexpr` case.
- Mirrors for internal Go data with their representation: `is_term_list`,
  `is_cell`/`is_heap (s : slice.t) (H : list (term*term))`, `is_state (l : loc) st`,
  `is_path`, `is_paths (s : slice.t) ps` (over `own_slice`), `is_env (l : loc) ρ`
  (the linked list). The internal ones are *not* persistent (states are mutated
  after `clone`), so they carry `DfracOwn 1` for slices and states; nodes of
  terms remain `↦□` because terms are never mutated.
- The matcher's internal `disjunct`/`sortEnv` structs get representation
  predicates too (`checker/match.go`).

## 6. Specs and proofs of the Go functions

Style throughout: `wp_start as "..."`, `wp_auto`, `wp_if_destruct`,
`wp_apply (wp_helper with "[$]")`, struct fields via the generated
`Node_access_*` instances, `iPersist` after allocating a node. Recursion is
handled by Löb or by induction on the Rocq mirror value with the spec
∀-quantified over locations.

### 6a. Pure helpers (`proof_helpers.v`)

Each spec states the Gallina *meaning* of the result; these are the
specification functions of §1:

- `TypeSort`: `{{{ is_type lt t }}} TypeSort #lt {{{ RET (#(sort_code s), #true) … }}}` iff `type_sort t = Some s`, else `(…, #false)`.
- `TypeEq`: `RET #(bool_decide (t1 = t2))`. `typeZero`: returns a term `z` with `is_term lz z` and `teval V z = zero value of type_of t` for all `V`.
- `TermEq`: `RET #(bool_decide (a = b))` (needs `EqDecision term`, `Defined`).
- `SortOf`/`sortOfEnv`: `RET (#(sort_code s), #true)` iff `sort_of … t = Some s`.
- `negate`: returns `lc'` with `is_term lc' (negate c)`.
- `envLookup`/`envBind`: `is_env l ρ` and `env_lookup`/cons on the Gallina list.
- `heapLookup`: `is_heap s H` and `heap_lookup l H = Some v` ⇒ `RET (#lv, #true)` with `is_term lv v`.
- `heapUpdate`: returns a fresh heap slice representing `heap_update l v H`.
- `clone`: `is_state l st -∗ … RET #l'; is_state l st ∗ is_state l' st`.
- `applyBinOp`/`applyUnOp`: `RET (#lv, #true)` with `is_term lv r` and the
  *semantic* fact `∀ V, well-sorted operands → teval V r = the GooseLang result`
  (i.e. `teval V (TAdd a b) = ival (word.add x y)` when `teval V a = ival x`, …);
  these are exactly the right-hand sides of §3, so the exec proof only glues.
- Slice helpers as used (`append`, `make`+`copy`) via `new/golang/theory/slice.v`.

### 6b. `exec` (`proof_exec.v`) — the main theorem

```
Lemma wp_exec e ρ st le lρ lst :
  {{{ is_expr le e ∗ is_env lρ ρ ∗ is_state lst st ∗ ⌜wf_state st ∧ wf_env (length st.svars) ρ⌝ }}}
    @! checker.exec #le #lρ #lst
  {{{ (s : slice.t) (lfail : loc), RET (#s, #lfail);
      if decide (lfail = null)
      then ∃ ps, is_paths s ps ∗ ⌜paths_wf (length st.svars) ps⌝ ∗ ⌜exec_sound e ρ st ps⌝
      else True }}}.
```

Proof by induction on `e : cexpr` (the Go recursion is structural on the
tree; `is_expr` gives the children). Each `case` of the Go `switch` becomes
one Rocq case; the semantic obligation `exec_sound` is discharged by:

- literals/`EVar`: `wp_value`; `env_interp` lookup lemma.
- `ELet`: IH on `e1` gives paths; for each path continue with `e2` under
  `env_bind`; in the inner WP: `wp_bind` the value, `Rec` step, `wp_call`,
  `subst_map_insert`; the loop over paths needs a loop invariant "the results
  so far are sound for the paths so far" (`for _, p := range ps` → `wp_for` with
  invariant over the prefix of `ps` and the accumulated `out`).
- `ESeq`: as `ELet` without binding.
- `EIf`: IH on the condition; per path: `sort_of_sound` gives `teval V c = bval b`;
  literal condition → one branch; otherwise `wp_if_destruct` on `b`, use the IH
  for the taken branch with `pc_sat` extended by `c` or `negate c` (§1 negate
  lemma); results are the concatenation, `paths_post` is closed under `++`.
- `ELoad`/`EStore`/`EAlloc`/`EZero`: IH for the address/value; §3 step lemma;
  `heap_interp_lookup/update/alloc`; for alloc the fresh `TVar k` and the
  valuation update `upd_var V k (lval l)`, with `heap_interp_agree` to keep the
  rest of the heap unchanged and `vars_sat` extended with `SLoc`.
- `EBinOp`/`EUnOp`: IH twice; `applyBinOp` spec + §3 lemma; `wp_bind` on `Pair`.
- `EConvert`: `TypeEq` spec gives `t1 = t2`; `Convert t t` pure step.
- `EDo`/`EReturn`/`EExcSeq`/`EExcDo`: §3 monad steps; `EExcSeq` case-splits on
  the result term being `TExec`/`TRet` — this is syntactic on the term, and
  `teval` of those is exactly `exec_v`/`ret_v v`, which is what the pure steps need.

The loops over path slices are the main Perennial-side effort: one invariant
pattern reused in every case (`is_paths` for the input prefix, `is_paths` for
`out`, soundness of `out` as a *disjunction*, `wf` bookkeeping). Consider
factoring the loop bodies into small Go helpers if the inline loops make the
proofs unwieldy (§9).

### 6c. `Analyze`, `Verify`, `Check` (`proof_check.v`)

- `Analyze`: `RET (#s, #null)` ⇒ `∃ ps, is_paths s ps ∗ ⌜∀ θ, vars_sat θ vars → ⊢ pre_interp θ pre -∗ WP apply_vals (func_val f) (arg_vals f θ) {{ paths_post … }}⌝`.
  Uses: `assnWellSorted` (sorts of pre atoms), `assnHeap`/`assnPure` (pre's
  `assn_interp` equals `heap_interp` of the collected cells plus `pc_sat` of the
  collected pure atoms — a lemma by induction on `cassn` without `CAOr`/`CAExists`,
  which `Analyze` rejects), parameter binding (§3 application lemma), then `wp_exec`.
- `checkDisjunct` (the matcher): the central lemma is
  `match_sound`: if matching path `p` against disjunct `d` succeeds with
  substitution `σ` (pattern vars → terms), then
  `heap_interp V p.sheap -∗ assn_interp (V with vpat := teval V ∘ σ, vret := teval V p.pret) d`
  given `pc_sat V p.spc`. Proof: phase 1 consumes distinct cells (separation),
  each `matchTerm` success gives syntactic equality after substitution hence
  equal `teval`; phase 2 pure atoms hold by `pc_sat`, reflexivity, or `true`;
  leftover cells are dropped (affine). The existentials of the disjunct are
  witnessed by `teval V (σ i)` with `has_sort` from the matcher's sort check.
  The fixpoint loop needs an invariant "resolved atoms are matched, `used`
  marks the consumed cells, `σ` is consistent".
- `Verify`: every path has a matching disjunct ⇒ `paths_post … ps v -∗ post_interp θ v post`
  (choose the disjunct per path; `CAOr` interpretation is `∨`).
- `Check`: compose; the returned `b = true` case yields the inner triple by
  unfolding `{{{ }}}` to WP and chaining `Analyze`'s WP with `Verify`'s entailment.

## 7. Invariant checklist (things easy to forget)

- `wf_state`/`wf_env` bounds so valuation extension is harmless (`teval_agree`).
- Valuation changes only at indices ≥ current `length svars`; `vpat`/`vret` untouched during exec.
- Path order irrelevant to soundness (disjunction), but the loops still need prefix invariants.
- `heapUpdate` updates the *first* matching cell; with syntactic `TVar` keys
  any second match would make `heap_interp` `False` (two points-to for one
  location), so uniqueness is free.
- `TExec`/`TRet` have no sort; the `if:` check rejects them, so the monad
  values never reach `GoOp`.
- Duplicate parameter names: `envBind` order matches substitution order (later wins).
- `arg_vals` for a parameterless function is `[uval]` and the body is `λ: <>, body`.

## 8. From the lemma to a usable theorem (`adequacy.v`)

- Replace `Axiom check_sound` by the lemma (same statement).
- End-to-end for one program: state `run_axiom : rtc erased_step ([prog], (σ0, g0)) (Val #true :: efs, (σ', g'))`
  for `prog := Check` applied to trees built by a `build : cexpr → expr` that
  allocates the input (a short `wp_build` lemma by induction: `{{{ True }}} build e {{{ l, RET #l; is_expr l e }}}`),
  then derive `{{{ pre }}} Double args {{{ post }}}` via adequacy. Perennial has
  only recovery adequacy (`goose_recv_adequacy` in `src/goose_lang/recovery_adequacy.v`);
  either use it with a trivial recovery program and `wp_wpr`, or add a plain
  `wp_adequacy` wrapper (worth doing once, small).
- The correspondence between the concrete Go source and `expr_of e_Double`:
  `func_val e_Double = examples.Doubleⁱᵐᵖˡ` by `reflexivity` (unseal-free, since
  `func_val` produces the sealed combinators through `expr_of`).

## 9. Optional Go changes that would simplify the proof

None are required; each trades a little code style for proof effort.

- Loops → recursion: the `for _, p := range ps` loops in `exec.go` could become
  small recursive helpers (`execLetAll` style), turning loop invariants into
  inductive specs. This was the shape of the earlier prototype and is the
  single largest proof simplification available.
- Path lists as linked lists instead of slices would remove all `own_slice`
  reasoning, at the cost of less idiomatic Go.
- `Failure` could carry the state at failure (`St *State`) for better
  diagnostics; irrelevant to soundness since the `false` case is trivial.

## 10. Order of work and rough effort

1. `term_lemmas.v`, `subst.v`, `steps.v`, `interp.v` — independent of the Go
   code's details; a few days. Can be done in parallel by separate agents.
2. `repr.v` decoding lemmas and `proof_helpers.v` — establishes the proof
   style against the generated code; several days.
3. `wp_exec` — the bulk; expect the slice/loop bookkeeping to dominate.
4. `match_sound` and `proof_check.v`.
5. Adequacy wrapper and the `Double` instantiation.

Check every file with `.vok`; keep `soundness.v` untouched until step 5 so the
statement cannot drift from what the tool computes.
