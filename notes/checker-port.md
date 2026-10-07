# Porting `new/checker/` to Lean

How the Rocq soundness development of the Go checker (`~/bootstrap-go/new/checker/`)
maps onto `Checkers/Checker/` here. Read `notes/porting.md` first (layout,
build, conventions) and the etcdGrove porting guide
(`.lake/packages/etcdGrove/notes/porting-guide.md`, Rocq → Lean cheat sheet).

## What exists

| Rocq | Lean | |
|---|---|---|
| `defs.v` | `Defs.lean` | statement vocabulary: `teval`, `cexpr`, `expr_of`, `func_val`, `assn_interp`, `is_*`, `triple_holds` |
| `term_lemmas.v` | `TermLemmas.lean` | pure: `sort_of`, `env_sat`, `vars_below`, `negate`, `pc_sat` |
| `subst.v` | `Subst.lean` | `pname_inj`, `csubst`, `binds`, `lams_step`, `env_interp`, `env_lookup` |
| `interp.v` | `Interp.lean` | `scell`/`sstate`/`spath`, `heap_interp`, `paths_post`, `paths_wf` |
| `steps.v` | `Steps.lean` | `ival_eq` & co, `wp_ctype_{load,store,alloc,zero}`, `wp_binop`, `wp_unop`, `wp_convert`, exception monad, `wp_func_val(_nil)` |
| `repr.v` | `Repr.lean` | persistence, `*_not_null`, `is_otype`/`is_oterm`, `is_type_node`, `is_term_node`, `is_heap`/`is_state`/`is_env`… |
| `prelude.v` | `Prelude.lean` | imports all of the above, `checker_pkg`, `wp_initialize'` |
| `nodes.v` | `Nodes.lean` | `is_expr_node`, `is_assn_node`, `is_oexpr`, `is_oassn`, `is_sortenv` |
| `fn/X.v` | `Fn/X.lean` | done: `TypeEq`, `termEq` (worked examples), `TermEq`, `TypeSort`, `typeSigned`, `negate`, `envBind`, `envLookup`, `onePath`, `copySorts`, `State__clone` |

All build (`lake build Checkers.Checker.Fn.<X>`), no `sorry`, no `axiom`
(`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).
`Checkers.lean` (the library root) does not import them yet.

Fidelity check: the bottom of `Defs.lean` has the hand-written `cfunc`s of
`examples.Double` and `examples.Median3` and checks
`func_val f = checker.examples.Median3.impl` by `rfl` (instant).

## A `fn/X.v` file → `Fn/X.lean`

File skeleton (copy `Fn/TypeEq.lean`):

```lean
import Checkers.Checker.Prelude          -- plus `import Checkers.Checker.Fn.<callee>` per callee
noncomputable section
namespace Perennial
namespace Checker
open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go   -- so `checker.F` names the Goose output
section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]
...
end proof
end Checker
end Perennial
```

Never `open` the `checker` namespace itself: its constants `checker.TVar`,
`checker.SortInt`, … (`val`s) would clash with our constructors `TVar`, `SInt`.
Lean only abstracts section variables a declaration uses, so pure lemmas in
these sections are fine (Rocq's "`Default Proof Using "All"` poisons pure
lemmas" and the `package_sem` exclusion dance do not exist); still, put pure
mirror functions before `section proof`.

### Specs

| Rocq | Lean |
|---|---|
| `{{{ is_pkg_init checker ∗ P }}}` | `{{ isPkgInit (PROP := IProp GF) checker_pkg ∗ P }}` |
| `@! checker.F #a #b` | `(App (App (Val (@! checker.F)) (Val #a)) (Val #b))` (the expression must be parenthesised: the triple's expression slot is `term:max`) |
| `lst @! (go.PointerType checker.State) @! "clone" #()` | `(App (Val (lst @!! go.GoType.PointerType checker.State.ty @!! go!"clone")) (Val #()))` |
| `{{{ (l : loc), RET #l; Q }}}` | `{{ (l : Loc), RET #l; Q }}` |
| `RET (#a, #b)` | `RET (PairV #a #b)` |
| `bool_decide (oa = ob)` | `decide (oa = ob)` |
| `slice.t`, `checker.Cell.t`, `own_slice_cap V s (DfracOwn 1)` | `GoSlice`, `checker.Cell`, `ownSliceCap V s (DFrac.own 1)` |
| `heap_pointsto l (DfracOwn 1) v` | `heapPointsto l (DFrac.own 1) v` |

Lemma names are Rocq's (`wp_TypeEq`, `wp_State__clone`, `term_eq_iff`), in
namespace `Perennial.Checker`. Rocq's `_aux` + public pair (e.g.
`wp_envLookup_aux`) can be one theorem proved by `induction … generalizing`.

### Proofs

* `wp_start as ⟨#Hoa, #Hob⟩` (pattern for the precondition minus `isPkgInit`,
  which goes to `□Hpkg`), then `wp_auto`.
* Destructing a representation predicate: `icases is_term_node _ _ $$ Hoa with
  ⟨%la, %lb, %lc, %Hwf, #Hn, #Ha, #Hb, #Hc⟩`; keep the original with `ihave`.
  For a recursive predicate's own unfolding use `unfold is_state` /
  `simp only [is_env]` on the goal, then `icases`.
* **Loads from a node** (`l ↦□ checker.Term.mk ..`): `wp_auto` does *not* find
  fields of a persistent struct points-to (Perennial's `Access` search picks
  the store instance first and forces `DFrac.own 1`). Split it first:
  `iStructNamedSuffix Hn "_a"` (fields become `Kind_a`, `Num_a`, …; use a
  suffix when two nodes are open). Spatial struct points-tos work directly.
* `wp_if_destruct`: hypothesis `Hif` (each new one shadows the previous: save
  with `have Hk := Hif`); `x = null` is substituted. Order as in Rocq (the
  `==` case first). Branch on Lean data (`cases oa`, `cases ty`) rather than
  with `wp_if_destruct` for kind dispatch; once a node's kind is a literal
  `wp_auto` evaluates the tests.
* Calls of other checker functions: `wp_apply wp_termEq la lb oa ob $$ []`
  then `· iframe #` for a persistent precondition (or `$$ [H1 H2]` and
  `· iframe H1 H2`). Give `as %x ⟨%Hx, #Hy⟩` for the postcondition; if the
  postcondition is `True` and code follows, still write `as _`, otherwise the
  goal keeps a `True -∗ WP …` (`Fn/TypeSort.lean`).
* Recursion through a heap pointer: `iloeb as IH generalizing %x %y` before
  `wp_start`; recursive call `wp_apply IH $$ %x' %y' []`. Recursion down a
  Lean list: `induction ρ generalizing le`, then `wp_start` in each case, and
  `wp_apply IH lnx $$ []` (`Fn/envLookup.lean`).
* Finish: rewrite the returned value into the spec's form with a pure `have`
  (`rw [Hd]`), then `iapply HΦ; itrivial` (or `iframe …`). `wp_end` also works.
* Anonymous allocation `&T{…}` (`GoAlloc t (struct literal)`): `wp_auto` stops
  *before* evaluating the literal's loads; do `wp_pures; wp_load; wp_pures; …;
  wp_alloc l as Hl` (`Fn/State__clone.lean`), or directly `wp_alloc l as Hl`
  when the fields are already values (`Fn/negate.lean`). Persist with
  `ipersist Hl` while the goal is still a WP.
* A freshly allocated struct may show `Num' := 0` where the predicate says
  `W64 0`: `iExactEq Hl; rfl`.
* Goose constants (`checker.SortInt`, `checker.TNot`, …) can stay folded:
  `simp only [checker.SortInt, checker.SortLoc]` before `iapply HΦ`.
* Slices: `wp_slice_make2 as %sl ⟨Hs, Hcap⟩` (side goal `ipureintro; word`),
  `wp_slice_copy dst _ src _ dq $$ [Hdst]` (pass the slices and the fraction
  explicitly; `DFrac.discard` for `↦*□`), then normalise with
  `List.drop_of_length_le`, `List.length_replicate`, `List.take_of_length_le`,
  `List.append_nil`. `wp_slice_literal; isplitr; · ipureintro; rfl; iintro %sl
  ⟨Hsl, _⟩`, and `wp_slice_append (t := T.ty) slice.nil [] _ [x] (DFrac.own 1)`
  with `ownSlice_nil`/`ownSliceCap_nil` (`Fn/onePath.lean`). `ihave H := lemma`
  of a `⊢ P` lemma lands in the *intuitionistic* context, which a bare
  `iframe` does not frame: name it (`iframe Hsl Hnil Hnilcap`).
* Big ops: `[∗list] x;y ∈ [a];[b], P x y` — `iapply BigSepL2.bigSepL2_singleton.2`.
* Unfolding `is_otype`/`is_oterm` of `some t`: `rw [is_otype_some]`
  (`simp only [is_otype]` would also unfold the `is_otype` inside a Löb
  hypothesis).
* `rw [pnames_cons]`-style rewrites hit every occurrence; to rewrite one
  instance use `rw [show <lhs> = <rhs> from rfl]`.
* Lean has **no** naming trap: a Lean variable may share a Go local's name
  (`wp_alloc_auto` makes `t_ptr`/`t` regardless). Rocq's renamings (`la` for
  `a`) are kept only to keep the files comparable. (Untested: an *Iris*
  hypothesis named like a Go local may still clash.)

### Steps.lean for the exec proofs

* `ival_eq : #w = ival w` (also `bval_eq`, `lval_eq`, `uval_eq`, `sval_eq`)
  need only `[GoLocalContext] [go.Semantics]`, so `rw [← ival_eq]` works in
  any WP goal.
* `wp_binop op t a b r V Φ : apply_binop … = some r → has_sort … → has_sort … →
  Φ (teval V r) ⊢ WP (App (Val (GoInstruction (GoOp (binop_of op) (type_of t))))
  (Val (PairV (teval V a) (teval V b)))) {{ Φ }}` — Rocq's `Φ v -∗ WP …` are
  entailments `⊢`; `iapply (wp_binop op cty …)` as in Rocq.
* Instruction lemmas are stated on the shapes `expr_of`/`csubst` produce
  (`App (Val (GoInstruction (GoLoad (type_of t)))) (Val #l)`,
  `App (Val doExecute) (Val v)`, `App (App (Val exceptionSeq) (Rec BAnon BAnon
  e2)) (Val exec_v)`, …).
* `exec_v_eq : exec_v = executeVal`, `ret_v_eq : ret_v v = returnVal v`.
* `wp_func_val`/`wp_func_val_nil` (for pre_sound) keep Rocq's statements.
  `fill (app_ctx vs) h = apply_vals_e h vs` by `rfl`; Iris-lean also has
  `wp_bind_inv` (Rocq does not), should a later proof want it.

## Differences from Rocq the next files must know

* `pname : GoString → String` (Rocq `go.go_string_to_string`) maps each byte to
  `Char.ofNat`; injective (`pname_inj`), and equal to goose's identifier on
  ASCII names.
* The **Lean goose backend can nest statements differently** from Rocq's:
  statement sequences are left-nested `(s₁ ;;; s₂) ;;; s₃`, and a `let` may
  end before a later statement (Lean `Double.impl` has `(let: "y" := … in …)
  ;;; return: #()`, Rocq's has the `return:` inside the `let:`). `cexpr`
  expresses both, but a checker input must follow the Lean output. Rocq's
  `observed/median3_input.v` happens to denote Lean's `Median3.impl` too
  (checked by `rfl`); do not assume that for other functions — check
  `func_val f = F.impl` by `rfl` (as at the bottom of `Defs.lean`).
* `triple_holds` also quantifies over `GoGlobalContext` and `HasLC` (in Rocq
  the former came with `heapGS`; the latter does not exist).
* `go.Semantics` gives `Convert t t v ⤳ v` for every `v` (as Rocq), so
  `wp_convert` is unchanged.
* `GoOp GoGt`/`GoGe` produce `decide (y < x)` / `decide (y ≤ x)`, matching
  `apply_binop`'s swapped `TLt`/`TLe`; `GoUnOp GoNeg` gives `-x`.

## Gotchas (exec chain)

* `ExecSpec.lean` (built) has `exec_sound_at`/`exec_sound` and all of
  exec_spec.v's lemmas under Rocq's names. `exec_sound_at … ` is
  `wf_state sst → env_below … → ∀ V, st_sat V sst → heap_interp V (sheap sst) ⊢
  WP …` (Rocq's `⊢ P -∗ WP` as an entailment). `exec_sound` quantifies over
  `ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem` (nine binders, like
  `triple_holds`); to use an `H : exec_sound …` at the ambient ghost state,
  apply it to the section variables by name: `H ext ffi _ _ go_gctx hlc GF hG sem`
  (explicit `_` for the instance binders do not unify — name them).
  Lifting a lemma: `fun H ext ffi fi fs gc hlc GF hG sem => exec_sound_at_X
  (GF := GF) … (H ext ffi fi fs gc hlc GF hG sem)`.
* Pure mirrors `heap_lookup` (`Fn/heapLookup.lean`), `heap_update`
  (`Fn/heapUpdate.lean`), `st_assume`, `st_alloc`, `upd_var` (`ExecSpec.lean`)
  are outside the proof sections and need no ghost-state variables.
* `iapply wp_bind (fill [Ki])` does not unify with a goal `WP (App f e)`:
  first `rw [show App f e = fill [EctxItem.AppRCtx f] e from rfl]`. After the
  bind, `rw [fill_singleton]; simp only [fillItem]` (`ExecSpec.fill_singleton`)
  turns `fill [Ki] (Val w)` back into the expression. `refine`/`exact` of a
  lemma stated with `fill K` do unify (default transparency).
* Range loops (`slice.forRange`) unfold under `wp_auto` to a `doFor` with an
  `i_ptr` local: `ihave HI : (∃ n …, "i" ∷ i_ptr ↦ n ∗ … : IProp GF) $$ [i …]`,
  `wp_for HI`, `wp_if_destruct`, then `rw [ite_eq_left ⟨Hn.1, Hif⟩]` for the
  bounds check, `list_elem`, `wp_apply wp_load_slice_index s (sint.Z n) cs _
  x Hn.1 $$ [Hs] with Hs` (`Fn/heapLookup.lean`, `Fn/heapUpdate.lean`).
  `wp_if_destruct` already runs `wp_auto`; a following `wp_auto` errors with
  "no progress" or "is not a GooseLang WP" (when the goal is a
  `forPostcondition`): go straight to `wp_for_post`.
* `[∗list] c;sc ∈ cs;H, is_cell c sc`: get one element with
  `ihave #Hcell := BigSepL2.bigSepL2_lookup (Φ := fun _ c sc => is_cell (GF := GF) c sc) H1 H2 $$ Hcs`,
  then `rw [show is_cell c sc = iprop(is_term … ∗ is_term …) from rfl]` before
  `icases` (icases does not unfold `is_cell`). Extend with
  `iapply BigSepL2.bigSepL2_snoc.2`.

## Gotchas (parse/pre chain)

* Built: `Fn/sortOfEnv` (`osort_of`/`osort_code`/`osort_ok`, `env_pts`,
  `wp_sortOfEnv_pts`, `wp_sortOfEnv`, `wp_sortOfEnv'`), `Fn/SortOf`
  (`wp_SortOf`), `Fn/atomWellSorted` (`atom_well_sorted`), `Fn/assnWellSorted`
  (`cassn_ws`/`oassn_ws`), `Fn/assnHasOr`, `Fn/assnHasExists`, `Fn/assnHeap`
  (`cassn_heap`/`oassn_heap`, `is_heap_nil`), `Fn/assnPure`
  (`cassn_pure`/`oassn_pure`, `is_cond_nil`).
* Lean's `wp_auto` is fast enough that `sortOfEnv`'s 18-way dispatch with a
  full sort-by-sort case split after each recursive call (`rcases sort_of E x
  with _ | (_|_|_|_)`, 125 cases for `TIte`) checks in under a minute; no
  narrow per-shape tactics needed.
* `wp_auto` cannot load a *field* through a fractional (`↦{dq}`) struct
  points-to either (not only `↦□`): split it with `iStructNamed H` after
  `ihave %Hnn := typedPointsto_not_null _ _ _ $$ H`, and put it back with
  `iapply typedPointsto_combine _ _ _ Hnn; simp only
  [TypedPointsto.typedPointstoDef]; iframe` (`finish_split` in
  `Fn/sortOfEnv.lean`).
* Macros that introduce Iris names the caller refers to need
  `set_option hygiene false in local macro …` (Lean macro hygiene renames
  them otherwise).
* A `def … : IProp GF := iprop({{ … }} …)` used as a Löb hypothesis needs a
  `Persistent` instance (`unfold X; infer_instance`), or `iintro #IH` fails.
* `iframe` of a whole goal sometimes refuses `slice.nil ↦*□ []` against an
  identical hypothesis (seen in `wp_SortOf`); `isplitr` and `iexact` each
  conjunct instead.
* `iframe #` does not frame `is_oassn l (some a)` from `is_assn l a`:
  `rw [is_oassn_some]` first.
* `wp_apply spec $$ … as _` when the postcondition is `True` *without* other
  binders and code follows: in these files `as _` was rejected ("not a
  wand") — drop the `as`.

## Gotchas (match chain)

* Built: `Disjunct` (`cdisjunct`, `disjunct_env`, `is_disjunct`),
  `DisjunctRo` (`is_disjunct_ro`, `is_disjunct_freeze : is_disjunct l dj ⊢
  |==> is_disjunct_ro l dj`), `VerifyDef` (`dj_interp`, `path_sat_dj_at`,
  `path_sat_dj`, `dj_entails`; the uniform forms also quantify over
  `GoGlobalContext` and `HasLC`, like `triple_holds`), `MatchSound`
  (`match_rel`, `phase1_inv`, `undone`, `pure_ok`, `match_path_sat`), and
  `Fn/{hasPat, instantiate, findCell, condHolds, countPointsTo,
  firstUnresolved, matchTerm, matchAtom, matchPass, matchHeap, checkSorts,
  checkPure, checkDisjunct, anyDisjunct}` (`anyDisjunct` defines
  `is_disjuncts_ro`). All build, no `sorry`, no axioms beyond the usual three.
* Iris has a global three-way notation `a || b || c` (disjointness), so a
  Boolean chain `x || y || z` fails with "failed to synthesize Disjoint
  Bool": parenthesise, `(x || y) || z`. A binary `x || y` is fine.
* The pure mirrors of the match chain (`has_pat`, `is_tpat`, `instantiate_t`,
  `cond_holds`, `find_cell`, `count_pts`, ...) are all outside the proof
  sections, so `MatchSound.lean` reuses `has_pat_node` and `term_eq_iff`
  directly (Rocq re-proved them). `is_tpat`/`is_tpat_code` live in
  `Fn/hasPat.lean` only (Rocq has a copy in instantiate.v too; one Lean
  namespace cannot hold both).
* Kind-code facts `decide (term_code x = W64 2) = is_tpat x`: `cases x <;>
  simp only [term_code, is_tpat] <;> (try split) <;> rfl` (`decide` complains
  about the free variables of the constructor arguments; `rfl` evaluates).
* `rw [Bool.true_or]` rewrites only the instances matching the first
  unification; use `simp only [Bool.true_or, Bool.false_or]` on the goal
  (which includes the Iris context, so `HΦ`'s postcondition gets simplified
  too).
* A Go function with its own local `i` *and* a `range` loop: `wp_auto`
  allocates both, the Go counter becomes inaccessible; `rename_i gi_ptr`
  (exactly one name: `rename_i` names the *last* inaccessible hypotheses,
  and two names would grab an instance) then `irename: gi_ptr ↦ (W64 0) => gi`
  (`Fn/findCell.lean`, `Fn/firstUnresolved.lean`).
* The Go local `at` is a Lean keyword: name its points-to `"Hat"` in a loop
  invariant (`wp_auto` finds it anyway) and write `«at»` in `$$ [...]`.
* `wp_apply` of a callee whose postcondition is followed by a `let "$r0" :=
  &T{…}` already allocates it as `«$r0_ptr»`/`«$r0»` (no `wp_alloc`);
  `ipersist «$r0»` (`Fn/checkSorts.lean`).
* `is_sortenv DFrac.discard l E` has no `Persistent` instance in Nodes.lean;
  `Fn/checkSorts.lean` declares `is_sortenv_discard_persistent`.
* A big existential over a seven-fold `∗` (`is_disjunct_ro`) exceeds the
  default `synthInstance.maxSize` when proving `Persistent`; raise it locally.
* `σ !! n` on a `List (Option term)` needs the binder types written:
  `∀ (n : Nat) (y : term), σ[n]? = some (some y) → …` (otherwise "typeclass
  instance problem is stuck: GetElem?").
* `is_disjunct_ro_open` (Fn/matchTerm.lean) unfolds `is_disjunct_ro` in one
  hypothesis: `icases is_disjunct_ro_open _ _ $$ Hdj with ⟨%sp, %sok, %sa,
  %lf, %las, #Hld, …⟩`. A global `unfold is_disjunct_ro` (or `unfold
  is_path is_state`) also rewrites `HΦ` and the Löb hypothesis; after that,
  give a folded `Hpath` back to the unfolded `HΦ` with `isplitl [Hpath]; ·
  unfold is_path is_state; iexact Hpath` (`iframe Hpath` fails).
* After `wp_if_destruct` the pure hypotheses of an earlier one are shadowed
  (all named `Hif`); save loop-bound facts first if `word` needs them later.
* `&Failure{…}` returns: after `wp_auto` the literal is a value, `wp_alloc lf
  as Hf` works, and `ihave %Hnn := typedPointsto_not_null $$ Hf` discharges
  the `lf = null → …` postcondition.
* `wp_store_slice_index sl i vs v' $$ [Hs] as Hs` gives `sl ↦* vs.set
  i.toNat v'`; `(sint.Z k).toNat` and `sint.nat k` are interchangeable by
  `change`.
* No Mathlib: `swap`, `tauto`, `match goal` are unavailable (`rotate_left`
  works); for pure lemmas about `Option`-valued mirrors prefer `simp_all`
  with small `isSome` lemmas (`tbind2_isSome` in Fn/instantiate.lean) over
  hand-written destructuring.
