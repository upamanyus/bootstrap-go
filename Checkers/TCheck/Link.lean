/-
Port of `new/tcheck/link.v`.

# Proving a table's rules valid

A rule's validity, `rule_valid DA r`, computes to the Hoare triple it stands
for, in the form `{{ P }} e {{ x .. y, RET v; Q }}` unfolds to.  So most
links are a lemma's name: `rule_valid raft_den raft_rule_store_step` *is*
`raft.wp_store_step`'s statement up to unfolding (definitional equality),
and `theorem … := raft.wp_store_step` is the whole proof.  A rule proved by
hand (a pure step, a slice literal) starts with `rule_start`, which
introduces the rule's variables and computes the triple, unfolding the
checker's denotation (this library) and the table's own definitions but not
the Lean the table's denotation maps symbols to, so the goal ends up stated
in the vocabulary of the program logic.

Lean notes:
* Links to lemmas are terms, checked by unfolding (Rocq needed `rule_start`
  before `apply`); `rule_start` is only for rules proved by hand.
* Rocq's `tc_simp` (a `lazy` with an explicit delta list) is `tc_simp` here:
  `whnf` everywhere under an unfolding predicate that admits exactly that list
  (`tcUnfoldBase`), the table's definitions and the `match`es they compile to
  (`tcReducePass`). `simp only`/`dsimp only` with the same definitions do not
  work: their (reducible) unification cannot see through the dependent types
  of a denotation (`nat_cast`'s argument has type `srt_den ds (SU 1)`, not
  `Loc`), and `simp only` timed out.
* Rocq's `forall_by`/`table_valid_by`/`preds_persistent` are not needed: a
  concrete `table_valid` is an anonymous constructor of the rules' lemmas
  (`Forall` is a recursive conjunction), and the persistence obligations are
  one of the instances.
* With the ambient fixed by the context (`Denote.lean`), `rule_start`
  introduces only the rule's variables, and `call_ok_by` none; `call_ok_by`
  is the premise of a lemma `call_ok_of` (Rocq rewrote with `Hfv` inside the
  tactic).
* `rule_pure` uses `wp_auto` (Rocq `wp_pures`): a struct field reference or a
  method resolution is a `wp_auto` step here.
-/
import Checkers.TCheck.Observe

noncomputable section

namespace Perennial
namespace TCheck

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

open Lean Meta Elab Tactic in
/-- The checker's definitions `tc_simp` unfolds (Rocq: `tc_simp`'s delta list),
the few library functions they compute with, and what reducing a `match` on
a numeral needs (as Lean's `canUnfoldAtMatcher`). -/
def tcUnfoldBase : List Name :=
  [``rule_valid, ``fact_valid, ``preds_valid, ``spec_valid, ``table_valid, ``forall_sorts,
   ``bi_forall_sorts, ``triple_at, ``val_den, ``type_den, ``as_val, ``teval, ``tevals, ``vals_of,
   ``sym_apply, ``cast, ``nat_cast, ``atom_den, ``assn_den, ``pat_den, ``lookup_sym, ``lookup_pred,
   ``nth_error, ``vapp, ``pers_obl, ``pers_ok, ``srt_den, ``arrows, ``sym_ty, ``pred_ty,
   ``apply_vals, ``spec_rule, ``call_pat, ``func_val, ``cexpr_den, ``lit_den, ``lams, ``dyn,
   ``Forall, ``DenAt.d_sort, ``DenAt.d_sym, ``DenAt.d_pred,
   ``trule.r_vars, ``trule.r_lhs, ``trule.r_pre, ``trule.r_ex, ``trule.r_ret, ``trule.r_post,
   ``tfact.f_vars, ``tfact.f_lhs, ``tfact.f_rhs, ``tspec.sp_vars, ``tspec.sp_args,
   ``tspec.sp_pre, ``tspec.sp_ex, ``tspec.sp_ret, ``tspec.sp_post, ``symdecl.sd_args,
   ``symdecl.sd_res, ``preddecl.pd_pers, ``preddecl.pd_args,
   ``List.foldl, ``List.map, ``List.tail,
   ``OfNat.ofNat, ``instOfNatNat, ``Nat.beq, ``dite, ``ite, ``decEq, ``Nat.decEq, ``instDecidableEqNat]

open Lean Meta in
/-- One pass of `tc_simp`: `whnf` everywhere (every argument of an
application, binder types and bodies), under whatever unfolding predicate is
in effect. -/
partial def tcReducePass (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args ← e.getAppArgs.mapM tcReducePass
    return mkAppN f args
  | .lam n t b bi =>
    let t ← tcReducePass t
    withLocalDecl n bi t fun x => do mkLambdaFVars #[x] (← tcReducePass (b.instantiate1 x))
  | .forallE n t b bi =>
    let t ← tcReducePass t
    withLocalDecl n bi t fun x => do mkForallFVars #[x] (← tcReducePass (b.instantiate1 x))
  | .proj n i s => return mkProj n i (← tcReducePass s)
  | .mdata _ b => tcReducePass b
  | _ => return e

/-- Unfold the checker's denotation, and the definitions `xs` (the table's), in
the goal, and nothing else: Rocq's `lazy beta iota zeta delta [..]`. The Lean
that symbols and predicates denote (`ownRaftPhys`, `#`, `∗`, `WP`) is left
alone, so the goal ends up stated in the vocabulary of the program logic.
Implemented as `whnf` everywhere under a `whnf` that may unfold only these
constants and matchers, repeated until nothing changes (a `match` whose
discriminant one pass reduces is reduced by the next). -/
syntax "tc_simp" ("[" ident,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| tc_simp $[[ $xs,* ]]?) => do
  let xs : Array Ident := match xs with
    | some xs => xs.getElems
    | none => #[]
  let extra ← xs.mapM fun x => realizeGlobalConstNoOverloadWithInfo x
  let names : NameSet := (tcUnfoldBase ++ extra.toList).foldl (·.insert ·) {}
  let pred : Meta.Config → ConstantInfo → CoreM Bool := fun _ info => do
    -- the auxiliary definitions of a definition (its `_sparseCasesOn_n`, `match_n`)
    if names.contains info.name || names.contains info.name.getPrefix then return true
    return (Lean.Meta.Match.Extension.getMatcherInfo? (← getEnv) info.name).isSome
  liftMetaTactic1 fun g => withCanUnfoldPred pred do
    let mut t ← instantiateMVars (← g.getType)
    for _ in [0:64] do
      let t' ← tcReducePass t
      if t' == t then break
      t := t'
    g.replaceTargetDefEq t

/-- Introduce the rule's variables and compute the triple; `xs` are the
table's definitions to unfold. -/
syntax "rule_start" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| rule_start $[[ $xs,* ]]?) => do
    let xs : Array Lean.Ident := match xs with
      | some xs => xs.getElems
      | none => #[]
    `(tactic| (tc_simp [$xs,*]; intros))

/-- A pure step, by `wp_auto` (Rocq `rule_pure`, by `wp_pures`). -/
macro "rule_pure" : tactic =>
  `(tactic| (iintro %Φ - HΦ; wp_auto; iapply HΦ; itrivial))

section call
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## Specifications as rules

`spec_rule_valid`: the observed specification of a function (about
`func_val f` applied to its arguments) gives the rule callers use (about
the call `h a1 .. an`, `h` the method value).  Proved once, with the
function's body abstract: the only per-function obligation is that `h`
is the method value and that the method unfolds to `func_val f`. -/

theorem apply_vals_fill (args : List val) (e : Expr) :
    args.foldl (fun e v => App e (Val v)) e = fill (args.map EctxItem.AppLCtx) e := by
  induction args generalizing e with
  | nil => rfl
  | cons v args ih => exact ih (App e (Val v))

theorem wp_method_call_vals (T : go.GoType) (m : GoString) (impl : val) [MethodUnfold T m impl]
    (recv a : val) (rest : List val) (Φ : val → IProp GF) :
    WP (apply_vals impl (recv :: a :: rest)) {{ Φ }} ⊢
    WP (apply_vals #(methods T m recv) (a :: rest)) {{ Φ }} := by
  simp only [apply_vals, List.foldl_cons]
  rw [apply_vals_fill, apply_vals_fill, MethodUnfold.method_unfold]
  refine tac_wp_pure_wp' (K := rest.map EctxItem.AppLCtx)
    (Hwp := wp_call a BAnon (BNamed "arg1") _) trivial later_intro ?_ .rfl
  simp [subst', subst]

variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

theorem pat_den_call_pat (θ : List (dyn DA)) (p0 : tpat) (args : List tterm) :
    pat_den DA θ (args.foldl (fun p a => PApp p (PVal a)) p0) =
    (args.map (val_den DA θ)).foldl (fun e v => App e (Val v)) (pat_den DA θ p0) := by
  induction args generalizing p0 with
  | nil => rfl
  | cons a args ih => exact ih (PApp p0 (PVal a))

theorem forall_sorts_mono2 (ss : List srt) (P R Q : List (dyn DA) → Prop) :
    (∀ θ, P θ → R θ → Q θ) → forall_sorts DA ss P → forall_sorts DA ss R → forall_sorts DA ss Q := by
  induction ss generalizing P R Q with
  | nil => intro h; exact h []
  | cons s ss ih =>
    intro h hP hR x
    exact ih (fun θ => P (⟨s, x⟩ :: θ)) (fun θ => R (⟨s, x⟩ :: θ)) (fun θ => Q (⟨s, x⟩ :: θ))
      (fun θ => h _) (hP x) (hR x)

/-- A triple for `e1` is one for `e2` if `e2`'s WP follows from `e1`'s. -/
theorem triple_at_mono (θ : List (dyn DA)) (pre : List tatom) (e1 e2 : Expr) (ex : List srt)
    (ret : tterm) (post : List tatom) (H : ∀ Φ : val → IProp GF, WP e1 {{ Φ }} ⊢ WP e2 {{ Φ }}) :
    triple_at DA θ pre e1 ex ret post → triple_at DA θ pre e2 ex ret post := by
  intro Ht
  unfold triple_at at *
  iintro %Φ Hpre Hpost
  iapply H Φ
  iapply Ht $$ %Φ Hpre Hpost

/-- The per-function obligation of `spec_rule_valid`: at every valuation,
the arguments are a receiver and at least one more value, `h` is the
method value of the receiver, and the method unfolds to the checked
function. -/
def call_ok (f : cfunc) (sp : tspec) (h : tterm) : Prop :=
  forall_sorts DA sp.sp_vars (fun θ =>
    ∃ (T : go.GoType) (m : GoString) (recv a : val) (rest : List val),
      sp.sp_args.map (val_den DA θ) = recv :: a :: rest ∧
      val_den DA θ h = #(methods T m recv) ∧ MethodUnfold T m (func_val DA f))

theorem spec_rule_valid (f : cfunc) (sp : tspec) (h : tterm) :
    spec_valid DA f sp → call_ok DA f sp h → rule_valid DA (spec_rule h sp) := by
  intro Hspec Hcall
  unfold spec_valid at Hspec
  unfold call_ok at Hcall
  unfold rule_valid spec_rule
  revert Hspec Hcall
  apply forall_sorts_mono2
  intro θ Htr ⟨T, m, recv, a, rest, Hargs, Hh, Hunf⟩
  refine triple_at_mono DA θ _ _ _ _ _ _ ?_ Htr
  intro Φ
  simp only [call_pat]
  rw [pat_den_call_pat]
  simp only [pat_den]
  rw [Hh]
  cases hargs : sp.sp_args with
  | nil => rw [hargs] at Hargs; cases Hargs
  | cons a0 args =>
    rw [hargs] at Hargs
    simp only [List.map_cons, List.cons.injEq] at Hargs
    obtain ⟨Hrecv, Hargs⟩ := Hargs
    simp only [List.tail_cons, List.map_cons, Hrecv, Hargs]
    exact wp_method_call_vals T m (func_val DA f) recv a rest Φ

/-- `call_ok DA f sp h`, given `Hfv : func_val DA f = impl`: rewrite the
function before anything is computed (so that the table's denotation is
never normalized inside it); what is left, at every valuation, is found by
unification (`rfl`) and instance search. -/
theorem call_ok_of (f : cfunc) (sp : tspec) (h : tterm) (impl : val) (Hfv : func_val DA f = impl)
    (H : forall_sorts DA sp.sp_vars (fun θ =>
      ∃ (T : go.GoType) (m : GoString) (recv a : val) (rest : List val),
        sp.sp_args.map (val_den DA θ) = recv :: a :: rest ∧
        val_den DA θ h = #(methods T m recv) ∧ MethodUnfold T m impl)) :
    call_ok DA f sp h := by
  unfold call_ok; rw [Hfv]; exact H

end call

/-- Discharge the premise of `call_ok_of` at every valuation: introduce the
specification's variables and solve the existential by unification and
instance search. -/
macro "call_ok_by" : tactic =>
  `(tactic| (repeat intro
             exact ⟨_, _, _, _, _, rfl, rfl, inferInstance⟩))

end TCheck
end Perennial
