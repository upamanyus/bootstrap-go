/-
Port of `new/checker/exec_spec.v`.

What a result of `exec` means.

`exec` returns one `Path` per feasible execution of the expression. The
list is a *disjunction*: the program ends in some one of them. This file
says that precisely (`exec_sound`) and proves the structural facts about
it that every case of the exec proof needs -- above all that soundness is
closed under concatenating result lists, which is what the loops in
checker/exec.go build.

The statement comes in two layers. `exec_sound_at` is about the ambient
`HeapGS hlc GF`, that is, about one particular choice of ghost state (and FFI
and Go semantics); the lemmas of the section are proved about it.
`exec_sound`, at the end, quantifies it over every FFI, every `HeapGS`
and every Go semantics, and the lemmas are lifted to it under their plain
names; it is what the specifications of the checker's functions promise.
The lemmas about `exec_sound_at` do not assume `checker.Assumptions`: they
are about the analysed program, not about the checker's code.
The quantification is what lets a `true` answer survive adequacy
(new/checker/adequacy.v): adequacy runs the checker in ghost state it
allocates itself, and what it hands back must be a fact about the
function under analysis in any ghost state.

Lean notes:
* Rocq's `⊢ heap_interp V H -∗ WP …` is the entailment
  `heap_interp V H ⊢ WP …` (equivalent).
* `exec_sound` also quantifies over `GoGlobalContext` and `HasLC` (as
  `triple_holds` in `Defs.lean`: in Rocq the former came with `heapGS`, the
  latter does not exist).
* Rocq's `exec_lift` tactic is replaced by writing each lifted proof as a
  term (`fun ext ffi … => exec_sound_at_X (GF := GF) … (H ext ffi …)`).
* The proofs of the compound cases share two helpers that Rocq inlines in
  each case: `exec_bind` (run the subexpression under an evaluation context
  and continue from each of its paths) and `exec_run` (run a continuation's
  sound result list and weaken its postcondition to the caller's). They
  are extra lemmas; no statement changed.
* `wp_ctype_{load,store,alloc}_any` are stated, like `Steps.lean`'s
  `wp_ctype_*`, on the instruction applied to a value
  (`App (Val (GoInstruction (GoLoad (type_of t)))) (Val #lo)` for Rocq's
  `![type_of cty] #lo`).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Fn.heapLookup
import Checkers.Checker.Fn.heapUpdate

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

/-! ## Pure parts -/

/-- The two states `execIf` forks into. -/
def st_assume (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst) (spc sst ++ [x]) (svars sst)

/-- The state `exec` forks to on an allocation. -/
def st_alloc (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst ++ [mkCell (TVar (svars sst).length) x])
          (spc sst)
          (svars sst ++ [SLoc])

section pure
variable [ext : FfiSyntax]

/-- A term the environment binds is scoped by the state's variables. -/
theorem env_below_lookup (k : Nat) (ρ : List (GoString × term)) (gx : GoString) (x : term) :
    env_below k ρ → env_lookup ρ gx = some x → vars_below k x := by
  induction ρ with
  | nil => intro _ H; cases H
  | cons yt ρ ih =>
    obtain ⟨gy, y⟩ := yt
    intro Hb Hlk
    simp only [env_lookup] at Hlk
    split at Hlk
    · cases Hlk; exact Hb _ (List.mem_cons_self ..)
    · exact ih (fun xt Hxt => Hb xt (List.mem_cons_of_mem _ Hxt)) Hlk

theorem wf_state_assume (sst : sstate) (x : term) :
    wf_state sst → vars_below (svars sst).length x → wf_state (st_assume sst x) := by
  intro ⟨Hh, Hpc⟩ Hx
  refine ⟨Hh, ?_⟩
  intro y Hy
  rcases List.mem_append.mp Hy with Hy | Hy
  · exact Hpc y Hy
  · rw [List.mem_singleton.mp Hy]; exact Hx

theorem wf_state_alloc (sst : sstate) (x : term) :
    wf_state sst → vars_below (svars sst).length x → wf_state (st_alloc sst x) := by
  intro ⟨Hh, Hpc⟩ Hx
  have Hlen : (svars (st_alloc sst x)).length = (svars sst).length + 1 := by
    simp [st_alloc]
  refine ⟨?_, ?_⟩
  · rw [Hlen]
    intro c Hc
    simp only [st_alloc] at Hc
    rcases List.mem_append.mp Hc with Hc | Hc
    · obtain ⟨H1, H2⟩ := Hh c Hc
      exact ⟨vars_below_mono _ _ _ (by omega) H1, vars_below_mono _ _ _ (by omega) H2⟩
    · rw [List.mem_singleton.mp Hc]
      refine ⟨?_, vars_below_mono _ _ _ (by omega) Hx⟩
      simp only [vars_below]; omega
  · rw [Hlen]
    intro y Hy
    exact vars_below_mono _ _ _ (by omega) (Hpc y Hy)

theorem st_sat_assume (V : valuation) (sst : sstate) (x : term) :
    st_sat V sst → teval V x = bval true → st_sat V (st_assume sst x) := by
  intro ⟨Hv, Hpc⟩ Hx
  exact ⟨Hv, pc_sat_snoc V _ _ Hpc Hx⟩

/-- Extending a valuation at one logical variable. -/
def upd_var (V : valuation) (n : Nat) (v : val) : valuation :=
  mkVal (fun m => if m = n then v else vvar V m) (vpat V) (vret V)

theorem agree_below_upd_var (k : Nat) (V : valuation) (n : Nat) (v : val) :
    k ≤ n → agree_below k V (upd_var V n v) := by
  intro Hle
  refine ⟨?_, rfl, rfl⟩
  intro m Hm
  simp only [upd_var]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

theorem upd_var_here (V : valuation) (n : Nat) (v : val) : vvar (upd_var V n v) n = v := by
  simp [upd_var]

theorem teval_upd_var_here (V : valuation) (n : Nat) (v : val) :
    teval (upd_var V n v) (TVar n) = v := by
  simp [teval, upd_var]

theorem upd_var_other (V : valuation) (n m : Nat) (v : val) :
    m ≠ n → vvar (upd_var V n v) m = vvar V m := by
  intro H; simp [upd_var, H]

theorem st_sat_alloc (V : valuation) (sst : sstate) (x : term) (lo : Loc) :
    wf_state sst → st_sat V sst →
    st_sat (upd_var V (svars sst).length (lval lo)) (st_alloc sst x) := by
  intro Hwf ⟨Hv, Hpc⟩
  refine ⟨?_, ?_⟩
  · intro m sg Hsv
    simp only [st_alloc] at Hsv
    by_cases Heqm : m = (svars sst).length
    · subst Heqm
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at Hsv
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hsv
      subst Hsv
      rw [upd_var_here]
      exact ⟨lo, rfl⟩
    · rw [upd_var_other _ _ _ _ Heqm]
      apply Hv
      have Hlt : m < (svars sst).length := by
        have := (List.getElem?_eq_some_iff.mp Hsv).1
        simp at this; omega
      rwa [List.getElem?_append_left Hlt] at Hsv
  · exact pc_sat_agree _ V _ _ (agree_below_upd_var _ V _ _ (Nat.le_refl _)) Hwf.wf_pc Hpc

end pure

section exec_spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The environment the checker carries stands for a substitution; `csubst`
applies it, so the analysed program is `csubst (env_interp V ρ) ce`. -/
def exec_sound_at (ce : cexpr) (ρ : List (GoString × term))
    (sst : sstate) (ps : List spath) : Prop :=
  wf_state sst →
  env_below (svars sst).length ρ →
  ∀ V, st_sat V sst →
    heap_interp (GF := GF) V (sheap sst) ⊢
      WP (csubst (env_interp V ρ) ce) {{ paths_post (svars sst).length V ps }}

/-! ## Structure

A result list is a disjunction, so more paths is a weaker claim: this is
what lets a case of `exec` concatenate the results of its subcases. -/

theorem exec_sound_at_mono (ce : cexpr) ρ sst (ps ps' : List spath) :
    ps ⊆ ps' → exec_sound_at (GF := GF) ce ρ sst ps → exec_sound_at (GF := GF) ce ρ sst ps' := by
  intro Hsub Hs Hwf Hρ V Hsat
  refine (Hs Hwf Hρ V Hsat).trans (wp_mono fun w => ?_)
  exact paths_post_mono _ V ps ps' w Hsub

/-- The loops in checker/exec.go build their answer by appending the results
of the subcases; each contributes its own paths and the caller's choice is
the union. -/
theorem exec_sound_at_app_l (ce : cexpr) ρ sst (ps ps' : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps → exec_sound_at (GF := GF) ce ρ sst (ps ++ ps') :=
  exec_sound_at_mono ce ρ sst _ _ (fun _ h => List.mem_append_left _ h)

theorem exec_sound_at_app_r (ce : cexpr) ρ sst (ps ps' : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps' → exec_sound_at (GF := GF) ce ρ sst (ps ++ ps') :=
  exec_sound_at_mono ce ρ sst _ _ (fun _ h => List.mem_append_right _ h)

/-! ## The value cases

An expression that neither forks nor touches the heap produces the single
path `onePath` builds. -/

theorem exec_sound_at_value (ce : cexpr) ρ sst (x : term) :
    (∀ V, csubst (env_interp V ρ) ce = Val (teval V x)) →
    vars_below (svars sst).length x →
    exec_sound_at (GF := GF) ce ρ sst [mkPath x sst] := by
  intro Hval _ _ _ V Hsat
  rw [Hval]
  iintro Hheap
  iapply wp_value'
  unfold paths_post
  iexists mkPath x sst, V
  iframe Hheap
  ipureintro
  exact ⟨List.mem_singleton_self _, agree_below_refl _ V, rfl, Hsat⟩

/-- The cases of `exec` that neither fork nor touch the heap. -/
theorem exec_sound_at_int (ρ : List (GoString × term)) sst (w : w64) :
    exec_sound_at (GF := GF) (CEInt w) ρ sst [mkPath (TInt w) sst] :=
  exec_sound_at_value _ _ _ _ (fun V => by simp only [csubst, teval]; rw [ival_eq]) trivial

theorem exec_sound_at_bool (ρ : List (GoString × term)) sst (b : Bool) :
    exec_sound_at (GF := GF) (CEBool b) ρ sst [mkPath (TBool b) sst] :=
  exec_sound_at_value _ _ _ _ (fun V => by simp only [csubst, teval]; rw [bval_eq]) trivial

theorem exec_sound_at_unit (ρ : List (GoString × term)) sst :
    exec_sound_at (GF := GF) CEUnit ρ sst [mkPath TUnit sst] :=
  exec_sound_at_value _ _ _ _ (fun V => by simp only [csubst, teval]; rw [uval_eq]) trivial

theorem exec_sound_at_var (ρ : List (GoString × term)) sst (gx : GoString) (x : term) :
    env_lookup ρ gx = some x →
    vars_below (svars sst).length x →
    exec_sound_at (GF := GF) (CEVar gx) ρ sst [mkPath x sst] := by
  intro Hlk Hb
  refine exec_sound_at_value _ _ _ _ (fun V => ?_) Hb
  simp only [csubst]
  rw [env_interp_lookup, Hlk]
  rfl

/-- `GoZeroVal` does not touch the heap either, but its value depends on the
type rather than on the environment. -/
theorem exec_sound_at_zero (ρ : List (GoString × term)) sst (cty : ctype) :
    exec_sound_at (GF := GF) (CEZero cty) ρ sst [mkPath (ctype_zero cty) sst] := by
  intro _ _ V Hsat
  simp only [csubst]
  iintro Hheap
  iapply wp_ctype_zero cty V
  unfold paths_post
  iexists mkPath (ctype_zero cty) sst, V
  iframe Hheap
  ipureintro
  exact ⟨List.mem_singleton_self _, agree_below_refl _ V, rfl, Hsat⟩

/-! ## Composing sound result lists

Every compound case of `exec` runs a subexpression, then continues from
each of its paths. The valuation may grow (an allocation introduces a
fresh logical variable), so the continuation's paths are stated over a
valuation that only agrees with the caller's below the caller's number of
variables -- which is exactly what `paths_post` records. -/

theorem paths_post_compose (k k' : Nat) (V V' : valuation) (qs : List spath) (v : val) :
    k ≤ k' → agree_below k V V' →
    paths_post (GF := GF) k' V' qs v ⊢ paths_post k V qs v := by
  intro Hle Hag
  unfold paths_post
  iintro ⟨%q, %V'', %Hin, %Hag', %Hret, %Hsat, Hheap⟩
  iexists q, V''
  iframe Hheap
  ipureintro
  exact ⟨Hin, agree_below_trans _ _ _ _ Hag (agree_below_weaken _ _ _ _ Hle Hag'), Hret, Hsat⟩

/-- An environment whose terms are all scoped by the caller's variables means
the same thing under any valuation that agrees that far. -/
theorem env_interp_agree (k : Nat) (V V' : valuation) (ρ : List (GoString × term)) :
    agree_below k V V' → env_below k ρ → env_interp V ρ = env_interp V' ρ := by
  intro Hag Hb
  induction ρ with
  | nil => rfl
  | cons yt ρ ih =>
    obtain ⟨gy, y⟩ := yt
    rw [env_interp_bind, env_interp_bind,
      teval_agree k V V' y Hag (Hb (gy, y) (List.mem_cons_self ..)),
      ih (fun xt Hxt => Hb xt (List.mem_cons_of_mem _ Hxt))]

theorem fill_singleton (Ki : EctxItem) (e : Expr) : fill [Ki] e = fillItem Ki e := rfl

/-- Lean addition: run a subexpression in an evaluation context `K` and
continue from each of its paths (the first half of every compound case in
Rocq). -/
theorem exec_bind (K : List EctxItem) (ce : cexpr) ρ sst (ps : List spath) (V : valuation)
    (Ψ : val → IProp GF) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    wf_state sst → env_below (svars sst).length ρ → st_sat V sst →
    (∀ p V', p ∈ ps → agree_below (svars sst).length V V' → st_sat V' (pst p) →
      heap_interp (GF := GF) V' (sheap (pst p)) ⊢ WP (fill K (Val (teval V' (pret p)))) {{ Ψ }}) →
    heap_interp (GF := GF) V (sheap sst) ⊢ WP (fill K (csubst (env_interp V ρ) ce)) {{ Ψ }} := by
  intro He Hwf Hρ Hsat Hk
  iintro Hheap
  iapply wp_bind (fill K)
  iapply wp_wand $$ [Hheap]
  · iapply He Hwf Hρ V Hsat
    iexact Hheap
  · iintro %w Hw
    unfold paths_post
    icases Hw with ⟨%p, %V', %Hin, %Hag, %Hret, %Hsat', Hheap'⟩
    rw [Hret]
    iapply Hk p V' Hin Hag Hsat'
    iexact Hheap'

/-- Lean addition: run a continuation whose result list is sound and contained
in the caller's, from a state with at least the caller's variables (the
second half of every compound case in Rocq). -/
theorem exec_run (ce : cexpr) ρ' (st : sstate) (qs out : List spath) (k : Nat)
    (V V' : valuation) :
    exec_sound_at (GF := GF) ce ρ' st qs →
    wf_state st → env_below (svars st).length ρ' → st_sat V' st →
    qs ⊆ out → k ≤ (svars st).length → agree_below k V V' →
    heap_interp (GF := GF) V' (sheap st) ⊢
      WP (csubst (env_interp V' ρ') ce) {{ paths_post k V out }} := by
  intro Hqs Hwf Hρ Hsat Hsub Hle Hag
  refine (Hqs Hwf Hρ V' Hsat).trans (wp_mono fun u => ?_)
  exact (paths_post_compose k _ V V' qs u Hle Hag).trans (paths_post_mono k V qs out u Hsub)

/-! ## `let`

`exec` evaluates the bound expression, then continues from each of its
paths with the name bound to that path's return term. The GooseLang term
binds the name with a beta step, so the two meet at `csubst_insert`. -/

theorem wp_beta_rec_expr (gx : String) (B : Expr) (v : val) (Ψ : val → IProp GF) :
    WP (subst gx v B) {{ Ψ }} ⊢ WP (App (Rec BAnon (BNamed gx) B) (Val v)) {{ Ψ }} := by
  iintro H
  wp_pure
  wp_pure
  iexact H

/-- The argument of an application is evaluated first, which is the order
`exec` uses too. -/
theorem wp_let_bind (gx : String) (B e1 : Expr) (Φ : val → IProp GF) :
    WP e1 {{ w, WP (subst gx w B) {{ Φ }} }} ⊢
    WP (App (Rec BAnon (BNamed gx) B) e1) {{ Φ }} := by
  iintro H
  rw [show App (Rec BAnon (BNamed gx) B) e1 = fill [EctxItem.AppRCtx (Rec BAnon (BNamed gx) B)] e1
    from rfl]
  iapply wp_bind (fill [EctxItem.AppRCtx (Rec BAnon (BNamed gx) B)])
  iapply wp_wand $$ [H]
  · iexact H
  · iintro %w Hw
    rw [fill_singleton]; simp only [fillItem]
    iapply wp_beta_rec_expr
    iexact Hw

theorem exec_sound_at_let (gx : GoString) (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at (GF := GF) ce2 ((gx, pret p) :: ρ) (pst p) qs) →
    exec_sound_at (GF := GF) (CELet gx ce1 ce2) ρ sst out := by
  intro He1 Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce1 ρ sst ps V _ He1 Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  obtain ⟨qs, Hsub, Hqs⟩ := Hcont p Hin
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbp : env_below (svars (pst p)).length ((gx, pret p) :: ρ) :=
    env_below_cons _ _ _ _ (Hwfps.paths_wf_ret p Hin) (env_below_mono _ _ _ Hgrow Hρ)
  refine (exec_run ce2 _ (pst p) qs out _ V V' Hqs Hwfp Hbp Hsat' Hsub Hgrow Hag).trans ?_
  rw [env_interp_bind, ← csubst_insert, env_interp_agree _ V V' ρ Hag Hρ]
  exact wp_beta_rec_expr _ _ _ _

/-! ## Sequencing

`ESeq` is `ELet` with an anonymous binder: the continuation runs in the
caller's environment. -/

theorem wp_beta_anon_expr (B : Expr) (v : val) (Ψ : val → IProp GF) :
    WP B {{ Ψ }} ⊢ WP (App (Rec BAnon BAnon B) (Val v)) {{ Ψ }} := by
  iintro H
  wp_pure
  wp_pure
  iexact H

theorem wp_seq_bind (B e1 : Expr) (Φ : val → IProp GF) :
    WP e1 {{ _w, WP B {{ Φ }} }} ⊢ WP (App (Rec BAnon BAnon B) e1) {{ Φ }} := by
  iintro H
  rw [show App (Rec BAnon BAnon B) e1 = fill [EctxItem.AppRCtx (Rec BAnon BAnon B)] e1 from rfl]
  iapply wp_bind (fill [EctxItem.AppRCtx (Rec BAnon BAnon B)])
  iapply wp_wand $$ [H]
  · iexact H
  · iintro %w Hw
    rw [fill_singleton]; simp only [fillItem]
    iapply wp_beta_anon_expr
    iexact Hw

theorem exec_sound_at_seq (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ exec_sound_at (GF := GF) ce2 ρ (pst p) qs) →
    exec_sound_at (GF := GF) (CESeq ce1 ce2) ρ sst out := by
  intro He1 Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce1 ρ sst ps V _ He1 Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  obtain ⟨qs, Hsub, Hqs⟩ := Hcont p Hin
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
  refine (exec_run ce2 _ (pst p) qs out _ V V' Hqs Hwfp Hbp Hsat' Hsub Hgrow Hag).trans ?_
  rw [env_interp_agree _ V V' ρ Hag Hρ]
  exact wp_beta_anon_expr _ _ _

/-! ## The exception monad

`teval` of `TExec`/`TRet` is exactly `executeVal`/`returnVal`, so these
cases are pure steps once the subexpression's path is in hand. -/

theorem exec_sound_at_do (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    (∀ p, p ∈ ps → mkPath TExec (pst p) ∈ out) →
    exec_sound_at (GF := GF) (CEDo ce) ρ sst out := by
  intro He Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  iintro Hheap'
  iapply wp_do
  unfold paths_post
  iexists mkPath TExec (pst p), V'
  iframe Hheap'
  ipureintro
  exact ⟨Hcont p Hin, Hag, rfl, Hsat'⟩

theorem exec_sound_at_return (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    (∀ p, p ∈ ps → mkPath (TRet (pret p)) (pst p) ∈ out) →
    exec_sound_at (GF := GF) (CEReturn ce) ρ sst out := by
  intro He Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  iintro Hheap'
  iapply wp_return
  unfold paths_post
  iexists mkPath (TRet (pret p)) (pst p), V'
  iframe Hheap'
  ipureintro
  exact ⟨Hcont p Hin, Hag, rfl, Hsat'⟩

/-- `exception_do` strips the label: an `execute` becomes `()` and a
`return v` becomes `v`. The checker case-splits on the *term*, which is
exactly what `teval` turns into the two monad values. -/
theorem exec_sound_at_exc_do (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    (∀ p, p ∈ ps →
       (pret p = TExec ∧ mkPath TUnit (pst p) ∈ out) ∨
       (∃ x, pret p = TRet x ∧ mkPath x (pst p) ∈ out)) →
    exec_sound_at (GF := GF) (CEExcDo ce) ρ sst out := by
  intro He Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  iintro Hheap'
  rcases Hcont p Hin with ⟨Hex, Hout⟩ | ⟨x, Hrx, Hout⟩
  · rw [Hex]; simp only [teval]
    iapply wp_exc_do_exec
    unfold paths_post
    iexists mkPath TUnit (pst p), V'
    iframe Hheap'
    ipureintro
    exact ⟨Hout, Hag, rfl, Hsat'⟩
  · rw [Hrx]; simp only [teval]
    iapply wp_exc_do_ret
    unfold paths_post
    iexists mkPath x (pst p), V'
    iframe Hheap'
    ipureintro
    exact ⟨Hout, Hag, rfl, Hsat'⟩

/-! ## `if`

The condition is boolean-sorted -- that is what `execIf` checks with
`SortOf` -- so it really evaluates to a boolean, and the branch taken is
determined by it. The checker explores both branches, recording the
condition on one and its negation on the other; a valuation satisfies at
most one of the two extended path conditions, which is why the two
branches can be analysed independently. -/

theorem wp_if_bval (b : Bool) (A B : Expr) (Ψ : val → IProp GF) :
    WP (if b then A else B) {{ Ψ }} ⊢ WP (If (Val (bval b)) A B) {{ Ψ }} := by
  iintro H
  rw [← bval_eq]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> wp_pure <;> iexact H

theorem exec_sound_at_if (cc ct cf : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) cc ρ sst ps →
    paths_wf (svars sst).length ps →
    -- the condition is boolean-sorted on every path
    (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = some SBool) →
    -- and each branch is analysed under the corresponding assumption
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at (GF := GF) ct ρ (st_assume (pst p) (pret p)) qs) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at (GF := GF) cf ρ (st_assume (pst p) (negate (pret p))) qs) →
    exec_sound_at (GF := GF) (CEIf cc ct cf) ρ sst out := by
  intro Hc Hwfps Hsort Hthen Helse Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.IfCtx _ _] cc ρ sst ps V _ Hc Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbret := Hwfps.paths_wf_ret p Hin
  have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
  -- the condition really is a boolean
  obtain ⟨b, Hb⟩ := sort_of_vars_sound V' _ _ _ Hsat'.1 (Hsort p Hin)
  rw [Hb, env_interp_agree _ V V' ρ Hag Hρ]
  refine Entails.trans ?_ (wp_if_bval b _ _ _)
  cases b
  · -- the `else` branch, with the negation recorded
    obtain ⟨qs, Hsub, Hqs⟩ := Helse p Hin
    exact exec_run cf ρ (st_assume (pst p) (negate (pret p))) qs out _ V V' Hqs
      (wf_state_assume _ _ Hwfp (vars_below_negate _ _ Hbret)) Hbp
      (st_sat_assume _ _ _ Hsat' (teval_negate V' (pret p) false Hb)) Hsub Hgrow Hag
  · -- the `then` branch, with the condition recorded
    obtain ⟨qs, Hsub, Hqs⟩ := Hthen p Hin
    exact exec_run ct ρ (st_assume (pst p) (pret p)) qs out _ V V' Hqs (wf_state_assume _ _ Hwfp Hbret) Hbp
      (st_sat_assume _ _ _ Hsat' Hb) Hsub Hgrow Hag

/-! ## Memory, without a sort constraint on the value

`Steps.lean` proves the load/store/alloc lemmas at a value of the type's
sort, which is the shape the operator cases need. The memory *cases of
exec* need less: the checker does not check that a stored or allocated
value has the type's sort, and it does not have to, because the GooseLang
step for a store does not look at the value at all. These are the
sort-free versions. -/

attribute [local instance] go.tagged_internal_inst

theorem wp_ctype_load_any (cty : ctype) (lo : Loc) (dq : DFrac) (v : val) :
    {{ heapPointsto (GF := GF) lo dq v }}
      (App (Val (GoInstruction (GoLoad (type_of cty)))) (Val #lo))
    {{ RET v; heapPointsto lo dq v }} := by
  iintro %Φ Hl HΦ
  cases cty <;> simp only [type_of] <;> wp_pures <;>
    wp_apply_core _internal_wp_untyped_read lo dq v $$ Hl <;>
    iintro Hl <;> iapply HΦ $$ Hl

theorem wp_ctype_store_any (cty : ctype) (lo : Loc) (v w : val) :
    {{ heapPointsto (GF := GF) lo (DFrac.own 1) v }}
      (App (Val (GoInstruction (GoStore (type_of cty)))) (Val (PairV #lo w)))
    {{ RET #(); heapPointsto lo (DFrac.own 1) w }} := by
  iintro %Φ Hl HΦ
  cases cty <;> simp only [type_of] <;> wp_pures <;>
    wp_apply_core _internal_wp_untyped_store lo v w $$ Hl <;>
    iintro Hl <;> iapply HΦ $$ Hl

theorem wp_ctype_alloc_any (cty : ctype) (v : val) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoAlloc (type_of cty)))) (Val v))
    {{ (l : Loc), RET #l; heapPointsto l (DFrac.own 1) v }} := by
  iintro %Φ _ HΦ
  cases cty <;> simp only [type_of] <;> wp_pures <;>
    wp_apply_core wp_alloc_untyped v <;>
    iintro %l Hl <;> iapply HΦ $$ Hl

/-! ## The heap cases

A symbolic cell is a real points-to, so a successful `heapLookup` hands
out the points-to the load needs, and a successful `heapUpdate` is the
frame-preserving update the store performs. -/

theorem heap_interp_lookup (V : valuation) (H : List scell) (x y : term) :
    heap_lookup H x = some y →
    heap_interp (GF := GF) V H ⊢
      ∃ lo : Loc, ⌜teval V x = lval lo⌝ ∗ heapPointsto lo (DFrac.own 1) (teval V y) ∗
        (heapPointsto lo (DFrac.own 1) (teval V y) -∗ heap_interp V H) := by
  induction H with
  | nil => intro h; cases h
  | cons c H ih =>
    simp only [heap_lookup]
    rw [(heap_interp_cons V c H).to_eq]
    split
    · rename_i Heq
      intro Hy
      cases Hy
      iintro ⟨⟨%lo, %Hl, Hp⟩, HH⟩
      iexists lo
      rw [Heq] at Hl
      iframe Hp
      isplitr
      · ipureintro; exact Hl
      iintro Hp
      iframe HH
      iexists lo
      iframe Hp
      ipureintro; rw [Heq]; exact Hl
    · intro Hlk
      iintro ⟨Hc, HH⟩
      icases ih Hlk $$ HH with ⟨%lo, %Hl, Hp, Hback⟩
      iexists lo
      iframe Hp
      isplitr
      · ipureintro; exact Hl
      iintro Hp
      iframe Hc
      iapply Hback $$ Hp

/-- Updating the first matching cell: the rest of the heap is untouched. -/
theorem heap_interp_update (V : valuation) (H H' : List scell) (x y : term) (lo : Loc) :
    heap_update H x y = some H' →
    teval V x = lval lo →
    heap_interp (GF := GF) V H ⊢
      ∃ z : term, heapPointsto lo (DFrac.own 1) (teval V z) ∗
        (heapPointsto lo (DFrac.own 1) (teval V y) -∗ heap_interp V H') := by
  induction H generalizing H' with
  | nil => intro h; cases h
  | cons c H ih =>
    simp only [heap_update]
    rw [(heap_interp_cons V c H).to_eq]
    split
    · rename_i Heq
      intro Hh Hx
      cases Hh
      iintro ⟨⟨%lo', %Hl, Hp⟩, HH⟩
      rw [Heq, Hx] at Hl
      obtain rfl : lo' = lo := (lval_inj _ _ Hl).symm
      iexists cval c
      iframe Hp
      iintro Hp
      rw [(heap_interp_cons V _ H).to_eq]
      iframe HH
      iexists lo'
      iframe Hp
      ipureintro; rw [Heq, Hx]
    · cases Hup : heap_update H x y with
      | none => intro h; cases h
      | some H'' =>
        intro Hh Hx
        cases Hh
        iintro ⟨Hc, HH⟩
        icases ih H'' Hup Hx $$ HH with ⟨%z, Hp, Hback⟩
        iexists z
        iframe Hp
        iintro Hp
        rw [(heap_interp_cons V c H'').to_eq]
        iframe Hc
        iapply Hback $$ Hp

/-! ## Load

`exec` requires a cell whose location term is *syntactically* the address,
which is what `heapLookup` finds; the value it holds is the result. -/
theorem exec_sound_at_load (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ y, heap_lookup (sheap (pst p)) (pret p) = some y ∧
                        mkPath y (pst p) ∈ out) →
    exec_sound_at (GF := GF) (CELoad cty ce) ρ sst out := by
  intro He _ Hcell Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  obtain ⟨y, Hlk, Hout⟩ := Hcell p Hin
  iintro Hheap'
  icases heap_interp_lookup V' _ _ _ Hlk $$ Hheap' with ⟨%lo, %Hl, Hp, Hback⟩
  rw [Hl, ← lval_eq]
  wp_apply wp_ctype_load_any cty lo (DFrac.own 1) (teval V' y) $$ Hp as Hp
  unfold paths_post
  iexists mkPath y (pst p), V'
  isplitr
  · ipureintro; exact Hout
  isplitr
  · ipureintro; exact Hag
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Hsat'
  iapply Hback $$ Hp

/-! ## Allocation

`exec` introduces a fresh logical variable for the new location: the
state's sort table grows by one `SLoc`, and the heap by a cell whose
location term is that variable. The valuation is extended to send the new
variable to the location GooseLang produced -- which is exactly the
freedom `paths_post` leaves, since the extension is at an index at or
above the caller's count. -/

theorem exec_sound_at_alloc (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps →
       mkPath (TVar (svars (pst p)).length) (st_alloc (pst p) (pret p)) ∈ out) →
    exec_sound_at (GF := GF) (CEAlloc cty ce) ρ sst out := by
  intro He Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbret := Hwfps.paths_wf_ret p Hin
  iintro Hheap'
  wp_apply wp_ctype_alloc_any cty (teval V' (pret p)) $$ [] as %lo Hp
  have Hag2 : agree_below (svars (pst p)).length V'
      (upd_var V' (svars (pst p)).length (lval lo)) :=
    agree_below_upd_var _ V' _ _ (Nat.le_refl _)
  unfold paths_post
  iexists mkPath (TVar (svars (pst p)).length) (st_alloc (pst p) (pret p)),
    upd_var V' (svars (pst p)).length (lval lo)
  isplitr
  · ipureintro; exact Hcont p Hin
  isplitr
  · ipureintro
    exact agree_below_trans _ _ _ _ Hag (agree_below_weaken _ _ _ _ Hgrow Hag2)
  isplitr
  · ipureintro; rw [lval_eq]; exact (teval_upd_var_here _ _ _).symm
  isplitr
  · ipureintro; exact st_sat_alloc _ _ _ _ Hwfp Hsat'
  -- the new cell, and the old heap under the extended valuation
  simp only [st_alloc]
  rw [(heap_interp_app _ _ _).to_eq]
  isplitl [Hheap']
  · rw [← (heap_interp_agree _ V' _ _ Hag2 Hwfp.wf_heap).to_eq]
    iexact Hheap'
  rw [(heap_interp_cons _ _ _).to_eq, (heap_interp_nil _).to_eq]
  isplitl
  · iexists lo
    rw [teval_upd_var_here, ← teval_agree _ V' _ (pret p) Hag2 Hbret]
    iframe Hp
    ipureintro; rfl
  · itrivial

end exec_spec

/-! ## The ghost-state-independent layer -/
def exec_sound (ce : cexpr) (ρ : List (GoString × term)) (sst : sstate) (ps : List spath) : Prop :=
  ∀ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_interp : FfiInterp ffi)
    (_ffi_sem : FfiSemantics ext ffi) (_go_gctx : GoGlobalContext)
    (hlc : HasLC) (GF : BundledGFunctors) (_hG : HeapGS hlc GF) (_sem : go.Semantics),
    exec_sound_at (GF := GF) ce ρ sst ps

section exec_uniform_lemmas

theorem exec_sound_mono (ce : cexpr) ρ sst (ps ps' : List spath) :
    ps ⊆ ps' → exec_sound ce ρ sst ps → exec_sound ce ρ sst ps' :=
  fun Hsub H ext ffi fi fs gc hlc GF hG sem => exec_sound_at_mono (GF := GF) _ _ _ _ _ Hsub (H ext ffi fi fs gc hlc GF hG sem)

theorem exec_sound_app_l (ce : cexpr) ρ sst (ps ps' : List spath) :
    exec_sound ce ρ sst ps → exec_sound ce ρ sst (ps ++ ps') :=
  fun H ext ffi fi fs gc hlc GF hG sem => exec_sound_at_app_l (GF := GF) _ _ _ _ _ (H ext ffi fi fs gc hlc GF hG sem)

theorem exec_sound_app_r (ce : cexpr) ρ sst (ps ps' : List spath) :
    exec_sound ce ρ sst ps' → exec_sound ce ρ sst (ps ++ ps') :=
  fun H ext ffi fi fs gc hlc GF hG sem => exec_sound_at_app_r (GF := GF) _ _ _ _ _ (H ext ffi fi fs gc hlc GF hG sem)

theorem exec_sound_int (ρ : List (GoString × term)) sst (w : w64) :
    exec_sound (CEInt w) ρ sst [mkPath (TInt w) sst] :=
  fun ext ffi fi fs gc hlc GF hG sem => exec_sound_at_int (GF := GF) _ _ _

theorem exec_sound_bool (ρ : List (GoString × term)) sst (b : Bool) :
    exec_sound (CEBool b) ρ sst [mkPath (TBool b) sst] :=
  fun ext ffi fi fs gc hlc GF hG sem => exec_sound_at_bool (GF := GF) _ _ _

theorem exec_sound_unit (ρ : List (GoString × term)) sst :
    exec_sound CEUnit ρ sst [mkPath TUnit sst] :=
  fun ext ffi fi fs gc hlc GF hG sem => exec_sound_at_unit (GF := GF) _ _

theorem exec_sound_var (ρ : List (GoString × term)) sst (gx : GoString) (x : term) :
    env_lookup ρ gx = some x →
    vars_below (svars sst).length x →
    exec_sound (CEVar gx) ρ sst [mkPath x sst] :=
  fun Hlk Hb ext ffi fi fs gc hlc GF hG sem => exec_sound_at_var (GF := GF) _ _ _ _ Hlk Hb

theorem exec_sound_zero (ρ : List (GoString × term)) sst (cty : ctype) :
    exec_sound (CEZero cty) ρ sst [mkPath (ctype_zero cty) sst] :=
  fun ext ffi fi fs gc hlc GF hG sem => exec_sound_at_zero (GF := GF) _ _ _

theorem exec_sound_let (gx : GoString) (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ce2 ((gx, pret p) :: ρ) (pst p) qs) →
    exec_sound (CELet gx ce1 ce2) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_let (GF := GF) _ _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf
    (fun p Hp => let ⟨qs, Hs, Hq⟩ := Hc p Hp; ⟨qs, Hs, Hq ext ffi fi fs gc hlc GF hG sem⟩)

theorem exec_sound_seq (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ exec_sound ce2 ρ (pst p) qs) →
    exec_sound (CESeq ce1 ce2) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_seq (GF := GF) _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf
    (fun p Hp => let ⟨qs, Hs, Hq⟩ := Hc p Hp; ⟨qs, Hs, Hq ext ffi fi fs gc hlc GF hG sem⟩)

theorem exec_sound_do (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    (∀ p, p ∈ ps → mkPath TExec (pst p) ∈ out) →
    exec_sound (CEDo ce) ρ sst out :=
  fun He Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_do (GF := GF) _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hc

theorem exec_sound_return (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    (∀ p, p ∈ ps → mkPath (TRet (pret p)) (pst p) ∈ out) →
    exec_sound (CEReturn ce) ρ sst out :=
  fun He Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_return (GF := GF) _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hc

theorem exec_sound_exc_do (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    (∀ p, p ∈ ps →
       (pret p = TExec ∧ mkPath TUnit (pst p) ∈ out) ∨
       (∃ x, pret p = TRet x ∧ mkPath x (pst p) ∈ out)) →
    exec_sound (CEExcDo ce) ρ sst out :=
  fun He Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_exc_do (GF := GF) _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hc

theorem exec_sound_if (cc ct cf : cexpr) ρ sst (ps out : List spath) :
    exec_sound cc ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = some SBool) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ct ρ (st_assume (pst p) (pret p)) qs) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound cf ρ (st_assume (pst p) (negate (pret p))) qs) →
    exec_sound (CEIf cc ct cf) ρ sst out :=
  fun He Hwf Hs Ht Hf ext ffi fi fs gc hlc GF hG sem => exec_sound_at_if (GF := GF) _ _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf Hs
    (fun p Hp => let ⟨qs, Hs, Hq⟩ := Ht p Hp; ⟨qs, Hs, Hq ext ffi fi fs gc hlc GF hG sem⟩)
    (fun p Hp => let ⟨qs, Hs, Hq⟩ := Hf p Hp; ⟨qs, Hs, Hq ext ffi fi fs gc hlc GF hG sem⟩)

theorem exec_sound_load (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ y, heap_lookup (sheap (pst p)) (pret p) = some y ∧
                        mkPath y (pst p) ∈ out) →
    exec_sound (CELoad cty ce) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_load (GF := GF) _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf Hc

theorem exec_sound_alloc (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps →
       mkPath (TVar (svars (pst p)).length) (st_alloc (pst p) (pret p)) ∈ out) →
    exec_sound (CEAlloc cty ce) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem => exec_sound_at_alloc (GF := GF) _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf Hc

end exec_uniform_lemmas

end Checker
end Perennial
