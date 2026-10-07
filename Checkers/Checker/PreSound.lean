/-
Port of `new/checker/pre_sound.v`.

The meaning of a precondition that `Analyze` accepts, and of the entry
environment it builds.

`Analyze` (checker/check.go) turns the precondition into the initial
symbolic state -- its points-to atoms become the heap (`assnHeap`), its
pure atoms the path condition (`assnPure`) -- and binds parameter `i` to
the logical variable `TVar i`. This file proves that this is faithful:

- a precondition that passes `assnWellSorted` has no `∨` and no `∃`
  (those forms are rejected), so its interpretation is exactly the
  heap of `assnHeap` plus the facts of `assnPure` (`pre_interp_state`);
- its terms are sorted by the declared variables alone, so they mention
  no pattern variable, no `ret`, and only variables below `length vars`
  (`pre_state_wf`);
- the environment the parameter loop builds stands for the substitution
  `binds` that applying `func_val f` performs (`env_interp_penv`).

`analyze_sound` puts these together with `exec_sound` of the body into
the WP that `Analyze`'s specification promises.

Lean notes:
* Rocq's `vvar V <$> seq k n` is `(List.range' k n).map (vvar V)`; Lean's
  `arg_vals` (Defs.lean) uses `List.range`, which `analyze_sound` converts
  with `List.range_eq_range'`.
* `exec_sound` (ExecSpec.lean) also quantifies over `GoGlobalContext` and
  `HasLC`; `analyze_sound` instantiates it at the section variables.
-/
import Checkers.Checker.ExecSpec
import Checkers.Checker.Fn.assnHeap
import Checkers.Checker.Fn.assnPure
import Checkers.Checker.Fn.assnWellSorted

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-! ## Pure facts -/

/-- A term sorted by the declared variables alone mentions only them. -/
theorem sort_of_vars_below (vars : List sort) (t : term) (s : sort) :
    sort_of (vars_env vars) t = some s → vars_below vars.length t := by
  induction t generalizing s with
  | TVar n =>
    intro h
    simp only [sort_of, vars_env] at h
    exact (List.getElem?_eq_some_iff.mp h).1
  | TPat n => intro h; simp [sort_of, vars_env] at h
  | TResult => intro h; simp [sort_of, vars_env] at h
  | TExec => intro h; simp [sort_of] at h
  | TRet a => intro h; simp [sort_of] at h
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    intro h
    simp only [sort_of] at h
    rcases ha : sort_of (vars_env vars) a with _ | sa <;>
      rcases hb : sort_of (vars_env vars) b with _ | sb
    all_goals first | exact ⟨iha _ ha, ihb _ hb⟩ | simp [ha, hb] at h
  | TNeg a iha | TNot a iha =>
    intro h
    simp only [sort_of] at h
    rcases ha : sort_of (vars_env vars) a with _ | sa
    all_goals first | exact iha _ ha | simp [ha] at h
  | TIte c a b ihc iha ihb =>
    intro h
    simp only [sort_of] at h
    rcases hc : sort_of (vars_env vars) c with _ | sc <;>
      rcases ha : sort_of (vars_env vars) a with _ | sa <;>
      rcases hb : sort_of (vars_env vars) b with _ | sb
    all_goals first | exact ⟨ihc _ hc, iha _ ha, ihb _ hb⟩ | simp [hc, ha, hb] at h
  | _ => intro _; trivial

-- `pre_state`, `penv_from`, `penv`: in LCheck/Fns.lean.

theorem pre_below (vars : List sort) (pre : cassn) :
    cassn_ws (vars_env vars) pre = true →
    heap_below vars.length (cassn_heap pre) ∧ pc_below vars.length (cassn_pure pre) := by
  induction pre with
  | CAEmp => intro _; exact ⟨fun _ h => by simp [cassn_heap] at h, fun _ h => by simp [cassn_pure] at h⟩
  | CASep p q ihp ihq =>
    intro Hws
    simp only [cassn_ws, Bool.and_eq_true] at Hws
    obtain ⟨Hp1, Hp2⟩ := ihp Hws.1
    obtain ⟨Hq1, Hq2⟩ := ihq Hws.2
    simp only [cassn_heap, cassn_pure]
    refine ⟨fun c Hc => ?_, fun c Hc => ?_⟩
    · rcases List.mem_append.mp Hc with H | H
      · exact Hp1 c H
      · exact Hq1 c H
    · rcases List.mem_append.mp Hc with H | H
      · exact Hp2 c H
      · exact Hq2 c H
  | CAOr => intro h; simp [cassn_ws] at h
  | CAExists => intro h; simp [cassn_ws] at h
  | CAPure t =>
    intro Hws
    simp only [cassn_ws] at Hws
    rcases Ht : sort_of (vars_env vars) t with _ | st
    · simp [Ht] at Hws
    · simp only [cassn_heap, cassn_pure]
      refine ⟨fun _ h => by simp at h, fun c Hc => ?_⟩
      simp only [List.mem_singleton] at Hc
      subst Hc
      exact sort_of_vars_below vars c st Ht
  | CAPointsTo x v =>
    intro Hws
    simp only [cassn_ws] at Hws
    rcases Hx : sort_of (vars_env vars) x with _ | sx <;>
      rcases Hv : sort_of (vars_env vars) v with _ | sv
    all_goals try (simp [Hx, Hv] at Hws; done)
    simp only [cassn_heap, cassn_pure]
    refine ⟨fun c Hc => ?_, fun _ h => by simp at h⟩
    simp only [List.mem_singleton] at Hc
    subst Hc
    exact ⟨sort_of_vars_below vars x sx Hx, sort_of_vars_below vars v sv Hv⟩

theorem pre_state_wf (vars : List sort) (pre : cassn) :
    cassn_ws (vars_env vars) pre = true → wf_state (pre_state vars pre) := by
  intro Hws
  obtain ⟨H1, H2⟩ := pre_below vars pre Hws
  exact ⟨H1, H2⟩

/-! ## The entry environment

Mirrors the parameter loop of `Analyze`: parameter `k + i` is bound to
`TVar (k + i)`, each new binding in front, so a later parameter shadows an
earlier one of the same name. -/


theorem penv_from_snoc (k : Nat) (xs : List GoString) (x : GoString) (ρ : List (GoString × term)) :
    penv_from k (xs ++ [x]) ρ = (x, TVar (k + xs.length)) :: penv_from k xs ρ := by
  induction xs generalizing k ρ with
  | nil => rfl
  | cons y xs IH =>
    simp only [List.cons_append, penv_from, IH, List.length_cons]
    congr 3
    omega

theorem penv_snoc (xs : List GoString) (x : GoString) :
    penv (xs ++ [x]) = (x, TVar xs.length) :: penv xs := by
  simp only [penv, penv_from_snoc, Nat.zero_add]

section pre_sound
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem penv_from_below (K k : Nat) (xs : List GoString) (ρ : List (GoString × term)) :
    env_below K ρ → k + xs.length ≤ K → env_below K (penv_from k xs ρ) := by
  induction xs generalizing k ρ with
  | nil => intro Hρ _; exact Hρ
  | cons x xs IH =>
    intro Hρ Hlen
    simp only [List.length_cons] at Hlen
    exact IH (k + 1) _ (env_below_cons _ _ _ _ (by simp only [vars_below]; omega) Hρ)
      (by omega)

theorem penv_below (K : Nat) (xs : List GoString) : xs.length ≤ K → env_below K (penv xs) := by
  intro Hlen
  exact penv_from_below K 0 xs [] (fun _ h => by cases h) (by omega)

theorem env_interp_penv_from (V : valuation) (k : Nat) (xs : List GoString)
    (ρ : List (GoString × term)) :
    env_interp V (penv_from k xs ρ) =
      binds (pnames xs) ((List.range' k xs.length).map (vvar V)) (env_interp V ρ) := by
  induction xs generalizing k ρ with
  | nil => rfl
  | cons x xs IH =>
    simp only [penv_from, IH, List.length_cons, List.range'_succ, List.map_cons, pnames_cons,
      binds_cons]
    rfl

theorem env_interp_penv (V : valuation) (xs : List GoString) :
    env_interp V (penv xs) = binds (pnames xs) ((List.range' 0 xs.length).map (vvar V)) ∅ :=
  env_interp_penv_from V 0 xs []

/-- An accepted precondition means exactly its heap and its path condition. -/
theorem assn_interp_ws (E : sort_env) (V : valuation) (pre : cassn) :
    cassn_ws E pre = true →
    assn_interp (GF := GF) V pre ⊢ heap_interp V (cassn_heap pre) ∗ ⌜pc_sat V (cassn_pure pre)⌝ := by
  induction pre with
  | CAEmp =>
    intro _
    simp only [assn_interp, cassn_heap, cassn_pure]
    iintro _
    isplitr
    · iapply (heap_interp_nil _).2; itrivial
    · ipureintro; exact pc_sat_nil V
  | CASep p q ihp ihq =>
    intro Hws
    simp only [cassn_ws, Bool.and_eq_true] at Hws
    simp only [assn_interp, cassn_heap, cassn_pure]
    iintro ⟨Hp, Hq⟩
    icases ihp Hws.1 $$ Hp with ⟨Hhp, %Hcp⟩
    icases ihq Hws.2 $$ Hq with ⟨Hhq, %Hcq⟩
    isplitl [Hhp Hhq]
    · iapply (heap_interp_app _ _ _).2; iframe
    · ipureintro; exact pc_sat_app V _ _ Hcp Hcq
  | CAOr => intro h; simp [cassn_ws] at h
  | CAExists => intro h; simp [cassn_ws] at h
  | CAPure t =>
    intro _
    simp only [assn_interp, cassn_heap, cassn_pure]
    iintro %Ht
    isplitr
    · iapply (heap_interp_nil _).2; itrivial
    · ipureintro
      intro t' Ht'
      simp only [List.mem_singleton] at Ht'
      subst Ht'; exact Ht
  | CAPointsTo x v =>
    intro _
    simp only [assn_interp, cassn_heap, cassn_pure]
    iintro H
    isplitl [H]
    · iapply (heap_interp_cons _ _ _).2
      isplitl [H]
      · iexact H
      · iapply (heap_interp_nil _).2; itrivial
    · ipureintro; exact pc_sat_nil V

theorem pre_interp_state (θ : Nat → val) (vars : List sort) (pre : cassn) :
    vars_sat θ vars →
    cassn_ws (vars_env vars) pre = true →
    pre_interp (GF := GF) θ pre ⊢
      ⌜st_sat (mkVal θ (fun _ => uval) uval) (pre_state vars pre)⌝ ∗
      heap_interp (mkVal θ (fun _ => uval) uval) (sheap (pre_state vars pre)) := by
  intro Hθ Hws
  unfold pre_interp
  iintro H
  icases assn_interp_ws _ _ pre Hws $$ H with ⟨Hh, %Hpc⟩
  simp only [pre_state]
  iframe Hh
  ipureintro
  exact ⟨fun n s Hn => Hθ n s Hn, Hpc⟩

/-- `Analyze`'s promise, from `exec_sound` of the body in the entry state. -/
theorem analyze_sound (f : cfunc) (vars : List sort) (pre : cassn) (ps : List spath)
    (θ : Nat → val) :
    (fparams f).length ≤ vars.length →
    cassn_ws (vars_env vars) pre = true →
    exec_sound (fbody f) (penv (fparams f)) (pre_state vars pre) ps →
    vars_sat θ vars →
    ⊢ pre_interp (GF := GF) θ pre -∗
      WP (apply_vals (func_val f) (arg_vals f θ))
        {{ paths_post vars.length (mkVal θ (fun _ => uval) uval) ps }} := by
  intro Hlen Hws Hsnd Hθ
  iintro Hpre
  icases pre_interp_state θ vars pre Hθ Hws $$ Hpre with ⟨%Hsat, Hh⟩
  have Hwp := Hsnd ext ffi inferInstance inferInstance go_gctx hlc GF hG sem (pre_state_wf vars pre Hws)
    (penv_below _ _ Hlen) _ Hsat
  ihave Hwp := Hwp $$ Hh
  rw [env_interp_penv]
  simp only [pre_state] at Hwp ⊢
  rcases Hps : fparams f with _ | ⟨x, xs⟩
  · iapply wp_func_val_nil f θ _ Hps
    rw [Hps] at *
    simp only [pnames, List.map_nil, List.length_nil, List.range'_zero, binds, csubst_empty]
      at *
    iexact Hwp
  · have Hargs : arg_vals f θ = (List.range' 0 (fparams f).length).map θ := by
      simp only [arg_vals, Hps, List.range_eq_range']
    rw [Hargs]
    iapply wp_func_val f _ _ (by simp) (by rw [Hps]; simp)
    rw [Hps] at *
    iexact Hwp

end pre_sound

/-- What `Analyze` establishes, independent of the ghost state: the premises
of `analyze_sound`. -/
def analyze_ok (f : cfunc) (vars : List sort) (pre : cassn) (ps : List spath) : Prop :=
  (fparams f).length ≤ vars.length ∧
  cassn_ws (vars_env vars) pre = true ∧
  exec_sound (fbody f) (penv (fparams f)) (pre_state vars pre) ps

end Checker
end Perennial
