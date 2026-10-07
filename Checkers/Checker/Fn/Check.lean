/-
Port of `new/checker/fn/Check.v`.

`checker.Check` (checker/check.go): the entry point. `Analyze`, and if it
succeeds, `Verify` of its paths against the postcondition.

The specification promises `triple_holds` (Defs.lean), the Hoare triple of
`check_sound` (Soundness.lean) in every ghost state; `check_sound` is its
instance at the ambient one. The composition, in one ghost state, is
`check_triple`: `Analyze`'s WP ends in one of the paths (`paths_post`),
`Verify` gives that path a disjunct it satisfies (`path_sat_dj`), and the
disjunct entails the postcondition. `triple_holds_intro` does it in every
ghost state, from the ghost-state-independent answers of `Analyze`
(`analyze_ok`) and `Verify` (`path_ok`).

Lean notes:
* Rocq's `apply_vals_e_not_val`/`arg_vals_not_val` are about `to_val`;
  here `toVal` (the language's `toVal`, which `wp_frame_step_l'` takes).
* No naming trap: `wp_Check` could use the names of soundness.v, but keeps
  Rocq's (`cf`, `vs`, `P`, `Q`) so the files compare; CheckSound.lean
  restates it.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.VerifyDef
import Checkers.Checker.PreSound
import Checkers.Checker.Fn.Analyze
import Checkers.Checker.Fn.Verify

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section not_val
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]

/-- A function application is never a value, so the `▷` in front of a Hoare
triple's continuation can be stripped by its first step. -/
theorem apply_vals_e_not_val (h : Expr) (vs : List val) :
    toVal h = none → toVal (apply_vals_e h vs) = none := by
  induction vs generalizing h with
  | nil => exact id
  | cons v vs IH => intro _; exact IH (App h (Val v)) rfl

theorem arg_vals_not_val (cf : cfunc) (θ : Nat → val) :
    toVal (apply_vals (func_val cf) (arg_vals cf θ)) = none := by
  rw [apply_vals_unfold]
  rcases Hargs : arg_vals cf θ with _ | ⟨v, vs⟩
  · exfalso
    revert Hargs
    unfold arg_vals
    rcases fparams cf with _ | ⟨x, xs⟩ <;> simp
  · exact apply_vals_e_not_val (App (Val (func_val cf)) (Val v)) vs rfl

end not_val

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The composition. -/
theorem check_triple (cf : cfunc) (vs : List sort) (P Q : cassn) (ps : List spath)
    (θ : Nat → val) :
    paths_wf vs.length ps →
    (∀ θ, vars_sat θ vs → ⊢ pre_interp (GF := GF) θ P -∗
       WP (apply_vals (func_val cf) (arg_vals cf θ))
         {{ paths_post vs.length (mkVal θ (fun _ => uval) uval) ps }}) →
    (∀ sp, sp ∈ ps → ∃ dj, d_fail dj = false ∧ path_sat_dj_at (GF := GF) vs sp dj ∧
                           ∀ V, dj_interp (GF := GF) V dj ⊢ assn_interp V Q) →
    vars_sat θ vs →
    {{ pre_interp (GF := GF) θ P }}
      (apply_vals (func_val cf) (arg_vals cf θ))
    {{ (v : val), RET v; post_interp (GF := GF) θ v Q }} := by
  intro Hwf Hwp Hver Hθ
  iintro %Φ Hpre HΦ
  iapply wp_wand_r (Φ := fun v => iprop((∀ v, post_interp (GF := GF) θ v Q -∗ Φ v) ∗
                               paths_post (GF := GF) vs.length (mkVal θ (fun _ => uval) uval) ps v))
  isplitl
  · iapply wp_frame_step_l' (arg_vals_not_val cf θ) Iris.Std.LawfulSet.subset_refl
    iframe HΦ
    iapply Hwp θ Hθ $$ Hpre
  iintro %v ⟨HΦ, Hv⟩
  unfold paths_post
  icases Hv with ⟨%p, %V', %Hin, %Hag, %Hret, %Hsat, Hh⟩
  obtain ⟨dj, -, Hdj, Hent⟩ := Hver p Hin
  iapply HΦ
  unfold post_interp
  iapply Hent
  subst Hret
  iapply Hdj θ V' Hθ Hag Hsat (Hwf.paths_wf_state p Hin) (Hwf.paths_wf_grow p Hin)
    (Hwf.paths_wf_ret p Hin) $$ Hh

end proof

/-- The composition in every ghost state. -/
theorem triple_holds_intro (cf : cfunc) (vs : List sort) (P Q : cassn) (ps : List spath) :
    paths_wf vs.length ps →
    analyze_ok cf vs P ps →
    (∀ sp, sp ∈ ps → path_ok vs Q sp) →
    triple_holds cf vs P Q := by
  intro Hwf ⟨Hlen, Hws, Hsnd⟩ Hver ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem θ Hθ
  refine check_triple cf vs P Q ps θ Hwf ?_ ?_ Hθ
  · intro θ' Hθ'
    exact analyze_sound cf vs P ps θ' Hlen Hws Hsnd Hθ'
  · intro sp Hsp
    obtain ⟨dj, Hf, Hsat, Hent⟩ := Hver sp Hsp
    exact ⟨dj, Hf, Hsat ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem,
      Hent ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem⟩

section proof_Check
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_Check (cf : cfunc) (vs : List sort) (P Q : cassn)
    (lf : Loc) (sv : GoSlice) (lpre lpost : Loc) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗
        is_func lf cf ∗ is_sorts sv vs ∗ is_assn lpre P ∗ is_assn lpost Q }}
      (App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #sv)) (Val #lpre)) (Val #lpost))
    {{ (b : Bool), RET #b; ⌜b = true → triple_holds cf vs P Q⌝ }} := by
  wp_start as ⟨#Hf, #Hsv, #Hpre, #Hpost⟩
  wp_auto
  wp_apply wp_Analyze lf cf sv vs lpre P $$ [] as %s %lfail Hres
  · iframe #
  by_cases Hnull : lfail = null
  · subst Hnull
    simp only [↓reduceIte]
    icases Hres with ⟨%ps, Hps, %Hwf, %Hok⟩
    wp_auto
    wp_apply wp_Verify s ps sv vs lpost Q $$ [Hps] as %lv %Hver
    · iframe Hps Hsv Hpost
    iapply HΦ
    ipureintro
    intro Hb
    refine triple_holds_intro cf vs P Q ps Hwf Hok (Hver ?_)
    simpa using Hb
  · -- `Analyze` failed
    rw [decide_eq_false Hnull]
    wp_auto
    iapply HΦ
    ipureintro
    intro Hb
    simp at Hb

end proof_Check

end Checker
end Perennial
