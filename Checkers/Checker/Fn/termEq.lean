/-
Port of `new/checker/fn/termEq.v`.

`checker.termEq` (checker/term.go): structural equality of two terms.

Lean notes:
* `tcode`/`term_eq_iff` are pure and stated outside the proof section (Rocq
  had to re-prove `term_eq_iff` in match_sound.v because the section version
  took the ghost-state variables; here it is reusable as is).
* Three recursive calls, each followed by `wp_if_destruct` on the `&&`; the
  `wp_if_destruct` hypotheses are all called `Hif`, so they are saved with
  `have Hk := Hif` before the next split.
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The kind code as a `Nat`, so that the 18x18 case analysis below can
discharge the impossible cases by comparing `Nat` literals instead of `w64`
computations. -/
def tcode : term → Nat
  | TVar _ => 1 | TPat _ => 2 | TResult => 3 | TInt _ => 4
  | TBool _ => 5 | TUnit => 6 | TNull => 7
  | TPlus _ _ => 8 | TMinus _ _ => 9 | TMul _ _ => 10
  | TNeg _ => 11 | TEq _ _ => 12
  | TLt sg _ _ => if sg then 13 else 14
  | TLe sg _ _ => if sg then 15 else 16
  | TNot _ => 17 | TIte _ _ _ => 18 | TExec => 19 | TRet _ => 20

theorem tcode_term_code (t : term) : (term_code t).toNat = tcode t := by
  cases t <;> try rfl
  all_goals rename_i sg _ _; cases sg <;> rfl

theorem term_eq_iff (ta tb : term) :
    term_idx_wf ta → term_idx_wf tb →
    (ta = tb ↔ term_code ta = term_code tb ∧ term_num ta = term_num tb ∧
               term_a ta = term_a tb ∧ term_b ta = term_b tb ∧ term_c ta = term_c tb) := by
  intro Hwa Hwb
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro ⟨Hc, Hn, Ha, Hb, Hc2⟩
    have Hc' := congrArg BitVec.toNat Hc
    rw [tcode_term_code, tcode_term_code] at Hc'
    cases ta <;> cases tb <;> simp only [tcode] at Hc' <;> (repeat' split at Hc') <;>
      (try omega)
    all_goals first
      | (simp_all [term_num, term_a, term_b, term_c]; done)
      | (simp only [term_num] at Hn; congr 1; exact W64_nat_inj _ _ Hwa Hwb Hn)
      | (simp only [term_num] at Hn; rename_i b b'; cases b <;> cases b' <;> first
          | rfl | (revert Hn; decide))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- The recursion runs into the `A`/`B`/`C` fields, which are `null` wherever
the constructor has no child there, so the specification has to talk about
a possibly absent term. -/
theorem wp_termEq (la lb : Loc) (oa ob : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oterm la oa ∗ is_oterm lb ob }}
      (App (App (Val (@! checker.termEq)) (Val #la)) (Val #lb))
    {{ RET #(decide (oa = ob)); True }} := by
  iloeb as IH generalizing %la %lb %oa %ob
  wp_start as ⟨#Hoa, #Hob⟩
  ihave %Hna := is_oterm_null _ _ $$ Hoa
  ihave %Hnb := is_oterm_null _ _ $$ Hob
  wp_auto
  wp_if_destruct
  · -- the first argument is nil
    obtain rfl : oa = none := Hna.mp rfl
    have Hd : decide (none = ob) = decide (lb = null) := by
      simp only [decide_eq_decide]; exact ⟨fun h => Hnb.mpr h.symm, fun h => (Hnb.mp h).symm⟩
    rw [← Hd]
    iapply HΦ
    itrivial
  · cases oa with
    | none => exact absurd (Hna.mpr rfl) Hif
    | some ta =>
    wp_if_destruct
    · -- the second argument is nil
      obtain rfl : ob = none := Hnb.mp rfl
      rw [show decide (some ta = none) = false from rfl]
      iapply HΦ
      itrivial
    · cases ob with
      | none => exact absurd (Hnb.mpr rfl) Hif
      | some tb =>
      rw [is_oterm_some, is_oterm_some]
      icases is_term_node _ _ $$ Hoa with ⟨%laa, %lab, %lac, %Hwa, #Hn1, #Haa, #Hab, #Hac⟩
      icases is_term_node _ _ $$ Hob with ⟨%lba, %lbb, %lbc, %Hwb, #Hn2, #Hba, #Hbb, #Hbc⟩
      iStructNamedSuffix Hn1 "_a"
      iStructNamedSuffix Hn2 "_b"
      wp_auto
      -- a failed comparison of one of the five fields refutes `some ta = some tb`
      have Hne : ∀ P : Prop, ¬ P → (ta = tb → P) → decide (some ta = some tb) = false :=
        fun P hP h => decide_eq_false (fun e => hP (h (Option.some.inj e)))
      wp_if_destruct
      · -- the kind codes agree
        have Hk := Hif
        try wp_auto
        wp_if_destruct
        · -- the `Num` fields agree: recurse into the three children
          have Hn := Hif
          wp_apply IH $$ %laa %lba %(term_a ta) %(term_a tb) []
          · iframe #
          wp_if_destruct
          · have Ha := Hif
            wp_apply IH $$ %lab %lbb %(term_b ta) %(term_b tb) []
            · iframe #
            wp_if_destruct
            · have Hb := Hif
              wp_apply IH $$ %lac %lbc %(term_c ta) %(term_c tb) []
              · iframe #
              have Hd : decide (some ta = some tb) = decide (term_c ta = term_c tb) := by
                simp only [decide_eq_decide, Option.some.injEq]
                rw [term_eq_iff _ _ Hwa Hwb]
                exact ⟨fun h => h.2.2.2.2, fun h => ⟨Hk, Hn, Ha, Hb, h⟩⟩
              rw [Hd]
              iapply HΦ
              itrivial
            · rw [Hne _ Hif (fun e => by rw [e])]
              iapply HΦ
              itrivial
          · rw [Hne _ Hif (fun e => by rw [e])]
            iapply HΦ
            itrivial
        · -- the `Num` fields differ
          rw [Hne _ Hif (fun e => by rw [e])]
          iapply HΦ
          itrivial
      · -- the kind codes differ
        rw [Hne _ Hif (fun e => by rw [e])]
        iapply HΦ
        itrivial

end proof

end Checker
end Perennial
