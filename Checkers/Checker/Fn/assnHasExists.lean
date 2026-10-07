/-
Port of `new/checker/fn/assnHasExists.v`.

`checker.assnHasExists` (checker/check.go): does an existential occur
anywhere in an assertion?
-/
import Checkers.Checker.Nodes

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The mirror. As in `assnHasOr` the Go code recurses into `L` and `R` only
(`assn_l` and `assn_r`); an `AExists` answers `true` without looking at its
body. -/
def cassn_has_exists : cassn → Bool
  | CAEmp => false
  | CASep p q => cassn_has_exists p || cassn_has_exists q
  | CAOr p q => cassn_has_exists p || cassn_has_exists q
  | CAExists _ _ _ => true
  | CAPure _ => false
  | CAPointsTo _ _ => false

def oassn_has_exists : Option cassn → Bool
  | none => false
  | some x' => cassn_has_exists x'

theorem oassn_has_exists_exists (x : cassn) :
    assn_code x = W64 4 → oassn_has_exists (some x) = true := by
  cases x <;> simp only [assn_code] <;> first | (intro; rfl) | (intro h; exact absurd h (by decide))

theorem oassn_has_exists_children (x : cassn) :
    assn_code x ≠ W64 4 →
    oassn_has_exists (some x) = (oassn_has_exists (assn_l x) || oassn_has_exists (assn_r x)) := by
  cases x <;> simp [assn_code, oassn_has_exists, cassn_has_exists, assn_l, assn_r]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_assnHasExists (l : Loc) (x : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oassn l x }}
      (App (Val (@! checker.assnHasExists)) (Val #l))
    {{ RET #(oassn_has_exists x); True }} := by
  iloeb as IH generalizing %l %x
  wp_start as #Hx
  ihave %Hn := is_oassn_null _ _ $$ Hx
  wp_auto
  wp_if_destruct
  · -- the argument is nil
    obtain rfl : x = none := Hn.mp rfl
    simp only [oassn_has_exists]
    iapply HΦ; itrivial
  · cases x with
    | none => exact absurd (Hn.mpr rfl) Hif
    | some x' =>
    rw [is_oassn_some]
    icases is_assn_node _ _ $$ Hx with ⟨%lL, %lR, %lX, %lY, %Hwf, #Hnode, #HL, #HR, -⟩
    iStructNamed Hnode
    try wp_auto
    wp_if_destruct
    · -- an AExists right here
      rw [oassn_has_exists_exists x' Hif]
      iapply HΦ; itrivial
    · -- otherwise recurse into L, then into R
      rw [oassn_has_exists_children x' Hif]
      try wp_auto
      wp_apply IH $$ %lL %(assn_l x') []
      · iframe #
      cases oassn_has_exists (assn_l x')
      · try wp_auto
        wp_apply IH $$ %lR %(assn_r x') []
        · iframe #
        try wp_auto
        iapply HΦ; itrivial
      · try wp_auto
        iapply HΦ; itrivial

end proof

end Checker
end Perennial
