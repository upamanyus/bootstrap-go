/-
Port of `new/checker/fn/TypeSort.v`.

`checker.TypeSort` (checker/sorts.go): the sort of a supported type.
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- Every `ctype` is supported, so the `Bool` result is `true` at every
`some`; the `none` case is the nil pointer, where the Go code answers
`(SortInt, false)`. -/
def octype_sort : Option ctype → sort × Bool
  | none => (SInt, false)
  | some t' => (ctype_sort t', true)

theorem wp_TypeSort (lt : Loc) (ot : Option ctype) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_otype lt ot }}
      (App (Val (@! checker.TypeSort)) (Val #lt))
    {{ RET (PairV #(sort_code (octype_sort ot).1) #((octype_sort ot).2)); True }} := by
  iloeb as IH generalizing %lt %ot
  wp_start as #Hot
  ihave %Hn := is_otype_null _ _ $$ Hot
  wp_auto
  wp_if_destruct
  · -- the argument is nil
    obtain rfl : ot = none := Hn.mp rfl
    simp only [octype_sort, sort_code, checker.SortInt]
    iapply HΦ
    itrivial
  · cases ot with
    | none => exact absurd (Hn.mpr rfl) Hif
    | some ty =>
    rw [is_otype_some]
    icases is_type_node _ _ $$ Hot with ⟨%le, #Hnode, #Helem⟩
    iStructNamed Hnode
    cases ty <;> simp only [type_code, ctype_elem, octype_sort, ctype_sort, sort_code]
    all_goals wp_auto
    all_goals try (simp only [checker.SortInt, checker.SortBool]; iapply HΦ; itrivial; done)
    wp_apply IH $$ %le %(some _) [] as _
    · iframe #
    simp only [checker.SortLoc]
    iapply HΦ
    itrivial

end proof

end Checker
end Perennial
