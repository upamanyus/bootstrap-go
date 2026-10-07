/-
Port of `new/checker/fn/typeZero.v`.

`checker.typeZero` (checker/sorts.go): the term for the zero value.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Fn.TypeSort

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

theorem wp_typeZero (lt : Loc) (t : ctype) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_type lt t }}
      (App (Val (@! checker.typeZero)) (Val #lt))
    {{ (lz : Loc), RET (PairV #lz #true); is_term lz (ctype_zero t) }} := by
  wp_start as #Ht
  wp_auto
  wp_apply wp_TypeSort lt (some t) $$ []
  · rw [is_otype_some]; iframe #
  cases t <;> simp only [ctype_sort, sort_code] <;> wp_auto
  all_goals
    wp_alloc lz as Hz
    ipersist Hz
    wp_auto
    iapply HΦ
    simp only [ctype_zero, is_term, tnode, bool_code, Bool.false_eq_true, ite_false]
    first | iexact Hz | (iExactEq Hz; rfl)

end proof

end Checker
end Perennial
