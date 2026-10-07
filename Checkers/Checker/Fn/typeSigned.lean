/-
Port of `new/checker/fn/typeSigned.v`.

`checker.typeSigned` (checker/sorts.go): is this integer type signed?
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

/-- The Go function dereferences `t.Kind` with no nil check; that is safe
exactly because `is_type` owns a real node (`is_type_not_null`). -/
theorem wp_typeSigned (lt : Loc) (ty : ctype) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_type lt ty }}
      (App (Val (@! checker.typeSigned)) (Val #lt))
    {{ RET #(ctype_signed ty); True }} := by
  wp_start as #Ht
  icases is_type_node _ _ $$ Ht with ⟨%le, #Hnode, -⟩
  iStructNamed Hnode
  cases ty <;> simp only [type_code, ctype_signed] <;> wp_auto <;> iapply HΦ <;> itrivial

end proof

end Checker
end Perennial
