/-
Port of `new/checker/fn/SortOf.v`.

`checker.SortOf` (checker/sorts.go): the sort of a term over a list of
logical-variable sorts.
-/
import Checkers.Checker.Fn.sortOfEnv

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

/-- `SortOf` builds a `sortEnv` with only `vars` populated, which is exactly
`vars_env`: no pattern variables, and no `ret`. -/
theorem wp_SortOf (sv : GoSlice) (lterm : Loc) (vl : List sort) (oty : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ sv ↦*□ (vl.map sort_code) ∗
        is_oterm lterm oty }}
      (App (App (Val (@! checker.SortOf)) (Val #sv)) (Val #lterm))
    {{ RET (PairV #(osort_code (osort_of (vars_env vl) oty))
                  #(osort_ok (osort_of (vars_env vl) oty))); True }} := by
  wp_start as ⟨#Hsl, #Hot⟩
  wp_auto
  ipersist «$r0»
  ihave Hnil1 := ownSlice_nil (GF := GF) (V := w64) DFrac.discard
  ihave Hnil2 := ownSlice_nil (GF := GF) (V := Bool) DFrac.discard
  wp_apply wp_sortOfEnv_pts DFrac.discard «$r0_ptr» (vars_env vl) sv slice.nil slice.nil lterm oty
    (vars_env_wf vl) $$ [] as _
  · simp only [vars_env, List.map_nil, sort_code]
    isplitr
    · iExactEq «$r0»; rfl
    isplitr
    · iexact Hsl
    isplitr
    · iexact Hnil1
    isplitr
    · iexact Hnil2
    iexact Hot
  iapply HΦ; itrivial

end proof

end Checker
end Perennial
