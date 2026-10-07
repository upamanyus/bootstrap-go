/-
Port of `new/checker/fn/onePath.v`.

`checker.onePath` (checker/exec.go): the singleton path list.
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

/-- The Go code appends a one-element slice literal to a nil slice, so the
proof supplies the nil slice's (empty) contents and capacity itself; the
caller gets back only `is_paths`, the capacity of the result being of no
use to the callers of `onePath`. -/
theorem wp_onePath (lv lst : Loc) (tv : term) (sst : sstate) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_term lv tv ∗ is_state lst sst }}
      (App (App (Val (@! checker.onePath)) (Val #lv)) (Val #lst))
    {{ (s : GoSlice), RET #s; is_paths s [mkPath tv sst] }} := by
  wp_start as ⟨#Hv, Hst⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_auto
  ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
  ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  -- the destination slice is pinned down explicitly (Rocq: left to unification,
  -- framing uses the nil points-to for the source as well)
  wp_apply wp_slice_append (t := checker.Path.ty) slice.nil [] _ [checker.Path.mk lv lst]
    (DFrac.own 1) $$ [Hsl] as %s' ⟨Hs', -, -⟩
  · iframe Hsl Hnil Hnilcap
  iapply HΦ
  unfold is_paths
  iexists [checker.Path.mk lv lst]
  simp only [List.nil_append]
  iframe Hs'
  iapply BigSepL2.bigSepL2_singleton.2
  unfold is_path
  iframe Hv Hst

end proof

end Checker
end Perennial
