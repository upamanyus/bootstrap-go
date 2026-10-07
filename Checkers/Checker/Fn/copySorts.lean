/-
Port of `new/checker/fn/copySorts.v`.

`checker.copySorts` (checker/sorts.go): a fresh copy of a sort vector.

`is_vars` is persistent, so the copy is persisted before it is returned
and its `ownSliceCap` is dropped.
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

theorem wp_copySorts (s : GoSlice) (vars : List sort) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_vars s vars }}
      (App (Val (@! checker.copySorts)) (Val #s))
    {{ (s' : GoSlice), RET #s'; is_vars s' vars }} := by
  wp_start as #Hs
  unfold is_vars
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply wp_slice_make2 as %sl ⟨Hout, Hcap⟩
  · ipureintro; word
  wp_apply wp_slice_copy sl _ s _ DFrac.discard $$ [Hout] as %nc ⟨%Hn, Hout, -⟩
  · iframe Hout Hs
  rw [List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_of_eq Hlen.1.symm),
    List.length_replicate, List.take_of_length_le (Nat.le_of_eq Hlen.1), List.append_nil]
  ipersist Hout
  wp_auto
  iapply HΦ
  iexact Hout

end proof

end Checker
end Perennial
