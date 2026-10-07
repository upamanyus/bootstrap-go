/-
Port of `new/checker/fn/State__clone.v`.

The `clone` method of `checker.State` (checker/state.go): the deep-enough copy a
state gets before it is modified, so that forking at an `if:` or appending to a
heap on one path can never be observed on another. The copy comes back as
`is_state_fresh` -- owned slices with their capacities, ready to be appended
to -- and `is_state_fresh_publish` turns it into a state.
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

theorem wp_State__clone (lst : Loc) (sst : sstate) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_state lst sst }}
      (App (Val (lst @!! go.GoType.PointerType checker.State.ty @!! go!"clone")) (Val #()))
    {{ (lst' : Loc), RET #lst'; is_state lst sst ∗ is_state_fresh lst' sst }} := by
  wp_start as Hst
  unfold is_state
  icases Hst with ⟨%sh, %sc, %sv, Hl, Hheap, Hcond, #Hvars⟩
  unfold is_heap is_cond is_vars
  icases Hheap with ⟨%cells, Hsh, #Hcells⟩
  icases Hcond with ⟨%locs, Hsc, #Hlocs⟩
  ihave %Hlh := ownSlice_len _ _ _ $$ Hsh
  ihave %Hlc := ownSlice_len _ _ _ $$ Hsc
  ihave %Hlv := ownSlice_len _ _ _ $$ Hvars
  wp_auto
  -- the three make+copy pairs
  wp_apply wp_slice_make2 as %nh ⟨Hnh, Hnhcap⟩
  · ipureintro; word
  wp_apply wp_slice_copy nh _ sh cells (DFrac.own 1) $$ [Hnh Hsh] as %k1 ⟨%Hk1, Hnh, Hsh⟩
  · iframe Hnh Hsh
  rw [List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_of_eq Hlh.1.symm),
    List.length_replicate, List.take_of_length_le (Nat.le_of_eq Hlh.1), List.append_nil]
  wp_apply wp_slice_make2 as %nc ⟨Hnc, Hnccap⟩
  · ipureintro; word
  wp_apply wp_slice_copy nc _ sc locs (DFrac.own 1) $$ [Hnc Hsc] as %k2 ⟨%Hk2, Hnc, Hsc⟩
  · iframe Hnc Hsc
  rw [List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_of_eq Hlc.1.symm),
    List.length_replicate, List.take_of_length_le (Nat.le_of_eq Hlc.1), List.append_nil]
  wp_apply wp_slice_make2 as %nv ⟨Hnv, Hnvcap⟩
  · ipureintro; word
  wp_apply wp_slice_copy nv _ sv _ DFrac.discard $$ [Hnv] as %k3 ⟨%Hk3, Hnv, -⟩
  · iframe Hnv Hvars
  rw [List.drop_of_length_le (by rw [List.length_replicate]; exact Nat.le_of_eq Hlv.1.symm),
    List.length_replicate, List.take_of_length_le (Nat.le_of_eq Hlv.1), List.append_nil]
  wp_pures
  wp_load; wp_pures; wp_load; wp_pures; wp_load
  wp_pures
  wp_alloc lnew as Hnew
  wp_auto
  iapply HΦ
  unfold is_state_fresh is_heap is_cond
  isplitl [Hl Hsh Hsc]
  · iexists sh, sc, sv
    iframe Hl Hvars
    isplitl [Hsh]
    · iexists cells; iframe Hsh Hcells
    · iexists locs; iframe Hsc Hlocs
  · iexists nh, nc, nv
    iframe Hnew Hnhcap Hnccap Hnv Hnvcap
    isplitl [Hnh]
    · iexists cells; iframe Hnh Hcells
    · iexists locs; iframe Hnc Hlocs

end proof

end Checker
end Perennial
