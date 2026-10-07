/-
Port of `new/checker/fn/execAlloc.v`.

`checker.execAlloc` (checker/exec.go): `GoAlloc t e`. Runs `e`; on each
path the state is cloned, extended by a fresh logical variable of sort
`SLoc` and a cell at that variable holding the path's return term, and the
new path returns the variable (`alloc_path`, exec_sound_c.v).

Lean notes:
* Rocq's `wp_execAlloc_aux` (naming trap) is not needed; `wp_execAlloc` is
  proved directly.
* The kind dispatch is on `term_code (pret q)` with `term_code_TExec` /
  `term_code_TRet`, as in Rocq (the term is not destructed).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.ExecSoundC
import Checkers.Checker.Fn.State__clone
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

theorem wp_execAlloc (t : ctype) (e : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e) →
    ⊢ exec_like (GF := GF) checker.execAlloc (CEAlloc t e) := by
  intro Hex1
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lt, %la, #Hnode, #Ht, #Ha⟩
  iStructNamed Hnode
  wp_auto
  wp_apply wp_TypeSort lt (some t) $$ []
  · rw [is_otype_some]; iframe Ht
  wp_apply exec_like_triple _ _ Hex1 la lρ lst ρ sst $$ [Hst] as %s %lf Hpost
  · iframe Hst Ha Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
  wp_if_destruct
  · rw [(exec_post_ok _ _ _ _).to_eq]
    icases Hpost with ⟨%ps0, Hps, %Hwf0, %Hsnd0⟩
    unfold is_paths
    icases Hps with ⟨%xs, Hs, Hxs⟩
    ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxs
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
    ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    ihave HI : (∃ (k : w64) (pcur : checker.Path) (so : GoSlice) (os : List checker.Path),
        "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ pcur ∗ "out" ∷ out_ptr ↦ so ∗
        "Hos" ∷ so ↦* os ∗ "Hcap" ∷ ownSliceCap checker.Path so (DFrac.own 1) ∗
        "Hosp" ∷ ([∗list] x;q ∈ os;(ps0.take (sint.nat k)).map alloc_path, is_path x q) ∗
        "Hrest" ∷ ([∗list] x;q ∈ xs.drop (sint.nat k);ps0.drop (sint.nat k), is_path x q) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ xs.length⌝ : IProp GF)
        $$ [i p out Hxs Hnil Hnilcap]
    · iexists W64 0, _, slice.nil, []
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.drop_zero,
        List.map_nil]
      iframe i p out Hxs Hnil Hnilcap
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro; word
    wp_for HI
    wp_if_destruct
    · rw [ite_eq_left ⟨Hk.1, Hif⟩]
      list_elem xs (sint.nat k) as x0
      list_elem ps0 (sint.nat k) as p0
      wp_apply wp_load_slice_index s (sint.Z k) xs _ x0 Hk.1 $$ [Hs] with Hs
      · iframe Hs; ipureintro; exact Hx0_lookup
      rw [drop_cons_of_getElem? _ _ _ Hx0_lookup, drop_cons_of_getElem? _ _ _ Hp0_lookup]
      icases (BigSepL2.bigSepL2_cons (Φ := fun _ y o => is_path (GF := GF) y o)).1 $$ Hrest
        with ⟨Hpp, Hrest⟩
      rw [show is_path x0 p0 = iprop(is_term (GF := GF) x0.Ret' (pret p0) ∗ is_state x0.St' (pst p0))
        from rfl]
      icases Hpp with ⟨#Hret, Hst0⟩
      wp_apply wp_State__clone $$ [Hst0] as %lst2 ⟨-, Hfr⟩
      · iframe Hst0
      unfold is_state_fresh
      icases Hfr with ⟨%hs, %cs, %vs, Hl, Hh, Hhcap, Hc, Hccap, Hv, Hvcap⟩
      ihave %Hlv := ownSlice_len _ _ _ $$ Hv
      rw [List.length_map] at Hlv
      have Hvl : vs.len = W64 (svars (pst p0)).length := by word
      have Hidx : idx_wf (svars (pst p0)).length := by unfold idx_wf; word
      wp_auto
      simp only [checker.SortLoc]
      wp_apply wp_slice_literal (l := [W64 2])
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Sort.ty) vs ((svars (pst p0)).map sort_code) _ [W64 2]
        (DFrac.own 1) $$ [Hv Hvcap Hsl] as %vs' ⟨Hv, Hvcap, -⟩
      · iframe Hv Hvcap Hsl
      ipersist «$r0»
      ihave #Hlterm : is_term (GF := GF) «$r0_ptr» (TVar (svars (pst p0)).length) $$ []
      · simp only [is_term, tnode]
        iframe
        isplitr
        · ipureintro; exact Hidx
        rw [← Hvl]
        iexact «$r0»
      unfold is_heap
      icases Hh with ⟨%cells, Hcells, #Hcellsp⟩
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Cell.ty) hs cells _ [checker.Cell.mk «$r0_ptr» x0.Ret']
        (DFrac.own 1) $$ [Hcells Hhcap Hsl2] as %hs' ⟨Hcells, Hhcap, -⟩
      · iframe Hcells Hhcap Hsl2
      ihave Hfr : is_state_fresh (GF := GF) lst2 (st_alloc (pst p0) (pret p0))
        $$ [Hl Hcells Hhcap Hc Hccap Hv Hvcap]
      · unfold is_state_fresh is_heap
        simp only [st_alloc]
        iexists hs', cs, vs'
        iframe Hc Hccap Hhcap Hvcap
        isplitl [Hl]
        · iexact Hl
        isplitl [Hcells]
        · iexists cells ++ [checker.Cell.mk «$r0_ptr» x0.Ret']
          iframe Hcells
          iapply BigSepL2.bigSepL2_snoc.2
          iframe Hcellsp
          rw [show is_cell (checker.Cell.mk «$r0_ptr» x0.Ret')
              (mkCell (TVar (svars (pst p0)).length) (pret p0)) =
            iprop(is_term (GF := GF) «$r0_ptr» (TVar (svars (pst p0)).length) ∗
              is_term x0.Ret' (pret p0)) from rfl]
          iframe Hlterm Hret
        rw [List.map_append, show [SLoc].map sort_code = [W64 2] from rfl]
        iexact Hv
      imod is_state_fresh_publish _ _ $$ Hfr with Hst2
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Path.ty) so os _ [checker.Path.mk «$r0_ptr» lst2]
        (DFrac.own 1) $$ [Hos Hcap Hsl3] as %so' ⟨Hos, Hcap, -⟩
      · iframe Hos Hcap Hsl3
      wp_for_post
      iframe HΦ Hs
      iexists k + W64 1, x0, so', os ++ [checker.Path.mk «$r0_ptr» lst2]
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [Hk1]
      iframe i p out Hos Hcap Hrest
      isplitl [Hosp Hst2]
      · rw [take_snoc_of_getElem? _ _ _ Hp0_lookup, List.map_append, List.map_singleton]
        unfold named
        iapply BigSepL2.bigSepL2_snoc.2
        iframe Hosp
        rw [show is_path (checker.Path.mk «$r0_ptr» lst2) (alloc_path p0) =
          iprop(is_term (GF := GF) «$r0_ptr» (TVar (svars (pst p0)).length) ∗
            is_state lst2 (st_alloc (pst p0) (pret p0))) from rfl]
        iframe Hlterm Hst2
      ipureintro; word
    · -- the loop is over
      have Htake : ps0.take (sint.nat k) = ps0 := List.take_of_length_le (by word)
      rw [Htake]
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists ps0.map alloc_path
      isplitl
      · unfold is_paths; iexists os; iframe Hos Hosp
      · ipureintro
        exact ⟨paths_wf_alloc _ _ Hwf0, exec_sound_alloc _ _ _ _ _ _ Hsnd0 Hwf0
          (fun p1 Hp1 => List.mem_map_of_mem Hp1)⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
