/-
Port of `new/checker/fn/matchAtom.v`.

`checker.matchAtom` (checker/match.go): try to resolve one points-to
atom `x ↦ v` against the path's heap. What a `nil` failure establishes is
`atom_step` (MatchSound.lean).

Lean notes:
* The path is passed by value (`checker.Path`), as in Rocq (`pth`).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.hasPat
import Checkers.Checker.Fn.findCell
import Checkers.Checker.Fn.termEq
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.SortOf
import Checkers.Checker.Fn.matchTerm

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

theorem wp_matchAtom (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (lat : Loc) (x v : term) (ss : GoSlice) (σ : List (Option term))
    (su : GoSlice) (us : List Bool) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_assn lat (CAPointsTo x v) ∗ is_subst ss σ ∗ ⌜σ.length = (d_pats dj).length⌝ ∗
        su ↦* us ∗ ⌜us.length = (sheap (pst sp)).length⌝ }}
      (App (App (App (App (App (Val (@! checker.matchAtom)) (Val #pth)) (Val #ld)) (Val #lat))
        (Val #ss)) (Val #su))
    {{ (okb : Bool) (lf : Loc), RET (PairV #okb #lf);
        is_path pth sp ∗
        ∃ σ' us', is_subst ss σ' ∗ su ↦* us' ∗
          ⌜σ'.length = σ.length ∧ us'.length = us.length⌝ ∗
          ⌜lf = null → atom_step (sheap (pst sp)) (d_pats dj) (d_pat_ok dj)
                         (svars (pst sp)) (pret sp) x v σ us okb σ' us'⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, #Hat, Hsub, %Hlσ, Hus, %Hlus⟩
  unfold is_path
  icases Hpath with ⟨#Hret, Hst⟩
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
  simp only [is_assn]
  icases Hat with ⟨%lx, %ly, #Hatn, #Hx, #Hv⟩
  iStructNamedSuffix Hatn "_a"
  wp_auto
  wp_apply wp_instantiate_ret lx ss _ (some x) σ (pret sp) $$ [Hsub] as %ll ⟨Hsub, #Hll⟩
  · rw [is_oterm_some]; iframe Hsub; iframe #
  obtain ⟨y, Hy⟩ := inst_Some_r x σ (some (pret sp)) rfl
  simp only [oinstantiate_t, Hy]
  wp_apply wp_hasPat ll (some y) $$ []
  · iframe #
  simp only [ohas_pat]
  cases Hpy : has_pat y
  · rw [is_oterm_some]
    wp_auto
    wp_apply wp_findCell hs su (sheap (pst sp)) us ll y (by omega) $$ [Hheap Hus]
      as %idx %okb ⟨Hheap, Hus, %Hok, %Hidx⟩
    · iframe Hheap Hus; iframe #
    cases Hfc : find_cell (sheap (pst sp)) us y 0 with
    | none =>
      -- no free cell at that location
      simp only [Hfc, ne_eq, not_true_eq_false, decide_false] at Hok
      subst Hok
      wp_auto
      wp_alloc lf as Hf
      ihave %Hnn := typedPointsto_not_null $$ Hf
      wp_auto
      iapply HΦ
      isplitr [Hsub Hus]
      · iframe Hret; iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
      iexists σ, us; iframe Hsub Hus
      ipureintro
      exact ⟨⟨rfl, rfl⟩, fun h => absurd h Hnn⟩
    | some jj =>
    simp only [Hfc, ne_eq, reduceCtorEq, not_false_eq_true, decide_true] at Hok
    subst Hok
    have Hidx' := Hidx jj Hfc
    obtain ⟨c, Hc, Huj, Hcl⟩ := find_cell_Some _ _ _ _ _ Hfc
    rw [Nat.sub_zero] at Hc
    have Hjj : jj < (sheap (pst sp)).length := (List.getElem?_eq_some_iff.mp Hc).1
    wp_auto
    unfold is_heap
    icases Hheap with ⟨%cells, Hhs, #Hcells⟩
    ihave %Hlenc := BigSepL2.bigSepL2_length $$ Hcells
    ihave %Hlenh := ownSlice_len _ _ _ $$ Hhs
    have Hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z hs.len := by word
    have Hiz : (sint.Z idx).toNat = jj := by word
    list_elem cells jj as cc
    ihave #Hcc := BigSepL2.bigSepL2_lookup (Φ := fun _ c sc => is_cell (GF := GF) c sc)
      Hcc_lookup Hc $$ Hcells
    unfold is_cell
    icases Hcc with ⟨#Hccl, #Hccv⟩
    rw [ite_eq_left Hb]
    icases ownSlice_elem_acc (sint.Z idx) cc hs _ cells Hb.1 (by rw [Hiz]; exact Hcc_lookup) $$ Hhs
      with ⟨Hel, Hclose⟩
    wp_auto
    ihave Hhs := Hclose $$ Hel
    have Hset : cells.set (sint.Z idx).toNat cc = cells := by
      rw [Hiz]; obtain ⟨_, Hcc⟩ := List.getElem?_eq_some_iff.mp Hcc_lookup; subst Hcc; simp
    rw [Hset]
    unfold is_vars at *
    wp_apply wp_matchTerm ly cc.Val' (some v) (some (cval c)) ss σ ld dj vs (svars (pst sp))
      pth.Ret' (pret sp) $$ [Hsub] as %lf1 Hp1
    · rw [is_oterm_some, is_oterm_some]; iframe Hsub; iframe #; ipureintro; exact Hlσ
    unfold match_post
    icases Hp1 with ⟨%σ1, Hsub, %Hl1, (⟨%Hn1, %Hm1⟩ | ⟨%fv, Hf1⟩)⟩
    rotate_left
    · -- the value does not match: record the atom in the failure
      ihave %Hnn := typedPointsto_not_null $$ Hf1
      wp_if_destruct
      · exact absurd rfl Hnn
      iapply HΦ
      isplitr [Hsub Hus]
      · iframe Hret; iexists hs, cs, vs; iframe Hstl Hcond Hvars; iexists cells; iframe Hhs Hcells
      iexists σ1, us; iframe Hsub Hus
      ipureintro
      exact ⟨⟨Hl1, rfl⟩, fun h => absurd h Hnn⟩
    subst Hn1
    wp_auto
    ihave %Hlenu := ownSlice_len _ _ _ $$ Hus
    have Hbu : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z su.len := by word
    rw [ite_eq_left Hbu]
    wp_apply wp_store_slice_index su (sint.Z idx) us true $$ [Hus] as Hus
    · iframe Hus; ipureintro; omega
    rw [Hiz]
    iapply HΦ
    isplitr [Hsub Hus]
    · iframe Hret; iexists hs, cs, vs; iframe Hstl Hcond Hvars; iexists cells; iframe Hhs Hcells
    iexists σ1, us.set jj true; iframe Hsub Hus
    ipureintro
    refine ⟨⟨Hl1, List.length_set⟩, fun _ => Or.inr ⟨rfl, jj, c, ?_, ?_, Hc, ?_, rfl, Hm1⟩⟩
    · rw [Hcl]; exact Hy
    · rw [Hcl]; exact Hpy
    · have : jj < us.length := by omega
      rw [List.getElem?_eq_getElem this]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this,
        Option.getD_some] at Huj
      rw [Huj]
  · -- the location is not resolved yet
    wp_auto
    iapply HΦ
    isplitr [Hsub Hus]
    · iframe Hret; iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
    iexists σ, us; iframe Hsub Hus
    ipureintro
    exact ⟨⟨rfl, rfl⟩, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩

end proof

end Checker
end Perennial
