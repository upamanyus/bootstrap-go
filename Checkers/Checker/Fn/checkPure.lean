/-
Port of `new/checker/fn/checkPure.v`.

`checker.checkPure` (checker/match.go): phase 2 of `checkDisjunct`. Each
pure atom, instantiated with the substitution phase 1 built, must mention
no pattern variable and be justified by the path condition: `pure_ok`
(MatchSound.lean).

Lean notes:
* `pure_ok_step` is pure and stated before the proof section.
* The Go local `at` is a Lean keyword, so the loop invariant names its
  points-to `Hat` (`wp_auto` finds it anyway).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.hasPat
import Checkers.Checker.Fn.condHolds
import Checkers.Checker.Fn.countPointsTo

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

theorem pure_ok_step (pc : List term) (atms : List cassn) (σ : List (Option term)) (r : term)
    (k : Nat) (acur : cassn) :
    atms[k]? = some acur →
    (∀ (j : Nat) (x : term), j < k → atms[j]? = some (CAPure x) →
       ∃ y, instantiate_t x σ (some r) = some y ∧ has_pat y = false ∧
         cond_holds pc (some y) = true) →
    (∀ x, acur = CAPure x →
       ∃ y, instantiate_t x σ (some r) = some y ∧ has_pat y = false ∧
         cond_holds pc (some y) = true) →
    (∀ (j : Nat) (x : term), j < k + 1 → atms[j]? = some (CAPure x) →
       ∃ y, instantiate_t x σ (some r) = some y ∧ has_pat y = false ∧
         cond_holds pc (some y) = true) := by
  intro Hk Hpre Hcur j x Hj Hx
  by_cases Hjk : j = k
  · subst Hjk; rw [Hk] at Hx; cases Hx; exact Hcur x rfl
  · exact Hpre j x (by omega) Hx

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_checkPure (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (ss : GoSlice) (σ : List (Option term)) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_subst ss σ }}
      (App (App (App (Val (@! checker.checkPure)) (Val #pth)) (Val #ld)) (Val #ss))
    {{ (lf : Loc), RET #lf;
        is_path pth sp ∗ is_subst ss σ ∗
        ⌜lf = null → pure_ok (spc (pst sp)) (d_atoms dj) σ (pret sp)⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, Hsub⟩
  unfold is_path
  icases Hpath with ⟨#Hret, Hst⟩
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
  unfold is_disjunct_ro
  icases Hdj with ⟨%sp', %sok, %sa, %lf, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlena := ownSlice_len _ _ _ $$ Hsa
  iStructNamed Hld
  wp_auto
  ihave HI : (∃ (k : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ k ∗
      "Hat" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ las.length⌝ ∗
      "%Hpre" ∷ ⌜∀ (j : Nat) (x : term), j < sint.nat k → (d_atoms dj)[j]? = some (CAPure x) →
         ∃ y, instantiate_t x σ (some (pret sp)) = some y ∧ has_pat y = false ∧
              cond_holds (spc (pst sp)) (some y) = true⌝ : IProp GF) $$ [i «at»]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro j x Hj; exact absurd Hj (by simp)
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem las (sint.nat k) as lcur'
    list_elem (d_atoms dj) (sint.nat k) as acur
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l a => is_assn (GF := GF) l a)
      Hlcur'_lookup Hacur_lookup $$ Has
    wp_apply wp_load_slice_index sa (sint.Z k) las _ lcur' Hk.1 $$ [] with _
    · iframe Hsa; ipureintro; exact Hlcur'_lookup
    icases is_assn_node _ _ $$ Hcur with ⟨%lL, %lR, %lX, %lY, _, #Hnode, _, _, #HX, _⟩
    iStructNamed Hnode
    wp_auto
    rw [is_pure_code]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    cases Hpure : is_pure acur
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, lcur'
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [Hk1]
      refine pure_ok_step _ _ σ _ _ acur Hacur_lookup Hpre ?_
      intro x' Hx'; subst Hx'; simp [is_pure] at Hpure
    · obtain ⟨x, rfl⟩ := is_pure_inv _ Hpure
      simp only [assn_x] at *
      wp_auto
      wp_apply wp_instantiate_ret lX ss pth.Ret' (some x) σ (pret sp) $$ [Hsub]
        as %lt ⟨Hsub, #Hlt⟩
      · iframe Hsub; iframe #
      obtain ⟨y, Hy⟩ := inst_Some_r x σ (some (pret sp)) rfl
      rw [show oinstantiate_t (some x) σ (some (pret sp)) = instantiate_t x σ (some (pret sp))
        from rfl, Hy]
      wp_apply wp_hasPat lt (some y) $$ []
      · iframe #
      rw [show ohas_pat (some y) = has_pat y from rfl]
      cases Hpy : has_pat y
      · wp_auto
        wp_apply wp_condHolds cs (spc (pst sp)) lt (some y) $$ [Hcond] as Hcond
        · iframe Hcond; rw [is_oterm_some]; iframe #
        cases Hch : cond_holds (spc (pst sp)) (some y)
        · wp_auto
          wp_alloc lf' as Hf
          ihave %Hnn := typedPointsto_not_null $$ Hf
          wp_auto
          wp_for_post
          iapply HΦ
          iframe Hsub Hret
          isplitl [Hstl Hheap Hcond]
          · iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
          · ipureintro; intro H; exact absurd H Hnn
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, lcur'
          iframe
          ipureintro
          refine ⟨by word, ?_⟩
          rw [Hk1]
          refine pure_ok_step _ _ σ _ _ _ Hacur_lookup Hpre ?_
          intro x' Hx'; cases Hx'; exact ⟨y, Hy, Hpy, Hch⟩
      · wp_auto
        wp_alloc lf' as Hf
        ihave %Hnn := typedPointsto_not_null $$ Hf
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Hsub Hret
        isplitl [Hstl Hheap Hcond]
        · iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
        · ipureintro; intro H; exact absurd H Hnn
  · iapply HΦ
    iframe Hsub Hret
    isplitl [Hstl Hheap Hcond]
    · iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
    · ipureintro
      intro _ j x Hx
      apply Hpre j x _ Hx
      have := (List.getElem?_eq_some_iff.mp Hx).1
      word

end proof

end Checker
end Perennial
