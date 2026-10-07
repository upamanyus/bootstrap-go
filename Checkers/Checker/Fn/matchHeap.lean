/-
Port of `new/checker/fn/matchHeap.v`.

`checker.matchHeap` (checker/match.go): phase 1 of `checkDisjunct`.
`matchPass` runs until every points-to atom is resolved; a pass that
resolves nothing is a failure. Partial correctness: the loop maintains
`phase1_inv` (MatchSound.lean), and `remaining` is the number of
unresolved points-to atoms.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.countPointsTo
import Checkers.Checker.Fn.firstUnresolved
import Checkers.Checker.Fn.matchPass

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

theorem wp_matchHeap (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (ss : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_subst ss (List.replicate (d_pats dj).length none) }}
      (App (App (App (Val (@! checker.matchHeap)) (Val #pth)) (Val #ld)) (Val #ss))
    {{ (lf : Loc), RET #lf;
        is_path pth sp ∗
        ∃ σ, is_subst ss σ ∗
          ⌜lf = null → ∃ us dn,
             phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
               (svars (pst sp)) (pret sp) σ us dn ∧ undone (d_atoms dj) dn = 0⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, Hsub⟩
  icases is_disjunct_ro_open _ _ $$ Hdj with
    ⟨%sp', %sok, %sa, %lfl, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlena := ownSlice_len _ _ _ $$ Hsa
  iStructNamed Hld
  unfold is_path
  icases Hpath with ⟨#Hret, Hst⟩
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
  unfold is_heap
  icases Hheap with ⟨%cells, Hhs, #Hcells⟩
  ihave %Hlenc := BigSepL2.bigSepL2_length $$ Hcells
  ihave %Hlenh := ownSlice_len _ _ _ $$ Hhs
  wp_auto
  wp_apply wp_slice_make2 as %su ⟨Hus, -⟩
  · ipureintro; word
  wp_apply wp_slice_make2 as %sdn ⟨Hdn, -⟩
  · ipureintro; word
  wp_apply wp_countPointsTo sa DFrac.discard las (d_atoms dj) $$ [] as -
  · iframe #
  ihave Hpath : is_path pth sp $$ [Hstl Hhs Hcond]
  · unfold is_path is_state is_heap
    iframe Hret
    iexists hs, cs, vs
    iframe Hstl Hcond Hvars
    iexists cells; iframe Hhs Hcells
  rw [count_pts_undone]
  have Hinit := phase1_inv_init (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
    (svars (pst sp)) (pret sp)
  have Eh : sint.nat hs.len = (sheap (pst sp)).length := by omega
  have Ea : sint.nat sa.len = (d_atoms dj).length := by omega
  rw [Eh, Ea, show (zero_val Bool) = false from rfl]
  ihave HI : (∃ (σk : List (Option term)) (usk dnk : List Bool),
      "remaining" ∷ remaining_ptr ↦ W64 (undone (d_atoms dj) dnk) ∗
      "Hsub" ∷ is_subst ss σk ∗
      "Hus" ∷ su ↦* usk ∗
      "Hdn" ∷ sdn ↦* dnk ∗
      "%Hinvk" ∷ ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
                    (svars (pst sp)) (pret sp) σk usk dnk⌝ : IProp GF)
      $$ [remaining Hsub Hus Hdn]
  · iexists _, _, _
    iframe
    ipureintro; exact Hinit
  wp_for HI
  have Hule := undone_le (d_atoms dj) dnk
  wp_if_destruct
  · wp_apply wp_matchPass pth sp ld dj ss σk su usk sdn dnk $$ [Hpath Hsub Hus Hdn]
      as %cnt %lf ⟨Hpath, %σ', %us', %dn', Hsub, Hus, Hdn, %Hst⟩
    · iframe Hpath Hsub Hus Hdn Hdj; ipureintro; exact Hinvk
    wp_if_destruct
    · obtain ⟨Hinv', Hund'⟩ := Hst rfl
      wp_if_destruct
      · -- no progress: report the first unresolved atom
        wp_apply wp_firstUnresolved ld dj sdn dn' $$ [Hdn] as %lat Hdn
        · iframe Hdn Hdj; ipureintro; exact Hinv'.p1_len_done
        wp_alloc lf' as Hf
        ihave %Hnn := typedPointsto_not_null $$ Hf
        wp_auto
        wp_for_post
        iapply HΦ
        isplitl [Hpath]
        · unfold is_path is_state is_heap; iexact Hpath
        iexists σ'; iframe Hsub
        ipureintro; intro h; exact absurd h Hnn
      · wp_for_post
        iframe
        iexists σ', us', dn'
        rw [show W64 (undone (d_atoms dj) dnk : Int) - cnt = W64 (undone (d_atoms dj) dn' : Int)
          by word]
        iframe
        ipureintro; exact Hinv'
    · -- the pass failed
      wp_for_post
      iapply HΦ
      isplitl [Hpath]
      · unfold is_path is_state is_heap; iexact Hpath
      iexists σ'; iframe Hsub
      ipureintro; intro h; exact absurd h Hif
  · -- nothing left to resolve
    have Hz : undone (d_atoms dj) dnk = 0 := by word
    iapply HΦ
    isplitl [Hpath]
    · unfold is_path is_state is_heap; iexact Hpath
    iexists σk; iframe Hsub
    ipureintro; intro _; exact ⟨usk, dnk, Hinvk, Hz⟩

end proof

end Checker
end Perennial
