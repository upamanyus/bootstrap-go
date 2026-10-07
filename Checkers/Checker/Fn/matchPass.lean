/-
Port of `new/checker/fn/matchPass.v`.

`checker.matchPass` (checker/match.go): one pass of phase 1 over the
points-to atoms not resolved yet. It preserves `phase1_inv`
(MatchSound.lean) and returns how many atoms it resolved.

Lean notes:
* The Go function has its own local `i` next to the range loop's index;
  `wp_auto` allocates both and the Go counter is recovered with `rename_i`
  + `irename` (as in Fn/findCell.lean).
* The Go local `at` is a Lean keyword: its points-to is `Hat` in the loop
  invariant.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.countPointsTo
import Checkers.Checker.Fn.matchAtom

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

theorem wp_matchPass (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (ss : GoSlice) (σ : List (Option term)) (su : GoSlice) (us : List Bool)
    (sdn : GoSlice) (dn : List Bool) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_subst ss σ ∗ su ↦* us ∗ sdn ↦* dn ∗
        ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
           (svars (pst sp)) (pret sp) σ us dn⌝ }}
      (App (App (App (App (App (Val (@! checker.matchPass)) (Val #pth)) (Val #ld)) (Val #ss))
        (Val #su)) (Val #sdn))
    {{ (cnt : w64) (lf : Loc), RET (PairV #cnt #lf);
        is_path pth sp ∗
        ∃ σ' us' dn', is_subst ss σ' ∗ su ↦* us' ∗ sdn ↦* dn' ∗
          ⌜lf = null →
             phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
               (svars (pst sp)) (pret sp) σ' us' dn' ∧
             undone (d_atoms dj) dn' + uint.nat cnt = undone (d_atoms dj) dn⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, Hsub, Hus, Hdn, %Hinv⟩
  ihave #Hdj' : is_disjunct_ro ld dj $$ []
  · iexact Hdj
  unfold is_disjunct_ro
  icases Hdj' with ⟨%sp', %sok, %sa, %lfl, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlena := ownSlice_len _ _ _ $$ Hsa
  iStructNamed Hld
  wp_auto
  rename_i gi_ptr
  irename: gi_ptr ↦ (W64 0) => gi
  ihave HI : (∃ (k cnt : w64) (lcur : Loc) (σk : List (Option term)) (usk dnk : List Bool),
      "i" ∷ i_ptr ↦ k ∗ "gi" ∷ gi_ptr ↦ k ∗
      "n" ∷ n_ptr ↦ cnt ∗
      "Hat" ∷ at_ptr ↦ lcur ∗
      "Hsub" ∷ is_subst ss σk ∗
      "Hus" ∷ su ↦* usk ∗
      "Hdn" ∷ sdn ↦* dnk ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ las.length⌝ ∗
      "%Hcnt" ∷ ⌜uint.Z cnt ≤ sint.Z k⌝ ∗
      "%Hinvk" ∷ ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
                    (svars (pst sp)) (pret sp) σk usk dnk⌝ ∗
      "%Hund" ∷ ⌜undone (d_atoms dj) dnk + uint.nat cnt = undone (d_atoms dj) dn⌝ : IProp GF)
      $$ [i gi n «at» Hsub Hus Hdn]
  · iexists W64 0, W64 0, _, σ, us, dn
    iframe
    ipureintro
    exact ⟨by word, by word, Hinv, by simp⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem las (sint.nat k) as lcur'
    list_elem (d_atoms dj) (sint.nat k) as acur
    have Hklt : sint.nat k < las.length := (List.getElem?_eq_some_iff.mp Hlcur'_lookup).1
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l a => is_assn (GF := GF) l a)
      Hlcur'_lookup Hacur_lookup $$ Has
    wp_apply wp_load_slice_index sa (sint.Z k) las _ lcur' Hk.1 $$ [] with -
    · iframe Hsa; ipureintro; exact Hlcur'_lookup
    icases is_assn_node _ _ $$ Hcur with ⟨%lL, %lR, %lX, %lY, _, #Hnode, _⟩
    iStructNamed Hnode
    wp_auto
    rw [is_pts_code]
    cases Hpts : is_pts acur
    · -- not a points-to atom
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, cnt, lcur', σk, usk, dnk
      iframe
      ipureintro
      exact ⟨by word, by word, Hinvk, Hund⟩
    obtain ⟨x, v, rfl⟩ := is_pts_inv _ Hpts
    obtain ⟨Hlσ, Hlu, Hld, Hwf, Hmap⟩ := Hinvk
    wp_auto
    ihave %Hlendn := ownSlice_len _ _ _ $$ Hdn
    list_elem dnk (sint.nat k) as dcur
    have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sdn.len := by
      have := (List.getElem?_eq_some_iff.mp Hdcur_lookup).1; word
    rw [ite_eq_left Hb]
    wp_apply wp_load_slice_index sdn (sint.Z k) dnk _ dcur Hb.1 $$ [Hdn] with Hdn
    · iframe Hdn; ipureintro; exact Hdcur_lookup
    cases dcur
    · -- not done yet: try to resolve it
      wp_auto
      wp_apply wp_matchAtom pth sp ld dj lcur' x v ss σk su usk $$ [Hpath Hsub Hus]
        as %okb %lf ⟨Hpath, %σ', %us', Hsub, Hus, %Hls, %Hstep⟩
      · iframe Hpath Hsub Hus
        unfold is_disjunct_ro
        iframe #
        ipureintro; exact ⟨⟨Hpl, Hfail⟩, Hlσ, Hlu⟩
      wp_if_destruct
      · have Hstep' := Hstep rfl
        cases okb
        · wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, cnt, lcur', σ', us', dnk
          iframe
          ipureintro
          exact ⟨by word, by word,
            phase1_inv_skip ⟨Hlσ, Hlu, Hld, Hwf, Hmap⟩ Hstep', Hund⟩
        · -- resolved: mark it done
          wp_auto
          rw [ite_eq_left Hb]
          have Hdlt : sint.nat k < dnk.length := (List.getElem?_eq_some_iff.mp Hdcur_lookup).1
          wp_apply wp_store_slice_index sdn (sint.Z k) dnk true $$ [Hdn] as Hdn
          · iframe Hdn; ipureintro; exact ⟨Hb.1, by word⟩
          wp_for_post
          iframe
          iexists k + W64 1, cnt + W64 1, lcur', σ', us', dnk.set (sint.Z k).toNat true
          iframe
          ipureintro
          have Hu := undone_insert _ _ _ _ _ Hacur_lookup Hdcur_lookup
          have Hc1 : uint.nat (cnt + W64 1) = uint.nat cnt + 1 := by word
          refine ⟨by word, by word,
            phase1_inv_step (sint.nat k) ⟨Hlσ, Hlu, Hld, Hwf, Hmap⟩ Hacur_lookup Hdcur_lookup
              Hstep', ?_⟩
          rw [Hc1]
          change undone (d_atoms dj) (dnk.set (sint.nat k) true) + (uint.nat cnt + 1) = _
          omega
      · -- `matchAtom` failed
        wp_for_post
        iapply HΦ
        iframe Hpath
        iexists σ', us', dnk
        iframe Hsub Hus Hdn
        ipureintro; intro h; exact absurd h Hif
    · -- already done
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, cnt, lcur', σk, usk, dnk
      iframe
      ipureintro
      exact ⟨by word, by word, ⟨Hlσ, Hlu, Hld, Hwf, Hmap⟩, Hund⟩
  · -- the pass is over
    iapply HΦ
    iframe Hpath
    iexists σk, usk, dnk
    iframe Hsub Hus Hdn
    ipureintro; intro _; exact ⟨Hinvk, Hund⟩

end proof

end Checker
end Perennial
