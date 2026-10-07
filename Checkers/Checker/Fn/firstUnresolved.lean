/-
Port of `new/checker/fn/firstUnresolved.v`.

`checker.firstUnresolved` (checker/match.go): the first points-to atom
phase 1 left unresolved, reported in `matchHeap`'s failure. Only safety
matters here: the result is a diagnostic nothing reads back.

Lean notes:
* The Go function has its own local `i` next to the range loop's index; as
  in Fn/findCell.lean, `wp_auto` allocates both and the Go counter is
  recovered with `rename_i` + `irename`.
* The Go local `at` is a Lean keyword: its points-to is named `Hat` in the
  loop invariant (`wp_auto` finds it regardless of the name).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.countPointsTo

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

theorem wp_firstUnresolved (ld : Loc) (dj : cdisjunct) (sdn : GoSlice) (dn : List Bool) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_disjunct_ro ld dj ∗ sdn ↦* dn ∗
        ⌜dn.length = (d_atoms dj).length⌝ }}
      (App (App (Val (@! checker.firstUnresolved)) (Val #ld)) (Val #sdn))
    {{ (lat : Loc), RET #lat; sdn ↦* dn }} := by
  wp_start as ⟨#Hdj, Hdn, %Hlen⟩
  unfold is_disjunct_ro
  icases Hdj with ⟨%sp, %sok, %sa, %lf, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlena := ownSlice_len _ _ _ $$ Hsa
  ihave %Hlend := ownSlice_len _ _ _ $$ Hdn
  iStructNamed Hld
  wp_auto
  rename_i gi_ptr
  irename: gi_ptr ↦ (W64 0) => gi
  ihave HI : (∃ (k : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ k ∗ "gi" ∷ gi_ptr ↦ k ∗ "Hat" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ las.length⌝ : IProp GF) $$ [i gi «at»]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem las (sint.nat k) as lcur'
    list_elem (d_atoms dj) (sint.nat k) as acur
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l a => is_assn (GF := GF) l a)
      Hlcur'_lookup Hacur_lookup $$ Has
    wp_apply wp_load_slice_index sa (sint.Z k) las _ lcur' Hk.1 $$ [] with -
    · iframe Hsa; ipureintro; exact Hlcur'_lookup
    icases is_assn_node _ _ $$ Hcur with ⟨%lL, %lR, %lX, %lY, _, #Hnode, _⟩
    iStructNamed Hnode
    wp_auto
    rw [is_pts_code]
    have Hk1 : sint.Z (k + W64 1) ≤ las.length := by word
    cases Hp : is_pts acur
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, lcur'
      iframe
      ipureintro; word
    · wp_auto
      have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sdn.len := by
        have := (List.getElem?_eq_some_iff.mp Hacur_lookup).1; word
      list_elem dn (sint.nat k) as dcur
      rw [ite_eq_left Hb]
      wp_apply wp_load_slice_index sdn (sint.Z k) dn _ dcur Hb.1 $$ [Hdn] with Hdn
      · iframe Hdn; ipureintro; exact Hdcur_lookup
      cases dcur
      · -- unresolved: return it
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Hdn
      · wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, lcur'
        iframe
        ipureintro; word
  · iapply HΦ
    iframe Hdn

end proof

end Checker
end Perennial
