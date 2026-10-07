/-
Port of `new/checker/fn/countPointsTo.v`.

`checker.countPointsTo` (checker/match.go): the number of points-to atoms
of a disjunct, `count_pts` (MatchSound.lean).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.MatchSound

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The Go code tests the kind code of each atom. -/
theorem is_pts_code (a : cassn) : decide (assn_code a = W64 6) = is_pts a := by
  cases a <;> rfl

theorem is_pure_code (a : cassn) : decide (assn_code a = W64 5) = is_pure a := by
  cases a <;> rfl

theorem count_pts_take_S (atms : List cassn) (k : Nat) (a : cassn) :
    atms[k]? = some a →
    count_pts (atms.take (k + 1)) = count_pts (atms.take k) + if is_pts a then 1 else 0 := by
  intro Hk
  rw [List.take_add_one, Hk, Option.toList_some, count_pts_app]
  simp [count_pts]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_countPointsTo (sa : GoSlice) (dq : DFrac) (las : List Loc) (atms : List cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ sa ↦*{dq} las ∗
        □ ([∗list] la;x ∈ las;atms, is_assn la x) }}
      (App (Val (@! checker.countPointsTo)) (Val #sa))
    {{ RET #(W64 (count_pts atms)); sa ↦*{dq} las }} := by
  wp_start as ⟨Hs, #Has⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HI : (∃ (k : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ k ∗
      "n" ∷ n_ptr ↦ W64 (count_pts (atms.take (sint.nat k))) ∗
      "Hat" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ las.length⌝ : IProp GF) $$ [i n «at»]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem las (sint.nat k) as lcur'
    list_elem atms (sint.nat k) as acur
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l a => is_assn (GF := GF) l a)
      Hlcur'_lookup Hacur_lookup $$ Has
    wp_apply wp_load_slice_index sa (sint.Z k) las _ lcur' Hk.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hlcur'_lookup
    icases is_assn_node _ _ $$ Hcur with ⟨%lL, %lR, %lX, %lY, _, #Hnode, _⟩
    iStructNamed Hnode
    wp_auto
    rw [is_pts_code]
    have HS := count_pts_take_S _ _ acur Hacur_lookup
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    cases Hp : is_pts acur
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, lcur'
      rw [Hk1, HS, Hp]
      iframe
      ipureintro; word
    · wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, lcur'
      rw [Hk1, HS, Hp]
      simp only [↓reduceIte]
      rw [show W64 ((count_pts (atms.take (sint.nat k)) + 1 : Nat) : Int) =
          W64 (count_pts (atms.take (sint.nat k)) : Int) + W64 1 by word]
      iframe
      ipureintro; word
  · rw [List.take_of_length_le (by word)]
    iapply HΦ
    iframe Hs

end proof

end Checker
end Perennial
