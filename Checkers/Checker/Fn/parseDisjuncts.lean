/-
Port of `new/checker/fn/parseDisjuncts.v`.

`checker.parseDisjuncts` (checker/match.go): parse every disjunct of a
postcondition, left to right.

Every disjunct that parsed without failure entails the whole
postcondition: it entails the member of the top-level `∨` chain it was
parsed from (`wp_parseDisjunct`), which entails the chain
(`assn_disjuncts_sound`).

Lean notes:
* Rocq's `lit_singleton` (for `wp_slice_literal`'s insert form) is not
  needed: the Lean `wp_slice_literal` hands back the literal list.
-/
import Checkers.Checker.Fn.parseDisjunct

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

/-- The slice of `*disjunct` the function returns. -/
def is_disjuncts (s : GoSlice) (djs : List cdisjunct) : IProp GF :=
  iprop(∃ lds : List Loc, s ↦* lds ∗ ownSliceCap Loc s (DFrac.own 1) ∗
                     [∗list] ld;dj ∈ lds;djs, is_disjunct ld dj)

theorem wp_parseDisjuncts (lP : Loc) (P : cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_assn lP P }}
      (App (Val (@! checker.parseDisjuncts)) (Val #lP))
    {{ (s : GoSlice) (djs : List cdisjunct), RET #s;
        is_disjuncts s djs ∗
        ⌜∀ dj, dj ∈ djs → d_fail dj = false → dj_entails dj P⌝ }} := by
  wp_start as #HP
  wp_auto
  wp_apply wp_collectDisjuncts lP (some P) $$ [] as %sr Hr
  · rw [is_oassn_some]; iframe #
  unfold is_assns
  icases Hr with ⟨%las, Hsr, Hsrc, #Hlas⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hlas
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsr
  ihave HI : (∃ (n : w64) (lcur : Loc) (so : GoSlice) (lds : List Loc) (djs : List cdisjunct),
      "i" ∷ i_ptr ↦ n ∗
      "a" ∷ a_ptr ↦ lcur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hso" ∷ so ↦* lds ∗
      "Hsoc" ∷ ownSliceCap Loc so (DFrac.own 1) ∗
      "Hds" ∷ ([∗list] ld;dj ∈ lds;djs, is_disjunct ld dj) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ las.length⌝ ∗
      "%Hsnd" ∷ ⌜∀ dj, dj ∈ djs → d_fail dj = false → dj_entails dj P⌝ : IProp GF) $$ [i a out]
  · iexists _, _, slice.nil, [], []
    ihave Hnil := ownSlice_nil (GF := GF) (V := Loc) (DFrac.own 1)
    ihave Hnilc := ownSliceCap_nil (GF := GF) (V := Loc)
    iframe i a out Hnil Hnilc
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro
    exact ⟨by word, fun _ h => by simp at h⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem las (sint.nat n) as lx
    list_elem (oassn_disjuncts (some P)) (sint.nat n) as ox
    ihave #Hox := BigSepL2.bigSepL2_lookup (Φ := fun _ l y => is_oassn (GF := GF) l y)
      Hlx_lookup Hox_lookup $$ Hlas
    wp_apply wp_load_slice_index sr (sint.Z n) las _ lx Hn.1 $$ [Hsr] as Hsr
    · iframe Hsr; ipureintro; exact Hlx_lookup
    try wp_auto
    wp_apply wp_parseDisjunct lx ox $$ [] as %ld %dj ⟨Hdj, %Hdj⟩
    · iframe #
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, _⟩
    try wp_auto
    wp_apply wp_slice_append (t := go.GoType.PointerType checker.disjunct.ty) so lds _ [ld]
      (DFrac.own 1) $$ [Hso Hsoc Hsl] as %so' ⟨Hso, Hsoc, -⟩
    · iframe Hso Hsoc Hsl
    try wp_auto
    wp_for_post
    iframe HΦ Hsr Hsrc
    iexists n + W64 1, lx, so', lds ++ [ld], djs ++ [dj]
    iframe i a out Hso Hsoc
    isplitl [Hds Hdj]
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe Hds Hdj
    ipureintro
    refine ⟨by word, ?_⟩
    intro dj' Hin Hf
    rcases List.mem_append.mp Hin with Hin | Hin
    · exact Hsnd dj' Hin Hf
    · simp only [List.mem_singleton] at Hin
      subst Hin
      obtain ⟨y, rfl, Hent⟩ := Hdj Hf
      intro ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V
      exact (Hent ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V).trans
        (assn_disjuncts_sound V P y (List.mem_of_getElem? Hox_lookup))
  · iapply HΦ $$ %so %djs
    unfold is_disjuncts
    isplitl [Hso Hsoc Hds]
    · iexists lds
      iframe Hso Hsoc Hds
    · ipureintro; exact Hsnd

end proof

end Checker
end Perennial
