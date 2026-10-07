/-
Port of `new/checker/fn/anyDisjunct.v`.

`checker.anyDisjunct` (checker/check.go): does path `p` satisfy some
disjunct of the (parsed, frozen) postcondition?
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.VerifyDef
import Checkers.Checker.Fn.checkDisjunct

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

/-- The parsed postcondition, frozen: `Verify` only reads it. -/
def is_disjuncts_ro (s : GoSlice) (djs : List cdisjunct) : IProp GF :=
  iprop(∃ lds : List Loc, s ↦*□ lds ∗ [∗list] ld;dj ∈ lds;djs, is_disjunct_ro ld dj)

instance is_disjuncts_ro_persistent (s : GoSlice) (djs : List cdisjunct) :
    Persistent (is_disjuncts_ro (GF := GF) s djs) := by
  unfold is_disjuncts_ro; infer_instance

theorem wp_anyDisjunct (pp : checker.Path) (sp : spath) (sd : GoSlice)
    (djs : List cdisjunct) (svs : GoSlice) (vs : List sort) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pp sp ∗ is_disjuncts_ro sd djs ∗
        is_sorts svs vs }}
      (App (App (App (Val (@! checker.anyDisjunct)) (Val #pp)) (Val #sd)) (Val #svs))
    {{ (b : Bool), RET #b;
        is_path pp sp ∗
        ⌜b = true → ∃ dj, dj ∈ djs ∧ d_fail dj = false ∧ path_sat_dj vs sp dj⌝ }} := by
  wp_start as ⟨Hp, #Hds, #Hvs⟩
  unfold is_disjuncts_ro
  icases Hds with ⟨%lds, #Hsd, #Hlds⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hlds
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsd
  wp_auto
  ihave HI : (∃ (n : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ n ∗ "d" ∷ d_ptr ↦ lcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ lds.length⌝ : IProp GF) $$ [i d]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem lds (sint.nat n) as lcur'
    list_elem djs (sint.nat n) as dj
    ihave #Hdj := BigSepL2.bigSepL2_lookup (Φ := fun _ l d => is_disjunct_ro (GF := GF) l d)
      Hlcur'_lookup Hdj_lookup $$ Hlds
    wp_apply wp_load_slice_index sd (sint.Z n) lds _ lcur' Hn.1 $$ [] with -
    · iframe Hsd; ipureintro; exact Hlcur'_lookup
    wp_apply wp_checkDisjunct pp sp lcur' dj svs vs $$ [Hp] as %lf ⟨Hp, %Hlf⟩
    · iframe Hp Hdj Hvs
    wp_if_destruct
    · -- this disjunct matches
      wp_for_post
      iapply HΦ
      iframe Hp
      ipureintro
      intro _
      obtain ⟨Hf, Hsat⟩ := Hlf rfl
      exact ⟨dj, List.mem_of_getElem? Hdj_lookup, Hf, Hsat⟩
    · wp_for_post
      iframe
      iexists n + W64 1, lcur'
      iframe
      ipureintro; word
  · iapply HΦ
    iframe Hp
    ipureintro; intro h; cases h

end proof

end Checker
end Perennial
