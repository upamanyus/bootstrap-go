/-
Port of `new/checker/fn/Verify.v`.

`checker.Verify` (checker/check.go): every path satisfies some disjunct
of the postcondition.

The postcondition is parsed once (`parseDisjuncts`) and each parsed
disjunct frozen (`is_disjunct_freeze`), since from then on it is only
read, once per path (`anyDisjunct`). A nil result then says that every
path satisfies a disjunct that parsed without failure, and such a
disjunct entails the postcondition.

Lean notes:
* Rocq's `wp_Verify_aux` (with variables renamed away from the Go locals)
  and its restatement `wp_Verify` are one theorem: Lean has no naming trap.
* `path_ok` mentions only ghost-state-independent facts, so it is defined
  outside the proof section.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.VerifyDef
import Checkers.Checker.Fn.parseDisjuncts
import Checkers.Checker.Fn.anyDisjunct

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- What a path needs from the postcondition. -/
def path_ok (vs : List sort) (P : cassn) (sp : spath) : Prop :=
  ∃ dj, d_fail dj = false ∧ path_sat_dj vs sp dj ∧ dj_entails dj P

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem big_disjunct_freeze (lds : List Loc) (djs : List cdisjunct) :
    ([∗list] ld;dj ∈ lds;djs, is_disjunct (GF := GF) ld dj) ⊢
      |==> [∗list] ld;dj ∈ lds;djs, is_disjunct_ro (GF := GF) ld dj := by
  induction lds generalizing djs with
  | nil =>
    cases djs with
    | nil => iintro -; imodintro; iapply BigSepL2.bigSepL2_nil.2; iempintro
    | cons dj djs => iintro H; icases BigSepL2.bigSepL2_nil_inv_left $$ H with %h; cases h
  | cons ld lds IH =>
    cases djs with
    | nil => iintro H; icases BigSepL2.bigSepL2_nil_inv_right $$ H with %h; cases h
    | cons dj djs =>
      iintro H
      icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨H, Hs⟩
      imod is_disjunct_freeze _ _ $$ H with H
      imod IH djs $$ Hs with Hs
      imodintro
      iapply BigSepL2.bigSepL2_cons.2
      iframe H Hs

theorem is_disjuncts_freeze (sd : GoSlice) (djs : List cdisjunct) :
    is_disjuncts (GF := GF) sd djs ⊢ |==> is_disjuncts_ro sd djs := by
  unfold is_disjuncts is_disjuncts_ro
  iintro ⟨%lds, Hs, -, Hl⟩
  imod ownSlice_persist _ _ _ $$ Hs with #Hs
  imod big_disjunct_freeze lds djs $$ Hl with Hl
  imodintro
  iexists lds
  iframe Hs Hl

theorem wp_Verify (s : GoSlice) (ps : List spath) (sv : GoSlice) (vars : List sort)
    (lpost : Loc) (post : cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_paths s ps ∗ is_sorts sv vars ∗
        is_assn lpost post }}
      (App (App (App (Val (@! checker.Verify)) (Val #s)) (Val #sv)) (Val #lpost))
    {{ (lf : Loc), RET #lf;
        ⌜lf = null → ∀ sp, sp ∈ ps → path_ok vars post sp⌝ }} := by
  wp_start as ⟨Hps, #Hvs, #HP⟩
  unfold is_paths
  icases Hps with ⟨%xs, Hsps, Hxs⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsps
  wp_auto
  wp_apply wp_parseDisjuncts lpost post $$ [] as %sd %djs ⟨Hds, %Hsnd⟩
  · iframe #
  imod is_disjuncts_freeze _ _ $$ Hds with #Hds
  ihave HI : (∃ (n pin : w64) (pcur : checker.Path),
      "i" ∷ i_ptr ↦ n ∗ "pi" ∷ pi_ptr ↦ pin ∗ "p" ∷ p_ptr ↦ pcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ xs.length⌝ ∗
      "%Hok" ∷ ⌜∀ (k : Nat) (sp : spath), k < sint.nat n → ps[k]? = some sp →
                path_ok vars post sp⌝ : IProp GF) $$ [i pi p]
  · iexists W64 0, _, _
    iframe
    ipureintro
    exact ⟨by word, fun k _ hk _ => by word⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem xs (sint.nat n) as x
    list_elem ps (sint.nat n) as sp
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ x p => is_path (GF := GF) x p)
      Hx_lookup Hsp_lookup $$ Hxs with ⟨Hp, Hxs⟩
    wp_apply wp_load_slice_index s (sint.Z n) xs _ x Hn.1 $$ [Hsps] as Hsps
    · iframe Hsps; ipureintro; exact Hx_lookup
    wp_apply wp_anyDisjunct x sp sd djs sv vars $$ [Hp] as %b ⟨Hp, %Hb⟩
    · iframe Hp Hds Hvs
    ihave Hxs := Hxs $$ Hp
    cases b with
    | true =>
      -- this path is fine: on to the next
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, _, _
      iframe
      ipureintro
      refine ⟨by word, fun k sp' hk hsp' => ?_⟩
      by_cases hkn : k = sint.nat n
      · subst hkn
        rw [Hsp_lookup] at hsp'
        cases hsp'
        obtain ⟨dj, Hin, Hf, Hsat⟩ := Hb rfl
        exact ⟨dj, Hf, Hsat, Hsnd dj Hin Hf⟩
      · exact Hok k sp' (by word) hsp'
    | false =>
      -- no disjunct matches this path
      wp_auto
      wp_alloc lfail as Hfail
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hfail
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro
      intro Hnull
      exact absurd Hnull Hnn
  · -- every path has been checked
    iapply HΦ
    ipureintro
    intro _ sp Hin
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem Hin
    exact Hok k sp (by word) (by rw [List.getElem?_eq_getElem hk, hkeq])

end proof

end Checker
end Perennial
