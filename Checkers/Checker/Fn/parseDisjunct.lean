/-
Port of `new/checker/fn/parseDisjunct.v`.

`checker.parseDisjunct` (checker/match.go): peel the leading `AExists`
binders off one disjunct of a postcondition, recording each binder's
sort, and flatten the separating conjunction underneath.

A pattern variable bound twice, a nil disjunct, and a body that is not a
separating conjunction of atoms all set `d.fail`. A disjunct that parsed
without failure entails the assertion it was parsed from
(ParseSound.lean).

Lean notes:
* `is_disjunct_fail` takes the pure premises (`lf' ≠ null`, the length
  agreement) as Lean hypotheses rather than as `⌜…⌝ -∗`.
* The loop condition `body != nil && body.Kind == AExists` is evaluated
  first with `wp_wand` against `oassn_is_exists` (as Rocq's `wp_wand_r`).
-/
import Checkers.Checker.ParseSound

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The loop condition `body != nil && body.Kind == AExists`. -/
def oassn_is_exists : Option cassn → Bool
  | some (CAExists _ _ _) => true
  | _ => false

theorem oassn_is_exists_true (ob : Option cassn) :
    oassn_is_exists ob = true → ∃ k s p, ob = some (CAExists k s p) := by
  cases ob with
  | none => simp [oassn_is_exists]
  | some b => cases b <;> simp [oassn_is_exists]

def dj_failed (dj : cdisjunct) : cdisjunct :=
  mkDisjunct (d_pats dj) (d_pat_ok dj) (d_atoms dj) true

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- Storing a non-nil `*Failure` into `d.fail`. -/
theorem is_disjunct_fail (ld : Loc) (dj : cdisjunct) (sp sok sa : GoSlice) (las : List Loc)
    (lf' : Loc) (Hnn : lf' ≠ null) (Hlen : (d_pats dj).length = (d_pat_ok dj).length) :
    ld ↦ checker.disjunct.mk sp sok sa lf' ∗
    sp ↦* ((d_pats dj).map sort_code) ∗
    ownSliceCap w64 sp (DFrac.own 1) ∗
    sok ↦* d_pat_ok dj ∗
    ownSliceCap Bool sok (DFrac.own 1) ∗
    sa ↦* las ∗
    ownSliceCap Loc sa (DFrac.own 1) ∗
    ([∗list] la;y ∈ las;d_atoms dj, is_assn la y) ⊢
    is_disjunct (GF := GF) ld (dj_failed dj) := by
  iintro ⟨Hs, Hp, Hpc, Hok, Hokc, Ha, Hac, Hats⟩
  unfold is_disjunct
  iexists sp, sok, sa, lf', las
  simp only [dj_failed]
  iframe
  ipureintro
  exact ⟨Hlen, by simp [Hnn]⟩

theorem wp_parseDisjunct (lx : Loc) (x : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oassn lx x }}
      (App (Val (@! checker.parseDisjunct)) (Val #lx))
    {{ (ld : Loc) (dj : cdisjunct), RET #ld;
        is_disjunct ld dj ∗
        ⌜d_fail dj = false → ∃ y, x = some y ∧ dj_entails dj y⌝ }} := by
  wp_start as #Hx
  wp_auto
  ihave Hdj : is_disjunct (GF := GF) «$r0_ptr» (mkDisjunct [] [] [] false) $$ [«$r0»]
  · unfold is_disjunct
    iexists slice.nil, slice.nil, slice.nil, null, []
    ihave Hn1 := ownSlice_nil (GF := GF) (V := w64) (DFrac.own 1)
    ihave Hc1 := ownSliceCap_nil (GF := GF) (V := w64)
    ihave Hn2 := ownSlice_nil (GF := GF) (V := Bool) (DFrac.own 1)
    ihave Hc2 := ownSliceCap_nil (GF := GF) (V := Bool)
    ihave Hn3 := ownSlice_nil (GF := GF) (V := Loc) (DFrac.own 1)
    ihave Hc3 := ownSliceCap_nil (GF := GF) (V := Loc)
    simp only [List.map_nil]
    isplitl [«$r0»]
    · iExactEq «$r0»; rfl
    iframe Hn1 Hc1 Hn2 Hc2 Hn3 Hc3
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro
    exact ⟨rfl, by simp⟩
  ihave HI : (∃ (dj : cdisjunct) (lb : Loc) (ob : Option cassn),
      "body" ∷ body_ptr ↦ lb ∗
      "Hdj" ∷ is_disjunct «$r0_ptr» dj ∗
      "Hb" ∷ is_oassn lb ob ∗
      "%Hfl" ∷ ⌜d_fail dj = false⌝ ∗
      "%Hat" ∷ ⌜d_atoms dj = []⌝ ∗
      "%Hsem" ∷ ⌜∀ b, ob = some b → ∃ y, x = some y ∧ binders_entails dj b y⌝ : IProp GF)
    $$ [body Hdj]
  · iexists _, lx, x
    iframe body Hdj Hx
    ipureintro
    refine ⟨rfl, rfl, ?_⟩
    intro b Hb
    refine ⟨b, Hb, ?_⟩
    intro ext' ffi' _ _ _ hlc' GF' hG' sem' V
    exact binders_interp_init V _ b rfl
  wp_for HI
  icases Hb with #Hb
  iapply wp_wand (Φ := fun v => iprop(⌜v = #(oassn_is_exists ob)⌝ ∗ body_ptr ↦ lb)) $$ [body]
  · ihave %Hnull := is_oassn_null _ _ $$ Hb
    cases ob with
    | none =>
      obtain rfl : lb = null := Hnull.mpr rfl
      wp_auto
      iframe; ipureintro; rfl
    | some b =>
      have Hnn : lb ≠ null := fun h => by simp at Hnull; exact Hnull h
      rw [is_oassn_some]
      icases is_assn_node _ _ $$ Hb with ⟨%lL, %lR, %lX, %lY, %Hwf, #Hnode, -⟩
      iStructNamed Hnode
      simp only [Hnn, decide_false, Bool.not_false]
      cases b <;> (simp only [assn_code]; wp_auto; iframe; ipureintro; rfl)
  iintro %v ⟨%Hv, body⟩
  subst Hv
  cases Hex : oassn_is_exists ob with
  | true =>
    -- one more binder
    obtain ⟨k, srt, p, rfl⟩ := oassn_is_exists_true _ Hex
    rw [is_oassn_some]
    icases is_assn_node _ _ $$ Hb with ⟨%lL, %lR, %lX, %lY, %Hidx, #Hnode, #HL, -⟩
    simp only [assn_idx_wf, assn_code, assn_var, assn_sort, assn_l, idx_wf] at *
    iStructNamed Hnode
    simp only [decide_true, ↓reduceIte]
    wp_auto
    ihave %Hlen0 := is_disjunct_wf _ _ [] SInt false $$ Hdj
    simp only [sort_env_wf, disjunct_env] at Hlen0
    wp_apply wp_disjunct__growPats $$ [Hdj] as Hdj
    · iframe
    rw [Hidx]
    unfold is_disjunct
    icases Hdj with ⟨%sp, %sok, %sa, %lf, %las, Hs, Hp, Hpc, Hok, Hokc, Ha, Hac, #Hats,
      %Hlen, %Hf⟩
    obtain ⟨Hk1, Hk2⟩ := grow_pats_lookup dj k
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hok
    ihave %Hl3 := ownSlice_len _ _ _ $$ Hp
    simp only [List.length_map] at Hl3
    have Hsk : sint.Z (W64 k) = (k : Int) := by word
    wp_auto
    simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z sok.len from by word,
      ↓reduceIte]
    obtain ⟨okk, Hokk⟩ : ∃ b, (d_pat_ok (grow_pats dj k))[k]? = some b :=
      ⟨_, List.getElem?_eq_getElem Hk2⟩
    wp_apply wp_load_slice_index sok (sint.Z (W64 k)) _ _ okk (by word) $$ [Hok] as Hok
    · iframe Hok; ipureintro; rw [Hsk]; exact Hokk
    cases okk with
    | true =>
      -- the same pattern variable bound twice
      wp_auto
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
      wp_for_post
      iapply HΦ $$ %_ %(dj_failed (grow_pats dj k))
      isplitl [Hs Hp Hpc Hok Hokc Ha Hac]
      · iexists sp, sok, sa, _, las
        simp only [dj_failed]
        iframe # ∗
        ipureintro
        exact ⟨Hlen, by simp [Hnn]⟩
      · ipureintro; simp [dj_failed]
    | false =>
      -- record the binder and move on to its body
      have Hnot : (d_pat_ok (grow_pats dj k))[k]? ≠ some true := by rw [Hokk]; simp
      wp_auto
      simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z sp.len from by word,
        ↓reduceIte]
      wp_apply wp_store_slice_index sp (sint.Z (W64 k)) _ (sort_code srt) $$ [Hp] as Hp
      · iframe Hp; ipureintro; simp only [List.length_map]; word
      try wp_auto
      simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z sok.len from by word,
        ↓reduceIte]
      wp_apply wp_store_slice_index sok (sint.Z (W64 k)) _ true $$ [Hok] as Hok
      · iframe Hok; ipureintro; word
      try wp_auto
      wp_for_post
      iframe HΦ d
      iexists bind_pat (grow_pats dj k) k srt, lL, some p
      rw [show (sint.Z (W64 k)).toNat = k by word, ← List.map_set]
      iframe body HL
      isplitl
      · iexists sp, sok, sa, lf, las
        simp only [bind_pat]
        iframe # ∗
        ipureintro
        simp only [grow_pats] at Hlen Hf ⊢
        exact ⟨by simp [Hlen], Hf⟩
      · ipureintro
        refine ⟨Hfl, Hat, ?_⟩
        intro b Hb
        cases Hb
        obtain ⟨y, Hy, Hent⟩ := Hsem (CAExists k srt p) rfl
        refine ⟨y, Hy, ?_⟩
        intro ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V
        exact (binders_interp_step V dj k srt p Hlen0 Hnot).trans
          (Hent ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V)
  | false =>
    -- the binders are done: flatten the body
    have Hne : decide ((#false : val) = #true) = false := by
      rw [bval_eq, bval_eq]; simp [bval]
    rw [Hne]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_true]
    wp_auto
    wp_apply wp_disjunct__flatten $$ [Hdj] as %lres Hres
    · iframe # ∗
    cases Hof : oassn_flatten ob with
    | some ats =>
      simp only [flatten_post]
      icases Hres with ⟨%Hl, Hdj⟩
      subst Hl
      wp_auto
      iapply HΦ
      iframe Hdj
      ipureintro
      intro _
      cases ob with
      | none => simp [oassn_flatten] at Hof
      | some b =>
        simp only [oassn_flatten] at Hof
        obtain ⟨y, Hy, Hent⟩ := Hsem b rfl
        refine ⟨y, Hy, ?_⟩
        intro ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V
        exact (dj_interp_flatten V dj b ats Hat Hof).trans
          (Hent ext' ffi' fi' fs' gc' hlc' GF' hG' sem' V)
    | none =>
      simp only [flatten_post]
      icases Hres with ⟨%Hnn, %ats, Hdj⟩
      unfold is_disjunct
      icases Hdj with ⟨%sp, %sok, %sa, %lf, %las, Hs, Hp, Hpc, Hok, Hokc, Ha, Hac, #Hats,
        %Hlen, %Hf⟩
      wp_if_destruct
      · exact absurd rfl Hnn
      try wp_auto
      iapply HΦ $$ %_ %(dj_failed (dj_atoms dj ats))
      isplitl [Hs Hp Hpc Hok Hokc Ha Hac]
      · iexists sp, sok, sa, _, las
        simp only [dj_failed]
        iframe # ∗
        ipureintro
        exact ⟨Hlen, by simp [Hnn]⟩
      · ipureintro; simp [dj_failed]

end proof

end Checker
end Perennial
