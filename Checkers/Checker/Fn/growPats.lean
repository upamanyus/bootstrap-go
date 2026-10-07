/-
Port of `new/checker/fn/growPats.v`.

The `growPats` method of the postcondition matcher's `disjunct`
(checker/match.go): extend `pats`/`patOk` with default entries until
index `n` is addressable.
-/
import Checkers.Checker.Disjunct

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- Pad a list with `x` until index `k` is in range. -/
def pad {A : Type} (xs : List A) (x : A) (k : Nat) : List A :=
  xs ++ List.replicate (k + 1 - xs.length) x

theorem pad_length {A : Type} (xs : List A) (x : A) (k : Nat) :
    (pad xs x k).length = max xs.length (k + 1) := by
  simp only [pad, List.length_append, List.length_replicate]; omega

theorem pad_done {A : Type} (xs : List A) (x : A) (k : Nat) :
    k < xs.length → pad xs x k = xs := by
  intro Hk
  simp only [pad, show k + 1 - xs.length = 0 by omega, List.replicate_zero, List.append_nil]

/-- One iteration of the loop does not change the padded result. -/
theorem pad_step {A : Type} (xs : List A) (x : A) (k : Nat) :
    xs.length ≤ k → pad (xs ++ [x]) x k = pad xs x k := by
  intro Hle
  simp only [pad, List.length_append, List.length_singleton, List.append_assoc]
  congr 1
  rw [show k + 1 - xs.length = (k + 1 - (xs.length + 1)) + 1 by omega,
    List.replicate_succ]
  rfl

/-- The mirror: both fields are extended, so the length agreement
`sort_env_wf` needs is preserved. -/
def grow_pats (dj : cdisjunct) (k : Nat) : cdisjunct :=
  mkDisjunct (pad (d_pats dj) SInt k) (pad (d_pat_ok dj) false k) (d_atoms dj) (d_fail dj)

theorem grow_pats_wf (dj : cdisjunct) (k : Nat) :
    (d_pats dj).length = (d_pat_ok dj).length →
    (d_pats (grow_pats dj k)).length = (d_pat_ok (grow_pats dj k)).length := by
  intro Heq
  simp only [grow_pats, pad_length, Heq]

/-- Index `k` really is addressable afterwards. -/
theorem grow_pats_lookup (dj : cdisjunct) (k : Nat) :
    k < (d_pats (grow_pats dj k)).length ∧ k < (d_pat_ok (grow_pats dj k)).length := by
  simp only [grow_pats, pad_length]; omega

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_disjunct__growPats (ld : Loc) (dj : cdisjunct) (m : w64) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_disjunct ld dj }}
      (App (Val (ld @!! go.GoType.PointerType checker.disjunct.ty @!! go!"growPats")) (Val #m))
    {{ RET #(); is_disjunct ld (grow_pats dj (uint.nat m)) }} := by
  wp_start as Hdj
  unfold is_disjunct
  icases Hdj with ⟨%sp0, %sok0, %sa, %lf, %las, Hs, Hp, Hpc, Hok, Hokc, Ha, Hac, #Hats,
    %Hlen0, %Hf⟩
  wp_auto
  ihave HI : (∃ (ps : List sort) (ok : List Bool) (sp sok : GoSlice),
      "Hs" ∷ ld ↦ checker.disjunct.mk sp sok sa lf ∗
      "Hp" ∷ sp ↦* (ps.map sort_code) ∗
      "Hpc" ∷ ownSliceCap w64 sp (DFrac.own 1) ∗
      "Hok" ∷ sok ↦* ok ∗
      "Hokc" ∷ ownSliceCap Bool sok (DFrac.own 1) ∗
      "%Hlen" ∷ ⌜ps.length = ok.length⌝ ∗
      "%Hgp" ∷ ⌜pad ps SInt (uint.nat m) = pad (d_pats dj) SInt (uint.nat m)⌝ ∗
      "%Hgo" ∷ ⌜pad ok false (uint.nat m) = pad (d_pat_ok dj) false (uint.nat m)⌝ : IProp GF)
    $$ [Hs Hp Hpc Hok Hokc]
  · iexists d_pats dj, d_pat_ok dj, sp0, sok0
    iframe
    ipureintro
    exact ⟨Hlen0, rfl, rfl⟩
  wp_for HI
  ihave %Hsl := ownSlice_len _ _ _ $$ Hp
  simp only [List.length_map] at Hsl
  wp_if_destruct
  · -- the loop body: append a default entry to each slice
    have Hle : ps.length ≤ uint.nat m := by word
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, _⟩
    try wp_auto
    wp_apply wp_slice_append (t := checker.Sort.ty) sp (ps.map sort_code) _ [W64 0]
      (DFrac.own 1) $$ [Hp Hpc Hsl1] as %sp' ⟨Hp', Hpc', -⟩
    · iframe Hp Hpc Hsl1
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, _⟩
    try wp_auto
    wp_apply wp_slice_append (t := go.bool) sok ok _ [false]
      (DFrac.own 1) $$ [Hok Hokc Hsl2] as %sok' ⟨Hok', Hokc', -⟩
    · iframe Hok Hokc Hsl2
    try wp_auto
    wp_for_post
    iframe
    iexists ps ++ [SInt], ok ++ [false], sp', sok'
    rw [List.map_append, List.map_singleton, show sort_code SInt = W64 0 from rfl]
    iframe
    ipureintro
    refine ⟨by simp [Hlen], ?_, ?_⟩
    · rw [pad_step _ _ _ Hle]; exact Hgp
    · rw [pad_step _ _ _ (by omega)]; exact Hgo
  · -- the loop is done: the slices are exactly the padded ones
    have Hgt : uint.nat m < ps.length := by word
    rw [pad_done _ _ _ Hgt] at Hgp
    rw [pad_done _ _ _ (by omega)] at Hgo
    iapply HΦ
    iexists sp, sok, sa, lf, las
    simp only [grow_pats, ← Hgp, ← Hgo]
    iframe # ∗
    ipureintro
    exact ⟨Hlen, Hf⟩

end proof

end Checker
end Perennial
