/-
Port of `new/checker/fn/flatten.v`.

The `flatten` method of the postcondition matcher's `disjunct`
(checker/match.go): collect the atoms of a separating conjunction into
`d.atoms`.

`AOr` and `AExists` are only allowed *above* a disjunct's separating
conjunction, so meeting either here -- or meeting nil -- is a failure,
and the atoms appended before the failure are left in place (the caller
sets `d.fail` and never looks at them again).

Lean notes:
* The postcondition's `match oassn_flatten x with …` is the definition
  `flatten_post` (unfolded by `simp only [flatten_post]`); it is the same
  proposition as Rocq's inline `match`.
-/
import Checkers.Checker.Disjunct

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

-- `dj_atoms`, `assn_flatten`: in LCheck/Fns.lean.

theorem dj_atoms_nil (dj : cdisjunct) : dj_atoms dj [] = dj := by
  cases dj; simp [dj_atoms]

theorem dj_atoms_app (dj : cdisjunct) (l1 l2 : List cassn) :
    dj_atoms (dj_atoms dj l1) l2 = dj_atoms dj (l1 ++ l2) := by
  cases dj; simp [dj_atoms]


def oassn_flatten : Option cassn → Option (List cassn)
  | none => none
  | some x' => assn_flatten x'

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

def flatten_post (ld : Loc) (dj : cdisjunct) (lres : Loc) : Option (List cassn) → IProp GF
  | some ats => iprop(⌜lres = null⌝ ∗ is_disjunct ld (dj_atoms dj ats))
  | none => iprop(⌜lres ≠ null⌝ ∗ ∃ ats, is_disjunct ld (dj_atoms dj ats))

set_option hygiene false in
/-- A rejection: allocate the `Failure` and return it; no atoms added. -/
local macro "reject" : tactic => `(tactic| (
  try wp_auto
  first
    | wp_alloc lfail as Hfail
    | (wp_pures; wp_load; wp_pures; wp_alloc lfail as Hfail)
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hfail
  try wp_auto
  iapply HΦ
  simp only [flatten_post, oassn_flatten, assn_flatten]
  isplitr
  · ipureintro; exact Hnn
  iexists []
  rw [dj_atoms_nil]
  iexact Hdj))

set_option hygiene false in
/-- One atom: append it to `d.atoms`. -/
local macro "one_atom" : tactic => `(tactic| (
  unfold is_disjunct
  icases Hdj with ⟨%sp, %sok, %sa, %lf, %las, Hs, Hp, Hpc, Hok, Hokc, Ha, Hac, #Hats,
    %Hlen, %Hf⟩
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  try wp_auto
  wp_apply wp_slice_append (t := go.GoType.PointerType checker.Assn.ty) sa las _ [la]
    (DFrac.own 1) $$ [Ha Hac Hsl] as %sa' ⟨Ha', Hac', -⟩
  · iframe Ha Hac Hsl
  try wp_auto
  iapply HΦ
  simp only [flatten_post, oassn_flatten, assn_flatten]
  isplitr
  · ipureintro; trivial
  unfold is_disjunct
  iexists sp, sok, sa', lf, las ++ [la]
  simp only [dj_atoms]
  iframe Hs Hp Hpc Hok Hokc Ha' Hac'
  isplitl
  · iapply BigSepL2.bigSepL2_snoc.2
    iframe Hats
    iexact Hx
  · ipureintro; exact ⟨Hlen, Hf⟩))

/-- The specification as an `IProp`, so that the Löb hypothesis keeps the
method-call form `ld @!! … @!! "flatten"` (`wp_start` would otherwise unfold
it inside the hypothesis as well, and the recursive call no longer
matches). -/
def flatten_spec (ld : Loc) (dj : cdisjunct) (la : Loc) (x : Option cassn) : IProp GF :=
  iprop({{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_disjunct ld dj ∗ is_oassn la x }}
      (App (Val (ld @!! go.GoType.PointerType checker.disjunct.ty @!! go!"flatten")) (Val #la))
    {{ (lres : Loc), RET #lres; flatten_post ld dj lres (oassn_flatten x) }})

instance flatten_spec_persistent (ld : Loc) (dj : cdisjunct) (la : Loc) (x : Option cassn) :
    Persistent (flatten_spec (GF := GF) ld dj la x) := by
  unfold flatten_spec; infer_instance

theorem flatten_spec_holds (ld : Loc) :
    ⊢ ∀ (la : Loc) (x : Option cassn) (dj : cdisjunct), flatten_spec (GF := GF) ld dj la x := by
  iloeb as IH
  iintro %la %x %dj
  rw [flatten_spec]
  wp_start as ⟨Hdj, #Hx⟩
  ihave %Hnull := is_oassn_null _ _ $$ Hx
  wp_auto
  wp_if_destruct
  · -- nil: unsupported
    obtain rfl : x = none := Hnull.mp rfl
    reject
  cases x with
  | none => exact absurd (Hnull.mpr rfl) Hif
  | some x' =>
  ihave #Hx' := Hx
  rw [is_oassn_some] at *
  icases is_assn_node _ _ $$ Hx' with ⟨%lL, %lR, %lX, %lY, %Hwf, #Hnode, #HL, #HR, #HX, #HY⟩
  iStructNamed Hnode
  cases x' with
  | CAEmp =>
    simp only [assn_code] at *
    try wp_auto
    iapply HΦ
    simp only [flatten_post, oassn_flatten, assn_flatten]
    isplitr
    · ipureintro; trivial
    rw [dj_atoms_nil]; iexact Hdj
  | CASep x1 x2 =>
    -- the left conjunct, then the right one
    simp only [assn_code, assn_l, assn_r] at *
    try wp_auto
    ihave #IH1 := IH $$ %lL %(some x1) %dj
    rw [flatten_spec]
    wp_apply IH1 $$ [Hdj] as %lres1 Hres1
    · iframe # ∗
    simp only [oassn_flatten]
    cases Hf1 : assn_flatten x1 with
    | some ats1 =>
      simp only [flatten_post]
      icases Hres1 with ⟨%Hl1, Hdj1⟩
      subst Hl1
      try wp_auto
      ihave #IH2 := IH $$ %lR %(some x2) %(dj_atoms dj ats1)
      rw [flatten_spec]
      wp_apply IH2 $$ [Hdj1] as %lres2 Hres2
      · iframe # ∗
      simp only [oassn_flatten]
      cases Hf2 : assn_flatten x2 with
      | some ats2 =>
        simp only [flatten_post]
        icases Hres2 with ⟨%Hl2, Hdj2⟩
        try wp_auto
        iapply HΦ
        simp only [flatten_post, oassn_flatten, assn_flatten, Hf1, Hf2]
        isplitr
        · ipureintro; exact Hl2
        rw [← dj_atoms_app]; iexact Hdj2
      | none =>
        simp only [flatten_post]
        icases Hres2 with ⟨%Hnn, %ats2, Hdj2⟩
        try wp_auto
        iapply HΦ
        simp only [flatten_post, oassn_flatten, assn_flatten, Hf1, Hf2]
        isplitr
        · ipureintro; exact Hnn
        iexists ats1 ++ ats2
        rw [← dj_atoms_app]; iexact Hdj2
    | none =>
      simp only [flatten_post]
      icases Hres1 with ⟨%Hnn, Hdj1⟩
      try wp_auto
      wp_if_destruct
      · exact absurd rfl Hnn
      try wp_auto
      iapply HΦ
      simp only [flatten_post, oassn_flatten, assn_flatten, Hf1]
      isplitr
      · ipureintro; exact Hnn
      iexact Hdj1
  | CAOr x1 x2 => simp only [assn_code] at *; reject
  | CAExists n s x1 => simp only [assn_code] at *; reject
  | CAPure x1 => simp only [assn_code] at *; one_atom
  | CAPointsTo x1 x2 => simp only [assn_code] at *; one_atom

theorem wp_disjunct__flatten (ld : Loc) (dj : cdisjunct) (la : Loc) (x : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_disjunct ld dj ∗ is_oassn la x }}
      (App (Val (ld @!! go.GoType.PointerType checker.disjunct.ty @!! go!"flatten")) (Val #la))
    {{ (lres : Loc), RET #lres; flatten_post ld dj lres (oassn_flatten x) }} := by
  iintro %Φ Hpre HΦ
  ihave #H := flatten_spec_holds (GF := GF) ld
  ispecialize H $$ %la %x %dj
  unfold flatten_spec
  iapply H $$ Hpre HΦ

end proof

end Checker
end Perennial
