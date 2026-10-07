/-
Port of `new/checker/disjunct.v`.

The postcondition matcher's parsed disjunct (checker/match.go).

A disjunct is one arm of the top-level disjunction of a postcondition:
the declared sorts of its pattern variables (indexed by the `AExists`
`Var` field, with `patOk` marking the indices a binder actually declared)
together with the flat list of the atoms of its separating conjunction.

Unlike the `Assn`/`Term` nodes it points at, a `disjunct` is *mutated*:
`growPats` extends `pats`/`patOk` and `flatten` extends `atoms`, both by
`append`. So `is_disjunct` owns its three slices -- and their capacities,
which is what `append` consumes -- while the `Assn` nodes inside stay
persistent.

Lean notes:
* `cdisjunct` and `disjunct_env` need no section variables; they are outside
  the ghost-state section.
* Rocq's wands `P -∗ ⌜…⌝` are entailments `⊢`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

/-! ## The mirror

`d_fail` records only *whether* the disjunct is malformed: the `*Failure`
the Go code stores there is a diagnostic that nothing reads back. -/
-- `cdisjunct`, `disjunct_env`: in LCheck/Fns.lean and LCheck/Syntax.lean.


section disjunct
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `pats`/`patOk` length agreement is an invariant of the Go struct --
`growPats` is the only thing that changes either length, and it extends
both together -- and it is exactly `sort_env_wf`, which `sortOfEnv` needs
because it indexes `patOk` after bounds-checking against `pats`. Carrying
it here means every caller gets it for free. -/
def is_disjunct (l : Loc) (dj : cdisjunct) : IProp GF :=
  iprop(∃ (sp sok sa : GoSlice) (lf : Loc) (las : List Loc),
      l ↦ checker.disjunct.mk sp sok sa lf ∗
      sp ↦* ((d_pats dj).map sort_code) ∗
      ownSliceCap w64 sp (DFrac.own 1) ∗
      sok ↦* d_pat_ok dj ∗
      ownSliceCap Bool sok (DFrac.own 1) ∗
      sa ↦* las ∗
      ownSliceCap Loc sa (DFrac.own 1) ∗
      ([∗list] la;x ∈ las;d_atoms dj, is_assn la x) ∗
      ⌜(d_pats dj).length = (d_pat_ok dj).length⌝ ∗
      ⌜lf = null ↔ d_fail dj = false⌝)

theorem is_disjunct_wf (l : Loc) (dj : cdisjunct) (vars : List sort) (rs : sort) (rok : Bool) :
    is_disjunct (GF := GF) l dj ⊢ ⌜sort_env_wf (disjunct_env vars dj rs rok)⌝ := by
  unfold is_disjunct
  iintro ⟨%sp, %sok, %sa, %lf, %las, _, _, _, _, _, _, _, _, %Hlen, _⟩
  ipureintro; exact Hlen

theorem is_disjunct_not_null (l : Loc) (dj : cdisjunct) :
    is_disjunct (GF := GF) l dj ⊢ ⌜l ≠ null⌝ := by
  unfold is_disjunct
  iintro ⟨%sp, %sok, %sa, %lf, %las, H, _⟩
  iapply typedPointsto_not_null $$ H

end disjunct

end Checker
end Perennial
