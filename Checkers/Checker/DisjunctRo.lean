/-
Port of `new/checker/disjunct_ro.v`.

A parsed disjunct, frozen.

`is_disjunct` owns the disjunct's slices because parsing mutates them
(`growPats`, `flatten`). Once `parseDisjuncts` has returned, nothing
changes a disjunct again: `Verify` only reads it, once per path, and
`checkSorts` hands its `pats`/`patOk` to `sortOfEnv` next to the
(persistent) declared sort table, which needs a single fraction for all
of them. So `Verify` freezes each disjunct into this persistent form.

Lean notes:
* `is_disjunct_freeze : is_disjunct l dj ⊢ |==> is_disjunct_ro l dj`
  (Rocq `==∗`).
* The persistence instance needs larger `synthInstance` limits (five
  existentials over a seven-fold `∗` exceed the default `maxSize`).
-/
import Checkers.Checker.Disjunct

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

section disjunct_ro
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def is_disjunct_ro (l : Loc) (dj : cdisjunct) : IProp GF :=
  iprop(∃ (sp sok sa : GoSlice) (lf : Loc) (las : List Loc),
      l ↦□ checker.disjunct.mk sp sok sa lf ∗
      sp ↦*□ ((d_pats dj).map sort_code) ∗
      sok ↦*□ d_pat_ok dj ∗
      sa ↦*□ las ∗
      ([∗list] la;x ∈ las;d_atoms dj, is_assn la x) ∗
      ⌜(d_pats dj).length = (d_pat_ok dj).length⌝ ∗
      ⌜lf = null ↔ d_fail dj = false⌝)

instance is_disjunct_ro_persistent (l : Loc) (dj : cdisjunct) :
    Persistent (is_disjunct_ro (GF := GF) l dj) := by
  unfold is_disjunct_ro
  set_option synthInstance.maxHeartbeats 200000 in set_option synthInstance.maxSize 1024 in infer_instance

theorem is_disjunct_freeze (l : Loc) (dj : cdisjunct) :
    is_disjunct (GF := GF) l dj ⊢ |==> is_disjunct_ro l dj := by
  unfold is_disjunct is_disjunct_ro
  iintro ⟨%sp, %sok, %sa, %lf, %las, Hl, Hp, _, Hok, _, Ha, _, #Has, %H1, %H2⟩
  ipersist Hl
  ipersist Hp
  ipersist Hok
  ipersist Ha
  imodintro
  iexists sp, sok, sa, lf, las
  iframe Hl Hp Hok Ha Has
  ipureintro; exact ⟨H1, H2⟩

theorem is_disjunct_ro_wf (l : Loc) (dj : cdisjunct) (vars : List sort) (rs : sort) (rok : Bool) :
    is_disjunct_ro (GF := GF) l dj ⊢ ⌜sort_env_wf (disjunct_env vars dj rs rok)⌝ := by
  unfold is_disjunct_ro
  iintro ⟨%sp, %sok, %sa, %lf, %las, _, _, _, _, _, %Hlen, _⟩
  ipureintro; exact Hlen

end disjunct_ro

end Checker
end Perennial
