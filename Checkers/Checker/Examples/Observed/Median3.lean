/-
Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/observed/median3.v`.

wp_Median3, from one observed run of the checker.

gocheck/observe.sh runs gocheck on Median3 with the specification of
gocheck/demo.sh. It records the input gocheck hands to checker.Check in
Median3Input.lean (`median3_func`, `median3_vars`, `median3_pre`,
`median3_post`), and it fails unless checker.Check answers true on it.
`median3_check_run` is that observation, as an axiom: some GooseLang run of
checker.Check, from a state whose heap holds this input, returns #true.

Nothing else is trusted. `check_adequate` (Checkers/Checker/Adequacy.lean)
turns the run into `triple_holds`. The input's function is checked to be
exactly Goose's Median3 (`median3_func_val`, by `rfl`), and the input's
postcondition is translated into the one of the hand-written proof of
wp_Median3 (../Median3.lean) by computation (PostSimp.lean).

Lean notes:
* The run is `RealNsteps n … κs (Val #true :: tp, (σ', g'))`, a finite real
  execution (Rocq `rtc erased_step`), as in `check_adequate`.
* The axiom's model also provides `GF` with `GooseGpreS ffi GF`: Perennial
  Lean's `FfiInterpAdequacy` does not carry the FFI's functors (Rocq's
  `ffiΣ`/`subG_ffiPreG`, from which Rocq's adequacy.v builds `checkΣ`), so the
  ghost state adequacy runs in cannot be assembled for an arbitrary FFI and
  is part of the model the run is observed in (Adequacy.lean, Lean notes).
  The observation itself (`checker.Check` returned `#true` on this input) is
  unchanged.
* `wp_Median3` is stated on the application of `@! Median3`, like the
  hand-written ../Median3.lean, and its postcondition is that file's with
  `RET v` and `⌜v = #x⌝` for `RET #r` and `⌜r = x⌝` (see below).
* Cost (2026-10-07, `time lake env lean <file>`, 3 runs): this file 3.8-4.0 s,
  of which loading its imports is 2.0-2.2 s (a file with the same imports
  and nothing else); the hand-written ../Median3.lean takes 5.8-6.2 s.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Layout
import Checkers.Checker.Adequacy
import Checkers.Checker.PostSimp
import Checkers.Checker.Examples.ExamplesInit
import Checkers.Checker.Examples.Observed.Median3Input

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- OBSERVE-EXECUTION for Median3 (gocheck/observe.sh). The run is under some
model of GooseLang: an FFI (with the ghost state its adequacy needs), a Go
semantics satisfying `go.Semantics`, and `checker.Assumptions`. -/
axiom median3_check_run :
  ∃ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_sem : FfiSemantics ext ffi)
    (_ffi_interp : FfiInterp ffi) (_Hffi_adequacy : FfiInterpAdequacy ffi)
    (GF : BundledGFunctors) (_hPre : GooseGpreS ffi GF)
    (_go_gctx : GoGlobalContext) (lctx : GoLocalContext)
    (_sem : go.Semantics) (_package_sem : checker.Assumptions)
    (lf : Loc) (svars : GoSlice) (lpre lpost : Loc)
    (σ σ' : state) (g g' : GlobalState) (n : Nat) (κs : List Observation) (tp : List Expr),
    ffi_initgP g.globalWorld ∧ ffi_initP σ.world g.globalWorld ∧
    σ.goState.goLctx = lctx ∧
    inputs_in σ.heap lf median3_func svars median3_vars lpre median3_pre lpost median3_post ∧
    RealNsteps n
      ([App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #svars)) (Val #lpre)) (Val #lpost)],
        (σ, g))
      κs (Val #true :: tp, (σ', g'))

theorem median3_triple :
    triple_holds median3_func median3_vars median3_pre median3_post := by
  obtain ⟨ext, ffi, ffi_sem, ffi_interp, Hffi_adequacy, GF, hPre, go_gctx, lctx, sem,
    package_sem, lf, svars, lpre, lpost, σ, σ', g, g', n, κs, tp,
    Hinitg, Hinit, Hlctx, Hin, Hrun⟩ := median3_check_run
  exact check_adequate (GF := GF) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinitg Hinit Hlctx Hin Hrun

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [ffi_interp : FfiInterp ffi]
variable [ffi_sem : FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.examples.Assumptions]

/-- gocheck's translation of the body is Goose's. -/
theorem median3_func_val : func_val median3_func = checker.examples.Median3.impl := rfl

/-- The specification of the hand-written proof of wp_Median3 (../Median3.lean),
except that the result is a `val` `v` with `⌜v = #x⌝` in place of `RET #r`
with `⌜r = x⌝`. That is what makes it the checker's postcondition up to
simplification: in the form `RET #r`, the last two (contradictory) disjuncts
would have to be refuted by arithmetic to produce an `r`, and each of the
others would need a case of its own to pick one. -/
theorem wp_Median3 (a b c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples }}
      (App (App (App (Val (@! checker.examples.Median3)) (Val #a)) (Val #b)) (Val #c))
    {{ (v : val), RET v;
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜v = #b⌝) ∨
        (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜v = #b⌝) ∨
        (⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z a⌝ ∗ ⌜v = #c⌝) ∨
        (⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜v = #c⌝) ∨
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜v = #a⌝) ∨
        (⌜uint.Z c < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜v = #a⌝) ∨
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a < uint.Z b⌝) ∨
        (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b < uint.Z a⌝) }} := by
  iintro %Φ - HΦ
  rw [func_unfold, ← median3_func_val, ival_eq a, ival_eq b, ival_eq c]
  -- The logical variables 0, 1, 2 are the parameters.
  have Hθ : vars_sat (fun n => [ival a, ival b, ival c].getD n uval) median3_vars := by
    intro n s Hs
    rcases n with _ | _ | _ | n <;> simp [median3_vars] at Hs <;> subst Hs <;>
      exact ⟨_, rfl⟩
  have Htr := median3_triple ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem _ Hθ
  rw [show apply_vals (func_val median3_func)
        (arg_vals median3_func fun n => [ival a, ival b, ival c].getD n uval) =
      App (App (App (Val (func_val median3_func)) (Val (ival a))) (Val (ival b))) (Val (ival c))
      from rfl] at Htr
  iapply Htr $$ %Φ [] [HΦ]
  · simp only [pre_interp, median3_pre, assn_interp]; itrivial
  inext
  iintro %v Hpost
  -- The interpreted postcondition computes to the one above.
  simp only [post_interp, assn_interp_simp_eq, median3_post, assn_interp_simp, pure_meaning,
    int_rel, teval, ival, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  iapply HΦ $$ Hpost

end wps

end Checker
end Perennial
