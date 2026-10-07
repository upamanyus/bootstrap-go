/-
Port of `new/checker/adequacy.v`.

Adequacy of the checker: a closed execution of `checker.Check` that
returns `true` establishes the Hoare triple.

`check_sound` (Soundness.lean) is a separation-logic statement: its promise
lives inside the program logic, relative to one choice of ghost state. This
file discharges the program logic for a concrete run. Suppose `Check` is
started in a state `σ` whose heap holds the input trees (`inputs_in`,
Layout.lean, a plain proposition about `σ.heap`), and the run reduces, with
no crash, to `#true` (with any other threads in any state). Then
`triple_holds` (Defs.lean): the triple of `check_sound` holds for `f`, for
every FFI, in every ghost state and under every Go semantics satisfying
`go.Semantics`.

The proof is GooseLang's adequacy theorem for crash-free runs,
`goose_adequacy_heap` (`Checkers/GooseLang/HeapAdequacy.lean`), which also
hands the program the cells of the initial heap. Inside it,
`wp_Check_closed` reads the input trees out of those cells and runs
`wp_Check`. The postcondition that adequacy extracts has to be a fact that
does not mention the ghost state adequacy allocates, and `triple_holds` is
that fact: the checker's specifications promise their results in every
ghost state (see ExecSpec.lean).

Lean notes:
* The run is an ordinary finite execution of the real semantics,
  `RealNsteps n ([e], (σ, g)) κs (Val #true :: tp, (σ', g'))`, for some `n`
  and observations `κs` (Rocq `rtc erased_step`, which also has no crash
  steps), as in `GooseAdequate` (HeapAdequacy.lean) and tcheck's
  `observed_run` (`Checkers/TCheck/Observe.lean`).
* The ghost state. Rocq builds it, `checkΣ := #[heapΣ; all.allΣ]`, where
  `heapΣ` takes the FFI's functors from `ffi_interp_adequacy` (its `ffiΣ`
  and `subG_ffiPreG`). Perennial Lean's `FfiInterpAdequacy` has no such
  fields: `ffiGpreS : BundledGFunctors → Type` is an arbitrary predicate,
  so no `GF` with `GooseGpreS ffi GF` can be assembled for an arbitrary FFI.
  `check_adequate` therefore takes `{GF} [GooseGpreS ffi GF]` as a premise,
  as Perennial Lean's own `disk_adequacy`/`grove_adequacy` and
  `goose_adequacy_heap` do. The conclusion `triple_holds` does not mention
  `GF`. `all.allΣ` has no counterpart (HeapAdequacy.lean, Lean notes).
* `GoLocalContext` is a variable (`lctx`, an instance) as in Rocq; the run's
  `σ.goState.goLctx = lctx` lets the ghost state adequacy allocates (whose
  local context is `σ`'s) carry `sem` and `package_sem`.
* `is_pkg_init_checker` is `isPkgInit checker_pkg` from nothing.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Layout
import Checkers.Checker.Fn.Check
import Checkers.GooseLang.HeapAdequacy

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section closed
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- The checker package has no dependencies and a trivial initialisation
predicate (Defs.lean). -/
theorem is_pkg_init_checker : ⊢@{IProp GF} isPkgInit checker_pkg := by
  rw [isPkgInit_unfold]
  unfold named
  simp only [isPkgInitDeps, isPkgInitDef]
  isplit <;> imodintro <;> ipureintro <;> trivial

/-- `checker.Check`, from the raw cells of a heap holding its input. -/
theorem wp_Check_closed (h : heap_t) (cf : cfunc) (vs : List sort) (P Q : cassn)
    (lf : Loc) (sv : GoSlice) (lpre lpost : Loc) :
    inputs_in h lf cf sv vs lpre P lpost Q →
    ([∗map] l ↦ lkv ∈ h, naHeapPointstoSt (tls lkv.1) l (.own 1) lkv.2) ⊢@{IProp GF}
      |={⊤}=> WP (App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #sv)) (Val #lpre))
                (Val #lpost))
              {{ v, ⌜v = #true → triple_holds cf vs P Q⌝ }} := by
  intro Hin
  iintro Hcells
  imod heap_ro_init h $$ Hcells with #Hro
  icases inputs_in_sound h lf cf sv vs lpre P lpost Q Hin $$ Hro with ⟨Hf, Hs, Hpre, Hpost⟩
  imodintro
  ihave #Hpkg := is_pkg_init_checker (GF := GF)
  iapply wp_Check cf vs P Q lf sv lpre lpost $$ [Hf Hs Hpre Hpost]
  · iframe Hpkg Hf Hs Hpre Hpost
  inext
  iintro %b %Hb
  ipureintro
  intro Heq
  apply Hb
  rw [bval_eq, bval_eq] at Heq
  cases b
  · cases Heq
  · rfl

end closed

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [ffi_sem : FfiSemantics ext ffi]
variable [ffi_interp : FfiInterp ffi] [Hffi_adequacy : FfiInterpAdequacy ffi]
-- The Go semantics the run is in.
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [sem : go.Semantics] [package_sem : checker.Assumptions]

/-- The adequacy statement. `RealNsteps` has no crash steps: this is a run of
the machine that did not crash. -/
theorem check_adequate {GF : BundledGFunctors} [hPre : GooseGpreS ffi GF]
    (f : cfunc) (vars : List sort) (pre post : cassn)
    (lf : Loc) (svars : GoSlice) (lpre lpost : Loc)
    (σ σ' : state) (g g' : GlobalState) (n : Nat) (κs : List Observation) (tp : List Expr) :
    ffi_initgP g.globalWorld → ffi_initP σ.world g.globalWorld →
    σ.goState.goLctx = lctx →
    inputs_in σ.heap lf f svars vars lpre pre lpost post →
    RealNsteps n
      ([App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #svars)) (Val #lpre)) (Val #lpost)],
        (σ, g))
      κs (Val #true :: tp, (σ', g')) →
    triple_holds f vars pre post := by
  intro Hinitg Hinit Hlctx Hin Hsteps
  have Had : GooseAdequate
      (App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #svars)) (Val #lpre)) (Val #lpost))
      σ g (fun v => v = #true → triple_holds f vars pre post) := by
    refine goose_adequacy_heap (GF := GF) _ σ g _ Hinitg Hinit ?_
    intro hG Hctx
    -- The run's Go local context is `lctx`, so `sem` and `package_sem`
    -- describe the semantics of the ghost state adequacy provides.
    obtain ⟨G, ⟨ffiL, lctx', naG, goG⟩⟩ := hG
    subst Hlctx
    subst Hctx
    iintro - - - Hcells
    iapply wp_Check_closed (hG := ⟨G, ⟨ffiL, σ.goState.goLctx, naG, goG⟩⟩) σ.heap f vars pre post lf svars lpre lpost Hin $$ Hcells
  exact Had.goose_adequate_result n κs tp (σ', g') #true Hsteps rfl

end adequacy

end Checker
end Perennial
