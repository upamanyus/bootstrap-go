/-
Port of `new/checker/soundness.v`.

Statement of soundness for the Go symbolic-execution checker in checker/.

The checker (checker/*.go, translated by Goose into
`Generated/Code/github_com/upamanyus/bootstrap_go/checker.lean`) is verified.
This file states what a `true` answer of `checker.Check` means, as
`check_sound` at the end; the definitions it is stated over live in
`Checkers/Checker/Defs.lean`, which this file imports (and so re-exports).
The proof is `check_sound_proof` (`Checkers/Checker/CheckSound.lean`), about
the Goose translation of the checker; `notes/checker-port.md` and Rocq's
new/checker/NOTES.md and checker/SOUNDNESS_PLAN.md describe it.

`check_adequate` (`Checkers/Checker/Adequacy.lean`) closes the program
logic: a crash-free run of `checker.Check` from a state whose heap holds the
input (`inputs_in`, Layout.lean) that returns `#true` establishes
`triple_holds` (Defs.lean), the same triple for every FFI, ghost state and
Go semantics.

Trust boundary of the whole pipeline: the GooseLang semantics, the Goose
translation of the checker, and the unverified frontend (gocheck/) that
produces the checker's input from Go source.

Lean notes: the statement of `check_sound` is the text of
`check_sound_proof` (CheckSound.lean), character for character, so it can be
audited here without reading the proof; see CheckSound.lean for how the Rocq
syntax maps (`isPkgInit checker_pkg`, the application spelled out, the
inner triple a `Prop` inside `⌜⌝`).
-/
import Checkers.Checker.Defs
import Checkers.Checker.CheckSound

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section semantics
variable [ext : FfiSyntax] [ffi : FfiModel] [ffi_interp : FfiInterp ffi]
variable [ffi_sem : FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-! ## The soundness statement

If `checker.Check` answers `true` on (the heap representation of) a
function `f`, sort table `vars`, precondition `pre` and postcondition
`post`, then for every valuation of the logical variables respecting the
sorts, `f` applied to the values of variables `0 .. nparams-1` satisfies the
Hoare triple with precondition `pre` and postcondition `post` (in which
`ret` denotes the return value). -/
theorem check_sound :
    ∀ (f : cfunc) (vars : List sort) (pre post : cassn)
      (lf : Loc) (svars : GoSlice) (lpre lpost : Loc),
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗
        is_func lf f ∗ is_sorts svars vars ∗ is_assn lpre pre ∗ is_assn lpost post }}
      (App (App (App (App (Val (@! checker.Check)) (Val #lf)) (Val #svars)) (Val #lpre)) (Val #lpost))
    {{ (b : Bool), RET #b;
        ⌜b = true →
          ∀ θ : Nat → val,
            vars_sat θ vars →
            {{ pre_interp (GF := GF) θ pre }}
              (apply_vals (func_val f) (arg_vals f θ))
            {{ (v : val), RET v; post_interp (GF := GF) θ v post }}⌝ }} :=
  check_sound_proof

end semantics

end Checker
end Perennial
