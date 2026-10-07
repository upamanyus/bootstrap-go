/-
Port of `new/checker/prelude.v`.

Everything the per-function proofs need.

One file per Go function (in `Checkers/Checker/Fn/`), so that the files can
be checked in parallel and one slow proof does not hold up the others;
this is the shared prefix.

Lean notes:
* Lean `import` is transitive, so importing this module gives Defs, TermLemmas,
  Subst, Interp, Steps and Repr (and the generated proof boilerplate of the
  checker package). Namespaces are not opened by an import: a `Fn/` file
  writes `open Iris Iris.BI Iris.ProofMode github_com.upamanyus.bootstrap_go`
  itself (see `Fn/TypeEq.lean`).
* `checker_pkg` abbreviates the package name for `isPkgInit`.
-/
import Checkers.Checker.Defs
import Checkers.Checker.TermLemmas
import Checkers.Checker.Subst
import Checkers.Checker.Interp
import Checkers.Checker.Steps
import Checkers.Checker.Repr

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The checker package (`github.com/upamanyus/bootstrap-go/checker`). -/
abbrev checker_pkg : GoString := pkg_id.github_com.upamanyus.bootstrap_go.checker

section prelude
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The checker has no package-level state. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp checker_pkg get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val checker.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) checker_pkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end prelude

end Checker
end Perennial
