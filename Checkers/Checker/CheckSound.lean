/-
Port of `new/checker/check_sound.v`.

The statement of `check_sound` (Soundness.lean), proved.

The text of `check_sound_proof` is the statement of `check_sound`
(Soundness.lean), character for character. It is `wp_Check` (Fn/Check.lean),
whose postcondition `triple_holds` is the triple in every ghost state,
instantiated at the ambient one, and with the variables renamed back:
`wp_Check` keeps Rocq's names `cf`, `vs`, `P`, `Q` (in Rocq, `f`, `vars`,
`pre` and `post` were unusable there because they are Go locals of `Check`).

Lean notes:
* Rocq's `{{{ … }}} @! checker.Check #lf #svars #lpre #lpost {{{ … }}}` is
  the Lean triple on `(App (App (App (App (Val (@! checker.Check)) (Val #lf))
  (Val #svars)) (Val #lpre)) (Val #lpost))`; `is_pkg_init checker` is
  `isPkgInit checker_pkg`. The inner triple is a `Prop` (`⊢ …`) inside `⌜⌝`,
  as in Rocq.
* `triple_holds` also quantifies over `GoGlobalContext` and `HasLC`
  (Defs.lean), so the instantiation passes them too.
-/
import Checkers.Checker.Defs
import Checkers.Checker.Prelude
import Checkers.Checker.ExecDef
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.VerifyDef
import Checkers.Checker.Fn.Check

set_option linter.iris.style.nameCheck false
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

theorem check_sound_proof :
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
            {{ (v : val), RET v; post_interp (GF := GF) θ v post }}⌝ }} := by
  intro f vars pre post lf svars lpre lpost
  iintro %Φ Hpre HΦ
  iapply wp_Check f vars pre post lf svars lpre lpost $$ Hpre
  inext
  iintro %b %Hb
  iapply HΦ
  ipureintro
  intro Htrue θ Hθ
  exact Hb Htrue ext ffi ffi_interp ffi_sem go_gctx hlc GF hG sem θ Hθ

end semantics

end Checker
end Perennial
