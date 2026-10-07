/-
Port of `new/checker/fn/TypeEq.v`.

`checker.TypeEq` (checker/sorts.go): structural equality of two types.

Lean notes (this file is the worked example for `Fn/`; see
notes/checker-port.md):
* Rocq's naming trap (no Rocq variable may share a Go local's name, or
  `wp_auto` fails) does not exist in Lean: `wp_alloc_auto` invents `a_ptr`/`a`
  without clashing with a Lean variable `a`. The names `la`/`lb` are kept from
  Rocq.
* `iloeb as IH generalizing %oa %la %lb %ob` is Rocq's
  `iLöb as "IH" forall (oa la lb ob)`; the recursive call is
  `wp_apply IH $$ %x1 %x2 %x3 %x4 []` (pure arguments with `%`, the
  persistent precondition in a `[]` goal closed by `iframe #`).
* `wp_auto` cannot load a field of a *persistent* struct points-to
  (`l ↦□ checker.Type'.mk ..`): Perennial's `Access` search commits to the
  store instance, which forces `DFrac.own 1`. Split the node first with
  `iStructNamedSuffix H "_a"`; the field points-tos are then found.
* `wp_if_destruct` gives the case hypothesis `Hif` (equal case of `x == nil`
  first, as in Rocq) and substitutes `la = null`.
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- The recursion runs into the `Elem` field, which is `null` at every type
but a pointer, so the specification has to talk about a possibly absent
type. -/
theorem wp_TypeEq (oa : Option ctype) (la lb : Loc) (ob : Option ctype) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_otype la oa ∗ is_otype lb ob }}
      (App (App (Val (@! checker.TypeEq)) (Val #la)) (Val #lb))
    {{ RET #(decide (oa = ob)); True }} := by
  iloeb as IH generalizing %oa %la %lb %ob
  wp_start as ⟨#Hoa, #Hob⟩
  ihave %Hna := is_otype_null _ _ $$ Hoa
  ihave %Hnb := is_otype_null _ _ $$ Hob
  wp_auto
  wp_if_destruct
  · -- the first argument is nil
    obtain rfl : oa = none := Hna.mp rfl
    have Hd : decide (none = ob) = decide (lb = null) := by
      simp only [decide_eq_decide]; exact ⟨fun h => Hnb.mpr h.symm, fun h => (Hnb.mp h).symm⟩
    rw [← Hd]
    iapply HΦ
    itrivial
  · cases oa with
    | none => exact absurd (Hna.mpr rfl) Hif
    | some ta =>
    wp_if_destruct
    · -- the second argument is nil
      obtain rfl : ob = none := Hnb.mp rfl
      rw [show decide (some ta = none) = false from rfl]
      iapply HΦ
      itrivial
    · cases ob with
      | none => exact absurd (Hnb.mpr rfl) Hif
      | some tb =>
      rw [is_otype_some, is_otype_some]
      icases is_type_node _ _ $$ Hoa with ⟨%lea, #Hna', #Hea⟩
      icases is_type_node _ _ $$ Hob with ⟨%leb, #Hnb', #Heb⟩
      iStructNamedSuffix Hna' "_a"
      iStructNamedSuffix Hnb' "_b"
      wp_auto
      wp_if_destruct
      · -- the kind codes agree: recurse into the element types
        wp_apply IH $$ %(ctype_elem ta) %lea %leb %(ctype_elem tb) []
        · iframe #
        have Hd : decide (some ta = some tb) = decide (ctype_elem ta = ctype_elem tb) := by
          simp only [decide_eq_decide, Option.some.injEq]
          rw [ctype_eq_iff]
          exact ⟨fun h => h.2, fun h => ⟨Hif, h⟩⟩
        rw [Hd]
        iapply HΦ
        itrivial
      · -- the kind codes differ
        rw [show decide (some ta = some tb) = false from
          decide_eq_false (fun h => Hif (by cases h; rfl))]
        iapply HΦ
        itrivial

end proof

end Checker
end Perennial
