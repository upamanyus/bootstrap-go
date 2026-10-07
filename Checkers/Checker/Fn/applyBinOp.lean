/-
Port of `new/checker/fn/applyBinOp.v`.

`checker.applyBinOp` (checker/exec.go): the term for a binary Go operator
at a type, after checking that both operands' sorts are the type's.

Lean notes:
* `sort_code_inj'` and `oterm_ok`, which Rocq defines again here (section
  locals), are imported from `Fn/applyUnOp.lean`: both files are imported by
  `Fn/exec.lean`, and Lean does not allow the duplicate names.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Fn.TypeSort
import Checkers.Checker.Fn.typeSigned
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.SortOf
import Checkers.Checker.Fn.applyUnOp

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The Lean mirror of the whole function: the sort check of `applyBinOp`,
then the term-building half, which is `apply_binop` in Steps.lean. -/
def binop_result (o : cop) (cty : ctype) (vl : List sort) : Option term → Option term → Option term
  | some u, some w =>
      if sort_of_vars vl u = some (ctype_sort cty) ∧ sort_of_vars vl w = some (ctype_sort cty)
      then apply_binop o cty u w else none
  | _, _ => none

/-- Either operand failing the sort check makes the whole thing fail. This is
phrased over `osort_of` because that is the form the two `SortOf` results
appear in. -/
theorem binop_result_none (o : cop) (cty : ctype) (vl : List sort) (ox oy : Option term) :
    ¬ (osort_of (vars_env vl) ox = some (ctype_sort cty) ∧
       osort_of (vars_env vl) oy = some (ctype_sort cty)) →
    binop_result o cty vl ox oy = none := by
  intro Hne
  cases ox <;> cases oy <;> simp only [binop_result]
  exact ite_eq_right Hne

theorem binop_result_good (o : cop) (cty : ctype) (vl : List sort) (u w : term) :
    sort_of_vars vl u = some (ctype_sort cty) →
    sort_of_vars vl w = some (ctype_sort cty) →
    binop_result o cty vl (some u) (some w) = apply_binop o cty u w := by
  intro H1 H2; simp [binop_result, H1, H2]

/-- `ctype_sort` is never `SUnit`, so the `OpEq`-at-unit rejection in
`apply_binop` (and in the Go code) is unreachable at a supported type. -/
theorem ctype_sort_ne_unit (cty : ctype) : ctype_sort cty ≠ SUnit := by
  cases cty <;> simp [ctype_sort]

/-- `apply_binop` with its `decide`s resolved, at an integer type ... -/
theorem apply_binop_int (o : cop) (cty : ctype) (u w : term) :
    ctype_sort cty = SInt →
    apply_binop o cty u w =
      match o with
      | COAdd => some (TPlus u w)
      | COSub => some (TMinus u w)
      | COMul => some (TMul u w)
      | COEq => some (TEq u w)
      | COLt => some (TLt (ctype_signed cty) u w)
      | COLe => some (TLe (ctype_signed cty) u w)
      | COGt => some (TLt (ctype_signed cty) w u)
      | COGe => some (TLe (ctype_signed cty) w u)
      | CONeg | CONot => none := by
  intro Hs
  cases o <;> simp [apply_binop, Hs]

/-- ... and at `bool` or a pointer, where only `OpEq` survives. -/
theorem apply_binop_nonint (o : cop) (cty : ctype) (u w : term) :
    ctype_sort cty ≠ SInt →
    apply_binop o cty u w = match o with | COEq => some (TEq u w) | _ => none := by
  intro Hs
  cases o <;> simp [apply_binop, Hs, ctype_sort_ne_unit]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_applyBinOp (o : cop) (lty : Loc) (cty : ctype)
    (sv : GoSlice) (vl : List sort) (lp lq : Loc) (ox oy : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_type lty cty ∗
        sv ↦*□ (vl.map sort_code) ∗ is_oterm lp ox ∗ is_oterm lq oy }}
      (App (App (App (App (App (Val (@! checker.applyBinOp)) (Val #(op_code o))) (Val #lty))
        (Val #sv)) (Val #lp)) (Val #lq))
    {{ (lr : Loc) (ok : Bool), RET (PairV #lr #ok);
        ⌜ok = oterm_ok (binop_result o cty vl ox oy)⌝ ∗
        is_oterm lr (binop_result o cty vl ox oy) }} := by
  wp_start as ⟨#Hty, #Hsv, #Hp, #Hq⟩
  wp_auto
  wp_apply wp_TypeSort lty (some cty) $$ []
  · rw [is_otype_some]; iframe Hty
  wp_apply wp_SortOf sv lp vl ox $$ []
  · iframe Hsv Hp
  wp_apply wp_SortOf sv lq vl oy $$ []
  · iframe Hsv Hq
  cases E1 : osort_of (vars_env vl) ox with
  | none =>
    -- the first operand has no sort
    rw [binop_result_none _ _ _ _ _ (by rw [E1]; simp)]
    simp only [osort_ok, osort_code]
    wp_auto
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  | some s1 =>
  cases E2 : osort_of (vars_env vl) oy with
  | none =>
    -- the second operand has no sort
    rw [binop_result_none _ _ _ _ _ (by rw [E2]; simp)]
    simp only [osort_ok, osort_code]
    wp_auto
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  | some s2 =>
  simp only [osort_ok, osort_code]
  by_cases Hne1 : s1 = ctype_sort cty
  case neg =>
    -- the first operand's sort is not the type's
    rw [binop_result_none _ _ _ _ _ (by rw [E1]; exact fun ⟨h, _⟩ => Hne1 (Option.some.inj h))]
    wp_auto
    rw [show decide (sort_code s1 = sort_code (ctype_sort cty)) = false from
      decide_eq_false (fun h => Hne1 (sort_code_inj' _ _ h))]
    wp_auto
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  subst Hne1
  by_cases Hne2 : s2 = ctype_sort cty
  case neg =>
    -- the second operand's sort is not the type's
    rw [binop_result_none _ _ _ _ _ (by rw [E2]; exact fun ⟨_, h⟩ => Hne2 (Option.some.inj h))]
    wp_auto
    rw [show decide (sort_code s2 = sort_code (ctype_sort cty)) = false from
      decide_eq_false (fun h => Hne2 (sort_code_inj' _ _ h))]
    wp_auto
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  subst Hne2
  -- both operands have the type's sort
  cases ox with
  | none => cases E1
  | some u =>
  cases oy with
  | none => cases E2
  | some w =>
  rw [binop_result_good _ _ _ _ _ E1 E2, is_oterm_some, is_oterm_some]
  wp_auto
  cases o <;> cases cty <;>
    simp (config := {decide := true}) only [op_code, ctype_sort, sort_code, apply_binop,
      ctype_signed, checker.SortInt, checker.SortBool, checker.SortUnit] <;> wp_auto
  all_goals try (iapply HΦ; simp only [↓reduceIte, oterm_ok, is_oterm]; ipureintro; simp; done)
  all_goals try simp only [ite_true, ↓reduceIte]
  all_goals try (wp_apply wp_typeSigned lty _ $$ [] as _; · iframe Hty)
  all_goals try simp only [ctype_signed]
  all_goals try wp_auto
  all_goals try (iapply HΦ; simp only [↓reduceIte, oterm_ok, is_oterm]; ipureintro; simp; done)
  all_goals try (
    wp_alloc lr as Hr
    ipersist Hr
    wp_auto
    iapply HΦ
    simp only [oterm_ok, is_oterm, is_term, tnode]
    isplitr
    · ipureintro; trivial
    iexists _, _
    iframe Hp Hq
    iExactEq Hr; rfl)
  all_goals done

end proof

end Checker
end Perennial
