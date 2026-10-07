/-
Port of `new/checker/fn/applyUnOp.v`.

`checker.applyUnOp` (checker/exec.go): the term for a unary Go operator at
a type, after checking that the operand's sort is the type's.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Fn.TypeSort
import Checkers.Checker.Fn.typeSigned
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.SortOf

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The Go code compares sorts by their codes, the mirrors by `decide`; the
two agree because the encoding is injective. -/
theorem sort_code_inj' (s1 s2 : sort) : sort_code s1 = sort_code s2 → s1 = s2 :=
  sort_code_inj s1 s2

/-- Whether the Go function's second result is `true`. -/
def oterm_ok : Option term → Bool
  | some _ => true
  | none => false

/-- The Lean mirror of the whole function: the sort check of `applyUnOp`,
then the term-building half, which is `apply_unop` in Steps.lean. -/
def unop_result (o : cop) (cty : ctype) (vl : List sort) : Option term → Option term
  | none => none
  | some u => if sort_of_vars vl u = some (ctype_sort cty) then apply_unop o cty u else none

theorem unop_result_bad (o : cop) (cty : ctype) (vl : List sort) (u : term) :
    sort_of_vars vl u ≠ some (ctype_sort cty) → unop_result o cty vl (some u) = none := by
  intro Hne; simp [unop_result, Hne]

theorem unop_result_good (o : cop) (cty : ctype) (vl : List sort) (u : term) :
    sort_of_vars vl u = some (ctype_sort cty) →
    unop_result o cty vl (some u) = apply_unop o cty u := by
  intro Heq; simp [unop_result, Heq]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_applyUnOp (o : cop) (lty : Loc) (cty : ctype)
    (sv : GoSlice) (vl : List sort) (lx : Loc) (ox : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_type lty cty ∗
        sv ↦*□ (vl.map sort_code) ∗ is_oterm lx ox }}
      (App (App (App (App (Val (@! checker.applyUnOp)) (Val #(op_code o))) (Val #lty)) (Val #sv))
        (Val #lx))
    {{ (lr : Loc) (ok : Bool), RET (PairV #lr #ok);
        ⌜ok = oterm_ok (unop_result o cty vl ox)⌝ ∗
        is_oterm lr (unop_result o cty vl ox) }} := by
  wp_start as ⟨#Hty, #Hsv, #Hx⟩
  wp_auto
  wp_apply wp_TypeSort lty (some cty) $$ []
  · rw [is_otype_some]; iframe Hty
  wp_apply wp_SortOf sv lx vl ox $$ []
  · iframe Hsv Hx
  cases ox with
  | none =>
    -- the operand is nil: `SortOf` rejects it
    simp only [osort_of, osort_ok, osort_code]
    wp_auto
    iapply HΦ
    simp only [unop_result, oterm_ok, is_oterm]
    ipureintro; simp
  | some u =>
  rw [is_oterm_some]
  rw [show osort_of (vars_env vl) (some u) = sort_of_vars vl u from rfl]
  cases Hs : sort_of_vars vl u with
  | none =>
    -- the operand is ill-sorted
    simp only [osort_ok, osort_code]
    wp_auto
    rw [unop_result_bad _ _ _ _ (by rw [Hs]; simp)]
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  | some s1 =>
  simp only [osort_ok, osort_code]
  by_cases Hne : s1 = ctype_sort cty
  case neg =>
    -- the operand's sort is not the type's
    wp_auto
    rw [show decide (sort_code s1 = sort_code (ctype_sort cty)) = false from
      decide_eq_false (fun h => Hne (sort_code_inj' _ _ h))]
    wp_auto
    rw [unop_result_bad _ _ _ _ (by rw [Hs]; simpa using Hne)]
    iapply HΦ
    simp only [oterm_ok, is_oterm]
    ipureintro; simp
  subst Hne
  rw [unop_result_good _ _ _ _ Hs]
  wp_auto
  cases o <;> cases cty <;>
    simp (config := {decide := true}) only [op_code, ctype_sort, sort_code, apply_unop,
      checker.SortInt, checker.SortBool, checker.OpNot] <;> wp_auto
  all_goals try (iapply HΦ; simp only [↓reduceIte, oterm_ok, is_oterm]; ipureintro; simp; done)
  all_goals try simp only [ite_true]
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
    iexists lx
    iframe Hx
    iExactEq Hr; rfl)
  all_goals done

end proof

end Checker
end Perennial
