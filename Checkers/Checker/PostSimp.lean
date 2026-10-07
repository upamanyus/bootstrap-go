/-
Port of `new/checker/post_simp.v`.

Reading an interpreted assertion as an ordinary Iris assertion, by
computation.

`assn_interp V a` (Defs.lean) evaluates the checker's terms: a pure atom
`⌜t⌝` becomes `⌜teval V t = bval true⌝`. `assn_interp_simp` is the same
interpretation with each atom read directly as the proposition it stands
for (`pure_meaning`): `x <u y` as `uint.Z x < uint.Z y`, `¬ (y <u x)` as
`uint.Z x ≤ uint.Z y`, `t == t'` as an equation, and so on.
`assn_interp_simp_eq` says the two agree, once and for all. So a proof
that has `assn_interp V a` for a concrete `a` and a concrete valuation
rewrites with `assn_interp_simp_eq` and lets `simp only` compute the
ordinary statement, with no case analysis and no arithmetic.

Lean notes:
* `assn_interp_simp_eq` is an *equation* `assn_interp V a = assn_interp_simp V a`
  (by `propext` inside `⌜⌝` and `funext` under `∃`), which is stronger than
  Rocq's `⊣⊢` and is what lets a client `rw [assn_interp_simp_eq]` (Lean's
  `rw` cannot rewrite with `⊣⊢`). Rocq's `⊣⊢` statement is
  `assn_interp_simp_equiv`.
* After the rewrite, `simp only [assn_interp_simp, pure_meaning, int_rel, teval, …]`
  computes the statement for a concrete assertion and valuation; the
  `example` at the bottom checks this on a small postcondition.
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

section pure_meaning
variable [ext : FfiSyntax]

/-- `P x y`, if `v1` and `v2` are the integers `x` and `y`. -/
def int_rel (v1 v2 : val) (P : w64 → w64 → Prop) : Prop :=
  match v1, v2 with
  | LitV (LitInt x), LitV (LitInt y) => P x y
  | _, _ => False

/-- What `teval V t = bval true` says, for the atoms the checker's surface
syntax produces; anything else is left as it is. -/
def pure_meaning (V : valuation) (t : term) : Prop :=
  match t with
  | TLt sg a b => int_rel (teval V a) (teval V b)
      (fun x y => if sg then sint.Z x < sint.Z y else uint.Z x < uint.Z y)
  | TLe sg a b => int_rel (teval V a) (teval V b)
      (fun x y => if sg then sint.Z x ≤ sint.Z y else uint.Z x ≤ uint.Z y)
  | TNot (TLt sg a b) => int_rel (teval V a) (teval V b)
      (fun x y => if sg then sint.Z y ≤ sint.Z x else uint.Z y ≤ uint.Z x)
  | TNot (TLe sg a b) => int_rel (teval V a) (teval V b)
      (fun x y => if sg then sint.Z y < sint.Z x else uint.Z y < uint.Z x)
  | TEq a b => teval V a = teval V b
  | TBool b => b = true
  | _ => teval V t = bval true

theorem bval_eq_true (x : Bool) : bval x = bval true ↔ x = true := by
  constructor
  · intro h; simpa [bval] using h
  · intro h; rw [h]

/-- The comparison atoms: a `match` on two integer values, true exactly when
`f` holds of them. -/
theorem int_match_true (va vb : val) (f : w64 → w64 → Bool) (P : w64 → w64 → Prop)
    (Hf : ∀ x y, f x y = true ↔ P x y) :
    (match va, vb with
      | LitV (LitInt x), LitV (LitInt y) => bval (f x y)
      | _, _ => uval) = bval true ↔ int_rel va vb P := by
  unfold int_rel
  split
  · rw [bval_eq_true]; exact Hf _ _
  · rename_i Hno
    first
      | simp [uval, bval]
      | (split
         · rename_i x y; exact absurd rfl (Hno x y)
         · simp [uval, bval])

theorem teval_lt_true (V : valuation) (sg : Bool) (a b : term) :
    teval V (TLt sg a b) = bval true ↔ pure_meaning V (TLt sg a b) := by
  simp only [teval, pure_meaning]
  exact int_match_true _ _ _ _ (fun x y => by cases sg <;> simp [cmp_lt])

theorem teval_le_true (V : valuation) (sg : Bool) (a b : term) :
    teval V (TLe sg a b) = bval true ↔ pure_meaning V (TLe sg a b) := by
  simp only [teval, pure_meaning]
  exact int_match_true _ _ _ _ (fun x y => by cases sg <;> simp [cmp_le])

/-- `!b` of a comparison, as a `match` on the operands. -/
theorem not_match (va vb : val) (f : w64 → w64 → Bool) :
    (match (match va, vb with
        | LitV (LitInt x), LitV (LitInt y) => bval (f x y)
        | _, _ => uval) with
      | LitV (LitBool b) => bval (!b)
      | _ => uval) =
    (match va, vb with
      | LitV (LitInt x), LitV (LitInt y) => bval (!f x y)
      | _, _ => uval) := by
  split
  · rename_i b Hb
    split at Hb
    · simp only [bval] at Hb; cases Hb; rfl
    · simp [uval] at Hb
  · rename_i Hno
    split
    · rename_i x y; exact absurd rfl (Hno (f x y))
    · rfl

theorem teval_not_lt_true (V : valuation) (sg : Bool) (a b : term) :
    teval V (TNot (TLt sg a b)) = bval true ↔ pure_meaning V (TNot (TLt sg a b)) := by
  simp only [pure_meaning]
  refine Iff.trans ?_ (int_match_true (teval V a) (teval V b) (fun x y => !cmp_lt sg x y) _
    (fun x y => by cases sg <;> simp [cmp_lt] <;> omega))
  exact Iff.of_eq (congrArg (· = bval true) (not_match _ _ _))

theorem teval_not_le_true (V : valuation) (sg : Bool) (a b : term) :
    teval V (TNot (TLe sg a b)) = bval true ↔ pure_meaning V (TNot (TLe sg a b)) := by
  simp only [pure_meaning]
  refine Iff.trans ?_ (int_match_true (teval V a) (teval V b) (fun x y => !cmp_le sg x y) _
    (fun x y => by cases sg <;> simp [cmp_le] <;> omega))
  exact Iff.of_eq (congrArg (· = bval true) (not_match _ _ _))

theorem pure_meaning_iff (V : valuation) (t : term) :
    teval V t = bval true ↔ pure_meaning V t := by
  cases t with
  | TBool b => simp only [teval, pure_meaning]; exact bval_eq_true b
  | TEq a b => simp only [teval, pure_meaning, bval_eq_true, decide_eq_true_iff]
  | TLt sg a b => exact teval_lt_true V sg a b
  | TLe sg a b => exact teval_le_true V sg a b
  | TNot t =>
    cases t with
    | TLt sg a b => exact teval_not_lt_true V sg a b
    | TLe sg a b => exact teval_not_le_true V sg a b
    | _ => simp only [pure_meaning]
  | _ => simp only [pure_meaning]

end pure_meaning

section assn_interp_simp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

def assn_interp_simp (V : valuation) : cassn → IProp GF
  | CAEmp => iprop(True)
  | CASep p q => iprop(assn_interp_simp V p ∗ assn_interp_simp V q)
  | CAOr p q => iprop(assn_interp_simp V p ∨ assn_interp_simp V q)
  | CAExists n s p => iprop(∃ w : val, ⌜has_sort w s⌝ ∗ assn_interp_simp (upd_pat V n w) p)
  | CAPure t => iprop(⌜pure_meaning V t⌝)
  | CAPointsTo l v =>
      iprop(∃ lo : Loc, ⌜teval V l = lval lo⌝ ∗ heapPointsto lo (DFrac.own 1) (teval V v))

theorem assn_interp_simp_eq (V : valuation) (a : cassn) :
    assn_interp (GF := GF) V a = assn_interp_simp V a := by
  induction a generalizing V with
  | CAEmp => rfl
  | CASep p q ihp ihq => simp only [assn_interp, assn_interp_simp, ihp, ihq]
  | CAOr p q ihp ihq => simp only [assn_interp, assn_interp_simp, ihp, ihq]
  | CAExists n s p ihp => simp only [assn_interp, assn_interp_simp, ihp]
  | CAPure t => simp only [assn_interp, assn_interp_simp, pure_meaning_iff]
  | CAPointsTo l v => rfl

theorem assn_interp_simp_equiv (V : valuation) (a : cassn) :
    assn_interp (GF := GF) V a ⊣⊢ assn_interp_simp V a := by
  rw [assn_interp_simp_eq]; exact .rfl

/-- The computation a client does: a concrete postcondition at a concrete
valuation reads off by `rw` and `simp only`. -/
example (a b : w64) (v : val) :
    post_interp (GF := GF) (fun n => [ival a, ival b].getD n uval) v
      (CASep (CAPure (TLt false (TVar 0) (TVar 1)))
        (CASep (CAPure (TNot (TLt false (TVar 1) (TVar 0)))) (CAPure (TEq TResult (TVar 1))))) =
    iprop(⌜uint.Z a < uint.Z b⌝ ∗ ⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜v = ival b⌝) := by
  simp only [post_interp, assn_interp_simp_eq, assn_interp_simp, pure_meaning, int_rel, teval,
    ival, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Bool.false_eq_true, ↓reduceIte]

end assn_interp_simp

end Checker
end Perennial
