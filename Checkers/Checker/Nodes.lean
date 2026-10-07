/-
Port of `new/checker/nodes.v`.

Decoding lemmas for `Expr` and `Assn` nodes, and the representation of
the checker's `sortEnv`.

Kept apart from repr.v only because repr.v was already built when these
were written; they belong with the rest of the representation layer.

Lean notes:
* As in Repr.lean, the pure node-field functions are outside the ghost-state
  section, the decoding lemmas are entailments `⊢`, and `is_oexpr_some`/
  `is_oassn_some` (`rfl`) rewrite `is_oexpr l (some e)` to `is_expr l e`.
* `is_sortenv` keeps Rocq's `dq` argument order (`dq l E`).
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

/-! ## `Expr` node fields (pure) -/

def expr_code : cexpr → w64
  | CEInt _ => W64 1 | CEBool _ => W64 2 | CEUnit => W64 3 | CEVar _ => W64 4
  | CELet _ _ _ => W64 5 | CESeq _ _ => W64 6 | CEIf _ _ _ => W64 7
  | CELoad _ _ => W64 8 | CEStore _ _ _ => W64 9 | CEAlloc _ _ => W64 10
  | CEZero _ => W64 11 | CEBinOp _ _ _ _ => W64 12 | CEUnOp _ _ _ => W64 13
  | CEConvert _ _ _ => W64 14 | CEDo _ => W64 15 | CEReturn _ => W64 16
  | CEExcSeq _ _ => W64 17 | CEExcDo _ => W64 18

def expr_name : cexpr → GoString
  | CEVar x => x
  | CELet x _ _ => x
  | _ => go!""

def expr_num : cexpr → w64
  | CEInt w => w
  | CEBool b => bool_code b
  | _ => W64 0

def expr_op : cexpr → w64
  | CEBinOp op _ _ _ | CEUnOp op _ _ => op_code op
  | _ => W64 0

def expr_ty : cexpr → Option ctype
  | CELoad t _ | CEStore t _ _ | CEAlloc t _ | CEZero t
  | CEBinOp _ t _ _ | CEUnOp _ t _ | CEConvert t _ _ => some t
  | _ => none

def expr_ty2 : cexpr → Option ctype
  | CEConvert _ t2 _ => some t2
  | _ => none

def expr_a : cexpr → Option cexpr
  | CELet _ x _ | CESeq x _ | CEIf x _ _ | CELoad _ x | CEStore _ x _
  | CEAlloc _ x | CEBinOp _ _ x _ | CEUnOp _ _ x | CEConvert _ _ x
  | CEDo x | CEReturn x | CEExcSeq x _ | CEExcDo x => some x
  | _ => none

def expr_b : cexpr → Option cexpr
  | CELet _ _ y | CESeq _ y | CEIf _ y _ | CEStore _ _ y | CEBinOp _ _ _ y
  | CEExcSeq _ y => some y
  | _ => none

def expr_c : cexpr → Option cexpr
  | CEIf _ _ z => some z
  | _ => none

/-! ## `Assn` node fields (pure) -/

def assn_code : cassn → w64
  | CAEmp => W64 1 | CASep _ _ => W64 2 | CAOr _ _ => W64 3
  | CAExists _ _ _ => W64 4 | CAPure _ => W64 5 | CAPointsTo _ _ => W64 6

def assn_var : cassn → w64
  | CAExists n _ _ => W64 n
  | _ => W64 0

def assn_sort : cassn → w64
  | CAExists _ s _ => sort_code s
  | _ => W64 0

def assn_l : cassn → Option cassn
  | CASep p _ | CAOr p _ | CAExists _ _ p => some p
  | _ => none

def assn_r : cassn → Option cassn
  | CASep _ q | CAOr _ q => some q
  | _ => none

def assn_x : cassn → Option term
  | CAPure t => some t
  | CAPointsTo x _ => some x
  | _ => none

def assn_y : cassn → Option term
  | CAPointsTo _ y => some y
  | _ => none

def assn_idx_wf : cassn → Prop
  | CAExists n _ _ => idx_wf n
  | _ => True

section nodes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## `Expr` nodes -/

def is_oexpr (l : Loc) : Option cexpr → IProp GF
  | none => iprop(⌜l = null⌝)
  | some e' => is_expr l e'

theorem is_oexpr_some (l : Loc) (e : cexpr) : is_oexpr (GF := GF) l (some e) = is_expr l e := rfl
theorem is_oexpr_none (l : Loc) : is_oexpr (GF := GF) l none = iprop(⌜l = null⌝) := rfl

instance is_oexpr_persistent (l : Loc) (e : Option cexpr) :
    Persistent (is_oexpr (GF := GF) l e) := by
  cases e <;> unfold is_oexpr <;> infer_instance

theorem is_oexpr_null (l : Loc) (e : Option cexpr) :
    is_oexpr (GF := GF) l e ⊢ ⌜l = null ↔ e = none⌝ := by
  cases e with
  | none => simp only [is_oexpr]; iintro %H; ipureintro; simp [H]
  | some e' =>
    simp only [is_oexpr]
    iintro H
    ihave %Hn := is_expr_not_null _ _ $$ H
    ipureintro; simp [Hn]

theorem is_expr_node (l : Loc) (e : cexpr) :
    is_expr (GF := GF) l e ⊢ ∃ lty lty2 la lb lc : Loc,
      l ↦□ enode (expr_code e) (expr_name e) (expr_num e) (expr_op e) lty lty2 la lb lc ∗
      is_otype lty (expr_ty e) ∗ is_otype lty2 (expr_ty2 e) ∗
      is_oexpr la (expr_a e) ∗ is_oexpr lb (expr_b e) ∗ is_oexpr lc (expr_c e) := by
  cases e <;> simp only [is_expr, expr_code, expr_name, expr_num, expr_op, expr_ty, expr_ty2,
    expr_a, expr_b, expr_c, is_otype, is_oexpr, enode0]
  case CEInt | CEBool | CEUnit | CEVar =>
    iintro #H; iexists null, null, null, null, null; iframe H; ipureintro; trivial
  case CELet | CESeq | CEExcSeq =>
    iintro ⟨%q1, %q2, #H, #H1, #H2⟩; iexists null, null, q1, q2, null
    iframe H H1 H2; ipureintro; trivial
  case CEIf =>
    iintro ⟨%q1, %q2, %q3, #H, #H1, #H2, #H3⟩; iexists null, null, q1, q2, q3
    iframe H H1 H2 H3; ipureintro; trivial
  case CELoad | CEAlloc | CEUnOp =>
    iintro ⟨%r1, %q1, #H, #H1, #H2⟩; iexists r1, null, q1, null, null
    iframe H H1 H2; ipureintro; trivial
  case CEStore | CEBinOp =>
    iintro ⟨%r1, %q1, %q2, #H, #H1, #H2, #H3⟩; iexists r1, null, q1, q2, null
    iframe H H1 H2 H3; ipureintro; trivial
  case CEZero =>
    iintro ⟨%r1, #H, #H1⟩; iexists r1, null, null, null, null
    iframe H H1; ipureintro; trivial
  case CEConvert =>
    iintro ⟨%r1, %r2, %q1, #H, #H1, #H2, #H3⟩; iexists r1, r2, q1, null, null
    iframe H H1 H2 H3; ipureintro; trivial
  case CEDo | CEReturn | CEExcDo =>
    iintro ⟨%q1, #H, #H1⟩; iexists null, null, q1, null, null
    iframe H H1; ipureintro; trivial

/-! ## `Assn` nodes -/

def is_oassn (l : Loc) : Option cassn → IProp GF
  | none => iprop(⌜l = null⌝)
  | some a' => is_assn l a'

theorem is_oassn_some (l : Loc) (a : cassn) : is_oassn (GF := GF) l (some a) = is_assn l a := rfl
theorem is_oassn_none (l : Loc) : is_oassn (GF := GF) l none = iprop(⌜l = null⌝) := rfl

instance is_oassn_persistent (l : Loc) (a : Option cassn) :
    Persistent (is_oassn (GF := GF) l a) := by
  cases a <;> unfold is_oassn <;> infer_instance

theorem is_oassn_null (l : Loc) (a : Option cassn) :
    is_oassn (GF := GF) l a ⊢ ⌜l = null ↔ a = none⌝ := by
  cases a with
  | none => simp only [is_oassn]; iintro %H; ipureintro; simp [H]
  | some a' =>
    simp only [is_oassn]
    iintro H
    ihave %Hn := is_assn_not_null _ _ $$ H
    ipureintro; simp [Hn]

theorem is_assn_node (l : Loc) (a : cassn) :
    is_assn (GF := GF) l a ⊢ ∃ lL lR lX lY : Loc,
      ⌜assn_idx_wf a⌝ ∗
      l ↦□ anode (assn_code a) lL lR lX lY (assn_var a) (assn_sort a) ∗
      is_oassn lL (assn_l a) ∗ is_oassn lR (assn_r a) ∗
      is_oterm lX (assn_x a) ∗ is_oterm lY (assn_y a) := by
  cases a <;> simp only [is_assn, assn_idx_wf, assn_code, assn_var, assn_sort, assn_l, assn_r,
    assn_x, assn_y, is_oassn, is_oterm]
  case CAEmp =>
    iintro #H; iexists null, null, null, null; iframe H; ipureintro; trivial
  case CASep | CAOr =>
    iintro ⟨%q1, %q2, #H, #H1, #H2⟩; iexists q1, q2, null, null
    iframe H H1 H2; ipureintro; trivial
  case CAExists =>
    iintro ⟨%q1, %Hw, #H, #H1⟩; iexists q1, null, null, null
    iframe H H1; ipureintro; exact ⟨Hw, rfl, rfl, rfl⟩
  case CAPure =>
    iintro ⟨%q1, #H, #H1⟩; iexists null, null, q1, null
    iframe H H1; ipureintro; trivial
  case CAPointsTo =>
    iintro ⟨%q1, %q2, #H, #H1, #H2⟩; iexists null, null, q1, q2
    iframe H H1 H2; ipureintro; trivial

/-! ## `sortEnv`

The struct and the three slices it points at are read but never written
by `sortOfEnv`, so the specification is parametric in the fraction. -/
def is_sortenv (dq : DFrac) (l : Loc) (E : sort_env) : IProp GF :=
  iprop(∃ sv sp sok : GoSlice,
      l ↦{dq} checker.sortEnv.mk sv sp sok (sort_code (se_ret E)) (se_ret_ok E) ∗
      sv ↦*{dq} ((se_vars E).map sort_code) ∗
      sp ↦*{dq} ((se_pats E).map sort_code) ∗
      sok ↦*{dq} se_pat_ok E)

end nodes

end Checker
end Perennial
