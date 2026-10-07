/-
Port of `new/checker/fn/exec.v`.

`checker.exec` (checker/exec.go): the dispatcher of symbolic execution.

`exec` switches on the node's kind and tail-calls the function for that
kind, all of which share its signature and hence the one specification
`exec_like` (exec_def.v). So the proof is in two layers:

- one small lemma per kind, `exec_via_X`: if the case function meets
  `exec_like` for the node, so does `exec`. Each evaluates the kind
  switch with a literal kind code.
- `wp_exec`, by induction on the `cexpr`, feeding each case lemma the
  induction hypotheses for the subexpressions.

Lean notes:
* The Lean goose output of `exec` has no nil test on the expression (the
  Rocq proof's `try (wp_if_destruct; ...)` step); the switch is reached
  directly.
* The common proof of the `exec_via_X` lemmas (Rocq's `dispatch` Ltac) is
  the `exec_dispatch` macro.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.Fn.execInt
import Checkers.Checker.Fn.execBool
import Checkers.Checker.Fn.execUnit
import Checkers.Checker.Fn.execVar
import Checkers.Checker.Fn.execLet
import Checkers.Checker.Fn.execSeq
import Checkers.Checker.Fn.execIfs
import Checkers.Checker.Fn.execLoad
import Checkers.Checker.Fn.execStore
import Checkers.Checker.Fn.execAlloc
import Checkers.Checker.Fn.execZero
import Checkers.Checker.Fn.execBinOp
import Checkers.Checker.Fn.execUnOp
import Checkers.Checker.Fn.execConvert
import Checkers.Checker.Fn.execDo
import Checkers.Checker.Fn.execReturn
import Checkers.Checker.Fn.execExcSeq
import Checkers.Checker.Fn.execExcDo

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

set_option hygiene false in
/-- Everything up to and including the tail call to the case function. -/
macro "exec_dispatch" : tactic => `(tactic| (
  intro Hc
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  ihave %Hnn := is_expr_not_null _ _ $$ He
  icases is_expr_node _ _ $$ He with ⟨%a1, %a2, %a3, %a4, %a5, #Hnode, -, -, -, -, -⟩
  iStructNamed Hnode
  wp_auto
  rw [show decide (le = null) = false from decide_eq_false Hnn]
  wp_auto
  repeat (simp (config := {decide := true}) only [expr_code, checker.EInt, checker.EBool,
    checker.EUnit, checker.EVar, checker.ELet, checker.ESeq, checker.EIf, checker.ELoad,
    checker.EStore, checker.EAlloc, checker.EZero, checker.EBinOp, checker.EUnOp,
    checker.EConvert, checker.EDo, checker.EReturn, checker.EExcSeq, checker.EExcDo]; wp_auto)
  wp_apply exec_like_triple _ _ Hc le lρ lst ρ sst $$ [Hst] as %s %lf Hpost
  · iframe Hst He Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
  iapply HΦ
  iexact Hpost))

theorem exec_via_int (w : w64) :
    (⊢ exec_like (GF := GF) checker.execInt (CEInt w)) →
    ⊢ exec_like (GF := GF) checker.exec (CEInt w) := by
  exec_dispatch

theorem exec_via_bool (b : Bool) :
    (⊢ exec_like (GF := GF) checker.execBool (CEBool b)) →
    ⊢ exec_like (GF := GF) checker.exec (CEBool b) := by
  exec_dispatch

theorem exec_via_unit  :
    (⊢ exec_like (GF := GF) checker.execUnit CEUnit) →
    ⊢ exec_like (GF := GF) checker.exec CEUnit := by
  exec_dispatch

theorem exec_via_var (x : GoString) :
    (⊢ exec_like (GF := GF) checker.execVar (CEVar x)) →
    ⊢ exec_like (GF := GF) checker.exec (CEVar x) := by
  exec_dispatch

theorem exec_via_let (x : GoString) (c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execLet (CELet x c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CELet x c1 c2) := by
  exec_dispatch

theorem exec_via_seq (c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execSeq (CESeq c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CESeq c1 c2) := by
  exec_dispatch

theorem exec_via_if (c0 c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execIfs (CEIf c0 c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CEIf c0 c1 c2) := by
  exec_dispatch

theorem exec_via_load (t : ctype) (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execLoad (CELoad t c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CELoad t c1) := by
  exec_dispatch

theorem exec_via_store (t : ctype) (c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execStore (CEStore t c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CEStore t c1 c2) := by
  exec_dispatch

theorem exec_via_alloc (t : ctype) (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execAlloc (CEAlloc t c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEAlloc t c1) := by
  exec_dispatch

theorem exec_via_zero (t : ctype) :
    (⊢ exec_like (GF := GF) checker.execZero (CEZero t)) →
    ⊢ exec_like (GF := GF) checker.exec (CEZero t) := by
  exec_dispatch

theorem exec_via_binop (o : cop) (t : ctype) (c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execBinOp (CEBinOp o t c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CEBinOp o t c1 c2) := by
  exec_dispatch

theorem exec_via_unop (o : cop) (t : ctype) (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execUnOp (CEUnOp o t c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEUnOp o t c1) := by
  exec_dispatch

theorem exec_via_convert (t1 t2 : ctype) (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execConvert (CEConvert t1 t2 c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEConvert t1 t2 c1) := by
  exec_dispatch

theorem exec_via_do (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execDo (CEDo c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEDo c1) := by
  exec_dispatch

theorem exec_via_return (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execReturn (CEReturn c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEReturn c1) := by
  exec_dispatch

theorem exec_via_exc_seq (c1 c2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execExcSeq (CEExcSeq c1 c2)) →
    ⊢ exec_like (GF := GF) checker.exec (CEExcSeq c1 c2) := by
  exec_dispatch

theorem exec_via_exc_do (c1 : cexpr) :
    (⊢ exec_like (GF := GF) checker.execExcDo (CEExcDo c1)) →
    ⊢ exec_like (GF := GF) checker.exec (CEExcDo c1) := by
  exec_dispatch

/-! ## The induction -/

theorem wp_exec (ce : cexpr) : ⊢ exec_like (GF := GF) checker.exec ce := by
  induction ce with
  | CEInt w => exact exec_via_int w (wp_execInt w)
  | CEBool b => exact exec_via_bool b (wp_execBool b)
  | CEUnit => exact exec_via_unit wp_execUnit
  | CEVar x => exact exec_via_var x (wp_execVar x)
  | CELet x c1 c2 IH1 IH2 => exact exec_via_let x c1 c2 (wp_execLet x c1 c2 IH1 IH2)
  | CESeq c1 c2 IH1 IH2 => exact exec_via_seq c1 c2 (wp_execSeq c1 c2 IH1 IH2)
  | CEIf c0 c1 c2 IH0 IH1 IH2 => exact exec_via_if c0 c1 c2 (wp_execIfs c0 c1 c2 IH0 IH1 IH2)
  | CELoad t c1 IH1 => exact exec_via_load t c1 (wp_execLoad t c1 IH1)
  | CEStore t c1 c2 IH1 IH2 => exact exec_via_store t c1 c2 (wp_execStore t c1 c2 IH1 IH2)
  | CEAlloc t c1 IH1 => exact exec_via_alloc t c1 (wp_execAlloc t c1 IH1)
  | CEZero t => exact exec_via_zero t (wp_execZero t)
  | CEBinOp o t c1 c2 IH1 IH2 =>
    exact exec_via_binop o t c1 c2 (wp_execBinOp o t c1 c2 IH1 IH2)
  | CEUnOp o t c1 IH1 => exact exec_via_unop o t c1 (wp_execUnOp o t c1 IH1)
  | CEConvert t1 t2 c1 IH1 => exact exec_via_convert t1 t2 c1 (wp_execConvert t1 t2 c1 IH1)
  | CEDo c1 IH1 => exact exec_via_do c1 (wp_execDo c1 IH1)
  | CEReturn c1 IH1 => exact exec_via_return c1 (wp_execReturn c1 IH1)
  | CEExcSeq c1 c2 IH1 IH2 => exact exec_via_exc_seq c1 c2 (wp_execExcSeq c1 c2 IH1 IH2)
  | CEExcDo c1 IH1 => exact exec_via_exc_do c1 (wp_execExcDo c1 IH1)

end proof

end Checker
end Perennial
