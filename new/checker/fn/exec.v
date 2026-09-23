(** [checker.exec] (checker/exec.go): the dispatcher of symbolic execution.

    [exec] only tests for a nil expression and then tail-calls the function
    for the node's kind, all of which share its signature and hence the one
    specification [exec_like] (exec_def.v). So the proof is in two layers:

    - one small lemma per kind, [exec_via_X]: if the case function meets
      [exec_like] for the node, so does [exec]. Each evaluates the kind
      switch with a literal kind code; keeping them apart keeps each proof
      term small (see NOTES.md on fn/sortOfEnv.v).
    - [wp_exec], by induction on the [cexpr], feeding each case lemma the
      induction hypotheses for the subexpressions.

    Note on naming: the Go locals are [e], [en] and [st], so no Rocq variable
    here may have those names. *)
From New.checker Require Import prelude nodes exec_spec exec_def.
From New.checker.fn Require Import
  execInt execBool execUnit execVar execLet execSeq execIfs execLoad execStore
  execAlloc execZero execBinOp execUnOp execConvert execDo execReturn execExcSeq
  execExcDo.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** Everything up to and including the tail call to the case function [fn]. *)
Local Ltac dispatch :=
  let Hc := fresh "Hc" in
  intros Hc; iPoseProof Hc as "#Hcase";
  iIntros (?????);
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)";
  iDestruct (is_expr_not_null with "He") as %Hnn;
  iDestruct (is_expr_node with "He") as (?????) "(#Hnode & _)";
  iSimpl in "Hnode";
  wp_auto;
  try (wp_if_destruct; first congruence);
  try wp_auto;
  wp_apply ("Hcase" with "[$Hst]") as (??) "Hpost";
  [ iFrame "#"; done | ];
  try wp_auto;
  iApply "HΦ"; iExact "Hpost".

Lemma exec_via_int w : (⊢ exec_like checker.execInt (CEInt w)) → ⊢ exec_like checker.exec (CEInt w).
Proof. dispatch. Qed.
Lemma exec_via_bool b : (⊢ exec_like checker.execBool (CEBool b)) → ⊢ exec_like checker.exec (CEBool b).
Proof. dispatch. Qed.
Lemma exec_via_unit : (⊢ exec_like checker.execUnit CEUnit) → ⊢ exec_like checker.exec CEUnit.
Proof. dispatch. Qed.
Lemma exec_via_var x : (⊢ exec_like checker.execVar (CEVar x)) → ⊢ exec_like checker.exec (CEVar x).
Proof. dispatch. Qed.
Lemma exec_via_let x c1 c2 : (⊢ exec_like checker.execLet (CELet x c1 c2)) → ⊢ exec_like checker.exec (CELet x c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_seq c1 c2 : (⊢ exec_like checker.execSeq (CESeq c1 c2)) → ⊢ exec_like checker.exec (CESeq c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_if c0 c1 c2 : (⊢ exec_like checker.execIfs (CEIf c0 c1 c2)) → ⊢ exec_like checker.exec (CEIf c0 c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_load t c1 : (⊢ exec_like checker.execLoad (CELoad t c1)) → ⊢ exec_like checker.exec (CELoad t c1).
Proof. dispatch. Qed.
Lemma exec_via_store t c1 c2 : (⊢ exec_like checker.execStore (CEStore t c1 c2)) → ⊢ exec_like checker.exec (CEStore t c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_alloc t c1 : (⊢ exec_like checker.execAlloc (CEAlloc t c1)) → ⊢ exec_like checker.exec (CEAlloc t c1).
Proof. dispatch. Qed.
Lemma exec_via_zero t : (⊢ exec_like checker.execZero (CEZero t)) → ⊢ exec_like checker.exec (CEZero t).
Proof. dispatch. Qed.
Lemma exec_via_binop o t c1 c2 : (⊢ exec_like checker.execBinOp (CEBinOp o t c1 c2)) → ⊢ exec_like checker.exec (CEBinOp o t c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_unop o t c1 : (⊢ exec_like checker.execUnOp (CEUnOp o t c1)) → ⊢ exec_like checker.exec (CEUnOp o t c1).
Proof. dispatch. Qed.
Lemma exec_via_convert t1 t2 c1 : (⊢ exec_like checker.execConvert (CEConvert t1 t2 c1)) → ⊢ exec_like checker.exec (CEConvert t1 t2 c1).
Proof. dispatch. Qed.
Lemma exec_via_do c1 : (⊢ exec_like checker.execDo (CEDo c1)) → ⊢ exec_like checker.exec (CEDo c1).
Proof. dispatch. Qed.
Lemma exec_via_return c1 : (⊢ exec_like checker.execReturn (CEReturn c1)) → ⊢ exec_like checker.exec (CEReturn c1).
Proof. dispatch. Qed.
Lemma exec_via_exc_seq c1 c2 : (⊢ exec_like checker.execExcSeq (CEExcSeq c1 c2)) → ⊢ exec_like checker.exec (CEExcSeq c1 c2).
Proof. dispatch. Qed.
Lemma exec_via_exc_do c1 : (⊢ exec_like checker.execExcDo (CEExcDo c1)) → ⊢ exec_like checker.exec (CEExcDo c1).
Proof. dispatch. Qed.

(** * The induction *)

Lemma wp_exec (ce : cexpr) : ⊢ exec_like checker.exec ce.
Proof.
  induction ce as [w|b| |x|x c1 IH1 c2 IH2|c1 IH1 c2 IH2|c0 IH0 c1 IH1 c2 IH2
                  |t c1 IH1|t c1 IH1 c2 IH2|t c1 IH1|t|o t c1 IH1 c2 IH2|o t c1 IH1
                  |t1 t2 c1 IH1|c1 IH1|c1 IH1|c1 IH1 c2 IH2|c1 IH1].
  - apply exec_via_int, wp_execInt.
  - apply exec_via_bool, wp_execBool.
  - apply exec_via_unit, wp_execUnit.
  - apply exec_via_var, wp_execVar.
  - apply exec_via_let, wp_execLet; done.
  - apply exec_via_seq, wp_execSeq; done.
  - apply exec_via_if, wp_execIfs; done.
  - apply exec_via_load, wp_execLoad; done.
  - apply exec_via_store, wp_execStore; done.
  - apply exec_via_alloc, wp_execAlloc; done.
  - apply exec_via_zero, wp_execZero.
  - apply exec_via_binop, wp_execBinOp; done.
  - apply exec_via_unop, wp_execUnOp; done.
  - apply exec_via_convert, wp_execConvert; done.
  - apply exec_via_do, wp_execDo; done.
  - apply exec_via_return, wp_execReturn; done.
  - apply exec_via_exc_seq, wp_execExcSeq; done.
  - apply exec_via_exc_do, wp_execExcDo; done.
Qed.

End proof.
