(** Decoding lemmas for [Expr] and [Assn] nodes, and the representation of
    the checker's [sortEnv].

    Kept apart from repr.v only because repr.v was already built when these
    were written; they belong with the rest of the representation layer. *)
From New.checker Require Import prelude.

Section nodes.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

(** * [Expr] nodes *)

Definition is_oexpr (l : loc) (e : option cexpr) : iProp Σ :=
  match e with None => ⌜l = null⌝ | Some e' => is_expr l e' end%I.

#[global] Instance is_oexpr_persistent l e : Persistent (is_oexpr l e).
Proof. destruct e; apply _. Qed.

Lemma is_oexpr_null l e : is_oexpr l e -∗ ⌜l = null ↔ e = None⌝.
Proof.
  destruct e as [e'|]; simpl; last by iIntros "%"; iPureIntro; naive_solver.
  iIntros "H". iDestruct (is_expr_not_null with "H") as %?.
  iPureIntro. naive_solver.
Qed.

Definition expr_code (e : cexpr) : w64 :=
  match e with
  | CEInt _ => W64 1 | CEBool _ => W64 2 | CEUnit => W64 3 | CEVar _ => W64 4
  | CELet _ _ _ => W64 5 | CESeq _ _ => W64 6 | CEIf _ _ _ => W64 7
  | CELoad _ _ => W64 8 | CEStore _ _ _ => W64 9 | CEAlloc _ _ => W64 10
  | CEZero _ => W64 11 | CEBinOp _ _ _ _ => W64 12 | CEUnOp _ _ _ => W64 13
  | CEConvert _ _ _ => W64 14 | CEDo _ => W64 15 | CEReturn _ => W64 16
  | CEExcSeq _ _ => W64 17 | CEExcDo _ => W64 18
  end.

Definition expr_name (e : cexpr) : go_string :=
  match e with CEVar x => x | CELet x _ _ => x | _ => ""%go end.

Definition expr_num (e : cexpr) : w64 :=
  match e with CEInt w => w | CEBool b => bool_code b | _ => W64 0 end.

Definition expr_op (e : cexpr) : w64 :=
  match e with CEBinOp op _ _ _ | CEUnOp op _ _ => op_code op | _ => W64 0 end.

Definition expr_ty (e : cexpr) : option ctype :=
  match e with
  | CELoad t _ | CEStore t _ _ | CEAlloc t _ | CEZero t
  | CEBinOp _ t _ _ | CEUnOp _ t _ | CEConvert t _ _ => Some t
  | _ => None
  end.

Definition expr_ty2 (e : cexpr) : option ctype :=
  match e with CEConvert _ t2 _ => Some t2 | _ => None end.

Definition expr_a (e : cexpr) : option cexpr :=
  match e with
  | CELet _ x _ | CESeq x _ | CEIf x _ _ | CELoad _ x | CEStore _ x _
  | CEAlloc _ x | CEBinOp _ _ x _ | CEUnOp _ _ x | CEConvert _ _ x
  | CEDo x | CEReturn x | CEExcSeq x _ | CEExcDo x => Some x
  | _ => None
  end.

Definition expr_b (e : cexpr) : option cexpr :=
  match e with
  | CELet _ _ y | CESeq _ y | CEIf _ y _ | CEStore _ _ y | CEBinOp _ _ _ y
  | CEExcSeq _ y => Some y
  | _ => None
  end.

Definition expr_c (e : cexpr) : option cexpr :=
  match e with CEIf _ _ z => Some z | _ => None end.

Lemma is_expr_node l e :
  is_expr l e -∗ ∃ lty lty2 la lb lc : loc,
    l ↦□ enode (expr_code e) (expr_name e) (expr_num e) (expr_op e) lty lty2 la lb lc ∗
    is_otype lty (expr_ty e) ∗ is_otype lty2 (expr_ty2 e) ∗
    is_oexpr la (expr_a e) ∗ is_oexpr lb (expr_b e) ∗ is_oexpr lc (expr_c e).
Proof.
  iIntros "H". destruct e; simpl.
  - (* CEInt *)
    iExists null, null, null, null, null; iFrame "H"; iPureIntro; done.
  - (* CEBool *)
    iExists null, null, null, null, null; iFrame "H"; iPureIntro; done.
  - (* CEUnit *)
    iExists null, null, null, null, null; iFrame "H"; iPureIntro; done.
  - (* CEVar *)
    iExists null, null, null, null, null; iFrame "H"; iPureIntro; done.
  - (* CELet *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists null, null, q1, q2, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CESeq *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists null, null, q1, q2, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CEIf *)
    iDestruct "H" as (q1 q2 q3) "(H & #H1 & #H2 & #H3)"; iExists null, null, q1, q2, q3;
    iFrame "H H1 H2 H3"; iPureIntro; done.
  - (* CELoad *)
    iDestruct "H" as (r1 q1) "(H & #H1 & #H2)"; iExists r1, null, q1, null, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CEStore *)
    iDestruct "H" as (r1 q1 q2) "(H & #H1 & #H2 & #H3)"; iExists r1, null, q1, q2, null;
    iFrame "H H1 H2 H3"; iPureIntro; done.
  - (* CEAlloc *)
    iDestruct "H" as (r1 q1) "(H & #H1 & #H2)"; iExists r1, null, q1, null, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CEZero *)
    iDestruct "H" as (r1) "(H & #H1)"; iExists r1, null, null, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* CEBinOp *)
    iDestruct "H" as (r1 q1 q2) "(H & #H1 & #H2 & #H3)"; iExists r1, null, q1, q2, null;
    iFrame "H H1 H2 H3"; iPureIntro; done.
  - (* CEUnOp *)
    iDestruct "H" as (r1 q1) "(H & #H1 & #H2)"; iExists r1, null, q1, null, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CEConvert *)
    iDestruct "H" as (r1 r2 q1) "(H & #H1 & #H2 & #H3)"; iExists r1, r2, q1, null, null;
    iFrame "H H1 H2 H3"; iPureIntro; done.
  - (* CEDo *)
    iDestruct "H" as (q1) "(H & #H1)"; iExists null, null, q1, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* CEReturn *)
    iDestruct "H" as (q1) "(H & #H1)"; iExists null, null, q1, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* CEExcSeq *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists null, null, q1, q2, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CEExcDo *)
    iDestruct "H" as (q1) "(H & #H1)"; iExists null, null, q1, null, null;
    iFrame "H H1"; iPureIntro; done.
Qed.

(** * [Assn] nodes *)

Definition is_oassn (l : loc) (a : option cassn) : iProp Σ :=
  match a with None => ⌜l = null⌝ | Some a' => is_assn l a' end%I.

#[global] Instance is_oassn_persistent l a : Persistent (is_oassn l a).
Proof. destruct a; apply _. Qed.

Lemma is_oassn_null l a : is_oassn l a -∗ ⌜l = null ↔ a = None⌝.
Proof.
  destruct a as [a'|]; simpl; last by iIntros "%"; iPureIntro; naive_solver.
  iIntros "H". iDestruct (is_assn_not_null with "H") as %?.
  iPureIntro. naive_solver.
Qed.

Definition assn_code (a : cassn) : w64 :=
  match a with
  | CAEmp => W64 1 | CASep _ _ => W64 2 | CAOr _ _ => W64 3
  | CAExists _ _ _ => W64 4 | CAPure _ => W64 5 | CAPointsTo _ _ => W64 6
  end.

Definition assn_var (a : cassn) : w64 :=
  match a with CAExists n _ _ => W64 n | _ => W64 0 end.

Definition assn_sort (a : cassn) : w64 :=
  match a with CAExists _ s _ => sort_code s | _ => W64 0 end.

Definition assn_l (a : cassn) : option cassn :=
  match a with CASep p _ | CAOr p _ | CAExists _ _ p => Some p | _ => None end.

Definition assn_r (a : cassn) : option cassn :=
  match a with CASep _ q | CAOr _ q => Some q | _ => None end.

Definition assn_x (a : cassn) : option term :=
  match a with CAPure t => Some t | CAPointsTo x _ => Some x | _ => None end.

Definition assn_y (a : cassn) : option term :=
  match a with CAPointsTo _ y => Some y | _ => None end.

Definition assn_idx_wf (a : cassn) : Prop :=
  match a with CAExists n _ _ => idx_wf n | _ => True end.

Lemma is_assn_node l a :
  is_assn l a -∗ ∃ lL lR lX lY : loc,
    ⌜assn_idx_wf a⌝ ∗
    l ↦□ anode (assn_code a) lL lR lX lY (assn_var a) (assn_sort a) ∗
    is_oassn lL (assn_l a) ∗ is_oassn lR (assn_r a) ∗
    is_oterm lX (assn_x a) ∗ is_oterm lY (assn_y a).
Proof.
  iIntros "H". destruct a; simpl.
  - (* CAEmp *)
    iExists null, null, null, null; iFrame "H"; iPureIntro; done.
  - (* CASep *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists q1, q2, null, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CAOr *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists q1, q2, null, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* CAExists *)
    iDestruct "H" as (q1) "(%Hw & H & #H1)"; iExists q1, null, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* CAPure *)
    iDestruct "H" as (q1) "(H & #H1)"; iExists null, null, q1, null;
    iFrame "H H1"; iPureIntro; done.
  - (* CAPointsTo *)
    iDestruct "H" as (q1 q2) "(H & #H1 & #H2)"; iExists null, null, q1, q2;
    iFrame "H H1 H2"; iPureIntro; done.
Qed.

(** * [sortEnv]

    The struct and the three slices it points at are read but never written
    by [sortOfEnv], so the specification is parametric in the fraction. *)
Definition is_sortenv (dq : dfrac) (l : loc) (E : sort_env) : iProp Σ :=
  (∃ sv sp sok : slice.t,
      l ↦{dq} checker.sortEnv.mk sv sp sok (sort_code (se_ret E)) (se_ret_ok E) ∗
      sv ↦*{dq} (sort_code <$> se_vars E) ∗
      sp ↦*{dq} (sort_code <$> se_pats E) ∗
      sok ↦*{dq} se_pat_ok E)%I.

End nodes.
