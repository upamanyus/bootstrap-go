(** Representation predicates.

    [is_type], [is_term], [is_expr], [is_assn], [is_func] and [is_sorts]
    (defs.v) describe the checker's *input* in the Go heap; this file gives
    their persistence instances and the corresponding predicates for the
    checker's *internal* data (environments, cells, states, paths), which do
    not appear in the soundness statement. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Import defs term_lemmas interp.

Set Default Proof Using "All".

Section repr.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** * Persistence

    The checker never mutates a [Type], [Term], [Expr] or [Assn] node after
    construction (see the immutability invariant in checker/doc.go), which is
    what lets these be described with discarded fractions. *)

#[global] Instance is_type_persistent l t : Persistent (is_type l t).
Proof. revert l. induction t; apply _. Qed.

#[global] Instance is_term_persistent l t : Persistent (is_term l t).
Proof. revert l. induction t; apply _. Qed.

#[global] Instance is_expr_persistent l e : Persistent (is_expr l e).
Proof. revert l. induction e; apply _. Qed.

#[global] Instance is_assn_persistent l a : Persistent (is_assn l a).
Proof. revert l. induction a; apply _. Qed.

#[global] Instance is_func_persistent l f : Persistent (is_func l f).
Proof. apply _. Qed.

#[global] Instance is_sorts_persistent s vars : Persistent (is_sorts s vars).
Proof. apply _. Qed.

(** * Non-nullness

    A represented node is a real allocation, so the nil checks the Go code
    performs first always take the non-nil branch. *)

(** Every case of these predicates is a (possibly existentially quantified,
    possibly pure-prefixed) points-to for the node itself followed by its
    children; this peels off whatever prefix it has. *)
Ltac peel_node :=
  first [ iDestruct "H" as (???) "[H _]"
        | iDestruct "H" as (??) "[H _]"
        | iDestruct "H" as (?) "(_ & H & _)"
        | iDestruct "H" as (?) "[H _]"
        | iDestruct "H" as "[_ H]"
        | idtac ];
  iApply (typed_pointsto_not_null with "H").

Lemma is_type_not_null l t : is_type l t -∗ ⌜l ≠ null⌝.
Proof. iIntros "H". destruct t; simpl; peel_node. Qed.

Lemma is_term_not_null l t : is_term l t -∗ ⌜l ≠ null⌝.
Proof. iIntros "H". destruct t; simpl; peel_node. Qed.

Lemma is_expr_not_null l e : is_expr l e -∗ ⌜l ≠ null⌝.
Proof. iIntros "H". destruct e; simpl; peel_node. Qed.

Lemma is_assn_not_null l a : is_assn l a -∗ ⌜l ≠ null⌝.
Proof. iIntros "H". destruct a; simpl; peel_node. Qed.

(** * Decoding a node

    The Go code switches on a node's kind field, so each proof needs the node
    in a uniform shape: the kind code, and the children. *)

(** A [Type] node's [Elem] field is [null] at every type but a pointer. *)
Definition is_otype (l : loc) (t : option ctype) : iProp Σ :=
  match t with None => ⌜l = null⌝ | Some t' => is_type l t' end%I.

#[global] Instance is_otype_persistent l t : Persistent (is_otype l t).
Proof. destruct t; apply _. Qed.

Lemma is_otype_null l t : is_otype l t -∗ ⌜l = null ↔ t = None⌝.
Proof.
  destruct t as [t'|]; simpl; last by iIntros "%"; iPureIntro; naive_solver.
  iIntros "H". iDestruct (is_type_not_null with "H") as %?.
  iPureIntro. naive_solver.
Qed.

Definition type_code (t : ctype) : w64 :=
  match t with
  | CTyInt => W64 1 | CTyInt64 => W64 2 | CTyUint64 => W64 3
  | CTyBool => W64 4 | CTyPtr _ => W64 5
  end.

Definition ctype_elem (t : ctype) : option ctype :=
  match t with CTyPtr e => Some e | _ => None end.

(** A type is determined by its kind code and its element type -- which is
    what makes [TypeEq]'s two comparisons complete. *)
Lemma ctype_eq_iff ta tb :
  ta = tb ↔ type_code ta = type_code tb ∧ ctype_elem ta = ctype_elem tb.
Proof.
  split; first by intros ->.
  destruct ta, tb; simpl; intros [Hc He]; try done;
    try (exfalso; revert Hc; word); naive_solver.
Qed.

Lemma is_type_node l t :
  is_type l t -∗ ∃ le : loc,
    l ↦□ checker.Type'.mk (type_code t) le ∗ is_otype le (ctype_elem t).
Proof.
  destruct t; simpl; try (iIntros "H"; iExists null; by iFrame "H").
  iIntros "H". iDestruct "H" as (le) "[H #He]". iExists le. by iFrame "H He".
Qed.

(** * The checker's internal data *)

Definition is_cell (c : checker.Cell.t) (sc : scell) : iProp Σ :=
  (is_term c.(checker.Cell.Loc') (cloc sc) ∗ is_term c.(checker.Cell.Val') (cval sc))%I.

#[global] Instance is_cell_persistent c sc : Persistent (is_cell c sc).
Proof. apply _. Qed.

(** A symbolic heap: a slice of [Cell] structs, one per owned cell. The slice
    is mutable (a state is cloned before it is changed), the terms in it are
    not. *)
Definition is_heap (s : slice.t) (H : list scell) : iProp Σ :=
  (∃ cs : list checker.Cell.t, s ↦* cs ∗ [∗ list] c;sc ∈ cs;H, is_cell c sc)%I.

Definition is_cond (s : slice.t) (pc : list term) : iProp Σ :=
  (∃ ls : list loc, s ↦* ls ∗ [∗ list] l;t ∈ ls;pc, is_term l t)%I.

Definition is_vars (s : slice.t) (vars : list sort) : iProp Σ :=
  (s ↦* (sort_code <$> vars))%I.

Definition is_state (l : loc) (st : sstate) : iProp Σ :=
  (∃ hs cs vs : slice.t,
      l ↦ checker.State.mk hs cs vs ∗
      is_heap hs (sheap st) ∗ is_cond cs (spc st) ∗ is_vars vs (svars st))%I.

Definition is_path (p : checker.Path.t) (sp : spath) : iProp Σ :=
  (is_term p.(checker.Path.Ret') (pret sp) ∗ is_state p.(checker.Path.St') (pst sp))%I.

Definition is_paths (s : slice.t) (ps : list spath) : iProp Σ :=
  (∃ xs : list checker.Path.t, s ↦* xs ∗ [∗ list] x;p ∈ xs;ps, is_path x p)%I.

(** The variable environment of checker/exec.go: a linked list, most recent
    binding first, never mutated. *)
Fixpoint is_env (l : loc) (ρ : list (go_string * term)) : iProp Σ :=
  match ρ with
  | [] => ⌜l = null⌝
  | xt :: ρ' =>
      ∃ lt ln, l ↦□ checker.env.mk xt.1 lt ln ∗ is_term lt xt.2 ∗ is_env ln ρ'
  end%I.

#[global] Instance is_env_persistent l ρ : Persistent (is_env l ρ).
Proof. revert l. induction ρ; apply _. Qed.

End repr.
