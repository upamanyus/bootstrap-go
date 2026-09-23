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
Context {sem : go.Semantics}.
Set Default Proof Using "All".

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

(** A [Term] node's [A]/[B]/[C] fields are [null] where the constructor has
    no child there. *)
Definition is_oterm (l : loc) (t : option term) : iProp Σ :=
  match t with None => ⌜l = null⌝ | Some t' => is_term l t' end%I.

#[global] Instance is_oterm_persistent l t : Persistent (is_oterm l t).
Proof. destruct t; apply _. Qed.

Lemma is_oterm_null l t : is_oterm l t -∗ ⌜l = null ↔ t = None⌝.
Proof.
  destruct t as [t'|]; simpl; last by iIntros "%"; iPureIntro; naive_solver.
  iIntros "H". iDestruct (is_term_not_null with "H") as %?.
  iPureIntro. naive_solver.
Qed.

Definition term_code (t : term) : w64 :=
  match t with
  | TVar _ => W64 1 | TPat _ => W64 2 | TResult => W64 3 | TInt _ => W64 4
  | TBool _ => W64 5 | TUnit => W64 6 | TNull => W64 7
  | TPlus _ _ => W64 8 | TMinus _ _ => W64 9 | TMul _ _ => W64 10
  | TNeg _ => W64 11 | TEq _ _ => W64 12
  | TLt sg _ _ => if sg then W64 13 else W64 14
  | TLe sg _ _ => if sg then W64 15 else W64 16
  | TNot _ => W64 17 | TIte _ _ _ => W64 18 | TExec => W64 19 | TRet _ => W64 20
  end.

Definition term_num (t : term) : w64 :=
  match t with
  | TVar n | TPat n => W64 n
  | TInt w => w
  | TBool b => bool_code b
  | _ => W64 0
  end.

Definition term_a (t : term) : option term :=
  match t with
  | TPlus x _ | TMinus x _ | TMul x _ | TEq x _ | TLt _ x _ | TLe _ x _
  | TNeg x | TNot x | TRet x | TIte x _ _ => Some x
  | _ => None
  end.

Definition term_b (t : term) : option term :=
  match t with
  | TPlus _ y | TMinus _ y | TMul _ y | TEq _ y | TLt _ _ y | TLe _ _ y
  | TIte _ y _ => Some y
  | _ => None
  end.

Definition term_c (t : term) : option term :=
  match t with TIte _ _ z => Some z | _ => None end.

(** The side condition that makes the [Num] field pin down the index. *)
Definition term_idx_wf (t : term) : Prop :=
  match t with TVar n | TPat n => idx_wf n | _ => True end.

Lemma is_term_node l t :
  is_term l t -∗ ∃ la lb lc : loc,
    ⌜term_idx_wf t⌝ ∗
    l ↦□ tnode (term_code t) (term_num t) la lb lc ∗
    is_oterm la (term_a t) ∗ is_oterm lb (term_b t) ∗ is_oterm lc (term_c t).
Proof.
  iIntros "H". destruct t; simpl.
  - (* TVar *)
    iDestruct "H" as "[%Hw H]"; iExists null, null, null;
    iFrame "H"; iPureIntro; done.
  - (* TPat *)
    iDestruct "H" as "[%Hw H]"; iExists null, null, null;
    iFrame "H"; iPureIntro; done.
  - (* TResult *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TInt *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TBool *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TUnit *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TNull *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TPlus *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TMinus *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TMul *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TNeg *)
    iDestruct "H" as (x) "(H & #H1)"; iExists x, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* TEq *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TLt *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TLe *)
    iDestruct "H" as (x y) "(H & #H1 & #H2)"; iExists x, y, null;
    iFrame "H H1 H2"; iPureIntro; done.
  - (* TNot *)
    iDestruct "H" as (x) "(H & #H1)"; iExists x, null, null;
    iFrame "H H1"; iPureIntro; done.
  - (* TIte *)
    iDestruct "H" as (x y z) "(H & #H1 & #H2 & #H3)"; iExists x, y, z;
    iFrame "H H1 H2 H3"; iPureIntro; done.
  - (* TExec *)
    iExists null, null, null; iFrame "H"; iPureIntro; done.
  - (* TRet *)
    iDestruct "H" as (x) "(H & #H1)"; iExists x, null, null;
    iFrame "H H1"; iPureIntro; done.
Qed.

(** Index equality at the [Num] field. *)
Lemma W64_nat_inj (n m : nat) : idx_wf n → idx_wf m → W64 n = W64 m → n = m.
Proof. rewrite /idx_wf. intros Hn Hm Heq. by rewrite -Hn -Hm Heq. Qed.

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

(** A state's sort table is written only while the state is fresh (the one
    [append] in [EAlloc], on a clone), so it is read-only as part of a state:
    [SortOf], [applyBinOp] and [applyUnOp] all need it persistent. *)
Definition is_vars (s : slice.t) (vars : list sort) : iProp Σ :=
  (s ↦*□ (sort_code <$> vars))%I.

#[global] Instance is_vars_persistent s vars : Persistent (is_vars s vars).
Proof. apply _. Qed.

Definition is_state (l : loc) (st : sstate) : iProp Σ :=
  (∃ hs cs vs : slice.t,
      l ↦ checker.State.mk hs cs vs ∗
      is_heap hs (sheap st) ∗ is_cond cs (spc st) ∗ is_vars vs (svars st))%I.

(** A state straight out of [clone], before it is changed and published: all
    three slices owned together with their capacities, which is what the
    [append]s of [EIf] and [EAlloc] consume. *)
Definition is_state_fresh (l : loc) (st : sstate) : iProp Σ :=
  (∃ hs cs vs : slice.t,
      l ↦ checker.State.mk hs cs vs ∗
      is_heap hs (sheap st) ∗ own_slice_cap checker.Cell.t hs (DfracOwn 1) ∗
      is_cond cs (spc st) ∗ own_slice_cap loc cs (DfracOwn 1) ∗
      vs ↦* (sort_code <$> svars st) ∗ own_slice_cap w64 vs (DfracOwn 1))%I.

Lemma is_state_fresh_publish l st : is_state_fresh l st ==∗ is_state l st.
Proof.
  iIntros "H". iDestruct "H" as (hs cs vs) "(Hl & Hh & _ & Hc & _ & Hv & _)".
  iPersist "Hv". iModIntro. iExists hs, cs, vs. rewrite /is_vars. iFrame "∗#".
Qed.

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
