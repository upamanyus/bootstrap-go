(** The checker's input laid out in a concrete heap.

    [check_adequate] (adequacy.v) starts [checker.Check] in a state whose heap
    contains the input trees. Its precondition is a plain proposition about
    that heap, [inputs_in]: for every struct node that the input's
    representation predicate ([is_func], [is_sorts], [is_assn], ..., defs.v)
    asserts, each field's cell ([struct_field_ref]) holds the field's value,
    and for every slice, each element's cell ([array_index_ref]) holds the
    element. The predicates here mirror those of defs.v one for one, with
    [l ↦□ v] replaced by [node_in h l v], [∗] by [∧] and [⌜P⌝] by [P].

    The cells must be non-null and unlocked ([Free]): a cell that starts out
    locked is not a points-to fact a program can begin with.

    [inputs_in_sound] turns the proposition back into the representation
    predicates, from [heap_ro], a persistent read-only view of the initial
    heap that [heap_ro_init] builds from the cells adequacy hands out. *)
From New.checker Require Import prelude.

(** The heap of a GooseLang state. *)
Notation heap_t := (gmap loc (nonAtomic val)).

Section layout.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext} {sem_fn : GoSemanticsFunctions}.

(** Cell [l] of [h] holds [v], unlocked. *)
Definition heap_cell (h : heap_t) (l : loc) (v : val) : Prop :=
  l ≠ null ∧ h !! l = Some (Free v).

(** The cells a struct node occupies: one per field, holding the field. *)
Class NodeCells (V : Type) := node_cells : loc → V → list (loc * val).

#[global] Instance Type'_cells : NodeCells checker.Type'.t := λ l v,
  [(l.[checker.Type'.t, "Kind"], #v.(checker.Type'.Kind'));
   (l.[checker.Type'.t, "Elem"], #v.(checker.Type'.Elem'))].

#[global] Instance Term_cells : NodeCells checker.Term.t := λ l v,
  [(l.[checker.Term.t, "Kind"], #v.(checker.Term.Kind'));
   (l.[checker.Term.t, "Num"], #v.(checker.Term.Num'));
   (l.[checker.Term.t, "A"], #v.(checker.Term.A'));
   (l.[checker.Term.t, "B"], #v.(checker.Term.B'));
   (l.[checker.Term.t, "C"], #v.(checker.Term.C'))].

#[global] Instance Expr_cells : NodeCells checker.Expr.t := λ l v,
  [(l.[checker.Expr.t, "Kind"], #v.(checker.Expr.Kind'));
   (l.[checker.Expr.t, "Name"], #v.(checker.Expr.Name'));
   (l.[checker.Expr.t, "Num"], #v.(checker.Expr.Num'));
   (l.[checker.Expr.t, "Op"], #v.(checker.Expr.Op'));
   (l.[checker.Expr.t, "Ty"], #v.(checker.Expr.Ty'));
   (l.[checker.Expr.t, "Ty2"], #v.(checker.Expr.Ty2'));
   (l.[checker.Expr.t, "A"], #v.(checker.Expr.A'));
   (l.[checker.Expr.t, "B"], #v.(checker.Expr.B'));
   (l.[checker.Expr.t, "C"], #v.(checker.Expr.C'))].

#[global] Instance Assn_cells : NodeCells checker.Assn.t := λ l v,
  [(l.[checker.Assn.t, "Kind"], #v.(checker.Assn.Kind'));
   (l.[checker.Assn.t, "L"], #v.(checker.Assn.L'));
   (l.[checker.Assn.t, "R"], #v.(checker.Assn.R'));
   (l.[checker.Assn.t, "X"], #v.(checker.Assn.X'));
   (l.[checker.Assn.t, "Y"], #v.(checker.Assn.Y'));
   (l.[checker.Assn.t, "Var"], #v.(checker.Assn.Var'));
   (l.[checker.Assn.t, "Sort"], #v.(checker.Assn.Sort'))].

#[global] Instance Func_cells : NodeCells checker.Func.t := λ l v,
  [(l.[checker.Func.t, "Params"], #v.(checker.Func.Params'));
   (l.[checker.Func.t, "Body"], #v.(checker.Func.Body'))].

(** A struct node [v] at [l]. *)
Definition node_in {V} `{!NodeCells V} (h : heap_t) (l : loc) (v : V) : Prop :=
  l ≠ null ∧ Forall (λ c, heap_cell h c.1 c.2) (node_cells l v).

(** A slice [s] with elements [xs]: nil, or a backing array whose element
    cells hold [xs]. *)
Definition slice_in {V} (h : heap_t) (s : slice.t) (xs : list V) : Prop :=
  (s = slice.nil ∧ xs = []) ∨
  (Z.of_nat (length xs) = sint.Z s.(slice.len) ∧
   sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ∧
   s.(slice.ptr) ≠ null ∧
   ∀ (i : nat) x, xs !! i = Some x →
     heap_cell h (array_index_ref V (Z.of_nat i) s.(slice.ptr)) #x).

Fixpoint type_in (h : heap_t) (l : loc) (t : ctype) : Prop :=
  match t with
  | CTyInt => node_in h l (checker.Type'.mk (W64 1) null)
  | CTyInt64 => node_in h l (checker.Type'.mk (W64 2) null)
  | CTyUint64 => node_in h l (checker.Type'.mk (W64 3) null)
  | CTyBool => node_in h l (checker.Type'.mk (W64 4) null)
  | CTyPtr e => ∃ le, node_in h l (checker.Type'.mk (W64 5) le) ∧ type_in h le e
  end.

Fixpoint term_in (h : heap_t) (l : loc) (t : term) : Prop :=
  match t with
  | TVar n => idx_wf n ∧ node_in h l (tnode (W64 1) (W64 n) null null null)
  | TPat n => idx_wf n ∧ node_in h l (tnode (W64 2) (W64 n) null null null)
  | TResult => node_in h l (tnode (W64 3) (W64 0) null null null)
  | TInt w => node_in h l (tnode (W64 4) w null null null)
  | TBool b => node_in h l (tnode (W64 5) (bool_code b) null null null)
  | TUnit => node_in h l (tnode (W64 6) (W64 0) null null null)
  | TNull => node_in h l (tnode (W64 7) (W64 0) null null null)
  | TPlus a b =>
      ∃ la lb, node_in h l (tnode (W64 8) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TMinus a b =>
      ∃ la lb, node_in h l (tnode (W64 9) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TMul a b =>
      ∃ la lb, node_in h l (tnode (W64 10) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TNeg a => ∃ la, node_in h l (tnode (W64 11) (W64 0) la null null) ∧ term_in h la a
  | TEq a b =>
      ∃ la lb, node_in h l (tnode (W64 12) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TLt sg a b =>
      ∃ la lb, node_in h l (tnode (if sg then W64 13 else W64 14) (W64 0) la lb null) ∧
               term_in h la a ∧ term_in h lb b
  | TLe sg a b =>
      ∃ la lb, node_in h l (tnode (if sg then W64 15 else W64 16) (W64 0) la lb null) ∧
               term_in h la a ∧ term_in h lb b
  | TNot a => ∃ la, node_in h l (tnode (W64 17) (W64 0) la null null) ∧ term_in h la a
  | TIte c a b =>
      ∃ lc la lb, node_in h l (tnode (W64 18) (W64 0) lc la lb) ∧
                  term_in h lc c ∧ term_in h la a ∧ term_in h lb b
  | TExec => node_in h l (tnode (W64 19) (W64 0) null null null)
  | TRet a => ∃ la, node_in h l (tnode (W64 20) (W64 0) la null null) ∧ term_in h la a
  end.

Fixpoint expr_in (h : heap_t) (l : loc) (e : cexpr) : Prop :=
  match e with
  | CEInt w => node_in h l (enode (W64 1) ""%go w (W64 0) null null null null null)
  | CEBool b => node_in h l (enode (W64 2) ""%go (bool_code b) (W64 0) null null null null null)
  | CEUnit => node_in h l (enode0 (W64 3) null null null)
  | CEVar x => node_in h l (enode (W64 4) x (W64 0) (W64 0) null null null null null)
  | CELet x e1 e2 =>
      ∃ la lb, node_in h l (enode (W64 5) x (W64 0) (W64 0) null null la lb null) ∧
               expr_in h la e1 ∧ expr_in h lb e2
  | CESeq e1 e2 =>
      ∃ la lb, node_in h l (enode0 (W64 6) la lb null) ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEIf c e1 e2 =>
      ∃ lc la lb, node_in h l (enode0 (W64 7) lc la lb) ∧
                  expr_in h lc c ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CELoad t e =>
      ∃ lt la, node_in h l (enode (W64 8) ""%go (W64 0) (W64 0) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEStore t e1 e2 =>
      ∃ lt la lb, node_in h l (enode (W64 9) ""%go (W64 0) (W64 0) lt null la lb null) ∧
                  type_in h lt t ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEAlloc t e =>
      ∃ lt la, node_in h l (enode (W64 10) ""%go (W64 0) (W64 0) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEZero t =>
      ∃ lt, node_in h l (enode (W64 11) ""%go (W64 0) (W64 0) lt null null null null) ∧
            type_in h lt t
  | CEBinOp op t e1 e2 =>
      ∃ lt la lb, node_in h l (enode (W64 12) ""%go (W64 0) (op_code op) lt null la lb null) ∧
                  type_in h lt t ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEUnOp op t e =>
      ∃ lt la, node_in h l (enode (W64 13) ""%go (W64 0) (op_code op) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEConvert t1 t2 e =>
      ∃ lt1 lt2 la, node_in h l (enode (W64 14) ""%go (W64 0) (W64 0) lt1 lt2 la null null) ∧
                    type_in h lt1 t1 ∧ type_in h lt2 t2 ∧ expr_in h la e
  | CEDo e => ∃ la, node_in h l (enode0 (W64 15) la null null) ∧ expr_in h la e
  | CEReturn e => ∃ la, node_in h l (enode0 (W64 16) la null null) ∧ expr_in h la e
  | CEExcSeq e1 e2 =>
      ∃ la lb, node_in h l (enode0 (W64 17) la lb null) ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEExcDo e => ∃ la, node_in h l (enode0 (W64 18) la null null) ∧ expr_in h la e
  end.

Fixpoint assn_in (h : heap_t) (l : loc) (a : cassn) : Prop :=
  match a with
  | CAEmp => node_in h l (anode (W64 1) null null null null (W64 0) (W64 0))
  | CASep p q =>
      ∃ lp lq, node_in h l (anode (W64 2) lp lq null null (W64 0) (W64 0)) ∧
               assn_in h lp p ∧ assn_in h lq q
  | CAOr p q =>
      ∃ lp lq, node_in h l (anode (W64 3) lp lq null null (W64 0) (W64 0)) ∧
               assn_in h lp p ∧ assn_in h lq q
  | CAExists n s p =>
      ∃ lp, idx_wf n ∧ node_in h l (anode (W64 4) lp null null null (W64 n) (sort_code s)) ∧
            assn_in h lp p
  | CAPure t => ∃ lx, node_in h l (anode (W64 5) null null lx null (W64 0) (W64 0)) ∧ term_in h lx t
  | CAPointsTo x y =>
      ∃ lx ly, node_in h l (anode (W64 6) null null lx ly (W64 0) (W64 0)) ∧
               term_in h lx x ∧ term_in h ly y
  end.

Definition func_in (h : heap_t) (l : loc) (f : cfunc) : Prop :=
  ∃ (s : slice.t) (lb : loc),
    node_in h l (checker.Func.mk s lb) ∧ slice_in h s f.(fparams) ∧ expr_in h lb f.(fbody).

Definition sorts_in (h : heap_t) (s : slice.t) (vars : list sort) : Prop :=
  slice_in h s (sort_code <$> vars).

(** The whole input of [checker.Check #lf #svars #lpre #lpost]. *)
Definition inputs_in (h : heap_t) (lf : loc) (f : cfunc) (svars : slice.t) (vars : list sort)
    (lpre : loc) (pre : cassn) (lpost : loc) (post : cassn) : Prop :=
  func_in h lf f ∧ sorts_in h svars vars ∧ assn_in h lpre pre ∧ assn_in h lpost post.

End layout.

Section layout_sound.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

(** Every unlocked, non-null cell of [h], read-only. *)
Definition heap_ro (h : heap_t) : iProp Σ :=
  □ ∀ l v, ⌜heap_cell h l v⌝ → heap_pointsto l DfracDiscarded v.

#[global] Instance heap_ro_persistent h : Persistent (heap_ro h).
Proof. apply _. Qed.

(** From the cells of the initial heap, as adequacy hands them out
    ([goose_recv_adequacy_failstop_heap]). *)
Lemma heap_ro_init (h : heap_t) :
  ([∗ map] l ↦ lkv ∈ h, na_heap_pointsto_st (tls lkv.1) l (DfracOwn 1) lkv.2) ==∗ heap_ro h.
Proof.
  iIntros "Hh".
  iAssert (|==> [∗ map] l ↦ lkv ∈ h,
             □ (⌜lkv.1 = Reading 0⌝ → ⌜l ≠ null⌝ → heap_pointsto l DfracDiscarded lkv.2))%I
    with "[Hh]" as ">#Hh".
  { iApply big_sepM_bupd.
    iApply (big_sepM_impl with "Hh"). iIntros "!>" (l [m v] _) "Hc". simpl.
    destruct m as [|[|n]];
      [iModIntro; iIntros "!>" (Hm); by inversion Hm| |
       iModIntro; iIntros "!>" (Hm); by inversion Hm].
    destruct (decide (l = null)) as [->|Hnn].
    { iModIntro. iIntros "!>" (_ ?). done. }
    iMod (heap_pointsto_persist with "[Hc]") as "#Hp".
    { rewrite heap_pointsto_eq /heap_pointsto_def na_heap_pointsto_eq /na_heap_pointsto_def.
      by iFrame. }
    iModIntro. iIntros "!>" (_ _). done. }
  iModIntro. iIntros "!>" (l v [Hnn Hl]).
  iDestruct (big_sepM_lookup with "Hh") as "Hc"; first exact Hl.
  by iApply "Hc".
Qed.

Lemma cell_sound h c w :
  heap_cell h c w → heap_ro h ⊢ heap_pointsto c DfracDiscarded w ∗ ⌜c ≠ null⌝.
Proof. iIntros ([Hnn Hc]) "#H". iSplit; last done. by iApply "H". Qed.

(** A struct node, read from its cells. *)
Class NodeSound (V : Type) `{!NodeCells V} `{!TypedPointsto V} :=
  node_sound : ∀ h l (v : V), node_in h l v → heap_ro h ⊢ l ↦□ v.

Local Ltac node_tac :=
  let Hnn := fresh "Hnn" in let Hc := fresh "Hc" in
  intros ??? [Hnn Hc];
  unfold node_cells, Type'_cells, Term_cells, Expr_cells, Assn_cells, Func_cells in Hc;
  iIntros "#H";
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end;
  simpl in *;
  repeat match goal with
         | Hx : heap_cell _ _ _ |- _ =>
             iDestruct (cell_sound _ _ _ Hx with "H") as "[#? %]"; clear Hx
         end;
  rewrite !typed_pointsto_unseal_eq /= !typed_pointsto_unseal_eq /=;
  iFrame "#%".

#[global] Instance Type'_sound : NodeSound checker.Type'.t.
Proof. node_tac. Qed.
#[global] Instance Term_sound : NodeSound checker.Term.t.
Proof. node_tac. Qed.
#[global] Instance Expr_sound : NodeSound checker.Expr.t.
Proof. node_tac. Qed.
#[global] Instance Assn_sound : NodeSound checker.Assn.t.
Proof. node_tac. Qed.
#[global] Instance Func_sound : NodeSound checker.Func.t.
Proof. node_tac. Qed.

Local Ltac slice_tac :=
  let Hlen := fresh "Hlen" in let Hcap := fresh "Hcap" in
  let Hnn := fresh "Hnn" in let Hc := fresh "Hc" in
  intros h s xs [[-> ->]|(Hlen & Hcap & Hnn & Hc)]; iIntros "#H";
  [iApply own_slice_nil|];
  rewrite own_slice_unseal /own_slice_def !typed_pointsto_unseal_eq /=;
  iRight; iSplit; last done; iSplit; last done; iSplit; first done;
  iApply big_sepL_intro; iIntros "!>" (i x Hi);
  iDestruct (cell_sound with "H") as "[Hp %]"; [by apply Hc|];
  rewrite ?typed_pointsto_unseal_eq /=; by iFrame "∗%".

Lemma slice_in_sound_w64 : ∀ h s (xs : list w64), slice_in h s xs → heap_ro h ⊢ s ↦*□ xs.
Proof. slice_tac. Qed.

Lemma slice_in_sound_string :
  ∀ h s (xs : list go_string), slice_in h s xs → heap_ro h ⊢ s ↦*□ xs.
Proof. slice_tac. Qed.

(** The trees: take the conjuncts apart, read every node and subtree, and
    frame. *)
Local Ltac tree_tac :=
  repeat match goal with
         | H : ∃ _, _ |- _ => destruct H
         | H : _ ∧ _ |- _ => destruct H
         end;
  repeat match goal with
         | Hn : node_in _ _ _ |- _ =>
             iDestruct (node_sound _ _ _ Hn with "H") as "#?"; clear Hn
         | IH : ∀ l, ?P ?h l ?x → _, Hx : ?P ?h ?l0 ?x |- _ =>
             iDestruct (IH l0 Hx with "H") as "#?"; clear Hx
         end;
  iFrame "#%".

Lemma type_in_sound h l t : type_in h l t → heap_ro h ⊢ is_type l t.
Proof. revert l. induction t; intros l Hin; simpl in *; iIntros "#H"; tree_tac. Qed.

Lemma term_in_sound h l t : term_in h l t → heap_ro h ⊢ is_term l t.
Proof. revert l. induction t; intros l Hin; simpl in *; iIntros "#H"; tree_tac. Qed.

Lemma expr_in_sound h l e : expr_in h l e → heap_ro h ⊢ is_expr l e.
Proof.
  pose proof type_in_sound as Hty.
  revert l. induction e; intros l Hin; simpl in *; iIntros "#H";
    repeat match goal with
           | H : ∃ _, _ |- _ => destruct H
           | H : _ ∧ _ |- _ => destruct H
           end;
    repeat match goal with
           | Ht : type_in _ _ _ |- _ => iDestruct (Hty _ _ _ Ht with "H") as "#?"; clear Ht
           end;
    tree_tac.
Qed.

Lemma assn_in_sound h l a : assn_in h l a → heap_ro h ⊢ is_assn l a.
Proof.
  pose proof term_in_sound as Htm.
  revert l. induction a as [|p IHp q IHq|p IHp q IHq|n s p IHp|t|x y];
    intros la Hin; simpl in *; iIntros "#H";
    repeat match goal with
           | H : ∃ _, _ |- _ => destruct H
           | H : _ ∧ _ |- _ => destruct H
           end;
    repeat match goal with
           | Ht : term_in _ _ _ |- _ => iDestruct (Htm _ _ _ Ht with "H") as "#?"; clear Ht
           end;
    tree_tac.
Qed.

Lemma func_in_sound h l f : func_in h l f → heap_ro h ⊢ is_func l f.
Proof.
  intros (s & lb & Hn & Hs & He). iIntros "#H". iExists s, lb.
  iSplit; first by iApply node_sound.
  iSplit; first by iApply slice_in_sound_string.
  by iApply expr_in_sound.
Qed.

Lemma sorts_in_sound h s vars : sorts_in h s vars → heap_ro h ⊢ is_sorts s vars.
Proof. apply slice_in_sound_w64. Qed.

Lemma inputs_in_sound h lf f sv vars lpre pre lpost post :
  inputs_in h lf f sv vars lpre pre lpost post →
  heap_ro h ⊢ is_func lf f ∗ is_sorts sv vars ∗ is_assn lpre pre ∗ is_assn lpost post.
Proof.
  intros (Hf & Hs & Hpre & Hpost). iIntros "#H".
  iSplitL; first by iApply func_in_sound.
  iSplitL; first by iApply sorts_in_sound.
  iSplitL; by iApply assn_in_sound.
Qed.

End layout_sound.
