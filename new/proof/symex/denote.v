(** The meaning of the reflected syntax of syntax.v: symbolic values denote
    GooseLang values, [sexpr]s denote GooseLang expressions, symbolic heaps
    denote separating conjunctions of typed points-to facts, and a list of
    paths denotes the *residual goal* the soundness theorem leaves.

    Location atoms are looked up with [nth_error], so the denotation of a
    value that mentions a location is an [option]. That is what makes
    extending the environment with fresh locations harmless without any
    scoping invariant: a lookup that succeeded still succeeds, with the same
    answer, in the extended environment ([vden_ext], [eden_ext], ...). *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof.symex Require Export syntax.

Set Default Proof Using "Type".

(** * Environments *)

Record senv := mkEnv {
  e_ws : list w64;
  e_bs : list bool;
  e_ls : list loc;
}.

Definition env_ext (ρ : senv) (fr : list loc) : senv :=
  mkEnv (e_ws ρ) (e_bs ρ) (e_ls ρ ++ fr).

Lemma env_ext_nil ρ : env_ext ρ [] = ρ.
Proof. destruct ρ. by rewrite /env_ext /= app_nil_r. Qed.

Lemma env_ext_app ρ fr1 fr2 : env_ext (env_ext ρ fr1) fr2 = env_ext ρ (fr1 ++ fr2).
Proof. destruct ρ. by rewrite /env_ext /= app_assoc. Qed.

Lemma nth_error_ext {A} (l fr : list A) n x :
  nth_error l n = Some x → nth_error (l ++ fr) n = Some x.
Proof.
  revert n. induction l as [|y l IH]; intros [|n]; simpl; try done. apply IH.
Qed.

(** * Terms *)

Definition cmp_lt (signed : bool) (x y : w64) : Prop :=
  if signed then sint.Z x < sint.Z y else uint.Z x < uint.Z y.
Definition cmp_le (signed : bool) (x y : w64) : Prop :=
  if signed then sint.Z x ≤ sint.Z y else uint.Z x ≤ uint.Z y.

#[global] Instance cmp_lt_dec sg x y : Decision (cmp_lt sg x y).
Proof. destruct sg; rewrite /cmp_lt; apply _. Defined.
#[global] Instance cmp_le_dec sg x y : Decision (cmp_le sg x y).
Proof. destruct sg; rewrite /cmp_le; apply _. Defined.

Fixpoint weval (ρ : senv) (t : wterm) : w64 :=
  match t with
  | WAtom n => nth n (e_ws ρ) (W64 0)
  | WZero => W64 0
  | WAdd a b => word.add (weval ρ a) (weval ρ b)
  | WSub a b => word.sub (weval ρ a) (weval ρ b)
  | WMul a b => word.mul (weval ρ a) (weval ρ b)
  | WNeg a => word.opp (weval ρ a)
  end.

Definition leval (ρ : senv) (t : lterm) : option loc :=
  match t with
  | LAtom n => nth_error (e_ls ρ) n
  | LNull => Some null
  end.

Fixpoint beval (ρ : senv) (t : bterm) : option bool :=
  match t with
  | BAtom n => Some (nth n (e_bs ρ) false)
  | BLit b => Some b
  | BNot a => match beval ρ a with Some b => Some (negb b) | None => None end
  | BEqW a b => Some (bool_decide (weval ρ a = weval ρ b))
  | BEqB a b =>
      match beval ρ a, beval ρ b with
      | Some x, Some y => Some (bool_decide (x = y))
      | _, _ => None
      end
  | BLt sg a b => Some (bool_decide (cmp_lt sg (weval ρ a) (weval ρ b)))
  | BLe sg a b => Some (bool_decide (cmp_le sg (weval ρ a) (weval ρ b)))
  end.

(** [bprop pos ρ t] says that [t] evaluates to [pos], as the proposition a
    person would write: [bprop true] of [a <u b] is [uint.Z a < uint.Z b] and
    [bprop false] of it is [uint.Z b ≤ uint.Z a]. This is what the residual
    goals show for a path condition. *)
Fixpoint bprop (pos : bool) (ρ : senv) (t : bterm) : Prop :=
  match t with
  | BAtom n => nth n (e_bs ρ) false = pos
  | BLit b => b = pos
  | BNot a => if pos then bprop false ρ a else bprop true ρ a
  | BEqW a b => if pos then weval ρ a = weval ρ b else weval ρ a ≠ weval ρ b
  | BEqB a b =>
      match beval ρ a, beval ρ b with
      | Some x, Some y => if pos then x = y else x ≠ y
      | _, _ => False
      end
  | BLt sg a b =>
      if pos then cmp_lt sg (weval ρ a) (weval ρ b) else cmp_le sg (weval ρ b) (weval ρ a)
  | BLe sg a b =>
      if pos then cmp_le sg (weval ρ a) (weval ρ b) else cmp_lt sg (weval ρ b) (weval ρ a)
  end.

Lemma cmp_lt_not_le sg x y : ¬ cmp_lt sg x y ↔ cmp_le sg y x.
Proof. destruct sg; rewrite /cmp_lt /cmp_le; lia. Qed.
Lemma cmp_le_not_lt sg x y : ¬ cmp_le sg x y ↔ cmp_lt sg y x.
Proof. destruct sg; rewrite /cmp_lt /cmp_le; lia. Qed.

Lemma bprop_beval pos ρ t : bprop pos ρ t ↔ beval ρ t = Some pos.
Proof.
  revert pos. induction t as [n|b|a IH|a b|a IHa b IHb|sg a b|sg a b]; intros pos; simpl.
  - split; [by intros ->|by intros [= ->]].
  - split; [by intros ->|by intros [= ->]].
  - destruct pos; rewrite IH; destruct (beval ρ a) as [[]|]; naive_solver.
  - destruct pos; case_bool_decide; naive_solver.
  - destruct (beval ρ a) as [x|], (beval ρ b) as [y|]; try done.
    destruct pos; case_bool_decide; naive_solver.
  - destruct pos; case_bool_decide; try naive_solver.
    + split; [intros Hle; exfalso; by apply cmp_lt_not_le in Hle|done].
    + split; [done|intros _; by apply cmp_lt_not_le].
  - destruct pos; case_bool_decide; try naive_solver.
    + split; [intros Hlt; exfalso; by apply cmp_le_not_lt in Hlt|done].
    + split; [done|intros _; by apply cmp_le_not_lt].
Qed.

(** Extending the environment with fresh locations changes nothing that was
    already defined. *)
Lemma weval_ext ρ fr t : weval (env_ext ρ fr) t = weval ρ t.
Proof. induction t; simpl; congruence. Qed.

Lemma leval_ext ρ fr t l : leval ρ t = Some l → leval (env_ext ρ fr) t = Some l.
Proof. destruct t; simpl; [apply nth_error_ext|done]. Qed.

Lemma beval_ext ρ fr t b : beval ρ t = Some b → beval (env_ext ρ fr) t = Some b.
Proof.
  revert b. induction t as [n|b|a IH|a b|a IHa b IHb|sg a b|sg a b]; intros r; simpl;
    rewrite ?weval_ext; try done.
  - destruct (beval ρ a) as [x|]; last done. by rewrite (IH x).
  - destruct (beval ρ a) as [x|], (beval ρ b) as [y|]; try done.
    by rewrite (IHa x) // (IHb y).
Qed.

Lemma bprop_ext pos ρ fr t : bprop pos ρ t → bprop pos (env_ext ρ fr) t.
Proof. rewrite !bprop_beval. apply beval_ext. Qed.

Definition pc_holds (ρ : senv) (pc : list bterm) : Prop := Forall (bprop true ρ) pc.

Lemma pc_holds_ext ρ fr pc : pc_holds ρ pc → pc_holds (env_ext ρ fr) pc.
Proof. induction 1; constructor; auto using bprop_ext. Qed.

(** * Types and operators *)

Fixpoint ty_den (t : sty) : go.type :=
  match t with
  | TyInt => go.int
  | TyInt64 => go.int64
  | TyUint64 => go.uint64
  | TyBool => go.bool
  | TyPtr t => go.PointerType (ty_den t)
  end.

Definition binop_den (op : sbinop) : go_operator :=
  match op with
  | OPlus => GoPlus | OSub => GoSub | OMul => GoMul | OEq => GoEquals
  | OLt => GoLt | OLe => GoLe | OGt => GoGt | OGe => GoGe
  end.

Definition unop_den (op : sunop) : go_unary_operator :=
  match op with ONeg => GoNeg | ONot => GoNot end.

Section denote.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

(** * Values and expressions *)

Fixpoint vden (ρ : senv) (v : sval) : option val :=
  match v with
  | VW t => Some #(weval ρ t)
  | VB t => match beval ρ t with Some b => Some #b | None => None end
  | VL t => match leval ρ t with Some l => Some #l | None => None end
  | VUnit => Some #()
  | VExec => Some execute_val
  | VRet v => match vden ρ v with Some w => Some (return_val w) | None => None end
  end.

Lemma vden_ext ρ fr v w : vden ρ v = Some w → vden (env_ext ρ fr) v = Some w.
Proof.
  revert w. induction v as [t|t|t| | |v IH]; intros w; simpl; try done.
  - by rewrite weval_ext.
  - destruct (beval ρ t) as [b|] eqn:Hb; last done. by rewrite (beval_ext _ _ _ _ Hb).
  - destruct (leval ρ t) as [l|] eqn:Hl; last done. by rewrite (leval_ext _ _ _ _ Hl).
  - destruct (vden ρ v) as [u|]; last done. by rewrite (IH u).
Qed.

Fixpoint eden (ρ : senv) (e : sexpr) : option expr :=
  match e with
  | EVal v => match vden ρ v with Some w => Some (Val w) | None => None end
  | EVar x => Some (Var x)
  | ELet x e1 e2 =>
      match eden ρ e1, eden ρ e2 with
      | Some d1, Some d2 => Some (App (Rec BAnon (BNamed x) d2) d1)
      | _, _ => None
      end
  | EIf c e1 e2 =>
      match eden ρ c, eden ρ e1, eden ρ e2 with
      | Some dc, Some d1, Some d2 => Some (If dc d1 d2)
      | _, _, _ => None
      end
  | EAlloc t e =>
      match eden ρ e with
      | Some d => Some (App (Val (GoInstruction (GoAlloc (ty_den t)))) d)
      | None => None
      end
  | EZero t => Some (App (Val (GoInstruction (GoZeroVal (ty_den t)))) (Val #()))
  | ELoad t e =>
      match eden ρ e with
      | Some d => Some (App (Val (GoInstruction (GoLoad (ty_den t)))) d)
      | None => None
      end
  | EStore t e1 e2 =>
      match eden ρ e1, eden ρ e2 with
      | Some d1, Some d2 => Some (App (Val (GoInstruction (GoStore (ty_den t)))) (Pair d1 d2))
      | _, _ => None
      end
  | EBinOp op t e1 e2 =>
      match eden ρ e1, eden ρ e2 with
      | Some d1, Some d2 =>
          Some (App (Val (GoInstruction (GoOp (binop_den op) (ty_den t)))) (Pair d1 d2))
      | _, _ => None
      end
  | EUnOp op t e =>
      match eden ρ e with
      | Some d => Some (App (Val (GoInstruction (GoUnOp (unop_den op) (ty_den t)))) d)
      | None => None
      end
  | EConvert t1 t2 e =>
      match eden ρ e with
      | Some d => Some (App (Val (GoInstruction (Convert (ty_den t1) (ty_den t2)))) d)
      | None => None
      end
  | EDo e =>
      match eden ρ e with Some d => Some (App (Val do_execute) d) | None => None end
  | EReturn e =>
      match eden ρ e with Some d => Some (App (Val do_return) d) | None => None end
  | EExcSeq e1 e2 =>
      match eden ρ e1, eden ρ e2 with
      | Some d1, Some d2 => Some (App (App (Val exception_seq) (Rec BAnon BAnon d2)) d1)
      | _, _ => None
      end
  | EExcDo e =>
      match eden ρ e with Some d => Some (App (Val exception_do) d) | None => None end
  end.

(** Case analysis on the denotations of the subexpressions, remembering the
    induction hypothesis's conclusion for the ones that are defined. *)
Local Ltac eden_cases :=
  repeat match goal with
         | IH : ∀ d, eden ?ρ ?e = Some d → _ |- context[eden ?ρ ?e] =>
             let H := fresh "H" in
             destruct (eden ρ e) eqn:H; [specialize (IH _ eq_refl)|]
         end.

Lemma eden_ext ρ fr e d : eden ρ e = Some d → eden (env_ext ρ fr) e = Some d.
Proof.
  revert d. induction e; intros d; cbn [eden].
  { destruct (vden ρ v) eqn:Hv; last done. intros [= <-]. by rewrite (vden_ext _ _ _ _ Hv). }
  all: eden_cases; try done; intros [= <-];
    repeat match goal with H : eden (env_ext _ _) _ = Some _ |- _ => rewrite H; clear H end;
    try done.

Qed.

(** Substitution commutes with the denotation. *)
Lemma eden_ssubst ρ x v w e d :
  vden ρ v = Some w → eden ρ e = Some d → eden ρ (ssubst x v e) = Some (subst x w d).
Proof.
  intros Hw. revert d. induction e; intros d; cbn [eden ssubst].
  { (* EVal *) destruct (vden ρ v0); last done. by intros [= <-]. }
  { (* EVar *) intros [= <-]. destruct (String.eqb_spec x x0) as [<-|Hne]; cbn [eden subst].
    - by rewrite Hw decide_True.
    - by rewrite decide_False. }
  { (* ELet: the binder shadows [x] exactly when it is [x] *)
    destruct (String.eqb_spec x x0) as [<-|Hne]; eden_cases; try done; intros [= <-].
    - rewrite IHe1 /=. rewrite decide_False //. naive_solver.
    - rewrite IHe1 IHe2 /=. rewrite decide_True //. split; [done|naive_solver]. }
  all: eden_cases; try done; intros [= <-];
    repeat match goal with
           | H : eden _ (ssubst _ _ _) = Some _ |- _ => rewrite H; clear H
           end; done.
Qed.

(** * Heaps *)

(** The typed points-to fact a symbolic cell stands for. *)
Definition pts (l : loc) (ρ : senv) (v : sval) : iProp Σ :=
  match v with
  | VW t => l ↦ weval ρ t
  | VB t => match beval ρ t with Some b => l ↦ b | None => False end
  | VL t => match leval ρ t with Some l' => l ↦ l' | None => False end
  | _ => False
  end%I.

Definition cell_den (ρ : senv) (c : scell) : iProp Σ :=
  let '(n, v) := c in
  match nth_error (e_ls ρ) n with Some l => pts l ρ v | None => False end%I.

Fixpoint heap_den (ρ : senv) (h : list scell) : iProp Σ :=
  match h with
  | [] => emp
  | c :: h => cell_den ρ c ∗ heap_den ρ h
  end%I.

Lemma heap_den_filter ρ (f : scell → bool) h : heap_den ρ h ⊢ heap_den ρ (List.filter f h).
Proof.
  induction h as [|c h IH]; simpl; first done.
  destruct (f c); simpl; iIntros "[Hc Hh]"; [iFrame "Hc"|]; by iApply IH.
Qed.

Lemma pts_ext l ρ fr v : pts l ρ v ⊢ pts l (env_ext ρ fr) v.
Proof.
  destruct v as [t|t|t| | |]; simpl; try done.
  - by rewrite weval_ext.
  - destruct (beval ρ t) as [b|] eqn:Hb; last by iIntros "[]".
    by rewrite (beval_ext _ _ _ _ Hb).
  - destruct (leval ρ t) as [l'|] eqn:Hl; last by iIntros "[]".
    by rewrite (leval_ext _ _ _ _ Hl).
Qed.

Lemma cell_den_ext ρ fr c : cell_den ρ c ⊢ cell_den (env_ext ρ fr) c.
Proof.
  destruct c as [n v]. rewrite /cell_den.
  destruct (nth_error (e_ls ρ) n) as [l|] eqn:Hl; last by iIntros "[]".
  rewrite /= (nth_error_ext _ _ _ _ Hl). apply pts_ext.
Qed.

Lemma heap_den_ext ρ fr h : heap_den ρ h ⊢ heap_den (env_ext ρ fr) h.
Proof.
  induction h as [|c h IH]; simpl; first done.
  by rewrite cell_den_ext IH.
Qed.

(** * The residual goal

    For each path: for all the locations it allocated, assuming its path
    condition and given its heap, the postcondition holds of its value. The
    three are curried so that the goal reads as an ordinary Iris goal after
    [cbn]. *)
Fixpoint forall_locs (n : nat) (P : list loc → iProp Σ) : iProp Σ :=
  match n with
  | O => P []
  | S n => ∀ l : loc, forall_locs n (λ fr, P (l :: fr))
  end%I.

(** A path condition is a Rocq-level binder, so that one [iIntros "*"]
    introduces it together with the fresh locations. *)
Fixpoint pc_wand (ρ : senv) (pc : list bterm) (Q : iProp Σ) : iProp Σ :=
  match pc with
  | [] => Q
  | b :: pc => ∀ _ : bprop true ρ b, pc_wand ρ pc Q
  end%I.

Fixpoint heap_wand (ρ : senv) (h : list scell) (Q : iProp Σ) : iProp Σ :=
  match h with
  | [] => Q
  | c :: h => cell_den ρ c -∗ heap_wand ρ h Q
  end%I.

Definition vpost (ρ : senv) (v : sval) (Φ : val → iProp Σ) : iProp Σ :=
  match vden ρ v with Some w => Φ w | None => True end%I.

Definition path_goal (ρ0 : senv) (Φ : val → iProp Σ) (p : spath) : iProp Σ :=
  let '(v, s) := p in
  forall_locs (s_nlocs s - length (e_ls ρ0)) (λ fr,
    pc_wand (env_ext ρ0 fr) (s_pc s)
      (heap_wand (env_ext ρ0 fr) (s_heap s) (vpost (env_ext ρ0 fr) v Φ))).

Fixpoint paths_goal (ρ0 : senv) (Φ : val → iProp Σ) (r : list spath) : iProp Σ :=
  match r with
  | [] => True
  | [p] => path_goal ρ0 Φ p
  | p :: r => path_goal ρ0 Φ p ∧ paths_goal ρ0 Φ r
  end%I.

Lemma forall_locs_elim n P fr : length fr = n → forall_locs n P ⊢ P fr.
Proof.
  revert P fr. induction n as [|n IH]; intros P [|l fr]; simpl; try done.
  intros [= Hlen]. iIntros "H". iSpecialize ("H" $! l). by iApply (IH with "H").
Qed.

Lemma pc_wand_elim ρ pc Q : pc_holds ρ pc → pc_wand ρ pc Q ⊢ Q.
Proof.
  induction 1 as [|b pc Hb _ IH]; simpl; first done.
  iIntros "H". iApply IH. iApply ("H" $! Hb).
Qed.

Lemma heap_wand_elim ρ h Q : heap_den ρ h ∗ heap_wand ρ h Q ⊢ Q.
Proof.
  induction h as [|c h IH]; simpl; first by iIntros "[_ $]".
  iIntros "[[Hc Hh] H]". iApply IH. iFrame "Hh". by iApply "H".
Qed.

Lemma paths_goal_elem ρ0 Φ r p : p ∈ r → paths_goal ρ0 Φ r ⊢ path_goal ρ0 Φ p.
Proof.
  induction r as [|q r IH]; first by intros ?%elem_of_nil.
  intros [->|Hin]%elem_of_cons.
  - destruct r; simpl; [done|iIntros "[$ _]"].
  - destruct r as [|q' r]; first by apply elem_of_nil in Hin.
    iIntros "[_ H]". by iApply IH.
Qed.

End denote.
