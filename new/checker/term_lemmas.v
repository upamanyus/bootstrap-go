(** Semantics of the checker's symbolic terms.

    Pure Gallina metatheory of [teval], [has_sort] and the sort discipline
    [sortOfEnv] of checker/sorts.go, plus the small term operations the
    symbolic execution performs ([negate]). Nothing here mentions the Go
    program; these are the specification functions the Go specs are stated
    over. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Import defs.

Set Default Proof Using "All".

(** * Decidable equality *)

#[global] Instance sort_eq_dec : EqDecision sort.
Proof. solve_decision. Defined.

#[global] Instance term_eq_dec : EqDecision term.
Proof. solve_decision. Defined.

Section input_syntax.
Context {ext : ffi_syntax}.

#[global] Instance ctype_eq_dec : EqDecision ctype.
Proof. solve_decision. Defined.

#[global] Instance cop_eq_dec : EqDecision cop.
Proof. solve_decision. Defined.

#[global] Instance cexpr_eq_dec : EqDecision cexpr.
Proof. solve_decision. Defined.

#[global] Instance cassn_eq_dec : EqDecision cassn.
Proof. solve_decision. Defined.

End input_syntax.

Section term_semantics.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** * Injectivity of the value constructors *)

Lemma ival_inj w1 w2 : ival w1 = ival w2 → w1 = w2.
Proof. rewrite /ival. by intros [= ->]. Qed.
Lemma bval_inj b1 b2 : bval b1 = bval b2 → b1 = b2.
Proof. rewrite /bval. by intros [= ->]. Qed.
Lemma lval_inj l1 l2 : lval l1 = lval l2 → l1 = l2.
Proof. rewrite /lval. by intros [= ->]. Qed.

(** The four value shapes are pairwise distinct, which is what makes
    [has_sort] at one sort exclude the others. *)
Lemma has_sort_unique v s1 s2 : has_sort v s1 → has_sort v s2 → s1 = s2.
Proof.
  destruct s1, s2; rewrite /has_sort /ival /bval /lval /uval;
    intros H1 H2; try reflexivity;
    repeat match goal with H : ∃ _, _ |- _ => destruct H as [? H] end;
    simplify_eq.
Qed.

(** * The sort environment of checker/sorts.go *)

(** Mirrors [sortEnv]: sorts for the logical variables, for the
    postcondition's pattern variables (with [se_pat_ok] marking the ones a
    binder actually declared), and for [ret]. *)
Record sort_env := mkSortEnv {
  se_vars : list sort;
  se_pats : list sort;
  se_pat_ok : list bool;
  se_ret : sort;
  se_ret_ok : bool;
}.

(** [sortOfEnv] indexes [patOk] after bounds-checking against [pats], so it is
    only well defined when the two have the same length. Every [sortEnv] the
    checker builds satisfies this. *)
Definition sort_env_wf (E : sort_env) : Prop :=
  length (se_pats E) = length (se_pat_ok E).

(** Mirrors [sortOfEnv]. [TExec] and [TRet] have no sort. *)
Fixpoint sort_of (E : sort_env) (t : term) : option sort :=
  match t with
  | TVar n => se_vars E !! n
  | TPat n =>
      match se_pats E !! n, se_pat_ok E !! n with
      | Some s, Some true => Some s
      | _, _ => None
      end
  | TResult => if se_ret_ok E then Some (se_ret E) else None
  | TInt _ => Some SInt
  | TBool _ => Some SBool
  | TUnit => Some SUnit
  | TNull => Some SLoc
  | TPlus a b | TMinus a b | TMul a b =>
      match sort_of E a, sort_of E b with
      | Some SInt, Some SInt => Some SInt
      | _, _ => None
      end
  | TNeg a => match sort_of E a with Some SInt => Some SInt | _ => None end
  | TEq a b =>
      match sort_of E a, sort_of E b with
      | Some sa, Some sb => if decide (sa = sb) then Some SBool else None
      | _, _ => None
      end
  | TLt _ a b | TLe _ a b =>
      match sort_of E a, sort_of E b with
      | Some SInt, Some SInt => Some SBool
      | _, _ => None
      end
  | TNot a => match sort_of E a with Some SBool => Some SBool | _ => None end
  | TIte c a b =>
      match sort_of E c, sort_of E a, sort_of E b with
      | Some SBool, Some sa, Some sb => if decide (sa = sb) then Some sa else None
      | _, _, _ => None
      end
  | TExec => None
  | TRet _ => None
  end.

(** Mirrors [SortOf]: only the logical variables are in scope. *)
Definition vars_env (vars : list sort) : sort_env :=
  mkSortEnv vars [] [] SInt false.
Definition sort_of_vars (vars : list sort) (t : term) : option sort :=
  sort_of (vars_env vars) t.

Lemma vars_env_wf vars : sort_env_wf (vars_env vars).
Proof. done. Qed.

(** A valuation respects a sort environment. *)
Record env_sat (V : valuation) (E : sort_env) : Prop := mkEnvSat {
  env_sat_vars : ∀ n s, se_vars E !! n = Some s → has_sort (vvar V n) s;
  env_sat_pats : ∀ n s, se_pats E !! n = Some s → se_pat_ok E !! n = Some true →
                        has_sort (vpat V n) s;
  env_sat_ret : se_ret_ok E = true → has_sort (vret V) (se_ret E);
}.

(** The key fact: a term the checker assigns a sort to evaluates to a value of
    that sort, so the [if:] condition really is a boolean and the operands of
    a [GoOp] really are machine integers. *)
Lemma sort_of_sound V E t s :
  env_sat V E → sort_of E t = Some s → has_sort (teval V t) s.
Proof.
  intros HE. revert s.
  induction t; simpl; intros s Hs;
    (* leaves *)
    try (by inversion Hs; rewrite /has_sort; eauto).
  - by eapply env_sat_vars.
  - destruct (se_pats E !! n) as [sp|] eqn:Hp; last done.
    destruct (se_pat_ok E !! n) as [[]|] eqn:Hok; try done.
    inversion Hs; subst. by eapply env_sat_pats.
  - destruct (se_ret_ok E) eqn:Hr; last done.
    inversion Hs; subst. by eapply env_sat_ret.
  (* TPlus / TMinus / TMul *)
  - destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [[]|] eqn:H2; try done.
    inversion Hs; subst.
    destruct (IHt1 SInt eq_refl) as [x ->]. destruct (IHt2 SInt eq_refl) as [y ->].
    rewrite /ival /=. by eexists.
  - destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [[]|] eqn:H2; try done.
    inversion Hs; subst.
    destruct (IHt1 SInt eq_refl) as [x ->]. destruct (IHt2 SInt eq_refl) as [y ->].
    rewrite /ival /=. by eexists.
  - destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [[]|] eqn:H2; try done.
    inversion Hs; subst.
    destruct (IHt1 SInt eq_refl) as [x ->]. destruct (IHt2 SInt eq_refl) as [y ->].
    rewrite /ival /=. by eexists.
  - (* TNeg *)
    destruct (sort_of E t) as [[]|] eqn:H1; try done.
    inversion Hs; subst.
    destruct (IHt SInt eq_refl) as [x ->]. rewrite /ival /=. by eexists.
  - (* TEq *)
    destruct (sort_of E t1) as [sa|] eqn:H1; try done;
      destruct (sort_of E t2) as [sb|] eqn:H2; try done.
    destruct (decide (sa = sb)); last done. inversion Hs; subst.
    rewrite /has_sort. by eexists.
  - (* TLt *)
    destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [[]|] eqn:H2; try done.
    inversion Hs; subst.
    destruct (IHt1 SInt eq_refl) as [x ->]. destruct (IHt2 SInt eq_refl) as [y ->].
    rewrite /bval /=. by eexists.
  - (* TLe *)
    destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [[]|] eqn:H2; try done.
    inversion Hs; subst.
    destruct (IHt1 SInt eq_refl) as [x ->]. destruct (IHt2 SInt eq_refl) as [y ->].
    rewrite /bval /=. by eexists.
  - (* TNot *)
    destruct (sort_of E t) as [[]|] eqn:H1; try done.
    inversion Hs; subst.
    destruct (IHt SBool eq_refl) as [x ->]. rewrite /bval /=. by eexists.
  - (* TIte *)
    destruct (sort_of E t1) as [[]|] eqn:H1; try done;
      destruct (sort_of E t2) as [sa|] eqn:H2; try done;
      destruct (sort_of E t3) as [sb|] eqn:H3; try done.
    all: destruct (decide (_ = _)) eqn:Hd; try done.
    all: inversion Hs; subst.
    all: destruct (IHt1 SBool eq_refl) as [c ->].
    all: destruct c; [ by apply IHt2 | by apply IHt3 ].
Qed.

Corollary sort_of_vars_sound V vars t s :
  (∀ n s', vars !! n = Some s' → has_sort (vvar V n) s') →
  sort_of_vars vars t = Some s →
  has_sort (teval V t) s.
Proof.
  intros Hv Hs. eapply sort_of_sound; last done.
  split; simpl; [done| |done]. intros ?? H. by rewrite lookup_nil in H.
Qed.

(** * Variable bounds and agreement

    Symbolic execution only ever extends the valuation at indices at or above
    the current number of logical variables, so terms built earlier keep their
    meaning. *)

Fixpoint vars_below (k : nat) (t : term) : Prop :=
  match t with
  | TVar n => (n < k)%nat
  | TPat _ | TResult | TInt _ | TBool _ | TUnit | TNull | TExec => True
  | TPlus a b | TMinus a b | TMul a b | TEq a b | TLt _ a b | TLe _ a b =>
      vars_below k a ∧ vars_below k b
  | TNeg a | TNot a | TRet a => vars_below k a
  | TIte c a b => vars_below k c ∧ vars_below k a ∧ vars_below k b
  end.

Lemma vars_below_mono k k' t : (k ≤ k')%nat → vars_below k t → vars_below k' t.
Proof. intros Hle. induction t; simpl; naive_solver lia. Qed.

(** Two valuations agreeing on the variables a term mentions give it the same
    value. *)
Definition agree_below (k : nat) (V V' : valuation) : Prop :=
  (∀ n, (n < k)%nat → vvar V n = vvar V' n) ∧ vpat V = vpat V' ∧ vret V = vret V'.

Lemma agree_below_refl k V : agree_below k V V.
Proof. done. Qed.

Lemma agree_below_trans k V1 V2 V3 :
  agree_below k V1 V2 → agree_below k V2 V3 → agree_below k V1 V3.
Proof.
  intros (H1 & ? & ?) (H2 & ? & ?). split_and!; [|congruence..].
  intros n Hn. rewrite H1 //. by apply H2.
Qed.

Lemma agree_below_weaken k k' V V' :
  (k' ≤ k)%nat → agree_below k V V' → agree_below k' V V'.
Proof. intros ? (?&?&?). split_and!; auto with lia. Qed.

Lemma teval_agree k V V' t :
  agree_below k V V' → vars_below k t → teval V t = teval V' t.
Proof.
  intros (Hv & Hp & Hr). induction t; simpl; intros Hb;
    destruct_and?;
    try (by apply Hv); try (by rewrite Hp); try (by rewrite Hr);
    try (by rewrite IHt //);
    try (by rewrite IHt1 // IHt2 //);
    try (by rewrite IHt1 // IHt2 // IHt3 //);
    done.
Qed.

(** Sorting is insensitive to variables beyond the table, so extending the
    table preserves the sort of an already well-scoped term. *)
Lemma sort_of_vars_mono vars vars' t s :
  (∀ n s', vars !! n = Some s' → vars' !! n = Some s') →
  sort_of_vars vars t = Some s → sort_of_vars vars' t = Some s.
Proof.
  intros Hsub. rewrite /sort_of_vars /vars_env /=. revert s.
  induction t; simpl; intros s Hs; try done.
  - by apply Hsub.
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [[]|] eqn:H2; try done.
    by rewrite (IHt1 SInt eq_refl) (IHt2 SInt eq_refl).
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [[]|] eqn:H2; try done.
    by rewrite (IHt1 SInt eq_refl) (IHt2 SInt eq_refl).
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [[]|] eqn:H2; try done.
    by rewrite (IHt1 SInt eq_refl) (IHt2 SInt eq_refl).
  - destruct (sort_of _ t) as [[]|] eqn:H1; try done.
    by rewrite (IHt SInt eq_refl).
  - destruct (sort_of _ t1) as [sa|] eqn:H1; try done;
      destruct (sort_of _ t2) as [sb|] eqn:H2; try done.
    by rewrite (IHt1 sa eq_refl) (IHt2 sb eq_refl).
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [[]|] eqn:H2; try done.
    all: by rewrite (IHt1 SInt eq_refl) (IHt2 SInt eq_refl).
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [[]|] eqn:H2; try done.
    all: by rewrite (IHt1 SInt eq_refl) (IHt2 SInt eq_refl).
  - destruct (sort_of _ t) as [[]|] eqn:H1; try done.
    by rewrite (IHt SBool eq_refl).
  - destruct (sort_of _ t1) as [[]|] eqn:H1; try done;
      destruct (sort_of _ t2) as [sa|] eqn:H2; try done;
      destruct (sort_of _ t3) as [sb|] eqn:H3; try done.
    by rewrite (IHt1 SBool eq_refl) (IHt2 sa eq_refl) (IHt3 sb eq_refl).
Qed.

Corollary sort_of_vars_app vars vars' t s :
  sort_of_vars vars t = Some s → sort_of_vars (vars ++ vars') t = Some s.
Proof.
  apply sort_of_vars_mono. intros n s' Hn. by apply lookup_app_l_Some.
Qed.

(** * [negate] *)

(** Mirrors [negate] in checker/exec.go: the double negation is cancelled so
    that the [else] branch after [if !b] records just [b]. *)
Definition negate (t : term) : term :=
  match t with
  | TNot a => a
  | _ => TNot t
  end.

Lemma teval_negate V t b : teval V t = bval b → teval V (negate t) = bval (negb b).
Proof.
  destruct t; simpl; intros Ht; try (by rewrite Ht);
    cbv [ival bval lval uval exec_v ret_v] in Ht |- *;
    try congruence.
  (* [negate (TNot a) = a]: the checker cancels the double negation *)
  destruct (teval V t) eqn:Ha; try congruence.
  destruct l; try congruence.
  injection Ht as <-. by rewrite negb_involutive.
Qed.

Lemma sort_of_negate E t : sort_of E t = Some SBool → sort_of E (negate t) = Some SBool.
Proof.
  intros Ht. destruct t; simpl in Ht |- *; rewrite ?Ht //.
  by destruct (sort_of E t) as [[]|]; simplify_eq.
Qed.

Lemma vars_below_negate k t : vars_below k t → vars_below k (negate t).
Proof. destruct t; simpl; naive_solver. Qed.

(** * Path conditions *)

Definition pc_sat (V : valuation) (pc : list term) : Prop :=
  ∀ t, t ∈ pc → teval V t = bval true.

Lemma pc_sat_nil V : pc_sat V [].
Proof. intros ? H. by apply elem_of_nil in H. Qed.

Lemma pc_sat_app V pc1 pc2 : pc_sat V pc1 → pc_sat V pc2 → pc_sat V (pc1 ++ pc2).
Proof. intros H1 H2 t [?|?]%elem_of_app; eauto. Qed.

Lemma pc_sat_snoc V pc t :
  pc_sat V pc → teval V t = bval true → pc_sat V (pc ++ [t]).
Proof.
  intros ??. apply pc_sat_app; first done.
  intros t' Ht'. assert (t' = t) as -> by set_solver. done.
Qed.

Lemma pc_sat_weaken V pc1 pc2 : pc1 ⊆ pc2 → pc_sat V pc2 → pc_sat V pc1.
Proof. intros Hsub H t Ht. by apply H, Hsub. Qed.

Definition pc_below (k : nat) (pc : list term) : Prop :=
  ∀ t, t ∈ pc → vars_below k t.

Lemma pc_sat_agree k V V' pc :
  agree_below k V V' → pc_below k pc → pc_sat V pc → pc_sat V' pc.
Proof.
  intros Hag Hb H t Ht. rewrite -(teval_agree k V V') //; auto.
Qed.

End term_semantics.
