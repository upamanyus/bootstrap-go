(** * Tactics for proving a table's rules valid

    A rule's validity, [rule_valid D r], computes to the Hoare triple it
    stands for, in the form [{{{ P }}} e {{{ x .. y, RET v; Q }}}] unfolds
    to.  [tc_simp] performs exactly that computation and nothing else: it
    unfolds the checker's denotation (this library) but not the Gallina the
    table's denotation maps symbols to, so the goal ends up stated in the
    vocabulary of the lemma the rule is linked to.  A generated table file
    defines [<table>_unfold], which unfolds its own definitions first.

    [rule_start] then introduces the ambient setting, the package
    assumptions and the rule's variables. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.tcheck Require Export observe.

Ltac tc_simp :=
  lazy beta iota zeta delta [rule_valid fact_valid preds_valid spec_valid every_ambient
       forall_sorts bi_forall_sorts triple_at val_den type_den as_val teval vals_of sym_apply
       cast nat_cast atom_den assn_den pat_den lookup_sym lookup_pred sd_args sd_res pd_args
       pd_pers d_at d_pkg d_sort d_sym d_pred List.map List.nth_error app pers_obl pers_ok
       srt_den arrows sym_ty pred_ty r_vars r_lhs r_pre r_ex r_ret r_post f_vars f_lhs f_rhs
       projT1 projT2 sp_vars sp_args sp_pre sp_ex sp_ret sp_post apply_vals foldl
       spec_rule call_pat tail].

(** Introduce everything up to the triple; [unf] unfolds the table. *)
Ltac rule_start unf :=
  unf; tc_simp;
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem;
  intros.

(** A pure step, by [wp_pures]. *)
Ltac rule_pure :=
  iIntros "_ HΦ"; wp_pures; by iApply "HΦ".

(** The persistence obligations, by instance search. *)
Ltac preds_persistent :=
  repeat match goal with
         | |- _ ∧ _ => split
         | |- True => exact I
         | |- ∀ _, _ => intros
         | |- _ => apply _
         end.

(** [Forall P l], each element by [tac]. *)
Ltac forall_by tac :=
  lazymatch goal with
  | |- Forall ?P ?l =>
      let l' := eval hnf in l in
      lazymatch l' with
      | [] => apply Forall_nil_2
      | _ :: _ => change (Forall P l'); apply Forall_cons_2; [tac | forall_by tac]
      end
  end.

(** [table_valid D rs fs], given the persistence obligations [pers]: every
    rule and fact by [tac] (typically [auto with] the hint database of the
    table's link, which also sees the context, e.g. the rules for
    callees). *)
Ltac table_valid_by pers tac :=
  split; [forall_by tac | split; [forall_by tac | exact pers]].

(** * Specifications as rules

    [spec_rule_valid]: the observed specification of a function (about
    [func_val f] applied to its arguments) gives the rule callers use (about
    the call [h a1 .. an], [h] the method value).  Proved once, with the
    function's body abstract: the only per-function obligation is that [h]
    is the method value and that the method unfolds to [func_val f]. *)

Section call.
Context `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics}.

Lemma apply_vals_fill (args : list val) (e : expr) :
  foldl (λ e v, App e (Val v)) e args = fill (List.map AppLCtx args) e.
Proof. revert e; induction args as [|v args IH]; intros e; [done|]. simpl. by rewrite IH. Qed.

Lemma wp_method_call_vals (T : go.type) (m : go_string) (impl : val) `{!MethodUnfold T m impl}
    (recv a : val) (rest : list val) Φ :
  WP apply_vals impl (recv :: a :: rest) {{ Φ }} ⊢
  WP apply_vals #(methods T m recv) (a :: rest) {{ Φ }}.
Proof.
  iIntros "H". rewrite /apply_vals /=. rewrite !apply_vals_fill.
  rewrite method_unfold.
  apply (tac_wp_rec_no_later (List.map AppLCtx rest) (λ: "arg1", impl recv "arg1")%V a
           (f:=BAnon) (x:=BNamed "arg1") (e:=(impl recv "arg1")%E)).
  iIntros "_". simpl. iExact "H".
Qed.
End call.

Lemma pat_den_call_pat `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics} {syms preds}
    (DA : den_at (Σ:=Σ) syms preds) θ (p0 : tpat) (args : list tterm) :
  pat_den DA θ (foldl (λ p a, PApp p (PVal a)) p0 args) =
  foldl (λ e v, App e (Val v)) (pat_den DA θ p0) (List.map (val_den DA θ) args).
Proof. revert p0; induction args as [|a args IH]; intros p0; [done|]. simpl. by rewrite IH. Qed.

Lemma forall_sorts_mono2 `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics} {syms preds}
    (DA : den_at (Σ:=Σ) syms preds) ss (P R Q : list (dyn DA) → Prop) :
  (∀ θ, P θ → R θ → Q θ) → forall_sorts DA ss P → forall_sorts DA ss R → forall_sorts DA ss Q.
Proof.
  revert P R Q; induction ss as [|s ss IH]; intros P R Q HPQ; simpl; [by apply HPQ|].
  intros HP HR x. eapply (IH (λ θ, P (existT s x :: θ)) (λ θ, R (existT s x :: θ))); eauto.
Qed.

(** The per-function obligation of [spec_rule_valid]: at every valuation,
    the arguments are a receiver and at least one more value, [h] is the
    method value of the receiver, and the method unfolds to the checked
    function. *)
Definition call_ok {syms preds} (D : den syms preds) (f : cfunc) (sp : tspec) (h : tterm) : Prop :=
  every_ambient D (λ ext ffi ffi_interp0 Σ hG ffi_semantics0 sem DA,
    forall_sorts DA sp.(sp_vars) (λ θ,
      ∃ (T : go.type) (m : go_string) (recv a : val) (rest : list val),
        List.map (val_den DA θ) sp.(sp_args) = recv :: a :: rest ∧
        val_den DA θ h = #(methods T m recv) ∧ MethodUnfold T m (func_val DA f))).

Lemma spec_rule_valid {syms preds} (D : den syms preds) (f : cfunc) (sp : tspec) (h : tterm) :
  spec_valid D f sp → call_ok D f sp h → rule_valid D (spec_rule h sp).
Proof.
  intros Hspec Hcall ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg.
  specialize (Hspec ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg).
  specialize (Hcall ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg).
  cbn beta in Hspec, Hcall |- *. unfold spec_rule; cbn [r_vars r_lhs r_pre r_ex r_ret r_post].
  revert Hspec Hcall. apply forall_sorts_mono2.
  intros θ Htr (T & m & recv & a & rest & Hargs & Hh & Hunf).
  unfold triple_at in *. intros Φ. iIntros "Hpre Hpost".
  rewrite /call_pat pat_den_call_pat /=. rewrite Hh.
  destruct (sp_args sp) as [|a0 args]; first (simpl in Hargs; discriminate). simpl in Hargs |- *.
  injection Hargs as Hrecv Hargs. rewrite Hargs.
  iApply (wp_method_call_vals T m (func_val _ f) recv a rest).
  rewrite -Hrecv -Hargs. iApply (Htr with "Hpre Hpost").
Qed.


(** [call_ok D f sp h], given [Hfv : func_val (D.(d_at) ..) f = impl] for
    a method whose [MethodUnfold] instance needs the package assumptions
    [A]: rewrite the function before anything is computed (so that the
    table's denotation is never normalized inside it), compute, and find
    the instance. *)
Ltac call_ok_by Hfv unf A :=
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg; change A in pkg; cbv beta;
  rewrite Hfv; unf; tc_simp; intros;
  do 5 eexists; split; [reflexivity | split; [reflexivity | apply _]].
