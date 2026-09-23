(** What a result of [exec] means.

    [exec] returns one [Path] per feasible execution of the expression. The
    list is a *disjunction*: the program ends in some one of them. This file
    says that precisely ([exec_sound]) and proves the structural facts about
    it that every case of the exec proof needs -- above all that soundness is
    closed under concatenating result lists, which is what the loops in
    checker/exec.go build.

    The statement comes in two layers. [exec_sound_at] is about the ambient
    [heapGS Σ], that is, about one particular choice of ghost state; the
    lemmas of the section are proved about it. [exec_sound], at the end,
    quantifies it over every [heapGS Σ] (and every Go semantics satisfying the
    checker's assumptions), and the lemmas are lifted to it under their plain
    names; it is what the specifications of the checker's functions promise.
    The quantification is what lets a [true] answer survive adequacy
    (new/checker/adequacy.v): adequacy runs the checker in ghost state it
    allocates itself, and what it hands back must be a fact about the
    function under analysis in any ghost state. *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import heapLookup heapUpdate.

Section exec_spec.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The environment the checker carries stands for a substitution; [csubst]
    applies it, so the analysed program is [csubst (env_interp V ρ) ce]. *)
Definition exec_sound_at (ce : cexpr) (ρ : list (go_string * term))
                      (sst : sstate) (ps : list spath) : Prop :=
  wf_state sst →
  env_below (length (svars sst)) ρ →
  ∀ V, st_sat V sst →
    ⊢ heap_interp V (sheap sst) -∗
      WP csubst (env_interp V ρ) ce {{ paths_post (length (svars sst)) V ps }}.

(** * Structure

    A result list is a disjunction, so more paths is a weaker claim: this is
    what lets a case of [exec] concatenate the results of its subcases. *)

Lemma exec_sound_at_mono ce ρ sst ps ps' :
  ps ⊆ ps' → exec_sound_at ce ρ sst ps → exec_sound_at ce ρ sst ps'.
Proof.
  intros Hsub Hs Hwf Hρ V Hsat.
  iIntros "Hheap".
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (Hs Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw". by iApply (paths_post_mono with "Hw").
Qed.

(** The loops in checker/exec.go build their answer by appending the results
    of the subcases; each contributes its own paths and the caller's choice
    is the union. *)
Lemma exec_sound_at_app_l ce ρ sst ps ps' :
  exec_sound_at ce ρ sst ps → exec_sound_at ce ρ sst (ps ++ ps').
Proof. apply exec_sound_at_mono. set_solver. Qed.

Lemma exec_sound_at_app_r ce ρ sst ps ps' :
  exec_sound_at ce ρ sst ps' → exec_sound_at ce ρ sst (ps ++ ps').
Proof. apply exec_sound_at_mono. set_solver. Qed.

(** * The value cases

    An expression that neither forks nor touches the heap produces the single
    path [onePath] builds. *)
Lemma exec_sound_at_value ce ρ sst (x : term) :
  (∀ V, csubst (env_interp V ρ) ce = Val (teval V x)) →
  vars_below (length (svars sst)) x →
  exec_sound_at ce ρ sst [mkPath x sst].
Proof.
  intros Hval Hb Hwf Hρ V Hsat. iIntros "Hheap".
  rewrite Hval. iApply wp_value'.
  iExists (mkPath x sst), V. iFrame "Hheap".
  iPureIntro. split_and!; [set_solver|apply agree_below_refl|done|done].
Qed.

(** A term the environment binds is scoped by the state's variables. *)
Lemma env_below_lookup k ρ (gx : go_string) (x : term) :
  env_below k ρ → env_lookup ρ gx = Some x → vars_below k x.
Proof.
  induction ρ as [|[gy y] ρ IH]; first done.
  intros Hb Hlk. simpl in Hlk.
  destruct (decide (gy = gx)) as [->|Hne].
  - assert (y = x) as <- by congruence. apply (Hb (gx, y)). set_solver.
  - apply IH; last done. intros xt Hxt. apply Hb. set_solver.
Qed.

(** The cases of [exec] that neither fork nor touch the heap. *)
Lemma exec_sound_at_int ρ sst w : exec_sound_at (CEInt w) ρ sst [mkPath (TInt w) sst].
Proof. apply exec_sound_at_value; [intros V; simpl; by rewrite ival_eq|done]. Qed.

Lemma exec_sound_at_bool ρ sst b : exec_sound_at (CEBool b) ρ sst [mkPath (TBool b) sst].
Proof. apply exec_sound_at_value; [intros V; simpl; by rewrite bval_eq|done]. Qed.

Lemma exec_sound_at_unit ρ sst : exec_sound_at CEUnit ρ sst [mkPath TUnit sst].
Proof. apply exec_sound_at_value; [intros V; simpl; by rewrite uval_eq|done]. Qed.

Lemma exec_sound_at_var ρ sst (gx : go_string) (x : term) :
  env_lookup ρ gx = Some x →
  vars_below (length (svars sst)) x →
  exec_sound_at (CEVar gx) ρ sst [mkPath x sst].
Proof.
  intros Hlk Hb. apply exec_sound_at_value; last done.
  intros V. simpl. by rewrite env_interp_lookup Hlk.
Qed.

(** [GoZeroVal] does not touch the heap either, but its value depends on the
    type rather than on the environment. *)
Lemma exec_sound_at_zero ρ sst (cty : ctype) :
  exec_sound_at (CEZero cty) ρ sst [mkPath (ctype_zero cty) sst].
Proof.
  intros Hwf Hρ V Hsat. iIntros "Hheap".
  simpl. iApply (wp_ctype_zero cty V).
  iExists (mkPath (ctype_zero cty) sst), V. iFrame "Hheap".
  iPureIntro. split_and!; [set_solver|apply agree_below_refl|done|done].
Qed.

(** * Composing sound result lists

    Every compound case of [exec] runs a subexpression, then continues from
    each of its paths. The valuation may grow (an allocation introduces a
    fresh logical variable), so the continuation's paths are stated over a
    valuation that only agrees with the caller's below the caller's number of
    variables -- which is exactly what [paths_post] records. *)

Lemma paths_post_compose k k' V V' qs v :
  (k ≤ k')%nat → agree_below k V V' →
  paths_post k' V' qs v -∗ paths_post k V qs v.
Proof.
  iIntros (Hle Hag) "H".
  iDestruct "H" as (q V'') "(%Hin & %Hag' & %Hret & %Hsat & Hheap)".
  iExists q, V''. iFrame "Hheap". iPureIntro. split_and!; [done| |done|done].
  eapply agree_below_trans; first done.
  by eapply agree_below_weaken.
Qed.

(** An environment whose terms are all scoped by the caller's variables means
    the same thing under any valuation that agrees that far. *)
Lemma env_interp_agree k V V' ρ :
  agree_below k V V' → env_below k ρ → env_interp V ρ = env_interp V' ρ.
Proof.
  intros Hag Hb. induction ρ as [|[gy y] ρ IH]; first done.
  rewrite !env_interp_bind.
  rewrite (teval_agree k V V' y) //; last by apply (Hb (gy, y)); set_solver.
  rewrite IH //. intros xt Hxt. apply Hb. set_solver.
Qed.

(** * [let]

    [exec] evaluates the bound expression, then continues from each of its
    paths with the name bound to that path's return term. The GooseLang term
    binds the name with a beta step, so the two meet at [csubst_insert]. *)

Lemma wp_beta_rec_expr (gx : string) (B : expr) (v : val) (Ψ : val → iProp Σ) :
  WP subst gx v B {{ Ψ }} -∗ WP App (Rec BAnon (BNamed gx) B) (Val v) {{ Ψ }}.
Proof. iIntros "H". by wp_pures. Qed.

(** The argument of an application is evaluated first, which is the order
    [exec] uses too. *)
Lemma wp_let_bind (gx : string) (B e1 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ w, WP subst gx w B {{ Φ }} }} -∗
  WP App (Rec BAnon (BNamed gx) B) e1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_bind (fill [AppRCtx (Rec BAnon (BNamed gx) B)])).
  iApply (wp_wand_r _ _ _ (λ w, WP subst gx w B {{ Φ }})%I).
  iSplitL "H"; first iExact "H".
  iIntros (w) "Hw". by iApply wp_beta_rec_expr.
Qed.

Lemma exec_sound_at_let (gx : go_string) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound_at ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at ce2 ((gx, pret p) :: ρ) (pst p) qs) →
  exec_sound_at (CELet gx ce1 ce2) ρ sst out.
Proof.
  intros He1 Hwfps Hcont Hwf Hρ V Hsat.
  iIntros "Hheap". simpl.
  iApply wp_let_bind.
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He1 Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as (qs & Hsub & Hqs).
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ((gx, pret p) :: ρ)) as Hbp.
  { apply env_below_cons.
    - by apply (paths_wf_ret _ _ Hwfps).
    - by eapply env_below_mono. }
  rewrite csubst_insert.
  rewrite (env_interp_agree (length (svars sst)) V V') //.
  rewrite Hret -env_interp_bind.
  iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
  iSplitL "Hheap'".
  { by iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
  iIntros (u) "Hu".
  iApply (paths_post_mono _ _ qs out _ Hsub).
  iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
  iExact "Hu".
Qed.

(** * Sequencing

    [ESeq] is [ELet] with an anonymous binder: the continuation runs in the
    caller's environment. *)

Lemma wp_beta_anon_expr (B : expr) (v : val) (Ψ : val → iProp Σ) :
  WP B {{ Ψ }} -∗ WP App (Rec BAnon BAnon B) (Val v) {{ Ψ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_seq_bind (B e1 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ _, WP B {{ Φ }} }} -∗ WP App (Rec BAnon BAnon B) e1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_bind (fill [AppRCtx (Rec BAnon BAnon B)])).
  iApply (wp_wand_r _ _ _ (λ _, WP B {{ Φ }})%I).
  iSplitL "H"; first iExact "H".
  iIntros (w) "Hw". by iApply wp_beta_anon_expr.
Qed.

Lemma exec_sound_at_seq (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound_at ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ exec_sound_at ce2 ρ (pst p) qs) →
  exec_sound_at (CESeq ce1 ce2) ρ sst out.
Proof.
  intros He1 Hwfps Hcont Hwf Hρ V Hsat.
  iIntros "Hheap". simpl.
  iApply wp_seq_bind.
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He1 Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as (qs & Hsub & Hqs).
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ρ) as Hbp
    by (by eapply env_below_mono).
  rewrite (env_interp_agree (length (svars sst)) V V') //.
  iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
  iSplitL "Hheap'".
  { by iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
  iIntros (u) "Hu".
  iApply (paths_post_mono _ _ qs out _ Hsub).
  iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
  iExact "Hu".
Qed.

(** * The exception monad

    [teval] of [TExec]/[TRet] is exactly [execute_val]/[return_val], so these
    cases are pure steps once the subexpression's path is in hand. *)

Lemma exec_sound_at_do (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath TExec (pst p) ∈ out) →
  exec_sound_at (CEDo ce) ρ sst out.
Proof.
  intros He Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val do_execute)])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  iApply (wp_do w). iExists (mkPath TExec (pst p)), V'. iFrame "Hheap'".
  iPureIntro. split_and!; [by apply Hcont|done|done|done].
Qed.

Lemma exec_sound_at_return (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath (TRet (pret p)) (pst p) ∈ out) →
  exec_sound_at (CEReturn ce) ρ sst out.
Proof.
  intros He Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val do_return)])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  iApply (wp_return w). iExists (mkPath (TRet (pret p)) (pst p)), V'.
  iFrame "Hheap'". iPureIntro. split_and!; [by apply Hcont|done| |done].
  by rewrite /= -Hret.
Qed.

(** [exception_do] strips the label: an [execute] becomes [()] and a
    [return v] becomes [v]. The checker case-splits on the *term*, which is
    exactly what [teval] turns into the two monad values. *)
Lemma exec_sound_at_exc_do (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  (∀ p, p ∈ ps →
     (pret p = TExec ∧ mkPath TUnit (pst p) ∈ out) ∨
     (∃ x, pret p = TRet x ∧ mkPath x (pst p) ∈ out)) →
  exec_sound_at (CEExcDo ce) ρ sst out.
Proof.
  intros He Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val exception_do)])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as [[Hex Hout]|(x & Hrx & Hout)].
  - rewrite Hret Hex /=. iApply wp_exc_do_exec.
    iExists (mkPath TUnit (pst p)), V'. iFrame "Hheap'".
    iPureIntro. split_and!; [done|done|done|done].
  - rewrite Hret Hrx /=. iApply (wp_exc_do_ret (teval V' x)).
    iExists (mkPath x (pst p)), V'. iFrame "Hheap'".
    iPureIntro. split_and!; [done|done|done|done].
Qed.

(** * [if]

    The condition is boolean-sorted -- that is what [execIf] checks with
    [SortOf] -- so it really evaluates to a boolean, and the branch taken is
    determined by it. The checker explores both branches, recording the
    condition on one and its negation on the other; a valuation satisfies at
    most one of the two extended path conditions, which is why the two
    branches can be analysed independently. *)

(** The two states [execIf] forks into. *)
Definition st_assume (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst) (spc sst ++ [x]) (svars sst).

Lemma wf_state_assume sst x :
  wf_state sst → vars_below (length (svars sst)) x → wf_state (st_assume sst x).
Proof.
  intros [Hh Hpc] Hx. split; simpl; first done.
  intros y [Hy|Hy]%elem_of_app; first by apply Hpc.
  assert (y = x) as -> by set_solver. done.
Qed.

Lemma st_sat_assume V sst x :
  st_sat V sst → teval V x = bval true → st_sat V (st_assume sst x).
Proof.
  intros [Hv Hpc] Hx. split; simpl; first done.
  by apply pc_sat_snoc.
Qed.

Lemma wp_if_bval (b : bool) (A B : expr) (Ψ : val → iProp Σ) :
  WP (if b then A else B) {{ Ψ }} -∗ WP If (Val (bval b)) A B {{ Ψ }}.
Proof. iIntros "H". rewrite -bval_eq. destruct b; by wp_pures. Qed.

Lemma exec_sound_at_if (cc ct cf : cexpr) ρ sst ps out :
  exec_sound_at cc ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (* the condition is boolean-sorted on every path *)
  (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = Some SBool) →
  (* and each branch is analysed under the corresponding assumption *)
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at ct ρ (st_assume (pst p) (pret p)) qs) →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound_at cf ρ (st_assume (pst p) (negate (pret p))) qs) →
  exec_sound_at (CEIf cc ct cf) ρ sst out.
Proof.
  intros Hc Hwfps Hsort Hthen Helse Hwf Hρ V Hsat.
  iIntros "Hheap". simpl.
  iApply (wp_bind (fill [IfCtx (csubst (env_interp V ρ) ct)
                               (csubst (env_interp V ρ) cf)])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (Hc Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (vars_below (length (svars (pst p))) (pret p)) as Hbret
    by (by apply (paths_wf_ret _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ρ) as Hbp
    by (by eapply env_below_mono).
  (* the condition really is a boolean *)
  assert (has_sort (teval V' (pret p)) SBool) as [b Hb].
  { eapply sort_of_vars_sound; last by apply Hsort.
    by destruct Hsat'. }
  rewrite Hret Hb (env_interp_agree (length (svars sst)) V V') //.
  iApply wp_if_bval. destruct b; simpl.
  - (* the [then] branch, with the condition recorded *)
    destruct (Hthen p Hin) as (qs & Hsub & Hqs).
    iApply (wp_wand_r _ _ _
              (paths_post (length (svars (st_assume (pst p) (pret p)))) V' qs)).
    iSplitL "Hheap'".
    { iApply (Hqs _ _ V' _ with "Hheap'").
      Unshelve.
      - by apply wf_state_assume.
      - exact Hbp.
      - by apply st_sat_assume. }
    iIntros (u) "Hu".
    iApply (paths_post_mono _ _ qs out _ Hsub).
    iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
    iExact "Hu".
  - (* the [else] branch, with the negation recorded *)
    destruct (Helse p Hin) as (qs & Hsub & Hqs).
    iApply (wp_wand_r _ _ _
              (paths_post (length (svars (st_assume (pst p) (negate (pret p))))) V' qs)).
    iSplitL "Hheap'".
    { iApply (Hqs _ _ V' _ with "Hheap'").
      Unshelve.
      - apply wf_state_assume; [done|by apply vars_below_negate].
      - exact Hbp.
      - apply st_sat_assume; first done.
        rewrite (teval_negate V' (pret p) false) //. }
    iIntros (u) "Hu".
    iApply (paths_post_mono _ _ qs out _ Hsub).
    iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
    iExact "Hu".
Qed.

(** * Memory, without a sort constraint on the value

    [steps.v] proves the load/store/alloc lemmas at a value of the type's
    sort, which is the shape the operator cases need. The memory *cases of
    exec* need less: the checker does not check that a stored or allocated
    value has the type's sort, and it does not have to, because the GooseLang
    step for a store does not look at the value at all. These are the
    sort-free versions. *)

#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.
#[local] Hint Extern 1 (go.is_predeclared ?t) => constructor : typeclass_instances.

Lemma wp_ctype_load_any (cty : ctype) (lo : loc) dq (v : val) :
  {{{ heap_pointsto lo dq v }}}
    ![type_of cty] #lo
  {{{ RET v; heap_pointsto lo dq v }}}.
Proof.
  pose proof (go.tagged_steps internal).
  iIntros (Φ) "Hl HΦ". destruct cty; simpl; wp_pures;
    wp_apply (_internal_wp_untyped_read with "Hl"); iIntros "Hl"; by iApply "HΦ".
Qed.

Lemma wp_ctype_store_any (cty : ctype) (lo : loc) (v w : val) :
  {{{ heap_pointsto lo (DfracOwn 1) v }}}
    GoStore (type_of cty) (#lo, w)%V
  {{{ RET #(); heap_pointsto lo (DfracOwn 1) w }}}.
Proof.
  pose proof (go.tagged_steps internal).
  iIntros (Φ) "Hl HΦ". destruct cty; simpl; wp_pures;
    wp_apply (_internal_wp_untyped_store with "Hl"); iIntros "Hl"; by iApply "HΦ".
Qed.

Lemma wp_ctype_alloc_any (cty : ctype) (v : val) :
  {{{ True }}}
    GoAlloc (type_of cty) v
  {{{ (l : loc), RET #l; heap_pointsto l (DfracOwn 1) v }}}.
Proof.
  pose proof (go.tagged_steps internal).
  iIntros (Φ) "_ HΦ". destruct cty; simpl; wp_pures;
    wp_apply wp_alloc_untyped; iIntros (l) "Hl"; by iApply "HΦ".
Qed.

(** * The heap cases

    A symbolic cell is a real points-to, so a successful [heapLookup] hands
    out the points-to the load needs, and a successful [heapUpdate] is the
    frame-preserving update the store performs. *)

Lemma heap_interp_lookup V H (x y : term) :
  heap_lookup H x = Some y →
  heap_interp V H -∗
  ∃ lo : loc, ⌜teval V x = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V y) ∗
              (heap_pointsto lo (DfracOwn 1) (teval V y) -∗ heap_interp V H).
Proof.
  induction H as [|c H IH]; first done.
  simpl. destruct (decide (cloc c = x)) as [Heq|Hne].
  - intros Hy. assert (y = cval c) as -> by congruence.
    iIntros "[Hc HH]". iDestruct "Hc" as (lo) "[%Hl Hp]".
    iExists lo. rewrite Heq in Hl. iFrame "Hp". iSplit; first done.
    iIntros "Hp". iFrame "HH". iExists lo. rewrite Heq. by iFrame "Hp".
  - intros Hlk. iIntros "[Hc HH]".
    iDestruct (IH Hlk with "HH") as (lo) "(%Hl & Hp & Hback)".
    iExists lo. iFrame "Hp". iSplit; first done.
    iIntros "Hp". iFrame "Hc". by iApply "Hback".
Qed.

(** Updating the first matching cell: the rest of the heap is untouched. *)
Lemma heap_interp_update V H H' (x y : term) (lo : loc) :
  heap_update H x y = Some H' →
  teval V x = lval lo →
  heap_interp V H -∗
  ∃ z : term, heap_pointsto lo (DfracOwn 1) (teval V z) ∗
              (heap_pointsto lo (DfracOwn 1) (teval V y) -∗ heap_interp V H').
Proof.
  revert H'. induction H as [|c H IH]; first done.
  intros H'. simpl. destruct (decide (cloc c = x)) as [Heq|Hne].
  - intros Hh Hx. assert (H' = mkCell (cloc c) y :: H) as -> by congruence.
    iIntros "[Hc HH]". iDestruct "Hc" as (lo') "[%Hl Hp]".
    rewrite Heq Hx in Hl.
    assert (lo' = lo) as -> by (symmetry; by apply lval_inj).
    iExists (cval c). iFrame "Hp". iIntros "Hp". iFrame "HH".
    iExists lo. rewrite /= Heq Hx. by iFrame "Hp".
  - destruct (heap_update H x y) as [H''|] eqn:Hup; last done.
    intros Hh Hx. assert (H' = c :: H'') as -> by (simpl in Hh; congruence).
    iIntros "[Hc HH]".
    iDestruct (IH H'' eq_refl Hx with "HH") as (z) "[Hp Hback]".
    iExists z. iFrame "Hp". iIntros "Hp". iFrame "Hc". by iApply "Hback".
Qed.

(** * Load

    [exec] requires a cell whose location term is *syntactically* the
    address, which is what [heapLookup] finds; the value it holds is the
    result. *)
Lemma exec_sound_at_load (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ y, heap_lookup (sheap (pst p)) (pret p) = Some y ∧
                      mkPath y (pst p) ∈ out) →
  exec_sound_at (CELoad cty ce) ρ sst out.
Proof.
  intros He Hwfps Hcell Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoLoad (type_of cty))))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcell p Hin) as (y & Hlk & Hout).
  iDestruct (heap_interp_lookup V' _ _ _ Hlk with "Hheap'")
    as (lo) "(%Hl & Hp & Hback)".
  rewrite Hret Hl -lval_eq.
  iApply (wp_ctype_load_any cty lo (DfracOwn 1) (teval V' y) with "Hp").
  iIntros "!> Hp".
  iExists (mkPath y (pst p)), V'.
  iSplit; first (iPureIntro; exact Hout).
  iSplit; first (iPureIntro; exact Hag).
  iSplit; first done.
  iSplit; first (iPureIntro; exact Hsat').
  by iApply "Hback".
Qed.

(** * Allocation

    [exec] introduces a fresh logical variable for the new location: the
    state's sort table grows by one [SLoc], and the heap by a cell whose
    location term is that variable. The valuation is extended to send the new
    variable to the location GooseLang produced -- which is exactly the
    freedom [paths_post] leaves, since the extension is at an index at or
    above the caller's count. *)

Definition upd_var (V : valuation) (n : nat) (v : val) : valuation :=
  mkVal (λ m, if decide (m = n) then v else vvar V m) (vpat V) (vret V).

Lemma agree_below_upd_var k V n v : (k ≤ n)%nat → agree_below k V (upd_var V n v).
Proof.
  intros Hle. split_and!; [|done|done].
  intros m Hm. simpl. rewrite decide_False //. lia.
Qed.

Lemma upd_var_here V n v : vvar (upd_var V n v) n = v.
Proof. simpl. by rewrite decide_True. Qed.

Lemma teval_upd_var_here V n v : teval (upd_var V n v) (TVar n) = v.
Proof. simpl. by rewrite decide_True. Qed.

Lemma upd_var_other V n m v : m ≠ n → vvar (upd_var V n v) m = vvar V m.
Proof. intros. simpl. by rewrite decide_False. Qed.

(** The state [exec] forks to on an allocation. *)
Definition st_alloc (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst ++ [mkCell (TVar (length (svars sst))) x])
          (spc sst)
          (svars sst ++ [SLoc]).

Lemma wf_state_alloc sst x :
  wf_state sst → vars_below (length (svars sst)) x → wf_state (st_alloc sst x).
Proof.
  intros [Hh Hpc] Hx. split; cbn [st_alloc svars sheap spc]; rewrite length_app /=.
  - intros c Hc. apply elem_of_app in Hc as [Hin1|Hin2].
    + destruct (Hh c Hin1) as [H1 H2]. split.
      * eapply vars_below_mono; last exact H1. lia.
      * eapply vars_below_mono; last exact H2. lia.
    + assert (c = mkCell (TVar (length (svars sst))) x) as Heqc.
      { apply elem_of_cons in Hin2 as [?|Hnil]; [done|set_solver]. }
      rewrite Heqc. split; cbn [cloc cval vars_below]; first lia.
      eapply vars_below_mono; last exact Hx. lia.
  - intros y Hy. eapply vars_below_mono; last by apply Hpc. lia.
Qed.

Lemma st_sat_alloc V sst x (lo : loc) :
  wf_state sst → st_sat V sst →
  st_sat (upd_var V (length (svars sst)) (lval lo)) (st_alloc sst x).
Proof.
  intros Hwf [Hv Hpc]. split; cbn [st_alloc svars spc].
  - intros m sg Hsv.
    destruct (decide (m = length (svars sst))) as [Heqm|Hne].
    + assert (sg = SLoc) as Hsg.
      { rewrite lookup_app_Some in Hsv. destruct Hsv as [Hl|[_ Hr]].
        - exfalso. apply lookup_lt_Some in Hl. lia.
        - assert (m - length (svars sst) = 0)%nat as Hz by lia.
          rewrite Hz /= in Hr. congruence. }
      rewrite Hsg Heqm upd_var_here. by eexists.
    + rewrite upd_var_other //. apply Hv.
      rewrite lookup_app_Some in Hsv. destruct Hsv as [Hl|[Hge Hr]]; first done.
      exfalso. apply lookup_lt_Some in Hr. simpl in Hr.
      apply Hne. lia.
  - eapply pc_sat_agree; [by apply agree_below_upd_var| |done].
    by apply (wf_pc _ Hwf).
Qed.

Lemma exec_sound_at_alloc (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps →
     mkPath (TVar (length (svars (pst p)))) (st_alloc (pst p) (pret p)) ∈ out) →
  exec_sound_at (CEAlloc cty ce) ρ sst out.
Proof.
  intros He Hwfps Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoAlloc (type_of cty))))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (vars_below (length (svars (pst p))) (pret p)) as Hbret
    by (by apply (paths_wf_ret _ _ Hwfps)).
  iApply (wp_ctype_alloc_any cty w with "[//]").
  iIntros "!>" (lo) "Hp".
  assert (agree_below (length (svars (pst p))) V'
            (upd_var V' (length (svars (pst p))) (lval lo))) as Hag2
    by (by apply agree_below_upd_var).
  iExists (mkPath (TVar (length (svars (pst p)))) (st_alloc (pst p) (pret p))),
          (upd_var V' (length (svars (pst p))) (lval lo)).
  iSplit; first (iPureIntro; by apply Hcont).
  iSplit.
  { iPureIntro. eapply agree_below_trans; first exact Hag.
    by eapply agree_below_weaken. }
  iSplit.
  { iPureIntro. rewrite lval_eq. by rewrite teval_upd_var_here. }
  iSplit; first (iPureIntro; by apply st_sat_alloc).
  (* the new cell, and the old heap under the extended valuation *)
  cbn [st_alloc sheap]. rewrite heap_interp_app.
  iSplitL "Hheap'".
  { rewrite -(heap_interp_agree (length (svars (pst p))) V'
                (upd_var V' (length (svars (pst p))) (lval lo))) //.
    by apply (wf_heap _ Hwfp). }
  rewrite /heap_interp big_sepL_singleton.
  iExists lo. cbn [cloc cval].
  rewrite teval_upd_var_here. iSplit; first done.
  rewrite -(teval_agree (length (svars (pst p))) V'
              (upd_var V' (length (svars (pst p))) (lval lo)) (pret p)) //.
  rewrite -Hret. iExact "Hp".
Qed.

End exec_spec.

(** * The ghost-state-independent layer *)
Section exec_uniform.
Context {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
        {ffi_sem : ffi_semantics ext ffi}.

Definition exec_sound (ce : cexpr) (ρ : list (go_string * term))
                      (sst : sstate) (ps : list spath) : Prop :=
  ∀ Σ (hG : heapGS Σ) (sem : go.Semantics) (package_sem : checker.Assumptions),
    exec_sound_at ce ρ sst ps.

End exec_uniform.

(** Lifting a lemma about [exec_sound_at]: fix the ghost state, apply it, and
    specialise the (positively occurring) [exec_sound] premises. *)
Tactic Notation "exec_lift" uconstr(L) :=
  rewrite /exec_sound; intros;
  let Σ := fresh "Σ" in let hG := fresh "hG" in
  let sem := fresh "sem" in let psem := fresh "package_sem" in
  intros Σ hG sem psem; eapply L; eauto; naive_solver.

Section exec_uniform_lemmas.
Context {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
        {ffi_sem : ffi_semantics ext ffi}.

Lemma exec_sound_mono ce ρ sst ps ps' :
  ps ⊆ ps' → exec_sound ce ρ sst ps → exec_sound ce ρ sst ps'.
Proof. exec_lift exec_sound_at_mono. Qed.

Lemma exec_sound_app_l ce ρ sst ps ps' :
  exec_sound ce ρ sst ps → exec_sound ce ρ sst (ps ++ ps').
Proof. exec_lift exec_sound_at_app_l. Qed.

Lemma exec_sound_app_r ce ρ sst ps ps' :
  exec_sound ce ρ sst ps' → exec_sound ce ρ sst (ps ++ ps').
Proof. exec_lift exec_sound_at_app_r. Qed.

Lemma exec_sound_int ρ sst w : exec_sound (CEInt w) ρ sst [mkPath (TInt w) sst].
Proof. exec_lift exec_sound_at_int. Qed.

Lemma exec_sound_bool ρ sst b : exec_sound (CEBool b) ρ sst [mkPath (TBool b) sst].
Proof. exec_lift exec_sound_at_bool. Qed.

Lemma exec_sound_unit ρ sst : exec_sound CEUnit ρ sst [mkPath TUnit sst].
Proof. exec_lift exec_sound_at_unit. Qed.

Lemma exec_sound_var ρ sst (gx : go_string) (x : term) :
  env_lookup ρ gx = Some x →
  vars_below (length (svars sst)) x →
  exec_sound (CEVar gx) ρ sst [mkPath x sst].
Proof. exec_lift exec_sound_at_var. Qed.

Lemma exec_sound_zero ρ sst (cty : ctype) :
  exec_sound (CEZero cty) ρ sst [mkPath (ctype_zero cty) sst].
Proof. exec_lift exec_sound_at_zero. Qed.

Lemma exec_sound_let (gx : go_string) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ce2 ((gx, pret p) :: ρ) (pst p) qs) →
  exec_sound (CELet gx ce1 ce2) ρ sst out.
Proof. exec_lift exec_sound_at_let. Qed.

Lemma exec_sound_seq (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ exec_sound ce2 ρ (pst p) qs) →
  exec_sound (CESeq ce1 ce2) ρ sst out.
Proof. exec_lift exec_sound_at_seq. Qed.

Lemma exec_sound_do (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath TExec (pst p) ∈ out) →
  exec_sound (CEDo ce) ρ sst out.
Proof. exec_lift exec_sound_at_do. Qed.

Lemma exec_sound_return (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath (TRet (pret p)) (pst p) ∈ out) →
  exec_sound (CEReturn ce) ρ sst out.
Proof. exec_lift exec_sound_at_return. Qed.

Lemma exec_sound_exc_do (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps →
     (pret p = TExec ∧ mkPath TUnit (pst p) ∈ out) ∨
     (∃ x, pret p = TRet x ∧ mkPath x (pst p) ∈ out)) →
  exec_sound (CEExcDo ce) ρ sst out.
Proof. exec_lift exec_sound_at_exc_do. Qed.

Lemma exec_sound_if (cc ct cf : cexpr) ρ sst ps out :
  exec_sound cc ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = Some SBool) →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ct ρ (st_assume (pst p) (pret p)) qs) →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound cf ρ (st_assume (pst p) (negate (pret p))) qs) →
  exec_sound (CEIf cc ct cf) ρ sst out.
Proof. exec_lift exec_sound_at_if. Qed.

Lemma exec_sound_load (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ y, heap_lookup (sheap (pst p)) (pret p) = Some y ∧
                      mkPath y (pst p) ∈ out) →
  exec_sound (CELoad cty ce) ρ sst out.
Proof. exec_lift exec_sound_at_load. Qed.

Lemma exec_sound_alloc (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps →
     mkPath (TVar (length (svars (pst p)))) (st_alloc (pst p) (pret p)) ∈ out) →
  exec_sound (CEAlloc cty ce) ρ sst out.
Proof. exec_lift exec_sound_at_alloc. Qed.

End exec_uniform_lemmas.
