(** What a result of [exec] means.

    [exec] returns one [Path] per feasible execution of the expression. The
    list is a *disjunction*: the program ends in some one of them. This file
    says that precisely ([exec_sound]) and proves the structural facts about
    it that every case of the exec proof needs -- above all that soundness is
    closed under concatenating result lists, which is what the loops in
    checker/exec.go build. *)
From New.checker Require Import prelude nodes.

Section exec_spec.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The environment the checker carries stands for a substitution; [csubst]
    applies it, so the analysed program is [csubst (env_interp V ρ) ce]. *)
Definition exec_sound (ce : cexpr) (ρ : list (go_string * term))
                      (sst : sstate) (ps : list spath) : Prop :=
  wf_state sst →
  env_below (length (svars sst)) ρ →
  ∀ V, st_sat V sst →
    ⊢ heap_interp V (sheap sst) -∗
      WP csubst (env_interp V ρ) ce {{ paths_post (length (svars sst)) V ps }}.

(** * Structure

    A result list is a disjunction, so more paths is a weaker claim: this is
    what lets a case of [exec] concatenate the results of its subcases. *)

Lemma exec_sound_mono ce ρ sst ps ps' :
  ps ⊆ ps' → exec_sound ce ρ sst ps → exec_sound ce ρ sst ps'.
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
Lemma exec_sound_app_l ce ρ sst ps ps' :
  exec_sound ce ρ sst ps → exec_sound ce ρ sst (ps ++ ps').
Proof. apply exec_sound_mono. set_solver. Qed.

Lemma exec_sound_app_r ce ρ sst ps ps' :
  exec_sound ce ρ sst ps' → exec_sound ce ρ sst (ps ++ ps').
Proof. apply exec_sound_mono. set_solver. Qed.

(** * The value cases

    An expression that neither forks nor touches the heap produces the single
    path [onePath] builds. *)
Lemma exec_sound_value ce ρ sst (x : term) :
  (∀ V, csubst (env_interp V ρ) ce = Val (teval V x)) →
  vars_below (length (svars sst)) x →
  exec_sound ce ρ sst [mkPath x sst].
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
Lemma exec_sound_int ρ sst w : exec_sound (CEInt w) ρ sst [mkPath (TInt w) sst].
Proof. apply exec_sound_value; [intros V; simpl; by rewrite ival_eq|done]. Qed.

Lemma exec_sound_bool ρ sst b : exec_sound (CEBool b) ρ sst [mkPath (TBool b) sst].
Proof. apply exec_sound_value; [intros V; simpl; by rewrite bval_eq|done]. Qed.

Lemma exec_sound_unit ρ sst : exec_sound CEUnit ρ sst [mkPath TUnit sst].
Proof. apply exec_sound_value; [intros V; simpl; by rewrite uval_eq|done]. Qed.

Lemma exec_sound_var ρ sst (gx : go_string) (x : term) :
  env_lookup ρ gx = Some x →
  vars_below (length (svars sst)) x →
  exec_sound (CEVar gx) ρ sst [mkPath x sst].
Proof.
  intros Hlk Hb. apply exec_sound_value; last done.
  intros V. simpl. by rewrite env_interp_lookup Hlk.
Qed.

(** [GoZeroVal] does not touch the heap either, but its value depends on the
    type rather than on the environment. *)
Lemma exec_sound_zero ρ sst (cty : ctype) :
  exec_sound (CEZero cty) ρ sst [mkPath (ctype_zero cty) sst].
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

Lemma exec_sound_let (gx : go_string) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ce2 ((gx, pret p) :: ρ) (pst p) qs) →
  exec_sound (CELet gx ce1 ce2) ρ sst out.
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

Lemma exec_sound_seq (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ exec_sound ce2 ρ (pst p) qs) →
  exec_sound (CESeq ce1 ce2) ρ sst out.
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

Lemma exec_sound_do (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath TExec (pst p) ∈ out) →
  exec_sound (CEDo ce) ρ sst out.
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

Lemma exec_sound_return (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps → mkPath (TRet (pret p)) (pst p) ∈ out) →
  exec_sound (CEReturn ce) ρ sst out.
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
Lemma exec_sound_exc_do (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps →
     (pret p = TExec ∧ mkPath TUnit (pst p) ∈ out) ∨
     (∃ x, pret p = TRet x ∧ mkPath x (pst p) ∈ out)) →
  exec_sound (CEExcDo ce) ρ sst out.
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

Lemma exec_sound_if (cc ct cf : cexpr) ρ sst ps out :
  exec_sound cc ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (* the condition is boolean-sorted on every path *)
  (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = Some SBool) →
  (* and each branch is analysed under the corresponding assumption *)
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound ct ρ (st_assume (pst p) (pret p)) qs) →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧
        exec_sound cf ρ (st_assume (pst p) (negate (pret p))) qs) →
  exec_sound (CEIf cc ct cf) ρ sst out.
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

End exec_spec.
