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

End exec_spec.
