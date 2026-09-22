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

End exec_spec.
