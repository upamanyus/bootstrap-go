(** [checker.Check] (checker/check.go): the entry point. [Analyze], and if it
    succeeds, [Verify] of its paths against the postcondition.

    The specification is exactly [check_sound] (soundness.v); the composition
    is [check_triple]: [Analyze]'s WP ends in one of the paths
    ([paths_post]), [Verify] gives that path a disjunct it satisfies
    ([path_sat_dj]), and the disjunct entails the postcondition.

    Naming: the Go locals are [f], [vars], [pre], [post], [fail] and [paths],
    so no Rocq variable in [wp_Check] may be called any of those (see
    NOTES.md); check_sound.v restates it with the names of soundness.v. *)
From New.checker Require Import prelude nodes exec_spec exec_def disjunct
  disjunct_ro verify_def pre_sound.
From New.checker.fn Require Import Analyze Verify.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** TEMPORARY: discharged by fn/exec.v (the dispatcher, by induction on the
    [cexpr]). *)
Context (wp_exec : ∀ e : cexpr, ⊢ exec_like checker.exec e).

(** The matcher, as in fn/Verify.v. TEMPORARY: discharged by
    fn/checkDisjunct.v. *)
Context (wp_checkDisjunct : ∀ (p : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
        (sv : slice.t) (vars : list sort),
    {{{ is_pkg_init checker ∗ is_path p sp ∗ is_disjunct_ro ld dj ∗ is_sorts sv vars }}}
      @! checker.checkDisjunct #p #ld #sv
    {{{ (lf : loc), RET #lf;
        is_path p sp ∗ ⌜lf = null → d_fail dj = false ∧ path_sat_dj vars sp dj⌝ }}}).

(** A function application is never a value, so the [▷] in front of a Hoare
    triple's continuation can be stripped by its first step. *)
Lemma apply_vals_e_not_val (h : expr) (vs : list val) :
  to_val h = None → to_val (apply_vals_e h vs) = None.
Proof.
  revert h. induction vs as [|v vs IH]; intros h Hh; first done.
  change (apply_vals_e h (v :: vs)) with (apply_vals_e (App h (Val v)) vs).
  by apply IH.
Qed.

Lemma arg_vals_not_val (cf : cfunc) θ :
  to_val (apply_vals (func_val cf) (arg_vals cf θ)) = None.
Proof.
  rewrite apply_vals_unfold.
  destruct (arg_vals cf θ) as [|v vs] eqn:Hargs.
  - exfalso. revert Hargs. rewrite /arg_vals.
    destruct (fparams cf) as [|x xs]; first done.
    cbn [length seq fmap list_fmap]. done.
  - change (apply_vals_e (Val (func_val cf)) (v :: vs))
      with (apply_vals_e (App (Val (func_val cf)) (Val v)) vs).
    by apply apply_vals_e_not_val.
Qed.

(** The composition. *)
Lemma check_triple (cf : cfunc) (vs : list sort) (P Q : cassn) (ps : list spath) θ :
  paths_wf (length vs) ps →
  (∀ θ, vars_sat θ vs → ⊢ pre_interp θ P -∗
     WP apply_vals (func_val cf) (arg_vals cf θ)
       {{ paths_post (length vs) (mkVal θ (λ _, uval) uval) ps }}) →
  (∀ sp, sp ∈ ps → ∃ dj, d_fail dj = false ∧ path_sat_dj vs sp dj ∧
                         ∀ V, dj_interp V dj ⊢ assn_interp V Q) →
  vars_sat θ vs →
  {{{ pre_interp θ P }}}
    apply_vals (func_val cf) (arg_vals cf θ)
  {{{ (v : val), RET v; post_interp θ v Q }}}.
Proof.
  intros Hwf Hwp Hver Hθ. iIntros (Φ) "Hpre HΦ".
  iApply (wp_wand_r _ _ _ (λ v, (∀ v, post_interp θ v Q -∗ Φ v) ∗
                               paths_post (length vs) (mkVal θ (λ _, uval) uval) ps v)%I).
  iSplitL.
  { iApply wp_frame_step_l'; first (apply TCEq_eq; exact (arg_vals_not_val cf θ)).
    iFrame "HΦ". iApply (Hwp θ Hθ with "Hpre"). }
  iIntros (v) "[HΦ Hv]".
  iDestruct "Hv" as (p V') "(%Hin & %Hag & %Hret & %Hsat & Hh)".
  destruct (Hver p Hin) as (dj & _ & Hdj & Hent).
  iApply "HΦ". rewrite /post_interp. iApply Hent. subst v.
  iApply (Hdj θ V' with "Hh"); try done.
  - by apply (paths_wf_state _ _ Hwf).
  - by apply (paths_wf_grow _ _ Hwf).
  - by apply (paths_wf_ret _ _ Hwf).
Qed.

Lemma wp_Check (cf : cfunc) (vs : list sort) (P Q : cassn)
    (lf : loc) (sv : slice.t) (lpre lpost : loc) :
  {{{ is_pkg_init checker ∗
      is_func lf cf ∗ is_sorts sv vs ∗ is_assn lpre P ∗ is_assn lpost Q }}}
    @! checker.Check #lf #sv #lpre #lpost
  {{{ (b : bool), RET #b;
      ⌜ b = true →
        ∀ θ : nat → val,
          vars_sat θ vs →
          {{{ pre_interp θ P }}}
            apply_vals (func_val cf) (arg_vals cf θ)
          {{{ (v : val), RET v; post_interp θ v Q }}} ⌝ }}}.
Proof.
  wp_start as "(#Hf & #Hsv & #Hpre & #Hpost)".
  wp_auto.
  wp_apply (wp_Analyze wp_exec lf cf sv vs lpre P with "[$Hf $Hsv $Hpre]")
    as (s lfail) "Hres".
  try wp_auto.
  destruct (decide (lfail = null)) as [->|Hne].
  2:{ (* [Analyze] failed *)
    rewrite bool_decide_eq_false_2 //. wp_auto.
    iApply "HΦ". iPureIntro. done. }
  rewrite bool_decide_eq_true_2 //.
  iDestruct "Hres" as (ps) "(Hps & %Hwf & %Hwp)".
  wp_auto.
  wp_apply (wp_Verify wp_checkDisjunct s ps sv vs lpost Q with "[$Hps $Hsv $Hpost]")
    as (lv) "%Hver".
  try wp_auto.
  iApply "HΦ". iPureIntro. intros Hb θ Hθ.
  apply bool_decide_eq_true in Hb.
  by apply (check_triple cf vs P Q ps θ Hwf Hwp (Hver Hb)).
Qed.

End proof.
