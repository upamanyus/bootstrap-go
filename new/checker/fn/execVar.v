(** [checker.execVar] (checker/exec.go): a variable is looked up in the
    environment ([envLookup]); an unbound one is a failure, a bound one is
    the single path [onePath] builds with the bound term.

    Note on naming: no Rocq variable here may be called [e], [en], [st], [t]
    or [ok], because those are the names of the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b exec_sound_a.
From New.checker.fn Require Import onePath envLookup.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execVar (x : go_string) : ⊢ exec_like checker.execVar (CEVar x).
Proof.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  simpl.
  wp_auto.
  wp_apply (wp_envLookup lρ ρ x with "[$Hρ]").
  iIntros (lt okb) "[%Hok #Hlt]".
  wp_auto.
  destruct (env_lookup ρ x) as [xt|] eqn:Hlk.
  2:{ (* unbound *)
    assert (okb = false) as -> by (rewrite Hok; apply bool_decide_eq_false_2; naive_solver).
    wp_auto.
    wp_alloc lfail as "Hlf".
    iDestruct (typed_pointsto_not_null with "Hlf") as %Hnn.
    wp_auto.
    iApply "HΦ". by iApply exec_post_fail. }
  assert (okb = true) as -> by (rewrite Hok; apply bool_decide_eq_true_2; done).
  wp_auto.
  wp_apply (wp_onePath lt lst xt sst with "[$Hst]").
  { by iFrame "#". }
  iIntros (s) "Hs".
  wp_auto.
  assert (vars_below (length (svars sst)) xt) as Hb by (by eapply env_below_lookup).
  iApply "HΦ". rewrite exec_post_ok.
  iExists _. iFrame "Hs". iPureIntro. split.
  - by apply paths_wf_single.
  - by apply exec_sound_var.
Qed.
End proof.
