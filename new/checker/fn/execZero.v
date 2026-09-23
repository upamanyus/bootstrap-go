(** [checker.execZero] (checker/exec.go): the zero value of a type
    ([typeZero]) is the single path [onePath] builds.

    Note on naming: no Rocq variable here may be called [e], [en], [st], [z]
    or [ok], because those are the names of the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b exec_sound_a.
From New.checker.fn Require Import onePath typeZero.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execZero_aux (cty : ctype) : ⊢ exec_like checker.execZero (CEZero cty).
Proof.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (lty) "(#Hnode & #Hty)".
  wp_auto.
  wp_apply (wp_typeZero lty cty with "[$Hty]").
  iIntros (lz) "#Hlz".
  wp_auto.
  wp_apply (wp_onePath lz lst (ctype_zero cty) sst with "[$Hst]").
  { by iFrame "#". }
  iIntros (s) "Hs".
  wp_auto.
  iApply "HΦ". rewrite exec_post_ok.
  iExists _. iFrame "Hs". iPureIntro. split.
  - apply paths_wf_single; [done|done|apply vars_below_ctype_zero].
  - apply exec_sound_zero.
Qed.

Lemma wp_execZero (t : ctype) : ⊢ exec_like checker.execZero (CEZero t).
Proof. apply wp_execZero_aux. Qed.

End proof.
