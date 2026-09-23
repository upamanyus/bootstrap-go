(** [checker.execUnit] (checker/exec.go): the unit value is the single
    path [onePath] builds, with the term [TUnit].

    Note on naming: no Rocq variable here may be called [e], [en] or [st],
    because those are the names of the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b exec_sound_a.
From New.checker.fn Require Import onePath.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execUnit : ⊢ exec_like checker.execUnit CEUnit.
Proof.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  simpl.
  wp_auto.
  wp_alloc lt as "Hlt".
  iPersist "Hlt".
  wp_auto.
  wp_apply (wp_onePath lt lst TUnit sst with "[$Hst]").
  { by iFrame "#". }
  iIntros (s) "Hs".
  wp_auto.
  iApply "HΦ". rewrite exec_post_ok.
  iExists _. iFrame "Hs". iPureIntro. split.
  - by apply paths_wf_single.
  - apply exec_sound_unit.
Qed.
End proof.
