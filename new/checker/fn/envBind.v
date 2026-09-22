(** [checker.envBind] (checker/exec.go): extend the environment with a new
    binding.

    Note on naming: no Rocq variable here may be called [e], [x] or [t],
    because those are the names of the Go function's own locals and [wp_auto]
    derives Rocq identifiers from them. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The node is freshly allocated, so its points-to has to be discarded
    before it matches [is_env], which is stated with [↦□]. *)
Lemma wp_envBind (le : loc) (ρ : list (go_string * term)) (gx : go_string)
      (lt : loc) (tv : term) :
  {{{ is_pkg_init checker ∗ is_env le ρ ∗ is_term lt tv }}}
    @! checker.envBind #le #gx #lt
  {{{ (le' : loc), RET #le'; is_env le' ((gx, tv) :: ρ) }}}.
Proof.
  wp_start as "(#He & #Ht)".
  iApply wp_fupd.
  wp_auto.
  wp_alloc lnew as "Hnew".
  iPersist "Hnew".
  wp_auto.
  iApply "HΦ". simpl. iModIntro.
  iExists lt, le. by iFrame "Hnew Ht He".
Qed.

End proof.
