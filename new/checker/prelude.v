(** Everything the per-function proofs need.

    One Rocq file per Go function (in new/checker/fn/), so that the files can
    be checked in parallel and one slow proof does not hold up the others;
    this is the shared prefix. *)
From New.proof Require Export proof_prelude.
From New.golang Require Export theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Export checker.
From New.checker Require Export defs term_lemmas subst interp steps repr.

Set Default Proof Using "All".

Section prelude.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

(** The checker has no package-level state. *)
Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop checker get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    checker.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init checker }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End prelude.
