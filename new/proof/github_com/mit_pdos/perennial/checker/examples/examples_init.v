(* Package-initialization boilerplate shared by the proofs of the individual
   functions in checker/examples.

   Each function gets its own file so that the cost of checking its proof can
   be measured on its own; see gocheck/demo.sh, which times one [rocq compile
   -vok] per function against one run of the checker on the same
   specification. *)
From New.proof Require Export proof_prelude.
From New.generatedproof.github_com.mit_pdos.perennial.checker Require Export examples.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) examples := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop examples get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    examples.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init examples }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End init.
