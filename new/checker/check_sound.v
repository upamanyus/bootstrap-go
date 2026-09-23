(** The statement of [check_sound] (soundness.v), proved.

    The text of [check_sound_proof] is character-identical to the axiom's. It
    is [wp_Check] (fn/Check.v) with the variables renamed back: [wp_Check]
    cannot use the names [f], [vars], [pre] and [post] because they are Go
    locals of [Check] (see NOTES.md). *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Import defs.
From New.checker Require Import prelude exec_def disjunct disjunct_ro verify_def.
From New.checker.fn Require Import Check.

Section semantics.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma check_sound_proof :
  ∀ (f : cfunc) (vars : list sort) (pre post : cassn)
    (lf : loc) (svars : slice.t) (lpre lpost : loc),
  {{{ is_pkg_init checker ∗
      is_func lf f ∗ is_sorts svars vars ∗ is_assn lpre pre ∗ is_assn lpost post }}}
    @! checker.Check #lf #svars #lpre #lpost
  {{{ (b : bool), RET #b;
      ⌜ b = true →
        ∀ θ : nat → val,
          vars_sat θ vars →
          {{{ pre_interp θ pre }}}
            apply_vals (func_val f) (arg_vals f θ)
          {{{ (v : val), RET v; post_interp θ v post }}} ⌝ }}}.
Proof.
  intros f vars pre post lf svars lpre lpost.
  apply (wp_Check f vars pre post lf svars lpre lpost).
Qed.

End semantics.
