(** [checker.envLookup] (checker/exec.go): the first binding of a name in the
    environment linked list.

    Note on naming: no Rocq variable here may be called [e] or [x], because
    those are the names of the Go function's own locals and [wp_auto] derives
    Rocq identifiers from them. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The recursion runs down the [next] chain, so the induction is on the
    Gallina environment with the head location universally quantified. *)
Lemma wp_envLookup_aux (ρ : list (go_string * term)) (gx : go_string) :
  ∀ le : loc,
  {{{ is_pkg_init checker ∗ is_env le ρ }}}
    @! checker.envLookup #le #gx
  {{{ (lt : loc) (ok : bool), RET (#lt, #ok);
      ⌜ok = bool_decide (env_lookup ρ gx ≠ None)⌝ ∗ is_oterm lt (env_lookup ρ gx) }}}.
Proof.
  induction ρ as [|[gy ty] ρ IH]; iIntros (le).
  - (* the empty environment is the nil pointer *)
    wp_start as "#He". iDestruct "He" as %->.
    wp_auto.
    iApply ("HΦ" $! null false). simpl. iSplit; done.
  - wp_start as "#He".
    iDestruct "He" as (ltm lnx) "(#Hnode & #Ht & #Hrest)".
    iDestruct (typed_pointsto_not_null with "Hnode") as %Hnn.
    wp_auto.
    wp_if_destruct; first done.
    try wp_auto.
    wp_if_destruct.
    + (* the head binds the name *)
      simpl. rewrite decide_True //.
      iApply ("HΦ" $! ltm true). iFrame "Ht". iPureIntro.
      by rewrite bool_decide_eq_true_2.
    + (* look further down the chain *)
      try wp_auto.
      wp_apply (IH lnx with "[$]").
      iIntros (lt ok) "[%Hok #Hres]".
      wp_auto.
      simpl. rewrite decide_False //.
      iApply ("HΦ" $! lt ok). by iFrame "Hres".
Qed.

Lemma wp_envLookup (le : loc) (ρ : list (go_string * term)) (gx : go_string) :
  {{{ is_pkg_init checker ∗ is_env le ρ }}}
    @! checker.envLookup #le #gx
  {{{ (lt : loc) (ok : bool), RET (#lt, #ok);
      ⌜ok = bool_decide (env_lookup ρ gx ≠ None)⌝ ∗ is_oterm lt (env_lookup ρ gx) }}}.
Proof. apply wp_envLookup_aux. Qed.

End proof.
