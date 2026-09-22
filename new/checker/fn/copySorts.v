(** [checker.copySorts] (checker/sorts.go): a fresh copy of a sort vector.

    [is_vars] is an *owned* slice, so the caller's slice has to be handed
    back. The fresh slice's [own_slice_cap] is not part of [is_vars] and is
    dropped here; a caller that wants to [append] to the copy needs a
    strengthened specification that also returns it.

    Note on naming: the Go locals are [ss] and [out], so no Rocq variable
    here may be called either (see NOTES.md). *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_copySorts (s : slice.t) (vars : list sort) :
  {{{ is_pkg_init checker ∗ is_vars s vars }}}
    @! checker.copySorts #s
  {{{ (s' : slice.t), RET #s'; is_vars s vars ∗ is_vars s' vars }}}.
Proof.
  wp_start as "Hs".
  rewrite /is_vars.
  iDestruct (own_slice_len with "Hs") as %[Hlen Hnn].
  rewrite length_fmap in Hlen.
  wp_auto.
  wp_apply wp_slice_make2 as (sl) "[Hout Hcap]".
  { iPureIntro. word. }
  wp_apply (wp_slice_copy with "[$Hout $Hs]") as (nc) "(%Hn & Hout & Hs)".
  rewrite length_replicate take_ge; last (rewrite length_fmap; lia).
  rewrite drop_ge; last (rewrite length_replicate length_fmap; lia).
  rewrite app_nil_r.
  iApply "HΦ". iFrame.
Qed.

End proof.
