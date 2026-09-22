(** the [clone] method of [checker.State] (checker/state.go): the deep-enough copy a state gets
    before it is modified, so that forking at an [if:] or appending to a heap
    on one path can never be observed on another.

    Naming: the Go locals are [s], [h], [c], [v], so no Rocq variable here is
    called any of those (see NOTES.md). *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_State__clone (lst : loc) (sst : sstate) :
  {{{ is_pkg_init checker ∗ is_state lst sst }}}
    lst @! (go.PointerType checker.State) @! "clone" #()
  {{{ (lst' : loc), RET #lst'; is_state lst sst ∗ is_state lst' sst }}}.
Proof.
  wp_start as "Hst".
  iDestruct "Hst" as (sh sc sv) "(Hl & Hheap & Hcond & Hvars)".
  iDestruct "Hheap" as (cells) "[Hsh #Hcells]".
  iDestruct "Hcond" as (locs) "[Hsc #Hlocs]".
  rewrite /is_vars.
  iDestruct (own_slice_len with "Hsh") as %[Hlh Hbh].
  iDestruct (own_slice_len with "Hsc") as %[Hlc Hbc].
  iDestruct (own_slice_len with "Hvars") as %[Hlv Hbv].
  rewrite length_fmap in Hlv.
  try wp_auto.
  (* the three make+copy pairs *)
  wp_apply wp_slice_make2 as (nh) "[Hnh Hnhcap]"; first (iPureIntro; word).
  try wp_auto.
  wp_apply (wp_slice_copy with "[$Hnh $Hsh]") as (k1) "(%Hk1 & Hnh & Hsh)".
  rewrite length_replicate take_ge; last lia.
  rewrite drop_ge; last (rewrite length_replicate; lia).
  rewrite app_nil_r.
  try wp_auto.
  wp_apply wp_slice_make2 as (nc) "[Hnc Hnccap]"; first (iPureIntro; word).
  try wp_auto.
  wp_apply (wp_slice_copy with "[$Hnc $Hsc]") as (k2) "(%Hk2 & Hnc & Hsc)".
  rewrite length_replicate take_ge; last lia.
  rewrite drop_ge; last (rewrite length_replicate; lia).
  rewrite app_nil_r.
  try wp_auto.
  wp_apply wp_slice_make2 as (nv) "[Hnv Hnvcap]"; first (iPureIntro; word).
  try wp_auto.
  wp_apply (wp_slice_copy with "[$Hnv $Hvars]") as (k3) "(%Hk3 & Hnv & Hvars)".
  rewrite length_replicate take_ge; last (rewrite length_fmap; lia).
  rewrite drop_ge; last (rewrite length_replicate length_fmap; lia).
  rewrite app_nil_r.
  try wp_auto.
  wp_alloc lnew as "Hnew".
  try wp_auto.
  iApply "HΦ". iFrame "Hl Hnew".
  rewrite /is_heap /is_cond /is_vars.
  iSplitL "Hsh Hsc Hvars"; iFrame "#"; iFrame.
Qed.

End proof.
