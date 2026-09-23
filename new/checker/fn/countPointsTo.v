(** [checker.countPointsTo] (checker/match.go): the number of points-to atoms
    of a disjunct, [count_pts] (match_sound.v).

    Naming: the Go locals are [atoms], [n] and [at] (and the range loop's
    [i]), so no Rocq variable here is called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes match_sound.

(** The Go code tests the kind code of each atom. *)
Lemma is_pts_code a : bool_decide (assn_code a = W64 6) = is_pts a.
Proof. destruct a; simpl; by vm_compute. Qed.

Lemma is_pure_code a : bool_decide (assn_code a = W64 5) = is_pure a.
Proof. destruct a; simpl; by vm_compute. Qed.

Lemma count_pts_take_S atms k a :
  atms !! k = Some a →
  count_pts (take (S k) atms) = (count_pts (take k atms) + if is_pts a then 1 else 0)%nat.
Proof.
  intros Hk. rewrite (take_S_r _ _ a) // count_pts_app /=. lia.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_countPointsTo (sa : slice.t) (dq : dfrac) (las : list loc) (atms : list cassn) :
  {{{ is_pkg_init checker ∗ sa ↦*{dq} las ∗ □ ([∗ list] la;x ∈ las; atms, is_assn la x) }}}
    @! checker.countPointsTo #sa
  {{{ RET #(W64 (count_pts atms)); sa ↦*{dq} las }}}.
Proof.
  wp_start as "[Hs #Has]".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_auto.
  iAssert (∃ (k : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ k ∗
      "n" ∷ n_ptr ↦ W64 (count_pts (take (sint.nat k) atms)) ∗
      "at" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length las⌝)%I
    with "[i n at]" as "HI".
  { iExists (W64 0), null.
    replace (sint.nat (W64 0)) with 0%nat by word. rewrite take_0 /=.
    iFrame. iPureIntro. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat k) as lcur'.
    list_elem atms (sint.nat k) as acur.
    iDestruct (big_sepL2_lookup with "Has") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hs]"); [word|done|].
    iIntros "Hs".
    iDestruct (is_assn_node with "Hcur") as (lL lR lX lY) "(_ & #Hnode & _)".
    wp_auto.
    rewrite is_pts_code.
    pose proof (count_pts_take_S _ _ acur Hacur_lookup) as HS.
    destruct (is_pts acur).
    + wp_auto. wp_for_post. iFrame "Hs HΦ".
      iExists (word.add k (W64 1)), lcur'.
      replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word. rewrite HS.
      replace (W64 (count_pts (take (sint.nat k) atms) + 1)%nat)
        with (word.add (W64 (count_pts (take (sint.nat k) atms))) (W64 1)) by word.
      iFrame. iPureIntro. word.
    + wp_auto. wp_for_post. iFrame "Hs HΦ".
      iExists (word.add k (W64 1)), lcur'.
      replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word. rewrite HS.
      rewrite Nat.add_0_r. iFrame. iPureIntro. word.
  - rewrite take_ge; last word.
    try wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
