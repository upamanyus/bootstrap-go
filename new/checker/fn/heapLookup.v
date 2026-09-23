(** [checker.heapLookup] (checker/exec.go): the value stored at a location
    term, found by a linear scan of the symbolic heap.

    Note on naming: no Rocq variable here may be called [h], [l] or [c],
    because those are the names of the Go function's own locals and [wp_auto]
    derives Rocq identifiers from them. *)
From New.checker Require Import prelude.
From New.checker.fn Require Import termEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** The Gallina mirror: the first cell whose location term is syntactically
    [x]. *)
Fixpoint heap_lookup (H : list scell) (x : term) : option term :=
  match H with
  | [] => None
  | c :: H' => if decide (cloc c = x) then Some (cval c) else heap_lookup H' x
  end.

Lemma heap_lookup_app H1 H2 x :
  heap_lookup (H1 ++ H2) x =
    match heap_lookup H1 x with Some t => Some t | None => heap_lookup H2 x end.
Proof.
  induction H1 as [|c H1 IH]; simpl; first done.
  destruct (decide (cloc c = x)); done.
Qed.

(** What the loop learns when it reaches a matching cell. *)
Lemma heap_lookup_hit (H : list scell) (n : nat) (sc : scell) (x : term) :
  H !! n = Some sc →
  heap_lookup (take n H) x = None →
  cloc sc = x →
  heap_lookup H x = Some (cval sc).
Proof.
  intros Hn Hmiss Hloc.
  rewrite -(take_drop_middle H n sc) // heap_lookup_app Hmiss /=.
  by rewrite decide_True.
Qed.

(** ... and when it passes a non-matching one. *)
Lemma heap_lookup_step (H : list scell) (n : nat) (sc : scell) (x : term) :
  H !! n = Some sc →
  heap_lookup (take n H) x = None →
  cloc sc ≠ x →
  heap_lookup (take (S n) H) x = None.
Proof.
  intros Hn Hmiss Hloc.
  rewrite (take_S_r _ _ sc) // heap_lookup_app Hmiss /=.
  by rewrite decide_False.
Qed.

Lemma wp_heapLookup (s : slice.t) (H : list scell) (lx : loc) (x : term) :
  {{{ is_pkg_init checker ∗ is_heap s H ∗ is_term lx x }}}
    @! checker.heapLookup #s #lx
  {{{ (lv : loc) (ok : bool), RET (#lv, #ok);
      is_heap s H ∗ ⌜ok = bool_decide (heap_lookup H x ≠ None)⌝ ∗
      is_oterm lv (heap_lookup H x) }}}.
Proof using All.
  wp_start as "[Hheap #Hx]".
  iDestruct "Hheap" as (cs) "[Hs #Hcs]".
  iDestruct (big_sepL2_length with "Hcs") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_auto.
  iAssert (∃ (n : w64) (cur : checker.Cell.t),
      "i" ∷ i_ptr ↦ n ∗
      "c" ∷ c_ptr ↦ cur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length cs⌝ ∗
      "%Hmiss" ∷ ⌜heap_lookup (take (sint.nat n) H) x = None⌝)%I
    with "[i c]" as "HI".
  { iFrame. iPureIntro. split; first word.
    replace (sint.nat (W64 0)) with 0%nat by word. done. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem cs (sint.nat n) as cur'.
    list_elem H (sint.nat n) as sc.
    iDestruct (big_sepL2_lookup with "Hcs") as "#Hcell"; [done|done|].
    iDestruct "Hcell" as "[#Hloc #Hval]".
    wp_apply (wp_load_slice_index with "[$Hs]").
    { word. }
    { done. }
    iIntros "Hs".
    wp_auto.
    wp_apply (wp_termEq _ _ (Some (cloc sc)) (Some x) with "[$]").
    wp_if_destruct.
    + (* this cell is the one *)
      try wp_auto.
      wp_for_post.
      try wp_auto.
      assert (heap_lookup H x = Some (cval sc)) as Hhit.
      { eapply heap_lookup_hit; [done|done|congruence]. }
      iApply ("HΦ" $! _ true).
      iSplitL "Hs"; first by iFrame "Hs Hcs".
      iSplit.
      { iPureIntro. symmetry. apply bool_decide_eq_true_2. rewrite Hhit. done. }
      rewrite Hhit /=. iFrame "Hval".
    + (* keep scanning *)
      try wp_auto.
      wp_for_post.
      iFrame. iPureIntro. split; first word.
      replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
      eapply heap_lookup_step; [done|done|congruence].
  - (* the scan reached the end of the heap *)
    try wp_auto.
    assert (take (sint.nat n) H = H) as Htake.
    { apply take_ge. word. }
    rewrite Htake in Hmiss.
    iApply ("HΦ" $! null false).
    iSplitL "Hs"; first by iFrame "Hs Hcs".
    iSplit.
    { iPureIntro. rewrite Hmiss. symmetry. apply bool_decide_eq_false_2.
      naive_solver. }
    rewrite Hmiss /=. done.
Qed.

End proof.
