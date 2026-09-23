(** [checker.heapUpdate] (checker/exec.go): a fresh symbolic heap in which
    the *first* cell at a location term holds a new value, or failure if the
    location is not owned.

    Note on naming: no Rocq variable here may be called [h], [l], [v], [c],
    [out] or [found], because those are the names of the Go function's own
    locals and [wp_auto] derives Rocq identifiers from them.  The working
    lemma therefore calls the new value [vt] / [lvt]; [wp_heapUpdate] at the
    bottom restates it in the intended form and never runs [wp_auto]. *)
From New.checker Require Import prelude.
From New.checker.fn Require Import termEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** The Gallina mirror. *)
Fixpoint heap_update (H : list scell) (x v : term) : option (list scell) :=
  match H with
  | [] => None
  | c :: H' => if decide (cloc c = x) then Some (mkCell (cloc c) v :: H')
               else (λ r, c :: r) <$> heap_update H' x v
  end.

(** What the loop has built after scanning a prefix: the updated prefix if
    the prefix already contained the location, and the prefix itself
    otherwise. *)
Definition heap_updated (H : list scell) (x v : term) : list scell :=
  default H (heap_update H x v).

Lemma heap_update_app_some H1 H2 x v P :
  heap_update H1 x v = Some P → heap_update (H1 ++ H2) x v = Some (P ++ H2).
Proof.
  revert P. induction H1 as [|c H1 IH]; simpl; intros P Hup; first done.
  destruct (decide (cloc c = x)).
  - injection Hup as <-. done.
  - destruct (heap_update H1 x v) as [P'|] eqn:Heq; simpl in Hup; last done.
    injection Hup as <-. simpl. by rewrite (IH P').
Qed.

Lemma heap_update_app_none H1 H2 x v :
  heap_update H1 x v = None →
  heap_update (H1 ++ H2) x v = (λ r, H1 ++ r) <$> heap_update H2 x v.
Proof.
  induction H1 as [|c H1 IH]; simpl; intros Hup.
  - by destruct (heap_update H2 x v).
  - destruct (decide (cloc c = x)); first done.
    destruct (heap_update H1 x v) eqn:Heq; simpl in Hup; first done.
    rewrite IH //. by destruct (heap_update H2 x v).
Qed.

(** The three ways one more cell can extend the prefix. *)
Lemma heap_update_snoc_found H1 sc x v P :
  heap_update H1 x v = Some P →
  heap_update (H1 ++ [sc]) x v = Some (P ++ [sc]).
Proof. apply heap_update_app_some. Qed.

Lemma heap_update_snoc_hit H1 sc x v :
  heap_update H1 x v = None → cloc sc = x →
  heap_update (H1 ++ [sc]) x v = Some (H1 ++ [mkCell (cloc sc) v]).
Proof.
  intros Hup Hloc. rewrite (heap_update_app_none H1 [sc]) //.
  simpl. by rewrite decide_True.
Qed.

Lemma heap_update_snoc_miss H1 sc x v :
  heap_update H1 x v = None → cloc sc ≠ x →
  heap_update (H1 ++ [sc]) x v = None.
Proof.
  intros Hup Hloc. rewrite (heap_update_app_none H1 [sc]) //.
  simpl. by rewrite decide_False.
Qed.

(** [wp_slice_literal] hands back the one-element literal in the shape
    [<[0:=y]> [zero]]; this normalises it. *)
Lemma insert0_singleton {A} (y z : A) : <[Z.to_nat (sint.Z (W64 0)) := y]> [z] = [y].
Proof. replace (Z.to_nat (sint.Z (W64 0))) with 0%nat by word. done. Qed.

Lemma wp_heapUpdate_aux (s : slice.t) (H : list scell) (lx lvt : loc) (x vt : term) :
  {{{ is_pkg_init checker ∗ is_heap s H ∗ is_term lx x ∗ is_term lvt vt }}}
    @! checker.heapUpdate #s #lx #lvt
  {{{ (s' : slice.t) (ok : bool), RET (#s', #ok);
      is_heap s H ∗ ⌜ok = bool_decide (heap_update H x vt ≠ None)⌝ ∗
      (if ok then ∃ H', ⌜heap_update H x vt = Some H'⌝ ∗ is_heap s' H' else True) }}}.
Proof using All.
  wp_start as "(Hheap & #Hx & #Hvt)".
  iDestruct "Hheap" as (cs) "[Hs #Hcs]".
  iDestruct (big_sepL2_length with "Hcs") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_auto.
  iAssert (∃ (n : w64) (cur : checker.Cell.t) (fl : bool)
             (so : slice.t) (os : list checker.Cell.t) (Q : list scell),
      "i" ∷ i_ptr ↦ n ∗
      "c" ∷ c_ptr ↦ cur ∗
      "found" ∷ found_ptr ↦ fl ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hos" ∷ so ↦* os ∗
      "Hcap" ∷ own_slice_cap checker.Cell.t so (DfracOwn 1) ∗
      "#Hosc" ∷ ([∗ list] q;sq ∈ os;Q, is_cell q sq) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length cs⌝ ∗
      "%Hfl" ∷ ⌜if fl then heap_update (take (sint.nat n) H) x vt = Some Q
                else heap_update (take (sint.nat n) H) x vt = None ∧
                     Q = take (sint.nat n) H⌝)%I
    with "[i c found out]" as "HI".
  { iFrame. iDestruct own_slice_nil as "$". iDestruct own_slice_cap_nil as "$".
    iExists []. iSplit; first by iApply big_sepL2_nil.
    iPureIntro. replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite take_0. split; [word|done]. }
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
    assert (take (S (sint.nat n)) H = take (sint.nat n) H ++ [sc]) as Htk
      by (apply take_S_r; done).
    destruct fl.
    + (* the location was already replaced earlier in the scan *)
      wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "%sl [Hsl _]".
      rewrite insert0_singleton. wp_auto.
      wp_apply (wp_slice_append with "[$Hos $Hcap $Hsl]").
      iIntros "%so' (Hos & Hcap & _)".
      wp_auto.
      wp_for_post.
      iFrame "Hs HΦ v l".
      iExists (word.add n (W64 1)), cur', true, so', (os ++ [cur']), (Q ++ [sc]).
      iFrame "i c found out Hos Hcap".
      iSplit.
      { iApply (big_sepL2_app with "Hosc"). simpl.
        iSplitL; last done. iFrame "Hloc Hval". }
      iPureIntro. split; first word.
      replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
      rewrite Htk. by apply heap_update_snoc_found.
    + (* still looking: compare this cell's location term *)
      destruct Hfl as [Hnone ->].
      wp_auto.
      wp_apply (wp_termEq _ _ (Some (cloc sc)) (Some x) with "[$]").
      wp_if_destruct.
      * (* this is the cell to replace *)
        try wp_auto.
        assert (cloc sc = x) as Hhit by congruence.
        wp_apply wp_slice_literal.
        iSplitR; first done.
        iIntros "%sl [Hsl _]".
        rewrite insert0_singleton. wp_auto.
        wp_apply (wp_slice_append with "[$Hos $Hcap $Hsl]").
        iIntros "%so' (Hos & Hcap & _)".
        wp_auto.
        wp_for_post.
        iFrame "Hs HΦ v l".
        iExists (word.add n (W64 1)), cur', true, so',
          (os ++ [checker.Cell.mk cur'.(checker.Cell.Loc') lvt]),
          (take (sint.nat n) H ++ [mkCell (cloc sc) vt]).
        iFrame "i c found out Hos Hcap".
        iSplit.
        { iApply (big_sepL2_app with "Hosc"). simpl.
          iSplitL; last done. iFrame "Hloc Hvt". }
        iPureIntro. split; first word.
        replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
        rewrite Htk. by apply heap_update_snoc_hit.
      * (* not this cell either *)
        try wp_auto.
        assert (cloc sc ≠ x) as Hmiss by congruence.
        wp_apply wp_slice_literal.
        iSplitR; first done.
        iIntros "%sl [Hsl _]".
        rewrite insert0_singleton. wp_auto.
        wp_apply (wp_slice_append with "[$Hos $Hcap $Hsl]").
        iIntros "%so' (Hos & Hcap & _)".
        wp_auto.
        wp_for_post.
        iFrame "Hs HΦ v l".
        iExists (word.add n (W64 1)), cur', false, so', (os ++ [cur']),
          (take (sint.nat n) H ++ [sc]).
        iFrame "i c found out Hos Hcap".
        iSplit.
        { iApply (big_sepL2_app with "Hosc"). simpl.
          iSplitL; last done. iFrame "Hloc Hval". }
        iPureIntro.
        replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
        rewrite Htk. split; first word.
        split; last done. by apply heap_update_snoc_miss.
  - (* the scan is over *)
    assert (take (sint.nat n) H = H) as Htake by (apply take_ge; word).
    rewrite Htake in Hfl.
    destruct fl.
    + (* the location was found *)
      try wp_auto.
      iApply ("HΦ" $! so true).
      iSplitL "Hs"; first by iFrame "Hs Hcs".
      iSplit.
      { iPureIntro. symmetry. apply bool_decide_eq_true_2. rewrite Hfl. done. }
      iExists Q. iSplit; first done. iFrame "Hos Hosc".
    + (* no cell at that location *)
      destruct Hfl as [Hnone ->].
      try wp_auto.
      iApply ("HΦ" $! slice.nil false).
      iSplitL "Hs"; first by iFrame "Hs Hcs".
      iSplit; last done.
      iPureIntro. rewrite Hnone. symmetry. apply bool_decide_eq_false_2.
      naive_solver.
Qed.

(** The statement in the intended naming.  Proving it needs no [wp_auto], so
    the Go locals [v] and [l] may safely appear as Rocq variables here. *)
Lemma wp_heapUpdate (s : slice.t) (H : list scell) (lx lv : loc) (x v : term) :
  {{{ is_pkg_init checker ∗ is_heap s H ∗ is_term lx x ∗ is_term lv v }}}
    @! checker.heapUpdate #s #lx #lv
  {{{ (s' : slice.t) (ok : bool), RET (#s', #ok);
      is_heap s H ∗ ⌜ok = bool_decide (heap_update H x v ≠ None)⌝ ∗
      (if ok then ∃ H', ⌜heap_update H x v = Some H'⌝ ∗ is_heap s' H'
       else True) }}}.
Proof using All. apply wp_heapUpdate_aux. Qed.

End proof.
