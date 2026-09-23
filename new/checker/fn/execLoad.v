(** [checker.execLoad] (checker/exec.go): [![t] e]. Runs [e], then on each
    of its paths looks the result term up in the path's symbolic heap
    ([heapLookup]); the cell's value term is the result, in the same state.

    Note on naming: no Rocq variable here may be called [e], [en], [st],
    [tok], [ps], [fl], [out], [p], [ok], [v] or [i], because those are the
    names of the Go function's own locals and [wp_auto] derives Rocq
    identifiers from them; the specification is therefore proved over [cty]
    and [ce] and restated at the end. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b.
From New.checker.fn Require Import TypeSort heapLookup.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execLoad_aux (cty : ctype) (ce : cexpr) :
  (⊢ exec_like checker.exec ce) → ⊢ exec_like checker.execLoad (CELoad cty ce).
Proof.
  intros Hex1.
  iPoseProof Hex1 as "#Hex1".
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (lty la) "(#Hnode & #Hty & #Ha)".
  fold is_expr.
  wp_auto.
  wp_apply (wp_TypeSort lty (Some cty) with "[$Hty]").
  try wp_auto.
  wp_apply ("Hex1" $! la lρ lst ρ sst with "[Hst]").
  { iFrame "∗#". iPureIntro. done. }
  iIntros (s lf) "Hpost".
  wp_auto.
  wp_if_destruct.
  2:{ iApply "HΦ". by iApply exec_post_fail. }
  rewrite exec_post_ok.
  iDestruct "Hpost" as (ps0) "(Hps & %Hwf0 & %Hsnd0)".
  iDestruct "Hps" as (xs) "[Hs Hxs]".
  iDestruct (big_sepL2_length with "Hxs") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iAssert (∃ (n : w64) (cur : checker.Path.t) (so : slice.t)
             (ys : list checker.Path.t) (outs : list spath),
      "i" ∷ i_ptr ↦ n ∗
      "p" ∷ p_ptr ↦ cur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hys" ∷ so ↦* ys ∗
      "Hcap" ∷ own_slice_cap checker.Path.t so (DfracOwn 1) ∗
      "Hysp" ∷ ([∗ list] y;q ∈ ys;outs, is_path y q) ∗
      "Hrest" ∷ ([∗ list] x;q ∈ drop (sint.nat n) xs; drop (sint.nat n) ps0, is_path x q) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length xs⌝ ∗
      "%Hwfo" ∷ ⌜paths_wf (length (svars sst)) outs⌝ ∗
      "%Hdone" ∷ ⌜∀ q, q ∈ take (sint.nat n) ps0 →
                   ∃ y, heap_lookup (sheap (pst q)) (pret q) = Some y ∧
                        mkPath y (pst q) ∈ outs⌝)%I
    with "[i p out Hxs]" as "HI".
  { iExists (W64 0), _, slice.nil, [], []. iFrame "i p out".
    iDestruct (own_slice_nil (V:=checker.Path.t) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=checker.Path.t)) as "$".
    iSplit; first by iApply big_sepL2_nil.
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite !drop_0 take_0. iFrame "Hxs". iPureIntro.
    split_and!; [word|word|apply paths_wf_nil|set_solver]. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat n) as xp.
    list_elem ps0 (sint.nat n) as q.
    wp_apply (wp_load_slice_index with "[$Hs]").
    { word. }
    { done. }
    iIntros "Hs".
    rewrite (drop_S xs xp (sint.nat n)) // (drop_S ps0 q (sint.nat n)) //.
    iDestruct "Hrest" as "[[#Hret Hst'] Hrest]".
    iDestruct "Hst'" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
    assert (q ∈ ps0) as Hq by (by eapply list_elem_of_lookup_2).
    wp_auto.
    wp_apply (wp_heapLookup hs (sheap (pst q)) _ (pret q) with "[$Hheap $Hret]").
    iIntros (lv okb) "(Hheap & %Hok & #Hlv)".
    destruct (heap_lookup (sheap (pst q)) (pret q)) as [y|] eqn:Hlk.
    2:{ (* no cell at that location *)
      assert (okb = false) as -> by (rewrite Hok; apply bool_decide_eq_false_2; naive_solver).
      wp_auto.
      wp_alloc lfail as "Hlf".
      iDestruct (typed_pointsto_not_null with "Hlf") as %Hnn.
      wp_auto.
      wp_for_post.
      iApply "HΦ". by iApply exec_post_fail. }
    assert (okb = true) as -> by (rewrite Hok; apply bool_decide_eq_true_2; done).
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl [Hsl _]".
    replace (Z.to_nat (sint.Z (W64 0))) with 0%nat by word.
    iSimpl in "Hsl".
    wp_auto.
    wp_apply (wp_slice_append with "[$Hys $Hcap $Hsl]").
    iIntros (so') "(Hys & Hcap & _)".
    wp_auto.
    wp_for_post.
    iFrame "Hs HΦ e".
    iExists (word.add n (W64 1)), xp, so',
      (ys ++ [checker.Path.mk lv xp.(checker.Path.St')]), (outs ++ [mkPath y (pst q)]).
    iFrame "i p out Hys Hcap".
    replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
    iFrame "Hrest".
    iSplitL "Hysp Hstl Hheap Hcond".
    { iApply (big_sepL2_app with "Hysp"). simpl. iSplitL; last done.
      iFrame "Hlv". iExists hs, cs, vs. iFrame "∗#". }
    assert (wf_state (pst q)) as Hwfq by (by apply (paths_wf_state _ _ Hwf0)).
    iPureIntro. split; first word. split.
    + apply paths_wf_app; first done. split.
      * intros q' ->%list_elem_of_singleton. done.
      * intros q' ->%list_elem_of_singleton. simpl. by apply (paths_wf_grow _ _ Hwf0).
      * intros q' ->%list_elem_of_singleton. simpl.
        eapply heap_lookup_below; last done. by apply (wf_heap _ Hwfq).
    + intros q' Hq'. rewrite (take_S_r _ _ q) // in Hq'.
      apply elem_of_app in Hq' as [Hq'|Hq'].
      * destruct (Hdone q' Hq') as (y' & Hy' & Hin').
        exists y'. split; first done. set_solver.
      * apply list_elem_of_singleton in Hq' as ->.
        exists y. split; first done. set_solver.
  - (* the loop is over *)
    assert (take (sint.nat n) ps0 = ps0) as Htake by (apply take_ge; word).
    rewrite Htake in Hdone.
    try wp_auto.
    iApply "HΦ". rewrite exec_post_ok.
    iExists outs. iFrame "Hys Hysp". iPureIntro. split; first done.
    by eapply exec_sound_load.
Qed.

Lemma wp_execLoad t e : (⊢ exec_like checker.exec e) → ⊢ exec_like checker.execLoad (CELoad t e).
Proof. apply wp_execLoad_aux. Qed.

End proof.
