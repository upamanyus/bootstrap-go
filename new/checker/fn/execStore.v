(** [checker.execStore] (checker/exec.go): the [EStore] case of [exec].

    Runs the location operand; on each of its paths [p], runs the value
    operand from [p]'s state and hands the resulting paths to [storeAll],
    which performs the store at [p.Ret] on each.

    Naming: the Go locals are [e], [en], [st], [tok], [fl], [ps], [out], [p],
    [fl2], [ps2], [fl3], [qs], and the range loop's [i], so no Rocq variable
    here is called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_c.
From New.checker.fn Require Import TypeSort heapUpdate storeAll.

Lemma store_ok_mono x qvs outs outs' :
  outs ⊆ outs' → store_ok x qvs outs → store_ok x qvs outs'.
Proof.
  intros Hsub Hok qv Hin. destruct (Hok qv Hin) as (H' & Hup & Hout).
  exists H'. split; first done. by apply Hsub.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** What the loop has established for a prefix of the operand's paths. *)
Definition store_done (ce2 : cexpr) ρ (done : list spath) (outs : list spath) : Prop :=
  ∀ p1, p1 ∈ done → ∃ qvs, exec_sound ce2 ρ (pst p1) qvs ∧
                          paths_wf (length (svars (pst p1))) qvs ∧
                          store_ok (pret p1) qvs outs.

Lemma store_done_snoc ce2 ρ dn outs p1 qvs outs2 :
  store_done ce2 ρ dn outs →
  exec_sound ce2 ρ (pst p1) qvs →
  paths_wf (length (svars (pst p1))) qvs →
  store_rel (pret p1) qvs outs2 →
  store_done ce2 ρ (dn ++ [p1]) (outs ++ outs2).
Proof.
  intros Hdn Hs Hwf Hrel p2 [Hin|Hin]%elem_of_app.
  - destruct (Hdn p2 Hin) as (qv & H1 & H2 & H3). exists qv.
    split_and!; [done|done|]. eapply store_ok_mono; last done. set_solver.
  - apply list_elem_of_singleton in Hin as ->. exists qvs.
    split_and!; [done|done|]. eapply store_ok_mono; last by apply store_rel_ok.
    set_solver.
Qed.

Lemma wp_execStore_aux cty ce1 ce2 :
  (⊢ exec_like checker.exec ce1) → (⊢ exec_like checker.exec ce2) →
  ⊢ exec_like checker.execStore (CEStore cty ce1 ce2).
Proof.
  intros Hex1 Hex2.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (lt la lb) "(#Hn & #Ht & #Ha & #Hb)".
  fold (is_expr la ce1). fold (is_expr lb ce2).
  wp_auto.
  wp_apply (wp_TypeSort lt (Some cty) with "[$Ht]").
  try wp_auto.
  wp_apply (Hex1 $! la lρ lst ρ sst with "[$Hst]").
  { iFrame "#". done. }
  iIntros (sps lfl) "Hpost".
  rewrite /exec_post.
  try wp_auto.
  wp_if_destruct.
  2: { try wp_auto. iApply "HΦ".
       destruct (decide (lfl = null)); [congruence|done]. }
  destruct (decide (null = null)) as [_|]; last congruence.
  iDestruct "Hpost" as (pl) "(Hpl & %Hwfpl & %Hsnd)".
  iDestruct "Hpl" as (xs) "[Hxs Hxp]".
  iDestruct (big_sepL2_length with "Hxp") as %Hlen2.
  iDestruct (own_slice_len with "Hxs") as %Hlen.
  try wp_auto.
  iAssert (∃ (k : w64) (pcur : checker.Path.t) (so : slice.t) (os : list checker.Path.t)
             (outs : list spath),
      "i" ∷ i_ptr ↦ k ∗
      "p" ∷ p_ptr ↦ pcur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hos" ∷ so ↦* os ∗
      "Hcap" ∷ own_slice_cap checker.Path.t so (DfracOwn 1) ∗
      "Hosp" ∷ ([∗ list] y;o ∈ os; outs, is_path y o) ∗
      "Hrest" ∷ ([∗ list] y;o ∈ drop (sint.nat k) xs; drop (sint.nat k) pl, is_path y o) ∗
      "%Hdone" ∷ ⌜store_done ce2 ρ (take (sint.nat k) pl) outs⌝ ∗
      "%Hwfo" ∷ ⌜paths_wf (length (svars sst)) outs⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length xs⌝)%I
    with "[i p out Hxp]" as "HI".
  { iExists (W64 0), _, slice.nil, [], [].
    iFrame "i p out". iDestruct own_slice_nil as "$". iDestruct own_slice_cap_nil as "$".
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite take_0 !drop_0 /=. iFrame "Hxp".
    iPureIntro. split; [|split; [apply paths_wf_nil|word]].
    intros p1 Hp1. by apply elem_of_nil in Hp1. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat k) as x0.
    list_elem pl (sint.nat k) as p0.
    rewrite (drop_S xs x0 (sint.nat k)) // (drop_S pl p0 (sint.nat k)) //.
    iDestruct "Hrest" as "[[#Hret Hst0] Hrest]".
    wp_apply (wp_load_slice_index with "[$Hxs]").
    { word. }
    { done. }
    iIntros "Hxs".
    wp_auto.
    assert (p0 ∈ pl) as Hp0in by (by eapply list_elem_of_lookup_2).
    wp_apply (Hex2 $! lb lρ _ ρ (pst p0) with "[$Hst0]").
    { iFrame "#". iPureIntro. split.
      - by apply (paths_wf_state _ _ Hwfpl).
      - eapply env_below_mono; last done. by apply (paths_wf_grow _ _ Hwfpl). }
    iIntros (sps2 lfl2) "Hpost2".
    rewrite /exec_post.
    try wp_auto.
    wp_if_destruct.
    2: { try wp_auto. wp_for_post. iApply "HΦ".
         destruct (decide (lfl2 = null)); [congruence|done]. }
    destruct (decide (null = null)) as [_|]; last congruence.
    iDestruct "Hpost2" as (qvs) "(Hqvs & %Hwfq & %Hsndq)".
    wp_apply (wp_storeAll with "[$Hqvs]") as (sqs lfl3) "Hpost3".
    { iFrame "#". }
    try wp_auto.
    wp_if_destruct.
    2: { try wp_auto. wp_for_post. iApply "HΦ".
         destruct (decide (lfl3 = null)); [congruence|done]. }
    destruct (decide (null = null)) as [_|]; last congruence.
    iDestruct "Hpost3" as (outs2) "(Hout2 & %Hrel)".
    iDestruct "Hout2" as (ys) "[Hys Hysp]".
    wp_apply (wp_slice_append so os sqs ys (DfracOwn 1)
               with "[$Hos $Hcap $Hys]") as (so') "(Hos & Hcap & _)".
    wp_for_post.
    iFrame "HΦ Hxs en e".
    iExists (word.add k (W64 1)), x0, so', (os ++ ys), (outs ++ outs2).
    replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
    iFrame "i p out Hos Hcap Hrest".
    iSplitL "Hosp Hysp".
    { iApply (big_sepL2_app with "Hosp Hysp"). }
    iPureIntro. split_and!.
    + rewrite (take_S_r pl (sint.nat k) p0) //.
      by eapply store_done_snoc.
    + apply paths_wf_app; first done.
      eapply paths_wf_mono; last by eapply store_rel_wf.
      by apply (paths_wf_grow _ _ Hwfpl).
    + word.
    + word.
  - (* the loop is over *)
    try wp_auto.
    rewrite take_ge in Hdone; last lia.
    iApply "HΦ".
    destruct (decide (null = null)) as [_|]; last congruence.
    iExists outs. iSplitL.
    { iExists os. iFrame. }
    iPureIntro. split; first done.
    eapply exec_sound_store; [exact Hsnd|exact Hwfpl|].
    intros p1 Hp1. destruct (Hdone p1 Hp1) as (qv & H1 & H2 & H3).
    by exists qv.
  Unshelve. all: try apply _.
Qed.

Lemma wp_execStore t e1 e2 :
  (⊢ exec_like checker.exec e1) → (⊢ exec_like checker.exec e2) →
  ⊢ exec_like checker.execStore (CEStore t e1 e2).
Proof. apply wp_execStore_aux. Qed.

End proof.
