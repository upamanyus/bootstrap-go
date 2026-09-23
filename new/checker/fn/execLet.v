(** [checker.execLet] (checker/exec.go): [let: x := e1 in e2]. Runs [e1],
    then [e2] from each of its paths with [x] bound to that path's result
    term, and concatenates the results.

    Note on naming: no Rocq variable here may be called [e], [en], [st],
    [ps], [fl], [out], [p], [en2], [ps2], [fl2] or [i], because those are the names
    of the Go function's own locals and [wp_auto] derives Rocq identifiers
    from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b.
From New.checker.fn Require Import envBind.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execLet (x : go_string) (e1 e2 : cexpr) :
  (⊢ exec_like checker.exec e1) → (⊢ exec_like checker.exec e2) →
  ⊢ exec_like checker.execLet (CELet x e1 e2).
Proof.
  intros Hex1 Hex2.
  iPoseProof Hex1 as "#Hex1". iPoseProof Hex2 as "#Hex2".
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (la lb) "(#Hnode & #Ha & #Hb)".
  fold is_expr.
  wp_auto.
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
                   ∃ qs, qs ⊆ outs ∧ exec_sound e2 ((x, pret q) :: ρ) (pst q) qs⌝)%I
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
    assert (q ∈ ps0) as Hq by (by eapply list_elem_of_lookup_2).
    wp_auto.
    wp_apply (wp_envBind lρ ρ x _ (pret q) with "[$Hρ $Hret]").
    iIntros (lρ2) "#Hρ2".
    wp_auto.
    wp_apply ("Hex2" $! lb lρ2 xp.(checker.Path.St') ((x, pret q) :: ρ) (pst q)
               with "[Hst']").
    { iFrame "∗#". iPureIntro. split.
      - by apply (paths_wf_state _ _ Hwf0).
      - apply env_below_cons; first by apply (paths_wf_ret _ _ Hwf0).
        eapply env_below_mono; last done. by apply (paths_wf_grow _ _ Hwf0). }
    iIntros (s2 lf2) "Hpost2".
    wp_auto.
    wp_if_destruct.
    2:{ wp_for_post. iApply "HΦ". by iApply exec_post_fail. }
    rewrite exec_post_ok.
    iDestruct "Hpost2" as (ps2) "(Hps2 & %Hwf2 & %Hsnd2)".
    iDestruct "Hps2" as (zs) "[Hzs Hzsp]".
    wp_apply (wp_slice_append with "[$Hys $Hcap $Hzs]").
    iIntros (so') "(Hys & Hcap & _)".
    wp_auto.
    wp_for_post.
    iFrame "Hs HΦ en e".
    iExists (word.add n (W64 1)), xp, so', (ys ++ zs), (outs ++ ps2).
    iFrame "i p out Hys Hcap".
    replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
    iFrame "Hrest".
    iSplitL "Hysp Hzsp"; first by iApply (big_sepL2_app with "Hysp Hzsp").
    iPureIntro. split; first word. split.
    + apply paths_wf_app; first done.
      eapply paths_wf_mono; last done. by apply (paths_wf_grow _ _ Hwf0).
    + intros q' Hq'. rewrite (take_S_r _ _ q) // in Hq'.
      apply elem_of_app in Hq' as [Hq'|Hq'].
      * destruct (Hdone q' Hq') as (qs & Hsub & Hqs).
        exists qs. split; last done. set_solver.
      * apply list_elem_of_singleton in Hq' as ->.
        exists ps2. split; last done. set_solver.
  - (* the loop is over *)
    assert (take (sint.nat n) ps0 = ps0) as Htake by (apply take_ge; word).
    rewrite Htake in Hdone.
    try wp_auto.
    iApply "HΦ". rewrite exec_post_ok.
    iExists outs. iFrame "Hys Hysp". iPureIntro. split; first done.
    by eapply exec_sound_let.
Qed.
End proof.
