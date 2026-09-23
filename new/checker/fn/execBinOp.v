(** [checker.execBinOp] (checker/exec.go): a binary operator [op] at type
    [t] applied to [e1] and [e2]. Runs [e1], then [e2] from each of its
    paths, then [binOpAll] on the results of [e2] with the result term of
    [e1] as the left operand; the results are concatenated. This is
    GooseLang's evaluation order for [Pair]: left, then right.

    Note on naming: no Rocq variable here may be called [e], [en], [st],
    [tok], [ps], [fl], [out], [p], [ps2], [fl2], [qs], [fl3] or [i],
    because those are the names of the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b.
From New.checker.fn Require Import TypeSort binOpAll.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execBinOp op t e1 e2 :
  (⊢ exec_like checker.exec e1) → (⊢ exec_like checker.exec e2) →
  ⊢ exec_like checker.execBinOp (CEBinOp op t e1 e2).
Proof.
  intros Hex1 Hex2.
  iPoseProof Hex1 as "#Hex1". iPoseProof Hex2 as "#Hex2".
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iPoseProof "He" as "#He0".
  iDestruct "He0" as (lty la lb) "(#Hnode & #Hty & #Ha & #Hb)".
  fold is_expr.
  wp_auto.
  wp_apply (wp_TypeSort lty (Some t) with "[$Hty]").
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
                   ∃ rs, exec_sound e2 ρ (pst q) rs ∧
                     ∀ sq, sq ∈ rs → ∃ r,
                       sort_of_vars (svars (pst sq)) (pret q) = Some (ctype_sort t) ∧
                       sort_of_vars (svars (pst sq)) (pret sq) = Some (ctype_sort t) ∧
                       apply_binop op t (pret q) (pret sq) = Some r ∧
                       mkPath r (pst sq) ∈ outs⌝)%I
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
    list_elem xs (sint.nat n) as x.
    list_elem ps0 (sint.nat n) as q.
    wp_apply (wp_load_slice_index with "[$Hs]").
    { word. }
    { done. }
    iIntros "Hs".
    rewrite (drop_S xs x (sint.nat n)) // (drop_S ps0 q (sint.nat n)) //.
    iDestruct "Hrest" as "[[#Hret Hst'] Hrest]".
    assert (q ∈ ps0) as Hq by (by eapply list_elem_of_lookup_2).
    wp_auto.
    wp_apply ("Hex2" $! lb lρ x.(checker.Path.St') ρ (pst q) with "[Hst']").
    { iFrame "∗#". iPureIntro. split.
      - by apply (paths_wf_state _ _ Hwf0).
      - eapply env_below_mono; last done. by apply (paths_wf_grow _ _ Hwf0). }
    iIntros (s2 lf2) "Hpost2".
    wp_auto.
    wp_if_destruct.
    2:{ wp_for_post. iApply "HΦ". by iApply exec_post_fail. }
    rewrite exec_post_ok.
    iDestruct "Hpost2" as (rs0) "(Hps2 & %Hwf2 & %Hsnd2)".
    wp_apply (wp_binOpAll le _ op t e1 e2 (pret q) s2 rs0 with "[$He $Hret $Hps2]").
    iIntros (s3 lf3) "Hpost3".
    wp_auto.
    wp_if_destruct.
    2:{ wp_for_post. iApply "HΦ". by iApply exec_post_fail. }
    destruct (decide (null = null)) as [_|Hc]; last done.
    iDestruct "Hpost3" as (outs3) "(Hps3 & %HF)".
    iDestruct "Hps3" as (zs) "[Hzs Hzsp]".
    wp_apply (wp_slice_append with "[$Hys $Hcap $Hzs]").
    iIntros (so') "(Hys & Hcap & _)".
    wp_auto.
    wp_for_post.
    iFrame "Hs HΦ en e".
    iExists (word.add n (W64 1)), x, so', (ys ++ zs), (outs ++ outs3).
    iFrame "i p out Hys Hcap".
    replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
    iFrame "Hrest".
    iSplitL "Hysp Hzsp"; first by iApply (big_sepL2_app with "Hysp Hzsp").
    iPureIntro. split; first word. split.
    + apply paths_wf_app; first done.
      eapply binop_paths_wf; [|by apply (paths_wf_ret _ _ Hwf0)|done|done].
      by apply (paths_wf_grow _ _ Hwf0).
    + intros q' Hq'. rewrite (take_S_r _ _ q) // in Hq'.
      apply elem_of_app in Hq' as [Hq'|Hq'].
      * destruct (Hdone q' Hq') as (rs & Hrs & Hin).
        exists rs. split; first done.
        intros sq Hsq. destruct (Hin sq Hsq) as (r & H1 & H2 & H3 & H4).
        exists r. split_and!; [done|done|done|set_solver].
      * apply list_elem_of_singleton in Hq' as ->.
        exists rs0. split; first done.
        eapply binop_paths_in; [done|set_solver].
  - (* the loop is over *)
    assert (take (sint.nat n) ps0 = ps0) as Htake by (apply take_ge; word).
    rewrite Htake in Hdone.
    try wp_auto.
    iApply "HΦ". rewrite exec_post_ok.
    iExists outs. iFrame "Hys Hysp". iPureIntro. split; first done.
    by eapply exec_sound_binop.
Qed.
End proof.
