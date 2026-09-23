(** [checker.execIfs] (checker/exec.go): the [EIf] case of [exec].

    Runs the condition, then [execIf] on each of its paths, concatenating the
    results.

    Naming: the Go locals are [e], [en], [st], [fl], [ps], [out], [p], [fl2],
    [ps2], and the range loop's [i], so no Rocq variable here is called any
    of those (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_c.
From New.checker.fn Require Import heapUpdate execIf.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** What the loop has established for a prefix of the condition's paths. *)
Definition ifs_done (ct cf : cexpr) ρ (dn outs : list spath) : Prop :=
  ∀ p1, p1 ∈ dn → sort_of_vars (svars (pst p1)) (pret p1) = Some SBool ∧
                  ∃ qvs, qvs ⊆ outs ∧ if_ok ct cf ρ p1 qvs.

Lemma ifs_done_snoc ct cf ρ dn outs p1 qvs :
  ifs_done ct cf ρ dn outs →
  sort_of_vars (svars (pst p1)) (pret p1) = Some SBool →
  if_ok ct cf ρ p1 qvs →
  ifs_done ct cf ρ (dn ++ [p1]) (outs ++ qvs).
Proof.
  intros Hdn Hs Hok p2 [Hin|Hin]%elem_of_app.
  - destruct (Hdn p2 Hin) as (Hs2 & qv & Hsub & Hok2). split; first done.
    exists qv. split; last done. set_solver.
  - apply list_elem_of_singleton in Hin as ->. split; first done.
    exists qvs. split; last done. set_solver.
Qed.

Lemma wp_execIfs_aux (cc ct cf : cexpr) :
  (⊢ exec_like checker.exec cc) → (⊢ exec_like checker.exec ct) →
  (⊢ exec_like checker.exec cf) →
  ⊢ exec_like checker.execIfs (CEIf cc ct cf).
Proof.
  intros Hexc Hext Hexf.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iAssert (is_expr le (CEIf cc ct cf)) as "#He'"; first iExact "He".
  iDestruct "He" as (lcc la lb) "(#Hn & #Hc & #Ha & #Hb)".
  fold (is_expr lcc cc). fold (is_expr la ct). fold (is_expr lb cf).
  wp_auto.
  wp_apply (Hexc $! lcc lρ lst ρ sst with "[$Hst]").
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
      "%Hdone" ∷ ⌜ifs_done ct cf ρ (take (sint.nat k) pl) outs⌝ ∗
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
    wp_apply (wp_execIf _ _ _ _ cc ct cf (pret p0) ρ (pst p0) Hext Hexf
               with "[$Hst0]") as (sps2 lfl2) "Hpost2".
    { iFrame "#". iPureIntro. split_and!.
      - by apply (paths_wf_state _ _ Hwfpl).
      - eapply env_below_mono; last done. by apply (paths_wf_grow _ _ Hwfpl).
      - by apply (paths_wf_ret _ _ Hwfpl). }
    rewrite /execIf_post.
    try wp_auto.
    wp_if_destruct.
    2: { try wp_auto. wp_for_post. iApply "HΦ".
         destruct (decide (lfl2 = null)); [congruence|done]. }
    destruct (decide (null = null)) as [_|]; last congruence.
    iDestruct "Hpost2" as (qvs) "(Hq & %Hwfq & %Hsort & %Hok)".
    iDestruct "Hq" as (ys) "[Hys Hysp]".
    wp_apply (wp_slice_append so os sps2 ys (DfracOwn 1)
               with "[$Hos $Hcap $Hys]") as (so') "(Hos & Hcap & _)".
    wp_for_post.
    iFrame "HΦ Hxs en e".
    iExists (word.add k (W64 1)), x0, so', (os ++ ys), (outs ++ qvs).
    replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
    iFrame "i p out Hos Hcap Hrest".
    iSplitL "Hosp Hysp".
    { iApply (big_sepL2_app with "Hosp Hysp"). }
    iPureIntro. split_and!.
    + rewrite (take_S_r pl (sint.nat k) p0) //.
      apply ifs_done_snoc; [done|done|]. by destruct p0.
    + apply paths_wf_app; first done.
      eapply paths_wf_mono; last done.
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
    eapply exec_sound_if_gen; [exact Hsnd|exact Hwfpl| |].
    + intros p1 Hp1. by destruct (Hdone p1 Hp1).
    + intros p1 Hp1. by destruct (Hdone p1 Hp1).
  Unshelve. all: try apply _.
Qed.

Lemma wp_execIfs (c e1 e2 : cexpr) :
  (⊢ exec_like checker.exec c) → (⊢ exec_like checker.exec e1) → (⊢ exec_like checker.exec e2) →
  ⊢ exec_like checker.execIfs (CEIf c e1 e2).
Proof. apply wp_execIfs_aux. Qed.

End proof.
