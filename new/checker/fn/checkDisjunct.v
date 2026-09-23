(** [checker.checkDisjunct] (checker/match.go): does path [p] satisfy the
    parsed disjunct [d]? Phase 0 ([checkSorts]), phase 1 ([matchHeap]) and
    phase 2 ([checkPure]); a [nil] answer gives [path_sat_dj] through
    [match_path_sat] (match_sound.v).

    Naming: the Go locals are [p], [d], [vars], [fl], [subst] and [fl2], so
    no Rocq variable in the proof is called any of those (see NOTES.md). The
    statement's binder [p] is renamed [pth] below; it is alpha-equivalent. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro verify_def match_sound.
From New.checker.fn Require Import instantiate checkSorts matchHeap checkPure.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma is_subst_replicate_None (k : nat) :
  ⊢ [∗ list] li;oi ∈ replicate k null; replicate k (None : option term), is_oterm li oi.
Proof. induction k as [|k IH]; simpl; first done. iSplit; first done. iApply IH. Qed.

Lemma wp_checkDisjunct (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (sv : slice.t) (vl : list sort) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗ is_sorts sv vl }}}
    @! checker.checkDisjunct #pth #ld #sv
  {{{ (lf : loc), RET #lf;
      is_path pth sp ∗ ⌜lf = null → d_fail dj = false ∧ path_sat_dj vl sp dj⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & #Hsv)".
  iPoseProof "Hdj" as "Hdj'".
  iDestruct "Hdj'" as (sp' sok sa lfl las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (own_slice_len with "Hsp") as %Hlenp. rewrite length_fmap in Hlenp.
  iDestruct "Hpath" as "[#Hret Hst]".
  iDestruct "Hst" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
  iDestruct (typed_pointsto_not_null with "Hstl") as %Hstnn.
  iAssert (is_path pth sp) with "[Hstl Hheap Hcond]" as "Hpath".
  { iFrame "Hret". iExists hs, cs, vs. iFrame "∗#". }
  wp_auto.
  wp_if_destruct.
  2:{ (* the disjunct is malformed *)
    try wp_auto. iApply "HΦ". iFrame. iPureIntro. done. }
  assert (d_fail dj = false) as Hdf by naive_solver.
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  wp_apply (wp_checkSorts pth sp ld dj sv vl with "[$Hpath $Hdj $Hsv]").
  iIntros (lf1) "[Hpath %Hsc]".
  wp_auto.
  wp_if_destruct.
  2:{ (* ill-sorted *)
    try wp_auto. iApply "HΦ". iFrame. iPureIntro. done. }
  specialize (Hsc eq_refl).
  wp_apply wp_slice_make2 as (ss) "[Hss _]"; first (iPureIntro; word).
  try wp_auto.
  iAssert (is_subst ss (replicate (length (d_pats dj)) None)) with "[Hss]" as "Hsub".
  { iExists (replicate (length (d_pats dj)) null).
    replace (Z.to_nat (sint.Z sp'.(slice.len))) with (length (d_pats dj)) by lia.
    iFrame "Hss". iApply is_subst_replicate_None. }
  wp_apply (wp_matchHeap pth sp ld dj ss with "[$Hpath $Hsub $Hdj]").
  iIntros (lf2) "(Hpath & %σ & Hsub & %Hm)".
  wp_auto.
  wp_if_destruct.
  2:{ (* phase 1 failed *)
    try wp_auto. iApply "HΦ". iFrame. iPureIntro. done. }
  destruct (Hm eq_refl) as (us & dn & Hinv & Hund).
  wp_apply (wp_checkPure pth sp ld dj ss σ with "[$Hpath $Hsub $Hdj]").
  iIntros (lf3) "(Hpath & Hsub & %Hpure)".
  try wp_auto.
  iApply "HΦ". iFrame. iPureIntro. intros Hnull. split; first done.
  eapply match_path_sat; [done| |exact Hinv|done|by apply Hpure].
  done.
Qed.

End proof.
