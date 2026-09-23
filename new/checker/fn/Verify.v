(** [checker.Verify] (checker/check.go): every path satisfies some disjunct
    of the postcondition.

    The postcondition is parsed once ([parseDisjuncts]) and each parsed
    disjunct frozen ([is_disjunct_freeze]), since from then on it is only
    read, once per path ([anyDisjunct]). A nil result then says that every
    path satisfies a disjunct that parsed without failure, and such a
    disjunct entails the postcondition.

    Naming: the Go locals are [paths], [vars], [post], [ds], [pi] and [p],
    and the range loop introduces [i], so no Rocq variable in the working
    lemma is called any of those (see NOTES.md); [wp_Verify] restates it in
    the intended form. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro verify_def.
From New.checker.fn Require Import parseDisjuncts anyDisjunct.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** What a path needs from the postcondition. *)
Definition path_ok (vs : list sort) (P : cassn) (sp : spath) : Prop :=
  ∃ dj, d_fail dj = false ∧ path_sat_dj vs sp dj ∧ dj_entails dj P.

Lemma big_disjunct_freeze (lds : list loc) (djs : list cdisjunct) :
  ([∗ list] ld;dj ∈ lds; djs, is_disjunct ld dj) ==∗
  [∗ list] ld;dj ∈ lds; djs, is_disjunct_ro ld dj.
Proof.
  revert djs. induction lds as [|ld lds IH]; intros [|dj djs]; simpl;
    try (by iIntros "H").
  iIntros "[H Hs]". iMod (is_disjunct_freeze with "H") as "$".
  by iApply IH.
Qed.

Lemma is_disjuncts_freeze sd djs : is_disjuncts sd djs ==∗ is_disjuncts_ro sd djs.
Proof.
  iIntros "H". iDestruct "H" as (lds) "(Hs & _ & Hl)".
  iPersist "Hs".
  iMod (big_disjunct_freeze with "Hl") as "Hl".
  iModIntro. iExists lds. iFrame "Hs Hl".
Qed.

Lemma wp_Verify_aux (sps : slice.t) (ps : list spath) (svs : slice.t) (vs : list sort)
      (lP : loc) (P : cassn) :
  {{{ is_pkg_init checker ∗ is_paths sps ps ∗ is_sorts svs vs ∗ is_assn lP P }}}
    @! checker.Verify #sps #svs #lP
  {{{ (lf : loc), RET #lf; ⌜lf = null → ∀ sp, sp ∈ ps → path_ok vs P sp⌝ }}}.
Proof.
  wp_start as "(Hps & #Hvs & #HP)".
  iDestruct "Hps" as (xs) "[Hsps Hxs]".
  iDestruct (big_sepL2_length with "Hxs") as %Hlen2.
  iDestruct (own_slice_len with "Hsps") as %Hlen.
  wp_auto.
  wp_apply (wp_parseDisjuncts with "[$HP]") as (sd djs) "[Hds %Hsnd]".
  iMod (is_disjuncts_freeze with "Hds") as "#Hds".
  try wp_auto.
  iAssert (∃ (n pin : w64) (pcur : checker.Path.t),
      "i" ∷ i_ptr ↦ n ∗
      "pi" ∷ pi_ptr ↦ pin ∗
      "p" ∷ p_ptr ↦ pcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length xs⌝ ∗
      "%Hok" ∷ ⌜∀ (k : nat) sp, (k < sint.nat n)%nat → ps !! k = Some sp →
                path_ok vs P sp⌝)%I
    with "[i pi p]" as "HI".
  { iFrame. iPureIntro. split; first word. intros k sp Hk. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat n) as x.
    list_elem ps (sint.nat n) as sp.
    iDestruct (big_sepL2_lookup_acc with "Hxs") as "[Hp Hxs]"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsps]") as "Hsps".
    { word. }
    { done. }
    try wp_auto.
    wp_apply (wp_anyDisjunct x sp sd djs svs vs with "[$Hp $Hds $Hvs]")
      as (b) "[Hp %Hb]".
    iDestruct ("Hxs" with "Hp") as "Hxs".
    destruct b.
    + (* this path is fine: on to the next *)
      try wp_auto.
      wp_for_post.
      iFrame. iPureIntro. split; first word.
      intros k sp' Hk Hsp'.
      destruct (decide (k = sint.nat n)) as [->|Hne].
      * rewrite Hsp_lookup in Hsp'. injection Hsp' as <-.
        destruct (Hb eq_refl) as (dj & Hin & Hf & Hsat).
        exists dj. split; first done. split; first done.
        by apply Hsnd.
      * apply (Hok k); [word|done].
    + (* no disjunct matches this path *)
      try wp_auto.
      wp_alloc lfail as "Hfail".
      iDestruct (typed_pointsto_not_null with "Hfail") as %Hnn.
      try wp_auto.
      wp_for_post.
      iApply "HΦ". iPureIntro. intros Hnull. congruence.
  - (* every path has been checked *)
    try wp_auto.
    iApply "HΦ". iPureIntro. intros _ sp Hin.
    apply list_elem_of_lookup in Hin as [k Hk].
    apply (Hok k); last done.
    apply lookup_lt_Some in Hk. word.
Qed.

Lemma wp_Verify (s : slice.t) (ps : list spath) (sv : slice.t) (vars : list sort)
      (lpost : loc) (post : cassn) :
  {{{ is_pkg_init checker ∗ is_paths s ps ∗ is_sorts sv vars ∗ is_assn lpost post }}}
    @! checker.Verify #s #sv #lpost
  {{{ (lf : loc), RET #lf;
      ⌜lf = null → ∀ sp, sp ∈ ps → path_ok vars post sp⌝ }}}.
Proof. apply wp_Verify_aux. Qed.

End proof.
