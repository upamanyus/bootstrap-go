(** [checker.firstUnresolved] (checker/match.go): the first points-to atom
    phase 1 left unresolved, reported in [matchHeap]'s failure. Only safety
    matters here: the result is a diagnostic nothing reads back.

    Naming: the Go locals are [d], [done], [i] and [at], so no Rocq variable
    here is called any of those (see NOTES.md); since the Go function has its
    own [i], the range loop's index is allocated by hand. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import countPointsTo.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_firstUnresolved (ld : loc) (dj : cdisjunct) (sdn : slice.t) (dn : list bool) :
  {{{ is_pkg_init checker ∗ is_disjunct_ro ld dj ∗ sdn ↦* dn ∗
      ⌜length dn = length (d_atoms dj)⌝ }}}
    @! checker.firstUnresolved #ld #sdn
  {{{ (lat : loc), RET #lat; sdn ↦* dn }}}.
Proof.
  wp_start as "(#Hdj & Hdn & %Hlen)".
  iDestruct "Hdj" as (sp sok sa lf las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hsa") as %Hlena.
  iDestruct (own_slice_len with "Hdn") as %Hlend.
  wp_auto.
  wp_alloc ridx as "Hridx".
  wp_auto.
  iAssert (∃ (k : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ k ∗
      "Hridx" ∷ ridx ↦ k ∗
      "at" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length las⌝)%I
    with "[i Hridx at]" as "HI".
  { iFrame. iPureIntro. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat k) as lcur'.
    list_elem (d_atoms dj) (sint.nat k) as acur.
    iDestruct (big_sepL2_lookup with "Has") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsa]"); [word|done|].
    iIntros "_".
    iDestruct (is_assn_node with "Hcur") as (lL lR lX lY) "(_ & #Hnode & _)".
    wp_auto.
    rewrite is_pts_code.
    destruct (is_pts acur).
    + wp_auto.
      list_elem dn (sint.nat k) as dcur.
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hdn]"); [word|done|].
      iIntros "Hdn".
      destruct dcur.
      * wp_auto. wp_for_post. iFrame. iPureIntro. word.
      * wp_auto. wp_for_post. iApply "HΦ". iFrame.
    + wp_auto. wp_for_post. iFrame. iPureIntro. word.
  - try wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
