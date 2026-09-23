(** [checker.parseDisjuncts] (checker/match.go): parse every disjunct of a
    postcondition, left to right.

    Every disjunct that parsed without failure entails the whole
    postcondition: it entails the member of the top-level [∨] chain it was
    parsed from ([wp_parseDisjunct]), which entails the chain
    ([assn_disjuncts_sound]).

    Naming: the Go locals are [post], [out] and [a], and the range loop
    introduces [i], so no Rocq variable here is called any of those (see
    NOTES.md). *)
From New.checker Require Import prelude nodes disjunct verify_def parse_sound.
From New.checker.fn Require Import collectDisjuncts parseDisjunct.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The slice of [*disjunct] the function returns. *)
Definition is_disjuncts (s : slice.t) (djs : list cdisjunct) : iProp Σ :=
  (∃ lds : list loc, s ↦* lds ∗ own_slice_cap loc s (DfracOwn 1) ∗
                     [∗ list] ld;dj ∈ lds; djs, is_disjunct ld dj)%I.

(** [wp_slice_literal] hands back a one-element literal as [<[0:=y]> [z]]. *)
Lemma lit_singleton {A} (y z : A) : <[Z.to_nat (sint.Z (W64 0)) := y]> [z] = [y].
Proof. replace (Z.to_nat (sint.Z (W64 0))) with 0%nat by word. done. Qed.

Lemma wp_parseDisjuncts (lP : loc) (P : cassn) :
  {{{ is_pkg_init checker ∗ is_assn lP P }}}
    @! checker.parseDisjuncts #lP
  {{{ (s : slice.t) (djs : list cdisjunct), RET #s;
      is_disjuncts s djs ∗
      ⌜∀ dj, dj ∈ djs → d_fail dj = false → dj_entails dj P⌝ }}}.
Proof.
  wp_start as "#HP".
  wp_auto.
  wp_apply (wp_collectDisjuncts lP (Some P) with "[$]") as (sr) "Hr".
  iDestruct "Hr" as (las) "(Hsr & Hsrc & #Hlas)".
  iDestruct (big_sepL2_length with "Hlas") as %Hlen2.
  iDestruct (own_slice_len with "Hsr") as %Hlen.
  iAssert (∃ (n : w64) (lcur : loc) (so : slice.t) (lds : list loc)
             (djs : list cdisjunct),
      "i" ∷ i_ptr ↦ n ∗
      "a" ∷ a_ptr ↦ lcur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hso" ∷ so ↦* lds ∗
      "Hsoc" ∷ own_slice_cap loc so (DfracOwn 1) ∗
      "Hds" ∷ ([∗ list] ld;dj ∈ lds; djs, is_disjunct ld dj) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length las⌝ ∗
      "%Hsnd" ∷ ⌜∀ dj, dj ∈ djs → d_fail dj = false → dj_entails dj P⌝)%I
    with "[i a out]" as "HI".
  { iExists _, _, slice.nil, [], []. iFrame "i a out".
    iDestruct (own_slice_nil (V:=loc) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=loc)) as "$".
    iSplit; first by iApply big_sepL2_nil.
    iPureIntro. split; first word. intros dj Hin. by apply elem_of_nil in Hin. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat n) as lx.
    list_elem (oassn_disjuncts (Some P)) (sint.nat n) as ox.
    iDestruct (big_sepL2_lookup with "Hlas") as "#Hox"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsr]") as "Hsr".
    { word. }
    { done. }
    try wp_auto.
    wp_apply (wp_parseDisjunct with "[$]") as (ld dj) "[Hdj %Hdj]".
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%sl [Hsl _]".
    rewrite lit_singleton. try wp_auto.
    wp_apply (wp_slice_append so lds _ [ld] (DfracOwn 1)
               with "[$Hso $Hsoc $Hsl]") as (so') "(Hso & Hsoc & _)".
    try wp_auto.
    wp_for_post.
    iFrame "HΦ Hsr Hsrc".
    iExists (word.add n (W64 1)), lx, so', (lds ++ [ld]), (djs ++ [dj]).
    iFrame "i a out Hso Hsoc".
    iSplitL.
    { iApply (big_sepL2_app with "Hds"). by iFrame "Hdj". }
    iPureIntro. split; first word.
    intros dj' Hin Hf.
    apply elem_of_app in Hin as [Hin|Hin]; first by apply Hsnd.
    apply list_elem_of_singleton in Hin as ->.
    destruct (Hdj Hf) as (y & -> & Hent).
    intros ext' ffi' ffi_interp' ffi_sem' Σ' hG' sem' V.
    etrans; first apply (Hent _ _ _ _ _ _ _).
    apply assn_disjuncts_sound.
    by eapply list_elem_of_lookup_2.
  - try wp_auto.
    iApply "HΦ". iFrame. done.
  Unshelve. all: try apply _.
Qed.

End proof.
