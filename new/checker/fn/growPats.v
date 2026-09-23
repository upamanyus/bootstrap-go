(** the [growPats] method of the postcondition matcher's [disjunct]
    (checker/match.go): extend [pats]/[patOk] with default entries until
    index [n] is addressable.

    Naming: the Go locals are [d] and [n], so no Rocq variable here is called
    either (see NOTES.md). *)
From New.checker Require Import prelude nodes disjunct.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** Pad a list with [x] until index [k] is in range. *)
Definition pad {A} (xs : list A) (x : A) (k : nat) : list A :=
  xs ++ replicate (S k - length xs) x.

Lemma pad_length {A} (xs : list A) (x : A) (k : nat) :
  length (pad xs x k) = (length xs `max` S k)%nat.
Proof. rewrite /pad length_app length_replicate. lia. Qed.

Lemma pad_done {A} (xs : list A) (x : A) (k : nat) :
  (k < length xs)%nat → pad xs x k = xs.
Proof.
  intros Hk. rewrite /pad.
  replace (S k - length xs)%nat with 0%nat by lia. by rewrite app_nil_r.
Qed.

(** One iteration of the loop does not change the padded result. *)
Lemma pad_step {A} (xs : list A) (x : A) (k : nat) :
  (length xs ≤ k)%nat → pad (xs ++ [x]) x k = pad xs x k.
Proof.
  intros Hle. rewrite /pad length_app /=.
  destruct (S k - length xs)%nat as [|j] eqn:Hj; first lia.
  replace (S k - (length xs + 1))%nat with j by lia.
  by rewrite -app_assoc.
Qed.

(** The Gallina mirror: both fields are extended, so the length agreement
    [sort_env_wf] needs is preserved. *)
Definition grow_pats (dj : cdisjunct) (k : nat) : cdisjunct :=
  mkDisjunct (pad (d_pats dj) SInt k) (pad (d_pat_ok dj) false k)
             (d_atoms dj) (d_fail dj).

Lemma grow_pats_wf (dj : cdisjunct) (k : nat) :
  length (d_pats dj) = length (d_pat_ok dj) →
  length (d_pats (grow_pats dj k)) = length (d_pat_ok (grow_pats dj k)).
Proof. intros Heq. rewrite /grow_pats /= !pad_length Heq //. Qed.

(** Index [k] really is addressable afterwards. *)
Lemma grow_pats_lookup (dj : cdisjunct) (k : nat) :
  (k < length (d_pats (grow_pats dj k)))%nat ∧
  (k < length (d_pat_ok (grow_pats dj k)))%nat.
Proof. rewrite /grow_pats /= !pad_length. lia. Qed.

Lemma wp_disjunct__growPats (ld : loc) (dj : cdisjunct) (m : w64) :
  {{{ is_pkg_init checker ∗ is_disjunct ld dj }}}
    ld @! (go.PointerType checker.disjunct) @! "growPats" #m
  {{{ RET #(); is_disjunct ld (grow_pats dj (uint.nat m)) }}}.
Proof using All.
  wp_start as "Hdj".
  iDestruct "Hdj"
    as (sp0 sok0 sa lf las) "(Hs & Hp & Hpc & Hok & Hokc & Ha & Hac & #Hats & %Hlen0 & %Hf)".
  wp_auto.
  iAssert (∃ (ps : list sort) (ok : list bool) (sp sok : slice.t),
      "Hs" ∷ ld ↦ checker.disjunct.mk sp sok sa lf ∗
      "Hp" ∷ sp ↦* (sort_code <$> ps) ∗
      "Hpc" ∷ own_slice_cap w64 sp (DfracOwn 1) ∗
      "Hok" ∷ sok ↦* ok ∗
      "Hokc" ∷ own_slice_cap bool sok (DfracOwn 1) ∗
      "%Hlen" ∷ ⌜length ps = length ok⌝ ∗
      "%Hgp" ∷ ⌜pad ps SInt (uint.nat m) = pad (d_pats dj) SInt (uint.nat m)⌝ ∗
      "%Hgo" ∷ ⌜pad ok false (uint.nat m) = pad (d_pat_ok dj) false (uint.nat m)⌝)%I
    with "[Hs Hp Hpc Hok Hokc]" as "HI".
  { iExists (d_pats dj), (d_pat_ok dj), sp0, sok0. iFrame. done. }
  wp_for "HI".
  iDestruct (own_slice_len with "Hp") as %[Hsl Hsl0].
  rewrite length_fmap in Hsl.
  wp_if_destruct.
  - (* the loop body: append a default entry to each slice *)
    assert (length ps ≤ uint.nat m)%nat as Hle by word.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl1 Hsl1c]".
    try wp_auto.
    wp_apply (wp_slice_append sp (sort_code <$> ps) _ [sort_code SInt] (DfracOwn 1)
               with "[$Hp $Hpc $Hsl1]") as (sp') "(Hp' & Hpc' & _)".
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl2 Hsl2c]".
    try wp_auto.
    wp_apply (wp_slice_append sok ok _ [false] (DfracOwn 1)
               with "[$Hok $Hokc $Hsl2]") as (sok') "(Hok' & Hokc' & _)".
    try wp_auto.
    wp_for_post.
    iFrame "Ha Hac HΦ d n".
    iExists (ps ++ [SInt]), (ok ++ [false]), sp', sok'.
    rewrite fmap_app /=. iFrame.
    iPureIntro. rewrite !length_app Hlen.
    split; first done.
    rewrite !pad_step //; lia.
  - (* the loop is done: the slices are exactly the padded ones *)
    try wp_auto.
    assert (uint.nat m < length ps)%nat as Hgt by word.
    rewrite pad_done in Hgp; last done.
    rewrite pad_done in Hgo; last lia.
    iApply "HΦ".
    iExists sp, sok, sa, lf, las.
    rewrite /grow_pats /= -Hgp -Hgo. iFrame "Hs Hp Hpc Hok Hokc Ha Hac Hats".
    iPureIntro. split; [done|done].
  Unshelve.
  all: try apply _.
Qed.

End proof.
