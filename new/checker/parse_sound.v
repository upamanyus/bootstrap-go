(** Semantics of the parsing half of the postcondition check
    (checker/match.go: [parseDisjunct], [parseDisjuncts]).

    [parseDisjunct] peels a chain of [AExists] binders off a disjunct,
    recording each binder's sort in [pats]/[patOk], and then flattens the
    separating conjunction underneath into [atoms]. The invariant of that
    loop is [binders_interp]: the binders declared so far, existentially
    quantified exactly as [dj_interp] quantifies them, over the remaining
    body. This file proves that each step of the parse preserves the
    entailment towards the original assertion, and that the flattened atoms
    entail the body, so that a disjunct that parsed without failure entails
    the assertion it was parsed from. *)
From New.checker Require Import prelude nodes disjunct verify_def.
From New.checker.fn Require Import growPats flatten collectDisjuncts.

(** * Extensionality of the denotations *)



(** The binder a parse step records. *)
Definition bind_pat (dj : cdisjunct) (k : nat) (s : sort) : cdisjunct :=
  mkDisjunct (<[k:=s]> (d_pats dj)) (<[k:=true]> (d_pat_ok dj)) (d_atoms dj) (d_fail dj).

Lemma lookup_pad_Some {A} (xs : list A) (x y : A) (k m : nat) :
  pad xs x k !! m = Some y → xs !! m = Some y ∨ y = x.
Proof.
  rewrite /pad. intros Hm.
  rewrite lookup_app_Some in Hm. destruct Hm as [?|[_ Hr]]; first by left.
  right. by apply lookup_replicate in Hr as [-> _].
Qed.

Lemma lookup_pad_l {A} (xs : list A) (x y : A) (k m : nat) :
  xs !! m = Some y → pad xs x k !! m = Some y.
Proof. rewrite /pad. apply lookup_app_l_Some. Qed.

Section parse_sound.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma teval_ext V V' t :
  (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
  teval V t = teval V' t.
Proof.
  intros Hv Hp Hr. induction t; simpl;
    try (by apply Hv); try (by rewrite Hp); try (by rewrite Hr);
    try (by rewrite IHt //);
    try (by rewrite IHt1 // IHt2 //);
    try (by rewrite IHt1 // IHt2 // IHt3 //);
    done.
Qed.

Lemma assn_interp_ext_1 V V' a :
  (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
  assn_interp V a ⊢ assn_interp V' a.
Proof.
  revert V V'. induction a as [|p IHp q IHq|p IHp q IHq|k s p IHp|t|x y];
    intros V V' Hv Hp Hr; simpl.
  - done.
  - iIntros "[H1 H2]". iSplitL "H1"; [by iApply IHp|by iApply IHq].
  - iIntros "[H|H]"; [iLeft; by iApply IHp|iRight; by iApply IHq].
  - iIntros "(%w & %Hs & H)". iExists w. iSplit; first done.
    iApply (IHp with "H"); simpl; [done| |done].
    intros m. destruct (decide (m = k)); auto.
  - rewrite (teval_ext V V' t) //.
  - rewrite (teval_ext V V' x) // (teval_ext V V' y) //.
Qed.

Lemma assn_interp_ext V V' a :
  (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
  assn_interp V a ⊣⊢ assn_interp V' a.
Proof.
  intros. iSplit; iApply assn_interp_ext_1; eauto.
Qed.

(** The loop invariant of [parseDisjunct]: the binders declared so far over
    the remaining body [b]. *)
Definition binders_interp (V : valuation) (dj : cdisjunct) (b : cassn) : iProp Σ :=
  (∃ W : nat → val,
     ⌜∀ n, d_pat_ok dj !! n = Some true →
           ∃ s, d_pats dj !! n = Some s ∧ has_sort (W n) s⌝ ∗
     ⌜∀ n, d_pat_ok dj !! n ≠ Some true → W n = vpat V n⌝ ∗
     assn_interp (mkVal (vvar V) W (vret V)) b)%I.

(** Before any binder: the body itself. *)
Lemma binders_interp_init V dj b :
  d_pat_ok dj = [] → binders_interp V dj b ⊢ assn_interp V b.
Proof.
  intros Hok. iIntros "(%W & _ & %HW & H)".
  iApply (assn_interp_ext with "H"); simpl; [done| |done].
  intros n. symmetry. apply HW. rewrite Hok. done.
Qed.

(** One binder peeled: [growPats] and then the two stores. *)
Lemma binders_interp_step V dj k s p :
  length (d_pats dj) = length (d_pat_ok dj) →
  d_pat_ok (grow_pats dj k) !! k ≠ Some true →
  binders_interp V (bind_pat (grow_pats dj k) k s) p ⊢
  binders_interp V dj (CAExists k s p).
Proof.
  intros Hlen Hnot.
  destruct (grow_pats_lookup dj k) as [Hk1 Hk2].
  rewrite /grow_pats /= in Hnot Hk1 Hk2.
  rewrite /binders_interp /bind_pat /grow_pats /=.
  iIntros "(%W & %H1 & %H2 & H)".
  iExists (λ m, if decide (m = k) then vpat V m else W m).
  iSplit; [iPureIntro|iSplit; [iPureIntro|]].
  - intros m Hm. destruct (decide (m = k)) as [->|Hne].
    { exfalso. apply Hnot. by apply lookup_pad_l. }
    destruct (H1 m) as (s' & Hs' & Hsort).
    { rewrite list_lookup_insert_ne; last congruence.
      by apply lookup_pad_l. }
    exists s'. split; last done.
    rewrite list_lookup_insert_ne in Hs'; last congruence.
    assert (m < length (d_pats dj))%nat as Hlt.
    { rewrite Hlen. by apply lookup_lt_Some in Hm. }
    rewrite /pad lookup_app_l // in Hs'.
  - intros m Hm. destruct (decide (m = k)) as [->|Hne]; first done.
    apply H2. rewrite list_lookup_insert_ne; last congruence.
    intros Hp. destruct (lookup_pad_Some _ _ _ _ _ Hp) as [?|?]; [done|congruence].
  - simpl. iExists (W k).
    destruct (H1 k) as (s' & Hs' & Hsort).
    { by rewrite list_lookup_insert_eq. }
    rewrite list_lookup_insert_eq in Hs'; last done. injection Hs' as <-.
    iSplit; first done.
    iApply (assn_interp_ext with "H"); simpl; [done| |done].
    intros m. destruct (decide (m = k)) as [->|?]; done.
Qed.

Lemma assn_flatten_sound V b ats :
  assn_flatten b = Some ats → ([∗ list] a ∈ ats, assn_interp V a) ⊢ assn_interp V b.
Proof.
  revert ats. induction b; intros ats Hf; simpl in Hf.
  - by iIntros "_".
  - destruct (assn_flatten b1) as [l1|] eqn:H1; last done.
    destruct (assn_flatten b2) as [l2|] eqn:H2; last done.
    injection Hf as <-. rewrite big_sepL_app.
    iIntros "[A B]". iSplitL "A"; [by iApply IHb1|by iApply IHb2].
  - done.
  - done.
  - injection Hf as <-. simpl. by iIntros "[$ _]".
  - injection Hf as <-. simpl. by iIntros "[$ _]".
Qed.

(** The flattened body: [dj_interp] of the finished disjunct. *)
Lemma dj_interp_flatten V dj b ats :
  d_atoms dj = [] → assn_flatten b = Some ats →
  dj_interp V (dj_atoms dj ats) ⊢ binders_interp V dj b.
Proof.
  intros Hat Hf. iIntros "(%W & %H1 & %H2 & H)".
  iExists W. rewrite /dj_atoms /= Hat /=.
  iSplit; first done. iSplit; first done.
  by iApply assn_flatten_sound.
Qed.

(** The whole postcondition: [collectDisjuncts] flattens the top-level [∨]
    chain, and each of its members entails the chain. *)
Lemma assn_disjuncts_sound V post a :
  Some a ∈ assn_disjuncts post → assn_interp V a ⊢ assn_interp V post.
Proof.
  induction post; simpl; intros Hin;
    try (apply list_elem_of_singleton in Hin; injection Hin as ->; done).
  apply elem_of_app in Hin as [Hin|Hin].
  - iIntros "H". iLeft. by iApply IHpost1.
  - iIntros "H". iRight. by iApply IHpost2.
Qed.

End parse_sound.

(** [binders_interp] entails an assertion, in any ghost state: the invariant of
    [parseDisjunct]'s loop, which ends in [dj_entails] (verify_def.v). *)
Definition binders_entails {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
    {ffi_sem : ffi_semantics ext ffi} (dj : cdisjunct) (b y : cassn) : Prop :=
  ∀ Σ (hG : heapGS Σ) (sem : go.Semantics) (package_sem : checker.Assumptions),
    ∀ V, binders_interp V dj b ⊢ assn_interp V y.
