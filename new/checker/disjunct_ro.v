(** A parsed disjunct, frozen.

    [is_disjunct] owns the disjunct's slices because parsing mutates them
    ([growPats], [flatten]). Once [parseDisjuncts] has returned, nothing
    changes a disjunct again: [Verify] only reads it, once per path, and
    [checkSorts] hands its [pats]/[patOk] to [sortOfEnv] next to the
    (persistent) declared sort table, which needs a single fraction for all
    of them. So [Verify] freezes each disjunct into this persistent form. *)
From New.checker Require Import prelude nodes disjunct.

Section disjunct_ro.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

Definition is_disjunct_ro (l : loc) (dj : cdisjunct) : iProp Σ :=
  (∃ (sp sok sa : slice.t) (lf : loc) (las : list loc),
      l ↦□ checker.disjunct.mk sp sok sa lf ∗
      sp ↦*□ (sort_code <$> d_pats dj) ∗
      sok ↦*□ d_pat_ok dj ∗
      sa ↦*□ las ∗
      ([∗ list] la;x ∈ las; d_atoms dj, is_assn la x) ∗
      ⌜length (d_pats dj) = length (d_pat_ok dj)⌝ ∗
      ⌜lf = null ↔ d_fail dj = false⌝)%I.

#[global] Instance is_disjunct_ro_persistent l dj : Persistent (is_disjunct_ro l dj).
Proof. apply _. Qed.

Lemma is_disjunct_freeze l dj : is_disjunct l dj ==∗ is_disjunct_ro l dj.
Proof.
  iIntros "H".
  iDestruct "H" as (sp sok sa lf las) "(Hl & Hp & _ & Hok & _ & Ha & _ & #Has & % & %)".
  iPersist "Hl Hp Hok Ha". iModIntro.
  iExists sp, sok, sa, lf, las. iFrame "#%".
Qed.

Lemma is_disjunct_ro_wf l dj vars rs rok :
  is_disjunct_ro l dj -∗ ⌜sort_env_wf (disjunct_env vars dj rs rok)⌝.
Proof.
  iIntros "H". iDestruct "H" as (?????) "(_&_&_&_&_&%&_)".
  iPureIntro. by rewrite /sort_env_wf /disjunct_env /=.
Qed.

End disjunct_ro.
