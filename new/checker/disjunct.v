(** The postcondition matcher's parsed disjunct (checker/match.go).

    A disjunct is one arm of the top-level disjunction of a postcondition:
    the declared sorts of its pattern variables (indexed by the [AExists]
    [Var] field, with [patOk] marking the indices a binder actually declared)
    together with the flat list of the atoms of its separating conjunction.

    Unlike the [Assn]/[Term] nodes it points at, a [disjunct] is *mutated*:
    [growPats] extends [pats]/[patOk] and [flatten] extends [atoms], both by
    [append]. So [is_disjunct] owns its three slices -- and their capacities,
    which is what [append] consumes -- while the [Assn] nodes inside stay
    persistent. *)
From New.checker Require Import prelude nodes.

(** * The mirror

    [d_fail] records only *whether* the disjunct is malformed: the [*Failure]
    the Go code stores there is a diagnostic that nothing reads back. *)
Record cdisjunct := mkDisjunct {
  d_pats : list sort;
  d_pat_ok : list bool;
  d_atoms : list cassn;
  d_fail : bool;
}.

(** The sort environment a disjunct induces on a path: the path's logical
    variables, the disjunct's pattern variables, and the sort of the path's
    return term. This is the [sortEnv] that [checkDisjunct] builds. *)
Definition disjunct_env (vars : list sort) (dj : cdisjunct)
    (rs : sort) (rok : bool) : sort_env :=
  mkSortEnv vars (d_pats dj) (d_pat_ok dj) rs rok.

Section disjunct.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

(** The [pats]/[patOk] length agreement is an invariant of the Go struct --
    [growPats] is the only thing that changes either length, and it extends
    both together -- and it is exactly [sort_env_wf], which [sortOfEnv] needs
    because it indexes [patOk] after bounds-checking against [pats]. Carrying
    it here means every caller gets it for free. *)
Definition is_disjunct (l : loc) (dj : cdisjunct) : iProp Σ :=
  (∃ (sp sok sa : slice.t) (lf : loc) (las : list loc),
      l ↦ checker.disjunct.mk sp sok sa lf ∗
      sp ↦* (sort_code <$> d_pats dj) ∗
      own_slice_cap w64 sp (DfracOwn 1) ∗
      sok ↦* d_pat_ok dj ∗
      own_slice_cap bool sok (DfracOwn 1) ∗
      sa ↦* las ∗
      own_slice_cap loc sa (DfracOwn 1) ∗
      ([∗ list] la;x ∈ las; d_atoms dj, is_assn la x) ∗
      ⌜length (d_pats dj) = length (d_pat_ok dj)⌝ ∗
      ⌜lf = null ↔ d_fail dj = false⌝)%I.

Lemma is_disjunct_wf l dj vars rs rok :
  is_disjunct l dj -∗ ⌜sort_env_wf (disjunct_env vars dj rs rok)⌝.
Proof.
  iIntros "H". iDestruct "H" as (?????) "(_&_&_&_&_&_&_&_&%&_)".
  iPureIntro. by rewrite /sort_env_wf /disjunct_env /=.
Qed.

Lemma is_disjunct_not_null l dj : is_disjunct l dj -∗ ⌜l ≠ null⌝.
Proof.
  iIntros "H". iDestruct "H" as (?????) "(H&_)".
  iApply (typed_pointsto_not_null with "H").
Qed.

End disjunct.
