(** The contract between the two halves of the postcondition check
    (checker/match.go, checker/check.go).

    [Verify] parses the postcondition into disjuncts ([parseDisjuncts]) and
    asks, for each path, whether some disjunct matches it ([checkDisjunct]).
    The two halves meet in [dj_interp], the assertion a parsed disjunct
    stands for:

    - the parsing side proves that a disjunct that parsed without failure
      entails the postcondition: [∀ V, dj_interp V dj ⊢ assn_interp V post];
    - the matching side proves that a successful [checkDisjunct] of path [p]
      against [dj] gives [path_sat_dj vars p dj]: the path's heap entails
      [dj_interp] at the caller's valuation, with [ret] the path's value.

    [Check] then chains [Analyze]'s path postcondition ([paths_post]) through
    these two to [post_interp]. *)
From New.checker Require Import prelude nodes disjunct.

Section verify_def.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** What a parsed disjunct asserts at valuation [V]: some values [W] for its
    declared pattern variables, each of its declared sort, under which all of
    its atoms hold. Indices no binder declared keep [V]'s value, exactly as
    [assn_interp] of the [CAExists] chain leaves them. *)
Definition dj_interp (V : valuation) (dj : cdisjunct) : iProp Σ :=
  (∃ W : nat → val,
     ⌜∀ n, d_pat_ok dj !! n = Some true →
           ∃ s, d_pats dj !! n = Some s ∧ has_sort (W n) s⌝ ∗
     ⌜∀ n, d_pat_ok dj !! n ≠ Some true → W n = vpat V n⌝ ∗
     [∗ list] a ∈ d_atoms dj, assn_interp (mkVal (vvar V) W (vret V)) a)%I.

(** Path [sp] satisfies disjunct [dj], for a caller whose declared logical
    variables have sorts [vars]: whenever the path is reached from the
    caller's valuation [θ] (the facts [paths_post] and [paths_wf] provide),
    its heap entails the disjunct at [θ], with [ret] the path's value. *)
Definition path_sat_dj (vars : list sort) (sp : spath) (dj : cdisjunct) : Prop :=
  ∀ (θ : nat → val) (V' : valuation),
    vars_sat θ vars →
    agree_below (length vars) (mkVal θ (λ _, uval) uval) V' →
    st_sat V' (pst sp) →
    wf_state (pst sp) →
    (length vars ≤ length (svars (pst sp)))%nat →
    vars_below (length (svars (pst sp))) (pret sp) →
    heap_interp V' (sheap (pst sp)) ⊢
      dj_interp (mkVal θ (λ _, uval) (teval V' (pret sp))) dj.

End verify_def.
