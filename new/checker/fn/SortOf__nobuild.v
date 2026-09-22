(** UNFINISHED -- parked out of the build (the Makefile skips
    [*__nobuild.v]).

    The script is essentially complete, but the single Löb-induction proof
    over all eighteen term shapes produces a proof term too large to check
    (87519 evars, over 20 minutes, then a syntax error from the truncated
    tail). The fix is the one the plan warns about for long Iris files: split
    it into one lemma per term shape, passing the Löb hypothesis explicitly
    as a section hypothesis, and have the top-level lemma dispatch. See
    new/checker/NOTES.md.

    [new/checker/fn/atomWellSorted.v] currently assumes this file's
    specification as a section hypothesis; discharging it is the first thing
    to do once this compiles. *)
(** [checker.SortOf] (checker/sorts.go): the sort of a term over a list of
    logical-variable sorts.

    Note on naming: no Rocq variable here may be called [vars], [t] or [e] --
    those are the Go function's own locals and [wp_auto] derives Rocq
    identifiers from them. *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import sortOfEnv.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** [SortOf] builds a [sortEnv] with only [vars] populated, which is exactly
    [vars_env]. *)
Lemma wp_SortOf (sv : slice.t) (lterm : loc) (vl : list sort) (oty : option term) :
  {{{ is_pkg_init checker ∗ sv ↦*□ (sort_code <$> vl) ∗ is_oterm lterm oty }}}
    @! checker.SortOf #sv #lterm
  {{{ RET (#(osort_code (osort_of (vars_env vl) oty)),
           #(osort_ok (osort_of (vars_env vl) oty)));
      True }}}.
Proof.
  wp_start as "[#Hsl #Hot]".
  wp_auto.
  wp_alloc lenv as "Hlenv".
  wp_auto.
  iPersist "Hlenv".
  wp_apply (wp_sortOfEnv_aux DfracDiscarded lenv (vars_env vl) sv slice.nil slice.nil
              lterm oty (vars_env_wf vl) with "[$Hlenv $Hsl $Hot]").
  { iSplitL; iApply own_slice_nil. }
  iIntros "_". by iApply "HΦ".
Qed.

End proof.
