(** The specification shared by [exec] and every per-case function it
    dispatches to (checker/exec.go).

    Each of [execInt], [execLet], ..., [execExcDo] has [exec]'s signature
    [(e *Expr, en *env, st *State) ([]Path, *Failure)], so one specification
    template, [exec_like], covers all of them: given the input tree, the
    environment and the state, a [nil] failure means the returned slice holds
    a list of paths that is well-formed and sound for the expression
    ([exec_sound], exec_spec.v). A non-[nil] failure promises nothing.

    The input state is consumed: a result path may share it (that is what
    [onePath] does), and every state the checker changes is a fresh clone,
    so ownership stays linear -- each state of the result is either the input
    or new.

    The proof of [exec] is by induction on the [cexpr]; a case function whose
    body calls [exec] on a subexpression takes [⊢ exec_like checker.exec e']
    for that subexpression as a premise. *)
From New.checker Require Import prelude nodes exec_spec.

Section exec_def.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

Definition exec_post (ce : cexpr) (ρ : list (go_string * term)) (sst : sstate)
    (s : slice.t) (lf : loc) : iProp Σ :=
  (if decide (lf = null) then
     ∃ ps, is_paths s ps ∗ ⌜paths_wf (length (svars sst)) ps⌝ ∗ ⌜exec_sound ce ρ sst ps⌝
   else True)%I.

Definition exec_like (fn : go_string) (ce : cexpr) : iProp Σ :=
  (∀ (le lρ lst : loc) (ρ : list (go_string * term)) (sst : sstate),
    {{{ is_pkg_init checker ∗ is_expr le ce ∗ is_env lρ ρ ∗ is_state lst sst ∗
        ⌜wf_state sst⌝ ∗ ⌜env_below (length (svars sst)) ρ⌝ }}}
      @! fn #le #lρ #lst
    {{{ (s : slice.t) (lf : loc), RET (#s, #lf); exec_post ce ρ sst s lf }}})%I.

End exec_def.
