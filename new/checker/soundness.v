(** Statement of soundness for the Go symbolic-execution checker in checker/.

    The checker (checker/*.go, translated by Goose into
    new/code/github_com/mit_pdos/perennial/checker.v) is being verified. This
    file only *states* what a [true] answer of [checker.Check] means, as
    [Axiom check_sound] at the end; the definitions it is stated over live in
    new/checker/defs.v, which this file exports.

    Trust boundary of the whole pipeline: the GooseLang semantics, this axiom,
    and the unverified frontend (gocheck/) that produces the checker's input
    from Go source. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Export defs.

Set Default Proof Using "Type".

Section semantics.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** * The soundness statement

    If [checker.Check] answers [true] on (the heap representation of) a
    function [f], sort table [vars], precondition [pre] and postcondition
    [post], then for every valuation of the logical variables respecting the
    sorts, [f] applied to the values of variables [0 .. nparams-1] satisfies the
    Hoare triple with precondition [pre] and postcondition [post] (in which
    [ret] denotes the return value). This is the only unproved assumption of
    the pipeline besides the GooseLang semantics itself; the checker is not
    verified. *)
Axiom check_sound :
  ∀ (f : cfunc) (vars : list sort) (pre post : cassn)
    (lf : loc) (svars : slice.t) (lpre lpost : loc),
  {{{ is_pkg_init checker ∗
      is_func lf f ∗ is_sorts svars vars ∗ is_assn lpre pre ∗ is_assn lpost post }}}
    @! checker.Check #lf #svars #lpre #lpost
  {{{ (b : bool), RET #b;
      ⌜ b = true →
        ∀ θ : nat → val,
          vars_sat θ vars →
          {{{ pre_interp θ pre }}}
            apply_vals (func_val f) (arg_vals f θ)
          {{{ (v : val), RET v; post_interp θ v post }}} ⌝ }}}.

End semantics.
