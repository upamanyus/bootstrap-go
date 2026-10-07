/-
Port of `new/checker/exec_def.v`.

The specification shared by `exec` and every per-case function it
dispatches to (checker/exec.go).

Each of `execInt`, `execLet`, ..., `execExcDo` has `exec`'s signature
`(e *Expr, en *env, st *State) ([]Path, *Failure)`, so one specification
template, `exec_like`, covers all of them: given the input tree, the
environment and the state, a `nil` failure means the returned slice holds
a list of paths that is well-formed and sound for the expression
(`exec_sound`, exec_spec.v). A non-`nil` failure promises nothing.

The input state is consumed: a result path may share it (that is what
`onePath` does), and every state the checker changes is a fresh clone,
so ownership stays linear -- each state of the result is either the input
or new.

The proof of `exec` is by induction on the `cexpr`; a case function whose
body calls `exec` on a subexpression takes `⊢ exec_like checker.exec e'`
for that subexpression as a premise.

Lean notes:
* `exec_like` is an `IProp` (a persistent triple under `∀`), as in Rocq;
  `exec_like_triple` turns `⊢ exec_like fn ce` into the plain triple for
  given arguments, which `wp_apply` takes directly.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

section exec_def
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def exec_post (ce : cexpr) (ρ : List (GoString × term)) (sst : sstate)
    (s : GoSlice) (lf : Loc) : IProp GF :=
  if lf = null then
    iprop(∃ ps, is_paths s ps ∗ ⌜paths_wf (svars sst).length ps⌝ ∗ ⌜exec_sound ce ρ sst ps⌝)
  else iprop(True)

def exec_like (fn : GoString) (ce : cexpr) : IProp GF :=
  iprop(∀ (le lρ lst : Loc) (ρ : List (GoString × term)) (sst : sstate),
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_expr le ce ∗ is_env lρ ρ ∗
        is_state lst sst ∗ ⌜wf_state sst⌝ ∗ ⌜env_below (svars sst).length ρ⌝ }}
      (App (App (App (Val (@! fn)) (Val #le)) (Val #lρ)) (Val #lst))
    {{ (s : GoSlice) (lf : Loc), RET (PairV #s #lf); exec_post ce ρ sst s lf }})

/-- Lean addition: the triple `⊢ exec_like fn ce` stands for, at given
arguments. -/
theorem exec_like_triple (fn : GoString) (ce : cexpr) :
    (⊢ exec_like (GF := GF) fn ce) →
    ∀ (le lρ lst : Loc) (ρ : List (GoString × term)) (sst : sstate),
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_expr le ce ∗ is_env lρ ρ ∗
        is_state lst sst ∗ ⌜wf_state sst⌝ ∗ ⌜env_below (svars sst).length ρ⌝ }}
      (App (App (App (Val (@! fn)) (Val #le)) (Val #lρ)) (Val #lst))
    {{ (s : GoSlice) (lf : Loc), RET (PairV #s #lf); exec_post ce ρ sst s lf }} := by
  intro H le lρ lst ρ sst
  unfold exec_like at H
  iintro %Φ Hpre HΦ
  ihave #Hl := H
  iapply Hl $$ %le %lρ %lst %ρ %sst %Φ Hpre HΦ

/-- Lean addition: proving `⊢ exec_like fn ce` from the plain triples. -/
theorem exec_like_intro (fn : GoString) (ce : cexpr) :
    (∀ (le lρ lst : Loc) (ρ : List (GoString × term)) (sst : sstate),
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_expr le ce ∗ is_env lρ ρ ∗
        is_state lst sst ∗ ⌜wf_state sst⌝ ∗ ⌜env_below (svars sst).length ρ⌝ }}
      (App (App (App (Val (@! fn)) (Val #le)) (Val #lρ)) (Val #lst))
    {{ (s : GoSlice) (lf : Loc), RET (PairV #s #lf); exec_post ce ρ sst s lf }}) →
    ⊢ exec_like (GF := GF) fn ce := by
  intro H
  unfold exec_like
  iintro %le %lρ %lst %ρ %sst
  imodintro
  iintro %Φ Hpre HΦ
  iapply H le lρ lst ρ sst $$ %Φ Hpre HΦ

end exec_def

end Checker
end Perennial
