/-
Port of `new/checker/verify_def.v`.

The contract between the two halves of the postcondition check
(checker/match.go, checker/check.go).

`Verify` parses the postcondition into disjuncts (`parseDisjuncts`) and
asks, for each path, whether some disjunct matches it (`checkDisjunct`).
The two halves meet in `dj_interp`, the assertion a parsed disjunct
stands for:

- the parsing side proves that a disjunct that parsed without failure
  entails the postcondition: `∀ V, dj_interp V dj ⊢ assn_interp V post`;
- the matching side proves that a successful `checkDisjunct` of path `p`
  against `dj` gives `path_sat_dj vars p dj`: the path's heap entails
  `dj_interp` at the caller's valuation, with `ret` the path's value.

As with `exec_sound` (exec_spec.v), both facts come in two layers: the
`_at` form is about the ambient `HeapGS hlc GF`, and the plain form
(`path_sat_dj`, `dj_entails`) quantifies it over every FFI, ghost state
and Go semantics; the plain form is what the checker's specifications
promise.

`Check` then chains `Analyze`'s path postcondition (`paths_post`) through
these two to `post_interp`.

Lean notes:
* Rocq's section declares `package_sem : checker.Assumptions`, which none of
  the definitions use; it is omitted here.
* As with `triple_holds` (Defs.lean), the uniform forms also quantify over
  `GoGlobalContext` and `HasLC`.
-/
import Checkers.Checker.Disjunct

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

section verify_def
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What a parsed disjunct asserts at valuation `V`: some values `W` for its
declared pattern variables, each of its declared sort, under which all of
its atoms hold. Indices no binder declared keep `V`'s value, exactly as
`assn_interp` of the `CAExists` chain leaves them. -/
def dj_interp (V : valuation) (dj : cdisjunct) : IProp GF :=
  iprop(∃ W : Nat → val,
     ⌜∀ n, (d_pat_ok dj)[n]? = some true →
           ∃ s, (d_pats dj)[n]? = some s ∧ has_sort (W n) s⌝ ∗
     ⌜∀ n, (d_pat_ok dj)[n]? ≠ some true → W n = vpat V n⌝ ∗
     [∗list] a ∈ d_atoms dj, assn_interp (mkVal (vvar V) W (vret V)) a)

/-- Path `sp` satisfies disjunct `dj`, for a caller whose declared logical
variables have sorts `vars`: whenever the path is reached from the
caller's valuation `θ` (the facts `paths_post` and `paths_wf` provide),
its heap entails the disjunct at `θ`, with `ret` the path's value. -/
def path_sat_dj_at (vars : List sort) (sp : spath) (dj : cdisjunct) : Prop :=
  ∀ (θ : Nat → val) (V' : valuation),
    vars_sat θ vars →
    agree_below vars.length (mkVal θ (fun _ => uval) uval) V' →
    st_sat V' (pst sp) →
    wf_state (pst sp) →
    vars.length ≤ (svars (pst sp)).length →
    vars_below (svars (pst sp)).length (pret sp) →
    heap_interp (GF := GF) V' (sheap (pst sp)) ⊢
      dj_interp (mkVal θ (fun _ => uval) (teval V' (pret sp))) dj

end verify_def

def path_sat_dj (vars : List sort) (sp : spath) (dj : cdisjunct) : Prop :=
  ∀ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_interp : FfiInterp ffi)
    (_ffi_sem : FfiSemantics ext ffi) (_go_gctx : GoGlobalContext)
    (hlc : HasLC) (GF : BundledGFunctors) (_hG : HeapGS hlc GF) (_sem : go.Semantics),
    path_sat_dj_at (GF := GF) vars sp dj

/-- A parsed disjunct entails an assertion, in any ghost state. -/
def dj_entails (dj : cdisjunct) (P : cassn) : Prop :=
  ∀ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_interp : FfiInterp ffi)
    (_ffi_sem : FfiSemantics ext ffi) (_go_gctx : GoGlobalContext)
    (hlc : HasLC) (GF : BundledGFunctors) (_hG : HeapGS hlc GF) (_sem : go.Semantics),
    ∀ V, dj_interp (GF := GF) V dj ⊢ assn_interp V P

end Checker
end Perennial
