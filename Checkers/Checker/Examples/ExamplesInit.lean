/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/examples_init.v`.

Package-initialization boilerplate shared by the proofs of the individual
functions in checker/examples.

Each function gets its own file so that the cost of checking its proof can
be measured on its own; see gocheck/demo.sh, which times one [rocq compile
-vok] per function against one run of the checker on the same
specification.

Lean notes: the package is `github.com/upamanyus/bootstrap-go/checker/examples`
here (Lean namespace `github_com.upamanyus.bootstrap_go.checker.examples`). The
Lean counterpart of one `rocq compile -vok` is one `lake env lean <file>`.
Measured wall-clock times of `lake env lean <file>` (2026-10-07, median of 3
runs; a file that only imports `ExamplesInit` takes 2.0 s, the cost of loading
the imports): ExamplesInit 2.3 s, Double 2.8 s, Max 2.6 s, Swap 2.5 s, Abs
2.4 s, CondStore 2.5 s, Median3 5.8 s.
-/
import Perennial.Proof.ProofPrelude
import Generated.GeneratedProof.github_com.upamanyus.bootstrap_go.checker.examples

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.upamanyus.bootstrap_go.checker.examples

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : examples.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.upamanyus.bootstrap_go.checker.examples
      get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end init

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
