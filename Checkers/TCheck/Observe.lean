/-
Port of `new/tcheck/observe.v`.

# OBSERVE-EXECUTION for the table-driven checker

This file is the whole trusted interface between a run of the Go program
`tcheck.Check` and Lean.  Read it once; nothing else needs auditing in
order to trust a generated observation file.

- `observed_run b`: some GooseLang run of `tcheck.Check`, in the real
  semantics, from a state whose heap holds the byte slice `b`, returns
  `#true`. A generated observation file
  (`Checkers/TCheck/**/Observed/*.lean`, written by gocheck/tcheck) contains
  exactly one axiom, of the form `axiom name : observed_run obs!"<bytes>"`,
  where the bytes are verbatim the ones the Go run was given (as a Lean
  string literal, `"` escaped as `\"`), and `obs!` (below) elaborates them
  to `bytes_of_nat len N`: their number and their value as one big-endian
  number, the form the kernel compares with `ser_input` fast (Encode.lean).  It is *evidence*, not an
  assumption about the world: `bash gocheck/tcheck/observe.sh` reruns the
  Go checker on those very bytes and regenerates every such file, which
  must come out identical.

- `check_adequate`: if `tcheck.Check` returns `true` on `ser_input i`,
  then `input_holds i`.  This is the soundness of the checker (tcheck/),
  and **it is not yet proved**: it plays the role `check_sound` played for
  checker/ before new/checker/ proved it.  It is the one axiom about the
  checker's code; `#print axioms` of any result shows it next to the
  observation it was combined with.

Lean notes: the run is `RealNsteps` (`Perennial/GooseLang/BoundedLang.lean`),
the real thread-pool semantics the adequacy theorem `goose_adequacy` is
about, for some number of steps (Rocq: `rtc erased_step`); `ffi_initgP` and
`ffi_initP` are fields of `FfiInterpAdequacy`, as in Rocq's
`ffi_interp_adequacy`. The trusted base is also the `obs!` elaborator
(below), which turns the axiom's string literal into `bytes_of_nat` of its
UTF-8 bytes (`bytes_of_nat`, Encode.lean, a five-line definition, is then part
of what the axiom says). An older observation file may use Perennial's `go!`
instead (the bytes as a list), with `observed_input_holds`.
-/
import Perennial.GooseLang.Adequacy
import Generated.Code.github_com.upamanyus.bootstrap_go.tcheck
import Checkers.TCheck.Denote
import Checkers.TCheck.Encode

noncomputable section

namespace Perennial
namespace TCheck

/-- The heap of a GooseLang state. -/
abbrev heap_t [FfiSyntax] := GMap Loc (NonAtomic val)

section layout
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- Cell `l` of `h` holds `v`, unlocked. -/
def heap_cell (h : heap_t) (l : Loc) (v : val) : Prop :=
  l ≠ null ∧ h !! l = some (Free v)

/-- The byte slice `s` holds `b`: nil and empty, or a backing array whose
element cells hold the bytes (as new/checker/layout.v's `slice_in`). -/
def bytes_in (h : heap_t) (s : GoSlice) (b : GoString) : Prop :=
  (s = slice.nil ∧ b = []) ∨
  ((b.length : Int) = sint.Z s.len ∧
   sint.Z s.len ≤ sint.Z s.cap ∧
   s.ptr ≠ null ∧
   ∀ (i : Nat) (x : w8), b[i]? = some x →
     heap_cell h (arrayIndexRef w8 (i : Int) s.ptr) #x)
end layout

/-- A run of `tcheck.Check` on the bytes `b` that returned `true`, under
some model of GooseLang: an FFI, a Go semantics satisfying `go.Semantics`,
and `tcheck.Assumptions`. -/
def observed_run (b : GoString) : Prop :=
  ∃ (ext : FfiSyntax) (ffi : FfiModel) (_ffiSem : FfiSemantics ext ffi)
    (_ffiInterp : FfiInterp ffi) (_hAdeq : FfiInterpAdequacy ffi)
    (_go_gctx : GoGlobalContext) (lctx : GoLocalContext)
    (_sem : go.Semantics) (_pkg : github_com.upamanyus.bootstrap_go.tcheck.Assumptions)
    (s : GoSlice) (σ σ' : state) (g g' : GlobalState) (n : Nat) (κs : List Observation)
    (tp : List Expr),
    ffi_initgP g.globalWorld ∧ ffi_initP σ.world g.globalWorld ∧
    σ.goState.goLctx = lctx ∧
    bytes_in σ.heap s b ∧
    RealNsteps n
      ([App (Val #(functions github_com.upamanyus.bootstrap_go.tcheck.Check [])) (Val #s)], (σ, g))
      κs (Val #true :: tp, (σ', g'))

/-- The soundness of tcheck/, NOT YET PROVED (see the top of this file). -/
axiom check_adequate : ∀ i : tinput, observed_run (ser_input i) → input_holds i

/-- How a generated observation file concludes: its bytes are `ser_input`
of its input (by computation), and the run on them was observed. -/
theorem observed_input_holds (i : tinput) (b : GoString) :
    ser_input i = b → observed_run b → input_holds i := by
  intro h hrun; subst h; exact check_adequate i hrun

open Lean Elab Term Meta in
/-- `obs!"<bytes>"`: the UTF-8 bytes of the string literal, as
`bytes_of_nat len N` (Encode.lean) with `len` the number of bytes and `N`
the bytes read as one big-endian number -- the same `GoString` as
`go!"<bytes>"`, in a form whose comparison with `ser_input` the kernel does
with numbers. Trusted, as `go!` is: an observation axiom is stated with it. -/
elab:max "obs!" s:str : term => do
  let bs := s.getString.toUTF8.toList
  let n := bs.foldl (fun acc b => acc * 256 + b.toNat) 0
  return mkApp2 (mkConst ``bytes_of_nat) (mkNatLit bs.length) (mkNatLit n)

/-- How a generated observation file concludes, with the bytes as
`obs!"…"`: the encoder's answer on the input is the two numbers, which the
kernel checks by `rfl` (`kernel_rfl`), and the run on those bytes was
observed. -/
theorem observed_input_holds_enc (i : tinput) (len n : Nat) :
    encInput i = (len, n) → observed_run (bytes_of_nat len n) → input_holds i := by
  intro h hrun
  exact observed_input_holds i _ (ser_eq_of_enc i len n h) hrun

open Lean Elab Tactic Meta in
/-- Close `a = b` by `rfl`, `Eq.refl a`, checked by the kernel alone (the
elaborator's own check of the same definitional equality, which `exact rfl`
makes, is skipped: it is as slow as the kernel's, and redundant). -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "kernel_rfl: the goal is not an equation"
  g.assign (← mkEqRefl lhs)

end TCheck
end Perennial
