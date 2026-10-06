(** * OBSERVE-EXECUTION for the table-driven checker

    This file is the whole trusted interface between a run of the Go program
    [tcheck.Check] and Rocq.  Read it once; nothing else needs auditing in
    order to trust a generated observation file.

    - [observed_run b]: some crash-free GooseLang run of [tcheck.Check],
      from a state whose heap holds the byte slice [b], returns [#true].
      A generated observation file (new/proof/.../tcheck/observed_*.v,
      written by gocheck/tcheck) contains exactly one axiom, of the form
      [Axiom name : observed_run "<bytes>"%go], where the bytes are verbatim
      the ones the Go run was given.  It is *evidence*, not an assumption
      about the world: [bash gocheck/tcheck/observe.sh] reruns the Go
      checker on those very bytes and regenerates every such file, which
      must come out identical.

    - [check_adequate]: if [tcheck.Check] returns [true] on [ser_input i],
      then [input_holds i].  This is the soundness of the checker
      (tcheck/), and **it is not yet proved**: it plays the role
      [check_sound] played for checker/ before new/checker/ proved it.  It is
      the one axiom about the checker's code; [Print Assumptions] of any
      result shows it next to the observation it was combined with. *)
From Perennial.goose_lang Require Import adequacy.
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import tcheck.
From New.tcheck Require Export denote.

(** The heap of a GooseLang state. *)
Notation heap_t := (gmap loc (nonAtomic val)).

Section layout.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext} {sem_fn : GoSemanticsFunctions}.

(** Cell [l] of [h] holds [v], unlocked. *)
Definition heap_cell (h : heap_t) (l : loc) (v : val) : Prop :=
  l ≠ null ∧ h !! l = Some (Free v).

(** The byte slice [s] holds [b]: nil and empty, or a backing array whose
    element cells hold the bytes (as new/checker/layout.v's [slice_in]). *)
Definition bytes_in (h : heap_t) (s : slice.t) (b : go_string) : Prop :=
  (s = slice.nil ∧ b = []) ∨
  (Z.of_nat (length b) = sint.Z s.(slice.len) ∧
   sint.Z s.(slice.len) ≤ sint.Z s.(slice.cap) ∧
   s.(slice.ptr) ≠ null ∧
   ∀ (i : nat) (x : w8), b !! i = Some x →
     heap_cell h (array_index_ref w8 (Z.of_nat i) s.(slice.ptr)) #x).
End layout.

(** A run of [tcheck.Check] on the bytes [b] that returned [true], under
    some model of GooseLang: an FFI, a Go semantics satisfying
    [go.Semantics], and [tcheck.Assumptions]. *)
Definition observed_run (b : go_string) : Prop :=
  ∃ (ext : ffi_syntax) (ffi : ffi_model) (ffi_sem : ffi_semantics ext ffi)
    (ffi_interp0 : ffi_interp ffi) (Hffi_adequacy : ffi_interp_adequacy)
    (go_gctx : GoGlobalContext) (lctx : GoLocalContext)
    (sem : go.Semantics) (package_sem : tcheck.Assumptions)
    (s : slice.t) (σ σ' : state) (g g' : global_state) (tp : list expr),
    ffi_initgP g.(global_world) ∧ ffi_initP σ.(world) g.(global_world) ∧
    σ.(go_state).(go_lctx) = lctx ∧
    bytes_in σ.(heap) s b ∧
    rtc erased_step ([(@! tcheck.Check #s)%E], (σ, g)) (of_val #true :: tp, (σ', g')).

(** The soundness of tcheck/, NOT YET PROVED (see the top of this file). *)
Axiom check_adequate : ∀ i : tinput, observed_run (ser_input i) → input_holds i.

(** How a generated observation file concludes: its bytes are [ser_input]
    of its input (by computation), and the run on them was observed. *)
Lemma observed_input_holds (i : tinput) (b : go_string) :
  ser_input i = b → observed_run b → input_holds i.
Proof. intros <- Hrun. by apply check_adequate. Qed.
