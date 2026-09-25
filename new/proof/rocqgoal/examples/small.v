(** Small goals that use every node of the export format.

    Built with the rest of the tree, each goal reports only the size of its
    export. [gocheck/rocqgoal/testdata/regen.sh] prints the exports in full;
    they are the test inputs of the Go package [gocheck/rocqgoal]. *)
From Corelib Require Import PrimString PrimInt63.
From Stdlib Require Import PArray.
From New.proof.rocqgoal Require Import export.

(** A let-bound hypothesis, the four sorts, products, a [match] and a
    [fix]. *)
Goal let n := 3 in
  forall (b : bool) (X : Set) (Y : SProp) (P : nat -> Prop),
    match b with true => n | false => 0 end = 0 ->
    (fix f (k : nat) : nat := match k with O => O | S j => f j end) n = 0 ->
    P n -> Prop -> Type.
Proof.
  intros n b X Y P H1 H2 HP.
  ltac2:(report_goal "small_let").
Abort.

(** Primitive integers, strings (a double quote, a backslash and a
    non-ASCII byte, to exercise the escapes) and arrays, and a lambda. *)
Goal forall s : PrimString.string,
    s = "a""b\é"%pstring ->
    (fun x : int => x) 42%uint63 = 42%uint63 ->
    PArray.get [| 1; 2 | 0 |]%uint63 0%uint63 = 1%uint63 -> True.
Proof.
  intros s Hs Hi Ha.
  ltac2:(report_goal "small_prim").
Abort.

(** A primitive projection. *)
#[projections(primitive)] Record pt := { px : nat; py : nat }.

Goal forall p : pt, p.(px) = p.(py) -> True.
Proof.
  intros p Hp.
  ltac2:(report_goal "small_proj").
Abort.
