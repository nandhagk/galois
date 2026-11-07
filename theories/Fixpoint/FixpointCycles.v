(** * Static flows and cycle cuts

    Reads flow into every statically declared output of their constraint.
    For example, a read of x contributing to y introduces a flow from x to y.
    Builds on: FixpointSystem and Stdlib transitive closure. *)

From Stdlib Require Import List Relations.Relation_Operators.
From Galois.Fixpoint Require Import FixpointSystem.

(** A flow connects a declared read to a possible output of one listed constraint. *)
Definition flows {X C A} {S : System.t X C A} (SS : System.static S) (y x : X) :=
  exists c, In c (System.constraints S) /\ In y (deps SS c) /\
    (x = System.target S c \/ In x (side_targets SS c)).

(** Removing edges entering selected unknowns removes every nonempty cycle. *)
Definition cuts_every_cycle {X C A} {S : System.t X C A}
    (SS : System.static S) (selected : X -> bool) : Prop :=
  forall x, ~ clos_trans X (fun y z => flows SS y z /\ selected z = false) x x.
