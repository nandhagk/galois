(** * Depth-first search observations

    Traces retain visit order and edge classifications.
    For example, a self-loop produces a back edge.

    Groups:
    - [VisitOrderTests] The vertices that the search enters, in order.
    - [TraceTests] The full trace of events, including edge classes.

    Builds on: graph fixtures and search. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import Data Digraph SearchSig Search.
From Galois.Tests.Graph Require Import Fixtures.
Import List.ListNotations.

(** * Visit order *)

Module VisitOrderTests.

  Local Open Scope positive_scope.

  (** A search from the only vertex of a singleton enters that vertex alone. *)
  Example singleton_enters_its_root :
    entered (prepared_search_trace (DigraphCode.prepare Singleton.graph) [1]) = [1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A search of the diamond follows one branch down to the join before it enters the other. *)
  Example diamond_enters_branch_before_join :
    entered (prepared_search_trace (DigraphCode.prepare Diamond.graph) [1]) = [1; 2; 4; 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A root listed twice is entered once, at its first position. *)
  Example repeated_root_is_entered_once :
    entered (prepared_search_trace (DigraphCode.prepare Line.graph) [3; 1; 3]) = [3; 4; 1; 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

End VisitOrderTests.

(** * Traces *)

Module TraceTests.

  Local Open Scope positive_scope.

  (** A self-loop produces an entry, a back edge to its own vertex and an exit. *)
  Example self_loop_trace :
    prepared_search_trace (DigraphCode.prepare SelfLoop.graph) [1] =
      [Enter 1; Edge Back 1 1; Leave 1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A search with no roots produces an empty trace. *)
  Example no_roots_empty_trace :
    prepared_search_trace (DigraphCode.prepare Diamond.graph) [] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End TraceTests.
