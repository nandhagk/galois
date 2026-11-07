(** * Search tick observations

    These computations retain both engine work and arbitrary visitor callee charges.
    For example, charging every callback changes the diamond cost by its event count.
    Builds on: GraphSearchTest and GraphSearch. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphVisitor GraphSearch.
From Galois.Tests.Graph Require Import GraphSearchTest.
Import List.ListNotations Cost.Notations.

Definition charged_visitor {E} : Visitor.t E unit :=
  Visitor.Make (fun _ _ s => Cost.tick 37 ;; Cost.ret s)
    (fun _ _ _ _ s => Cost.tick 37 ;; Cost.ret s)
    (fun _ _ s => Cost.tick 37 ;; Cost.ret s).

Example singleton_ticks :
  Cost.ticks (SearchRun.run_c SearchFixtures.single Visitor.noop
    SearchFixtures.unrestricted [1]%positive tt) = 36%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_extra_visitor_ticks :
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond charged_visitor
    SearchFixtures.unrestricted [1]%positive tt) -
    Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
      SearchFixtures.unrestricted [1]%positive tt))%N = 444%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_search_ticks :
  Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
    SearchFixtures.unrestricted [] tt) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.
