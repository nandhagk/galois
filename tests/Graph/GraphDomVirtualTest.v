(** * Virtual-root and dense erasure clients

    Fixtures exercise the semantic boundary independently of a dominator producer.
    For example, a root parent is erased while a real parent on the line is retained.
    Builds on: GraphDomVirtual, GraphDomErase, GraphDomParents and GraphFixtures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom
  GraphFixtures GraphDomVirtual GraphDomErase GraphDomParents.
Import List.ListNotations Cost.Notations.
Open Scope positive_scope.

Definition virtual_line := DomVirtual.virtual Fixtures.Line.prepared.

Example virtual_line_entries :
  (Prepared.entry_ids virtual_line, Prepared.name_of virtual_line 5) = ([5], Some None).
Proof.
  vm_compute. reflexivity.
Qed.

Example virtual_line_original_names :
  map (Prepared.name_of virtual_line) [1; 2; 3; 4] =
    [Some (Some 1%nat); Some (Some 2%nat); Some (Some 3%nat); Some (Some 4%nat)].
Proof.
  vm_compute. reflexivity.
Qed.

Definition repeated := Fixtures.prepare [1; 1; 2; 1; 2]%nat [1; 2]%nat [].

Example repeated_entry_order :
  DomVirtual.entries nat_encoding (Prepared.graph repeated) = [1; 2]%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_virtual_edges :
  Graph.out (Prepared.graph (DomVirtual.virtual repeated)) None =
    [inr 1%nat; inr 2%nat].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_has_only_root :
  let p := DomVirtual.virtual (Fixtures.prepare [] [] []) in
  (Graph.nodes (Prepared.graph p), Prepared.entry_ids p) = ([None], [1]).
Proof.
  vm_compute. reflexivity.
Qed.

Example erase_root_binding :
  let m := Map.of_list positive_encoding [(1, 5); (2, 1); (3, 2); (4, 3)] in
  DomErase.erase Fixtures.Line.prepared m = Fixtures.Line.parents.
Proof.
  vm_compute. reflexivity.
Qed.

Definition virtual_parents :=
  Map.of_list positive_encoding [(1, 5); (2, 1); (3, 2); (4, 3)].

Definition virtual_tree := DomCheck.of_parents virtual_line virtual_parents.

Example virtual_tree_exact : Dom.exact virtual_line virtual_tree.
Proof.
  apply DomCheck.check_sound.
  - apply DomVirtual.virtual_ready. exact Fixtures.Line.fixture_ready.
  - apply Map.wf_of_list.
  - vm_compute. reflexivity.
Qed.

Example erasure_contract_client n d v u :
  reachable (Prepared.graph Fixtures.Line.prepared) n ->
  Prepared.id_of Fixtures.Line.prepared n = Some v ->
  Prepared.id_of Fixtures.Line.prepared d = Some u ->
  (Map.get positive_encoding v (DomErase.erase Fixtures.Line.prepared virtual_parents) =
    Some u <->
    immediately_dominates (Prepared.graph Fixtures.Line.prepared) d n).
Proof.
  intros Hn Hv Hu.
  exact (DomErase.erase_virtual_exact Fixtures.Line.prepared virtual_tree n d v u
    Fixtures.Line.fixture_ready virtual_tree_exact Hn Hv Hu).
Qed.

Example erase_unknown_and_root_endpoints :
  let m := Map.of_list positive_encoding [(1, 5); (5, 1); (9, 1); (2, 9)] in
  DomErase.erase Fixtures.Line.prepared m = Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Example exact_maps_client :
  Dom.idom Fixtures.Line.tree =
    Dom.idom (DomCheck.of_parents Fixtures.Line.prepared Fixtures.Line.parents).
Proof.
  apply (DomParents.maps_agree Fixtures.Line.prepared).
  - exact Fixtures.Line.fixture_ready.
  - exact Fixtures.Line.tree_exact.
  - exact Fixtures.Line.tree_exact.
Qed.

Example virtual_ready_client : Prepared.ready virtual_line.
Proof.
  apply DomVirtual.virtual_ready. exact Fixtures.Line.fixture_ready.
Qed.

Example virtual_frontier_contract_client {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Prepared.id_of (DomVirtual.virtual p) None = Some (Intern.next (Prepared.names p)).
Proof.
  apply DomVirtual.root_id_frontier.
Qed.

Example all_query_semantic_client (d n : nat) :
  dominates (Prepared.graph Fixtures.Line.prepared) d n <->
    dominates
      (DomVirtual.graph (Prepared.node_enc Fixtures.Line.prepared)
        (Prepared.graph Fixtures.Line.prepared)) (Some d) (Some n).
Proof.
  apply DomVirtual.virtual_dominates_iff.
  exact (Prepared.encoding_valid _
    (proj2 (proj2 Fixtures.Line.fixture_ready))).
Qed.

Definition weighted : Graph.t nat (nat * nat) :=
  Graph.Make [1]%nat [1; 2]%nat
    (fun _ => Cost.tick 7 ;; Cost.ret [(1, 2)%nat])
    (fun e => Cost.tick 11 ;; Cost.ret (fst e))
    (fun e => Cost.tick 13 ;; Cost.ret (snd e)).

Example selected_callback_charges :
  (Cost.ticks (DomVirtual.out_c weighted [] (Some 1%nat)),
   Cost.ticks (DomVirtual.source_c weighted (inl (1, 2)%nat)),
   Cost.ticks (DomVirtual.target_c weighted (inl (1, 2)%nat))) = (9, 12, 14)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_occurrences_are_charged :
  Cost.ticks
    (DomVirtual.entries_from_c nat_encoding Map.empty [1; 1; 1]%nat) = 19%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_virtual_has_overhead :
  (0 < Cost.ticks (DomVirtual.virtual_c (Fixtures.prepare [] [] [])))%N.
Proof.
  vm_compute. reflexivity.
Qed.
