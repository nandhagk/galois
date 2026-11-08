(** * Tarjan component observations

    Local prepared graphs exercise pending vertices, component order and rejected scope targets.
    For example, nested cycles form one maximal SCC while distinct cycles emit separately.
    Builds on: GraphTarjan and the public preparation laws. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSccSpec GraphTarjan.
Import List.ListNotations.

Module TarjanFixtures.
Local Open Scope nat_scope.

Definition graph roots nodes (edges : list (nat * nat)) :=
  Graph.of_pure roots nodes (fun v => filter (fun e => Nat.eqb (fst e) v) edges) fst snd.

Definition prepare roots nodes edges := Prepared.prepare nat_encoding (graph roots nodes edges).
Definition unrestricted := Scope.Make FinSet.empty None.

(** Local edge-list fixtures are ready when their nodes, entries and edge endpoints are valid. *)
Theorem fixture_ready roots nodes edges :
  NoDup nodes -> incl roots nodes -> NoDup edges ->
  (forall e, In e edges -> In (fst e) nodes /\ In (snd e) nodes) ->
  Prepared.ready (prepare roots nodes edges).
Proof.
  intros Hnodes Hroots Hedges Hendpoints.
  unfold prepare, graph.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + exact Hnodes.
    + exact Hroots.
    + intros v e He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_source. now apply Nat.eqb_eq, (proj2 He).
    + intros v e _ He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_target. exact (proj2 (Hendpoints e (proj1 He))).
  - intro v. rewrite Graph.of_pure_out. now apply NoDup_filter.
Qed.

Definition line := prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 4)].
Definition diamond := prepare [1] [1; 2; 3; 4] [(1, 2); (1, 3); (2, 4); (3, 4)].
Definition self_loop := prepare [1] [1] [(1, 1)].
Definition nested :=
  prepare [1] [1; 2; 3; 4] [(1, 2); (2, 3); (3, 2); (3, 4); (4, 1)].
Definition irreducible :=
  prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 3); (3, 2)].
Definition empty := prepare [] [] [].
Definition distinct :=
  prepare [1] [1; 2; 3; 4] [(1, 2); (2, 1); (2, 3); (3, 4); (4, 3)].

(** Each local fixture obtains readiness from preparation rather than a GraphFixtures import. *)
Example fixtures_ready :
  Prepared.ready line /\ Prepared.ready diamond /\ Prepared.ready self_loop /\
  Prepared.ready nested /\ Prepared.ready irreducible /\ Prepared.ready empty /\
  Prepared.ready distinct.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  all: apply fixture_ready;
    [ repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros x Hin; vm_compute in Hin |- *; intuition congruence
    | repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros [a b] Hin; vm_compute in Hin |- *; intuition congruence ].
Qed.

Definition components {V E} (p : Prepared.t V E) :=
  Scc.components (Tarjan.compute p unrestricted (Prepared.entry_ids p)).

Definition owner_list (r : Scc.result) vs := map (fun v => Map.get positive_encoding v
  (Scc.comp_of r)) vs.

Example line_components : components line = [[4]; [3]; [2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_components : components diamond = [[4]; [2]; [3]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_component : components self_loop = [[1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_is_one_maximal_component : components nested = [[4; 3; 2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example irreducible_components : components irreducible = [[3; 2]; [1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_components : components empty = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_reverse_topological : components distinct = [[4; 3]; [2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example distinct_exact_owner_indices :
  owner_list (Tarjan.compute distinct unrestricted [1]%positive) [1; 2; 3; 4; 99]%positive =
    [Some 2; Some 2; Some 1; Some 1; None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition inner_scope :=
  Scope.Make FinSet.empty (Some (FinSet.of_list positive_encoding [2; 3]%positive)).
Definition block_two := Scope.Make (FinSet.of_list positive_encoding [2]%positive) None.

Example within_one_component :
  let r := Tarjan.compute nested inner_scope [99; 2; 2; 1]%positive in
  (Scc.components r, owner_list r [1; 2; 3; 4; 99]%positive) =
    ([[3; 2]], [None; Some 1; Some 1; None; None])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_node_absent :
  let r := Tarjan.compute diamond block_two [1; 2; 99]%positive in
  (Scc.components r, owner_list r [1; 2; 3; 4; 99]%positive) =
    ([[4]; [3]; [1]], [Some 3; None; Some 2; Some 1; None])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_unknown_rejected_roots :
  Tarjan.compute nested inner_scope [99; 2; 2; 1; 99]%positive =
    Tarjan.compute nested inner_scope [2]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition parallel_graph :=
  Graph.of_pure [1] [1; 2]
    (fun v => filter (fun e => Nat.eqb (if Nat.eqb e 12 then 2 else 1) v) [10; 11; 12])
    (fun e => if Nat.eqb e 12 then 2 else 1)
    (fun e => if Nat.eqb e 12 then 1 else 2).
Definition parallel := Prepared.prepare nat_encoding parallel_graph.

(** The parallel-label graph is prepared from a well-formed, duplicate-free labelled adjacency. *)
Example parallel_ready : Prepared.ready parallel.
Proof.
  unfold parallel, parallel_graph.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - constructor.
    + cbn. repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
    + intros v Hv. vm_compute in Hv |- *. intuition congruence.
    + intros v e He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_source. now apply Nat.eqb_eq, (proj2 He).
    + intros v e _ He. rewrite Graph.of_pure_out, filter_In in He.
      rewrite Graph.of_pure_target.
      destruct He as [He _]. cbn in He.
      destruct He as [<-|[<-|[<-|Hfalse]]]; [vm_compute; auto|vm_compute; auto|
        vm_compute; auto|contradiction].
  - intro v. rewrite Graph.of_pure_out. apply NoDup_filter.
    repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example parallel_labels_same_component : components parallel = [[2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition pending_cross :=
  prepare [1] [1; 2; 3] [(1, 2); (1, 3); (2, 1); (3, 2)].

(** A finished sibling remains on Tarjan's stack until its enclosing SCC is emitted. *)
Example pending_cross_ready : Prepared.ready pending_cross.
Proof.
  apply fixture_ready;
    [ repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros x Hin; vm_compute in Hin |- *; intuition congruence
    | repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil
    | intros [a b] Hin; vm_compute in Hin |- *; intuition congruence ].
Qed.

Example cross_to_finished_pending_sibling : components pending_cross = [[3; 2; 1]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_roots : Tarjan.compute distinct unrestricted [] = Scc.Result [] Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

End TarjanFixtures.
