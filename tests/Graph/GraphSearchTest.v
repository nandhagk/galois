(** * Explicit-stack search fixtures

    These computations observe root order, scoped rejection, labelled events and visitor state.
    For example, two distinct labels with identical endpoints produce Tree then Forward.
    Builds on: GraphSearch and GraphFixtures. *)

From Stdlib Require Import List Bool Arith PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphFixtures.
Import List.ListNotations.

Module SearchFixtures.

Definition unrestricted := Scope.Make FinSet.empty None.
Definition blocked_one :=
  Scope.Make (FinSet.of_list positive_encoding [1%positive]) None.
Definition right_branch :=
  Scope.Make FinSet.empty (Some (FinSet.of_list positive_encoding [1; 3; 4]%positive)).

Definition single := Fixtures.prepare [1] [1] [].
Definition self_loop := Fixtures.prepare [1] [1] [(1, 1)].
Definition diamond := Fixtures.Diamond.prepared.
Definition line := Fixtures.Line.prepared.

Definition orders {V E} (p : Prepared.t V E) scope roots :=
  let r := SearchRun.dfs p scope roots in (Search.preorder r, Search.postorder r).

Definition count_edge {E} : Visitor.t E nat :=
  Visitor.of_pure (fun _ _ n => n) (fun _ _ _ _ n => S n) (fun _ _ n => n).

Definition count_kinds {E} : Visitor.t E (nat * nat * nat * nat) :=
  Visitor.of_pure (fun _ _ s => s)
    (fun _ _ _ k s =>
      let '(tree, back, forward, cross) := s in
      match k with
      | Search.Tree => (S tree, back, forward, cross)
      | Search.Back => (tree, S back, forward, cross)
      | Search.Forward => (tree, back, S forward, cross)
      | Search.Cross => (tree, back, forward, S cross)
      end)
    (fun _ _ s => s).

Definition labelled_graph :=
  Graph.of_pure [1] [1; 2]
    (fun v => if Nat.eqb v 1 then [10; 11] else [])
    (fun _ => 1) (fun _ => 2).
Definition parallel := Prepared.prepare nat_encoding labelled_graph.

Example singleton_orders : orders single unrestricted [1]%positive = ([1], [1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example self_loop_events :
  SearchRun.events self_loop unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Edge (1, 1)%nat 1 1 Search.Back;
     Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_orders :
  orders diamond unrestricted [1]%positive = ([1; 2; 4; 3], [4; 2; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_roots :
  orders line unrestricted [3; 1; 3]%positive = ([3; 4; 1; 2], [4; 3; 2; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_roots :
  orders diamond unrestricted [99; 1; 99]%positive = ([1; 2; 4; 3], [4; 2; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_roots : orders diamond unrestricted [] = ([], []).
Proof.
  vm_compute. reflexivity.
Qed.

Example blocked_root : SearchRun.events diamond blocked_one [1]%positive = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example within_orders :
  orders diamond right_branch [1]%positive = ([1; 3; 4], [4; 3; 1])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_kind_counts :
  snd (Cost.value
    (SearchRun.run_c diamond count_kinds unrestricted [1]%positive (0, 0, 0, 0))) =
    (3, 0, 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_label_events :
  SearchRun.events parallel unrestricted [1]%positive =
    [Search.Enter 1 None;
     Search.Edge 10%nat 1 2 Search.Tree; Search.Enter 2 (Some (10%nat, 1));
     Search.Exit 2 (Some 1); Search.Edge 11%nat 1 2 Search.Forward;
     Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_parent_label :
  Map.get positive_encoding 2%positive
    (Search.parent_edge (SearchRun.dfs parallel unrestricted [1]%positive)) =
    Some (10, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example endpoint_classification_loses_label :
  Search.classify (SearchRun.dfs parallel unrestricted [1]%positive) 1%positive 2%positive =
    Some Search.Tree.
Proof.
  vm_compute. reflexivity.
Qed.

Example eligible_callback_count :
  snd (Cost.value (SearchRun.run_c diamond count_edge right_branch [1]%positive 0)) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Definition reject_two :=
  Scope.Make (FinSet.of_list positive_encoding [2%positive]) None.
Definition one_rejected := Fixtures.prepare [1] [1; 2] [(1, 2)].
Definition no_edges := Fixtures.prepare [1] [1; 2] [].

Example rejected_occurrence_has_no_callback :
  snd (Cost.value (SearchRun.run_c one_rejected count_edge reject_two [1]%positive 0)) = 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example rejected_occurrence_still_costs :
  (Cost.ticks (SearchRun.run_c no_edges count_edge reject_two [1]%positive 0%nat) <
    Cost.ticks (SearchRun.run_c one_rejected count_edge reject_two [1]%positive 0%nat))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition unknown_target :=
  Prepared.Make (Prepared.graph parallel) (Prepared.node_enc parallel) (Prepared.names parallel)
    (Map.set positive_encoding 1%positive [(10, 99%positive)] Map.empty)
    Map.empty [1]%positive (Prepared.fuel parallel).

Example unknown_cached_target_is_rejected :
  SearchRun.events unknown_target unrestricted [1]%positive =
    [Search.Enter 1 None; Search.Exit 1 None]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

End SearchFixtures.
