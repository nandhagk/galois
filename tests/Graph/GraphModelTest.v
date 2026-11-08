(** * Graph model fixtures

    Finite edge lists exercise pure accessors and constructive entry reachability.
    For example, the diamond has two distinct paths to its join.
    Builds on: GraphModel. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphModel.
Import List.ListNotations.
Open Scope positive_scope.

Definition edge := (positive * positive)%type.

Definition fixture roots nodes (edges : list edge) :=
  Graph.of_pure roots nodes (fun v => filter (fun e => Pos.eqb (fst e) v) edges) fst snd.

Definition diamond_edges : list edge := [(1, 2); (1, 3); (2, 4); (3, 4)].
Definition diamond := fixture [1] [1; 2; 3; 4] diamond_edges.
Definition two_entry := fixture [1; 3] [1; 2; 3; 4] diamond_edges.
Definition self_loop := fixture [1] [1] [(1, 1)].
Definition empty := fixture [] [] [].

Example diamond_out : Graph.out diamond 1 = [(1, 2); (1, 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_absent : Graph.out diamond 9 = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_entries : Graph.entries empty = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example primitive_ticks : Cost.ticks (Graph.out_c diamond 1) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Section ConstructedObservers.
Context {V E : Type}.
Variable roots nodes : list V.
Variable outgoing : V -> Cost.t (list E).
Variable source target : E -> Cost.t V.

Example constructed_outgoing v :
  Graph.out (Graph.Make roots nodes outgoing source target) v = Cost.value (outgoing v).
Proof.
  apply Graph.make_out.
Qed.

Example constructed_endpoints e :
  Graph.source (Graph.Make roots nodes outgoing source target) e = Cost.value (source e) /\
  Graph.target (Graph.Make roots nodes outgoing source target) e = Cost.value (target e).
Proof.
  split; [apply Graph.make_source|apply Graph.make_target].
Qed.

End ConstructedObservers.

Example diamond_join_reachable : reachable diamond 4.
Proof.
  apply reachable_iff_path. exists 1, [(1, 2); (2, 4)].
  split; [vm_compute; auto|].
  apply (@path_cons positive edge diamond (1, 2)); [vm_compute; auto|].
  apply (@path_cons positive edge diamond (2, 4)); [vm_compute; auto|constructor].
Qed.

Example diamond_wf : graph_wf diamond.
Proof.
  constructor.
  - change (NoDup [1; 2; 3; 4]).
    repeat (apply NoDup_cons; [cbn; intuition discriminate|]). apply NoDup_nil.
  - vm_compute. intuition congruence.
  - intros v [s t] Hin. apply filter_In in Hin.
    destruct Hin as [_ Heq]. cbn in Heq. now apply Pos.eqb_eq in Heq.
  - intros v [s t] Hv Hin. apply filter_In in Hin.
    destruct Hin as [Hin _]. vm_compute in Hin |- *. intuition congruence.
Qed.

Example diamond_out_nodup : forall v, NoDup (Graph.out diamond v).
Proof.
  intro v. apply NoDup_filter.
  change (NoDup [(1, 2); (1, 3); (2, 4); (3, 4)]).
  repeat (apply NoDup_cons; [cbn; intuition congruence|]). apply NoDup_nil.
Qed.

Example self_loop_path : path self_loop 1 [(1, 1)] 1.
Proof.
  apply (@path_cons positive edge self_loop (1, 1)); [vm_compute; auto|constructor].
Qed.
