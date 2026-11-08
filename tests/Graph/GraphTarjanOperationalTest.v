(** * Law-free SCC support clients

    These clients use operational support on raw prepared records and short budgets.
    For example, a short-budget line can emit its last vertex while leaving earlier frames open.
    Builds on: GraphTarjanOperational and GraphFixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchOperational GraphSccSpec GraphTarjan GraphTarjanOperational
  GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example arbitrary_prepared_support {V E} (p : Prepared.t V E) scope roots c :
  In c (Scc.components (Tarjan.compute p scope roots)) ->
    NoDup c /\ forall v, In v c -> Scope.admits scope v = true.
Proof.
  apply TarjanOperational.component_support.
Qed.

Definition short_line :=
  let p := Fixtures.Line.prepared in
  Prepared.Make (Prepared.graph p) (Prepared.node_enc p) (Prepared.names p)
    (Prepared.succ p) (Prepared.pred p) (Prepared.entry_ids p) 1.

Example short_budget_actual_components :
  Scc.components (Tarjan.compute short_line (Scope.Make FinSet.empty None) [4; 3; 1]) =
    [[4]].
Proof.
  vm_compute. reflexivity.
Qed.

Example short_budget_partition_support :
  NoDup (concat (Scc.components
    (Tarjan.compute short_line (Scope.Make FinSet.empty None) [4; 3; 1]))).
Proof.
  exact (proj1 (TarjanOperational.partition_support _ _ _)).
Qed.

Definition limited :=
  Scope.Make (FinSet.of_list positive_encoding [3])
    (Some (FinSet.of_list positive_encoding [2; 3; 4])).

Example rejected_and_unknown_actual :
  Scc.components (Tarjan.compute short_line limited [3; 99; 4; 4]) = [[4]].
Proof.
  vm_compute. reflexivity.
Qed.

Example short_budget_component_support :
  NoDup [4] /\ forall v, In v [4] -> Scope.admits limited v = true.
Proof.
  apply (TarjanOperational.component_support short_line limited [3; 99; 4; 4]).
  rewrite rejected_and_unknown_actual. now left.
Qed.

Example raw_empty_support :
  NoDup (concat (Scc.components (Tarjan.compute Fixtures.Empty.prepared limited [99; 99]))).
Proof.
  exact (proj1 (TarjanOperational.partition_support _ _ _)).
Qed.

Example raw_empty_actual :
  Scc.components (Tarjan.compute Fixtures.Empty.prepared limited [99; 99]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example arbitrary_root_event_client {V E} (p : Prepared.t V E) scope roots :
  SearchOperational.events scope SearchRun.initial
    (snd (SearchRun.reference_roots p scope roots SearchRun.initial))
    (fst (SearchRun.reference_roots p scope roots SearchRun.initial)).
Proof.
  apply SearchOperational.roots_events, SearchInvariant.initial_representation.
Qed.
