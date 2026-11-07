(** * Components and condensation contracts

    Components partition the scoped reachable domain into maximal mutually reachable blocks.
    For example, a self-loop belongs to one component and creates no condensation edge.
    Builds on: GraphSearchSpec. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec.
Import List.ListNotations.

Module Scc.

Record result := Result {
  components : list (list positive);
  comp_of : Map.t positive positive
}.

(** A block is a nonempty maximal class for scoped mutual reachability. *)
Definition block {V E} (p : Prepared.t V E) scope roots c :=
  c <> [] /\ NoDup c /\
  (forall u, In u c -> Search.scoped_reachable p scope roots u) /\
  (forall u v, In u c ->
    (In v c <-> Search.scoped_reachable p scope roots v /\
      (exists es, Search.scoped_path p scope u es v) /\
      (exists es, Search.scoped_path p scope v es u))).

(** SCC output is a reverse-topological, duplicate-free partition with an exact owner map. *)
Record exact {V E} (p : Prepared.t V E) scope roots (r : result) : Prop := {
  components_exact : Forall (block p scope roots) (components r);
  partition_unique : NoDup (concat (components r));
  partition_complete : forall v, In v (concat (components r)) <->
    Search.scoped_reachable p scope roots v;
  owners_wf : Map.wf positive_encoding (comp_of r);
  owners_exact : forall v i, Map.get positive_encoding v (comp_of r) = Some i <->
    exists c, nth_error (components r) (Nat.pred (Pos.to_nat i)) = Some c /\ In v c;
  reverse_topological : forall u e v i j,
    Prepared.arc p u e v -> Map.get positive_encoding u (comp_of r) = Some i ->
    Map.get positive_encoding v (comp_of r) = Some j -> i <> j -> (j < i)%positive
}.

End Scc.

Module Condensation.

(** A natural count admits the empty condensation graph without a sentinel component. *)
Record t := Make {
  count : nat;
  succs : Map.t positive (list positive)
}.

(** Condensation has one node per SCC and exactly the distinct cross-component successors. *)
Record exact {V E} (p : Prepared.t V E) (r : Scc.result) (c : t) : Prop := {
  count_exact : count c = length (Scc.components r);
  successors_wf : Map.wf positive_encoding (succs c);
  successors_domain : forall i xs, Map.get positive_encoding i (succs c) = Some xs ->
    Pos.to_nat i <= count c;
  successors_unique : forall i xs, Map.get positive_encoding i (succs c) = Some xs ->
    NoDup xs;
  successors_exact : forall i j,
    (exists xs, Map.get positive_encoding i (succs c) = Some xs /\ In j xs) <->
    i <> j /\ exists u e v, Prepared.arc p u e v /\
      Map.get positive_encoding u (Scc.comp_of r) = Some i /\
      Map.get positive_encoding v (Scc.comp_of r) = Some j
}.

End Condensation.
