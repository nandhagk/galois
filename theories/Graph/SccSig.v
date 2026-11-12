(** * Strongly connected component signatures

    Components partition the listed graph vertices in reverse topological order.
    For example, two vertices joined in both directions have the same present owner.
    Builds on: graph semantics, trie data and preparation measures. *)

From Stdlib Require Import PArith NArith List.
From Argent Require Import Time BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig.
Import List.ListNotations.

(** Mutual reachability permits zero-edge paths at each endpoint. *)
Definition mutually_reachable (g : digraph) (u v : positive) : Prop :=
  (exists vs, path g u vs v) /\ (exists vs, path g v vs u).

Module Type SCC_OPS.
  Parameter run : prepared -> scc.
End SCC_OPS.

Module Type SCC_SPEC (Import S : SCC_OPS).
  (** A shared component requires a present owner for both endpoints. *)
  Definition same_component (g : prepared) (u v : positive) : Prop :=
    exists i, trie_get u (comp (run g)) = Some i /\ trie_get v (comp (run g)) = Some i.
End SCC_SPEC.

Module Type SCC_LAWS (Import S : SCC_OPS).
  (** Equal present owners characterize mutual reachability of listed vertices. *)
  Parameter comp_spec : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  (** Component lists contain each listed vertex once. *)
  Parameter comps_partition : forall g, wf_graph (base g) ->
    NoDup (concat (comps (run g))) /\
    (forall v, In v (concat (comps (run g))) <-> In v (nodes g)).
  (** Every emitted component has a member. *)
  Parameter comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  (** Owner indices are one-based positions in the component list. *)
  Parameter owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  (** Every edge stays in its component or targets an earlier component. *)
  Parameter comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
End SCC_LAWS.

Module Type SCC := SCC_OPS <+ SCC_SPEC <+ SCC_LAWS.

Module Type SCC_TIME (Import S : SCC).
  Parameter T_run : prepared -> N.
  Parameter c_scc : N.
  (** SCC computation charges graph vertices, successor occurrences and identifier bits. *)
  Parameter T_run_le : forall g,
    (T_run g <= c_scc * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** SCC computation has the published linear bit-cost bound. *)
  Parameter run_bigO : bigO (fun _ => True)
    (fun g => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) T_run.
End SCC_TIME.

Module Type SCC_T := SCC <+ SCC_TIME.
