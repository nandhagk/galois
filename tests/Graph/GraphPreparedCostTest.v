(** * Preparation values and callback charges

    Preparation retains callback costs and the original behavior on raw malformed graphs.
    For example, repeated source nodes repeat incoming occurrences and contribute to fuel.
    Builds on: GraphPreparedCost and GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphFixtures.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Definition raw_repeated := Fixtures.prepare [7; 99; 7] [7; 2; 7] [(7, 2)].

Example repeated_raw_preparation :
  (Prepared.entry_ids raw_repeated,
    Prepared.succ_edges raw_repeated 1%positive,
    Prepared.pred_edges raw_repeated 2%positive,
    Pos.to_nat (Prepared.fuel raw_repeated)) =
  ([1; 1]%positive, [((7, 2), 2%positive)],
    [((7, 2), 1%positive); ((7, 2), 1%positive)], 10).
Proof.
  vm_compute. reflexivity.
Qed.

Definition dangling := Fixtures.prepare [1; 99] [1] [(1, 99)].

Example dangling_target_filtered_but_counted :
  (Prepared.entry_ids dangling, Prepared.succ_edges dangling 1%positive,
    Pos.to_nat (Prepared.fuel dangling)) = ([1]%positive, [], 5).
Proof.
  vm_compute. reflexivity.
Qed.

Definition expensive_graph : Graph.t nat (nat * nat) :=
  Graph.Make [1] [1; 2]
    (fun v => Cost.tick 100%N ;; Cost.ret (if Nat.eqb v 1 then [(1, 2)] else []))
    (fun e => Cost.tick 200%N ;; Cost.ret (fst e))
    (fun e => Cost.tick 300%N ;; Cost.ret (snd e)).
Definition cheap_graph := Fixtures.graph [1] [1; 2] [(1, 2)].

Definition prepared_observation {V E} (p : Prepared.t V E) :=
  (Prepared.entry_ids p, Prepared.succ_edges p 1%positive,
    Prepared.pred_edges p 2%positive, Prepared.fuel p).

Example callee_costs_preserve_observations :
  prepared_observation (Prepared.prepare nat_encoding expensive_graph) =
    prepared_observation (Prepared.prepare nat_encoding cheap_graph).
Proof.
  vm_compute. reflexivity.
Qed.

Example preparation_retains_callee_charges :
  (Cost.ticks (Prepared.prepare_c nat_encoding cheap_graph) <
    Cost.ticks (Prepared.prepare_c nat_encoding expensive_graph))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_preparation_fuel :
  Pos.to_nat (Prepared.fuel (Fixtures.prepare [] [] [])) = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example preparation_value_bridge :
  Cost.value (Prepared.prepare_c nat_encoding expensive_graph) =
    Prepared.prepare nat_encoding expensive_graph.
Proof.
  vm_compute. reflexivity.
Qed.

Definition reverse_source := Prepared.prepare nat_encoding cheap_graph.
Definition repeated_reverse := Prepared.reverse reverse_source [1; 99; 1]%positive.

Example reversal_retains_raw_exit_occurrences :
  (Prepared.entry_ids repeated_reverse, Graph.entries (Prepared.graph repeated_reverse)) =
    ([1; 99; 1]%positive, [1; 1]).
Proof.
  vm_compute. reflexivity.
Qed.

Example reversal_shares_the_predecessor_index :
  Prepared.succ repeated_reverse = Prepared.pred reverse_source.
Proof.
  vm_compute. reflexivity.
Qed.

Example reversal_charges_duplicates_and_unknown_ids :
  Cost.ticks (Prepared.reverse_c reverse_source [1; 99; 1]%positive) = 21%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_reversal_ticks :
  Cost.ticks (Prepared.reverse_c reverse_source []) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_reversal_numeric_bound :
  (Cost.ticks (Prepared.reverse_c reverse_source [1; 99; 1]%positive) <=?
    N.of_nat 3 * (3 + 2 * 7))%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_budget_conversion :
  (Cost.value (Prepared.budget_c 0), Cost.ticks (Prepared.budget_c 0)) = (1%positive, 0%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example budget_conversion_retains_linear_work :
  (Cost.value (Prepared.budget_c 37), Cost.ticks (Prepared.budget_c 37)) =
    (38%positive, 37%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example evaluated_prepare_constant : PreparedCost.prepare_k = 36%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example cheap_preparation_ticks :
  Cost.ticks (Prepared.prepare_c nat_encoding cheap_graph) = 135%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example cheap_preparation_cost_bound :
  (Cost.ticks (Prepared.prepare_c nat_encoding cheap_graph) <=?
    PreparedCost.prepare_k * PreparedCost.prepare_size cheap_graph 1 2 1 1 1)%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_preparation_cost_bound :
  (Cost.ticks (Prepared.prepare_c nat_encoding (Prepared.graph Fixtures.Line.prepared)) <=?
    PreparedCost.prepare_k *
      PreparedCost.prepare_size (Prepared.graph Fixtures.Line.prepared) 1 3 1 1 1)%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example preparation_bound_retains_nonunit_callees :
  (Cost.ticks (Prepared.prepare_c nat_encoding expensive_graph) <=?
    PreparedCost.prepare_k * PreparedCost.prepare_size expensive_graph 1 2 100 200 300)%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition repeated_entries_graph := Fixtures.graph [1; 99; 1] [1; 2] [(1, 2)].

(** Repeated and unknown entries do not change the distinct source-node obligation. *)
Example repeated_entry_nodes_distinct : NoDup (Graph.nodes repeated_entries_graph).
Proof.
  vm_compute. repeat (apply NoDup_cons; [cbn; intuition congruence|]). apply NoDup_nil.
Qed.

Local Lemma entry_fixture_bounds entries :
  (forall v, In v entries -> v = 1 \/ v = 99) ->
  PreparedCost.prepare_bounds nat_encoding (Fixtures.graph entries [1; 2] [(1, 2)])
    1%N 7%N 1%N 1%N 1%N.
Proof.
  intro Hentries. constructor.
  - intros v Hin. vm_compute in Hin.
    destruct Hin as [<-|[<-|Hfalse]]; try contradiction; vm_compute; split; congruence.
  - intros v Hin. destruct (Hentries v Hin) as [Hone|Hunknown];
      subst v; vm_compute; split; congruence.
  - intros v Hin. vm_compute. congruence.
  - intros edge Hin. vm_compute in Hin.
    destruct Hin as [<-|Hfalse]; [vm_compute; repeat split; congruence|contradiction].
Qed.

(** Primitive budgets are proved on the actual finite node, entry and endpoint occurrences. *)
Example repeated_entry_prepare_bounds :
  PreparedCost.prepare_bounds nat_encoding repeated_entries_graph 1%N 7%N 1%N 1%N 1%N.
Proof.
  apply entry_fixture_bounds.
  intros v [<-|[<-|[<-|Hfalse]]]; auto; contradiction.
Qed.

Example cheap_prepare_bounds :
  PreparedCost.prepare_bounds nat_encoding cheap_graph 1%N 7%N 1%N 1%N 1%N.
Proof.
  apply entry_fixture_bounds. intros v [<-|Hfalse]; auto; contradiction.
Qed.

(** The real preparation contract permits repeated entries while discharging node distinctness. *)
Example repeated_entry_prepare_cost :
  (Cost.ticks (Prepared.prepare_c nat_encoding repeated_entries_graph) <=
    PreparedCost.prepare_k *
      PreparedCost.prepare_size repeated_entries_graph 1 7 1 1 1)%N.
Proof.
  apply (PreparedCost.prepare_cost nat_encoding nat_encoding_laws).
  - exact repeated_entry_nodes_distinct.
  - exact repeated_entry_prepare_bounds.
Qed.

Example repeated_entry_values :
  (Graph.entries repeated_entries_graph, Graph.nodes repeated_entries_graph,
    Prepared.entry_ids (Prepared.prepare nat_encoding repeated_entries_graph)) =
    ([1; 99; 1], [1; 2], [1; 1]%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** The inverse-lookup width premise includes each duplicate and unknown exit occurrence. *)
Example public_reverse_cost_bound :
  (Cost.ticks (Prepared.reverse_c reverse_source [1; 99; 1]%positive) <=
    N.of_nat 3 * (3 + 2 * 7))%N.
Proof.
  apply PreparedCost.reverse_cost_bound. intros i Hin. vm_compute in Hin.
  destruct Hin as [<-|[<-|[<-|Hfalse]]]; try contradiction; vm_compute; congruence.
Qed.

Definition entry_graph_family (repeated : bool) :=
  if repeated then repeated_entries_graph else cheap_graph.

(** Both concrete entry domains satisfy the public preparation family corollary. *)
Example repeated_entry_prepare_bigO :
  bigO (fun repeated : bool =>
    PreparedCost.prepare_size (entry_graph_family repeated) 1 7 1 1 1)%N
    (fun repeated => Cost.ticks (Prepared.prepare_c nat_encoding (entry_graph_family repeated))).
Proof.
  apply (PreparedCost.prepare_bigO nat_encoding nat_encoding_laws entry_graph_family
    (fun _ => 1%N) (fun _ => 7%N) (fun _ => 1%N) (fun _ => 1%N) (fun _ => 1%N)).
  - intros []; exact repeated_entry_nodes_distinct.
  - intros []; [exact repeated_entry_prepare_bounds|exact cheap_prepare_bounds].
Qed.
