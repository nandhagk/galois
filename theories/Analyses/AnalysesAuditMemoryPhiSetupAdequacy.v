(** * Initial graph setup erasure for phi pruning

    The complete counted call prepares the original graph and uses its actual predecessor index.
    For example, a missing predecessor entry returns the same empty row as the plain preparation.
    Builds on: AnalysesAuditMemoryPhiSetup, graph preparation and producer erasure. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditMapAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditBaseAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryPhiSetup
  AnalysesAuditMemoryPhiConsumerAdequacy AnalysesAuditMemoryPhiInputBudget
  AnalysesAuditMemoryPhiInputBudgetAdequacy.

Lemma audit_phi_input_graph_callbacks_erases N E CN OE TE (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) g :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, fst (out n) = Graph.out g n) ->
  (forall e, fst (target e) = Graph.target g e) ->
  audit_prepare_callbacks_erase EN g (audit_phi_input_graph_callbacks node_enc out target).
Proof.
  intros Hnode Hout Htarget.
  split.
  - intro n; specialize (Hout n).
    unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_out_model].
    destruct (out n); exact Hout.
  - split.
    + intro e; specialize (Htarget e).
      unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_target_model].
      destruct (target e); exact Htarget.
    + intro n; specialize (Hnode n).
      unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_encode_model].
      destruct (node_enc n); exact Hnode.
Qed.

(** * The original graph callback envelope *)

Lemma audit_phi_input_node_envelope N E OE TE (out : N -> list E * list OE)
    (target : E -> N * list TE) node_budget out_budget target_budget nodes n :
  In n nodes ->
  node_budget n <= audit_phi_input_graph_envelope out target node_budget out_budget target_budget
    nodes /\
  out_budget n <= audit_phi_input_graph_envelope out target node_budget out_budget target_budget
    nodes.
Proof.
  induction nodes as [|node rest IH]; intro Hin; [contradiction|].
  cbn [audit_phi_input_graph_envelope].
  destruct Hin as [->|Hin].
  - split; lia.
  - specialize (IH Hin); destruct IH; split; lia.
Qed.

Lemma audit_phi_input_targets_member N E TE (target : E -> N * list TE)
    node_budget target_budget edges edge :
  In edge edges ->
  target_budget edge <= audit_phi_input_targets_envelope target node_budget target_budget edges /\
  node_budget (fst (target edge)) <=
    audit_phi_input_targets_envelope target node_budget target_budget edges.
Proof.
  induction edges as [|first rest IH]; intro Hin; [contradiction|].
  cbn [audit_phi_input_targets_envelope].
  destruct Hin as [->|Hin].
  - split; lia.
  - specialize (IH Hin); destruct IH; split; lia.
Qed.

Lemma audit_phi_input_target_envelope N E OE TE (out : N -> list E * list OE)
    (target : E -> N * list TE) node_budget out_budget target_budget nodes n edge :
  In n nodes -> In edge (fst (out n)) ->
  target_budget edge <= audit_phi_input_graph_envelope out target node_budget out_budget
    target_budget nodes /\
  node_budget (fst (target edge)) <= audit_phi_input_graph_envelope out target node_budget
    out_budget target_budget nodes.
Proof.
  induction nodes as [|node rest IH]; intros Hin Hedge; [contradiction|].
  cbn [audit_phi_input_graph_envelope].
  destruct Hin as [->|Hin].
  - pose proof (audit_phi_input_targets_member N E TE target node_budget target_budget
      (fst (out n)) edge Hedge) as [Htarget Hnode]; split; lia.
  - specialize (IH Hin Hedge); destruct IH; split; lia.
Qed.

Lemma audit_phi_input_preparation_bound N E CN OE TE (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) node_work out_work target_work
    node_budget out_budget target_budget (g : Graph.t N E) :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, fst (out n) = Graph.out g n) ->
  (forall edge, fst (target edge) = Graph.target g edge) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall n, out_work (snd (out n)) <= out_budget n) ->
  (forall edge, target_work (snd (target edge)) <= target_budget edge) ->
  audit_prepare_source_work (audit_phi_input_graph_body_work node_work out_work target_work)
    (snd (audit_prepare_source_counted EN g
      (audit_phi_input_graph_callbacks node_enc out target))) <=
    audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_phi_input_graph_envelope out target node_budget out_budget target_budget
        (Graph.nodes g).
Proof.
  intros Hencode Hout Htarget Hnode Hout_work Htarget_work.
  apply audit_phi_prepare_source_input_bound.
  - apply audit_phi_input_graph_callbacks_erases; assumption.
  - intros n Hin.
    pose proof (audit_phi_input_node_envelope N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) n Hin) as [_ Henvelope].
    specialize (Hout_work n).
    unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_out_model].
    destruct (out n).
    cbn [snd fold_right audit_phi_input_graph_body_work] in Hout_work |- *; lia.
  - intros n Hin.
    pose proof (audit_phi_input_node_envelope N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) n Hin) as [Henvelope _].
    specialize (Hnode n).
    unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_encode_model].
    destruct (node_enc n).
    cbn [snd fold_right audit_phi_input_graph_body_work] in Hnode |- *; lia.
  - intros n edge Hin Hedge.
    rewrite <- (Hout n) in Hedge.
    pose proof (audit_phi_input_target_envelope N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) n edge Hin Hedge) as [Henvelope _].
    specialize (Htarget_work edge).
    unfold audit_phi_input_graph_callbacks; cbn [audit_prepare_target_model].
    destruct (target edge).
    cbn [snd fold_right audit_phi_input_graph_body_work] in Htarget_work |- *; lia.
  - intros n edge Hin Hedge.
    rewrite <- (Hout n) in Hedge.
    pose proof (audit_phi_input_target_envelope N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) n edge Hin Hedge) as [_ Henvelope].
    specialize (Hnode (fst (target edge))).
    unfold audit_phi_input_graph_callbacks.
    cbn [audit_prepare_target_model audit_prepare_encode_model].
    destruct (target edge) as [vertex body]; cbn [fst] in Hnode, Henvelope |- *.
    destruct (node_enc vertex).
    cbn [snd fold_right audit_phi_input_graph_body_work] in Hnode |- *; lia.
Qed.

Lemma audit_phi_predecessors_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) g (base : prepared EN g) n :
  (forall node, fst (node_enc node) = encode EN node) ->
  fst (@audit_phi_predecessors_counted N E CN EN node_enc g base n) = pred_edges base n.
Proof.
  intro Hnode.
  unfold audit_phi_predecessors_counted, pred_edges, index_edges.
  pose proof (audit_map_get_erases N _ CN node_enc EN n (in_index base) (Hnode n)) as Hget.
  destruct (audit_map_get node_enc n (in_index base)); cbn [fst] in Hget |- *.
  now rewrite Hget.
Qed.

(** Initial preparation and the counted producer return the exact plain graph and map. *)
Theorem audit_memory_phi_prune_counted_erases : audit_memory_phi_prune_counted_erases_statement.
Proof.
  intros N E T CN CE OE TE PE EN EE node_enc edge_enc out target operand g effects mg
    Hnode Hedge Hout Htarget Hoperand.
  unfold audit_memory_phi_prune_counted.
  pose proof (audit_prepare_source_correct N E _ EN g
    (audit_phi_input_graph_callbacks node_enc out target) (fun _ => 0)
    (audit_phi_input_graph_callbacks_erases N E CN OE TE EN node_enc out target g
      Hnode Hout Htarget)) as Hprepare.
  destruct (audit_prepare_source_counted EN g (audit_phi_input_graph_callbacks node_enc out target))
    as [base preparation].
  destruct Hprepare as [Hbase _].
  split; [exact Hbase|].
  apply audit_memory_phi_producer_erases; try assumption.
  intro n; rewrite Hbase.
  apply audit_phi_predecessors_erases; exact Hnode.
Qed.

(** Preparation work and actual predecessor reads compose with the complete producer bound. *)
Theorem audit_memory_phi_prune_whole_input_bound :
  audit_memory_phi_prune_whole_input_bound_statement.
Proof.
  intros N E T CN CE OE TE PE EN EE node_enc edge_enc out target operand
    node_work edge_work out_work target_work operand_work
    node_budget edge_budget out_budget target_budget operand_budget g effects mg
    Hencode Hout Htarget Hnode Hedge Hout_work Htarget_work Hoperand.
  unfold audit_memory_phi_prune_counted.
  pose proof (audit_phi_input_preparation_bound N E CN OE TE EN node_enc out target node_work
    out_work target_work node_budget out_budget target_budget g Hencode Hout Htarget Hnode
    Hout_work Htarget_work) as Hprepare.
  destruct (audit_prepare_source_counted EN g (audit_phi_input_graph_callbacks node_enc out target))
    as [base preparation].
  pose proof (audit_phi_producer_whole_input_bound N E T CN CE _ PE EN EE node_enc edge_enc
    (audit_phi_predecessors_counted EN node_enc g base) operand node_work edge_work
    (audit_map_source_work node_work) operand_work node_budget edge_budget
    (audit_phi_get_input_budget node_enc node_budget) operand_budget g effects mg Hencode Hnode
    Hedge) as Hproducer.
  assert (Hpred : forall n, audit_map_source_work node_work
    (snd (audit_phi_predecessors_counted EN node_enc g base n)) <=
      audit_phi_get_input_budget node_enc node_budget n).
  { intro n; unfold audit_phi_predecessors_counted.
    pose proof (audit_phi_get_input_bound N _ CN node_enc node_work node_budget n (in_index base)
      Hnode) as Hget.
    destruct (audit_map_get node_enc n (in_index base)); exact Hget. }
  specialize (Hproducer Hpred Hoperand).
  cbn [snd] in Hprepare; lia.
Qed.
