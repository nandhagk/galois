(** * Weak topological order audit examples

    Exercise actual WTO traces and captured graph callbacks on small graphs.
    For example, a cyclic component opens a nested self-loop.
    Builds on: GraphAuditWto and GraphGRA1a. *)

From Stdlib Require Import List Bool PArith Arith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphWto GraphAuditDfs
  GraphAuditScc GraphAuditBase GraphAuditWto GraphAuditWtoAdequacy.
From Galois.Tests.Graph Require Import GraphGRA1a.
Import List.ListNotations.

(** * Empty input and component choices *)

(** Removing from an empty component records the empty case. *)
Example wto_remove_empty :
    @audit_wto_remove_counted nat nat nat_encoding 0 [] = ([], [AuditWtoCase 4]).
Proof.
  reflexivity.
Qed.

(** Removing the head retains a distinct vertex. *)
Example wto_remove_keeps_other_vertex :
    fst (@audit_wto_remove_counted nat nat nat_encoding 0 [0; 1]) = [1].
Proof.
  reflexivity.
Qed.

(** The checker accepts the empty graph and empty ordering. *)
Example wto_empty_checker_accepts :
    check_wto (prepare nat_encoding empty_graph) [] = true.
Proof.
  reflexivity.
Qed.

(** The callback records the vertex or edge passed by the actual construction. *)
Definition wto_example_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (Graph.target example_graph edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

(** Recognize an actual WTO encoder receipt, including its result and body. *)
Definition wto_encoder_receipt (vertex : nat)
    (item : audit_wto_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match item with
  | (AuditWtoWrite actual _ _, [AuditGraphEncodeCapture _ _ _ captured code [body]]) =>
    Nat.eqb vertex actual && Nat.eqb vertex captured &&
      Pos.eqb code (encode nat_encoding vertex) && Nat.eqb body (300 + vertex)
  | _ => false
  end.

(** The actual rank-building run records the encoder result and body for vertex zero. *)
Example wto_rank_callback_receipt :
    existsb (wto_encoder_receipt 0)
      (snd (audit_wto_source_counted (prepare nat_encoding example_graph)
        wto_example_callbacks)) = true.
Proof.
  reflexivity.
Qed.

(** The checker accepts the computed ordering for the nontrivial graph. *)
Example wto_checker_accepts_example_graph :
    check_wto (prepare nat_encoding example_graph)
      (wto_of (prepare nat_encoding example_graph)) = true.
Proof.
  reflexivity.
Qed.

(** Recognize an SCC target call made inside the WTO traversal. *)
Definition wto_scc_target_receipt (edge vertex : nat)
    (item : audit_wto_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match item with
  | (AuditWtoScc (AuditTarjanTarget actual_edge actual_vertex),
      [AuditGraphTargetCapture _ _ _ captured_edge captured_vertex [body]]) =>
    Nat.eqb edge actual_edge && Nat.eqb vertex actual_vertex &&
      Nat.eqb edge captured_edge && Nat.eqb vertex captured_vertex && Nat.eqb body (200 + edge)
  | _ => false
  end.

(** SCC recursion records the real edge target and rejects a different target. *)
Example wto_scc_callback_receipt :
    existsb (wto_scc_target_receipt 10 2)
      (snd (audit_wto_source_counted (prepare nat_encoding example_graph)
        wto_example_callbacks)) = true /\
    existsb (wto_scc_target_receipt 10 3)
      (snd (audit_wto_source_counted (prepare nat_encoding example_graph)
        wto_example_callbacks)) = false.
Proof.
  split; reflexivity.
Qed.

(** The checker rejects an empty ordering for the nonempty graph. *)
Example wto_checker_rejects_missing_vertices :
    check_wto (prepare nat_encoding example_graph) [] = false.
Proof.
  reflexivity.
Qed.

(** The nontrivial run has events and its original-input event budget accepts them. *)
Example wto_example_event_budget_accepts :
    let p := prepare nat_encoding example_graph in
    let events := snd (audit_wto_counted p) in
    Nat.ltb 0 (length events) = true /\
      Nat.leb (length events) (audit_wto_input_event_bound p) = true.
Proof.
  split.
  - reflexivity.
  - apply Nat.leb_le, audit_wto_counted_event_bound.
Qed.

(** The source event theorem is available to an importing client. *)
Example wto_source_event_contract_witness :
    audit_wto_source_event_correspondence_statement.
Proof.
  exact audit_wto_source_event_correspondence_holds.
Qed.

(** The model work bound is checked symbolically against the nonempty actual run. *)
Example wto_example_model_budget_accepts :
    let p := prepare nat_encoding example_graph in
    let events := snd (audit_wto_counted p) in
    Nat.ltb 0 (audit_wto_model_work nat_encoding events) = true /\
    Nat.leb (audit_wto_model_work nat_encoding events)
      (audit_wto_input_budget nat_encoding example_graph p) = true.
Proof.
  split.
  - reflexivity.
  - apply Nat.leb_le.
    pose proof (audit_wto_counted_correct nat nat nat_encoding example_graph
      (prepare nat_encoding example_graph)) as Hbound.
    destruct (audit_wto_counted (prepare nat_encoding example_graph)) as [result events].
    exact (proj2 (proj2 Hbound)).
Qed.

(** The captured source budget includes the actual callback bodies of the same run. *)
Example wto_example_source_budget_accepts :
    let p := prepare nat_encoding example_graph in
    let events := snd (audit_wto_source_counted p wto_example_callbacks) in
    Nat.ltb 0 (length events) = true /\
    Nat.leb (audit_wto_source_work (fun _ => 1) events)
      (audit_wto_source_budget nat_encoding example_graph p +
        audit_wto_source_body_work (fun _ => 1) events) = true.
Proof.
  split.
  - reflexivity.
  - apply Nat.leb_le.
    pose proof (audit_wto_source_holds nat nat nat nat_encoding example_graph
      (prepare nat_encoding example_graph) wto_example_callbacks (fun _ => 1)) as Hbound.
    assert (Hcallbacks :
      audit_dfs_callbacks_erase nat_encoding example_graph wto_example_callbacks).
    { split; intro value; reflexivity. }
    specialize (Hbound Hcallbacks).
    destruct (audit_wto_source_counted (prepare nat_encoding example_graph) wto_example_callbacks)
      as [result events].
    exact (proj2 (proj2 Hbound)).
Qed.

(** Both callback adapters budget the single recorded item from each example callback. *)
Example wto_example_external_budget_accepts :
    let p := prepare nat_encoding example_graph in
    let events := snd (audit_wto_source_counted p wto_example_callbacks) in
    Nat.leb (audit_wto_source_work (fun _ => 1) events)
      (audit_wto_source_budget nat_encoding example_graph p +
        audit_wto_source_external_budget (fun _ => 1) (fun _ => 1) events) = true.
Proof.
  apply Nat.leb_le.
  pose proof (audit_wto_source_adapted_holds nat nat nat nat_encoding example_graph
    (prepare nat_encoding example_graph) wto_example_callbacks (fun _ => 1)
    (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ => 1) (fun _ => 1)) as Hbound.
  assert (Hcallbacks : audit_dfs_callbacks_erase nat_encoding example_graph wto_example_callbacks).
  { split; intro value; reflexivity. }
  assert (Hencode : audit_graph_external_callback_adapter
    (audit_dfs_encode_model wto_example_callbacks) (fun _ => 1) (fun _ _ _ _ => True) (fun _ => 1)).
  { constructor; intros arg result body Hcall; cbn in Hcall; inversion Hcall; cbn; auto. }
  assert (Htarget : audit_graph_external_callback_adapter
    (audit_dfs_target_model wto_example_callbacks) (fun _ => 1) (fun _ _ _ _ => True) (fun _ => 1)).
  { constructor; intros arg result body Hcall; cbn in Hcall; inversion Hcall; cbn; auto. }
  specialize (Hbound Hcallbacks Hencode Htarget).
  destruct (audit_wto_source_counted (prepare nat_encoding example_graph) wto_example_callbacks)
    as [result events].
  exact (proj2 Hbound).
Qed.

(** * Cyclic decomposition and same-run costs *)

(** Vertices zero and one form an SCC; vertex one also has a self-loop. *)
Definition wto_cyclic_graph : Graph.t nat nat :=
  {| Graph.entries := [0]; Graph.nodes := [0; 1];
     Graph.out := fun vertex =>
       match vertex with
       | 0 => [10]
       | 1 => [11; 12]
       | _ => []
       end;
     Graph.source := fun edge => if Nat.eqb edge 10 then 0 else 1;
     Graph.target := fun edge => if Nat.eqb edge 11 then 0 else 1 |}.

(** Each callback records its actual operand in a one-item body. *)
Definition wto_cyclic_callbacks : audit_dfs_callback_model nat nat nat :=
  AuditDfsCallbackModel nat nat nat
    (fun edge => (Graph.target wto_cyclic_graph edge, [200 + edge]))
    (fun vertex => (encode nat_encoding vertex, [300 + vertex])).

(** This single source run supplies the result, receipts, and work observations. *)
Definition wto_cyclic_run :=
  audit_wto_source_counted (prepare nat_encoding wto_cyclic_graph) wto_cyclic_callbacks.

(** Recognize the actual lookup of vertex one's outgoing edges and its encoder body. *)
Definition wto_cyclic_out_receipt
    (item : audit_wto_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match item with
  | (AuditWtoEdges vertex _ (Some [first; second]),
      [AuditGraphEncodeCapture _ _ _ captured code [body]]) =>
    Nat.eqb vertex 1 && Nat.eqb captured 1 && Pos.eqb code (encode nat_encoding 1) &&
      Nat.eqb body 301 && Nat.eqb first 11 && Nat.eqb second 12
  | _ => false
  end.

(** Recognize the self-loop target callback and its captured operand, result, and body. *)
Definition wto_cyclic_self_receipt
    (item : audit_wto_nested_event nat nat (audit_graph_callback_capture nat nat nat)) : bool :=
  match item with
  | (AuditWtoTarget edge vertex,
      [AuditGraphTargetCapture _ _ _ captured_edge captured_vertex [body]]) =>
    Nat.eqb edge 12 && Nat.eqb vertex 1 && Nat.eqb captured_edge 12 &&
      Nat.eqb captured_vertex 1 && Nat.eqb body 212
  | _ => false
  end.

(** SCC decomposition groups both vertices, then retains the nested singleton. *)
Example wto_cyclic_components :
    components (scc_within (prepare nat_encoding wto_cyclic_graph) [0; 1]) = [[1; 0]] /\
    components (scc_within (prepare nat_encoding wto_cyclic_graph) [1]) = [[1]].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The source opens the two-vertex SCC and its nested self-loop; the checker accepts it. *)
Example wto_cyclic_source_and_checker :
    fst wto_cyclic_run = [WOpen 0; WOpen 1; WClose; WClose] /\
    check_wto (prepare nat_encoding wto_cyclic_graph) (fst wto_cyclic_run) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The same trace retains rank encoding, SCC target, outgoing lookup, and self-loop receipts. *)
Example wto_cyclic_callback_receipts :
    existsb (wto_encoder_receipt 0) (snd wto_cyclic_run) = true /\
    existsb (wto_scc_target_receipt 11 0) (snd wto_cyclic_run) = true /\
    existsb (wto_scc_target_receipt 11 1) (snd wto_cyclic_run) = false /\
    existsb wto_cyclic_out_receipt (snd wto_cyclic_run) = true /\
    existsb wto_cyclic_self_receipt (snd wto_cyclic_run) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Unit-weight work is computed exactly on the same finite cyclic source trace. *)
Example wto_cyclic_exact_work :
    (N.of_nat (length (snd wto_cyclic_run)),
      N.of_nat (audit_wto_source_body_work (fun _ => 1) (snd wto_cyclic_run)),
      N.of_nat (audit_wto_source_work (fun _ => 1) (snd wto_cyclic_run))) =
    (244%N, 93%N, 29232%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** The large input-derived budget is checked symbolically for that same cyclic trace. *)
Example wto_cyclic_source_budget :
    let p := prepare nat_encoding wto_cyclic_graph in
    Nat.leb (audit_wto_source_work (fun _ => 1) (snd wto_cyclic_run))
      (audit_wto_source_budget nat_encoding wto_cyclic_graph p +
        audit_wto_source_body_work (fun _ => 1) (snd wto_cyclic_run)) = true.
Proof.
  apply Nat.leb_le.
  pose proof (audit_wto_source_holds nat nat nat nat_encoding wto_cyclic_graph
    (prepare nat_encoding wto_cyclic_graph) wto_cyclic_callbacks (fun _ => 1)) as Hbound.
  assert (Hcallbacks :
    audit_dfs_callbacks_erase nat_encoding wto_cyclic_graph wto_cyclic_callbacks).
  { split; intro value; reflexivity. }
  specialize (Hbound Hcallbacks).
  unfold wto_cyclic_run.
  destruct (audit_wto_source_counted (prepare nat_encoding wto_cyclic_graph)
    wto_cyclic_callbacks) as [result events].
  exact (proj2 (proj2 Hbound)).
Qed.
