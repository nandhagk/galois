(** * Actual pruned output queries and semantic consumers

    Returned memory fields evaluate their original callback and then the actual representative map.
    For example, a missing before-occurrence returns None without a representative lookup.
    Builds on: full phi production and the unchanged history and byte contracts. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesAuditMemoryPhiState.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryPhiProducer
  AnalysesAuditMemoryPhiInputBudget AnalysesAuditMemoryPhiPlain.
Import List.ListNotations.

Inductive audit_phi_closure_event (I N E CV CE : Type) : Type :=
  | AuditPhiClosureCall (input : I) (result : option (memory_version N E)) (body : list CE)
  | AuditPhiClosureRead (input : memory_version N E) (result : option (memory_version N E))
      (body : list (audit_map_event (memory_version N E) (memory_version N E) CV)).
Arguments AuditPhiClosureCall {I N E CV CE} _ _ _.
Arguments AuditPhiClosureRead {I N E CV CE} _ _ _.

Definition audit_phi_output_optional_call {I N E CV CE}
    (version_enc : memory_version N E -> positive * list CV)
    (base : I -> option (memory_version N E) * list CE)
    (reps : Map.t (memory_version N E) (memory_version N E)) (input : I) :
    option (memory_version N E) * list (audit_phi_closure_event I N E CV CE) :=
  let '(found, body) := base input in
  match found with
  | None => (None, [AuditPhiClosureCall input found body])
  | Some v =>
      let '(representative, calls) := audit_map_get version_enc v reps in
      (Some (
        match representative with
        | Some r => r
        | None => v
        end),
        [AuditPhiClosureCall input found body; AuditPhiClosureRead v representative calls])
  end.

Definition audit_phi_output_total_call {I N E CV CE}
    (version_enc : memory_version N E -> positive * list CV)
    (base : I -> memory_version N E * list CE)
    (reps : Map.t (memory_version N E) (memory_version N E)) (input : I) :=
  audit_phi_output_optional_call version_enc
    (fun arg => let '(v, body) := base arg in (Some v, body)) reps input.

Fixpoint audit_phi_closure_source_work {I N E CV CE} (version_work : list CV -> nat)
    (base_work : list CE -> nat) (events : list (audit_phi_closure_event I N E CV CE)) : nat :=
  match events with
  | [] => 0
  | AuditPhiClosureCall _ _ body :: rest => 4 + base_work body +
      audit_phi_closure_source_work version_work base_work rest
  | AuditPhiClosureRead _ _ body :: rest => 4 + audit_map_source_work version_work body +
      audit_phi_closure_source_work version_work base_work rest
  end.

Definition audit_phi_closure_input_budget {I N E CV CE}
    (version_enc : memory_version N E -> positive * list CV)
    (base : I -> option (memory_version N E) * list CE)
    (version_budget : memory_version N E -> nat) (base_budget : I -> nat) (input : I) : nat :=
  4 + base_budget input +
  match fst (base input) with
  | None => 0
  | Some v => 4 + audit_phi_get_input_budget version_enc version_budget v
  end.

(** Version-encoding and base-callback budgets bound an optional closure call, including any
    representative lookup. *)
Definition audit_phi_closure_whole_input_bound_statement : Prop :=
  forall I N E CV CE (version_enc : memory_version N E -> positive * list CV)
      (base : I -> option (memory_version N E) * list CE)
      version_work base_work version_budget base_budget reps input,
    (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
    (forall arg, base_work (snd (base arg)) <= base_budget arg) ->
    audit_phi_closure_source_work version_work base_work
      (snd (audit_phi_output_optional_call version_enc base reps input)) <=
      audit_phi_closure_input_budget version_enc base version_budget base_budget input.

(** A matching version encoder and base result make optional closure output the representative
    of each present result. *)
Definition audit_phi_output_optional_erases_statement : Prop :=
  forall I N E CV CE (EN : encoding N) (EE : encoding E)
      (version_enc : memory_version N E -> positive * list CV)
      (base : I -> option (memory_version N E) * list CE) original reps input,
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    fst (base input) = original input ->
    fst (audit_phi_output_optional_call version_enc base reps input) =
      option_map (audit_phi_producer_rep EN EE reps) (original input).

(** Matching version encoding and input, output, before and operand callbacks recover all four
    produced graph fields. *)
Definition audit_phi_output_fields_erases_statement : Prop :=
  forall N E CN CE BE OE CV (EN : encoding N) (EE : encoding E)
      (version_enc : memory_version N E -> positive * list CV)
      (in_body : N -> memory_version N E * list CN)
      (out_body : E -> memory_version N E * list CE)
      (before_body : (E * nat) -> option (memory_version N E) * list BE)
      (operand_body : (N * option E) -> option (memory_version N E) * list OE) old reps,
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    (forall n, fst (in_body n) = memory_in old n) ->
    (forall e, fst (out_body e) = memory_out old e) ->
    (forall e i, fst (before_body (e, i)) = memory_before old e i) ->
    (forall n key, fst (operand_body (n, key)) = memory_operand old n key) ->
    let output := audit_phi_producer_output EN EE old reps in
    (forall n, fst (audit_phi_output_total_call version_enc in_body reps n) =
      Some (memory_in output n)) /\
    (forall e, fst (audit_phi_output_total_call version_enc out_body reps e) =
      Some (memory_out output e)) /\
    (forall e i, fst (audit_phi_output_optional_call version_enc before_body reps (e, i)) =
      memory_before output e i) /\
    (forall n key, fst (audit_phi_output_optional_call version_enc operand_body reps (n, key)) =
      memory_operand output n key).

(** This fixed pruning computation supplies the actual result used by semantic consumers. *)
Definition audit_memory_phi_prune N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    phi_result N E :=
  audit_phi_compute N E T EN EE g effects mg.

(** The fixed pruner satisfies the history, terminal, cycle, legacy-checker and conditional
    legacy-byte contracts. *)
Definition audit_memory_phi_prune_semantics_statement : Prop :=
  phi_projection_statement audit_memory_phi_prune /\
  phi_terminal_elimination_statement audit_memory_phi_prune /\
  phi_self_only_retained_statement audit_memory_phi_prune /\
  phi_cycle_retained_statement audit_memory_phi_prune /\
  phi_legacy_checked_statement audit_memory_phi_prune /\
  phi_legacy_byte_statement audit_memory_phi_prune.

(** Matching node and edge encoders, predecessors and operands make the counted graph and
    representatives agree with pruning. *)
Definition audit_memory_phi_producer_erases_statement : Prop :=
  forall N E T CN CE PE OE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (pred n) = pred_edges (prepare EN g) n) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    let run := audit_phi_produce EN EE node_enc edge_enc pred operand
      (audit_memory_version_encode node_enc edge_enc) g effects mg in
    let original := audit_memory_phi_prune N E T EN EE g effects mg in
    audit_phi_run_output EN run = phi_graph original /\
    audit_phi_run_representatives EN run = phi_representatives original.

Example audit_phi_closure_none_skips_representative :
  let enc := fun _ : memory_version positive positive => (1%positive, [tt]) in
  let base := fun _ : unit => (@None (memory_version positive positive), [tt; tt]) in
  let run := audit_phi_output_optional_call enc base Map.empty tt in
  fst run = None /\ length (snd run) = 1.
Proof.
  vm_compute.
  split; reflexivity.
Qed.
