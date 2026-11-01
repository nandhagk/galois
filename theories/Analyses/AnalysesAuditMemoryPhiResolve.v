(** * Counted phi representative resolution

    This candidate fixes each indexed lookup, representative check and strict comparison.
    For example, a cyclic phi leaves the representative map unchanged.
    Builds on: AnalysesAuditMemoryPhiState and the shared collection observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditMap CollectionsAuditFinSet.
Import List.ListNotations.

Inductive audit_phi_resolve_event (N E CN CV : Type) : Type :=
  | AuditPhiCycleProbe (node : N) (result : bool) (events : list (audit_set_event N CN))
  | AuditPhiInputsProbe (node : N) (result : option (list (option E * memory_version N E)))
      (events : list (audit_map_event N (list (option E * memory_version N E)) CN))
  | AuditPhiRepresentative (input output : memory_version N E)
      (events : list (audit_map_event (memory_version N E) (memory_version N E) CV))
  | AuditPhiVersionEncode (input : memory_version N E) (code : positive) (events : list CV)
  | AuditPhiCompare (left right : positive) (result : bool) (events : list audit_positive_eqb_event)
  | AuditPhiForall (remaining : list (option E * memory_version N E))
  | AuditPhiWrite (events : list (audit_map_event (memory_version N E) (memory_version N E) CV)).

Arguments AuditPhiCycleProbe {N E CN CV} _ _ _.
Arguments AuditPhiInputsProbe {N E CN CV} _ _ _.
Arguments AuditPhiRepresentative {N E CN CV} _ _ _.
Arguments AuditPhiVersionEncode {N E CN CV} _ _ _.
Arguments AuditPhiCompare {N E CN CV} _ _ _ _.
Arguments AuditPhiForall {N E CN CV} _.
Arguments AuditPhiWrite {N E CN CV} _.

(** Lookup retains the actual stored representative or the original fallback. *)
Definition audit_phi_rep {N E CN CV}
    (enc : memory_version N E -> positive * list CV)
    (reps : Map.t (memory_version N E) (memory_version N E)) (input : memory_version N E)
    : memory_version N E * list (audit_phi_resolve_event N E CN CV) :=
  let '(found, events) := audit_map_get enc input reps in
  let output :=
    match found with
    | Some v => v
    | None => input
    end in
  (output, [AuditPhiRepresentative input output events]).

(** This executes both actual encoders and the fixed positive-equality observer. *)
Definition audit_phi_compare {N E CN CV}
    (enc : memory_version N E -> positive * list CV) (left right : memory_version N E)
    : bool * list (audit_phi_resolve_event N E CN CV) :=
  let '(lc, le) := enc left in
  let '(rc, re) := enc right in
  let '(result, eq) := audit_positive_eqb lc rc in
  (result, [AuditPhiVersionEncode left lc le; AuditPhiVersionEncode right rc re;
            AuditPhiCompare lc rc result eq]).

(** Every remaining operand is evaluated, including after a false previous comparison. *)
Fixpoint audit_phi_all_same {N E CN CV}
    (enc : memory_version N E -> positive * list CV)
    (reps : Map.t (memory_version N E) (memory_version N E))
    (candidate : memory_version N E) (input : list (option E * memory_version N E))
    : bool * list (audit_phi_resolve_event N E CN CV) :=
  match input with
  | [] => (true, [AuditPhiForall input])
  | (_, v) :: rest =>
      let '(rep, re) := @audit_phi_rep N E CN CV enc reps v in
      let '(equal, ee) := audit_phi_compare enc candidate rep in
      let '(tail, te) := audit_phi_all_same enc reps candidate rest in
      (andb equal tail, AuditPhiForall input :: re ++ ee ++ te)
  end.

(** One candidate resolution step fixes the source call order and persistent map result. *)
Definition audit_phi_resolve_step {N E CN CV} (EN : encoding N)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (index : phi_dependency_index (E := E) EN)
    (reps : Map.t (memory_version N E) (memory_version N E)) (n : N)
    : Map.t (memory_version N E) (memory_version N E) * list (audit_phi_resolve_event N E CN CV) :=
  let '(cyclic, ce) := audit_finset_mem node_enc n (phi_index_cycles index) in
  if cyclic then (reps, [AuditPhiCycleProbe n cyclic ce]) else
    let '(row, ie) := audit_map_get node_enc n (phi_index_inputs index) in
    match row with
    | None | Some [] => (reps, [AuditPhiCycleProbe n cyclic ce; AuditPhiInputsProbe n row ie])
    | Some ((_, v) :: rest) =>
        let '(candidate, re) := @audit_phi_rep N E CN CV version_enc reps v in
        let '(self, se) := audit_phi_compare version_enc candidate (MemoryPhi n) in
        let '(all_same, ae) := audit_phi_all_same version_enc reps candidate rest in
        if andb (negb self) all_same then
          let '(out, we) := audit_map_set version_enc (MemoryPhi n) candidate reps in
          (out, [AuditPhiCycleProbe n cyclic ce; AuditPhiInputsProbe n row ie] ++ re ++ se ++ ae ++
            [AuditPhiWrite we])
        else (reps, [AuditPhiCycleProbe n cyclic ce; AuditPhiInputsProbe n row ie] ++ re ++ se ++
          ae)
    end.

(** * Future semantic and strict traversal obligations *)

(** Matching node and version encoders make the counted resolution output a relational step. *)
Definition audit_phi_resolve_step_refines_statement : Prop :=
  forall N E CN CV (EN : encoding N) (EE : encoding E) (index : phi_dependency_index (E := E) EN)
      (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
      reps n,
    (forall x, fst (node_enc x) = encode EN x) ->
    (forall x, fst (version_enc x) = encode (memory_version_encoding EN EE) x) ->
    phi_resolve_step EN EE index reps n (fst (audit_phi_resolve_step EN node_enc version_enc index
      reps n)).

(** Fixed outer-frame work plus the exact captured primitive and encoder child traces. *)
Fixpoint audit_phi_resolve_primitive_work {N E CN CV}
    (node_work : list CN -> nat) (version_work : list CV -> nat)
    (events : list (audit_phi_resolve_event N E CN CV)) : nat :=
  match events with
  | [] => 0
  | AuditPhiCycleProbe _ _ calls :: rest => audit_finset_source_work node_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiInputsProbe _ _ calls :: rest => audit_map_source_work node_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiRepresentative _ _ calls :: rest => audit_map_source_work version_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiVersionEncode _ _ calls :: rest => version_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiCompare _ _ _ calls :: rest => audit_positive_eqb_source_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiForall _ :: rest => audit_phi_resolve_primitive_work node_work version_work rest
  | AuditPhiWrite calls :: rest => audit_map_source_work version_work calls +
      audit_phi_resolve_primitive_work node_work version_work rest
  end.

Definition audit_phi_resolve_source_work {N E CN CV}
    (node_work : list CN -> nat) (version_work : list CV -> nat)
    (events : list (audit_phi_resolve_event N E CN CV)) : nat :=
  2 * length events + audit_phi_resolve_primitive_work node_work version_work events.

(** One resolution step is bounded by fixed control, the actual stored row length and captured
    primitive work. *)
Definition audit_phi_resolve_source_bound_statement : Prop :=
  forall N E CN CV (EN : encoding N) (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (index : phi_dependency_index (E := E) EN) reps n node_work version_work,
    let events := snd (audit_phi_resolve_step EN node_enc version_enc index reps n) in
    let row := fst (audit_map_get node_enc n (phi_index_inputs index)) in
    audit_phi_resolve_source_work node_work version_work events <=
      16 + 10 * length (
        match row with
        | None => []
        | Some actual => actual
        end) +
      audit_phi_resolve_primitive_work node_work version_work events.

(** * Complete ordered resolution pass *)

(** Each next step sees the exact persistent map returned by the previous step. *)
Fixpoint audit_phi_resolve_all {N E CN CV} (EN : encoding N)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (index : phi_dependency_index (E := E) EN) (nodes : list N)
    (reps : Map.t (memory_version N E) (memory_version N E))
    : Map.t (memory_version N E) (memory_version N E) * list (audit_phi_resolve_event N E CN CV) :=
  match nodes with
  | [] => (reps, [])
  | n :: rest =>
      let '(next, first) := audit_phi_resolve_step EN node_enc version_enc index reps n in
      let '(final, tail) := audit_phi_resolve_all EN node_enc version_enc index rest next in
      (final, first ++ tail)
  end.

(** Matching node and version encoders make the counted full resolution output a relational
    trace. *)
Definition audit_phi_resolve_all_refines_statement : Prop :=
  forall N E CN CV (EN : encoding N) (EE : encoding E) (index : phi_dependency_index (E := E) EN)
      (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
      nodes reps,
    (forall x, fst (node_enc x) = encode EN x) ->
    (forall x, fst (version_enc x) = encode (memory_version_encoding EN EE) x) ->
    phi_resolve_trace EN EE index nodes reps
      (fst (audit_phi_resolve_all EN node_enc version_enc index nodes reps)).

(** The budget charges actual rows and child traces at each changing representative map. *)
Fixpoint audit_phi_resolve_all_budget {N E CN CV} (EN : encoding N)
    (node_enc : N -> positive * list CN) (version_enc : memory_version N E -> positive * list CV)
    (index : phi_dependency_index (E := E) EN) (nodes : list N)
    (reps : Map.t (memory_version N E) (memory_version N E))
    (node_work : list CN -> nat) (version_work : list CV -> nat) : nat :=
  match nodes with
  | [] => 0
  | n :: rest =>
      let '(next, events) := audit_phi_resolve_step EN node_enc version_enc index reps n in
      let row := fst (audit_map_get node_enc n (phi_index_inputs index)) in
      16 + 10 * length (
        match row with
        | None => []
        | Some actual => actual
        end) +
        audit_phi_resolve_primitive_work node_work version_work events +
        audit_phi_resolve_all_budget EN node_enc version_enc index rest next node_work version_work
  end.

(** Full resolution source work is bounded by the recurrence over input nodes and intermediate
    representative maps. *)
Definition audit_phi_resolve_all_source_bound_statement : Prop :=
  forall N E CN CV (EN : encoding N) (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (index : phi_dependency_index (E := E) EN) nodes reps node_work version_work,
    audit_phi_resolve_source_work node_work version_work
      (snd (audit_phi_resolve_all EN node_enc version_enc index nodes reps)) <=
    audit_phi_resolve_all_budget EN node_enc version_enc index nodes reps node_work version_work.
