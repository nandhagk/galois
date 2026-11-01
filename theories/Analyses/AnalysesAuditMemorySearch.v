(** * Counted memory search

    This mirror follows each binary-fuel search step and preserves its actual primitive calls.
    For example, a previously seen version records a cut and never invokes its successor callback.
    Builds on: AnalysesMemoryWalk and the audit map and finite-set models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Analyses Require Import AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
Import List.ListNotations.

(** * Source-shaped search trace *)

Inductive audit_memory_search_event (V E NE : Type) : Type :=
  | AuditSearchFuel (fuel : positive) (state : memory_search_state V)
  | AuditSearchStep (state : memory_search_state V)
  | AuditSearchRead (events : list (audit_map_event V nat E))
  | AuditSearchWrite (events : list (audit_map_event V nat E))
  | AuditSearchRoot (events : list (audit_set_event V E))
  | AuditSearchNext (version : V) (result : list V) (events : list NE).

Arguments AuditSearchFuel {V E NE} _ _.
Arguments AuditSearchStep {V E NE} _.
Arguments AuditSearchRead {V E NE} _.
Arguments AuditSearchWrite {V E NE} _.
Arguments AuditSearchRoot {V E NE} _.
Arguments AuditSearchNext {V E NE} _ _ _.

(** All primitive events contain the exact pre-state, encoded operand and returned value. *)
Definition audit_memory_search_step {V E NE}
    (enc : V -> positive * list E) (next : V -> list V * list NE) (st : memory_search_state V)
    : memory_search_state V * list (audit_memory_search_event V E NE) :=
  match memory_search_todo st with
  | [] => (st, [AuditSearchStep st])
  | v :: rest =>
      let '(seen, reads) := audit_map_get enc v (memory_search_seen st) in
      match seen with
      | Some _ =>
          let '(roots, root_events) := audit_finset_add enc v (memory_search_roots st) in
          (MemorySearchState rest (memory_search_seen st) (memory_search_clock st) roots false,
            [AuditSearchStep st; AuditSearchRead reads; AuditSearchRoot root_events])
      | None =>
          let '(updated, writes) := audit_map_set enc v (memory_search_clock st)
            (memory_search_seen st) in
          let '(successors, successor_events) := next v in
          match successors with
          | [] =>
              let '(roots, root_events) := audit_finset_add enc v (memory_search_roots st) in
              (MemorySearchState rest updated (S (memory_search_clock st)) roots
                (memory_search_complete st),
                [AuditSearchStep st; AuditSearchRead reads; AuditSearchWrite writes;
                 AuditSearchNext v successors successor_events; AuditSearchRoot root_events])
          | w :: ws =>
              (MemorySearchState ((w :: ws) ++ rest) updated (S (memory_search_clock st))
                (memory_search_roots st) (memory_search_complete st),
                [AuditSearchStep st; AuditSearchRead reads; AuditSearchWrite writes;
                 AuditSearchNext v successors successor_events])
          end
      end
  end.

(** Binary recursion records early empty states and the exact intermediate state of both halves. *)
Fixpoint audit_memory_search_run {V E NE} (enc : V -> positive * list E)
    (next : V -> list V * list NE) (fuel : positive) (st : memory_search_state V)
    : memory_search_state V * list (audit_memory_search_event V E NE) :=
  match memory_search_todo st with
  | [] => (st, [AuditSearchFuel fuel st])
  | _ =>
      match fuel with
      | xH =>
          let '(out, events) := audit_memory_search_step enc next st in
          (out, AuditSearchFuel fuel st :: events)
      | xO half =>
          let '(middle, first) := audit_memory_search_run enc next half st in
          let '(out, second) := audit_memory_search_run enc next half middle in
          (out, AuditSearchFuel fuel st :: first ++ second)
      | xI half =>
          let '(middle, first) := audit_memory_search_run enc next half st in
          let '(after, second) := audit_memory_search_run enc next half middle in
          let '(out, final) := audit_memory_search_step enc next after in
          (out, AuditSearchFuel fuel st :: first ++ second ++ final)
      end
  end.

(** * Future correctness and input bounds *)

Fixpoint audit_memory_search_steps {V E NE}
    (events : list (audit_memory_search_event V E NE)) : nat :=
  match events with
  | [] => 0
  | AuditSearchStep _ :: rest => S (audit_memory_search_steps rest)
  | _ :: rest => audit_memory_search_steps rest
  end.

(** Matching version codes recover the plain search with the same fuel, state and next callback. *)
Definition audit_memory_search_run_erases_statement : Prop :=
  forall V E NE (original : encoding V) (enc : V -> positive * list E)
      (next : V -> list V * list NE) fuel st,
    (forall v, fst (enc v) = encode original v) ->
    fst (audit_memory_search_run enc next fuel st) =
      memory_search_run original (fun v => fst (next v)) fuel st.

(** The counted search takes at most its positive fuel in steps. *)
Definition audit_memory_search_step_bound_statement : Prop :=
  forall V E NE (enc : V -> positive * list E) (next : V -> list V * list NE) fuel st,
    audit_memory_search_steps (snd (audit_memory_search_run enc next fuel st)) <= Pos.to_nat fuel.

(** * Fixed search charges and nested actual primitive work *)

Fixpoint audit_memory_search_primitive_work {V E NE} (encoder_work : list E -> nat)
    (next_work : list NE -> nat) (events : list (audit_memory_search_event V E NE)) : nat :=
  match events with
  | [] => 0
  | AuditSearchRead calls :: rest => audit_map_source_work encoder_work calls +
      audit_memory_search_primitive_work encoder_work next_work rest
  | AuditSearchWrite calls :: rest => audit_map_source_work encoder_work calls +
      audit_memory_search_primitive_work encoder_work next_work rest
  | AuditSearchRoot calls :: rest => audit_finset_source_work encoder_work calls +
      audit_memory_search_primitive_work encoder_work next_work rest
  | AuditSearchNext _ successors calls :: rest => length successors + next_work calls +
      audit_memory_search_primitive_work encoder_work next_work rest
  | _ :: rest => audit_memory_search_primitive_work encoder_work next_work rest
  end.

Fixpoint audit_memory_search_source_work {V E NE} (encoder_work : list E -> nat)
    (next_work : list NE -> nat) (events : list (audit_memory_search_event V E NE)) : nat :=
  match events with
  | [] => 0
  | AuditSearchFuel _ _ :: rest => 2 + audit_memory_search_source_work encoder_work next_work rest
  | AuditSearchStep _ :: rest => 2 + audit_memory_search_source_work encoder_work next_work rest
  | AuditSearchRead calls :: rest => audit_map_source_work encoder_work calls +
      audit_memory_search_source_work encoder_work next_work rest
  | AuditSearchWrite calls :: rest => audit_map_source_work encoder_work calls +
      audit_memory_search_source_work encoder_work next_work rest
  | AuditSearchRoot calls :: rest => audit_finset_source_work encoder_work calls +
      audit_memory_search_source_work encoder_work next_work rest
  | AuditSearchNext _ successors calls :: rest => 2 + length successors + next_work calls +
      audit_memory_search_source_work encoder_work next_work rest
  end.

(** Search source work is bounded by eight units per fuel step plus captured primitive work. *)
Definition audit_memory_search_source_bound_statement : Prop :=
  forall V E NE (enc : V -> positive * list E) (next : V -> list V * list NE)
      encoder_work next_work fuel st,
    let events := snd (audit_memory_search_run enc next fuel st) in
    audit_memory_search_source_work encoder_work next_work events <=
      8 * Pos.to_nat fuel + audit_memory_search_primitive_work encoder_work next_work events.
