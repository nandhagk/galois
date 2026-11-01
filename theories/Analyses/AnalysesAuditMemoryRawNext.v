(** * Counted raw memory successors

    This mirror retains actual incoming occurrences, operands, indexed effects and scope tests.
    For example, a missing operand produces no successor but retains its callback event.
    Builds on: AnalysesMemoryWalk and the memory effect and disjointness observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryEffects AnalysesAuditMemoryDisjoint.
Import List.ListNotations.

Inductive audit_raw_next_event (N E T CE SE IE OE BE : Type) : Type :=
  | AuditRawBranch (version : memory_version N E)
  | AuditRawIncoming (node : N) (edges : list E) (events : list IE)
  | AuditRawOperand (node : N) (key : option E) (result : option (memory_version N E))
      (events : list OE)
  | AuditRawEffectGet (events : list (audit_memory_effect_get_event E T CE))
  | AuditRawBefore (edge : E) (index : nat) (result : option (memory_version N E))
      (events : list BE)
  | AuditRawDisjoint (left right : memory_scope T) (result : bool)
      (events : list (audit_disjoint_event T SE)).

Arguments AuditRawBranch {N E T CE SE IE OE BE} _.
Arguments AuditRawIncoming {N E T CE SE IE OE BE} _ _ _.
Arguments AuditRawOperand {N E T CE SE IE OE BE} _ _ _ _.
Arguments AuditRawEffectGet {N E T CE SE IE OE BE} _.
Arguments AuditRawBefore {N E T CE SE IE OE BE} _ _ _ _.
Arguments AuditRawDisjoint {N E T CE SE IE OE BE} _ _ _ _.

(** Every key occurrence calls the actual operand function and preserves its nested trace. *)
Fixpoint audit_memory_operands {N E T CE SE IE OE BE}
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (node : N) (keys : list (option E))
    : list (memory_version N E) * list (audit_raw_next_event N E T CE SE IE OE BE) :=
  match keys with
  | [] => ([], [])
  | key :: rest =>
      let '(entry, oe) := operand node key in
      let '(tail, events) := @audit_memory_operands N E T CE SE IE OE BE operand node rest in
      (
        match entry with
        | Some v => v :: tail
        | None => tail
        end,
        AuditRawOperand node key entry oe :: events)
  end.

(** Both strict boolean operands and their nested calls are retained at definitions. *)
Definition audit_memory_raw_next {N E T CE SE IE OE BE}
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (incoming : N -> list E * list IE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (q : memory_scope T) (v : memory_version N E)
    : list (memory_version N E) * list (audit_raw_next_event N E T CE SE IE OE BE) :=
  match v with
  | MemoryLive => ([], [AuditRawBranch v])
  | MemoryPhi n =>
      let '(edges, ie) := incoming n in
      let '(out, oe) := @audit_memory_operands N E T CE SE IE OE BE operand n
        (None :: map Some edges) in
      (out, [AuditRawBranch v; AuditRawIncoming n edges ie] ++ oe)
  | MemoryDef e i =>
      let '(effect, ee) := audit_memory_effect_get edge_enc table e i in
      match effect with
      | None => ([], [AuditRawBranch v; AuditRawEffectGet ee])
      | Some a =>
        let '(previous, be) := before e i in
        match previous with
        | Some p =>
          let writes := effect_writes a in
          let '(disjoint, de) := audit_memory_scopes_disjoint site_enc writes q in
          let result := if andb (effect_is_def a) disjoint then [p] else [] in
          (result, [AuditRawBranch v; AuditRawEffectGet ee; AuditRawBefore e i previous be;
                    AuditRawDisjoint writes q disjoint de])
        | None => ([], [AuditRawBranch v; AuditRawEffectGet ee; AuditRawBefore e i previous be])
        end
      end
  end.

(** * Future exact-result and occurrence-count obligations *)

(** Matching callbacks recover the plain next versions while keeping the supplied incoming edges. *)
Definition audit_memory_raw_next_erases_statement : Prop :=
  forall N E T CE SE IE OE BE (EE : encoding E) (ET : encoding T)
      (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
      table (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE) mg q v,
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    fst (audit_memory_raw_next edge_enc site_enc table incoming operand before q v) =
      memory_walk_raw_next EE ET table (fun n => fst (incoming n)) mg q v.

(** Operand traversal emits one event for each key. *)
Definition audit_memory_operands_count_statement : Prop :=
  forall N E T CE SE IE OE BE
      (operand : N -> option E -> option (memory_version N E) * list OE) node keys,
    length (snd (@audit_memory_operands N E T CE SE IE OE BE operand node keys)) = length keys.

(** * Actual child work and occurrence-sensitive bound *)

Fixpoint audit_raw_next_primitive_work {N E T CE SE IE OE BE}
    (edge_work : list CE -> nat) (site_work : list SE -> nat)
    (incoming_work : list IE -> nat) (operand_work : list OE -> nat)
    (before_work : list BE -> nat) (events : list (audit_raw_next_event N E T CE SE IE OE BE))
    : nat :=
  match events with
  | [] => 0
  | AuditRawIncoming _ edges calls :: rest => length edges + incoming_work calls +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  | AuditRawOperand _ _ _ calls :: rest => operand_work calls +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  | AuditRawEffectGet calls :: rest => audit_memory_effect_get_work edge_work calls +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  | AuditRawBefore _ _ _ calls :: rest => before_work calls +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  | AuditRawDisjoint _ _ _ calls :: rest => audit_disjoint_source_work site_work calls +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  | _ :: rest =>
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work rest
  end.

Definition audit_raw_next_source_work {N E T CE SE IE OE BE}
    (edge_work : list CE -> nat) (site_work : list SE -> nat)
    (incoming_work : list IE -> nat) (operand_work : list OE -> nat) (before_work : list BE -> nat)
    (events : list (audit_raw_next_event N E T CE SE IE OE BE)) : nat :=
  2 * length events +
    audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work events.

(** Raw successor work is bounded by fixed control, all incoming phi-edge occurrences and
    captured primitive work. *)
Definition audit_raw_next_source_bound_statement : Prop :=
  forall N E T CE SE IE OE BE (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) table (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE) q v
      edge_work site_work incoming_work operand_work before_work,
    let events := snd (audit_memory_raw_next edge_enc site_enc table incoming operand before q v) in
    audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work events <=
      8 + 2 * (
        match v with
        | MemoryPhi n => length (fst (incoming n))
        | _ => 0
        end) +
      audit_raw_next_primitive_work edge_work site_work incoming_work operand_work before_work
        events.

(** The first missing effect suppresses the later memory-before callback in the source match. *)
Example audit_raw_next_first_missing_skips_before :
  let edge_enc := fun e : positive => (e, @nil unit) in
  let site_enc := fun t : positive => (t, @nil unit) in
  let incoming := fun _ : positive => (@nil positive, @nil unit) in
  let operand := fun (_ : positive) (_ : option positive) =>
    (@None (memory_version positive positive), @nil unit) in
  let before := fun (_ : positive) (_ : nat) =>
    (Some (@MemoryLive positive positive), [tt]) in
  let events := snd (audit_memory_raw_next edge_enc site_enc Map.empty incoming operand before
    MemoryAll (MemoryDef 1%positive 0)) in
  length events = 2 /\
  (forall e i result body, ~ In (AuditRawBefore e i result body) events).
Proof.
  vm_compute.
  split.
  - reflexivity.
  - intros e i result body [Hbranch | [Heffect | Hempty]].
    + discriminate Hbranch.
    + discriminate Heffect.
    + exact Hempty.
Qed.
