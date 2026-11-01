(** * Independent operand budgets for memory observers

    These recurrences inspect the original key, scope, table and callback operands.
    For example, a definition pays its unary index conversion only when its edge row exists.
    Builds on: concrete encoder budgets and memory effect, scope and successor models. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditEncoderBudget CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryEffects
  AnalysesAuditMemoryDisjoint AnalysesAuditMemoryRawNext.
Import List.ListNotations.

Definition audit_memory_version_input_budget {N E CN CE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (node_budget : N -> nat) (edge_budget : E -> nat) (v : memory_version N E) : nat :=
  match v with
  | MemoryLive => 1
  | MemoryPhi n => 1 + node_budget n
  | MemoryDef e i => 1 +
      audit_pair_input_budget edge_enc audit_nat_encode edge_budget audit_nat_input_budget (e, i)
  end.

Definition audit_memory_footprint_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (fp : footprint T) : nat :=
  audit_pair_input_budget site_enc (audit_pair_encode audit_z_encode audit_z_encode)
    site_budget (audit_pair_input_budget audit_z_encode audit_z_encode
      (fun _ => 1) (fun _ => 1)) (fp_site fp, (fp_lo fp, fp_hi fp)).

Definition audit_memory_scope_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (q : memory_scope T) : nat :=
  match q with
  | MemoryAll => 2
  | MemoryRegions fs => 1 + audit_list_input_budget (audit_memory_footprint_encode site_enc)
      (audit_memory_footprint_input_budget site_enc site_budget) fs
  end.

Definition audit_memory_memo_key_input_budget {N E CN CE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (node_budget : N -> nat) (edge_budget : E -> nat) (key : positive * memory_version N E) : nat :=
  audit_pair_input_budget audit_positive_encode (audit_memory_version_encode node_enc edge_enc)
    (fun _ => 1) (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget) key.

(** Component callback budgets bound version, footprint, scope and memo-key encoding work. *)
Definition audit_memory_encoders_input_bound_statement : Prop :=
  forall N E T CN CE SE (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
      node_work edge_work site_work node_budget edge_budget site_budget,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall v, audit_memory_version_work node_work edge_work
      (snd (audit_memory_version_encode node_enc edge_enc v)) <=
      audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget v) /\
    (forall fp, audit_memory_footprint_work site_work
      (snd (audit_memory_footprint_encode site_enc fp)) <=
      audit_memory_footprint_input_budget site_enc site_budget fp) /\
    (forall q, audit_memory_scope_work site_work (snd (audit_memory_scope_encode site_enc q)) <=
      audit_memory_scope_input_budget site_enc site_budget q) /\
    (forall key, audit_memory_memo_key_work node_work edge_work
      (snd (audit_memory_memo_key_encode node_enc edge_enc key)) <=
      audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget key).

Definition audit_disjoint_pair_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (left right : footprint T) : nat :=
  4 + site_budget (fp_site left) + site_budget (fp_site right) +
  2 * Nat.min (Pos.size_nat (fst (site_enc (fp_site left))))
    (Pos.size_nat (fst (site_enc (fp_site right)))) +
  audit_binary_weight (fp_hi left) (fp_lo right) +
  audit_binary_weight (fp_hi right) (fp_lo left).

Fixpoint audit_disjoint_inner_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (left : footprint T) (right : list (footprint T)) : nat :=
  match right with
  | [] => 1
  | item :: rest => 1 + audit_disjoint_pair_input_budget site_enc site_budget left item +
      audit_disjoint_inner_input_budget site_enc site_budget left rest
  end.

Fixpoint audit_disjoint_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (left right : list (footprint T)) : nat :=
  match left with
  | [] => 1
  | item :: rest => 1 + audit_disjoint_inner_input_budget site_enc site_budget item right +
      audit_disjoint_input_budget site_enc site_budget rest right
  end.

Definition audit_scopes_disjoint_input_budget {T CE} (site_enc : T -> positive * list CE)
    (site_budget : T -> nat) (left right : memory_scope T) : nat :=
  match left, right with
  | MemoryRegions fs, MemoryRegions gs => audit_disjoint_input_budget site_enc site_budget fs gs
  | _, _ => 0
  end.

Definition audit_memory_effect_get_input_budget {E T CE} (edge_enc : E -> positive * list CE)
    (edge_budget : E -> nat) (table : Map.t E (Map.t nat (memory_effect T)))
    (edge : E) (index : nat) : nat :=
  5 + edge_budget edge + 5 * Pos.size_nat (fst (edge_enc edge)) +
  match fst (audit_map_get edge_enc edge table) with
  | None => 0
  | Some _ => 5 + audit_nat_input_budget index +
      5 * Pos.size_nat (fst (audit_nat_encode index))
  end.

Fixpoint audit_operand_calls_input_budget {N E} (operand_budget : N -> option E -> nat)
    (node : N) (keys : list (option E)) : nat :=
  match keys with
  | [] => 0
  | key :: rest => 2 + operand_budget node key +
      audit_operand_calls_input_budget operand_budget node rest
  end.

(** The raw-successor budget uses per-call incoming, operand and before bodies at actual inputs. *)
Definition audit_raw_next_input_budget {N E T CE SE IE OE BE : Type}
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (incoming : N -> list E * list IE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (edge_budget : E -> nat) (site_budget : T -> nat) (incoming_budget : N -> nat)
    (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat)
    (q : memory_scope T) (v : memory_version N E) : nat :=
  match v with
  | MemoryLive => 2
  | MemoryPhi n =>
      let edges := fst (incoming n) in
      4 + incoming_budget n + length edges +
      audit_operand_calls_input_budget operand_budget n (None :: map Some edges)
  | MemoryDef e i =>
      8 + audit_memory_effect_get_input_budget edge_enc edge_budget table e i + before_budget e i +
      match fst (audit_memory_effect_get edge_enc table e i), fst (before e i) with
      | Some effect, Some _ =>
          audit_scopes_disjoint_input_budget site_enc site_budget (effect_writes effect) q
      | _, _ => 0
      end
  end.

(** Callback input budgets bound all raw successor work, including operand occurrences. *)
Definition audit_raw_next_whole_input_bound_statement : Prop :=
  forall N E T CE SE IE OE BE (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) table (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      edge_work site_work incoming_work operand_work before_work
      edge_budget site_budget incoming_budget operand_budget before_budget q v,
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, incoming_work (snd (incoming n)) <= incoming_budget n) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
    audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work
      (snd (audit_memory_raw_next edge_enc site_enc table incoming operand before q v)) <=
      @audit_raw_next_input_budget N E T CE SE IE OE BE edge_enc site_enc table incoming before
        edge_budget site_budget incoming_budget operand_budget before_budget q v.

Example audit_empty_disjoint_input_budget :
  audit_disjoint_input_budget audit_positive_encode (fun _ => 1) [] [] = 1.
Proof.
  reflexivity.
Qed.
