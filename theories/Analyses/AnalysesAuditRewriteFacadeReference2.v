(** * AnalysesAuditRewriteFacadeReference2

    This module defines legacy offer construction, gating, and strategy contracts.
    For example, an attempt with an empty binding map has an empty binding list.
    Builds on: AnalysesEgraph and
    RewriteAuditIndexMatchReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Rewrite Require Import RewriteAuditIndexMatchReference RewriteAuditIndexReference.
Import List.ListNotations.

Definition rw_legacy_binding_limit {K} (a : rw_attempt K unit nat nat) : option nat :=
  fold_right (fun entry limit =>
    match limit with
    | None => Some (fst entry)
    | Some n => Some (Nat.max (fst entry) n)
    end) None (Map.elements (rw_attempt_sub a)).

Definition rw_legacy_binding_value {K} (a : rw_attempt K unit nat nat) (index : nat) : term K :=
  match Map.get nat_encoding index (rw_attempt_sub a) with
  | None => TVar index
  | Some value => legacy_project value
  end.

Definition rw_legacy_binding_list {K} (a : rw_attempt K unit nat nat) : list (term K) :=
  match rw_legacy_binding_limit a with
  | None => []
  | Some max_index => map (rw_legacy_binding_value a) (seq 0 (S max_index))
  end.

Definition rw_legacy_offer_gate {K} (EK : encoding K) (rules : list (rewrite_rule K)) (a :
    rw_attempt K unit nat nat) : bool :=
  match nth_error rules (rw_attempt_rule a) with
  | None => false
  | Some legacy =>
    let rule := legacy_rule legacy in
    let sub := rw_attempt_substitution nat_encoding a in
    if rw_check_sub EK unit_encoding nat_encoding nat_encoding legacy_signature rule sub &&
        rw_condition rule sub then
      match rw_instantiate sub (rw_lhs rule), rw_instantiate sub (rw_rhs rule) with
      | Some lhs, Some rhs =>
        check_explanation EK rules (legacy_project lhs) (legacy_project rhs)
          [RewriteStep [] (rw_attempt_rule a) true (rw_legacy_binding_list a)]
      | _, _ => false
      end
    else false
  end.

Definition rw_legacy_prepared_gate {K} (EK : encoding K) (table : Map.t nat (rewrite_rule K)) (a :
    rw_attempt K unit nat nat) : bool :=
  match Map.get nat_encoding (rw_attempt_rule a) table with
  | None => false
  | Some legacy =>
    let rule := legacy_rule legacy in
    let sub := rw_attempt_substitution nat_encoding a in
    if rw_check_sub EK unit_encoding nat_encoding nat_encoding legacy_signature rule sub &&
        rw_condition rule sub then
      match rw_instantiate sub (rw_lhs rule), rw_instantiate sub (rw_rhs rule) with
      | Some lhs, Some rhs =>
        let step := RewriteStep [] (rw_attempt_rule a) true (rw_legacy_binding_list a) in
        match legacy_replay_step EK (fun i => Map.get nat_encoding i table) (legacy_project lhs)
          step with
        | None => false
        | Some actual => term_eqb EK actual (legacy_project rhs)
        end
      | _, _ => false
      end
    else false
  end.

(** The gate using a prepared legacy rule table agrees with the original offer gate. *)
Definition rw_legacy_prepared_gate_agrees_contract : Prop :=
  forall K (EK : encoding K) rules a, rw_legacy_prepared_gate EK (legacy_list_table rules 0) a =
    rw_legacy_offer_gate EK rules a.

Definition rw_legacy_choose {K} (EK : encoding K) (table : Map.t nat (rewrite_rule K)) (offers :
    list (rw_attempt K unit nat nat)) : option (rw_attempt K unit nat nat) :=
  find (rw_legacy_prepared_gate EK table) offers.

(** A chosen offer belongs to the input offers and passes the legacy gate. *)
Definition rw_legacy_choose_sound_contract : Prop :=
  forall K (EK : encoding K) rules offers chosen, rw_legacy_choose EK (legacy_list_table rules 0)
    offers = Some chosen ->
    In chosen offers /\
    rw_legacy_offer_gate EK rules chosen = true.

(** If an input offer passes the legacy gate, choosing from the prepared table succeeds. *)
Definition rw_legacy_choose_complete_contract : Prop :=
  forall K (EK : encoding K) rules offers, (exists offer, In offer offers /\ rw_legacy_offer_gate EK
    rules offer = true) ->
    exists chosen, rw_legacy_choose EK (legacy_list_table rules 0) offers = Some chosen.

Fixpoint rw_legacy_make_bindings {K} (g : rw_graph K unit nat) (trees : rw_tree_table K unit nat)
    (holes : list nat) (assignment : rw_assignment nat) : option (Map.t nat (rw_term K unit nat)) :=
  match holes with
  | [] => Some Map.empty
  | hole :: rest =>
    match rw_legacy_make_bindings g trees rest assignment with
    | None => None
    | Some bindings =>
      match Map.get nat_encoding hole assignment with
      | None => Some (Map.set nat_encoding hole (RWVar tt hole) bindings)
      | Some c =>
        match rw_tree_get g trees c with
        | None => None
        | Some candidate => Some (Map.set nat_encoding hole (rw_candidate_tree candidate) bindings)
        end
      end
    end
  end.

Definition rw_legacy_rule_offers {K} (EK : encoding K) (view : rw_snapshot_view K unit nat) (g :
    rw_graph K unit nat) (trees : rw_tree_table K unit nat) (entry : nat * rewrite_rule K) : list
    (rw_attempt K unit nat nat) :=
  let '(index, old_rule) := entry in
  let rule := legacy_rule old_rule in
  flat_map (fun root =>
    flat_map (fun assignment =>
      match rw_legacy_make_bindings g trees (rw_holes rule) assignment with
      | None => []
      | Some bindings => [RwAttempt index root bindings]
      end) (rw_view_match EK unit_encoding nat_encoding nat_encoding (rw_snapshot_base view)
        root (rw_lhs rule)))
    (rw_view_roots (rw_snapshot_base view) tt).

Definition rw_legacy_offers {K} (EK : encoding K) (rules : list (rewrite_rule K)) (view :
    rw_snapshot_view K unit nat) : list (rw_attempt K unit nat nat) :=
  let g := rw_snapshot_graph view tt in
  let trees := rw_tree_rounds EK unit_encoding nat_encoding (fun _ => 0) (fun _ => 0)
    g (N.of_nat (length (rw_roots g))) in
  flat_map (rw_legacy_rule_offers EK view g trees) (combine (seq 0 (length rules)) rules).

Definition rw_legacy_strategy {K} (EK : encoding K) (rules : list (rewrite_rule K)) (table : Map.t
    nat (rewrite_rule K)) (view : rw_snapshot_view K unit nat) : option (rw_attempt K unit nat nat)
    :=
  rw_legacy_choose EK table (rw_legacy_offers EK rules view).

(** An offer returned by the legacy strategy passes the legacy offer gate. *)
Definition rw_legacy_strategy_gate_contract : Prop :=
  forall K (EK : encoding K) rules view attempt, rw_legacy_strategy EK rules (legacy_list_table
    rules 0) view = Some attempt ->
    rw_legacy_offer_gate EK rules attempt = true.

(** If an enumerated legacy offer passes the gate, the legacy strategy returns an offer. *)
Definition rw_legacy_strategy_complete_offers_contract : Prop :=
  forall K (EK : encoding K) rules view, (exists attempt, In attempt (rw_legacy_offers EK rules
    view) /\ rw_legacy_offer_gate EK rules attempt = true) ->
    exists attempt, rw_legacy_strategy EK rules (legacy_list_table rules 0) view = Some attempt.
