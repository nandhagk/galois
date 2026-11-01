(** * RewriteAuditProofPlainPublic

    This module defines the plain tracked operations and representation search over phase views.
    For example, a variable search with no candidate identifiers returns None.
    Builds on: RewriteAuditPlainCore3 and
    RewriteAuditPlainCore4. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMatchReference RewriteAuditIndexReference
  RewriteAuditPlainCore1 RewriteAuditPlainCore2 RewriteAuditPlainCore3 RewriteAuditPlainCore4
  RewriteAuditPlainPrimitives RewriteAuditProofCarrier RewriteAuditProofRepresentation
  RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rw_plain_repr_term_view {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_phase_view K Sort V) (term : rw_term K Sort V) (root : rw_id)
    (acc : rw_rp_repr_acc K Sort V) {struct term} : option (positive * rw_rp_repr_acc K Sort V) :=
  let key_match := fun owner ty other_ty =>
    let same_sort := rw_plain_rw_ri_encoded_equal sort ty other_ty in
    if same_sort then
      let same_class := rw_view_same_class state root owner in
      same_class
    else false in
  match term with
  | RWVar ty v =>
    let candidates := rw_view_variable_nodes state v in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) :=
      match ids with
      | nil => None
      | id :: rest =>
        let found := rw_view_node state id in
        let candidate :=
          match found with
          | Some (owner, RWNVar declared other) =>
            let same := key_match owner ty declared in
            if same then
              let same_value := rw_plain_rw_ri_encoded_equal value v other in
              if same_value then
                let out := rw_plain_rw_rp_repr_emit (RWReprNode root id term nil) acc in
                Some out
              else None
            else None
          | _ => None
          end in
        match candidate with
        | Some out => Some out
        | None =>
          let out := visit rest in
          out
        end
      end in
    let out := visit candidates in
    out
  | RWApp ty key terms =>
    let candidates := rw_view_operator_nodes state key in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) :=
      match ids with
      | nil => None
      | id :: rest =>
        let found := rw_view_node state id in
        let candidate :=
          match found with
          | Some (owner, RWNApp declared other children) =>
            let same := key_match owner ty declared in
            if same then
              let same_op := rw_plain_rw_ri_encoded_equal op key other in
              if same_op then
                let fix descend (ts : list (rw_term K Sort V)) (cs : list rw_id)
                    (acc : rw_rp_repr_acc K Sort V) :
                    option (list positive * rw_rp_repr_acc K Sort V) :=
                  match ts, cs with
                  | nil, nil => Some (nil, acc)
                  | t :: ts, c :: cs =>
                    let head := rw_plain_repr_term_view op sort value state t c acc in
                    match head with
                    | None => None
                    | Some (pointer, next) =>
                      let tail := descend ts cs next in
                      option_map (fun pair => (pointer :: fst pair, snd pair)) tail
                    end
                  | _, _ => None
                  end in
                let children := descend terms children acc in
                match children with
                | None => None
                | Some (pointers, next) =>
                  let out := rw_plain_rw_rp_repr_emit (RWReprNode root id term pointers) next in
                  Some out
                end
              else None
            else None
          | _ => None
          end in
        match candidate with
        | Some out => Some out
        | None =>
          let out := visit rest in
          out
        end
      end in
    let out := visit candidates in
    out
  end.

Definition rw_plain_repr_find_view {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_phase_view K Sort V) (root : rw_id) (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) :=
  let found :=
    rw_plain_repr_term_view op sort value state term root (RwRpReprAcc nil Map.empty 1%positive) in
  option_map (fun pair => RWReprWitness (fst pair) (rw_rp_repr_ids (snd pair))
    (rw_rp_repr_nodes (snd pair))) found.

Definition rw_repr_find {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (view : rw_phase_view K Sort V) (root : rw_id) (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) :=
  rw_plain_repr_find_view EK ES EV view root term.

Definition rw_connect_class {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (graph : rw_graph K Sort V) (proof : rw_provenance K Sort V H) (root : rw_id)
    (lhs rhs : rw_term K Sort V) (witness : rw_repr_witness K Sort V) :
    option (rw_provenance K Sort V H * positive) :=
  rw_plain_rw_rp_connect_atomic EK ES EV proof lhs rhs.

Definition rw_tracked_tick {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (stamp : nat * nat) (state : rw_tracked_state K Sort V H) :
    option (rw_tracked_state K Sort V H * rw_index_event) :=
  rw_plain_rw_rp_tick_atomic EK ES EV stamp state.

Definition rw_tracked_rebuild {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (group : nat) (state : rw_tracked_state K Sort V H) :
    rw_tracked_state K Sort V H * list rw_index_event :=
  rw_plain_rw_rp_rebuild_atomic EK ES EV group state.

Definition rw_tracked_rule_step {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) :=
  rw_plain_rw_rp_rule_step_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) rules position
    state attempt.

Definition rw_tracked_run {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) (fuel : N)
    (seed : rw_term K Sort V) : rw_id * rw_tracked_output K Sort V H :=
  rw_plain_rw_rp_run_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) rules
    (fun state => strategy (rw_index_view EK ES EV state)) fuel seed.

Definition rw_selected_explanation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_tracked_state K Sort V H) (root : rw_id)
    (seed tree : rw_term K Sort V) : option (rw_provenance K Sort V H * positive) :=
  rw_plain_rw_rp_selected_atomic EK ES EV state root seed tree.

Definition rw_factful_run {K Sort V H C F} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (an : rw_analysis K Sort V C F)
    (strategy : rw_fact_view K Sort V F -> option (rw_attempt K Sort V H))
    (fuel : N) (input : rw_tracked_state K Sort V H * Map.t rw_id F) :
    rw_tracked_output K Sort V H * Map.t rw_id F :=
  rw_plain_rw_rp_fact_run_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) rules
    (rw_fact_unknown an)
    (fun state unknown facts => strategy (RWFactView (rw_index_view EK ES EV state)
      (fun id =>
        match Map.get positive_encoding id facts with
        | Some fact => fact
        | None => unknown
        end))) fuel input.

Definition rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Definition rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.
