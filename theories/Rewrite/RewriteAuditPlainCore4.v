(** * RewriteAuditPlainCore4

    This module implements plain tracked and factful runners and representation search.
    For example, repetition with fuel 1 returns an already stopped runner unchanged.
    Builds on: RewriteAuditPlainCore1 and
    RewriteAuditProofRun. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditPlainCore1
  RewriteAuditPlainCore2 RewriteAuditPlainCore3 RewriteAuditPlainPrimitives
  RewriteAuditProofCarrier RewriteAuditProofRepresentation RewriteAuditProofRun
  RewriteAuditProofTick.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rw_plain_rw_rp_run_repeat {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_plain_strategy K Sort V H)
    (fuel : positive) (state : rw_rp_run_state K Sort V H) : rw_rp_run_state K Sort V H :=
  if rw_rp_stopped state then state
  else
    match fuel with
    | xH =>
      let out :=
        rw_plain_rw_rp_run_once EK ES EV op sort value hole callbacks table strategy state in
      out
    | xO rest =>
      let middle :=
        rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest state in
      let out :=
        rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest
          middle in
      out
    | xI rest =>
      let first :=
        rw_plain_rw_rp_run_once EK ES EV op sort value hole callbacks table strategy state in
      let middle :=
        rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest first in
      let out :=
        rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest
          middle in
      out
    end.

Definition rw_plain_rw_rp_run_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H))
    (strategy : rw_plain_strategy K Sort V H) (fuel : N) (seed : rw_term K Sort V) :
    (rw_id * rw_tracked_output K Sort V H) :=
  let '(root, initial) := rw_plain_rw_rp_seed_atomic EK ES EV op value seed in
  match fuel with
  | N0 => (root, RwTrackedOutput initial RWFuelExhausted nil nil)
  | Npos p =>
    let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
    let '(ready, initial_events) := rw_plain_rw_rp_rebuild_atomic op sort value 0 initial in
    let final :=
      rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy p
        (RwRpRunState ready false 0 nil) in
    (root, RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else RWFuelExhausted)
      initial_events (rw_rp_events final))
  end.

Definition rw_plain_rw_rp_fact_run_once {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (unknown : F)
    (strategy : rw_plain_fact_strategy K Sort V H F)
    (state : rw_rp_run_state K Sort V H * Map.t rw_id F) :
    (rw_rp_run_state K Sort V H * Map.t rw_id F) :=
  let '(run, facts) := state in
  if rw_rp_stopped run then state
  else
    let tracked := rw_rp_current run in
    let offer := rw_plain_rw_rp_fact_strategy_run op value strategy (rw_tracked_machine tracked)
      unknown facts in
    match offer with
    | None => (RwRpRunState tracked true (rw_rp_position run) (rw_rp_events run), facts)
    | Some attempt =>
      let applied :=
        rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
          (rw_rp_position run) tracked attempt in
      match applied with
      | None =>
        (RwRpRunState tracked false (S (rw_rp_position run))
          (RWRunRejected attempt :: rw_rp_events run), facts)
      | Some (next, events) =>
        (RwRpRunState next false (S (rw_rp_position run))
          (RWRunAccepted attempt events :: rw_rp_events run), Map.empty)
      end
    end.

Fixpoint rw_plain_rw_rp_fact_run_repeat {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (unknown : F)
    (strategy : rw_plain_fact_strategy K Sort V H F) (fuel : positive)
    (state : rw_rp_run_state K Sort V H * Map.t rw_id F) :
    (rw_rp_run_state K Sort V H * Map.t rw_id F) :=
  if rw_rp_stopped (fst state) then state
  else
    match fuel with
    | xH =>
      let out :=
        rw_plain_rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown strategy
          state in
      out
    | xO rest =>
      let middle :=
        rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy
          rest state in
      let out :=
        rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy
          rest middle in
      out
    | xI rest =>
      let first :=
        rw_plain_rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown strategy
          state in
      let middle :=
        rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy
          rest first in
      let out :=
        rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy
          rest middle in
      out
    end.

Definition rw_plain_rw_rp_fact_run_atomic {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : encoding K) (sort : encoding Sort) (value : encoding V)
    (hole : encoding H) (callbacks : rw_plain_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (unknown : F)
    (strategy : rw_plain_fact_strategy K Sort V H F)
    (fuel : N) (input : rw_tracked_state K Sort V H * Map.t rw_id F) :
    (rw_tracked_output K Sort V H * Map.t rw_id F) :=
  let '(initial, facts) := input in
  match fuel with
  | N0 => (RwTrackedOutput initial RWFuelExhausted nil nil, facts)
  | Npos p =>
    let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
    let '(ready, initial_events) := rw_plain_rw_rp_rebuild_atomic op sort value 0 initial in
    let '(final, retained) :=
      rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy p
        (RwRpRunState ready false 0 nil, Map.empty) in
    (RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else RWFuelExhausted)
      initial_events (rw_rp_events final), retained)
  end.

Definition rw_plain_rw_rp_selected_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_tracked_state K Sort V H) (root : rw_id)
    (seed tree : rw_term K Sort V) : option (rw_provenance K Sort V H * positive) :=
  let machine := rw_tracked_machine state in
  let source_member := rw_plain_rw_ri_member_atomic op sort value machine seed root in
  let tree_member := rw_plain_rw_ri_member_atomic op sort value machine tree root in
  if source_member && tree_member then
    let out :=
      rw_plain_rw_rp_connect_atomic op sort value (rw_tracked_provenance state) seed tree in
    out
  else None.

Definition rw_plain_rw_rp_repr_emit {K Sort V} (node : rw_repr_node K Sort V)
    (acc : rw_rp_repr_acc K Sort V) : (positive * rw_rp_repr_acc K Sort V) :=
  let id := rw_rp_repr_next acc in
  let nodes :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id node (rw_rp_repr_nodes acc) in
  let fresh := rw_plain_rw_fuel_pos_succ id in
  (id, RwRpReprAcc (id :: rw_rp_repr_ids acc) nodes fresh).

Fixpoint rw_plain_rw_rp_repr_term_atomic {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_index_state K Sort V) (term : rw_term K Sort V) (root : rw_id)
    (acc : rw_rp_repr_acc K Sort V) {struct term} : option (positive * rw_rp_repr_acc K Sort V) :=
  let key_match := fun owner ty other_ty =>
    let same_sort := rw_plain_rw_ri_encoded_equal sort ty other_ty in
    if same_sort then
      let same_class := rw_plain_rw_ri_same_class_atomic state root owner in
      same_class
    else false in
  match term with
  | RWVar ty v =>
    let candidates :=
      rw_plain_rw_ri_bucket_ids (rw_plain_rw_external_encoding_events value)
        rw_plain_rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) :=
      match ids with
      | nil => None
      | id :: rest =>
        let found :=
          rw_plain_audit_map_get rw_plain_audit_positive_encode id
            (rw_nodes (rw_index_base state)) in
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
    let candidates :=
      rw_plain_rw_ri_bucket_ids (rw_plain_rw_external_encoding_events op)
        rw_plain_rw_external_events_work key (rw_index_operators state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) :=
      match ids with
      | nil => None
      | id :: rest =>
        let found :=
          rw_plain_audit_map_get rw_plain_audit_positive_encode id
            (rw_nodes (rw_index_base state)) in
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
                    let head := rw_plain_rw_rp_repr_term_atomic op sort value state t c acc in
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

Definition rw_plain_rw_rp_repr_find_atomic {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (state : rw_index_state K Sort V) (root : rw_id)
    (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) :=
  let found :=
    rw_plain_rw_rp_repr_term_atomic op sort value state term root
      (RwRpReprAcc nil Map.empty 1%positive) in
  option_map (fun pair => RWReprWitness (fst pair) (rw_rp_repr_ids (snd pair))
    (rw_rp_repr_nodes (snd pair))) found.
