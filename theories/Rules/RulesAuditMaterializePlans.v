(** * Literal retained-plan initialization, reset and extension

    All generic callback parameters are source-level arguments; whole callers supply fixed captured
      bodies.
    For example, a nested plan can rebuild its cached rows when a predicate is reset.
    Builds on: RulesAuditMaterializePrelude and the delta cache types. *)

From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTable.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditRelations RulesAuditNestedPrepare RulesAuditNestedProbe
  RulesAuditMultiwayPrepare RulesAuditMultiwayProbe RulesAuditTerminal RulesAuditMaterializePrelude
  RulesAuditMaterializeAdapters RulesAuditJoinSyntax RulesAuditIndex.
Import ListNotations.

(** * Plan preparation and updates *)

Fixpoint mat_nested_rows {Q} (ps : list (atom Q)) bound (rows : Q -> mat_run (list tuple)) :
    mat_run (delta_nested_cache Q) :=
  mat_mark 30 (
    match ps with
    | [] => mat_return []
    | a :: rest =>
        rs <- rows (pred a);; index <- mat_build_index_full bound (args a) rs;;
        search <- mat_return (NestedSearch bound (args a) index);; node <- mat_return (a, search);;
        next <- mat_bound_add bound a;; tail <- mat_nested_rows rest next rows;;
        mat_return (node :: tail)
    end).

Definition mat_nested_prepare {Q} ps bound (env : Q -> mat_run (FinSet.t tuple)) :=
  @mat_nested_rows Q ps bound (fun p => s <- env p;; mat_elements s).

Definition mat_nested_rebuild {Q} (env : Q -> mat_run (FinSet.t tuple))
    (cache : delta_nested_cache Q) :=
  mat_map (fun node =>
    let '(a, search) := node in s <- env (pred a);; rows <- mat_elements s;;
    index <- mat_build_index_full (nested_bound search) (nested_terms search) rows;;
    mat_return (NestedSearch (nested_bound search) (nested_terms search) index)) cache.

Definition mat_nested_update {Q} (reset : Q -> mat_run bool) (rows : Q -> mat_run (list tuple))
    (cache : delta_nested_cache Q) :=
  mat_map (fun node =>
    let '(a, search) := node in clear <- reset (pred a);;
    initial <- mat_return (if clear then Map.empty else nested_index search);;
    batch <- rows (pred a);;
    index <- mat_foldr (mat_index_add_full (nested_bound search) (nested_terms search))
      batch initial;;
    mat_return (a, NestedSearch (nested_bound search) (nested_terms search) index)) cache.

Definition mat_variable_domains {Q} v bound (ps : list (atom Q))
    (rows : Q -> mat_run (list tuple)) :=
  selected <- mat_atoms_with v ps;;
  mat_map (fun a => batch <- rows (pred a);;
    index <- mat_build_variable_full bound (args a) v batch;;
    mat_return (a, VariableSearch (args a) index)) selected.

Fixpoint mat_multiway_rows {Q} (vs : list nat) bound (ps : list (atom Q))
    (rows : Q -> mat_run (list tuple)) : mat_run (list (delta_variable_cache Q)) :=
  mat_mark 31 (
    match vs with
    | [] => mat_return []
    | v :: rest =>
        domains <- mat_variable_domains v bound ps rows;;
        layer <- mat_return (DeltaVariableCache v bound domains);; next <- mat_nat_add v bound;;
        tail <- mat_multiway_rows rest next ps rows;; mat_return (layer :: tail)
    end).

Definition mat_multiway_prepare {Q} vs bound ps (env : Q -> mat_run (FinSet.t tuple)) :=
  @mat_multiway_rows Q vs bound ps (fun p => s <- env p;; mat_elements s).

Definition mat_variable_erase {Q} (layer : delta_variable_cache Q) :=
  domains <- mat_map (fun node => mat_return (snd node)) (delta_domains layer);;
  mat_return (MultiwaySearch (delta_variable layer) (delta_bound layer) domains).

Definition mat_variable_rebuild {Q} (env : Q -> mat_run (FinSet.t tuple))
    (layer : delta_variable_cache Q) :=
  domains <- mat_map (fun node =>
    let '(a, search) := node in s <- env (pred a);; rows <- mat_elements s;;
    index <- mat_build_variable_full (delta_bound layer) (variable_terms search)
      (delta_variable layer) rows;; mat_return (VariableSearch (variable_terms search) index))
    (delta_domains layer);;
  mat_return (MultiwaySearch (delta_variable layer) (delta_bound layer) domains).

Definition mat_variable_update {Q} (reset : Q -> mat_run bool) (rows : Q -> mat_run (list tuple))
    (layer : delta_variable_cache Q) :=
  domains <- mat_map (fun node =>
    let '(a, search) := node in clear <- reset (pred a);;
    initial <- mat_return (if clear then Table.empty else variable_table search);;
    batch <- rows (pred a);;
    index <- mat_foldr (mat_variable_add_full (delta_bound layer) (variable_terms search)
      (delta_variable layer)) batch initial;;
    mat_return (a, VariableSearch (variable_terms search) index))
    (delta_domains layer);;
  mat_return (DeltaVariableCache (delta_variable layer) (delta_bound layer) domains).

Definition mat_plan_rows {Q} strategy (ps : list (atom Q)) rows : mat_run (delta_join_plan Q) :=
  mat_mark 32 (
    match strategy with
    | IndexedNested =>
        cache <- mat_nested_rows ps FinSet.empty rows;; mat_return (DeltaNested cache)
    | IndexedMultiway =>
        vs <- mat_join_variables ps;; cache <- mat_multiway_rows vs FinSet.empty ps rows;;
        mat_return (DeltaMultiway cache)
    end).

Definition mat_plan_prepare {Q} strategy ps (env : Q -> mat_run (FinSet.t tuple)) :=
  @mat_plan_rows Q strategy ps (fun p => s <- env p;; mat_elements s).

Definition mat_plan_update {Q} reset rows (plan : delta_join_plan Q) :=
  mat_mark 33 (
    match plan with
    | DeltaNested cache => out <- mat_nested_update reset rows cache;; mat_return (DeltaNested out)
    | DeltaMultiway cache =>
        out <- mat_map (mat_variable_update reset rows) cache;; mat_return (DeltaMultiway out)
    end).

Definition mat_terminal_atom {Q} (env : Q -> mat_run (FinSet.t tuple)) b (a : atom Q) :=
  row <- mat_instantiate b (args a);; s <- env (pred a);; mat_tuple_mem row s.

Definition mat_positive {Q} atoms (env : Q -> mat_run (FinSet.t tuple)) b :=
  mat_all (mat_terminal_atom env b) atoms.

Definition mat_negative {Q} (r : rule Q) (env : Q -> mat_run (FinSet.t tuple)) b :=
  mat_all (fun lit =>
    match lit with
    | LPos _ => mat_return true
    | LNeg a => found <- mat_terminal_atom env b a;; mat_return (negb found)
    end) (body r).

Definition mat_plan_bindings {Q} (ps : list (atom Q)) (env : Q -> mat_run (FinSet.t tuple))
    (plan : delta_join_plan Q) :=
  mat_mark 34 (
    match plan with
    | DeltaNested cache =>
        searches <- mat_map (fun node => mat_return (snd node)) cache;;
        mat_lift 35 (@length binding) rules_nested_probe_work
          (rules_run_nested_counted searches [Map.empty])
    | DeltaMultiway cache =>
        searches <- mat_map mat_variable_erase cache;;
        bindings <- mat_lift 36 (@length binding) rules_multi_probe_work
          (rules_run_multiway_counted searches [Map.empty]);;
        mat_filter (mat_positive ps env) bindings
    end).

Fixpoint mat_fill_snapshot {Q} (enc : Q -> mat_run positive) (keys : list Q)
    (values : list (list tuple)) : mat_run (Map.t Q (list tuple)) :=
  mat_mark 37 (
    match keys, values with
    | p :: ps, rows :: rest =>
        before <- mat_fill_snapshot enc ps rest;; mat_set_encoded enc p rows before
    | _, _ => mat_return Map.empty
    end).

Definition mat_snapshot_encoded {Q} (enc : Q -> mat_run positive) (atoms : list (atom Q))
    (env : Q -> mat_run (FinSet.t tuple)) :=
  predicates <- mat_map (fun a => mat_return (pred a)) atoms;;
  distinct <- mat_predicate_set_encoded enc predicates;; keys <- mat_elements distinct;;
  sets <- mat_map (fun p => s <- env p;; mat_elements s) keys;; mat_fill_snapshot enc keys sets.

(** The snapshot uses the supplied encoding to prepare each predicate once. *)
Definition mat_snapshot {Q} (E : encoding Q) := @mat_snapshot_encoded Q (mat_encode E).

Definition mat_snapshot_rows {Q} (E : encoding Q) (snapshot : Map.t Q (list tuple)) q :=
  found <- mat_get E q snapshot;;
  mat_return (
    match found with
    | Some rows => rows
    | None => []
    end).

Definition mat_snapshot_rows_encoded {Q} (enc : Q -> mat_run positive)
    (snapshot : Map.t Q (list tuple)) q :=
  found <- mat_get_encoded enc q snapshot;;
  mat_return (
    match found with
    | Some rows => rows
    | None => []
    end).

(** The proposed row-plan erasure returns the native delta plan for the selected strategy. *)
Definition mat_plan_rows_erases_statement : Prop :=
  forall Q strategy (ps : list (atom Q)) rows,
    fst (mat_plan_rows strategy ps (fun q => mat_return (rows q))) =
      delta_plan_rows strategy ps rows.

(** The proposed update erasure returns the native reset and row update of the same plan. *)
Definition mat_plan_update_erases_statement : Prop :=
  forall Q reset rows (plan : delta_join_plan Q),
    fst (mat_plan_update (fun q => mat_return (reset q)) (fun q => mat_return (rows q)) plan) =
      delta_update_plan reset rows plan.

(** The proposed binding erasure returns native bindings for the same plan and environment. *)
Definition mat_plan_bindings_erases_statement : Prop :=
  forall Q ps env (plan : delta_join_plan Q),
    fst (mat_plan_bindings ps (fun q => mat_return (env q)) plan) = delta_plan_bindings ps env plan.
