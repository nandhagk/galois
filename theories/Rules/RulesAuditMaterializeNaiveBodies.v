(** * Fixed generated naive-solver callback data bodies

    The remaining FX/RPO execution adapter must compose these concrete bodies at actual calls.
    For example, the numbered rule index associates each rule with its successive position.
    Builds on: RulesAuditMaterializeRounds and the prepared RulesSolve source. *)

From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditNestedProbe RulesAuditMaterializePrelude
  RulesAuditMaterializeAdapters RulesAuditJoinSyntax RulesAuditIndex RulesAuditMaterializePlans
  RulesAuditMaterializeJobs RulesAuditMaterializeRounds RulesAuditMaterializeStratify.
Import ListNotations.

(** * Generated inputs and callbacks *)

Definition mat_nat_encoder n :=
  mat_lift 120 Pos.size_nat audit_nat_events_work (audit_nat_encode n).

Fixpoint mat_numbered_rules {P} n (rs : list (rule P)) : mat_run (list (nat * rule P)) :=
  mat_mark 121 (
    match rs with
    | [] => mat_return []
    | r :: rest =>
        next <- mat_nat 30 Nat.add n 1;; tail <- mat_numbered_rules next rest;;
        mat_return ((n, r) :: tail)
    end).

Fixpoint mat_rule_index {P} n (rs : list (rule P)) : mat_run (Map.t nat (rule P)) :=
  mat_mark 122 (
    match rs with
    | [] => mat_return Map.empty
    | r :: rest =>
        next <- mat_nat 31 Nat.add n 1;; tail <- mat_rule_index next rest;;
        mat_set_encoded mat_nat_encoder n r tail
    end).

Definition mat_dependencies {P} (prog : program P) st k (r : rule P) :=
  ps <- mat_positive_atoms (body r);;
  selected <- mat_filter (fun a =>
    lev <- mat_level st (pred a);; mat_nat_test 32 Nat.eqb lev k) ps;;
  keys <- mat_map (fun a => mat_return (pred a)) selected;;
  set <- mat_predicate_set_encoded (mat_encode (penc prog)) keys;; mat_elements set.

Fixpoint mat_fill_values {P A} (E : encoding P) (ps : list P) (values : list A) :
    mat_run (Map.t P A) :=
  mat_mark 123 (
    match ps, values with
    | p :: rest, v :: tail => before <- mat_fill_values E rest tail;; mat_set E p v before
    | _, _ => mat_return Map.empty
    end).

Definition mat_generated_env {P} (prog : program P) facts st lower k
    (reads : Map.t P (relation prog facts)) p :=
  lev <- mat_level st p;; same <- mat_nat_test 33 Nat.eqb lev k;;
  if same then
    found <- mat_get (penc prog) p reads;;
    mat_return (
      match found with
      | Some value => proj1_sig value
      | None => FinSet.empty
      end)
  else lower p.

Fixpoint mat_classic_join {P} (ps : list (atom P)) bound
    (env : P -> mat_run (FinSet.t tuple)) bindings : mat_run (list binding) :=
  mat_mark 124 (
    match ps with
    | [] => mat_return bindings
    | a :: rest =>
        next_bound <- mat_bound_add bound a;; set <- env (pred a);; rows <- mat_elements set;;
        index <- mat_build_index_full bound (args a) rows;;
        joined <- mat_lift 125 (@length binding) rules_nested_probe_work
          (rules_probe_bindings (NestedSearch bound (args a) index) bindings);;
        mat_classic_join rest next_bound env joined
    end).

Definition mat_naive_firing {P} (prog : program P) cached (r : rule P) env :=
  ps <- mat_positive_atoms (body r);; bindings <- mat_classic_join ps FinSet.empty env [Map.empty];;
  accepted <- mat_filter (mat_negative r env) bindings;;
  rows <- mat_map (fun b => mat_instantiate b (args (head r))) accepted;;
  valid <- mat_filter (mat_accept_cached prog cached (pred (head r))) rows;;
  mat_of_list (audit_list_encode audit_positive_encode) (audit_list_events_work
    audit_basic_encoding_work) valid.

Definition mat_clamp {P} (prog : program P) cached p (set : FinSet.t tuple) :=
  rows <- mat_elements set;; accepted <- mat_filter (mat_accept_cached prog cached p) rows;;
  mat_of_list (audit_list_encode audit_positive_encode) (audit_list_events_work
    audit_basic_encoding_work) accepted.

Definition mat_constraints {P} (prog : program P) (facts : list (ground_atom P)) st k :=
  indexed <- mat_numbered_rules 0 (rules prog);;
  first <- mat_flatmap (fun ir =>
    lev <- mat_level st (pred (head (snd ir)));; same <- mat_nat_test 34 Nat.eqb lev k;;
    mat_return (if same then [FromRule (fst ir) (pred (head (snd ir)))] else [])) indexed;;
  predicates <- mat_map (fun fact => mat_return (fst fact)) facts;;
  distinct <- mat_predicate_set_encoded (mat_encode (penc prog)) predicates;;
  keys <- mat_elements distinct;;
  selected <- mat_filter (fun p => lev <- mat_level st p;; mat_nat_test 35 Nat.eqb lev k) keys;;
  second <- mat_map (fun p => mat_return (FromFact p)) selected;; mat_append first second.

Definition mat_generated_deps {P} (prog : program P) st k (ri : Map.t nat (rule P))
    (c : rconstraint P) :=
  match c with
  | FromFact _ => mat_return []
  | FromRule i _ =>
      found <- mat_get_encoded mat_nat_encoder i ri;;
      match found with
      | None => mat_return []
      | Some r => mat_dependencies prog st k r
      end
  end.

Definition mat_generated_targets {P} (prog : program P) facts st k :=
  constraints <- mat_constraints prog facts st k;;
  keys <- mat_map (fun c => mat_return (
    match c with
    | FromRule _ h => h
    | FromFact p => p
    end)) constraints;;
  set <- mat_predicate_set_encoded (mat_encode (penc prog)) keys;; mat_elements set.

Definition mat_store_relations {P} (prog : program P) facts ps (s : P -> relation prog facts) db :=
  mat_foldr (fun p before => value <- mat_return (proj1_sig (s p));;
    mat_set (penc prog) p value before) ps db.

(** The proposed index erasure keeps the native numbering and rule map. *)
Definition mat_rule_index_erases_statement : Prop :=
  forall P n (rs : list (rule P)), fst (mat_rule_index n rs) = index_rules_from n rs.

(** The proposed dependency erasure selects the native predicates at the same level. *)
Definition mat_dependencies_erases_statement : Prop :=
  forall P (prog : program P) st k r,
    fst (mat_dependencies prog (MatExternalLevels st) k r) = level_dependencies prog st k r.

(** The proposed constraints erasure returns the native stratum constraints. *)
Definition mat_constraints_erases_statement : Prop :=
  forall P (prog : program P) facts st k,
    fst (mat_constraints prog facts (MatExternalLevels st) k) =
      stratum_constraints prog facts st k.

(** The proposed classic join erasure returns the native positive-join bindings. *)
Definition mat_classic_join_erases_statement : Prop :=
  forall P ps bound env bindings,
    fst (@mat_classic_join P ps bound (fun p => mat_return (env p)) bindings) =
      join_positive ps bound env bindings.

(** The proposed erasure feeds source environment values to the native join. *)
Definition mat_classic_join_source_erases_statement : Prop :=
  forall P ps bound (env : P -> mat_run (FinSet.t tuple)) bindings,
    fst (mat_classic_join ps bound env bindings) =
      join_positive ps bound (fun p => fst (env p)) bindings.

(** The proposed firing erasure uses the fixed prepared universe sets. *)
Definition mat_naive_firing_erases_statement : Prop :=
  forall P (prog : program P) facts r env,
    fst (mat_naive_firing prog (fst (mat_setup_cached prog facts)) r env) =
      fire_rule prog facts r (fun p => fst (env p)).

(** The proposed clamp erasure compares its output with native restriction. *)
Definition mat_clamp_erases_statement : Prop :=
  forall P (prog : program P) facts p input,
    fst (mat_clamp prog (fst (mat_setup_cached prog facts)) p input) =
      proj1_sig (restrict prog facts p input).

(** The proposed environment erasure compares the actual level and lookup branches. *)
Definition mat_generated_env_erases_statement : Prop :=
  forall P (prog : program P) facts st lower k reads p,
    fst (mat_generated_env prog facts st (mat_rel prog lower) k reads p) =
      stratum_env prog facts (mat_native_levels st) (rel_of prog lower) k reads p.
