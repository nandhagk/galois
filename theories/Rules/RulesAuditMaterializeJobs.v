(** * Exact delta tagging, rule variants and prepared jobs

    Universe closures distinguish legacy partial preparation from the cached two-argument body.
    For example, a pivot atom is tagged as frontier while other recursive atoms use
    accumulated rows.
    Builds on: RulesAuditMaterializePlans and the native source callback captures. *)

From Stdlib Require Import List NArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditPrimitive.
From Galois.Rules Require Import RulesAuditRelations RulesAuditUniverse RulesAuditNestedPrepare
  RulesAuditNestedProbe RulesAuditMultiwayPrepare RulesAuditMultiwayProbe
  RulesAuditMaterializePrelude RulesAuditMaterializeAdapters RulesAuditJoinSyntax
  RulesAuditMaterializePlans.
Import ListNotations.

(** * Tagging and prepared jobs *)

Definition mat_pos_equal a b :=
  mat_lift 50 (fun _ => 1 + Pos.size_nat a + Pos.size_nat b)
    audit_positive_eqb_source_work (audit_positive_eqb a b).

Definition mat_term_equal a b :=
  mat_mark 51 (
    match a, b with
    | TVar x, TVar y => mat_nat_test 0 Nat.eqb x y
    | TConst x, TConst y => mat_pos_equal x y
    | _, _ => mat_return false
    end).

Fixpoint mat_terms_equal xs ys : mat_run bool :=
  mat_mark 52 (
    match xs, ys with
    | [], [] => mat_return true
    | x :: xs, y :: ys =>
        first <- mat_term_equal x y;; later <- mat_terms_equal xs ys;; mat_return (first && later)
    | _, _ => mat_return false
    end).

Definition mat_atom_equal {P} E (a b : atom P) :=
  first <- mat_encode E (pred a);; second <- mat_encode E (pred b);;
  same <- mat_pos_equal first second;; terms <- mat_terms_equal (args a) (args b);;
  mat_return (same && terms).

Definition mat_tag_atom {P} E (pivot a : atom P) :=
  same <- mat_atom_equal E a pivot;; mat_return (Atom (pred a, same) (args a)).

Definition mat_tag_rule {P} E (r : rule P) pivot :=
  ps <- mat_positive_atoms (body r);;
  literals <- mat_map (fun a => tagged <- mat_tag_atom E pivot a;; mat_return (LPos tagged)) ps;;
  mat_return (Rule (Atom (pred (head r), false) (args (head r))) literals).

Definition mat_recursive {P} (st : mat_level_context P) k (r : rule P) :=
  ps <- mat_positive_atoms (body r);;
  mat_filter (fun a => lev <- mat_level st (pred a);; mat_nat_test 1 Nat.eqb lev k) ps.

Definition mat_specs {P} (prog : program P) st k :=
  rs <- mat_filter (fun r => lev <- mat_level st (pred (head r));;
    mat_nat_test 2 Nat.eqb lev k) (rules prog);;
  mat_flatmap (fun r => atoms <- mat_recursive st k r;;
    mat_map (fun a => mat_return (r, a)) atoms) rs.

Definition mat_current {P} (prog : program P) st k (lower : P -> mat_run (FinSet.t tuple)) db p :=
  lev <- mat_level st p;; current <- mat_nat_test 3 Nat.eqb lev k;;
  if current then mat_rel prog db p else lower p.

Definition mat_tag_env {P} (prog : program P) st k lower acc front (q : P * bool) :=
  mat_mark 53 (
    if snd q then mat_rel prog front (fst q) else mat_current prog st k lower acc (fst q)).

(** Predicate encoders inside imported set operations remain actual typed callback occurrences. *)
Definition mat_predicate_set_calls {P} (prog : program P)
    (events : list (audit_set_event P (rules_encode_entry P))) : list mat_frame :=
  flat_map (fun event =>
    let encoded :=
      match event with
      | AuditSetAdd _ _ _ _ encoded _ | AuditSetMem _ _ _ _ encoded _ => encoded
      | _ => []
      end in
    map (fun entry =>
      match entry with
      | RulesEncodeEntry p code => MatEncode P (penc prog) p code
      end) encoded) events.

(** Imported universe preparation exposes its real encoder and arity calls. *)
Definition mat_universe_calls {P} (prog : program P)
    (events : list (rules_universe_event P)) : list mat_frame :=
  flat_map (fun event =>
    match event with
    | RuPredicatesSet _ _ inner | RuPredicateMem _ _ _ inner => mat_predicate_set_calls prog inner
    | RuArity p n => [MatArity P prog p n]
    | _ => []
    end) events.

Definition mat_universe_prepare_source {P} (prog : program P) facts p :=
  let '(state, events) := rules_universe_prepare_counted prog facts p in
  (state, MatImported _ 60 (state, events) (rules_universe_work events) 1 ::
    mat_universe_calls prog events).

Definition mat_setup_cached {P} (prog : program P) facts :=
  rule_ps <- mat_lift 54 (@length P) rules_universe_work (ru_rule_predicates (rules prog));;
  fact_ps <- mat_lift 55 (@length P) rules_universe_work (ru_fact_predicates facts);;
  ps <- mat_append rule_ps fact_ps;;
  predicates <- mat_predicate_set_encoded (mat_encode (penc prog)) ps;;
  rule_cs <- mat_lift 56 (@length positive) rules_universe_work (ru_rule_constants (rules prog));;
  fact_cs <- mat_lift 57 (@length positive) rules_universe_work (ru_fact_constants facts);;
  cs <- mat_append rule_cs fact_cs;;
  constants <- mat_of_list audit_positive_encode audit_basic_encoding_work cs;;
  mat_return (predicates, constants).

Definition mat_accept_cached {P} (prog : program P)
    (state : FinSet.t P * FinSet.t positive) p row :=
  found <- mat_get (penc prog) p (fst state);;
  present <- mat_return (
    match found with
    | Some _ => true
    | None => false
    end);;
  length <- mat_nat 4 (fun _ _ => List.length row) (List.length row) 0;; arity <- mat_arity prog p;;
  proper <- mat_nat_test 5 Nat.eqb length arity;;
  constants <- mat_all (fun c =>
    mat_lift 59 (fun _ => 1 + Pos.size_nat c + audit_trie_nodes (snd state))
      (audit_finset_source_work audit_basic_encoding_work)
      (audit_finset_mem audit_positive_encode c (snd state))) row;;
  mat_return (present && proper && constants).

Definition mat_variant {P} (prog : program P) (facts : list (ground_atom P)) lower (r : rule P)
    pivot env plan (accept : P -> tuple -> mat_run bool) : mat_run (list tuple) :=
  tagged <- mat_tag_rule (penc prog) r pivot;; ps <- mat_positive_atoms (body tagged);;
  bindings <- mat_plan_bindings ps env plan;; good <- mat_filter (mat_negative r lower) bindings;;
  rows <- mat_map (fun b => mat_instantiate b (args (head r))) good;;
  mat_filter (accept (pred (head r))) rows.

Definition mat_variant_legacy {P} (prog : program P) facts lower r pivot env plan :=
  state <- mat_universe_prepare_source prog facts (pred (head r));;
  @mat_variant P prog facts lower r pivot env plan (fun _ row =>
    mat_lift 61 (fun _ => 1 + mat_tuple_size row) rules_universe_work
      (@rules_universe_check_counted P state row)).

Definition mat_prepare_jobs {P} strategy (prog : program P) st k lower acc front :=
  specs <- mat_specs prog st k;;
  atoms <- mat_flatmap (fun spec => tagged <- mat_tag_rule (penc prog) (fst spec) (snd spec);;
    mat_positive_atoms (body tagged)) specs;;
  snapshot <- mat_snapshot_encoded (mat_tagged_encoder prog) atoms
    (mat_tag_env prog st k lower acc front);;
  mat_map (fun spec =>
    let '(r, pivot) := spec in tagged <- mat_tag_rule (penc prog) r pivot;;
    ps <- mat_positive_atoms (body tagged);;
    plan <- mat_plan_rows strategy ps
      (mat_snapshot_rows_encoded (mat_tagged_encoder prog) snapshot);;
    mat_return (spec, plan)) specs.

Definition mat_update_jobs {P} (prog : program P) (rows : P -> mat_run (list tuple))
    (jobs : list (delta_job P)) :=
  mat_map (fun job =>
    updated <- mat_plan_update (fun q => mat_return (snd q)) (fun q => rows (fst q)) (snd job);;
    mat_return (fst job, updated)) jobs.

Definition mat_candidates {P} (prog : program P) facts st k lower acc front
    (jobs : list (delta_job P)) :=
  atoms <- mat_flatmap (fun job =>
    let '((r, pivot), plan) := job in
    rows <- mat_variant_legacy prog facts lower r pivot
      (mat_tag_env prog st k lower acc front) plan;;
    mat_map (fun row => mat_return (pred (head r), row)) rows) jobs;; mat_ground_set prog atoms.

Definition mat_candidates_prepared {P} (prog : program P) facts st k lower acc front jobs cached :=
  atoms <- mat_flatmap (fun job =>
    let '((r, pivot), plan) := job in
    rows <- mat_variant prog facts lower r pivot (mat_tag_env prog st k lower acc front)
      plan (mat_accept_cached prog cached);;
    mat_map (fun row => mat_return (pred (head r), row)) rows) jobs;; mat_ground_set prog atoms.

(** The proposed tag erasure agrees with native delta rule tagging. *)
Definition mat_tag_rule_erases_statement : Prop :=
  forall P E (r : rule P) pivot, fst (mat_tag_rule E r pivot) = delta_tag_rule E r pivot.

(** The proposed job preparation erasure uses the native levels and relations. *)
Definition mat_prepare_jobs_erases_statement : Prop :=
  forall P strategy (prog : program P) st k lower acc front,
    fst (mat_prepare_jobs strategy prog (MatExternalLevels st) k (fun p => mat_return (lower p))
      acc front) = delta_prepare_jobs strategy prog st k lower acc front.

(** The proposed candidate erasure compares the legacy source run with native delta candidates. *)
Definition mat_candidates_erases_statement : Prop :=
  forall P (prog : program P) facts st k lower acc front jobs,
    fst (mat_candidates prog facts (MatExternalLevels st) k (fun p => mat_return (lower p))
      acc front jobs) =
      delta_candidates prog facts st k lower acc front jobs.
