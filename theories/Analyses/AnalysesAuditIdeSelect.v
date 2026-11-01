(** * Strict IDE selection

    Selects a generated or finite backend and records the selected execution.
    For example, incompatible weights select the finite backend.
    Builds on: AnalysesAuditIdeBase, AnalysesAuditIdeGenerated and AnalysesAuditIdeLegacy. *)

From Stdlib Require Import Decimal Arith Bool List PArith.
From Galois.Analyses Require Export AnalysesAuditIdeBase AnalysesAuditIdeGenerated
  AnalysesAuditIdeLegacy AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderBasic OrderLattice.
Import List.ListNotations.

(* Definition source: IdeSelectWhole.v *)
(** * Fixed public IDE producer, strict compatibility and exact selected execution

    Card: AUD-IDE. Construction and returned-query costs are separate. All dictionary and
    registry bodies are genuine supplied adapters; finite library bodies are expanded by the
    legacy and generated models. The generated interface never enumerates A or F. *)

Definition ide_registry_select {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (EA : encoding A) (old : ide_problem N P D A) (r : ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F) start seed initial :=
  if audit_ide_finite_compatible_check old r weight then
    let summary := ide_registry_solve EN EP ED (ide_lattice old) r (ide_graph old) weight start seed
      in
    AuditIdeFiniteSelection AuditIdeGenerated (ide_registry_query EN ED r summary initial)
  else AuditIdeFiniteSelection AuditIdeFiniteLegacy
    (audit_ide_legacy_query EN EP ED EA old start seed initial).

Section Selection.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A) (r : ide_registry A F)
  (weight : ip_edge N P D -> option D -> option D -> F).

Context (node_body : N -> nat) (site_body : P -> nat) (fact_body : D -> nat)
  (value_body : A -> nat).

Let Call := ide_generated_source_call N P D A F.

Definition ide_compatibility_value_counted edge x y a : exact_counted Call bool :=
  let transformer := weight edge x y in
  exact_bind 1100 (exact_call (IdeSourceWeight edge x y transformer) 0 transformer) (fun f =>
  let new := audit_ide_eval r f a in
  exact_bind 1101 (exact_call (IdeSourceEval f a new) 0 new) (fun new =>
  let prior := ide_weight old edge x y a in
  exact_bind 1102 (exact_call (IdeSourceOldWeight edge x y a prior) 0 prior) (fun prior =>
  let first := OrderLattice.leb (ide_lattice old) new prior in
  exact_bind 1103 (exact_call (IdeSourceLe new prior first) 0 first) (fun first =>
  let second := OrderLattice.leb (ide_lattice old) prior new in
  exact_bind 1104 (exact_call (IdeSourceLe prior new second) 0 second) (fun second =>
    exact_return 1105 (first && second)))))).

Definition ide_compatibility_counted : exact_counted Call bool :=
  exact_all 1106 (fun edge => exact_all 1107 (fun pair =>
    exact_all 1108 (ide_compatibility_value_counted edge (fst pair) (snd pair))
      (ide_values old)) (ip_pairs edge)) (ip_edges (ide_graph old)).

Definition ide_compatibility_input_budget : nat :=
  4096 * (1 + length (ip_edges (ide_graph old)) + audit_ide_strict_pair_count old +
    audit_ide_strict_pair_count old * length (ide_values old)).

(** A selection stores its mode, check, optional branches, query and associated work. *)
Record ide_source_selection : Type := IdeSourceSelection {
  ide_source_mode : audit_ide_selected_backend;
  ide_source_check : exact_counted Call bool;
  ide_source_generated : option (exact_counted Call (ide_registry_summary N D F));
  ide_source_legacy : option (ide_legacy_whole_run (N:=N) (P:=P) (D:=D) (A:=A));
  ide_source_selected_query : N -> option D -> option A;
  ide_source_selected_query_work : N -> option D -> nat;
  ide_source_build_work : nat
}.

Definition ide_select_source_counted start seed initial : ide_source_selection :=
  let check := ide_compatibility_counted in
  if exact_value check then
    let generated := ide_generated_source_counted EN EP ED r (ide_graph old)
      weight node_body site_body fact_body start seed in
    IdeSourceSelection AuditIdeGenerated check (Some generated) None
      (fun n d => exact_value (ide_generated_query_counted (P:=P) EN ED r node_body fact_body
        (exact_value generated) initial n d))
      (fun n d => exact_units (ide_generated_query_counted (P:=P) EN ED r node_body fact_body
        (exact_value generated) initial n d))
      (256 + exact_units check + exact_units generated)
  else
    let legacy := ide_legacy_whole_counted EN EP ED EA old node_body site_body fact_body
      value_body start seed initial in
    IdeSourceSelection AuditIdeFiniteLegacy check None (Some legacy)
      (fun n d => exact_value (ide_legacy_whole_query EN ED old node_body fact_body legacy n d))
      (fun n d => exact_units (ide_legacy_whole_query EN ED old node_body fact_body legacy n d))
      (256 + exact_units check + ide_legacy_whole_work EN ED EA node_body
        fact_body value_body legacy).

Definition ide_select_input_budget start seed initial : nat :=
  256 + ide_compatibility_input_budget +
  if audit_ide_finite_compatible_check old r weight then
    ide_generated_source_budget EN EP ED r (ide_graph old) weight node_body site_body fact_body
      start seed
  else ide_legacy_whole_input_budget EN EP ED EA old node_body site_body fact_body value_body start
    seed initial.

Definition ide_select_query_budget n d : nat :=
  (Nat.of_num_uint 8192%uint) + ide_legacy_query_input_budget EN ED node_body fact_body n d +
  4 * ide_fact_body EN ED node_body fact_body (inr (n,d)) +
    1024 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) (inr (n,d))).

(** The compatibility traversal returns its Boolean and charges all comparisons. *)
Definition audit_ide_compatibility_full_source_statement : Prop :=
  exact_value ide_compatibility_counted = audit_ide_finite_compatible_check old r weight /\
  exact_units ide_compatibility_counted <= ide_compatibility_input_budget /\
  length (filter (fun event => match event with
    | AuditCall (IdeSourceLe _ _ _) => true
    | _ => false
    end)
      (exact_events ide_compatibility_counted)) =
    2 * audit_ide_strict_pair_count old * length (ide_values old).

(** The selected construction and query agree with the public selector within budget. *)
Definition audit_ide_select_full_source_statement : Prop := forall start seed initial,
  ide_laws old -> ide_registry_laws (ide_lattice old) r ->
  ide_registry_congruence_laws (ide_lattice old) r ->
  In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_select_source_counted start seed initial in
  let reference := @ide_registry_select N P D A F EN EP ED EA old r weight start seed initial in
  ide_source_mode run = audit_ide_selected_mode reference /\
  ide_source_build_work run <= ide_select_input_budget start seed initial /\
  (ide_source_mode run = AuditIdeGenerated <->
    audit_ide_finite_compatible_check old r weight = true) /\
  forall n d, ide_source_selected_query run n d = audit_ide_selected_query reference n d /\
    ide_source_selected_query_work run n d <= ide_select_query_budget n d.

End Selection.

(** These public semantic obligations are instantiated to the fixed producer above. They
    retain all old path/rank/congruence and finite-selection premises without a census. *)

(** Under the stated laws, the fixed producer gives the least upper bounds of reachable paths. *)
Definition audit_ide_fixed_public_paths_statement : Prop := audit_ide_public_paths
  (@ide_registry_solve).

(** The fixed producer distinguishes absent paths from reachable bottom. *)
Definition audit_ide_fixed_public_bottom_statement : Prop := audit_ide_public_bottom
  (@ide_registry_solve).

(** The fixed producer supplies the required update trace. *)
Definition audit_ide_fixed_public_updates_statement : Prop := audit_ide_public_updates
  (@ide_registry_solve).

(** The fixed producer agrees with a compatible finite backend. *)
Definition audit_ide_fixed_public_finite_agreement_statement : Prop :=
  audit_ide_public_finite_agreement (@ide_registry_solve).

(** The fixed selector preserves finite backend behavior. *)
Definition audit_ide_fixed_public_select_correct_statement : Prop :=
  audit_ide_public_select_correct (@ide_registry_solve).

(** The fixed producer satisfies the stream path observation. *)
Definition audit_ide_fixed_stream_consumer_statement : Prop :=
  audit_ide_public_stream_consumer (@ide_registry_solve).

(** The fixed producer preserves reachable stream bottom. *)
Definition audit_ide_fixed_stream_bottom_statement : Prop :=
  audit_ide_public_stream_bottom (@ide_registry_solve).

(* Definition source: IdeSelectorConsumers.v *)
(** Card: AUD-IDE. Concrete public-client proof targets for both selected branches. *)
Definition audit_ide_selector_client : ide_problem bool unit unit bool :=
  IdeProblem (IpProblem [false] [] [] [IpEdge false false IpInternal [(None,None)]])
    bool_lattice [false;true] (fun _ _ _ value => value).

Definition audit_ide_selector_registry : ide_registry bool bool :=
  {| audit_ide_eval := fun f a => orb a f;
    audit_ide_id := false;
    audit_ide_compose := orb;
    audit_ide_join := orb;
    audit_ide_equal := Bool.eqb;
    audit_ide_rank := fun f => if f then 1 else 0;
    audit_ide_bound := 1 |}.

(** The concrete compatible client selects the generated backend. *)
Definition audit_ide_selector_fast_consumer_statement : Prop :=
  let weight := fun (_ : ip_edge bool unit unit) (_ _ : option unit) => false in
  let run := ide_select_source_counted bool_encoding unit_encoding unit_encoding bool_encoding
    audit_ide_selector_client audit_ide_selector_registry weight
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) false None false in
  ide_source_mode run = AuditIdeGenerated /\ ide_source_legacy run = None /\
  exact_value (ide_source_check run) = true /\
  ide_source_selected_query run false None = Some false /\
  ide_source_selected_query run true None = None /\
  0 < ide_source_build_work run /\
  ide_source_build_work run <= ide_select_input_budget bool_encoding unit_encoding unit_encoding
    bool_encoding audit_ide_selector_client audit_ide_selector_registry weight
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) false None false.

(** The concrete incompatible client selects the finite backend. *)
Definition audit_ide_selector_fallback_consumer_statement : Prop :=
  let weight := fun (_ : ip_edge bool unit unit) (_ _ : option unit) => true in
  let run := ide_select_source_counted bool_encoding unit_encoding unit_encoding bool_encoding
    audit_ide_selector_client audit_ide_selector_registry weight
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) false None false in
  ide_source_mode run = AuditIdeFiniteLegacy /\ ide_source_generated run = None /\
  exact_value (ide_source_check run) = false /\
  ide_source_selected_query run false None = Some false /\
  ide_source_selected_query run true None = None /\
  0 < ide_source_build_work run /\
  ide_source_build_work run <= ide_select_input_budget bool_encoding unit_encoding unit_encoding
    bool_encoding audit_ide_selector_client audit_ide_selector_registry weight
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) false None false.

(** Both selector branches and the stream observations have concrete obligations. *)
Definition audit_ide_nonempty_full_source_statement : Prop :=
  audit_ide_selector_fast_consumer_statement /\ audit_ide_selector_fallback_consumer_statement /\
  audit_ide_fixed_stream_consumer_statement /\ audit_ide_fixed_stream_bottom_statement.

(** * Whole selected execution with callback bodies

    Each compatibility callback runs its genuine counted adapter once. The selected branch
    uses the corresponding whole body model, and retains its actual callback receipts.
    For example, a failed compatibility test returns the finite fallback's own query.
    Builds on: generated and legacy body models. *)
Section SelectionBodies.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A) (r : ide_registry A F)
  (weight : ip_edge N P D -> option D -> option D -> F)
  (dictionary : audit_ide_registry_adapters r) (weighted : audit_ide_weight_adapter weight)
  (legacy : audit_ide_legacy_adapters EN EP ED EA old).

Let encoders := ide_legacy_graph_encoding legacy.

Let nb := external_input_budget (ide_node_encoding_adapter encoders).

Let pb := external_input_budget (ide_site_encoding_adapter encoders).

Let db := external_input_budget (ide_fact_encoding_adapter encoders).

Let ab := external_input_budget (ide_value_encoding_adapter legacy).

Let Call := ide_generated_source_call N P D A F.

Definition ide_compatibility_value_with_bodies edge x y a : exact_counted Call bool :=
  exact_bind 2300 (exact_external_call weighted (edge,(x,y))
    (fun output => IdeSourceWeight edge x y output)) (fun f =>
  exact_bind 2301 (exact_external_call (ide_eval_adapter dictionary) (f,a)
    (fun output => IdeSourceEval f a output)) (fun new =>
  exact_bind 2302 (exact_external_call (ide_legacy_weight_adapter legacy) (edge,(x,(y,a)))
    (fun output => IdeSourceOldWeight edge x y a output)) (fun prior =>
  exact_bind 2303 (exact_external_call (ide_lattice_order_adapter legacy) (new,prior)
    (fun output => IdeSourceLe new prior output)) (fun first =>
  exact_bind 2304 (exact_external_call (ide_lattice_order_adapter legacy) (prior,new)
    (fun output => IdeSourceLe prior new output)) (fun second =>
    exact_return 2305 (first && second)))))).

Definition ide_compatibility_with_bodies : exact_counted Call bool :=
  exact_all 2306 (fun edge => exact_all 2307 (fun pair =>
    exact_all 2308 (ide_compatibility_value_with_bodies edge (fst pair) (snd pair))
      (ide_values old)) (ip_pairs edge)) (ip_edges (ide_graph old)).

(** A compatibility callback receipt matches its actual external adapter. *)
Definition ide_compatibility_body_valid (body : Call * list audit_external_frame) : Prop :=
  match fst body with
  | IdeSourceWeight edge x y output =>
    audit_external_body weighted (edge,(x,y)) output (snd body)
  | IdeSourceEval f input output =>
    audit_external_body (ide_eval_adapter dictionary) (f,input) output (snd body)
  | IdeSourceOldWeight edge x y input output =>
    audit_external_body (ide_legacy_weight_adapter legacy) (edge,(x,(y,input))) output
      (snd body)
  | IdeSourceLe first second output =>
    audit_external_body (ide_lattice_order_adapter legacy) (first,second) output (snd body)
  | _ => False
  end.

Definition ide_compatibility_body_budget (body : Call * list audit_external_frame) : nat :=
  match fst body with
  | IdeSourceWeight edge x y _ => external_input_budget weighted (edge,(x,y))
  | IdeSourceEval f input _ => external_input_budget (ide_eval_adapter dictionary) (f,input)
  | IdeSourceOldWeight edge x y input _ =>
    external_input_budget (ide_legacy_weight_adapter legacy) (edge,(x,(y,input)))
  | IdeSourceLe first second _ =>
    external_input_budget (ide_lattice_order_adapter legacy) (first,second)
  | _ => 0
  end.

Definition ide_select_with_bodies start seed initial : ide_source_selection :=
  let check := ide_compatibility_with_bodies in
  if exact_value check then
    let generated := ide_generated_with_bodies_counted EN EP ED r (ide_graph old)
      weight encoders dictionary weighted start seed in
    IdeSourceSelection AuditIdeGenerated check (Some generated) None
      (fun n d => exact_value (ide_generated_query_with_bodies_counted (P:=P) EN EP ED r
        encoders dictionary (exact_value generated) initial n d))
      (fun n d => exact_units (ide_generated_query_with_bodies_counted (P:=P) EN EP ED r
        encoders dictionary (exact_value generated) initial n d))
      (256 + exact_units check + exact_units generated)
  else
    let finite := ide_legacy_whole_counted_with_bodies EN EP ED EA old legacy
      start seed initial in
    IdeSourceSelection AuditIdeFiniteLegacy check None (Some finite)
      (fun n d => exact_value (ide_legacy_whole_query EN ED old nb db finite n d))
      (fun n d => exact_units (ide_legacy_whole_query EN ED old nb db finite n d))
      (256 + exact_units check + ide_legacy_whole_work EN ED EA nb db ab finite).

Definition ide_select_body_allowance (run : ide_source_selection) : nat :=
  fold_right (fun body rest => ide_compatibility_body_budget body + rest) 0
    (exact_bodies (ide_source_check run)) +
  match ide_source_generated run with
  | Some generated => ide_generated_external_allowance r weight dictionary weighted
      (exact_bodies generated)
  | None => 0
  end +
  match ide_source_legacy run with
  | Some finite => fold_right (fun body rest => ide_legacy_body_budget EN EP ED EA old legacy body +
    rest) 0
      (ide_legacy_actual_bodies finite)
  | None => 0
  end.

(** Selected construction and query retain exact public results and charge every callback body. *)
Definition audit_ide_select_with_bodies_statement : Prop :=
  audit_ide_registry_adapter_laws dictionary -> audit_external_adapter_laws weighted ->
  audit_ide_legacy_adapter_laws legacy -> forall start seed initial,
  ide_laws old -> ide_registry_laws (ide_lattice old) r ->
  ide_registry_congruence_laws (ide_lattice old) r ->
  In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_select_with_bodies start seed initial in
  let plain := ide_registry_select EN EP ED EA old r weight start seed initial in
  ide_source_mode run = audit_ide_selected_mode plain /\
  Forall ide_compatibility_body_valid (exact_bodies (ide_source_check run)) /\
  ide_source_build_work run <=
    16 * ide_select_input_budget EN EP ED EA old r weight nb pb db ab start seed initial +
    ide_select_body_allowance run /\
  forall n d,
    ide_source_selected_query run n d = audit_ide_selected_query plain n d /\
    ide_source_selected_query_work run n d <=
      16 * ide_select_query_budget EN ED nb db n d +
      match ide_source_generated run with
      | Some generated => ide_generated_external_allowance r weight dictionary weighted
          (exact_bodies (ide_generated_query_with_bodies_counted (P:=P) EN EP ED r encoders
            dictionary (exact_value generated) initial n d))
      | None => 0
      end.

End SelectionBodies.

(** * Closed instances of reusable algorithm predicates

    Generic predicates over an arbitrary solver or generator are specification vocabulary.
    The future claims below use the actual fixed producer, generator and direct query.
    For example, the stream consumer runs the indexed producer on its retained graph.
    Builds on: the public producer and its pure mathematical summary view. *)
Definition audit_ide_fixed_execute {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
    weight start seed : audit_ide_summary N D F :=
  audit_ide_public_view (ide_registry_solve EN EP ED L r q weight start seed).

(** The fixed generator enumerates the bounded ground rules. *)
Definition audit_ide_fixed_rule_generator_statement : Prop :=
  audit_ide_rule_generator_statement (@audit_ide_ground_rules).

(** The fixed generator preserves the occurrence-based rule count. *)
Definition audit_ide_fixed_generator_occurrences_statement : Prop :=
  audit_ide_generator_occurrences_statement (@audit_ide_ground_rules).

(** The fixed generator preserves the exact reference rows. *)
Definition audit_ide_fixed_generator_exact_rows_statement : Prop :=
  audit_ide_generator_exact_rows_statement (@audit_ide_ground_rules).

(** The fixed producer observes the generated-rule machine. *)
Definition audit_ide_fixed_machine_consumer_statement : Prop :=
  audit_ide_machine_consumer_statement (@audit_ide_ground_rules) (@audit_ide_fixed_execute).

(** The fixed producer bounds its indexed incidence visits. *)
Definition audit_ide_fixed_public_incidence_bound_statement : Prop :=
  audit_ide_public_incidence_bound_statement (@audit_ide_ground_rules) (@audit_ide_fixed_execute).

(** The fixed producer bounds probe, join and composition counts. *)
Definition audit_ide_fixed_public_probe_counts_statement : Prop :=
  audit_ide_public_probe_counts_statement (@audit_ide_ground_rules) (@audit_ide_fixed_execute).

(** The counted producer agrees with the fixed generated producer. *)
Definition audit_ide_fixed_generator_producer_statement : Prop :=
  audit_ide_producer_counted_statement (@ide_registry_solve).

(** The fixed producer computes exact path joins under congruence. *)
Definition audit_ide_fixed_path_exact_statement : Prop :=
  audit_ide_strong_path_exact_statement (@audit_ide_fixed_execute).

(** The fixed producer agrees with a compatible finite solver. *)
Definition audit_ide_fixed_finite_agreement_statement : Prop :=
  audit_ide_strong_finite_agreement_statement (@audit_ide_fixed_execute).

(** The fixed finite selector preserves the legacy result. *)
Definition audit_ide_fixed_finite_select_correct_statement : Prop :=
  audit_ide_finite_select_correct_statement (@audit_ide_fixed_execute).

(** The fixed execution satisfies the stream path observation. *)
Definition audit_ide_fixed_stream_execute_statement : Prop :=
  audit_ide_stream_consumer_statement (@audit_ide_fixed_execute nat nat unit audit_ide_stream bool).

(** The fixed execution preserves reachable stream bottom. *)
Definition audit_ide_fixed_stream_bottom_execute_statement : Prop :=
  audit_ide_stream_bottom_statement (@audit_ide_fixed_execute nat nat unit audit_ide_stream bool).

(** The fixed execution records its generated-rule trace. *)
Definition audit_ide_fixed_execute_trace_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight,
    audit_ide_execute_trace_statement EN EP ED L r q weight
      (@audit_ide_fixed_execute N P D A F).

(** The fixed execution returns a closed rule state. *)
Definition audit_ide_fixed_execute_closed_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight,
    audit_ide_execute_closed_statement EN EP ED L r q weight
      (@audit_ide_fixed_execute N P D A F).
