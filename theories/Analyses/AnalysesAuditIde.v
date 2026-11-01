(** * Whole IDE caller and source closure

    Defines source receipts and proposition types for the complete IDE caller.
    For example, a reached fact key records its node and optional fact encoder calls.
    Builds on: AnalysesAuditIdeSelect, AnalysesAuditIdeLegacy and AnalysesAuditIdeGenerated. *)

From Stdlib Require Import Arith Bool List PArith.
From Galois.Analyses Require Export AnalysesAuditIdeBase AnalysesAuditIdeGenerated
  AnalysesAuditIdeLegacy AnalysesAuditIdeSelect AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditQueue
  CollectionsAuditTrie CollectionsAuditUnion CollectionsEncoding CollectionsMap.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
From Galois.Order Require Import OrderLattice.
Import List.ListNotations.

(* Definition source: IdeDerivedEncoding.v *)
(** Card: AUD-IDE. Concrete library-owned derived encoders and exact adequacy targets. *)

Definition ide_vertex_source_encoding {N D} (EN : encoding N) (ED : encoding D) :=
  audit_pair_encode (ide_encoding_entry EN) (audit_option_encode (ide_encoding_entry ED)).

Definition ide_vertex_source_encoding_work {N D} (nb : N -> nat) (db : D -> nat) :=
  audit_pair_events_work (A:=N) (B:=option D) (ide_encoding_entry_work nb)
    (audit_option_events_work (A:=D) (ide_encoding_entry_work db)).

Definition ide_fact_source_encoding {N D} (EN : encoding N) (ED : encoding D) :=
  let vertex := ide_vertex_source_encoding EN ED in
  audit_sum_encode (audit_pair_encode vertex vertex) vertex.

Definition ide_fact_source_encoding_work {N D} (nb : N -> nat) (db : D -> nat) :=
  let vertex := ide_vertex_source_encoding_work nb db in
  audit_sum_events_work (A:=(N * option D) * (N * option D)) (B:=N * option D)
    (audit_pair_events_work (A:=N * option D) (B:=N * option D) vertex vertex) vertex.

Definition ide_lifted_source_encoding {D A} (ED : encoding D) (EA : encoding A) :=
  audit_pair_encode (audit_option_encode (ide_encoding_entry ED))
    (audit_list_encode (ide_encoding_entry EA)).

Definition ide_lifted_source_encoding_work {D A} (db : D -> nat) (ab : A -> nat) :=
  audit_pair_events_work (A:=option D) (B:=list A)
    (audit_option_events_work (A:=D) (ide_encoding_entry_work db))
    (audit_list_events_work (A:=A) (ide_encoding_entry_work ab)).

(** Derived vertex, fact and lifted encoders match their concrete encodings. *)
Definition audit_ide_derived_encoding_adequacy_statement : Prop :=
  (forall N D (EN : encoding N) (ED : encoding D) (nb : N -> nat) (db : D -> nat) key,
    let run := ide_vertex_source_encoding EN ED key in
    fst run = encode (IpTab.vertex_encoding EN ED) key /\
    ide_vertex_source_encoding_work nb db (snd run) <= ide_vertex_encoding_body EN ED nb db key) /\
  (forall N D (EN : encoding N) (ED : encoding D) (nb : N -> nat) (db : D -> nat) key,
    let run := ide_fact_source_encoding EN ED key in
    fst run = encode (IpTab.fact_encoding EN ED) key /\
    ide_fact_source_encoding_work nb db (snd run) <= ide_fact_body EN ED nb db key) /\
  (forall D A (ED : encoding D) (EA : encoding A) (db : D -> nat) (ab : A -> nat) key,
    let run := ide_lifted_source_encoding ED EA key in
    fst run = encode (IdeTab.lifted_encoding ED EA) key /\
    ide_lifted_source_encoding_work db ab (snd run) <= ide_lifted_encoding_body ED EA db ab key).

Definition ide_horn_rule_source_encoding {K} (EK : encoding K) (rule : IpHorn.rule K) :=
  let element := ide_encoding_entry EK in
  let pair := audit_pair_encode element element in
  let triple := audit_pair_encode pair element in
  audit_sum_encode element (audit_sum_encode pair triple) (IpHorn.code EK rule).

Definition ide_horn_rule_source_encoding_work {K} (body : K -> nat) :=
  let element := ide_encoding_entry_work body in
  let pair := audit_pair_events_work (A:=K) (B:=K) element element in
  let triple := audit_pair_events_work (A:=K * K) (B:=K) pair element in
  audit_sum_events_work (A:=K) (B:=K * K + (K * K) * K) element
    (audit_sum_events_work (A:=K * K) (B:=(K * K) * K) pair triple).

(** The Horn rule encoder matches its concrete encoding within its allowance. *)
Definition audit_ide_horn_rule_encoding_adequacy_statement : Prop :=
  forall K (EK : encoding K) (body : K -> nat) rule,
    let run := ide_horn_rule_source_encoding EK rule in
    fst run = encode (IpHorn.rule_encoding EK) rule /\
    ide_horn_rule_source_encoding_work body (snd run) <= ide_horn_rule_encoding_body EK body rule.

(* Definition source: IdeFullSource.v *)
(** * Whole IDE source and implementation bridge obligations

    Card: AUD-IDE. Fixed local blocks cost64; fixed source primitives and library-created
    encoders are expanded below. Genuine supplied dictionary/weight/encoding bodies retain
    their actual entry events; body adapters are separate from this caller-work guarantee. *)
Section LegacyAdequacy.

Context {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A)
  (nb : N -> nat) (pb : P -> nat) (db : D -> nat) (ab : A -> nat).

Definition ide_legacy_literal_event_work (event : audit_event (ide_legacy_call N P D A)) : nat :=
  match event with
  | AuditCall (IdeLegacyTables call) => ide_table_literal_event_work EA ab (AuditCall call)
  | AuditCall (IdeLegacyLiftedSet call) =>
      exact_map_literal_work (ide_lifted_encoding_body ED EA db ab) call
  | AuditCall (IdeLegacyJoinMap call) =>
      exact_map_literal_work (ide_vertex_encoding_body EN ED nb db) call
  | AuditCall (IdeLegacyDirectMap call) => exact_map_literal_work (ide_fact_body EN ED nb db) call
  | AuditCall (IdeLegacyReachMap call) =>
      exact_map_literal_work (ide_fact_body EN (IdeTab.lifted_encoding ED EA) nb
        (ide_lifted_encoding_body ED EA db ab)) call
  | _ => 64
  end.

Definition ide_legacy_literal_work (events : audit_trace (ide_legacy_call N P D A)) : nat :=
  fold_right (fun e rest => ide_legacy_literal_event_work e + rest) 0 events.

(** The legacy stages charge their actual primitive events. *)
Definition audit_ide_legacy_implementation_adequacy_statement : Prop := forall start seed initial,
  let run := ide_legacy_whole_counted EN EP ED EA old nb pb db ab start seed initial in
  ide_legacy_literal_work (exact_events (ide_legacy_graph_stage run)) <=
    exact_units (ide_legacy_graph_stage run) /\
  ide_legacy_literal_work (exact_events (ide_legacy_seed_stage run)) <=
    exact_units (ide_legacy_seed_stage run) /\
  ide_legacy_literal_work (exact_events (ide_legacy_contribution_stage run)) <=
    exact_units (ide_legacy_contribution_stage run) /\
  ide_legacy_literal_work (exact_events (ide_legacy_collection_stage run)) <=
    exact_units (ide_legacy_collection_stage run) /\
  forall n d, ide_legacy_literal_work
    (exact_events (ide_legacy_whole_query EN ED old nb db run n d)) <=
    exact_units (ide_legacy_whole_query EN ED old nb db run n d).

End LegacyAdequacy.

Section HornAdequacy.

Context {K} (EK : encoding K) (body : K -> nat).

Definition ide_horn_literal_call_work (call : fx_declared_call K (IpHorn.rule K) bool) : nat :=
  match call with
  | FxGet key code before _ _ => 16 + body key + audit_trie_get_source_work code before
  | FxReaders key code before _ _ => 16 + body key + audit_trie_get_source_work code before
  | FxSet key code value before _ _ =>
      16 + body key + audit_trie_update_source_work code (Some (key,value)) before
  | FxPush _ _ _ _ events | FxPop _ _ events => 64 + ide_horn_nested_queue_source_work EK body
    events
  | _ => 64
  end.

Definition ide_horn_literal_work (events : audit_trace (fx_declared_call K (IpHorn.rule K) bool)) :=
  fold_right (fun event rest => match event with
    | AuditCall call => ide_horn_literal_call_work call + rest
    | _ => 64 + rest
    end) 0 events.

(** The Horn engine charges its actual initial and run events. *)
Definition audit_ide_horn_implementation_adequacy_statement : Prop := forall rules,
  let run := ide_horn_total_counted EK body rules in
  ide_horn_literal_work (ide_horn_initial_events run) <=
    ide_horn_source_work EK body (ide_horn_initial_events run) /\
  ide_horn_literal_work (ide_horn_run_events run) <=
    ide_horn_source_work EK body (ide_horn_run_events run).

End HornAdequacy.

(** The finite backend combines its source and primitive obligations. *)
Definition audit_ide_legacy_family_statement : Prop :=
  forall N P D A (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
    (old : ide_problem N P D A) (nb : N -> nat) (pb : P -> nat) (db : D -> nat) (ab : A -> nat),
  audit_ide_legacy_full_source_statement EN EP ED EA old nb pb db ab /\
  audit_ide_legacy_implementation_adequacy_statement EN EP ED EA old nb pb db ab.

(** The indexed backend combines construction and query obligations. *)
Definition audit_ide_generated_family_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight
    (nb : N -> nat) (pb : P -> nat) (db : D -> nat),
  audit_ide_generated_full_source_statement EN EP ED L r q weight nb pb db /\
  audit_ide_generated_query_source_statement (P:=P) EN ED r nb db.

(** Selection combines compatibility and chosen-backend source obligations. *)
Definition audit_ide_selector_full_source_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
    (old : ide_problem N P D A) (r : ide_registry A F) weight
    (nb : N -> nat) (pb : P -> nat) (db : D -> nat) (ab : A -> nat),
  audit_ide_compatibility_full_source_statement old r weight /\
  audit_ide_select_full_source_statement EN EP ED EA old r weight nb pb db ab.

(** Map, encoding, table, generated primitive, Horn and legacy duties form this conjunction. *)
Definition audit_ide_implementation_adequacy_statement : Prop :=
  exact_map_implementation_adequacy_statement /\ ide_list_encoding_adequacy_statement /\
  audit_ide_derived_encoding_adequacy_statement /\
  audit_ide_horn_rule_encoding_adequacy_statement /\
  ide_tables_implementation_adequacy_statement /\ ide_generated_primitive_adequacy_statement /\
  (forall K (EK : encoding K) (body : K -> nat), audit_ide_horn_implementation_adequacy_statement EK
    body) /\
  audit_ide_legacy_family_statement.

(** Caller obligations combine both source models with public semantics. *)
Definition audit_ide_caller_source_statement : Prop :=
  audit_ide_generated_family_statement /\ audit_ide_selector_full_source_statement /\
  audit_ide_implementation_adequacy_statement /\
  audit_ide_fixed_public_paths_statement /\ audit_ide_fixed_public_bottom_statement /\
  audit_ide_fixed_public_updates_statement /\ audit_ide_fixed_public_finite_agreement_statement /\
  audit_ide_fixed_public_select_correct_statement /\ audit_ide_fixed_stream_consumer_statement /\
  audit_ide_fixed_stream_bottom_statement.

(** * Actual derived-encoding source receipts

    Library pair, option, sum and list constructors retain their concrete collection source
    equations. Only original supplied base encoders use genuine external source receipts.
    For example, a reached-fact key records its node encoder and optional fact encoder.
    Builds on: the fixed derived encoders and relational component receipts. *)
Section EncodingReceipts.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A)
  (adapters : audit_ide_legacy_adapters EN EP ED EA old).

Let graph_adapters := ide_legacy_graph_encoding adapters.

Let node_adapter := ide_node_encoding_adapter graph_adapters.

Let site_adapter := ide_site_encoding_adapter graph_adapters.

Let fact_adapter := ide_fact_encoding_adapter graph_adapters.

Let value_adapter := ide_value_encoding_adapter adapters.

Let nb := external_input_budget node_adapter.

Let pb := external_input_budget site_adapter.

Let db := external_input_budget fact_adapter.

Let ab := external_input_budget value_adapter.

(** The option encoding retains receipts for its present component. *)
Definition ide_option_encoding_receipts input output events trace : Prop :=
  (output,events) = audit_option_encode (ide_encoding_entry ED) input /\
  audit_option_encoding_receipts (audit_base_encoding_receipts ED fact_adapter) events trace.

(** A vertex receipt combines node and optional fact encoding bodies. *)
Definition ide_vertex_encoding_receipts input output events trace : Prop :=
  (output,events) = ide_vertex_source_encoding EN ED input /\
  audit_pair_encoding_receipts (audit_base_encoding_receipts EN node_adapter)
    ide_option_encoding_receipts events trace.

(** A vertex-pair receipt combines both vertex encodings. *)
Definition ide_vertex_pair_encoding_receipts input output events trace : Prop :=
  (output,events) = audit_pair_encode (ide_vertex_source_encoding EN ED)
    (ide_vertex_source_encoding EN ED) input /\
  audit_pair_encoding_receipts ide_vertex_encoding_receipts ide_vertex_encoding_receipts
    events trace.

(** A fact receipt follows the selected sum and vertex encodings. *)
Definition ide_fact_encoding_receipts input output events trace : Prop :=
  (output,events) = ide_fact_source_encoding EN ED input /\
  audit_sum_encoding_receipts ide_vertex_pair_encoding_receipts ide_vertex_encoding_receipts
    events trace.

(** A value-list receipt retains each base value encoding. *)
Definition ide_value_list_encoding_receipts input output events trace : Prop :=
  (output,events) = audit_list_encode (ide_encoding_entry EA) input /\
  audit_list_encoding_receipts (audit_base_encoding_receipts EA value_adapter) events trace.

(** A lifted-key receipt combines optional fact and value-list bodies. *)
Definition ide_lifted_encoding_receipts input output events trace : Prop :=
  (output,events) = ide_lifted_source_encoding ED EA input /\
  audit_pair_encoding_receipts ide_option_encoding_receipts ide_value_list_encoding_receipts
    events trace.

(** Every actual derived encoder has a concrete source and a body allowance from base laws. *)
Definition audit_ide_encoding_body_receipts_statement : Prop :=
  audit_ide_legacy_adapter_laws adapters ->
  (forall key output, output = encode (IpTab.vertex_encoding EN ED) key ->
    exists trace,
      ide_vertex_encoding_receipts key output
        (snd (ide_vertex_source_encoding EN ED key)) trace /\
      ide_vertex_source_encoding_work (fun _ => 0) (fun _ => 0)
        (snd (ide_vertex_source_encoding EN ED key)) + audit_external_trace_work trace <=
        4 * ide_vertex_encoding_body EN ED nb db key) /\
  (forall key output, output = encode (IpTab.fact_encoding EN ED) key ->
    exists trace,
      ide_fact_encoding_receipts key output
        (snd (ide_fact_source_encoding EN ED key)) trace /\
      ide_fact_source_encoding_work (fun _ => 0) (fun _ => 0)
        (snd (ide_fact_source_encoding EN ED key)) + audit_external_trace_work trace <=
        4 * ide_fact_body EN ED nb db key) /\
  (forall key output, output = encode (IdeTab.lifted_encoding ED EA) key ->
    exists trace,
      ide_lifted_encoding_receipts key output
        (snd (ide_lifted_source_encoding ED EA key)) trace /\
      ide_lifted_source_encoding_work (fun _ => 0) (fun _ => 0)
        (snd (ide_lifted_source_encoding ED EA key)) + audit_external_trace_work trace <=
        4 * ide_lifted_encoding_body ED EA db ab key).

End EncodingReceipts.

Section GeneratedCallReceipts.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A) (r : ide_registry A F)
  (weight : ip_edge N P D -> option D -> option D -> F)
  (legacy : audit_ide_legacy_adapters EN EP ED EA old)
  (registry : audit_ide_registry_adapters r) (weighted : audit_ide_weight_adapter weight).

Let encoders := ide_legacy_graph_encoding legacy.

Let nb := external_input_budget (ide_node_encoding_adapter encoders).

Let pb := external_input_budget (ide_site_encoding_adapter encoders).

Let db := external_input_budget (ide_fact_encoding_adapter encoders).

Let Call := ide_generated_source_call N P D A F.

(** The actual fact encoder retains its derived encoding receipt. *)
Definition ide_actual_fact_encoding_source key trace : Prop :=
  ide_fact_encoding_receipts EN EP ED EA old legacy key
    (encode (IpTab.fact_encoding EN ED) key)
    (snd (ide_fact_source_encoding EN ED key)) trace.

(** The kind encoder records a site call only for calls and returns. *)
Definition ide_actual_kind_encoding_source kind trace : Prop :=
  match kind with
  | IpInternal => trace = []
  | IpCall site | IpReturn site => audit_external_same_call
      (ide_site_encoding_adapter encoders) site (encode EP site) trace
  end.

(** Each generator event records its actual external body calls. *)
Definition ide_generator_actual_source (event : audit_ide_generator_call N P D F) trace : Prop :=
  match event with
  | IdeGeneratorWeight edge x y output =>
    audit_external_same_call weighted (edge,(x,y)) output trace
  | IdeGeneratorIndexGet kind _ _ | IdeGeneratorIndexSet kind _ _ =>
    ide_actual_kind_encoding_source kind trace
  | _ => trace = []
  end.

(** Initialization records source receipts for fact-index operations. *)
Definition ide_initial_actual_source (event : audit_ide_initial_call N D F) trace : Prop :=
  match event with
  | IdeInitIndexGet _ key _ _ | IdeInitIndexSet _ key _ _ =>
    ide_actual_fact_encoding_source key trace
  | _ => trace = []
  end.

(** Machine events record the callback or fact-encoder bodies they invoke. *)
Definition ide_machine_actual_source (event : audit_ide_machine_call N D F) trace : Prop :=
  match event with
  | IdeMachineCompose first second output =>
    audit_external_same_call (ide_compose_adapter registry) (first,second) output trace
  | IdeMachineJoin first second output =>
    audit_external_same_call (ide_join_adapter registry) (first,second) output trace
  | IdeMachineEqual first second output =>
    audit_external_same_call (ide_equal_adapter registry) (first,second) output trace
  | IdeMachineFactRead key _ _ | IdeMachineFactWrite key _ _ _ |
      IdeMachineIncidenceRead key _ _ => ide_actual_fact_encoding_source key trace
  | _ => trace = []
  end.

(** Each event is paired with its own trace, and the resulting trace concatenates them in order. *)
Definition ide_nested_receipts {X} (source : X -> list audit_external_frame -> Prop)
    (events : list X) trace : Prop :=
  exists traces, Forall2 source events traces /\ trace = concat traces.

(** Generated events retain nested and direct external body receipts. *)
Definition ide_generated_actual_source (event : audit_event Call) trace : Prop :=
  match event with
  | AuditCall (IdeSourceGenerator nested) =>
    ide_nested_receipts ide_generator_actual_source nested trace
  | AuditCall (IdeSourceInitial nested) =>
    ide_nested_receipts ide_initial_actual_source nested trace
  | AuditCall (IdeSourceMachine nested) =>
    ide_nested_receipts ide_machine_actual_source nested trace
  | AuditCall (IdeSourceWeight edge x y output) =>
    audit_external_same_call weighted (edge,(x,y)) output trace
  | AuditCall (IdeSourceEval f input output) =>
    audit_external_same_call (ide_eval_adapter registry) (f,input) output trace
  | AuditCall (IdeSourceFact (ExactEncode key code)) =>
    code = encode (IpTab.fact_encoding EN ED) key /\
    ide_actual_fact_encoding_source key trace
  | _ => trace = []
  end.

Definition ide_generator_actual_body_budget (event : audit_ide_generator_call N P D F) : nat :=
  match event with
  | IdeGeneratorWeight edge x y _ => external_input_budget weighted (edge,(x,y))
  | IdeGeneratorIndexGet kind _ _ | IdeGeneratorIndexSet kind _ _ =>
    match kind with
    | IpInternal => 0
    | IpCall site | IpReturn site => pb site
    end
  | _ => 0
  end.

Definition ide_initial_actual_body_budget (event : audit_ide_initial_call N D F) : nat :=
  match event with
  | IdeInitIndexGet _ key _ _ | IdeInitIndexSet _ key _ _ =>
    4 * ide_fact_body EN ED nb db key
  | _ => 0
  end.

Definition ide_machine_actual_body_budget (event : audit_ide_machine_call N D F) : nat :=
  match event with
  | IdeMachineCompose first second _ =>
    external_input_budget (ide_compose_adapter registry) (first,second)
  | IdeMachineJoin first second _ =>
    external_input_budget (ide_join_adapter registry) (first,second)
  | IdeMachineEqual first second _ =>
    external_input_budget (ide_equal_adapter registry) (first,second)
  | IdeMachineFactRead key _ _ | IdeMachineFactWrite key _ _ _ |
      IdeMachineIncidenceRead key _ _ => 4 * ide_fact_body EN ED nb db key
  | _ => 0
  end.

Definition ide_generated_actual_body_budget (event : audit_event Call) : nat :=
  match event with
  | AuditCall (IdeSourceGenerator nested) =>
    fold_right (fun event rest => ide_generator_actual_body_budget event + rest) 0 nested
  | AuditCall (IdeSourceInitial nested) =>
    fold_right (fun event rest => ide_initial_actual_body_budget event + rest) 0 nested
  | AuditCall (IdeSourceMachine nested) =>
    fold_right (fun event rest => ide_machine_actual_body_budget event + rest) 0 nested
  | AuditCall (IdeSourceWeight edge x y _) => external_input_budget weighted (edge,(x,y))
  | AuditCall (IdeSourceEval f input _) =>
    external_input_budget (ide_eval_adapter registry) (f,input)
  | AuditCall (IdeSourceFact (ExactEncode key _)) => 4 * ide_fact_body EN ED nb db key
  | _ => 0
  end.

(** The fixed producer's actual caller stream carries source bodies on the same execution. *)
Definition audit_ide_actual_generated_source_statement : Prop :=
  audit_ide_legacy_adapter_laws legacy -> audit_ide_registry_adapter_laws registry ->
  audit_external_adapter_laws weighted -> forall start seed,
  ide_registry_laws (ide_lattice old) r -> ip_problem_wf (ide_graph old) ->
  In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_generated_source_counted EN EP ED r (ide_graph old) weight nb pb db start seed in
  exists traces,
    Forall2 ide_generated_actual_source (exact_events run) traces /\
    exact_value run = ide_registry_solve EN EP ED (ide_lattice old) r
      (ide_graph old) weight start seed /\
    exact_units run + audit_source_body_work traces <=
      16 * ide_generated_source_budget EN EP ED r (ide_graph old) weight nb pb db start seed +
      fold_right (fun event rest => ide_generated_actual_body_budget event + rest) 0
        (exact_events run).

End GeneratedCallReceipts.

(** * Source receipts for every actual finite-backend encoder call

    These relations inspect retained caller events. Library-created encoders expand their
    actual option/list/pair/sum bodies; no internal function receives a foreign-source law.
    For example, a lifted Horn queue key expands its rule, fact and finite-vector encoders.
    Builds on: concrete collection encoder and queue bodies and the fixed Horn execution. *)

(** A base encoding receipt records exactly one input-output event and its source trace. *)
Definition ide_receipt_leaf {K} (source : K -> positive -> list audit_external_frame -> Prop)
    input output (events : list (K * positive)) trace : Prop :=
  events = [(input,output)] /\ source input output trace.

(** The option encoder's result and events match the fixed encoder and component receipts. *)
Definition ide_option_expanded_source {D} (ED : encoding D)
    (source : D -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  (output,events) = audit_option_encode (ide_encoding_entry ED) input /\
  audit_option_encoding_receipts (ide_receipt_leaf source) events trace.

(** A vertex receipt expands its node and optional fact encoding calls. *)
Definition ide_vertex_expanded_source {N D} (EN : encoding N) (ED : encoding D)
    (node_source : N -> positive -> list audit_external_frame -> Prop)
    (fact_source : D -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  (output,events) = ide_vertex_source_encoding EN ED input /\
  audit_pair_encoding_receipts (ide_receipt_leaf node_source)
    (ide_option_expanded_source ED fact_source) events trace.

(** A vertex-pair receipt retains both vertex encodings in pair order. *)
Definition ide_vertex_pair_expanded_source {N D} (EN : encoding N) (ED : encoding D)
    (node_source : N -> positive -> list audit_external_frame -> Prop)
    (fact_source : D -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  let vertex := ide_vertex_source_encoding EN ED in
  (output,events) = audit_pair_encode vertex vertex input /\
  audit_pair_encoding_receipts (ide_vertex_expanded_source EN ED node_source fact_source)
    (ide_vertex_expanded_source EN ED node_source fact_source) events trace.

(** A fact receipt expands the selected sum branch into its vertex components. *)
Definition ide_fact_expanded_source {N D} (EN : encoding N) (ED : encoding D)
    (node_source : N -> positive -> list audit_external_frame -> Prop)
    (fact_source : D -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  (output,events) = ide_fact_source_encoding EN ED input /\
  audit_sum_encoding_receipts (ide_vertex_pair_expanded_source EN ED node_source fact_source)
    (ide_vertex_expanded_source EN ED node_source fact_source) events trace.

(** Only an encoding event carries a source receipt; other map events carry an empty trace. *)
Definition ide_recorded_map_source {K V}
    (source : K -> positive -> list audit_external_frame -> Prop)
    (event : exact_map_call K V) trace : Prop :=
  match event with
  | ExactEncode input output => source input output trace
  | _ => trace = []
  end.

Definition ide_recorded_map_budget {K V} (budget : K -> nat) (event : exact_map_call K V)
    : nat :=
  match event with
  | ExactEncode input _ => budget input
  | _ => 0
  end.

(** A pair-key receipt records both component encoding calls. *)
Definition ide_pair_key_expanded_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  (output,events) = audit_pair_encode (ide_encoding_entry EK) (ide_encoding_entry EK) input /\
  audit_pair_encoding_receipts (ide_receipt_leaf source) (ide_receipt_leaf source) events trace.

(** A triple-key receipt records the nested pair and final component encodings. *)
Definition ide_triple_key_expanded_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  let element := ide_encoding_entry EK in
  (output,events) = audit_pair_encode (audit_pair_encode element element) element input /\
  audit_pair_encoding_receipts (ide_pair_key_expanded_source EK source)
    (ide_receipt_leaf source) events trace.

(** A rule-tail receipt follows the pair or triple sum branch. *)
Definition ide_rule_tail_expanded_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop) input output events trace
    : Prop :=
  let element := ide_encoding_entry EK in
  (output,events) = audit_sum_encode (audit_pair_encode element element)
    (audit_pair_encode (audit_pair_encode element element) element) input /\
  audit_sum_encoding_receipts (ide_pair_key_expanded_source EK source)
    (ide_triple_key_expanded_source EK source) events trace.

(** A Horn rule receipt expands the encoded rule's sum and key components. *)
Definition ide_horn_rule_expanded_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop) rule output trace : Prop :=
  let run := ide_horn_rule_source_encoding EK rule in
  output = fst run /\
  audit_sum_encoding_receipts (ide_receipt_leaf source)
    (ide_rule_tail_expanded_source EK source) (snd run) trace.

(** Preparation map events retain their key encoding receipt; other events have empty traces. *)
Definition ide_horn_preparation_source {K}
    (source : K -> positive -> list audit_external_frame -> Prop) event trace : Prop :=
  match event with
  | AuditCall (IdeHornIndex call) => ide_recorded_map_source source call trace
  | AuditCall (IdeHornDistinct call) => ide_recorded_map_source source call trace
  | _ => trace = []
  end.

Definition ide_horn_preparation_budget {K} (budget : K -> nat)
    (event : audit_event (ide_horn_call K)) : nat :=
  match event with
  | AuditCall (IdeHornIndex call) => ide_recorded_map_budget budget call
  | AuditCall (IdeHornDistinct call) => ide_recorded_map_budget budget call
  | _ => 0
  end.

(** A queue key operation retains one matching rule-encoder entry and its expanded source. *)
Definition ide_horn_queue_actual_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop)
    (item : audit_queue_nested_event (IpHorn.rule K)
      (positive * list (fx_encoder_entry (IpHorn.rule K)))) trace : Prop :=
  let '(event,(_,bodies)) := item in
  match event with
  | QGet rule _ | QSet rule _ _ | QRemove rule _ | QEncode rule =>
    exists code,
      bodies = [(code,[FxEncodeEntry rule code])] /\
      ide_horn_rule_expanded_source EK source rule code trace
  | _ => trace = []
  end.

(** Horn map and queue calls retain key or nested queue receipts from their actual events. *)
Definition ide_horn_actual_source {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop)
    (event : audit_event (fx_declared_call K (IpHorn.rule K) bool)) trace : Prop :=
  match event with
  | AuditCall (FxGet key code _ _ _) | AuditCall (FxSet key code _ _ _ _) |
      AuditCall (FxReaders key code _ _ _) => source key code trace
  | AuditCall (FxPush _ _ _ _ nested) | AuditCall (FxPop _ _ nested) =>
    exists traces,
      Forall2 (ide_horn_queue_actual_source EK source) nested traces /\ trace = concat traces
  | _ => trace = []
  end.

Definition ide_horn_actual_body_budget {K} (EK : encoding K) (budget : K -> nat)
    (event : audit_event (fx_declared_call K (IpHorn.rule K) bool)) : nat :=
  match event with
  | AuditCall (FxGet key _ _ _ _) | AuditCall (FxSet key _ _ _ _ _) |
      AuditCall (FxReaders key _ _ _ _) => budget key
  | AuditCall (FxPush _ _ _ _ nested) | AuditCall (FxPop _ _ nested) =>
    audit_queue_recorded_encoder_budget (ide_horn_rule_encoding_body EK budget) nested
  | _ => 0
  end.

Section LegacyActualReceipts.

Context {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
  (old : ide_problem N P D A) (adapters : audit_ide_legacy_adapters EN EP ED EA old).

Let encoders := ide_legacy_graph_encoding adapters.

Let node_source := audit_external_same_call (ide_node_encoding_adapter encoders).

Let fact_source := audit_external_same_call (ide_fact_encoding_adapter encoders).

Let value_source := audit_external_same_call (ide_value_encoding_adapter adapters).

Let nb := external_input_budget (ide_node_encoding_adapter encoders).

Let pb := external_input_budget (ide_site_encoding_adapter encoders).

Let db := external_input_budget (ide_fact_encoding_adapter encoders).

Let ab := external_input_budget (ide_value_encoding_adapter adapters).

Let direct_key := IpTab.fact_encoding EN ED.

Let lifted_fact := IdeTab.lifted_encoding ED EA.

Let lifted_key := IpTab.fact_encoding EN lifted_fact.

Let direct_body := fun key => 64 * ide_fact_body EN ED nb db key.

Let lifted_body := fun key => 64 * ide_fact_body EN lifted_fact nb
  (ide_lifted_encoding_body ED EA db ab) key.

(** A legacy vertex encoding retains its component receipts. *)
Definition ide_legacy_actual_vertex_source input output trace : Prop :=
  ide_vertex_encoding_receipts EN EP ED EA old adapters input output
    (snd (ide_vertex_source_encoding EN ED input)) trace.

(** A legacy fact encoding retains its derived receipts. *)
Definition ide_legacy_actual_fact_source input output trace : Prop :=
  ide_fact_encoding_receipts EN EP ED EA old adapters input output
    (snd (ide_fact_source_encoding EN ED input)) trace.

(** A lifted encoding retains its fact and value receipts. *)
Definition ide_legacy_actual_lifted_source input output trace : Prop :=
  ide_lifted_encoding_receipts EN EP ED EA old adapters input output
    (snd (ide_lifted_source_encoding ED EA input)) trace.

(** A reachability fact expands both node and lifted encoders. *)
Definition ide_legacy_actual_reach_source input output trace : Prop :=
  ide_fact_expanded_source EN lifted_fact node_source ide_legacy_actual_lifted_source
    input output (snd (ide_fact_source_encoding EN lifted_fact input)) trace.

(** A vector encoding retains each value encoder receipt. *)
Definition ide_legacy_actual_vector_source input output trace : Prop :=
  ide_value_list_encoding_receipts EN EP ED EA old adapters input output
    (snd (audit_list_encode (ide_encoding_entry EA) input)) trace.

(** A legacy kind encoding records the applicable site call. *)
Definition ide_legacy_actual_kind_source input output trace : Prop :=
  output = encode (IpTab.kind_encoding EP) input /\
  match input with
  | IpInternal => trace = []
  | IpCall site | IpReturn site => audit_external_same_call
      (ide_site_encoding_adapter encoders) site (encode EP site) trace
  end.

(** Table encoding and join events retain their applicable external body receipts. *)
Definition ide_legacy_table_actual_source (event : ide_table_call A) trace : Prop :=
  match event with
  | IdeValueMap call => ide_recorded_map_source value_source call trace
  | IdeValueSet call => ide_recorded_map_source value_source call trace
  | IdeTableRegistry call => ide_recorded_map_source ide_legacy_actual_vector_source call trace
  | IdeTableJoin first second output =>
    audit_external_same_call (ide_lattice_join_adapter adapters) (first,second) output trace
  end.

Definition ide_legacy_table_body_budget (event : ide_table_call A) : nat :=
  match event with
  | IdeValueMap call => ide_recorded_map_budget ab call
  | IdeValueSet call => ide_recorded_map_budget ab call
  | IdeTableRegistry call => ide_recorded_map_budget (ide_list_encoding_body EA ab) call
  | IdeTableJoin first second _ =>
    external_input_budget (ide_lattice_join_adapter adapters) (first,second)
  end.

(** A legacy event carries the corresponding encoder or callback receipt when applicable. *)
Definition ide_legacy_actual_source (event : audit_event (ide_legacy_call N P D A)) trace
    : Prop :=
  match event with
  | AuditCall (IdeLegacyTables call) => ide_legacy_table_actual_source call trace
  | AuditCall (IdeLegacyLiftedSet call) =>
    ide_recorded_map_source ide_legacy_actual_lifted_source call trace
  | AuditCall (IdeLegacyJoinMap call) =>
    ide_recorded_map_source ide_legacy_actual_vertex_source call trace
  | AuditCall (IdeLegacyDirectMap call) =>
    ide_recorded_map_source ide_legacy_actual_fact_source call trace
  | AuditCall (IdeLegacyReachMap call) =>
    ide_recorded_map_source ide_legacy_actual_reach_source call trace
  | AuditCall (IdeLegacyWeight edge x y input output) =>
    audit_external_same_call (ide_legacy_weight_adapter adapters) (edge,(x,(y,input))) output trace
  | AuditCall (IdeLegacyJoin first second output) =>
    audit_external_same_call (ide_lattice_join_adapter adapters) (first,second) output trace
  | _ => trace = []
  end.

Definition ide_legacy_actual_body_budget (event : audit_event (ide_legacy_call N P D A))
    : nat :=
  match event with
  | AuditCall (IdeLegacyTables call) => ide_legacy_table_body_budget call
  | AuditCall (IdeLegacyLiftedSet call) =>
    ide_recorded_map_budget (fun key => 64 * ide_lifted_encoding_body ED EA db ab key) call
  | AuditCall (IdeLegacyJoinMap call) =>
    ide_recorded_map_budget (fun key => 64 * ide_vertex_encoding_body EN ED nb db key) call
  | AuditCall (IdeLegacyDirectMap call) => ide_recorded_map_budget direct_body call
  | AuditCall (IdeLegacyReachMap call) => ide_recorded_map_budget lifted_body call
  | AuditCall (IdeLegacyWeight edge x y input _) =>
    external_input_budget (ide_legacy_weight_adapter adapters) (edge,(x,(y,input)))
  | AuditCall (IdeLegacyJoin first second _) =>
    external_input_budget (ide_lattice_join_adapter adapters) (first,second)
  | _ => 0
  end.

Definition ide_legacy_same_run_events (run : ide_legacy_whole_run (N:=N) (P:=P) (D:=D) (A:=A)) :=
  exact_events (ide_legacy_graph_stage run) ++ exact_events (ide_legacy_seed_stage run) ++
  exact_events (ide_legacy_contribution_stage run) ++ exact_events (ide_legacy_collection_stage
    run).

(** Preparation and engine traces retain corresponding events and a bound on their total work. *)
Definition ide_horn_execution_body_receipts {K} (EK : encoding K)
    (source : K -> positive -> list audit_external_frame -> Prop) (budget : K -> nat)
    (run : ide_horn_execution (K:=K)) : Prop :=
  exists prepare_traces engine_traces,
    Forall2 (ide_horn_preparation_source source)
      (exact_events (ide_horn_preparation run)) prepare_traces /\
    Forall2 (ide_horn_actual_source EK source)
      (ide_horn_initial_events run ++ ide_horn_run_events run) engine_traces /\
    audit_source_body_work prepare_traces + audit_source_body_work engine_traces <=
      fold_right (fun event rest => ide_horn_preparation_budget budget event + rest) 0
        (exact_events (ide_horn_preparation run)) +
      fold_right (fun event rest => ide_horn_actual_body_budget EK budget event + rest) 0
        (ide_horn_initial_events run ++ ide_horn_run_events run).

(** The whole finite execution attaches source bodies to its actual encoder and callback calls. *)
Definition audit_ide_actual_legacy_source_statement : Prop :=
  audit_ide_legacy_adapter_laws adapters -> forall start seed initial,
  ide_laws old -> In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_legacy_whole_counted EN EP ED EA old nb pb db ab start seed initial in
  ide_horn_execution_body_receipts direct_key ide_legacy_actual_fact_source direct_body
    (ide_legacy_direct_engine run) /\
  ide_horn_execution_body_receipts lifted_key ide_legacy_actual_reach_source lifted_body
    (ide_legacy_lifted_engine run) /\
  (exists traces,
    Forall2 ide_legacy_actual_source (ide_legacy_same_run_events run) traces /\
    audit_source_body_work traces <=
      fold_right (fun event rest => ide_legacy_actual_body_budget event + rest) 0
        (ide_legacy_same_run_events run)) /\
  forall n d, exists traces,
    Forall2 ide_legacy_actual_source
      (exact_events (ide_legacy_whole_query EN ED old nb db run n d)) traces /\
    exact_units (ide_legacy_whole_query EN ED old nb db run n d) +
      audit_source_body_work traces <=
      64 * ide_legacy_query_input_budget EN ED nb db n d.

(** Horn input map events retain their kind-encoding source receipt. *)
Definition ide_legacy_input_actual_source {D0}
    (event : audit_event (ide_horn_input_call N P D0)) trace : Prop :=
  match event with
  | AuditCall (IdeHornActionMap call) =>
    ide_recorded_map_source ide_legacy_actual_kind_source call trace
  | _ => trace = []
  end.

Definition ide_legacy_kind_body_allowance kind :=
  match kind with
  | IpInternal => 0
  | IpCall site | IpReturn site => pb site
  end.

Definition ide_legacy_input_body_budget {D0}
    (event : audit_event (ide_horn_input_call N P D0)) : nat :=
  match event with
  | AuditCall (IdeHornActionMap call) =>
    ide_recorded_map_budget ide_legacy_kind_body_allowance call
  | _ => 0
  end.

Definition ide_legacy_total_body_allowance
    (run : ide_legacy_whole_run (N:=N) (P:=P) (D:=D) (A:=A)) : nat :=
  let direct := ide_legacy_direct_engine run in
  let lifted := ide_legacy_lifted_engine run in
  fold_right (fun event rest => ide_legacy_input_body_budget event + rest) 0
    (exact_events (ide_legacy_direct_rules run)) +
  fold_right (fun event rest => ide_legacy_input_body_budget event + rest) 0
    (exact_events (ide_legacy_lifted_rules run)) +
  fold_right (fun event rest => ide_horn_preparation_budget direct_body event + rest) 0
    (exact_events (ide_horn_preparation direct)) +
  fold_right (fun event rest => ide_horn_actual_body_budget direct_key direct_body event + rest) 0
    (ide_horn_initial_events direct ++ ide_horn_run_events direct) +
  fold_right (fun event rest => ide_horn_preparation_budget lifted_body event + rest) 0
    (exact_events (ide_horn_preparation lifted)) +
  fold_right (fun event rest => ide_horn_actual_body_budget lifted_key lifted_body event + rest) 0
    (ide_horn_initial_events lifted ++ ide_horn_run_events lifted) +
  fold_right (fun event rest => ide_legacy_actual_body_budget event + rest) 0
    (ide_legacy_same_run_events run).

(** Whole finite source work sums caller and foreign body costs from this one execution. *)
Definition audit_ide_actual_legacy_whole_bound_statement : Prop :=
  audit_ide_legacy_adapter_laws adapters -> forall start seed initial,
  ide_laws old -> In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_legacy_whole_counted EN EP ED EA old nb pb db ab start seed initial in
  let direct := ide_legacy_direct_engine run in
  let lifted := ide_legacy_lifted_engine run in
  exists direct_input lifted_input direct_prepare lifted_prepare direct_engine lifted_engine stages,
    Forall2 ide_legacy_input_actual_source
      (exact_events (ide_legacy_direct_rules run)) direct_input /\
    Forall2 ide_legacy_input_actual_source
      (exact_events (ide_legacy_lifted_rules run)) lifted_input /\
    Forall2 (ide_horn_preparation_source ide_legacy_actual_fact_source)
      (exact_events (ide_horn_preparation direct)) direct_prepare /\
    Forall2 (ide_horn_preparation_source ide_legacy_actual_reach_source)
      (exact_events (ide_horn_preparation lifted)) lifted_prepare /\
    Forall2 (ide_horn_actual_source direct_key ide_legacy_actual_fact_source)
      (ide_horn_initial_events direct ++ ide_horn_run_events direct) direct_engine /\
    Forall2 (ide_horn_actual_source lifted_key ide_legacy_actual_reach_source)
      (ide_horn_initial_events lifted ++ ide_horn_run_events lifted) lifted_engine /\
    Forall2 ide_legacy_actual_source (ide_legacy_same_run_events run) stages /\
    ide_legacy_whole_work EN ED EA nb db ab run +
      audit_source_body_work direct_input + audit_source_body_work lifted_input +
      audit_source_body_work direct_prepare + audit_source_body_work lifted_prepare +
      audit_source_body_work direct_engine + audit_source_body_work lifted_engine +
      audit_source_body_work stages <=
        64 * ide_legacy_whole_input_budget EN EP ED EA old nb pb db ab start seed initial +
        ide_legacy_total_body_allowance run.

End LegacyActualReceipts.

(** All generated callback bodies and their direct query belong to the fixed producer. *)
Definition audit_ide_generated_body_family_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (encoders : audit_ide_graph_encoding_adapters EN EP ED)
    (registry : audit_ide_registry_adapters r) (weighted : audit_ide_weight_adapter weight),
    audit_ide_generated_with_bodies_statement EN EP ED L r q weight encoders registry weighted /\
    audit_ide_generated_query_with_bodies_statement EN EP ED r weight encoders registry weighted.

(** The finite fallback's genuine callbacks have separate actual source and budget receipts. *)
Definition audit_ide_legacy_body_family_statement : Prop :=
  forall N P D A (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
    (old : ide_problem N P D A) (legacy : audit_ide_legacy_adapters EN EP ED EA old),
    audit_ide_legacy_with_bodies_statement EN EP ED EA old legacy /\
    audit_ide_encoding_body_receipts_statement EN EP ED EA old legacy /\
    audit_ide_actual_legacy_source_statement EN EP ED EA old legacy /\
    audit_ide_actual_legacy_whole_bound_statement EN EP ED EA old legacy.

(** Selection pays the strict compatibility callbacks and the branch it actually constructs. *)
Definition audit_ide_selector_body_family_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
    (old : ide_problem N P D A) (r : ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (registry : audit_ide_registry_adapters r) (weighted : audit_ide_weight_adapter weight)
    (legacy : audit_ide_legacy_adapters EN EP ED EA old),
    audit_ide_select_with_bodies_statement EN EP ED EA old r weight registry weighted legacy /\
    audit_ide_actual_generated_source_statement EN EP ED EA old r weight legacy registry weighted.

(** The full source claim combines concrete caller, callback-body and encoding closure. *)
Definition audit_ide_full_source_statement : Prop :=
  audit_ide_caller_source_statement /\ audit_ide_generated_body_family_statement /\
  audit_ide_legacy_body_family_statement /\ audit_ide_selector_body_family_statement.
