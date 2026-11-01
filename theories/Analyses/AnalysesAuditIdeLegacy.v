(** * Exact finite IDE fallback source

    Models finite table construction and the fallback Horn execution.
    For example, two Boolean positions produce four Boolean vectors.
    Builds on: AnalysesAuditIdeBase, AnalysesAuditSource and FixpointAuditWorklist. *)

From Stdlib Require Import Decimal Arith Bool List PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditIdeBase AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditQueue
  CollectionsAuditTrie CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsHeap
  CollectionsMap CollectionsTrie.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointIndex FixpointSystem FixpointTotal
  FixpointWorklist.
From Galois.Order Require Import OrderBasic OrderLattice.
Import List.ListNotations.

(* Definition source: IdeLegacyTables.v *)
(** * Complete finite table and vector source equations

    These fixed mirrors retain repeated vector generation inside the range callback.
    For example, the source recomputes the tail vectors once for each range occurrence.
    Builds on: AnalysesInterprocedural and ExactSource. *)

Inductive ide_table_call (A : Type) : Type :=
  | IdeValueMap (call : exact_map_call A A)
  | IdeValueSet (call : exact_map_call A unit)
  | IdeTableRegistry (call : exact_map_call (list A) (Map.t A A))
  | IdeTableJoin (first second output : A).

Arguments IdeValueMap {A}.

Arguments IdeValueSet {A}.

Arguments IdeTableRegistry {A}.

Arguments IdeTableJoin {A}.

(** Literal emit_list/emit_code/stream_positive input recurrence; component encoder work is
    a genuine external adapter. The derived list encoder bridge is library-owned. *)
Fixpoint ide_list_encoding_body {A} (EA : encoding A) (body : A -> nat) (xs : list A) : nat :=
  match xs with
  | [] => 3
  | a :: rest => 8 + body a + 16 * Pos.size_nat (encode EA a) +
      ide_list_encoding_body EA body rest
  end.

Section Tables.

Context {A : Type} (EA : encoding A) (L : lattice A) (body : A -> nat).

Fixpoint ide_vectors_counted (positions range : list A)
    : exact_counted (ide_table_call A) (list (list A)) :=
  match positions with
  | [] => exact_case 100 (exact_return 100 [[]])
  | _ :: rest => exact_case 101
      (exact_flat_map 102 (fun a =>
        exact_bind 103 (ide_vectors_counted rest range) (fun tails =>
          exact_map 104 (fun tail => exact_return 104 (a :: tail)) tails)) range)
  end.

Fixpoint ide_table_build_counted (inputs outputs : list A)
    : exact_counted (ide_table_call A) (Map.t A A) :=
  match inputs with
  | [] => exact_case 110 (exact_return 110 Map.empty)
  | input :: rest => exact_case 111
      (match outputs with
      | [] => exact_case 112 (exact_return 112 Map.empty)
      | output :: later => exact_case 113
          (exact_bind 114 (ide_table_build_counted rest later) (fun table =>
            exact_set IdeValueMap EA body input output table))
      end)
  end.

Definition ide_table_apply_counted (table : Map.t A A) (a : A)
    : exact_counted (ide_table_call A) A :=
  exact_bind 120 (exact_get IdeValueMap EA body a table) (fun found =>
    exact_case 121 (exact_return 121 (match found with
    | Some value => value
    | None => bot L
    end))).

Definition ide_table_eval_counted (domain outputs : list A) (a : A)
    : exact_counted (ide_table_call A) A :=
  exact_bind 122 (ide_table_build_counted domain outputs) (fun table => ide_table_apply_counted
    table a).

Definition ide_registry_counted (domain : list A)
    : exact_counted (ide_table_call A) (Map.t (list A) (Map.t A A)) :=
  exact_bind 130 (ide_vectors_counted domain domain) (fun functions =>
    exact_fold_right 131 (fun outputs index =>
      exact_bind 132 (ide_table_build_counted domain outputs) (fun table =>
        exact_set IdeTableRegistry (list_encoding EA) (ide_list_encoding_body EA body)
          outputs table index)) Map.empty functions).

Definition ide_indexed_eval_counted (index : Map.t (list A) (Map.t A A))
    (outputs : list A) (a : A) : exact_counted (ide_table_call A) A :=
  exact_bind 140 (exact_get IdeTableRegistry (list_encoding EA)
    (ide_list_encoding_body EA body) outputs index) (fun found =>
      match found with
      | None => exact_case 141 (exact_return 141 (bot L))
      | Some table => exact_case 142 (ide_table_apply_counted table a)
      end).

Definition ide_finite_domain_counted (values : list A)
    : exact_counted (ide_table_call A) (list A) :=
  exact_bind 150 (exact_set_of_list IdeValueSet EA body values)
    (fun set => exact_set_elements IdeValueSet set).

Definition ide_table_max_operand (values : list A) : nat :=
  fold_right (fun a rest => Nat.max (body a + Pos.size_nat (encode EA a)) rest) 0 values.

(** Independent finite input bounds; these do not inspect counted outputs or their traces. *)
Definition ide_vectors_input_budget (positions range : list A) : nat :=
  4096 * Nat.pow (S (length range)) (length positions + 2) * Nat.pow (S (length positions)) 2.

Definition ide_table_build_input_budget (inputs outputs : list A) : nat :=
  4096 * S (length inputs) * Nat.pow (S (ide_table_max_operand inputs)) 2.

Definition ide_registry_input_budget (domain : list A) : nat :=
  let d := length domain in
  let functions := Nat.pow d d in
  ide_vectors_input_budget domain domain +
    (Nat.of_num_uint 32768%uint) * Nat.pow (S functions) 2 * Nat.pow (S d) 2 *
      Nat.pow (S (ide_table_max_operand domain))
      2.

Definition ide_finite_domain_input_budget (values : list A) : nat :=
  (Nat.of_num_uint 8192%uint) * Nat.pow (S (length values)) 2 *
    Nat.pow (S (ide_table_max_operand values)) 2.

(** Counted vectors match the finite table vectors within input budget. *)
Definition ide_vectors_counted_correct_statement : Prop := forall positions range,
  let run := ide_vectors_counted positions range in
  exact_value run = IdeTable.vectors positions range /\
  exact_units run <= ide_vectors_input_budget positions range.

(** Counted table construction matches the finite table within input budget. *)
Definition ide_table_build_counted_correct_statement : Prop := forall inputs outputs,
  let run := ide_table_build_counted inputs outputs in
  exact_value run = IdeTable.build EA inputs outputs /\
  exact_units run <= ide_table_build_input_budget inputs outputs.

(** Counted registry construction matches the finite registry within input budget. *)
Definition ide_registry_counted_correct_statement : Prop := forall domain,
  let run := ide_registry_counted domain in
  exact_value run = IdeTable.registry EA domain /\
  exact_units run <= ide_registry_input_budget domain.

(** Counted lookup returns the finite indexed evaluation. *)
Definition ide_indexed_eval_counted_correct_statement : Prop := forall index outputs a,
  exact_value (ide_indexed_eval_counted index outputs a) = IdeTable.indexed_eval EA L index outputs
    a.

(** Counted domain construction returns the canonical finite set elements within budget. *)
Definition ide_finite_domain_counted_correct_statement : Prop := forall values,
  let run := ide_finite_domain_counted values in
  exact_value run = FinSet.elements (FinSet.of_list EA values) /\
  exact_units run <= ide_finite_domain_input_budget values.

End Tables.

(** Finite input examples check real model computations, not universal erasure or source laws. *)

(* Definition source: IdeHornInput.v *)
(** * Literal Horn input generation for the old IDE backend

    This model deliberately rebuilds action indexes at each original action_rows occurrence.
    For example, matching two calls performs two distinct return-bucket preparations.
    Builds on: AnalysesInterprocedural and ExactSource. *)

Inductive ide_horn_input_call (N P D : Type) : Type :=
  | IdeHornActionMap (call : exact_map_call (ip_kind P)
      (list ((N * option D) * (N * option D)))).

Arguments IdeHornActionMap {N P D}.

Section HornInput.

Context {N P D : Type} (EP : encoding P) (q : ip_problem N P D) (site_body : P -> nat).

Definition ide_horn_kind_body (kind : ip_kind P) : nat :=
  match kind with
  | IpInternal => 8
  | IpCall p | IpReturn p => 8 + site_body p
  end.

Definition ide_horn_vertices_counted : exact_counted (ide_horn_input_call N P D)
    (list (N * option D)) :=
  exact_flat_map 300 (fun n =>
    exact_bind 301 (exact_map 302 (fun d => exact_return 302 (Some d)) (ip_facts q))
      (fun ds => exact_map 303 (fun d => exact_return 303 (n,d)) (None :: ds))) (ip_nodes q).

Definition ide_horn_arcs_counted : exact_counted (ide_horn_input_call N P D)
    (list (ip_kind P * ((N * option D) * (N * option D)))) :=
  exact_flat_map 310 (fun e => exact_map 311 (fun xy => exact_return 311
    (ip_action e, ((ip_source e, fst xy), (ip_target e, snd xy)))) (ip_pairs e)) (ip_edges q).

Definition ide_horn_actions_counted : exact_counted (ide_horn_input_call N P D)
    (Map.t (ip_kind P) (list ((N * option D) * (N * option D)))) :=
  exact_bind 320 ide_horn_arcs_counted (fun rows =>
    exact_fold_right 321 (fun kv table =>
      exact_bind 322 (exact_get IdeHornActionMap (IpTab.kind_encoding EP)
        ide_horn_kind_body (fst kv) table) (fun found =>
      exact_bind 323 (exact_case 323 (exact_return 323
        (match found with
        | Some xs => xs
        | None => []
        end))) (fun row =>
      exact_bind 324 (exact_return 324 (snd kv :: row)) (fun added =>
        exact_set IdeHornActionMap (IpTab.kind_encoding EP) ide_horn_kind_body
          (fst kv) added table)))) Map.empty rows).

Definition ide_horn_action_rows_counted (kind : ip_kind P)
    : exact_counted (ide_horn_input_call N P D) (list ((N * option D) * (N * option D))) :=
  exact_bind 330 ide_horn_actions_counted (fun table =>
  exact_bind 331 (exact_get IdeHornActionMap (IpTab.kind_encoding EP) ide_horn_kind_body kind table)
    (fun found => exact_case 332 (exact_return 332
      (match found with
      | Some rows => rows
      | None => []
      end)))).

Definition ide_horn_calls_counted : exact_counted (ide_horn_input_call N P D)
    (list (P * ((N * option D) * (N * option D)))) :=
  exact_flat_map 340 (fun site => exact_bind 341 (ide_horn_action_rows_counted (IpCall site))
    (fun rows => exact_map 342 (fun uv => exact_return 342 (site,uv)) rows)) (ip_sites q).

Definition ide_horn_matches_counted : exact_counted (ide_horn_input_call N P D)
    (list ((N * option D) * ((N * option D) * ((N * option D) * (N * option D))))) :=
  exact_bind 350 ide_horn_calls_counted (fun calls =>
    exact_flat_map 351 (fun call => let '(site,(u,entry)) := call in
      exact_bind 352 (ide_horn_action_rows_counted (IpReturn site)) (fun returns =>
        exact_map 353 (fun ret => exact_return 353 (u,(entry,ret))) returns)) calls).

Definition ide_horn_rules_counted (root : N * option D)
    : exact_counted (ide_horn_input_call N P D) (list (IpHorn.rule (IpTab.fact N D))) :=
  exact_bind 360 (exact_return 360 (IpHorn.Seed (inr root))) (fun seed =>
  exact_bind 361 ide_horn_vertices_counted (fun vs =>
  exact_bind 362 (exact_map 363 (fun u => exact_return 363 (IpHorn.Seed (inl (u,u)))) vs)
    (fun identities =>
  exact_bind 364 (ide_horn_action_rows_counted IpInternal) (fun internal =>
  exact_bind 365 (exact_flat_map 366 (fun uv =>
    exact_bind 367 ide_horn_vertices_counted (fun vertices =>
      exact_map 368 (fun a => exact_return 368
        (IpHorn.Unary (inl (a,fst uv)) (inl (a,snd uv)))) vertices)) internal) (fun unary =>
  exact_bind 369 ide_horn_matches_counted (fun matches =>
  exact_bind 370 (exact_flat_map 371 (fun matched =>
    let '(u,(entry,(exit,v))) := matched in
    exact_bind 372 ide_horn_vertices_counted (fun vertices =>
      exact_map 373 (fun a => exact_return 373
        (IpHorn.Binary (inl (a,u)) (inl (entry,exit)) (inl (a,v)))) vertices)) matches) (fun binary
          =>
  exact_bind 374 ide_horn_vertices_counted (fun outer =>
  exact_bind 375 (exact_flat_map 376 (fun u => exact_bind 377 ide_horn_vertices_counted
    (fun vertices => exact_map 378 (fun v => exact_return 378
      (IpHorn.Binary (inr u) (inl (u,v)) (inr v))) vertices)) outer) (fun prefixes =>
  exact_bind 379 ide_horn_calls_counted (fun calls =>
  exact_bind 380 (exact_map 381 (fun call => let '(_,(u,v)) := call in
    exact_return 381 (IpHorn.Unary (inr u) (inr v))) calls) (fun call_rules =>
  exact_bind 382 (exact_append 382 prefixes call_rules) (fun tail1 =>
  exact_bind 383 (exact_append 383 binary tail1) (fun tail2 =>
  exact_bind 384 (exact_append 384 unary tail2) (fun tail3 =>
  exact_bind 385 (exact_append 385 identities tail3) (fun tail4 =>
    exact_return 386 (seed :: tail4)))))))))))))))).

Definition ide_horn_input_geometry : nat :=
  1 + length (ip_nodes q) + length (ip_facts q) + length (ip_sites q) + length (ip_edges q) +
    fold_right (fun edge rest => length (ip_pairs edge) + rest) 0 (ip_edges q).

Definition ide_horn_site_operand : nat :=
  fold_right Nat.max 0
    (map (fun p => site_body p + Pos.size_nat (encode EP p)) (ip_sites q) ++
      map (fun edge => match ip_action edge with
        | IpInternal => 0
        | IpCall p | IpReturn p => site_body p + Pos.size_nat (encode EP p)
        end) (ip_edges q)).

(** This intentionally conservative polynomial is input-only and pays repeated source indexes. *)
Definition ide_horn_input_budget : nat :=
  (Nat.of_num_uint 65536%uint) * Nat.pow ide_horn_input_geometry 12 * S ide_horn_site_operand.

(** Counted Horn input generation returns the original rules within budget. *)
Definition ide_horn_rules_counted_correct_statement : Prop := forall root,
  let run := ide_horn_rules_counted root in
  exact_value run = IpTab.rules q EP root /\ exact_units run <= ide_horn_input_budget.

End HornInput.

(* Definition source: IdeLegacyLift.v *)
(** * Literal lifted finite IDE input and contribution models

    Each function-key occurrence recomputes the original finite registry input as the
    original source does. Weight callbacks retain the actual edge, facts and value.
    Builds on: IdeLegacyTables. *)

Inductive ide_legacy_call (N P D A : Type) : Type :=
  | IdeLegacyTables (call : ide_table_call A)
  | IdeLegacyLiftedSet (call : exact_map_call (option D * list A) unit)
  | IdeLegacyJoinMap (call : exact_map_call (N * option D) A)
  | IdeLegacyDirectMap (call : exact_map_call (IpTab.fact N D) bool)
  | IdeLegacyReachMap (call : exact_map_call (IpTab.fact N (option D * list A)) bool)
  | IdeLegacyWeight (edge : ip_edge N P D) (source target : option D) (input output : A)
  | IdeLegacyReach (n : N) (fact : option (option D * list A)) (result : bool)
  | IdeLegacyJoin (first second output : A).

Arguments IdeLegacyTables {N P D A}.

Arguments IdeLegacyLiftedSet {N P D A}.

Arguments IdeLegacyJoinMap {N P D A}.

Arguments IdeLegacyDirectMap {N P D A}.

Arguments IdeLegacyReachMap {N P D A}.

Arguments IdeLegacyWeight {N P D A}.

Arguments IdeLegacyReach {N P D A}.

Arguments IdeLegacyJoin {N P D A}.

Section LegacyLift.

Context {N P D A : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A).

Context (node_body : N -> nat) (site_body : P -> nat) (fact_body : D -> nat)
  (value_body : A -> nat).

Definition ide_legacy_domain : exact_counted (ide_legacy_call N P D A) (list A) :=
  exact_lift IdeLegacyTables (ide_finite_domain_counted EA value_body (ide_values old)).

Definition ide_legacy_function_keys : exact_counted (ide_legacy_call N P D A) (list (list A)) :=
  exact_bind 200 ide_legacy_domain (fun domain =>
    exact_lift IdeLegacyTables (ide_vectors_counted domain domain)).

Definition ide_lifted_encoding_body (key : option D * list A) : nat :=
  let first := match fst key with
    | None => 3
    | Some d => 4 + fact_body d
    end in
  64 + first + ide_list_encoding_body EA value_body (snd key) +
    32 * Pos.size_nat (encode (IdeTab.lifted_encoding ED EA) key).

Definition ide_legacy_lifted_facts : exact_counted (ide_legacy_call N P D A)
    (list (option D * list A)) :=
  exact_bind 201 (exact_map 202 (fun d => exact_return 202 (Some d))
    (ip_facts (ide_graph old))) (fun facts =>
  exact_bind 203 (exact_return 203 (None :: facts)) (fun options =>
  exact_bind 204 ide_legacy_function_keys (fun functions =>
  exact_bind 205 (exact_flat_map 206 (fun d =>
    exact_map 207 (fun f => exact_return 207 (d, f)) functions) options) (fun pairs =>
  exact_bind 208 (exact_set_of_list IdeLegacyLiftedSet (IdeTab.lifted_encoding ED EA)
    ide_lifted_encoding_body pairs) (fun set => exact_set_elements IdeLegacyLiftedSet set))))).

Definition ide_legacy_weight (edge : ip_edge N P D) (source target : option D) (a : A)
    : exact_counted (ide_legacy_call N P D A) A :=
  let output := ide_weight old edge source target a in
  exact_call (IdeLegacyWeight edge source target a output) 0 output.

Definition ide_legacy_lifted_edge (edge : ip_edge N P D)
    : exact_counted (ide_legacy_call N P D A) (ip_edge N P (option D * list A)) :=
  exact_bind 210 (exact_flat_map 211 (fun xy =>
    exact_bind 212 ide_legacy_function_keys (fun functions =>
      exact_map 213 (fun f =>
        exact_bind 214 (exact_map 215 (ide_legacy_weight edge (fst xy) (snd xy)) f)
          (fun transformed => exact_return 216
            (Some (fst xy, f), Some (snd xy, transformed)))) functions)) (ip_pairs edge))
    (fun pairs => exact_return 217
      (IpEdge (ip_source edge) (ip_target edge) (ip_action edge) ((None, None) :: pairs))).

Definition ide_legacy_lifted_graph : exact_counted (ide_legacy_call N P D A)
    (ip_problem N P (option D * list A)) :=
  exact_bind 220 ide_legacy_lifted_facts (fun facts =>
  exact_bind 221 (exact_map 222 ide_legacy_lifted_edge (ip_edges (ide_graph old))) (fun edges =>
    exact_return 223 (IpProblem (ip_nodes (ide_graph old)) (ip_sites (ide_graph old)) facts
      edges))).

Definition ide_legacy_value_index : exact_counted (ide_legacy_call N P D A)
    (Map.t (list A) (Map.t A A)) :=
  exact_bind 230 ide_legacy_domain (fun domain =>
    exact_lift IdeLegacyTables (ide_registry_counted EA value_body domain)).

Definition ide_legacy_vertices : exact_counted (ide_legacy_call N P D A)
    (list (N * option D)) :=
  exact_flat_map 240 (fun n =>
    exact_bind 241 (exact_map 242 (fun d => exact_return 242 (Some d))
      (ip_facts (ide_graph old))) (fun facts =>
      exact_map 243 (fun d => exact_return 243 (n, d)) (None :: facts)))
    (ip_nodes (ide_graph old)).

(** The actual reachability child is supplied by the fixed Horn counted engine. Its source
    instance is internal and must be proved from that concrete engine, not from a whole-bound
    law. *)
Definition ide_legacy_contributions
    (reachable : N -> option (option D * list A) -> exact_counted (ide_legacy_call N P D A) bool)
    (initial : A) : exact_counted (ide_legacy_call N P D A) (list ((N * option D) * A)) :=
  exact_bind 250 ide_legacy_value_index (fun tables =>
  exact_bind 251 ide_legacy_vertices (fun vertices =>
  exact_bind 252 ide_legacy_function_keys (fun functions =>
  exact_bind 253 (exact_flat_map 254 (fun vertex =>
    exact_map 255 (fun f => exact_return 255 (vertex, f)) functions) vertices) (fun queries =>
    exact_flat_map 256 (fun query =>
      let '((n,d), f) := query in
      exact_bind 257 (reachable n (Some (d,f))) (fun present =>
        if present then exact_case 258
          (exact_bind 259 (exact_lift IdeLegacyTables
            (ide_indexed_eval_counted EA (ide_lattice old) value_body tables f initial))
            (fun value => exact_return 260 [((n,d),value)]))
        else exact_case 261 (exact_return 261 []))) queries)))).

Definition ide_vertex_encoding_body (key : N * option D) : nat :=
  64 + node_body (fst key) +
    (match snd key with
    | None => 3
    | Some d => 4 + fact_body d
    end) +
    32 * Pos.size_nat (encode (IpTab.vertex_encoding EN ED) key).

Definition ide_legacy_join_put (key : N * option D) (value : A)
    (table : Map.t (N * option D) A) : exact_counted (ide_legacy_call N P D A)
      (Map.t (N * option D) A) :=
  exact_bind 270 (exact_get IdeLegacyJoinMap (IpTab.vertex_encoding EN ED)
    ide_vertex_encoding_body key table) (fun found =>
  exact_bind 271 (exact_case 271 (exact_return 271
    (match found with
    | Some prior => prior
    | None => bot (ide_lattice old)
    end))) (fun prior =>
  let output := join (ide_lattice old) value prior in
  exact_bind 272 (exact_call (IdeLegacyJoin value prior output) 0 output) (fun joined =>
    exact_set IdeLegacyJoinMap (IpTab.vertex_encoding EN ED) ide_vertex_encoding_body key joined
      table))).

Definition ide_legacy_collect (contributions : list ((N * option D) * A))
    : exact_counted (ide_legacy_call N P D A) (Map.t (N * option D) A) :=
  exact_fold_right 280 (fun item table => ide_legacy_join_put (fst item) (snd item) table)
    Map.empty contributions.

(** The counted lifted graph equals the original lifted graph. *)
Definition ide_legacy_lifted_graph_correct_statement : Prop :=
  exact_value ide_legacy_lifted_graph = IdeTab.graph ED EA old.

(** The counted value index equals the original finite index. *)
Definition ide_legacy_value_index_correct_statement : Prop :=
  exact_value ide_legacy_value_index = IdeTab.value_index EA old.

(** Counted contribution collection equals the original join collection. *)
Definition ide_legacy_collect_correct_statement : Prop := forall items,
  exact_value (ide_legacy_collect items) = IpJoin.collect (IpTab.vertex_encoding EN ED) (ide_lattice
    old) items.

End LegacyLift.

(* Definition source: IdeHornEngine.v *)
(** * Bounded instrumentation of the actual total Boolean Horn engine

    A fixed credit stops only the observer, not the represented source engine. The future
    completion theorem proves that the actual empty pop occurs before credit exhaustion.
    Builds on: FixpointDeclaredModel and ExactSource. *)

Inductive ide_horn_call (K : Type) : Type :=
  | IdeHornIndex (call : exact_map_call K (list (IpHorn.rule K)))
  | IdeHornDistinct (call : exact_map_call K unit)
  | IdeHornTarget (rule : IpHorn.rule K) (result : K)
  | IdeHornReads (rule : IpHorn.rule K) (result : list K).

Arguments IdeHornIndex {K}.

Arguments IdeHornDistinct {K}.

Arguments IdeHornTarget {K}.

Arguments IdeHornReads {K}.

Section HornEngine.

Context {K : Type} (EK : encoding K) (body : K -> nat) (rules : list (IpHorn.rule K)).

Let EC := IpHorn.rule_encoding EK.

Let system := IpHorn.system rules.

Definition ide_horn_distinct (xs : list K) : exact_counted (ide_horn_call K) (list K) :=
  exact_bind 400 (exact_set_of_list IdeHornDistinct EK body xs)
    (fun set => exact_set_elements IdeHornDistinct set).

Definition ide_horn_index_push (c : IpHorn.rule K) (x : K)
    (table : Map.t K (list (IpHorn.rule K)))
    : exact_counted (ide_horn_call K) (Map.t K (list (IpHorn.rule K))) :=
  exact_bind 401 (exact_get IdeHornIndex EK body x table) (fun found =>
  exact_bind 402 (exact_case 402 (exact_return 402
    (match found with
    | Some cs => cs
    | None => []
    end))) (fun cs =>
  exact_bind 403 (exact_return 403 (c :: cs)) (fun added => exact_set IdeHornIndex EK body x added
    table))).

Definition ide_horn_index_counted : exact_counted (ide_horn_call K) (sys_index K (IpHorn.rule K)) :=
  exact_fold_right 410 (fun c ix =>
    let target := IpHorn.target c in
    exact_bind 411 (exact_call (IdeHornTarget c target) 0 target) (fun target =>
    exact_bind 412 (ide_horn_distinct [target]) (fun outputs =>
    exact_bind 413 (exact_fold_right 414 (ide_horn_index_push c) (contributors ix) outputs) (fun
      writers =>
    let deps := IpHorn.reads c in
    exact_bind 415 (exact_call (IdeHornReads c deps) 0 deps) (fun deps =>
    exact_bind 416 (ide_horn_distinct deps) (fun inputs =>
    exact_bind 417 (exact_fold_right 418 (ide_horn_index_push c) (readers ix) inputs) (fun users =>
      exact_return 419 (SysIndex writers users)))))))) (SysIndex Map.empty Map.empty) rules.

Definition ide_horn_rule_keys (rule : IpHorn.rule K) : list K :=
  IpHorn.target rule :: IpHorn.reads rule.

Definition ide_horn_key_max : nat :=
  fold_right Nat.max 0 (map (fun k => body k + Pos.size_nat (encode EK k))
    (flat_map ide_horn_rule_keys rules)).

(** One initial enqueue per occurrence and at most one Boolean increase per target key. *)
Definition ide_horn_credit : nat := S (length rules + length rules * length rules).

Definition ide_horn_queue_size (q : PQueue.t (IpHorn.rule K)) : nat :=
  length (PQueue.pending q) + length (PQueue.entries (PQueue.pending q)) + PQueue.pending_count q.

Definition ide_horn_queue_budget (q : PQueue.t (IpHorn.rule K)) : nat :=
  4096 * Nat.pow (S (ide_horn_queue_size q)) 3 * Nat.pow (S ide_horn_key_max) 2.

Definition ide_horn_rule_encoding_body (rule : IpHorn.rule K) : nat :=
  256 + 64 * Pos.size_nat (encode EC rule) +
    fold_right (fun key rest => body key + 64 * Pos.size_nat (encode EK key) + rest)
      0 (ide_horn_rule_keys rule).

(** Fixed local source-block allowances expand every actual queue event. QChildren retains
    its actual tree, so reversal and mapping iterations are charged by the actual child list. *)
Definition ide_horn_queue_source_event (event : queue_event (IpHorn.rule K)) : nat :=
  64 + match event with
  | QGet c _ => ide_horn_rule_encoding_body c + 32 * Pos.size_nat (encode EC c)
  | QSet c _ _ | QRemove c _ =>
      ide_horn_rule_encoding_body c + 64 * Pos.size_nat (encode EC c)
  | QEncode c => ide_horn_rule_encoding_body c
  | QEntryCompare first second =>
      8 * (audit_binary_weight (Z.pos (fst (fst first))) (Z.pos (fst (fst second))) +
        audit_binary_weight (Z.pos (snd (fst first))) (Z.pos (snd (fst second))))
  | QPriorityLt a b | QPriorityEq a b => 8 * audit_binary_weight (Z.pos a) (Z.pos b)
  | QChildren tree => match tree with
    | PQueue.Tree _ children => 64 * (2 + 2 * length children)
    end
  | _ => 0
  end.

Definition ide_horn_queue_source_work (events : list (queue_event (IpHorn.rule K))) : nat :=
  fold_right (fun event rest => ide_horn_queue_source_event event + rest) 0 events.

Definition ide_horn_nested_queue_source_work
    (events : list (audit_queue_nested_event (IpHorn.rule K)
      (positive * list (fx_encoder_entry (IpHorn.rule K))))) : nat :=
  audit_queue_recorded_full_source_work
    (fun event => match event with
      | FxEncodeEntry rule _ => ide_horn_rule_encoding_body rule
      end)
      events.

(** Internal Horn callbacks have bounded literal bodies: target/reads case, at most two Ask
    constructors/continuations, Boolean lattice cases and constant priority one. They are not
    priced by an arbitrary external callback law. Queue and primitive bridges are library-owned. *)
Definition ide_horn_call_work (call : fx_declared_call K (IpHorn.rule K) bool) : nat :=
  match call with
  | FxGet x code _ _ _ | FxReaders x code _ _ _ => 256 + body x + 32 * Pos.size_nat code
  | FxSet x code _ _ _ _ => 256 + body x + 64 * Pos.size_nat code
  | FxPush _ _ _ _ events | FxPop _ _ events => 64 + ide_horn_nested_queue_source_work events
  | _ => 64
  end.

Definition ide_horn_source_work (events : audit_trace (fx_declared_call K (IpHorn.rule K) bool)) :
  nat :=
  fold_right (fun event rest => match event with
    | AuditCall call => ide_horn_call_work call + rest
    | _ => 64 + rest
    end) 0 events.

Fixpoint ide_horn_loop_counted (ix : sys_index K (IpHorn.rule K)) (credit : nat)
    (state : Engine.t K (IpHorn.rule K) bool)
    : option (assignment K bool) * audit_trace (fx_declared_call K (IpHorn.rule K) bool) :=
  match credit with
  | 0 => (None, [])
  | S remaining =>
      let '(outcome, here) := fx_model_step EK EC bool_lattice IpHorn.schedule Joining system ix
        state in
      match outcome with
      | Done values => (Some values, here)
      | Pending next =>
          let '(result, later) := ide_horn_loop_counted ix remaining next in
          (result, here ++ later)
      end
  end.

(** The retained Horn run separates preparation, initial queue and execution events. *)
Record ide_horn_execution : Type := IdeHornExecution {
  ide_horn_prepared : sys_index K (IpHorn.rule K);
  ide_horn_preparation : exact_counted (ide_horn_call K) (sys_index K (IpHorn.rule K));
  ide_horn_initial : Engine.t K (IpHorn.rule K) bool;
  ide_horn_initial_events : audit_trace (fx_declared_call K (IpHorn.rule K) bool);
  ide_horn_returned : option (assignment K bool);
  ide_horn_run_events : audit_trace (fx_declared_call K (IpHorn.rule K) bool)
}.

Definition ide_horn_total_counted : ide_horn_execution :=
  let preparation := ide_horn_index_counted in
  let ix := exact_value preparation in
  let '(queue, initial_events) := fx_model_enqueue EC IpHorn.schedule system rules PQueue.empty in
  let initial := Engine.State Map.empty queue Map.empty in
  let '(returned, events) := ide_horn_loop_counted ix ide_horn_credit initial in
  IdeHornExecution ix preparation initial initial_events returned events.

Definition ide_horn_total_work (run : ide_horn_execution) : nat :=
  exact_units (ide_horn_preparation run) + 64 +
  ide_horn_source_work (ide_horn_initial_events run) +
  ide_horn_source_work (ide_horn_run_events run).

(** This explicit input polynomial does not inspect returned events or work. *)
Definition ide_horn_total_input_budget : nat :=
  (Nat.of_num_uint 1048576%uint) * Nat.pow (S (length rules)) 16 * Nat.pow (S ide_horn_key_max) 4.

(** The counted Horn engine returns the original total solver result within budget. *)
Definition ide_horn_total_counted_correct_statement : Prop :=
  let run := ide_horn_total_counted in
  exists values,
    ide_horn_prepared run = index_system EK system (IpHorn.static rules) /\
    ide_horn_initial run = initial_state EC IpHorn.schedule system /\
    ide_horn_returned run = Some values /\
    fx_declared_total_engine_run EK EC bool_lattice IpHorn.schedule Joining system
      (ide_horn_prepared run) (ide_horn_initial run) values (ide_horn_run_events run) /\
    values = proj1_sig (total_solver_map EK EC bool_lattice bool_laws IpHorn.schedule Joining
      system (IpHorn.static rules) (IpHorn.termination rules)) /\
    ide_horn_total_work run <= ide_horn_total_input_budget.

End HornEngine.

(* Definition source: IdeLegacyWhole.v *)
(** * Whole old finite IDE construction and actual returned query

    This composition executes the direct and lifted Horn children on their actual generated
    inputs, then the table/contribution/join stages. No callback is replayed to recover work.
    Builds on: IdeHornInput, IdeHornEngine and IdeLegacyLift. *)

Section WholeLegacy.

Context {N P D A : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A).

Context (node_body : N -> nat) (site_body : P -> nat) (fact_body : D -> nat)
  (value_body : A -> nat).

Let direct_key := IpTab.fact_encoding EN ED.

Let lifted_fact := IdeTab.lifted_encoding ED EA.

Let lifted_key := IpTab.fact_encoding EN lifted_fact.

Let direct_body := ide_fact_body EN ED node_body fact_body.

Let lifted_body := ide_fact_body EN lifted_fact node_body
  (ide_lifted_encoding_body ED EA fact_body value_body).

(** The finite run retains both Horn children and the graph, seed, contribution and collection
    stages. *)
Record ide_legacy_whole_run : Type := IdeLegacyWholeRun {
  ide_legacy_direct_rules : exact_counted (ide_horn_input_call N P D)
    (list (IpHorn.rule (IpTab.fact N D)));
  ide_legacy_direct_engine : ide_horn_execution (K := IpTab.fact N D);
  ide_legacy_graph_stage : exact_counted (ide_legacy_call N P D A)
    (ip_problem N P (option D * list A));
  ide_legacy_seed_stage : exact_counted (ide_legacy_call N P D A) (list A);
  ide_legacy_lifted_rules : exact_counted (ide_horn_input_call N P (option D * list A))
    (list (IpHorn.rule (IpTab.fact N (option D * list A))));
  ide_legacy_lifted_engine : ide_horn_execution (K := IpTab.fact N (option D * list A));
  ide_legacy_contribution_stage : exact_counted (ide_legacy_call N P D A) (list ((N * option D) *
    A));
  ide_legacy_collection_stage : exact_counted (ide_legacy_call N P D A) (Map.t (N * option D) A)
}.

Definition ide_legacy_lifted_query (values : assignment (IpTab.fact N (option D * list A)) bool)
    (n : N) (d : option (option D * list A))
    : exact_counted (ide_legacy_call N P D A) bool :=
  exact_bind 500 (exact_get IdeLegacyReachMap lifted_key lifted_body (inr (n,d)) values)
    (fun found => exact_case 501 (exact_return 501
      (match found with
      | Some value => value
      | None => false
      end))).

Definition ide_legacy_whole_counted (start : N) (seed : option D) (initial : A)
    : ide_legacy_whole_run :=
  let direct_rules := ide_horn_rules_counted EP (ide_graph old) site_body (start,seed) in
  let direct_engine := ide_horn_total_counted direct_key direct_body (exact_value direct_rules) in
  let graph_run := ide_legacy_lifted_graph ED EA old fact_body value_body in
  let seed_run := ide_legacy_domain EA old value_body in
  let lifted_seed := Some (seed, exact_value seed_run) in
  let lifted_rules := ide_horn_rules_counted EP (exact_value graph_run) site_body
    (start,lifted_seed) in
  let lifted_engine := ide_horn_total_counted lifted_key lifted_body (exact_value lifted_rules) in
  let lifted_values := match ide_horn_returned lifted_engine with
    | Some values => values
    | None => Map.empty
    end in
  let contribution_run := ide_legacy_contributions EA old value_body
    (ide_legacy_lifted_query lifted_values) initial in
  let collection_run := ide_legacy_collect EN ED old node_body fact_body (exact_value
    contribution_run) in
  IdeLegacyWholeRun direct_rules direct_engine graph_run seed_run lifted_rules lifted_engine
    contribution_run collection_run.

Definition ide_legacy_whole_query (run : ide_legacy_whole_run) (n : N) (d : option D)
    : exact_counted (ide_legacy_call N P D A) (option A) :=
  let values := match ide_horn_returned (ide_legacy_direct_engine run) with
    | Some values => values
    | None => Map.empty
    end in
  exact_bind 510 (exact_get IdeLegacyDirectMap direct_key direct_body (inr (n,d)) values)
    (fun raw =>
    let present := match raw with
    | Some b => b
    | None => false
    end in
    if present then exact_case 511
      (exact_bind 512 (exact_get IdeLegacyJoinMap (IpTab.vertex_encoding EN ED)
        (ide_vertex_encoding_body EN ED node_body fact_body) (n,d)
        (exact_value (ide_legacy_collection_stage run))) (fun found =>
        exact_return 513 (Some (match found with
          | Some value => value
          | None => bot (ide_lattice old)
          end))))
    else exact_case 514 (exact_return 514 None)).

Definition ide_legacy_whole_work (run : ide_legacy_whole_run) : nat :=
  1024 + exact_units (ide_legacy_direct_rules run) +
  ide_horn_total_work direct_key direct_body (ide_legacy_direct_engine run) + exact_units
    (ide_legacy_graph_stage run) +
  exact_units (ide_legacy_seed_stage run) + exact_units (ide_legacy_lifted_rules run) +
  ide_horn_total_work lifted_key lifted_body (ide_legacy_lifted_engine run) + exact_units
    (ide_legacy_contribution_stage run) +
  exact_units (ide_legacy_collection_stage run).

(** Closed, input-only geometry includes the original finite function-space explosion. *)
Definition ide_legacy_closed_geometry : nat :=
  let values := length (ide_values old) in
  let functions := Nat.pow (S values) (S values) in
  (1 + length (ip_nodes (ide_graph old)) + length (ip_facts (ide_graph old)) +
    length (ip_sites (ide_graph old)) + length (ip_edges (ide_graph old)) +
    fold_right (fun e n => length (ip_pairs e) + n) 0 (ip_edges (ide_graph old))) * S functions.

Definition ide_legacy_operand_max (start : N) (seed : option D) (initial : A) : nat :=
  let graph := IdeTab.graph ED EA old in
  let direct_rules := IpTab.rules (ide_graph old) EP (start,seed) in
  let lifted_rules := IpTab.rules graph EP (start,Some (seed,IdeTab.domain EA old)) in
  node_body start + ide_option_body fact_body seed + value_body initial +
  ide_horn_key_max direct_key direct_body direct_rules +
  ide_horn_key_max lifted_key lifted_body lifted_rules +
  fold_right Nat.max 0 (map (fun a => value_body a + Pos.size_nat (encode EA a)) (ide_values old)) +
  fold_right Nat.max 0 (map (fun p => site_body p + Pos.size_nat (encode EP p)) (ip_sites (ide_graph
    old))).

Definition ide_legacy_whole_input_budget (start : N) (seed : option D) (initial : A) : nat :=
  let graph := IdeTab.graph ED EA old in
  let direct_rules := IpTab.rules (ide_graph old) EP (start,seed) in
  let lifted_rules := IpTab.rules graph EP (start,Some (seed,IdeTab.domain EA old)) in
  ide_horn_total_input_budget direct_key direct_body direct_rules +
  ide_horn_total_input_budget lifted_key lifted_body lifted_rules +
  ide_horn_input_budget EP (ide_graph old) site_body + ide_horn_input_budget EP graph site_body +
  (Nat.of_num_uint 16777216%uint) * Nat.pow (S ide_legacy_closed_geometry) 32 *
    Nat.pow (S (ide_legacy_operand_max start seed initial)) 8.

Definition ide_legacy_query_input_budget (n : N) (d : option D) : nat :=
  4096 + 4 * direct_body (inr (n,d)) +
    4 * ide_vertex_encoding_body EN ED node_body fact_body (n,d) +
    1024 * (Pos.size_nat (encode direct_key (inr (n,d))) +
      Pos.size_nat (encode (IpTab.vertex_encoding EN ED) (n,d))).

(** Under the old-problem and start premises, both Horn children return and the finite run bounds
    construction and query work while matching the legacy query. *)
Definition audit_ide_legacy_full_source_statement : Prop :=
  forall start seed initial,
    ide_laws old -> In start (ip_nodes (ide_graph old)) ->
    (match seed with
    | None => True
    | Some d => In d (ip_facts (ide_graph old))
    end) ->
    let run := ide_legacy_whole_counted start seed initial in
    (exists direct_values lifted_values,
      ide_horn_returned (ide_legacy_direct_engine run) = Some direct_values /\
      ide_horn_returned (ide_legacy_lifted_engine run) = Some lifted_values) /\
    ide_legacy_whole_work run <= ide_legacy_whole_input_budget start seed initial /\
    forall n d,
      exact_units (ide_legacy_whole_query run n d) <= ide_legacy_query_input_budget n d /\
      exact_value (ide_legacy_whole_query run n d) =
        (if ifds_solve EN EP ED (ide_graph old) start seed n d
          then Some (ide_solve EN EP ED EA old start seed initial n d) else None).

End WholeLegacy.

(* Definition source: IdePrimitiveAdequacy.v *)
(** * Concrete source-primitive expansion for the IDE mirrors

    The expansion calls the fixed library source recurrences on the actual retained operands.
    It does not assume an arbitrary whole-operation source cost from a client.
    Builds on: AUD-CL-MODELS and ExactSource. *)

(** External encoding entries retain their actual input and result. The body budget is a
    genuine external adapter; the list/option/pair/sum constructors are expanded internally. *)
Definition ide_encoding_entry {K} (E : encoding K) (key : K) : positive * list (K * positive) :=
  let code := encode E key in (code,[(key,code)]).

Definition ide_encoding_entry_work {K} (body : K -> nat) (events : list (K * positive)) : nat :=
  fold_right (fun event rest => body (fst event) + rest) 0 events.

Definition ide_list_encoding_source_work {A} (EA : encoding A) (body : A -> nat) (xs : list A) : nat
  :=
  audit_list_events_work (ide_encoding_entry_work body)
    (snd (audit_list_encode (ide_encoding_entry EA) xs)).

(** The list source encoder matches the library encoding within its allowance. *)
Definition ide_list_encoding_adequacy_statement : Prop :=
  forall A (EA : encoding A) (body : A -> nat) xs,
    fst (audit_list_encode (ide_encoding_entry EA) xs) = encode (list_encoding EA) xs /\
    ide_list_encoding_source_work EA body xs <= ide_list_encoding_body EA body xs.

(** Raw trie position depth and actual output traversal are counted, not merely bindings. *)
Definition exact_map_literal_work {K V} (body : K -> nat) (event : exact_map_call K V) : nat :=
  match event with
  | ExactEncode key _ => 1 + body key
  | ExactGet _ code before _ => 5 + audit_trie_get_source_work code before
  | ExactSet key code value before _ =>
      2 + audit_trie_update_source_work code (Some (key,value)) before
  | ExactRemove _ code before _ => 2 + audit_trie_update_source_work code None before
  | ExactElements before _ => audit_elements_work (snd (audit_map_elements before))
  end.

Definition exact_map_model_charge {K V} (body : K -> nat) (event : exact_map_call K V) : nat :=
  64 + match event with
  | ExactEncode key code => audit_encoding_weight (Pos.size_nat code) + body key
  | ExactGet _ code _ _ => audit_get_weight code + 32 * Pos.size_nat code
  | ExactSet _ code _ _ _ => audit_set_weight code + 64 * Pos.size_nat code
  | ExactRemove _ code _ _ => audit_remove_weight code + 64 * Pos.size_nat code
  | ExactElements before answer =>
      1 + 32 * Nat.pow (S (exact_trie_nodes before)) 2 + 8 * length answer
  end.

(** The model charge bounds the actual map primitive work. *)
Definition exact_map_implementation_adequacy_statement : Prop :=
  forall K V (body : K -> nat) (event : exact_map_call K V),
    exact_map_literal_work body event <= exact_map_model_charge body event.

Definition ide_table_literal_event_work {A} (EA : encoding A) (body : A -> nat)
    (event : audit_event (ide_table_call A)) : nat :=
  match event with
  | AuditCall (IdeValueMap call) => exact_map_literal_work body call
  | AuditCall (IdeValueSet call) => exact_map_literal_work body call
  | AuditCall (IdeTableRegistry call) =>
      match call with
      | ExactEncode xs _ => 1 + ide_list_encoding_source_work EA body xs
      | _ => exact_map_literal_work (ide_list_encoding_body EA body) call
      end
  | AuditCall (IdeTableJoin _ _ _) => 64
  | _ => 64
  end.

Definition ide_table_literal_work {A} (EA : encoding A) (body : A -> nat)
    (events : audit_trace (ide_table_call A)) : nat :=
  fold_right (fun event total => ide_table_literal_event_work EA body event + total) 0 events.

(** Literal event work is bounded by counted units for vectors, registry and finite domain. *)
Definition ide_tables_implementation_adequacy_statement : Prop :=
  forall A (EA : encoding A) (body : A -> nat) domain,
    let vectors := ide_vectors_counted domain domain in
    let registry := ide_registry_counted EA body domain in
    let finite := ide_finite_domain_counted EA body domain in
    ide_table_literal_work EA body (exact_events vectors) <= exact_units vectors /\
    ide_table_literal_work EA body (exact_events registry) <= exact_units registry /\
    ide_table_literal_work EA body (exact_events finite) <= exact_units finite.

(** * Actual legacy callback bodies

    The finite fallback executes each weight and lattice join adapter once at its original
    source call. The whole run retains these body receipts through graph and collection.
    For example, one contribution records its actual old join operand and returned value.
    Builds on: the literal finite backend above and typed external source adapters. *)
Section LegacyBodies.

Context {N P D A : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (old : ide_problem N P D A)
  (adapters : audit_ide_legacy_adapters EN EP ED EA old).

Let node_body := external_input_budget
  (ide_node_encoding_adapter (ide_legacy_graph_encoding adapters)).

Let site_body := external_input_budget
  (ide_site_encoding_adapter (ide_legacy_graph_encoding adapters)).

Let fact_body := external_input_budget
  (ide_fact_encoding_adapter (ide_legacy_graph_encoding adapters)).

Let value_body := external_input_budget (ide_value_encoding_adapter adapters).

Let legacy_functions := ide_legacy_function_keys EA old value_body.

Let legacy_facts := ide_legacy_lifted_facts ED EA old fact_body value_body.

Let vertex_body := ide_vertex_encoding_body EN ED node_body fact_body.

Let direct_key := IpTab.fact_encoding EN ED.

Let lifted_fact := IdeTab.lifted_encoding ED EA.

Let lifted_key := IpTab.fact_encoding EN lifted_fact.

Let direct_body := ide_fact_body EN ED node_body fact_body.

Let lifted_body := ide_fact_body EN lifted_fact node_body
  (ide_lifted_encoding_body ED EA fact_body value_body).

Definition ide_legacy_weight_with_bodies (edge : ip_edge N P D) (source target : option D) (a : A)
    : exact_counted (ide_legacy_call N P D A) A :=
  exact_external_call (ide_legacy_weight_adapter adapters) (edge,(source,(target,a)))
    (fun output => IdeLegacyWeight edge source target a output).

Definition ide_legacy_lifted_edge_with_bodies (edge : ip_edge N P D)
    : exact_counted (ide_legacy_call N P D A) (ip_edge N P (option D * list A)) :=
  exact_bind 210 (exact_flat_map 211 (fun xy =>
    exact_bind 212 legacy_functions (fun functions =>
      exact_map 213 (fun f =>
        exact_bind 214 (exact_map 215 (ide_legacy_weight_with_bodies edge (fst xy) (snd xy)) f)
          (fun transformed => exact_return 216
            (Some (fst xy, f), Some (snd xy, transformed)))) functions)) (ip_pairs edge))
    (fun pairs => exact_return 217
      (IpEdge (ip_source edge) (ip_target edge) (ip_action edge) ((None, None) :: pairs))).

Definition ide_legacy_lifted_graph_with_bodies : exact_counted (ide_legacy_call N P D A)
    (ip_problem N P (option D * list A)) :=
  exact_bind 220 legacy_facts (fun facts =>
  exact_bind 221 (exact_map 222 ide_legacy_lifted_edge_with_bodies (ip_edges (ide_graph old))) (fun
    edges =>
    exact_return 223 (IpProblem (ip_nodes (ide_graph old)) (ip_sites (ide_graph old)) facts
      edges))).

Definition ide_legacy_join_put_with_bodies (key : N * option D) (value : A)
    (table : Map.t (N * option D) A) : exact_counted (ide_legacy_call N P D A)
      (Map.t (N * option D) A) :=
  exact_bind 270 (exact_get IdeLegacyJoinMap (IpTab.vertex_encoding EN ED)
    vertex_body key table) (fun found =>
  exact_bind 271 (exact_case 271 (exact_return 271
    (match found with
    | Some prior => prior
    | None => bot (ide_lattice old)
    end))) (fun prior =>
  exact_bind 272 (exact_external_call (ide_lattice_join_adapter adapters) (value,prior)
    (fun output => IdeLegacyJoin value prior output)) (fun joined =>
    exact_set IdeLegacyJoinMap (IpTab.vertex_encoding EN ED) vertex_body key joined table))).

Definition ide_legacy_collect_with_bodies (contributions : list ((N * option D) * A))
    : exact_counted (ide_legacy_call N P D A) (Map.t (N * option D) A) :=
  exact_fold_right 280 (fun item table => ide_legacy_join_put_with_bodies (fst item) (snd item)
    table)
    Map.empty contributions.

Definition ide_legacy_whole_counted_with_bodies (start : N) (seed : option D) (initial : A)
    : ide_legacy_whole_run :=
  let direct_rules := ide_horn_rules_counted EP (ide_graph old) site_body (start,seed) in
  let direct_engine := ide_horn_total_counted direct_key direct_body (exact_value direct_rules) in
  let graph_run := ide_legacy_lifted_graph_with_bodies in
  let seed_run := ide_legacy_domain EA old value_body in
  let lifted_seed := Some (seed, exact_value seed_run) in
  let lifted_rules := ide_horn_rules_counted EP (exact_value graph_run) site_body
    (start,lifted_seed) in
  let lifted_engine := ide_horn_total_counted lifted_key lifted_body (exact_value lifted_rules) in
  let lifted_values := match ide_horn_returned lifted_engine with
    | Some values => values
    | None => Map.empty
    end in
  let contribution_run := ide_legacy_contributions EA old value_body
    (ide_legacy_lifted_query EN ED EA node_body fact_body value_body lifted_values) initial in
  let collection_run := ide_legacy_collect_with_bodies (exact_value contribution_run) in
  IdeLegacyWholeRun direct_rules direct_engine graph_run seed_run lifted_rules lifted_engine
    contribution_run collection_run.

(** Only recorded weight and join calls can be valid legacy callback bodies. *)
Definition ide_legacy_body_valid (body : ide_legacy_call N P D A * list audit_external_frame)
    : Prop :=
  match fst body with
  | IdeLegacyWeight edge x y input output =>
    audit_external_body (ide_legacy_weight_adapter adapters) (edge,(x,(y,input))) output
      (snd body)
  | IdeLegacyJoin first second output =>
    audit_external_body (ide_lattice_join_adapter adapters) (first,second) output (snd body)
  | _ => False
  end.

Definition ide_legacy_body_budget (body : ide_legacy_call N P D A * list audit_external_frame)
    : nat :=
  match fst body with
  | IdeLegacyWeight edge x y input _ =>
    external_input_budget (ide_legacy_weight_adapter adapters) (edge,(x,(y,input)))
  | IdeLegacyJoin first second _ =>
    external_input_budget (ide_lattice_join_adapter adapters) (first,second)
  | _ => 0
  end.

Definition ide_legacy_actual_bodies (run : ide_legacy_whole_run (N:=N) (P:=P) (D:=D) (A:=A)) :=
  exact_bodies (ide_legacy_graph_stage run) ++ exact_bodies (ide_legacy_collection_stage run).

(** Valid fallback bodies contribute their summed budgets to the whole construction bound. *)
Definition audit_ide_legacy_with_bodies_statement : Prop :=
  audit_ide_legacy_adapter_laws adapters -> forall start seed initial,
  ide_laws old -> In start (ip_nodes (ide_graph old)) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts (ide_graph old))
  end) ->
  let run := ide_legacy_whole_counted_with_bodies start seed initial in
  Forall ide_legacy_body_valid (ide_legacy_actual_bodies run) /\
  ide_legacy_whole_work EN ED EA node_body fact_body value_body run <=
    16 * ide_legacy_whole_input_budget EN EP ED EA old node_body site_body fact_body
      value_body start seed initial +
    fold_right (fun body rest => ide_legacy_body_budget body + rest) 0
      (ide_legacy_actual_bodies run) /\
  forall n d,
    exact_value (ide_legacy_whole_query EN ED old node_body fact_body run n d) =
      audit_ide_legacy_query EN EP ED EA old start seed initial n d.

End LegacyBodies.
