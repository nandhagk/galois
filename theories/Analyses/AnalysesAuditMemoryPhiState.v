(** * G4 memory phi semantics

    This declaration-only pilot isolates G4 semantic contracts.
    For example, it keeps the historical observation in its original statement.
    Builds on: Galois.Analyses. *)

From Stdlib Require Import List Bool NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesMemoryLegacy AnalysesMemoryFrontier AnalysesMemorySealed.
Import List.ListNotations.

(** Declarations from the PhiProbe candidate. *)
Record phi_result (N E : Type) : Type := PhiResult {
  phi_graph : memory_graph N E;
  phi_representatives : Map.t (memory_version N E) (memory_version N E)
}.

Arguments phi_graph {N E}.
Arguments phi_representatives {N E}.

Definition phi_rep {N E} (EN : encoding N) (EE : encoding E)
    (r : phi_result N E) (v : memory_version N E) : memory_version N E :=
  match Map.get (memory_version_encoding EN EE) v (phi_representatives r) with
  | Some representative => representative
  | None => v
  end.

(** The new graph and map are well formed, retained phis come from the old graph, and idempotent
    representatives preserve valid versions, fix live, definitions and retained phis, rewrite
    fields, identify removed operands, and transport provenance and occurrence histories. *)
Definition phi_history_projection {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (old : memory_graph N E)
    (r : phi_result N E) : Prop :=
  let new := phi_graph r in
  let rep := phi_rep EN EE r in
  memory_graph_wf g effects new /\
  Map.wf (memory_version_encoding EN EE) (phi_representatives r) /\
  (forall n, In n (memory_phis new) -> In n (memory_phis old)) /\
  (forall v, memory_valid_version g effects old v -> memory_valid_version g effects new (rep v)) /\
  rep MemoryLive = MemoryLive /\
  (forall e i, rep (MemoryDef e i) = MemoryDef e i) /\
  (forall n, In n (memory_phis new) -> rep (MemoryPhi n) = MemoryPhi n) /\
  (forall v, rep (rep v) = rep v) /\
  (forall n, memory_in new n = rep (memory_in old n)) /\
  (forall e, memory_out new e = rep (memory_out old e)) /\
  (forall e i, memory_before new e i = option_map rep (memory_before old e i)) /\
  (forall n key, In n (memory_phis new) ->
    memory_operand new n key = option_map rep (memory_operand old n key)) /\
  (forall n, In n (memory_phis old) -> ~ In n (memory_phis new) ->
    rep (MemoryPhi n) <> MemoryPhi n /\
    forall key input, memory_operand old n key = Some input -> rep input = rep (MemoryPhi n)) /\
  (forall root es n v origin, memory_provenance g effects old root es n v origin ->
    memory_provenance g effects new root es n (rep v) origin) /\
  forall es e i input origin, memory_occurrence_history g effects old es e i input origin ->
    memory_occurrence_history g effects new es e i (rep input) origin.

(** A dependency path follows one or more phi operands from its source to its target. *)
Inductive phi_dependency_path {N E} (mg : memory_graph N E) : N -> N -> Prop :=
  | PhiDependencyEdge : forall n key next,
      memory_operand mg n key = Some (MemoryPhi next) -> phi_dependency_path mg n next
  | PhiDependencyExtend : forall n key middle last,
      memory_operand mg n key = Some (MemoryPhi middle) ->
      phi_dependency_path mg middle last -> phi_dependency_path mg n last.

Section Candidate.
  Variable prune : forall N E T, encoding N -> encoding E -> Graph.t N E ->
    (E -> list (memory_effect T)) -> memory_graph N E -> phi_result N E.

  (** Pruning a well-formed graph satisfies the history projection through its representatives. *)
  Definition phi_projection_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) old,
      memory_graph_wf g effects old -> phi_history_projection EN EE g effects old
        (prune N E T EN EE g effects old).

  (** In a well-formed input, a phi with at least one operand, all equal to one live or definition
    version, is removed. *)
  Definition phi_terminal_elimination_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) old,
      memory_graph_wf g effects old ->
      forall n v, In n (memory_phis old) ->
        (v = MemoryLive \/ exists e i, v = MemoryDef e i) ->
        (exists key, memory_operand old n key = Some v) ->
        (forall key input, memory_operand old n key = Some input -> input = v) ->
        ~ In n (memory_phis (phi_graph (prune N E T EN EE g effects old))).

  (** A phi with at least one operand, all referring to itself, remains when a well-formed
    input is pruned. *)
  Definition phi_self_only_retained_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) old,
      memory_graph_wf g effects old ->
      forall n, In n (memory_phis old) ->
        (exists key, memory_operand old n key = Some (MemoryPhi n)) ->
        (forall key input, memory_operand old n key = Some input -> input = MemoryPhi n) ->
        In n (memory_phis (phi_graph (prune N E T EN EE g effects old))).

  (** A phi on a dependency cycle remains after pruning a well-formed graph. *)
  Definition phi_cycle_retained_statement : Prop :=
    forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) old,
      memory_graph_wf g effects old -> forall n, In n (memory_phis old) ->
      phi_dependency_path old n n -> In n (memory_phis (phi_graph (prune N E T EN EE g effects
        old))).

  (** For a well-formed input, both original and pruned legacy projections pass the no-clobber
    checker. *)
  Definition phi_legacy_checked_statement : Prop :=
    forall F N E T (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T)
      (f : F) (g : Graph.t N E) (effects : E -> list (memory_effect T))
      (writes reads : N -> list (footprint T)) old loads fuel,
      memory_graph_wf g effects old ->
      let new := phi_graph (prune N E T EN EE g effects old) in
      no_clobber_check EN EF ET f g writes reads
        (project_memory_legacy EN EE EF ET f g effects writes reads old loads fuel) = true /\
      no_clobber_check EN EF ET f g writes reads
        (project_memory_legacy EN EE EF ET f g effects writes reads new loads fuel) = true.

  (** Under byte laws and a well-formed input, each projection preserves a covered read byte
    along a reachable run from just after an edge, or from entry, when the selected definition
    matches that edge's source, or live entry respectively, and the byte identity has that site
    at the corresponding starting state. *)
  Definition phi_legacy_byte_statement : Prop :=
    forall S O N E T F L (m : semantics S O) (bv : bytes_view S O N E T L)
      (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T) (f : F)
      (effects : E -> list (memory_effect T)) (reads : N -> list (footprint T)) old loads fuel,
      bytes_laws m bv -> memory_graph_wf (cfg (bgv bv)) effects old ->
      let g := cfg (bgv bv) in
      let new := phi_graph (prune N E T EN EE g effects old) in
      let original := project_memory_legacy EN EE EF ET f g effects (writes_at bv) reads old loads
        fuel in
      let pruned := project_memory_legacy EN EE EF ET f g effects (writes_at bv) reads new loads
        fuel in
      (forall before first after e es n l site offset,
        reachable_state m before -> run_edges m (bgv bv) before (e :: nil) first ->
        run_edges m (bgv bv) first es after -> point (bgv bv) after = n ->
        covered (reads n) site offset 1 -> bsite bv first l = Some site ->
        (def_of_load original n = Some (MDef f (Graph.source g e)) ->
          byte bv after l offset = byte bv first l offset) /\
        (def_of_load pruned n = Some (MDef f (Graph.source g e)) ->
          byte bv after l offset = byte bv first l offset)) /\
      (forall before es after n l site offset,
        reachable_state m before -> In (point (bgv bv) before) (Graph.entries g) ->
        run_edges m (bgv bv) before es after -> point (bgv bv) after = n ->
        covered (reads n) site offset 1 -> bsite bv before l = Some site ->
        (def_of_load original n = Some (MLive f) ->
          byte bv after l offset = byte bv before l offset) /\
        (def_of_load pruned n = Some (MLive f) ->
          byte bv after l offset = byte bv before l offset)).
End Candidate.

(** Declarations from the PhiApiProbe candidate. *)
(** A map-returning pruner accepts a well-formed graph and returns a well-formed phi result. *)
Definition memory_prune_with_map_type : Type :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    memory_graph_wf g effects mg -> {r : phi_result N E | memory_graph_wf g effects (phi_graph r)}.

(** Projecting a well-formed phi result returns its graph with the same well-formedness proof. *)
Definition memory_prune_projection {N E T} (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (r : {r : phi_result N E | memory_graph_wf g effects (phi_graph r)}) :
    {mg : memory_graph N E | memory_graph_wf g effects mg} :=
  exist _ (phi_graph (proj1_sig r)) (proj2_sig r).

(** A graph-only pruner accepts and returns a well-formed memory graph. *)
Definition memory_prune_type : Type :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    memory_graph_wf g effects mg -> {mg' : memory_graph N E | memory_graph_wf g effects mg'}.

(** Projecting a map-returning pruner gives a graph-only well-formedness-preserving pruner. *)
Definition memory_prune_from_map (prune : memory_prune_with_map_type) : memory_prune_type :=
  fun N E T EN EE g effects mg wf => memory_prune_projection g effects (prune N E T EN EE g
    effects mg wf).

(** For a well-formed input, pruning maps memory fields and histories through idempotent
    representatives. *)
Definition memory_phi_projection_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg),
    phi_history_projection EN EE g effects mg (proj1_sig (prune N E T EN EE g effects mg wf)).

(** In a well-formed input, an original phi with at least one operand, all equal to one live or
    definition version, is removed. *)
Definition memory_phi_terminal_removed_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg) n v,
    In n (memory_phis mg) -> (v = MemoryLive \/ exists e i, v = MemoryDef e i) ->
    (exists key, memory_operand mg n key = Some v) ->
    (forall key input, memory_operand mg n key = Some input -> input = v) ->
    ~ In n (memory_phis (phi_graph (proj1_sig (prune N E T EN EE g effects mg wf)))).

(** A phi on a dependency cycle remains after pruning. *)
Definition memory_phi_cycles_retained_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg) n,
    In n (memory_phis mg) -> phi_dependency_path mg n n ->
    In n (memory_phis (phi_graph (proj1_sig (prune N E T EN EE g effects mg wf)))).

(** A well-formed graph's frontier builder followed by pruning returns a well-formed phi result. *)
Definition memory_frontier_pruned {N E T} (prune : memory_prune_with_map_type)
    (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (wf : graph_wf g) :
    {r : phi_result N E | memory_graph_wf g effects (phi_graph r)} :=
  let original := memory_frontier_build EN EE g effects wf in
  prune N E T EN EE g effects (proj1_sig original) (proj2_sig original).

(** A well-formed graph's sealed builder followed by pruning returns a well-formed phi result. *)
Definition memory_sealed_pruned {N E T} (prune : memory_prune_with_map_type)
    (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (wf : graph_wf g) :
    {r : phi_result N E | memory_graph_wf g effects (phi_graph r)} :=
  let original := memory_sealed_build EN EE g effects wf in
  prune N E T EN EE g effects (proj1_sig original) (proj2_sig original).

(** For a well-formed input graph, both builders map their original memory fields and histories
    through representatives. *)
Definition memory_pruned_builders_projection_statement (prune : memory_prune_with_map_type) : Prop
  :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (wf : graph_wf g),
    phi_history_projection EN EE g effects (proj1_sig (memory_frontier_build EN EE g effects wf))
      (proj1_sig (memory_frontier_pruned prune EN EE g effects wf)) /\
    phi_history_projection EN EE g effects (proj1_sig (memory_sealed_build EN EE g effects wf))
      (proj1_sig (memory_sealed_pruned prune EN EE g effects wf)).

(** Legacy projections before and after pruning both pass the checker. *)
Definition memory_prune_legacy_checked_statement (prune : memory_prune_with_map_type) : Prop :=
  forall F N E T (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T)
    (f : F) (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (writes reads : N -> list (footprint T)) old (wf : memory_graph_wf g effects old) loads fuel,
    let new := phi_graph (proj1_sig (prune N E T EN EE g effects old wf)) in
    no_clobber_check EN EF ET f g writes reads
      (project_memory_legacy EN EE EF ET f g effects writes reads old loads fuel) = true /\
    no_clobber_check EN EF ET f g writes reads
      (project_memory_legacy EN EE EF ET f g effects writes reads new loads fuel) = true.

(** Under byte laws and a well-formed input, each projection preserves a covered read byte
    along a reachable run from just after an edge, or from entry, when the selected definition
    matches that edge's source, or live entry respectively, and the byte identity has that site
    at the corresponding starting state. *)
Definition memory_prune_legacy_bytes_statement (prune : memory_prune_with_map_type) : Prop :=
  forall S O N E T F L (m : semantics S O) (bv : bytes_view S O N E T L)
    (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T) (f : F)
    (effects : E -> list (memory_effect T)) (reads : N -> list (footprint T)) old
    (wf : memory_graph_wf (cfg (bgv bv)) effects old) loads fuel,
    bytes_laws m bv ->
    let g := cfg (bgv bv) in
    let new := phi_graph (proj1_sig (prune N E T EN EE g effects old wf)) in
    let original := project_memory_legacy EN EE EF ET f g effects (writes_at bv) reads old loads
      fuel in
    let pruned := project_memory_legacy EN EE EF ET f g effects (writes_at bv) reads new loads
      fuel in
    (forall before first after e es n l site offset,
      reachable_state m before -> run_edges m (bgv bv) before (e :: nil) first ->
      run_edges m (bgv bv) first es after -> point (bgv bv) after = n ->
      covered (reads n) site offset 1 -> bsite bv first l = Some site ->
      (def_of_load original n = Some (MDef f (Graph.source g e)) ->
        byte bv after l offset = byte bv first l offset) /\
      (def_of_load pruned n = Some (MDef f (Graph.source g e)) ->
        byte bv after l offset = byte bv first l offset)) /\
    (forall before es after n l site offset,
      reachable_state m before -> In (point (bgv bv) before) (Graph.entries g) ->
      run_edges m (bgv bv) before es after -> point (bgv bv) after = n ->
      covered (reads n) site offset 1 -> bsite bv before l = Some site ->
      (def_of_load original n = Some (MLive f) ->
        byte bv after l offset = byte bv before l offset) /\
      (def_of_load pruned n = Some (MLive f) ->
        byte bv after l offset = byte bv before l offset)).

(** Each removed phi has an operand with the same representative. *)
Definition memory_phi_removed_has_operand_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg) n,
    let r := proj1_sig (prune N E T EN EE g effects mg wf) in
    In n (memory_phis mg) -> ~ In n (memory_phis (phi_graph r)) ->
    exists key input, memory_operand mg n key = Some input /\
      phi_rep EN EE r input = phi_rep EN EE r (MemoryPhi n).

(** A noncyclic original phi with at least one operand and a common nonself representative is
    removed. *)
Definition memory_phi_resolved_removed_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg) n,
    let r := proj1_sig (prune N E T EN EE g effects mg wf) in
    In n (memory_phis mg) -> ~ phi_dependency_path mg n n ->
    (exists key first, memory_operand mg n key = Some first /\
      phi_rep EN EE r first <> MemoryPhi n /\
      forall key' input, memory_operand mg n key' = Some input ->
        phi_rep EN EE r input = phi_rep EN EE r first) ->
    ~ In n (memory_phis (phi_graph r)).

(** Pruning filters original phi nodes and versions and leaves non-original phi representatives
    unchanged. *)
Definition memory_phi_output_shape_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg),
    let r := proj1_sig (prune N E T EN EE g effects mg wf) in
    let new := phi_graph r in
    let kept := FinSet.of_list EN (memory_phis new) in
    (forall n, ~ In n (memory_phis mg) -> phi_rep EN EE r (MemoryPhi n) = MemoryPhi n) /\
    memory_phis new = filter (fun n => FinSet.mem EN n kept) (memory_phis mg) /\
    memory_versions new = filter (fun v =>
      match v with
      | MemoryPhi n => FinSet.mem EN n kept
      | _ => true
      end) (memory_versions mg).

(** The representative map contains exactly removed original phis, mapped to their
    representatives. *)
Definition memory_phi_map_domain_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg) v w,
    let r := proj1_sig (prune N E T EN EE g effects mg wf) in
    Map.get (memory_version_encoding EN EE) v (phi_representatives r) = Some w <->
    exists n, v = MemoryPhi n /\ In n (memory_phis mg) /\
      ~ In n (memory_phis (phi_graph r)) /\ w = phi_rep EN EE r v.

(** Declarations from the PhiDependencyProbe candidate. *)
Record phi_dependency_edge (N E : Type) : Type := PhiDependencyEdgeData {
  dependency_source : N;
  dependency_key : option E;
  dependency_target : N
}.
Arguments PhiDependencyEdgeData {N E}.
Arguments dependency_source {N E}.
Arguments dependency_key {N E}.
Arguments dependency_target {N E}.

Definition phi_input_rows {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    Map.t N (list (option E * memory_version N E)) :=
  let base := prepare EN g in
  memory_result_index EN (fun n =>
    let raw_keys := None :: map Some (pred_edges base n) in
    let keys := memory_distinct (option_encoding EE) raw_keys in
    flat_map (fun key =>
      match memory_operand mg n key with
      | Some input => [(key,input)]
      | None => []
      end) keys) (memory_phis mg).

Definition phi_dependency_rows_from_inputs {N E} (EN : encoding N) (mg : memory_graph N E)
    (inputs : Map.t N (list (option E * memory_version N E))) :
    Map.t N (list (phi_dependency_edge N E)) :=
  memory_result_index EN (fun n => flat_map (fun kv =>
    match snd kv with
    | MemoryPhi target => [PhiDependencyEdgeData n (fst kv) target]
    | _ => []
    end) (index_edges EN inputs n)) (memory_phis mg).

Definition phi_dependency_graph_from_inputs {N E} (EN : encoding N) (mg : memory_graph N E)
    (inputs : Map.t N (list (option E * memory_version N E))) : Graph.t N (phi_dependency_edge N
      E) :=
  let rows := phi_dependency_rows_from_inputs EN mg inputs in
  {| Graph.entries := memory_phis mg;
     Graph.nodes := memory_phis mg;
     Graph.out := index_edges EN rows;
     Graph.source := dependency_source;
     Graph.target := dependency_target |}.

Definition phi_dependency_graph {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) : Graph.t N
      (phi_dependency_edge N E) :=
  phi_dependency_graph_from_inputs EN mg (phi_input_rows EN EE g effects mg).

(** A well-formed memory graph yields a well-formed dependency graph with duplicate-free
    outgoing rows and valid prepared indexes. *)
Definition phi_dependency_ready_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg,
    memory_graph_wf g effects mg ->
    let dep := phi_dependency_graph EN EE g effects mg in ready EN dep (prepare EN dep).

(** In a well-formed graph, paths from original phis correspond to nonempty dependency-graph
    paths. *)
Definition phi_dependency_paths_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg,
    memory_graph_wf g effects mg -> forall n m,
    In n (memory_phis mg) ->
    (phi_dependency_path mg n m <->
      exists edges, edges <> [] /\ path (phi_dependency_graph EN EE g effects mg) n edges m).

Definition phi_component_cyclic {N E} (EN : encoding N) (dep : Graph.t N (phi_dependency_edge N E))
    (p : prepared EN dep) (component : list N) : bool :=
  match component with
  | [] => false
  | [n] => existsb (fun edge => Pos.eqb (encode EN (Graph.target dep edge)) (encode EN n))
    (succ_edges p n)
  | _ :: _ :: _ => true
  end.

Definition phi_cycle_flags {N E} (EN : encoding N) (dep : Graph.t N (phi_dependency_edge N E))
    (p : prepared EN dep) (r : scc_result N) : FinSet.t N :=
  fold_left (fun marked component =>
    if phi_component_cyclic EN dep p component then
      fold_left (fun flags n => FinSet.add EN n flags) component marked
    else marked) (components r) FinSet.empty.

Record phi_dependency_index {N E} (EN : encoding N) : Type := PhiDependencyIndex {
  phi_index_inputs : Map.t N (list (option E * memory_version N E));
  phi_index_graph : Graph.t N (phi_dependency_edge N E);
  phi_index_prepared : prepared EN phi_index_graph;
  phi_index_scc : scc_result N;
  phi_index_cycles : FinSet.t N
}.
Arguments PhiDependencyIndex {N E EN}.
Arguments phi_index_inputs {N E EN}.
Arguments phi_index_graph {N E EN}.
Arguments phi_index_prepared {N E EN}.
Arguments phi_index_scc {N E EN}.
Arguments phi_index_cycles {N E EN}.

Definition phi_prepare_dependencies {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    phi_dependency_index (E := E) EN :=
  let inputs := phi_input_rows EN EE g effects mg in
  let dep := phi_dependency_graph_from_inputs EN mg inputs in
  let prep := prepare EN dep in
  let components := scc prep in
  PhiDependencyIndex inputs dep prep components (phi_cycle_flags EN dep prep components).

(** For a well-formed graph, cycle flags identify precisely its original phis on dependency
    cycles. *)
Definition phi_cycle_flags_statement : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg,
    memory_graph_wf g effects mg -> forall n, In n (memory_phis mg) ->
    (FinSet.mem EN n (phi_index_cycles (phi_prepare_dependencies EN EE g effects mg)) = true <->
      phi_dependency_path mg n n).

(** Declarations from the PhiResolveProbe candidate. *)
Definition phi_rep_from_map {N E} (EN : encoding N) (EE : encoding E)
    (representatives : Map.t (memory_version N E) (memory_version N E)) (v : memory_version N E) :
    memory_version N E :=
  match Map.get (memory_version_encoding EN EE) v representatives with
  | Some r => r
  | None => v
  end.

Definition phi_same_rep {N E} (EN : encoding N) (EE : encoding E)
    (representatives : Map.t (memory_version N E) (memory_version N E))
    (candidate : memory_version N E) (entry : option E * memory_version N E) : bool :=
  Pos.eqb (encode (memory_version_encoding EN EE) candidate)
    (encode (memory_version_encoding EN EE) (phi_rep_from_map EN EE representatives (snd entry))).

(** A resolution step keeps cyclic, empty, self or conflicting rows and maps equal nonself rows. *)
Inductive phi_resolve_step {N E} (EN : encoding N) (EE : encoding E)
    (index : phi_dependency_index (E := E) EN) :
    Map.t (memory_version N E) (memory_version N E) -> N ->
    Map.t (memory_version N E) (memory_version N E) -> Prop :=
  | PhiResolveCyclic : forall representatives n,
      FinSet.mem EN n (phi_index_cycles index) = true ->
      phi_resolve_step EN EE index representatives n representatives
  | PhiResolveEmpty : forall representatives n,
      FinSet.mem EN n (phi_index_cycles index) = false ->
      index_edges EN (phi_index_inputs index) n = [] ->
      phi_resolve_step EN EE index representatives n representatives
  | PhiResolveEqual : forall representatives n key input rest candidate,
      FinSet.mem EN n (phi_index_cycles index) = false ->
      index_edges EN (phi_index_inputs index) n = (key,input) :: rest ->
      candidate = phi_rep_from_map EN EE representatives input ->
      Pos.eqb (encode (memory_version_encoding EN EE) candidate)
        (encode (memory_version_encoding EN EE) (MemoryPhi n)) = false ->
      forallb (phi_same_rep EN EE representatives candidate) rest = true ->
      phi_resolve_step EN EE index representatives n
        (Map.set (memory_version_encoding EN EE) (MemoryPhi n) candidate representatives)
  | PhiResolveKeep : forall representatives n key input rest candidate,
      FinSet.mem EN n (phi_index_cycles index) = false ->
      index_edges EN (phi_index_inputs index) n = (key,input) :: rest ->
      candidate = phi_rep_from_map EN EE representatives input ->
      (Pos.eqb (encode (memory_version_encoding EN EE) candidate)
         (encode (memory_version_encoding EN EE) (MemoryPhi n)) = true \/
       forallb (phi_same_rep EN EE representatives candidate) rest = false) ->
      phi_resolve_step EN EE index representatives n representatives.

(** A resolution trace threads the representative map through the listed nodes in order. *)
Inductive phi_resolve_trace {N E} (EN : encoding N) (EE : encoding E)
    (index : phi_dependency_index (E := E) EN) : list N ->
    Map.t (memory_version N E) (memory_version N E) ->
    Map.t (memory_version N E) (memory_version N E) -> Prop :=
  | PhiResolveTraceNil : forall representatives,
      phi_resolve_trace EN EE index [] representatives representatives
  | PhiResolveTraceCons : forall n rest before after final,
      phi_resolve_step EN EE index before n after ->
      phi_resolve_trace EN EE index rest after final ->
      phi_resolve_trace EN EE index (n :: rest) before final.

(** From an empty map, resolution in component order yields the pruning representatives. *)
Definition phi_resolution_statement (prune : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg),
    let index := phi_prepare_dependencies EN EE g effects mg in
    let result := proj1_sig (prune N E T EN EE g effects mg wf) in
    phi_resolve_trace EN EE index (concat (components (phi_index_scc index))) Map.empty
      (phi_representatives result).

(** Every phi resolution step has a successor state. *)
Definition phi_resolve_step_total_statement : Prop :=
  forall N E (EN : encoding N) (EE : encoding E) (index : phi_dependency_index (E := E) EN)
    before n, exists after, phi_resolve_step EN EE index before n after.

(** A phi resolution step has at most one successor state. *)
Definition phi_resolve_step_deterministic_statement : Prop :=
  forall N E (EN : encoding N) (EE : encoding E) (index : phi_dependency_index (E := E) EN)
    before n a b, phi_resolve_step EN EE index before n a -> phi_resolve_step EN EE index before n
      b -> a = b.

(** Declarations from the PhiPublishedNamesProbe candidate. *)
(** The public pruner type is the graph-only well-formedness-preserving interface. *)
Definition memory_prune_public_type := memory_prune_type.

(** Pruning preserves well-formedness of the resulting memory graph. *)
Definition memory_prune_wf_contract (prune : memory_prune_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg),
    memory_graph_wf g effects (proj1_sig (prune N E T EN EE g effects mg wf)).

(** The public graph-returning operation projects the same representative-bearing result. *)
Definition memory_prune_map_projection_contract (prune : memory_prune_type)
    (with_map : memory_prune_with_map_type) : Prop :=
  forall N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) mg (wf : memory_graph_wf g effects mg),
    proj1_sig (prune N E T EN EE g effects mg wf) =
      phi_graph (proj1_sig (with_map N E T EN EE g effects mg wf)).

(** For a well-formed input, the public projection maps memory fields and histories through
    idempotent representatives. *)
Definition memory_phi_projection_contract := memory_phi_projection_statement.

(** In a well-formed input, an original phi with at least one operand, all equal to one live or
    definition version, is removed. *)
Definition memory_phi_terminal_removed_contract := memory_phi_terminal_removed_statement.

(** Every original phi on a dependency cycle remains after pruning. *)
Definition memory_phi_cycles_retained_contract := memory_phi_cycles_retained_statement.

(** Each removed phi has an operand with the same representative. *)
Definition memory_phi_removed_has_operand_contract := memory_phi_removed_has_operand_statement.

(** A noncyclic original phi with at least one operand and a common nonself representative is
    removed. *)
Definition memory_phi_resolved_removed_contract := memory_phi_resolved_removed_statement.

(** Pruning filters original phi nodes and versions and leaves non-original phi representatives
    unchanged. *)
Definition memory_phi_output_shape_contract := memory_phi_output_shape_statement.

(** The public map contract maps exactly removed original phis to their representatives. *)
Definition memory_phi_map_domain_contract := memory_phi_map_domain_statement.

(** For a well-formed input graph, both builders preserve their memory histories through the
    representative map. *)
Definition memory_pruned_builders_projection_contract :=
  memory_pruned_builders_projection_statement.

(** Legacy projections before and after pruning both pass the checker. *)
Definition memory_prune_legacy_checked_contract := memory_prune_legacy_checked_statement.

(** Under byte laws and a well-formed input, each projection preserves a covered read byte
    along a reachable run from just after an edge, or from entry, when the selected definition
    matches that edge's source, or live entry respectively, and the byte identity has that site
    at the corresponding starting state. *)
Definition memory_prune_legacy_bytes_contract := memory_prune_legacy_bytes_statement.

(** A well-formed memory graph yields a well-formed dependency graph with duplicate-free
    outgoing rows and valid prepared indexes. *)
Definition memory_phi_dependency_ready_contract := phi_dependency_ready_statement.

(** In a well-formed graph, phi dependencies from original phis correspond to nonempty graph
    paths. *)
Definition memory_phi_dependency_paths_contract := phi_dependency_paths_statement.

(** For a well-formed graph, cycle flags identify original phis on dependency cycles. *)
Definition memory_phi_cycle_flags_contract := phi_cycle_flags_statement.

(** From an empty map, resolution in component order yields the pruning representatives. *)
Definition memory_phi_resolution_contract := phi_resolution_statement.

(** Every phi resolution step has a successor state. *)
Definition memory_phi_resolution_total_contract := phi_resolve_step_total_statement.

(** A phi resolution step has at most one successor state. *)
Definition memory_phi_resolution_deterministic_contract := phi_resolve_step_deterministic_statement.
