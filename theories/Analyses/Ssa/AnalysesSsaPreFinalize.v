(** * Indexed SSA PRE finalization

    Finalization resolves FRG classes during a block-dominator preorder and ordered point folds.
    For example, a join phi selects an inserted value on an unavailable incoming arm.
    Builds on: AnalysesSsaPreReset, AnalysesSsaPreFrameEdges and the public search driver. *)

From Stdlib Require Import List Bool NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphVisitor
  GraphSearchSpec GraphSearch.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Framework Require Import FrameworkBitvector FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreFrameEdges AnalysesSsaPreReset.
Import List.ListNotations Cost.Notations.

Module PreFinalize.

(** Cache origins distinguish retained instructions, inserted edge computations and parameter writes. *)
Inductive cache_version (E U : Type) :=
  | Initial (u : U)
  | Computed (e : E) (u : U)
  | Inserted (e : E) (u : U)
  | Merged (parameter : E) (u : U).
Arguments Initial {E U}.
Arguments Computed {E U}.
Arguments Inserted {E U}.
Arguments Merged {E U}.

Definition version_expr {E U} (v : cache_version E U) :=
  match v with
  | Initial u | Computed _ u | Inserted _ u | Merged _ u => u
  end.

(** Plans retain the original four edge-indexed placement observations. *)
Record plan (E U : Type) := Plan {
  insertions : Map.t E (FinSet.t U);
  deletions : Map.t E (FinSet.t U);
  reload_versions : Map.t E (cache_version E U);
  phi_versions : Map.t ((E * E) * U) (cache_version E U)
}.
Arguments Plan {E U}.
Arguments insertions {E U}.
Arguments deletions {E U}.
Arguments reload_versions {E U}.
Arguments phi_versions {E U}.
Definition empty_plan {E U} : plan E U := Plan Map.empty Map.empty Map.empty Map.empty.

(** Stored definitions cache their actual point without putting a semantic proof into computation. *)
Record slot (N E U : Type) := Slot {
  selected : cache_version E U;
  definition_point : N
}.
Arguments Slot {N E U}.
Arguments selected {N E U}.
Arguments definition_point {N E U}.
Definition scope N E U := Map.t positive (slot N E U).

(** Coordinates retain their source owner and its supplied dense block identity. *)
Record location (B : Type) := Location {
  location_block : B;
  location_id : positive;
  location_rank : positive
}.
Arguments Location {B}.
Arguments location_block {B}.
Arguments location_id {B}.
Arguments location_rank {B}.

(** Each argument retains the exact predecessor, parameter and original operand decision. *)
Record argument (B BE E U : Type) := Argument {
  argument_block : B;
  argument_expression : U;
  argument_block_edge : BE;
  argument_incoming : E;
  argument_parameter : E;
  argument_operand : PreFrg.operand B E U;
  argument_class : option positive
}.
Arguments Argument {B BE E U}.
Arguments argument_block {B BE E U}.
Arguments argument_expression {B BE E U}.
Arguments argument_block_edge {B BE E U}.
Arguments argument_incoming {B BE E U}.
Arguments argument_parameter {B BE E U}.
Arguments argument_operand {B BE E U}.
Arguments argument_class {B BE E U}.

(** Preparation caches syntax and all point buckets before the single placement traversal. *)
Record prepared (B BE N E U : Type) := Prepared {
  block_points : Map.t positive (B * list N);
  coordinates : Map.t N (location B);
  class_names : Intern.t (PreFrg.version B E U);
  occurrence_classes : Map.t E (option positive);
  phi_rows : Index.t N (N * (positive * slot N E U));
  argument_rows : Index.t N (N * argument B BE E U);
  initial_scope : scope N E U;
  forest : Prepared.t positive (positive * positive);
  order : list positive;
  budget : positive
}.
Arguments Prepared {B BE N E U}.
Arguments block_points {B BE N E U}.
Arguments coordinates {B BE N E U}.
Arguments class_names {B BE N E U}.
Arguments occurrence_classes {B BE N E U}.
Arguments phi_rows {B BE N E U}.
Arguments argument_rows {B BE N E U}.
Arguments initial_scope {B BE N E U}.
Arguments forest {B BE N E U}.
Arguments order {B BE N E U}.
Arguments budget {B BE N E U}.

(** Detailed finalization keeps missing-name and fuel exhaustion outcomes observable. *)
Inductive finish_reason :=
  | Finished
  | OutOfFuel
  | MissingBlock.

Record result (E U : Type) := Result {
  output : plan E U;
  reason : finish_reason
}.
Arguments Result {E U}.
Arguments output {E U}.
Arguments reason {E U}.

Record work (N E U : Type) := Work {
  pending : list positive;
  snapshots : Map.t positive (scope N E U);
  current_plan : plan E U;
  missing_block : bool
}.
Arguments Work {N E U}.
Arguments pending {N E U}.
Arguments snapshots {N E U}.
Arguments current_plan {N E U}.
Arguments missing_block {N E U}.

Section Context.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition phi_encoding :=
  pair_encoding (pair_encoding (Pre.ee (Pre.keys c)) (Pre.ee (Pre.keys c)))
    (Pre.eu (Pre.keys c)).
Definition version_key (v : cache_version E U) : U + ((E * U) + ((E * U) + (E * U))) :=
  match v with
  | Initial u => inl u
  | Computed e u => inr (inl (e, u))
  | Inserted e u => inr (inr (inl (e, u)))
  | Merged e u => inr (inr (inr (e, u)))
  end.
Definition version_codes :=
  sum_encoding (Pre.eu (Pre.keys c))
    (sum_encoding (pair_encoding (Pre.ee (Pre.keys c)) (Pre.eu (Pre.keys c)))
      (sum_encoding (pair_encoding (Pre.ee (Pre.keys c)) (Pre.eu (Pre.keys c)))
        (pair_encoding (Pre.ee (Pre.keys c)) (Pre.eu (Pre.keys c))))).
Definition version_encoding : encoding (cache_version E U) :=
  Encoding (fun v => Cost.step ;; encode_c version_codes (version_key v)).

Definition inserted_c (p : plan E U) e u :=
  let* row := Map.find_or_c (Pre.ee (Pre.keys c)) FinSet.empty e (insertions p) in
  FinSet.mem_c (Pre.eu (Pre.keys c)) u row.
Definition inserted p e u := Cost.value (inserted_c p e u).
Definition deleted_c (p : plan E U) e u :=
  let* row := Map.find_or_c (Pre.ee (Pre.keys c)) FinSet.empty e (deletions p) in
  FinSet.mem_c (Pre.eu (Pre.keys c)) u row.
Definition deleted p e u := Cost.value (deleted_c p e u).

(** Extension changes generated occurrences while retaining the original presentation metadata. *)
Definition extended_view (p : plan E U) : Bitvector.t N E U :=
  let original := Pre.expr (Pre.input c) in
  Bitvector.Make (Bitvector.cfg original) (Bitvector.fact_enc original)
    (Bitvector.universe original) (Bitvector.dir original)
    (fun e =>
      Cost.step ;;
      let* generated := Bitvector.gen_c original e in
      let* row := Map.find_or_c (Pre.ee (Pre.keys c)) FinSet.empty e (insertions p) in
      let* added := FinSet.elements_c row in app_c generated added)
    (Bitvector.kill_c original) (Bitvector.boundary_c original).

Definition version_point_c (v : cache_version E U) :=
  match v with
  | Initial _ => Cost.ret (nth_error (Graph.entries (Pre.pg c)) 0)
  | Computed e _ | Inserted e _ | Merged e _ =>
    Cost.step ;; Cost.map (@Some N) (Graph.target_c (Pre.pg c) e)
  end.
Definition version_point v := Cost.value (version_point_c v).

Definition version_written_c e (v : cache_version E U) :=
  match v with
  | Initial _ => Cost.ret false
  | Computed d _ | Inserted d _ | Merged d _ => eqb_c (Pre.ee (Pre.keys c)) e d
  end.
Definition version_written e v := Cost.value (version_written_c e v).

(** Phi reads select every predecessor value from the same old cache. *)
Definition phi_update_c {A} (p : plan E U) incoming parameter
    (old : cache_version E U -> Cost.t (option A)) v :=
  match v with
  | Merged d u =>
    let* same := eqb_c (Pre.ee (Pre.keys c)) d parameter in
    if same then
      let* chosen := Map.get_c phi_encoding ((d, incoming), u) (phi_versions p) in
      Cost.step ;;
      old (match chosen with Some selected => selected | None => v end)
    else Cost.step ;; old v
  | _ => Cost.step ;; old v
  end.
Definition phi_update {A} p incoming parameter (old : cache_version E U -> option A) v :=
  Cost.value (phi_update_c p incoming parameter (Cost.lift (fun _ => 1%N) old) v).

Definition will_c (facts : PreReset.facts B U) key :=
  let* can := PreReset.flag_c c (PreReset.can_available facts) key in
  let* later := PreReset.flag_c c (PreReset.later facts) key in Cost.ret (can && negb later).
Definition will facts key := Cost.value (will_c facts key).
Definition insert_operand_c facts (op : PreFrg.operand B E U) :=
  match PreFrg.operand_version op with
  | PreFrg.Unavailable _ => Cost.ret true
  | PreFrg.Phi b u =>
    let* enabled := will_c facts (b, u) in Cost.ret (negb (PreFrg.real_use op) && negb enabled)
  | _ => Cost.ret false
  end.
Definition insert_operand facts op := Cost.value (insert_operand_c facts op).

(** Positive comparisons pay for every bit they inspect, including supplied dominator clocks. *)
Definition le_c p q :=
  Cost.tick_bits p ;; Cost.tick_bits q ;; Cost.ret (Pos.leb p q).

Definition block_dominates_c d n :=
  let tree := Pre.dom c in
  let* a := Map.get_c positive_encoding d (Dom.tin tree) in
  let* b := Map.get_c positive_encoding n (Dom.tin tree) in
  let* c := Map.get_c positive_encoding n (Dom.tout tree) in
  let* e := Map.get_c positive_encoding d (Dom.tout tree) in
  match a, b, c, e with
  | Some a, Some b, Some c, Some e =>
    let* before := le_c a b in
    let* after := le_c c e in Cost.ret (before && after)
  | _, _, _, _ => Cost.ret false
  end.
Definition block_dominates d n := Cost.value (block_dominates_c d n).

Definition point_dominates_c (index : prepared B BE N E U) q n :=
  let* q := Map.get_c (Pre.en (Pre.keys c)) q (coordinates index) in
  let* n := Map.get_c (Pre.en (Pre.keys c)) n (coordinates index) in
  match q, n with
  | Some q, Some n =>
    let* same := positive_eqb_c (location_id q) (location_id n) in
    if same then le_c (location_rank q) (location_rank n)
    else block_dominates_c (location_id q) (location_id n)
  | _, _ => Cost.ret false
  end.
Definition point_dominates index q n := Cost.value (point_dominates_c index q n).

Fixpoint number_points_c b id rank (ns : list N) : Cost.t (list (N * location B)) :=
  match ns with
  | [] => Cost.ret []
  | n :: rest =>
    Cost.step ;;
    let* tail := number_points_c b id (Pos.succ rank) rest in
    Cost.ret ((n, Location b id rank) :: tail)
  end.

Definition describe_block_c b :=
  let* id := Prepared.id_of_c (Pre.blocks c) b in
  Cost.step ;;
  let* ns := SsaPoints.points_in_block_c (Pre.points (Pre.input c)) b in
  Cost.ret (b, (id, ns)).

Definition block_entries_c (descriptions : list (B * (option positive * list N))) :=
  filter_map_c (fun description =>
    let '(b, (id, ns)) := description in
    Cost.ret (option_map (fun id => (id, (b, ns))) id)) descriptions.
Definition block_entries descriptions := Cost.value (block_entries_c descriptions).

Definition point_entries_c (descriptions : list (B * (option positive * list N))) :=
  fw_flat_map_c (fun description =>
    let '(b, (id, ns)) := description in
    match id with
    | None => Cost.ret []
    | Some id => number_points_c b id 1%positive ns
    end) descriptions.
Definition point_entries descriptions := Cost.value (point_entries_c descriptions).
Definition block_descriptions_c := map_c describe_block_c (Graph.nodes (Pre.bg c)).
Definition block_descriptions := Cost.value block_descriptions_c.

Definition point_layout_c :=
  let* descriptions := block_descriptions_c in
  let* blocks := block_entries_c descriptions in
  let* positions := point_entries_c descriptions in
  let* blocks := Map.of_list_c positive_encoding blocks in
  let* positions := Map.of_list_c (Pre.en (Pre.keys c)) positions in
  Cost.ret (blocks, positions).
Definition point_layout := Cost.value point_layout_c.

(** The forest uses the supplied block-parent map and one source index, without another DFS engine. *)
Definition forest_c :=
  let* parent_pairs := Map.elements_c (Dom.idom (Pre.dom c)) in
  let* children := Index.group_by_c positive_encoding
    (Cost.lift (fun _ => 1%N) (@snd positive positive)) parent_pairs in
  let* names := Map.elements_c (Intern.inverse (Prepared.names (Pre.blocks c))) in
  let* nodes := map_c (fun pair => Cost.ret (fst pair)) names in
  let g := Graph.Make (Prepared.entry_ids (Pre.blocks c)) nodes
    (fun id => Index.find_c positive_encoding id children)
    (Cost.lift (fun _ => 1%N) (@snd positive positive))
    (Cost.lift (fun _ => 1%N) (@fst positive positive)) in
  Prepared.prepare_c positive_encoding g.

Definition initial_step_c names (frames : scope N E U) d :=
  match d with
  | PreFrg.Initial u =>
    Cost.step ;;
    let* enabled := Pre.initial_c (Pre.input c) u in
    if enabled then
      let* id := Intern.find_c (PreFrg.version_encoding c) d names in
      match id, nth_error (Graph.entries (Pre.pg c)) 0 with
      | Some id, Some n => Map.set_c positive_encoding id (Slot (Initial u) n) frames
      | _, _ => Cost.ret frames
      end
    else Cost.ret frames
  | _ => Cost.ret frames
  end.
Definition initial_step names frames d := Cost.value (initial_step_c names frames d).
Definition initial_scope_c names versions := fold_left_c (initial_step_c names) versions Map.empty.
Definition initial_frames names versions := Cost.value (initial_scope_c names versions).

Definition phi_pair_c names facts key :=
  let* enabled := will_c facts key in
  if enabled then
    let* id := Intern.find_c (PreFrg.version_encoding c)
      (PreFrg.Phi (fst key) (snd key)) names in
    Cost.step ;;
    let* parameter := SsaPoints.parameter_edge_c (Pre.points (Pre.input c)) (fst key) in
    Cost.step ;;
    let* n := Graph.target_c (Pre.pg c) parameter in
    Cost.ret (option_map (fun id => (n, (id, Slot (Merged parameter (snd key)) n))) id)
  else Cost.ret None.
Definition phi_pair names facts key := Cost.value (phi_pair_c names facts key).
Definition phi_pairs_c names facts keys := filter_map_c (phi_pair_c names facts) keys.

Definition argument_pair_c names edges binding :=
  let '(((b, u), be), op) := binding in
  let* incoming := Map.get_c (Pre.ebe (Pre.keys c)) be edges in
  match incoming with
  | None => Cost.ret None
  | Some incoming =>
    Cost.step ;;
    let* n := Graph.source_c (Pre.pg c) incoming in
    Cost.step ;;
    let* parameter := SsaPoints.parameter_edge_c (Pre.points (Pre.input c)) b in
    let* id := Intern.find_c (PreFrg.version_encoding c) (PreFrg.operand_version op) names in
    Cost.ret (Some (n, Argument b u be incoming parameter op id))
  end.
Definition argument_pair names edges binding := Cost.value (argument_pair_c names edges binding).
Definition argument_pairs_c names edges links := filter_map_c (argument_pair_c names edges) links.

Definition occurrence_pair_c names (binding : E * PreFrg.version B E U) :=
  let* id := Intern.find_c (PreFrg.version_encoding c) (snd binding) names in
  Cost.ret (fst binding, id).
Definition occurrence_index_c names (f : PreFrg.frg B BE E U) :=
  let* occurrences := Map.elements_c (PreFrg.occurrences f) in
  let* pairs := map_c (occurrence_pair_c names) occurrences in
  Map.of_list_c (Pre.ee (Pre.keys c)) pairs.
Definition occurrence_index names f := Cost.value (occurrence_index_c names f).

Definition prepare_c (f : PreFrg.frg B BE E U) facts :=
  let* layout := point_layout_c in
  let* names := Intern.of_list_c (PreFrg.version_encoding c) (PreFrg.versions f) in
  let* initial := initial_scope_c names (PreFrg.versions f) in
  let* occurrence_index := occurrence_index_c names f in
  let* keys := FinSet.elements_c (PreFrg.phis f) in
  let* phis := phi_pairs_c names facts keys in
  let* phi_index := Index.group_by_c (Pre.en (Pre.keys c))
    (Cost.lift (fun _ => 1%N) (@fst N (positive * slot N E U))) phis in
  let* edges := PreFrameEdges.point_edge_index_c c in
  let* links := Map.elements_c (PreFrg.operands f) in
  let* args := argument_pairs_c names edges links in
  let* argument_index := Index.group_by_c (Pre.en (Pre.keys c))
    (Cost.lift (fun _ => 1%N) (@fst N (argument B BE E U))) args in
  let* forest := forest_c in
  let* search := SearchRun.run_c forest Visitor.noop (Scope.Make FinSet.empty None)
    (Prepared.entry_ids forest) tt in
  let* order := Prepared.present_c (Prepared.name_of_c forest) (Search.preorder (fst search)) in
  let* count := length_c order in
  let* budget := Prepared.budget_c count in
  Cost.ret (Prepared (fst layout) (snd layout) names occurrence_index phi_index argument_index
    initial forest order budget).
Definition prepare f facts := Cost.value (prepare_c f facts).

Definition available_c (index : prepared B BE N E U) (frames : scope N E U) id u n :=
  let* found := Map.get_c positive_encoding id frames in
  match found with
  | None => Cost.ret None
  | Some definition =>
    let* same := eqb_c (Pre.eu (Pre.keys c)) (version_expr (selected definition)) u in
    if same then
      let* dominates := point_dominates_c index (definition_point definition) n in
      Cost.ret (if dominates then Some (selected definition) else None)
    else Cost.ret None
  end.
Definition available index frames id u n := Cost.value (available_c index frames id u n).

Definition select_c (p : plan E U) parameter incoming u v :=
  let* chosen := Map.set_c phi_encoding ((parameter, incoming), u) v (phi_versions p) in
  Cost.ret (Plan (insertions p) (deletions p) (reload_versions p) chosen).
Definition select p parameter incoming u v := Cost.value (select_c p parameter incoming u v).

Definition occurrence_c (index : prepared B BE N E U) n (state : scope N E U * plan E U) e :=
  let '(frames, p) := state in
  Cost.step ;;
  let* recomputed := Pre.recomputed_c (Pre.input c) e in
  let* class := Map.get_c (Pre.ee (Pre.keys c)) e (occurrence_classes index) in
  match recomputed, class with
  | Some u, Some (Some id) =>
    Cost.step ;;
    let* pure := Pre.pure_c (Pre.input c) u in
    if pure then
      let* found := available_c index frames id u n in
      match found with
      | Some v =>
        let* reloads := Map.set_c (Pre.ee (Pre.keys c)) e v (reload_versions p) in
        Cost.ret (frames, Plan (insertions p) (deletions p) reloads (phi_versions p))
      | None =>
        Cost.step ;;
        let* target := Graph.target_c (Pre.pg c) e in
        let* frames := Map.set_c positive_encoding id (Slot (Computed e u) target) frames in
        Cost.ret (frames, p)
      end
    else Cost.ret state
  | _, _ => Cost.ret state
  end.
Definition occurrence index n state e := Cost.value (occurrence_c index n state e).

Definition argument_c (index : prepared B BE N E U) facts frames (p : plan E U)
    (entry : N * argument B BE E U) :=
  let '(n, arg) := entry in
  let u := argument_expression arg in
  let* enabled := will_c facts (argument_block arg, u) in
  if enabled then
    Cost.step ;;
    let* translated := Pre.translate_c (Pre.input c) (argument_block_edge arg) u in
    match translated with
    | None => Cost.ret p
    | Some translated =>
      let* insert := insert_operand_c facts (argument_operand arg) in
      if insert then
        Cost.step ;;
        let* pure := Pre.pure_c (Pre.input c) translated in
        let* killed := Pre.killed_c c (argument_incoming arg) translated in
        if pure && negb killed then
          select_c p (argument_parameter arg) (argument_incoming arg) u
            (Inserted (argument_incoming arg) translated)
        else Cost.ret p
      else
        match argument_class arg with
        | None => Cost.ret p
        | Some id =>
          let* found := available_c index frames id translated n in
          match found with
          | None => Cost.ret p
          | Some v => select_c p (argument_parameter arg) (argument_incoming arg) u v
          end
        end
    end
  else Cost.ret p.
Definition argument_step index facts frames p entry :=
  Cost.value (argument_c index facts frames p entry).

Definition node_c (index : prepared B BE N E U) facts
    (state : scope N E U * plan E U) n :=
  let* phis := Index.find_c (Pre.en (Pre.keys c)) n (phi_rows index) in
  let* frames := fold_left_c (fun frames entry =>
    Map.set_c positive_encoding (fst (snd entry)) (snd (snd entry)) frames) phis (fst state) in
  let* args := Index.find_c (Pre.en (Pre.keys c)) n (argument_rows index) in
  let* p := fold_left_c (argument_c index facts frames) args (snd state) in
  let* id := Prepared.id_of_c (Pre.point_graph c) n in
  let* edges := match id with
    | None => Cost.ret []
    | Some id => Prepared.succ_edges_c (Pre.point_graph c) id
    end in
  fold_left_c (fun state edge => occurrence_c index n state (fst edge)) edges (frames, p).
Definition node index facts state n := Cost.value (node_c index facts state n).

Definition block_c (index : prepared B BE N E U) facts frames p ns :=
  fold_left_c (node_c index facts) ns (frames, p).
Definition block index facts frames p ns := Cost.value (block_c index facts frames p ns).

Definition step_c (index : prepared B BE N E U) facts (state : work N E U)
    : Cost.t (work N E U + result E U) :=
  match pending state with
  | [] => Cost.ret (inr (Result (current_plan state)
      (if missing_block state then MissingBlock else Finished)))
  | id :: rest =>
    let* body := Map.get_c positive_encoding id (block_points index) in
    match body with
    | None => Cost.ret (inl (Work rest (snapshots state) (current_plan state) true))
    | Some (_, ns) =>
      let* parent := Map.get_c positive_encoding id (Dom.idom (Pre.dom c)) in
      let* inherited := match parent with
        | None => Cost.ret (initial_scope index)
        | Some parent =>
          Map.find_or_c positive_encoding (initial_scope index) parent (snapshots state)
        end in
      let* finished := block_c index facts inherited (current_plan state) ns in
      let* outputs := Map.set_c positive_encoding id (fst finished) (snapshots state) in
      Cost.ret (inl (Work rest outputs (snd finished) (missing_block state)))
    end
  end.
Definition step index facts state := Cost.value (step_c index facts state).

Definition run_c (index : prepared B BE N E U) facts :=
  let* answer := CostLoop.iterate (step_c index facts) (budget index)
    (Work (order index) Map.empty empty_plan false) in
  Cost.ret (match answer with
    | inl unfinished => Result (current_plan unfinished) OutOfFuel
    | inr finished => finished
    end).
Definition run index facts := Cost.value (run_c index facts).

Definition add_expression_c (rows : Map.t E (FinSet.t U)) (item : E * U) :=
  let* old := Map.find_or_c (Pre.ee (Pre.keys c)) FinSet.empty (fst item) rows in
  let* row := FinSet.add_c (Pre.eu (Pre.keys c)) (snd item) old in
  Map.set_c (Pre.ee (Pre.keys c)) (fst item) row rows.

(** Materialisation scans only emitted phi selections and reloads, never program edges per version. *)
Definition materialize_c (p : plan E U) :=
  let* selected := Map.elements_c (phi_versions p) in
  let* inserted := filter_map_c (fun binding =>
    Cost.ret (match snd binding with Inserted e u => Some (e, u) | _ => None end)) selected in
  let* insertions := fold_left_c add_expression_c inserted Map.empty in
  let* reloads := Map.elements_c (reload_versions p) in
  let* deleted := filter_map_c (fun binding =>
    Cost.step ;;
    let* recomputed := Pre.recomputed_c (Pre.input c) (fst binding) in
    Cost.ret (option_map (fun u => (fst binding, u)) recomputed)) reloads in
  let* deletions := fold_left_c add_expression_c deleted Map.empty in
  Cost.ret (Plan insertions deletions (reload_versions p) (phi_versions p)).
Definition materialize p := Cost.value (materialize_c p).

(** Finalization retains its actual loop result and materialises the same producer's selected maps. *)
Definition finalize_c f facts :=
  let* index := prepare_c f facts in
  let* finished := run_c index facts in
  let* p := materialize_c (output finished) in
  Cost.ret (Result p (reason finished)).
Definition finalize f facts := Cost.value (finalize_c f facts).

(** The plan projection shares all preparation, decisions and output maps with detailed finalization. *)
Definition place_c f facts := Cost.map output (finalize_c f facts).
Definition place f facts := Cost.value (place_c f facts).

(** * Producer observations *)

(** Tagged cache definitions retain their original edge and expression identities. *)
Theorem version_encoding_laws :
  Pre.laws c -> encoding_laws version_encoding.
Proof.
  intro Hlaw.
  assert (Hpair : encoding_laws (pair_encoding (Pre.ee (Pre.keys c)) (Pre.eu (Pre.keys c)))).
  { apply pair_encoding_laws.
    - exact (Pre.ee_laws c (Pre.graphs c Hlaw)).
    - exact (Pre.eu_laws c (Pre.graphs c Hlaw)). }
  assert (Hcodes : encoding_laws version_codes).
  { apply sum_encoding_laws; [exact (Pre.eu_laws c (Pre.graphs c Hlaw))|].
    apply sum_encoding_laws; [exact Hpair|]. apply sum_encoding_laws; exact Hpair. }
  constructor. intros x y Heq.
  change (encode version_codes (version_key x) = encode version_codes (version_key y)) in Heq.
  apply (encode_injective Hcodes) in Heq.
  destruct x, y; cbn [version_key] in Heq; inversion Heq; reflexivity.
Qed.

(** Insertion lookup defaults to the empty row without changing the original membership meaning. *)
Theorem inserted_equation p e u :
  inserted p e u = FinSet.mem (Pre.eu (Pre.keys c)) u
    (Map.find_or (Pre.ee (Pre.keys c)) FinSet.empty e (insertions p)).
Proof.
  unfold inserted, inserted_c. rewrite Cost.value_bind. reflexivity.
Qed.

(** Deletion lookup defaults to the empty row without changing the original membership meaning. *)
Theorem deleted_equation p e u :
  deleted p e u = FinSet.mem (Pre.eu (Pre.keys c)) u
    (Map.find_or (Pre.ee (Pre.keys c)) FinSet.empty e (deletions p)).
Proof.
  unfold deleted, deleted_c. rewrite Cost.value_bind. reflexivity.
Qed.

(** Cache definitions become available at entry or at their actual defining edge's target. *)
Theorem version_point_equation v :
  version_point v = match v with
    | Initial _ => nth_error (Graph.entries (Pre.pg c)) 0
    | Computed e _ | Inserted e _ | Merged e _ => Some (Graph.target (Pre.pg c) e)
    end.
Proof.
  destruct v; unfold version_point, version_point_c; autorewrite with galois_cost; reflexivity.
Qed.

(** The translated phi reads its selected predecessor from the same old cache. *)
Theorem phi_update_equation {A} p incoming parameter (old : cache_version E U -> option A) v :
  phi_update p incoming parameter old v =
    match v with
    | Merged d u =>
      if eqb (Pre.ee (Pre.keys c)) d parameter then
        match Map.get phi_encoding ((d, incoming), u) (phi_versions p) with
        | Some chosen => old chosen
        | None => old v
        end
      else old v
    | _ => old v
    end.
Proof.
  destruct v as [u|e u|e u|d u]; unfold phi_update, phi_update_c;
    autorewrite with galois_cost; try reflexivity.
  fold (eqb (Pre.ee (Pre.keys c)) d parameter).
  destruct (eqb (Pre.ee (Pre.keys c)) d parameter); [|reflexivity].
  rewrite Cost.value_bind.
  fold (Map.get phi_encoding ((d, incoming), u) (phi_versions p)).
  destruct (Map.get phi_encoding ((d, incoming), u) (phi_versions p));
    autorewrite with galois_cost; reflexivity.
Qed.

(** Enabled phis are precisely can-available sites whose later flag was reset. *)
Theorem will_equation facts key :
  will facts key =
    PreReset.flag c (PreReset.can_available facts) key &&
      negb (PreReset.flag c (PreReset.later facts) key).
Proof.
  unfold will, will_c. rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** The original insertion decision distinguishes unavailable inputs and unused disabled phis. *)
Theorem insert_operand_equation facts op :
  insert_operand facts op =
    match PreFrg.operand_version op with
    | PreFrg.Unavailable _ => true
    | PreFrg.Phi b u => negb (PreFrg.real_use op) && negb (will facts (b, u))
    | _ => false
    end.
Proof.
  unfold insert_operand, insert_operand_c.
  destruct (PreFrg.operand_version op); autorewrite with galois_cost; reflexivity.
Qed.

(** The charged positive comparison returns the standard nonstrict order test. *)
Theorem le_equation p q : Cost.value (le_c p q) = Pos.leb p q.
Proof.
  unfold le_c. autorewrite with galois_cost. reflexivity.
Qed.

(** Block dominance uses only the supplied tree's interval observations. *)
Theorem block_dominates_equation d n :
  block_dominates d n =
    match Map.get positive_encoding d (Dom.tin (Pre.dom c)),
      Map.get positive_encoding n (Dom.tin (Pre.dom c)),
      Map.get positive_encoding n (Dom.tout (Pre.dom c)),
      Map.get positive_encoding d (Dom.tout (Pre.dom c)) with
    | Some a, Some b, Some c, Some e => Pos.leb a b && Pos.leb c e
    | _, _, _, _ => false
    end.
Proof.
  unfold block_dominates, block_dominates_c. rewrite !Cost.value_bind.
  fold (Map.get positive_encoding d (Dom.tin (Pre.dom c))).
  fold (Map.get positive_encoding n (Dom.tin (Pre.dom c))).
  fold (Map.get positive_encoding n (Dom.tout (Pre.dom c))).
  fold (Map.get positive_encoding d (Dom.tout (Pre.dom c))).
  destruct (Map.get positive_encoding d (Dom.tin (Pre.dom c))),
    (Map.get positive_encoding n (Dom.tin (Pre.dom c))),
    (Map.get positive_encoding n (Dom.tout (Pre.dom c))),
    (Map.get positive_encoding d (Dom.tout (Pre.dom c)));
    autorewrite with galois_cost; rewrite ?le_equation; reflexivity.
Qed.

(** Cached point dominance compares instruction ranks locally and block dominance across owners. *)
Theorem point_dominates_equation index q n :
  point_dominates index q n =
    match Map.get (Pre.en (Pre.keys c)) q (coordinates index),
      Map.get (Pre.en (Pre.keys c)) n (coordinates index) with
    | Some q, Some n =>
      if Pos.eqb (location_id q) (location_id n)
      then Pos.leb (location_rank q) (location_rank n)
      else block_dominates (location_id q) (location_id n)
    | _, _ => false
    end.
Proof.
  unfold point_dominates, point_dominates_c. rewrite !Cost.value_bind.
  fold (Map.get (Pre.en (Pre.keys c)) q (coordinates index)).
  fold (Map.get (Pre.en (Pre.keys c)) n (coordinates index)).
  destruct (Map.get (Pre.en (Pre.keys c)) q (coordinates index)) as [qloc|],
    (Map.get (Pre.en (Pre.keys c)) n (coordinates index)) as [nloc|];
    [|reflexivity|reflexivity|reflexivity].
  rewrite Cost.value_bind, positive_eqb_equation.
  destruct (Pos.eqb (location_id qloc) (location_id nloc)); [apply le_equation|reflexivity].
Qed.

(** Point numbering visits the ordered source list with one positive successor per occurrence. *)
Theorem number_points_equation b id rank ns :
  Cost.value (number_points_c b id rank ns) =
    match ns with
    | [] => []
    | n :: rest => (n, Location b id rank) ::
        Cost.value (number_points_c b id (Pos.succ rank) rest)
    end.
Proof.
  destruct ns; cbn [number_points_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Block descriptions retain the original supplied ID lookup and the one syntax-reader result. *)
Theorem describe_block_equation b :
  Cost.value (describe_block_c b) =
    (b, (Prepared.id_of (Pre.blocks c) b,
      SsaPoints.points_in_block (Pre.points (Pre.input c)) b)).
Proof.
  unfold describe_block_c. rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** The complete description inventory is enumerated once in original block order. *)
Theorem block_descriptions_equation :
  block_descriptions = map (fun b =>
    (b, (Prepared.id_of (Pre.blocks c) b,
      SsaPoints.points_in_block (Pre.points (Pre.input c)) b))) (Graph.nodes (Pre.bg c)).
Proof.
  unfold block_descriptions, block_descriptions_c. rewrite value_map_c.
  apply map_ext. apply describe_block_equation.
Qed.

(** Block entries retain successful dense names and preserve ordered point lists. *)
Theorem block_entries_equation descriptions :
  block_entries descriptions =
    filter_map (fun description =>
      let '(b, (id, ns)) := description in option_map (fun id => (id, (b, ns))) id)
      descriptions.
Proof.
  unfold block_entries, block_entries_c. rewrite value_filter_map_c.
  apply filter_map_ext. intros [b [id ns]]. reflexivity.
Qed.

(** Point entries flatten each successfully named source block's actual ordered numbering. *)
Theorem point_entries_equation descriptions :
  point_entries descriptions =
    flat_map (fun description =>
      let '(b, (id, ns)) := description in
      match id with
      | None => []
      | Some id => Cost.value (number_points_c b id 1%positive ns)
      end) descriptions.
Proof.
  unfold point_entries, point_entries_c. rewrite fw_flat_map_value.
  apply flat_map_ext. intros [b [id ns]]. destruct id; reflexivity.
Qed.

(** Both layout maps are built from the same single description inventory. *)
Theorem point_layout_equation :
  point_layout =
    (Map.of_list positive_encoding (block_entries block_descriptions),
      Map.of_list (Pre.en (Pre.keys c)) (point_entries block_descriptions)).
Proof.
  unfold point_layout, point_layout_c. rewrite !Cost.value_bind, Cost.value_ret.
  reflexivity.
Qed.

(** Initial-scope updates install only explicitly enabled entry definitions. *)
Theorem initial_step_equation names frames d :
  initial_step names frames d =
    match d with
    | PreFrg.Initial u =>
      if Pre.initial c u then
        match Intern.find (PreFrg.version_encoding c) d names,
          nth_error (Graph.entries (Pre.pg c)) 0 with
        | Some id, Some n => Map.set positive_encoding id (Slot (Initial u) n) frames
        | _, _ => frames
        end
      else frames
    | _ => frames
    end.
Proof.
  unfold initial_step, initial_step_c. destruct d; [reflexivity| |reflexivity|reflexivity].
  rewrite !Cost.value_bind. fold (Pre.initial c u).
  destruct (Pre.initial c u); [|reflexivity].
  rewrite Cost.value_bind.
  fold (Intern.find (PreFrg.version_encoding c) (PreFrg.Initial u) names).
  destruct (Intern.find (PreFrg.version_encoding c) (PreFrg.Initial u) names),
    (nth_error (Graph.entries (Pre.pg c)) 0); reflexivity.
Qed.

(** Initial materialisation is the value fold of the same charged updates. *)
Theorem initial_frames_equation names versions :
  initial_frames names versions = fold_left (initial_step names) versions Map.empty.
Proof.
  unfold initial_frames, initial_scope_c. apply value_fold_left_c.
Qed.

(** Dense occurrence classes retain each original selected FRG definition. *)
Theorem occurrence_index_equation names f :
  occurrence_index names f = Map.of_list (Pre.ee (Pre.keys c))
    (map (fun binding => (fst binding,
      Intern.find (PreFrg.version_encoding c) (snd binding) names))
      (Map.elements (PreFrg.occurrences f))).
Proof.
  unfold occurrence_index, occurrence_index_c. rewrite !Cost.value_bind, value_map_c.
  change (Map.of_list (Pre.ee (Pre.keys c))
    (map (fun binding => Cost.value (occurrence_pair_c names binding))
      (Map.elements (PreFrg.occurrences f))) =
    Map.of_list (Pre.ee (Pre.keys c))
      (map (fun binding => (fst binding,
        Intern.find (PreFrg.version_encoding c) (snd binding) names))
        (Map.elements (PreFrg.occurrences f)))).
  reflexivity.
Qed.

(** Phi preparation retains the enabled site, class identity and actual parameter target. *)
Theorem phi_pair_equation names facts key :
  phi_pair names facts key =
    if will facts key then
      option_map (fun id =>
        let parameter := SsaPoints.parameter_edge (Pre.points (Pre.input c)) (fst key) in
        let n := Graph.target (Pre.pg c) parameter in
        (n, (id, Slot (Merged parameter (snd key)) n)))
        (Intern.find (PreFrg.version_encoding c) (PreFrg.Phi (fst key) (snd key)) names)
    else None.
Proof.
  unfold phi_pair, phi_pair_c. rewrite Cost.value_bind. fold (will facts key).
  destruct (will facts key); [|reflexivity].
  rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** Each argument description retains its exact original crossing and class lookup. *)
Theorem argument_pair_equation names edges b u be op :
  argument_pair names edges (((b, u), be), op) =
    match Map.get (Pre.ebe (Pre.keys c)) be edges with
    | None => None
    | Some incoming =>
      Some (Graph.source (Pre.pg c) incoming,
        Argument b u be incoming (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b)
          op (Intern.find (PreFrg.version_encoding c) (PreFrg.operand_version op) names))
    end.
Proof.
  unfold argument_pair, argument_pair_c. rewrite Cost.value_bind.
  fold (Map.get (Pre.ebe (Pre.keys c)) be edges).
  destruct (Map.get (Pre.ebe (Pre.keys c)) be edges); [|reflexivity].
  rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** * Independent correctness predicates *)

(** Regular cache definitions exclude insertions, which are selected only on their own edge. *)
Definition regular (v : cache_version E U) : Prop :=
  match v with Inserted _ _ => False | _ => True end.

(** A stored slot retains a regular origin and the actual defining point of that origin. *)
Definition scope_valid (frames : scope N E U) : Prop :=
  Map.wf positive_encoding frames /\
  forall id definition, Map.get positive_encoding id frames = Some definition ->
    regular (selected definition) /\ version_point (selected definition) = Some (definition_point definition).

(** Reload safety retains the original expression and point-dominance obligation. *)
Definition reload_property e v : Prop :=
  exists u q, Pre.recomputed c e = Some u /\ Pre.pure c u = true /\ version_expr v = u /\
    version_point v = Some q /\ dominates (Pre.pg c) q (Graph.source (Pre.pg c) e).

(** Phi safety retains predecessor identity, translation and inserted-or-dominating provenance. *)
Definition phi_property parameter incoming u v : Prop :=
  exists b be translated,
    Map.get (Pre.ebe (Pre.keys c)) be (PreFrameEdges.point_edge_index c) = Some incoming /\
    Graph.target (Pre.bg c) be = b /\
    parameter = SsaPoints.parameter_edge (Pre.points (Pre.input c)) b /\
    Pre.translate c be u = Some translated /\ version_expr v = translated /\
    ((v = Inserted incoming translated /\ Pre.pure c translated = true /\
        Pre.killed c incoming translated = false) \/
      (regular v /\ exists q, version_point v = Some q /\
        dominates (Pre.pg c) q (Graph.source (Pre.pg c) incoming))).

(** Finalization retains canonical selected maps and the full original safety provenance. *)
Record finalize_invariant (state : scope N E U * plan E U) : Prop := FinalizeInvariant {
  scope_correct : scope_valid (fst state);
  reloads_wf : Map.wf (Pre.ee (Pre.keys c)) (reload_versions (snd state));
  phis_wf : Map.wf phi_encoding (phi_versions (snd state));
  reloads_safe : forall e v, Map.get (Pre.ee (Pre.keys c)) e
    (reload_versions (snd state)) = Some v -> reload_property e v;
  phis_safe : forall parameter incoming u v, Map.get phi_encoding ((parameter, incoming), u)
    (phi_versions (snd state)) = Some v -> phi_property parameter incoming u v
}.

End Context.

End PreFinalize.
