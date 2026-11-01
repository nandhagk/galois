(** * Whole PRE source and old-state semantics

    The adapters retain original behavior through synthetic entry points and snapshots.
    For example, a fresh entry value reads the saved original state.
    Builds on: PRE phase models, graph audits and SSA views. *)

From Stdlib Require Import Arith Bool List PArith.
From Galois.Analyses Require Export AnalysesAuditPreFamily AnalysesAuditPreFinite
  AnalysesAuditPreFrg AnalysesAuditPrePlan AnalysesAuditPreSolve AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSsaPre AnalysesSsaPreGraph
  AnalysesSsaPreSemantics.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditTrie CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditDominators
  GraphAuditFrontier GraphAuditLengauerTarjan GraphAuditSemiDominators GraphAuditVirtual GraphCore
  GraphDfs GraphDominance GraphDominators GraphFrontier GraphLengauerTarjan GraphPrepare
  GraphSemiDominators.
From Galois.Views Require Import ViewsGraph ViewsSemantics ViewsSsa ViewsSsaPoints.
Import List.ListNotations.

(* Definition source: PreVirtualSemantics.v *)

(** * Synthetic entry graph and snapshot semantics *)

Definition audit_entry_point_graph {N E} (EN : encoding N) (g : Graph.t N E)
    : Graph.t (N + bool) (E + (unit + N)) :=
  Graph.Make [inr false] (map (@inl N bool) (Graph.nodes g) ++ [inr false; inr true])
    (fun p =>
      match p with
      | inl n => map (@inl E (unit + N)) (Graph.out g n)
      | inr false => [inr (inl tt)]
      | inr true => map (fun n => inr (inr n)) (virtual_entries EN g)
      end)
    (fun e =>
      match e with
      | inl edge => inl (Graph.source g edge)
      | inr (inl _) => inr false
      | inr (inr _) => inr true
      end)
    (fun e =>
      match e with
      | inl edge => inl (Graph.target g edge)
      | inr (inl _) => inr true
      | inr (inr n) => inl n
      end).

Definition audit_entry_point_semantics {S O} (m : semantics S O) : semantics (S + (S + S)) O :=
  Semantics (fun s =>
    match s with
    | inr (inl x) => initial m x
    | _ => False end)
    (fun s events t =>
      match s, t with
      | inr (inl x), inr (inr y) => x = y /\ events = []
      | inr (inr x), inl y => x = y /\ events = []
      | inl x, inl y => step m x events y
      | _, _ => False
      end).

Definition audit_entry_point_endings {S} (en : endings S) : endings (S + (S + S)) :=
  Endings (fun s =>
    match s with
    | inl x => final en x
    | _ => False end)
    (fun s =>
      match s with
      | inl x => trapped en x
      | _ => False end)
    (fun s =>
      match s with
      | inl x => stopped en x
      | _ => False end).

Definition audit_entry_point_view {S O N E} (EN : encoding N) (gv : graph_view S O N E)
    : graph_view (S + (S + S)) O (N + bool) (E + (unit + N)) :=
  GraphView (audit_entry_point_graph EN (cfg gv))
    (fun s =>
      match s with
      | inl x => inl (point gv x)
      | inr (inl _) => inr false
      | inr (inr _) => inr true
      end)
    (fun s events t edge =>
      match s, t, edge with
      | inr (inl x), inr (inr y), inr (inl _) => x = y /\ events = []
      | inr (inr x), inl y, inr (inr n) => x = y /\ events = [] /\ n = point gv x
      | inl x, inl y, inl e => taken gv x events y e
      | _, _, _ => False
      end)
    (fun s events t =>
      match s, t with
      | inl x, inl y => stays gv x events y
      | _, _ => False
      end).

(** At block level the parameter instruction stays inside the synthetic entry block. *)
Definition audit_entry_block_view {S O B BE} (EB : encoding B) (gv : graph_view S O B BE)
    : graph_view (S + (S + S)) O (B + unit) (BE + B) :=
  GraphView (virtual_graph EB (cfg gv))
    (fun s =>
      match s with
      | inl x => inl (point gv x)
      | _ => inr tt end)
    (fun s events t edge =>
      match s, t, edge with
      | inr (inr x), inl y, inr b => x = y /\ events = [] /\ b = point gv x
      | inl x, inl y, inl e => taken gv x events y e
      | _, _, _ => False
      end)
    (fun s events t =>
      match s, t with
      | inr (inl x), inr (inr y) => x = y /\ events = []
      | inl x, inl y => stays gv x events y
      | _, _ => False
      end).

(** The block projection classifies both administrative steps under the original view laws. *)
Definition audit_entry_block_view_statement : Prop :=
  forall S O B BE (EB : encoding B) (m : semantics S O) (gv : graph_view S O B BE),
    graph_view_laws m gv ->
    graph_view_laws (audit_entry_point_semantics m) (audit_entry_block_view EB gv).

(** The two administrative steps preserve the original graph view and all behavior observations. *)
Definition audit_entry_point_semantics_statement : Prop :=
  forall S O N E (EN : encoding N) (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E), graph_view_laws m gv ->
    graph_view_laws (audit_entry_point_semantics m) (audit_entry_point_view EN gv) /\
    forall s, same_behaviour m en s (audit_entry_point_semantics m)
      (audit_entry_point_endings en) (inr (inl s)).

(** A ready input remains ready with its two tagged entry points and distinct entry edges. *)
Definition audit_entry_point_ready_statement : Prop :=
  forall N E (EN : encoding N) (g : Graph.t N E) (p : prepared EN g),
    ready EN g p ->
    ready (sum_encoding EN bool_encoding) (audit_entry_point_graph EN g)
      (prepare (sum_encoding EN bool_encoding) (audit_entry_point_graph EN g)).

(** Every entry-to-point path is preserved after the two tagged administrative edges. *)
Definition audit_entry_point_path_statement : Prop :=
  forall N E (EN : encoding N) (g : Graph.t N E) start target es,
    In start (Graph.entries g) ->
    (path g start es target <->
      path (audit_entry_point_graph EN g) (inr false)
        (inr (inl tt) :: inr (inr start) :: map (@inl E (unit + N)) es) (inl target)).

(** A path from the new root to an original point has one original entry and suffix. *)
Definition audit_entry_point_path_complete_statement : Prop :=
  forall N E (EN : encoding N) (g : Graph.t N E) path_edges target,
    path (audit_entry_point_graph EN g) (inr false) path_edges (inl target) ->
    exists start es, In start (Graph.entries g) /\
      path_edges = inr (inl tt) :: inr (inr start) :: map (@inl E (unit + N)) es /\
      path g start es target.

Definition audit_entry_values_of {B BE N E V} (EB : encoding B)
    (s : ssa_points B BE N E V) : list (B * V) :=
  flat_map (fun b => map (fun x => (b,x)) (block_params s b))
    (virtual_entries EB (block_graph s)).

Definition audit_entry_construct_points {B BE N E V} (EB : encoding B) (EN : encoding N)
    (EV : encoding V) (s : ssa_points B BE N E V)
    : ssa_points (B + unit) (BE + B) (N + bool) (E + (unit + N)) (V + (B * V)) :=
  let old := @inl V (B * V) in
  let fresh := @inr V (B * V) in
  let inputs := audit_entry_values_of EB s in
  let roots := map fresh inputs in
  let fresh_index := FinSet.of_list (pair_encoding EB EV) inputs in
  let parameters := fun b =>
    match b with
    | inl old_b => map old (block_params s old_b)
    | inr _ => roots
    end in
  let arguments := fun e =>
    match e with
    | inl old_e => map old (block_edge_args s old_e)
    | inr b => map (fun x => fresh (b,x)) (block_params s b)
    end in
  SsaPoints
    (PointUses (audit_entry_point_graph EN (live_graph (point_model s)))
      (fun e =>
        match e with
        | inl edge => map old (edge_use (point_model s) edge)
        | inr (inl _) => []
        | inr (inr n) => arguments (inr (block_of_point s n))
        end)
      (fun e =>
        match e with
        | inl edge => map old (edge_def (point_model s) edge)
        | inr (inl _) => roots
        | inr (inr _) => []
        end)
      (fun n =>
        match n with
        | inl point => map old (exit_use (point_model s) point)
        | inr _ => []
        end))
    (virtual_graph EB (block_graph s))
    (fun b =>
      match b with
      | inl old_b => map (@inl N bool) (points_in_block s old_b)
      | inr _ => [inr false; inr true] end)
    (fun b =>
      match b with
      | inl old_b => map (@inl E (unit + N)) (instruction_edges s old_b)
      | inr _ => [inr (inl tt)] end)
    (fun b =>
      match b with
      | inl old_b => inl (parameter_edge s old_b)
      | inr _ => inr (inl tt) end)
    (fun n =>
      match n with
      | inl point => inl (block_of_point s point)
      | inr _ => inr tt end)
    (fun e =>
      match e with
      | inl old_e => option_map (@inl BE B) (block_edge_of s old_e)
      | inr (inl _) => None
      | inr (inr n) => Some (inr (block_of_point s n)) end)
    parameters arguments
    (fun x =>
      match x with
      | inl old_x => option_map (@inl N bool) (point_definition s old_x)
      | inr fresh_x =>
        if FinSet.mem (pair_encoding EB EV) fresh_x
          fresh_index
        then Some (inr false) else None
      end).

(** Separate client premises require only original SSA facts and the entry correspondence. *)
Record audit_entry_source_laws {B BE N E V} (s : ssa_points B BE N E V) : Prop := {
  (** The original point structure obeys the SSA point laws. *)
  audit_entry_source_points : ssa_point_laws s;
  (** Each reachable use has a reachable strictly dominating definition. *)
  audit_entry_source_uses : forall n x,
    reachable (live_graph (point_model s)) n -> point_use_at (point_model s) n x ->
    exists d, point_definition s x = Some d /\ reachable (live_graph (point_model s)) d /\
      strictly_dominates (live_graph (point_model s)) d n;
  (** Definitions on reachable outgoing edges agree with the point definition. *)
  audit_entry_source_defs : forall n e x,
    reachable (live_graph (point_model s)) n ->
    In e (Graph.out (live_graph (point_model s)) n) ->
    In x (edge_def (point_model s) e) -> point_definition s x = Some n;
  (** A reachable definition is present on every outgoing edge. *)
  audit_entry_source_kills : forall x d e,
    point_definition s x = Some d -> reachable (live_graph (point_model s)) d ->
    In e (Graph.out (live_graph (point_model s)) d) -> In x (edge_def (point_model s) e);
  (** Block and point entries correspond through their first points. *)
  audit_entry_source_bijection :
    (forall b, In b (Graph.entries (block_graph s)) ->
      exists n, nth_error (points_in_block s b) 0 = Some n /\
        In n (Graph.entries (live_graph (point_model s))) /\ block_of_point s n = b) /\
    (forall n, In n (Graph.entries (live_graph (point_model s))) ->
      In (block_of_point s n) (Graph.entries (block_graph s)) /\
      nth_error (points_in_block s (block_of_point s n)) 0 = Some n);
  (** Each block has distinct parameters. *)
  audit_entry_source_params_unique : forall b, NoDup (block_params s b)
}.

(** Entry-source laws give valid and reachable strict SSA for the constructed points. *)
Definition audit_entry_construct_points_statement : Prop :=
  forall B BE N E V (EB : encoding B) (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V), audit_entry_source_laws s ->
    ssa_point_laws (audit_entry_construct_points EB EN EV s) /\
    reachable_point_ssa (audit_entry_construct_points EB EN EV s).

Definition audit_entry_snapshot {S O B BE V K C} (EB : encoding B) (EV : encoding V)
    (sv : ssa_view S O B BE V K C) (inputs : list (B * V)) (s : S)
    : Map.t (B * V) (option C) :=
  Map.of_list (pair_encoding EB EV)
    (map (fun bx => (bx, val sv s (snd bx))) inputs).

Definition audit_snapshot_semantics {S O B V C} (m : semantics S O)
    (capture : S -> Map.t (B * V) (option C))
    : semantics (S * Map.t (B * V) (option C)) O :=
  Semantics (fun state => initial m (fst state) /\ snd state = capture (fst state))
    (fun state events next => step m (fst state) events (fst next) /\ snd next = snd state).

Definition audit_snapshot_endings {S B V C} (en : endings S)
    : endings (S * Map.t (B * V) (option C)) :=
  Endings (fun state => final en (fst state)) (fun state => trapped en (fst state))
    (fun state => stopped en (fst state)).

Definition audit_snapshot_graph_view {S O N E B V C} (gv : graph_view S O N E)
    : graph_view (S * Map.t (B * V) (option C)) O N E :=
  GraphView (cfg gv) (fun state => point gv (fst state))
    (fun state events next edge => taken gv (fst state) events (fst next) edge)
    (fun state events next => stays gv (fst state) events (fst next)).

(** Every fresh value lookup reads its own captured value, defaulting to None. *)
Definition audit_entry_snapshot_get {B V C} (EB : encoding B) (EV : encoding V)
    (snapshot : Map.t (B * V) (option C)) (b : B) (v : V) : option C :=
  match Map.get (pair_encoding EB EV) (b,v) snapshot with
  | Some captured => captured
  | None => None
  end.

(** Taking the snapshot preserves every requested entry input, even when it is absent. *)
Definition audit_entry_snapshot_get_statement : Prop :=
  forall S O B BE V K C (EB : encoding B) (EV : encoding V)
      (sv : ssa_view S O B BE V K C) inputs s b v,
    In (b,v) inputs ->
    audit_entry_snapshot_get EB EV (audit_entry_snapshot EB EV sv inputs s) b v = val sv s v.

(** The saved finite map is unchanged by every original-state step. *)
Definition audit_snapshot_step_frame_statement : Prop :=
  forall S O B V C (m : semantics S O) (s t : S)
    (snap snap' : Map.t (B * V) (option C))
    (capture : S -> Map.t (B * V) (option C)) events,
    step (audit_snapshot_semantics (B:=B) (V:=V) (C:=C) m capture) (s,snap) events (t,snap') ->
    step m s events t /\ snap' = snap.

(** Adding a stable finite snapshot and the two silent points preserves all old observations. *)
Definition audit_entry_snapshot_behavior_statement : Prop :=
  forall S O B BE V K C (EB : encoding B) (EV : encoding V)
      (m : semantics S O) (en : endings S) (sv : ssa_view S O B BE V K C)
      (inputs : list (B * V)) (s : S),
    same_behaviour m en s
      (audit_entry_point_semantics (audit_snapshot_semantics (B:=B) (V:=V) (C:=C) m
        (audit_entry_snapshot EB EV sv inputs)))
      (audit_entry_point_endings (audit_snapshot_endings (B:=B) (V:=V) (C:=C) en))
      (inr (inl (s, audit_entry_snapshot EB EV sv inputs s))).

(** A graph client can keep its old graph observations while carrying the snapshot. *)
Definition audit_snapshot_graph_laws_statement : Prop :=
  forall S O N E B V C (m : semantics S O) (gv : graph_view S O N E)
      (capture : S -> Map.t (B * V) (option C)),
    graph_view_laws m gv ->
    graph_view_laws (audit_snapshot_semantics (B:=B) (V:=V) (C:=C) m capture)
      (audit_snapshot_graph_view (B:=B) (V:=V) (C:=C) gv).

(** A snapshot state pairs the current state with captured entry values. *)
Definition audit_snapshot_state (S B V C : Type) : Type :=
  S * Map.t (B * V) (option C).

(** A virtual state tags an original point or either synthetic entry point. *)
Definition audit_virtual_state (S B V C : Type) : Type :=
  (audit_snapshot_state S B V C + (audit_snapshot_state S B V C + audit_snapshot_state S B V
    C))%type.

Definition audit_virtual_payload {S B V C} (state : audit_virtual_state S B V C)
    : audit_snapshot_state S B V C :=
  match state with
  | inl x => x
  | inr (inl x) => x
  | inr (inr x) => x end.

Definition audit_snapshot_ssa_view_from {S O B BE N E V K C} (EB : encoding B) (EN : encoding N)
    (EV : encoding V) (s : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C)
    (points : ssa_points (B + unit) (BE + B) (N + bool) (E + (unit + N)) (V + (B * V)))
    : ssa_view (audit_virtual_state S B V C) O (B + unit) (BE + B) (V + (B * V)) K C :=
  let inputs := audit_entry_values_of EB s in
  let positions := Map.of_list (pair_encoding EB EV) (combine inputs (seq 0 (length inputs))) in
  SsaView (audit_entry_block_view EB (audit_snapshot_graph_view (base sv)))
    (fun value =>
      match value with
      | inl old =>
        match def sv old with
        | Op op args => Op op (map (@inl V (B * V)) args)
        | Param block index => Param (inl block) index
        | Arbitrary => Arbitrary
        end
      | inr fresh =>
        match Map.get (pair_encoding EB EV) fresh positions with
        | Some index => Param (inr tt) index
        | None => Arbitrary
        end
      end)
    (fun value =>
      match value with
      | inl old => inl (home sv old)
      | inr _ => inr tt end)
    (block_params points) (block_edge_args points)
    (fun edge =>
      match edge with
      | inl old => map (fun cd => Condition (inl (subject cd)) (kind cd)) (edge_guard sv old)
      | inr _ => []
      end)
    (fun state value =>
      let '(old_state, snapshot) := audit_virtual_payload state in
      match value with
      | inl old => val sv old_state old
      | inr (b,x) => audit_entry_snapshot_get EB EV snapshot b x
      end)
    (op_eval sv) (truth sv).

Definition audit_snapshot_ssa_view {S O B BE N E V K C} (EB : encoding B) (EN : encoding N)
    (EV : encoding V) (s : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C)
    : ssa_view (audit_virtual_state S B V C) O (B + unit) (BE + B) (V + (B * V)) K C :=
  let points := audit_entry_construct_points EB EN EV s in
  audit_snapshot_ssa_view_from EB EN EV s sv points.

(** The synthetic parameter list and edge arguments are exactly the constructed point view. *)
Definition audit_snapshot_view_structure_statement : Prop :=
  forall S O B BE N E V K C (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (s : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C) b e,
    params (audit_snapshot_ssa_view EB EN EV s sv) b =
      block_params (audit_entry_construct_points EB EN EV s) b /\
    edge_args (audit_snapshot_ssa_view EB EN EV s sv) e =
      block_edge_args (audit_entry_construct_points EB EN EV s) e.

(** Source compatibility is explicit and does not assume the adapted view laws. *)
Record audit_snapshot_view_source_laws {S O B BE N E V K C}
    (m : semantics S O) (s : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C)
    : Prop := {
  (** The original points satisfy the entry source laws. *)
  audit_snapshot_source_points : audit_entry_source_laws s;
  (** The original view satisfies the source semantics laws. *)
  audit_snapshot_source_view : ssa_view_laws m sv;
  (** The point structure and SSA view use the same block graph. *)
  audit_snapshot_source_graph : block_graph s = cfg (base sv);
  (** The view parameters agree with the point structure. *)
  audit_snapshot_source_params : forall b, params sv b = block_params s b;
  (** The view arguments agree with the point structure. *)
  audit_snapshot_source_args : forall e, edge_args sv e = block_edge_args s e
}.

(** Source compatibility gives SSA view laws for the snapshot and synthetic-entry adapter. *)
Definition audit_snapshot_view_laws_statement : Prop :=
  forall S O B BE N E V K C (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (m : semantics S O) (s : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C),
    audit_snapshot_view_source_laws m s sv ->
    let inputs := audit_entry_values_of EB s in
    let capture := audit_entry_snapshot EB EV sv inputs in
    ssa_view_laws (audit_entry_point_semantics
      (audit_snapshot_semantics (B:=B) (V:=V) (C:=C) m capture))
      (audit_snapshot_ssa_view EB EN EV s sv).

(** The client supplies lifted expression syntax and its edge-specific operations. *)
Record audit_snapshot_syntax (B BE N E V U T C : Type) : Type := AuditSnapshotSyntax {
  (** Embed original expressions in the lifted syntax. *)
  audit_snapshot_old_expression : U -> T;
  (** Supply the finite lifted expression family. *)
  audit_snapshot_family : list T;
  (** Identify the operator shape of each lifted expression. *)
  audit_snapshot_shape : T -> positive;
  (** List the old and synthetic operands of an expression. *)
  audit_snapshot_operands : T -> list (V + (B * V));
  (** Evaluate against an environment for those operands. *)
  audit_snapshot_eval : T -> ((V + (B * V)) -> option C) -> option C;
  (** Translate an expression across an original or synthetic block edge. *)
  audit_snapshot_translate : (BE + B) -> T -> option T;
  (** Identify total pure expressions. *)
  audit_snapshot_pure : T -> bool;
  (** Identify expressions killed by an original or synthetic point edge. *)
  audit_snapshot_kill : (E + (unit + N)) -> T -> bool;
  (** Identify expressions available at entry. *)
  audit_snapshot_initial : T -> bool
}.

Arguments audit_snapshot_old_expression {B BE N E V U T C}.

Arguments audit_snapshot_family {B BE N E V U T C}.

Arguments audit_snapshot_shape {B BE N E V U T C}.

Arguments audit_snapshot_operands {B BE N E V U T C}.

Arguments audit_snapshot_eval {B BE N E V U T C}.

Arguments audit_snapshot_translate {B BE N E V U T C}.

Arguments audit_snapshot_pure {B BE N E V U T C}.

Arguments audit_snapshot_kill {B BE N E V U T C}.

Arguments audit_snapshot_initial {B BE N E V U T C}.

Definition audit_snapshot_pre {S O B BE N E V K C U T} (EB : encoding B) (EN : encoding N)
    (EV : encoding V) (old : pre_expr_ssa S O B BE N E V K C U)
    (syntax : audit_snapshot_syntax B BE N E V U T C)
    : pre_expr_ssa (audit_virtual_state S B V C) O (B + unit) (BE + B) (N + bool)
        (E + (unit + N)) (V + (B * V)) K C T :=
  let source_points := pre_ssa_points old in
  let points := audit_entry_construct_points EB EN EV source_points in
  let view := audit_snapshot_ssa_view_from EB EN EV source_points (pre_ssa_view old) points in
  let oldexpr := audit_snapshot_old_expression syntax in
  let value_universe := map (@inl V (B * V)) (pre_value_universe old) ++
    map (@inr V (B * V)) (audit_entry_values_of EB source_points) in
  PreExprSsa points view
    (PreExpressionView
      (GenKillView (audit_entry_point_view EN
        (audit_snapshot_graph_view (gkview (pre_genkill (pre_expression old)))))
        (fun e =>
          match e with
          | inl old_e => map oldexpr (gen (pre_genkill (pre_expression old)) old_e)
          | inr _ => []
          end)
        (audit_snapshot_kill syntax)
        (fun state u => audit_snapshot_eval syntax u (val view state)))
      (audit_snapshot_pure syntax)
      (fun e =>
        match e with
        | inl old_e => option_map oldexpr (pre_recomputed (pre_expression old) old_e)
        | inr _ => None
        end))
    (map oldexpr (pre_seed_expressions old)) value_universe
    (audit_snapshot_shape syntax) (audit_snapshot_operands syntax) (audit_snapshot_eval syntax)
    (audit_snapshot_translate syntax) (audit_snapshot_initial syntax)
    (fun n =>
      match n with
      | inl old_n => pre_exit_point old old_n
      | inr _ => false end).

(** Runtime equality is built into the adapter and makes no old-state constancy assumption. *)
Definition audit_snapshot_pre_runtime_statement : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (old : pre_expr_ssa S O B BE N E V K C U)
      (syntax : audit_snapshot_syntax B BE N E V U T C) state u,
    let new := audit_snapshot_pre EB EN EV old syntax in
    uval (pre_genkill (pre_expression new)) state u = pre_expr_eval new u (val (pre_ssa_view new)
      state).

(** Source-side facts do not require an already single-entry PRE client. *)
Record audit_snapshot_pre_source_laws {S O B BE N E V K C U}
    (old : pre_expr_ssa S O B BE N E V K C U) : Prop := {
  (** The original points satisfy the entry source laws. *)
  audit_pre_source_point_laws : audit_entry_source_laws (pre_ssa_points old);
  (** The point structure and SSA view share the block graph. *)
  audit_pre_source_block_graph : block_graph (pre_ssa_points old) = cfg (base (pre_ssa_view old));
  (** The point structure and expression view share the live graph. *)
  audit_pre_source_point_graph : live_graph (point_model (pre_ssa_points old)) =
    cfg (gkview (pre_genkill (pre_expression old)));
  (** Every listed block is reachable. *)
  audit_pre_source_blocks_reachable : forall b, In b (Graph.nodes (block_graph (pre_ssa_points
    old))) ->
    reachable (block_graph (pre_ssa_points old)) b;
  (** Every listed point is reachable. *)
  audit_pre_source_points_reachable : forall n,
    In n (Graph.nodes (live_graph (point_model (pre_ssa_points old)))) ->
    reachable (live_graph (point_model (pre_ssa_points old))) n;
  (** The original value universe has no duplicates. *)
  audit_pre_source_universe_unique : NoDup (pre_value_universe old);
  (** Every initially available expression belongs to the inductive family closure. *)
  audit_pre_source_initial_family : forall u, pre_initial_available old u = true ->
    pre_expr_in_family old u;
  (** Runtime expression evaluation agrees with the SSA value environment. *)
  audit_pre_source_runtime : forall s u,
    uval (pre_genkill (pre_expression old)) s u =
      pre_expr_eval old u (val (pre_ssa_view old) s);
  (** Every recomputed expression is a seed. *)
  audit_pre_source_occurrences : forall e u, pre_recomputed (pre_expression old) e = Some u ->
    In u (pre_seed_expressions old);
  (** Each edge definition belongs to the source point block. *)
  audit_pre_source_def_home : forall e x,
    In e (edges_of (live_graph (point_model (pre_ssa_points old)))) ->
    In x (edge_def (point_model (pre_ssa_points old)) e) ->
    home (pre_ssa_view old) x = block_of_point (pre_ssa_points old)
      (Graph.source (live_graph (point_model (pre_ssa_points old))) e);
  (** A crossing edge defines no values. *)
  audit_pre_source_cross_no_defs : forall e be,
    In e (edges_of (live_graph (point_model (pre_ssa_points old)))) ->
    block_edge_of (pre_ssa_points old) e = Some be ->
    edge_def (point_model (pre_ssa_points old)) e = [];
  (** A recomputation edge is neither a block crossing nor a parameter edge. *)
  audit_pre_source_real_internal : forall e u,
    pre_recomputed (pre_expression old) e = Some u ->
    block_edge_of (pre_ssa_points old) e = None /\
      (forall b, e <> parameter_edge (pre_ssa_points old) b)
}.

Section SnapshotSyntaxLaws.

  Context {S O B BE N E V K C U T : Type} (EB : encoding B) (EN : encoding N) (EV : encoding V)
    (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C).

  (** The lifted client, value encoding, finite family and old-expression injection. *)
  Let new := audit_snapshot_pre EB EN EV old syntax.

  Let EW := sum_encoding EV (pair_encoding EB EV).

  Let family := audit_snapshot_family syntax.

  Let oldexpr := audit_snapshot_old_expression syntax.

  (** This finite witness states the client's actual lifted syntax, including all phi translations.
    *)
  Record audit_snapshot_syntax_laws : Prop := {
    (** The supplied family is duplicate free and exactly the lifted family. *)
    audit_snapshot_family_exact : NoDup family /\ forall u, In u family <-> pre_expr_in_family new
      u;
    (** Lifting old expressions preserves their distinct identities. *)
    audit_snapshot_old_expression_injective : forall u v, oldexpr u = oldexpr v -> u = v;
    (** Within the family, shape and operands uniquely determine an expression. *)
    audit_snapshot_shape_identity : forall u v, In u family -> In v family ->
      pre_expression_shape new u = pre_expression_shape new v ->
      pre_operands new u = pre_operands new v -> u = v;
    (** Equal family shapes have the same operand count. *)
    audit_snapshot_shape_arity : forall u v, In u family -> In v family ->
      pre_expression_shape new u = pre_expression_shape new v ->
      length (pre_operands new u) = length (pre_operands new v);
    (** Every family operand belongs to the lifted value universe. *)
    audit_snapshot_finite_operands : forall u, In u family -> incl (pre_operands new u)
      (pre_value_universe new);
    (** Expression evaluation depends only on its listed operands. *)
    audit_snapshot_operand_support : forall u env1 env2,
      (forall x, In x (pre_operands new u) -> env1 x = env2 x) ->
      pre_expr_eval new u env1 = pre_expr_eval new u env2;
    (** Every initially available expression is in the lifted family. *)
    audit_snapshot_initial_family : forall u, pre_initial_available new u = true -> In u family;
    (** A killed family expression has an operand defined by that edge. *)
    audit_snapshot_kill_operand : forall e u,
      In e (edges_of (live_graph (point_model (pre_ssa_points new)))) -> In u family ->
      kill (pre_genkill (pre_expression new)) e u = true ->
      exists x, In x (pre_operands new u) /\ In x (edge_def (point_model (pre_ssa_points new)) e);
    (** Every family expression translates on each listed block edge. *)
    audit_snapshot_translation_closed : forall be u,
      In be (edges_of (block_graph (pre_ssa_points new))) -> In u family ->
      exists v, pre_phi_translate new be u = Some v;
    (** Translation preserves the expression shape. *)
    audit_snapshot_translation_shape : forall be u v, In u family ->
      pre_phi_translate new be u = Some v -> pre_expression_shape new v = pre_expression_shape new
        u;
    (** Translation substitutes the actual edge-specific phi operands. *)
    audit_snapshot_translation_operands : forall be u v, In u family ->
      In be (edges_of (block_graph (pre_ssa_points new))) ->
      pre_phi_translate new be u = Some v ->
      pre_operands new v = map (pre_phi_operand EW new be) (pre_operands new u);
    (** Translation preserves purity when the source expression is pure. *)
    audit_snapshot_translation_pure : forall be u v,
      pre_total_pure (pre_expression new) u = true -> pre_phi_translate new be u = Some v ->
      pre_total_pure (pre_expression new) v = true;
    (** Evaluation after phi substitution agrees with evaluation of the translation. *)
    audit_snapshot_translation_eval : forall be u v env,
      In be (edges_of (block_graph (pre_ssa_points new))) -> In u family ->
      pre_phi_translate new be u = Some v ->
      pre_expr_eval new u (pre_phi_env EW new be env) = pre_expr_eval new v env;
    (** Old expressions retain their shape, lifted operands and purity. *)
    audit_snapshot_old_syntax : forall u,
      pre_expression_shape new (oldexpr u) = pre_expression_shape old u /\
      pre_operands new (oldexpr u) = map (@inl V (B * V)) (pre_operands old u) /\
      pre_total_pure (pre_expression new) (oldexpr u) = pre_total_pure (pre_expression old) u;
    (** A lifted old expression evaluates in the projected old environment. *)
    audit_snapshot_old_evaluation : forall u env,
      pre_expr_eval new (oldexpr u) env = pre_expr_eval old u (fun x => env (inl x));
    (** Old edges preserve the original kill observation for old expressions. *)
    audit_snapshot_old_kill : forall e u,
      kill (pre_genkill (pre_expression new)) (inl e) (oldexpr u) =
        kill (pre_genkill (pre_expression old)) e u;
    (** Synthetic entry edges do not kill expressions. *)
    audit_snapshot_synthetic_no_kill : forall e u,
      kill (pre_genkill (pre_expression new)) (inr e) u = false;
    (** Old block-edge translation commutes with lifting old expressions. *)
    audit_snapshot_old_phi : forall be u,
      pre_phi_translate new (inl be) (oldexpr u) = option_map oldexpr (pre_phi_translate old be u);
    (** Lifting preserves initial availability of old expressions. *)
    audit_snapshot_old_initial : forall u,
      pre_initial_available new (oldexpr u) = pre_initial_available old u
  }.

End SnapshotSyntaxLaws.

(** Under explicit source and client syntax laws, every existing PRE structural law holds. *)
Definition audit_snapshot_pre_laws_statement : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C),
    audit_snapshot_pre_source_laws old -> audit_snapshot_syntax_laws EB EN EV old syntax ->
    pre_expr_ssa_laws (sum_encoding EV (pair_encoding EB EV)) (audit_snapshot_pre EB EN EV old
      syntax).

(** The existing PRE semantic theorem composes with captured entry and both silent steps. *)
Definition audit_snapshot_pre_behavior_statement : Prop :=
  forall S O B BE N E NT ET V K C U T
      (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
      (EV : encoding V) (ETexpr : encoding T) (m : semantics S O) (en : endings S)
      (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C)
      (r : pre_realizer (audit_virtual_state S B V C) O (N + bool) (E + (unit + N)) NT ET T C)
      (s : S) (target : audit_virtual_state S B V C),
    let Eblock := sum_encoding EB unit_encoding in
    let Eblockedge := sum_encoding EBE EB in
    let Epoint := sum_encoding EN bool_encoding in
    let Epointedge := sum_encoding EE (sum_encoding unit_encoding EN) in
    let Evalue := sum_encoding EV (pair_encoding EB EV) in
    let new := audit_snapshot_pre EB EN EV old syntax in
    let inputs := audit_entry_values_of EB (pre_ssa_points old) in
    let capture := audit_entry_snapshot EB EV (pre_ssa_view old) inputs in
    let source := inr (inl (s, capture s)) in
    let plan := ssa_pre_place Eblock Eblockedge Epoint Epointedge Evalue ETexpr new in
    audit_snapshot_pre_source_laws old -> audit_snapshot_syntax_laws EB EN EV old syntax ->
    ready Eblock (block_graph (pre_ssa_points new))
      (prepare Eblock (block_graph (pre_ssa_points new))) ->
    ready Epoint (live_graph (point_model (pre_ssa_points new)))
      (prepare Epoint (live_graph (point_model (pre_ssa_points new)))) ->
    pre_source r = audit_entry_point_semantics
      (audit_snapshot_semantics (B:=B) (V:=V) (C:=C) m capture) ->
    pre_source_end r = audit_entry_point_endings (audit_snapshot_endings (B:=B) (V:=V) (C:=C) en) ->
    pre_exit_covered new r -> pre_phi_source_laws Eblockedge Evalue new r ->
    pre_local_laws Eblockedge Epoint Epointedge Evalue ETexpr new (pre_expression new)
      (pre_initial_available new) r plan ->
    initial m s -> initial (pre_target r plan) target ->
    pre_boundary r plan (point (pre_source_graph r) source) target ->
    pre_cache_agree Epoint Epointedge ETexpr (pre_expression new) r plan
      (point (pre_source_graph r) source) source target ->
    same_behaviour m en s (pre_target r plan) (pre_target_end r plan) target.

(** Old expression observations are unchanged at every embedded original state. *)
Definition audit_snapshot_old_value_statement : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C)
      (s : S) (snapshot : Map.t (B * V) (option C)) (u : U),
    audit_snapshot_pre_source_laws old -> audit_snapshot_syntax_laws EB EN EV old syntax ->
    uval (pre_genkill (pre_expression (audit_snapshot_pre EB EN EV old syntax)))
      (inl (s,snapshot)) (audit_snapshot_old_expression syntax u) =
    uval (pre_genkill (pre_expression old)) s u.

(** The lifted old edges retain graph identity, uses, definitions, generation and recomputation. *)
Definition audit_snapshot_old_edge_projection_statement : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C)
      (e : E),
    let new := audit_snapshot_pre EB EN EV old syntax in
    Graph.source (live_graph (point_model (pre_ssa_points new))) (inl e) =
      inl (Graph.source (live_graph (point_model (pre_ssa_points old))) e) /\
    Graph.target (live_graph (point_model (pre_ssa_points new))) (inl e) =
      inl (Graph.target (live_graph (point_model (pre_ssa_points old))) e) /\
    edge_use (point_model (pre_ssa_points new)) (inl e) =
      map (@inl V (B * V)) (edge_use (point_model (pre_ssa_points old)) e) /\
    edge_def (point_model (pre_ssa_points new)) (inl e) =
      map (@inl V (B * V)) (edge_def (point_model (pre_ssa_points old)) e) /\
    gen (pre_genkill (pre_expression new)) (inl e) =
      map (audit_snapshot_old_expression syntax) (gen (pre_genkill (pre_expression old)) e) /\
    pre_recomputed (pre_expression new) (inl e) =
      option_map (audit_snapshot_old_expression syntax) (pre_recomputed (pre_expression old) e).

(** Lifted block-edge endpoints, arguments, parameters and point-edge projections agree with
    the original structure. *)
Definition audit_snapshot_old_block_projection_statement : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
      (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C)
      (be : BE) (b : B) (e : E),
    let new := audit_snapshot_pre EB EN EV old syntax in
    Graph.source (block_graph (pre_ssa_points new)) (inl be) =
      inl (Graph.source (block_graph (pre_ssa_points old)) be) /\
    Graph.target (block_graph (pre_ssa_points new)) (inl be) =
      inl (Graph.target (block_graph (pre_ssa_points old)) be) /\
    block_edge_args (pre_ssa_points new) (inl be) =
      map (@inl V (B * V)) (block_edge_args (pre_ssa_points old) be) /\
    block_params (pre_ssa_points new) (inl b) =
      map (@inl V (B * V)) (block_params (pre_ssa_points old) b) /\
    block_edge_of (pre_ssa_points new) (inl e) =
      option_map (@inl BE B) (block_edge_of (pre_ssa_points old) e).

(** Consolidated from pre_fullstate_adapter_candidate.v. *)
(** Full initial-state snapshot avoids requiring a finite universe of pure expressions. *)
Definition full_snapshot_semantics {S O} (m : semantics S O) : semantics (S*S) O :=
  Semantics (fun state => initial m (fst state) /\ snd state = fst state)
  (fun state events next => step m (fst state) events (fst next) /\ snd next = snd state).

Definition full_snapshot_endings {S} (en : endings S) : endings (S*S) :=
  Endings (fun state => final en (fst state)) (fun state => trapped en (fst state))
  (fun state => stopped en (fst state)).

Definition full_snapshot_view {S O N E} (gv : graph_view S O N E) : graph_view (S*S) O N E :=
  GraphView (cfg gv) (fun state => point gv (fst state))
  (fun state events next e => taken gv (fst state) events (fst next) e)
  (fun state events next => stays gv (fst state) events (fst next)).

(** A full virtual state tags a current and saved initial state at each point. *)
Definition full_virtual_state (S : Type) := ((S*S) + ((S*S)+(S*S)))%type.

Definition full_virtual_payload {S} (state : full_virtual_state S) : S*S :=
  match state with
  | inl x => x
  | inr (inl x) => x
  | inr (inr x) => x end.

Definition full_snapshot_ssa_view {S O B BE N E V K C} (EB : encoding B) (EN : encoding N)
  (EV : encoding V) (points : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C)
  : ssa_view (full_virtual_state S) O (B+unit) (BE+B) (V+(B*V)) K C :=
  let old_view := audit_snapshot_ssa_view EB EN EV points sv in
  let new_points := audit_entry_construct_points EB EN EV points in
  SsaView (audit_entry_block_view EB (full_snapshot_view (base sv)))
  (def old_view) (home old_view) (block_params new_points) (block_edge_args new_points)
  (edge_guard old_view)
  (fun state value => let pair := full_virtual_payload state in
    match value with
    | inl x => val sv (fst pair) x
    | inr (_,x) => val sv (snd pair) x end)
  (op_eval old_view) (truth old_view).

Definition full_snapshot_pre {S O B BE N E V K C U T} (EB : encoding B) (EN : encoding N)
  (EV : encoding V) (old : pre_expr_ssa S O B BE N E V K C U)
  (syntax : audit_snapshot_syntax B BE N E V U T C)
  : pre_expr_ssa (full_virtual_state S) O (B+unit) (BE+B) (N+bool) (E+(unit+N)) (V+(B*V)) K C T :=
  let proxy := audit_snapshot_pre EB EN EV old syntax in
  let points := audit_entry_construct_points EB EN EV (pre_ssa_points old) in
  let view := full_snapshot_ssa_view EB EN EV (pre_ssa_points old) (pre_ssa_view old) in
  let oldgk := pre_genkill (pre_expression old) in
  PreExprSsa points view
  (PreExpressionView
    (GenKillView (audit_entry_point_view EN (full_snapshot_view (gkview oldgk)))
      (gen (pre_genkill (pre_expression proxy))) (kill (pre_genkill (pre_expression proxy)))
      (fun state u => audit_snapshot_eval syntax u (val view state)))
    (pre_total_pure (pre_expression proxy)) (pre_recomputed (pre_expression proxy)))
  (pre_seed_expressions proxy) (pre_value_universe proxy) (pre_expression_shape proxy)
  (pre_operands proxy) (pre_expr_eval proxy) (pre_phi_translate proxy)
  (pre_initial_available proxy) (pre_exit_point proxy).

(** At an original point, old values use the current state and fresh values use the
    initial state. *)
Definition full_snapshot_value_law : Prop :=
  forall S O B BE N E V K C (EB : encoding B) (EN : encoding N) (EV : encoding V)
  (points : ssa_points B BE N E V) (sv : ssa_view S O B BE V K C) current initial b x,
  let view := full_snapshot_ssa_view EB EN EV points sv in
  val view (inl (current,initial)) (inl x) = val sv current x /\
  val view (inl (current,initial)) (inr (b,x)) = val sv initial x.

(** The full-state snapshot and synthetic entry preserve all original behavior observations. *)
Definition full_snapshot_semantics_law : Prop :=
  forall S O (m : semantics S O) (en : endings S) s,
  same_behaviour m en s (audit_entry_point_semantics (full_snapshot_semantics m))
    (audit_entry_point_endings (full_snapshot_endings en)) (inr (inl (s,s))).

(** The full-state adapter satisfies PRE structural laws under the source and syntax premises. *)
Definition full_snapshot_pre_laws : Prop :=
  forall S O B BE N E V K C U T (EB : encoding B) (EN : encoding N) (EV : encoding V)
    (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C),
  audit_snapshot_pre_source_laws old -> audit_snapshot_syntax_laws EB EN EV old syntax ->
  pre_expr_ssa_laws (sum_encoding EV (pair_encoding EB EV)) (full_snapshot_pre EB EN EV old syntax).

(** A realized placement preserves old behavior under the stated readiness and local laws. *)
Definition full_snapshot_pre_behavior : Prop :=
  forall S O B BE N E NT ET V K C U T
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (ETexpr : encoding T) (m : semantics S O) (en : endings S)
    (old : pre_expr_ssa S O B BE N E V K C U) (syntax : audit_snapshot_syntax B BE N E V U T C)
    (r : pre_realizer (full_virtual_state S) O (N+bool) (E+(unit+N)) NT ET T C)
    (s : S) (target : full_virtual_state S),
  let Eblock := sum_encoding EB unit_encoding in
  let Eblockedge := sum_encoding EBE EB in
  let Epoint := sum_encoding EN bool_encoding in
  let Epointedge := sum_encoding EE (sum_encoding unit_encoding EN) in
  let Evalue := sum_encoding EV (pair_encoding EB EV) in
  let new := full_snapshot_pre EB EN EV old syntax in
  let source := inr (inl (s,s)) in
  let plan := ssa_pre_place Eblock Eblockedge Epoint Epointedge Evalue ETexpr new in
  audit_snapshot_pre_source_laws old -> audit_snapshot_syntax_laws EB EN EV old syntax ->
  ready Eblock (block_graph (pre_ssa_points new))
    (prepare Eblock (block_graph (pre_ssa_points new)))
    ->
  ready Epoint (live_graph (point_model (pre_ssa_points new)))
    (prepare Epoint (live_graph (point_model (pre_ssa_points new)))) ->
  pre_source r = audit_entry_point_semantics (full_snapshot_semantics m) ->
  pre_source_end r = audit_entry_point_endings (full_snapshot_endings en) ->
  pre_exit_covered new r -> pre_phi_source_laws Eblockedge Evalue new r ->
  pre_local_laws Eblockedge Epoint Epointedge Evalue ETexpr new (pre_expression new)
    (pre_initial_available new) r plan ->
  initial m s -> initial (pre_target r plan) target ->
  pre_boundary r plan (point (pre_source_graph r) source) target ->
  pre_cache_agree Epoint Epointedge ETexpr (pre_expression new) r plan
    (point (pre_source_graph r) source) source target ->
  same_behaviour m en s (pre_target r plan) (pre_target_end r plan) target.

(* Definition source: PrePlaceBody.v *)
(** * Same-execution PRE body composition around explicit graph-backend boundaries

    Card: AUD-SP. This is not the full public-entry source theorem: preparation, dominator,
    frontier and second forest backend costs remain GR-owned obligations. All PRE-owned
    bodies below are executed once on their actual child outputs. *)
Inductive pre_place_body_call (B BE N E V U : Type) : Type :=
  | PreBodyFrg (call : pre_frg_call B BE N E V U)
  | PreBodySolve (call : pre_solver_call B BE E U)
  | PreBodyFinalize (call : pre_rows_call B BE N E U)
  | PreBodyMaterialize (call : pre_materialize_call E U).

Arguments PreBodyFrg {B BE N E V U}.

Arguments PreBodySolve {B BE N E V U}.

Arguments PreBodyFinalize {B BE N E V U}.

Arguments PreBodyMaterialize {B BE N E V U}.

Section PlaceBody.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** The call type records the PRE-owned placement phases. *)
Let Call := pre_place_body_call B BE N E V U.

Definition pre_place_from_backends_counted
    (p : prepared EB (block_graph (pre_ssa_points a))) (tree : dom_tree B)
    (df : Map.t B (FinSet.t B))
    (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (final_tree : dom_tree N) (order : list N) : exact_counted Call (pre_plan E U) :=
  exact_bind 2000 (exact_lift PreBodyFrg
    (pre_build_frg_from_graph_counted EB EBE EN EE EV EU a bb beb nb eb vb ub p tree df)) (fun f =>
  exact_bind 2001 (exact_lift PreBodySolve (pre_solve_source EB EU bb ub f)) (fun facts =>
  exact_bind 2002 (exact_lift PreBodyFinalize
    (pre_finalize_order_counted EB EBE EN EE EU a bb beb nb eb ub f facts final_tree points order))
      (fun plan => exact_lift PreBodyMaterialize
        (pre_materialize_counted EE EU (pre_expression a) eb ub (fun _ => 0) plan)))).

Definition pre_place_from_backends_budget
    (p : prepared EB (block_graph (pre_ssa_points a))) (tree : dom_tree B)
    (df : Map.t B (FinSet.t B))
    (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (final_tree : dom_tree N) (order : list N) : nat :=
  let f := pre_build_frg_from_graph EB EBE EN EE EV EU a p tree df in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  let plan := snd (fold_left (AnalysesSsaPre.pre_finalize_table_step EB EN EE EU a f facts
    final_tree points (AnalysesSsaPre.pre_finalize_phi_rows EB EN EU a f facts)
    (AnalysesSsaPre.pre_finalize_argument_rows EBE EN a f)
    (AnalysesSsaPre.pre_finalize_initial EB EE EU a (frg_versions f))) order
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)) in
  1024 + pre_frg_from_graph_input_budget EB EBE EN EE EV EU a bb beb nb eb vb ub p tree df +
    pre_solve_input_budget EB EU bb ub f +
    pre_finalize_order_input_budget EB EBE EN EE EU a bb beb nb eb ub f facts final_tree points
      order +
    pre_materialize_input_budget EE EU (pre_expression a) eb ub (fun _ => 0) plan.

(** The four counted PRE phases return the placement and meet their composed budget
    for actual backends. *)
Definition audit_pre_body_composition_statement : Prop :=
  forall p tree df points final_tree order,
    pre_expr_ssa_laws EV a ->
    p = prepare EB (block_graph (pre_ssa_points a)) -> tree = dominator_tree p ->
    df = dominance_frontier p tree ->
    points = prepare EN (live_graph (point_model (pre_ssa_points a))) ->
    let parents := simple_lt_idom points in
    let search := dom_search points parents in
    final_tree = DomTree parents (pre_num search) (post_num search) -> order = preorder search ->
    let run := pre_place_from_backends_counted p tree df points final_tree order in
    exact_value run = ssa_pre_place EB EBE EN EE EV EU a /\
    exact_units run <= pre_place_from_backends_budget p tree df points final_tree order.

End PlaceBody.

(* Definition source: PreGraphAssembly.v *)
(** * Fixed whole PRE source-model assembly

    Card: AUD-SP. Internal graph children use fixed library source relations. Their witness
    data is not a client's desired bound law. Totality/erasure/bound are future proof duties.
    Complete implementation-adequacy conjunction and independent review remain required. *)
Inductive pre_graph_view_call (V E : Type) : Type :=
  | PreViewOut : V -> list E -> pre_graph_view_call V E
  | PreViewTarget : E -> V -> pre_graph_view_call V E
  | PreViewSource : E -> V -> pre_graph_view_call V E
  | PreViewEncode : V -> positive -> pre_graph_view_call V E.

Arguments PreViewOut {V E}.

Arguments PreViewTarget {V E}.

Arguments PreViewSource {V E}.

Arguments PreViewEncode {V E}.

Definition pre_view_out {V E} (g : Graph.t V E) v :=
  let result := Graph.out g v in (result,[PreViewOut v result]).

Definition pre_view_target {V E} (g : Graph.t V E) e :=
  let result := Graph.target g e in (result,[PreViewTarget e result]).

Definition pre_view_source {V E} (g : Graph.t V E) e :=
  let result := Graph.source g e in (result,[PreViewSource e result]).

Definition pre_view_encode {V E} (EV : encoding V) v : positive * list (pre_graph_view_call V E) :=
  let code := encode EV v in (code,[PreViewEncode v code]).

Definition pre_view_weight {V E} (body : V -> nat) (event : pre_graph_view_call V E) :=
  64 +
    match event with
    | PreViewEncode v code => body v + audit_encoding_weight (Pos.size_nat code)
    | _ => 0 end.

Definition pre_view_prepare {V E} EV (g : Graph.t V E) :=
  AuditPrepareCallbackModel V E (pre_graph_view_call V E) (pre_view_out g) (pre_view_target g)
    (pre_view_encode EV).

Definition pre_view_virtual {V E} EV (g : Graph.t V E) :=
  AuditVirtualBaseCallbacks V E (pre_graph_view_call V E) (pre_view_out g) (pre_view_target g)
    (pre_view_encode EV).

Definition pre_view_frontier {V E} EV (g : Graph.t V E) :=
  AuditFrontierSourceCallbacks V E (pre_graph_view_call V E)
    (pre_view_encode EV) (pre_view_source g) (pre_view_target g).

(** One dominance witness retains the search, backend traces, parents and final tree. *)
Record pre_dom_source_data (V E X : Type) (EV : encoding V) : Type := PreDomSourceData {
  (** Events from preparing the virtual graph. *)
  pre_dom_prepare_events : list (audit_prepare_source_event (V + unit) (E + V)
    (audit_virtual_full_call V E X));
  (** Events from its depth-first search. *)
  pre_dom_dfs_events : list (audit_dfs_nested_event (V + unit) (E + V)
    (audit_graph_callback_capture (V + unit) (E + V) (audit_virtual_full_call V E X)));
  (** The final tree produced by this witness. *)
  pre_dom_result : dom_tree V;
  (** Original-graph immediate dominator parents. *)
  pre_dom_parents : Map.t V V;
  (** Semidominator producer events. *)
  pre_dom_semi : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call
    V E X));
  (** Lengauer-Tarjan events. *)
  pre_dom_lt : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E X));
  (** Events erasing the synthetic vertex. *)
  pre_dom_erase : list (audit_erase_nested_event V X);
  (** Receipt for the final original-graph dominator search. *)
  pre_dom_search : audit_dom_source_receipt V E X EV
}.

Arguments pre_dom_prepare_events {V E X EV}.

Arguments pre_dom_dfs_events {V E X EV}.

Arguments pre_dom_result {V E X EV}.

Arguments pre_dom_parents {V E X EV}.

Arguments pre_dom_semi {V E X EV}.

Arguments pre_dom_lt {V E X EV}.

Arguments pre_dom_erase {V E X EV}.

Arguments pre_dom_search {V E X EV}.

(** One witness ties virtual search, dominance stages, erasure and the final tree
    to the same execution. *)
Definition pre_dom_fixed_run {V E X EV g} (p : @prepared V E EV g) cb source
    (data : pre_dom_source_data V E X EV) :=
  exists vp search semi_state virtual_parents,
    audit_virtual_source_search EV g cb =
      (vp,(search,(pre_dom_prepare_events data,pre_dom_dfs_events data))) /\
    audit_semi_producer_nested_run (audit_virtual_full_encode cb)
      (audit_virtual_full_source source) vp search semi_state (pre_dom_semi data) /\
    audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      search (SemiState.result semi_state) virtual_parents (pre_dom_lt data) /\
    audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
      (pre_dom_parents data,pre_dom_erase data) /\
    pre_dom_search data = audit_dom_search_source_counted p (pre_dom_parents data)
      (AuditDfsCallbackModel V E X (audit_virtual_base_target cb)
        (audit_virtual_base_encode cb)) /\
    pre_dom_result data = DomTree (pre_dom_parents data)
      (pre_num (audit_dom_source_result (pre_dom_search data)))
      (post_num (audit_dom_source_result (pre_dom_search data))).

(** Whole dominance work uses the single retained virtual search and its actual traces. *)
Definition pre_dom_whole_work {V E X EV} (weight : X -> nat)
    (data : pre_dom_source_data V E X EV) : nat :=
  audit_prepare_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) (pre_dom_prepare_events data) +
  audit_dfs_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) (pre_dom_dfs_events data) +
  audit_virtual_semi_stage_work weight (pre_dom_semi data) +
  audit_virtual_lt_stage_work weight (pre_dom_lt data) +
  audit_erase_nested_work weight (pre_dom_erase data) +
  audit_dom_source_work weight (audit_dom_source_events (pre_dom_search data)).

Definition pre_dom_external_work {V E X EV} (weight : X -> nat)
    (data : pre_dom_source_data V E X EV) : nat :=
  audit_prepare_source_body_work (audit_virtual_full_body_event_work weight)
    (pre_dom_prepare_events data) +
  audit_dfs_source_body_work (audit_virtual_full_body_event_work weight)
    (pre_dom_dfs_events data) +
  audit_virtual_semi_external_work weight (pre_dom_semi data) +
  audit_virtual_lt_external_work weight (pre_dom_lt data) +
  audit_erase_nested_body_work weight (pre_dom_erase data) +
  audit_dom_source_external_work weight (audit_dom_source_events (pre_dom_search data)).

Section Assembly.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** The block and live point graphs and their respective dominance witness types. *)
Let bg := block_graph (pre_ssa_points a).

Let pg := live_graph (point_model (pre_ssa_points a)).

Let BD := pre_dom_source_data B BE (pre_graph_view_call B BE) EB.

Let ND := pre_dom_source_data N E (pre_graph_view_call N E) EN.

(** A placement witness records both graph executions and the exact combined phase work. *)
Definition pre_place_graph_run (bd : BD) (nd : ND) (result : pre_plan E U) (work : nat) : Prop :=
  let '(p,prepare_b) := audit_prepare_source_counted EB bg (pre_view_prepare EB bg) in
  pre_dom_fixed_run p (pre_view_virtual EB bg) (pre_view_source bg) bd /\
  let '(df,frontier_events) := audit_frontier_source_counted (pre_view_frontier EB bg) p
    (pre_dom_result bd) in
  let frg := pre_build_frg_from_graph_counted EB EBE EN EE EV EU a bb beb nb eb vb ub p
    (pre_dom_result bd) df in
  let facts := pre_solve_source EB EU bb ub (exact_value frg) in
  let '(points,prepare_n) := audit_prepare_source_counted EN pg (pre_view_prepare EN pg) in
  pre_dom_fixed_run points (pre_view_virtual EN pg) (pre_view_source pg) nd /\
  let final := pre_finalize_order_counted EB EBE EN EE EU a bb beb nb eb ub
    (exact_value frg) (exact_value facts) (pre_dom_result nd) points
      (preorder (audit_dom_source_result (pre_dom_search nd))) in
  let material := pre_materialize_counted EE EU (pre_expression a) eb ub (fun _ => 0) (exact_value
    final) in
  result = exact_value material /\
  work = 2048 + audit_prepare_source_work (pre_view_weight bb) prepare_b +
    pre_dom_whole_work (pre_view_weight bb) bd +
    audit_frontier_source_work (pre_view_weight bb) frontier_events + exact_units frg + exact_units
      facts +
    audit_prepare_source_work (pre_view_weight nb) prepare_n +
    pre_dom_whole_work (pre_view_weight nb) nd +
    exact_units final + exact_units material.

Definition pre_place_graph_budget (bd : BD) (nd : ND) : nat :=
  let '(p,prepare_b) := audit_prepare_source_counted EB bg (pre_view_prepare EB bg) in
  let '(df,frontier_events) := audit_frontier_source_counted (pre_view_frontier EB bg) p
    (pre_dom_result bd) in
  let '(points,prepare_n) := audit_prepare_source_counted EN pg (pre_view_prepare EN pg) in
  2048 + audit_prepare_source_budget EB bg + audit_prepare_source_body_work (pre_view_weight bb)
    prepare_b +
    audit_virtual_lt_input_budget EB bg +
    audit_dom_search_source_budget EB bg p (pre_dom_parents bd) (pre_dom_search bd) +
    pre_dom_external_work (pre_view_weight bb) bd +
    audit_frontier_source_input_budget EB bg p (pre_dom_result bd) +
    audit_frontier_source_body_work (pre_view_weight bb) frontier_events +
    audit_prepare_source_budget EN pg + audit_prepare_source_body_work (pre_view_weight nb)
      prepare_n +
    audit_virtual_lt_input_budget EN pg +
    audit_dom_search_source_budget EN pg points (pre_dom_parents nd) (pre_dom_search nd) +
    pre_dom_external_work (pre_view_weight nb) nd +
    pre_place_from_backends_budget EB EBE EN EE EV EU a bb beb nb eb vb ub p (pre_dom_result bd) df
      points (pre_dom_result nd) (preorder (audit_dom_source_result (pre_dom_search nd))).

(** A lawful PRE input admits one exact placement run bounded by its graph budget. *)
Definition audit_pre_place_source_model_statement : Prop :=
  pre_expr_ssa_laws EV a -> exists bd nd result work,
    pre_place_graph_run bd nd result work /\ result = ssa_pre_place EB EBE EN EE EV EU a /\
    work <= pre_place_graph_budget bd nd.

End Assembly.

(* Definition source: PreFullSource.v *)
(** Card: AUD-SP. Candidate full conjunction; every universal theorem remains future proof.
    No source dispatch or independent acceptance is implied by these declaration types. *)

(** The fixed graph callbacks erase to the original graph operations and encoder. *)
Definition audit_pre_graph_callback_instances_statement : Prop :=
  (forall V E (EV : encoding V) (g : GraphCore.Graph.t V E),
    audit_prepare_callbacks_erase EV g (pre_view_prepare EV g) /\
    audit_virtual_base_callbacks_erase EV g (pre_view_virtual EV g) /\
    audit_frontier_source_callbacks_erase EV g (pre_view_frontier EV g)).

(** The fixed collection, arithmetic and graph obligations are all required
    for implementation adequacy. *)
Definition audit_pre_implementation_adequacy_statement : Prop :=
  audit_pre_map_implementation_adequacy_statement /\ audit_pre_pair_encoding_adequacy_statement /\
  audit_pre_derived_encoding_adequacy_statement /\
    audit_pre_arithmetic_implementation_adequacy_statement /\
  exact_get_erases_statement /\ exact_set_erases_statement /\
  audit_pre_graph_callback_instances_statement /\ audit_prepare_source_statement /\
    audit_dfs_source_statement /\
  audit_default_dom_single_run_statement /\ audit_dom_search_source_statement /\
    audit_frontier_source_statement.

(** Every PRE input and callback-cost choice satisfies the whole placement source proposition. *)
Definition audit_pre_place_full_source_statement : Prop :=
  forall S O B BE N E V K C U (EB : encoding B) (EBE : encoding BE) (EN : encoding N)
    (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
    (vb : V -> nat) (ub : U -> nat),
    audit_pre_place_source_model_statement EB EBE EN EE EV EU a bb beb nb eb vb ub.

(** Finite checking and bounded correction accompany the placement objective evidence. *)
Definition audit_pre_certificate_full_source_statement : Prop :=
  (forall E U (EE : encoding E) (EU : encoding U) (eb : E -> nat) (ub : U -> nat)
    (edges : list E) (exprs : list U), audit_pre_finite_source_statement EE EU eb ub edges exprs) /\
  pre_objective_evidence /\ audit_pre_bounded_correction_statement.

(** The caller contract combines source bounds, implementation duties and full
    snapshot guarantees. *)
Definition audit_pre_caller_source_statement : Prop :=
  audit_pre_place_full_source_statement /\ audit_pre_certificate_full_source_statement /\
  audit_pre_implementation_adequacy_statement /\ full_snapshot_value_law /\
    full_snapshot_semantics_law /\
  full_snapshot_pre_laws /\ full_snapshot_pre_behavior.

(** At any embedded original state, old values read the current state and fresh values read
    the initial state. *)
Definition audit_pre_full_snapshot_value_statement : Prop := full_snapshot_value_law.

(** The full snapshot adapter preserves all source behaviors. *)
Definition audit_pre_full_snapshot_semantics_statement : Prop := full_snapshot_semantics_law.

(** Under the source and syntax laws, the full snapshot adapter satisfies PRE structural laws. *)
Definition audit_pre_full_snapshot_laws_statement : Prop := full_snapshot_pre_laws.

(** Realized transformed placement preserves the complete old-state source behavior. *)
Definition audit_pre_full_snapshot_behavior_statement : Prop := full_snapshot_pre_behavior.
