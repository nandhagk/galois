(** * Finite instruction points and edge operands

    Instruction points retain ordered blocks and individual incoming phi edges.
    For example, parallel block edges can read different arguments before one parameter edge.
    Builds on: ProgramSsa, ProgramCfg and GraphDomSpec. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa.
Import List.ListNotations.

(** A point-use model is a variable presentation, including its encodings. *)
Definition point_uses := Vars.t.
Definition live_graph {N E V} (p : point_uses N E V) := Cfg.graph (Vars.cfg p).
Definition edge_use {N E V} (p : point_uses N E V) := Vars.uses p.
Definition edge_def {N E V} (p : point_uses N E V) := Vars.defs p.
Definition exit_use {N E V} (p : point_uses N E V) := Vars.exits p.

(** A value is live when a finite edge sequence reaches a use before killing it. *)
Inductive syntactic_live {N E V} (p : point_uses N E V) (x : V) : N -> Prop :=
  | live_exit : forall n, In x (exit_use p n) -> syntactic_live p x n
  | live_edge_use : forall n e, In e (Graph.out (live_graph p) n) ->
      In x (edge_use p e) -> syntactic_live p x n
  | live_edge_next : forall n e, In e (Graph.out (live_graph p) n) ->
      ~ In x (edge_def p e) -> syntactic_live p x (Graph.target (live_graph p) e) ->
      syntactic_live p x n.
Arguments live_exit {N E V p x} n _.
Arguments live_edge_use {N E V p x} n e _ _.
Arguments live_edge_next {N E V p x} n e _ _ _.

(** A point reads a value at an exit or on an outgoing edge occurrence. *)
Definition point_use_at {N E V} (p : point_uses N E V) n x : Prop :=
  In x (exit_use p n) \/
  exists e, In e (Graph.out (live_graph p) n) /\ In x (edge_use p e).

Local Lemma syntactic_live_path_sound {N E V} (p : point_uses N E V) x n :
  graph_wf (live_graph p) -> syntactic_live p x n ->
  exists m es, path (live_graph p) n es m /\
    Forall (fun e => ~ In x (edge_def p e)) es /\ point_use_at p m x.
Proof.
  intros Hwf Hlive; induction Hlive as [n Hexit|n e Hedge Huse|n e Hedge Hkill Hlive IH].
  - exists n, []; split; [constructor|split; [constructor|left; exact Hexit]].
  - exists n, []; split; [constructor|split; [constructor|right; exists e; auto]].
  - destruct IH as [m [es [Hpath [Hkills Huse]]]].
    exists m, (e :: es); split.
    + pose proof (out_source Hwf n e Hedge) as Hsource.
      rewrite <- Hsource; constructor; [rewrite Hsource; exact Hedge|exact Hpath].
    + split; [constructor; assumption|exact Huse].
Qed.

Local Lemma syntactic_live_path_complete {N E V} (p : point_uses N E V) x n m es :
  path (live_graph p) n es m ->
  Forall (fun e => ~ In x (edge_def p e)) es -> point_use_at p m x ->
  syntactic_live p x n.
Proof.
  intro Hpath; induction Hpath as [n|e es m Hedge Hpath IH]; intros Hkills Huse.
  - destruct Huse as [Hexit|[e [Hedge Huse]]].
    + apply live_exit; exact Hexit.
    + eapply live_edge_use; eassumption.
  - inversion Hkills as [|a rest Hkill Htail]; subst.
    eapply live_edge_next; [exact Hedge|exact Hkill|apply IH; assumption].
Qed.

(** The kill-free prefix omits the terminal use edge, which may itself define the value. *)
Theorem syntactic_live_path_iff {N E V} (p : point_uses N E V) x n :
  graph_wf (live_graph p) ->
  (syntactic_live p x n <->
    exists m es, path (live_graph p) n es m /\
      Forall (fun e => ~ In x (edge_def p e)) es /\ point_use_at p m x).
Proof.
  intro Hwf; split.
  - apply syntactic_live_path_sound; exact Hwf.
  - intros [m [es [Hpath [Hkills Huse]]]].
    eapply syntactic_live_path_complete; eassumption.
Qed.

(** A chain lists successive points and the edges between adjacent points. *)
Inductive point_chain {N E} (g : Graph.t N E) : list N -> list E -> Prop :=
  | point_chain_one : forall n, point_chain g [n] []
  | point_chain_step : forall n m ns e es,
      In e (Graph.out g n) -> Graph.target g e = m ->
      point_chain g (m :: ns) es -> point_chain g (n :: m :: ns) (e :: es).
Arguments point_chain_one {N E g} n.
Arguments point_chain_step {N E g} n m ns e es _ _ _.

Module SsaPoints.

(** Ordered point and block presentations retain all encodings and charged syntax readers. *)
Record t (B BE N E V : Type) := Make {
  point_model : point_uses N E V;
  block_cfg : Cfg.t B BE;
  points_in_block_c : B -> Cost.t (list N);
  instruction_edges_c : B -> Cost.t (list E);
  parameter_edge_c : B -> Cost.t E;
  block_of_point_c : N -> Cost.t B;
  block_edge_of_c : E -> Cost.t (option BE);
  block_params_c : B -> Cost.t (list V);
  block_edge_args_c : BE -> Cost.t (list V);
  point_definition_c : V -> Cost.t (option N)
}.
Arguments Make {B BE N E V}.
Arguments point_model {B BE N E V}.
Arguments block_cfg {B BE N E V}.
Arguments points_in_block_c {B BE N E V}.
Arguments instruction_edges_c {B BE N E V}.
Arguments parameter_edge_c {B BE N E V}.
Arguments block_of_point_c {B BE N E V}.
Arguments block_edge_of_c {B BE N E V}.
Arguments block_params_c {B BE N E V}.
Arguments block_edge_args_c {B BE N E V}.
Arguments point_definition_c {B BE N E V}.

Definition block_graph {B BE N E V} (s : t B BE N E V) := Cfg.graph (block_cfg s).
Definition points_in_block {B BE N E V} (s : t B BE N E V) b :=
  Cost.value (points_in_block_c s b).
Definition instruction_edges {B BE N E V} (s : t B BE N E V) b :=
  Cost.value (instruction_edges_c s b).
Definition parameter_edge {B BE N E V} (s : t B BE N E V) b :=
  Cost.value (parameter_edge_c s b).
Definition block_of_point {B BE N E V} (s : t B BE N E V) n :=
  Cost.value (block_of_point_c s n).
Definition block_edge_of {B BE N E V} (s : t B BE N E V) e :=
  Cost.value (block_edge_of_c s e).
Definition block_params {B BE N E V} (s : t B BE N E V) b :=
  Cost.value (block_params_c s b).
Definition block_edge_args {B BE N E V} (s : t B BE N E V) e :=
  Cost.value (block_edge_args_c s e).
Definition point_definition {B BE N E V} (s : t B BE N E V) v :=
  Cost.value (point_definition_c s v).

(** Pure point readers use the same one-tick primitive convention as SSA readers. *)
Definition of_pure {B BE N E V} pm bc points instructions parameter owner projection
    params args definition : t B BE N E V :=
  Make pm bc (Cost.lift (fun _ => 1%N) points) (Cost.lift (fun _ => 1%N) instructions)
    (Cost.lift (fun _ => 1%N) parameter) (Cost.lift (fun _ => 1%N) owner)
    (Cost.lift (fun _ => 1%N) projection) (Cost.lift (fun _ => 1%N) params)
    (Cost.lift (fun _ => 1%N) args) (Cost.lift (fun _ => 1%N) definition).

(** A block SSA presentation supplies its actual CFG, parameters and incoming operands. *)
Definition of_ssa {B BE N E V K G} pm (p : Ssa.t B BE V K G)
    points instructions parameter owner projection definition : t B BE N E V :=
  Make pm (Ssa.cfg p) points instructions parameter owner projection
    (Ssa.params_c p) (Ssa.args_c p) definition.

End SsaPoints.
Import SsaPoints.

(** Point chains retain all blocks and each incoming edge reads its own phi operands. *)
Record ssa_point_laws {B BE N E V} (s : SsaPoints.t B BE N E V) : Prop := {
  points_graph_wf : graph_wf (live_graph (point_model s));
  points_out_nodup : forall n, NoDup (Graph.out (live_graph (point_model s)) n);
  blocks_graph_wf : graph_wf (block_graph s);
  blocks_out_nodup : forall b, NoDup (Graph.out (block_graph s) b);
  points_covered : forall n, In n (Graph.nodes (live_graph (point_model s))) <->
    exists b, In b (Graph.nodes (block_graph s)) /\ In n (points_in_block s b);
  points_unique : forall b, NoDup (points_in_block s b);
  points_owner : forall b n, In b (Graph.nodes (block_graph s)) ->
    In n (points_in_block s b) -> block_of_point s n = b;
  blocks_nonempty : forall b, In b (Graph.nodes (block_graph s)) -> points_in_block s b <> [];
  points_ordered : forall b, In b (Graph.nodes (block_graph s)) ->
    point_chain (live_graph (point_model s)) (points_in_block s b) (instruction_edges s b);
  instruction_edges_internal : forall b e,
    In b (Graph.nodes (block_graph s)) -> In e (instruction_edges s b) ->
    block_edge_of s e = None;
  instruction_edges_complete : forall n e,
    In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) -> block_edge_of s e = None ->
    In e (instruction_edges s (block_of_point s n));
  parameter_edge_first : forall b, In b (Graph.nodes (block_graph s)) ->
    nth_error (instruction_edges s b) 0 = Some (parameter_edge s b);
  parameter_edge_defs : forall b x, In b (Graph.nodes (block_graph s)) ->
    (In x (edge_def (point_model s) (parameter_edge s b)) <-> In x (block_params s b));
  point_edge_projection : forall n e, In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) ->
    match block_edge_of s e with
    | None =>
      block_of_point s n = block_of_point s (Graph.target (live_graph (point_model s)) e)
    | Some be =>
      In be (Graph.out (block_graph s) (block_of_point s n)) /\
      Graph.target (block_graph s) be =
        block_of_point s (Graph.target (live_graph (point_model s)) e) /\
      last (points_in_block s (block_of_point s n)) n = n /\
      nth_error (points_in_block s (Graph.target (block_graph s) be)) 0 =
        Some (Graph.target (live_graph (point_model s)) e)
    end;
  phi_args_length : forall be, In be (Cfg.edges (block_cfg s)) ->
    length (block_edge_args s be) = length (block_params s (Graph.target (block_graph s) be));
  phi_edge_use : forall n e be, In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) -> block_edge_of s e = Some be ->
    forall x, In x (block_edge_args s be) -> In x (edge_use (point_model s) e);
  block_edge_covered : forall be, In be (Cfg.edges (block_cfg s)) ->
    exists n e, In n (Graph.nodes (live_graph (point_model s))) /\
      In e (Graph.out (live_graph (point_model s)) n) /\ block_edge_of s e = Some be;
  block_edge_unique : forall e1 e2 be,
    In e1 (Cfg.edges (Vars.cfg (point_model s))) ->
    In e2 (Cfg.edges (Vars.cfg (point_model s))) ->
    block_edge_of s e1 = Some be -> block_edge_of s e2 = Some be -> e1 = e2
}.
Arguments points_graph_wf {B BE N E V s}.
Arguments points_out_nodup {B BE N E V s}.
Arguments blocks_graph_wf {B BE N E V s}.
Arguments blocks_out_nodup {B BE N E V s}.
Arguments points_covered {B BE N E V s}.
Arguments points_unique {B BE N E V s}.
Arguments points_owner {B BE N E V s}.
Arguments blocks_nonempty {B BE N E V s}.
Arguments points_ordered {B BE N E V s}.
Arguments instruction_edges_internal {B BE N E V s}.
Arguments instruction_edges_complete {B BE N E V s}.
Arguments parameter_edge_first {B BE N E V s}.
Arguments parameter_edge_defs {B BE N E V s}.
Arguments point_edge_projection {B BE N E V s}.
Arguments phi_args_length {B BE N E V s}.
Arguments phi_edge_use {B BE N E V s}.
Arguments block_edge_covered {B BE N E V s}.
Arguments block_edge_unique {B BE N E V s}.

(** Static definition homes are unique on the reachable graph regardless of loop counts. *)
Record reachable_point_ssa {B BE N E V} (s : SsaPoints.t B BE N E V) : Prop := {
  point_ssa_single_entry : exists entry, Graph.entries (live_graph (point_model s)) = [entry];
  point_ssa_uses_defined : forall n x,
    reachable (live_graph (point_model s)) n -> point_use_at (point_model s) n x ->
    exists d, point_definition s x = Some d /\
      reachable (live_graph (point_model s)) d /\
      strictly_dominates (live_graph (point_model s)) d n;
  point_ssa_defs_at_home : forall n e x,
    reachable (live_graph (point_model s)) n ->
    In e (Graph.out (live_graph (point_model s)) n) ->
    In x (edge_def (point_model s) e) -> point_definition s x = Some n;
  point_ssa_home_kills : forall x d e,
    point_definition s x = Some d -> reachable (live_graph (point_model s)) d ->
    In e (Graph.out (live_graph (point_model s)) d) -> In x (edge_def (point_model s) e)
}.
Arguments point_ssa_single_entry {B BE N E V s}.
Arguments point_ssa_uses_defined {B BE N E V s}.
Arguments point_ssa_defs_at_home {B BE N E V s}.
Arguments point_ssa_home_kills {B BE N E V s}.

(** Two reachable static definition sites of one value are the same point. *)
Theorem point_ssa_definitions_unique {B BE N E V} (s : SsaPoints.t B BE N E V)
    (Hssa : reachable_point_ssa s) n1 n2 e1 e2 x :
  reachable (live_graph (point_model s)) n1 ->
  reachable (live_graph (point_model s)) n2 ->
  In e1 (Graph.out (live_graph (point_model s)) n1) ->
  In e2 (Graph.out (live_graph (point_model s)) n2) ->
  In x (edge_def (point_model s) e1) -> In x (edge_def (point_model s) e2) -> n1 = n2.
Proof.
  intros Hn1 Hn2 He1 He2 Hdef1 Hdef2.
  pose proof (point_ssa_defs_at_home Hssa n1 e1 x Hn1 He1 Hdef1) as Hhome1.
  pose proof (point_ssa_defs_at_home Hssa n2 e2 x Hn2 He2 Hdef2) as Hhome2.
  rewrite Hhome1 in Hhome2; inversion Hhome2; reflexivity.
Qed.
