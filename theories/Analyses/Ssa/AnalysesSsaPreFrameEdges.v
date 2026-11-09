(** * Incoming block-edge to point-edge correspondence

    A charged single pass indexes each crossing point-edge under its exact block-edge identity.
    For example, two parallel incoming edges retain two separate point-edge observations.
    Builds on: AnalysesSsaPreFrameCache, ProgramSsaPoints and the public map contracts. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Framework Require Import FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrameCache.
Import List.ListNotations Cost.Notations.

Module PreFrameEdges.

Section Edges.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let points := Pre.points (Pre.input c).

Definition edge_pair_c e :=
  Cost.step ;;
  let* be := SsaPoints.block_edge_of_c points e in
  Cost.ret (option_map (fun be => (be, e)) be).

Definition edge_pairs_c :=
  let* edges := fw_edges_c (Pre.point_cfg c) in
  Prepared.present_c edge_pair_c edges.
Definition edge_pairs := Cost.value edge_pairs_c.

(** The public incoming-point index is constructed once from ordered source edge occurrences. *)
Definition point_edge_index_c :=
  let* pairs := edge_pairs_c in
  Map.of_list_c (Pre.ebe (Pre.keys c)) pairs.
Definition point_edge_index := Cost.value point_edge_index_c.

(** Each crossing callback retains the original point edge and its own block-edge identity. *)
Theorem edge_pair_value e :
  Cost.value (edge_pair_c e) =
    option_map (fun be => (be, e)) (SsaPoints.block_edge_of points e).
Proof.
  unfold edge_pair_c; rewrite !Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** The ordered pair inventory contains precisely the original crossing point-edge occurrences. *)
Theorem edge_pairs_exact be e :
  In (be, e) edge_pairs <->
    In e (Cfg.edges (Pre.point_cfg c)) /\ SsaPoints.block_edge_of points e = Some be.
Proof.
  unfold edge_pairs, edge_pairs_c; rewrite Cost.value_bind, fw_edges_value,
    Prepared.present_c_value, Prepared.present_spec; split.
  - intros [edge [He Hpair]]; rewrite edge_pair_value in Hpair.
    destruct (SsaPoints.block_edge_of points edge) as [block|] eqn:Hproject;
      cbn [option_map] in Hpair; [|discriminate].
    inversion Hpair; subst edge block; auto.
  - intros [He Hproject]; exists e; split; [exact He|].
    rewrite edge_pair_value, Hproject; reflexivity.
Qed.

(** Constructing the index retains the actual ordered pair inventory without a graph rescan. *)
Theorem point_edge_index_equation :
  point_edge_index = Map.of_list (Pre.ebe (Pre.keys c)) edge_pairs.
Proof.
  unfold point_edge_index, point_edge_index_c; rewrite Cost.value_bind; reflexivity.
Qed.

Local Lemma assignment_unique {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (pairs : list (X * Y)) x y :
  (forall value, In (x, value) pairs -> value = y) ->
  In (x, y) pairs -> Map.get enc x (Map.of_list enc pairs) = Some y.
Proof.
  intros Hunique Hin; rewrite Map.of_list_get.
  assert (Hfold : forall rest old, incl rest pairs ->
    (old = Some y \/ In (x, y) rest) ->
    fold_left (fun acc pair =>
      if eqb enc x (fst pair) then Some (snd pair) else acc) rest old = Some y).
  { intros rest; induction rest as [|[key value] rest IH]; intros old Hsub Hhit.
    - destruct Hhit as [Hvalue|[]]; exact Hvalue.
    - cbn [fold_left fst snd]; destruct (eqb enc x key) eqn:Hsame.
      + apply (eqb_true_iff _ HE) in Hsame; subst key.
        assert (Hvalue : value = y) by (apply Hunique; apply Hsub; now left).
        subst value; apply IH; [intros pair Hpair; apply Hsub; now right|now left].
      + apply IH; [intros pair Hpair; apply Hsub; now right|].
        destruct Hhit as [Hold|[Heq|Hrest]]; [now left| |now right].
        inversion Heq; subst key value; rewrite eqb_refl in Hsame; discriminate. }
  apply Hfold; [apply incl_refl|now right].
Qed.

(** A lawful point presentation identifies exactly one crossing point edge for each stored block edge. *)
Theorem point_edge_index_exact :
  Pre.laws c ->
  forall be e, Map.get (Pre.ebe (Pre.keys c)) be point_edge_index = Some e <->
    In e (Cfg.edges (Pre.point_cfg c)) /\ SsaPoints.block_edge_of points e = Some be.
Proof.
  intros Hlaw be e; rewrite point_edge_index_equation; split.
  - intro Hget; apply edge_pairs_exact.
    exact (PreFrameCache.assignment_sound _ (Pre.ebe_laws c (Pre.graphs c Hlaw))
      edge_pairs be e Hget).
  - intros [He Hproject]; apply (assignment_unique _ (Pre.ebe_laws c (Pre.graphs c Hlaw))).
    + intros other Hpair; apply edge_pairs_exact in Hpair; destruct Hpair as [Hother Hcross].
      exact (block_edge_unique (Pre.point_laws c (Pre.graphs c Hlaw)) other e be
        Hother He Hcross Hproject).
    + apply edge_pairs_exact; auto.
Qed.

(** Every listed incoming block-edge identity has a point-edge representative in the same index. *)
Theorem point_edge_index_total :
  Pre.laws c ->
  forall be, In be (Cfg.edges (Pre.block_cfg c)) ->
    exists e, Map.get (Pre.ebe (Pre.keys c)) be point_edge_index = Some e.
Proof.
  intros Hlaw be Hbe.
  destruct (block_edge_covered (Pre.point_laws c (Pre.graphs c Hlaw)) be Hbe)
    as [n [e [Hn [Hout Hcross]]]].
  exists e; apply (point_edge_index_exact Hlaw); split; [|exact Hcross].
  apply Cfg.edges_spec; exists n; auto.
Qed.

(** A stored crossing leaves the actual last point of its source block and enters the target first point. *)
Theorem point_edge_boundary :
  Pre.laws c ->
  forall be e, Map.get (Pre.ebe (Pre.keys c)) be point_edge_index = Some e ->
    last (SsaPoints.points_in_block points (Graph.source (Pre.bg c) be))
      (Graph.source (Pre.pg c) e) = Graph.source (Pre.pg c) e /\
    nth_error (SsaPoints.points_in_block points (Graph.target (Pre.bg c) be)) 0 =
      Some (Graph.target (Pre.pg c) e).
Proof.
  intros Hlaw be e Hget.
  destruct (proj1 (point_edge_index_exact Hlaw be e) Hget) as [He Hcross].
  apply Cfg.edges_spec in He; destruct He as [n [Hn Hout]].
  pose proof (point_edge_projection (Pre.point_laws c (Pre.graphs c Hlaw)) n e Hn Hout) as Hpoint.
  fold points in Hpoint; rewrite Hcross in Hpoint.
  destruct Hpoint as [Hbe [Htarget [Hlast Hfirst]]].
  pose proof (out_source (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw))) _ be Hbe)
    as Hsource_block.
  pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw))) n e Hout)
    as Hsource_point.
  change (Graph.source (Pre.bg c) be = SsaPoints.block_of_point points n) in Hsource_block.
  change (Graph.source (Pre.pg c) e = n) in Hsource_point.
  rewrite Hsource_block, Hsource_point; exact (conj Hlast Hfirst).
Qed.

(** The single-pass index retains edge enumeration, crossing callbacks and map materialization charges. *)
Theorem point_edge_index_cost :
  Cost.ticks point_edge_index_c =
    (Cost.ticks (fw_edges_c (Pre.point_cfg c)) +
      Cost.ticks (Prepared.present_c edge_pair_c (Cfg.edges (Pre.point_cfg c))) +
      Cost.ticks (Map.of_list_c (Pre.ebe (Pre.keys c)) edge_pairs))%N.
Proof.
  unfold point_edge_index_c; rewrite Cost.ticks_bind.
  fold edge_pairs; unfold edge_pairs_c; rewrite Cost.ticks_bind, fw_edges_value; reflexivity.
Qed.

End Edges.

End PreFrameEdges.
