(** * Alteration coverage and the meaning of scoped frames

    Frame laws retain the nearest definition even after availability has been invalidated.
    For example, an unused phi can become an unsafe seed while its definition remains nearest.
    Builds on: AnalysesSsaPreRename and GraphFrontierSpec. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom
  GraphFrontierSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename.
Import List.ListNotations.

Module PreCoverage.

Local Open Scope nat_scope.

Section Coverage.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** The frontier of an operand's home is a required expression phi boundary. *)
Theorem operand_frontier_phi :
  forall u x b, PreFamily.in_family c u -> In x (Pre.operands c u) ->
    in_df (Pre.bg c) (Ssa.home (Pre.ssa (Pre.input c)) x) b ->
    PreFrg.phi_needed c u b.
Proof.
  intros u x b Hfamily Hoperand Hfrontier.
  eapply PreFrg.phi_seed; [exact Hfamily| |exact Hfrontier].
  apply PreFrg.definition_operand; exact Hoperand.
Qed.

(** Every killing definition's block frontier is covered by an expression phi. *)
Theorem kill_frontier_phi :
  Pre.laws c ->
  forall u e b, PreFamily.in_family c u -> In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.killed c e u = true ->
    in_df (Pre.bg c)
      (SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e)) b ->
    PreFrg.phi_needed c u b.
Proof.
  intros Hlaw u e b Hfamily He Hkill Hfrontier.
  destruct (Pre.kill_operand c (Pre.kills c Hlaw) e u He Hfamily Hkill)
    as [x [Hx Hdef]].
  pose proof (Pre.def_home c (Pre.kills c Hlaw) e x He Hdef) as Hhome.
  eapply operand_frontier_phi; [exact Hfamily|exact Hx|].
  rewrite Hhome; exact Hfrontier.
Qed.

(** A real-use witness names its selected occurrence and the dominance of its target. *)
Definition real_use_at (g : PreFrg.frg B BE E U) n d : Prop :=
  exists e, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d /\
    dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n.

(** No graph definition of the expression dominates the point. *)
Definition no_reaching_version (g : PreFrg.frg B BE E U) u n : Prop :=
  forall d q, In d (PreFrg.versions g) -> PreFrg.version_expr d = u ->
    PreFrg.version_point c d = Some q -> ~ dominates (Pre.pg c) q n.

(** Alterations below a definition and dominating a use are precisely its local killing events. *)
Definition no_dominating_kill u q n : Prop :=
  forall e, In e (Cfg.edges (Pre.point_cfg c)) ->
    strictly_dominates (Pre.pg c) q (Graph.target (Pre.pg c) e) ->
    dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n -> Pre.killed c e u = false.

(** Frame availability and real-use bits describe the same selected definition at this point. *)
Definition frame_laws (g : PreFrg.frg B BE E U) u n (frame : PreRename.frame B E U) : Prop :=
  let d := PreFrg.operand_version (PreRename.selected frame) in
  PreFrg.version_expr d = u /\
  (PreFrg.real_use (PreRename.selected frame) = true <-> real_use_at g n d) /\
  match PreFrg.version_point c d with
  | Some q => PreRename.nearest_version c g u n d /\
      (PreRename.available frame = true <-> no_dominating_kill u q n)
  | None => d = PreFrg.Unavailable u /\ PreRename.available frame = false /\
      no_reaching_version g u n
  end.

(** Each eligible expression has a frame meaning at the same point of the scope. *)
Definition scope_laws (g : PreFrg.frg B BE E U) n (frames : PreRename.scope B E U) : Prop :=
  forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
    frame_laws g u n (PreRename.top c frames u).

(** Provenance records expression identity, dominance and a definition for every available frame. *)
Definition frame_sound u n (frame : PreRename.frame B E U) : Prop :=
  let d := PreFrg.operand_version (PreRename.selected frame) in
  PreFrg.version_expr d = u /\
  (forall q, PreFrg.version_point c d = Some q -> dominates (Pre.pg c) q n) /\
  (PreRename.available frame = true -> exists q, PreFrg.version_point c d = Some q).

Definition scope_sound n (frames : PreRename.scope B E U) : Prop :=
  forall u, frame_sound u n (PreRename.top c frames u).

(** Full frame meaning supplies expression and definition provenance without any output premise. *)
Theorem frame_laws_sound (g : PreFrg.frg B BE E U) :
  forall u n frame, frame_laws g u n frame -> frame_sound u n frame.
Proof.
  intros u n frame [Hexpr [Hreal Hmeaning]].
  unfold frame_sound; split; [exact Hexpr|].
  destruct (PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)))
    as [q|] eqn:Hpoint.
  - destruct Hmeaning as [Hnearest Havailable].
    destruct Hnearest as [_ [_ [p [Hp [Hdom Hminimal]]]]].
    assert (p = q) by congruence; subst p.
    split.
    + intros other Hother; inversion Hother; subst other; exact Hdom.
    + intros _; exists q; reflexivity.
  - destruct Hmeaning as [_ [Hfalse Hnone]]; split.
    + intros q Hq; discriminate.
    + intro Htrue; congruence.
Qed.

(** Definition provenance remains valid at every dominated point. *)
Theorem frame_sound_monotone :
  forall u n target frame, dominates (Pre.pg c) n target ->
    frame_sound u n frame -> frame_sound u target frame.
Proof.
  intros u n target frame Hdom [Hexpr [Hpoint Havailable]].
  split; [exact Hexpr|]; split; [|exact Havailable].
  intros q Hq; eapply dominates_trans; [apply Hpoint; exact Hq|exact Hdom].
Qed.

(** An unavailable frame excludes every dominating graph definition of its expression. *)
Theorem unavailable_frame_excludes (g : PreFrg.frg B BE E U) :
  forall u n frame, frame_laws g u n frame ->
    PreFrg.operand_version (PreRename.selected frame) = PreFrg.Unavailable u ->
    no_reaching_version g u n.
Proof.
  intros u n frame [_ [_ Hmeaning]] Hmissing.
  rewrite Hmissing, PreFrg.version_point_equation in Hmeaning.
  exact (proj2 (proj2 Hmeaning)).
Qed.

End Coverage.

Section Geometry.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let s := Pre.points (Pre.input c).

(** A listed edge is outgoing from its own listed source point. *)
Lemma listed_edge_out {e} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  In (Graph.source (Pre.pg c) e) (Graph.nodes (Pre.pg c)) /\
    In e (Graph.out (Pre.pg c) (Graph.source (Pre.pg c) e)).
Proof.
  intros Hlaw He; apply Cfg.edges_spec in He; destruct He as [n [Hn He]].
  pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw))) n e He)
    as Hsource.
  change (Graph.source (Pre.pg c) e = n) in Hsource; rewrite Hsource; auto.
Qed.

(** Every ordered instruction occurrence belongs to the original finite point-edge inventory. *)
Lemma instruction_edge_listed {b e} :
  Pre.laws c -> In b (Graph.nodes (Pre.bg c)) ->
  In e (SsaPoints.instruction_edges s b) -> In e (Cfg.edges (Pre.point_cfg c)).
Proof.
  intros Hlaw Hb He; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (PreFrg.chain_source _ (points_ordered Hpoints b Hb) He) as [n [Hn Hedge]].
  apply Cfg.edges_spec; exists n; split; [|exact Hedge].
  apply (points_covered Hpoints); exists b; auto.
Qed.

(** A completed internal instruction is strictly beyond every block's first point. *)
Lemma internal_target_not_first {e b first} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> In b (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
  Graph.target (Pre.pg c) e <> first.
Proof.
  intros Hlaw He Hi Hb Hfirst Heq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (PreFrg.internal_edge_block c Hlaw He Hi) as [owner [Ho [Hedge Htarget]]].
  fold s in Htarget.
  assert (Howner : owner = b).
  { rewrite <- (points_owner Hpoints owner _ Ho (PreFrg.tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)). }
  subst owner; rewrite Heq in Htarget.
  pose proof (points_unique Hpoints b) as Hunique.
  destruct (SsaPoints.points_in_block s b) as [|head rest]; cbn [nth_error] in Hfirst;
    [discriminate|].
  inversion Hfirst; subst head; apply NoDup_cons_iff in Hunique; tauto.
Qed.

(** An internal instruction target has no different listed incoming point-edge occurrence. *)
Lemma internal_incoming_unique {e other} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> In other (Cfg.edges (Pre.point_cfg c)) ->
  Graph.target (Pre.pg c) other = Graph.target (Pre.pg c) e -> other = e.
Proof.
  intros Hlaw He Hi Hother Htarget.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (SsaPoints.block_edge_of s other) as [be|] eqn:Hcross.
  - apply Cfg.edges_spec in Hother; destruct Hother as [n [Hn Hedge]].
    pose proof (point_edge_projection Hpoints n other Hn Hedge) as Hprojection.
    rewrite Hcross in Hprojection; destruct Hprojection as [Hbe [Ht [Hlast Hfirst]]].
    destruct (PreFrg.point_owner_listed c Hlaw Hn) as [Hb Hpoint].
    pose proof (out_target_in (blocks_graph_wf Hpoints) _ be Hb Hbe) as Hblock.
    exfalso; apply (internal_target_not_first Hlaw He Hi Hblock Hfirst).
    symmetry; exact Htarget.
  - eapply PreFrg.internal_target_unique; eassumption.
Qed.

Local Lemma unique_incoming_dominates {e} :
  Pre.laws c ->
  (forall n, In n (Graph.entries (Pre.pg c)) -> Graph.target (Pre.pg c) e <> n) ->
  (forall other, In other (Cfg.edges (Pre.point_cfg c)) ->
    Graph.target (Pre.pg c) other = Graph.target (Pre.pg c) e -> other = e) ->
  dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e).
Proof.
  intros Hlaw Hentry Hunique start es Hstart Hpath.
  destruct es as [|a rest].
  - inversion Hpath; subst; exfalso; exact (Hentry _ Hstart eq_refl).
  - destruct (PreRename.path_last _ Hpath ltac:(discriminate))
      as [prefix [last [Hsplit [Hprefix [Htarget Hout]]]]].
    assert (Hlisted : In last (Cfg.edges (Pre.point_cfg c))).
    { apply Cfg.edges_spec; exists (Graph.source (Pre.pg c) last); split; [|exact Hout].
      apply (reachable_in_nodes _ _ (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
      apply reachable_iff_path; exists start, prefix; auto. }
    specialize (Hunique last Hlisted Htarget); subst last.
    destruct (PreRename.path_endpoint _ Hprefix) as [Heq|[earlier [Hin Htarget']]].
    + now left.
    + right; exists earlier; split; [rewrite Hsplit; apply in_or_app; now left|exact Htarget'].
Qed.

(** Each internal instruction source dominates its completed target point. *)
Theorem internal_source_dominates {e} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) -> SsaPoints.block_edge_of s e = None ->
    dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e).
Proof.
  intros Hlaw He Hi; apply unique_incoming_dominates; [exact Hlaw| |].
  - intros n Hn; exact (PreFrg.internal_target_not_entry c Hlaw He Hi Hn).
  - intros other Hother Htarget; eapply internal_incoming_unique; eassumption.
Qed.

Local Lemma chain_not_self {X A} (g : Graph.t X A) {ns es} :
  graph_wf g -> point_chain g ns es -> NoDup ns ->
  forall e, In e es -> Graph.source g e <> Graph.target g e.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros Hnodup e Hin; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  destruct Hin as [<-|Hin].
  - rewrite (out_source Hwf n edge Hedge), Htarget; intro Heq; apply Hfresh.
    left; symmetry; exact Heq.
  - exact (IH Htail e Hin).
Qed.

(** Internal instruction targets are immediate point-dominance successors of their sources. *)
Theorem internal_immediate {e} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) -> SsaPoints.block_edge_of s e = None ->
    immediately_dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e).
Proof.
  intros Hlaw He Hi; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (PreFrg.internal_edge_block c Hlaw He Hi) as [b [Hb [Hin Htarget]]].
  split; [split|].
  - apply internal_source_dominates; assumption.
  - exact (chain_not_self _ (points_graph_wf Hpoints) (points_ordered Hpoints b Hb)
      (points_unique Hpoints b) e Hin).
  - intros q Hstrict; exact (PreRename.strict_target_dominates_source _ e q
      (proj2 (listed_edge_out Hlaw He)) Hstrict).
Qed.

(** Every point in an ordered block dominates the last point of that same block. *)
Theorem block_member_dominates_last :
  Pre.laws c ->
  forall b q default, In b (Graph.nodes (Pre.bg c)) -> In q (SsaPoints.points_in_block s b) ->
    dominates (Pre.pg c) q (last (SsaPoints.points_in_block s b) default).
Proof.
  intros Hlaw b q default Hb Hq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  eapply PreRename.chain_member_dominates_last; [exact (points_graph_wf Hpoints)|
    exact (points_ordered Hpoints b Hb)| |exact Hq].
  intros e He; apply internal_source_dominates; [exact Hlaw| |].
  - exact (instruction_edge_listed Hlaw Hb He).
  - exact (instruction_edges_internal Hpoints b e Hb He).
Qed.

Local Lemma nth_index_unique {X} (xs : list X) {i j x} :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof.
  intros Hnodup Hi Hj; apply (proj1 (NoDup_nth_error xs) Hnodup).
  - apply nth_error_Some; congruence.
  - congruence.
Qed.

(** Point dominance within one ordered block agrees exactly
    with the instruction-list index order. *)
Theorem block_instruction_order :
  Pre.laws c ->
  forall b i j q n, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block s b) i = Some q ->
    nth_error (SsaPoints.points_in_block s b) j = Some n ->
    (dominates (Pre.pg c) q n <-> i <= j).
Proof.
  intros Hlaw b i j q n Hb Hq Hn.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  assert (Hforward : forall k l x y,
    nth_error (SsaPoints.points_in_block s b) k = Some x ->
    nth_error (SsaPoints.points_in_block s b) l = Some y -> k <= l -> dominates (Pre.pg c) x y).
  { apply (PreRename.chain_index_dominates _
      (points_graph_wf Hpoints) (points_ordered Hpoints b Hb)).
    intros e He; apply internal_source_dominates; [exact Hlaw| |].
    - exact (instruction_edge_listed Hlaw Hb He).
    - exact (instruction_edges_internal Hpoints b e Hb He). }
  split; [|exact (Hforward i j q n Hq Hn)].
  intro Hdom; destruct (Nat.le_gt_cases i j) as [Hle|Hgt]; [exact Hle|].
  assert (Heq : q = n).
  { apply (dominates_antisym_reachable (Pre.en (Pre.keys c))
      (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c)).
    - apply (Pre.reachable_points c (Pre.graphs c Hlaw)); apply (points_covered Hpoints).
      exists b; split; [exact Hb|exact (nth_error_In _ _ Hq)].
    - apply (Pre.reachable_points c (Pre.graphs c Hlaw)); apply (points_covered Hpoints).
      exists b; split; [exact Hb|exact (nth_error_In _ _ Hn)].
    - exact Hdom.
    - apply (Hforward j i n q Hn Hq); lia. }
  subst n; pose proof (nth_index_unique _ (points_unique Hpoints b) Hq Hn); lia.
Qed.

(** Projection preserves ordered concatenation of point-edge occurrences. *)
Lemma project_edges_app xs ys :
  PreRename.project_edges c (xs ++ ys) =
    PreRename.project_edges c xs ++ PreRename.project_edges c ys.
Proof.
  rewrite !PreRename.project_edges_equation, flat_map_app; reflexivity.
Qed.

(** Each projected block edge retains its actual point-edge occurrence witness. *)
Lemma project_edges_member es be :
  In be (PreRename.project_edges c es) <->
    exists e, In e es /\ SsaPoints.block_edge_of s e = Some be.
Proof.
  rewrite PreRename.project_edges_equation, in_flat_map; split.
  - intros [e [He Hin]]; fold s in Hin.
    destruct (SsaPoints.block_edge_of s e) as [block|] eqn:Hcross; [|contradiction].
    destruct Hin as [<-|[]]; exists e; auto.
  - intros [e [He Hcross]]; exists e; split; [exact He|].
    fold s; rewrite Hcross; now left.
Qed.

(** A point path inside one instruction chain has an empty block-edge projection. *)
Lemma project_internal es :
  (forall e, In e es -> SsaPoints.block_edge_of s e = None) ->
    PreRename.project_edges c es = nil.
Proof.
  intro Hinternal; rewrite PreRename.project_edges_equation.
  induction es as [|e rest IH]; [reflexivity|].
  cbn [flat_map]; fold s; rewrite (Hinternal e (or_introl eq_refl)).
  apply IH; intros a Ha; apply Hinternal; now right.
Qed.

Local Lemma point_path_listed {start es finish} :
  Pre.laws c -> In start (Graph.nodes (Pre.pg c)) -> path (Pre.pg c) start es finish ->
    incl es (Cfg.edges (Pre.point_cfg c)).
Proof.
  intros Hlaw Hstart Hpath; revert Hstart.
  induction Hpath as [n|e rest finish He Hpath IH]; intros Hstart a Ha; [contradiction|].
  destruct Ha as [<-|Ha].
  - apply Cfg.edges_spec; exists (Graph.source (Pre.pg c) e); auto.
  - apply IH; [|exact Ha].
    exact (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw))) _ e Hstart He).
Qed.

Local Lemma lift_block_edge {be first} :
  Pre.laws c -> In be (Cfg.edges (Pre.block_cfg c)) ->
  nth_error (SsaPoints.points_in_block s (Graph.source (Pre.bg c) be)) 0 = Some first ->
  exists es next, path (Pre.pg c) first es next /\
    nth_error (SsaPoints.points_in_block s (Graph.target (Pre.bg c) be)) 0 = Some next /\
    PreRename.project_edges c es = [be].
Proof.
  intros Hlaw Hbe Hfirst.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (block_edge_covered Hpoints be Hbe) as [n [e [Hn [He Hcross]]]].
  pose proof (point_edge_projection Hpoints n e Hn He) as Hprojection.
  rewrite Hcross in Hprojection; destruct Hprojection as [Hout [Htarget [Hlast Hnext]]].
  pose proof (out_source (blocks_graph_wf Hpoints) _ be Hout) as Hsource.
  change (Graph.source (Pre.bg c) be = SsaPoints.block_of_point s n) in Hsource.
  destruct (PreFrg.point_owner_listed c Hlaw Hn) as [Hb Hmember].
  fold s in Hb, Hmember.
  rewrite <- Hsource in Hb, Hlast.
  exists (SsaPoints.instruction_edges s (Graph.source (Pre.bg c) be) ++ [e]),
    (Graph.target (Pre.pg c) e); split.
  - apply (PreRename.path_app (Pre.pg c) _ _ n).
    + rewrite <- Hlast; apply PreRename.chain_path; [exact (points_graph_wf Hpoints)|
        exact (points_ordered Hpoints _ Hb)|exact Hfirst].
    + pose proof (out_source (points_graph_wf Hpoints) n e He) as Hsourcepoint.
      rewrite <- Hsourcepoint; constructor; [rewrite Hsourcepoint; exact He|constructor].
  - split; [exact Hnext|]; rewrite project_edges_app, project_internal.
    + rewrite PreRename.project_edges_equation; cbn [flat_map]; fold s; rewrite Hcross; reflexivity.
    + intros edge Hedge; exact (instruction_edges_internal Hpoints _ edge Hb Hedge).
Qed.

(** A block path lifts to point instructions and crossings
    with exactly the same ordered projection. *)
Theorem lift_block_path :
  Pre.laws c ->
  forall b bes target first, In b (Graph.nodes (Pre.bg c)) -> path (Pre.bg c) b bes target ->
    nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
    exists es next, path (Pre.pg c) first es next /\
      nth_error (SsaPoints.points_in_block s target) 0 = Some next /\
      PreRename.project_edges c es = bes.
Proof.
  intros Hlaw b bes target first Hb Hpath; revert first Hb.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  induction Hpath as [b|be rest target Hbe Hpath IH]; intros first Hb Hfirst.
  - exists nil, first; split; [constructor|auto].
  - assert (Hlisted : In be (Cfg.edges (Pre.block_cfg c))).
    { apply Cfg.edges_spec; exists (Graph.source (Pre.bg c) be); auto. }
    destruct (lift_block_edge Hlaw Hlisted Hfirst) as [prefix [mid [Hprefix [Hmid Hprojected]]]].
    destruct (IH mid (out_target_in (blocks_graph_wf Hpoints) _ be Hb Hbe) Hmid)
      as [suffix [last [Hsuffix [Hlast Hprojected']]]].
    exists (prefix ++ suffix), last; split.
    + eapply PreRename.path_app; eassumption.
    + split; [exact Hlast|rewrite project_edges_app, Hprojected, Hprojected'; reflexivity].
Qed.

Local Lemma point_visit_owner {start es finish q} :
  Pre.laws c -> In start (Graph.nodes (Pre.pg c)) -> path (Pre.pg c) start es finish ->
  (q = start \/ exists e, In e es /\ Graph.target (Pre.pg c) e = q) ->
    SsaPoints.block_of_point s q = SsaPoints.block_of_point s start \/
    exists be, In be (PreRename.project_edges c es) /\
      Graph.target (Pre.bg c) be = SsaPoints.block_of_point s q.
Proof.
  intros Hlaw Hstart Hpath [<-|[e [He Htarget]]]; [now left|].
  destruct (PreRename.path_prefix_target _ Hpath He) as [prefix [Hprefix Hsub]].
  pose proof (PreRename.project_path c Hlaw _ _ _ Hstart Hprefix) as Hprojected.
  fold s in Hprojected; rewrite Htarget in Hprojected.
  destruct (PreRename.path_endpoint _ Hprojected) as [Heq|[be [Hbe Htarget']]].
  - now left.
  - right; exists be; split; [|exact Htarget'].
    apply project_edges_member in Hbe; destruct Hbe as [edge [Hedge Hcross]].
    apply project_edges_member; exists edge; split; [apply Hsub; exact Hedge|exact Hcross].
Qed.

Local Lemma lift_path_to_member :
  Pre.laws c ->
  forall b bes target first n, In b (Graph.nodes (Pre.bg c)) ->
    In target (Graph.nodes (Pre.bg c)) -> path (Pre.bg c) b bes target ->
    nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
    In n (SsaPoints.points_in_block s target) ->
    exists es, path (Pre.pg c) first es n /\ PreRename.project_edges c es = bes.
Proof.
  intros Hlaw b bes target first n Hb Htarget Hpath Hfirst Hmember.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (lift_block_path Hlaw b bes target first Hb Hpath Hfirst)
    as [prefix [mid [Hprefix [Hmid Hprojected]]]].
  destruct (PreRename.chain_prefix _ (points_graph_wf Hpoints)
    (points_ordered Hpoints target Htarget) Hmid n Hmember) as [suffix [Hsuffix Hsub]].
  exists (prefix ++ suffix); split; [eapply PreRename.path_app; eassumption|].
  rewrite project_edges_app, Hprojected, project_internal, app_nil_r; [reflexivity|].
  intros edge Hedge.
  exact (instruction_edges_internal Hpoints target edge Htarget (Hsub edge Hedge)).
Qed.

(** Dominating a point entails dominating its block on every block-entry path. *)
Theorem point_block_dominates {q n} :
  Pre.laws c -> In n (Graph.nodes (Pre.pg c)) -> dominates (Pre.pg c) q n ->
    dominates (Pre.bg c) (SsaPoints.block_of_point s q) (SsaPoints.block_of_point s n).
Proof.
  intros Hlaw Hn Hdom start bes Hstart Hpath.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw))
    as [entry [first [Hblocks [Hentries Hfirst]]]]; fold s in Hfirst.
  rewrite Hblocks in Hstart; destruct Hstart as [<-|[]].
  assert (Hentry : In entry (Graph.nodes (Pre.bg c))).
  { apply (entries_in (blocks_graph_wf Hpoints)).
    change (In entry (Graph.entries (Pre.bg c))); rewrite Hblocks; now left. }
  destruct (PreFrg.point_owner_listed c Hlaw Hn) as [Hb Hmember]; fold s in Hmember.
  destruct (lift_path_to_member Hlaw entry bes _ first n Hentry Hb Hpath Hfirst Hmember)
    as [es [Hpointpath Hprojected]].
  assert (Hpointentry : In first (Graph.entries (Pre.pg c))).
  { rewrite Hentries; now left. }
  destruct (point_visit_owner Hlaw
    (entries_in (points_graph_wf Hpoints) first Hpointentry) Hpointpath
    (Hdom first es Hpointentry Hpointpath)) as [Howner|[be [Hbe Htarget]]].
  - left; rewrite Howner; exact (points_owner Hpoints entry first Hentry (nth_error_In _ _ Hfirst)).
  - right; exists be; split; [rewrite <- Hprojected; exact Hbe|exact Htarget].
Qed.

Local Lemma point_entry_owner {n} :
  Pre.laws c -> In n (Graph.entries (Pre.pg c)) ->
    In (SsaPoints.block_of_point s n) (Graph.entries (Pre.bg c)).
Proof.
  intros Hlaw Hn; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw))
    as [entry [first [Hblocks [Hentries Hfirst]]]]; fold s in Hfirst.
  rewrite Hentries in Hn; destruct Hn as [<-|[]].
  assert (Hentry : In entry (Graph.nodes (Pre.bg c))).
  { apply (entries_in (blocks_graph_wf Hpoints)).
    change (In entry (Graph.entries (Pre.bg c))); rewrite Hblocks; now left. }
  rewrite (points_owner Hpoints entry first Hentry (nth_error_In _ _ Hfirst)), Hblocks; now left.
Qed.

Local Lemma path_departure {b start es n} :
  Pre.laws c -> In start (Graph.nodes (Pre.pg c)) -> path (Pre.pg c) start es n ->
  In (SsaPoints.block_of_point s start) (Graph.entries (Pre.bg c)) ->
  b <> SsaPoints.block_of_point s n ->
  dominates (Pre.bg c) b (SsaPoints.block_of_point s n) ->
  exists e, In e es /\ SsaPoints.block_of_point s (Graph.source (Pre.pg c) e) = b /\
    last (SsaPoints.points_in_block s b) (Graph.source (Pre.pg c) e) = Graph.source (Pre.pg c) e.
Proof.
  intros Hlaw Hstart Hpath Hentry Hne Hdom.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  pose proof (PreRename.project_path c Hlaw _ _ _ Hstart Hpath) as Hprojected; fold s in Hprojected.
  destruct (PreRename.path_leaves _ Hprojected Hne (Hdom _ _ Hentry Hprojected))
    as [be [Hbe Hsource]].
  apply project_edges_member in Hbe; destruct Hbe as [e [He Hcross]].
  destruct (listed_edge_out Hlaw (point_path_listed Hlaw Hstart Hpath e He)) as [Hn Hout].
  pose proof (point_edge_projection Hpoints _ e Hn Hout) as Hprojection.
  rewrite Hcross in Hprojection; destruct Hprojection as [Houtblock [Htarget [Hlast Hfirst]]].
  pose proof (out_source (blocks_graph_wf Hpoints) _ be Houtblock) as Howner.
  change (Graph.source (Pre.bg c) be =
    SsaPoints.block_of_point s (Graph.source (Pre.pg c) e)) in Howner.
  rewrite Hsource in Howner; symmetry in Howner; rewrite Howner in Hlast.
  exists e; auto.
Qed.

(** A point of a dominating different block dominates the queried point. *)
Theorem block_point_dominates :
  Pre.laws c ->
  forall b q n, In b (Graph.nodes (Pre.bg c)) -> In q (SsaPoints.points_in_block s b) ->
    b <> SsaPoints.block_of_point s n ->
    dominates (Pre.bg c) b (SsaPoints.block_of_point s n) -> dominates (Pre.pg c) q n.
Proof.
  intros Hlaw b q n Hb Hq Hne Hdom start es Hentry Hpath.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (path_departure Hlaw (entries_in (points_graph_wf Hpoints) start Hentry)
    Hpath (point_entry_owner Hlaw Hentry) Hne Hdom) as [e [He [Howner Hlast]]].
  pose proof (block_member_dominates_last Hlaw b q (Graph.source (Pre.pg c) e) Hb Hq) as Hsource.
  rewrite Hlast in Hsource.
  destruct (PreRename.path_prefix_source _ Hpath He) as [prefix [Hprefix Hsub]].
  destruct (Hsource start prefix Hentry Hprefix) as [Heq|[earlier [Hearlier Htarget]]].
  - now left.
  - right; exists earlier; split; [apply Hsub; exact Hearlier|exact Htarget].
Qed.

Local Lemma dominator_owner {q n} :
  Pre.laws c -> In n (Graph.nodes (Pre.pg c)) -> dominates (Pre.pg c) q n ->
  In (SsaPoints.block_of_point s q) (Graph.nodes (Pre.bg c)) /\
    In q (SsaPoints.points_in_block s (SsaPoints.block_of_point s q)).
Proof.
  intros Hlaw Hn Hdom; apply PreFrg.point_owner_listed; [exact Hlaw|].
  apply (reachable_in_nodes _ _ (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
  exact (DomCheck.dominator_reachable _ q n (Pre.reachable_points c (Pre.graphs c Hlaw) n Hn) Hdom).
Qed.

(** A strict dominator of a block's first point belongs to a strictly dominating block. *)
Theorem point_strict_dom_first :
  Pre.laws c ->
  forall b first q, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
    strictly_dominates (Pre.pg c) q first ->
    strictly_dominates (Pre.bg c) (SsaPoints.block_of_point s q) b.
Proof.
  intros Hlaw b first q Hb Hfirst [Hdom Hne].
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  assert (Hlisted : In first (Graph.nodes (Pre.pg c))).
  { apply (points_covered Hpoints); exists b; split; [exact Hb|exact (nth_error_In _ _ Hfirst)]. }
  pose proof (point_block_dominates Hlaw Hlisted Hdom) as Hblock.
  rewrite (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)) in Hblock.
  split; [exact Hblock|]; intro Howner.
  destruct (dominator_owner Hlaw Hlisted Hdom) as [Hqb Hq].
  rewrite Howner in Hq; destruct (In_nth_error _ _ Hq) as [i Hi].
  pose proof (proj1 (block_instruction_order Hlaw b i 0 q first Hb Hi Hfirst) Hdom) as Horder.
  assert (Hi0 : i = 0) by lia; subst i; apply Hne; congruence.
Qed.

Local Lemma chain_last_member {X A} (g : Graph.t X A) {ns es default} :
  point_chain g ns es -> In (last ns default) ns.
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es He Htarget Hchain IH].
  - now left.
  - right; exact IH.
Qed.

(** A supplied block-parent binding induces the exact point-dominance boundary
    between the scopes. *)
Theorem block_parent_immediate :
  Pre.laws c ->
  forall b child first parent_id child_id,
    In b (Graph.nodes (Pre.bg c)) -> In child (Graph.nodes (Pre.bg c)) ->
    Prepared.id_of (Pre.blocks c) b = Some parent_id ->
    Prepared.id_of (Pre.blocks c) child = Some child_id ->
    Map.get positive_encoding child_id (Dom.idom (Pre.dom c)) = Some parent_id ->
    nth_error (SsaPoints.points_in_block s child) 0 = Some first ->
    immediately_dominates (Pre.pg c) (last (SsaPoints.points_in_block s b) first) first.
Proof.
  intros Hlaw b child first parent_id child_id Hb Hchild Hid Hchildid Hparent Hfirst.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
  pose proof (Dom.idom_sound _ _ (Pre.tree_exact c (Pre.graphs c Hlaw)) child_id parent_id
    child b Hparent (Prepared.name_of_id_of _ _ _ Hp Hchildid)
    (Prepared.name_of_id_of _ _ _ Hp Hid)) as Himmediate.
  rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Himmediate.
  destruct Himmediate as [[Hblockdom Hblockne] Hblockmin].
  pose proof (chain_last_member _ (default := first) (points_ordered Hpoints b Hb)) as Hlast.
  pose proof (points_owner Hpoints b _ Hb Hlast) as Hownerlast.
  pose proof (points_owner Hpoints child first Hchild (nth_error_In _ _ Hfirst)) as Hownerfirst.
  split; [split|].
  - apply (block_point_dominates Hlaw b _ first Hb Hlast).
    + rewrite Hownerfirst; exact Hblockne.
    + rewrite Hownerfirst; exact Hblockdom.
  - intro Heq; rewrite Heq in Hownerlast; congruence.
  - intros q Hstrict.
    pose proof (point_strict_dom_first Hlaw child first q Hchild Hfirst Hstrict) as Hqblock.
    pose proof (Hblockmin _ Hqblock) as Hqparent.
    assert (Hlisted : In first (Graph.nodes (Pre.pg c))).
    { apply (points_covered Hpoints); exists child; split.
      - exact Hchild.
      - exact (nth_error_In _ _ Hfirst). }
    destruct (dominator_owner Hlaw Hlisted (proj1 Hstrict)) as [Hqb Hq].
    destruct (eqb_dec (Pre.eb (Pre.keys c)) (Pre.eb_laws c (Pre.graphs c Hlaw))
      (SsaPoints.block_of_point s q) b) as [Heq|Hne].
    + rewrite Heq in Hq; exact (block_member_dominates_last Hlaw b q first Hb Hq).
    + apply (block_point_dominates Hlaw _ q _ Hqb Hq).
      * rewrite Hownerlast; exact Hne.
      * rewrite Hownerlast; exact Hqparent.
Qed.

(** Queries occur at real recomputations or at individual block-crossing sources. *)
Definition observed n : Prop :=
  (exists e u, In e (Cfg.edges (Pre.point_cfg c)) /\ Graph.source (Pre.pg c) e = n /\
    Pre.recomputed c e = Some u) \/
  (exists e be, In e (Cfg.edges (Pre.point_cfg c)) /\ Graph.source (Pre.pg c) e = n /\
    SsaPoints.block_edge_of s e = Some be).

(** Every observed query point belongs to the actual point-graph inventory. *)
Lemma observed_listed {n} :
  Pre.laws c -> observed n -> In n (Graph.nodes (Pre.pg c)).
Proof.
  intros Hlaw [[e [u [He [<- Hcomputed]]]]|[e [be [He [<- Hcross]]]]];
    exact (proj1 (listed_edge_out Hlaw He)).
Qed.

Local Lemma chain_source_member {X A} (g : Graph.t X A) {ns es e} :
  graph_wf g -> point_chain g ns es -> In e es -> In (Graph.source g e) ns.
Proof.
  intros Hwf Hchain He; destruct (PreFrg.chain_source _ Hchain He) as [n [Hn Hout]].
  rewrite (out_source Hwf n e Hout); exact Hn.
Qed.

Local Lemma chain_source_unique {X A} (g : Graph.t X A) {ns es} :
  graph_wf g -> point_chain g ns es -> NoDup ns ->
  forall e other, In e es -> In other es -> Graph.source g e = Graph.source g other -> e = other.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros Hnodup e other He Hother Heq; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  destruct He as [<-|He], Hother as [<-|Hother]; [reflexivity| | |].
  - exfalso; apply Hfresh; rewrite <- (out_source Hwf n edge Hedge), Heq.
    exact (chain_source_member _ Hwf Hchain Hother).
  - exfalso; apply Hfresh; rewrite <- (out_source Hwf n edge Hedge), <- Heq.
    exact (chain_source_member _ Hwf Hchain He).
  - exact (IH Htail e other He Hother Heq).
Qed.

Local Lemma chain_first_edge {X A} (g : Graph.t X A) {ns es first parameter} :
  point_chain g ns es -> NoDup ns -> nth_error ns 0 = Some first ->
  nth_error es 0 = Some parameter ->
  In parameter (Graph.out g first) /\ last ns first <> first.
Proof.
  intro Hchain; destruct Hchain as [n|n next ns edge es Hedge Htarget Hchain];
    intros Hnodup Hfirst Hparameter; [discriminate|].
  cbn [nth_error] in Hfirst, Hparameter; inversion Hfirst; inversion Hparameter;
    subst first parameter.
  split; [exact Hedge|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  intro Hlast; apply Hfresh; rewrite <- Hlast; exact (chain_last_member _ Hchain).
Qed.

(** The first outgoing instruction of a listed block is its parameter-binding edge. *)
Theorem first_out_parameter :
  Pre.laws c ->
  forall b first e, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
    In e (Graph.out (Pre.pg c) first) -> e = SsaPoints.parameter_edge s b.
Proof.
  intros Hlaw b first e Hb Hfirst He.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  assert (Hlisted : In first (Graph.nodes (Pre.pg c))).
  { apply (points_covered Hpoints); exists b; split; [exact Hb|exact (nth_error_In _ _ Hfirst)]. }
  pose proof (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)) as Howner.
  destruct (chain_first_edge _ (points_ordered Hpoints b Hb) (points_unique Hpoints b)
    Hfirst (parameter_edge_first Hpoints b Hb)) as [Hparameter Hlast].
  pose proof (point_edge_projection Hpoints first e Hlisted He) as Hprojection.
  destruct (SsaPoints.block_edge_of s e) as [be|] eqn:Hcross.
  - destruct Hprojection as [_ [_ [Hbad _]]]; rewrite Howner in Hbad; contradiction.
  - pose proof (instruction_edges_complete Hpoints first e Hlisted He Hcross) as Hin.
    rewrite Howner in Hin.
    eapply chain_source_unique; [exact (points_graph_wf Hpoints)|
      exact (points_ordered Hpoints b Hb)|exact (points_unique Hpoints b)|exact Hin| |].
    + exact (nth_error_In _ _ (parameter_edge_first Hpoints b Hb)).
    + rewrite (out_source (points_graph_wf Hpoints) first e He),
        (out_source (points_graph_wf Hpoints) first _ Hparameter); reflexivity.
Qed.

(** An observed recomputation or crossing source is never the pre-parameter first point. *)
Theorem observed_not_first :
  Pre.laws c ->
  forall b first n, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
    observed n -> n <> first.
Proof.
  intros Hlaw b first n Hb Hfirst Hobserved Heq; subst n.
  destruct Hobserved as [[e [u [He [Hsource Hcomputed]]]]|[e [be [He [Hsource Hcross]]]]].
  - pose proof (proj2 (listed_edge_out Hlaw He)) as Hout; rewrite Hsource in Hout.
    pose proof (first_out_parameter Hlaw b first e Hb Hfirst Hout) as Hparameter.
    exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed) b Hparameter).
  - pose proof (proj2 (listed_edge_out Hlaw He)) as Hout; rewrite Hsource in Hout.
    pose proof (first_out_parameter Hlaw b first e Hb Hfirst Hout) as Hparameter.
    destruct (PreFrg.parameter_edge_listed c Hlaw Hb) as [_ Hinternal].
    fold s in Hinternal; rewrite Hparameter, Hinternal in Hcross; discriminate.
Qed.

Local Lemma parameter_target_position {b} :
  Pre.laws c -> In b (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block s b) 1 =
    Some (Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b)).
Proof.
  intros Hlaw Hb; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  pose proof (points_ordered Hpoints b Hb) as Hchain.
  pose proof (parameter_edge_first Hpoints b Hb) as Hparameter.
  destruct Hchain as [n|n next ns e es He Htarget Hchain]; [discriminate|].
  cbn [nth_error] in Hparameter; inversion Hparameter; subst e.
  cbn [nth_error]; f_equal; symmetry; exact Htarget.
Qed.

(** At observed points, a dominating phi block's completed parameter edge dominates the query. *)
Theorem phi_point_dominates :
  Pre.laws c ->
  forall b n, In b (Graph.nodes (Pre.bg c)) -> observed n ->
    dominates (Pre.bg c) b (SsaPoints.block_of_point s n) ->
    dominates (Pre.pg c) (Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b)) n.
Proof.
  intros Hlaw b n Hb Hobserved Hdom.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  pose proof (parameter_target_position Hlaw Hb) as Hphi.
  destruct (eqb_dec (Pre.eb (Pre.keys c)) (Pre.eb_laws c (Pre.graphs c Hlaw))
    b (SsaPoints.block_of_point s n)) as [Heq|Hne].
  - destruct (PreFrg.point_owner_listed c Hlaw (observed_listed Hlaw Hobserved))
      as [Hblock Hmember].
    fold s in Hmember; rewrite <- Heq in Hmember.
    destruct (In_nth_error _ _ Hmember) as [j Hn]; destruct j as [|j].
    + exfalso; exact (observed_not_first Hlaw b n n Hb Hn Hobserved eq_refl).
    + apply (proj2 (block_instruction_order Hlaw b 1 (S j) _ n Hb Hphi Hn)); lia.
  - apply (block_point_dominates Hlaw b _ n Hb (nth_error_In _ _ Hphi) Hne Hdom).
Qed.

Local Lemma parameter_point_on_path {b first es n} :
  Pre.laws c -> In b (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block s b) 0 = Some first ->
  path (Pre.pg c) first es n -> n <> first ->
  exists e, In e es /\ Graph.target (Pre.pg c) e =
    Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b).
Proof.
  intros Hlaw Hb Hfirst Hpath Hne; destruct Hpath as [n|e rest n He Hpath]; [contradiction|].
  pose proof (first_out_parameter Hlaw b _ e Hb Hfirst He) as Hparameter.
  exists e; split; [now left|rewrite Hparameter; reflexivity].
Qed.

(** A projected visit to a phi block crosses its parameter definition before an observed query. *)
Theorem phi_point_on_projected_path :
  Pre.laws c ->
  forall start es n b be, In start (Graph.nodes (Pre.pg c)) -> path (Pre.pg c) start es n ->
    observed n -> In b (Graph.nodes (Pre.bg c)) ->
    In be (PreRename.project_edges c es) -> Graph.target (Pre.bg c) be = b ->
    exists edge, In edge es /\ Graph.target (Pre.pg c) edge =
      Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b).
Proof.
  intros Hlaw start es n b be Hstart Hpath Hobserved Hb Hbe Htarget.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  apply project_edges_member in Hbe; destruct Hbe as [e [He Hcross]].
  destruct (listed_edge_out Hlaw (point_path_listed Hlaw Hstart Hpath e He)) as [Hsource Hout].
  pose proof (point_edge_projection Hpoints _ e Hsource Hout) as Hprojection.
  rewrite Hcross in Hprojection; destruct Hprojection as [_ [_ [_ Hfirst]]].
  change (nth_error (SsaPoints.points_in_block s (Graph.target (Pre.bg c) be)) 0 =
    Some (Graph.target (Pre.pg c) e)) in Hfirst; rewrite Htarget in Hfirst.
  destruct (PreRename.path_split _ Hpath He) as [prefix [suffix [Hsplit [Hprefix Hsuffix]]]].
  destruct (parameter_point_on_path Hlaw Hb Hfirst Hsuffix
    (observed_not_first Hlaw b _ n Hb Hfirst Hobserved)) as [edge [Hedge Hpoint]].
  exists edge; split; [rewrite Hsplit; apply in_or_app; right; now right|exact Hpoint].
Qed.

Local Lemma strict_dom_dec {b target} :
  Pre.laws c -> reachable (Pre.bg c) target ->
    {strictly_dominates (Pre.bg c) b target} + {~ strictly_dominates (Pre.bg c) b target}.
Proof.
  intros Hlaw Htarget.
  pose proof (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw))) as Hgraph.
  destruct (in_dec (eqb_dec (Pre.eb (Pre.keys c)) (Pre.eb_laws c (Pre.graphs c Hlaw)))
    b (Graph.nodes (Pre.bg c))) as [Hb|Hb].
  - destruct (Prepared.id_of (Pre.blocks c) b) as [bid|] eqn:Hbid.
    2: { exfalso; destruct (PreFrg.block_node_id c Hlaw b Hb) as [id Hid]; congruence. }
    destruct (Prepared.id_of (Pre.blocks c) target) as [tid|] eqn:Htid.
    2: { exfalso; destruct (PreFrg.block_node_id c Hlaw target
      (reachable_in_nodes _ _ Hgraph Htarget)) as [id Hid]; congruence. }
    assert (Hbr : reachable (Prepared.graph (Pre.blocks c)) b).
    { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)).
      apply (Pre.reachable_blocks c (Pre.graphs c Hlaw)); exact Hb. }
    assert (Htr : reachable (Prepared.graph (Pre.blocks c)) target).
    { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)); exact Htarget. }
    pose proof (DomCheck.dominates_b_spec _ _ target b tid bid
      (Pre.blocks_ready c (Pre.graphs c Hlaw)) (Pre.tree_exact c (Pre.graphs c Hlaw))
      Htr Hbr Htid Hbid) as Hspec.
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hspec.
    destruct (DomCheck.dominates_b (Pre.dom c) bid tid) eqn:Hdom.
    + destruct (eqb_dec (Pre.eb (Pre.keys c)) (Pre.eb_laws c (Pre.graphs c Hlaw)) b target)
        as [Heq|Hne].
      * right; intros [_ Hfalse]; contradiction.
      * left; split; [apply Hspec; reflexivity|exact Hne].
    + right; intros [Hsemantic _]; apply Hspec in Hsemantic; discriminate.
  - right; intros [Hdom _]; apply Hb; apply (reachable_in_nodes _ _ Hgraph).
    exact (DomCheck.dominator_reachable _ b target Htarget Hdom).
Qed.

Local Lemma frontier_track (Sphi : B -> Prop) {d start es target} :
  Pre.laws c ->
  (forall b next, (b = d \/ Sphi b) -> in_df (Pre.bg c) b next -> Sphi next) ->
  path (Pre.bg c) start es target -> reachable (Pre.bg c) start ->
  forall root, (root = d \/ Sphi root) -> dominates (Pre.bg c) root start ->
    exists result, dominates (Pre.bg c) result target /\
      ((result = root /\ forall e, In e es -> strictly_dominates (Pre.bg c) root
          (Graph.target (Pre.bg c) e)) \/
       (Sphi result /\ exists e, In e es /\ Graph.target (Pre.bg c) e = result)).
Proof.
  intros Hlaw Hclosed Hpath.
  induction Hpath as [n|e rest target He Hpath IH]; intros Hreachable root Hroot Hdom.
  - exists root; split; [exact Hdom|left; split; [reflexivity|intros edge []]].
  - pose proof (reachable_step e Hreachable He) as Htarget.
    destruct (strict_dom_dec (b := root) Hlaw Htarget) as [Hstrict|Hnot].
    + destruct (IH Htarget root Hroot (proj1 Hstrict)) as [result [Hr [Hsame|Hphi]]].
      * exists result; split; [exact Hr|left].
        destruct Hsame as [Heq Hall]; split; [exact Heq|].
        intros edge [<-|Hedge]; [exact Hstrict|apply Hall; exact Hedge].
      * exists result; split; [exact Hr|right].
        destruct Hphi as [Hphi [edge [Hedge Hpoint]]]; split; [exact Hphi|].
        exists edge; split; [now right|exact Hpoint].
    + assert (Hphi : Sphi (Graph.target (Pre.bg c) e)).
      { apply (Hclosed root _ Hroot); exists e; repeat split; assumption || reflexivity. }
      destruct (IH Htarget (Graph.target (Pre.bg c) e) (or_intror Hphi) (dominates_refl _ _))
        as [result [Hr [[Heq Hall]|[Hphi' [edge [Hedge Hpoint]]]]]].
      * exists result; split; [exact Hr|right]; subst result; split; [exact Hphi|].
        exists e; split; [now left|reflexivity].
      * exists result; split; [exact Hr|right]; split; [exact Hphi'|].
        exists edge; split; [now right|exact Hpoint].
Qed.

Local Lemma point_occurrence_dec {q start es} :
  Pre.laws c ->
  {q = start \/ exists e, In e es /\ Graph.target (Pre.pg c) e = q} +
  {q <> start /\ forall e, In e es -> Graph.target (Pre.pg c) e <> q}.
Proof.
  intro Hlaw.
  destruct (eqb_dec (Pre.en (Pre.keys c)) (Pre.en_laws c (Pre.graphs c Hlaw)) q start)
    as [Heq|Hne]; [left; now left|].
  induction es as [|e rest IH].
  - right; split; [exact Hne|intros edge []].
  - destruct (eqb_dec (Pre.en (Pre.keys c)) (Pre.en_laws c (Pre.graphs c Hlaw))
      (Graph.target (Pre.pg c) e) q) as [Heq|Hedge].
    + left; right; exists e; split; [now left|exact Heq].
    + destruct IH as [Hvisit|[_ Hclear]].
      * left; destruct Hvisit as [Heq|[edge [Hin Htarget]]]; [contradiction|].
        right; exists edge; split; [now right|exact Htarget].
      * right; split; [exact Hne|].
        intros edge [<-|Hin]; [exact Hedge|apply Hclear; exact Hin].
Qed.

Local Lemma path_last_visit {q start es n} :
  Pre.laws c -> path (Pre.pg c) start es n ->
  (q = start \/ exists e, In e es /\ Graph.target (Pre.pg c) e = q) ->
  exists suffix, path (Pre.pg c) q suffix n /\ incl suffix es /\
    Forall (fun e => Graph.target (Pre.pg c) e <> q) suffix.
Proof.
  intros Hlaw Hpath; induction Hpath as [n|e rest n He Hpath IH]; intro Hvisit.
  - destruct Hvisit as [<-|[e [[] _]]].
    exists []; split; [constructor|split; [intros edge []|constructor]].
  - destruct (point_occurrence_dec (q := q) (start := Graph.target (Pre.pg c) e)
      (es := rest) Hlaw) as [Htail|[Hdifferent Hclear]].
    + destruct (IH Htail) as [suffix [Hsuffix [Hsub Hfree]]].
      exists suffix; split; [exact Hsuffix|]; split; [|exact Hfree].
      intros edge Hin; right; apply Hsub; exact Hin.
    + destruct Hvisit as [Heq|[edge [[<-|Hin] Htarget]]].
      * subst q; exists (e :: rest); split; [constructor; assumption|].
        split; [intros edge Hin; exact Hin|].
        apply Forall_forall; intros edge [<-|Hin]; [congruence|apply Hclear; exact Hin].
      * congruence.
      * exfalso; exact (Hclear edge Hin Htarget).
Qed.

(** Dominating reachable definitions have a path to the use that never revisits the definition. *)
Theorem dominating_path {q n} :
  Pre.laws c -> reachable (Pre.pg c) n -> dominates (Pre.pg c) q n ->
  exists es, path (Pre.pg c) q es n /\ Forall (fun e => Graph.target (Pre.pg c) e <> q) es.
Proof.
  intros Hlaw Hn Hdom; apply reachable_iff_path in Hn.
  destruct Hn as [start [es [Hentry Hpath]]].
  destruct (path_last_visit Hlaw Hpath (Hdom start es Hentry Hpath))
    as [suffix [Hsuffix [_ Hfree]]]; exists suffix; auto.
Qed.

(** A dominating definition also dominates the start of any suffix that avoids returning to it. *)
Theorem dominance_suffix {q start es n} :
  dominates (Pre.pg c) q n -> path (Pre.pg c) start es n ->
  Forall (fun e => Graph.target (Pre.pg c) e <> q) es -> dominates (Pre.pg c) q start.
Proof.
  intros Hdom Hpath Hfree entry prefix Hentry Hprefix.
  assert (Hcombined : path (Pre.pg c) entry (prefix ++ es) n)
    by (eapply PreRename.path_app; eassumption).
  destruct (Hdom entry _ Hentry Hcombined) as [Heq|[e [He Htarget]]]; [now left|].
  apply in_app_iff in He; destruct He as [He|He].
  - right; exists e; auto.
  - exfalso; exact (proj1 (Forall_forall _ _) Hfree e He Htarget).
Qed.

Local Lemma nearest_path_excludes_definition {g u n d q other point es} :
  Pre.laws c -> reachable (Pre.pg c) n ->
  PreRename.nearest_version c g u n d -> PreFrg.version_point c d = Some q ->
  In other (PreFrg.versions g) -> PreFrg.version_expr other = u ->
  PreFrg.version_point c other = Some point -> dominates (Pre.pg c) point n ->
  path (Pre.pg c) q es n -> Forall (fun e => Graph.target (Pre.pg c) e <> q) es ->
  (exists e, In e es /\ Graph.target (Pre.pg c) e = point) -> False.
Proof.
  intros Hlaw Hn [_ [_ [position [Hposition [Hdom Hnearest]]]]] Hq
    Hother Hexpr Hpoint Hpointdom Hpath Hfree [e [He Htarget]].
  assert (Heq : position = q) by congruence; subst position.
  pose proof (Hnearest other point Hother Hexpr Hpoint Hpointdom) as Hback.
  destruct (PreRename.path_split _ Hpath He) as [prefix [suffix [Hsplit [Hprefix Hsuffix]]]].
  rewrite Htarget in Hsuffix.
  assert (Hsuffixfree : Forall (fun edge => Graph.target (Pre.pg c) edge <> q) suffix).
  { rewrite Hsplit in Hfree; apply Forall_app in Hfree.
    exact (Forall_inv_tail (proj2 Hfree)). }
  pose proof (dominance_suffix Hdom Hsuffix Hsuffixfree) as Hforward.
  assert (Heq : q = point).
  { apply (dominates_antisym_reachable (Pre.en (Pre.keys c))
      (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c)).
    - exact (DomCheck.dominator_reachable _ q n Hn Hdom).
    - exact (DomCheck.dominator_reachable _ point n Hn Hpointdom).
    - exact Hforward.
    - exact Hback. }
  exact (proj1 (Forall_forall _ _) Hfree e He ltac:(congruence)).
Qed.

(** An expression kill on the supported family is always an internal instruction occurrence. *)
Lemma kill_internal {e u} :
  Pre.laws c -> PreFamily.in_family c u -> In e (Cfg.edges (Pre.point_cfg c)) ->
  Pre.killed c e u = true -> SsaPoints.block_edge_of s e = None.
Proof.
  intros Hlaw Hu He Hkill.
  destruct (Pre.kill_operand c (Pre.kills c Hlaw) e u He Hu Hkill) as [x [Hx Hdef]].
  destruct (SsaPoints.block_edge_of s e) as [be|] eqn:Hcross; [|reflexivity].
  rewrite (Pre.cross_no_defs c (Pre.kills c Hlaw) e be He Hcross) in Hdef; contradiction.
Qed.

Local Lemma project_empty {es} :
  PreRename.project_edges c es = [] ->
  forall e, In e es -> SsaPoints.block_edge_of s e = None.
Proof.
  intros Hempty e He; destruct (SsaPoints.block_edge_of s e) as [be|] eqn:Hcross;
    [|reflexivity].
  assert (Hin : In be (PreRename.project_edges c es)).
  { apply project_edges_member; exists e; auto. }
  rewrite Hempty in Hin; contradiction.
Qed.

Local Lemma stays_in_region {start es n d} :
  Pre.laws c -> In start (Graph.nodes (Pre.pg c)) -> path (Pre.pg c) start es n ->
  SsaPoints.block_of_point s start = d -> In d (Graph.nodes (Pre.bg c)) ->
  (forall be, In be (PreRename.project_edges c es) ->
    strictly_dominates (Pre.bg c) d (Graph.target (Pre.bg c) be)) ->
    dominates (Pre.pg c) start n.
Proof.
  intros Hlaw Hstart Hpath Howner Hd Hstrict.
  destruct (PreRename.project_edges c es) as [|be rest] eqn:Hedges.
  - apply (PreRename.path_dominance_chain _ Hpath); intros e He.
    apply internal_source_dominates; [exact Hlaw|exact (point_path_listed Hlaw Hstart Hpath e He)|].
    exact (project_empty Hedges e He).
  - pose proof (PreRename.project_path c Hlaw _ _ _ Hstart Hpath) as Hprojected.
    rewrite Hedges in Hprojected.
    destruct (PreRename.path_last _ Hprojected ltac:(discriminate))
      as [prefix [last [Hsplit [Hprefix [Htarget Hlast]]]]].
    assert (Hin : In last (be :: rest)).
    { rewrite Hsplit; apply in_or_app; right; now left. }
    pose proof (Hstrict last Hin) as Hdom; rewrite Htarget in Hdom.
    destruct (PreFrg.point_owner_listed c Hlaw Hstart) as [Hblock Hmember].
    fold s in Hmember; rewrite Howner in Hmember.
    exact (block_point_dominates Hlaw d start n Hd Hmember (proj2 Hdom) (proj1 Hdom)).
Qed.

(** A killing path reaches either its dominating alteration
    or a required dominating phi boundary. *)
Theorem kill_reaching_boundary :
  Pre.laws c ->
  forall u e suffix n, PreFamily.in_family c u -> In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.killed c e u = true -> path (Pre.pg c) (Graph.target (Pre.pg c) e) suffix n ->
    observed n ->
    dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n \/
    exists b, PreFrg.phi_needed c u b /\
      dominates (Pre.pg c) (Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b)) n /\
      exists edge, In edge suffix /\ Graph.target (Pre.pg c) edge =
        Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b).
Proof.
  intros Hlaw u e suffix n Hfamily He Hkill Hpath Hobserved.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints; fold s in Hpoints.
  destruct (listed_edge_out Hlaw He) as [Hsource Hout].
  pose proof (out_target_in (points_graph_wf Hpoints) _ e Hsource Hout) as Htarget.
  destruct (PreFrg.point_owner_listed c Hlaw Hsource) as [Hd Hmember]; fold s in Hd.
  pose proof (point_edge_projection Hpoints _ e Hsource Hout) as Howner.
  rewrite (kill_internal Hlaw Hfamily He Hkill) in Howner.
  change (SsaPoints.block_of_point s (Graph.source (Pre.pg c) e) =
    SsaPoints.block_of_point s (Graph.target (Pre.pg c) e)) in Howner.
  set (d := SsaPoints.block_of_point s (Graph.source (Pre.pg c) e)) in *.
  pose proof (PreRename.project_path c Hlaw _ _ _ Htarget Hpath) as Hprojected.
  fold s in Hprojected.
  change (path (Pre.bg c) (SsaPoints.block_of_point s (Graph.target (Pre.pg c) e))
    (PreRename.project_edges c suffix) (SsaPoints.block_of_point s n)) in Hprojected.
  rewrite <- Howner in Hprojected.
  assert (Hclosed : forall root target, (root = d \/ PreFrg.phi_needed c u root) ->
    in_df (Pre.bg c) root target -> PreFrg.phi_needed c u target).
  { intros root target [Hroot|Hphi] Hdf.
    - subst root; exact (kill_frontier_phi c Hlaw u e target Hfamily He Hkill Hdf).
    - eapply PreFrg.phi_iterate; eassumption. }
  destruct (frontier_track (PreFrg.phi_needed c u) Hlaw Hclosed Hprojected
    (Pre.reachable_blocks c (Pre.graphs c Hlaw) d Hd) d (or_introl eq_refl) (dominates_refl _ d))
    as [root [Hdom [[Heq Hall]|[Hphi [be [Hbe Hblock]]]]]].
  - left; subst root; exact (stays_in_region Hlaw Htarget Hpath (eq_sym Howner) Hd Hall).
  - right; exists root; split; [exact Hphi|].
    pose proof (PreFrg.phi_needed_nodes c Hlaw Hphi) as Hroot; split.
    + exact (phi_point_dominates Hlaw root n Hroot Hobserved Hdom).
    + exact (phi_point_on_projected_path Hlaw _ suffix n root be Htarget Hpath
        Hobserved Hroot Hbe Hblock).
Qed.

(** At observed uses, absence of dominating kills makes a nearest version reusable
    on every return-free path. *)
Theorem reusable_of_dominating_kills :
  Pre.laws c ->
  forall g u n d q, PreFamily.in_family c u -> observed n ->
    (forall b, PreFrg.phi_needed c u b -> In (PreFrg.Phi b u) (PreFrg.versions g)) ->
    PreRename.nearest_version c g u n d -> PreFrg.version_point c d = Some q ->
    no_dominating_kill c u q n -> PreRename.reusable c g u n d.
Proof.
  intros Hlaw g u n d q Hfamily Hobserved Hphis Hnearest Hq Hkills.
  pose proof (Pre.reachable_points c (Pre.graphs c Hlaw) n (observed_listed Hlaw Hobserved))
    as Hreachable.
  pose proof Hnearest as [_ [_ [position [Hposition [Hdom Hmax]]]]].
  assert (Heq : position = q) by congruence; subst position.
  split; [exact Hnearest|]; exists q; split; [exact Hq|].
  intros es Hpath Hfree; apply Forall_forall; intros e He.
  destruct (Pre.killed c e u) eqn:Hkill; [|reflexivity]; exfalso.
  pose proof (DomCheck.dominator_reachable _ q n Hreachable Hdom) as Hqreachable.
  pose proof (reachable_in_nodes _ _ (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    Hqreachable) as Hqlisted.
  pose proof (point_path_listed Hlaw Hqlisted Hpath e He) as Hlisted.
  destruct (PreRename.path_split _ Hpath He) as [prefix [suffix [Hsplit [Hprefix Hsuffix]]]].
  assert (Hsuffixfree : Forall (fun edge => Graph.target (Pre.pg c) edge <> q) suffix).
  { rewrite Hsplit in Hfree; apply Forall_app in Hfree; exact (Forall_inv_tail (proj2 Hfree)). }
  destruct (kill_reaching_boundary Hlaw u e suffix n Hfamily Hlisted Hkill Hsuffix Hobserved)
    as [Htargetdom|[b [Hphi [Hphidom [edge [Hedge Hpoint]]]]]].
  - pose proof (dominance_suffix Hdom Hsuffix Hsuffixfree) as Hforward.
    assert (Hstrict : strictly_dominates (Pre.pg c) q (Graph.target (Pre.pg c) e)).
    { split; [exact Hforward|].
      pose proof (proj1 (Forall_forall _ _) Hfree e He); congruence. }
    pose proof (Hkills e Hlisted Hstrict Htargetdom); congruence.
  - eapply (nearest_path_excludes_definition Hlaw Hreachable Hnearest Hq
      (Hphis b Hphi) eq_refl ltac:(rewrite PreFrg.version_point_equation; reflexivity)
      Hphidom Hpath Hfree).
    exists edge; split; [rewrite Hsplit; apply in_or_app; right; now right|exact Hpoint].
Qed.

(** A reusable nearest version excludes every dominating internal alteration
    below its definition. *)
Theorem reusable_dominating_kills :
  Pre.laws c ->
  forall g u n d q, PreFamily.in_family c u -> reachable (Pre.pg c) n ->
    PreRename.reusable c g u n d -> PreFrg.version_point c d = Some q ->
    no_dominating_kill c u q n.
Proof.
  intros Hlaw g u n d q Hfamily Hreachable [Hnearest [safe [Hsafe Hpaths]]] Hq.
  destruct Hnearest as [_ [_ [position [Hposition [Hdom Hmax]]]]].
  assert (Heq : position = q) by congruence; subst position.
  assert (Heq : safe = q) by congruence; subst safe.
  intros e Hlisted Hstrict Htargetdom.
  destruct (Pre.killed c e u) eqn:Hkill; [|reflexivity]; exfalso.
  pose proof (kill_internal Hlaw Hfamily Hlisted Hkill) as Hinternal.
  destruct (dominating_path Hlaw Hreachable Hdom) as [es [Hpath Hfree]].
  destruct (point_occurrence_dec (q := Graph.target (Pre.pg c) e) (start := q) (es := es) Hlaw)
    as [[Heq|[edge [Hedge Htarget]]]|[Hdifferent Hclear]].
  - exact (proj2 Hstrict (eq_sym Heq)).
  - pose proof (DomCheck.dominator_reachable _ q n Hreachable Hdom) as Hqreachable.
    pose proof (point_path_listed Hlaw
      (reachable_in_nodes _ _ (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
        Hqreachable) Hpath edge Hedge) as Hlistededge.
    pose proof (internal_incoming_unique Hlaw Hlisted Hinternal Hlistededge Htarget) as Heq;
      subst edge.
    pose proof (proj1 (Forall_forall _ _) (Hpaths es Hpath Hfree) e Hedge); congruence.
  - assert (Hfree_target : Forall (fun edge =>
      Graph.target (Pre.pg c) edge <> Graph.target (Pre.pg c) e) es).
    { apply Forall_forall; exact Hclear. }
    pose proof (dominance_suffix Htargetdom Hpath Hfree_target) as Hback.
    apply (proj2 Hstrict).
    apply (dominates_antisym_reachable (Pre.en (Pre.keys c))
      (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c)).
    + exact (DomCheck.dominator_reachable _ q n Hreachable Hdom).
    + exact (DomCheck.dominator_reachable _ _ n Hreachable Htargetdom).
    + exact (proj1 Hstrict).
    + exact Hback.
Qed.

Local Lemma nearest_points_agree {g u n d q other point} :
  Pre.laws c -> reachable (Pre.pg c) n ->
  PreRename.nearest_version c g u n d -> PreFrg.version_point c d = Some q ->
  PreRename.nearest_version c g u n other -> PreFrg.version_point c other = Some point ->
    q = point.
Proof.
  intros Hlaw Hn Hd Hq Hother Hpoint.
  destruct (PreRename.nearest_points_mutual c g u n d other Hd Hother)
    as [q0 [p0 [Hq0 [Hp0 [Hqn [Hpn [Hqp Hpq]]]]]]].
  assert (Hsame : q0 = q) by congruence; subst q0.
  assert (Hsame : p0 = point) by congruence; subst p0.
  apply (dominates_antisym_reachable (Pre.en (Pre.keys c))
    (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c)).
  - exact (DomCheck.dominator_reachable _ q n Hn Hqn).
  - exact (DomCheck.dominator_reachable _ point n Hn Hpn).
  - exact Hqp.
  - exact Hpq.
Qed.

(** A meaningful scoped frame is available exactly when a reusable graph version
    reaches the observed use. *)
Theorem frame_availability :
  Pre.laws c ->
  forall g u n frame, PreFamily.in_family c u -> observed n ->
    (forall b, PreFrg.phi_needed c u b -> In (PreFrg.Phi b u) (PreFrg.versions g)) ->
    frame_laws c g u n frame ->
    (PreRename.available frame = true <-> exists d, PreRename.reusable c g u n d) /\
    (PreRename.available frame = true ->
      PreRename.reusable c g u n (PreFrg.operand_version (PreRename.selected frame))).
Proof.
  intros Hlaw g u n frame Hfamily Hobserved Hphis [Hexpr [Hreal Hmeaning]].
  pose proof (Pre.reachable_points c (Pre.graphs c Hlaw) n (observed_listed Hlaw Hobserved)) as Hn.
  destruct (PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)))
    as [q|] eqn:Hq.
  - destruct Hmeaning as [Hnearest Havailable].
    assert (Hsound : PreRename.available frame = true ->
      PreRename.reusable c g u n (PreFrg.operand_version (PreRename.selected frame))).
    { intro Htrue; eapply reusable_of_dominating_kills; [exact Hlaw|exact Hfamily|
        exact Hobserved|exact Hphis|exact Hnearest|exact Hq|].
      apply Havailable; exact Htrue. }
    split; [split|exact Hsound].
    + intro Htrue; exists (PreFrg.operand_version (PreRename.selected frame)).
      apply Hsound; exact Htrue.
    + intros [d Hreuse]; pose proof Hreuse as [Hnearest' [point [Hpoint Hsafe]]].
      pose proof (nearest_points_agree Hlaw Hn Hnearest Hq Hnearest' Hpoint) as Heq.
      apply Havailable; rewrite Heq.
      exact (reusable_dominating_kills Hlaw g u n d point Hfamily Hn Hreuse Hpoint).
  - destruct Hmeaning as [_ [Hfalse Hnone]]; split; [split|].
    + intro Htrue; congruence.
    + intros [d [[Hd [Hu [q [Hpoint [Hdom Hnearest]]]]] Hsafe]].
      exfalso; exact (Hnone d q Hd Hu Hpoint Hdom).
    + intro Htrue; congruence.
Qed.

End Geometry.

End PreCoverage.
