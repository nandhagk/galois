(** * Definition-point provenance through the indexed walk

    Selected definitions dominate the current point and reused definitions dominate their uses.
    For example, invalidating a frame preserves the dominance of its retained definition.
    Builds on: AnalysesSsaPreFrameInvariant, AnalysesSsaPreCoverage and the actual prepared indexes. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameCache
  AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd AnalysesSsaPreFrameInvariant.
Import List.ListNotations.

Module PreFrameDominance.

Section Provenance.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Hypothesis Hlaw : Pre.laws c.
Hypothesis Hdata : PreFrameCache.placement_laws c data.
Let bank := PreFrameCache.names c data.
Let index := PreRename.prepare c data.
Let points := Pre.points (Pre.input c).

(** Every named selected definition dominates the current point, including retained invalid frames. *)
Definition scope_dominance n (frames : PreRename.scope B E U) : Prop :=
  forall u id, Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  forall q, PreFrg.version_point c
    (PreFrg.operand_version (PreRename.selected (PreRename.top c frames u))) = Some q ->
    dominates (Pre.pg c) q n.

(** A selected occurrence's definition dominates its target and every nonfresh selection's source. *)
Definition occurrence_dominance e (d : PreFrg.version B E U) : Prop :=
  exists q, PreFrg.version_point c d = Some q /\
    dominates (Pre.pg c) q (Graph.target (Pre.pg c) e) /\
    (d <> PreFrg.Fresh e (PreFrg.version_expr d) ->
      dominates (Pre.pg c) q (Graph.source (Pre.pg c) e)).

(** All accumulated occurrence answers retain definition-point dominance in the source graph. *)
Record output_dominance (acc : PreRename.accumulator B BE E U) : Prop := OutputDominance {
  dominance_occurrences_wf : Map.wf (Pre.ee (Pre.keys c)) (PreRename.occurrence_index acc);
  dominance_occurrences : forall e d,
    Map.get (Pre.ee (Pre.keys c)) e (PreRename.occurrence_index acc) = Some d ->
      occurrence_dominance e d
}.

Definition local_dominance n (work : PreRename.scope B E U * PreRename.accumulator B BE E U) :=
  PreFrameInvariant.scope_source c data (fst work) /\
  scope_dominance n (fst work) /\ output_dominance (snd work).

Local Lemma scope_advance {n target frames} :
  dominates (Pre.pg c) n target -> scope_dominance n frames -> scope_dominance target frames.
Proof.
  intros Hdom Hframes u id Hid q Hq.
  eapply dominates_trans; [exact (Hframes u id Hid q Hq)|exact Hdom].
Qed.

Local Lemma store_dominance {n frames u id frame} :
  PreFrameCache.scope_wf c frames -> PreRename.symbols frames = bank ->
  scope_dominance n frames ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  (forall q, PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)) = Some q ->
    dominates (Pre.pg c) q n) ->
    scope_dominance n (PreRename.store frames id frame).
Proof.
  intros Hwf Hsymbols Hframes Hid Hframe v other Hv q Hq.
  rewrite (PreFrameCache.top_store c Hlaw frames u id frame) in Hq.
  - destruct (eqb (Pre.eu (Pre.keys c)) v u).
    + exact (Hframe q Hq).
    + exact (Hframes v other Hv q Hq).
  - exact Hwf.
  - rewrite Hsymbols; exact Hid.
Qed.

Local Lemma dense_dominance {n frames u id q} :
  PreFrameInvariant.scope_source c data frames -> scope_dominance n frames ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  PreFrg.version_point c
    (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u))) = Some q ->
    dominates (Pre.pg c) q n.
Proof.
  intros Hsource Hframes Hid Hq; apply (Hframes u id Hid q).
  rewrite (PreFrameCache.top_id_agrees c (frames := frames) (u := u) (id := id)).
  - exact Hq.
  - rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hid.
Qed.

Local Lemma available_dense_point {frames u id} :
  PreFrameInvariant.scope_source c data frames ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  PreRename.available (PreRename.top_id frames id u) = true ->
    exists q, PreFrg.version_point c
      (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u))) = Some q.
Proof.
  intros Hsource Hid Havailable.
  pose proof (PreFrameInvariant.scope_frames c data frames Hsource u id Hid) as Hframe.
  rewrite (PreFrameCache.top_id_agrees c (frames := frames) (u := u) (id := id)) in Hframe.
  2: { rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hid. }
  destruct Hframe as [Hexpr [Hdomain Hnonmissing]].
  destruct (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u)))
    as [v|v|edge v|block v] eqn:Hversion.
  - cbn [PreFrg.version_expr] in Hexpr; subst v; exfalso.
    exact (Hnonmissing Havailable eq_refl).
  - destruct (Pre.entry_position c (Pre.graphs c Hlaw)) as [b [first [Hblocks [Hentry Hfirst]]]].
    exists first; rewrite PreFrg.version_point_equation, Hentry; reflexivity.
  - exists (Graph.target (Pre.pg c) edge); rewrite PreFrg.version_point_equation; reflexivity.
  - exists (Graph.target (Pre.pg c) (SsaPoints.parameter_edge points block)).
    rewrite PreFrg.version_point_equation; reflexivity.
Qed.

(** Actual prepared entry frames dominate the source program's unique entry point. *)
Theorem entry_dominance :
  forall first, Graph.entries (Pre.pg c) = [first] ->
    scope_dominance first (PreRename.entry_scope index).
Proof.
  intros first Hentry u id Hid q Hpoint.
  unfold index in Hpoint.
  rewrite (PreFrameCache.cached_entry c data _ (PreFrameCache.prepare_laws c data)),
    PreFrameCache.initial_top in Hpoint; [|exact Hlaw|].
  - rewrite PreRename.initial_frame_equation in Hpoint.
    destruct (Pre.initial c u); cbn [PreRename.selected PreFrg.operand_version] in Hpoint;
      rewrite PreFrg.version_point_equation in Hpoint; [|discriminate].
    rewrite Hentry in Hpoint; cbn [nth_error] in Hpoint; inversion Hpoint; subst q.
    apply dominates_refl.
  - apply (PreFrameCache.eligible_exact c data Hdata).
    apply (proj1 (PreFrameCache.names_domain c data Hlaw Hdata u)); now exists id.
Qed.

Local Lemma set_occurrence_dominance acc e d (fresh : bool) :
  output_dominance acc -> occurrence_dominance e d ->
    output_dominance (PreRename.Accumulator
      (Map.set (Pre.ee (Pre.keys c)) e d (PreRename.occurrence_index acc))
      (if fresh then FinSet.add (Pre.ee (Pre.keys c)) e (PreRename.fresh_index acc)
        else PreRename.fresh_index acc)
      (PreRename.link_index acc) (PreRename.unsafe_index acc)
      (if fresh then d :: PreRename.created acc else PreRename.created acc)).
Proof.
  intros Hacc Hd; constructor.
  - apply Map.wf_set; exact (dominance_occurrences_wf _ Hacc).
  - intros other value Hget; cbn [PreRename.occurrence_index] in Hget.
    rewrite Map.get_set in Hget by exact (dominance_occurrences_wf _ Hacc).
    destruct (eqb (Pre.ee (Pre.keys c)) other e) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hsame.
      inversion Hget; subst other value; exact Hd.
    + exact (dominance_occurrences _ Hacc other value Hget).
Qed.

Local Lemma reused_dominance {frames e u id} :
  PreFrameInvariant.scope_source c data frames ->
  scope_dominance (Graph.source (Pre.pg c) e) frames ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  PreRename.frame_reuse c (PreRename.top_id frames id u) u = true ->
  dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e) ->
    occurrence_dominance e (PreFrg.operand_version (PreRename.selected
      (PreRename.top_id frames id u))).
Proof.
  intros Hsource Hframes Hid Hreuse Hstep.
  assert (Havailable : PreRename.available (PreRename.top_id frames id u) = true).
  { unfold PreRename.frame_reuse in Hreuse.
    destruct (PreRename.available (PreRename.top_id frames id u)); [reflexivity|discriminate]. }
  destruct (available_dense_point Hsource Hid Havailable) as [q Hq].
  pose proof (dense_dominance Hsource Hframes Hid Hq) as Hdom.
  exists q; split; [exact Hq|]; split.
  - eapply dominates_trans; eassumption.
  - intros _; exact Hdom.
Qed.

(** An available reused frame cannot be the very fresh definition that this instruction would create. *)
Theorem reuse_not_current :
  forall e frames u id, In e (Cfg.edges (Pre.point_cfg c)) ->
    SsaPoints.block_edge_of points e = None ->
    PreFrameInvariant.scope_source c data frames ->
    scope_dominance (Graph.source (Pre.pg c) e) frames ->
    Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    PreRename.frame_reuse c (PreRename.top_id frames id u) u = true ->
    PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u)) <>
      PreFrg.Fresh e u.
Proof.
  intros e frames u id He Hi Hsource Hframes Hid Hreuse Heq.
  assert (Hpoint : PreFrg.version_point c (PreFrg.operand_version
    (PreRename.selected (PreRename.top_id frames id u))) = Some (Graph.target (Pre.pg c) e)).
  { rewrite Heq, PreFrg.version_point_equation; reflexivity. }
  pose proof (dense_dominance Hsource Hframes Hid Hpoint) as Hback.
  pose proof (PreCoverage.internal_immediate c Hlaw He Hi) as [[Hforward Hne] Hminimal].
  destruct (PreCoverage.listed_edge_out c Hlaw He) as [Hstart Hout].
  pose proof (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
    _ e Hstart Hout) as Hfinish.
  apply Hne; exact (dominates_antisym_reachable (Pre.en (Pre.keys c))
    (Pre.en_laws c (Pre.graphs c Hlaw)) (Pre.pg c) _ _
    (Pre.reachable_points c (Pre.graphs c Hlaw) _ Hstart)
    (Pre.reachable_points c (Pre.graphs c Hlaw) _ Hfinish) Hforward Hback).
Qed.

(** Actual occurrence selection records definition dominance and leaves frames at the source point. *)
Theorem occurrence_dominance_transfer :
  forall e {instance work}, local_dominance (Graph.source (Pre.pg c) e) work ->
    dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e) ->
    (forall id u, instance = Some (id, u) ->
      Intern.find (Pre.eu (Pre.keys c)) u bank = Some id) ->
    local_dominance (Graph.source (Pre.pg c) e)
      (fst (PreRename.occurrence c e instance work)).
Proof.
  intros e instance [frames acc] [Hsource [Hframes Hacc]] Hstep Hinstance.
  pose proof (PreFrameInvariant.occurrence_source c data Hlaw
    frames acc e instance Hsource Hinstance) as Hnew_source.
  rewrite PreRename.occurrence_equation in Hnew_source |- *.
  destruct instance as [[id u]|]; [|split; [exact Hsource|auto]].
  cbn zeta in Hnew_source |- *.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u) eqn:Hreuse.
  - split; [exact Hnew_source|]; split.
    + apply (store_dominance (u := u));
        [exact (PreFrameInvariant.scope_representation c data frames Hsource)|
         exact (PreFrameInvariant.scope_symbols c data frames Hsource)|
         exact Hframes|apply Hinstance; reflexivity|].
      intros q Hq; exact (dense_dominance Hsource Hframes (Hinstance id u eq_refl) Hq).
    + apply (set_occurrence_dominance acc e _ false); [exact Hacc|].
      exact (reused_dominance Hsource Hframes (Hinstance id u eq_refl) Hreuse Hstep).
  - split; [exact Hnew_source|]; split; [exact Hframes|].
    apply (set_occurrence_dominance acc e _ true); [exact Hacc|].
    exists (Graph.target (Pre.pg c) e); split; [rewrite PreFrg.version_point_equation; reflexivity|].
    split; [apply dominates_refl|intros Hneq; exfalso; apply Hneq; reflexivity].
Qed.

Local Lemma output_transport before after :
  PreRename.occurrence_index before = PreRename.occurrence_index after ->
    output_dominance before -> output_dominance after.
Proof.
  intros Heq [Hwf Hdom]; constructor; rewrite <- Heq; assumption.
Qed.

Local Lemma mark_output frames acc key :
  PreRename.occurrence_index (PreRename.mark c frames acc key) =
    PreRename.occurrence_index acc.
Proof.
  apply PreFrameEnd.mark_occurrences.
Qed.

Local Lemma mark_exit_dominance n endpoint work :
  local_dominance n work -> local_dominance n (PreRename.mark_exit c index endpoint work).
Proof.
  intro Hwork; rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) endpoint (PreRename.exit_points index));
    [|exact Hwork].
  destruct Hwork as [Hsource [Hscope Houtput]]; split; [exact Hsource|].
  split; [exact Hscope|]; eapply output_transport; [|exact Houtput].
  symmetry; apply PreFrameStep.fold_observation; intros acc key; apply mark_output.
Qed.

Local Lemma alter_dominance n instance frames acc id u :
  local_dominance n (frames, acc) ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    local_dominance n (PreRename.alter c instance (frames, acc) (id, u)).
Proof.
  intros [Hsource [Hscope Houtput]] Hid; split.
  - exact (PreFrameInvariant.alter_source c data Hlaw frames acc instance id u Hsource Hid).
  - rewrite PreRename.alter_equation; cbn [fst snd]; split.
    + apply (store_dominance (u := u)).
      * exact (PreFrameInvariant.scope_representation c data frames Hsource).
      * exact (PreFrameInvariant.scope_symbols c data frames Hsource).
      * exact Hscope.
      * exact Hid.
      * intros q Hq; exact (dense_dominance Hsource Hscope Hid Hq).
    + destruct instance as [current|].
      * destruct (eqb positive_encoding (fst current) id); [exact Houtput|].
        eapply output_transport; [symmetry; apply mark_output|exact Houtput].
      * eapply output_transport; [symmetry; apply mark_output|exact Houtput].
Qed.

Local Lemma fold_alter_dominance n instance :
  forall changes work, local_dominance n work ->
    Forall (fun pair => Intern.find (Pre.eu (Pre.keys c)) (snd pair) bank = Some (fst pair))
      changes ->
    local_dominance n (fold_left (PreRename.alter c instance) changes work).
Proof.
  intros changes; induction changes as [|[id u] rest IH]; intros [frames acc] Hwork Hchanges;
    cbn [fold_left]; [exact Hwork|].
  inversion Hchanges as [|pair tail Hid Hrest]; subst pair tail.
  apply IH; [apply alter_dominance; assumption|exact Hrest].
Qed.

Definition positioned n (frames : PreRename.scope B E U) : Prop :=
  PreFrameCache.scope_wf c frames /\ PreRename.symbols frames = bank /\ scope_dominance n frames.

Local Lemma store_positioned {n frames u id frame} :
  positioned n frames ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  (forall q, PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)) = Some q ->
    dominates (Pre.pg c) q n) ->
    positioned n (PreRename.store frames id frame).
Proof.
  intros [Hwf [Hsymbols Hscope]] Hid Hframe.
  split; [apply PreFrameCache.store_wf; exact Hwf|]; split.
  - rewrite PreRename.store_equation; exact Hsymbols.
  - exact (store_dominance Hwf Hsymbols Hscope Hid Hframe).
Qed.

Local Lemma install_phi_positioned {b e frames pair} :
  e = SsaPoints.parameter_edge points b ->
  positioned (Graph.target (Pre.pg c) e) frames ->
  In pair (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions index)) ->
    positioned (Graph.target (Pre.pg c) e) (PreRename.install_phi b frames pair).
Proof.
  intros He Hframes Hin; destruct pair as [owner [id u]].
  assert (Hid : Intern.find (Pre.eu (Pre.keys c)) u bank = Some id).
  { unfold index in Hin.
    rewrite (PreFrameCache.cached_phi_definitions c data _ (PreFrameCache.prepare_laws c data)),
      Index.find_group_by, filter_In in Hin.
    exact (proj2 (proj1 (PreFrameCache.phi_pairs_exact c data Hlaw Hdata owner id u)
      (proj1 Hin))). }
  rewrite PreRename.install_phi_equation; cbn [fst snd].
  apply (store_positioned (u := u) Hframes Hid).
  intros q Hq; cbn [PreRename.selected PreFrg.operand_version] in Hq.
  rewrite PreFrg.version_point_equation in Hq; inversion Hq; subst q.
  rewrite He; apply dominates_refl.
Qed.

Local Lemma definitions_dominance b parameter e fresh frames :
  PreFrameInvariant.scope_source c data frames ->
  scope_dominance (Graph.source (Pre.pg c) e) frames ->
  dominates (Pre.pg c) (Graph.source (Pre.pg c) e) (Graph.target (Pre.pg c) e) ->
  parameter = SsaPoints.parameter_edge points b ->
  (forall id u, fresh = Some (id, u) ->
    Intern.find (Pre.eu (Pre.keys c)) u bank = Some id) ->
    scope_dominance (Graph.target (Pre.pg c) e)
      (PreRename.definitions c index b parameter e fresh frames).
Proof.
  intros Hsource Hscope Hadvance Hparameter Hfresh; rewrite PreRename.definitions_equation.
  assert (Hpositioned : positioned (Graph.target (Pre.pg c) e) frames).
  { split; [exact (PreFrameInvariant.scope_representation c data frames Hsource)|]; split.
    - exact (PreFrameInvariant.scope_symbols c data frames Hsource).
    - exact (scope_advance Hadvance Hscope). }
  assert (Hnew : positioned (Graph.target (Pre.pg c) e) (match fresh with
    | None => frames
    | Some (id, u) => PreRename.store frames id
        (PreRename.Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true)
    end)).
  { destruct fresh as [[id u]|]; [|exact Hpositioned].
    apply (store_positioned (u := u) Hpositioned (Hfresh id u eq_refl)).
    intros q Hq; cbn [PreRename.selected PreFrg.operand_version] in Hq.
    rewrite PreFrg.version_point_equation in Hq; inversion Hq; subst q; apply dominates_refl. }
  destruct (eqb (Pre.ee (Pre.keys c)) e parameter) eqn:Hsame; [|exact (proj2 (proj2 Hnew))].
  apply (eqb_true_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hsame.
  assert (Hfold : forall pairs current,
    Forall (fun pair => In pair
      (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions index))) pairs ->
    positioned (Graph.target (Pre.pg c) e) current ->
    positioned (Graph.target (Pre.pg c) e)
      (fold_left (PreRename.install_phi b) pairs current)).
  { intros pairs current Hpairs; revert current; induction Hpairs as
      [|pair rest Hpair Hrest IH]; intros current Hcurrent; cbn [fold_left]; [exact Hcurrent|].
    apply IH; eapply install_phi_positioned; [congruence|exact Hcurrent|exact Hpair]. }
  exact (proj2 (proj2 (Hfold _ _ (proj2 (Forall_forall _ _) (fun pair Hin => Hin)) Hnew))).
Qed.

(** Every actual internal instruction preserves point provenance at its completed target. *)
Theorem instruction_dominance :
  forall b parameter work e, In e (Cfg.edges (Pre.point_cfg c)) ->
    SsaPoints.block_edge_of points e = None ->
    parameter = SsaPoints.parameter_edge points b ->
    local_dominance (Graph.source (Pre.pg c) e) work ->
    local_dominance (Graph.target (Pre.pg c) e)
      (PreRename.instruction c index b parameter work e).
Proof.
  intros b parameter work e He Hi Hparameter Hwork.
  pose proof (PreFrameInvariant.instruction_source c data Hlaw Hdata b parameter work e
    (proj1 Hwork)) as Hsource_final.
  fold index in Hsource_final.
  pose proof (PreFrameCache.event_lookup c data Hlaw e He) as Hlookup; fold index in Hlookup.
  rewrite PreRename.instruction_equation, Hlookup in Hsource_final |- *.
  cbn zeta in Hsource_final; unfold index in Hsource_final.
  rewrite PreFrameInvariant.mark_exit_scope in Hsource_final; cbn [fst] in Hsource_final.
  fold index in Hsource_final.
  pose proof (PreCoverage.internal_source_dominates c Hlaw He Hi) as Hadvance.
  set (instance := PreRename.evaluation (PreFrameCache.event_description c bank e)).
  assert (Hinstance : forall id u, instance = Some (id, u) ->
    Intern.find (Pre.eu (Pre.keys c)) u bank = Some id).
  { intros id u Hvalue; apply PreFrameCache.evaluation_exact in Hvalue; tauto. }
  pose proof (occurrence_dominance_transfer e Hwork Hadvance Hinstance) as Hobserved.
  set (observed := PreRename.occurrence c e instance work) in *.
  assert (Haltered : local_dominance (Graph.source (Pre.pg c) e)
    (fold_left (PreRename.alter c instance)
      (PreRename.alterations (PreFrameCache.event_description c bank e)) (fst observed))).
  { apply fold_alter_dominance; [exact Hobserved|].
    apply Forall_forall; intros [id u] Hin; cbn [fst snd].
    apply (PreFrameCache.event_alterations c bank e Hlaw) in Hin; exact (proj2 Hin). }
  apply mark_exit_dominance; split; [exact Hsource_final|]; split.
  - cbn [fst]; apply definitions_dominance.
    + exact (proj1 Haltered).
    + exact (proj1 (proj2 Haltered)).
    + exact Hadvance.
    + exact Hparameter.
    + intros id u Hfresh; apply Hinstance.
      exact (PreFrameInvariant.occurrence_fresh c (e := e) (instance := instance) (work := work)
        Hfresh).
  - exact (proj2 (proj2 Haltered)).
Qed.

Local Lemma chain_dominance b :
  forall ns es, point_chain (Pre.pg c) ns es ->
  forall first default work, In b (Graph.nodes (Pre.bg c)) ->
    nth_error ns 0 = Some first ->
    incl es (SsaPoints.instruction_edges points b) ->
    local_dominance first work ->
    local_dominance (last ns default)
      (fold_left (PreRename.instruction c index b (SsaPoints.parameter_edge points b)) es work).
Proof.
  intros ns es Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros first default work Hb Hfirst Hedges Hwork.
  - cbn [nth_error] in Hfirst; inversion Hfirst; subst first; exact Hwork.
  - cbn [nth_error] in Hfirst; inversion Hfirst; subst first.
    cbn [fold_left last].
    assert (Hedge_list : In edge (SsaPoints.instruction_edges points b)).
    { apply Hedges; now left. }
    assert (Hnext : local_dominance next
      (PreRename.instruction c index b (SsaPoints.parameter_edge points b) work edge)).
    { rewrite <- Htarget; apply instruction_dominance.
      - exact (PreCoverage.instruction_edge_listed c Hlaw Hb Hedge_list).
      - exact (instruction_edges_internal (Pre.point_laws c (Pre.graphs c Hlaw))
          b edge Hb Hedge_list).
      - reflexivity.
      - pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
          n edge Hedge) as Hsource.
        change (Graph.source (Pre.pg c) edge = n) in Hsource; rewrite Hsource; exact Hwork. }
    apply (IH next default); [exact Hb|reflexivity| |exact Hnext].
    intros e He; apply Hedges; now right.
Qed.

Local Lemma argument_output_dominance frames acc arg :
  output_dominance acc -> output_dominance (PreRename.select_argument c frames acc arg).
Proof.
  intro Hacc; rewrite PreRename.select_argument_equation.
  destruct Hacc; constructor; assumption.
Qed.

(** The actual ordered block ends with selected definitions dominating its last point. *)
Theorem block_dominance :
  forall b first frames acc, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
    local_dominance first (frames, acc) ->
    local_dominance (last (SsaPoints.points_in_block points b) first)
      (PreRename.block c index b frames acc).
Proof.
  intros b first frames acc Hb Hfirst Hwork; rewrite PreRename.block_equation.
  set (entered := match SsaPoints.points_in_block points b with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c index point (frames, acc)
    end).
  assert (Hentered : local_dominance first entered).
  { unfold entered; destruct (SsaPoints.points_in_block points b); [exact Hwork|].
    apply mark_exit_dominance; exact Hwork. }
  pose proof (chain_dominance b _ _ (points_ordered (Pre.point_laws c (Pre.graphs c Hlaw)) b Hb)
    first first entered Hb Hfirst (fun e He => He) Hentered) as Hbody.
  destruct Hbody as [Hsource [Hscope Houtput]].
  split; [exact Hsource|]; split; [exact Hscope|].
  apply (PreFrameStep.fold_preserves _ output_dominance); [|exact Houtput].
  intros current pair Hcurrent; apply argument_output_dominance; exact Hcurrent.
Qed.

(** Pending scopes denote named source blocks and dominate each block's actual first point. *)
Definition task_dominance (pair : positive * PreRename.scope B E U) : Prop :=
  exists b first, Prepared.name_of (Pre.blocks c) (fst pair) = Some b /\
    In b (Graph.nodes (Pre.bg c)) /\
    nth_error (SsaPoints.points_in_block points b) 0 = Some first /\
    PreFrameInvariant.scope_source c data (snd pair) /\ scope_dominance first (snd pair).

Definition walk_dominance (current : PreRename.work B BE E U) : Prop :=
  output_dominance (PreRename.output current) /\ Forall task_dominance (PreRename.pending current).

Local Lemma empty_output_dominance : output_dominance PreRename.empty_accumulator.
Proof.
  constructor; [apply Map.wf_empty|].
  intros e d Hget; cbn [PreRename.empty_accumulator PreRename.occurrence_index] in Hget.
  rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Prepared root tasks start with source-backed scopes dominating their actual entry point. *)
Theorem initial_dominance : walk_dominance (PreRename.initial index).
Proof.
  split; rewrite PreRename.initial_equation; cbn [PreRename.output PreRename.pending].
  - exact empty_output_dominance.
  - apply Forall_forall; intros [id frames] Hin; apply in_map_iff in Hin.
    destruct Hin as [root [Heq Hroot]]; inversion Heq; subst frames root.
    unfold index in Hroot.
    rewrite (proj1 (PreRename.prepare_walk_equations c data)) in Hroot.
    pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
    apply (Prepared.entry_ids_spec _ _ Hp) in Hroot; destruct Hroot as [b [Hb Hid]].
    rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)) in Hb.
    destruct (Pre.entry_position c (Pre.graphs c Hlaw)) as
      [entry [first [Hentries [Hentry Hposition]]]].
    rewrite Hentries in Hb; destruct Hb as [<-|[]].
    exists entry, first; split.
    + exact (Prepared.name_of_id_of _ _ _ Hp Hid).
    + split.
      * apply (entries_in (blocks_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))).
        change (In entry (Graph.entries (Pre.bg c))); rewrite Hentries; now left.
      * split; [exact Hposition|]; split.
        -- exact (PreFrameInvariant.entry_source c data Hlaw Hdata).
        -- apply entry_dominance; exact Hentry.
Qed.

(** The last element of a nonempty list is independent of its fallback value. *)
Theorem last_default {X} (xs : list X) a b :
  xs <> [] -> last xs a = last xs b.
Proof.
  induction xs as [|head rest IH]; [contradiction|].
  intro Hnonempty; destruct rest as [|next rest]; [reflexivity|].
  cbn [last]; apply IH; discriminate.
Qed.

Local Lemma child_task {id b first frames pair} :
  Prepared.name_of (Pre.blocks c) id = Some b -> In b (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block points b) 0 = Some first ->
  PreFrameInvariant.scope_source c data frames ->
  scope_dominance (last (SsaPoints.points_in_block points b) first) frames ->
  In pair (Index.find positive_encoding id (PreRename.children index)) ->
    task_dominance (fst pair, frames).
Proof.
  intros Hname Hb Hfirst Hsource Hscope Hpair; destruct pair as [child parent].
  unfold index in Hpair.
  destruct (PreRename.prepare_walk_equations c data) as [Hroots [Hparents [Hchildren Hbudget]]].
  rewrite Hchildren, Index.find_group_by, filter_In in Hpair.
  destruct Hpair as [Hpair Hsame]; cbn [snd] in Hsame.
  apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst parent.
  apply (Map.elements_spec positive_encoding positive_encoding_laws) in Hpair;
    [|exact (proj1 (Dom.maps_wf _ _ (Pre.tree_exact c (Pre.graphs c Hlaw))))].
  destruct (Dom.idom_domain _ _ (Pre.tree_exact c (Pre.graphs c Hlaw)) child id Hpair)
    as [owner [parent [Hchild_name [Hparent_name [Hreachable Hparent_reachable]]]]].
  assert (Hparent : parent = b) by congruence; subst parent.
  assert (Howner : In owner (Graph.nodes (Pre.bg c))).
  { rewrite <- (Pre.blocks_source c (Pre.graphs c Hlaw)).
    apply (reachable_in_nodes _ _ (proj1 (Pre.blocks_ready c (Pre.graphs c Hlaw)))); exact Hreachable. }
  pose proof (blocks_nonempty (Pre.point_laws c (Pre.graphs c Hlaw)) owner Howner) as Hnonempty.
  fold points in Hnonempty.
  destruct (SsaPoints.points_in_block points owner) as [|head rest] eqn:Hpoints; [contradiction|].
  exists owner, head; split; [exact Hchild_name|]; split; [exact Howner|].
  split; [rewrite Hpoints; reflexivity|]; split; [exact Hsource|].
  apply (scope_advance (n := last (SsaPoints.points_in_block points b) head)); [|].
  - pose proof (PreCoverage.block_parent_immediate c Hlaw b owner head id child
      Hb Howner
      (Prepared.id_of_name_of _ _ _ (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) Hname)
      (Prepared.id_of_name_of _ _ _ (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw))))
        Hchild_name) Hpair ltac:(fold points; rewrite Hpoints; reflexivity)) as Hboundary.
    exact (proj1 (proj1 Hboundary)).
  - rewrite (last_default (SsaPoints.points_in_block points b) head first
      (blocks_nonempty (Pre.point_laws c (Pre.graphs c Hlaw)) b Hb)).
    exact Hscope.
Qed.

Definition result_dominance
    (result : PreRename.work B BE E U + PreRename.stopped B BE E U) : Prop :=
  match result with
  | inl current => walk_dominance current
  | inr final => output_dominance (PreRename.stop_output final)
  end.

(** One actual driver step preserves point provenance and the pending task domains. *)
Theorem step_dominance current :
  walk_dominance current -> result_dominance (PreRename.step c index current).
Proof.
  intros [Houtput Htasks]; rewrite PreRename.step_equation.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [exact Houtput|].
  inversion Htasks as [|pair tail Htask Hrest]; subst pair tail.
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)); [split; assumption|].
  destruct Htask as [b [first [Hname [Hb [Hfirst [Hsource Hscope]]]]]]; cbn [fst snd] in Hname.
  rewrite Hname.
  destruct (block_dominance b first frames (PreRename.output current) Hb Hfirst
    (conj Hsource (conj Hscope Houtput))) as [Hfinal_source [Hfinal_scope Hfinal_output]].
  split; [exact Hfinal_output|]; apply Forall_app; split; [|exact Hrest].
  apply Forall_forall; intros [child scope] Hin; apply in_map_iff in Hin.
  destruct Hin as [pair [Heq Hpair]]; inversion Heq; subst scope.
  exact (child_task Hname Hb Hfirst Hfinal_source Hfinal_scope Hpair).
Qed.

Local Lemma runs_dominance :
  forall budget current result, runs (PreRename.step_c c index) budget current result ->
    walk_dominance current -> result_dominance result.
Proof.
  apply (PreFrameStep.runs_invariant (PreRename.step_c c index) result_dominance).
  exact step_dominance.
Qed.

(** The same actual indexed run preserves occurrence-target and reused-source definition dominance. *)
Theorem run_dominance :
  output_dominance (PreRename.stop_output (PreRename.run c index)).
Proof.
  pose proof (runs_dominance _ _ _ (iterate_value (PreRename.step_c c index)
    (PreRename.walk_budget index) (PreRename.initial index)) initial_dominance) as Hrun.
  rewrite PreRename.run_equation.
  destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index))); [exact (proj1 Hrun)|exact Hrun].
Qed.

End Provenance.

End PreFrameDominance.
