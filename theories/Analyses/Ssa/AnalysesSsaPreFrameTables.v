(** * Stability of visited-block occurrence tables

    Every written occurrence belongs to a visited block and later blocks preserve its table entry.
    For example, visiting the right arm of a diamond cannot overwrite the left arm's fresh flag.
    Builds on: AnalysesSsaPreFrameEnd, AnalysesSsaPreCoverage and GraphPrepared. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd.
Import List.ListNotations.

Module PreFrameTables.

Section Stability.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Hypothesis Hlaw : Pre.laws c.

(** An edge's occurrence and fresh bit form the protected instruction-table observation. *)
Definition stamp query (acc : PreRename.accumulator B BE E U) :=
  (Map.get (Pre.ee (Pre.keys c)) query (PreRename.occurrence_index acc),
    FinSet.mem (Pre.ee (Pre.keys c)) query (PreRename.fresh_index acc)).

Local Lemma mark_stamp query frames acc key :
  stamp query (PreRename.mark c frames acc key) = stamp query acc.
Proof.
  rewrite PreRename.mark_equation.
  destruct (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) as [d real].
  destruct d, real; reflexivity.
Qed.

Local Lemma mark_exit_stamp query index n work :
  stamp query (snd (PreRename.mark_exit c index n work)) = stamp query (snd work).
Proof.
  rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index)); [|reflexivity].
  apply PreFrameStep.fold_observation; intros acc key; apply mark_stamp.
Qed.

Local Lemma alter_stamp query instance work key :
  stamp query (snd (PreRename.alter c instance work key)) = stamp query (snd work).
Proof.
  rewrite PreRename.alter_equation; destruct work as [frames acc].
  destruct instance as [current|]; cbn [snd].
  - destruct (eqb positive_encoding (fst current) (fst key)); [reflexivity|apply mark_stamp].
  - apply mark_stamp.
Qed.

Local Lemma occurrence_other query e instance work :
  PreFrameEnd.accumulator_wf c (snd work) -> query <> e ->
    stamp query (snd (fst (PreRename.occurrence c e instance work))) = stamp query (snd work).
Proof.
  intros [Hocc [Hfresh Hrest]] Hne; rewrite PreRename.occurrence_equation.
  destruct instance as [[id u]|]; [|reflexivity].
  destruct work as [frames acc]; cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u); unfold stamp;
    cbn [fst snd PreRename.occurrence_index PreRename.fresh_index].
  - rewrite (Map.get_set_other _ (Pre.ee_laws c (Pre.graphs c Hlaw))) by assumption; reflexivity.
  - rewrite (Map.get_set_other _ (Pre.ee_laws c (Pre.graphs c Hlaw))) by assumption.
    rewrite FinSet.mem_add by exact Hfresh.
    rewrite (proj2 (eqb_false_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw)) _ _) Hne).
    reflexivity.
Qed.

(** An instruction changes no other edge's selected occurrence or fresh flag. *)
Theorem instruction_other query {index b parameter work e} :
  PreFrameEnd.accumulator_wf c (snd work) -> query <> e ->
    stamp query (snd (PreRename.instruction c index b parameter work e)) = stamp query (snd work).
Proof.
  intros Hwf Hne; rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|]; [|reflexivity].
  rewrite mark_exit_stamp; cbn [snd].
  rewrite (PreFrameStep.fold_observation (PreRename.alter c (PreRename.evaluation info))
    (fun work => stamp query (snd work)) (fun work key => alter_stamp query _ work key)).
  apply occurrence_other; assumption.
Qed.

Local Lemma fold_instruction_other query index b parameter :
  forall es work, PreFrameEnd.accumulator_wf c (snd work) -> ~ In query es ->
    stamp query (snd (fold_left (PreRename.instruction c index b parameter) es work)) =
      stamp query (snd work).
Proof.
  intro es; induction es as [|e rest IH]; intros work Hwf Hnone; [reflexivity|].
  cbn [fold_left]; rewrite IH.
  - apply instruction_other; [exact Hwf|intro Heq; subst query; apply Hnone; now left].
  - apply PreFrameEnd.instruction_wf; exact Hwf.
  - intro Hin; apply Hnone; now right.
Qed.

Local Lemma argument_stamp query frames acc arg :
  stamp query (PreRename.select_argument c frames acc arg) = stamp query acc.
Proof.
  rewrite PreRename.select_argument_equation; reflexivity.
Qed.

(** An indexed block cannot change the table stamp of an edge outside its ordered body. *)
Theorem block_other query {index b frames acc} :
  PreFrameEnd.accumulator_wf c acc ->
    ~ In query (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    stamp query (snd (PreRename.block c index b frames acc)) = stamp query acc.
Proof.
  intros Hwf Hnone; rewrite PreRename.block_equation; cbn [snd].
  rewrite (PreFrameStep.fold_observation
    (fun current pair => PreRename.select_argument c _ current (snd pair))
    (stamp query) (fun current pair => argument_stamp query _ current (snd pair))).
  rewrite fold_instruction_other; [| |exact Hnone].
  - destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [reflexivity|apply mark_exit_stamp].
  - destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|apply PreFrameEnd.mark_exit_wf; exact Hwf].
Qed.

(** Every ordered instruction's actual source point belongs to that same source block. *)
Theorem instruction_owner {b e} :
  In b (Graph.nodes (Pre.bg c)) ->
  In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e) = b.
Proof.
  intros Hb He; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hp.
  destruct (PreFrg.chain_source _ (points_ordered Hp b Hb) He) as [point [Hpoint Hedge]].
  pose proof (out_source (points_graph_wf Hp) point e Hedge) as Hsource.
  change (Graph.source (Pre.pg c) e = point) in Hsource; rewrite Hsource.
  exact (points_owner Hp b point Hb Hpoint).
Qed.

Local Lemma named_block {id b} :
  Prepared.name_of (Pre.blocks c) id = Some b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intro Hname; pose proof (Pre.blocks_ready c (Pre.graphs c Hlaw)) as Hready.
  rewrite <- (Pre.blocks_source c (Pre.graphs c Hlaw)).
  apply (Prepared.ids_domain _ (proj2 (proj2 Hready))).
  exists id; exact (Prepared.id_of_name_of _ _ _ (proj2 (proj2 Hready)) Hname).
Qed.

Local Lemma named_injective {id other b} :
  Prepared.name_of (Pre.blocks c) id = Some b ->
  Prepared.name_of (Pre.blocks c) other = Some b -> id = other.
Proof.
  intros Hid Hother; pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
  pose proof (Prepared.id_of_name_of _ _ _ Hp Hid).
  pose proof (Prepared.id_of_name_of _ _ _ Hp Hother); congruence.
Qed.

(** Every nonempty table stamp is owned by an actually visited named block. *)
Record owned (current : PreRename.work B BE E U) : Prop := Owned {
  owned_seen_wf : FinSet.wf positive_encoding (PreRename.visited current);
  owned_output_wf : PreFrameEnd.accumulator_wf c (PreRename.output current);
  owned_written : forall e,
    stamp e (PreRename.output current) <> (None, false) ->
    exists id b, Prepared.name_of (Pre.blocks c) id = Some b /\
      FinSet.mem positive_encoding id (PreRename.visited current) = true /\
      In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)
}.

Local Lemma edge_membership e b :
  existsb (fun other => eqb (Pre.ee (Pre.keys c)) e other)
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) = true <->
  In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b).
Proof.
  rewrite existsb_exists; split.
  - intros [other [Hother Hsame]].
    apply (eqb_true_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hsame; subst other; exact Hother.
  - intro Hin; exists e; split; [exact Hin|apply eqb_refl].
Qed.

(** The actual initial task list starts with no written occurrence or fresh flag. *)
Theorem initial_owned (index : PreRename.prepared B BE N E U) : owned (PreRename.initial index).
Proof.
  constructor; rewrite PreRename.initial_equation.
  - apply FinSet.wf_empty.
  - exact (PreFrameEnd.empty_accumulator_wf c).
  - intros e Hwritten; exfalso; apply Hwritten; unfold stamp.
    cbn [PreRename.output PreRename.empty_accumulator
      PreRename.occurrence_index PreRename.fresh_index].
    rewrite Map.get_empty, FinSet.mem_empty; reflexivity.
Qed.

Local Lemma add_owned index current id frames rest b :
  owned current -> Prepared.name_of (Pre.blocks c) id = Some b ->
  owned (PreRename.Work
    (map (fun pair => (fst pair, fst (PreRename.block c index b frames (PreRename.output current))))
      (Index.find positive_encoding id (PreRename.children index)) ++ rest)
    (FinSet.add positive_encoding id (PreRename.visited current))
    (snd (PreRename.block c index b frames (PreRename.output current)))).
Proof.
  intros Howned Hname; constructor.
  - apply FinSet.wf_add; exact (owned_seen_wf _ Howned).
  - apply PreFrameEnd.block_wf; exact (owned_output_wf _ Howned).
  - intros e Hwritten.
    destruct (existsb (fun other => eqb (Pre.ee (Pre.keys c)) e other)
      (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)) eqn:Hin.
    + exists id, b; split; [exact Hname|]; split.
      * cbn [PreRename.visited]; rewrite FinSet.mem_add by exact (owned_seen_wf _ Howned).
        rewrite eqb_refl; reflexivity.
      * apply edge_membership; exact Hin.
    + assert (Hnone : ~ In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)).
      { intro Hmember; apply edge_membership in Hmember; congruence. }
      cbn [PreRename.output] in Hwritten.
      rewrite (block_other e (owned_output_wf _ Howned) Hnone) in Hwritten.
      destruct (owned_written _ Howned e Hwritten) as [other [owner [Howner [Hseen Hmember]]]].
      exists other, owner; split; [exact Howner|]; split; [|exact Hmember].
      cbn [PreRename.visited]; rewrite FinSet.mem_add by exact (owned_seen_wf _ Howned).
      rewrite Hseen, orb_true_r; reflexivity.
Qed.

Local Lemma step_owned {index current next} :
  owned current -> PreRename.step c index current = inl next -> owned next.
Proof.
  intros Howned Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest]; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)).
  - inversion Hstep; subst next; destruct Howned; constructor; assumption.
  - destruct (Prepared.name_of (Pre.blocks c) id) as [b|] eqn:Hname; [|discriminate].
    inversion Hstep; subst next; exact (add_owned index current id frames rest b Howned Hname).
Qed.

(** Every continuing actual driver prefix retains visited-block ownership of all written entries. *)
Theorem runs_owned {index budget current final} :
  runs (PreRename.step_c c index) budget current (inl final) -> owned current -> owned final.
Proof.
  intro Hrun; remember (inl final) as result eqn:Hresult; revert final Hresult.
  induction Hrun as [current|budget current stopped Hstop|
    budget current next result Hstep Hrun IH]; intros final Hresult Howned.
  - inversion Hresult; subst final; exact Howned.
  - discriminate.
  - apply (IH final Hresult); eapply step_owned; eassumption.
Qed.

(** A fresh block task has no previous occurrence or fresh flag for any instruction in its body. *)
Theorem unvisited_unwritten {current id b} :
  owned current -> Prepared.name_of (Pre.blocks c) id = Some b ->
  FinSet.mem positive_encoding id (PreRename.visited current) = false ->
  forall e, In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    stamp e (PreRename.output current) = (None, false).
Proof.
  intros Howned Hname Hfresh e He.
  destruct (stamp e (PreRename.output current)) as [[d|] fresh] eqn:Hstamp.
  all: try (destruct fresh; [|reflexivity]).
  all: exfalso; destruct (owned_written _ Howned e ltac:(rewrite Hstamp; discriminate))
    as [other [owner [Howner [Hseen Hmember]]]].
  all: assert (Hblock : owner = b) by
    (pose proof (instruction_owner (named_block Howner) Hmember);
      pose proof (instruction_owner (named_block Hname) He); congruence).
  all: subst owner; pose proof (named_injective Hname Howner); subst other; congruence.
Qed.

Local Lemma step_seen_stamp {index current next id b e} :
  owned current -> Prepared.name_of (Pre.blocks c) id = Some b ->
  FinSet.mem positive_encoding id (PreRename.visited current) = true ->
  In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
  PreRename.step c index current = inl next ->
    FinSet.mem positive_encoding id (PreRename.visited next) = true /\
    stamp e (PreRename.output next) = stamp e (PreRename.output current).
Proof.
  intros Howned Hname Hseen He Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[other frames] rest]; [discriminate|].
  destruct (FinSet.mem positive_encoding other (PreRename.visited current)) eqn:Hother_seen.
  - inversion Hstep; subst next; split; [exact Hseen|reflexivity].
  - destruct (Prepared.name_of (Pre.blocks c) other) as [owner|] eqn:Howner; [|discriminate].
    inversion Hstep; subst next; split.
    + cbn [PreRename.visited]; rewrite FinSet.mem_add by exact (owned_seen_wf _ Howned).
      rewrite Hseen, orb_true_r; reflexivity.
    + apply block_other; [exact (owned_output_wf _ Howned)|].
      intro Hmember.
      assert (Hblock : owner = b).
      { pose proof (instruction_owner (named_block Howner) Hmember).
        pose proof (instruction_owner (named_block Hname) He); congruence. }
      subst owner; pose proof (named_injective Hname Howner); subst other; congruence.
Qed.

Definition output_of (result : PreRename.work B BE E U + PreRename.stopped B BE E U) :=
  match result with
  | inl current => PreRename.output current
  | inr final => PreRename.stop_output final
  end.

Local Lemma terminal_output {index current final} :
  PreRename.step c index current = inr final ->
    PreRename.stop_output final = PreRename.output current.
Proof.
  intro Hstep; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest].
  - inversion Hstep; reflexivity.
  - destruct (FinSet.mem positive_encoding id (PreRename.visited current)); [discriminate|].
    destruct (Prepared.name_of (Pre.blocks c) id); [discriminate|].
    inversion Hstep; reflexivity.
Qed.

(** Every later raw driver outcome preserves the occurrence and fresh flag of a visited block. *)
Theorem runs_seen_stamp {index budget current result} :
  runs (PreRename.step_c c index) budget current result -> owned current ->
  forall id b, Prepared.name_of (Pre.blocks c) id = Some b ->
    FinSet.mem positive_encoding id (PreRename.visited current) = true ->
  forall e, In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    stamp e (output_of result) = stamp e (PreRename.output current).
Proof.
  intro Hrun; induction Hrun as [current|budget current final Hstop|
    budget current next result Hstep Hrun IH]; intros Howned id b Hname Hseen e He.
  - reflexivity.
  - cbn [output_of]; rewrite (terminal_output Hstop); reflexivity.
  - destruct (step_seen_stamp Howned Hname Hseen He Hstep) as [Hnext_seen Hstamp].
    rewrite (IH (step_owned Howned Hstep) id b Hname Hnext_seen e He); exact Hstamp.
Qed.

(** The actual suffix retains exactly the table produced by a newly visited block. *)
Theorem block_table_final :
  forall index current, owned current ->
  forall next result budget id frames rest b,
    PreRename.pending current = (id, frames) :: rest ->
    FinSet.mem positive_encoding id (PreRename.visited current) = false ->
    Prepared.name_of (Pre.blocks c) id = Some b ->
    PreRename.step c index current = inl next ->
    runs (PreRename.step_c c index) budget next result ->
  forall e, In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    stamp e (output_of result) =
      stamp e (snd (PreRename.block c index b frames (PreRename.output current))).
Proof.
  intros index current Howned next result budget id frames rest b
    Hpending Hfresh Hname Hstep Hrun e He.
  pose proof (step_owned Howned Hstep) as Hnext.
  assert (Hseen : FinSet.mem positive_encoding id (PreRename.visited next) = true).
  { rewrite PreRename.step_equation, Hpending, Hfresh, Hname in Hstep.
    inversion Hstep; subst next; cbn [PreRename.visited].
    rewrite FinSet.mem_add by exact (owned_seen_wf _ Howned); rewrite eqb_refl; reflexivity. }
  rewrite (runs_seen_stamp Hrun Hnext id b Hname Hseen e He).
  rewrite PreRename.step_equation, Hpending, Hfresh, Hname in Hstep.
  inversion Hstep; reflexivity.
Qed.

(** Remaining instructions have no previous occurrence or fresh flag before their first visit. *)
Definition unwritten es (acc : PreRename.accumulator B BE E U) :=
  forall e, In e es -> stamp e acc = (None, false).

(** A local instruction packet records its unwritten input and literal final-table agreement. *)
Definition instruction_packet index b parameter final
    (work : PreRename.scope B E U * PreRename.accumulator B BE E U) e : Prop :=
  stamp e (snd work) = (None, false) /\
  stamp e final = stamp e (snd (PreRename.instruction c index b parameter work e)).

Local Lemma chain_edges_nodup {ns es} :
  point_chain (Pre.pg c) ns es -> NoDup ns -> NoDup es.
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intro Hunique; [constructor|].
  apply NoDup_cons_iff in Hunique; destruct Hunique as [Hfresh Htail]; constructor.
  - intro Hin.
    destruct (PreFrg.chain_source _ Hchain Hin) as [point [Hpoint Hout]].
    pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      n edge Hedge) as Hsource.
    pose proof (out_source (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      point edge Hout) as Hsource'.
    assert (Hn : point = n) by congruence; rewrite Hn in Hpoint; exact (Hfresh Hpoint).
  - exact (IH Htail).
Qed.

(** The actual point ordering makes each block's instruction occurrence list duplicate-free. *)
Theorem instructions_nodup :
  forall b, In b (Graph.nodes (Pre.bg c)) ->
    NoDup (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b).
Proof.
  intros b Hb; apply (chain_edges_nodup (points_ordered
    (Pre.point_laws c (Pre.graphs c Hlaw)) b Hb)).
  exact (points_unique (Pre.point_laws c (Pre.graphs c Hlaw)) b).
Qed.

Local Lemma instruction_preserves_unwritten index b parameter work e es :
  PreFrameEnd.accumulator_wf c (snd work) -> ~ In e es -> unwritten es (snd work) ->
    unwritten es (snd (PreRename.instruction c index b parameter work e)).
Proof.
  intros Hwf Hfresh Hunwritten query Hquery.
  rewrite (instruction_other query Hwf).
  - exact (Hunwritten query Hquery).
  - intro Heq; subst query; exact (Hfresh Hquery).
Qed.

(** A duplicate-free ordered fold certifies every actual local packet against its final table. *)
Theorem instruction_packets :
  forall index b parameter final es work,
    PreFrameEnd.accumulator_wf c (snd work) -> NoDup es -> unwritten es (snd work) ->
    (forall e, In e es -> stamp e final =
      stamp e (snd (fold_left (PreRename.instruction c index b parameter) es work))) ->
    PreFrameStep.fold_enabled (PreRename.instruction c index b parameter)
      (instruction_packet index b parameter final) es work.
Proof.
  intros index b parameter final es; induction es as [|e rest IH];
    intros work Hwf Hunique Hunwritten Hfinal; [exact I|].
  apply NoDup_cons_iff in Hunique; destruct Hunique as [Hfresh Htail].
  split; [split|].
  - exact (Hunwritten e (or_introl eq_refl)).
  - specialize (Hfinal e (or_introl eq_refl)); cbn [fold_left] in Hfinal.
    rewrite (fold_instruction_other e index b parameter rest _
      (PreFrameEnd.instruction_wf c Hwf) Hfresh) in Hfinal; exact Hfinal.
  - apply IH.
    + apply PreFrameEnd.instruction_wf; exact Hwf.
    + exact Htail.
    + apply instruction_preserves_unwritten; [exact Hwf|exact Hfresh|].
      intros query Hin; apply Hunwritten; now right.
    + intros query Hin; exact (Hfinal query (or_intror Hin)).
Qed.

(** Successful real packets retain the exact selected version and freshly-created Boolean. *)
Theorem real_packet_stamp :
  forall {index b parameter work e info id u},
    PreFrameEnd.accumulator_wf c (snd work) ->
    Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index) = Some info ->
    PreRename.evaluation info = Some (id, u) -> stamp e (snd work) = (None, false) ->
    stamp e (snd (PreRename.instruction c index b parameter work e)) =
      let frame := PreRename.top_id (fst work) id u in
      let reuse := PreRename.frame_reuse c frame u in
      (Some (if reuse then PreFrg.operand_version (PreRename.selected frame)
        else PreFrg.Fresh e u), negb reuse).
Proof.
  intros index b parameter work e info id u Hwf Hinfo Hinstance Hunwritten.
  rewrite PreRename.instruction_equation, Hinfo, mark_exit_stamp; cbn [snd].
  rewrite (PreFrameStep.fold_observation (PreRename.alter c (PreRename.evaluation info))
    (fun work => stamp e (snd work)) (fun work key => alter_stamp e _ work key)).
  rewrite PreRename.occurrence_equation, Hinstance.
  destruct work as [frames acc]; cbn zeta; cbn [fst snd].
  unfold stamp in Hunwritten; inversion Hunwritten as [[Hget Hfresh]].
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u); unfold stamp;
    cbn [fst snd PreRename.occurrence_index PreRename.fresh_index].
  - rewrite Map.get_set_same by exact (proj1 Hwf); rewrite Hfresh; reflexivity.
  - rewrite Map.get_set_same by exact (proj1 Hwf).
    rewrite FinSet.mem_add by exact (proj1 (proj2 Hwf)); rewrite eqb_refl; reflexivity.
Qed.

Local Lemma block_body_stamp query index b frames acc :
  stamp query (snd (PreRename.block c index b frames acc)) =
    let entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | [] => (frames, acc)
    | first :: _ => PreRename.mark_exit c index first (frames, acc)
    end in
    stamp query (snd (fold_left (PreRename.instruction c index b
      (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
      (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered)).
Proof.
  rewrite PreRename.block_equation; cbn [snd].
  apply PreFrameStep.fold_observation; intros current pair; apply argument_stamp.
Qed.

(** Actual block-body histories certify local packets using the same final table observation. *)
Theorem block_packets :
  forall index b frames acc final, In b (Graph.nodes (Pre.bg c)) ->
    PreFrameEnd.accumulator_wf c acc ->
    unwritten (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) acc ->
    (forall e, In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
      stamp e final = stamp e (snd (PreRename.block c index b frames acc))) ->
    let entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | [] => (frames, acc)
    | first :: _ => PreRename.mark_exit c index first (frames, acc)
    end in
    PreFrameStep.history
      (PreFrameStep.checked_step (PreRename.instruction c index b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
        (instruction_packet index b (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) final))
      entered (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)
      (fold_left (PreRename.instruction c index b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
        (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered).
Proof.
  intros index b frames acc final Hb Hwf Hunwritten Hfinal entered.
  apply (proj2 (PreFrameStep.checked_history_fold _ _)); split; [|reflexivity].
  apply instruction_packets.
  - unfold entered; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact Hwf|apply PreFrameEnd.mark_exit_wf; exact Hwf].
  - exact (instructions_nodup b Hb).
  - intros e He; unfold entered.
    destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [exact (Hunwritten e He)|rewrite mark_exit_stamp; exact (Hunwritten e He)].
  - intros e He; unfold entered; rewrite <- block_body_stamp; exact (Hfinal e He).
Qed.

End Stability.

End PreFrameTables.
