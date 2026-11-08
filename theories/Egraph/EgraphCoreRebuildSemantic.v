(** * Semantic laws of the actual dirty rebuild

    Local grammar and soundness preservation compose through the counted parent loop.
    For example, an exhausted prefix preserves old terms and maintained fuel proves closure.
    Builds on: EgraphCoreSemantic, EgraphCoreProgress and EgraphCoreRepresentation. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseMap.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphCoreRepresentation
  EgraphCoreStructural EgraphCoreMaintained EgraphCoreInvariant EgraphCoreTransition
  EgraphCoreBatch EgraphCoreProgress EgraphCoreView EgraphCoreSemantic EgraphCoreRepair
  EgraphCoreRepairStep EgraphCoreObservation.
Import List.ListNotations.

Module EggRebuildSem.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).
Context (Hl : EggRepresentation.encoding_laws a).

(** The semantic loop property retains raw WF, old meanings and every old soundness instance. *)
Definition semantic_inv (initial h : Egraph.t K Sort V) : Prop :=
  EggRepresentation.structural_wf a h /\
  EggRepresentation.extends a initial h /\
  forall (H F C : Type) (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)),
    EggRepresentation.sound a adm facts rules initial ->
    EggRepresentation.sound a adm facts rules h.

Local Lemma initial_semantic g :
  EggRepresentation.structural_wf a g -> semantic_inv g g.
Proof.
  intro Hwf; split; [exact Hwf|]; split; [split; auto|].
  intros H F C adm facts rules Hsound; exact Hsound.
Qed.

Local Lemma queue_semantic initial g queue :
  semantic_inv initial g -> semantic_inv initial (Egraph.with_queue g queue).
Proof.
  intros [Hwf [Hext Hsound]]; split; [exact (EggView.queue_structural a g queue Hwf)|].
  split.
  - exact (EggStructural.extends_trans a initial g (Egraph.with_queue g queue) Hext
      (EggView.extends_observation a g (Egraph.with_queue g queue) eq_refl eq_refl)).
  - intros H F C adm facts rules Hinitial.
    exact (EggView.sound_observation a adm facts rules g (Egraph.with_queue g queue)
      eq_refl eq_refl (Hsound H F C adm facts rules Hinitial)).
Qed.

Local Lemma parent_semantic initial g i work :
  Egraph.kernel_inv_on a g (i :: work) -> EggTransition.layout a g ->
  semantic_inv initial g -> semantic_inv initial (Egraph.repair_node a g i).
Proof.
  intros Hkernel Hlayout [Hwf [Hext Hsound]]; split.
  - exact (EggSemantic.repair_node_structural a Hl g i work Hwf Hkernel).
  - split.
    + exact (EggStructural.extends_trans a initial g (Egraph.repair_node a g i) Hext
        (EggSemantic.repair_node_extends a Hl g i work Hwf Hkernel)).
    + intros H F C adm facts rules Hinitial.
      exact (EggSemantic.repair_node_sound a Hl adm facts rules g i work Hwf Hkernel
        (Hsound H F C adm facts rules Hinitial)).
Qed.

(** The actual counted iterator preserves raw WF, old terms and soundness on both outcomes. *)
Theorem rebuild_semantics g :
  EggRepresentation.wf a g -> semantic_inv g (Egraph.rebuild a g).
Proof.
  intro Hwf.
  pose proof (EggStructural.node_code_injective a Hl) as Hcodes.
  pose proof (EggRepresentation.wf_structural a g Hwf) as Hstruct.
  pose proof (EggRepairBatch.iterate_property a Hcodes (semantic_inv g)
    (parent_semantic g) (queue_semantic g) (Egraph.rebuild_fuel g) g 0%N
    (EggRepresentation.wf_kernel a g Hwf) (EggMaintained.layout a g Hstruct)
    (initial_semantic g Hstruct)) as Hrun.
  rewrite Egraph.rebuild_equation, Egraph.rebuild_run_equation.
  destruct (Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0%N)))
    as [[h visits]|[h visits]]; exact Hrun.
Qed.

(** Maintained fuel stops the actual rebuild with unchanged nodes and an empty dirty queue. *)
Theorem rebuild_local g :
  EggRepresentation.wf a g ->
  Egraph.kernel_inv a (Egraph.rebuild a g) /\
  Egraph.dirty (Egraph.rebuild a g) = [] /\
  Egraph.nodes (Egraph.rebuild a g) = Egraph.nodes g /\
  Egraph.next (Egraph.rebuild a g) = Egraph.next g.
Proof.
  intro Hwf.
  destruct (EggProgress.iterate_stops a g (EggStructural.node_code_injective a Hl)
    (EggRepresentation.wf_kernel a g Hwf)
    (EggMaintained.layout a g (EggRepresentation.wf_structural a g Hwf)))
    as [h [visits [Hrun [Hkernel [Hlayout [Hnodes [Hnext Hempty]]]]]]].
  rewrite Egraph.rebuild_equation, Egraph.rebuild_run_equation, Hrun.
  split; [exact Hkernel|]; split; [exact Hempty|]; split; assumption.
Qed.

(** Rebuild establishes the unchanged public clean predicate under maintained WF. *)
Theorem rebuild_clean g :
  EggRepresentation.wf a g -> EggRepresentation.clean a (Egraph.rebuild a g).
Proof.
  intro Hwf.
  destruct (rebuild_semantics g Hwf) as [Hstruct Hsemantic].
  destruct (rebuild_local g Hwf) as [Hkernel [Hempty Hdata]]; constructor.
  - constructor; assumption.
  - intros i j n m Hi Hj Hcanonical.
    exact (EggKernelInv.quiescent_congruence a _ i j n m Hkernel Hempty Hi Hj Hcanonical).
  - intros key owner Hget.
    destruct (EggKernelInv.quiescent_memo_current a _ key owner Hkernel Hempty Hget)
      as [n [Hnode Hcode]].
    exists owner, n; split; [exact Hnode|]; split; [reflexivity|exact Hcode].
  - intros i n Hnode.
    exact (EggKernelInv.quiescent_memo_complete a _ i n Hkernel Hempty Hnode).
Qed.

(** Rebuild preserves old finite terms and class equalities through the actual callbacks. *)
Theorem rebuild_preserves g :
  EggRepresentation.wf a g -> EggRepresentation.extends a g (Egraph.rebuild a g).
Proof.
  intro Hwf; exact (proj1 (proj2 (rebuild_semantics g Hwf))).
Qed.

(** Rebuild preserves generated-equality soundness without requiring sound rules. *)
Theorem rebuild_sound {H F C} (adm : EggSem.t K V C -> Prop)
    (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)) g :
  EggRepresentation.wf a g -> EggRepresentation.sound a adm facts rules g ->
  EggRepresentation.sound a adm facts rules (Egraph.rebuild a g).
Proof.
  intro Hwf; exact (proj2 (proj2 (rebuild_semantics g Hwf)) H F C adm facts rules).
Qed.

(** No dirty class remains after a maintained rebuild. *)
Theorem rebuild_dirty_empty g :
  EggRepresentation.wf a g -> Egraph.dirty (Egraph.rebuild a g) = [].
Proof.
  intro Hwf; exact (proj1 (proj2 (rebuild_local g Hwf))).
Qed.

Section Idle.
Context (initial : Egraph.t K Sort V) (Hclean : EggRepresentation.clean a initial).

Local Definition idle_inv h : Prop :=
  Egraph.nodes h = Egraph.nodes initial /\
  forall c, Egraph.find a h c = Egraph.find a initial c.

Local Lemma idle_queue g queue :
  idle_inv g -> idle_inv (Egraph.with_queue g queue).
Proof.
  intros [Hnodes Hfind]; split; [exact Hnodes|exact Hfind].
Qed.

Local Lemma idle_collision g i n other work :
  Egraph.kernel_inv_on a g work -> EggTransition.layout a g -> idle_inv g ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g) = Some other ->
  Egraph.find a g i = Egraph.find a g other.
Proof.
  intros Hkernel Hlayout [Hnodes Hfind] Hi Hhit.
  destruct (EggRepairInv.collision_witness a g n other Hkernel
    (EggTransition.forest_wf a g Hlayout) (EggStructural.node_code_injective a Hl) Hhit)
    as [m [Hother Hcanonical]].
  rewrite Hnodes in Hi, Hother.
  assert (Hinitial : Egraph.canonical a initial n = Egraph.canonical a initial m).
  { rewrite <- (EggView.canonical_representatives a g initial Hfind n),
      <- (EggView.canonical_representatives a g initial Hfind m); exact Hcanonical. }
  pose proof (EggRepresentation.congruence_closed a initial Hclean i other n m
    Hi Hother Hinitial) as Hsame.
  rewrite Hfind, Hfind; exact Hsame.
Qed.

Local Lemma idle_parent g i work :
  Egraph.kernel_inv_on a g (i :: work) -> EggTransition.layout a g ->
  idle_inv g -> idle_inv (Egraph.repair_node a g i).
Proof.
  intros Hkernel Hlayout [Hnodes Hfind]; split.
  - rewrite EggRepairStep.repair_node_nodes; exact Hnodes.
  - intro query; rewrite Egraph.repair_node_equation.
    destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode,
      (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try apply Hfind.
    cbv zeta; rewrite <- Egraph.repair_base_equation.
    rewrite (EggObservation.base_equation a g i n Hkernel Hlayout
      (EggStructural.node_code_injective a Hl) Hnode).
    destruct (Map.get Egraph.id_encoding
      (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|] eqn:Hhit.
    + exact (eq_trans
        (EggTransition.merge_same_representatives a g i other _ query
          (EggTransition.forest_wf a g Hlayout)
          (idle_collision g i n other (i :: work) Hkernel Hlayout (conj Hnodes Hfind)
            Hnode Hhit)) (Hfind query)).
    + exact (Hfind query).
Qed.

(** A clean start retains every exact representative throughout the actual dirty loop. *)
Theorem rebuild_idle : EggRepresentation.same_class_equal a initial (Egraph.rebuild a initial).
Proof.
  pose proof (EggRepresentation.clean_wf a initial Hclean) as Hwf.
  pose proof (EggRepairBatch.iterate_property a (EggStructural.node_code_injective a Hl)
    idle_inv idle_parent idle_queue (Egraph.rebuild_fuel initial) initial 0%N
    (EggRepresentation.wf_kernel a initial Hwf)
    (EggMaintained.layout a initial (EggRepresentation.wf_structural a initial Hwf))
    (conj eq_refl (fun _ => eq_refl))) as Hrun.
  rewrite Egraph.rebuild_equation, Egraph.rebuild_run_equation.
  destruct (Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel initial)
    (initial, 0%N))) as [[h visits]|[h visits]]; destruct Hrun as [Hnodes Hfind];
    intros c d; unfold EggRepresentation.same_class; rewrite !Hfind; reflexivity.
Qed.

End Idle.

End Graph.

End EggRebuildSem.
