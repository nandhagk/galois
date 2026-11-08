(** * Semantic preservation of actual parent repair

    A collision union is justified by a common finite term of its two stored nodes.
    For example, productive cyclic classes use their old finite witnesses in that justification.
    Builds on: EgraphCoreStructural, EgraphCoreRepairStep and EgraphCoreView. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseMap.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphCoreRepresentation
  EgraphCoreStructural EgraphCoreMaintained EgraphCoreInvariant EgraphCoreTransition
  EgraphCoreRepair EgraphCoreRepairStep EgraphCoreObservation EgraphCoreView.

Module EggSemantic.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).
Context (Hl : EggRepresentation.encoding_laws a).

Local Lemma given_congruent g i j n m :
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.nodes_get g j = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.union a g i j = Some (Egraph.merge a g i j Egraph.JGiven).
Proof.
  exact (EggRepairInv.congruent_union_equation a g i j n m Egraph.JGiven).
Qed.

(** Congruent merging retains raw WF for every justification annotation. *)
Theorem congruent_merge_structural g i j n m reason :
  EggRepresentation.structural_wf a g ->
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.nodes_get g j = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  EggRepresentation.structural_wf a (Egraph.merge a g i j reason).
Proof.
  intros Hwf Hi Hj Hcanonical.
  pose proof (EggStructural.union_wf a g i j (Egraph.merge a g i j Egraph.JGiven)
    Hl Hwf (given_congruent g i j n m Hi Hj Hcanonical)) as Hgiven.
  apply (EggView.structural_transport a (Egraph.merge a g i j Egraph.JGiven)
    (Egraph.merge a g i j reason) Hgiven eq_refl eq_refl eq_refl).
  - exact (EggRepresentation.memo_wf a g Hwf).
  - exact (EggView.memo_observation a (Egraph.merge a g i j Egraph.JGiven)
      (Egraph.merge a g i j reason) eq_refl eq_refl eq_refl
      (EggRepresentation.memo_correct a _ Hgiven)).
Qed.

(** Every actual class merge preserves old finite terms and old class equalities. *)
Theorem merge_extends g i j reason :
  EggRepresentation.structural_wf a g ->
  EggRepresentation.extends a g (Egraph.merge a g i j reason).
Proof.
  intro Hwf.
  assert (Hclasses : forall x y, EggRepresentation.same_class a g x y ->
    EggRepresentation.same_class a (Egraph.merge a g i j reason) x y).
  { intros x y; exact (EggTransition.merge_class_mono a g i j reason x y
      (EggRepresentation.forest_wf a g Hwf)). }
  split; [|exact Hclasses].
  apply (EggStructural.represents_mono a g (Egraph.merge a g i j reason)).
  - intros c n Hnode; exact Hnode.
  - exact Hclasses.
Qed.

Section Soundness.
Context {H F C : Type} (adm : EggSem.t K V C -> Prop)
  (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)).

Local Lemma congruent_join g i j n m :
  EggRepresentation.structural_wf a g -> EggRepresentation.sound a adm facts rules g ->
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.nodes_get g j = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  forall t u, EggRepresentation.represents a g i t -> EggRepresentation.represents a g j u ->
    EggEqual.rel a adm facts rules t u.
Proof.
  intros Hwf Hsound Hi Hj Hcanonical t u Ht Hu.
  destruct (EggStructural.node_witness a g n Hwf (EggRepresentation.nodes_typed a g Hwf i n Hi))
    as [e He].
  assert (Hei : EggRepresentation.represents a g i e).
  { exact (EggStructural.stored_represents a g i n i e Hi eq_refl He). }
  assert (Hej : EggRepresentation.represents a g j e).
  { apply (EggStructural.stored_represents a g j m j e Hj eq_refl).
    exact (EggStructural.node_represents_congruent a g n m e Hcanonical He). }
  eapply EggEqual.trans; [exact (Hsound i t e Ht Hei)|exact (Hsound j e u Hej Hu)].
Qed.

(** Actual congruence merging preserves old soundness using its stored finite witnesses. *)
Theorem congruent_merge_sound g i j n m reason :
  EggRepresentation.structural_wf a g -> EggRepresentation.sound a adm facts rules g ->
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.nodes_get g j = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  EggRepresentation.sound a adm facts rules (Egraph.merge a g i j reason).
Proof.
  intros Hwf Hsound Hi Hj Hcanonical.
  pose proof (EggStructural.union_sound a adm facts rules g i j
    (Egraph.merge a g i j Egraph.JGiven) Hl Hwf Hsound
    (congruent_join g i j n m Hwf Hsound Hi Hj Hcanonical)
    (given_congruent g i j n m Hi Hj Hcanonical)) as Hgiven.
  exact (EggView.sound_observation a adm facts rules
    (Egraph.merge a g i j Egraph.JGiven) (Egraph.merge a g i j reason)
    eq_refl eq_refl Hgiven).
Qed.

End Soundness.

(** The original memo observation justifies raw WF of the actual collision base. *)
Theorem base_structural {work} g i n :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g work ->
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.structural_wf a
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n))).
Proof.
  intros Hwf Hkernel Hnode.
  pose proof (EggMaintained.layout a g Hwf) as Hlayout.
  pose proof (EggStructural.node_code_injective a Hl) as Hcodes.
  rewrite (EggObservation.base_equation a g i n Hkernel Hlayout Hcodes Hnode).
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|] eqn:Hhit;
    [|exact Hwf].
  destruct (EggRepairInv.collision_witness a g n other Hkernel
    (EggRepresentation.forest_wf a g Hwf) Hcodes Hhit) as [m [Hother Hcanonical]].
  exact (congruent_merge_structural g i other n m _ Hwf Hnode Hother Hcanonical).
Qed.

(** The actual collision base extends the original grammar and partition. *)
Theorem base_extends {work} g i n :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g work ->
  EggRepresentation.nodes_get g i = Some n ->
  EggRepresentation.extends a g
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n))).
Proof.
  intros Hwf Hkernel Hnode.
  rewrite (EggObservation.base_equation a g i n Hkernel (EggMaintained.layout a g Hwf)
    (EggStructural.node_code_injective a Hl) Hnode).
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)).
  - apply merge_extends; exact Hwf.
  - split; auto.
Qed.

(** Actual parent repair preserves raw structural validity and its finite witnesses. *)
Theorem repair_node_structural g i work :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g (i :: work) ->
  EggRepresentation.structural_wf a (Egraph.repair_node a g i).
Proof.
  intros Hwf Hkernel.
  destruct (EggRepairStep.repair_node_correct a g i work Hkernel
    (EggMaintained.layout a g Hwf) (EggStructural.node_code_injective a Hl))
    as [Hnew Hlayout].
  rewrite Egraph.repair_node_equation in Hnew, Hlayout |- *.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode,
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try exact Hwf.
  cbv zeta in Hnew, Hlayout |- *.
  rewrite <- Egraph.repair_base_equation in Hnew, Hlayout |- *.
  apply (EggView.maintained_transport a
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))
    (Egraph.install (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))
      i (Egraph.canonical a g n) (Egraph.node_code a historical)
      (Egraph.node_code a (Egraph.canonical a g n)))
    (base_structural g i n Hwf Hkernel Hnode) eq_refl eq_refl eq_refl Hnew Hlayout).
Qed.

(** Actual parent repair preserves every old finite term and class equality. *)
Theorem repair_node_extends g i work :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g (i :: work) ->
  EggRepresentation.extends a g (Egraph.repair_node a g i).
Proof.
  intros Hwf Hkernel; rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode,
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|];
    try solve [split; auto].
  cbv zeta; rewrite <- Egraph.repair_base_equation.
  apply (EggStructural.extends_trans a g
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))).
  - exact (base_extends g i n Hwf Hkernel Hnode).
  - apply EggView.extends_observation; reflexivity.
Qed.

Section SoundRepair.
Context {H F C : Type} (adm : EggSem.t K V C -> Prop)
  (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)).

Local Lemma base_sound {work} g i n :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g work ->
  EggRepresentation.nodes_get g i = Some n -> EggRepresentation.sound a adm facts rules g ->
  EggRepresentation.sound a adm facts rules
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n))).
Proof.
  intros Hwf Hkernel Hnode Hsound.
  pose proof (EggStructural.node_code_injective a Hl) as Hcodes.
  rewrite (EggObservation.base_equation a g i n Hkernel (EggMaintained.layout a g Hwf)
    Hcodes Hnode).
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|] eqn:Hhit;
    [|exact Hsound].
  destruct (EggRepairInv.collision_witness a g n other Hkernel
    (EggRepresentation.forest_wf a g Hwf) Hcodes Hhit) as [m [Hother Hcanonical]].
  exact (congruent_merge_sound adm facts rules g i other n m _ Hwf Hsound Hnode Hother Hcanonical).
Qed.

(** Old soundness is preserved by the actual collision union and metadata installation. *)
Theorem repair_node_sound g i work :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv_on a g (i :: work) ->
  EggRepresentation.sound a adm facts rules g ->
  EggRepresentation.sound a adm facts rules (Egraph.repair_node a g i).
Proof.
  intros Hwf Hkernel Hsound; rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode,
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try exact Hsound.
  cbv zeta; rewrite <- Egraph.repair_base_equation.
  apply (EggView.sound_observation a adm facts rules
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))
    (Egraph.install (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))
      i (Egraph.canonical a g n) (Egraph.node_code a historical)
      (Egraph.node_code a (Egraph.canonical a g n))) eq_refl eq_refl).
  exact (base_sound g i n Hwf Hkernel Hnode Hsound).
Qed.

End SoundRepair.
End Graph.

End EggSemantic.
