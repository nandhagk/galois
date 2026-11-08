(** * Strict progress and sufficient fuel for dirty rebuilding

    Missing class pairs pay for new dirty entries and each dequeue spends one remaining obligation.
    For example, a repair union decreases the partition measure before its loser is enqueued.
    Builds on: EgraphCoreBatch, EgraphIndex and public Cost iteration laws. *)

From Stdlib Require Import List PArith NArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphIndex EgraphCoreIndex EgraphCoreInvariant
  EgraphCoreTransition EgraphCoreObservation EgraphCoreRepair EgraphCoreRepairStep
  EgraphCoreBatch EgraphRebuild.
Import List.ListNotations.
Local Open Scope nat_scope.

Module EggProgress.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** The finite proof universe contains every positive key below the fixed allocation bound. *)
Definition ids limit := map Pos.of_succ_nat (seq 0 (Pos.to_nat limit)).

(** The proof universe has the natural size of its binary bound. *)
Theorem ids_length limit : length (ids limit) = Pos.to_nat limit.
Proof.
  unfold ids; rewrite length_map, length_seq; reflexivity.
Qed.

(** Every strictly bounded positive identifier belongs to the proof universe. *)
Theorem ids_complete limit key :
  (key < limit)%positive -> In key (ids limit).
Proof.
  intro Hbound; unfold ids; apply in_map_iff.
  exists (Nat.pred (Pos.to_nat key)); split.
  - apply Pos2Nat.inj; rewrite SuccNat2Pos.id_succ.
    pose proof (Pos2Nat.is_pos key); lia.
  - apply in_seq; apply Pos2Nat.inj_lt in Hbound.
    pose proof (Pos2Nat.is_pos key); lia.
Qed.

(** Missing pairs plus pending classes is a proof-side potential, never a runtime traversal. *)
Definition potential limit (g : Egraph.t K Sort V) :=
  EggIndex.missing (Egraph.find a g) (ids limit) + length (Egraph.dirty g).

Local Lemma missing_mono (old new : positive -> positive) universe :
  (forall c d, old c = old d -> new c = new d) ->
  EggIndex.missing new universe <= EggIndex.missing old universe.
Proof.
  intro Hclasses; unfold EggIndex.missing.
  generalize (EggIndex.pairs universe) as pairs; intro pairs.
  induction pairs as [|[c d] pairs IH]; cbn [filter fst snd].
  - reflexivity.
  - destruct (Pos.eqb (old c) (old d)) eqn:Hold,
      (Pos.eqb (new c) (new d)) eqn:Hnew; cbn [negb length] in *; try lia.
    apply Pos.eqb_eq in Hold; pose proof (Hclasses c d Hold) as Hsame.
    rewrite Hsame, Pos.eqb_refl in Hnew; discriminate.
Qed.

Local Lemma merge_queue_bound g c d reason :
  length (Egraph.dirty (Egraph.merge a g c d reason)) <= S (length (Egraph.dirty g)).
Proof.
  unfold Egraph.dirty at 1; rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d));
    [exact (Nat.le_succ_diag_r (length (Egraph.dirty g)))|].
  rewrite Egraph.linked_kernel_equation; cbn [Egraph.pending].
  destruct (EggParent.get (Egraph.parents g)
    (if Pos.eqb
      (fst (UnionFind.find Egraph.id_encoding c
        (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))) (Egraph.find a g c)
     then Egraph.find a g d else Egraph.find a g c));
    [exact (Nat.le_succ_diag_r (length (Egraph.dirty g)))|].
  apply EggPending.push_length.
Qed.

Local Lemma merge_queue_same g c d reason :
  Egraph.find a g c = Egraph.find a g d ->
  Egraph.dirty (Egraph.merge a g c d reason) = Egraph.dirty g.
Proof.
  intro Hsame; unfold Egraph.dirty at 1; rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta; rewrite Hsame, Pos.eqb_refl; reflexivity.
Qed.

Local Lemma merge_missing_decreases limit g c d reason :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < limit)%positive ->
  (Egraph.find a g d < limit)%positive ->
  Egraph.find a g c <> Egraph.find a g d ->
  EggIndex.missing (Egraph.find a (Egraph.merge a g c d reason)) (ids limit) <
    EggIndex.missing (Egraph.find a g) (ids limit).
Proof.
  intros Hforest Hc Hd Hdistinct.
  set (rc := Egraph.find a g c); set (rd := Egraph.find a g d).
  assert (Hrc : Egraph.find a g rc = rc).
  { apply UnionFind.find_rep_canonical; [exact positive_encoding_laws|exact Hforest]. }
  assert (Hrd : Egraph.find a g rd = rd).
  { apply UnionFind.find_rep_canonical; [exact positive_encoding_laws|exact Hforest]. }
  apply (EggIndex.missing_decreases _ _ (ids limit) rc rd).
  - apply ids_complete; exact Hc.
  - apply ids_complete; exact Hd.
  - rewrite Hrc, Hrd; exact Hdistinct.
  - pose proof (EggTransition.merge_class_mono a g c d reason rc c Hforest Hrc) as Hleft.
    pose proof (EggTransition.merge_class_mono a g c d reason rd d Hforest Hrd) as Hright.
    pose proof (EggTransition.merge_same a g c d reason Hforest) as Hsame.
    congruence.
  - intros x y; exact (EggTransition.merge_class_mono a g c d reason x y Hforest).
Qed.

(** A rank-selected union pays for its at-most-one new dirty class by decreasing missing pairs. *)
Theorem merge_progress limit g c d reason :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < limit)%positive ->
  (Egraph.find a g d < limit)%positive ->
  potential limit (Egraph.merge a g c d reason) <= potential limit g.
Proof.
  intros Hforest Hc Hd.
  pose proof (missing_mono (Egraph.find a g) (Egraph.find a (Egraph.merge a g c d reason))
    (ids limit) (fun x y => EggTransition.merge_class_mono a g c d reason x y Hforest))
    as Hmono.
  unfold potential; destruct (Pos.eq_dec (Egraph.find a g c) (Egraph.find a g d))
    as [Hsame|Hdistinct].
  - rewrite (merge_queue_same g c d reason Hsame); lia.
  - pose proof (merge_missing_decreases limit g c d reason Hforest Hc Hd Hdistinct) as Hdrop.
    pose proof (merge_queue_bound g c d reason) as Hqueue; lia.
Qed.

(** Signature installation changes neither the partition nor the scheduling potential. *)
Theorem install_progress limit g i current oldkey key :
  potential limit (Egraph.install g i current oldkey key) = potential limit g.
Proof.
  rewrite Egraph.install_equation; reflexivity.
Qed.

Section Repair.
Context (Hcodes : forall first second,
  Egraph.node_code a first = Egraph.node_code a second -> first = second).

Local Lemma base_progress limit g i n work :
  Egraph.kernel_inv_on a g work -> EggTransition.layout a g ->
  Egraph.next g = limit ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  potential limit (Egraph.repair_base a g i
    (Egraph.node_code a (Egraph.canonical a g n))) <= potential limit g.
Proof.
  intros Hinv Hlayout Hlimit Hnode.
  rewrite (EggObservation.base_equation a g i n Hinv Hlayout Hcodes Hnode).
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|] eqn:Hhit;
    [|reflexivity].
  destruct (EggObservation.collision_roots a g i n Hinv Hlayout Hcodes Hnode other Hhit)
    as [Hi Hother].
  apply merge_progress; [exact (EggTransition.forest_wf a g Hlayout)| |];
    rewrite <- Hlimit; assumption.
Qed.

(** One actual parent repair does not increase the fixed-universe partition-and-queue potential. *)
Theorem repair_node_progress limit g i work :
  Egraph.kernel_inv_on a g (i :: work) -> EggTransition.layout a g ->
  Egraph.next g = limit ->
  potential limit (Egraph.repair_node a g i) <= potential limit g.
Proof.
  intros Hinv Hlayout Hlimit; rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode,
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try reflexivity.
  cbv zeta; rewrite <- Egraph.repair_base_equation, install_progress.
  exact (base_progress limit g i n (i :: work) Hinv Hlayout Hlimit Hnode).
Qed.

Local Lemma fold_progress limit parents g visits :
  Egraph.kernel_inv_on a g parents -> EggTransition.layout a g ->
  Egraph.next g = limit ->
  potential limit (fst (fold_left (fun state i =>
    (Egraph.repair_node a (fst state) i, N.succ (snd state))) parents (g, visits))) <=
    potential limit g.
Proof.
  revert g visits; induction parents as [|i parents IH]; intros g visits Hinv Hlayout Hlimit.
  - reflexivity.
  - destruct (EggRepairStep.repair_node_correct a g i parents Hinv Hlayout Hcodes)
      as [Hnext Hnext_layout].
    pose proof (repair_node_progress limit g i parents Hinv Hlayout Hlimit) as Hhead.
    assert (Hnext_limit : Egraph.next (Egraph.repair_node a g i) = limit).
    { rewrite EggRepairStep.repair_node_next; exact Hlimit. }
    pose proof (IH (Egraph.repair_node a g i) (N.succ visits) Hnext Hnext_layout Hnext_limit)
      as Htail.
    cbn [fold_left fst snd]; lia.
Qed.

Local Lemma pop_progress limit g loser queue :
  EggPending.pop (Egraph.pending (Egraph.private g)) = Some (loser, queue) ->
  S (potential limit (Egraph.with_queue g queue)) = potential limit g.
Proof.
  intro Hpop; unfold potential.
  change (S (EggIndex.missing (Egraph.find a g) (ids limit) +
    length (EggPending.entries queue)) =
    EggIndex.missing (Egraph.find a g) (ids limit) +
    length (EggPending.entries (Egraph.pending (Egraph.private g)))).
  rewrite (EggPending.pop_entries _ _ _ Hpop); cbn [length]; lia.
Qed.

(** Every continuing dirty callback strictly decreases the actual loop's proof potential. *)
Theorem dirty_step_progress limit g visits :
  Egraph.kernel_inv a g -> EggTransition.layout a g -> Egraph.next g = limit ->
  match Cost.value (Egraph.dirty_step_c a (g, visits)) with
  | inl (h, _) => potential limit h < potential limit g
  | inr _ => True
  end.
Proof.
  intros Hinv Hlayout Hlimit; rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|] eqn:Hpop;
    [|exact I].
  cbv zeta; fold (Egraph.with_queue g queue).
  pose proof (EggRepairInv.pop_kernel_inv a g loser queue Hinv Hpop) as Hactive.
  pose proof (EggTransition.queue_layout a g queue Hlayout) as Hpopped.
  pose proof (fold_progress limit
    (EggParent.get (Egraph.parents (Egraph.with_queue g queue)) loser)
    (Egraph.with_queue g queue) 0%N Hactive Hpopped Hlimit) as Hrepair.
  rewrite <- (EggRebuild.repair_equation a (Egraph.with_queue g queue) loser) in Hrepair.
  pose proof (pop_progress limit g loser queue Hpop) as Hdrop.
  destruct (EggRebuild.repair a (Egraph.with_queue g queue) loser) as [h count];
    cbn [fst snd] in Hrepair |- *; lia.
Qed.

End Repair.

(** Duplicate-free dirty scheduling is bounded by the finite identifier proof universe. *)
Theorem dirty_bound limit g :
  Egraph.kernel_inv a g -> Egraph.next g = limit ->
  length (Egraph.dirty g) <= Pos.to_nat limit.
Proof.
  intros Hinv Hlimit; rewrite <- ids_length.
  apply NoDup_incl_length.
  - exact (EggPending.entries_nodup _ (Egraph.pending_wf a g Hinv)).
  - intros key Hin; apply ids_complete; rewrite <- Hlimit.
    exact (Egraph.pending_allocated a g Hinv key Hin).
Qed.

(** The charged binary fuel exceeds the initial potential without enumerating runtime graph data. *)
Theorem fuel_sufficient g :
  Egraph.kernel_inv a g ->
  potential (Egraph.next g) g < Pos.to_nat (Egraph.rebuild_fuel g).
Proof.
  intro Hinv.
  pose proof (EggIndex.missing_bound (Egraph.find a g) (ids (Egraph.next g))) as Hmissing.
  pose proof (dirty_bound (Egraph.next g) g Hinv eq_refl) as Hdirty.
  unfold potential; rewrite ids_length in Hmissing.
  rewrite Egraph.rebuild_fuel_equation, Pos2Nat.inj_succ, Pos2Nat.inj_add, Pos2Nat.inj_mul; lia.
Qed.

(** The actual counted dirty iterator stops with maintained data and an empty queue. *)
Theorem iterate_stops g :
  (forall first second, Egraph.node_code a first = Egraph.node_code a second -> first = second) ->
  Egraph.kernel_inv a g -> EggTransition.layout a g ->
  exists h visits,
    Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0%N)) =
      inr (h, visits) /\
    Egraph.kernel_inv a h /\ EggTransition.layout a h /\
    Egraph.nodes h = Egraph.nodes g /\ Egraph.next h = Egraph.next g /\ Egraph.dirty h = [].
Proof.
  intros Hcodes Hinv Hlayout.
  set (I := EggRepairBatch.execution_inv a g).
  set (measure := fun state : Egraph.t K Sort V * N =>
    potential (Egraph.next g) (fst state)).
  assert (Hinitial : I (g, 0%N)).
  { unfold I, EggRepairBatch.execution_inv; cbn [fst].
    split; [exact Hinv|]; split; [exact Hlayout|]; split; reflexivity. }
  assert (Hstep : forall state, I state ->
    match Cost.value (Egraph.dirty_step_c a state) with
    | inl final => I final /\ measure final < measure state
    | inr final => I final /\ Egraph.dirty (fst final) = []
    end).
  { intros [h visits] HI.
    pose proof (EggRepairBatch.step_execution_inv a Hcodes g h visits HI) as Hpreserved.
    destruct HI as [Hh [Hl [Hnodes Hnext]]]; cbn [fst] in Hh, Hl, Hnext.
    pose proof (dirty_step_progress Hcodes (Egraph.next g) h visits Hh Hl Hnext) as Hprogress.
    destruct (Cost.value (Egraph.dirty_step_c a (h, visits))) as [[j count]|[j count]].
    - split; [exact Hpreserved|exact Hprogress].
    - exact Hpreserved. }
  destruct (EggIndex.iterate_stops (Egraph.dirty_step_c a) I
    (fun state => I state /\ Egraph.dirty (fst state) = [])
    measure (Egraph.rebuild_fuel g) (g, 0%N) Hstep Hinitial (fuel_sufficient g Hinv))
    as [[h visits] [Hrun [Hfinal Hempty]]].
  exists h, visits; split; [exact Hrun|].
  destruct Hfinal as [Hh [Hl [Hnodes Hnext]]].
  split; [exact Hh|]; split; [exact Hl|]; split; [exact Hnodes|]; split; assumption.
Qed.

End Graph.

End EggProgress.
