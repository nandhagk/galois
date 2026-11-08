(** * Actual Tarjan partition and owner guarantees

    Complete root traces cover the scoped reachable region without duplicate component members.
    For example, every reached vertex has its actual one-based owner after the pending stack drains.
    Builds on: GraphTarjanTrace and the public Search exactness theorem. *)

From Stdlib Require Import List PArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphSccSpec GraphTarjan GraphTarjanState GraphTarjanBookkeeping GraphTarjanLow
  GraphTarjanTrace.
Import List.ListNotations.

Module TarjanPartition.

(** Reversing the component list changes no flattened membership. *)
Theorem concat_rev_members {A} (cs : list (list A)) x :
  In x (concat (rev cs)) <-> In x (concat cs).
Proof.
  rewrite !in_concat. split; intros [c [Hc Hx]]; exists c; split; [|exact Hx| |exact Hx].
  - exact (proj2 (in_rev cs c) Hc).
  - exact (proj1 (in_rev cs c) Hc).
Qed.

(** Reversing component order permutes the flattened members. *)
Theorem concat_rev_permutation {A} (cs : list (list A)) :
  Permutation (concat cs) (concat (rev cs)).
Proof.
  induction cs as [|c rest IH]; [constructor|].
  cbn [concat rev]. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
  eapply Permutation_trans; [apply Permutation_app_head, IH|apply Permutation_app_comm].
Qed.

(** Each actual output component is nonempty. *)
Theorem components_nonempty {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  forall c, In c (Scc.components (Tarjan.compute p scope roots)) -> c <> [].
Proof.
  intro Hready. destruct (TarjanTrace.actual_invariant p scope roots Hready) as [final [_ HI]].
  intros c Hc. rewrite Tarjan.compute_equation, Tarjan.result_equation in Hc.
  cbn [Scc.components] in Hc. apply (proj2 (in_rev _ _)) in Hc.
  exact (TarjanBook.components_nonempty _
    (TarjanBook.output_indexed _ _ (TarjanLow.book _ _ _ _ (TarjanTrace.low _ _ _ _ _ HI)))
    c Hc).
Qed.

(** The actual emitted partition has no repeated member within or between components. *)
Theorem partition_unique {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> NoDup (concat (Scc.components (Tarjan.compute p scope roots))).
Proof.
  intro Hready. destruct (TarjanTrace.actual_invariant p scope roots Hready) as [final [_ HI]].
  rewrite Tarjan.compute_equation, Tarjan.result_equation. cbn [Scc.components].
  eapply Permutation_NoDup; [apply concat_rev_permutation|].
  exact (proj2 (TarjanBook.nodup_parts _ _
    (TarjanBook.distinct _ _ (TarjanLow.book _ _ _ _ (TarjanTrace.low _ _ _ _ _ HI))))).
Qed.

(** Actual owner lookup is exactly the one-based position of its containing output component. *)
Theorem owners_exact {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  (Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i <->
    exists c, nth_error (Scc.components (Tarjan.compute p scope roots))
      (Nat.pred (Pos.to_nat i)) = Some c /\ In v c).
Proof.
  intro Hready. destruct (TarjanTrace.actual_invariant p scope roots Hready) as [final [_ HI]].
  rewrite Tarjan.compute_equation, Tarjan.result_equation. cbn [Scc.comp_of Scc.components].
  exact (TarjanBook.owner_index _
    (TarjanBook.output_indexed _ _ (TarjanLow.book _ _ _ _ (TarjanTrace.low _ _ _ _ _ HI))) v i).
Qed.

(** The actual partition covers precisely the admitted reachable region for arbitrary roots. *)
Theorem partition_complete {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p ->
  (In v (concat (Scc.components (Tarjan.compute p scope roots))) <->
    Search.scoped_reachable p scope roots v).
Proof.
  intro Hready. split; [now apply TarjanStateFacts.components_reachable|].
  intro Hreachable.
  pose proof (SearchExact.run_exact p Tarjan.visitor scope roots Tarjan.initial Hready) as Hsearch.
  apply (proj2 (Search.pre_complete _ _ _ _ Hsearch v)) in Hreachable.
  apply In_nth_error in Hreachable. destruct Hreachable as [n Hnth].
  assert (Hnumber : Map.get positive_encoding v
    (Tarjan.disc (snd (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))) =
      Some (Pos.of_succ_nat n)).
  { apply (TarjanStateFacts.discovery_index p scope roots v (Pos.of_succ_nat n) Hready).
    rewrite SuccNat2Pos.id_succ. exact Hnth. }
  destruct (TarjanTrace.actual_invariant p scope roots Hready) as [final [_ HI]].
  rewrite Tarjan.compute_equation, Tarjan.result_equation. cbn [Scc.components].
  apply concat_rev_members.
  pose proof (TarjanBook.disc_domain _ _ (TarjanLow.book _ _ _ _
    (TarjanTrace.low _ _ _ _ _ HI)) v) as Hdomain.
  pose proof (proj1 Hdomain (ex_intro _ (Pos.of_succ_nat n) Hnumber)) as Hin.
  rewrite (TarjanTrace.actual_stack_empty p scope roots Hready) in Hin. exact Hin.
Qed.

(** Every scoped reachable vertex has an actual owner rather than a default component index. *)
Theorem visited_has_component {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> Search.scoped_reachable p scope roots v ->
  exists i, Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i.
Proof.
  intros Hready Hreachable. apply (proj2 (partition_complete p scope roots v Hready)) in Hreachable.
  apply in_concat in Hreachable. destruct Hreachable as [c [Hc Hv]].
  apply In_nth_error in Hc. destruct Hc as [n Hnth].
  exists (Pos.of_succ_nat n). apply (owners_exact p scope roots v (Pos.of_succ_nat n) Hready).
  rewrite SuccNat2Pos.id_succ. exists c. auto.
Qed.

(** Members of each actual output component are mutually scoped reachable. *)
Theorem components_mutual {V E} (p : Prepared.t V E) scope roots c u v :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
  In u c -> In v c -> TarjanLow.reaches p scope u v /\ TarjanLow.reaches p scope v u.
Proof.
  intros Hready Hc Hu Hv.
  destruct (TarjanTrace.actual_invariant p scope roots Hready) as [final [_ HI]].
  rewrite Tarjan.compute_equation, Tarjan.result_equation in Hc. cbn [Scc.components] in Hc.
  apply (proj2 (in_rev _ _)) in Hc.
  exact (TarjanTrace.output _ _ _ _ _ HI c Hc u v Hu Hv).
Qed.

Local Lemma concat_member_nodup {A} (cs : list (list A)) c :
  NoDup (concat cs) -> In c cs -> NoDup c.
Proof.
  intros Hnodup Hc. apply in_split in Hc. destruct Hc as [prefix [rest ->]].
  rewrite concat_app in Hnodup. cbn [concat] in Hnodup.
  exact (proj1 (TarjanBook.nodup_parts _ _
    (proj2 (TarjanBook.nodup_parts _ _ Hnodup)))).
Qed.

(** Each actual output component is individually duplicate-free. *)
Theorem component_nodup {V E} (p : Prepared.t V E) scope roots c :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) -> NoDup c.
Proof.
  intros Hready Hc.
  exact (concat_member_nodup (Scc.components (Tarjan.compute p scope roots)) c
    (partition_unique p scope roots Hready) Hc).
Qed.

End TarjanPartition.
