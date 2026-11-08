(** * Dirty-work accounting through actual repair transitions

    Every additional dirty entry is paid by a newly recorded distinct-class merge.
    For example, a parent collision can enqueue at most the one losing root of its new edge.
    Builds on: EgraphGraph, EgraphCoreIndex and EgraphRebuild. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph EgraphCoreIndex EgraphRebuild.
Import List.ListNotations.

Module EggWork.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** New pending classes never outnumber the actual distinct-class merges recorded as edges. *)
Definition queue_credit (g h : Egraph.t K Sort V) :=
  length (Egraph.dirty h) + length (Egraph.edges g) <=
    length (Egraph.dirty g) + length (Egraph.edges h).

Local Lemma merge_queue_credit g c d why :
  queue_credit g (Egraph.merge a g c d why).
Proof.
  unfold queue_credit, Egraph.dirty, Egraph.edges.
  rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d)); [lia|].
  rewrite Egraph.linked_kernel_equation; cbn [Egraph.pending Egraph.reasons].
  fold (Egraph.edges g).
  destruct (EggParent.get (Egraph.parents g)
    (if Pos.eqb
      (fst (UnionFind.find Egraph.id_encoding c
        (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))) (Egraph.find a g c)
      then Egraph.find a g d else Egraph.find a g c)).
  - cbn [length]; lia.
  - pose proof (EggPending.push_length
      (if Pos.eqb
        (fst (UnionFind.find Egraph.id_encoding c
          (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))) (Egraph.find a g c)
        then Egraph.find a g d else Egraph.find a g c)
      (Egraph.pending (Egraph.private g))) as Hpush.
    cbn [length]; lia.
Qed.

Local Lemma base_queue_credit g i key :
  queue_credit g (Egraph.repair_base a g i key).
Proof.
  rewrite Egraph.repair_base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|];
    [|unfold queue_credit; lia].
  rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g i) as [si|], (Egraph.sort_of a g other) as [so|];
    try solve [unfold queue_credit; lia].
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) si)
    (encode (EggAlg.sort_enc K Sort V a) so)).
  - apply merge_queue_credit.
  - unfold queue_credit; lia.
  - unfold queue_credit; lia.
Qed.

(** One actual parent callback adds pending work only when it adds a justification edge. *)
Theorem repair_node_queue_credit g i :
  queue_credit g (Egraph.repair_node a g i).
Proof.
  rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|],
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [old|];
    try solve [unfold queue_credit; lia].
  cbv zeta; rewrite <- Egraph.repair_base_equation.
  change (queue_credit g
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))).
  apply base_queue_credit.
Qed.

Local Lemma fold_queue_credit parents g visits :
  queue_credit g (fst (fold_left (fun state i =>
    (Egraph.repair_node a (fst state) i, N.succ (snd state))) parents (g, visits))).
Proof.
  revert g visits; induction parents as [|i parents IH]; intros g visits.
  - unfold queue_credit; reflexivity.
  - pose proof (repair_node_queue_credit g i) as Hhead.
    pose proof (IH (Egraph.repair_node a g i) (N.succ visits)) as Htail.
    cbn [fold_left fst snd]; unfold queue_credit in *; lia.
Qed.

(** Dequeuing spends one pending class before the actual batch creates any new merge edges. *)
Theorem dirty_step_queue_credit g visits h total :
  Cost.value (Egraph.dirty_step_c a (g, visits)) = inl (h, total) ->
  length (Egraph.dirty h) + length (Egraph.edges g) + 1 <=
    length (Egraph.dirty g) + length (Egraph.edges h).
Proof.
  rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|] eqn:Hpop;
    [|discriminate].
  cbv zeta; fold (Egraph.with_queue g queue).
  intro Heq; injection Heq as Hgraph Hcount.
  pose proof (fold_queue_credit (EggParent.get (Egraph.parents g) loser)
    (Egraph.with_queue g queue) 0%N) as Hcredit.
  change (EggParent.get (Egraph.parents g) loser) with
    (EggParent.get (Egraph.parents (Egraph.with_queue g queue)) loser) in Hcredit.
  rewrite <- EggRebuild.repair_equation in Hcredit.
  rewrite Hgraph in Hcredit.
  unfold queue_credit in Hcredit.
  change (length (Egraph.dirty h) + length (Egraph.edges g) <=
    length (EggPending.entries queue) + length (Egraph.edges h)) in Hcredit.
  pose proof (EggPending.pop_entries _ _ _ Hpop) as Hentries.
  change (length (Egraph.dirty h) + length (Egraph.edges g) + 1 <=
    length (EggPending.entries (Egraph.pending (Egraph.private g))) + length (Egraph.edges h)).
  rewrite Hentries; cbn [length]; lia.
Qed.

End Graph.

End EggWork.
