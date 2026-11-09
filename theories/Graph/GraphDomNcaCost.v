(** * Numeric costs of the actual Semi-NCA finisher

    Strict numeric descent bounds each threshold walk independently of parent-map semantics.
    For example, a walk from discovery rank four visits at most four ranks.
    Builds on: GraphDomNca, GraphDomDfs and primitive map and rank-comparison costs. *)

From Stdlib Require Import List PArith NArith Arith Lia Wf_nat.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseInternCost.
From Galois.Graph Require Import GraphPrepared GraphSearchSpec GraphDomSemi GraphDomNca
  GraphDomRank GraphDomLink GraphDomDfs.
Import Cost.Notations.

Module DomNcaCost.
Local Open Scope N_scope.

Definition width v := N.pos (Pos.size v).

(** A failed parent lookup has the same query-width cost as a successful lookup. *)
Theorem get_cost {A} (m : Map.t positive A) v :
  Cost.ticks (Map.get_c positive_encoding v m) = 2 + width v.
Proof.
  rewrite Map.get_cost.
  change (1 + 1 + N.pos (Pos.size v) = 2 + width v). reflexivity.
Qed.

(** Parent insertion charges its key independently of the stored parent's numeric size. *)
Theorem set_cost {A} (m : Map.t positive A) v value :
  Cost.ticks (Map.set_c positive_encoding v value m) = 2 + width v.
Proof.
  rewrite Map.set_cost.
  change (1 + 1 + N.pos (Pos.size v) = 2 + width v). reflexivity.
Qed.

(** Rank-descent testing also bounds its charge by the current rank's width. *)
Theorem smaller_right_cost parent v :
  Cost.ticks (DomRank.smaller_c parent v) <= width v.
Proof.
  unfold DomRank.smaller_c. rewrite Cost.ticks_map, Cost.ticks_refine.
  exact (proj2 (DomRank.compare_cont_cost Eq parent v)).
Qed.

(** The walk's per-rank coefficient covers its step, comparisons and parent lookup. *)
Definition walk_k : N := 4.

(** Every raw threshold walk has a numeric bound without an output-success or map-validity premise. *)
Theorem walk_cost limit m v :
  Cost.ticks (DomNca.walk_c limit m v) <= N.pos v * (walk_k * (1 + width v)).
Proof.
  induction v as [v IH] using (well_founded_induction (well_founded_ltof _ Pos.to_nat)).
  pose proof (DomRank.compare_cost v limit) as Hthreshold.
  pose proof (get_cost m v) as Hget.
  assert (Hpositive : 0 < N.pos v) by reflexivity.
  rewrite DomNca.walk_equation. unfold DomNca.walk_body_c.
  autorewrite with galois_cost.
  destruct (Cost.value (DomRank.compare_c v limit));
    autorewrite with galois_cost.
  - unfold walk_k, width in *. nia.
  - unfold walk_k, width in *. nia.
  - fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m) as [parent|] eqn:Hparent;
      autorewrite with galois_cost.
    + pose proof (smaller_right_cost parent v) as Hcompare.
      destruct (Cost.value (DomRank.smaller_c parent v)) as [Hdecrease|Hstop];
        autorewrite with galois_cost.
      * specialize (IH parent Hdecrease).
        assert (Hlt : (parent < v)%positive) by now apply Pos2Nat.inj_lt.
        pose proof (InternCost.bits_monotone parent v (Pos.lt_le_incl _ _ Hlt)) as Hwidth.
        assert (Hrank : N.pos parent < N.pos v) by exact Hlt.
        unfold width in *. unfold walk_k in *. nia.
      * unfold walk_k, width in *. nia.
    + unfold walk_k, width in *. nia.
Qed.

(** The finite-rank walk bound retains the actual maximum rank and its actual binary width. *)
Theorem walk_numeric_cost limit m v bound :
  (v <= bound)%positive ->
  Cost.ticks (DomNca.walk_c limit m v) <= N.pos bound * (walk_k * (1 + width bound)).
Proof.
  intro Hrank. pose proof (walk_cost limit m v) as Hwalk.
  pose proof (InternCost.bits_monotone v bound Hrank) as Hwidth.
  assert (Hle : N.pos v <= N.pos bound) by exact Hrank.
  eapply N.le_trans; [exact Hwalk|].
  apply N.mul_le_mono; [exact Hle|].
  apply N.mul_le_mono; [reflexivity|].
  unfold width. lia.
Qed.

(** A forward step needs only finite actual DFS-parent ranks and no hypothesis on its result. *)
Theorem step_cost {L} (ranked : DomSemi.layout L) semis m v bound :
  (v <= bound)%positive ->
  (forall parent, Map.get positive_encoding v (DomSemi.parents ranked) = Some parent ->
    (parent <= bound)%positive) ->
  Cost.ticks (DomNca.step_c ranked semis m v) <=
    3 * (2 + width bound) + N.pos bound * (walk_k * (1 + width bound)).
Proof.
  intros Hv Hparents.
  pose proof (InternCost.bits_monotone v bound Hv) as Hwidth.
  pose proof (get_cost (DomSemi.parents ranked) v) as Hget.
  unfold DomNca.step_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding v (DomSemi.parents ranked)).
  destruct (Map.get positive_encoding v (DomSemi.parents ranked)) as [parent|] eqn:Hparent.
  - pose proof (walk_numeric_cost (DomLink.identity_value semis v) m parent bound
      (Hparents parent eq_refl)) as Hwalk.
    rewrite !Cost.ticks_bind.
    fold (DomLink.identity_value semis v).
    rewrite set_cost.
    assert (Hscore : Cost.ticks (DomLink.identity_value_c semis v) = 2 + width v).
    { unfold DomLink.identity_value_c. autorewrite with galois_cost.
      rewrite get_cost. lia. }
    unfold width in *. lia.
  - autorewrite with galois_cost. unfold width in *. nia.
Qed.

Definition finish_bound count bound :=
  count * (2 + 3 * (2 + width bound) + N.pos bound * (walk_k * (1 + width bound))).

(** Finisher accounting expands every forward step and the charged order reversal. *)
Theorem finish_cost {V E} (shared : DomSemi.semi V E) bound :
  (forall v, In v (DomSemi.reverse_order (DomSemi.ranked shared)) ->
    (v <= bound)%positive) ->
  (forall v parent, In v (DomSemi.reverse_order (DomSemi.ranked shared)) ->
    Map.get positive_encoding v (DomSemi.parents (DomSemi.ranked shared)) = Some parent ->
    (parent <= bound)%positive) ->
  Cost.ticks (DomNca.finish_c shared) <=
    finish_bound (N.of_nat (length (DomSemi.reverse_order (DomSemi.ranked shared)))) bound.
Proof.
  intros Horder Hparents. unfold DomNca.finish_c.
  rewrite Cost.ticks_bind, ticks_rev_c, value_rev_c.
  assert (Hfold : forall xs m,
    incl xs (DomSemi.reverse_order (DomSemi.ranked shared)) ->
    Cost.ticks (fold_left_c
      (DomNca.step_c (DomSemi.ranked shared) (DomSemi.semis (DomSemi.settled shared))) xs m) <=
    N.of_nat (length xs) *
      (1 + 3 * (2 + width bound) + N.pos bound * (walk_k * (1 + width bound)))).
  { intro xs. induction xs as [|v rest IH]; intros m Hincl.
    - autorewrite with galois_cost. reflexivity.
    - rewrite ticks_fold_left_c_cons.
      pose proof (step_cost (DomSemi.ranked shared) (DomSemi.semis (DomSemi.settled shared))
        m v bound (Horder v (Hincl v (or_introl eq_refl)))
        (fun parent Hget => Hparents v parent (Hincl v (or_introl eq_refl)) Hget)) as Hstep.
      specialize (IH (Cost.value (DomNca.step_c (DomSemi.ranked shared)
        (DomSemi.semis (DomSemi.settled shared)) m v))
        ltac:(intros u Hu; apply Hincl; now right)).
      cbn [length]. rewrite Nat2N.inj_succ. nia. }
  specialize (Hfold (rev (DomSemi.reverse_order (DomSemi.ranked shared))) Map.empty
    ltac:(intros v Hv; now apply in_rev)).
  rewrite length_rev in Hfold. unfold finish_bound. nia.
Qed.

(** The actual prologue discharges every finisher rank duty from readiness alone. *)
Theorem actual_finish_cost {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  let count := length (Search.preorder (DomSemi.search (DomSemi.compute p))) in
  Cost.ticks (DomNca.finish_c (DomSemi.compute p)) <=
    finish_bound (N.of_nat count) (Pos.of_succ_nat count).
Proof.
  intro Hready. cbn zeta.
  assert (Hrank : forall v, In v (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) ->
    (v <= Pos.of_succ_nat
      (length (Search.preorder (DomSemi.search (DomSemi.compute p)))))%positive).
  { intros v Hv. apply (DomDfs.settlement_member p v Hready) in Hv.
    apply Pos2Nat.inj_le. rewrite SuccNat2Pos.id_succ. lia. }
  pose proof (finish_cost (DomSemi.compute p)
    (Pos.of_succ_nat (length (Search.preorder (DomSemi.search (DomSemi.compute p))))) Hrank
    ltac:(intros v parent Hv Hparent; eapply Pos.le_trans;
      [apply Pos.lt_le_incl; exact (DomDfs.parent_decreases p v parent Hready Hparent)
      |exact (Hrank v Hv)])) as Hfinish.
  rewrite (DomDfs.settlement_order p Hready), length_rev, length_map, length_seq in Hfinish.
  exact Hfinish.
Qed.

(** The forward finisher's size counts actual discovered vertices and the fresh upper rank's width. *)
Definition actual_work {V E} (p : Prepared.t V E) :=
  let count := length (Search.preorder (DomSemi.search (DomSemi.compute p))) in
  N.of_nat count * (1 + N.of_nat count) * (1 + width (Pos.of_succ_nat count)).

(** The actual forward finisher is quadratically bounded in discovery count, including reversal. *)
Theorem actual_finish_numeric_cost {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Cost.ticks (DomNca.finish_c (DomSemi.compute p)) <= 16 * actual_work p.
Proof.
  intro Hready. pose proof (actual_finish_cost p Hready) as Hfinish.
  cbn zeta in Hfinish.
  set (count := length (Search.preorder (DomSemi.search (DomSemi.compute p)))) in *.
  assert (Hrank : N.pos (Pos.of_succ_nat count) = 1 + N.of_nat count).
  { rewrite <- (N2Nat.id (N.pos (Pos.of_succ_nat count))).
    cbn [N.to_nat]. rewrite SuccNat2Pos.id_succ, Nat2N.inj_succ. lia. }
  unfold finish_bound, walk_k in Hfinish. rewrite Hrank in Hfinish.
  unfold actual_work. fold count. nia.
Qed.

(** This big-O contract covers the actual NCA finisher and makes no whole-pipeline claim. *)
Theorem actual_finish_bigO {X V E} (p : X -> Prepared.t V E) :
  (forall x, Prepared.ready (p x)) ->
  bigO (fun x => actual_work (p x))
    (fun x => Cost.ticks (DomNca.finish_c (DomSemi.compute (p x)))).
Proof.
  intro Hready. exists 16. intro x.
  pose proof (actual_finish_numeric_cost (p x) (Hready x)). lia.
Qed.

End DomNcaCost.
