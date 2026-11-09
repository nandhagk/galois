(** * Numeric costs of the actual shared settlement

    Finite rank support is preserved through every predecessor evaluation and linked settlement step.
    For example, each actual incoming occurrence pays one rank-linear evaluator query.
    Builds on: GraphDomLinkCost and the shared ranked DFS transport contracts. *)

From Stdlib Require Import List PArith NArith Arith Lia Wf_nat.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseInternCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSemi GraphDomLink
  GraphDomRank GraphDomPath GraphDomDfs GraphDomTransport GraphDomLinkProof GraphDomLinkCost
  GraphDomCostBasis.
Import Cost.Notations.

Module DomSemiCost.
Local Open Scope N_scope.

(** Numeric state support is independent of any desired semidominator result. *)
Definition state_bounded limit st : Prop :=
  DomLinkCost.values_bounded limit (DomSemi.semis st) /\
    DomLinkCost.bounded limit (DomSemi.links st).

Definition accumulator_bounded limit (acc : DomLink.t * positive) : Prop :=
  DomLinkCost.bounded limit (fst acc) /\ (snd acc <= limit)%positive.

Definition eval_bound limit :=
  N.pos limit * (20 + 11 * key_bits positive_encoding limit).

Definition predecessor_bound limit := eval_bound limit + 4 + 2 * key_bits positive_encoding limit.

(** One actual predecessor evaluation preserves the finite state and selected score support. *)
Theorem predecessor_bounded limit settled acc source :
  DomLinkCost.values_bounded limit settled ->
  accumulator_bounded limit acc -> (source <= limit)%positive ->
  accumulator_bounded limit (Cost.value (DomSemi.predecessor_c settled acc source)).
Proof.
  intros Hsettled Hacc Hsource. destruct acc as [links best].
  destruct Hacc as [Hlinks Hbest].
  pose proof (DomLinkCost.eval_bounded limit (DomLink.identity_value_c settled) links source
    Hlinks Hsource) as Hquery.
  rewrite DomSemi.predecessor_value.
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c settled) links source))
    as [links' chosen].
  destruct Hquery as [Hlinks' Hchosen].
  assert (Hcandidate : (DomLink.identity_value settled chosen <= limit)%positive).
  { exact (DomLinkCost.identity_bounded limit settled chosen Hsettled Hchosen). }
  split; [exact Hlinks'|].
  destruct (DomLinkProof.minimum_member (fun rank => Cost.ret rank)
    best (DomLink.identity_value settled chosen)) as [Heq|Heq]; cbn [snd]; rewrite Heq; assumption.
Qed.

(** One predecessor price expands the actual evaluator, settled-score lookup and minimum selection. *)
Theorem predecessor_cost limit settled acc source :
  DomLinkCost.values_bounded limit settled ->
  accumulator_bounded limit acc -> (source <= limit)%positive ->
  Cost.ticks (DomSemi.predecessor_c settled acc source) <= predecessor_bound limit.
Proof.
  intros Hsettled Hacc Hsource. destruct acc as [links best].
  destruct Hacc as [Hlinks Hbest].
  pose proof (DomLinkCost.eval_identity_cost limit settled links source Hsettled Hlinks Hsource)
    as Heval.
  pose proof (DomLinkCost.eval_bounded limit (DomLink.identity_value_c settled) links source
    Hlinks Hsource) as Hquery.
  unfold DomSemi.predecessor_c.
  rewrite (Cost.ticks_bind (DomLink.eval_c (DomLink.identity_value_c settled) links source)).
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c settled) links source))
    as [links' chosen].
  destruct Hquery as [Hlinks' Hchosen].
  assert (Hcandidate : (DomLink.identity_value settled chosen <= limit)%positive).
  { exact (DomLinkCost.identity_bounded limit settled chosen Hsettled Hchosen). }
  pose proof (InternCost.bits_monotone chosen limit Hchosen) as Hwidth.
  change (key_bits positive_encoding chosen <= key_bits positive_encoding limit) in Hwidth.
  pose proof (DomLinkCost.minimum_cost limit (fun rank => Cost.ret rank) 0
    (key_bits positive_encoding limit) best (DomLink.identity_value settled chosen)
    ltac:(intros v Hv; split; [reflexivity|now apply InternCost.bits_monotone])
    Hbest Hcandidate) as Hminimum.
  rewrite (Cost.ticks_bind (DomLink.identity_value_c settled chosen)).
  fold (DomLink.identity_value settled chosen).
  rewrite (Cost.ticks_bind (DomLink.minimum_c (fun rank => Cost.ret rank)
    best (DomLink.identity_value settled chosen))), Cost.ticks_ret, DomLinkCost.identity_cost.
  unfold predecessor_bound, eval_bound in *. lia.
Qed.

Local Lemma predecessors_cost {L} limit settled incoming links parent :
  DomLinkCost.values_bounded limit settled -> DomLinkCost.bounded limit links ->
  (parent <= limit)%positive ->
  (forall eu : L * positive, In eu incoming -> (snd eu <= limit)%positive) ->
  let answer := fold_left_c (fun acc eu => DomSemi.predecessor_c settled acc (snd eu))
    incoming (links, parent) in
  accumulator_bounded limit (Cost.value answer) /\
    Cost.ticks answer <= N.of_nat (length incoming) * (1 + predecessor_bound limit).
Proof.
  intros Hsettled Hlinks Hparent Hsources.
  pose proof (ticks_fold_left_c_potential
    (fun acc eu => DomSemi.predecessor_c settled acc (snd eu))
    (accumulator_bounded limit) (fun _ => 0) (predecessor_bound limit) incoming (links, parent)
    ltac:(intros acc eu Hacc Heu; split;
      [apply predecessor_bounded; [exact Hsettled|exact Hacc|now apply Hsources]
      |pose proof (predecessor_cost limit settled acc (snd eu)
        Hsettled Hacc (Hsources eu Heu)); cbn beta; lia])
    ltac:(split; assumption)) as Hfold.
  assert (Hsupport : forall xs acc, incl xs incoming -> accumulator_bounded limit acc ->
    accumulator_bounded limit
      (Cost.value (fold_left_c (fun acc eu => DomSemi.predecessor_c settled acc (snd eu)) xs acc))).
  { intro xs. induction xs as [|eu rest IH]; intros acc Hincl Hacc; [exact Hacc|].
    change (accumulator_bounded limit (Cost.value (fold_left_c
      (fun acc eu => DomSemi.predecessor_c settled acc (snd eu)) rest
      (Cost.value (DomSemi.predecessor_c settled acc (snd eu)))))).
    apply IH.
    - intros ev Hev. apply Hincl. now right.
    - apply predecessor_bounded; [exact Hsettled|exact Hacc|].
      apply Hsources. apply Hincl. now left. }
  cbn beta in Hfold. split.
  - apply Hsupport; [intros eu Heu; exact Heu|now split].
  - rewrite N.add_comm. lia.
Qed.

Definition settle_bound {L} limit (ranked : DomSemi.layout L) w :=
  12 + 6 * key_bits positive_encoding limit +
    N.of_nat (length (Index.find positive_encoding w (DomSemi.predecessors ranked))) *
      (1 + predecessor_bound limit).

(** Settlement preserves the finite state and expands every inspected row occurrence. *)
Theorem settle_cost {L} limit (ranked : DomSemi.layout L) st w :
  DomLinkCost.values_bounded limit (DomSemi.parents ranked) ->
  state_bounded limit st -> (w <= limit)%positive ->
  (forall eu, In eu (Index.find positive_encoding w (DomSemi.predecessors ranked)) ->
    (snd eu <= limit)%positive) ->
  state_bounded limit (Cost.value (DomSemi.settle_c ranked st w)) /\
    Cost.ticks (DomSemi.settle_c ranked st w) <= settle_bound limit ranked w.
Proof.
  intros Hparents [Hsemis Hlinks] Hw Hsources.
  pose proof (InternCost.bits_monotone w limit Hw) as Hwidth.
  change (key_bits positive_encoding w <= key_bits positive_encoding limit) in Hwidth.
  unfold DomSemi.settle_c.
  rewrite Cost.value_bind.
  fold (Map.get positive_encoding w (DomSemi.parents ranked)).
  destruct (Map.get positive_encoding w (DomSemi.parents ranked)) as [parent|] eqn:Hparent.
  - assert (Hparent_bound : (parent <= limit)%positive) by exact (proj2 Hparents w parent Hparent).
    pose proof (predecessors_cost limit (DomSemi.semis st)
      (Index.find positive_encoding w (DomSemi.predecessors ranked))
      (DomSemi.links st) parent Hsemis Hlinks Hparent_bound Hsources) as Hfold.
    cbn zeta in Hfold.
    split.
    + rewrite Cost.value_bind.
      fold (Index.find positive_encoding w (DomSemi.predecessors ranked)).
      rewrite Cost.value_bind.
      destruct (Cost.value (fold_left_c
        (fun acc eu => DomSemi.predecessor_c (DomSemi.semis st) acc (snd eu))
        (Index.find positive_encoding w (DomSemi.predecessors ranked)) (DomSemi.links st, parent)))
        as [links' best].
      destruct Hfold as [[Hlinks' Hbest] Hcost].
      rewrite !Cost.value_bind. fold (Map.set positive_encoding w best (DomSemi.semis st)).
      change (DomLinkCost.values_bounded limit (Map.set positive_encoding w best (DomSemi.semis st)) /\
        DomLinkCost.bounded limit (Cost.value (DomLink.link_c links' w parent))).
      split.
      * exact (DomLinkCost.values_set limit (DomSemi.semis st) w best Hsemis Hbest).
      * exact (DomLinkCost.link_bounded limit links' w parent Hlinks' Hw Hparent_bound).
    + rewrite (Cost.ticks_bind (Map.get_c positive_encoding w (DomSemi.parents ranked))).
      cbn beta. fold (Map.get positive_encoding w (DomSemi.parents ranked)). rewrite Hparent.
      rewrite (Cost.ticks_bind (Index.find_c positive_encoding w (DomSemi.predecessors ranked))).
      fold (Index.find positive_encoding w (DomSemi.predecessors ranked)).
      rewrite (Cost.ticks_bind (fold_left_c
        (fun acc eu => DomSemi.predecessor_c (DomSemi.semis st) acc (snd eu))
        (Index.find positive_encoding w (DomSemi.predecessors ranked)) (DomSemi.links st, parent))).
      destruct (Cost.value (fold_left_c
        (fun acc eu => DomSemi.predecessor_c (DomSemi.semis st) acc (snd eu))
        (Index.find positive_encoding w (DomSemi.predecessors ranked)) (DomSemi.links st, parent)))
        as [links' best].
      rewrite (Cost.ticks_bind (Map.set_c positive_encoding w best (DomSemi.semis st))),
        (Cost.ticks_bind (DomLink.link_c links' w parent)), Cost.ticks_ret,
        DomLinkCost.link_cost, Index.find_cost, !DomCostBasis.get_cost, DomCostBasis.set_cost.
      destruct Hfold as [Hsupport Hcost]. unfold settle_bound. lia.
  - split; [now split|].
    rewrite (Cost.ticks_bind (Map.get_c positive_encoding w (DomSemi.parents ranked))).
    cbn beta. fold (Map.get positive_encoding w (DomSemi.parents ranked)). rewrite Hparent.
    rewrite Cost.ticks_ret, DomCostBasis.get_cost.
    unfold settle_bound. lia.
Qed.

(** This occurrence inventory counts the actual indexed incoming rows inspected by the supplied pass. *)
Definition incoming_mass {L} (ranked : DomSemi.layout L) xs :=
  fold_right (fun w rest =>
    N.of_nat (length (Index.find positive_encoding w (DomSemi.predecessors ranked))) + rest) 0 xs.

Definition settlement_bound {L} limit (ranked : DomSemi.layout L) xs :=
  N.of_nat (length xs) * (13 + 6 * key_bits positive_encoding limit) +
    incoming_mass ranked xs * (1 + predecessor_bound limit).

(** The actual settlement fold preserves support and pays every vertex and incoming occurrence. *)
Theorem settlement_cost {L} limit (ranked : DomSemi.layout L) xs :
  DomLinkCost.values_bounded limit (DomSemi.parents ranked) ->
  (forall w, In w xs -> (w <= limit)%positive) ->
  (forall w eu, In w xs ->
    In eu (Index.find positive_encoding w (DomSemi.predecessors ranked)) ->
    (snd eu <= limit)%positive) ->
  forall st, state_bounded limit st ->
  state_bounded limit (Cost.value (fold_left_c (DomSemi.settle_c ranked) xs st)) /\
    Cost.ticks (fold_left_c (DomSemi.settle_c ranked) xs st) <= settlement_bound limit ranked xs.
Proof.
  intro Hparents. induction xs as [|w rest IH]; intros Hranks Hsources st Hst.
  - split; [exact Hst|]. rewrite ticks_fold_left_c_nil. unfold settlement_bound, incoming_mass.
    cbn [length fold_right]. lia.
  - destruct (settle_cost limit ranked st w Hparents Hst (Hranks w (or_introl eq_refl))
      (fun eu Heu => Hsources w eu (or_introl eq_refl) Heu)) as [Hst' Hstep].
    specialize (IH ltac:(intros v Hv; apply Hranks; now right)
      ltac:(intros v eu Hv Heu; apply (Hsources v eu); [now right|exact Heu])
      (Cost.value (DomSemi.settle_c ranked st w)) Hst').
    destruct IH as [Hsupport Hcost]. split.
    + change (state_bounded limit (Cost.value (fold_left_c (DomSemi.settle_c ranked) rest
        (Cost.value (DomSemi.settle_c ranked st w))))). exact Hsupport.
    + rewrite ticks_fold_left_c_cons.
      unfold settlement_bound, incoming_mass in *.
      cbn [length fold_right]. rewrite Nat2N.inj_succ. unfold settle_bound in Hstep. nia.
Qed.

Definition rank_limit {V E} (p : Prepared.t V E) :=
  Pos.of_succ_nat (length (Search.preorder (DomSemi.search (DomSemi.compute p)))).

(** Every actual settlement rank fits the same discovery-count frontier used by numeric recursion bounds. *)
Theorem actual_rank_bound {V E} (p : Prepared.t V E) v :
  Prepared.ready p -> In v (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) ->
  (v <= rank_limit p)%positive.
Proof.
  intros Hready Hv. apply (DomDfs.settlement_member p v Hready) in Hv.
  apply Pos2Nat.inj_le. unfold rank_limit. rewrite SuccNat2Pos.id_succ. lia.
Qed.

(** Readiness establishes finite canonical DFS-parent values for the actual shared ranked layout. *)
Theorem actual_parents_bounded {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  DomLinkCost.values_bounded (rank_limit p) (DomSemi.parents (DomSemi.ranked (DomSemi.compute p))).
Proof.
  intro Hready. split; [apply DomDfs.parents_wf|].
  intros v parent Hget. apply (actual_rank_bound p parent Hready).
  apply (DomDfs.vertex_member p parent Hready).
  exact (proj2 (DomDfs.parent_vertices p v parent Hready Hget)).
Qed.

(** Every retained incoming occurrence carries a source rank within that same actual finite frontier. *)
Theorem actual_sources_bounded {V E} (p : Prepared.t V E) w eu :
  Prepared.ready p -> In w (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) ->
  In eu (Index.find positive_encoding w (DomSemi.predecessors (DomSemi.ranked (DomSemi.compute p)))) ->
  (snd eu <= rank_limit p)%positive.
Proof.
  intros Hready Hw Heu. destruct eu as [e source]. cbn [snd].
  apply (actual_rank_bound p source Hready).
  apply (DomDfs.vertex_member p source Hready).
  apply (DomDfs.vertex_member p w Hready) in Hw. destruct Hw as [target Htarget].
  apply (proj1 (DomTransport.ranked_arc_spec p target w e source Hready Htarget)) in Heu.
  destruct Heu as [raw [Harc Hrank]]. now exists raw.
Qed.

(** Readiness alone establishes finite state and numeric cost for the same actual shared settlement. *)
Theorem actual_settlement_cost {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  state_bounded (rank_limit p) (DomSemi.settled (DomSemi.compute p)) /\
  Cost.ticks (fold_left_c (DomSemi.settle_c (DomSemi.ranked (DomSemi.compute p)))
    (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))) DomSemi.initial) <=
    settlement_bound (rank_limit p) (DomSemi.ranked (DomSemi.compute p))
      (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p))).
Proof.
  intro Hready.
  pose proof (settlement_cost (rank_limit p) (DomSemi.ranked (DomSemi.compute p))
    (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)))
    (actual_parents_bounded p Hready)
    (fun w Hw => actual_rank_bound p w Hready Hw)
    (fun w eu Hw Heu => actual_sources_bounded p w eu Hready Hw Heu) DomSemi.initial
    ltac:(split;
      [split; [apply Map.wf_empty|intros v a Hget;
        change (Map.get positive_encoding v Map.empty = Some a) in Hget;
        rewrite Map.get_empty in Hget; discriminate]
      |apply DomLinkCost.empty_bounded])) as Hsettlement.
  exact Hsettlement.
Qed.

End DomSemiCost.
