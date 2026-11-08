(** * Closed emitted components and owner ranks

    An emitted component's admitted successors are in itself or earlier emitted components.
    For example, an arc into an older pending suffix contradicts the root's final low link.
    Builds on: GraphTarjanFrontier and GraphTarjanExamined. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch GraphTarjan
  GraphTarjanState GraphTarjanBookkeeping GraphTarjanLow GraphTarjanFrontier GraphTarjanExamined.
Import List.ListNotations.

Module TarjanClosed.

(** No popped member retains an unread occurrence below the actual empty top search frame. *)
Theorem popped_finished {E} v (rest : list (SearchRun.frame E)) s w e z :
  TarjanBook.bookkeeping (v :: map fst rest) s ->
  In w (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
    ~ TarjanExamined.remaining ((v, []) :: rest) w e z.
Proof.
  intros Hbook Hw [es [[Heq|Hframe] Hedge]].
  - inversion Heq; subst es. contradiction.
  - set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
    fold answer in Hw.
    destruct (TarjanFrontier.pop_cut v (map fst rest) s Hbook)
      as [prefix [Hstack [Hmembers Hopen]]]. fold answer in Hopen.
    assert (Htail : In w (Tarjan.tail answer)).
    { apply (TarjanBook.stack_member _ _ Hopen). apply in_map_iff.
      exists (w, es). auto. }
    destruct (TarjanStateFacts.pop_split v (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
    fold answer in Hsplit.
    pose proof (proj1 (TarjanBook.nodup_parts _ _ (TarjanBook.distinct _ _ Hbook))) as Hnodup.
    rewrite Hsplit in Hnodup.
    exact (TarjanBook.nodup_disjoint _ _ Hnodup w Hw Htail).
Qed.

(** An emitted root's admitted successors belong to its actual popped prefix or older output. *)
Theorem emission_closed {V E} (p : Prepared.t V E) scope v rest s d :
  TarjanLow.invariant p scope (v :: map fst rest) s ->
  TarjanFrontier.frontier (v :: map fst rest) s ->
  TarjanExamined.examined p scope ((v, []) :: rest) s ->
  Map.get positive_encoding v (Tarjan.disc s) = Some d ->
  Map.get positive_encoding v (Tarjan.low s) = Some d ->
  forall w e z,
  In w (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
  Prepared.arc p w e z -> Scope.admits scope z = true ->
  In z (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) \/
    In z (concat (Tarjan.emitted_rev s)).
Proof.
  intros HI Hfrontier Hexamined Hvd Hvl w e z Hw Harc Hallowed.
  pose proof (TarjanLow.book _ _ _ _ HI) as Hbook.
  pose proof (TarjanLow.numbers _ _ _ _ HI) as Hnumbers.
  set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  fold answer in Hw |- *.
  destruct (TarjanStateFacts.pop_split v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit Hroot].
  fold answer in Hsplit, Hroot.
  assert (Hwpending : In w (Tarjan.stack s)) by (rewrite Hsplit; apply in_or_app; now left).
  destruct (Hexamined w e z Hwpending Harc Hallowed) as [Hremaining|[dt [Htarget Hbound]]].
  - exfalso. exact (popped_finished v rest s w e z Hbook Hw Hremaining).
  - pose proof (proj1 (TarjanBook.disc_domain _ _ Hbook z) (ex_intro _ dt Htarget)) as Hz.
    apply in_app_iff in Hz. destruct Hz as [Hpending|Hblack]; [|now right].
    rewrite Hsplit, in_app_iff in Hpending. destruct Hpending as [Hmember|Htail]; [now left|].
    exfalso.
    destruct (proj2 (TarjanBook.low_domain _ _ Hbook w) Hwpending) as [lw Hwl].
    destruct (TarjanLow.links _ _ _ _ HI w lw Hwl) as [dw [x [Hwd Hrest]]].
    assert (Hvw : (d <= dw)%positive) by
      exact (TarjanLow.popped_number v (map fst rest) s w d dw Hbook Hnumbers Hw Hvd Hwd).
    assert (Hlowbound : (d <= lw)%positive) by
      exact (TarjanFrontier.top_bound v (map fst rest) s w d dw d lw
        Hbook Hnumbers Hfrontier Hwpending Hvd Hwd Hvl Hwl Hvw).
    assert (Hzpending : In z (Tarjan.stack s)) by (rewrite Hsplit; apply in_or_app; now right).
    specialize (Hbound Hzpending lw Hwl).
    assert (Hstrict : (dt < d)%positive).
    { apply (TarjanLow.pending_numbers s v z d dt Hnumbers); [|exact Hvd|exact Htarget].
      rewrite Hsplit. apply TarjanLow.before_cross; [|exact Htail].
      apply Hroot, (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook)). now left. }
    exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hstrict
      (Pos.le_trans _ _ _ Hlowbound Hbound))).
Qed.

(** Every admitted arc from an owned vertex reaches an actual owner with no greater index. *)
Definition output_rank {V E} (p : Prepared.t V E) scope (s : Tarjan.state) :=
  forall u e v i, Map.get positive_encoding u (Tarjan.owners s) = Some i ->
    Prepared.arc p u e v -> Scope.admits scope v = true ->
    exists j, Map.get positive_encoding v (Tarjan.owners s) = Some j /\ (j <= i)%positive.

(** Initial empty owner storage has no emitted-edge rank obligations. *)
Theorem initial_rank {V E} (p : Prepared.t V E) scope : output_rank p scope Tarjan.initial.
Proof.
  intros u e v i Hfalse.
  change (Map.get positive_encoding u Map.empty = Some i) in Hfalse.
  rewrite Map.get_empty in Hfalse. discriminate.
Qed.

(** Emitting a prefix preserves every previously assigned owner. *)
Theorem emit_old_owner open s root x i :
  TarjanBook.bookkeeping open s -> Map.get positive_encoding x (Tarjan.owners s) = Some i ->
    Map.get positive_encoding x (Tarjan.owners (Tarjan.emit root s)) = Some i.
Proof.
  intros Hbook Howner.
  pose proof (proj1 (TarjanBook.owner_location s x i (TarjanBook.output_indexed _ _ Hbook) Howner))
    as Hblack.
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  rewrite Tarjan.emit_equation. cbn [Tarjan.owners].
  rewrite TarjanStateFacts.pop_owners by
    exact (TarjanStateFacts.owners_wf s (TarjanBook.canonical _ _ Hbook)).
  destruct (existsb (eqb positive_encoding x)
    (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)))) eqn:Hmem; [|exact Howner].
  apply TarjanStateFacts.member_test in Hmem. exfalso.
  apply (TarjanBook.nodup_disjoint _ _ (TarjanBook.distinct _ _ Hbook) x); [|exact Hblack].
  rewrite Hsplit. apply in_or_app. now left.
Qed.

(** Each actual member of the new prefix receives precisely the next chronological owner. *)
Theorem emit_member_owner open s root x :
  TarjanBook.bookkeeping open s ->
  In x (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
  Map.get positive_encoding x (Tarjan.owners (Tarjan.emit root s)) =
    Some (Tarjan.next_component s).
Proof.
  intros Hbook Hx. rewrite Tarjan.emit_equation. cbn [Tarjan.owners].
  rewrite TarjanStateFacts.pop_owners by
    exact (TarjanStateFacts.owners_wf s (TarjanBook.canonical _ _ Hbook)).
  rewrite (proj2 (TarjanStateFacts.member_test _ _) Hx). reflexivity.
Qed.

(** Local emitted-edge closure extends the actual owner-rank invariant through component emission. *)
Theorem emit_rank {V E} (p : Prepared.t V E) scope open s root :
  TarjanBook.bookkeeping open s -> output_rank p scope s ->
  (forall u e v,
    In u (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
    Prepared.arc p u e v -> Scope.admits scope v = true ->
    In v (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) \/
      In v (concat (Tarjan.emitted_rev s))) ->
    output_rank p scope (Tarjan.emit root s).
Proof.
  intros Hbook Hrank Hclosed u e v i Howner Harc Hallowed.
  rewrite Tarjan.emit_equation in Howner. cbn [Tarjan.owners] in Howner.
  rewrite TarjanStateFacts.pop_owners in Howner by
    exact (TarjanStateFacts.owners_wf s (TarjanBook.canonical _ _ Hbook)).
  destruct (existsb (eqb positive_encoding u)
    (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)))) eqn:Hmem.
  - inversion Howner; subst i. apply TarjanStateFacts.member_test in Hmem.
    destruct (Hclosed u e v Hmem Harc Hallowed) as [Htarget|Htarget].
    + exists (Tarjan.next_component s). split; [|apply Pos.le_refl].
      exact (emit_member_owner open s root v Hbook Htarget).
    + destruct (TarjanBook.member_owner s v (TarjanBook.output_indexed _ _ Hbook) Htarget)
        as [j Hj].
      exists j. split; [exact (emit_old_owner open s root v j Hbook Hj)|].
      apply Pos.lt_le_incl.
      exact (proj2 (TarjanBook.owner_location s v j (TarjanBook.output_indexed _ _ Hbook) Hj)).
  - destruct (Hrank u e v i Howner Harc Hallowed) as [j [Hj Hbound]].
    exists j. split; [exact (emit_old_owner open s root v j Hbook Hj)|exact Hbound].
Qed.

(** Entry changes no existing component owner or emitted-edge rank. *)
Theorem enter_rank {V E} (p : Prepared.t V E) scope s v :
  output_rank p scope s -> output_rank p scope (Tarjan.enter v s).
Proof.
  intro Hrank. rewrite Tarjan.enter_equation. exact Hrank.
Qed.

(** Lowering changes no component owner or emitted-edge rank. *)
Theorem lower_rank {V E} (p : Prepared.t V E) scope s v n :
  output_rank p scope s -> output_rank p scope (Tarjan.lower v n s).
Proof.
  intro Hrank. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); exact Hrank.
Qed.

(** Edge callbacks change no component owner or emitted-edge rank. *)
Theorem edge_rank {V E} (p : Prepared.t V E) scope s u v k :
  output_rank p scope s -> output_rank p scope (Tarjan.edge u v k s).
Proof.
  intro Hrank. rewrite Tarjan.edge_equation. destruct k; try exact Hrank.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hrank.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hrank.
  all: now apply lower_rank.
Qed.

(** Actual root exit preserves emitted owner ranks using its proved frontier and examined edges. *)
Theorem exit_rank {V E} (p : Prepared.t V E) scope v rest s parent :
  TarjanLow.invariant p scope (v :: map fst rest) s ->
  TarjanFrontier.frontier (v :: map fst rest) s ->
  TarjanExamined.examined p scope ((v, []) :: rest) s ->
  output_rank p scope s -> output_rank p scope (Tarjan.exit v parent s).
Proof.
  intros HI Hfrontier Hexamined Hrank. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|] eqn:Hvl;
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|] eqn:Hvd; try exact Hrank.
  destruct (Pos.eqb l d) eqn:Heq.
  - apply Pos.eqb_eq in Heq; subst l.
    apply emit_rank with (open := v :: map fst rest);
      [exact (TarjanLow.book _ _ _ _ HI)|exact Hrank|].
    exact (emission_closed p scope v rest s d HI Hfrontier Hexamined Hvd Hvl).
  - destruct parent; [now apply lower_rank|exact Hrank].
Qed.

End TarjanClosed.
