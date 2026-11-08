(** * Examined scoped edge bounds

    Pending vertices retain unread actual occurrences or discovery and low-link bounds for them.
    For example, a non-tree event bounds its source by a target that is still pending.
    Builds on: GraphTarjanFrontier and the public prepared-arc laws. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphTarjan GraphTarjanState GraphTarjanBookkeeping GraphTarjanLow
  GraphTarjanFrontier.
Import List.ListNotations.

Module TarjanExamined.

(** An unread occurrence is held by an actual Search frame for its source. *)
Definition remaining {E} (frames : list (SearchRun.frame E)) u e v :=
  exists es, In (u, es) frames /\ In (e, v) es.

(** A processed admitted arc has a discovered target that bounds its pending source's low link. *)
Definition processed {E} (s : Tarjan.state) u (_e : E) v :=
  exists d, Map.get positive_encoding v (Tarjan.disc s) = Some d /\
    (In v (Tarjan.stack s) ->
      forall l, Map.get positive_encoding u (Tarjan.low s) = Some l -> (l <= d)%positive).

(** Every admitted arc of a pending vertex is either unread or has its precise processed bound. *)
Definition examined {V E} (p : Prepared.t V E) scope
    (frames : list (SearchRun.frame E)) (s : Tarjan.state) :=
  forall u e v, In u (Tarjan.stack s) -> Prepared.arc p u e v ->
    Scope.admits scope v = true -> remaining frames u e v \/ processed s u e v.

(** Empty pending storage has no examined-edge obligations. *)
Theorem initial_examined {V E} (p : Prepared.t V E) scope :
  examined p scope [] Tarjan.initial.
Proof.
  intros u e v Hfalse. contradiction.
Qed.

(** Genuine prepared arcs have valid sources and targets under readiness. *)
Theorem arc_valid {V E} (p : Prepared.t V E) u e v :
  Prepared.ready p -> Prepared.arc p u e v -> Prepared.valid_id p u /\ Prepared.valid_id p v.
Proof.
  intros Hready Harc.
  assert (Hu : Prepared.valid_id p u).
  { destruct Harc as [a [b [Ha [Hi Hrest]]]]. exists a. auto. }
  split; [exact Hu|].
  exact (proj2 (SearchInvariant.successor_arc p u e v Hready Hu
    (SearchInvariant.arc_successor p u e v Hready Harc))).
Qed.

Local Lemma valid_named {V E} (p : Prepared.t V E) v :
  Prepared.ready p -> Prepared.valid_id p v -> exists name, Prepared.name_of p v = Some name.
Proof.
  intros [_ [_ Hlaws]] [name [_ Hi]]. exists name.
  exact (Prepared.name_of_id_of p name v Hlaws Hi).
Qed.

(** Consuming one actual occurrence preserves the others and installs its proved processed bound. *)
Theorem consume {V E} (p : Prepared.t V E) scope s prefix u e v es rest :
  examined p scope (prefix ++ (u, (e, v) :: es) :: rest) s ->
  (Prepared.arc p u e v -> Scope.admits scope v = true -> processed s u e v) ->
    examined p scope (prefix ++ (u, es) :: rest) s.
Proof.
  intros Hexamined Hconsumed w a z Hw Harc Hallowed.
  destruct (Hexamined w a z Hw Harc Hallowed) as [[pending [Hframe Hedge]]|Hdone];
    [|now right].
  apply in_app_iff in Hframe. destruct Hframe as [Hprefix|[Heq|Hrest]].
  - left. exists pending. split; [apply in_or_app; now left|exact Hedge].
  - inversion Heq; subst w pending. destruct Hedge as [Hedge_eq|Hedge].
    + inversion Hedge_eq; subst a z. right. now apply Hconsumed.
    + left. exists es. split; [apply in_or_app; right; now left|exact Hedge].
  - left. exists pending. split; [apply in_or_app; right; now right|exact Hedge].
Qed.

(** Dropping a finished empty frame discards no unread edge occurrence. *)
Theorem drop_empty {V E} (p : Prepared.t V E) scope s u rest :
  examined p scope ((u, []) :: rest) s -> examined p scope rest s.
Proof.
  intros Hexamined w e v Hw Harc Hallowed.
  destruct (Hexamined w e v Hw Harc Hallowed) as [[es [[Heq|Hframe] Hedge]]|Hdone].
  - inversion Heq; subst es. contradiction.
  - left. exists es. auto.
  - now right.
Qed.

(** Lowering preserves each processed bound because it never increases an existing low link. *)
Theorem lower_examined {V E} (p : Prepared.t V E) scope frames open s v n :
  TarjanBook.bookkeeping open s -> examined p scope frames s ->
    examined p scope frames (Tarjan.lower v n s).
Proof.
  intros Hbook Hexamined. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [old|] eqn:Hold;
    [|exact Hexamined].
  intros w e z Hw Harc Hallowed.
  destruct (Hexamined w e z Hw Harc Hallowed) as [Hremaining|[d [Hd Hbound]]].
  - now left.
  - right. exists d. split; [exact Hd|]. intros Hz l Hlink. cbn [Tarjan.low] in Hlink.
    destruct (TarjanFrontier.low_set_inverse _ v old n w l
      (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)) Hold Hlink)
      as [l0 [Hlink0 Hle]].
    eapply Pos.le_trans; [exact Hle|exact (Hbound Hz l0 Hlink0)].
Qed.

(** Emission keeps processed bounds for every surviving pending source and target. *)
Theorem emit_examined {V E} (p : Prepared.t V E) scope frames s root :
  examined p scope frames s -> examined p scope frames (Tarjan.emit root s).
Proof.
  intro Hexamined.
  set (answer := Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _]. fold answer in Hsplit.
  rewrite Tarjan.emit_equation. intros w e v Hw Harc Hallowed.
  cbn [Tarjan.stack] in Hw. fold answer in Hw.
  assert (Hwold : In w (Tarjan.stack s)) by (rewrite Hsplit; apply in_or_app; now right).
  destruct (Hexamined w e v Hwold Harc Hallowed) as [Hremaining|[d [Hd Hbound]]].
  - now left.
  - right. exists d. split; [exact Hd|]. intros Hv l Hlink.
    cbn [Tarjan.stack Tarjan.low] in Hv, Hlink. fold answer in Hv, Hlink.
    pose proof (TarjanStateFacts.pop_links root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) w) as Hlinks.
    fold answer in Hlinks. rewrite Hlinks in Hlink.
    destruct (existsb (eqb positive_encoding w) (Tarjan.members answer)); [discriminate|].
    apply (Hbound); [|exact Hlink]. rewrite Hsplit. apply in_or_app. now right.
Qed.

(** A fresh child initially retains every one of its actual outgoing occurrences unread. *)
Theorem enter_examined {V E} (p : Prepared.t V E) scope frames open s v :
  Prepared.ready p -> TarjanBook.bookkeeping open s -> examined p scope frames s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
  examined p scope ((v, Prepared.succ_edges p v) :: frames) (Tarjan.enter v s).
Proof.
  intros Hready Hbook Hexamined Hfresh w e z Hw Harc Hallowed.
  pose proof (TarjanBook.canonical _ _ Hbook) as Hstorage.
  rewrite Tarjan.enter_equation in Hw |- *. cbn [Tarjan.stack Tarjan.disc Tarjan.low In] in *.
  destruct Hw as [<-|Hw].
  - left. exists (Prepared.succ_edges p v). split; [now left|].
    now apply SearchInvariant.arc_successor.
  - destruct (Hexamined w e z Hw Harc Hallowed) as [[es [Hframe Hedge]]|[d [Hd Hbound]]].
    + left. exists es. split; [now right|exact Hedge].
    + assert (Hzne : z <> v) by (intro Heq; subst z; congruence).
      assert (Hwne : w <> v) by
        (intro Heq; subst w; exact (TarjanFrontier.fresh_pending open s v Hbook Hfresh Hw)).
      right. exists d. cbn [Tarjan.disc Tarjan.stack Tarjan.low].
      rewrite (Map.get_set_other positive_encoding positive_encoding_laws) by
        (try exact (TarjanStateFacts.disc_wf s Hstorage); exact Hzne).
      split; [exact Hd|]. intros Hz l Hlink. cbn [In] in Hz.
      rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by
        (try exact (TarjanStateFacts.low_wf s Hstorage); exact Hwne).
      destruct Hz as [Heq|Hz]; [congruence|exact (Hbound Hz l Hlink)].
Qed.

(** Fresh target entry also processes the actual selected parent occurrence before its child frame. *)
Theorem enter_edge_examined {V E} (p : Prepared.t V E) scope u open s e v es rest :
  Prepared.ready p -> TarjanLow.invariant p scope (u :: open) s ->
  examined p scope ((u, (e, v) :: es) :: rest) s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
  examined p scope ((v, Prepared.succ_edges p v) :: (u, es) :: rest) (Tarjan.enter v s).
Proof.
  intros Hready HI Hexamined Hfresh.
  pose proof (TarjanLow.book _ _ _ _ HI) as Hbook.
  pose proof (TarjanBook.canonical _ _ Hbook) as Hstorage.
  assert (Hu : In u (Tarjan.stack s)) by
    exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) u (or_introl eq_refl)).
  assert (Hne : u <> v) by
    (intro Heq; subst u; exact (TarjanFrontier.fresh_pending _ s v Hbook Hfresh Hu)).
  apply (consume p scope (Tarjan.enter v s) [(v, Prepared.succ_edges p v)] u e v es rest).
  - now apply enter_examined with (open := u :: open).
  - intros _ _. exists (Tarjan.clock s).
    rewrite Tarjan.enter_equation. cbn [Tarjan.disc Tarjan.stack Tarjan.low].
    rewrite Map.get_set_same by exact (TarjanStateFacts.disc_wf s Hstorage).
    split; [reflexivity|]. intros _ l Hlink.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by
      (try exact (TarjanStateFacts.low_wf s Hstorage); exact Hne).
    destruct (TarjanLow.links _ _ _ _ HI u l Hlink) as [du [x [Hud [Hbound Hrest]]]].
    eapply Pos.le_trans; [exact Hbound|]. apply Pos.lt_le_incl.
    exact (TarjanLow.number_bound s u du (TarjanLow.numbers _ _ _ _ HI) Hud).
Qed.

(** Rejected occurrences leave no scoped-path obligation when consumed by Search. *)
Theorem skip_rejected {V E} (p : Prepared.t V E) scope s u e v es rest :
  examined p scope ((u, (e, v) :: es) :: rest) s -> Scope.admits scope v = false ->
    examined p scope ((u, es) :: rest) s.
Proof.
  intros Hexamined Hrejected. apply (consume p scope s [] u e v es rest Hexamined).
  intros _ Hallowed. congruence.
Qed.

(** An unknown target cannot be a genuine ready prepared arc and creates no processed obligation. *)
Theorem skip_unknown {V E} (p : Prepared.t V E) scope s u e v es rest :
  Prepared.ready p -> examined p scope ((u, (e, v) :: es) :: rest) s ->
  Prepared.name_of p v = None -> examined p scope ((u, es) :: rest) s.
Proof.
  intros Hready Hexamined Hunknown. apply (consume p scope s [] u e v es rest Hexamined).
  intros Harc _. destruct (valid_named p v Hready (proj2 (arc_valid p u e v Hready Harc)))
    as [name Hname]. congruence.
Qed.

Local Lemma seen_not_pending {V E} (p : Prepared.t V E) scope u open s e v es rest d :
  TarjanBook.bookkeeping (u :: open) s ->
  examined p scope ((u, (e, v) :: es) :: rest) s ->
  Map.get positive_encoding v (Tarjan.disc s) = Some d ->
  FinSet.mem positive_encoding v (Tarjan.on_stack s) = false ->
    examined p scope ((u, es) :: rest) s.
Proof.
  intros Hbook Hexamined Hdisc Hnot.
  apply (consume p scope s [] u e v es rest Hexamined). intros _ _.
  exists d. split; [exact Hdisc|]. intros Hv.
  apply (TarjanBook.pending_exact _ _ Hbook) in Hv. congruence.
Qed.

Local Lemma seen_pending {V E} (p : Prepared.t V E) scope u open s e v es rest d :
  TarjanBook.bookkeeping (u :: open) s ->
  examined p scope ((u, (e, v) :: es) :: rest) s ->
  Map.get positive_encoding v (Tarjan.disc s) = Some d ->
    examined p scope ((u, es) :: rest) (Tarjan.lower u d s).
Proof.
  intros Hbook Hexamined Hdisc.
  assert (Hu : In u (Tarjan.stack s)) by
    exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) u (or_introl eq_refl)).
  destruct (proj2 (TarjanBook.low_domain _ _ Hbook u) Hu) as [old Hold].
  pose proof (lower_examined p scope _ _ s u d Hbook Hexamined) as Hlower.
  apply (consume p scope (Tarjan.lower u d s) [] u e v es rest Hlower).
  intros _ _. exists d. rewrite Tarjan.lower_equation, Hold.
  cbn [Tarjan.disc Tarjan.low]. split; [exact Hdisc|]. intros _ l Hlink.
  rewrite Map.get_set_same in Hlink by
    exact (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)).
  inversion Hlink; subst l. apply Pos.le_min_r.
Qed.

(** A seen non-tree occurrence installs the actual source-to-target discovery bound. *)
Theorem edge_examined {V E} (p : Prepared.t V E) scope u open s e v es rest k d :
  TarjanBook.bookkeeping (u :: open) s ->
  examined p scope ((u, (e, v) :: es) :: rest) s ->
  Map.get positive_encoding v (Tarjan.disc s) = Some d -> k <> Search.Tree ->
    examined p scope ((u, es) :: rest) (Tarjan.edge u v k s).
Proof.
  intros Hbook Hexamined Hdisc Hnot. rewrite Tarjan.edge_equation.
  destruct k; [contradiction| | |].
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)) eqn:Hpending.
  all: try (rewrite Hdisc;
    exact (seen_pending p scope u open s e v es rest d Hbook Hexamined Hdisc)).
  all: exact (seen_not_pending p scope u open s e v es rest d Hbook Hexamined Hdisc Hpending).
Qed.

(** Exit first drops its actual empty frame, then retains examined bounds through emission or lowering. *)
Theorem exit_examined {V E} (p : Prepared.t V E) scope u open s rest parent :
  TarjanBook.bookkeeping (u :: open) s ->
  examined p scope ((u, []) :: rest) s ->
    examined p scope rest (Tarjan.exit u parent s).
Proof.
  intros Hbook Hexamined.
  pose proof (drop_empty p scope s u rest Hexamined) as Hclosed.
  rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding u (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding u (Tarjan.disc s)) as [d|]; try exact Hclosed.
  destruct (Pos.eqb l d); [now apply emit_examined|].
  destruct parent; [now apply lower_examined with (open := u :: open)|exact Hclosed].
Qed.

End TarjanExamined.
