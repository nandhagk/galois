(** * Preservation of scoped low-link witnesses

    Entry, lowering and component emission preserve the pending-path and closed-link obligations.
    For example, a finished child propagates a witness reached through its actual parent edge.
    Builds on: GraphTarjanLow and the exact stack-prefix update laws. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphTarjan
  GraphTarjanState GraphTarjanBookkeeping GraphTarjanLow.
Import List.ListNotations.

Module TarjanLowStep.

Local Lemma fresh_pending open s v :
  TarjanBook.bookkeeping open s -> Map.get positive_encoding v (Tarjan.disc s) = None ->
    ~ In v (Tarjan.stack s).
Proof.
  intros Hbook Hfresh Hin.
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook v) ltac:(apply in_or_app; now left))
    as [n Hn]. congruence.
Qed.

(** Entry adds only its admitted valid vertex to the discovered domain. *)
Theorem enter_domain {V E} (p : Prepared.t V E) scope open s v :
  TarjanBook.bookkeeping open s -> TarjanLow.discovered_domain p scope s ->
  Prepared.valid_id p v -> Scope.admits scope v = true ->
    TarjanLow.discovered_domain p scope (Tarjan.enter v s).
Proof.
  intros Hbook Hdomain Hv Ha w n Hget.
  rewrite Tarjan.enter_equation in Hget. cbn [Tarjan.disc] in Hget.
  rewrite Map.get_set in Hget by
    exact (TarjanStateFacts.disc_wf s (TarjanBook.canonical _ _ Hbook)).
  destruct (eqb_spec positive_encoding positive_encoding_laws w v) as [->|Hne].
  - auto.
  - exact (Hdomain w n Hget).
Qed.

(** Entry creates a reflexive low-link witness and preserves every older pending witness. *)
Theorem enter_links {V E} (p : Prepared.t V E) scope open s v :
  TarjanBook.bookkeeping open s -> TarjanLow.low_witness p scope s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
  Prepared.valid_id p v -> Scope.admits scope v = true ->
    TarjanLow.low_witness p scope (Tarjan.enter v s).
Proof.
  intros Hbook Hlow Hfresh Hv Ha w l Hlink.
  pose proof (TarjanBook.canonical _ _ Hbook) as Hstorage.
  rewrite Tarjan.enter_equation in Hlink |- *. cbn [Tarjan.low Tarjan.disc Tarjan.stack] in *.
  destruct (Pos.eq_dec w v) as [->|Hne].
  - rewrite Map.get_set_same in Hlink by exact (TarjanStateFacts.low_wf s Hstorage).
    inversion Hlink; subst l. exists (Tarjan.clock s), v.
    rewrite Map.get_set_same by exact (TarjanStateFacts.disc_wf s Hstorage).
    split; [reflexivity|]. split; [apply Pos.le_refl|].
    split; [now left|]. split; [reflexivity|]. exists []. now apply Search.scoped_nil.
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by
      (try exact (TarjanStateFacts.low_wf s Hstorage); exact Hne).
    destruct (Hlow w l Hlink) as [d [x [Hwd [Hbound [Hx [Hxd Hpath]]]]]].
    assert (Hxne : x <> v) by (intro Heq; subst x; exact (fresh_pending open s v Hbook Hfresh Hx)).
    exists d, x. rewrite !Map.get_set_other by
      (first [exact positive_encoding_laws|exact (TarjanStateFacts.disc_wf s Hstorage)|
        exact Hne|exact Hxne]).
    split; [exact Hwd|]. split; [exact Hbound|].
    split; [now right|]. split; assumption.
Qed.

(** Entry keeps every previously closed pending link strict below its discovery number. *)
Theorem enter_closed open s v :
  TarjanBook.bookkeeping open s -> TarjanLow.closed_low open s ->
    TarjanLow.closed_low (v :: open) (Tarjan.enter v s).
Proof.
  intros Hbook Hclosed w l d Hin Hnot Hlink Hdisc.
  rewrite Tarjan.enter_equation in Hin, Hlink, Hdisc.
  cbn [Tarjan.stack Tarjan.low Tarjan.disc In] in Hin, Hnot, Hlink, Hdisc.
  assert (Hne : w <> v) by (intro Heq; subst w; apply Hnot; now left).
  destruct Hin as [Heq|Hin]; [congruence|].
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by
    (try exact (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)); exact Hne).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hdisc by
    (try exact (TarjanStateFacts.disc_wf s (TarjanBook.canonical _ _ Hbook)); exact Hne).
  apply (Hclosed w l d); try assumption. intro Hopen. apply Hnot. now right.
Qed.

(** Entry extends pending paths when each old pending vertex reaches the newly entered child. *)
Theorem enter_paths {V E} (p : Prepared.t V E) scope open s v :
  TarjanBook.bookkeeping open s -> TarjanLow.numbered s -> TarjanLow.pending_paths p scope s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
  Prepared.valid_id p v -> Scope.admits scope v = true ->
  (forall w, In w (Tarjan.stack s) -> TarjanLow.reaches p scope w v) ->
    TarjanLow.pending_paths p scope (Tarjan.enter v s).
Proof.
  intros Hbook Hnumbers Hpaths Hfresh Hv Ha Hreach u w a b Hu Hw Hua Hwb Hab.
  rewrite Tarjan.enter_equation in Hu, Hw, Hua, Hwb. cbn [Tarjan.stack Tarjan.disc In] in *.
  pose proof (TarjanStateFacts.disc_wf s (TarjanBook.canonical _ _ Hbook)) as Hwf.
  destruct Hu as [<-|Hu], Hw as [<-|Hw].
  - exists []. now apply Search.scoped_nil.
  - rewrite Map.get_set_same in Hua by exact Hwf. inversion Hua; subst a.
    assert (Hne : w <> v) by (intro Heq; subst w; exact (fresh_pending open s v Hbook Hfresh Hw)).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwb by assumption.
    pose proof (TarjanLow.number_bound s w b Hnumbers Hwb) as Hclock. exfalso.
    exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hab Hclock)).
  - apply Hreach, Hu.
  - assert (Hune : u <> v) by (intro Heq; subst u; exact (fresh_pending open s v Hbook Hfresh Hu)).
    assert (Hwne : w <> v) by (intro Heq; subst w; exact (fresh_pending open s v Hbook Hfresh Hw)).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hua by assumption.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwb by assumption.
    exact (Hpaths u w a b Hu Hw Hua Hwb Hab).
Qed.

(** A fresh entry preserves the complete low-link invariant using only local incoming reachability. *)
Theorem enter_invariant {V E} (p : Prepared.t V E) scope open s v :
  TarjanLow.invariant p scope open s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
  Prepared.valid_id p v -> Scope.admits scope v = true ->
  (forall w, In w (Tarjan.stack s) -> TarjanLow.reaches p scope w v) ->
    TarjanLow.invariant p scope (v :: open) (Tarjan.enter v s).
Proof.
  intros [Hbook Hnumbers Hdomain Hlinks Hclosed Hpaths] Hfresh Hv Ha Hreach. constructor.
  - now apply TarjanBook.enter_bookkeeping.
  - now apply TarjanLow.enter_numbered.
  - now apply enter_domain with (open := open).
  - now apply enter_links with (open := open).
  - now apply enter_closed.
  - now apply enter_paths with (open := open).
Qed.

(** Lowering retains an old low-link witness or replaces it by the supplied reachable witness. *)
Theorem lower_links {V E} (p : Prepared.t V E) scope open s v n :
  TarjanBook.bookkeeping open s -> TarjanLow.low_witness p scope s ->
  (exists x, In x (Tarjan.stack s) /\ Map.get positive_encoding x (Tarjan.disc s) = Some n /\
    TarjanLow.reaches p scope v x) ->
    TarjanLow.low_witness p scope (Tarjan.lower v n s).
Proof.
  intros Hbook Hlow [x [Hx [Hxn Hreach]]]. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [old|] eqn:Hold; [|exact Hlow].
  intros w l Hlink. cbn [Tarjan.low] in Hlink.
  pose proof (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)) as Hwf.
  destruct (Pos.eq_dec w v) as [->|Hne].
  - rewrite Map.get_set_same in Hlink by exact Hwf. inversion Hlink; subst l.
    destruct (Hlow v old Hold) as [d [y [Hvd [Hbound [Hy [Hyd Hypath]]]]]].
    destruct (Pos.leb old n) eqn:Htest.
    + apply Pos.leb_le in Htest. rewrite Pos.min_l by exact Htest. exists d, y.
      repeat split; assumption.
    + apply Pos.leb_gt in Htest.
      assert (Hle : (n <= old)%positive) by now apply Pos.lt_le_incl.
      rewrite Pos.min_r by exact Hle. exists d, x. split; [exact Hvd|].
      split; [eapply Pos.le_trans; eassumption|]. auto.
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by assumption.
    exact (Hlow w l Hlink).
Qed.

(** Lowering an open vertex leaves strict links at every closed pending vertex unchanged. *)
Theorem lower_closed open s v n :
  TarjanBook.bookkeeping open s -> TarjanLow.closed_low open s -> In v open ->
    TarjanLow.closed_low open (Tarjan.lower v n s).
Proof.
  intros Hbook Hclosed Hv. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); [|exact Hclosed].
  intros w l d Hw Hnot Hlink Hdisc. cbn [Tarjan.stack Tarjan.low Tarjan.disc] in *.
  assert (Hne : w <> v) by (intro Heq; subst w; contradiction).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hlink by
    (try exact (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)); exact Hne).
  exact (Hclosed w l d Hw Hnot Hlink Hdisc).
Qed.

(** Lowering an open vertex preserves all low-link fields from one explicit reachable witness. *)
Theorem lower_invariant {V E} (p : Prepared.t V E) scope open s v n :
  TarjanLow.invariant p scope open s -> In v open ->
  (exists x, In x (Tarjan.stack s) /\ Map.get positive_encoding x (Tarjan.disc s) = Some n /\
    TarjanLow.reaches p scope v x) ->
    TarjanLow.invariant p scope open (Tarjan.lower v n s).
Proof.
  intros HI Hv Hreach. constructor.
  - apply TarjanBook.lower_bookkeeping, (TarjanLow.book _ _ _ _ HI).
  - apply TarjanLow.lower_numbered, (TarjanLow.numbers _ _ _ _ HI).
  - rewrite Tarjan.lower_equation. destruct (Map.get positive_encoding v (Tarjan.low s));
      exact (TarjanLow.domain _ _ _ _ HI).
  - apply lower_links with (open := open); [exact (TarjanLow.book _ _ _ _ HI)|
      exact (TarjanLow.links _ _ _ _ HI)|exact Hreach].
  - apply lower_closed; [exact (TarjanLow.book _ _ _ _ HI)|
      exact (TarjanLow.closed _ _ _ _ HI)|exact Hv].
  - rewrite Tarjan.lower_equation. destruct (Map.get positive_encoding v (Tarjan.low s));
      exact (TarjanLow.paths _ _ _ _ HI).
Qed.

(** A surviving low-link entry belongs to the untouched suffix and retains its old value. *)
Theorem pop_survivor root i xs lows active own w l :
  In w xs ->
  Map.get positive_encoding w (Tarjan.links (Tarjan.pop root i xs lows active own)) = Some l ->
  In w (Tarjan.tail (Tarjan.pop root i xs lows active own)) /\
    Map.get positive_encoding w lows = Some l.
Proof.
  intro Hin. destruct (TarjanStateFacts.pop_split root i xs lows active own) as [Hsplit _].
  rewrite TarjanStateFacts.pop_links.
  destruct (existsb (eqb positive_encoding w)
    (Tarjan.members (Tarjan.pop root i xs lows active own))) eqn:Hmem; [discriminate|].
  intro Hget. split; [|exact Hget].
  rewrite Hsplit, in_app_iff in Hin. destruct Hin as [Hmember|Htail]; [|exact Htail].
  apply TarjanStateFacts.member_test in Hmember. congruence.
Qed.

(** Surviving low links cannot point into the newer emitted prefix. *)
Theorem emit_links {V E} (p : Prepared.t V E) scope open s root :
  TarjanBook.bookkeeping open s -> TarjanLow.numbered s -> TarjanLow.low_witness p scope s ->
    TarjanLow.low_witness p scope (Tarjan.emit root s).
Proof.
  intros Hbook Hnumbers Hlow.
  set (answer := Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  fold answer in Hsplit. rewrite Tarjan.emit_equation.
  intros w l Hlink. cbn [Tarjan.low] in Hlink. fold answer in Hlink.
  pose proof (TarjanStateFacts.pop_links root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) w) as Hlinks.
  fold answer in Hlinks. rewrite Hlinks in Hlink.
  destruct (existsb (eqb positive_encoding w) (Tarjan.members answer)) eqn:Hmem;
    [discriminate|].
  destruct (Hlow w l Hlink) as [d [x [Hwd [Hbound [Hx [Hxd Hpath]]]]]].
  assert (Hw : In w (Tarjan.tail answer)).
  { assert (Hpending : In w (Tarjan.stack s)).
    { apply (TarjanBook.low_domain _ _ Hbook). now exists l. }
    assert (Hget : Map.get positive_encoding w (Tarjan.links answer) = Some l).
    { rewrite Hlinks. exact Hlink. }
    exact (proj1 (pop_survivor root (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) w l Hpending Hget)). }
  exists d, x. cbn [Tarjan.disc Tarjan.stack]. fold answer.
  split; [exact Hwd|]. split; [exact Hbound|]. split; [|auto].
  rewrite Hsplit, in_app_iff in Hx. destruct Hx as [Hmember|Htail]; [|exact Htail].
  exfalso.
  assert (Hlt : (d < l)%positive).
  { apply (TarjanLow.pending_numbers s x w l d Hnumbers); [|exact Hxd|exact Hwd].
    rewrite Hsplit. now apply TarjanLow.before_cross. }
  exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hlt Hbound)).
Qed.

(** Emission preserves all older pending paths because it only removes a stack prefix. *)
Theorem emit_paths {V E} (p : Prepared.t V E) scope s root :
  TarjanLow.pending_paths p scope s -> TarjanLow.pending_paths p scope (Tarjan.emit root s).
Proof.
  intro Hpaths.
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  rewrite Tarjan.emit_equation. intros u v a b Hu Hv Hua Hvb Hbound.
  cbn [Tarjan.stack Tarjan.disc] in *.
  apply (Hpaths u v a b); try assumption; rewrite Hsplit; apply in_or_app; now right.
Qed.

(** Removing one non-root open vertex makes its already strict low link a closed obligation. *)
Theorem close_pending v open s :
  TarjanLow.closed_low (v :: open) s ->
  (forall l d, Map.get positive_encoding v (Tarjan.low s) = Some l ->
    Map.get positive_encoding v (Tarjan.disc s) = Some d -> (l < d)%positive) ->
    TarjanLow.closed_low open s.
Proof.
  intros Hclosed Hv w l d Hw Hnot Hlink Hdisc.
  destruct (Pos.eq_dec w v) as [->|Hne]; [exact (Hv l d Hlink Hdisc)|].
  apply (Hclosed w l d); try assumption.
  intros [Heq|Hopen]; [congruence|contradiction].
Qed.

(** Emitting the top root removes it from pending and keeps every surviving closed link strict. *)
Theorem emit_closed v open s :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.closed_low (v :: open) s ->
    TarjanLow.closed_low open (Tarjan.emit v s).
Proof.
  intros Hbook Hclosed.
  set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit Hroot].
  fold answer in Hsplit, Hroot.
  assert (Hv : In v (Tarjan.members answer)).
  { apply Hroot, (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook)). now left. }
  rewrite Tarjan.emit_equation. intros w l d Hw Hnot Hlink Hdisc.
  cbn [Tarjan.stack Tarjan.low Tarjan.disc] in *. fold answer in Hw, Hlink.
  assert (Hwpending : In w (Tarjan.stack s)) by (rewrite Hsplit; apply in_or_app; now right).
  destruct (pop_survivor v (Tarjan.next_component s) (Tarjan.stack s) (Tarjan.low s)
    (Tarjan.on_stack s) (Tarjan.owners s) w l Hwpending Hlink) as [_ Hold].
  assert (Hne : v <> w).
  { intro Heq. subst w. pose proof (TarjanBook.distinct _ _ Hbook) as Hdistinct.
    rewrite Hsplit, <- app_assoc in Hdistinct.
    apply (TarjanBook.nodup_disjoint _ _ Hdistinct v Hv). apply in_or_app. now left. }
  apply (Hclosed w l d); try assumption.
  intros [Heq|Hopen]; [congruence|contradiction].
Qed.

(** Emitting a top root preserves the complete low-link invariant on the remaining open vertices. *)
Theorem emit_invariant {V E} (p : Prepared.t V E) scope v open s :
  TarjanLow.invariant p scope (v :: open) s ->
    TarjanLow.invariant p scope open (Tarjan.emit v s).
Proof.
  intro HI. constructor.
  - apply TarjanBook.emit_bookkeeping, (TarjanLow.book _ _ _ _ HI).
  - apply TarjanLow.emit_numbered, (TarjanLow.numbers _ _ _ _ HI).
  - rewrite Tarjan.emit_equation. exact (TarjanLow.domain _ _ _ _ HI).
  - apply emit_links with (open := v :: open); [exact (TarjanLow.book _ _ _ _ HI)|
      exact (TarjanLow.numbers _ _ _ _ HI)|exact (TarjanLow.links _ _ _ _ HI)].
  - apply emit_closed; [exact (TarjanLow.book _ _ _ _ HI)|exact (TarjanLow.closed _ _ _ _ HI)].
  - apply emit_paths, (TarjanLow.paths _ _ _ _ HI).
Qed.

(** Exiting a non-root preserves low-link semantics through its actual parent-to-child path. *)
Theorem exit_invariant {V E} (p : Prepared.t V E) scope v open s parent :
  TarjanLow.invariant p scope (v :: open) s ->
  (match parent with
  | None => True
  | Some u => In u open /\ TarjanLow.reaches p scope u v
  end) ->
    TarjanLow.invariant p scope open (Tarjan.exit v parent s).
Proof.
  intros HI Hparent.
  pose proof (TarjanLow.book _ _ _ _ HI) as Hbook.
  assert (Hv : In v (Tarjan.stack s)).
  { apply (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook)). now left. }
  destruct (proj2 (TarjanBook.low_domain _ _ Hbook v) Hv) as [l Hvl].
  destruct (TarjanLow.links _ _ _ _ HI v l Hvl)
    as [d [x [Hvd [Hbound [Hx [Hxd Hpath]]]]]].
  rewrite Tarjan.exit_equation, Hvl, Hvd.
  destruct (Pos.eqb l d) eqn:Heq; [now apply emit_invariant|].
  apply Pos.eqb_neq in Heq.
  assert (Hstrict : (l < d)%positive) by (apply Pos.lt_eq_cases in Hbound; tauto).
  assert (Hclosed : TarjanLow.closed_low open s).
  { apply close_pending with (v := v); [exact (TarjanLow.closed _ _ _ _ HI)|].
    intros a b Ha Hb. rewrite Hvl in Ha. rewrite Hvd in Hb.
    inversion Ha; inversion Hb; subst. exact Hstrict. }
  assert (Hpending : TarjanLow.invariant p scope open s).
  { constructor; try apply HI.
    - now apply TarjanBook.drop_bookkeeping with (v := v).
    - exact Hclosed. }
  destruct parent as [u|]; [|exact Hpending].
  destruct Hparent as [Hu Huv]. apply lower_invariant; [exact Hpending|exact Hu|].
  exists x. split; [exact Hx|]. split; [exact Hxd|].
  eapply TarjanLow.reaches_trans; eassumption.
Qed.

(** A non-tree event lowers only the current open source using its pending target's discovery rank. *)
Theorem edge_invariant {V E} (p : Prepared.t V E) scope u open s v k :
  TarjanLow.invariant p scope (u :: open) s ->
  TarjanLow.reaches p scope u v ->
    TarjanLow.invariant p scope (u :: open) (Tarjan.edge u v k s).
Proof.
  intros HI Hreach. rewrite Tarjan.edge_equation. destruct k; try exact HI.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)) eqn:Hpending; try exact HI.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|] eqn:Hdisc; try exact HI.
  all: apply lower_invariant; [exact HI|now left|].
  all: exists v; split; [apply (TarjanBook.pending_exact _ _ (TarjanLow.book _ _ _ _ HI));
    exact Hpending|auto].
Qed.

End TarjanLowStep.
