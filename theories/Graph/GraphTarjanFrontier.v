(** * Open low-link frontier

    Open vertices account for low links of newer pending vertices until child exit propagation.
    For example, closing a non-root child transfers its frontier witness to the actual parent.
    Builds on: GraphTarjanBookkeeping, GraphTarjanLow and exact pop-update laws. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphTarjan GraphTarjanState GraphTarjanBookkeeping GraphTarjanLow.
Import List.ListNotations.

Module TarjanFrontier.

(** A newer pending low link is bounded by this open vertex or by a newer open witness. *)
Definition frontier open (s : Tarjan.state) :=
  forall a w da dw la lw, In a open -> In w (Tarjan.stack s) ->
    Map.get positive_encoding a (Tarjan.disc s) = Some da ->
    Map.get positive_encoding w (Tarjan.disc s) = Some dw ->
    Map.get positive_encoding a (Tarjan.low s) = Some la ->
    Map.get positive_encoding w (Tarjan.low s) = Some lw -> (da <= dw)%positive ->
    (la <= lw)%positive \/
    exists b db lb, In b open /\ (da < db)%positive /\ (db <= dw)%positive /\
      Map.get positive_encoding b (Tarjan.disc s) = Some db /\
      Map.get positive_encoding b (Tarjan.low s) = Some lb /\ (lb <= lw)%positive.

(** The empty open list has no frontier obligations. *)
Theorem initial_frontier : frontier [] Tarjan.initial.
Proof.
  intros a w da dw la lw Hfalse. contradiction.
Qed.

(** At the top open vertex no newer open witness can replace the direct low-link bound. *)
Theorem top_bound v open s w dv dw lv lw :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.numbered s -> frontier (v :: open) s ->
  In w (Tarjan.stack s) ->
  Map.get positive_encoding v (Tarjan.disc s) = Some dv ->
  Map.get positive_encoding w (Tarjan.disc s) = Some dw ->
  Map.get positive_encoding v (Tarjan.low s) = Some lv ->
  Map.get positive_encoding w (Tarjan.low s) = Some lw -> (dv <= dw)%positive ->
    (lv <= lw)%positive.
Proof.
  intros Hbook Hnumbers Hfrontier Hw Hvd Hwd Hvl Hwl Hbound.
  destruct (Hfrontier v w dv dw lv lw (or_introl eq_refl) Hw Hvd Hwd Hvl Hwl Hbound)
    as [Hle|[b [db [lb [Hb [Hvb [_ [Hbd _]]]]]]]]; [exact Hle|].
  destruct Hb as [<-|Hb].
  - rewrite Hvd in Hbd. inversion Hbd; subst db. exfalso. exact (Pos.lt_irrefl _ Hvb).
  - pose proof (TarjanLow.open_head_number v open s b db dv Hbook Hnumbers Hb Hbd Hvd) as Hbv.
    exfalso. exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hvb Hbv)).
Qed.

(** Lowering one map entry can only decrease each existing entry. *)
Theorem low_set_bound (links : Map.t positive positive) v old n b lb :
  Map.wf positive_encoding links ->
  Map.get positive_encoding v links = Some old ->
  Map.get positive_encoding b links = Some lb ->
  exists lb', Map.get positive_encoding b
    (Map.set positive_encoding v (Pos.min old n) links) = Some lb' /\ (lb' <= lb)%positive.
Proof.
  intros Hwf Hold Hb. destruct (Pos.eq_dec b v) as [->|Hne].
  - rewrite Hold in Hb. inversion Hb; subst lb.
    exists (Pos.min old n). rewrite Map.get_set_same by exact Hwf.
    split; [reflexivity|apply Pos.le_min_l].
  - exists lb. rewrite (Map.get_set_other positive_encoding positive_encoding_laws) by assumption.
    split; [exact Hb|apply Pos.le_refl].
Qed.

(** An updated low-link lookup is bounded above by its corresponding previous lookup. *)
Theorem low_set_inverse (links : Map.t positive positive) v old n a la :
  Map.wf positive_encoding links -> Map.get positive_encoding v links = Some old ->
  Map.get positive_encoding a (Map.set positive_encoding v (Pos.min old n) links) = Some la ->
  exists la0, Map.get positive_encoding a links = Some la0 /\ (la <= la0)%positive.
Proof.
  intros Hwf Hold Ha. destruct (Pos.eq_dec a v) as [->|Hne].
  - rewrite Map.get_set_same in Ha by exact Hwf. inversion Ha; subst la.
    exists old. split; [exact Hold|apply Pos.le_min_l].
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Ha by assumption.
    exists la. split; [exact Ha|apply Pos.le_refl].
Qed.

(** Lowering the top open vertex retains every frontier witness, decreasing its low link if needed. *)
Theorem lower_frontier v open s n :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.numbered s -> frontier (v :: open) s ->
    frontier (v :: open) (Tarjan.lower v n s).
Proof.
  intros Hbook Hnumbers Hfrontier. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [old|] eqn:Hold;
    [|exact Hfrontier].
  pose proof (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)) as Hwf.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [Tarjan.stack Tarjan.disc Tarjan.low] in *.
  destruct (Pos.eq_dec w v) as [->|Hwne].
  - rewrite Map.get_set_same in Hwl by exact Hwf. inversion Hwl; subst lw.
    destruct (Pos.eq_dec a v) as [->|Hane].
    + rewrite Map.get_set_same in Hal by exact Hwf. inversion Hal; subst la.
      left. apply Pos.le_refl.
    + right. exists v, dw, (Pos.min old n). split; [now left|]. split.
      * apply (TarjanLow.open_head_number v open s a da dw Hbook Hnumbers);
          [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hwd].
      * split; [apply Pos.le_refl|]. split; [exact Hwd|].
        rewrite Map.get_set_same by exact Hwf. split; [reflexivity|apply Pos.le_refl].
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwl by assumption.
    destruct (Pos.eq_dec a v) as [->|Hane].
    + rewrite Map.get_set_same in Hal by exact Hwf. inversion Hal; subst la. left.
      eapply Pos.le_trans; [apply Pos.le_min_l|].
      exact (top_bound v open s w da dw old lw Hbook Hnumbers Hfrontier Hw
        Had Hwd Hold Hwl Hbound).
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hal by assumption.
      destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound)
        as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
      destruct (low_set_bound _ v old n b lb Hwf Hold Hbl) as [lb' [Hbl' Hle']].
      right. exists b, db, lb'. repeat split; try assumption.
      eapply Pos.le_trans; eassumption.
Qed.

(** A fresh entry is absent from the actual pending stack. *)
Theorem fresh_pending open s v :
  TarjanBook.bookkeeping open s -> Map.get positive_encoding v (Tarjan.disc s) = None ->
    ~ In v (Tarjan.stack s).
Proof.
  intros Hbook Hfresh Hin.
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook v) ltac:(apply in_or_app; now left))
    as [n Hn]. congruence.
Qed.

(** A fresh entry is absent from the ordered open-vertex subsequence. *)
Theorem fresh_open open s v :
  TarjanBook.bookkeeping open s -> Map.get positive_encoding v (Tarjan.disc s) = None ->
    ~ In v open.
Proof.
  intros Hbook Hfresh Hin. apply (fresh_pending open s v Hbook Hfresh).
  exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) v Hin).
Qed.

(** A fresh entry becomes the newest open frontier witness for every older open vertex. *)
Theorem enter_frontier open s v :
  TarjanBook.bookkeeping open s -> TarjanLow.numbered s -> frontier open s ->
  Map.get positive_encoding v (Tarjan.disc s) = None ->
    frontier (v :: open) (Tarjan.enter v s).
Proof.
  intros Hbook Hnumbers Hfrontier Hfresh a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  rewrite Tarjan.enter_equation in Hw, Had, Hwd, Hal, Hwl |- *.
  cbn [Tarjan.stack Tarjan.disc Tarjan.low In] in *.
  pose proof (TarjanStateFacts.disc_wf s (TarjanBook.canonical _ _ Hbook)) as Hdwf.
  pose proof (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)) as Hlwf.
  destruct Hw as [<-|Hw], Ha as [<-|Ha].
  - rewrite Map.get_set_same in Hal, Hwl by exact Hlwf.
    inversion Hal; inversion Hwl; subst. left. apply Pos.le_refl.
  - rewrite Map.get_set_same in Hwd by exact Hdwf.
    rewrite Map.get_set_same in Hwl by exact Hlwf. inversion Hwd; inversion Hwl; subst dw lw.
    assert (Hane : a <> v) by (intro Heq; subst a; exact (fresh_open open s v Hbook Hfresh Ha)).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Had by assumption.
    right. exists v, (Tarjan.clock s), (Tarjan.clock s). split; [now left|].
    split; [exact (TarjanLow.number_bound s a da Hnumbers Had)|].
    split; [apply Pos.le_refl|]. rewrite Map.get_set_same by exact Hdwf.
    rewrite Map.get_set_same by exact Hlwf. split; [reflexivity|].
    split; [reflexivity|apply Pos.le_refl].
  - rewrite Map.get_set_same in Had by exact Hdwf. inversion Had; subst da.
    assert (Hwne : w <> v) by (intro Heq; subst w; exact (fresh_pending open s v Hbook Hfresh Hw)).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwd by assumption.
    pose proof (TarjanLow.number_bound s w dw Hnumbers Hwd) as Hstrict.
    exfalso. exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hbound Hstrict)).
  - assert (Hwne : w <> v) by (intro Heq; subst w; exact (fresh_pending open s v Hbook Hfresh Hw)).
    assert (Hane : a <> v) by (intro Heq; subst a; exact (fresh_open open s v Hbook Hfresh Ha)).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Had by assumption.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwd by assumption.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hal by assumption.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwl by assumption.
    destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound)
      as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
    assert (Hbne : b <> v) by (intro Heq; subst b; exact (fresh_open open s v Hbook Hfresh Hb)).
    right. exists b, db, lb. split; [now right|].
    rewrite !Map.get_set_other by
      (first [exact positive_encoding_laws|exact Hdwf|exact Hlwf|exact Hbne]).
    auto.
Qed.

(** A pending suffix keeps every old low-link entry after an actual prefix pop. *)
Theorem pop_tail_links root i xs lows active own x :
  NoDup xs -> In x (Tarjan.tail (Tarjan.pop root i xs lows active own)) ->
  Map.get positive_encoding x (Tarjan.links (Tarjan.pop root i xs lows active own)) =
    Map.get positive_encoding x lows.
Proof.
  intros Hnodup Hx. rewrite TarjanStateFacts.pop_links.
  destruct (existsb (eqb positive_encoding x)
    (Tarjan.members (Tarjan.pop root i xs lows active own))) eqn:Hmem; [|reflexivity].
  apply TarjanStateFacts.member_test in Hmem.
  destruct (TarjanStateFacts.pop_split root i xs lows active own) as [Hsplit _].
  rewrite Hsplit in Hnodup. exfalso.
  exact (TarjanBook.nodup_disjoint _ _ Hnodup x Hmem Hx).
Qed.

(** Popping a top open vertex cuts exactly at that vertex and retains the older open subsequence. *)
Theorem pop_cut v open s :
  TarjanBook.bookkeeping (v :: open) s ->
  let answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) in
  exists prefix, Tarjan.stack s = prefix ++ v :: Tarjan.tail answer /\
    Tarjan.members answer = prefix ++ [v] /\ TarjanBook.stack_order open (Tarjan.tail answer).
Proof.
  intro Hbook.
  destruct (TarjanBook.stack_head v open (Tarjan.stack s) (TarjanBook.open_order _ _ Hbook))
    as [prefix [tail [Hstack Hopen]]].
  assert (Hnot : ~ In v prefix).
  { intro Hin. pose proof (TarjanBook.distinct _ _ Hbook) as Hdistinct.
    rewrite Hstack, <- app_assoc in Hdistinct.
    apply (TarjanBook.nodup_disjoint _ _ Hdistinct v Hin). now left. }
  pose proof (TarjanStateFacts.pop_prefix v (Tarjan.next_component s) prefix tail
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) Hnot) as [Hmembers Htail].
  rewrite <- Hstack in Hmembers, Htail. exists prefix. rewrite Htail. auto.
Qed.

(** Emitting the top root removes its frontier witnesses and preserves all older surviving witnesses. *)
Theorem emit_frontier v open s :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.numbered s -> frontier (v :: open) s ->
    frontier open (Tarjan.emit v s).
Proof.
  intros Hbook Hnumbers Hfrontier.
  set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (pop_cut v open s Hbook) as [prefix [Hstack [Hmembers Hopen]]].
  fold answer in Hstack, Hmembers, Hopen.
  assert (Hnodup : NoDup (Tarjan.stack s)) by
    exact (proj1 (TarjanBook.nodup_parts _ _ (TarjanBook.distinct _ _ Hbook))).
  assert (Htail : forall x, In x (Tarjan.tail answer) ->
    Map.get positive_encoding x (Tarjan.links answer) = Map.get positive_encoding x (Tarjan.low s)).
  { intros x Hx. exact (pop_tail_links v (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) x Hnodup Hx). }
  rewrite Tarjan.emit_equation. intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [Tarjan.stack Tarjan.disc Tarjan.low] in *. fold answer in Hw, Hal, Hwl |- *.
  assert (Hatail : In a (Tarjan.tail answer)) by exact (TarjanBook.stack_member _ _ Hopen a Ha).
  rewrite Htail in Hal, Hwl by assumption.
  assert (Hwold : In w (Tarjan.stack s)) by (rewrite Hstack; apply in_or_app; right; now right).
  destruct (Hfrontier a w da dw la lw (or_intror Ha) Hwold Had Hwd Hal Hwl Hbound)
    as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]]; [now left|].
  destruct Hb as [<-|Hb].
  - assert (Hstrict : (dw < db)%positive).
    { apply (TarjanLow.pending_numbers s v w db dw Hnumbers); [|exact Hbd|exact Hwd].
      rewrite Hstack. apply TarjanLow.before_prefix, TarjanLow.before_cons. left. auto. }
    exfalso. exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hbw Hstrict)).
  - right. exists b, db, lb. repeat split; try assumption.
    rewrite Htail; [exact Hbl|exact (TarjanBook.stack_member _ _ Hopen b Hb)].
Qed.

Local Lemma frontier_self v open s lows a da dv la lv :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.numbered s -> In a (v :: open) ->
  Map.get positive_encoding a (Tarjan.disc s) = Some da ->
  Map.get positive_encoding v (Tarjan.disc s) = Some dv ->
  Map.get positive_encoding a lows = Some la -> Map.get positive_encoding v lows = Some lv ->
  (la <= lv)%positive \/
  exists b db lb, In b (v :: open) /\ (da < db)%positive /\ (db <= dv)%positive /\
    Map.get positive_encoding b (Tarjan.disc s) = Some db /\
    Map.get positive_encoding b lows = Some lb /\ (lb <= lv)%positive.
Proof.
  intros Hbook Hnumbers Ha Had Hvd Hal Hvl. destruct (Pos.eq_dec a v) as [->|Hne].
  - rewrite Hvl in Hal. inversion Hal. left. apply Pos.le_refl.
  - right. exists v, dv, lv. split; [now left|]. split.
    + apply (TarjanLow.open_head_number v open s a da dv Hbook Hnumbers);
        [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hvd].
    + split; [apply Pos.le_refl|]. split; [exact Hvd|].
      split; [exact Hvl|apply Pos.le_refl].
Qed.

Local Lemma parent_witness v parent open s a da dp dv dw lp l lw :
  TarjanBook.bookkeeping (v :: parent :: open) s -> TarjanLow.numbered s ->
  In a (parent :: open) -> a <> parent ->
  Map.get positive_encoding a (Tarjan.disc s) = Some da ->
  Map.get positive_encoding parent (Tarjan.disc s) = Some dp ->
  Map.get positive_encoding v (Tarjan.disc s) = Some dv ->
  (dv <= dw)%positive -> (l <= lw)%positive ->
  exists b db lb, In b (parent :: open) /\ (da < db)%positive /\ (db <= dw)%positive /\
    Map.get positive_encoding b (Tarjan.disc s) = Some db /\
    Map.get positive_encoding b (Map.set positive_encoding parent (Pos.min lp l) (Tarjan.low s)) =
      Some lb /\ (lb <= lw)%positive.
Proof.
  intros Hbook Hnumbers Ha Hne Had Hpd Hvd Hvw Hle.
  exists parent, dp, (Pos.min lp l). split; [now left|]. split.
  - apply (TarjanLow.open_head_number parent open s a da dp
      (TarjanBook.drop_bookkeeping v (parent :: open) s Hbook) Hnumbers);
      [destruct Ha as [Heq|Ha]; [congruence|exact Ha]|exact Had|exact Hpd].
  - split.
    + eapply Pos.le_trans; [|exact Hvw]. apply Pos.lt_le_incl.
      exact (TarjanLow.open_head_number v (parent :: open) s parent dp dv
        Hbook Hnumbers (or_introl eq_refl) Hpd Hvd).
    + split; [exact Hpd|].
      rewrite Map.get_set_same by exact (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)).
      split; [reflexivity|]. eapply Pos.le_trans; [apply Pos.le_min_r|exact Hle].
Qed.

(** Closing a pending child transfers each frontier witness to its actual remaining parent. *)
Theorem close_lower_frontier v parent open s l :
  TarjanBook.bookkeeping (v :: parent :: open) s -> TarjanLow.numbered s ->
  frontier (v :: parent :: open) s -> Map.get positive_encoding v (Tarjan.low s) = Some l ->
    frontier (parent :: open) (Tarjan.lower parent l s).
Proof.
  intros Hbook Hnumbers Hfrontier Hvl.
  assert (Hp : In parent (Tarjan.stack s)) by
    exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) parent
      (or_intror (or_introl eq_refl))).
  destruct (proj2 (TarjanBook.low_domain _ _ Hbook parent) Hp) as [lp Hpl].
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook parent) ltac:(apply in_or_app; now left))
    as [dp Hpd].
  pose proof (TarjanStateFacts.low_wf s (TarjanBook.canonical _ _ Hbook)) as Hwf.
  rewrite Tarjan.lower_equation, Hpl.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [Tarjan.stack Tarjan.disc Tarjan.low] in *.
  destruct (Pos.eq_dec w parent) as [->|Hwne].
  - exact (frontier_self parent open s _ a da dw la lw
      (TarjanBook.drop_bookkeeping v (parent :: open) s Hbook) Hnumbers Ha Had Hwd Hal Hwl).
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hwl by assumption.
    destruct (low_set_inverse _ parent lp l a la Hwf Hpl Hal) as [la0 [Hal0 Hla]].
    destruct (Hfrontier a w da dw la0 lw (or_intror Ha) Hw Had Hwd Hal0 Hwl Hbound)
      as [Hle|[b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]]].
    + left. eapply Pos.le_trans; eassumption.
    + destruct Hb as [<-|Hb].
      * rewrite Hvl in Hbl. inversion Hbl; subst lb.
        destruct (Pos.eq_dec a parent) as [->|Hane].
        -- rewrite Map.get_set_same in Hal by exact Hwf. inversion Hal; subst la.
           left. eapply Pos.le_trans; [apply Pos.le_min_r|exact Hle].
        -- right. exact (parent_witness v parent open s a da dp db dw lp l lw
             Hbook Hnumbers Ha Hane Had Hpd Hbd Hbw Hle).
      * destruct (low_set_bound _ parent lp l b lb Hwf Hpl Hbl) as [lb' [Hbl' Hlb']].
        right. exists b, db, lb'. repeat split; try assumption.
        eapply Pos.le_trans; eassumption.
Qed.

(** Actual exit keeps the frontier on exactly the remaining open-vertex list. *)
Theorem exit_frontier v open s :
  TarjanBook.bookkeeping (v :: open) s -> TarjanLow.numbered s -> frontier (v :: open) s ->
    frontier open (Tarjan.exit v (hd_error open) s).
Proof.
  intros Hbook Hnumbers Hfrontier.
  assert (Hv : In v (Tarjan.stack s)) by
    exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) v (or_introl eq_refl)).
  destruct (proj2 (TarjanBook.low_domain _ _ Hbook v) Hv) as [l Hvl].
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook v) ltac:(apply in_or_app; now left))
    as [d Hvd].
  rewrite Tarjan.exit_equation, Hvl, Hvd. destruct (Pos.eqb l d).
  - now apply emit_frontier.
  - destruct open as [|parent open].
    + intros a w da dw la lw Hfalse. contradiction.
    + now apply close_lower_frontier with (v := v).
Qed.

(** Every non-tree edge lowers only the top source and preserves its open frontier. *)
Theorem edge_frontier u open s v k :
  TarjanBook.bookkeeping (u :: open) s -> TarjanLow.numbered s -> frontier (u :: open) s ->
    frontier (u :: open) (Tarjan.edge u v k s).
Proof.
  intros Hbook Hnumbers Hfrontier. rewrite Tarjan.edge_equation. destruct k; try exact Hfrontier.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hfrontier.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hfrontier.
  all: now apply lower_frontier.
Qed.

End TarjanFrontier.
