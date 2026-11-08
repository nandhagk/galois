(** * Scoped low-link witnesses

    Low links identify older pending vertices reached by scoped paths.
    For example, a finished pending vertex reaches an open vertex through decreasing witnesses.
    Builds on: GraphTarjanBookkeeping and the public Search numbering laws. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchInvariant GraphTarjan GraphTarjanState GraphTarjanBookkeeping.
Import List.ListNotations.

Module TarjanLow.
Local Open Scope nat_scope.

(** Scoped reachability between vertices records an actual admitted path. *)
Definition reaches {V E} (p : Prepared.t V E) scope u v :=
  exists es, Search.scoped_path p scope u es v.

(** Concatenating two scoped paths retains both their endpoints and their edge labels. *)
Theorem path_append {V E} (p : Prepared.t V E) scope u first v last w :
  Search.scoped_path p scope u first v -> Search.scoped_path p scope v last w ->
    Search.scoped_path p scope u (first ++ last) w.
Proof.
  intro Hfirst. revert last w.
  induction Hfirst as [v Hv Ha|u e v es z Hu Ha Hedge Hpath IH]; intros last w Hlast.
  - exact Hlast.
  - cbn [app]. eapply Search.scoped_cons; [exact Hu|exact Ha|exact Hedge|].
    now apply IH.
Qed.

(** Scoped reachability composes through the same intermediate vertex. *)
Theorem reaches_trans {V E} (p : Prepared.t V E) scope u v w :
  reaches p scope u v -> reaches p scope v w -> reaches p scope u w.
Proof.
  intros [first Hfirst] [last Hlast]. exists (first ++ last).
  eapply path_append; eassumption.
Qed.

(** Every discovered ID is valid and admitted, independently of pending or emitted status. *)
Definition discovered_domain {V E} (p : Prepared.t V E) scope (s : Tarjan.state) :=
  forall v n, Map.get positive_encoding v (Tarjan.disc s) = Some n ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.

(** Discovered vertices have a reflexive scoped path. *)
Theorem discovered_refl {V E} (p : Prepared.t V E) scope s v n :
  discovered_domain p scope s -> Map.get positive_encoding v (Tarjan.disc s) = Some n ->
    reaches p scope v v.
Proof.
  intros Hdomain Hnumber. destruct (Hdomain v n Hnumber) as [Hv Ha].
  exists []. now apply Search.scoped_nil.
Qed.

(** Textual precedence on a nonempty list either starts at its head or occurs in its tail. *)
Theorem before_cons {A} (xs : list A) w u v :
  before (w :: xs) u v <-> (u = w /\ In v xs) \/ before xs u v.
Proof.
  split.
  - intros [[|a first] [middle [last Heq]]].
    + cbn in Heq. inversion Heq; subst w xs. left. split; [reflexivity|].
      apply in_or_app. right. now left.
    + cbn in Heq. inversion Heq; subst a xs.
      right. exists first, middle, last. reflexivity.
  - intros [[-> Hin]|[first [middle [last Heq]]]].
    + apply in_split in Hin. destruct Hin as [middle [last ->]].
      exists [], middle, last. reflexivity.
    + exists (w :: first), middle, last. cbn. now rewrite Heq.
Qed.

(** A common prefix preserves textual precedence. *)
Theorem before_prefix {A} (prefix xs : list A) u v :
  before xs u v -> before (prefix ++ xs) u v.
Proof.
  intros [first [middle [last ->]]]. exists (prefix ++ first), middle, last.
  rewrite <- app_assoc. reflexivity.
Qed.

(** A member of the left list precedes a member of the right list in their concatenation. *)
Theorem before_cross {A} (xs ys : list A) u v :
  In u xs -> In v ys -> before (xs ++ ys) u v.
Proof.
  intros Hu Hv. apply in_split in Hu, Hv.
  destruct Hu as [first [middle ->]], Hv as [front [last ->]].
  exists first, (middle ++ front), last. rewrite <- !app_assoc. reflexivity.
Qed.

(** Reversing a list reverses textual precedence. *)
Theorem before_reverse {A} (xs : list A) u v :
  before xs u v <-> before (rev xs) v u.
Proof.
  assert (Hforward : forall (ys : list A) a b, before ys a b -> before (rev ys) b a).
  { intros ys a b [first [middle [last ->]]].
    exists (rev last), (rev middle), (rev first).
    rewrite !rev_app_distr. cbn [rev]. rewrite rev_app_distr. cbn [rev].
    rewrite <- !app_assoc. reflexivity. }
  split; [apply Hforward|]. intro Hbefore. apply Hforward in Hbefore.
  now rewrite rev_involutive in Hbefore.
Qed.

(** Ordered subsequences preserve textual precedence in the pending history. *)
Theorem stack_before open xs u v :
  TarjanBook.stack_order open xs -> before open u v -> before xs u v.
Proof.
  intro Hstack. induction Hstack as [xs|w rest prefix tail Htail IH]; intro Hbefore.
  - destruct Hbefore as [[|a first] [middle [last Hfalse]]]; discriminate.
  - apply before_prefix, before_cons. apply before_cons in Hbefore.
    destruct Hbefore as [[Heq Hin]|Hbefore].
    + left. split; [exact Heq|exact (TarjanBook.stack_member _ _ Htail v Hin)].
    + right. now apply IH.
Qed.

(** Pending vertices retain their order in the shared fresh-discovery numbering history. *)
Definition numbered (s : Tarjan.state) :=
  exists history, SearchInvariant.numbering history (Tarjan.disc s) (Tarjan.clock s) /\
    TarjanBook.stack_order (Tarjan.stack s) history.

(** The empty pending stack agrees with the empty shared numbering history. *)
Theorem initial_numbered : numbered Tarjan.initial.
Proof.
  exists []. split; constructor.
Qed.

(** Fresh entry reuses the public Search numbering constructor. *)
Theorem enter_numbered s v :
  numbered s -> Map.get positive_encoding v (Tarjan.disc s) = None ->
    numbered (Tarjan.enter v s).
Proof.
  intros [history [Hnumbers Hstack]] Hfresh.
  rewrite Tarjan.enter_equation. exists (v :: history). split.
  - constructor; [exact Hnumbers|].
    intro Hin. apply (SearchInvariant.numbering_domain _ _ _ Hnumbers) in Hin.
    destruct Hin as [n Hn]. congruence.
  - change (TarjanBook.stack_order (v :: Tarjan.stack s) ([] ++ v :: history)).
    constructor. exact Hstack.
Qed.

(** Lowering leaves the shared discovery history and pending order unchanged. *)
Theorem lower_numbered s v n : numbered s -> numbered (Tarjan.lower v n s).
Proof.
  intro Hnumbers. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); exact Hnumbers.
Qed.

(** Emission removes a pending prefix without changing any discovery number. *)
Theorem emit_numbered s root : numbered s -> numbered (Tarjan.emit root s).
Proof.
  intros [history [Hnumbers Hstack]].
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  rewrite Tarjan.emit_equation. exists history. split; [exact Hnumbers|].
  cbn [Tarjan.stack]. rewrite Hsplit in Hstack.
  eapply TarjanBook.stack_suffix. exact Hstack.
Qed.

(** The earlier pending occurrence has the larger discovery number. *)
Theorem pending_numbers s u v a b :
  numbered s -> before (Tarjan.stack s) u v ->
  Map.get positive_encoding u (Tarjan.disc s) = Some a ->
  Map.get positive_encoding v (Tarjan.disc s) = Some b -> (b < a)%positive.
Proof.
  intros [history [Hnumbers Hstack]] Hbefore Hu Hv.
  apply (proj1 (SearchInvariant.numbering_order history _ _ Hnumbers v u b a Hv Hu)).
  apply (proj1 (before_reverse history u v)).
  exact (stack_before _ _ u v Hstack Hbefore).
Qed.

(** Every pending discovery rank is below the next shared discovery clock. *)
Theorem number_bound s v d :
  numbered s -> Map.get positive_encoding v (Tarjan.disc s) = Some d ->
    (d < Tarjan.clock s)%positive.
Proof.
  intros [history [Hnumbers _]] Hget.
  exact (SearchInvariant.numbering_bound _ _ _ Hnumbers v d Hget).
Qed.

(** The top open vertex is newer than every other currently open vertex. *)
Theorem open_head_number v open s a da dv :
  TarjanBook.bookkeeping (v :: open) s -> numbered s -> In a open ->
  Map.get positive_encoding a (Tarjan.disc s) = Some da ->
  Map.get positive_encoding v (Tarjan.disc s) = Some dv -> (da < dv)%positive.
Proof.
  intros Hbook Hnumbers Ha Had Hvd.
  apply (pending_numbers s v a dv da Hnumbers); [|exact Hvd|exact Had].
  apply (stack_before _ _ v a (TarjanBook.open_order _ _ Hbook)), before_cons.
  left. auto.
Qed.

(** Every low link denotes an older pending vertex reachable by a scoped path from its owner. *)
Definition low_witness {V E} (p : Prepared.t V E) scope (s : Tarjan.state) :=
  forall w l, Map.get positive_encoding w (Tarjan.low s) = Some l ->
    exists d x, Map.get positive_encoding w (Tarjan.disc s) = Some d /\
      (l <= d)%positive /\ In x (Tarjan.stack s) /\
      Map.get positive_encoding x (Tarjan.disc s) = Some l /\ reaches p scope w x.

(** A pending vertex whose search frame has exited has a strictly older low-link witness. *)
Definition closed_low open (s : Tarjan.state) :=
  forall w l d, In w (Tarjan.stack s) -> ~ In w open ->
    Map.get positive_encoding w (Tarjan.low s) = Some l ->
    Map.get positive_encoding w (Tarjan.disc s) = Some d -> (l < d)%positive.

(** Every older pending vertex reaches every newer pending vertex through the scope. *)
Definition pending_paths {V E} (p : Prepared.t V E) scope (s : Tarjan.state) :=
  forall u v a b, In u (Tarjan.stack s) -> In v (Tarjan.stack s) ->
    Map.get positive_encoding u (Tarjan.disc s) = Some a ->
    Map.get positive_encoding v (Tarjan.disc s) = Some b ->
    (a <= b)%positive -> reaches p scope u v.

(** Low-link descent connects each pending vertex to a still-open vertex of no greater rank. *)
Theorem pending_support {V E} (p : Prepared.t V E) scope open s :
  TarjanBook.bookkeeping open s -> discovered_domain p scope s ->
  low_witness p scope s -> closed_low open s ->
  forall w d, In w (Tarjan.stack s) ->
    Map.get positive_encoding w (Tarjan.disc s) = Some d ->
    exists a da, In a open /\ reaches p scope w a /\
      Map.get positive_encoding a (Tarjan.disc s) = Some da /\ (da <= d)%positive.
Proof.
  intros Hbook Hdomain Hlow Hclosed.
  assert (Hsupport : forall n w d, Pos.to_nat d = n -> In w (Tarjan.stack s) ->
    Map.get positive_encoding w (Tarjan.disc s) = Some d ->
    exists a da, In a open /\ reaches p scope w a /\
      Map.get positive_encoding a (Tarjan.disc s) = Some da /\ (da <= d)%positive).
  { intro n. induction n as [n IH] using lt_wf_ind; intros w d Hn Hw Hwd.
    destruct (in_dec Pos.eq_dec w open) as [Hopen|Hnot].
    - exists w, d. split; [exact Hopen|]. split.
      + exact (discovered_refl p scope s w d Hdomain Hwd).
      + split; [exact Hwd|apply Pos.le_refl].
    - destruct (proj2 (TarjanBook.low_domain _ _ Hbook w) Hw) as [l Hwl].
      destruct (Hlow w l Hwl) as [d' [x [Hwd' [_ [Hx [Hxd Hpath]]]]]].
      assert (Hstrict : (l < d)%positive) by (apply (Hclosed w l d); assumption).
      destruct (IH (Pos.to_nat l)
        ltac:(rewrite <- Hn; apply Pos2Nat.inj_lt; exact Hstrict) x l eq_refl Hx Hxd)
        as [a [da [Ha [Hreach [Had Hbound]]]]].
      exists a, da. split; [exact Ha|]. split.
      + eapply reaches_trans; eassumption.
      + split; [exact Had|]. eapply Pos.le_trans; [exact Hbound|].
        now apply Pos.lt_le_incl. }
  intros w d Hw Hwd. exact (Hsupport (Pos.to_nat d) w d eq_refl Hw Hwd).
Qed.

(** A search boundary with no open vertices has no pending Tarjan vertices. *)
Theorem pending_empty {V E} (p : Prepared.t V E) scope s :
  TarjanBook.bookkeeping [] s -> discovered_domain p scope s ->
  low_witness p scope s -> closed_low [] s -> Tarjan.stack s = [].
Proof.
  intros Hbook Hdomain Hlow Hclosed. destruct (Tarjan.stack s) as [|w rest] eqn:Hstack;
    [reflexivity|].
  assert (Hw : In w (Tarjan.stack s)) by (rewrite Hstack; now left).
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook w) ltac:(apply in_or_app; now left))
    as [d Hwd].
  destruct (pending_support p scope [] s Hbook Hdomain Hlow Hclosed w d Hw Hwd)
    as [a [da [Hfalse _]]]. contradiction.
Qed.

(** Every pending vertex reaches the current top open vertex through its open low-link support. *)
Theorem pending_current {V E} (p : Prepared.t V E) scope v open s :
  TarjanBook.bookkeeping (v :: open) s -> numbered s -> discovered_domain p scope s ->
  low_witness p scope s -> closed_low (v :: open) s -> pending_paths p scope s ->
  forall w, In w (Tarjan.stack s) -> reaches p scope w v.
Proof.
  intros Hbook Hnumbers Hdomain Hlow Hclosed Hpaths w Hw.
  assert (Hv : In v (Tarjan.stack s)).
  { apply (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook)). now left. }
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook w) ltac:(apply in_or_app; now left))
    as [dw Hwd].
  destruct (proj2 (TarjanBook.disc_domain _ _ Hbook v) ltac:(apply in_or_app; now left))
    as [dv Hvd].
  destruct (pending_support p scope (v :: open) s Hbook Hdomain Hlow Hclosed w dw Hw Hwd)
    as [a [da [Ha [Hreach [Had Hbound]]]]].
  eapply reaches_trans; [exact Hreach|]. apply (Hpaths a v da dv).
  - exact (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ Hbook) a Ha).
  - exact Hv.
  - exact Had.
  - exact Hvd.
  - destruct Ha as [<-|Ha].
    + rewrite Hvd in Had. inversion Had. apply Pos.le_refl.
    + apply Pos.lt_le_incl. exact (open_head_number v open s a da dv Hbook Hnumbers Ha Had Hvd).
Qed.

(** Low-link semantics are tied to the actual open-vertex subsequence and discovery partition. *)
Record invariant {V E} (p : Prepared.t V E) scope open (s : Tarjan.state) : Prop := Invariant {
  book : TarjanBook.bookkeeping open s;
  numbers : numbered s;
  domain : discovered_domain p scope s;
  links : low_witness p scope s;
  closed : closed_low open s;
  paths : pending_paths p scope s
}.

(** Empty visitor state satisfies every low-link semantic obligation on every graph and scope. *)
Theorem initial_invariant {V E} (p : Prepared.t V E) scope :
  invariant p scope [] Tarjan.initial.
Proof.
  constructor.
  - apply TarjanBook.initial_bookkeeping.
  - apply initial_numbered.
  - intros v n Hfalse. change (Map.get positive_encoding v Map.empty = Some n) in Hfalse.
    rewrite Map.get_empty in Hfalse. discriminate.
  - intros w l Hfalse. change (Map.get positive_encoding w Map.empty = Some l) in Hfalse.
    rewrite Map.get_empty in Hfalse. discriminate.
  - intros w l d Hfalse. contradiction.
  - intros u v a b Hfalse. contradiction.
Qed.

(** Popping the top open vertex makes it the oldest member of its actual emitted prefix. *)
Theorem popped_number v open s w dv dw :
  TarjanBook.bookkeeping (v :: open) s -> numbered s ->
  In w (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
  Map.get positive_encoding v (Tarjan.disc s) = Some dv ->
  Map.get positive_encoding w (Tarjan.disc s) = Some dw -> (dv <= dw)%positive.
Proof.
  intros Hbook Hnumbers Hw Hvd Hwd.
  destruct (TarjanBook.stack_head v open (Tarjan.stack s) (TarjanBook.open_order _ _ Hbook))
    as [prefix [tail [Hstack Hopen]]].
  assert (Hnot : ~ In v prefix).
  { intro Hin. pose proof (TarjanBook.distinct _ _ Hbook) as Hdistinct.
    rewrite Hstack, <- app_assoc in Hdistinct.
    apply (TarjanBook.nodup_disjoint _ _ Hdistinct v Hin). now left. }
  rewrite Hstack, (proj1 (TarjanStateFacts.pop_prefix v (Tarjan.next_component s)
    prefix tail (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) Hnot)) in Hw.
  apply in_app_iff in Hw. destruct Hw as [Hw|[<-|Hfalse]].
  - apply Pos.lt_le_incl. apply (pending_numbers s w v dw dv Hnumbers); [|exact Hwd|exact Hvd].
    rewrite Hstack. apply before_cross; [exact Hw|now left].
  - rewrite Hvd in Hwd. inversion Hwd. apply Pos.le_refl.
  - contradiction.
Qed.

(** Every actually emitted prefix is mutually scoped reachable before its root is closed. *)
Theorem emission_strong {V E} (p : Prepared.t V E) scope v open s :
  invariant p scope (v :: open) s ->
  forall u w,
  In u (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
  In w (Tarjan.members (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) ->
    reaches p scope u w /\ reaches p scope w u.
Proof.
  intro HI.
  set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _]. fold answer in Hsplit.
  assert (Hv : In v (Tarjan.stack s)).
  { apply (TarjanBook.stack_member _ _ (TarjanBook.open_order _ _ (book _ _ _ _ HI))). now left. }
  destruct (proj2 (TarjanBook.disc_domain _ _ (book _ _ _ _ HI) v)
    ltac:(apply in_or_app; now left)) as [dv Hvd].
  assert (Hreach : forall w, In w (Tarjan.members answer) ->
    reaches p scope v w /\ reaches p scope w v).
  { intros w Hw.
    assert (Hpending : In w (Tarjan.stack s)) by (rewrite Hsplit; apply in_or_app; now left).
    destruct (proj2 (TarjanBook.disc_domain _ _ (book _ _ _ _ HI) w)
      ltac:(apply in_or_app; now left)) as [dw Hwd]. split.
    - apply (paths _ _ _ _ HI v w dv dw Hv Hpending Hvd Hwd).
      exact (popped_number v open s w dv dw (book _ _ _ _ HI) (numbers _ _ _ _ HI) Hw Hvd Hwd).
    - exact (pending_current p scope v open s (book _ _ _ _ HI) (numbers _ _ _ _ HI)
        (domain _ _ _ _ HI) (links _ _ _ _ HI) (closed _ _ _ _ HI) (paths _ _ _ _ HI)
        w Hpending). }
  intros u w Hu Hw. destruct (Hreach u Hu) as [Hvu Huv], (Hreach w Hw) as [Hvw Hwv].
  split; eapply reaches_trans; eassumption.
Qed.

End TarjanLow.
