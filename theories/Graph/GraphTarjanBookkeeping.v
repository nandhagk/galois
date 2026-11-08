(** * Tarjan's pending and emitted partition

    Bookkeeping relates open search vertices, pending vertices and one-based component owners.
    For example, emitting a prefix moves its vertices from pending membership to one owner.
    Builds on: GraphTarjanState and the public map and set laws. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphTarjan GraphTarjanState.
Import List.ListNotations.

Module TarjanBook.
Local Open Scope nat_scope.

(** Open search vertices form an ordered subsequence of the pending Tarjan stack. *)
Inductive stack_order : list positive -> list positive -> Prop :=
  | stack_nil : forall xs, stack_order [] xs
  | stack_cons : forall v rest prefix tail, stack_order rest tail ->
      stack_order (v :: rest) (prefix ++ v :: tail).

(** Adding pending vertices before a stack subsequence does not change its order. *)
Theorem stack_prefix open xs prefix :
  stack_order open xs -> stack_order open (prefix ++ xs).
Proof.
  intro Hstack. destruct Hstack as [xs|v rest front tail Hrest].
  - constructor.
  - rewrite app_assoc. apply (stack_cons v rest (prefix ++ front) tail). exact Hrest.
Qed.

(** Every open vertex is pending. *)
Theorem stack_member open xs : stack_order open xs -> incl open xs.
Proof.
  intro Hstack. induction Hstack as [xs|v rest prefix tail Hrest IH]; intros x Hin.
  - contradiction.
  - apply in_or_app. right. destruct Hin as [<-|Hin]; [now left|right; now apply IH].
Qed.

(** The top open vertex cuts the pending stack before the subsequence of older open vertices. *)
Theorem stack_head v rest xs :
  stack_order (v :: rest) xs ->
  exists prefix tail, xs = prefix ++ v :: tail /\ stack_order rest tail.
Proof.
  intro Hstack. inversion Hstack as [|w open prefix tail Htail]; subst.
  exists prefix, tail. auto.
Qed.

(** Removing the top open vertex keeps the remaining open vertices in pending order. *)
Theorem stack_drop v rest xs : stack_order (v :: rest) xs -> stack_order rest xs.
Proof.
  intro Hstack. destruct (stack_head v rest xs Hstack) as [prefix [tail [-> Htail]]].
  replace (prefix ++ v :: tail) with ((prefix ++ [v]) ++ tail) by
    (rewrite <- app_assoc; reflexivity).
  now apply stack_prefix.
Qed.

(** A suffix of open vertices retains its pending-stack order. *)
Theorem stack_suffix prefix tail xs :
  stack_order (prefix ++ tail) xs -> stack_order tail xs.
Proof.
  induction prefix as [|v rest IH]; intro Hstack; [exact Hstack|].
  apply IH. now apply stack_drop with (v := v).
Qed.

(** Duplicate-free concatenation separates its left and right members. *)
Theorem nodup_disjoint {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> forall x, In x xs -> ~ In x ys.
Proof.
  intro Hnodup. induction xs as [|v rest IH]; intros x Hin; [contradiction|].
  inversion Hnodup as [|head tail Hnot Htail]; subst.
  destruct Hin as [<-|Hin].
  - intro Hx. apply Hnot. apply in_or_app. now right.
  - now apply IH.
Qed.

(** Each side of a duplicate-free concatenation is duplicate-free. *)
Theorem nodup_parts {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> NoDup xs /\ NoDup ys.
Proof.
  intro Hnodup. induction xs as [|v rest IH]; [split; [constructor|exact Hnodup]|].
  inversion Hnodup as [|head tail Hnot Htail]; subst.
  destruct (IH Htail) as [Hrest Hys]. split; [constructor|exact Hys].
  - intro Hin. apply Hnot. apply in_or_app. now left.
  - exact Hrest.
Qed.

(** Moving a consumed prefix behind the untouched suffix preserves duplicate freedom. *)
Theorem nodup_rotate {A} (xs ys zs : list A) :
  NoDup (xs ++ ys ++ zs) -> NoDup (ys ++ zs ++ xs).
Proof.
  intro Hnodup.
  replace (ys ++ zs ++ xs) with ((ys ++ zs) ++ xs) by (symmetry; apply app_assoc).
  eapply Permutation_NoDup; [apply Permutation_app_comm|exact Hnodup].
Qed.

(** Swapping two disjoint prefixes preserves duplicate freedom before their common suffix. *)
Theorem nodup_swap {A} (xs ys zs : list A) :
  NoDup (xs ++ ys ++ zs) -> NoDup (ys ++ xs ++ zs).
Proof.
  intro Hnodup. rewrite !app_assoc in *.
  eapply Permutation_NoDup; [apply Permutation_app_tail, Permutation_app_comm|exact Hnodup].
Qed.

(** The positive component counter is exactly the next chronological output position. *)
Record indexed (s : Tarjan.state) : Prop := Indexed {
  next_count : Pos.to_nat (Tarjan.next_component s) = S (length (Tarjan.emitted_rev s));
  owner_index : forall x i, Map.get positive_encoding x (Tarjan.owners s) = Some i <->
    exists c, nth_error (rev (Tarjan.emitted_rev s)) (Nat.pred (Pos.to_nat i)) = Some c /\
      In x c;
  components_nonempty : forall c, In c (Tarjan.emitted_rev s) -> c <> []
}.

(** Empty output has no owner and starts its next chronological position at one. *)
Theorem initial_indexed : indexed Tarjan.initial.
Proof.
  constructor.
  - reflexivity.
  - intros x i. cbn [Tarjan.initial Tarjan.owners Tarjan.emitted_rev rev].
    rewrite Map.get_empty. split; [discriminate|].
    intros [c [Hnth _]]. rewrite nth_error_nil in Hnth. discriminate.
  - intros c Hfalse. contradiction.
Qed.

(** Appending one output block adds exactly its one-based final position. *)
Theorem append_position (cs : list (list positive)) next x i members :
  Pos.to_nat next = S (length cs) ->
  ((exists c, nth_error (cs ++ [members]) (Nat.pred (Pos.to_nat i)) = Some c /\ In x c) <->
    (i = next /\ In x members) \/
    exists c, nth_error cs (Nat.pred (Pos.to_nat i)) = Some c /\ In x c).
Proof.
  intro Hnext.
  set (n := Nat.pred (Pos.to_nat i)).
  assert (Hi : Pos.to_nat i = S n) by (unfold n; pose proof (Pos2Nat.is_pos i); lia).
  destruct (lt_dec n (length cs)) as [Hlt|Hge].
  - rewrite nth_error_app1 by exact Hlt. split; [auto|].
    intros [[Heq _]|Hmember]; [subst i; lia|exact Hmember].
  - rewrite nth_error_app2 by lia.
    destruct (n - length cs) as [|k] eqn:Hminus.
    + assert (Heq : i = next) by (apply Pos2Nat.inj; lia).
      cbn [nth_error]. split.
      * intros [c [Hc Hx]]. inversion Hc; subst c. now left.
      * intros [[_ Hx]|[c [Hnth _]]].
        -- exists members. auto.
        -- assert (Hlt : n < length cs) by
             (apply nth_error_Some; rewrite Hnth; discriminate). lia.
    + cbn [nth_error]. rewrite nth_error_nil. split.
      * intros [c [Hfalse _]]. discriminate.
      * intros [[Heq _]|[c [Hnth _]]].
        -- subst i. lia.
        -- assert (Hlt : n < length cs) by
             (apply nth_error_Some; rewrite Hnth; discriminate). lia.
Qed.

(** Existing bindings locate actual emitted members and lie below the next component counter. *)
Theorem owner_location s x i :
  indexed s -> Map.get positive_encoding x (Tarjan.owners s) = Some i ->
  In x (concat (Tarjan.emitted_rev s)) /\ (i < Tarjan.next_component s)%positive.
Proof.
  intros Hindex Howner. apply (owner_index s Hindex) in Howner.
  destruct Howner as [c [Hnth Hx]]. split.
  - apply in_concat. exists c. split; [|exact Hx].
    apply (proj2 (in_rev _ _)). now apply nth_error_In in Hnth.
  - apply Pos2Nat.inj_lt. rewrite (next_count s Hindex).
    assert (Hbound : Nat.pred (Pos.to_nat i) < length (rev (Tarjan.emitted_rev s))).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    rewrite length_rev in Hbound. pose proof (Pos2Nat.is_pos i). lia.
Qed.

(** Every emitted member has an actual component owner without choosing a default index. *)
Theorem member_owner s x :
  indexed s -> In x (concat (Tarjan.emitted_rev s)) ->
    exists i, Map.get positive_encoding x (Tarjan.owners s) = Some i.
Proof.
  intros Hindex Hin. apply in_concat in Hin. destruct Hin as [c [Hc Hx]].
  apply (proj1 (in_rev _ _)) in Hc. apply In_nth_error in Hc. destruct Hc as [n Hnth].
  exists (Pos.of_succ_nat n). apply (owner_index s Hindex). exists c.
  rewrite SuccNat2Pos.id_succ. cbn [Nat.pred]. auto.
Qed.

(** Emission extends chronological owners exactly at the next index and keeps old output separate. *)
Theorem emit_indexed root s :
  TarjanStateFacts.storage s -> indexed s -> In root (Tarjan.stack s) ->
  (forall x, In x (Tarjan.stack s) -> ~ In x (concat (Tarjan.emitted_rev s))) ->
    indexed (Tarjan.emit root s).
Proof.
  intros Hstorage Hindex Hroot Hdisjoint.
  set (answer := Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit Hrootmember].
  fold answer in Hsplit, Hrootmember.
  assert (Hnonempty : Tarjan.members answer <> []).
  { intro Hempty. specialize (Hrootmember Hroot). rewrite Hempty in Hrootmember. contradiction. }
  assert (Hmembers : forall x, In x (Tarjan.members answer) ->
    ~ In x (concat (Tarjan.emitted_rev s))).
  { intros x Hx. apply Hdisjoint. rewrite Hsplit. apply in_or_app. now left. }
  rewrite Tarjan.emit_equation. fold answer. constructor.
  - cbn [Tarjan.next_component Tarjan.emitted_rev length].
    rewrite Pos2Nat.inj_succ, (next_count s Hindex). reflexivity.
  - intros x i. cbn [Tarjan.owners Tarjan.emitted_rev rev].
    rewrite (append_position (rev (Tarjan.emitted_rev s)) (Tarjan.next_component s))
      by (rewrite length_rev; exact (next_count s Hindex)).
    unfold answer at 1.
    rewrite TarjanStateFacts.pop_owners by exact (TarjanStateFacts.owners_wf s Hstorage).
    fold answer.
    destruct (existsb (eqb positive_encoding x) (Tarjan.members answer)) eqn:Hmem.
    + apply TarjanStateFacts.member_test in Hmem. split.
      * intro Heq. inversion Heq; subst i. now left.
      * intros [[-> _]|[c [Hnth Hx]]]; [reflexivity|].
        exfalso. apply (Hmembers x Hmem). apply in_concat. exists c. split; [|exact Hx].
        apply (proj2 (in_rev _ _)). now apply nth_error_In in Hnth.
    + rewrite (owner_index s Hindex). split; [auto|].
      intros [[_ Hx]|Hold]; [|exact Hold].
      apply TarjanStateFacts.member_test in Hx. congruence.
  - intros c [<-|Hc]; [exact Hnonempty|exact (components_nonempty s Hindex c Hc)].
Qed.

(** Pending and emitted vertices partition discovery; low links and the pending set index the stack. *)
Record bookkeeping (open : list positive) (s : Tarjan.state) : Prop := Bookkeeping {
  canonical : TarjanStateFacts.storage s;
  distinct : NoDup (Tarjan.stack s ++ concat (Tarjan.emitted_rev s));
  disc_domain : forall x, (exists n, Map.get positive_encoding x (Tarjan.disc s) = Some n) <->
    In x (Tarjan.stack s ++ concat (Tarjan.emitted_rev s));
  low_domain : forall x, (exists n, Map.get positive_encoding x (Tarjan.low s) = Some n) <->
    In x (Tarjan.stack s);
  pending_exact : forall x, FinSet.mem positive_encoding x (Tarjan.on_stack s) = true <->
    In x (Tarjan.stack s);
  open_order : stack_order open (Tarjan.stack s);
  output_indexed : indexed s
}.

(** Initial Tarjan storage has an empty discovered partition and no open search vertices. *)
Theorem initial_bookkeeping : bookkeeping [] Tarjan.initial.
Proof.
  constructor.
  - apply TarjanStateFacts.initial_storage.
  - constructor.
  - intro x. change ((exists n : positive,
      Map.get positive_encoding x Map.empty = Some n) <-> False).
    rewrite Map.get_empty. split; [intros [n Hfalse]; discriminate|contradiction].
  - intro x. change ((exists n : positive,
      Map.get positive_encoding x Map.empty = Some n) <-> False).
    rewrite Map.get_empty. split; [intros [n Hfalse]; discriminate|contradiction].
  - intro x. change (FinSet.mem positive_encoding x FinSet.empty = true <-> False).
    rewrite FinSet.mem_empty. split; [discriminate|contradiction].
  - constructor.
  - apply initial_indexed.
Qed.

(** A fresh entry adds exactly one new pending and discovered vertex without changing output. *)
Theorem enter_bookkeeping open s v :
  bookkeeping open s -> Map.get positive_encoding v (Tarjan.disc s) = None ->
    bookkeeping (v :: open) (Tarjan.enter v s).
Proof.
  intros Hbook Hfresh.
  assert (Hnot : ~ In v (Tarjan.stack s ++ concat (Tarjan.emitted_rev s))).
  { intro Hin. apply (disc_domain open s Hbook) in Hin. destruct Hin as [n Hn]. congruence. }
  assert (Hdiscwf := TarjanStateFacts.disc_wf s (canonical open s Hbook)).
  assert (Hlowwf := TarjanStateFacts.low_wf s (canonical open s Hbook)).
  constructor.
  - apply TarjanStateFacts.enter_storage, (canonical open s Hbook).
  - rewrite Tarjan.enter_equation. cbn [Tarjan.stack Tarjan.emitted_rev app].
    constructor; [exact Hnot|exact (distinct open s Hbook)].
  - intro x. rewrite Tarjan.enter_equation. cbn [Tarjan.disc Tarjan.stack Tarjan.emitted_rev app In].
    rewrite Map.get_set by exact Hdiscwf.
    destruct (eqb_spec positive_encoding positive_encoding_laws x v) as [->|Hne].
    + split; [auto|intros _; now exists (Tarjan.clock s)].
    + rewrite (disc_domain open s Hbook x). cbn [app In]. intuition congruence.
  - intro x. rewrite Tarjan.enter_equation. cbn [Tarjan.low Tarjan.stack In].
    rewrite Map.get_set by exact Hlowwf.
    destruct (eqb_spec positive_encoding positive_encoding_laws x v) as [->|Hne].
    + split; [auto|intros _; now exists (Tarjan.clock s)].
    + rewrite (low_domain open s Hbook x). intuition congruence.
  - intro x. rewrite Tarjan.enter_equation. cbn [Tarjan.on_stack Tarjan.stack In].
    rewrite FinSet.mem_add by exact (TarjanStateFacts.stack_set_wf s (canonical open s Hbook)).
    rewrite orb_true_iff, (eqb_true_iff positive_encoding positive_encoding_laws),
      (pending_exact open s Hbook x). intuition congruence.
  - rewrite Tarjan.enter_equation. change (stack_order (v :: open) ([] ++ v :: Tarjan.stack s)).
    constructor. exact (open_order open s Hbook).
  - destruct (output_indexed open s Hbook).
    rewrite Tarjan.enter_equation. constructor; assumption.
Qed.

(** Lowering changes an existing low link and preserves its exact pending domain. *)
Theorem lower_bookkeeping open s v n :
  bookkeeping open s -> bookkeeping open (Tarjan.lower v n s).
Proof.
  intro Hbook. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [old|] eqn:Hold; [|exact Hbook].
  pose proof (canonical open s Hbook) as Hstorage.
  constructor.
  - constructor; cbn; try apply Map.wf_set; apply Hstorage.
  - exact (distinct open s Hbook).
  - exact (disc_domain open s Hbook).
  - intro x. cbn [Tarjan.low Tarjan.stack].
    rewrite Map.get_set by exact (TarjanStateFacts.low_wf s Hstorage).
    destruct (eqb_spec positive_encoding positive_encoding_laws x v) as [->|Hne].
    + split.
      * intros _. apply (low_domain open s Hbook). now exists old.
      * intros _. now exists (Pos.min old n).
    + exact (low_domain open s Hbook x).
  - exact (pending_exact open s Hbook).
  - exact (open_order open s Hbook).
  - destruct (output_indexed open s Hbook). constructor; assumption.
Qed.

(** Removing a finished open vertex without emitting it retains the pending subsequence. *)
Theorem drop_bookkeeping v open s :
  bookkeeping (v :: open) s -> bookkeeping open s.
Proof.
  intro Hbook. destruct Hbook. constructor; try assumption. now apply stack_drop with (v := v).
Qed.

(** Popping the top open root leaves all older open vertices in the surviving pending suffix. *)
Theorem pop_open_suffix v open s :
  bookkeeping (v :: open) s ->
  stack_order open
    (Tarjan.tail (Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))).
Proof.
  intro Hbook.
  destruct (stack_head v open (Tarjan.stack s) (open_order _ _ Hbook))
    as [prefix [tail [Hstack Htail]]].
  assert (Hnot : ~ In v prefix).
  { intro Hin. pose proof (distinct _ _ Hbook) as Hdistinct.
    rewrite Hstack, <- app_assoc in Hdistinct.
    apply (nodup_disjoint prefix ((v :: tail) ++ concat (Tarjan.emitted_rev s))
      Hdistinct v Hin). now left. }
  rewrite Hstack. rewrite (proj2 (TarjanStateFacts.pop_prefix v (Tarjan.next_component s)
    prefix tail (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) Hnot)).
  exact Htail.
Qed.

(** A prefix pop removes exactly its members from the low-link domain. *)
Theorem pop_low_domain open s root i x :
  bookkeeping open s ->
  ((exists l, Map.get positive_encoding x (Tarjan.links (Tarjan.pop root i (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) = Some l) <->
    In x (Tarjan.tail (Tarjan.pop root i (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)))).
Proof.
  intro Hbook.
  set (answer := Tarjan.pop root i (Tarjan.stack s) (Tarjan.low s)
    (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split root i (Tarjan.stack s) (Tarjan.low s)
    (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _]. fold answer in Hsplit.
  assert (Hdisjoint : forall y, In y (Tarjan.members answer) -> ~ In y (Tarjan.tail answer)).
  { apply nodup_disjoint. rewrite <- Hsplit.
    exact (proj1 (nodup_parts _ _ (distinct _ _ Hbook))). }
  unfold answer at 1. rewrite TarjanStateFacts.pop_links. fold answer.
  destruct (existsb (eqb positive_encoding x) (Tarjan.members answer)) eqn:Hmem.
  - apply TarjanStateFacts.member_test in Hmem. split.
    + intros [l Hfalse]. discriminate.
    + intro Htail. exfalso. exact (Hdisjoint x Hmem Htail).
  - rewrite (low_domain _ _ Hbook x), Hsplit, in_app_iff.
    split; [intros [Hmember|Htail]; [|exact Htail]|auto].
    apply TarjanStateFacts.member_test in Hmember. congruence.
Qed.

(** A prefix pop leaves exactly its surviving suffix in the on-stack set. *)
Theorem pop_pending_exact open s root i x :
  bookkeeping open s ->
  (FinSet.mem positive_encoding x (Tarjan.pending (Tarjan.pop root i (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s))) = true <->
    In x (Tarjan.tail (Tarjan.pop root i (Tarjan.stack s)
      (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)))).
Proof.
  intro Hbook.
  set (answer := Tarjan.pop root i (Tarjan.stack s) (Tarjan.low s)
    (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split root i (Tarjan.stack s) (Tarjan.low s)
    (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _]. fold answer in Hsplit.
  assert (Hdisjoint : forall y, In y (Tarjan.members answer) -> ~ In y (Tarjan.tail answer)).
  { apply nodup_disjoint. rewrite <- Hsplit.
    exact (proj1 (nodup_parts _ _ (distinct _ _ Hbook))). }
  unfold answer at 1. rewrite TarjanStateFacts.pop_pending. fold answer.
  rewrite andb_true_iff, negb_true_iff, (pending_exact _ _ Hbook x), Hsplit, in_app_iff.
  split.
  - intros [Hnot [Hmember|Htail]]; [|exact Htail].
    apply TarjanStateFacts.member_test in Hmember. congruence.
  - intro Htail. split; [|auto].
    destruct (existsb (eqb positive_encoding x) (Tarjan.members answer)) eqn:Hmem;
      [|reflexivity].
    apply TarjanStateFacts.member_test in Hmem. exfalso. exact (Hdisjoint x Hmem Htail).
Qed.

(** Emitting the top open root transfers exactly its pending prefix to the next component. *)
Theorem emit_bookkeeping v open s :
  bookkeeping (v :: open) s -> bookkeeping open (Tarjan.emit v s).
Proof.
  intro Hbook.
  set (answer := Tarjan.pop v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  destruct (TarjanStateFacts.pop_split v (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  fold answer in Hsplit.
  assert (Hroot : In v (Tarjan.stack s)).
  { apply (stack_member _ _ (open_order _ _ Hbook)). now left. }
  pose proof (distinct _ _ Hbook) as Hdistinct.
  constructor.
  - apply TarjanStateFacts.emit_storage, (canonical _ _ Hbook).
  - rewrite Tarjan.emit_equation. fold answer.
    cbn [Tarjan.stack Tarjan.emitted_rev concat].
    apply nodup_swap. rewrite app_assoc, <- Hsplit. exact Hdistinct.
  - intro x. rewrite Tarjan.emit_equation. fold answer.
    cbn [Tarjan.disc Tarjan.stack Tarjan.emitted_rev concat].
    rewrite (disc_domain _ _ Hbook x), Hsplit, !in_app_iff. tauto.
  - intro x. rewrite Tarjan.emit_equation. fold answer.
    cbn [Tarjan.low Tarjan.stack].
    exact (pop_low_domain _ s v (Tarjan.next_component s) x Hbook).
  - intro x. rewrite Tarjan.emit_equation. fold answer.
    cbn [Tarjan.on_stack Tarjan.stack].
    exact (pop_pending_exact _ s v (Tarjan.next_component s) x Hbook).
  - rewrite Tarjan.emit_equation. apply pop_open_suffix, Hbook.
  - apply emit_indexed; [exact (canonical _ _ Hbook)|exact (output_indexed _ _ Hbook)|
      exact Hroot|].
    exact (nodup_disjoint _ _ Hdistinct).
Qed.

(** A non-tree edge only lowers a pending source link and keeps all bookkeeping fields. *)
Theorem edge_bookkeeping open s u v k :
  bookkeeping open s -> bookkeeping open (Tarjan.edge u v k s).
Proof.
  intro Hbook. rewrite Tarjan.edge_equation. destruct k; try exact Hbook.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hbook.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hbook.
  all: now apply lower_bookkeeping.
Qed.

(** Exiting a top open vertex either emits its component or retains it pending below its parent. *)
Theorem exit_bookkeeping v open parent s :
  bookkeeping (v :: open) s -> bookkeeping open (Tarjan.exit v parent s).
Proof.
  intro Hbook. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|];
    try (now apply drop_bookkeeping with (v := v)).
  destruct (Pos.eqb l d); [now apply emit_bookkeeping|].
  destruct parent; [apply lower_bookkeeping|]; now apply drop_bookkeeping with (v := v).
Qed.

End TarjanBook.
