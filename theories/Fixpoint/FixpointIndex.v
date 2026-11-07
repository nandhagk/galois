(** * Prepared dependency indexes

    Preparation stores distinct per-constraint output and read keys in finite maps.
    For example, two occurrences of a declared side key add one bucket entry per constraint.
    Builds on: FixpointSystem, BaseIndex and BaseSet. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Fixpoint Require Import FixpointSystem.
Import List.ListNotations Cost.Notations.

(** Prepared indexes store contributor and reader buckets separately. *)
Record sys_index (X C : Type) := SysIndex {
  contributors : Map.t X (list C);
  readers : Map.t X (list C)
}.

Arguments SysIndex {X C}.
Arguments contributors {X C}.
Arguments readers {X C}.

Definition contributors_of_c {X C} (EX : encoding X) (ix : sys_index X C) x :=
  Index.find_c EX x (contributors ix).
Definition readers_of_c {X C} (EX : encoding X) (ix : sys_index X C) x :=
  Index.find_c EX x (readers ix).
Definition contributors_of {X C} (EX : encoding X) (ix : sys_index X C) x :=
  Cost.value (contributors_of_c EX ix x).
Definition readers_of {X C} (EX : encoding X) (ix : sys_index X C) x :=
  Cost.value (readers_of_c EX ix x).

(** Deduplication uses canonical set enumeration. *)
Definition distinct_c {X} (EX : encoding X) xs :=
  let* keys := FinSet.of_list_c EX xs in FinSet.elements_c keys.
Definition distinct {X} (EX : encoding X) xs := Cost.value (distinct_c EX xs).

Local Lemma distinct_equation {X} (EX : encoding X) xs :
  distinct EX xs = FinSet.elements (FinSet.of_list EX xs).
Proof.
  reflexivity.
Qed.

(** Distinct enumeration retains precisely the input keys under injectivity. *)
Theorem distinct_spec {X} (EX : encoding X) (HE : encoding_laws EX) xs x :
  In x (distinct EX xs) <-> In x xs.
Proof.
  rewrite distinct_equation.
  rewrite (FinSet.elements_spec EX HE x _ (FinSet.wf_of_list EX xs)).
  rewrite FinSet.mem_of_list, existsb_exists.
  split.
  - intros [y [Hy Heq]]; apply (eqb_true_iff EX HE) in Heq; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply eqb_refl].
Qed.

(** Distinct enumeration contains no duplicate key. *)
Theorem distinct_nodup {X} (EX : encoding X) xs : NoDup (distinct EX xs).
Proof.
  rewrite distinct_equation.
  apply (FinSet.elements_nodup EX), FinSet.wf_of_list.
Qed.

Definition push_c {X C} (EX : encoding X) c x (m : Map.t X (list C)) :=
  let* old := Index.find_c EX x m in Map.set_c EX x (c :: old) m.
Definition push {X C} (EX : encoding X) c x (m : Map.t X (list C)) :=
  Cost.value (push_c EX c x m).

Fixpoint push_many_c {X C} (EX : encoding X) c xs (m : Map.t X (list C)) :=
  match xs with
  | [] => Cost.ret m
  | x :: rest =>
    Cost.step ;;
    let* next := push_many_c EX c rest m in push_c EX c x next
  end.

Definition push_many {X C} (EX : encoding X) c xs (m : Map.t X (list C)) :=
  Cost.value (push_many_c EX c xs m).

Fixpoint index_rows_c {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) cs : Cost.t (sys_index X C) :=
  match cs with
  | [] => Cost.ret (SysIndex Map.empty Map.empty)
  | c :: rest =>
    Cost.step ;;
    let* ix := index_rows_c EX S SS rest in
    Cost.step ;;
    let* target := System.target_c S c in
    Cost.step ;;
    let* sides := System.side_targets_c SS c in
    Cost.step ;;
    let* reads := System.deps_c SS c in
    let* outputs := distinct_c EX (target :: sides) in
    let* inputs := distinct_c EX reads in
    let* contrib := push_many_c EX c outputs (contributors ix) in
    let* readers := push_many_c EX c inputs (readers ix) in
    Cost.ret (SysIndex contrib readers)
  end.

(** Preparation preserves listed constraint occurrences and deduplicates each row's keys. *)
Definition index_system_c {X C A} (EX : encoding X) (S : System.t X C A) SS :=
  index_rows_c EX S SS (System.constraints S).
Definition index_system {X C A} (EX : encoding X) (S : System.t X C A) SS :=
  Cost.value (index_system_c EX S SS).

(** Index laws include map invariants, membership agreement and conditional bucket uniqueness. *)
Record sys_index_laws {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) : Prop := {
  contributors_wf : Map.wf EX (contributors ix);
  readers_wf : Map.wf EX (readers ix);
  contributors_agree : forall x c, In c (contributors_of EX ix x) <->
    In c (System.constraints S) /\ (System.target S c = x \/ In x (side_targets SS c));
  readers_agree : forall x c, In c (readers_of EX ix x) <->
    In c (System.constraints S) /\ In x (deps SS c);
  index_nodup : NoDup (System.constraints S) ->
    forall x, NoDup (contributors_of EX ix x) /\ NoDup (readers_of EX ix x)
}.

Arguments contributors_wf {X C A EX S SS ix}.
Arguments readers_wf {X C A EX S SS ix}.
Arguments contributors_agree {X C A EX S SS ix}.
Arguments readers_agree {X C A EX S SS ix}.
Arguments index_nodup {X C A EX S SS ix}.

Section IndexLaws.
Context {X C A : Type} (EX : encoding X) (HE : encoding_laws EX)
  (S : System.t X C A) (SS : System.static S).

Local Lemma push_equation (c : C) (x : X) (m : Map.t X (list C)) :
  push EX c x m = Map.set EX x (c :: Index.find EX x m) m.
Proof.
  reflexivity.
Qed.

Local Lemma push_many_equation (c : C) (xs : list X) (m : Map.t X (list C)) :
  push_many EX c xs m =
  match xs with
  | [] => m
  | x :: rest => push EX c x (push_many EX c rest m)
  end.
Proof.
  destruct xs; reflexivity.
Qed.

Local Lemma push_many_wf (c : C) (xs : list X) (m : Map.t X (list C)) :
  Map.wf EX m -> Map.wf EX (push_many EX c xs m).
Proof.
  induction xs as [|x xs IH]; intro Hwf; rewrite push_many_equation; [exact Hwf|].
  rewrite push_equation; apply Map.wf_set, IH, Hwf.
Qed.

Local Lemma find_push (c : C) (x y : X) (m : Map.t X (list C)) :
  Map.wf EX m ->
  Index.find EX y (push EX c x m) =
    if eqb EX y x then c :: Index.find EX y m else Index.find EX y m.
Proof.
  intro Hwf; rewrite push_equation, Index.find_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x) eqn:Heq; [|apply Index.find_equation].
  apply (eqb_true_iff EX HE) in Heq; subst y; reflexivity.
Qed.

Local Lemma push_many_agree (c d : C) (xs : list X) (m : Map.t X (list C)) (y : X) :
  Map.wf EX m ->
  (In d (Index.find EX y (push_many EX c xs m)) <->
    (d = c /\ In y xs) \/ In d (Index.find EX y m)).
Proof.
  intro Hwf; induction xs as [|x xs IH]; rewrite push_many_equation.
  - cbn; tauto.
  - rewrite find_push by now apply push_many_wf.
    destruct (eqb EX y x) eqn:Hxy.
    + apply (eqb_true_iff EX HE) in Hxy; subst y; cbn; rewrite IH; intuition congruence.
    + apply (eqb_false_iff EX HE) in Hxy; rewrite IH; cbn; intuition congruence.
Qed.

Local Lemma push_many_nodup (c : C) (xs : list X) (m : Map.t X (list C)) :
  Map.wf EX m -> NoDup xs -> (forall y, NoDup (Index.find EX y m)) ->
  (forall y, ~ In c (Index.find EX y m)) ->
  forall y, NoDup (Index.find EX y (push_many EX c xs m)).
Proof.
  intros Hwf Hxs Hnodup Hfresh; induction Hxs as [|x xs Hnotin Hxs IH]; intro y;
    rewrite push_many_equation.
  - apply Hnodup.
  - rewrite find_push by now apply push_many_wf.
    destruct (eqb EX y x) eqn:Hxy; [|apply IH].
    apply (eqb_true_iff EX HE) in Hxy; subst y.
    constructor; [|apply IH].
    rewrite push_many_agree by exact Hwf.
    intros [[_ Hin]|Hin]; [exact (Hnotin Hin)|exact (Hfresh x Hin)].
Qed.

Local Lemma rows_equation cs :
  Cost.value (index_rows_c EX S SS cs) =
  match cs with
  | [] => SysIndex Map.empty Map.empty
  | c :: rest =>
    let ix := Cost.value (index_rows_c EX S SS rest) in
    SysIndex
      (push_many EX c (distinct EX (System.target S c :: side_targets SS c)) (contributors ix))
      (push_many EX c (distinct EX (deps SS c)) (readers ix))
  end.
Proof.
  destruct cs; reflexivity.
Qed.

Local Lemma rows_wf cs :
  Map.wf EX (contributors (Cost.value (index_rows_c EX S SS cs))) /\
  Map.wf EX (readers (Cost.value (index_rows_c EX S SS cs))).
Proof.
  induction cs as [|c cs [IHc IHr]]; rewrite rows_equation; cbn [contributors readers].
  - split; apply Map.wf_empty.
  - split; apply push_many_wf; assumption.
Qed.

Local Lemma rows_agree cs :
  (forall x c, In c (contributors_of EX (Cost.value (index_rows_c EX S SS cs)) x) <->
    In c cs /\ (System.target S c = x \/ In x (side_targets SS c))) /\
  (forall x c, In c (readers_of EX (Cost.value (index_rows_c EX S SS cs)) x) <->
    In c cs /\ In x (deps SS c)).
Proof.
  induction cs as [|d cs [IHc IHr]].
  - split; intros x c; unfold contributors_of, contributors_of_c, readers_of, readers_of_c;
      rewrite rows_equation; cbn [contributors readers].
    all: fold (Index.find EX x (@Map.empty X (list C)));
      rewrite Index.find_equation, Map.get_empty; cbn; tauto.
  - destruct (rows_wf cs) as [Hwc Hwr].
    split; intros x c; unfold contributors_of, contributors_of_c, readers_of, readers_of_c;
      rewrite rows_equation; cbn [contributors readers].
    + fold (Index.find EX x
        (push_many EX d (distinct EX (System.target S d :: side_targets SS d))
          (contributors (Cost.value (index_rows_c EX S SS cs))))).
      rewrite push_many_agree by exact Hwc.
      rewrite distinct_spec by exact HE.
      change ((c = d /\ In x (System.target S d :: side_targets SS d)) \/
        In c (contributors_of EX (Cost.value (index_rows_c EX S SS cs)) x) <->
        In c (d :: cs) /\ (System.target S c = x \/ In x (side_targets SS c))).
      rewrite IHc; cbn; intuition congruence.
    + fold (Index.find EX x (push_many EX d (distinct EX (deps SS d))
        (readers (Cost.value (index_rows_c EX S SS cs))))).
      rewrite push_many_agree by exact Hwr.
      rewrite distinct_spec by exact HE.
      change ((c = d /\ In x (deps SS d)) \/
        In c (readers_of EX (Cost.value (index_rows_c EX S SS cs)) x) <->
        In c (d :: cs) /\ In x (deps SS c)).
      rewrite IHr; cbn; intuition congruence.
Qed.

Local Lemma rows_nodup cs :
  NoDup cs -> forall x,
    NoDup (contributors_of EX (Cost.value (index_rows_c EX S SS cs)) x) /\
    NoDup (readers_of EX (Cost.value (index_rows_c EX S SS cs)) x).
Proof.
  intro Hcs; induction Hcs as [|c cs Hfresh Hcs IH]; intro x.
  - unfold contributors_of, contributors_of_c, readers_of, readers_of_c.
    rewrite rows_equation; cbn [contributors readers].
    change (NoDup (Index.find EX x (@Map.empty X (list C))) /\
      NoDup (Index.find EX x (@Map.empty X (list C)))).
    rewrite Index.find_equation, Map.get_empty; split; constructor.
  - destruct (rows_agree cs) as [Hc Hr]; destruct (rows_wf cs) as [Hwc Hwr].
    unfold contributors_of, contributors_of_c, readers_of, readers_of_c.
    rewrite rows_equation; cbn [contributors readers]; split.
    + fold (Index.find EX x
        (push_many EX c (distinct EX (System.target S c :: side_targets SS c))
          (contributors (Cost.value (index_rows_c EX S SS cs))))).
      apply push_many_nodup; [exact Hwc|apply distinct_nodup| |].
      * intro y; exact (proj1 (IH y)).
      * intros y Hin; apply Hfresh; exact (proj1 (proj1 (Hc y c) Hin)).
    + fold (Index.find EX x (push_many EX c (distinct EX (deps SS c))
        (readers (Cost.value (index_rows_c EX S SS cs))))).
      apply push_many_nodup; [exact Hwr|apply distinct_nodup| |].
      * intro y; exact (proj2 (IH y)).
      * intros y Hin; apply Hfresh; exact (proj1 (proj1 (Hr y c) Hin)).
Qed.

(** Preparation establishes the complete index invariant under key encoding injectivity. *)
Theorem index_system_laws : sys_index_laws EX S SS (index_system EX S SS).
Proof.
  destruct (rows_wf (System.constraints S)) as [Hwc Hwr].
  destruct (rows_agree (System.constraints S)) as [Hc Hr].
  constructor; [exact Hwc|exact Hwr|exact Hc|exact Hr|apply rows_nodup].
Qed.

End IndexLaws.

Arguments index_system_c {X C A} EX S SS : simpl never.
Arguments index_system {X C A} EX S SS : simpl never.
