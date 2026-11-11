(** * Finite class-count progress

    Counting the last occurrence of each equivalence class bounds strict refinements.
    For example, splitting a two-element class increases the count from one to two.
    Builds on: Stdlib lists and boolean reflection. *)

From Stdlib Require Import List Bool Arith Lia.
Import List.ListNotations.

Module NumberingClasses.

(** A boolean equivalence supplies the laws needed to count its finite classes. *)
Record equivalence {A} (r : A -> A -> bool) : Prop := {
  class_refl : forall x, r x x = true;
  class_sym : forall x y, r x y = true -> r y x = true;
  class_trans : forall x y z, r x y = true -> r y z = true -> r x z = true
}.

Arguments class_refl {A r}.
Arguments class_sym {A r}.
Arguments class_trans {A r}.

(** The last occurrence of a class contributes one, even when the inventory has duplicates. *)
Fixpoint classes {A} (r : A -> A -> bool) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    (if existsb (r x) rest then 0 else 1) + classes r rest
  end.

(** A finite inventory has at most one class per occurrence. *)
Theorem classes_bound {A} (r : A -> A -> bool) xs : classes r xs <= length xs.
Proof.
  induction xs as [|x rest IH]; cbn [classes length]; [lia|].
  destruct (existsb (r x) rest); lia.
Qed.

Local Lemma existsb_refines {A} (p q : A -> A -> bool) xs x :
  (forall a b, q a b = true -> p a b = true) ->
  existsb (q x) xs = true -> existsb (p x) xs = true.
Proof.
  intros Hrefine Hexists; apply existsb_exists in Hexists as [y [Hy Hxy]].
  apply existsb_exists; exists y; split; [exact Hy|now apply Hrefine].
Qed.

(** Removing equalities cannot decrease the number of classes on a fixed inventory. *)
Theorem classes_mono {A} (p q : A -> A -> bool) xs :
  (forall a b, q a b = true -> p a b = true) ->
  classes p xs <= classes q xs.
Proof.
  intro Hrefine; induction xs as [|x rest IH]; cbn [classes]; [lia|].
  destruct (existsb (q x) rest) eqn:Hq.
  - rewrite (existsb_refines p q rest x Hrefine Hq); lia.
  - destruct (existsb (p x) rest); lia.
Qed.

Local Lemma split_transport {A} (p q : A -> A -> bool)
    (Hp : equivalence p) (Hq : equivalence q)
    (Hrefine : forall a b, q a b = true -> p a b = true) x y z :
  p x y = true -> q x y = false -> q x z = true ->
  p z y = true /\ q z y = false.
Proof.
  intros Hpxy Hqxy Hqxz; split.
  - apply (class_trans Hp z x y).
    + apply (class_sym Hp); exact (Hrefine x z Hqxz).
    + exact Hpxy.
  - destruct (q z y) eqn:Hqzy; [|reflexivity].
    pose proof (class_trans Hq x z y Hqxz Hqzy) as Htrue; congruence.
Qed.

Local Lemma split_at_head {A} (p q : A -> A -> bool)
    (Hp : equivalence p) (Hq : equivalence q)
    (Hrefine : forall a b, q a b = true -> p a b = true) x y rest :
  In y rest -> p x y = true -> q x y = false ->
  existsb (q x) rest = true ->
  exists a b, In a rest /\ In b rest /\ p a b = true /\ q a b = false.
Proof.
  intros Hy Hpxy Hqxy Hexists.
  apply existsb_exists in Hexists as [z [Hz Hqxz]].
  destruct (split_transport p q Hp Hq Hrefine x y z Hpxy Hqxy Hqxz) as [Hpzy Hqzy].
  exists z, y; repeat split; assumption.
Qed.

Local Lemma split_in_tail {A} (p q : A -> A -> bool)
    (Hp : equivalence p) (Hq : equivalence q)
    (Hrefine : forall a b, q a b = true -> p a b = true) x rest :
  (exists a b, In a (x :: rest) /\ In b (x :: rest) /\
    p a b = true /\ q a b = false) ->
  existsb (q x) rest = true ->
  exists a b, In a rest /\ In b rest /\ p a b = true /\ q a b = false.
Proof.
  intros [a [b [Ha [Hb [Hpab Hqab]]]]] Hpresent.
  destruct Ha as [<-|Ha], Hb as [<-|Hb].
  - rewrite (class_refl Hq x) in Hqab; discriminate.
  - exact (split_at_head p q Hp Hq Hrefine x b rest Hb Hpab Hqab Hpresent).
  - apply (split_at_head p q Hp Hq Hrefine x a rest Ha).
    + apply (class_sym Hp); exact Hpab.
    + destruct (q x a) eqn:Hqxa; [|reflexivity].
      pose proof (class_sym Hq x a Hqxa); congruence.
    + exact Hpresent.
  - exists a, b; repeat split; assumption.
Qed.

(** A genuine split of a supported class strictly increases the finite class count. *)
Theorem classes_strict {A} (p q : A -> A -> bool) xs :
  equivalence p -> equivalence q ->
  (forall a b, q a b = true -> p a b = true) ->
  (exists a b, In a xs /\ In b xs /\ p a b = true /\ q a b = false) ->
  classes p xs < classes q xs.
Proof.
  intros Hp Hq Hrefine; induction xs as [|x rest IH]; intro Hsplit.
  - destruct Hsplit as [a [b [Ha _]]]; contradiction.
  - cbn [classes]; destruct (existsb (q x) rest) eqn:Hpresent.
    + rewrite (existsb_refines p q rest x Hrefine Hpresent).
      apply IH; exact (split_in_tail p q Hp Hq Hrefine x rest Hsplit Hpresent).
    + destruct (existsb (p x) rest) eqn:Hold.
      * pose proof (classes_mono p q rest Hrefine); lia.
      * assert (Htail : exists a b,
          In a rest /\ In b rest /\ p a b = true /\ q a b = false).
        { destruct Hsplit as [a [b [Ha [Hb [Hpab Hqab]]]]].
        destruct Ha as [<-|Ha], Hb as [<-|Hb].
        -- rewrite (class_refl Hq x) in Hqab; discriminate.
        -- assert (Htrue : existsb (p x) rest = true).
           { apply existsb_exists; exists b; split; assumption. }
           congruence.
        -- assert (Htrue : existsb (p x) rest = true).
           { apply existsb_exists; exists a; split; [exact Ha|now apply (class_sym Hp)]. }
           congruence.
        -- exists a, b; repeat split; assumption. }
        specialize (IH Htail); lia.
Qed.

End NumberingClasses.
