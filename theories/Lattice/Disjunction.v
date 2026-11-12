(** * Capped disjunction lattices

    Lists denote unions and compare by coverage of every alternative.
    For example, cap one collapses two incomparable flat values to their top.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Argent Require Import Time Std.
From Galois.Lattice Require Import LatticeSig.
Import List.ListNotations.

Definition cap_predecessor (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => k
  end.

TimeFun cap_predecessor.

Module DisjunctionCode (L : LATTICE_OPS) (C : CAP) <: LATTICE_OPS.
  Definition t := list L.t.
  Definition leb (xs ys : t) := forallb (fun x => existsb (L.leb x) ys) xs.
  Definition bot : t := [].
  Definition is_bot (xs : t) := match xs with [] => true | _ => false end.
  Definition join_all (xs : t) : L.t :=
    match xs with
    | [] => L.bot
    | x :: rest => fold_left L.join rest x
    end.
  Fixpoint compact_tail (n : nat) (xs : t) : t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [join_all xs]
    end.
  Definition compact (xs : t) :=
    if Nat.leb (length xs) C.k then xs else compact_tail (cap_predecessor C.k) xs.
  Definition join (xs ys : t) := compact (xs ++ ys).
End DisjunctionCode.

Module Disjunction (L : LATTICE) (C : CAP) <: LATTICE.
  Include DisjunctionCode L C.

  Lemma leb_spec xs ys : leb xs ys = true <->
    forall x, In x xs -> exists y, In y ys /\ L.leb x y = true.
  Proof.
    unfold leb. rewrite forallb_forall.
    split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
  Qed.

  Lemma leb_refl xs : leb xs xs = true.
  Proof.
    apply leb_spec; intros x Hin; exists x; split; [exact Hin | apply L.leb_refl].
  Qed.

  Lemma leb_trans xs ys zs : leb xs ys = true -> leb ys zs = true -> leb xs zs = true.
  Proof.
    rewrite !leb_spec; intros Hxy Hyz x Hin.
    destruct (Hxy x Hin) as [y [Hy Hle]], (Hyz y Hy) as [z [Hz Hle']].
    exists z; split; [exact Hz | eapply L.leb_trans; eassumption].
  Qed.

  Lemma bot_least xs : leb bot xs = true.
  Proof. reflexivity. Qed.

  Lemma is_bot_bot : is_bot bot = true.
  Proof. reflexivity. Qed.

  Lemma is_bot_least xs ys : is_bot xs = true -> leb xs ys = true.
  Proof. destruct xs; cbn; congruence. Qed.

  Local Lemma fold_upper_start xs a : L.leb a (fold_left L.join xs a) = true.
  Proof.
    revert a; induction xs as [|x xs IH]; intro a; cbn.
    - apply L.leb_refl.
    - eapply L.leb_trans; [apply L.join_ub_l | apply IH].
  Qed.

  Local Lemma fold_upper_member xs a x : In x xs ->
    L.leb x (fold_left L.join xs a) = true.
  Proof.
    revert a; induction xs as [|y xs IH]; intros a Hin; cbn in *; [contradiction |].
    destruct Hin as [<- | Hin].
    - eapply L.leb_trans; [apply L.join_ub_r | apply fold_upper_start].
    - apply IH; exact Hin.
  Qed.

  Lemma join_all_upper xs x : In x xs -> L.leb x (join_all xs) = true.
  Proof.
    destruct xs as [|a xs]; cbn; intro Hin; [contradiction |].
    destruct Hin as [<- | Hin]; auto using fold_upper_start, fold_upper_member.
  Qed.

  Local Lemma compact_tail_equation n xs :
    compact_tail n xs = firstn n xs ++ [join_all (skipn n xs)].
  Proof.
    revert xs; induction n as [|n IH]; intros [|x xs]; cbn; auto.
    now rewrite IH.
  Qed.

  Lemma compact_covers xs : leb xs (compact xs) = true.
  Proof.
    unfold compact; destruct (Nat.leb (length xs) C.k); [apply leb_refl |].
    rewrite compact_tail_equation. apply leb_spec; intros x Hin.
    rewrite <- (firstn_skipn (cap_predecessor C.k) xs) in Hin; apply in_app_iff in Hin.
    destruct Hin as [Hp | Hs].
    - exists x; split; [apply in_app_iff; auto | apply L.leb_refl].
    - exists (join_all (skipn (cap_predecessor C.k) xs)); split.
      + apply in_app_iff; right; now left.
      + apply join_all_upper; exact Hs.
  Qed.

  Local Lemma append_covers xs ys : leb xs (xs ++ ys) = true /\ leb ys (xs ++ ys) = true.
  Proof.
    split; apply leb_spec; intros x Hin; exists x; split;
      try apply L.leb_refl; apply in_app_iff; auto.
  Qed.

  Lemma join_ub_l xs ys : leb xs (join xs ys) = true.
  Proof.
    unfold join. eapply leb_trans; [exact (proj1 (append_covers xs ys)) | apply compact_covers].
  Qed.

  Lemma join_ub_r xs ys : leb ys (join xs ys) = true.
  Proof.
    unfold join. eapply leb_trans; [exact (proj2 (append_covers xs ys)) | apply compact_covers].
  Qed.
End Disjunction.

Module DisjunctionT (L : LATTICE_T) (J : JOIN_SIZE L) (C : CAP).
  Include Disjunction L C.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join_all.
  TimeFun compact_tail.
  TimeFun compact.
  TimeFun join.
End DisjunctionT.
