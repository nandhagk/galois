(** * Map lattices

    Sparse environments use explicit defaults for absent keys.
    For example, joining top-default maps drops a binding present on one side.
    Builds on: LatticeSig and MapSig. *)

From Stdlib Require Import Bool List Arith NArith Lia.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.

Module MapLatticeCode (K : KEY_OPS) (M : MAP_OPS K) (L : LATTICE_OPS)
    <: LATTICE_OPS.
  Definition t := M.t L.t.
  Definition default (x : option L.t) : L.t :=
    match x with Some a => a | None => L.bot end.
  Definition leb (x y : t) : bool :=
    M.forall2b (fun a b =>
      L.leb (match a with Some v => v | None => L.bot end)
        (match b with Some v => v | None => L.bot end)) x y.
  Definition bot : t := M.empty.
  Definition is_bot (x : t) : bool := negb (M.existsb (fun a => negb (L.is_bot a)) x).
  Definition join (x y : t) : t :=
    M.merge (fun a b =>
      match a, b with
      | None, None => None
      | Some a, None => Some a
      | None, Some b => Some b
      | Some a, Some b => Some (L.join a b)
      end) x y.
End MapLatticeCode.

Module MapLattice (K : KEY) (M : MAP K) (L : LATTICE) <: LATTICE.
  Include MapLatticeCode K M L.
  Definition read (m : t) (k : positive) := default (M.find k m).
  Lemma leb_read : forall a b, leb a b = true <-> forall k, L.leb (read a k) (read b k) = true.
  Proof.
    intros a b; unfold leb, read.
    apply M.forall2b_spec; cbn [default]; apply L.leb_refl.
  Qed.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply leb_read; intro k; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc; apply leb_read; intro k.
    eapply L.leb_trans; [apply (proj1 (leb_read a b) Hab)|apply (proj1 (leb_read b c) Hbc)].
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a; apply leb_read; intro k; unfold read, bot; rewrite M.find_empty; apply L.bot_least.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b; apply leb_read; intro k; unfold read, join.
    rewrite M.find_merge by reflexivity.
    destruct (M.find k a), (M.find k b); cbn [default];
      try apply L.leb_refl; try apply L.bot_least; apply L.join_ub_l.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b; apply leb_read; intro k; unfold read, join.
    rewrite M.find_merge by reflexivity.
    destruct (M.find k a), (M.find k b); cbn [default];
      try apply L.leb_refl; try apply L.bot_least; apply L.join_ub_r.
  Qed.
End MapLattice.

Module MapLatticeT (K : KEY_T) (M : MAP_T K) (L : LATTICE_T) <: LATTICE_T.
  Include MapLattice K M L.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (m : t) : nat :=
    M.fold (fun acc _ a => acc + L.size a) m 1.
  Definition c_lat : N := 1. (* STUB *)
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End MapLatticeT.
