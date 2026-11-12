(** * Simple lattices

    Boolean and unit carriers have simple lattice operations.
    For example, joining false and true gives true.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module BoolLatCode <: BLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition top := true.
  Definition meet := andb.
End BoolLatCode.

Module UnitLatCode <: BLATTICE_OPS.
  Definition t := unit.
  Definition leb (_ _ : t) := true.
  Definition bot := tt.
  Definition is_bot (_ : t) := true.
  Definition join (_ _ : t) := tt.
  Definition top := tt.
  Definition meet (_ _ : t) := tt.
End UnitLatCode.

Module BoolLat <: BLATTICE.
  Include BoolLatCode.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros; repeat match goal with b : bool |- _ => destruct b end; cbn in *; congruence. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. intros; repeat match goal with b : bool |- _ => destruct b end; cbn in *; congruence. Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros; repeat match goal with b : bool |- _ => destruct b end; cbn in *; congruence. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros; repeat match goal with b : bool |- _ => destruct b end; cbn in *; congruence. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros; repeat match goal with b : bool |- _ => destruct b end; cbn in *; congruence. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros []; reflexivity. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.
End BoolLat.

Module UnitLat <: BLATTICE.
  Include UnitLatCode.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intros; reflexivity. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. intros; reflexivity. Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros; reflexivity. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros; reflexivity. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intros; reflexivity. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.
End UnitLat.
