(** * Sign sets for words

    Three flags describe the possible signed classes of a word.
    For example, intersecting nonnegative and nonpositive sets leaves only zero.
    Builds on: LatticeCore and BitsWord. *)

From Stdlib Require Import Bool ZArith Lia.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord.

(** Each flag permits one signed class. *)
Record sign : Type := Sign {
  neg : bool;
  zero : bool;
  pos : bool
}.

Definition sign_le (a b : sign) : bool :=
  (negb (neg a) || neg b) && (negb (zero a) || zero b) &&
    (negb (pos a) || pos b).

Definition sign_join (a b : sign) : sign :=
  Sign (neg a || neg b) (zero a || zero b) (pos a || pos b).

Definition sign_lattice : lattice sign :=
  simple sign_le (Sign false false false) sign_join.

(** The three flags form a lattice under inclusion and union. *)
Theorem sign_lattice_laws : lattice_laws sign_lattice.
Proof.
  apply simple_laws.
  - intros [a b c]. destruct a, b, c; reflexivity.
  - intros [a b c] [d e f] [g h i]. destruct a, b, c, d, e, f, g, h, i;
      cbn; intros; try discriminate; reflexivity.
  - intros [a b c]. reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
Qed.

(** The number of permitted classes is a height bounded by three. *)
Theorem sign_height_on : height_on sign_lattice (fun _ => True).
Proof.
  refine {| rank := fun s => ((if neg s then 1 else 0) +
                                (if zero s then 1 else 0) +
                                (if pos s then 1 else 0))%nat;
            bound := 3%nat |}.
  - intros [a b c] _. destruct a, b, c; cbn; lia.
  - intros [a b c] [d e f] _ _. destruct a, b, c, d, e, f;
      cbn; intro Hle; try discriminate; lia.
  - intros [a b c] [d e f] _ _. destruct a, b, c, d, e, f;
      cbn; intro Hstrict; try discriminate; lia.
Defined.

(** A sign set permits each class inhabited by its signed word. *)
Definition sign_gamma (w : width) (s : sign) (z : Z) : Prop :=
  ((signed w z < 0)%Z -> neg s = true) /\
  ((signed w z = 0)%Z -> zero s = true) /\
  ((0 < signed w z)%Z -> pos s = true).

Definition sign_meet (a b : sign) : sign :=
  Sign (neg a && neg b) (zero a && zero b) (pos a && pos b).

(** Intersection retains any word admitted by both sign sets. *)
Theorem sign_meet_sound : forall w a b z,
  sign_gamma w a z -> sign_gamma w b z -> sign_gamma w (sign_meet a b) z.
Proof.
  intros w a b z [Hneg [Hzero Hpos]] [Hneg' [Hzero' Hpos']].
  split; [|split]; cbn [sign_meet neg zero pos]; intro Hsign;
    apply andb_true_iff; auto.
Qed.
