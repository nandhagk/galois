(** * Self-delimiting positive codes

    Codes combine injective positive encodings of structured keys.
    For example, an optional value uses a low zero bit and absence uses 1.
    Builds on: Stdlib binary arithmetic and Argent time derivation. *)

From Stdlib Require Import NArith PArith List.
From Argent Require Import Time Std.
Module List.
  TimeFun flat_map.
End List.

Fixpoint glue (a b : positive) : positive :=
  match a with
  | xH => xO b
  | xO a' => xI (xO (glue a' b))
  | xI a' => xI (xI (glue a' b))
  end.

TimeFun glue.

Definition pair_code {A B} (fa : A -> positive) (fb : B -> positive) (x : A * B)
    : positive := glue (fa (fst x)) (fb (snd x)).

TimeFun pair_code.

Definition sum_code {A B} (fa : A -> positive) (fb : B -> positive) (x : A + B)
    : positive :=
  match x with
  | inl a => xO (fa a)
  | inr b => xI (fb b)
  end.

TimeFun sum_code.

Definition option_code {A} (f : A -> positive) (x : option A) : positive :=
  match x with
  | None => xH
  | Some a => xO (f a)
  end.

TimeFun option_code.

Fixpoint list_code {A} (f : A -> positive) (l : list A) : positive :=
  match l with
  | nil => xH
  | x :: r => glue (f x) (list_code f r)
  end.

TimeFun list_code.

(** Equal glued codes identify both components. *)
Lemma glue_inj : forall a b a' b', glue a b = glue a' b' -> a = a' /\ b = b'.
Proof. Admitted.

(** Gluing doubles the first component's bits apart from its final delimiter. *)
Lemma glue_bits : forall a b,
  Pos.size_nat (glue a b) = 2 * Pos.size_nat a + Pos.size_nat b - 1.
Proof. Admitted.

Definition c_glue : N := 1. (* STUB *)

(** Gluing takes time bounded by the first component's bit length. *)
Lemma T_glue_le : forall a b, (T_glue a b <= c_glue * N.of_nat (Pos.size_nat a + 1))%N.
Proof. Admitted. (* STUB *)
