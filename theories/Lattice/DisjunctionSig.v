(** * Capped disjunction contracts

    Bounded lists compare by coverage and collapse excess alternatives at a fixed cap.
    For example, cap zero admits only the empty list and clips every raw input to it.
    Builds on: LatticeSig, Stdlib lists and Argent time interfaces. *)

From Stdlib Require Import List Arith NArith.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
Import List.ListNotations.

Module Type DISJUNCTION_OPS (L : LATTICE_OPS) (C : CAP).
  Include (LATTICE_OPS with Definition t :=
    {xs : list L.t | Nat.leb (length xs) C.k = true}).
  Parameter clip : list L.t -> t.
End DISJUNCTION_OPS.

Module Type DISJUNCTION_LAWS (L : LATTICE) (C : CAP)
    (Import D : DISJUNCTION_OPS L C).
  (** Order compares the projected lists by Hoare coverage. *)
  Parameter leb_spec : forall xs ys, leb xs ys = true <->
    forall x, In x (proj1_sig xs) ->
      exists y, In y (proj1_sig ys) /\ L.leb x y = true.
  (** Bottom projects to the empty list. *)
  Parameter bot_raw : proj1_sig bot = [].
  (** The bottom test recognizes exactly the empty projected list. *)
  Parameter is_bot_spec : forall xs, is_bot xs = true <-> proj1_sig xs = [].
  (** Joining clips the concatenation of the projected operands. *)
  Parameter join_clip : forall xs ys, join xs ys = clip (proj1_sig xs ++ proj1_sig ys).
  (** Clipping preserves a raw list that already fits the cap. *)
  Parameter clip_small : forall xs, length xs <= C.k -> proj1_sig (clip xs) = xs.
  (** At cap zero clipping discards every raw alternative. *)
  Parameter clip_zero : forall xs, C.k = 0 -> proj1_sig (clip xs) = [].
  (** With a positive cap clipping covers every raw alternative. *)
  Parameter clip_covers : forall xs, 0 < C.k ->
    forall x, In x xs -> exists y, In y (proj1_sig (clip xs)) /\ L.leb x y = true.
End DISJUNCTION_LAWS.

Module Type DISJUNCTION (L : LATTICE) (C : CAP) :=
  DISJUNCTION_OPS L C <+ LATTICE_LAWS <+ DISJUNCTION_LAWS L C.

Module Type DISJUNCTION_TIME (L : LATTICE_T) (J : JOIN_SIZE L) (C : CAP)
    (Import D : DISJUNCTION L C).
  Include (LATTICE_TIME D with Definition size :=
    fun (xs : t) => fold_right (fun a n => L.size a + 1 + n) 1 (proj1_sig xs)).
  Parameter T_clip : list L.t -> N.
  (** Clipping charges raw length and component sizes within twice the cap. *)
  Parameter T_clip_le : forall xs, length xs <= 2 * C.k ->
    (T_clip xs <= c_lat * N.of_nat
      (length xs + fold_right (fun a n => L.size a + n) 0 xs + 1)%nat)%N.
  (** A join has size bounded by the sizes of its operands. *)
  Parameter join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
End DISJUNCTION_TIME.

Module Type DISJUNCTION_T (L : LATTICE_T) (J : JOIN_SIZE L) (C : CAP) :=
  DISJUNCTION L C <+ DISJUNCTION_TIME L J C.

Module Type DISJUNCTION_ALL (L : LATTICE_T) (J : JOIN_SIZE L) (C : CAP) :=
  DISJUNCTION_T L J C.
