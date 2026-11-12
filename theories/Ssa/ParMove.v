(** * Placeholder parallel move sequentialisation

    These operations provide the interfaces for a move producer and its checker.
    For example, the placeholder producer returns an empty sequence.
    Builds on: ParMoveSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Ssa Require Import ParMoveSig.

Import List.ListNotations.

Module ParMoveCode <: PARMOVE_OPS.
  (* STUB-CODE *)
  Definition seq (_ : moves) (_ : positive) : moves := [].
  (* STUB-CODE *)
  Definition check_moves (_ : moves) (_ : positive) (_ : moves) : bool := false.
End ParMoveCode.

Module ParMove <: PARMOVE.
  Include ParMoveCode.

  Lemma check_moves_sound : forall par tmp sq,
    NoDup (map fst par) -> ~ In tmp (map fst par ++ map snd par) ->
    check_moves par tmp sq = true -> forall A (env : positive -> option A) x,
      x <> tmp -> exec_seq sq env x = exec_par par env x.
  Proof. Admitted.
  Lemma seq_length : forall par tmp, length (seq par tmp) <= 2 * length par.
  Proof. Admitted.
End ParMove.

Module ParMoveT <: PARMOVE_ALL.
  Include ParMove.
  TimeFun seq.
  TimeFun check_moves.
  Definition c_pm : N := 1. (* STUB *)
  Lemma T_seq_le : forall par tmp,
    (T_seq par tmp <= c_pm * N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_moves_le : forall par tmp sq,
    (T_check_moves par tmp sq <= c_pm * N.of_nat (length par + length sq + 1) *
      N.of_nat (bits_of (par ++ sq) + 1))%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition symbolic (_ : moves) (_ : positive) : option positive := None.
  TimeFun symbolic.
  Definition k_symbolic : N := 1. (* STUB *)
  Definition relevant (par sq : moves) := map fst par ++ map snd par ++ map fst sq ++ map snd sq.
  Lemma F1_symbolic : forall sq x, symbolic sq x = exec_seq sq (@Some positive) x.
  Proof. Admitted. (* STUB *)
  Lemma F2_check_symbolic : forall par tmp sq, check_moves par tmp sq = true ->
    forall x, In x (relevant par sq) -> x <> tmp ->
      symbolic sq x = exec_par par (@Some positive) x.
  Proof. Admitted. (* STUB *)
  Lemma F3_unaffected : forall par sq x, ~ In x (relevant par sq) ->
    exec_seq sq (@Some positive) x = Some x /\ exec_par par (@Some positive) x = Some x.
  Proof. Admitted. (* STUB *)
  Lemma F4_symbolic_transport : forall par sq x,
    exec_seq sq (@Some positive) x = exec_par par (@Some positive) x ->
    forall A (env : positive -> option A), exec_seq sq env x = exec_par par env x.
  Proof. Admitted. (* STUB *)
  Lemma T1_seq : forall par tmp,
    (T_seq par tmp <= c_pm * N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_check : forall par tmp sq,
    (T_check_moves par tmp sq <= c_pm * N.of_nat (length par + length sq + 1) *
      N.of_nat (bits_of (par ++ sq) + 1))%N.
  Proof. Admitted. (* STUB *)
End ParMoveT.
