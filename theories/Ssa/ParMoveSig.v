(** * Checked sequentialisation of parallel moves

    A move producer may use a fresh temporary to break cycles, and a checker validates its result.
    For example, swapping two variables requires saving one value before overwriting its source.
    Builds on: Stdlib lists and binary identifiers, and Argent. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.

Import List.ListNotations.

Definition moves := list (positive * positive).

Fixpoint exec_par {A} (par : moves) (env : positive -> option A) (x : positive) : option A :=
  match par with
  | [] => env x
  | (dst, src) :: rest => if Pos.eqb x dst then env src else exec_par rest env x
  end.
TimeFun exec_par.

Fixpoint exec_seq {A} (sq : moves) (env : positive -> option A) (x : positive) : option A :=
  match sq with
  | [] => env x
  | (dst, src) :: rest =>
    exec_seq rest (fun y => if Pos.eqb y dst then env src else env y) x
  end.
TimeFun exec_seq.

Module Nat.
  TimeFun Nat.max.
End Nat.

Definition bits_of (par : moves) : nat :=
  fold_right (fun move w => Nat.max (Pos.size_nat (fst move))
    (Nat.max (Pos.size_nat (snd move)) w)) 0 par.
TimeFun bits_of.

Module Type PARMOVE_OPS.
  Parameter seq : moves -> positive -> moves.
  Parameter check_moves : moves -> positive -> moves -> bool.
End PARMOVE_OPS.

Module Type PARMOVE_LAWS (Import P : PARMOVE_OPS).
  (** Accepted sequences agree with simultaneous assignment outside the fresh temporary. *)
  Parameter check_moves_sound : forall par tmp sq,
    NoDup (map fst par) -> ~ In tmp (map fst par ++ map snd par) ->
    check_moves par tmp sq = true -> forall A (env : positive -> option A) x,
      x <> tmp -> exec_seq sq env x = exec_par par env x.
  (** Sequentialisation emits at most twice the number of parallel moves. *)
  Parameter seq_length : forall par tmp, length (seq par tmp) <= 2 * length par.
  (** Emitted moves write parallel destinations or the temporary and read sources or it. *)
  Parameter seq_ids : forall par tmp m, In m (seq par tmp) ->
    (In (fst m) (map fst par) \/ fst m = tmp) /\
    (In (snd m) (map snd par) \/ snd m = tmp).
End PARMOVE_LAWS.

Module Type PARMOVE := PARMOVE_OPS <+ PARMOVE_LAWS.

Module Type PARMOVE_TIME (Import P : PARMOVE).
  Parameter T_seq : moves -> positive -> N.
  Parameter T_check_moves : moves -> positive -> moves -> N.
  Parameter c_pm : N.
  (** The move producer pays for the parallel assignment at its identifier width. *)
  Parameter T_seq_le : forall par tmp,
    (T_seq par tmp <= c_pm * N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  (** Checking pays for the source and proposed sequence at their identifier width. *)
  Parameter T_check_moves_le : forall par tmp sq,
    (T_check_moves par tmp sq <= c_pm * N.of_nat (length par + length sq + 1) *
      N.of_nat (bits_of (par ++ sq) + 1))%N.
End PARMOVE_TIME.

Module Type PARMOVE_T := PARMOVE <+ PARMOVE_TIME.

Module Type PARMOVE_PLAN (Import P : PARMOVE_T).
  Parameter symbolic_all : moves -> ptrie positive.
  Parameter T_symbolic_all : moves -> N.
  Parameter symbolic : moves -> positive -> option positive.
  Parameter k_symbolic k_cycle : N.
  Parameter cycle_search : moves -> list positive.
  Parameter T_cycle_search : moves -> N.
  (** Every cycle representative is a distinct parallel destination. *)
  Parameter F0_cycle_search : forall par,
    NoDup (cycle_search par) /\ forall x, In x (cycle_search par) -> In x (map fst par).
  (** Cycle search visits each move at its identifier width. *)
  Parameter T0_cycle_search : forall par,
    (T_cycle_search par <= k_cycle * N.of_nat (length par + 1) *
      N.of_nat (bits_of par + 1))%N.
  Definition relevant (par sq : moves) := map fst par ++ map snd par ++ map fst sq ++ map snd sq.
  (** One pass records the original source of every written variable. *)
  Parameter F1_symbolic_all : forall sq x,
    exec_seq sq (@Some positive) x =
      match trie_get x (symbolic_all sq) with Some y => Some y | None => Some x end.
  (** Symbolic execution records the original variable supplying each final value. *)
  Parameter F1_symbolic : forall sq x, symbolic sq x = exec_seq sq (@Some positive) x.
  (** Acceptance compares symbolic values at every affected non-temporary variable. *)
  Parameter F2_check_symbolic : forall par tmp sq, check_moves par tmp sq = true ->
    forall x, In x (relevant par sq) -> x <> tmp ->
      symbolic sq x = exec_par par (@Some positive) x.
  (** Variables outside the affected set keep their initial symbolic values. *)
  Parameter F3_unaffected : forall par sq x, ~ In x (relevant par sq) ->
    exec_seq sq (@Some positive) x = Some x /\ exec_par par (@Some positive) x = Some x.
  (** Symbolic agreement transports to every option-valued environment. *)
  Parameter F4_symbolic_transport : forall par sq x,
    exec_seq sq (@Some positive) x = exec_par par (@Some positive) x ->
    forall A (env : positive -> option A), exec_seq sq env x = exec_par par env x.
  (** The table pass charges each move at the sequence width. *)
  Parameter T1_symbolic_all : forall sq,
    (T_symbolic_all sq <= k_symbolic * N.of_nat (length sq + 1) *
      N.of_nat (bits_of sq + 1))%N.
  (** Sequentialisation charges cycle discovery and indexed move emission. *)
  Parameter T1_seq : forall par tmp,
    (T_seq par tmp <= T_cycle_search par + k_cycle *
      N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  (** Checking builds two tables and compares them on the relevant variables. *)
  Parameter T2_check : forall par tmp sq,
    (T_check_moves par tmp sq <= T_symbolic_all sq + k_symbolic *
      N.of_nat (length par + length sq + 1) * N.of_nat (bits_of (par ++ sq) + 1))%N.
End PARMOVE_PLAN.

Module Type PARMOVE_ALL := PARMOVE_T <+ PARMOVE_PLAN.
