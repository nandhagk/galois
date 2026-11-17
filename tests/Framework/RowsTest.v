(** * Ordered prepared row observations

    Explicit query frames retain the order of a row's two reads.
    For example, reversing the read order changes checker acceptance.

    Groups:
    - Reads: a row accepts the values it reads in order and rejects them reversed.
    - Empty: a system without rows accepts any values.
    - Constant: a row whose target is false rejects the empty candidate.

    Builds on: Fixpoint.Query and Fixpoint.Check. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import Key Trie.
From Galois.Fixpoint Require Import Query SystemSig Check.
Import List.ListNotations.

(** * Fixtures *)

(** Booleans ordered by implication, with false as bottom and or as join. *)
Module BoolOps.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
End BoolOps.

(** A system with one row, whose two reads are true and then the answer of the first read. *)
Module Rows <: SYSTEM_OPS BoolOps.
  Definition prog := option bool.
  Definition key := bool.
  Definition row := unit.
  Definition frame := (bool * option bool)%type.
  Definition key_code := BoolKeyCode.encode.
  Definition key_eqb := Bool.eqb.
  Definition rows (p : prog) := match p with None => [] | _ => [tt] end.
  Definition target (_ : prog) (_ : unit) := true.
  Definition start (p : prog) (_ : unit) : query bool bool frame :=
    match p with Some false => Ask false (true, None) | _ => Ask true (false, None) end.
  Definition resume (_ : prog) (f : frame) (a : bool) : query bool bool frame :=
    match snd f with
    | None => Ask (fst f) (false, Some a)
    | Some x => Ret (andb x (negb a))
    end.
  Definition deps (_ : prog) (_ : unit) := [true; false].
  Definition sides (_ : prog) (_ : unit) : list bool := [].
End Rows.

Module C := CheckCode BoolOps Rows.

(** The candidate that maps false to the pair (false, true) and no other key. *)
Definition values := PTrieCode.set (Rows.key_code false) (false, true) PTrieCode.empty.

(** * Reads *)

Module ReadTests.

  (** The row with the reads in their stated order is accepted by the candidate. *)
  Example ordered_reads_accepted : C.check (Some true) values = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The row with the reads reversed is rejected by the same candidate. *)
  Example reversed_reads_rejected : C.check (Some false) values = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ReadTests.

(** * Empty *)

Module EmptyTests.

  (** A program without rows is accepted by the candidate. *)
  Example no_rows_accepted : C.check None values = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End EmptyTests.

(** * Constant *)

Module ConstantTests.

  (** A system whose only row has target false rejects the empty candidate. *)
  Module Constant <: SYSTEM_OPS BoolOps.
    Definition prog := unit.
    Definition key := bool.
    Definition row := unit.
    Definition frame := unit.
    Definition key_code := BoolKeyCode.encode.
    Definition key_eqb := Bool.eqb.
    Definition rows (_ : unit) := [tt].
    Definition target (_ : unit) (_ : unit) := false.
    Definition start (_ : unit) (_ : unit) : query bool bool unit := Ret true.
    Definition resume (_ : unit) (_ : unit) (a : bool) : query bool bool unit := Ret a.
    Definition deps (_ : unit) (_ : unit) : list bool := [].
    Definition sides (_ : unit) (_ : unit) : list bool := [].
  End Constant.

  Module CC := CheckCode BoolOps Constant.

  (** The empty candidate fails the constant row. *)
  Example constant_row_rejects_empty : CC.check tt PTrieCode.empty = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ConstantTests.
