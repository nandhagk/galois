(** * Ordered prepared row observations

    Explicit query frames retain the order of a row's two reads.
    For example, reversing the read order changes checker acceptance.
    Builds on: Fixpoint.Query and Fixpoint.Check. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import Key Trie.
From Galois.Fixpoint Require Import Query SystemSig Check.
Import List.ListNotations.
Module BoolOps.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
End BoolOps.

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
Definition values := PTrieCode.set (Rows.key_code false) (false, true) PTrieCode.empty.

Example ordered_row_accepts : C.check (Some true) values = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reversed_row_rejects : C.check (Some false) values = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows : C.check None values = true.
Proof.
  vm_compute; reflexivity.
Qed.

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

Example constant_row_rejects_bottom : CC.check tt PTrieCode.empty = false.
Proof.
  vm_compute; reflexivity.
Qed.

(* arbitrary_reader_reflection quantified over the retired Rows.t closure record.
   SYSTEM_SPEC.post_solution now specifies the query evaluator directly.
   The old empty_rows was universal in the reader and assignment. This executable
   empty inventory retains its acceptance observation without claiming that theorem. *)
