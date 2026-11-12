(** * Word language observations

    These examples run word operations through the tagged constant harness.
    For example, adding two 32-bit singleton words yields a singleton two.
    Builds on: BitsLang, Tagged and Harness. *)

From Stdlib Require Import List ZArith.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig Const ConstSig Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Payload := ConstWordCode WordLanguageCode.
Module Table := ConstWordTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Definition p (w : positive) (z : Z) := TVal w (FVal z).

Example bridge_arithmetic :
  Domain.forward (BOp bvadd) [p 32 1; p 32 1] = p 32 2.
Proof. vm_compute. reflexivity. Qed.
Example truth_positive : Domain.guard (BTruth true) [p 32 7] = [p 32 7].
Proof. vm_compute. reflexivity. Qed.
Example truth_boundary : Domain.guard (BTruth false) [p 1 0] = [p 1 0].
Proof. vm_compute. reflexivity. Qed.
Example truth_unknown_width : Domain.guard (BTruth true) [TAny] = [TAny].
Proof. vm_compute. reflexivity. Qed.
Example false_unknown_width : Domain.guard (BTruth false) [TAny] = [TAny].
Proof. vm_compute. reflexivity. Qed.
Example malformed_guard_arity :
  Domain.guard (BTruth true) [p 1 0; p 32 0] = [p 1 0; p 32 0].
Proof. vm_compute. reflexivity. Qed.
Example malformed_expression_bottom : Domain.forward (BOp bvadd) [p 32 1] = TBot.
Proof. vm_compute. reflexivity. Qed.
Example point_wrap_boundary : Payload.pconst 1%positive 2 = FVal 0.
Proof. vm_compute. reflexivity. Qed.

(* The old truth_rejected expected [TBot] for a zero input. The current guard table
   leaves the same input unchanged as [p 32 0].
Example truth_rejected : Domain.guard (BTruth true) [p 32 0] = [TBot].
Proof. vm_compute. reflexivity. Qed.
*)

Example point_empty_operand :
  Domain.forward (BOp bvadd) [TVal 1%positive FBot] = TBot.
Proof. vm_compute. reflexivity. Qed.
