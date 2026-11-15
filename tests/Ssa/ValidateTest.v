(** * Translation validation examples

    These examples check renamed instructions and a join parameter, including rejected copies.
    For example, a target edge may pass the renamed value just defined in its source block.
    Builds on: Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Key.
From Galois.Graph Require Import Digraph Dom.
From Galois.Ssa Require Import Lang LiveSig ValidateSig Validate Present.
Import List.ListNotations.
Open Scope positive_scope.

Module Ops <: OPS.
  Definition K := positive.
  Definition G := positive.
  Definition C := positive.
  Definition eval (_ : positive) (values : list positive) : option positive := hd_error values.
  Definition test (_ : positive) (values : list positive) : option bool :=
    match values with [] => None | x :: _ => Some (Pos.eqb x 1) end.
  Definition mov := 1.
End Ops.

Module Source.
  Definition t := func positive positive positive.
End Source.
Module View := PresentT Ops PosKeyT PosKeyT.
Module V := ValidateCode Ops PosKeyCode PosKeyCode Source View.Q View.R BlockEdge
  View.BC View.S DigraphCode DomCode.

Definition imperative : Source.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [(1, 1, [1])] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return [1]))].

Definition translated : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [11]));
     (2, Block positive positive positive [12] [] (Return [12]))].

Definition certificate : cert :=
  ([(1, [(1, 10)]); (2, [(1, 12)])], [(1, [1]); (2, [1])]).

Example accepts_instruction_and_parameter_renaming :
  V.check imperative translated certificate = true.
Proof. vm_compute; reflexivity. Qed.

Example preserves_fuel_and_arity_observations :
  (run_with Ops.eval Ops.test 0 translated [7],
   run_with Ops.eval Ops.test 1 translated [7],
   run_with Ops.eval Ops.test 2 translated [7],
   run_with Ops.eval Ops.test 2 imperative [7],
   run_with Ops.eval Ops.test 2 translated []) =
  (Timeout, Timeout, Returned [7], Returned [7], Wrong).
Proof. vm_compute; reflexivity. Qed.

Definition wrong_return : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [11]));
     (2, Block positive positive positive [12] [] (Return [10]))].

Example rejects_stale_return_value : V.check imperative wrong_return certificate = false.
Proof. vm_compute; reflexivity. Qed.

Definition wrong_argument : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [99]));
     (2, Block positive positive positive [12] [] (Return [12]))].

Example rejects_unavailable_edge_argument :
  V.check imperative wrong_argument certificate = false.
Proof. vm_compute; reflexivity. Qed.

Example rejects_clobbered_live_renaming :
  V.check_code [(1, 1, [1])] [(20, 1, [10])] [(1, 10); (2, 20)] [1; 2] = None.
Proof. vm_compute; reflexivity. Qed.
