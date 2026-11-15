(** * Translation validation examples

    These examples check renamed instructions and a join parameter, including rejected copies.
    For example, a target edge may pass the renamed value just defined in its source block.
    Builds on: Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Loop.
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

Example accepts_strict_ssa : V.check_ssa translated = true.
Proof. vm_compute; reflexivity. Qed.

Definition cross_block : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return [11]))].

Example accepts_dominating_definition : V.check_ssa cross_block = true.
Proof. vm_compute; reflexivity. Qed.

Definition use_before_definition : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [(11, 1, [11])] (Return [11]))].

Example rejects_self_use : V.check_ssa use_before_definition = false.
Proof. vm_compute; reflexivity. Qed.

Example rejects_duplicate_definition : V.check_ssa imperative = false.
Proof. vm_compute; reflexivity. Qed.

Module W := Validate Ops PosKey PosKey Source View.Q View.R BlockEdge
  View.BC View.S Digraph Dom View.Link.

Definition weak_source : Source.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return [1]))].

Definition weak_target : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [] (Jump 2 [10]));
     (2, Block positive positive positive [12] [] (Return [12]))].

Example weak_state_translation_accepted : W.check weak_source weak_target certificate = true.
Proof. vm_compute; reflexivity. Qed.

(** The frozen state relation admits two environments in which a live value is absent. *)
Example weak_state_relation :
  W.state_sim weak_source weak_target certificate (1, [], []) (1, [], []).
Proof.
  split; [reflexivity|]; intros x Hin.
  change (1 = x \/ False) in Hin; destruct Hin as [Heq|Hfalse]; [subst x|contradiction].
  exists 10; split; reflexivity.
Qed.

(** This is the one-step counterexample to F4 and the fuel-one counterexample to F7. *)
Example weak_state_distinct_outcomes :
  (step Ops.eval Ops.test weak_target (1, [], []),
   step Ops.eval Ops.test weak_source (1, [], []),
   loop_fuel (step Ops.eval Ops.test weak_target) 1 (1, [], []),
   loop_fuel (step Ops.eval Ops.test weak_source) 1 (1, [], [])) =
  (inr Wrong, inl (2, [], []), inr Wrong, inl (2, [], [])).
Proof. vm_compute; reflexivity. Qed.

Module WT := ValidateT Ops PosKeyT PosKeyT Source View.Q View.R BlockEdge
  View.BC View.S DigraphT DomT View.Link.

Definition empty_program : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [] (Return []))].

Definition padded_entry (n : nat) : cert := ([(1, repeat (1, 1) n)], []).

(** Repeated unused mappings cost work even though the entry and block plan sizes are fixed. *)
Example padded_entry_time_family :
  let a := padded_entry 1 in let b := padded_entry 8 in
  let ta := WT.tables empty_program empty_program a in
  let tb := WT.tables empty_program empty_program b in
  (WT.check empty_program empty_program a,
   WT.check empty_program empty_program b,
   Nat.eqb (WT.check_width empty_program empty_program a)
     (WT.check_width empty_program empty_program b),
   N.ltb (WT.T_check_entry empty_program empty_program a ta)
     (WT.T_check_entry empty_program empty_program b tb),
   N.ltb (WT.T_check_block ta 1) (WT.T_check_block tb 1)) =
  (true, true, true, true, true).
Proof. vm_compute; reflexivity. Qed.

Definition padded_unused (n : nat) : cert := ([(2, repeat (1, 1) n)], []).

(** The entry phase also accounts for inspecting rows unused by executable blocks. *)
Example unused_row_time_family :
  let a := padded_unused 1 in let b := padded_unused 8 in
  let ta := WT.tables empty_program empty_program a in
  let tb := WT.tables empty_program empty_program b in
  (N.eqb (WT.T_tables empty_program empty_program a)
     (WT.T_tables empty_program empty_program b),
   N.ltb (WT.T_check_entry empty_program empty_program a ta)
     (WT.T_check_entry empty_program empty_program b tb),
   N.eqb (WT.T_check_block ta 1) (WT.T_check_block tb 1),
   N.ltb (WT.T_check empty_program empty_program a)
     (WT.T_check empty_program empty_program b)) =
  (true, true, true, true).
Proof. vm_compute; reflexivity. Qed.

Definition empty_edge_program : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return []))].

(** A target environment row is absent from the edge plan's size expression. *)
Example padded_edge_time_family :
  let a := padded_unused 1 in let b := padded_unused 8 in
  let ta := WT.tables empty_edge_program empty_edge_program a in
  let tb := WT.tables empty_edge_program empty_edge_program b in
  (WT.check_edge ta 1 2 [], WT.check_edge tb 1 2 [],
   N.ltb (WT.T_check_edge ta 1 2 []) (WT.T_check_edge tb 1 2 []),
   WT.row_budget empty_edge_program a, WT.row_budget empty_edge_program b) =
  (true, true, true, true, false).
Proof. vm_compute; reflexivity. Qed.
