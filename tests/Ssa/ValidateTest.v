(** * Translation validation examples

    These examples check renamed instructions and a join parameter, including rejected copies.
    For example, a target edge may pass the renamed value just defined in its source block.
    Builds on: Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Loop.
From Galois.Base Require Import Key Trie.
From Galois.Graph Require Import Data Digraph Dom.
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
Proof.
  vm_compute; reflexivity.
Qed.

Example preserves_fuel_and_arity_observations :
  (run_with Ops.eval Ops.test 0 translated [7],
   run_with Ops.eval Ops.test 1 translated [7],
   run_with Ops.eval Ops.test 2 translated [7],
   run_with Ops.eval Ops.test 2 imperative [7],
   run_with Ops.eval Ops.test 2 translated []) =
  (Timeout, Timeout, Returned [7], Returned [7], Wrong).
Proof.
  vm_compute; reflexivity.
Qed.

Definition wrong_return : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [11]));
     (2, Block positive positive positive [12] [] (Return [10]))].

Example rejects_stale_return_value : V.check imperative wrong_return certificate = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition wrong_argument : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [99]));
     (2, Block positive positive positive [12] [] (Return [12]))].

Example rejects_unavailable_edge_argument :
  V.check imperative wrong_argument certificate = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** An arm with a mismatched destination fails before checking its target arguments. *)
Example mismatched_arm_rejected :
  let t := V.tables imperative translated certificate in
  (V.check_arm t 2 [(1, 11)] (val_set [1]) (Jump 2 []) (Jump 3 [11]) true,
   V.check_arm t 2 [(1, 11)] (val_set [1]) (Jump 2 []) (Jump 2 [11]) true) =
  (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition branch_source : Source.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []));
     (2, Block positive positive positive [] [] (Return [1]));
     (3, Block positive positive positive [] [] (Return [1]))].

Definition branch_target : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [] (Branch 1 [10] 2 [] 3 []));
     (2, Block positive positive positive [] [] (Return [10]));
     (3, Block positive positive positive [] [] (Return [10]))].

Definition branch_certificate : cert :=
  ([(1, [(1, 10)]); (2, [(1, 10)]); (3, [(1, 10)])],
   [(1, [1]); (2, [1]); (3, [1])]).

(** A branch exits early on a guard mismatch and keeps the accepted branch unchanged. *)
Example branch_exit_checks_agree :
  let t := V.tables branch_source branch_target branch_certificate in
  let ib := Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []) in
  let sb := Block positive positive positive [] [] (Branch 1 [10] 2 [] 3 []) in
  let bad := Block positive positive positive [] [] (Branch 2 [10] 2 [] 3 []) in
  (V.check branch_source branch_target branch_certificate,
   V.check_exit t 1 ib sb [(1, 10)], V.check_exit t 1 ib bad [(1, 10)],
   V.check_exit_ref t 1 ib sb [(1, 10)], V.check_exit_ref t 1 ib bad [(1, 10)]) =
  (true, true, false, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Reused exit tables preserve both branch and return blocks. *)
Example shared_exit_tables_agree :
  let t := V.tables branch_source branch_target branch_certificate in
  (map (V.check_block t) [1; 2; 3], map (V.check_block_ref t) [1; 2; 3]) =
  ([true; true; true], [true; true; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_clobbered_live_renaming :
  V.check_code [(1, 1, [1])] [(20, 1, [10])] [(1, 10); (2, 20)] [1; 2] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example accepts_strict_ssa : V.check_ssa translated = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition cross_block : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return [11]))].

Example accepts_dominating_definition : V.check_ssa cross_block = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition use_before_definition : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [(11, 1, [11])] (Return [11]))].

Example rejects_self_use : V.check_ssa use_before_definition = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_duplicate_definition : V.check_ssa imperative = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** Sharing preparation preserves both an accepted and a rejected SSA check. *)
Example shared_preparation_agrees :
  (V.check_ssa translated, V.check_ssa use_before_definition) =
  (V.check_ssa_ref translated, V.check_ssa_ref use_before_definition).
Proof.
  vm_compute; reflexivity.
Qed.

(** Locally available operands need no entries in the home or dominance tables. *)
Example local_operands_are_visible :
  let tree := DomTree Empty Empty Empty Empty in
  (V.ssa_local tree Empty 1 (val_set [10])
     [(11, 1, [10]); (12, 1, [11])] [12],
   V.ssa_local tree Empty 1 (val_set [10]) [(11, 1, [99])] [11]) =
  (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

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
Proof.
  vm_compute; reflexivity.
Qed.

(** The frozen state relation admits two environments in which a live value is absent. *)
Lemma weak_state_relation :
  W.state_sim weak_source weak_target certificate (1, [], []) (1, [], []).
Proof.
  split; [reflexivity|]; intros x Hin.
  change (1 = x \/ False) in Hin; destruct Hin as [Heq|Hfalse]; [subst x|contradiction].
  exists 10; split; reflexivity.
Qed.

(** One step and one unit of fuel separate these weakly related states, which the ready
    relation of F4 and F7 excludes. *)
Example weak_state_distinct_outcomes :
  (step Ops.eval Ops.test weak_target (1, [], []),
   step Ops.eval Ops.test weak_source (1, [], []),
   loop_fuel (step Ops.eval Ops.test weak_target) 1 (1, [], []),
   loop_fuel (step Ops.eval Ops.test weak_source) 1 (1, [], [])) =
  (inr Wrong, inl (2, [], []), inr Wrong, inl (2, [], [])).
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_program : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [] (Return []))].

Definition padded_entry (n : nat) : cert := ([(1, repeat (1, 1) n)], []).

(** Unused repeated mappings preserve the accepted empty-block behavior. *)
Example padded_entry_checker_family :
  (V.check empty_program empty_program (padded_entry 1),
   V.check empty_program empty_program (padded_entry 8)) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition padded_unused (n : nat) : cert := ([(2, repeat (1, 1) n)], []).

Definition empty_edge_program : Source.t :=
  Func positive positive positive 1 []
    [(1, Block positive positive positive [] [] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return []))].

(** Padding the certificate environment row of the edge target keeps the edge check
    accepting, and the row budget rejects the larger padding. *)
Example padded_edge_checker_and_budget_family :
  let a := padded_unused 1 in let b := padded_unused 8 in
  let ta := V.tables empty_edge_program empty_edge_program a in
  let tb := V.tables empty_edge_program empty_edge_program b in
  (V.check_edge ta 1 2 [], V.check_edge tb 1 2 [],
   V.row_budget empty_edge_program a, V.row_budget empty_edge_program b) =
  (true, true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.
