(** * Translation validation examples

    These examples check renamed instructions and a join parameter, including rejected copies.
    For example, a target edge may pass the renamed value just defined in its source block.

    Groups:
    - [CheckTests] The checker on renamed instructions, arguments and arms.
    - [FuelTests] The observations of the renamed program at each fuel.
    - [BranchTests] The exit checks of a branch.
    - [ScanTests] The scan of bindings, with shadowed and overwritten locals.
    - [ExitTests] The exit tables after a local is overwritten.
    - [SsaTests] The strict SSA check and the local operands.
    - [WeakTests] A weakly related state pair.
    - [PaddingTests] Padded certificates and the row budget.

    Builds on: Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Loop.
From Galois.Base Require Import Key Trie.
From Galois.Graph Require Import Data Digraph Dom.
From Galois.Ssa Require Import Lang LiveSig ValidateSig Validate Present.
Import List.ListNotations.
Open Scope positive_scope.

(** * Fixtures *)

(** The test operations on positive values: an evaluation that returns the first operand. *)
Module Ops <: OPS.
  Definition K := positive.
  Definition G := positive.
  Definition C := positive.
  Definition eval (_ : positive) (values : list positive) : option positive := hd_error values.
  Definition test (_ : positive) (values : list positive) : option bool :=
    match values with [] => None | x :: _ => Some (Pos.eqb x 1) end.
  Definition mov := 1.
End Ops.

(** The source functions of the examples. *)
Module Source.
  Definition t := func positive positive positive.
End Source.

(** The presentation of the source functions. *)
Module View := PresentT Ops PosKeyT PosKeyT.

(** The validator of the source functions. *)
Module V := ValidateCode Ops PosKeyCode PosKeyCode Source View.Q View.R BlockEdge
  View.BC View.S DigraphCode DomCode.

(** A function that defines the variable 1 with an imperative move in block 1. *)
Definition imperative : Source.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [(1, 1, [1])] (Jump 2 []));
     (2, Block positive positive positive [] [] (Return [1]))].

(** The renamed form of the imperative function, with a join parameter 12 in block 2. *)
Definition translated : Source.t :=
  Func positive positive positive 1 [10]
    [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [11]));
     (2, Block positive positive positive [12] [] (Return [12]))].

(** The certificate that maps the imperative variables to the renamed ones. *)
Definition certificate : cert :=
  ([(1, [(1, 10)]); (2, [(1, 12)])], [(1, [1]); (2, [1])]).

(** Source code of the overwrite example, whose block 2 defines a local twice. *)
Definition cache_source_code : list (positive * positive * list positive) :=
  [(2, 1, [1]); (3, 1, [2]); (2, 1, [3])].

(** Target code of the overwrite example. *)
Definition cache_target_code : list (positive * positive * list positive) :=
  [(20, 1, [10]); (30, 1, [20]); (21, 1, [30])].

(** * Checks *)

Module CheckTests.

  Local Open Scope positive_scope.

  (** The renamed function is accepted under the certificate. *)
  Example renamed_instruction_and_parameter_are_accepted :
    V.check imperative translated certificate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A return of a stale value is rejected. *)
  Definition wrong_return : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [11]));
       (2, Block positive positive positive [12] [] (Return [10]))].

  Example stale_return_value_is_rejected :
    V.check imperative wrong_return certificate = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A jump argument that no block makes available is rejected. *)
  Definition wrong_argument : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 [99]));
       (2, Block positive positive positive [12] [] (Return [12]))].

  Example unavailable_edge_argument_is_rejected :
    V.check imperative wrong_argument certificate = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The tables of the imperative and renamed functions under the certificate. *)
  Definition translated_tables := V.tables imperative translated certificate.

  (** An arm whose destination does not match its jump fails before its arguments are checked. *)
  Example mismatched_destination_arm_is_rejected :
    V.check_arm translated_tables 2 [(1, 11)] (val_set [1]) (Jump 2 []) (Jump 3 [11]) true
      = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An arm whose destination matches its jump is accepted. *)
  Example matching_destination_arm_is_accepted :
    V.check_arm translated_tables 2 [(1, 11)] (val_set [1]) (Jump 2 []) (Jump 2 [11]) true
      = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CheckTests.

(** * Fuel *)

Module FuelTests.

  Local Open Scope positive_scope.

  (** With no fuel the renamed function times out. *)
  Example zero_fuel_times_out :
    run_with Ops.eval Ops.test 0 translated [7] = Timeout.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With one unit of fuel the renamed function still times out. *)
  Example one_fuel_times_out :
    run_with Ops.eval Ops.test 1 translated [7] = Timeout.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With two units of fuel the renamed function returns 7. *)
  Example two_fuel_returns_seven :
    run_with Ops.eval Ops.test 2 translated [7] = Returned [7].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The imperative function returns 7 as well, with two units of fuel. *)
  Example imperative_returns_seven :
    run_with Ops.eval Ops.test 2 imperative [7] = Returned [7].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Running the renamed function without its input is wrong. *)
  Example missing_input_is_wrong :
    run_with Ops.eval Ops.test 2 translated [] = Wrong.
  Proof.
    vm_compute; reflexivity.
  Qed.

End FuelTests.

(** * Branch *)

Module BranchTests.

  Local Open Scope positive_scope.

  (** A branch on variable 1 whose arms go to blocks 2 and 3. *)
  Definition branch_source : Source.t :=
    Func positive positive positive 1 [1]
      [(1, Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []));
       (2, Block positive positive positive [] [] (Return [1]));
       (3, Block positive positive positive [] [] (Return [1]))].

  (** The renamed branch, whose guard reads the renamed variable 10. *)
  Definition branch_target : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] [] (Branch 1 [10] 2 [] 3 []));
       (2, Block positive positive positive [] [] (Return [10]));
       (3, Block positive positive positive [] [] (Return [10]))].

  Definition branch_certificate : cert :=
    ([(1, [(1, 10)]); (2, [(1, 10)]); (3, [(1, 10)])],
     [(1, [1]); (2, [1]); (3, [1])]).

  Definition branch_tables := V.tables branch_source branch_target branch_certificate.

  (** The source branch block, with its guard on variable 1. *)
  Definition branch_in_block := Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []).

  (** The target branch block, with its guard on variable 10. *)
  Definition branch_out_block := Block positive positive positive [] [] (Branch 1 [10] 2 [] 3 []).

  (** A target branch block whose guard names a different test. *)
  Definition bad_guard_block := Block positive positive positive [] [] (Branch 2 [10] 2 [] 3 []).

  (** The whole branch function passes the checker. *)
  Example branch_function_is_accepted :
    V.check branch_source branch_target branch_certificate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A branch exit accepts a matching guard. *)
  Example branch_exit_accepts_matching_guard :
    V.check_exit branch_tables 1 branch_in_block branch_out_block [(1, 10)] = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A branch exit rejects a mismatched guard. *)
  Example branch_exit_rejects_mismatched_guard :
    V.check_exit branch_tables 1 branch_in_block bad_guard_block [(1, 10)] = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The reference exit check also accepts a matching guard. *)
  Example branch_exit_ref_accepts_matching_guard :
    V.check_exit_ref branch_tables 1 branch_in_block branch_out_block [(1, 10)] = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The reference exit check also rejects a mismatched guard. *)
  Example branch_exit_ref_rejects_mismatched_guard :
    V.check_exit_ref branch_tables 1 branch_in_block bad_guard_block [(1, 10)] = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The checks of the three blocks pass on the shared exit tables. *)
  Example block_checks_pass_on_shared_tables :
    map (V.check_block branch_tables) [1; 2; 3] = [true; true; true].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The reference checks of the three blocks also pass on the shared exit tables. *)
  Example block_ref_checks_pass_on_shared_tables :
    map (V.check_block_ref branch_tables) [1; 2; 3] = [true; true; true].
  Proof.
    vm_compute; reflexivity.
  Qed.

End BranchTests.

(** * Scan *)

Module ScanTests.

  Local Open Scope positive_scope.

  (** Two bindings of variable 1 shadow one another, and the scan keeps the first. *)
  Definition shadowed_bindings := [(1, 10); (1, 9); (1, 10)].

  (** The scan result of the shadowed bindings, in order. *)
  Definition shadowed_result := [(1, 12); (1, 11); (1, 10); (1, 9); (1, 10)].

  (** Repeated bindings of the same variable check to the shadowed result. *)
  Example repeated_bindings_check_to_result :
    V.check_code [(1, 1, [1]); (1, 1, [1])]
      [(11, 1, [10]); (12, 1, [11])] shadowed_bindings [1; 1] = Some shadowed_result.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The exit tables of the shadowed scan keep the inverse history of its result. *)
  Example shadowed_history_keeps_exit_tables :
    V.check_code_tables [(1, 1, [1]); (1, 1, [1])]
      [(11, 1, [10]); (12, 1, [11])] shadowed_bindings [1; 1] =
      Some (shadowed_result,
        ExitTables (val_index shadowed_result) (val_inverse shadowed_result) (val_set [1])).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The result of the overwrite example, in scan order. *)
  Definition overwrite_result := [(2, 21); (3, 30); (2, 20); (1, 10)].

  (** A local overwrite updates the forward table and keeps the inverse history and membership. *)
  Example local_overwrite_keeps_inverse_history :
    V.check_code_tables cache_source_code cache_target_code [(1, 10)] [1; 1] =
      Some (overwrite_result, ExitTables (val_index overwrite_result)
        (val_inverse overwrite_result) (val_set [2; 3; 2; 1; 1])).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two sources that map to one target are rejected by the tables scan. *)
  Example conflicting_owners_rejected_by_tables :
    V.check_code_tables [] [] [(1, 10); (2, 10)] [1; 2] = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two sources that map to one target are rejected by the code scan. *)
  Example conflicting_owners_rejected_by_code :
    V.check_code [] [] [(1, 10); (2, 10)] [1; 2] = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two sources that map to one target are rejected by the reference scan. *)
  Example conflicting_owners_rejected_by_reference :
    V.check_code_ref [] [] [(1, 10); (2, 10)] [1; 2] = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A renaming that overwrites a live value is rejected. *)
  Example clobbered_live_renaming_is_rejected :
    V.check_code [(1, 1, [1])] [(20, 1, [10])] [(1, 10); (2, 20)] [1; 2] = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ScanTests.

(** * Exit *)

Module ExitTests.

  Local Open Scope positive_scope.

  (** A function whose block 1 overwrites a local, with a return of the final values. *)
  Definition cache_source : Source.t :=
    Func positive positive positive 1 [1]
      [(1, Block positive positive positive [] cache_source_code (Return [2; 3]))].

  (** The renamed function whose block 1 returns its final renamed values. *)
  Definition cache_target : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] cache_target_code (Return [21; 30]))].

  Definition cache_certificate : cert := ([(1, [(1, 10)])], [(1, [1])]).

  Definition cache_tables := V.tables cache_source cache_target cache_certificate.

  (** The exit consumes the final scan tables after an imperative local is overwritten. *)
  Example overwritten_local_check_passes :
    V.check cache_source cache_target cache_certificate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The block check accepts the exit of the overwritten local. *)
  Example overwritten_local_block_check_passes :
    V.check_block cache_tables 1 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The reference block check accepts the exit of the overwritten local. *)
  Example overwritten_local_block_ref_check_passes :
    V.check_block_ref cache_tables 1 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The renamed function passes the strict SSA check. *)
  Example overwritten_target_is_ssa :
    V.check_ssa cache_target = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ExitTests.

(** * SSA *)

Module SsaTests.

  Local Open Scope positive_scope.

  (** The renamed function is strict SSA. *)
  Example translated_is_strict_ssa :
    V.check_ssa translated = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A variable defined in block 1 is accepted in block 2, which block 1 dominates. *)
  Definition cross_block : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] [(11, 1, [10])] (Jump 2 []));
       (2, Block positive positive positive [] [] (Return [11]))].

  Example dominating_definition_is_accepted :
    V.check_ssa cross_block = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A definition that uses its own variable is rejected. *)
  Definition use_before_definition : Source.t :=
    Func positive positive positive 1 []
      [(1, Block positive positive positive [] [(11, 1, [11])] (Return [11]))].

  Example self_use_is_rejected :
    V.check_ssa use_before_definition = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A variable defined twice is rejected by the SSA check. *)
  Example duplicate_definition_is_rejected :
    V.check_ssa imperative = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The shared preparation gives the same SSA verdict on the renamed function. *)
  Example shared_preparation_agrees_on_translated :
    V.check_ssa translated = V.check_ssa_ref translated.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The shared preparation gives the same SSA verdict on the function with a self use. *)
  Example shared_preparation_agrees_on_self_use :
    V.check_ssa use_before_definition = V.check_ssa_ref use_before_definition.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An empty dominance tree, with the local operands of block 1 in the given rows. *)
  Definition empty_tree := DomTree Empty Empty Empty Empty.

  (** A local operand that an earlier definition in its block provides is visible. *)
  Example local_operand_is_visible :
    V.ssa_local empty_tree Empty 1 (val_set [10])
      [(11, 1, [10]); (12, 1, [11])] [12] = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An operand that no definition provides is not visible locally. *)
  Example undefined_local_operand_is_not_visible :
    V.ssa_local empty_tree Empty 1 (val_set [10]) [(11, 1, [99])] [11] = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End SsaTests.

(** * Weak state *)

Module WeakTests.

  Local Open Scope positive_scope.

  (** The weak validator, which shares the presentation and the tables of the strict one. *)
  Module W := Validate Ops PosKey PosKey Source View.Q View.R BlockEdge
    View.BC View.S Digraph Dom View.Link.

  (** A source that returns the variable 1 after a jump. *)
  Definition weak_source : Source.t :=
    Func positive positive positive 1 [1]
      [(1, Block positive positive positive [] [] (Jump 2 []));
       (2, Block positive positive positive [] [] (Return [1]))].

  (** A target that passes the variable 10 through a join parameter 12. *)
  Definition weak_target : Source.t :=
    Func positive positive positive 1 [10]
      [(1, Block positive positive positive [] [] (Jump 2 [10]));
       (2, Block positive positive positive [12] [] (Return [12]))].

  Example weak_state_translation_is_accepted :
    W.check weak_source weak_target certificate = true.
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

  (** The target takes one step to a wrong state, because it cannot run the join. *)
  Example weak_target_step_is_wrong :
    step Ops.eval Ops.test weak_target (1, [], []) = inr Wrong.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The source takes one step to block 2. *)
  Example weak_source_step_reaches_block_two :
    step Ops.eval Ops.test weak_source (1, [], []) = inl (2, [], []).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The target is wrong after one unit of fuel, so the two weakly related states differ. *)
  Example weak_target_fuel_is_wrong :
    loop_fuel (step Ops.eval Ops.test weak_target) 1 (1, [], []) = inr Wrong.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The source reaches block 2 after one unit of fuel. *)
  Example weak_source_fuel_reaches_block_two :
    loop_fuel (step Ops.eval Ops.test weak_source) 1 (1, [], []) = inl (2, [], []).
  Proof.
    vm_compute; reflexivity.
  Qed.

End WeakTests.

(** * Padding *)

Module PaddingTests.

  Local Open Scope positive_scope.

  (** A function with one empty block and no parameters. *)
  Definition empty_program : Source.t :=
    Func positive positive positive 1 []
      [(1, Block positive positive positive [] [] (Return []))].

  (** A certificate with n copies of the same mapping for the entry block. *)
  Definition padded_entry (n : nat) : cert := ([(1, repeat (1, 1) n)], []).

  (** One copy of the padding is accepted for the empty block. *)
  Example one_padding_entry_is_accepted :
    V.check empty_program empty_program (padded_entry 1) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Eight copies of the padding are also accepted for the empty block. *)
  Example eight_padding_entries_are_accepted :
    V.check empty_program empty_program (padded_entry 8) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A certificate with n copies of the same mapping for block 2, which is the edge target. *)
  Definition padded_unused (n : nat) : cert := ([(2, repeat (1, 1) n)], []).

  (** A function with an edge from block 1 to block 2. *)
  Definition empty_edge_program : Source.t :=
    Func positive positive positive 1 []
      [(1, Block positive positive positive [] [] (Jump 2 []));
       (2, Block positive positive positive [] [] (Return []))].

  Definition small_padding_tables :=
    V.tables empty_edge_program empty_edge_program (padded_unused 1).

  Definition large_padding_tables :=
    V.tables empty_edge_program empty_edge_program (padded_unused 8).

  (** Padding the target row with one copy keeps the edge check accepting. *)
  Example small_padding_passes_edge_check :
    V.check_edge small_padding_tables 1 2 [] = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Padding the target row with eight copies also keeps the edge check accepting. *)
  Example large_padding_passes_edge_check :
    V.check_edge large_padding_tables 1 2 [] = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** One copy of the padding is within the row budget. *)
  Example small_padding_is_within_row_budget :
    V.row_budget empty_edge_program (padded_unused 1) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Eight copies of the padding exceed the row budget. *)
  Example large_padding_exceeds_row_budget :
    V.row_budget empty_edge_program (padded_unused 8) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End PaddingTests.
