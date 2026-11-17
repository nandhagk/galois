(** * Checked SSA construction examples

    Conservative liveness rows isolate placement and renaming from the liveness producer.
    For example, a diamond join receives one parameter and a loop carries its updated value.

    Groups:
    - BuildTests: the results of running the built functions.
    - PlacementTests: the definition index and the parameters that the placement adds.
    - RejectionTests: sources and validators that the build must reject.
    - ShortCircuitTests: the build agrees with the checked produce-then-validate path.
    - LocalTemporaryTests: a function whose temporaries are all local to one block.
    - LargeUniverseTests: a large function with twenty live inputs.

    Builds on: Ssa.Build, Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith NArith Arith.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig DomSig FrontierSig Digraph Dom Frontier.
From Galois.Ssa Require Import Lang LiveSig ValidateSig Validate Present Build.
Import List.ListNotations.

Open Scope positive_scope.

(** * Fixtures *)

(** The test operations: operation 2 increments its input, and other operations keep it. *)
Module TestOps <: OPS.
  Definition K := positive.
  Definition G := positive.
  Definition C := positive.
  Definition eval (op : positive) (values : list positive) : option positive :=
    match values with
    | [] => None
    | x :: _ => Some (if Pos.eqb op 2 then Pos.succ x else x)
    end.
  Definition test (_ : positive) (values : list positive) : option bool :=
    match values with [] => None | x :: _ => Some (Pos.eqb x 1) end.
  Definition mov := 1.
End TestOps.

(** The source functions that the examples build. *)
Module TestSource.
  Definition t := func positive positive positive.
End TestSource.

(** The presentation of the test functions. *)
Module TestView := PresentT TestOps PosKeyT PosKeyT.

(** Each block has the value 1 live on entry. *)
Module TestLive.
  Definition live_in (p : TestSource.t) : list (positive * list positive) :=
    map (fun item => (fst item, [1])) (blocks _ _ _ p).
End TestLive.

(** The validator of the test functions. *)
Module TestValidate := ValidateCode TestOps PosKeyCode PosKeyCode TestSource
  TestView.Q TestView.R BlockEdge TestView.BC TestView.S DigraphCode DomCode.

(** The builder, which takes its liveness from TestLive. *)
Module TestBuild := BuildCode TestOps PosKeyCode PosKeyCode TestSource
  TestView.Q TestView.R BlockEdge PointEdge PointKey TestView.BC TestView.C TestView.U
  TestView.SP TestView.S DigraphCode DomCode FrontierCode TestLive TestValidate.

(** The inputs stay live across blocks, and the temporaries of each block stay local to it. *)
Module TestInputLive.
  Definition live_in (p : TestSource.t) : list (positive * list positive) :=
    map (fun item => (fst item, inputs _ _ _ p)) (blocks _ _ _ p).
End TestInputLive.

(** The builder, which takes its liveness from TestInputLive. *)
Module TestInputBuild := BuildCode TestOps PosKeyCode PosKeyCode TestSource
  TestView.Q TestView.R BlockEdge PointEdge PointKey TestView.BC TestView.C TestView.U
  TestView.SP TestView.S DigraphCode DomCode FrontierCode TestInputLive TestValidate.

(** Runs the built function of a source with the given fuel and inputs, or reports a wrong build. *)
Definition build_run p fuel values :=
  match TestBuild.build p with
  | Some s => run_with TestOps.eval TestOps.test fuel s values
  | None => Wrong
  end.

(** A block that moves one value through two increments. *)
Definition build_straight : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [(1, 2, [1]); (1, 2, [1])] (Return [1]))].

(** A diamond whose join receives the value from either branch. *)
Definition build_diamond : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []));
     (2, Block positive positive positive [] [(1, 2, [1])] (Jump 4 []));
     (3, Block positive positive positive [] [(1, 1, [1])] (Jump 4 []));
     (4, Block positive positive positive [] [] (Return [1]))].

(** A source that returns the value 2, which no block defines. *)
Definition build_unavailable : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Return [2]))].

(** * Build *)

Module BuildTests.

  (** A block of two increments returns the input plus two. *)
  Example straight_line_returns_three :
    build_run build_straight 1 [1] = Returned [3].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A diamond with input 1 returns the value 2 from the join. *)
  Example diamond_first_branch_returns_two :
    build_run build_diamond 3 [1] = Returned [2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A diamond with input 2 returns the value 2 from the join. *)
  Example diamond_second_branch_returns_two :
    build_run build_diamond 3 [2] = Returned [2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A loop with a fuel of four runs out before it returns. *)
  Definition build_loop : TestSource.t :=
    Func positive positive positive 1 [1]
      [(1, Block positive positive positive [] [] (Jump 2 []));
       (2, Block positive positive positive [] [] (Branch 1 [1] 3 [] 4 []));
       (3, Block positive positive positive [] [(1, 2, [1])] (Jump 2 []));
       (4, Block positive positive positive [] [] (Return [1]))].

  Example loop_times_out_with_fuel_four :
    build_run build_loop 4 [1] = Timeout.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The same loop returns the value 2 once it has fuel five. *)
  Example loop_returns_with_fuel_five :
    build_run build_loop 5 [1] = Returned [2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The built function keeps the blocks of the diamond in their source order. *)
  Example blocks_keep_source_order :
    option_map (fun s => map fst (blocks _ _ _ s)) (TestBuild.build build_diamond) =
      Some [1; 2; 3; 4].
  Proof.
    vm_compute; reflexivity.
  Qed.

End BuildTests.

(** * Placement *)

Module PlacementTests.

  (** The definition index lists the variable once for each definition in its block. *)
  Example definition_index_keeps_repeated_definitions :
    frontier_row (TestBuild.def_index build_straight) 1 = [1; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The join of the diamond gets one parameter, for the value 1. *)
  Example join_gets_parameter_one :
    index_row (TestBuild.placement build_diamond) 4 = [1].
  Proof.
    vm_compute; reflexivity.
  Qed.

End PlacementTests.

(** * Rejection *)

Module RejectionTests.

  (** A source that returns a value that no block defines is rejected. *)
  Example unavailable_source_is_rejected :
    TestBuild.build build_unavailable = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two blocks with the same label are rejected before renaming. *)
  Definition build_duplicate_block : TestSource.t :=
    Func positive positive positive 1 [1]
      [(1, Block positive positive positive [] [] (Return [1]));
       (1, Block positive positive positive [] [] (Return [1]))].

  Example duplicate_block_is_rejected_before_renaming :
    TestBuild.produce build_duplicate_block = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A validator whose check always fails. *)
  Module TestRejectValidate.
    Definition check (_ _ : TestSource.t) (_ : cert) : bool := false.
    Definition check_ssa := TestValidate.check_ssa.
  End TestRejectValidate.

  Module TestRejectBuild := BuildCode TestOps PosKeyCode PosKeyCode TestSource
    TestView.Q TestView.R BlockEdge PointEdge PointKey TestView.BC TestView.C TestView.U
    TestView.SP TestView.S DigraphCode DomCode FrontierCode TestLive TestRejectValidate.

  Example rejected_candidate_is_still_produced :
    TestRejectBuild.produce build_diamond <> None.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** The same validator makes the build return no function. *)
  Example rejected_candidate_is_not_built :
    TestRejectBuild.build build_diamond = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

End RejectionTests.

(** * Short circuit *)

Module ShortCircuitTests.

  (** Building agrees with producing and then validating, on accepted and rejected sources. *)
  Example build_agrees_with_checked_produce :
    map TestBuild.build [build_diamond; build_unavailable] =
      map (fun p => match TestBuild.produce p with
        | None => None
        | Some (s, c) =>
          if andb (TestValidate.check p s c) (TestValidate.check_ssa s) then Some s else None
        end) [build_diamond; build_unavailable].
  Proof.
    vm_compute; reflexivity.
  Qed.

End ShortCircuitTests.

(** * Local temporaries *)

Module LocalTemporaryTests.

  (** A function whose first block defines forty temporaries that no other block uses. *)
  Definition build_local_temporaries : TestSource.t :=
    Func _ _ _ 1 [1; 2]
      [(1, Block _ _ _ []
        (map (fun j => (Pos.of_nat (j + 3), 1, [Pos.of_succ_nat (j mod 2)%nat])) (seq 0 40))
        (Branch 1 [1] 2 [] 3 []));
       (2, Block _ _ _ [] [] (Jump 4 []));
       (3, Block _ _ _ [] [] (Jump 4 []));
       (4, Block _ _ _ [] [] (Return [1; 2]))].

  (** The universe of the function, with its two inputs and its forty temporaries. *)
  Definition local_universe :=
    TestView.U.universe (TestView.R.prepare build_local_temporaries).

  (** The universe holds 42 variables: the two inputs and forty block-local temporaries. *)
  Example local_universe_has_42_variables :
    length local_universe = 42%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Only the two inputs are live across blocks. *)
  Example only_inputs_are_live_across_blocks :
    length (live_variables (TestInputLive.live_in build_local_temporaries) local_universe) =
      2%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Filtering leaves exactly the same placement table as the complete universe. *)
  Example placement_matches_complete_universe :
    TestInputBuild.placement build_local_temporaries =
      TestInputBuild.placement_with (TestInputBuild.frontiers build_local_temporaries)
        (TestInputBuild.def_index build_local_temporaries)
        (TestInputBuild.live_sets (TestInputLive.live_in build_local_temporaries))
        local_universe.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A function accepted by the original guard keeps its exact checked candidate. *)
  Example checked_build_is_unchanged :
    TestInputBuild.build build_local_temporaries =
      match TestInputBuild.rename build_local_temporaries
        (TestInputBuild.dom_tree build_local_temporaries)
        (TestInputBuild.placement_with (TestInputBuild.frontiers build_local_temporaries)
          (TestInputBuild.def_index build_local_temporaries)
          (TestInputBuild.live_sets (TestInputLive.live_in build_local_temporaries))
          local_universe)
        (TestInputLive.live_in build_local_temporaries) with
      | None => None
      | Some (s, c) =>
        if andb (TestValidate.check build_local_temporaries s c) (TestValidate.check_ssa s)
        then Some s else None
      end.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The built function returns the two inputs, 4 and 5, from its join. *)
  Example local_temporaries_return_inputs :
    option_map (fun s => run_with TestOps.eval TestOps.test 3 s [4; 5])
      (TestInputBuild.build build_local_temporaries) = Some (Returned [4; 5]).
  Proof.
    vm_compute; reflexivity.
  Qed.

End LocalTemporaryTests.

(** * Large universe *)

Module LargeUniverseTests.

  (** The twenty inputs of the large function. *)
  Definition build_large_inputs : list positive := map Pos.of_succ_nat (seq 0 20).

  (** One block of 99 temporaries that branches to two of the other blocks. *)
  Definition build_large_block (i : nat) : positive * block positive positive positive :=
    (Pos.of_succ_nat i,
     Block _ _ _ []
       (map (fun j =>
         (Pos.of_nat (21 + 99 * i + j), 1, [Pos.of_succ_nat (j mod 20)%nat])) (seq 0 99))
       (Branch 1 build_large_inputs (Pos.of_nat (Nat.min 20 (i + 2))) []
         (Pos.of_nat (Nat.max 2 i)) [])).

  (** The large function: twenty blocks, each built by build_large_block. *)
  Definition build_large_universe : TestSource.t :=
    Func _ _ _ 1 build_large_inputs (map build_large_block (seq 0 20)).

  (** A large function with twenty live inputs is still produced. *)
  Example large_function_is_produced :
    TestInputBuild.produce build_large_universe <> None.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** The large function is accepted by the build. *)
  Example large_function_is_built :
    TestInputBuild.build build_large_universe <> None.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** The built large function passes the SSA check. *)
  Example large_function_is_ssa :
    option_map TestValidate.check_ssa (TestInputBuild.build build_large_universe) = Some true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End LargeUniverseTests.
