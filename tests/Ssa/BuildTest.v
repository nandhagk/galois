(** * Checked SSA construction examples

    Conservative liveness rows isolate placement and renaming from the liveness producer.
    For example, a diamond join receives one parameter and a loop carries its updated value.
    Builds on: Ssa.Build, Ssa.Validate and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig DomSig FrontierSig Digraph Dom Frontier.
From Galois.Ssa Require Import Lang LiveSig ValidateSig Validate Present Build.
Import List.ListNotations.
Open Scope positive_scope.

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
Module TestSource.
  Definition t := func positive positive positive.
End TestSource.
Module TestView := PresentT TestOps PosKeyT PosKeyT.
Module TestLive.
  Definition live_in (p : TestSource.t) : list (positive * list positive) :=
    map (fun item => (fst item, [1])) (blocks _ _ _ p).
End TestLive.
Module TestValidate := ValidateCode TestOps PosKeyCode PosKeyCode TestSource
  TestView.Q TestView.R BlockEdge TestView.BC TestView.S DigraphCode DomCode.
Module TestBuild := BuildCode TestOps PosKeyCode PosKeyCode TestSource
  TestView.Q TestView.R BlockEdge PointEdge PointKey TestView.BC TestView.C TestView.U
  TestView.SP TestView.S DigraphCode DomCode FrontierCode TestLive TestValidate.

Definition build_straight : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [(1, 2, [1]); (1, 2, [1])] (Return [1]))].
Definition build_diamond : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Branch 1 [1] 2 [] 3 []));
     (2, Block positive positive positive [] [(1, 2, [1])] (Jump 4 []));
     (3, Block positive positive positive [] [(1, 1, [1])] (Jump 4 []));
     (4, Block positive positive positive [] [] (Return [1]))].
Definition build_loop : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Jump 2 []));
     (2, Block positive positive positive [] [] (Branch 1 [1] 3 [] 4 []));
     (3, Block positive positive positive [] [(1, 2, [1])] (Jump 2 []));
     (4, Block positive positive positive [] [] (Return [1]))].
Definition build_run p fuel values :=
  match TestBuild.build p with
  | Some s => run_with TestOps.eval TestOps.test fuel s values
  | None => Wrong
  end.
Example build_straight_result : build_run build_straight 1 [1] = Returned [3].
Proof. vm_compute; reflexivity. Qed.
Example build_diamond_results :
  (build_run build_diamond 3 [1], build_run build_diamond 3 [2]) =
    (Returned [2], Returned [2]).
Proof. vm_compute; reflexivity. Qed.
Example build_loop_result :
  (build_run build_loop 4 [1], build_run build_loop 5 [1]) = (Timeout, Returned [2]).
Proof. vm_compute; reflexivity. Qed.
Example build_keeps_block_order :
  option_map (fun s => map fst (blocks _ _ _ s)) (TestBuild.build build_diamond) =
    Some [1; 2; 3; 4].
Proof. vm_compute; reflexivity. Qed.
Example build_definition_index_deduplicates_within_blocks :
  frontier_row (TestBuild.def_index build_straight) 1 = [1; 1].
Proof. vm_compute; reflexivity. Qed.
Example build_places_join_parameter :
  index_row (TestBuild.placement build_diamond) 4 = [1].
Proof. vm_compute; reflexivity. Qed.
Definition build_unavailable : TestSource.t :=
  Func positive positive positive 1 [1]
    [(1, Block positive positive positive [] [] (Return [2]))].
Example build_rejects_unavailable_source : TestBuild.build build_unavailable = None.
Proof. vm_compute; reflexivity. Qed.
