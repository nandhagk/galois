(** * Hand-written dominator scope fixtures

    Checked parent maps distinguish ancestor reuse from sibling-local expressions.
    For example, the two arms of a diamond receive separate persistent symbol tables.
    Builds on: AnalysesEqualityScope and GraphCheckDom. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityRefine AnalysesEqualityScope.
Import List.ListNotations.

Definition scope_line_graph : Graph.t nat (nat * nat) :=
  Graph.of_pure [0] [0; 1; 2]
    (fun b => if Nat.eqb b 0 then [(0, 1)] else if Nat.eqb b 1 then [(1, 2)] else [])
    fst snd.

Definition scope_line_cfg :=
  Cfg.Make scope_line_graph nat_encoding (codec_enc (pair_codec nat_codec nat_codec)).

Definition scope_line_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure scope_line_cfg nat_encoding [0; 1; 2; 3]
    (fun x => if Nat.leb 2 x then Op 0 [0; 1] else Arbitrary)
    (fun x => if Nat.eqb x 2 then 1 else if Nat.eqb x 3 then 2 else 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition scope_line_problem := Numbering.of_pure scope_line_ssa nat_encoding (fun _ => true).
Definition scope_line_prepared := Prepared.prepare nat_encoding scope_line_graph.
Definition scope_line_parents :=
  Map.of_list positive_encoding [(2%positive, 1%positive); (3%positive, 2%positive)].
Definition scope_line_tree := DomCheck.of_parents scope_line_prepared scope_line_parents.

Example accepts_hand_written_line :
  DomCheck.check scope_line_prepared scope_line_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_wrong_line :
  DomCheck.check scope_line_prepared
    (Map.of_list positive_encoding [(2%positive, 1%positive); (3%positive, 1%positive)]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example line_ancestor_reused :
  NumberingRefine.equivalent_b scope_line_problem
    (NumberingScope.dominator_numbering scope_line_problem nat_encoding_laws scope_line_tree)
    2 3 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example line_result_checked :
  NumberingSignature.check scope_line_problem
    (NumberingScope.dominator_numbering scope_line_problem nat_encoding_laws scope_line_tree) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example line_scope_queue_drained :
  NumberingScope.scopes_finished scope_line_problem
    (Cost.value (NumberingScope.dominator_c scope_line_problem nat_encoding_laws scope_line_tree)) =
      true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scope_chain_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure scope_line_cfg nat_encoding [0; 1; 2; 3; 4; 5; 6; 7]
    (fun x =>
      match x with
      | 2 | 4 => Op 0 []
      | 3 => Op 1 [2]
      | 5 => Op 1 [4]
      | 6 => Op 2 [3]
      | 7 => Op 2 [5]
      | _ => Arbitrary
      end)
    (fun x => if Nat.eqb x 4 || Nat.eqb x 5 then 1 else if Nat.eqb x 7 then 2 else 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition scope_chain_problem :=
  Numbering.of_pure scope_chain_ssa nat_encoding (fun _ => true).

Example three_scoped_congruences_reuse_ancestor_leaders :
  let p := NumberingScope.dominator_numbering scope_chain_problem nat_encoding_laws scope_line_tree in
  (NumberingRefine.equivalent_b scope_chain_problem p 2 4,
    NumberingRefine.equivalent_b scope_chain_problem p 3 5,
    NumberingRefine.equivalent_b scope_chain_problem p 6 7) = (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition scope_diamond_graph : Graph.t nat (nat * nat) :=
  Graph.of_pure [0] [0; 1; 2; 3]
    (fun b =>
      match b with
      | 0 => [(0, 1); (0, 2)]
      | 1 => [(1, 3)]
      | 2 => [(2, 3)]
      | _ => []
      end) fst snd.

Definition scope_diamond_cfg :=
  Cfg.Make scope_diamond_graph nat_encoding (codec_enc (pair_codec nat_codec nat_codec)).

Definition scope_diamond_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure scope_diamond_cfg nat_encoding [0; 1; 2; 3; 4]
    (fun x => if Nat.leb 2 x then Op 0 [0; 1] else Arbitrary)
    (fun x => if Nat.leb 2 x then Nat.pred x else 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition scope_diamond_problem :=
  Numbering.of_pure scope_diamond_ssa nat_encoding (fun _ => true).
Definition scope_diamond_prepared := Prepared.prepare nat_encoding scope_diamond_graph.
Definition scope_diamond_parents :=
  Map.of_list positive_encoding
    [(2%positive, 1%positive); (3%positive, 1%positive); (4%positive, 1%positive)].
Definition scope_diamond_tree := DomCheck.of_parents scope_diamond_prepared scope_diamond_parents.

Example accepts_hand_written_diamond :
  DomCheck.check scope_diamond_prepared scope_diamond_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example siblings_do_not_share_local_symbols :
  NumberingRefine.equivalent_b scope_diamond_problem
    (NumberingScope.dominator_numbering scope_diamond_problem nat_encoding_laws scope_diamond_tree)
    2 3 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example join_does_not_inherit_one_arm :
  NumberingRefine.equivalent_b scope_diamond_problem
    (NumberingScope.dominator_numbering scope_diamond_problem nat_encoding_laws scope_diamond_tree)
    2 4 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_checked_contract :
  NumberingSignature.check scope_diamond_problem
    (NumberingScope.dominator_numbering scope_diamond_problem nat_encoding_laws scope_diamond_tree) =
      true.
Proof.
  exact (NumberingScope.dominator_checked scope_diamond_problem nat_encoding_laws scope_diamond_tree).
Qed.

Definition scope_empty_ssa : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure
    (Cfg.Make (Graph.of_pure [] [] (fun _ : nat => []) fst snd) nat_encoding
      (codec_enc (pair_codec nat_codec nat_codec)))
    nat_encoding [] (fun _ => Arbitrary) (fun _ => 0)
    (fun _ => []) (fun _ => []) (fun _ => []).

Definition scope_empty_problem := Numbering.of_pure scope_empty_ssa nat_encoding (fun _ => true).
Definition scope_empty_tree := Dom.Tree Map.empty Map.empty Map.empty.

Example empty_scope_boundary :
  NumberingSignature.check scope_empty_problem
    (NumberingScope.dominator_numbering scope_empty_problem nat_encoding_laws scope_empty_tree) =
      true.
Proof.
  vm_compute; reflexivity.
Qed.
