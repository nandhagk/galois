(** * Prepared SSA observations

    Preparation keeps the first block and indexes the resulting graph and variables.
    For example, a dangling branch target contributes no edge.
    Builds on: Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Program Require Import Ssa.
From Galois.Ssa Require Import Lang LiveSig Present.
Import List.ListNotations.
Open Scope positive_scope.

Definition fixture : func positive unit unit :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [2] [(3, tt, [2])]
      (Branch tt [3] 2 [3] 7 [9]));
     (1, Block positive unit unit [] [] (Return [9]));
     (2, Block positive unit unit [4] [] (Return [4]))].

Definition prepared := lang_prepare fixture.
Definition edge := BlockEdge 1 True_arm 2.

Example keeps_first_block_and_listed_edges :
  (lang_entries prepared, lang_blocks prepared, lang_edges prepared) = ([1], [1; 2], [edge]).
Proof. vm_compute; reflexivity. Qed.

Example adjacency_and_inventories :
  (index_row (lang_out prepared) 1, index_row (lang_inc prepared) 2,
   ssa_entry_params (lang_ssa prepared), ssa_arg_rows (lang_ssa prepared)) =
  ([edge], [edge], [2], [(edge, (4, 3))]).
Proof. vm_compute; reflexivity. Qed.

Example point_graph_and_arguments :
  (lang_points prepared, lang_point_edges prepared,
   trie_get (BlockEdge.encode edge) (point_args (lang_point_tables prepared))) =
  ([(1, 0%N); (1, 1%N); (1, 2%N); (2, 0%N); (2, 1%N)],
   [PointEdge (1, 0%N) (1, 1%N) None; PointEdge (1, 1%N) (1, 2%N) None;
    PointEdge (1, 2%N) (2, 0%N) (Some edge); PointEdge (2, 0%N) (2, 1%N) None],
   Some [3]).
Proof. vm_compute; reflexivity. Qed.

Definition missing_entry : func positive unit unit :=
  Func positive unit unit 8 [] [(1, Block positive unit unit [] [] (Jump 7 [9]))].

Example missing_entry_and_dangling_target :
  (lang_entries (lang_prepare missing_entry), lang_edges (lang_prepare missing_entry)) = ([], []).
Proof. vm_compute; reflexivity. Qed.

Example edge_identity_ignores_arguments :
  map fst (exit_edge_args 1 (@Jump positive unit 2 [3])) = map fst (exit_edge_args 1 (@Jump positive unit 2 [9; 8])).
Proof. vm_compute; reflexivity. Qed.

Module Ops <: OPS.
  Definition K := unit.
  Definition G := unit.
  Definition C := unit.
  Definition eval (_ : unit) (_ : list unit) : option unit := None.
  Definition test (_ : unit) (_ : list unit) : option bool := None.
  Definition mov := tt.
End Ops.
Module View := PresentT Ops UnitKeyT UnitKeyT.

Example presentation_readers :
  (View.BC.out prepared 1, View.BC.inc prepared 2,
   View.S.params prepared 1, View.S.args prepared edge,
   View.SP.block_edge_args prepared edge) =
  ([edge], [edge], [2], [(4, 3)], [3]).
Proof. vm_compute; reflexivity. Qed.
