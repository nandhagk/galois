(** * Prepared SSA observations

    Preparation keeps the first block and indexes the resulting graph and variables.
    For example, a dangling branch target contributes no edge.

    Groups:
    - PrepareTests: the entries, blocks and edges that preparation keeps.
    - AdjacencyTests: the adjacency rows, inventories and point tables of a prepared function.
    - PresentationTests: the readers of the presentation of a prepared function.
    - SharedKeyTests: point tables whose edges share a key.
    - MeasurementTests: the shape of a generated program.

    Builds on: Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Program Require Import Ssa.
From Galois.Ssa Require Import Lang LiveSig Present.
Import List.ListNotations.
Open Scope positive_scope.

(** * Fixtures *)

(** A function whose block 1 branches to block 2 and to a block 7 that is not defined. *)
Definition fixture : func positive unit unit :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [2] [(3, tt, [2])]
      (Branch tt [3] 2 [3] 7 [9]));
     (1, Block positive unit unit [] [] (Return [9]));
     (2, Block positive unit unit [4] [] (Return [4]))].

(** The prepared form of the fixture. *)
Definition prepared := lang_prepare fixture.

(** The edge from block 1 to block 2. *)
Definition edge := BlockEdge 1 True_arm 2.

(** * Prepare *)

Module PrepareTests.

  (** Preparation keeps block 1 as the only entry. *)
  Example first_block_is_the_entry :
    lang_entries prepared = [1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Each block label appears once, though block 1 is listed twice in the source. *)
  Example blocks_list_each_label_once :
    lang_blocks prepared = [1; 2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Only the edge from block 1 to block 2 is kept, since block 7 is not defined. *)
  Example dangling_branch_adds_no_edge :
    lang_edges prepared = [edge].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A function with a missing entry and a dangling target has no entries. *)
  Definition missing_entry : func positive unit unit :=
    Func positive unit unit 8 [] [(1, Block positive unit unit [] [] (Jump 7 [9]))].

  Example missing_entry_has_no_entries :
    lang_entries (lang_prepare missing_entry) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A function with a missing entry and a dangling target has no edges. *)
  Example missing_entry_has_no_edges :
    lang_edges (lang_prepare missing_entry) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End PrepareTests.

(** * Adjacency *)

Module AdjacencyTests.

  (** Block 1 has the edge to block 2 as its only outgoing edge. *)
  Example block_one_has_outgoing_edge :
    index_row (lang_out prepared) 1 = [edge].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Block 2 has the same edge as its only incoming edge. *)
  Example block_two_has_incoming_edge :
    index_row (lang_inc prepared) 2 = [edge].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The entry parameter of the prepared function is the variable 2. *)
  Example entry_parameter_is_two :
    ssa_entry_params (lang_ssa prepared) = [2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The edge to block 2 carries the arguments 4 and 3. *)
  Example edge_arguments_are_listed :
    ssa_arg_rows (lang_ssa prepared) = [(edge, (4, 3))].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The points of block 1 and block 2 are listed in order, with their indices. *)
  Example points_of_both_blocks :
    lang_points prepared =
      [(1, 0%N); (1, 1%N); (1, 2%N); (2, 0%N); (2, 1%N)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The point edges chain the points within each block, and link block 1 to block 2. *)
  Example point_edges_chain_within_blocks :
    lang_point_edges prepared =
      [PointEdge (1, 0%N) (1, 1%N) None; PointEdge (1, 1%N) (1, 2%N) None;
       PointEdge (1, 2%N) (2, 0%N) (Some edge); PointEdge (2, 0%N) (2, 1%N) None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The edge to block 2 has the argument 3. *)
  Example edge_has_argument_three :
    trie_get (BlockEdge.encode edge) (point_args (lang_point_tables prepared)) = Some [3].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Exiting an edge gives the same edge identity, whatever its arguments are. *)
  Example edge_identity_ignores_arguments :
    map fst (exit_edge_args 1 (@Jump positive unit 2 [3])) =
      map fst (exit_edge_args 1 (@Jump positive unit 2 [9; 8])).
  Proof.
    vm_compute; reflexivity.
  Qed.

End AdjacencyTests.

(** * Presentation *)

Module PresentationTests.

  (** The operations of the presentation, whose values are units. *)
  Module Ops <: OPS.
    Definition K := unit.
    Definition G := unit.
    Definition C := unit.
    Definition eval (_ : unit) (_ : list unit) : option unit := None.
    Definition test (_ : unit) (_ : list unit) : option bool := None.
    Definition mov := tt.
  End Ops.

  Module View := PresentT Ops UnitKeyT UnitKeyT.

  (** Block 1 has the edge to block 2 as an outgoing edge. *)
  Example presented_out_edges_of_block_one :
    View.BC.out prepared 1 = [edge].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Block 2 has the edge from block 1 as an incoming edge. *)
  Example presented_incoming_edges_of_block_two :
    View.BC.inc prepared 2 = [edge].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The parameters of block 1 are the variable 2. *)
  Example presented_params_of_block_one :
    View.S.params prepared 1 = [2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The edge to block 2 carries the arguments 4 and 3. *)
  Example presented_args_of_edge :
    View.S.args prepared edge = [(4, 3)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The block-edge arguments of the edge to block 2 are the variable 3. *)
  Example presented_block_edge_args_of_edge :
    View.SP.block_edge_args prepared edge = [3].
  Proof.
    vm_compute; reflexivity.
  Qed.

End PresentationTests.

(** * Shared keys *)

Module SharedKeyTests.

  (** Two point edges that share a source key, and one that does not. *)
  Definition shared_key_edges : list point_edge :=
    [PointEdge (1, 0%N) (1, 1%N) None;
     PointEdge (2, 0%N) (2, 1%N) None;
     PointEdge (1, 0%N) (2, 0%N) (Some edge)].

  (** The key of a point edge is the encoding of its source point. *)
  Definition shared_key (e : point_edge) := PointKey.encode (point_src e).

  (** The multi-table of the shared key agrees with its specification. *)
  Definition shared_table := multi_table shared_key shared_key_edges.

  Example shared_key_table_matches_specification :
    shared_table = multi_table_specification shared_key shared_key_edges.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The row of the shared key keeps its two edges in source order. *)
  Example shared_key_row_keeps_source_order :
    index_row shared_table (PointKey.encode (1, 0%N)) =
      [PointEdge (1, 0%N) (1, 1%N) None;
       PointEdge (1, 0%N) (2, 0%N) (Some edge)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A key that no edge has gives an empty row. *)
  Example absent_key_has_empty_row :
    index_row shared_table (PointKey.encode (3, 0%N)) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SharedKeyTests.

(** * Measurement *)

Module MeasurementTests.

  (** The fixture uses forty inputs and one reassigned local per block. *)
  Definition measurement_globals : list positive := map Pos.of_nat (seq 1 40).

  (** A block that assigns its local once and then reassigns it, with the given count. *)
  Definition measurement_block (instructions i : nat) : positive * block positive unit unit :=
    let b := Pos.of_nat (S i) in
    let local := Pos.of_nat (101 + i) in
    (b, Block positive unit unit []
      ((local, tt, measurement_globals) :: repeat (local, tt, [local]) (Nat.pred instructions))
      (if Nat.eqb i 99 then Return (measurement_globals ++ [local])
       else Jump (Pos.of_nat (S (S i))) [])).

  (** The program of one hundred such blocks, each with the given instruction count. *)
  Definition measurement_program (instructions : nat) : func positive unit unit :=
    Func positive unit unit 1 measurement_globals
      (map (measurement_block instructions) (seq 0 100)).

  Definition measurement_five := measurement_program 5.

  (** The measurement program has one hundred blocks. *)
  Example measurement_program_block_count :
    length (blocks _ _ _ measurement_five) = 100%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The measurement program has five hundred instructions in all. *)
  Example measurement_program_instruction_count :
    fold_right (fun item total => length (code _ _ _ (snd item)) + total)%nat
      0%nat (blocks _ _ _ measurement_five) = 500%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The measurement program has forty inputs. *)
  Example measurement_program_input_count :
    length (inputs _ _ _ measurement_five) = 40%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

End MeasurementTests.
