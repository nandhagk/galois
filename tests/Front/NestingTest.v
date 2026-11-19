(** * Other datatypes, lists of lists and pairs in datatypes

    Datatypes whose constructors hold another datatype of the program, directly or in a list,
    and lists whose elements are lists, read by [Egglog] and run on the engine. The congruence
    closure of the engine joins two terms whose parts it joins, at every depth. A pattern may
    write an element of a list of pairs as one variable, and a congruence law may relate two
    lists of values by an equality and two lists of pairs by [Forall2 (pair_rel ra rb)].
    For example, once the input says that the values 2 and 3 are the same, the blocks
    [Block [Store 1 2]] and [Block [Store 1 3]] share a class.

    Groups:
    - [DeclarationTests] The tables of another datatype and of lists of lists.
    - [OtherDatatypeTests] Blocks of statements, joined by the unions of statements.
    - [NestedListTests] Grids of lists of lists, joined at the inner elements.
    - [PairVariableTests] Rewrites that move and read pairs written as variables.
    - [LawTests] The congruence laws of lists of values and of pairs.
    - [RejectionTests] The command stops at containers that it cannot read.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Encode Derive.
Import List.ListNotations.

(** * Fixtures *)

Module ExampleValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End ExampleValue.

Module ExampleIndex := IndexCode ExampleValue.
Module ExampleJoin := JoinCode ExampleValue ExampleIndex.
Module ExampleDatabase := DatabaseCode ExampleValue ExampleIndex.
Module ExampleRun := RunCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase.
Module ExampleRunner :=
  RunnerCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase ExampleRun.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** A statement is a skip or a store of a value into a variable. *)
Inductive stmt : Type :=
  | Skip
  | Store (x v : positive).

(** Blocks of statements, and a statement that guards a block. *)
Inductive block : Type :=
  | Block (body : list stmt)
  | Guard (s : stmt) (rest : block).

(** [stmt_eq same s t] says that [s] and [t] are equal once the two values of each pair of
    [same] are equal. *)
Inductive stmt_eq (same : list (positive * positive)) : stmt -> stmt -> Prop :=
  | stmt_refl s : stmt_eq same s s
  | stmt_sym s t : stmt_eq same s t -> stmt_eq same t s
  | stmt_trans s t u : stmt_eq same s t -> stmt_eq same t u -> stmt_eq same s u
  | stmt_same x v w : In (v, w) same -> stmt_eq same (Store x v) (Store x w).

(** [block_eq same b c] says that [b] and [c] are equal, and a skip at the front of a block does
    nothing. *)
Inductive block_eq (same : list (positive * positive)) : block -> block -> Prop :=
  | block_refl b : block_eq same b b
  | block_sym b c : block_eq same b c -> block_eq same c b
  | block_trans b c d : block_eq same b c -> block_eq same c d -> block_eq same b d
  | block_skip rest : block_eq same (Block (Skip :: rest)) (Block rest).

Egglog Programs from stmt_eq block_eq.

(** The equality of blocks alone, which names no statement. *)
Egglog Blocks from block_eq.

(** Cells of numbers, and grids that hold rows of cells. *)
Inductive grid : Type :=
  | Cell (n : positive)
  | Rows (rs : list (list grid)).

(** [grid_eq unions g h] says that [g] and [h] are equal once the two numbers of each pair of
    [unions] are equal. *)
Inductive grid_eq (unions : list (positive * positive)) : grid -> grid -> Prop :=
  | grid_refl g : grid_eq unions g g
  | grid_sym g h : grid_eq unions g h -> grid_eq unions h g
  | grid_trans g h k : grid_eq unions g h -> grid_eq unions h k -> grid_eq unions g k
  | grid_union x y : In (x, y) unions -> grid_eq unions (Cell x) (Cell y).

Egglog Grids from grid_eq.

(** Tags, tuples of integers, records of fields named by keys, and the value of the first field
    of a record. *)
Inductive item : Type :=
  | Tag (n : positive)
  | Tuple (vs : list Z)
  | Fields (fs : list (positive * item))
  | First (r : item).

(** Equality of items. Two tuples of equal integers are equal, and two records are equal when
    their keys are equal and their values are equal. Two first fields swap, and [First] reads
    the value of the first field. *)
Inductive item_eq : item -> item -> Prop :=
  | item_refl a : item_eq a a
  | item_sym a b : item_eq a b -> item_eq b a
  | item_trans a b c : item_eq a b -> item_eq b c -> item_eq a c
  | item_tuple vs ws : vs = ws -> item_eq (Tuple vs) (Tuple ws)
  | item_fields fs gs : Forall2 (pair_rel eq item_eq) fs gs -> item_eq (Fields fs) (Fields gs)
  | item_first a b : item_eq a b -> item_eq (First a) (First b)
  | fields_swap p q rest : item_eq (Fields (p :: q :: rest)) (Fields (q :: p :: rest))
  | first_value p rest : item_eq (First (Fields (p :: rest))) (snd p).

Egglog Items from item_eq.

(** Whether saturating [Programs] after the pairs of [same] puts two blocks in one class. *)
Definition same_block (same : list (positive * positive)) (b c : block) : bool :=
  ExampleRunner.equal Programs.program (Programs.facts same) example_limits
    (Programs.encode_block b) (Programs.encode_block c).

(** Whether saturating [Grids] after the unions puts two grids in one class. *)
Definition same_grid (unions : list (positive * positive)) (g h : grid) : bool :=
  ExampleRunner.equal Grids.program (Grids.facts unions) example_limits
    (Grids.encode_grid g) (Grids.encode_grid h).

(** Whether saturating [Items] puts two items in one class. *)
Definition same_item (a b : item) : bool :=
  ExampleRunner.equal Items.program Items.facts example_limits
    (Items.encode_item a) (Items.encode_item b).

(** * Declarations *)

Module DeclarationTests.

  (** The statements come first, as the first relation reads them, and the list tables of the
      body of a block follow the constructors of [block]. *)
  Example statements_and_blocks_have_tables :
    map name (tables Programs.spec) =
      [Programs.same_code; Programs.Skip_code; Programs.Store_code; Programs.Block_code;
       Programs.Guard_code; Programs.nil_stmt_code; Programs.cons_stmt_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** No relation of [Blocks] names the statements, and they join the program through the
      blocks that hold them, after the tables of [block]. *)
  Example held_datatype_joins_the_program :
    map name (tables Blocks.spec) =
      [Blocks.Block_code; Blocks.Guard_code; Blocks.nil_stmt_code; Blocks.cons_stmt_code;
       Blocks.Skip_code; Blocks.Store_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The tables of the outer list of a grid come before the tables of its rows. *)
  Example outer_list_tables_come_first :
    map name (tables Grids.spec) =
      [Grids.unions_code; Grids.Cell_code; Grids.Rows_code; Grids.nil_list_grid_code;
       Grids.cons_list_grid_code; Grids.nil_grid_code; Grids.cons_grid_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A row of a grid is a class in a cons node of the outer list. *)
  Example inner_list_is_a_class :
    lookup_sorts (tables Grids.spec) Grids.cons_list_grid_code = Some [SId; SId].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A grid is a chain of chains of cons nodes. *)
  Example grid_is_a_chain_of_chains :
    Grids.encode_grid (Rows [[Cell 1]]) =
      EApp Grids.Rows_code
        [EApp Grids.cons_list_grid_code
           [EApp Grids.cons_grid_code
              [EApp Grids.Cell_code [ELit 1%positive]; EApp Grids.nil_grid_code []];
            EApp Grids.nil_list_grid_code []]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The laws of tuples and records are closure laws, so they give no clause. *)
  Example laws_give_no_clause :
    length (clauses Items.spec) = 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DeclarationTests.

(** * Other datatypes *)

Module OtherDatatypeTests.

  Local Open Scope positive_scope.

  (** After the union of the values 2 and 3, the bodies of two blocks have joined statements,
      so the blocks share a class. *)
  Example blocks_of_joined_statements_share_a_class :
    same_block [(2, 3)] (Block [Store 1 2]) (Block [Store 1 3]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without the union, the two blocks stay apart. *)
  Example blocks_stay_apart_without_the_union :
    same_block [] (Block [Store 1 2]) (Block [Store 1 3]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A statement that guards a block joins too. *)
  Example guards_of_joined_statements_share_a_class :
    same_block [(2, 3)] (Guard (Store 1 2) (Block [])) (Guard (Store 1 3) (Block [])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrite of [block_skip] matches a skip at the front of a body. *)
  Example skip_at_the_front_does_nothing :
    same_block [] (Block [Skip; Store 1 2]) (Block [Store 1 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A skip after a store stays. *)
  Example skip_after_a_store_stays :
    same_block [] (Block [Store 1 2; Skip]) (Block [Store 1 2]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OtherDatatypeTests.

(** * Lists of lists *)

Module NestedListTests.

  Local Open Scope positive_scope.

  (** The union of 1 and 2 reaches an inner element of a grid. *)
  Example grids_of_joined_cells_share_a_class :
    same_grid [(1, 2)] (Rows [[Cell 1]; []]) (Rows [[Cell 2]; []]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A grid with the cell in another row stays apart. *)
  Example rows_keep_their_order :
    same_grid [(1, 2)] (Rows [[Cell 1]; []]) (Rows [[]; [Cell 2]]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The union reaches a grid inside a grid. *)
  Example nested_grids_share_a_class :
    same_grid [(1, 2)] (Rows [[Rows [[Cell 1]]]]) (Rows [[Rows [[Cell 2]]]]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NestedListTests.

(** * Pairs written as variables *)

Module PairVariableTests.

  Local Open Scope positive_scope.

  (** A record with the key 1 at the tag 10 and the key 2 at the tag 20. *)
  Definition two_fields : item := Fields [(1, Tag 10); (2, Tag 20)].

  (** The rewrite of [fields_swap] moves the two first fields as wholes. *)
  Example first_fields_swap :
    same_item two_fields (Fields [(2, Tag 20); (1, Tag 10)]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrite of [first_value] reads the second side of the first field. *)
  Example first_reads_the_first_value :
    same_item (First two_fields) (Tag 10) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** After a swap, the first value is the value of the other field. *)
  Example first_reads_the_value_after_a_swap :
    same_item (First two_fields) (Tag 20) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The value of a field with another key is no value of the record. *)
  Example other_values_stay_apart :
    same_item (First two_fields) (Tag 30) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PairVariableTests.

(** * Congruence laws *)

Module LawTests.

  Local Open Scope positive_scope.

  (** The law [item_tuple] relates two tuples of equal integers. *)
  Example equal_tuples_are_congruent :
    congruent ExampleValue.prim Items.spec Items.inputs
      (Items.encode_item (Tuple [1%Z; (-1)%Z])) (Items.encode_item (Tuple [1%Z; (-1)%Z])).
  Proof.
    apply Items.item_eq_congruent.
    apply item_tuple. reflexivity.
  Qed.

  (** The law [item_fields] relates two records whose keys are equal and whose values are
      related, here by the rewrite of [first_value]. *)
  Example related_records_are_congruent :
    congruent ExampleValue.prim Items.spec Items.inputs
      (Items.encode_item (Fields [(1, First (Fields [(2, Tag 5)]))]))
      (Items.encode_item (Fields [(1, Tag 5)])).
  Proof.
    apply Items.item_eq_congruent.
    apply item_fields.
    apply Forall2_cons; [| apply Forall2_nil].
    split; simpl; [reflexivity |].
    apply (first_value (2, Tag 5) []).
  Qed.

  (** The congruence lemma covers the laws over any two lists of fields. *)
  Example records_law_gives_congruence :
    forall fs gs, Forall2 (pair_rel eq item_eq) fs gs ->
      congruent ExampleValue.prim Items.spec Items.inputs
        (Items.encode_item (Fields fs)) (Items.encode_item (Fields gs)).
  Proof.
    intros fs gs Hall.
    apply Items.item_eq_congruent.
    exact (item_fields fs gs Hall).
  Qed.

  (** The fire lemma of a rewrite over a pair written as a variable relates the encodings of its
      two sides. *)
  Example first_value_is_congruent :
    forall p rest, congruent ExampleValue.prim Items.spec Items.inputs
      (Items.encode_item (First (Fields (p :: rest)))) (Items.encode_item (snd p)).
  Proof.
    exact (Items.first_value_fires ExampleValue.prim).
  Qed.

  (** The statements of a block give a congruence of the blocks, through [block_eq_congruent]
      and the fire lemma of [block_skip]. *)
  Example skip_gives_congruence :
    congruent ExampleValue.prim Programs.spec (Programs.inputs [])
      (Programs.encode_block (Block [Skip])) (Programs.encode_block (Block [])).
  Proof.
    apply Programs.block_eq_congruent.
    exact (block_skip [] []).
  Qed.

End LawTests.

(** * Rejections *)

Module RejectionTests.

  (** Trees whose children are in groves, and groves that hold trees. *)
  Inductive tree : Type :=
    | Leaf (n : positive)
    | Branch (kids : list grove)
  with grove : Type :=
    | Grove (t : tree).

  (** Equality of trees, with reflexivity only. *)
  Inductive tree_eq : tree -> tree -> Prop :=
    | tree_refl t : tree_eq t t.

  (** Two datatypes that hold each other have no encoders. *)
  Fail Egglog Trees from tree_eq.

  (** Points of two numbers, and lists of points. *)
  Inductive shape : Type :=
    | Point (p : positive * positive)
    | Path (ps : list (positive * positive)).

  (** A path whose first point is a variable, which the clause also uses whole. *)
  Inductive shape_eq : shape -> shape -> Prop :=
    | shape_refl s : shape_eq s s
    | path_start p rest : shape_eq (Path (p :: rest)) (Point p).

  (** A pair written as a list element stands for its two sides, which no value is. *)
  Fail Egglog Shapes from shape_eq.

  (** A law that reads the statements of two blocks by the equality of statements. *)
  Inductive body_eq (same : list (positive * positive)) : block -> block -> Prop :=
    | body_refl b : body_eq same b b
    | body_law ss ts : Forall2 (stmt_eq same) ss ts -> body_eq same (Block ss) (Block ts).

  (** A list of another datatype has no congruence law that the command reads. *)
  Fail Egglog Bodies from stmt_eq body_eq.

  (** A law that relates the rows of two grids element by element. *)
  Inductive rows_eq : grid -> grid -> Prop :=
    | rows_refl g : rows_eq g g
    | rows_law rs ss : Forall2 (Forall2 rows_eq) rs ss -> rows_eq (Rows rs) (Rows ss).

  (** A list of lists has no congruence law that the command reads. *)
  Fail Egglog RowLaws from rows_eq.

  (** A tuple read from an input list of integer lists. *)
  Inductive tuple_eq (tuples : list (positive * list Z)) : item -> item -> Prop :=
    | tuple_refl a : tuple_eq tuples a a
    | tuple_of k vs : In (k, vs) tuples -> tuple_eq tuples (Tag k) (Tuple vs).

  (** In an equation, a variable of a list type is a class, so it reads no input value. *)
  Fail Egglog Tuples from tuple_eq.

End RejectionTests.
