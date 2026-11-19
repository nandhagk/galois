(** * Lists of classes in derived programs

    Datatypes whose constructors hold lists, read by [Egglog] and run on the engine. The command
    encodes a list whose elements have the type [T] as a chain of nodes of two constructor
    tables, [nil_T] and [cons_T], so the congruence closure of the engine joins two lists whose
    elements it joins, as egglog rebuilds its vectors. The law [Forall2 R xs ys -> R (C xs)
    (C ys)] is the congruence of a list argument, and the generated lemma [<R>_congruent] covers
    it. A list may hold values, and a list of pairs from values to classes is an association
    list.
    For example, after the union of [Num 1] and [Num 2], the vectors [[Num 1; Num 2]] and
    [[Num 2; Num 2]] share a class, and so do [MyVec] of each.

    Groups:
    - [DeclarationTests] The tables nil and cons of each element type, with their sorts.
    - [EncoderTests] The encoder of a datatype encodes a list as a chain of cons nodes.
    - [RebuildTests] The first block of egglog's [container-rebuild.egg].
    - [PatternTests] Rewrites that match [[]], [x :: t] and list literals.
    - [ValueListTests] A list of integers in a clause.
    - [AssociationTests] A list of pairs from keys to classes, read by a lookup.
    - [ConditionTests] The conditions of the theorems hold for a program with lists.
    - [GlueTests] The generated lemmas over lists.
    - [RejectionTests] The command stops at lists that it cannot encode.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Encode Derive CongruenceRefSig.
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

(** Numbers and vectors of terms, as in the first block of egglog's [container-rebuild.egg]. *)
Inductive math : Type :=
  | Num (n : positive)
  | MyVec (xs : list math).

(** [math_eq unions t u] says that [t] and [u] are equal once the two numbers of each pair of
    [unions] are equal. Two vectors are equal when their elements are equal one by one. *)
Inductive math_eq (unions : list (positive * positive)) : math -> math -> Prop :=
  | math_refl t : math_eq unions t t
  | math_sym t u : math_eq unions t u -> math_eq unions u t
  | math_trans t u w : math_eq unions t u -> math_eq unions u w -> math_eq unions t w
  | math_vec xs ys : Forall2 (math_eq unions) xs ys -> math_eq unions (MyVec xs) (MyVec ys)
  | math_union x y : In (x, y) unions -> math_eq unions (Num x) (Num y).

Egglog Vectors from math_eq.

(** Numbers, products of two terms and products of lists of terms. *)
Inductive arith : Type :=
  | Number (n : positive)
  | Mul (a b : arith)
  | Prod (xs : list arith).

(** Equality of terms. The product of no factor is one, a list of factors multiplies its first
    factor with the product of the rest, two factors swap, one is neutral and multiplication
    commutes. *)
Inductive arith_eq : arith -> arith -> Prop :=
  | arith_refl a : arith_eq a a
  | arith_sym a b : arith_eq a b -> arith_eq b a
  | arith_trans a b c : arith_eq a b -> arith_eq b c -> arith_eq a c
  | arith_mul a a' b b' : arith_eq a a' -> arith_eq b b' -> arith_eq (Mul a b) (Mul a' b')
  | arith_prod xs ys : Forall2 arith_eq xs ys -> arith_eq (Prod xs) (Prod ys)
  | prod_nil : arith_eq (Prod []) (Number 1)
  | prod_cons x t : arith_eq (Prod (x :: t)) (Mul x (Prod t))
  | prod_swap a b : arith_eq (Prod [a; b]) (Prod [b; a])
  | mul_one a : arith_eq (Mul a (Number 1)) a
  | mul_comm a b : arith_eq (Mul a b) (Mul b a).

Egglog Products from arith_eq.

(** The comparison of two keys, as a primitive. *)
Egglog Primitives Keys Pos.eqb.

(** Tags, tuples of integers, records of fields named by keys, and the field of a record. *)
Inductive item : Type :=
  | Tag (n : positive)
  | Tuple (vs : list Z)
  | Fields (fs : list (positive * item))
  | Get (k : positive) (r : item).

(** Equality of items. The tuple [(1, -1)] is the tag 1, and the field of a record at a key is
    the value of the first field with that key. *)
Inductive item_eq : item -> item -> Prop :=
  | item_refl a : item_eq a a
  | item_sym a b : item_eq a b -> item_eq b a
  | item_trans a b c : item_eq a b -> item_eq b c -> item_eq a c
  | item_get k a b : item_eq a b -> item_eq (Get k a) (Get k b)
  | tuple_tag : item_eq (Tuple [1%Z; (-1)%Z]) (Tag 1)
  | get_here k v rest : item_eq (Get k (Fields ((k, v) :: rest))) v
  | get_next k k' v rest : Pos.eqb k k' = false ->
      item_eq (Get k (Fields ((k', v) :: rest))) (Get k (Fields rest)).

Egglog Items from item_eq with Keys.

(** The primitive function of [Items] is the one that [Keys] generated. *)
Module KeysValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Keys.prim.
  Definition merge (_ : positive) := Pos.max.
End KeysValue.

Module KeysIndex := IndexCode KeysValue.
Module KeysJoin := JoinCode KeysValue KeysIndex.
Module KeysDatabase := DatabaseCode KeysValue KeysIndex.
Module KeysRun := RunCode KeysValue KeysIndex KeysJoin KeysDatabase.
Module KeysRunner := RunnerCode KeysValue KeysIndex KeysJoin KeysDatabase KeysRun.

(** Whether saturating [Vectors] after the unions puts two terms in one class. *)
Definition joined (unions : list (positive * positive)) (a b : math) : bool :=
  ExampleRunner.equal Vectors.program (Vectors.facts unions) example_limits
    (Vectors.encode_math a) (Vectors.encode_math b).

(** Whether saturating [Products] puts two terms in one class. *)
Definition same_product (a b : arith) : bool :=
  ExampleRunner.equal Products.program Products.facts example_limits
    (Products.encode_arith a) (Products.encode_arith b).

(** Whether saturating [Items] puts two items in one class. *)
Definition same_item (a b : item) : bool :=
  KeysRunner.equal Items.program Items.facts example_limits
    (Items.encode_item a) (Items.encode_item b).

(** * Declarations *)

Module DeclarationTests.

  (** The tables of the nodes of a pattern, in prefix order. *)
  Fixpoint pat_nodes (p : pat positive) : list positive :=
    match p with
    | PNode f args =>
        f :: (fix go (ps : list (pat positive)) : list positive :=
                match ps with
                | [] => []
                | q :: rest => pat_nodes q ++ go rest
                end) args
    | _ => []
    end.

  (** The node tables of the left side of the head of a clause. *)
  Definition left_nodes (c : clause positive) : list positive :=
    match head c with
    | Unify l _ | Rewrites l _ => pat_nodes l
    | _ => []
    end.

  (** The tables nil and cons of the elements of a vector follow the constructors of the
      datatype. *)
  Example list_tables_follow_the_constructors :
    map name (tables Vectors.spec) =
      [Vectors.unions_code; Vectors.Num_code; Vectors.MyVec_code; Vectors.nil_math_code;
       Vectors.cons_math_code].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The list tables build classes, as the constructors of a datatype do. *)
  Example list_tables_build_classes :
    map out (tables Vectors.spec) = [ORel; OId; OId; OId; OId].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A vector is one class argument, nil takes no argument, and cons takes the class of an
      element and the class of the rest. *)
  Example list_argument_is_a_class :
    map arg_sorts (tables Vectors.spec) = [[SVal; SVal]; [SVal]; [SId]; []; [SId; SId]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cons of a list of integers takes a value and the class of the rest. *)
  Example value_cons_takes_a_value :
    lookup_sorts (tables Items.spec) Items.cons_Z_code = Some [SVal; SId].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The cons of an association list takes the key, the class of the value and the class of the
      rest. *)
  Example pair_cons_takes_both_sides :
    lookup_sorts (tables Items.spec) Items.cons_positive_item_code = Some [SVal; SId; SId].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The law over [Forall2] is the congruence of [MyVec], so the union of numbers is the only
      clause. *)
  Example list_law_gives_no_clause :
    length (clauses Vectors.spec) = 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The left sides read [[]] as a nil node, [x :: t] as a cons node over a class [t], and the
      literal [[a; b]] as two cons nodes and a nil node. *)
  Example list_patterns_are_nodes :
    map left_nodes (clauses Products.spec) =
      [[Products.Prod_code; Products.nil_arith_code];
       [Products.Prod_code; Products.cons_arith_code];
       [Products.Prod_code; Products.cons_arith_code; Products.cons_arith_code;
        Products.nil_arith_code];
       [Products.Mul_code; Products.Number_code];
       [Products.Mul_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

End DeclarationTests.

(** * Encoders *)

Module EncoderTests.

  Local Open Scope positive_scope.

  (** The empty vector is the node of [nil]. *)
  Example empty_vector_is_nil :
    Vectors.encode_math (MyVec []) = EApp Vectors.MyVec_code [EApp Vectors.nil_math_code []].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A vector is a chain of cons nodes that ends in the node of [nil]. *)
  Example vector_is_a_chain_of_cons_nodes :
    Vectors.encode_math (MyVec [Num 1]) =
      EApp Vectors.MyVec_code
        [EApp Vectors.cons_math_code
           [EApp Vectors.Num_code [ELit 1]; EApp Vectors.nil_math_code []]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An integer in a list is the literal of its encoding. *)
  Example integer_element_is_a_literal :
    Items.encode_item (Tuple [(-1)%Z]) =
      EApp Items.Tuple_code
        [EApp Items.cons_Z_code [ELit (ZEncode.encode (-1)); EApp Items.nil_Z_code []]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A pair in a list gives two arguments of its cons node. *)
  Example pair_element_gives_two_arguments :
    Items.encode_item (Fields [(1, Tag 2)]) =
      EApp Items.Fields_code
        [EApp Items.cons_positive_item_code
           [ELit 1; EApp Items.Tag_code [ELit 2]; EApp Items.nil_positive_item_code []]].
  Proof.
    vm_compute. reflexivity.
  Qed.

End EncoderTests.

(** * Rebuilding vectors *)

Module RebuildTests.

  Local Open Scope positive_scope.

  (** After the union of 1 and 2, the vectors [[1; 2]] and [[2; 2]] have joined elements, so
      their nodes [MyVec] share a class. *)
  Example vectors_of_joined_elements_share_a_class :
    joined [(1, 2)] (MyVec [Num 1; Num 2]) (MyVec [Num 2; Num 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without the union, the two vectors stay apart. *)
  Example vectors_stay_apart_without_the_union :
    joined [] (MyVec [Num 1; Num 2]) (MyVec [Num 2; Num 2]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A vector of another length stays apart, although its elements are joined. *)
  Example vector_of_another_length_stays_apart :
    joined [(1, 2)] (MyVec [Num 1]) (MyVec [Num 2; Num 2]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each element joins by its own union, as the second vector of the egglog block does. *)
  Example each_element_joins_by_its_union :
    joined [(4, 6); (5, 7)] (MyVec [Num 4; Num 5]) (MyVec [Num 6; Num 7]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rebuild reaches vectors of vectors. *)
  Example nested_vectors_share_a_class :
    joined [(1, 2)] (MyVec [MyVec [Num 1]]) (MyVec [MyVec [Num 2]]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RebuildTests.

(** * Patterns *)

Module PatternTests.

  Local Open Scope positive_scope.

  (** The rewrite of [[]] makes the empty product one. *)
  Example empty_product_is_one :
    same_product (Prod []) (Number 1) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrite of [x :: t] unfolds the product of two factors into multiplications, and one
      is neutral, so the product is the multiplication of the factors. *)
  Example product_unfolds_into_multiplications :
    same_product (Prod [Number 2; Number 3]) (Mul (Number 2) (Number 3)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A product of one factor stays apart from another number. *)
  Example product_keeps_its_factor :
    same_product (Prod [Number 2]) (Number 3) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrites of products build finitely many terms, so the run saturates. *)
  Example product_rewrites_saturate :
    fst (fst (ExampleRunner.saturate Products.program Products.facts
      [Products.encode_arith (Prod [Number 2; Number 3])] example_limits)) = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PatternTests.

(** * Lists of values *)

Module ValueListTests.

  Local Open Scope positive_scope.

  (** The tuple [(1, -1)] matches the literal of the clause [tuple_tag]. *)
  Example tuple_matches_its_literal :
    same_item (Tuple [1%Z; (-1)%Z]) (Tag 1) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The tuple [(-1, 1)] has its integers in another order, so it matches no clause. *)
  Example tuple_order_matters :
    same_item (Tuple [(-1)%Z; 1%Z]) (Tag 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ValueListTests.

(** * Association lists *)

Module AssociationTests.

  Local Open Scope positive_scope.

  (** A record with the key 1 at the tag 10 and the key 2 at the tag 20. *)
  Definition two_fields : item := Fields [(1, Tag 10); (2, Tag 20)].

  (** A record with the key 1 twice. *)
  Definition repeated_key : item := Fields [(1, Tag 10); (1, Tag 20)].

  (** The lookup of the key 2 skips the field of the key 1 and finds the tag 20. *)
  Example lookup_finds_a_later_key :
    same_item (Get 2 two_fields) (Tag 20) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lookup of the key 2 does not find the value of the key 1. *)
  Example lookup_skips_other_keys :
    same_item (Get 2 two_fields) (Tag 10) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key that no field has finds no value. *)
  Example missing_key_finds_nothing :
    same_item (Get 3 two_fields) (Tag 10) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The first field of a repeated key gives its value. *)
  Example first_field_of_a_key_wins :
    same_item (Get 1 repeated_key) (Tag 10) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A later field of a repeated key is not its value. *)
  Example later_field_of_a_key_loses :
    same_item (Get 1 repeated_key) (Tag 20) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssociationTests.

(** * Conditions *)

Module ConditionTests.

  Local Open Scope positive_scope.

  (** The engine accepts the sorts and the kinds of the program of vectors. *)
  Example vectors_are_well_sorted :
    spec_ok Vectors.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The program of vectors has only unions over input rows, so the ground theorems cover it. *)
  Example vectors_are_ground :
    ground Vectors.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An encoded vector is a well-sorted term of the program. *)
  Example encoded_vector_is_a_term :
    term_ok Vectors.spec (Vectors.encode_math (MyVec [Num 1; MyVec []])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The facts of the unions are input rows. *)
  Example union_facts_are_input_rows :
    rows_ok Vectors.spec (Vectors.facts [(1, 2)]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConditionTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** Trees whose nodes carry a label and a list of children. *)
  Inductive tree : Type :=
    | Leaf (n : positive)
    | Node (label : tree) (kids : list tree).

  (** Equality of trees: the closure laws, and the congruence of a node in its label and in its
      children. *)
  Inductive tree_eq : tree -> tree -> Prop :=
    | tree_refl t : tree_eq t t
    | tree_sym t u : tree_eq t u -> tree_eq u t
    | tree_trans t u w : tree_eq t u -> tree_eq u w -> tree_eq t w
    | tree_node a b xs ys : tree_eq a b -> Forall2 tree_eq xs ys ->
        tree_eq (Node a xs) (Node b ys).

  Egglog Trees from tree_eq.

  (** The congruence lemma turns two vectors of equal elements into the congruence of their
      encodings. *)
  Example equal_vectors_are_congruent :
    congruent ExampleValue.prim Vectors.spec (Vectors.inputs [(1, 2)])
      (Vectors.encode_math (MyVec [Num 1; Num 2])) (Vectors.encode_math (MyVec [Num 2; Num 2])).
  Proof.
    apply Vectors.math_eq_congruent.
    apply math_vec.
    apply Forall2_cons; [apply math_union; simpl; auto |].
    apply Forall2_cons; [apply math_refl | apply Forall2_nil].
  Qed.

  (** The congruence lemma covers a law over a class and a list together. *)
  Example node_law_gives_congruence :
    forall a b xs ys, tree_eq a b -> Forall2 tree_eq xs ys ->
      congruent ExampleValue.prim Trees.spec Trees.inputs
        (Trees.encode_tree (Node a xs)) (Trees.encode_tree (Node b ys)).
  Proof.
    intros a b xs ys Hab Hall.
    apply Trees.tree_eq_congruent.
    exact (tree_node a b xs ys Hab Hall).
  Qed.

  (** The fire lemma of a rewrite over a list variable relates the encodings of its two
      sides. *)
  Example rest_of_a_product_is_congruent :
    forall x t, congruent ExampleValue.prim Products.spec Products.inputs
      (Products.encode_arith (Prod (x :: t))) (Products.encode_arith (Mul x (Prod t))).
  Proof.
    exact (Products.prod_cons_fires ExampleValue.prim).
  Qed.

End GlueTests.

(** * Rejections *)

Module RejectionTests.

  (** Another relation between the elements of two vectors. *)
  Inductive other_rel : math -> math -> Prop :=
    | other_same a : other_rel a a.

  (** An equality of vectors whose law reads the elements by [other_rel]. *)
  Inductive related_eq : math -> math -> Prop :=
    | related_refl a : related_eq a a
    | related_vec xs ys : Forall2 other_rel xs ys -> related_eq (MyVec xs) (MyVec ys).

  (** A batch of numbers in an input list. *)
  Inductive batch : Type :=
    | Batch (xs : list positive).

  (** [batched bs x] says that a batch of [bs] holds [x] alone. *)
  Inductive batched (bs : list batch) : positive -> Prop :=
    | batched_one x : In (Batch [x]) bs -> batched bs x.

  (** The law of a list argument relates the elements by another relation. *)
  Fail Egglog Related from related_eq.

  (** An input constructor holds a list value, and a pattern writes a variable inside it. *)
  Fail Egglog Batches from batched.

End RejectionTests.
