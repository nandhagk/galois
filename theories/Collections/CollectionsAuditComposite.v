(** * Historical composite-key work

    Callback prices here are abstract observations. Actual library component bodies are
    accounted by the concrete source-shaped models in CollectionsAuditEncoding.
    For example, pair work records both component widths.
    Builds on: CollectionsEncoding and CollectionsAuditState. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding
  CollectionsAuditState.

Record composite_costs (A B : Type) : Type := CompositeCosts {
  composite_left_encode : A -> nat;
  composite_right_encode : B -> nat
}.
Arguments composite_left_encode {A B}.
Arguments composite_right_encode {A B}.

Record composite_cost_laws {A B} (observed bound : composite_costs A B) : Prop := {
  composite_left_bound : forall a, composite_left_encode observed a <= composite_left_encode
    bound a;
  composite_right_bound : forall b, composite_right_encode observed b <= composite_right_encode
    bound b
}.

Record composite_pair_work : Type := CompositePairWork {
  composite_left_bits : nat;
  composite_right_bits : nat;
  composite_emitted_bits : nat;
  composite_stream_nodes : nat;
  composite_callback_work : nat
}.

Definition prepared_pair_work {A B} (EA : encoding A) (EB : encoding B)
    (cost : composite_costs A B) (a : A) (b : B) : composite_pair_work :=
  let left := Pos.size_nat (encode EA a) in
  let right := Pos.size_nat (encode EB b) in
  CompositePairWork left right (2 * left + 2 * right) (S (2 * left + 2 * right))
    (composite_left_encode cost a + composite_right_encode cost b).

(** The pair work record accounts for component encodings, emitted bits and callbacks. *)
Definition prepared_pair_work_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (cost : composite_costs A B) a b,
    let work := prepared_pair_work EA EB cost a b in
    composite_stream_nodes work = Pos.size_nat (key_code (prepare_key (pair_encoding EA EB)
      (a,b))) /\
    composite_emitted_bits work = 2 * composite_left_bits work + 2 * composite_right_bits work /\
    composite_callback_work work = composite_left_encode cost a + composite_right_encode cost b.

Record composite_list_costs (A : Type) : Type := CompositeListCosts {
  composite_element_encode : A -> nat
}.
Arguments composite_element_encode {A}.
Record composite_list_cost_laws {A} (observed bound : composite_list_costs A) : Prop := {
  composite_element_bound : forall a, composite_element_encode observed a <=
    composite_element_encode bound a
}.
Record composite_list_work : Type := CompositeListWork {
  composite_list_elements : nat;
  composite_list_input_bits : nat;
  composite_list_emitted_bits : nat;
  composite_list_stream_nodes : nat;
  composite_list_callbacks : nat
}.
Definition prepared_list_work {A} (EA : encoding A) (cost : composite_list_costs A) (xs : list A) :
    composite_list_work :=
  let bits := fold_right (fun a total => Pos.size_nat (encode EA a) + total) 0 xs in
  CompositeListWork (length xs) bits (2 * bits) (S (2 * bits))
    (fold_right (fun a total => composite_element_encode cost a + total) 0 xs).
(** The list work record accounts for each element, emitted bits and callbacks. *)
Definition prepared_list_work_statement : Prop :=
  forall A (EA : encoding A) (cost : composite_list_costs A) xs,
    let work := prepared_list_work EA cost xs in
    composite_list_stream_nodes work = Pos.size_nat (key_code (prepare_key (list_encoding EA)
      xs)) /\
    composite_list_elements work = length xs /\
    composite_list_emitted_bits work = 2 * composite_list_input_bits work /\
    composite_list_callbacks work = fold_right (fun a total => composite_element_encode cost a
      + total) 0 xs.
