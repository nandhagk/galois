(** * Input budgets for concrete encoders

    These budgets depend on key operands and component budgets, never returned event work.
    For example, a pair pays for both child codes and their delimiter and stream traversals.
    Builds on: CollectionsEncoding and the counted encoding bodies. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding
  CollectionsAuditEncoding.
Import List.ListNotations.

(** An external body exposes its actual execution separately from its counted adapter. *)
Record audit_encoder_adapter (K CE : Type) : Type := AuditEncoderAdapter {
  audit_encoder_run : K -> positive * list CE;
  audit_encoder_work : list CE -> nat;
  audit_encoder_budget : K -> nat;
  audit_encoder_source : K -> positive -> nat -> Prop
}.

Arguments audit_encoder_run {K CE} _ _.
Arguments audit_encoder_work {K CE} _ _.
Arguments audit_encoder_budget {K CE} _ _.
Arguments audit_encoder_source {K CE} _ _ _ _.

(** Clients prove their external source body, its returned code and its per-input budget. *)
Record audit_encoder_adapter_laws {K CE} (original : encoding K)
    (adapter : audit_encoder_adapter K CE) : Prop := AuditEncoderAdapterLaws {
  audit_encoder_source_total : forall key, exists code work,
    audit_encoder_source adapter key code work;
  audit_encoder_source_agrees : forall key code work,
    audit_encoder_source adapter key code work ->
    code = fst (audit_encoder_run adapter key) /\
    work = audit_encoder_work adapter (snd (audit_encoder_run adapter key));
  audit_encoder_code_agrees : forall key,
    fst (audit_encoder_run adapter key) = encode original key;
  audit_encoder_input_bound : forall key,
    audit_encoder_work adapter (snd (audit_encoder_run adapter key)) <=
      audit_encoder_budget adapter key
}.

Definition audit_nat_input_budget (key : nat) : nat :=
  2 * S key * S (Pos.size_nat (encode nat_encoding key)).

Definition audit_N_input_budget (key : N) : nat :=
  match key with
  | N0 => 2
  | Npos p => 2 + 2 * Pos.size_nat p
  end.

Definition audit_pair_input_budget {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB)
    (first_budget : A -> nat) (second_budget : B -> nat) (key : A * B) : nat :=
  5 + 10 * (Pos.size_nat (fst (first (fst key))) +
    Pos.size_nat (fst (second (snd key)))) +
    first_budget (fst key) + second_budget (snd key).

Fixpoint audit_child_input_budget {A} (budget : A -> nat) (keys : list A) : nat :=
  match keys with
  | [] => 0
  | key :: rest => budget key + audit_child_input_budget budget rest
  end.

Definition audit_list_input_budget {A CE} (element : A -> positive * list CE)
    (element_budget : A -> nat) (keys : list A) : nat :=
  4 + 2 * length keys + 10 * audit_encoded_bits element keys +
    audit_child_input_budget element_budget keys.

Definition audit_option_input_budget {A} (element_budget : A -> nat) (key : option A) : nat :=
  match key with
  | None => 1
  | Some a => 1 + element_budget a
  end.

Definition audit_sum_input_budget {A B} (left_budget : A -> nat) (right_budget : B -> nat)
    (key : A + B) : nat :=
  match key with
  | inl a => 1 + left_budget a
  | inr b => 1 + right_budget b
  end.

(** Every fixed base encoder has its own body and an independent operand budget. *)
Definition audit_base_encoder_input_bound_statement : Prop :=
  (forall p, audit_basic_encoding_work (snd (audit_positive_encode p)) <= 1) /\
  (forall b, audit_basic_encoding_work (snd (audit_bool_encode b)) <= 1) /\
  (forall u, audit_basic_encoding_work (snd (audit_unit_encode u)) <= 1) /\
  (forall z, audit_basic_encoding_work (snd (audit_z_encode z)) <= 1) /\
  (forall n, audit_nat_events_work (snd (audit_nat_encode n)) <= audit_nat_input_budget n) /\
  (forall n, audit_N_encoding_work (snd (audit_N_encode n)) <= audit_N_input_budget n).

(** Pair composition requires only the two actual external component call bounds. *)
Definition audit_pair_input_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget key,
    (forall a, first_work (snd (first a)) <= first_budget a) ->
    (forall b, second_work (snd (second b)) <= second_budget b) ->
    audit_pair_events_work first_work second_work (snd (audit_pair_encode first second key)) <=
      audit_pair_input_budget first second first_budget second_budget key.

(** List composition charges each original element occurrence and every emitted code bit. *)
Definition audit_list_input_bound_statement : Prop :=
  forall A CE (element : A -> positive * list CE) element_work element_budget keys,
    (forall a, element_work (snd (element a)) <= element_budget a) ->
    audit_list_events_work element_work (snd (audit_list_encode element keys)) <=
      audit_list_input_budget element element_budget keys.

(** Sum and option bounds retain the selected constructor without evaluating another body. *)
Definition audit_sum_option_input_bound_statement : Prop :=
  (forall A CE (element : A -> positive * list CE) work budget key,
    (forall a, work (snd (element a)) <= budget a) ->
    audit_option_events_work work (snd (audit_option_encode element key)) <=
      audit_option_input_budget budget key) /\
  (forall A B EA EB (left : A -> positive * list EA) (right : B -> positive * list EB)
      left_work right_work left_budget right_budget key,
    (forall a, left_work (snd (left a)) <= left_budget a) ->
    (forall b, right_work (snd (right b)) <= right_budget b) ->
    audit_sum_events_work left_work right_work (snd (audit_sum_encode left right key)) <=
      audit_sum_input_budget left_budget right_budget key).

Example audit_pair_budget_retains_width :
  audit_pair_input_budget audit_positive_encode audit_positive_encode
    (fun _ => 1) (fun _ => 1) (1%positive, 8%positive) = 57.
Proof.
  reflexivity.
Qed.

Example audit_list_budget_retains_occurrences :
  audit_list_input_budget audit_positive_encode (fun _ => 1)
    [1%positive; 1%positive] = 30.
Proof.
  reflexivity.
Qed.
