(** * Counted encoding primitives

    These candidate mirrors preserve encoder operands, outputs and intermediate stream work.
    For example, unary zero encodes to one and a successor traverses its carry bits.
    Builds on: CollectionsEncoding and the audit vocabulary. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
Import List.ListNotations.

(** * Successor and unary conversion *)

Inductive audit_nat_encoding_event : Type :=
  | AuditNatFrame (input : nat)
  | AuditPositiveSuccFrame (input output : positive).

(** This mirror visits the actual carry chain of [Pos.succ]. *)
Fixpoint audit_positive_succ (input : positive)
    : positive * list audit_nat_encoding_event :=
  match input with
  | xH => (xO xH, [AuditPositiveSuccFrame input (xO xH)])
  | xO p => (xI p, [AuditPositiveSuccFrame input (xI p)])
  | xI p =>
      let '(next, events) := audit_positive_succ p in
      (xO next, AuditPositiveSuccFrame input (xO next) :: events)
  end.

(** This mirror retains every unary constructor and every positive successor frame. *)
Fixpoint audit_nat_encode (input : nat) : positive * list audit_nat_encoding_event :=
  match input with
  | O => (xH, [AuditNatFrame input])
  | S rest =>
      let '(previous, events) := audit_nat_encode rest in
      let '(next, succ_events) := audit_positive_succ previous in
      (next, AuditNatFrame input :: events ++ succ_events)
  end.

(** Discarding successor events recovers [Pos.succ]. *)
Definition audit_positive_succ_erases_statement : Prop :=
  forall input, fst (audit_positive_succ input) = Pos.succ input.

(** Discarding the nat encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_nat_encode_erases_statement : Prop :=
  forall input, fst (audit_nat_encode input) = encode nat_encoding input.

(** The successor carry trace has at most one event per input bit. *)
Definition audit_positive_succ_count_statement : Prop :=
  forall input, length (snd (audit_positive_succ input)) <= Pos.size_nat input.

(** Unary encoding events are bounded by the input and encoded output widths. *)
Definition audit_nat_encode_count_statement : Prop :=
  forall input, length (snd (audit_nat_encode input)) <=
    S input * S (Pos.size_nat (encode nat_encoding input)).

(** * Source-indexed unary and carry derivations *)

(** Each successor rule preserves the concrete carry suffix and output constructor. *)
Inductive audit_positive_succ_run : positive -> positive -> list audit_nat_encoding_event ->
    nat -> Prop :=
  | AuditSuccOne : audit_positive_succ_run xH (xO xH) [AuditPositiveSuccFrame xH (xO xH)] 2
  | AuditSuccZero : forall p,
      audit_positive_succ_run (xO p) (xI p) [AuditPositiveSuccFrame (xO p) (xI p)] 2
  | AuditSuccCarry : forall p result events work,
      audit_positive_succ_run p result events work ->
      audit_positive_succ_run (xI p) (xO result)
        (AuditPositiveSuccFrame (xI p) (xO result) :: events) (2 + work).

(** A positive succ source run agrees with the counted result and its work bounds. *)
Definition audit_positive_succ_run_correct_statement : Prop :=
  forall input output events work,
    audit_positive_succ_run input output events work ->
    output = Pos.succ input /\ (output, events) = audit_positive_succ input /\
    work = 2 * length events /\ work <= 2 * Pos.size_nat input.

(** Every positive succ input has a corresponding source run. *)
Definition audit_positive_succ_run_total_statement : Prop :=
  forall input, exists output events work, audit_positive_succ_run input output events work.

(** Each unary step composes the actual successor derivation for that prior result. *)
Inductive audit_nat_encode_run : nat -> positive -> list audit_nat_encoding_event -> nat -> Prop :=
  | AuditNatZero : audit_nat_encode_run 0 xH [AuditNatFrame 0] 2
  | AuditNatSuccessor : forall input previous output events succ_events work succ_work,
      audit_nat_encode_run input previous events work ->
      audit_positive_succ_run previous output succ_events succ_work ->
      audit_nat_encode_run (S input) output (AuditNatFrame (S input) :: events ++ succ_events)
        (2 + work + succ_work).

(** A nat encode source run agrees with the counted result and its work bounds. *)
Definition audit_nat_encode_run_correct_statement : Prop :=
  forall input output events work,
    audit_nat_encode_run input output events work ->
    output = encode nat_encoding input /\ (output, events) = audit_nat_encode input /\
    work = 2 * length events /\
    work <= 2 * S input * S (Pos.size_nat (encode nat_encoding input)).

(** Every nat encode input has a corresponding source run. *)
Definition audit_nat_encode_run_total_statement : Prop :=
  forall input, exists output events work, audit_nat_encode_run input output events work.

(** * Fixed primitive encoding adapters *)

Inductive audit_basic_encoding_event (K : Type) : Type :=
  | AuditBasicEncoding (input : K) (output : positive).

Arguments AuditBasicEncoding {K} _ _.

Definition audit_positive_encode (input : positive)
    : positive * list (audit_basic_encoding_event positive) :=
  (input, [AuditBasicEncoding input input]).

Definition audit_bool_encode (input : bool) : positive * list (audit_basic_encoding_event bool) :=
  let output := if input then xO xH else xH in (output, [AuditBasicEncoding input output]).

Definition audit_unit_encode (input : unit) : positive * list (audit_basic_encoding_event unit) :=
  (xH, [AuditBasicEncoding input xH]).

Definition audit_z_encode (input : Z) : positive * list (audit_basic_encoding_event Z) :=
  let output := match input with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end in
  (output, [AuditBasicEncoding input output]).

Inductive audit_n_encoding_event : Type :=
  | AuditNEncoding (input : N) (output : positive)
  | AuditNSucc (event : audit_nat_encoding_event).

(** Binary conversion retains the actual successor carry frames. *)
Definition audit_N_encode (input : N) : positive * list audit_n_encoding_event :=
  match input with
  | N0 => (xH, [AuditNEncoding input xH])
  | Npos p =>
      let '(output, events) := audit_positive_succ p in
      (output, AuditNEncoding input output :: map AuditNSucc events)
  end.

(** Discarding the N encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_N_encode_erases_statement : Prop :=
  forall input, fst (audit_N_encode input) = encode N_encoding input.

(** Primitive source cases preserve their actual exact returned codes. *)
Definition audit_positive_encode_erases_statement : Prop :=
  forall input, fst (audit_positive_encode input) = encode positive_encoding input.

(** Discarding the bool encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_bool_encode_erases_statement : Prop :=
  forall input, fst (audit_bool_encode input) = encode bool_encoding input.

(** Discarding the unit encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_unit_encode_erases_statement : Prop :=
  forall input, fst (audit_unit_encode input) = encode unit_encoding input.

(** Discarding the z encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_z_encode_erases_statement : Prop :=
  forall input, fst (audit_z_encode input) = encode Z_encoding input.

(** * Delimited stream construction *)

Inductive audit_encoding_frame : Type :=
  | AuditEmitCode (input : positive) (tail output : list bool)
  | AuditStreamPositive (input : list bool) (output : positive).

(** Every frame includes the actual tail and returned stream. *)
Fixpoint audit_emit_code (input : positive) (tail : list bool)
    : list bool * list audit_encoding_frame :=
  match input with
  | xH =>
      let output := false :: true :: tail in
      (output, [AuditEmitCode input tail output])
  | xO rest =>
      let '(suffix, events) := audit_emit_code rest tail in
      let output := false :: false :: suffix in
      (output, AuditEmitCode input tail output :: events)
  | xI rest =>
      let '(suffix, events) := audit_emit_code rest tail in
      let output := true :: true :: suffix in
      (output, AuditEmitCode input tail output :: events)
  end.

(** Each stream constructor preserves its actual suffix and final positive code. *)
Fixpoint audit_stream_positive (input : list bool) : positive * list audit_encoding_frame :=
  match input with
  | [] => (xH, [AuditStreamPositive input xH])
  | false :: rest =>
      let '(next, events) := audit_stream_positive rest in
      (xO next, AuditStreamPositive input (xO next) :: events)
  | true :: rest =>
      let '(next, events) := audit_stream_positive rest in
      (xI next, AuditStreamPositive input (xI next) :: events)
  end.

(** Discarding the emit code events recovers the corresponding original operation under its
  premises. *)
Definition audit_emit_code_erases_statement : Prop :=
  forall p tail, fst (audit_emit_code p tail) = emit_code p tail.

(** Discarding the stream positive events recovers the corresponding original operation under
  its premises. *)
Definition audit_stream_positive_erases_statement : Prop :=
  forall bits, fst (audit_stream_positive bits) = stream_positive bits.

(** * Pair composition *)

Inductive audit_pair_event (A B EA EB : Type) : Type :=
  | AuditPairFirst (input : A) (output : positive) (events : list EA)
  | AuditPairSecond (input : B) (output : positive) (events : list EB)
  | AuditPairFrame (event : audit_encoding_frame).

Arguments AuditPairFirst {A B EA EB} _ _ _.
Arguments AuditPairSecond {A B EA EB} _ _ _.
Arguments AuditPairFrame {A B EA EB} _.

(** Actual component traces are retained, not replaced by a price or discarded on composition. *)
Definition audit_pair_encode {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB) (input : A * B)
    : positive * list (audit_pair_event A B EA EB) :=
  let '(a, b) := input in
  let '(ac, ae) := first a in
  let '(bc, be) := second b in
  let '(bt, bframes) := audit_emit_code bc [] in
  let '(stream, aframes) := audit_emit_code ac bt in
  let '(result, sframes) := audit_stream_positive stream in
  (result, [AuditPairFirst a ac ae; AuditPairSecond b bc be] ++
    map AuditPairFrame (bframes ++ aframes ++ sframes)).

(** Component erasure applies only to these actual calls; internal components prove it
  separately. *)
Definition audit_pair_encode_erases_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      (e1 : encoding A) (e2 : encoding B) (a : A) (b : B),
    fst (first a) = encode e1 a -> fst (second b) = encode e2 b ->
    fst (audit_pair_encode first second (a, b)) = encode (pair_encoding e1 e2) (a, b).

(** * List, option and sum composition *)

Inductive audit_list_event (A E : Type) : Type :=
  | AuditListCase (input : list A)
  | AuditListComponent (input : A) (output : positive) (events : list E)
  | AuditListFrame (event : audit_encoding_frame).

Arguments AuditListCase {A E} _.
Arguments AuditListComponent {A E} _ _ _.
Arguments AuditListFrame {A E} _.

(** Each list element is encoded once, including its own actual nested event sequence. *)
Fixpoint audit_emit_list {A E} (element : A -> positive * list E) (input : list A)
    : list bool * list (audit_list_event A E) :=
  match input with
  | [] => ([], [AuditListCase input])
  | x :: rest =>
      let '(code, component_events) := element x in
      let '(tail, tail_events) := audit_emit_list element rest in
      let '(result, frames) := audit_emit_code code tail in
      (result, [AuditListCase input; AuditListComponent x code component_events] ++
        tail_events ++ map AuditListFrame frames)
  end.

(** The stream conversion follows the exact emitted list and keeps all its frames. *)
Definition audit_list_encode {A E} (element : A -> positive * list E) (input : list A)
    : positive * list (audit_list_event A E) :=
  let '(bits, events) := audit_emit_list element input in
  let '(result, frames) := audit_stream_positive bits in
  (result, events ++ map AuditListFrame frames).

(** Discarding the emit list events recovers the corresponding original operation under its
  premises. *)
Definition audit_emit_list_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : list A),
    (forall x, In x input -> fst (element x) = encode enc x) ->
    fst (audit_emit_list element input) = emit_list enc input.

(** Discarding the list encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_list_encode_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : list A),
    (forall x, In x input -> fst (element x) = encode enc x) ->
    fst (audit_list_encode element input) = encode (list_encoding enc) input.

Inductive audit_sum_event (A B EA EB : Type) : Type :=
  | AuditSumLeft (input : A) (code : positive) (events : list EA)
  | AuditSumRight (input : B) (code : positive) (events : list EB).

Arguments AuditSumLeft {A B EA EB} _ _ _.
Arguments AuditSumRight {A B EA EB} _ _ _.

(** Sum encoding evaluates only the selected actual component. *)
Definition audit_sum_encode {A B EA EB}
    (left : A -> positive * list EA) (right : B -> positive * list EB) (input : A + B)
    : positive * list (audit_sum_event A B EA EB) :=
  match input with
  | inl a => let '(code, events) := left a in (xO code, [AuditSumLeft a code events])
  | inr b => let '(code, events) := right b in (xI code, [AuditSumRight b code events])
  end.

(** Discarding the sum encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_sum_encode_erases_statement : Prop :=
  forall A B EA EB (left : A -> positive * list EA) (right : B -> positive * list EB)
      (e1 : encoding A) (e2 : encoding B) (input : A + B),
    (forall a, input = inl a -> fst (left a) = encode e1 a) ->
    (forall b, input = inr b -> fst (right b) = encode e2 b) ->
    fst (audit_sum_encode left right input) = encode (sum_encoding e1 e2) input.

Inductive audit_option_event (A E : Type) : Type :=
  | AuditOptionNone
  | AuditOptionSome (input : A) (code : positive) (events : list E).

Arguments AuditOptionNone {A E}.
Arguments AuditOptionSome {A E} _ _ _.

Definition audit_option_encode {A E} (element : A -> positive * list E) (input : option A)
    : positive * list (audit_option_event A E) :=
  match input with
  | None => (xH, [AuditOptionNone])
  | Some a => let '(code, events) := element a in (xO code, [AuditOptionSome a code events])
  end.

(** Discarding the option encode events recovers the corresponding original operation under its
  premises. *)
Definition audit_option_encode_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : option A),
    (forall a, input = Some a -> fst (element a) = encode enc a) ->
    fst (audit_option_encode element input) = encode (option_encoding enc) input.

(** * Fixed event folds *)

(** Fixed positive source-frame charges distinguish delimiter and stream cases. *)
Definition audit_encoding_frame_charge (event : audit_encoding_frame) : nat :=
  match event with
  | AuditEmitCode _ _ _ => 4
  | AuditStreamPositive _ _ => 3
  end.

Fixpoint audit_encoding_frames_work (events : list audit_encoding_frame) : nat :=
  match events with
  | [] => 0
  | event :: rest => audit_encoding_frame_charge event + audit_encoding_frames_work rest
  end.

(** Unary frames and base constructors have fixed, operand-independent event charges. *)
Definition audit_nat_events_work (events : list audit_nat_encoding_event) : nat := 2 * length
  events.

Definition audit_basic_encoding_work {K} (events : list (audit_basic_encoding_event K)) : nat :=
  length events.

Definition audit_N_encoding_work (events : list audit_n_encoding_event) : nat :=
  2 * length events.

(** The supplied folds consume actual child traces; library children use their fixed folds. *)
Fixpoint audit_pair_events_work {A B EA EB}
    (first_work : list EA -> nat) (second_work : list EB -> nat)
    (events : list (audit_pair_event A B EA EB)) : nat :=
  match events with
  | [] => 0
  | AuditPairFirst _ _ child :: rest => 1 + first_work child +
      audit_pair_events_work first_work second_work rest
  | AuditPairSecond _ _ child :: rest => 1 + second_work child +
      audit_pair_events_work first_work second_work rest
  | AuditPairFrame frame :: rest => audit_encoding_frame_charge frame +
      audit_pair_events_work first_work second_work rest
  end.

Fixpoint audit_list_events_work {A E} (child_work : list E -> nat)
    (events : list (audit_list_event A E)) : nat :=
  match events with
  | [] => 0
  | AuditListCase _ :: rest => 1 + audit_list_events_work child_work rest
  | AuditListComponent _ _ child :: rest => 1 + child_work child +
      audit_list_events_work child_work rest
  | AuditListFrame frame :: rest => audit_encoding_frame_charge frame +
      audit_list_events_work child_work rest
  end.

Fixpoint audit_sum_events_work {A B EA EB}
    (left_work : list EA -> nat) (right_work : list EB -> nat)
    (events : list (audit_sum_event A B EA EB)) : nat :=
  match events with
  | [] => 0
  | AuditSumLeft _ _ child :: rest => 1 + left_work child +
      audit_sum_events_work left_work right_work rest
  | AuditSumRight _ _ child :: rest => 1 + right_work child +
      audit_sum_events_work left_work right_work rest
  end.

Fixpoint audit_option_events_work {A E} (child_work : list E -> nat)
    (events : list (audit_option_event A E)) : nat :=
  match events with
  | [] => 0
  | AuditOptionNone :: rest => 1 + audit_option_events_work child_work rest
  | AuditOptionSome _ _ child :: rest => 1 + child_work child +
      audit_option_events_work child_work rest
  end.

(** The original key operands determine emitted bit counts without event self-bounds. *)
Fixpoint audit_encoded_bits {A E} (element : A -> positive * list E) (input : list A) : nat :=
  match input with
  | [] => 0
  | x :: rest => Pos.size_nat (fst (element x)) + audit_encoded_bits element rest
  end.

(** Code emission produces one event per input bit. *)
Definition audit_emit_code_count_statement : Prop :=
  forall code tail, length (snd (audit_emit_code code tail)) = Pos.size_nat code.

(** Positive stream construction emits one event per bit plus the terminal frame. *)
Definition audit_stream_positive_count_statement : Prop :=
  forall bits, length (snd (audit_stream_positive bits)) = S (length bits).

(** List emission counts two frames per element, one terminal frame and the emitted bits. *)
Definition audit_emit_list_count_statement : Prop :=
  forall A E (element : A -> positive * list E) input,
    length (snd (audit_emit_list element input)) =
      1 + 2 * length input + audit_encoded_bits element input.

(** List encoding counts two frames, two per element and three per encoded bit. *)
Definition audit_list_encode_count_statement : Prop :=
  forall A E (element : A -> positive * list E) input,
    length (snd (audit_list_encode element input)) =
      2 + 2 * length input + 3 * audit_encoded_bits element input.

(** Pair encoding counts its frames and the widths of both encoded components. *)
Definition audit_pair_encode_count_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB) a b,
    length (snd (audit_pair_encode first second (a, b))) =
      3 + 3 * (Pos.size_nat (fst (first a)) + Pos.size_nat (fst (second b))).
