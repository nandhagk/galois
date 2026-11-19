(** * Literals and calls over registered value types

    Clauses over [Z] and [string] that hold literals and calls of primitives, read by [Egglog]
    and run on the engine. The encoder of a registered type is opaque to [simpl], so the
    encoding of a literal keeps the form [encode c] in the glue lemmas, and their tactics decode
    it as they decode the encoding of a variable. The generated lemmas prove for these clauses as
    they do over [positive].
    For example, the conclusion [counter (Z.add x 1)] of [counter_next] computes its value with
    the primitive [Z.add], and the run derives the row of [counter 3] in three steps from the
    literal of [counter_zero].

    Groups:
    - [CallTests] A call of a primitive over [Z] in a conclusion.
    - [HeadLiteralTests] Literals of [Z] and of [string] in conclusions.
    - [PremiseLiteralTests] Literals of [Z] and of [string] in premises.
    - [GlueTests] The generated lemmas in both directions.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith String.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Encode Derive.
Import List.ListNotations.

(** * Fixtures *)

(** Addition on integers. *)
Egglog Primitives ZOps Z.add.

(** Values are positives, and the primitive function is the one that [ZOps] generated. *)
Module ZOpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := ZOps.prim.
  Definition merge (_ : positive) := Pos.max.
End ZOpsValue.

Module ZOpsIndex := IndexCode ZOpsValue.
Module ZOpsJoin := JoinCode ZOpsValue ZOpsIndex.
Module ZOpsDatabase := DatabaseCode ZOpsValue ZOpsIndex.
Module ZOpsRun := RunCode ZOpsValue ZOpsIndex ZOpsJoin ZOpsDatabase.
Module ZOpsRunner := RunnerCode ZOpsValue ZOpsIndex ZOpsJoin ZOpsDatabase ZOpsRun.

(** [counter z] says that [z] counts up from zero by ones. *)
Inductive counter : Z -> Prop :=
  | counter_zero : counter 0
  | counter_next x : counter x -> counter (Z.add x 1).

(** [past_two z] says that the count reaches 2 and [z]. *)
Inductive past_two : Z -> Prop :=
  | past_two_at x : counter 2 -> counter x -> past_two x.

Egglog Counters from counter past_two with ZOps.

(** [greeting s] says that [s] is a greeting. *)
Inductive greeting : string -> Prop :=
  | greeting_hello : greeting "hello"
  | greeting_hi : greeting "hi".

(** [answer s] says that [s] answers a greeting [hello]. *)
Inductive answer : string -> Prop :=
  | answer_hello : greeting "hello" -> answer "hi".

Egglog Greetings from greeting answer.

(** The database after a run of [Counters] with at most [n] iterations. *)
Definition count_result (n : N) : ZOpsDatabase.t :=
  snd (ZOpsRunner.solve Counters.program Counters.facts (Limits n 1000%N)).

(** The database after a run of [Greetings]. *)
Definition greeting_result : ZOpsDatabase.t :=
  snd (ZOpsRunner.solve Greetings.program Greetings.facts (Limits 10%N 1000%N)).

(** * Calls in conclusions *)

Module CallTests.

  Local Open Scope Z_scope.

  (** Whether the database after [n] iterations has the row of [counter] for [z]. *)
  Definition counts (n : N) (z : Z) : bool :=
    ZOpsRunner.holds Counters.counter_code [ZEncode.encode z] (count_result n).

  (** The run counts in steps of one, so it never saturates. *)
  Example counter_never_saturates :
    fst (ZOpsRunner.solve Counters.program Counters.facts (Limits 5%N 1000%N)) = IterLimit.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Four iterations count from 0 to 2. *)
  Example call_counts_up :
    counts 4 2 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The count of 3 needs one more iteration. *)
  Example counts_past_the_limit_wait :
    counts 4 3 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The count never goes below zero. *)
  Example count_stays_nonnegative :
    counts 4 (-1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CallTests.

(** * Literals in conclusions *)

Module HeadLiteralTests.

  Local Open Scope string_scope.

  (** The literal of [counter_zero] is a row of the run. *)
  Example zero_is_counted :
    ZOpsRunner.holds Counters.counter_code [ZEncode.encode 0%Z] (count_result 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Each literal string of [greeting] is a row. *)
  Example literal_strings_are_greetings :
    ZOpsRunner.holds Greetings.greeting_code [StringEncode.encode "hello"] greeting_result =
      true /\
    ZOpsRunner.holds Greetings.greeting_code [StringEncode.encode "hi"] greeting_result =
      true.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** A string that no clause names is no greeting. *)
  Example other_string_is_no_greeting :
    ZOpsRunner.holds Greetings.greeting_code [StringEncode.encode "bye"] greeting_result =
      false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End HeadLiteralTests.

(** * Literals in premises *)

Module PremiseLiteralTests.

  Local Open Scope string_scope.

  (** Once the count reaches 2, every count is past 2. *)
  Example literal_premise_reads_its_row :
    ZOpsRunner.holds Counters.past_two_code [ZEncode.encode 1%Z] (count_result 6) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Before the count reaches 2, no count is past 2. *)
  Example literal_premise_waits_for_its_row :
    ZOpsRunner.holds Counters.past_two_code [ZEncode.encode 1%Z] (count_result 2) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The literal premise of [answer_hello] holds, so [hi] answers. *)
  Example literal_string_premise_holds :
    ZOpsRunner.holds Greetings.answer_code [StringEncode.encode "hi"] greeting_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PremiseLiteralTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope Z_scope.

  (** The count of 1 gives its derived row, through the call of [counter_next]. *)
  Example counter_gives_derived_row :
    derived ZOps.prim Counters.spec Counters.inputs Counters.counter_code [ZEncode.encode 1].
  Proof.
    apply (proj1 (Counters.counter_spec 1)).
    exact (counter_next 0 counter_zero).
  Qed.

  (** A derived row of [counter] gives the count, through [counter_spec]. *)
  Example derived_row_gives_counter :
    derived ZOps.prim Counters.spec Counters.inputs Counters.counter_code [ZEncode.encode 1] ->
    counter 1.
  Proof.
    intros Hrow.
    exact (proj2 (Counters.counter_spec 1) Hrow).
  Qed.

  (** A derived row of [past_two] gives its instance, through the literal premise. *)
  Example derived_row_gives_past_two :
    derived ZOps.prim Counters.spec Counters.inputs Counters.past_two_code
      [ZEncode.encode 0] -> past_two 0.
  Proof.
    intros Hrow.
    exact (proj2 (Counters.past_two_spec 0) Hrow).
  Qed.

  (** A literal string in a conclusion gives its derived row. *)
  Example greeting_gives_derived_row :
    derived (fun _ _ => None) Greetings.spec Greetings.inputs Greetings.greeting_code
      [StringEncode.encode "hello"%string].
  Proof.
    apply (proj1 (Greetings.greeting_spec _ "hello"%string)).
    exact greeting_hello.
  Qed.

  (** A derived row of [answer] gives its instance, through the literal premise. *)
  Example derived_row_gives_answer :
    derived (fun _ _ => None) Greetings.spec Greetings.inputs Greetings.answer_code
      [StringEncode.encode "hi"%string] -> answer "hi"%string.
  Proof.
    intros Hrow.
    exact (proj2 (Greetings.answer_spec _ "hi"%string) Hrow).
  Qed.

End GlueTests.
