(** * Programs over integers and strings

    Programs derived with [Egglog] over value types other than [positive]. The types [Z] and
    [string] are registered with their encoders in [Encode.v], so the command encodes their
    values as positives for the engine. A run uses the engine's [positive] values, and the
    tests read its rows through the encoders.

    For example, a step relation over [Z] with the equation premise [Z.add x k = y] derives the
    row for [2] from the step [(0, 2)].

    Groups:
    - [IntegerTests] A relation over [Z] with an input list and an equation premise.
    - [MixedTests] A primitive over [positive] and [Z] with a result in [Z].
    - [StringTests] A relation whose input is a list of string pairs.
    - [TermTests] Terms with an integer and a string argument, folded with [Z.add] and [Z.mul].
    - [GlueTests] The generated lemma turns a derived row into the inductive and back.
    - [RegistrationTests] The command stops on a type without an encoder.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith String.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner EncodeSig Encode Derive.
Import List.ListNotations.

(** * Fixtures *)

(** The primitives of the examples: addition and multiplication on integers, and the
    difference of two positives as an integer, and the successor on natural numbers. *)
Egglog Primitives IntOps Z.add Z.mul Z.pos_sub N.succ.

(** Values are positives, and the primitive function is the one that [IntOps] generated. *)
Module IntValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := IntOps.prim.
  Definition merge (_ : positive) := Pos.max.
End IntValue.

Module IntIndex := IndexCode IntValue.
Module IntJoin := JoinCode IntValue IntIndex.
Module IntDatabase := DatabaseCode IntValue IntIndex.
Module IntRun := RunCode IntValue IntIndex IntJoin IntDatabase.
Module IntRunner := RunnerCode IntValue IntIndex IntJoin IntDatabase IntRun.

(** Integers reached by the listed steps: [reach steps x y] says that [y] is [x] plus a step,
    or a step further from a reached point. *)
Inductive reach (steps : list (Z * Z)) : Z -> Z -> Prop :=
  | reach_first x k y : In (x, k) steps -> Z.add x k = y -> reach steps x y
  | reach_next x y k z : reach steps x y -> In (y, k) steps -> Z.add y k = z -> reach steps x z.

Egglog Reach from reach with IntOps.

(** Integers one step from zero. The integer constant is a literal in the premise and in the
    equation. *)
Inductive origin (steps : list (Z * Z)) : Z -> Prop :=
  | origin_step k y : In (0%Z, k) steps -> Z.add 0%Z k = y -> origin steps y.

Egglog Origins from origin with IntOps.

(** The distance between two positives, as an integer. *)
Inductive gap (pairs : list (positive * positive)) : positive -> positive -> Z -> Prop :=
  | gap_of x y d : In (x, y) pairs -> Z.pos_sub x y = d -> gap pairs x y d.

Egglog Gaps from gap with IntOps.

(** Names linked by the listed pairs, and the names reachable through links. *)
Inductive linked (links : list (string * string)) : string -> string -> Prop :=
  | linked_direct a b : In (a, b) links -> linked links a b
  | linked_chain a b c : linked links a b -> In (b, c) links -> linked links a c.

Egglog Links from linked.

(** Arithmetic terms of [eqsat-basic.egg], with integer numbers and named variables. *)
Inductive term : Type :=
  | Num (n : Z)
  | Var (x : string)
  | Add (a b : term)
  | Mul (a b : term).

(** Equality of terms: the closure laws, commutativity of both operations, distributivity of
    multiplication over addition, and the folding of constants with the primitives. *)
Inductive equiv : term -> term -> Prop :=
  | equiv_refl a : equiv a a
  | equiv_sym a b : equiv a b -> equiv b a
  | equiv_trans a b c : equiv a b -> equiv b c -> equiv a c
  | equiv_add a a' b b' : equiv a a' -> equiv b b' -> equiv (Add a b) (Add a' b')
  | equiv_mul a a' b b' : equiv a a' -> equiv b b' -> equiv (Mul a b) (Mul a' b')
  | equiv_comm_add a b : equiv (Add a b) (Add b a)
  | equiv_comm_mul a b : equiv (Mul a b) (Mul b a)
  | equiv_distrib a b c : equiv (Mul a (Add b c)) (Add (Mul a b) (Mul a c))
  | equiv_fold_add x y : equiv (Add (Num x) (Num y)) (Num (Z.add x y))
  | equiv_fold_mul x y : equiv (Mul (Num x) (Num y)) (Num (Z.mul x y)).

Egglog Math from equiv with IntOps.

(** * Integers *)

Module IntegerTests.

  Local Open Scope Z_scope.

  (** Two steps, from 0 by 2 and from 2 by -5. *)
  Definition two_steps : list (Z * Z) := [(0, 2); (2, -5)].

  (** The database after running [Reach] on the two steps. *)
  Definition reach_result : IntDatabase.t :=
    snd (IntRunner.solve Reach.program (Reach.facts two_steps) (Limits 6%N 1000%N)).

  (** Whether the database has the row of [reach] for two integers. *)
  Definition reaches (x y : Z) : bool :=
    IntRunner.holds Reach.reach_code [ZEncode.encode x; ZEncode.encode y] reach_result.

  (** The engine accepts the sorts of the lowered program. *)
  Example reach_program_is_well_sorted :
    spec_ok Reach.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The facts have one row for each step, with the integers encoded. *)
  Example facts_encode_the_steps :
    Reach.facts two_steps =
      [(Reach.steps_code, [ZEncode.encode 0; ZEncode.encode 2]);
       (Reach.steps_code, [ZEncode.encode 2; ZEncode.encode (-5)])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The first step takes 0 to 2. *)
  Example first_step_is_reached :
    reaches 0 2 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A second step from the reached point takes 0 to -3, a negative integer. *)
  Example second_step_reaches_a_negative :
    reaches 0 (-3) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The step from 2 gives its own row too. *)
  Example later_start_is_reached :
    reaches 2 (-3) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An integer that no step reaches has no row. *)
  Example unreached_integer_has_no_row :
    reaches 0 5 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The row for an integer is not the row of its negation. *)
  Example negation_has_no_row :
    reaches 0 3 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The database after running [Origins] on the two steps. *)
  Definition origin_result : IntDatabase.t :=
    snd (IntRunner.solve Origins.program (Origins.facts two_steps) (Limits 4%N 1000%N)).

  (** A step from the literal 0 gives its end, and the step from 2 does not. *)
  Example literal_start_selects_its_steps :
    IntRunner.holds Origins.origin_code [ZEncode.encode 2] origin_result = true /\
    IntRunner.holds Origins.origin_code [ZEncode.encode (-3)] origin_result = false.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** The glue lemma of a relation with literals turns an instance into a derived row. *)
  Example literal_gives_derived_row :
    derived IntOps.prim Origins.spec (Origins.inputs two_steps) Origins.origin_code
      [ZEncode.encode 2].
  Proof.
    apply (proj1 (Origins.origin_spec two_steps 2)).
    apply (origin_step two_steps 2 2); [left; reflexivity | reflexivity].
  Qed.

End IntegerTests.

(** * Mixed values *)

Module MixedTests.

  Local Open Scope positive_scope.

  (** Two pairs of positives. *)
  Definition two_pairs : list (positive * positive) := [(5, 3); (3, 7)].

  (** The database after running [Gaps] on the pairs. *)
  Definition gap_result : IntDatabase.t :=
    snd (IntRunner.solve Gaps.program (Gaps.facts two_pairs) (Limits 4%N 1000%N)).

  (** Whether the database has the row of [gap] for two positives and an integer. *)
  Definition has_gap (x y : positive) (d : Z) : bool :=
    IntRunner.holds Gaps.gap_code [x; y; ZEncode.encode d] gap_result.

  (** A pair has the difference of its positives, which is an integer. *)
  Example gap_is_the_difference :
    has_gap 5 3 2%Z = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The difference of the second pair is negative. *)
  Example gap_may_be_negative :
    has_gap 3 7 (-4)%Z = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wrong difference has no row. *)
  Example wrong_gap_has_no_row :
    has_gap 5 3 3%Z = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The primitive of the mixed call decodes its two positives and encodes an integer. *)
  Example mixed_primitive_encodes_its_result :
    IntOps.prim IntOps.pos_sub_code [5; 3] = Some (ZEncode.encode 2%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A primitive on natural numbers decodes its argument and encodes the successor. *)
  Example natural_primitive_encodes_its_result :
    IntOps.prim IntOps.succ_code [NEncode.encode 4%N] = Some (NEncode.encode 5%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A primitive on natural numbers has no result on an argument that encodes none. *)
  Example decoding_failure_has_no_result :
    IntOps.prim IntOps.succ_code [3] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End MixedTests.

(** * Strings *)

Module StringTests.

  Local Open Scope string_scope.

  (** A chain of three names. *)
  Definition three_links : list (string * string) := [("a", "b"); ("b", "c")].

  (** The database after running [Links] on the chain. *)
  Definition link_result : IntDatabase.t :=
    snd (IntRunner.solve Links.program (Links.facts three_links) (Limits 6%N 1000%N)).

  (** Whether the database has the row of [linked] for two names. *)
  Definition is_linked (a b : string) : bool :=
    IntRunner.holds Links.linked_code [StringEncode.encode a; StringEncode.encode b] link_result.

  (** A listed pair is linked. *)
  Example listed_pair_is_linked :
    is_linked "a" "b" = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Chaining two pairs links the ends. *)
  Example chain_links_the_ends :
    is_linked "a" "c" = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The links have a direction. *)
  Example links_have_a_direction :
    is_linked "c" "a" = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A name that is a prefix of a linked name is not linked. *)
  Example prefix_is_not_linked :
    is_linked "a" "" = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A longer name has its own row. *)
  Example long_names_are_distinct :
    IntRunner.holds Links.linked_code
      [StringEncode.encode "alpha"; StringEncode.encode "beta"]
      (snd (IntRunner.solve Links.program (Links.facts [("alpha", "beta")])
              (Limits 4%N 1000%N))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End StringTests.

(** * Terms *)

Module TermTests.

  Local Open Scope string_scope.

  (** The tutorial's [2 * (x + 3)]. *)
  Definition two_times_sum : term := Mul (Num 2) (Add (Var "x") (Num 3)).

  (** The product folded and distributed, [6 + 2 * x]. *)
  Definition folded : term := Add (Num 6) (Mul (Num 2) (Var "x")).

  (** A different sum of the same parts, [2 + 2 * x]. *)
  Definition other_sum : term := Add (Num 2) (Mul (Num 2) (Var "x")).

  (** Twenty iterations and a thousand identifiers are far more than these terms need. *)
  Definition term_limits : limits := Limits 20%N 1000%N.

  (** Whether saturating the rules of [Math] with two terms puts them in one class. *)
  Definition joined (a b : term) : bool :=
    IntRunner.equal Math.program [] term_limits (Math.encode_term a) (Math.encode_term b).

  (** The engine accepts the sorts of the rules that [Math] derives. *)
  Example math_program_is_well_sorted :
    spec_ok Math.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Distributing and folding [2 * 3] puts [2 * (x + 3)] in the class of [6 + 2 * x]. *)
  Example folding_joins_the_tutorial_terms :
    joined two_times_sum folded = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A different sum of the same parts stays in its own class. *)
  Example different_terms_stay_apart :
    joined two_times_sum other_sum = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Variables with different names are different terms. *)
  Example variables_with_other_names_stay_apart :
    joined (Var "x") (Var "y") = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The folded sum of integers meets its value, with a negative number. *)
  Example folding_a_negative_number :
    joined (Add (Num 2) (Num (-5))) (Num (-3)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End TermTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope Z_scope.

  (** The steps of the glue tests. *)
  Definition one_step : list (Z * Z) := [(1, 2)].

  (** An instance of [reach] gives the derived row of its encoded integers. *)
  Example reach_gives_derived_row :
    derived IntOps.prim Reach.spec (Reach.inputs one_step) Reach.reach_code
      [ZEncode.encode 1; ZEncode.encode 3].
  Proof.
    apply (proj1 (Reach.reach_spec one_step 1 3)).
    apply (reach_first one_step 1 2 3); [left; reflexivity | reflexivity].
  Qed.

  (** A derived row of encoded integers gives the instance of [reach]. *)
  Example derived_row_gives_reach :
    derived IntOps.prim Reach.spec (Reach.inputs one_step) Reach.reach_code
      [ZEncode.encode 1; ZEncode.encode 3] -> reach one_step 1 3.
  Proof.
    intros Hrow.
    exact (proj2 (Reach.reach_spec one_step 1 3) Hrow).
  Qed.

  (** The one step reaches only 3, so the row of 1 and 4 is not derived, through the glue. *)
  Example unreached_row_is_not_derived :
    ~ derived IntOps.prim Reach.spec (Reach.inputs one_step) Reach.reach_code
      [ZEncode.encode 1; ZEncode.encode 4].
  Proof.
    intros Hrow.
    apply (proj2 (Reach.reach_spec one_step 1 4)) in Hrow.
    assert (Hthree : forall x y, reach one_step x y -> y = 3).
    { intros x y Hreach.
      induction Hreach as [x k y Hin Hadd | x y k z Hreach IH Hin Hadd].
      - destruct Hin as [Hstep | []].
        injection Hstep as Hx Hk.
        subst x k.
        rewrite <- Hadd.
        reflexivity.
      - destruct Hin as [Hstep | []].
        injection Hstep as Hy Hk.
        rewrite <- Hy in IH.
        discriminate IH. }
    discriminate (Hthree 1 4 Hrow).
  Qed.

  (** Names give derived rows too, through [linked_spec]. *)
  Example link_gives_derived_row :
    derived (fun _ _ => None) Links.spec (Links.inputs [("a"%string, "b"%string)]) Links.linked_code
      [StringEncode.encode "a"; StringEncode.encode "b"].
  Proof.
    apply (proj1 (Links.linked_spec _ _ _ _)).
    apply linked_direct. left. reflexivity.
  Qed.

  (** An instance of the equality of terms gives a congruence of the encodings. *)
  Example equiv_gives_congruence :
    congruent IntOps.prim Math.spec (Math.inputs)
      (Math.encode_term (Add (Num 2) (Num 3))) (Math.encode_term (Num 5)).
  Proof.
    apply Math.equiv_congruent.
    apply (equiv_fold_add 2 3).
  Qed.

End GlueTests.

(** * Registration *)

Module RegistrationTests.

  (** A relation over natural numbers, which have no encoder. *)
  Inductive step (steps : list (nat * nat)) : nat -> nat -> Prop :=
    | step_in x y : In (x, y) steps -> step steps x y.

  (** An input list of an unregistered type stops the command. *)
  Fail Egglog Steps from step.

  (** A relation with an index of an unregistered type stops the command. A relation whose two
      indices are the same inductive type would read it as a datatype instead. *)
  Inductive count : nat -> positive -> Prop :=
    | count_zero : count O xH.

  Fail Egglog Count from count.

  (** A primitive over an unregistered type stops the command. *)
  Fail Egglog Primitives NatOps Nat.add.

  (** An encoder module of another type is refused. *)
  Fail Egglog Value nat ZEncode.

  (** A type that is registered cannot be registered again. *)
  Fail Egglog Value Z ZEncode.

  (** Positive is a value type already. *)
  Fail Egglog Value positive ZEncode.

End RegistrationTests.
