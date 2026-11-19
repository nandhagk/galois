(** * Primitives of many arguments

    Primitive sets whose functions take four and five arguments, read by [Egglog] and run on
    the engine. The primitive function of a set decodes the arguments one by one, so a function
    may take any number of them, of any value types. A call stands in the conclusion of a
    clause, in an equation premise and in the right side of a rewrite, and the generated glue
    lemmas connect the rows and classes to the inductives.
    For example, [blend 1 2 3 4] is [1 * 2 + 3 * 4], so the rewrite of [Terms] puts the term
    [Blend (Num 1) (Num 2) (Num 3) (Num 4)] in the class of [Num 14].

    Groups:
    - [DispatchTests] The primitive function decodes every argument and checks their number.
    - [ConclusionTests] A call of four arguments in the conclusion of a relation.
    - [PremiseTests] A call of five arguments in an equation premise.
    - [RewriteTests] A call of four arguments in the right side of a rewrite folds constants.
    - [GlueTests] The generated lemmas in both directions.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Encode Derive.
Import List.ListNotations.

(** * Fixtures *)

(** Two products added, [a * b + c * d]. *)
Definition blend (a b c d : positive) : positive := Pos.add (Pos.mul a b) (Pos.mul c d).

(** The integer [base] moved by [a], [b] and [c], forward or back. *)
Definition offset (forward : bool) (base a b c : Z) : Z :=
  if forward then (base + a + b + c)%Z else (base - a - b - c)%Z.

(** A set with a function of four positives and a function of a boolean and four integers. *)
Egglog Primitives Wide blend offset.

(** Values are positives, and the primitive function is the one that [Wide] generated. *)
Module WideValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Wide.prim.
  Definition merge (_ : positive) := Pos.max.
End WideValue.

Module WideIndex := IndexCode WideValue.
Module WideJoin := JoinCode WideValue WideIndex.
Module WideDatabase := DatabaseCode WideValue WideIndex.
Module WideRun := RunCode WideValue WideIndex WideJoin WideDatabase.
Module WideRunner := RunnerCode WideValue WideIndex WideJoin WideDatabase WideRun.

(** Saturation stops after at most 20 iterations and allocates at most 1000 identifiers. *)
Definition wide_limits : limits := Limits 20%N 1000%N.

(** [mixed pairs x y] says that [y] blends a pair [(x, k)] of [pairs] with itself, as
    [x * k + k * x]. *)
Inductive mixed (pairs : list (positive * positive)) : positive -> positive -> Prop :=
  | mixed_pair x k : In (x, k) pairs -> mixed pairs x (blend x k k x).

Egglog Mixes from mixed with Wide.

(** [moved steps x y] says that a step [(x, d)] of [steps] moves [x] forward by [d] three
    times, to [y]. *)
Inductive moved (steps : list (Z * Z)) : Z -> Z -> Prop :=
  | moved_by x d y : In (x, d) steps -> offset true x d d d = y -> moved steps x y.

Egglog Moves from moved with Wide.

(** Numbers and blends of four terms. *)
Inductive term : Type :=
  | Num (n : positive)
  | Blend (a b c d : term).

(** Equality of terms, with the closure laws, the congruence of [Blend] and the folding of a blend
    of four numbers into its value. *)
Inductive term_eq : term -> term -> Prop :=
  | term_refl a : term_eq a a
  | term_sym a b : term_eq a b -> term_eq b a
  | term_trans a b c : term_eq a b -> term_eq b c -> term_eq a c
  | term_blend a a' b b' c c' d d' : term_eq a a' -> term_eq b b' -> term_eq c c' ->
      term_eq d d' -> term_eq (Blend a b c d) (Blend a' b' c' d')
  | term_fold a b c d : term_eq (Blend (Num a) (Num b) (Num c) (Num d)) (Num (blend a b c d)).

Egglog Terms from term_eq with Wide.

(** * Dispatch *)

Module DispatchTests.

  Local Open Scope positive_scope.

  (** The call of [blend] on four positives gives [1 * 2 + 3 * 4]. *)
  Example four_positives_give_the_blend :
    Wide.prim Wide.blend_code [1; 2; 3; 4] = Some 14.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A call with three values has no result, because [blend] takes four. *)
  Example three_values_are_too_few :
    Wide.prim Wide.blend_code [1; 2; 3] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A call with five values has no result either. *)
  Example five_values_are_too_many :
    Wide.prim Wide.blend_code [1; 2; 3; 4; 5] = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The call of [offset] decodes a boolean and four integers and encodes the integer result. *)
  Example mixed_arguments_are_decoded :
    Wide.prim Wide.offset_code
      [BoolEncode.encode false; ZEncode.encode 10%Z; ZEncode.encode 1%Z; ZEncode.encode 2%Z;
       ZEncode.encode 3%Z] = Some (ZEncode.encode 4%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A first value that encodes no boolean leaves [offset] without a result. *)
  Example undecoded_argument_has_no_result :
    Wide.prim Wide.offset_code
      [3; ZEncode.encode 10%Z; ZEncode.encode 1%Z; ZEncode.encode 2%Z; ZEncode.encode 3%Z] =
      None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DispatchTests.

(** * Conclusions *)

Module ConclusionTests.

  Local Open Scope positive_scope.

  (** Two pairs, 1 with 2 and 3 with 1. *)
  Definition two_pairs : list (positive * positive) := [(1, 2); (3, 1)].

  (** The database after running [Mixes] on the two pairs. *)
  Definition mixed_result : WideDatabase.t :=
    snd (WideRunner.solve Mixes.program (Mixes.facts two_pairs) wide_limits).

  (** The pair of 1 and 2 blends to [1 * 2 + 2 * 1]. *)
  Example first_pair_is_blended :
    WideRunner.holds Mixes.mixed_code [1; 4] mixed_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The pair of 3 and 1 blends to [3 * 1 + 1 * 3]. *)
  Example second_pair_is_blended :
    WideRunner.holds Mixes.mixed_code [3; 6] mixed_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A pair blends with its own number, so 1 has no row with the result of 3. *)
  Example pairs_stay_apart :
    WideRunner.holds Mixes.mixed_code [1; 6] mixed_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The program is relational and well sorted, so the theorems about relations cover it. *)
  Example mixes_are_covered :
    spec_ok Mixes.spec = true /\ relational Mixes.spec = true.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

End ConclusionTests.

(** * Equation premises *)

Module PremiseTests.

  Local Open Scope Z_scope.

  (** Two steps, from 0 by 2 and from 5 by -1. *)
  Definition two_steps : list (Z * Z) := [(0, 2); (5, -1)].

  (** The database after running [Moves] on the two steps. *)
  Definition moved_result : WideDatabase.t :=
    snd (WideRunner.solve Moves.program (Moves.facts two_steps) wide_limits).

  (** Whether the database has the row of [moved] for two integers. *)
  Definition moves (x y : Z) : bool :=
    WideRunner.holds Moves.moved_code [ZEncode.encode x; ZEncode.encode y] moved_result.

  (** Three steps of 2 move 0 to 6. *)
  Example zero_moves_to_six :
    moves 0 6 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Three steps of -1 move 5 to 2. *)
  Example negative_steps_move_back :
    moves 5 2 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** One step of 2 is not the result. *)
  Example one_step_is_not_the_result :
    moves 0 2 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PremiseTests.

(** * Rewrites *)

Module RewriteTests.

  Local Open Scope positive_scope.

  (** Whether saturating [Terms] puts two terms in one class. *)
  Definition same_term (a b : term) : bool :=
    WideRunner.equal Terms.program Terms.facts wide_limits
      (Terms.encode_term a) (Terms.encode_term b).

  (** The blend of 1, 2, 3 and 4 folds into 14. *)
  Example blend_of_numbers_folds :
    same_term (Blend (Num 1) (Num 2) (Num 3) (Num 4)) (Num 14) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inner blend folds first, and the outer blend then folds its value. *)
  Example nested_blends_fold :
    same_term (Blend (Blend (Num 1) (Num 1) (Num 1) (Num 1)) (Num 3) (Num 1) (Num 1)) (Num 7) =
      true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The folded value is the blend of the numbers in their order. *)
  Example order_of_arguments_matters :
    same_term (Blend (Num 1) (Num 2) (Num 3) (Num 4)) (Num 11) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RewriteTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** An instance of [mixed] gives its derived row, through [mixed_spec]. *)
  Example mixed_gives_derived_row :
    derived Wide.prim Mixes.spec (Mixes.inputs [(1, 2)]) Mixes.mixed_code [1; 4].
  Proof.
    apply (proj1 (Mixes.mixed_spec [(1, 2)] 1 4)).
    apply (mixed_pair [(1, 2)] 1 2).
    left. reflexivity.
  Qed.

  (** A derived row of [mixed] gives the instance, through [mixed_spec]. *)
  Example derived_row_gives_mixed :
    derived Wide.prim Mixes.spec (Mixes.inputs [(1, 2)]) Mixes.mixed_code [1; 4] ->
    mixed [(1, 2)] 1 4.
  Proof.
    intros Hrow.
    exact (proj2 (Mixes.mixed_spec [(1, 2)] 1 4) Hrow).
  Qed.

  (** An instance of [moved] gives the derived row of its encoded integers. *)
  Example moved_gives_derived_row :
    derived Wide.prim Moves.spec (Moves.inputs [(0%Z, 2%Z)]) Moves.moved_code
      [ZEncode.encode 0; ZEncode.encode 6].
  Proof.
    apply (proj1 (Moves.moved_spec [(0%Z, 2%Z)] 0 6)).
    apply (moved_by [(0%Z, 2%Z)] 0 2 6); [left; reflexivity | reflexivity].
  Qed.

  (** A derived row of encoded integers gives the instance of [moved]. *)
  Example derived_row_gives_moved :
    derived Wide.prim Moves.spec (Moves.inputs [(0%Z, 2%Z)]) Moves.moved_code
      [ZEncode.encode 0; ZEncode.encode 6] -> moved [(0%Z, 2%Z)] 0 6.
  Proof.
    intros Hrow.
    exact (proj2 (Moves.moved_spec [(0%Z, 2%Z)] 0 6) Hrow).
  Qed.

  (** The fold of a blend gives a congruence of the encodings, through [term_eq_congruent]. *)
  Example fold_gives_congruence :
    congruent Wide.prim Terms.spec Terms.inputs
      (Terms.encode_term (Blend (Num 1) (Num 2) (Num 3) (Num 4))) (Terms.encode_term (Num 14)).
  Proof.
    apply Terms.term_eq_congruent.
    exact (term_fold 1 2 3 4).
  Qed.

End GlueTests.
