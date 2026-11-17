(** * Transfer dispatch fixtures

    These examples exercise singleton evaluation and abstract table dispatch.
    For example, a missing entry gives top when point collection fails.
    Builds on: Harness. *)

(* Groups:
   - Fixtures: a small language, its abstract base, a table of transfers and the harness.
   - Dispatch: forward results of the table on points, failures and missing entries.
   - Arity: forward results for one, two, three and four operands.
   - Backward: the default backward transfer of the table.
   - Word context: word results that lie in the one-bit unsigned context. *)

From Stdlib Require Import List Arith NArith ZArith.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import Harness.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Fixtures *)

(** Operators are naturals, guards are units and values are naturals. *)
Module FixtureLanguage.
  Definition op := nat.
  Definition guard := unit.
  Definition val := nat.
  (** Operator zero fails, and any other operator sums its operands. *)
  Definition eval k xs := if Nat.eqb k 0 then None else Some (fold_right Nat.add 0 xs).
  (** No operator is a literal. *)
  Definition literal (_ : op) : option Z := None.
End FixtureLanguage.

(** The abstract base: an optional optional natural, with None as bottom. *)
Module FixtureBase.
  Definition t := option (option nat).
  Definition bot : t := None.
  Definition top : t := Some None.
  Definition is_bot (x : t) := match x with None => true | _ => false end.
  Definition leb (_ _ : t) := true.
  Definition join (x _ : t) := x.
  Definition meet (x _ : t) := x.
  Definition wparam := unit.
  Definition widen (_ : unit) (x _ : t) := x.
  Definition narrow (x _ : t) := x.
  (** The point of an abstract value, or None when it has no point. *)
  Definition point (x : t) := match x with Some p => p | None => None end.
  Definition abst (x : nat) : t := Some (Some x).
End FixtureBase.

(** A table of forward transfers, with arity-dependent results. *)
Module FixtureTable.
  (** Operator one adds ten to the operand count, operator two adds twenty. *)
  Definition fwd k (xs : list FixtureBase.t) : option FixtureBase.t :=
    if Nat.eqb k 1 then Some (Some (Some (10 + length xs))) else
    if Nat.eqb k 2 then Some (Some (Some (20 + length xs))) else None.
  (** The backward table has no entry. *)
  Definition bwd (_ : nat) (_ : FixtureBase.t) (_ : list FixtureBase.t)
      : option (list FixtureBase.t) := None.
  (** The guard table has no entry. *)
  Definition grd (_ : unit) (_ : list FixtureBase.t) : option (list FixtureBase.t) := None.
End FixtureTable.

(** The harness over the fixture language, base and table. *)
Module Fixture := HarnessCode FixtureLanguage FixtureBase FixtureTable.

(** Reads the point of an abstract value, with bottom as zero. *)
Definition observe (x : FixtureBase.t) : option nat :=
  match x with None => Some 0 | Some p => p end.

(** The observed forward result of operator k on the operands xs. *)
Definition dispatch k xs := observe (Fixture.forward k xs).

(** A word is in the context of width w when its first component is w and it is a word. *)
Definition word_context w (v : word) := fst v = w /\ is_word w (snd v).

(** * Dispatch *)

Module DispatchTests.

  (** A bottom operand makes the observed point zero. *)
  Example bottom_operand_observes_zero : dispatch 1 [None; Some None] = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  (** Points of the operands are combined into one result. *)
  Example points_are_summed_into_result : dispatch 1 [Some (Some 2); Some (Some 3)] = Some 5.
  Proof. vm_compute. reflexivity. Qed.

  (** A failed concrete operator gives an observed zero. *)
  Example failed_operator_observes_zero : dispatch 0 [Some (Some 2)] = Some 0.
  Proof. vm_compute. reflexivity. Qed.

  (** An operator without a table entry has no result. *)
  Example missing_entry_has_no_result : dispatch 3 [Some None] = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A zero-arity operand list still reaches the point path. *)
  Example zero_arity_takes_point_path : dispatch 2 [] = Some 0.
  Proof. vm_compute. reflexivity. Qed.

End DispatchTests.

(** * Arity *)

Module ArityTests.

  (** One operand gives the result for one operand. *)
  Example one_operand_result : dispatch 1 [Some None] = Some 11.
  Proof. vm_compute. reflexivity. Qed.

  (** Two operands give the result for two operands. *)
  Example two_operand_result : dispatch 1 [Some None; Some None] = Some 12.
  Proof. vm_compute. reflexivity. Qed.

  (** Three operands give the result for three operands. *)
  Example three_operand_result : dispatch 2 [Some None; Some None; Some None] = Some 23.
  Proof. vm_compute. reflexivity. Qed.

  (** Four operands give the result for four operands. *)
  Example four_operand_result :
    dispatch 2 [Some None; Some None; Some None; Some None] = Some 24.
  Proof. vm_compute. reflexivity. Qed.

End ArityTests.

(** * Backward *)

Module BackwardTests.

  (** The default backward transfer returns the operands it was given, observed. *)
  Example default_backward_observes_operands :
    map observe (Fixture.backward 1 None [Some (Some 2); Some None]) = [Some 2; None].
  Proof. vm_compute. reflexivity. Qed.

End BackwardTests.

(** * Word context *)

Module WordContextTests.

  (** The lower endpoint of the one-bit unsigned range is in the context. *)
  Example lower_endpoint_in_context : word_context 1%positive (1%positive, 0%Z).
  Proof. vm_compute; intuition discriminate. Qed.

  (** The upper endpoint of the one-bit unsigned range is in the context. *)
  Example upper_endpoint_in_context : word_context 1%positive (1%positive, 1%Z).
  Proof. vm_compute; intuition discriminate. Qed.

  (** A value above the one-bit unsigned range is outside the context. *)
  Example overflow_outside_context : ~ word_context 1%positive (1%positive, 2%Z).
  Proof. vm_compute; intuition discriminate. Qed.

  (** A negative raw integer is outside the context. *)
  Example negative_raw_outside_context : ~ word_context 1%positive (1%positive, (-1)%Z).
  Proof. vm_compute; intuition discriminate. Qed.

  (** A word of another width is outside the context. *)
  Example width_mismatch_outside_context : ~ word_context 1%positive (2%positive, 1%Z).
  Proof. vm_compute; intuition discriminate. Qed.

  (** Every successful operator result supplies the context used by the word-table laws. *)
  Example successful_result_in_context o xs r :
    eval_op o xs = Some r -> word_context (fst r) r.
  Proof.
    intro Hresult. split; [reflexivity | now apply (eval_op_is_word o xs r)].
  Qed.

End WordContextTests.
