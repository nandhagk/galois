(** * Transfer dispatch fixtures

    These examples exercise singleton evaluation and abstract table dispatch.
    For example, a missing entry gives top when point collection fails.
    Builds on: Harness. *)

From Stdlib Require Import List Arith NArith ZArith.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import Harness.
Import List.ListNotations.
Local Open Scope nat_scope.

Module FixtureLanguage.
  Definition op := nat.
  Definition guard := unit.
  Definition val := nat.
  Definition eval k xs := if Nat.eqb k 0 then None else Some (fold_right Nat.add 0 xs).
  Definition literal (_ : op) : option Z := None.
End FixtureLanguage.

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
  Definition point (x : t) := match x with Some p => p | None => None end.
  Definition abst (x : nat) : t := Some (Some x).
End FixtureBase.

Module FixtureTable.
  Definition fwd k (xs : list FixtureBase.t) : option FixtureBase.t :=
    if Nat.eqb k 1 then Some (Some (Some (10 + length xs))) else
    if Nat.eqb k 2 then Some (Some (Some (20 + length xs))) else None.
  Definition bwd (_ : nat) (_ : FixtureBase.t) (_ : list FixtureBase.t)
      : option (list FixtureBase.t) := None.
  Definition grd (_ : unit) (_ : list FixtureBase.t) : option (list FixtureBase.t) := None.
End FixtureTable.

Module Fixture := HarnessCode FixtureLanguage FixtureBase FixtureTable.
Definition observe (x : FixtureBase.t) : option nat :=
  match x with None => Some 0 | Some p => p end.
Definition dispatch k xs := observe (Fixture.forward k xs).
Definition word_context w (v : word) := fst v = w /\ is_word w (snd v).
Example empty_operand : dispatch 1 [None; Some None] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example all_points : dispatch 1 [Some (Some 2); Some (Some 3)] = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example failed_concrete : dispatch 0 [Some (Some 2)] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example missing_entry : dispatch 3 [Some None] = None.
Proof. vm_compute. reflexivity. Qed.

Example arity_one : dispatch 1 [Some None] = Some 11.
Proof. vm_compute. reflexivity. Qed.

Example arity_two : dispatch 1 [Some None; Some None] = Some 12.
Proof. vm_compute. reflexivity. Qed.

Example arity_three : dispatch 2 [Some None; Some None; Some None] = Some 23.
Proof. vm_compute. reflexivity. Qed.

Example variadic_arity : dispatch 2 [Some None; Some None; Some None; Some None] = Some 24.
Proof. vm_compute. reflexivity. Qed.

Example zero_arity_point_path : dispatch 2 [] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example default_backward :
  map observe (Fixture.backward 1 None [Some (Some 2); Some None]) =
    [Some 2; None].
Proof. vm_compute. reflexivity. Qed.


(** Both one-bit unsigned endpoints satisfy the result context. *)
Example word_context_endpoints :
  word_context 1%positive (1%positive, 0%Z) /\
  word_context 1%positive (1%positive, 1%Z).
Proof.
  vm_compute; intuition discriminate.
Qed.

(** The first out-of-range result cannot require a finite-width payload top to contain it. *)
Example word_context_rejects_overflow :
  ~ word_context 1%positive (1%positive, 2%Z).
Proof.
  vm_compute; intuition discriminate.
Qed.

(** Result context rejects a negative raw integer and a mismatched result width. *)
Example word_context_rejects_malformed :
  ~ word_context 1%positive (1%positive, (-1)%Z) /\
  ~ word_context 1%positive (2%positive, 1%Z).
Proof.
  vm_compute; intuition discriminate.
Qed.

(** Every successful operator result supplies the context used by the word-table laws. *)
Example successful_word_context o xs r :
  eval_op o xs = Some r -> word_context (fst r) r.
Proof.
  intro Hresult. split; [reflexivity | now apply (eval_op_is_word o xs r)].
Qed.
