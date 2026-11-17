(** * Language translation fixtures

    A language morphism lets a value abstraction run under a source language.
    For example, renaming a value abstraction keeps its operator result.
    Builds on: Translate and ValueOpenTest.

    Groups:
    - [RenamingTests] The translated value abstraction keeps the forward result. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Domains Require Import Translate.
From Galois.Tests.Domains Require Import ValueOpenTest.
Import List.ListNotations.

(** * Fixtures *)

Module SourceLanguage.
  (** Operators are booleans, guards are naturals and values are units. *)
  Definition op := bool.
  Definition guard := nat.
  Definition val := unit.
  (** Every operator succeeds with the unit value. *)
  Definition eval (_ : op) (_ : list val) := Some tt.
  (** No operator is a literal. *)
  Definition literal (_ : op) : option Z := None.
  (** Every guard holds. *)
  Definition holds (_ : guard) (_ : list val) := True.
End SourceLanguage.

Module FixtureMorphism.
  (** Each source operator maps to the unit operator. *)
  Definition op (_ : bool) := tt.
  (** Each source guard maps to the unit guard. *)
  Definition guard (_ : nat) := tt.
  (** Each source value maps to the unit value. *)
  Definition value (_ : unit) := tt.
  (** Translating operands first and then evaluating gives the translated result. *)
  Lemma eval_commutes : forall o cs,
    UnitLanguage.eval (op o) (map value cs) = option_map value (SourceLanguage.eval o cs).
  Proof. intros. reflexivity. Qed.
  (** A source guard that holds still holds after translation. *)
  Lemma guard_preserves : forall g cs,
    SourceLanguage.holds g cs -> UnitLanguage.holds (guard g) (map value cs).
  Proof. intros. exact I. Qed.
End FixtureMorphism.

(** The value abstraction renamed through the morphism. *)
Module Renamed := TranslateCode SourceLanguage UnitLanguage FixtureMorphism ReachCode.

(** * Renaming *)

Module RenamingTests.

  (** The renamed value abstraction keeps the forward result of its operator. *)
  Example renamed_forward_keeps_result : Renamed.forward false [] = true.
  Proof. vm_compute. reflexivity. Qed.

End RenamingTests.
