(** * Language translation fixtures

    A language morphism lets a value abstraction run under a source language.
    For example, renaming a value abstraction keeps its operator result.
    Builds on: Translate and ValueOpenTest. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Domains Require Import Translate.
From Galois.Tests.Domains Require Import ValueOpenTest.
Import List.ListNotations.

Module SourceLanguage.
  Definition op := bool.
  Definition guard := nat.
  Definition val := unit.
  Definition eval (_ : op) (_ : list val) := Some tt.
  Definition literal (_ : op) : option Z := None.
End SourceLanguage.

Module FixtureMorphism.
  Definition op (_ : bool) := tt.
  Definition guard (_ : nat) := tt.
End FixtureMorphism.

Module Renamed := TranslateCode SourceLanguage UnitLanguage FixtureMorphism ReachCode.

Example renamed_transfer : Renamed.forward false [] = true.
Proof. vm_compute. reflexivity. Qed.

(* The old rename-law client awaits conversion to module laws.
Example renamed_laws :
  value_laws
    (ValueAbs.rename (fun _ : bool => Cost.ret tt) (fun _ : nat => Cost.ret tt) reach_values)
    {| ValueSem.eval := fun _ _ => Some tt; ValueSem.holds := fun _ _ => True |}
    bool_gamma.
Proof.
  apply rename_laws with (M := unit_sem).
  - exact reach_value_laws.
  - intros. reflexivity.
  - intros. exact I.
Qed.


*)
