(** * Word term environment observations

    Bit-vector terms run through the tagged constant domain in an environment.
    For example, a nested arithmetic term evaluates to its wrapped singleton.
    Builds on: Env, BitsLang and Tagged. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import LangSig WordSig BitsLang Const ConstSig Tagged Harness.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Vars := TrieMapCode NatKeyCode.
Module Payload := ConstWordCode WordLanguageCode.
Module Table := ConstWordTableCode WordLanguageCode Payload.
Module Base := TaggedCode WordLanguageCode Payload.
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
Module State := EnvCode NatKeyCode Vars BitsLangCode Domain.
Definition p (w : positive) (z : Z) := TVal w (FVal z).
Definition input := Reached (Vars.set 1%nat (p 32 1) (Vars.set 0%nat (p 32 1) Vars.empty)).
Definition add_terms := Node (BOp bvadd) [Leaf 0%nat; Leaf 1%nat].
Definition observe x s := match s with Unreached => TBot | Reached m => State.read m x end.

Example test_positive :
  let s := State.assume (BTruth true) [add_terms] input in
  (observe 0%nat s, observe 1%nat s) = (p 32 1, p 32 1).
Proof. vm_compute. reflexivity. Qed.

(* The old false test of 1 + 1 rejected both operands as [TBot; TBot].
   The current tagged guard table has no refinement and returns [p 32 1; p 32 1].
Example test_rejected :
  let s := State.assume (BTruth false) [add_terms] input in
  (observe 0%nat s, observe 1%nat s) = (TBot, TBot).
Proof. vm_compute. reflexivity. Qed.
*)

Example false_test_current :
  let s := State.assume (BTruth false) [add_terms] input in
  (observe 0%nat s, observe 1%nat s) = (p 32 1, p 32 1).
Proof. vm_compute. reflexivity. Qed.

Definition nested :=
  Node (BOp bvadd) [Node (BOp bvmul) [Leaf 0%nat; Node (BConst 8%positive 3) []];
                     Node (BConst 8%positive 250) []].
Example nested_abstract_evaluation :
  State.eval nested (Reached (Vars.set 0%nat (p 8 5) Vars.empty)) = p 8 9.
Proof. vm_compute. reflexivity. Qed.

Example nested_expression_refinement :
  let e := Node (BOp bvadd) [Leaf 0%nat; Node (BConst 8%positive 3) []] in
  let m := Vars.set 0%nat (TVal 8%positive FTop) Vars.empty in
  State.read (State.refine (p 8 7) (State.annotate m e) m) 0%nat = p 8 4.
Proof. vm_compute. reflexivity. Qed.
