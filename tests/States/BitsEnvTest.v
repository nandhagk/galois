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

Definition equal_seven :=
  Node (BOp bveq) [Leaf 0%nat; Node (BConst 32%positive 7) []].
Definition one_value z := Reached (Vars.set 0%nat (p 32 z) Vars.empty).
Example equal_positive : observe 0%nat (State.assume (BTruth true) [equal_seven] (one_value 7)) =
  p 32 7.
Proof. vm_compute. reflexivity. Qed.

(* The old Equal guard returned TBot for word 6. The current BTruth on an equality
   term leaves that value unchanged as p 32 6.
Example equal_rejected :
  observe 0%nat (State.assume (BTruth true) [equal_seven] (one_value 6)) = TBot.
Proof. vm_compute. reflexivity. Qed.
*)
Example equal_rejected_current :
  observe 0%nat (State.assume (BTruth true) [equal_seven] (one_value 6)) = p 32 6.
Proof. vm_compute. reflexivity. Qed.

Definition equal_one := Node (BOp bveq) [Leaf 0%nat; Node (BConst 1%positive 1) []].
Definition unknown_input : State.t := Reached (Vars.set 0%nat TAny Vars.empty).
(* The old Equal guard on TAny returned p 1 1. The current equality term and BTruth
   leave the variable unchanged as TAny.
Example equal_boundary :
  observe 0%nat (State.assume (BTruth true) [equal_one] unknown_input) = p 1 1.
Proof. vm_compute. reflexivity. Qed.
*)
Example equal_boundary_current :
  observe 0%nat (State.assume (BTruth true) [equal_one] unknown_input) = TAny.
Proof. vm_compute. reflexivity. Qed.

Definition differs_one := Node (BOp bvne) [Leaf 0%nat; Node (BConst 1%positive 1) []].
Definition one_bit z := Reached (Vars.set 0%nat (p 1 z) Vars.empty).
Example differ_boundary :
  observe 0%nat (State.assume (BTruth true) [differs_one] (one_bit 0)) = p 1 0.
Proof. vm_compute. reflexivity. Qed.
(* The old Differ true guard returned TBot for one. The current BTruth on disequality
   leaves the value unchanged as p 1 1.
Example differ_rejected :
  observe 0%nat (State.assume (BTruth true) [differs_one] (one_bit 1)) = TBot.
Proof. vm_compute. reflexivity. Qed.
*)
Example differ_rejected_current :
  observe 0%nat (State.assume (BTruth true) [differs_one] (one_bit 1)) = p 1 1.
Proof. vm_compute. reflexivity. Qed.

Definition differs_zero := Node (BOp bvne) [Leaf 0%nat; Node (BConst 1%positive 0) []].
Example differ_positive :
  observe 0%nat (State.assume (BTruth true) [differs_zero] (one_bit 1)) = p 1 1.
Proof. vm_compute. reflexivity. Qed.

Example test_boundary :
  let e := Node (BOp (bvtrunc 1%positive)) [Leaf 0%nat] in
  observe 0%nat (State.assume (BTruth false) [e] (one_value 2)) = p 32 2.
Proof. vm_compute. reflexivity. Qed.

Example comparison_truth :
  let e := Node (BOp bvult) [Leaf 0%nat; Leaf 1%nat] in
  let m := Vars.set 1%nat (p 32 2) (Vars.set 0%nat (p 32 1) Vars.empty) in
  let s := State.assume (BTruth true) [e] (Reached m) in
  (observe 0%nat s, observe 1%nat s) = (p 32 1, p 32 2).
Proof. vm_compute. reflexivity. Qed.

Example empty_guard_support : State.assume (BTruth true) [] State.top = State.top.
Proof. vm_compute. reflexivity. Qed.

Definition differs_seven :=
  Node (BOp bvne) [Leaf 0%nat; Node (BConst 32%positive 7) []].
Example differ_mixed_width_fallback :
  observe 0%nat (State.assume (BTruth true) [differs_seven] (one_bit 1)) = p 1 1.
Proof. vm_compute. reflexivity. Qed.
