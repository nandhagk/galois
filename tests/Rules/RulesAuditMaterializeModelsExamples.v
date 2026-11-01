(** * Materialization model computations

    These examples observe the bounded materializer and its set difference.
    For example, a ground rule produces a tuple that is present in the resulting database.
    Builds on: RulesAuditMaterializeDeltaTotal and RulesAuditMaterializeDifference. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesJoin RulesSolve
  RulesAuditMaterializeDeltaTotal RulesAuditMaterializeDifference.
Import List.ListNotations.

Definition model_ground_program : program nat :=
  Program nat_encoding (fun _ => 1) [Rule (Atom 0 [TConst 5%positive]) []].

(** The bounded materializer includes the rule's ground tuple and excludes another. *)
Example model_ground_materialization :
  option_map (fun db =>
    (db_holds model_ground_program db 0 [5%positive],
     db_holds model_ground_program db 0 [6%positive]))
    (fst (mat_bounded_program IndexedNested model_ground_program [] 2%positive)) =
  Some (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

(** Subtracting one singleton leaves the other input element. *)
Example model_finite_difference :
  let a := FinSet.of_list nat_encoding [1; 2] in
  let b := FinSet.of_list nat_encoding [2] in
  let result := fst (mat_diff a b) in
  (FinSet.mem nat_encoding 1 result, FinSet.mem nat_encoding 2 result) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.
