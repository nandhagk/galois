(** * Map interface fixtures

    These fixtures observe replacement, deletion and canonical enumeration.
    For example, codes two, one and three have the trie traversal order.
    Builds on: BaseMap and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
Import List.ListNotations.

Definition sample := Map.of_list positive_encoding [(1%positive, 10); (2%positive, 20);
  (3%positive, 30); (1%positive, 11)].

Example map_found : Map.get positive_encoding 1%positive sample = Some 11.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_absent : Map.get positive_encoding 4%positive sample = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_trie_order : List.map fst (Map.elements sample) = [2; 1; 3]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_update_absent :
  Map.get positive_encoding 4%positive
    (Map.update positive_encoding 4%positive (fun _ => Some 40) sample) = Some 40.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_remove_last :
  Map.is_empty (Map.remove positive_encoding 1%positive
    (Map.set positive_encoding 1%positive 0 Map.empty)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example map_empty : Map.elements (@Map.empty positive nat) = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** This reference-list observation changes with a backend's proved cost bounds. *)
Example map_reference_ticks :
  Cost.ticks (Map.get_code_c 3%positive sample) = 8%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** Combination keeps callback values and retains an expensive callback's declared charge. *)
Example map_costed_combination :
  let merged := Map.combine_c
    (fun a b => Cost.lift (fun _ => 1000%N)
      (fun _ => match a with Some _ => a | None => b end) tt) sample Map.empty in
  (Map.elements (Cost.value merged), N.ltb 1000 (Cost.ticks merged)) =
    ([(2%positive, 20); (1%positive, 11); (3%positive, 30)], true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Comparison keeps callback results and retains their declared charge. *)
Example map_costed_comparison :
  let checked := Map.forall2_c
    (fun v w => Cost.lift (fun _ => 1000%N)
      (fun _ => match w with Some w => Nat.eqb v w | None => false end) tt) sample sample in
  (Cost.value checked, N.ltb 1000 (Cost.ticks checked)) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.
