(** * Map interface fixtures

    These fixtures observe replacement, deletion and canonical enumeration.
    For example, codes two, one and three have the trie traversal order.
    Builds on: BaseMap and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
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
  Cost.ticks (Map.get_code_c 3%positive sample) = 2%N.
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

Example raw_set_client {K V} (enc : encoding K) k a (v : V) m :
  Map.get enc k (Map.set enc a v m) =
    if eqb enc k a then Some v else Map.get enc k m.
Proof.
  apply Map.get_set_raw.
Qed.

Definition collision_encoding : encoding positive := of_pure (fun _ => 1%positive).
Definition malformed_storage := Map.set collision_encoding 2%positive 10 Map.empty.

Example malformed_storage_control : ~ Map.wf positive_encoding malformed_storage.
Proof.
  intro Hwf.
  pose proof (Hwf 1%positive 2%positive 10 ltac:(vm_compute; reflexivity)) as Hcode.
  vm_compute in Hcode. discriminate.
Qed.

Example malformed_storage_update_client :
  Map.get positive_encoding 1%positive (Map.set positive_encoding 3%positive 30 malformed_storage) =
    Some 10.
Proof.
  rewrite Map.get_set_raw. vm_compute. reflexivity.
Qed.

Example colliding_keys_update_client :
  Map.get collision_encoding 1%positive
    (Map.set collision_encoding 2%positive 20 malformed_storage) = Some 20.
Proof.
  rewrite Map.get_set_raw. vm_compute. reflexivity.
Qed.
