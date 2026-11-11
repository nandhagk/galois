(** * Importing map merge cost clients

    Right-key budgets leave the accumulated map unrestricted and retain nonunit collisions.
    For example, a nineteen-tick callback is charged at a shared singleton key.
    Builds on: BaseMapCost and BaseEncoding. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseTrieCost BaseMap BaseMapCost.

(** Generic union retains a nonunit collision callback under the right-key numerical theorem. *)
Example map_union_callback_contract (old : Map.t positive nat) :
  (Cost.ticks (Map.union_with_c
    (fun a b => Cost.lift (fun _ => 19%N) (fun _ => (a + b)%nat) tt)
    old (Map.set positive_encoding 2%positive 7%nat Map.empty)) <=
    (TrieCost.trie_k + 19) * (1 + 1 * 2))%N.
Proof.
  eapply N.le_trans.
  - apply (MapCost.union_with_numeric_cost_right positive_encoding _ _ _ 2 19).
    + apply Map.wf_set, Map.wf_empty.
    + intros k v Hget; rewrite Map.get_set in Hget by apply Map.wf_empty.
      destruct (eqb_spec positive_encoding positive_encoding_laws k 2%positive)
        as [Heq | Hne].
      * subst k; vm_compute; discriminate.
      * rewrite Map.get_empty in Hget; discriminate.
    + intros a b; rewrite Cost.ticks_lift; reflexivity.
  - vm_compute; discriminate.
Qed.

Example map_union_collision_ticks :
  Cost.ticks (Map.union_with_c
    (fun a b => Cost.lift (fun _ => 19%N) (fun _ => (a + b)%nat) tt)
    (Map.set positive_encoding 2%positive 5%nat Map.empty)
    (Map.set positive_encoding 2%positive 7%nat Map.empty)) = 23%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example map_union_disjoint_ticks :
  Cost.ticks (Map.union_with_c
    (fun a b => Cost.lift (fun _ => 19%N) (fun _ => (a + b)%nat) tt)
    (Map.set positive_encoding 3%positive 5%nat Map.empty)
    (Map.set positive_encoding 2%positive 7%nat Map.empty)) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example symbolic_raw_map_emptiness {K V} (m : Map.t K V) :
  Cost.ticks (Map.is_empty_c m) = 0%N.
Proof.
  apply MapCost.is_empty_cost.
Qed.

Example empty_map_root_control :
  (Map.is_empty (@Map.empty positive nat),
   Cost.ticks (Map.is_empty_c (@Map.empty positive nat))) = (true, 0%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example nonempty_map_root_control :
  let m := Map.set positive_encoding 2%positive 7%nat Map.empty in
  (Map.is_empty m, Cost.ticks (Map.is_empty_c m)) = (false, 0%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** Combination retains arbitrary callback charges and counts both physical skeletons. *)
Example map_combine_symbolic_contract {K V W U}
    (f : option V -> option W -> Cost.t (option U)) (m : Map.t K V) (n : Map.t K W) :
  (Cost.ticks (Map.combine_c f m n) <=
    TrieCost.trie_k * (1 + MapCost.skeleton_nodes m + MapCost.skeleton_nodes n) +
      TrieCost.combine_work (fun a b => Cost.ticks (Map.combine_pair_c f a b)) m n)%N.
Proof.
  apply MapCost.combine_cost.
Qed.

(** The combination callback charges nineteen ticks even on one-sided entries. *)
Definition combine_nonunit (a b : option nat) : Cost.t (option nat) :=
  Cost.lift (fun _ => 19%N) (fun _ =>
    match a, b with
    | Some x, Some y => Some (x + y)%nat
    | Some x, None | None, Some x => Some x
    | None, None => None
    end) tt.

Example map_combine_empty_ticks :
  Cost.ticks (Map.combine_c combine_nonunit
    (@Map.empty positive nat) (@Map.empty positive nat)) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example map_combine_shared_callback :
  Cost.ticks (Map.combine_c combine_nonunit
    (Map.set positive_encoding 2%positive 5%nat Map.empty)
    (Map.set positive_encoding 2%positive 7%nat Map.empty)) = 23%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example map_combine_one_sided_callbacks :
  Cost.ticks (Map.combine_c combine_nonunit
    (Map.set positive_encoding 2%positive 5%nat Map.empty)
    (Map.set positive_encoding 3%positive 7%nat Map.empty)) = 45%N.
Proof.
  vm_compute; reflexivity.
Qed.
