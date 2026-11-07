(** * Real trie VM gate workloads

    Legacy and costed tries perform identical insertion, lookup, intersection and difference.
    For example, intersection with the first half retains that half in both implementations.
    Builds on: CollectionsTrie, BaseTrie, BaseTrieMerge and CostList. *)

From Stdlib Require Import NArith List Bool.
From GaloisLegacy.Collections Require Import CollectionsTrie.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseTrie BaseTrieMerge.
Import List.ListNotations Cost.Notations.

Module Pure := CollectionsTrie.Trie.

(** Binary successor supplies identical inputs without repeated unary conversion. *)
Fixpoint keys_from (n : nat) (p : positive) : list positive :=
  match n with
  | O => []
  | S n => p :: keys_from n (Pos.succ p)
  end.

Definition keys n := keys_from n 1.

(** Both measured clients use the pilot's binary-successor input size. *)
Definition gate_size : nat := 10 * 4000.

Definition pure_build n : Pure.t bool :=
  fold_left (fun tr p => Pure.set p true tr) (keys n) Pure.empty.

Definition costed_build n : Cost.t (Trie.t bool) :=
  fold_left_c (fun tr p => Trie.set_c p true tr) (keys n) Trie.empty.

(** The observation includes every lookup result from each of the three result tries. *)
Definition pure_workload n :=
  let all := pure_build n in
  let half := pure_build (Nat.div n 2) in
  let inter := Pure.combine
    (fun a b => match a, b with Some _, Some _ => Some true | _, _ => None end) all half in
  let diff := Pure.combine
    (fun a b => match b with None => a | Some _ => None end) all half in
  (List.map (fun p => Pure.get p all) (keys n),
    List.map (fun p => Pure.get p inter) (keys n),
    List.map (fun p => Pure.get p diff) (keys n)).

(** The costed client retains all builder, lookup and specialized merge charges. *)
Definition costed_workload n :=
  let* all := costed_build n in
  let* half := costed_build (Nat.div n 2) in
  let* inter := TrieMerge.inter_with_c (fun a b => Cost.ret (andb a b)) all half in
  let* diff := TrieMerge.diff_c all half in
  let* obs_all := map_c (fun p => Trie.get_c p all) (keys n) in
  let* obs_inter := map_c (fun p => Trie.get_c p inter) (keys n) in
  let* obs_diff := map_c (fun p => Trie.get_c p diff) (keys n) in
  Cost.ret (obs_all, obs_inter, obs_diff).

(** A shared independent observation fixes all values and their input order. *)
Definition expected n :=
  let half_limit := N.of_nat (Nat.div n 2) in
  let in_half := fun p => N.leb (N.pos p) half_limit in
  (repeat (Some true) n,
    List.map (fun p => if in_half p then Some true else None) (keys n),
    List.map (fun p => if in_half p then None else Some true) (keys n)).

Example differential_small : Cost.value (costed_workload 7) = pure_workload 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_workloads :
  (Cost.value (costed_workload 0), pure_workload 0) = (expected 0, expected 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_workloads :
  (Cost.value (costed_workload 1), pure_workload 1) = (expected 1, expected 1).
Proof.
  vm_compute. reflexivity.
Qed.
