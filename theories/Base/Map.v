(** * Trie maps

    Maps store client keys and values in a canonical trie.
    For example, enumeration returns the client key stored by insertion.
    Builds on: KeySig, TrieSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig TrieSig MapSig.
From Galois.Base Require Import Trie.


Module Datatypes.
  TimeFun option_map.
End Datatypes.

Module TrieMapCode (K : KEY_OPS) <: MAP_OPS K.
  Definition t := kmap K.t.
  Definition empty {A} : t A := PTrieCode.empty.
  Definition find {A} (p : positive) (m : t A) := option_map snd (PTrieCode.get p m).
  Definition get {A} (k : K.t) (m : t A) := option_map snd (PTrieCode.get (K.encode k) m).
  Definition set {A} (k : K.t) (a : A) (m : t A) := PTrieCode.set (K.encode k) (k, a) m.
  Definition remove {A} (k : K.t) (m : t A) := PTrieCode.remove (K.encode k) m.
  Definition merge {A B C} (f : option A -> option B -> option C) (x : t A) (y : t B) : t C :=
    PTrieCode.merge (fun a b =>
      match a, b with
      | Some (k, v), Some (_, w) => option_map (pair k) (f (Some v) (Some w))
      | Some (k, v), None => option_map (pair k) (f (Some v) None)
      | None, Some (k, w) => option_map (pair k) (f None (Some w))
      | None, None => None
      end) x y.
  Definition forall2b {A B} (f : option A -> option B -> bool) (x : t A) (y : t B) :=
    PTrieCode.forall2b (fun a b => f (option_map snd a) (option_map snd b)) x y.
  Definition existsb {A} (f : A -> bool) (x : t A) := PTrieCode.existsb (fun kv => f (snd kv)) x.
  Definition fold {A B} (f : B -> K.t -> A -> B) (x : t A) (b : B) :=
    PTrieCode.fold_values (fun acc kv => f acc (fst kv) (snd kv)) x b.
  Definition elements {A} (x : t A) : list (K.t * A) :=
    List.rev (fold (fun acc k a => (k, a) :: acc) x nil).
End TrieMapCode.

Module TrieMapTimePilot (K : KEY_T).
  Include TrieMapCode K.
  TimeFun get.
  TimeFun set.
  Definition lookup_again {A} (k : K.t) (m : t A) := get k m.
  TimeFun lookup_again.
End TrieMapTimePilot.

Module TrieMap (K : KEY) <: MAP K.
  Include TrieMapCode K.
  Include MAP_SPEC K.
  Definition wf {A} (m : t A) : Prop :=
    forall p k a, PTrieCode.get p m = Some (k, a) -> K.encode k = p.
  Definition nodes {A} (m : t A) : nat := PTrie.nodes m.
  Definition codes {A} (m : t A) : list positive := List.map fst (PTrieCode.elements m).
  Lemma wf_empty : forall A, wf (@empty A).
  Proof. Admitted.
  Lemma wf_set : forall A k (a : A) m, wf m -> wf (set k a m).
  Proof. Admitted.
  Lemma wf_remove : forall A k (m : t A), wf m -> wf (remove k m).
  Proof. Admitted.
  Lemma wf_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
    wf m1 -> wf m2 -> wf (merge f m1 m2).
  Proof. Admitted.
  Lemma get_empty : forall A k, get k (@empty A) = None.
  Proof. Admitted.
  Lemma get_set_same : forall A k (a : A) m, get k (set k a m) = Some a.
  Proof. Admitted.
  Lemma get_set_other : forall A k q (a : A) m,
    k <> q -> get k (set q a m) = get k m.
  Proof. Admitted.
  Lemma get_remove_same : forall A k (m : t A), get k (remove k m) = None.
  Proof. Admitted.
  Lemma get_remove_other : forall A k q (m : t A),
    k <> q -> get k (remove q m) = get k m.
  Proof. Admitted.
  Lemma get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 k,
    f None None = None -> get k (merge f m1 m2) = f (get k m1) (get k m2).
  Proof. Admitted.
  Lemma elements_spec : forall A (m : t A) k a, wf m ->
    (In (k, a) (elements m) <-> get k m = Some a).
  Proof. Admitted.
  Lemma elements_nodup : forall A (m : t A), wf m -> NoDup (List.map fst (elements m)).
  Proof. Admitted.
  Lemma fold_spec : forall A B (f : B -> K.t -> A -> B) m b,
    fold f m b = fold_left (fun acc ka => f acc (fst ka) (snd ka)) (elements m) b.
  Proof. Admitted.
  Lemma ext : forall A (m n : t A), wf m -> wf n ->
    (forall k, get k m = get k n) -> m = n.
  Proof. Admitted.
  Lemma get_find : forall A k (m : t A), get k m = find (K.encode k) m.
  Proof. Admitted.
  Lemma find_empty : forall A p, find p (@empty A) = None.
  Proof. Admitted.
  Lemma find_set : forall A p k (a : A) m,
  find p (set k a m) = if Pos.eqb p (K.encode k) then Some a else find p m.
  Proof. Admitted.
  Lemma find_remove : forall A p k (m : t A),
  find p (remove k m) = if Pos.eqb p (K.encode k) then None else find p m.
  Proof. Admitted.
  Lemma find_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
  f None None = None -> find p (merge f m1 m2) = f (find p m1) (find p m2).
  Proof. Admitted.
  Lemma forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
  f None None = true ->
  (forall2b f m1 m2 = true <-> forall p, f (find p m1) (find p m2) = true).
  Proof. Admitted.
  Lemma existsb_spec : forall A (f : A -> bool) m,
  existsb f m = true <-> exists p a, find p m = Some a /\ f a = true.
  Proof. Admitted.
  Lemma wf_find : forall A (m : t A) p a, wf m -> find p m = Some a ->
  exists k, K.encode k = p.
  Proof. Admitted.
  Lemma nodes_empty : forall A, nodes (@empty A) = 0.
  Proof. Admitted.
  Lemma nodes_set : forall A k (a : A) m, nodes (set k a m) <= nodes m + K.bits k.
  Proof. Admitted.
  Lemma nodes_remove : forall A k (m : t A), nodes (remove k m) <= nodes m.
  Proof. Admitted.
  Lemma nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
  nodes (merge f m1 m2) <= nodes m1 + nodes m2.
  Proof. Admitted.
  Lemma nodes_le_weight : forall A (m : t A), wf m -> nodes m <= weight m.
  Proof. Admitted.
  Lemma codes_spec : forall A (m : t A) p, In p (codes m) <-> find p m <> None.
  Proof. Admitted.
  Lemma codes_nodup : forall A (m : t A), NoDup (codes m).
  Proof. Admitted.
End TrieMap.

Module TrieMapT (K : KEY_T) <: MAP_T K.
  Include TrieMap K.
  TimeFun find.
  TimeFun get.
  TimeFun set.
  TimeFun remove.
  TimeFun merge.
  TimeFun forall2b.
  TimeFun existsb.
  TimeFun fold.
  TimeFun elements.
  Definition c_map : N := 1. (* STUB *)
  Lemma T_get_le : forall A k (m : t A), (T_get k m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_set_le : forall A k (a : A) m, (T_set k a m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_remove_le : forall A k (m : t A), (T_remove k m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_merge f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_forall2b f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_existsb_le : forall A (f : A -> bool) T_f m c,
    ((forall a, T_f a <= c) -> T_existsb f T_f m <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fold_le : forall A B (f : B -> K.t -> A -> B) T_f m b c,
    ((forall acc k a, T_f acc k a <= c) ->
    T_fold f T_f m b <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_elements_le : forall A (m : t A),
    (wf m -> T_elements m <= c_map * N.of_nat (weight m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forall2b_sum_le : forall A B (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_map * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match find p m with Some a => T_f a | None => 0 end) (codes m))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fold_sum_le : forall A B (f : B -> K.t -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_map * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof. Admitted. (* STUB *)

End TrieMapT.
