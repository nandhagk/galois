(** * Keyed map signatures

    Keyed maps retain each original key alongside its value in a positive-key trie.
    For example, enumeration returns the client key stored by insertion.
    Builds on: KeySig, Trie and Argent time interfaces. *)

From Stdlib Require Import NArith PArith List Bool.
From Argent Require Import Time.
From Galois.Base Require Import KeySig Trie.

Definition kmap (K A : Type) : Type := PTrieCode.t (K * A).

Module Type MAP_OPS (K : KEY_OPS).
  Parameter t : Type -> Type.
  Parameter empty : forall {A}, t A.
  Parameter get : forall {A}, K.t -> t A -> option A.
  Parameter set : forall {A}, K.t -> A -> t A -> t A.
  Parameter remove : forall {A}, K.t -> t A -> t A.
  Parameter merge : forall {A B C}, (option A -> option B -> option C) -> t A -> t B -> t C.
  Parameter forall2b : forall {A B}, (option A -> option B -> bool) -> t A -> t B -> bool.
  Parameter existsb : forall {A}, (A -> bool) -> t A -> bool.
  Parameter fold : forall {A B}, (B -> K.t -> A -> B) -> t A -> B -> B.
  Parameter elements : forall {A}, t A -> list (K.t * A).
End MAP_OPS.

Module Type MAP_SPEC (K : KEY_OPS) (Import M : MAP_OPS K).
  (** Weight counts encoded key bits and one unit per binding. *)
  Definition weight {A} (m : t A) : nat :=
    fold_right Nat.add 0
      (List.map (fun kv => Pos.size_nat (K.encode (fst kv)) + 1) (elements m)).
End MAP_SPEC.

Module Type MAP_LAWS (K : KEY) (Import M : MAP_OPS K) (Import S : MAP_SPEC K M).
  (* spec: wf nodes find codes *)
  Parameter find : forall {A}, positive -> t A -> option A.
  Parameter wf : forall {A}, t A -> Prop.
  Parameter nodes : forall {A}, t A -> nat.
  (** Empty maps have consistent stored keys. *)
  Parameter wf_empty : forall A, wf (@empty A).
  (** Insertion retains consistency of stored keys. *)
  Parameter wf_set : forall A k (a : A) m, wf m -> wf (set k a m).
  (** Removal retains consistency of stored keys. *)
  Parameter wf_remove : forall A k (m : t A), wf m -> wf (remove k m).
  (** Merging consistent maps retains consistent stored keys. *)
  Parameter wf_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
    wf m1 -> wf m2 -> wf (merge f m1 m2).
  (** Empty maps bind no key. *)
  Parameter get_empty : forall A k, get k (@empty A) = None.
  (** Insertion supplies the selected key's binding. *)
  Parameter get_set_same : forall A k (a : A) m, get k (set k a m) = Some a.
  (** Insertion leaves other keys unchanged. *)
  Parameter get_set_other : forall A k q (a : A) m,
    k <> q -> get k (set q a m) = get k m.
  (** Removal clears the selected binding. *)
  Parameter get_remove_same : forall A k (m : t A), get k (remove k m) = None.
  (** Removal leaves other keys unchanged. *)
  Parameter get_remove_other : forall A k q (m : t A),
    k <> q -> get k (remove q m) = get k m.
  (** Merging acts pointwise when absence remains absent. *)
  Parameter get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 k,
    f None None = None -> get k (merge f m1 m2) = f (get k m1) (get k m2).
  (** Consistent maps enumerate precisely their bindings. *)
  Parameter elements_spec : forall A (m : t A) k a, wf m ->
    (In (k, a) (elements m) <-> get k m = Some a).
  (** Consistent maps enumerate each key once. *)
  Parameter elements_nodup : forall A (m : t A), wf m -> NoDup (List.map fst (elements m)).
  (** Folding follows enumeration order. *)
  Parameter fold_spec : forall A B (f : B -> K.t -> A -> B) m b,
    fold f m b = fold_left (fun acc ka => f acc (fst ka) (snd ka)) (elements m) b.
  (** Lookup determines a consistent map. *)
  Parameter ext : forall A (m n : t A), wf m -> wf n ->
    (forall k, get k m = get k n) -> m = n.
  Parameter get_find : forall A k (m : t A), get k m = find (K.encode k) m.
  Parameter find_empty : forall A p, find p (@empty A) = None.
  Parameter find_set : forall A p k (a : A) m,
  find p (set k a m) = if Pos.eqb p (K.encode k) then Some a else find p m.
  Parameter find_remove : forall A p k (m : t A),
  find p (remove k m) = if Pos.eqb p (K.encode k) then None else find p m.
  Parameter find_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
  f None None = None -> find p (merge f m1 m2) = f (find p m1) (find p m2).
  Parameter forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
  f None None = true ->
  (forall2b f m1 m2 = true <-> forall p, f (find p m1) (find p m2) = true).
  Parameter existsb_spec : forall A (f : A -> bool) m,
  existsb f m = true <-> exists p a, find p m = Some a /\ f a = true.
  Parameter wf_find : forall A (m : t A) p a, wf m -> find p m = Some a ->
  exists k, K.encode k = p.

  Parameter nodes_empty : forall A, nodes (@empty A) = 0.
  Parameter nodes_set : forall A k (a : A) m, nodes (set k a m) <= nodes m + K.bits k.
  Parameter nodes_remove : forall A k (m : t A), nodes (remove k m) <= nodes m.
  Parameter nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
  nodes (merge f m1 m2) <= nodes m1 + nodes m2.
  Parameter nodes_le_weight : forall A (m : t A), wf m -> nodes m <= weight m.

  Parameter codes : forall {A}, t A -> list positive.
  Parameter codes_spec : forall A (m : t A) p, In p (codes m) <-> find p m <> None.
  Parameter codes_nodup : forall A (m : t A), NoDup (codes m).
  (** The stored codes cover the skeleton nodes of every map. *)
  Parameter nodes_le_codes : forall A (m : t A),
    nodes m <= fold_right Nat.add 0 (List.map (fun p => Pos.size_nat p + 1) (codes m)).
  (** Insertion adds at most the weight of its key. *)
  Parameter weight_set : forall A k (a : A) m, weight (set k a m) <= weight m + K.bits k + 1.
  (** Removal adds no label. *)
  Parameter weight_remove : forall A k (m : t A), weight (remove k m) <= weight m.
  (** A merge that keeps nothing of the right map alone keeps left labels. *)
  Parameter weight_merge_l : forall A B C (f : option A -> option B -> option C) m1 m2,
    (forall b, f None b = None) -> weight (merge f m1 m2) <= weight m1.
End MAP_LAWS.

Module Type MAP (K : KEY) := MAP_OPS K <+ MAP_SPEC K <+ MAP_LAWS K.

Module Type MAP_TIME (K : KEY_T) (Import M : MAP K).
  Parameter T_get : forall {A}, K.t -> t A -> N.
  Parameter T_set : forall {A}, K.t -> A -> t A -> N.
  Parameter T_remove : forall {A}, K.t -> t A -> N.
  Parameter T_merge : forall {A B C}, (option A -> option B -> option C) ->
    (option A -> option B -> N) -> t A -> t B -> N.
  Parameter T_forall2b : forall {A B}, (option A -> option B -> bool) ->
    (option A -> option B -> N) -> t A -> t B -> N.
  Parameter T_existsb : forall {A}, (A -> bool) -> (A -> N) -> t A -> N.
  Parameter T_fold : forall {A B}, (B -> K.t -> A -> B) ->
    (B -> K.t -> A -> N) -> t A -> B -> N.
  Parameter T_elements : forall {A}, t A -> N.
  Parameter c_map : N.
  (** Lookup takes time bounded by the encoded key length. *)
  Parameter T_get_le : forall A k (m : t A), (T_get k m <= c_map * N.of_nat (K.bits k + 1))%N.
  (** Insertion takes time bounded by the encoded key length. *)
  Parameter T_set_le : forall A k (a : A) m, (T_set k a m <= c_map * N.of_nat (K.bits k + 1))%N.
  (** Removal takes time bounded by the encoded key length. *)
  Parameter T_remove_le : forall A k (m : t A), (T_remove k m <= c_map * N.of_nat (K.bits k + 1))%N.
  (** Merging charges bounded callbacks over both skeletons. *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_merge f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  (** Relational checking charges bounded callbacks over both skeletons. *)
  Parameter T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_forall2b f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  (** Existential checking charges bounded callbacks over one skeleton. *)
  Parameter T_existsb_le : forall A (f : A -> bool) T_f m c,
    ((forall a, T_f a <= c) -> T_existsb f T_f m <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A B (f : B -> K.t -> A -> B) T_f m b c,
    ((forall acc k a, T_f acc k a <= c) ->
    T_fold f T_f m b <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  (** Enumeration charges the encoded keys returned by a consistent map. *)
  Parameter T_elements_le : forall A (m : t A),
    (wf m -> T_elements m <= c_map * N.of_nat (weight m + 1))%N.
  Parameter T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Parameter T_forall2b_sum_le : forall A B (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Parameter T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_map * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match find p m with Some a => T_f a | None => 0 end) (codes m))))%N.
  Parameter T_fold_sum_le : forall A B (f : B -> K.t -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_map * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
End MAP_TIME.

Module Type MAP_T (K : KEY_T) := MAP K <+ MAP_TIME K.
