(** * Keyed map signatures

    Keyed maps retain each original key alongside its value in a positive-key trie.
    For example, enumeration returns the client key stored by insertion.
    Builds on: KeySig, Trie and Argent time interfaces. *)

From Stdlib Require Import PArith List Bool.
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

Module Type MAP_LAWS (K : KEY) (Import M : MAP_OPS K).
  (* spec: wf nodes *)
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
  (** Relational checking covers all keys when absence passes. *)
  Parameter forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
    f None None = true ->
    (forall2b f m1 m2 = true <-> forall k, f (get k m1) (get k m2) = true).
  (** Existential checking finds a present value satisfying its predicate. *)
  Parameter existsb_spec : forall A (f : A -> bool) m,
    existsb f m = true <-> exists k a, get k m = Some a /\ f a = true.
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
End MAP_LAWS.

Module Type MAP (K : KEY) := MAP_OPS K <+ MAP_SPEC K <+ MAP_LAWS K.

Module Type MAP_TIME (K : KEY_T) (Import M : MAP K).
  Parameter T_get : forall {A}, K.t -> t A -> nat.
  Parameter T_set : forall {A}, K.t -> A -> t A -> nat.
  Parameter T_remove : forall {A}, K.t -> t A -> nat.
  Parameter T_merge : forall {A B C}, (option A -> option B -> option C) ->
    (option A -> option B -> nat) -> t A -> t B -> nat.
  Parameter T_forall2b : forall {A B}, (option A -> option B -> bool) ->
    (option A -> option B -> nat) -> t A -> t B -> nat.
  Parameter T_existsb : forall {A}, (A -> bool) -> (A -> nat) -> t A -> nat.
  Parameter T_fold : forall {A B}, (B -> K.t -> A -> B) ->
    (B -> K.t -> A -> nat) -> t A -> B -> nat.
  Parameter T_elements : forall {A}, t A -> nat.
  Parameter c_map : nat.
  (** Lookup takes time bounded by the encoded key length. *)
  Parameter T_get_le : forall A k (m : t A), T_get k m <= c_map * (K.bits k + 1).
  (** Insertion takes time bounded by the encoded key length. *)
  Parameter T_set_le : forall A k (a : A) m, T_set k a m <= c_map * (K.bits k + 1).
  (** Removal takes time bounded by the encoded key length. *)
  Parameter T_remove_le : forall A k (m : t A), T_remove k m <= c_map * (K.bits k + 1).
  (** Merging charges bounded callbacks over both skeletons. *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 c,
    (forall a b, T_f a b <= c) ->
    T_merge f T_f m1 m2 <= c_map * (c + 1) * (nodes m1 + nodes m2 + 1).
  (** Relational checking charges bounded callbacks over both skeletons. *)
  Parameter T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 c,
    (forall a b, T_f a b <= c) ->
    T_forall2b f T_f m1 m2 <= c_map * (c + 1) * (nodes m1 + nodes m2 + 1).
  (** Existential checking charges bounded callbacks over one skeleton. *)
  Parameter T_existsb_le : forall A (f : A -> bool) T_f m c,
    (forall a, T_f a <= c) -> T_existsb f T_f m <= c_map * (c + 1) * (nodes m + 1).
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A B (f : B -> K.t -> A -> B) T_f m b c,
    (forall acc k a, T_f acc k a <= c) ->
    T_fold f T_f m b <= c_map * (c + 1) * (nodes m + 1).
  (** Enumeration charges the encoded keys returned by a consistent map. *)
  Parameter T_elements_le : forall A (m : t A),
    wf m -> T_elements m <= c_map * (weight m + 1).
End MAP_TIME.

Module Type MAP_T (K : KEY_T) := MAP K <+ MAP_TIME K.
