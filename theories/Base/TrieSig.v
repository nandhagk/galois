(** * Trie signatures

    Canonical tries store values at positive keys.
    For example, lookup after setting key 1 returns the inserted value.
    Builds on: Stdlib lists and binary arithmetic, and Argent time interfaces. *)

From Stdlib Require Import PArith List Bool Sorting.Sorted.
From Argent Require Import Time.

Module Type TRIE_OPS.
  Parameter t : Type -> Type.
  Parameter empty : forall {A}, t A.
  Parameter is_empty : forall {A}, t A -> bool.
  Parameter get : forall {A}, positive -> t A -> option A.
  Parameter set : forall {A}, positive -> A -> t A -> t A.
  Parameter remove : forall {A}, positive -> t A -> t A.
  Parameter merge : forall {A B C}, (option A -> option B -> option C) -> t A -> t B -> t C.
  Parameter forall2b : forall {A B}, (option A -> option B -> bool) -> t A -> t B -> bool.
  Parameter existsb : forall {A}, (A -> bool) -> t A -> bool.
  Parameter map : forall {A B}, (A -> B) -> t A -> t B.
  Parameter fold : forall {A B}, (B -> positive -> A -> B) -> t A -> B -> B.
  Parameter elements : forall {A}, t A -> list (positive * A).
End TRIE_OPS.

Module Type TRIE_SPEC (Import T : TRIE_OPS).
  (** Weight counts the bits of every stored key and one unit per binding. *)
  Definition weight {A} (m : t A) : nat :=
    fold_right Nat.add 0 (List.map (fun kv => Pos.size_nat (fst kv) + 1) (elements m)).
End TRIE_SPEC.

Module Type TRIE_LAWS (Import T : TRIE_OPS) (Import S : TRIE_SPEC T).
  (* spec: nodes trie_lt *)
  Parameter nodes : forall {A}, t A -> nat.
  Parameter trie_lt : positive -> positive -> Prop.
  (** Empty tries have no bindings. *)
  Parameter get_empty : forall A p, get p (@empty A) = None.
  (** Setting a key supplies its binding. *)
  Parameter get_set_same : forall A p (a : A) m, get p (set p a m) = Some a.
  (** Setting another key leaves a lookup unchanged. *)
  Parameter get_set_other : forall A p q (a : A) m,
    p <> q -> get p (set q a m) = get p m.
  (** Removing a key clears its binding. *)
  Parameter get_remove_same : forall A p (m : t A), get p (remove p m) = None.
  (** Removing another key leaves a lookup unchanged. *)
  Parameter get_remove_other : forall A p q (m : t A),
    p <> q -> get p (remove q m) = get p m.
  (** Merging acts pointwise when the callback creates no absent binding. *)
  Parameter get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
    f None None = None -> get p (merge f m1 m2) = f (get p m1) (get p m2).
  (** Relational checking covers every key when absence passes. *)
  Parameter forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
    f None None = true ->
    (forall2b f m1 m2 = true <-> forall p, f (get p m1) (get p m2) = true).
  (** Existential checking finds a stored value satisfying the predicate. *)
  Parameter existsb_spec : forall A (f : A -> bool) m,
    existsb f m = true <-> exists p a, get p m = Some a /\ f a = true.
  (** Mapping changes each present value independently. *)
  Parameter get_map : forall A B (f : A -> B) m p,
    get p (map f m) = option_map f (get p m).
  (** Enumeration contains precisely the bindings. *)
  Parameter elements_spec : forall A (m : t A) p a,
    In (p, a) (elements m) <-> get p m = Some a.
  (** Enumeration follows the trie key order. *)
  Parameter elements_sorted : forall A (m : t A),
    StronglySorted (fun x y => trie_lt (fst x) (fst y)) (elements m).
  (** Enumeration visits each key once. *)
  Parameter elements_nodup : forall A (m : t A), NoDup (List.map fst (elements m)).
  (** Folding follows enumeration order. *)
  Parameter fold_spec : forall A B (f : B -> positive -> A -> B) m b,
    fold f m b = fold_left (fun acc kv => f acc (fst kv) (snd kv)) (elements m) b.
  (** Lookup observations determine a canonical trie. *)
  Parameter ext : forall A (m n : t A), (forall p, get p m = get p n) -> m = n.
  (** Setting allocates at most one skeleton node per key bit. *)
  Parameter nodes_set : forall A p (a : A) m,
    nodes (set p a m) <= nodes m + Pos.size_nat p.
  (** Binding weight covers the skeleton nodes. *)
  Parameter nodes_le_weight : forall A (m : t A), nodes m <= weight m.
End TRIE_LAWS.

Module Type TRIE := TRIE_OPS <+ TRIE_SPEC <+ TRIE_LAWS.

Module Type TRIE_TIME (Import T : TRIE).
  Parameter T_is_empty : forall {A}, t A -> nat.
  Parameter T_get : forall {A}, positive -> t A -> nat.
  Parameter T_set : forall {A}, positive -> A -> t A -> nat.
  Parameter T_remove : forall {A}, positive -> t A -> nat.
  Parameter T_merge : forall {A B C}, (option A -> option B -> option C) ->
    (option A -> option B -> nat) -> t A -> t B -> nat.
  Parameter T_forall2b : forall {A B}, (option A -> option B -> bool) ->
    (option A -> option B -> nat) -> t A -> t B -> nat.
  Parameter T_existsb : forall {A}, (A -> bool) -> (A -> nat) -> t A -> nat.
  Parameter T_map : forall {A B}, (A -> B) -> (A -> nat) -> t A -> nat.
  Parameter T_fold : forall {A B}, (B -> positive -> A -> B) ->
    (B -> positive -> A -> nat) -> t A -> B -> nat.
  Parameter T_elements : forall {A}, t A -> nat.
  Parameter c_trie : nat.
  (** Emptiness testing takes constant time. *)
  Parameter T_is_empty_le : forall A (m : t A), T_is_empty m <= c_trie.
  (** Lookup takes time bounded by the key bit length. *)
  Parameter T_get_le : forall A p (m : t A),
    T_get p m <= c_trie * (Pos.size_nat p + 1).
  (** Setting takes time bounded by the key bit length. *)
  Parameter T_set_le : forall A p (a : A) m,
    T_set p a m <= c_trie * (Pos.size_nat p + 1).
  (** Removal takes time bounded by the key bit length. *)
  Parameter T_remove_le : forall A p (m : t A),
    T_remove p m <= c_trie * (Pos.size_nat p + 1).
  (** Merging charges bounded callbacks over both skeletons. *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 k,
    (forall a b, T_f a b <= k) ->
    T_merge f T_f m1 m2 <= c_trie * (k + 1) * (nodes m1 + nodes m2 + 1).
  (** Relational checking charges bounded callbacks over both skeletons. *)
  Parameter T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 k,
    (forall a b, T_f a b <= k) ->
    T_forall2b f T_f m1 m2 <= c_trie * (k + 1) * (nodes m1 + nodes m2 + 1).
  (** Existential checking charges bounded callbacks over one skeleton. *)
  Parameter T_existsb_le : forall A (f : A -> bool) T_f m k,
    (forall a, T_f a <= k) -> T_existsb f T_f m <= c_trie * (k + 1) * (nodes m + 1).
  (** Mapping charges bounded callbacks over one skeleton. *)
  Parameter T_map_le : forall A B (f : A -> B) T_f m k,
    (forall a, T_f a <= k) -> T_map f T_f m <= c_trie * (k + 1) * (nodes m + 1).
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A B (f : B -> positive -> A -> B) T_f m b k,
    (forall acc p a, T_f acc p a <= k) ->
    T_fold f T_f m b <= c_trie * (k + 1) * (nodes m + 1).
  (** Enumeration charges the bits of the keys it returns. *)
  Parameter T_elements_le : forall A (m : t A), T_elements m <= c_trie * (weight m + 1).
  (** Lookup visits every key bit even below absent subtrees. *)
  Parameter get_tight : forall A p (m : t A), Pos.size_nat p <= T_get p m.
End TRIE_TIME.

Module Type TRIE_T := TRIE <+ TRIE_TIME.
