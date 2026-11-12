(** * Trie signatures

    Canonical tries store values at positive keys.
    For example, lookup after setting key 1 returns the inserted value.
    Builds on: Stdlib lists and binary arithmetic, and Argent time interfaces. *)

From Stdlib Require Import NArith PArith List Bool Sorting.Sorted.
From Argent Require Import Time.

Fixpoint trie_lt (p q : positive) : Prop :=
  match p, q with
  | xO p, xO q => trie_lt p q
  | xI p, xI q => trie_lt p q
  | xO _, xH | xO _, xI _ | xH, xI _ => True
  | _, _ => False
  end.

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
  (* spec: nodes *)
  Parameter nodes : forall {A}, t A -> nat.
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
  Parameter is_empty_spec : forall A (m : t A), is_empty m = true <-> m = empty.
  Parameter nodes_remove : forall A p (m : t A), nodes (remove p m) <= nodes m.
  Parameter nodes_map : forall A B (f : A -> B) m, nodes (map f m) <= nodes m.
  Parameter nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
  nodes (merge f m1 m2) <= nodes m1 + nodes m2.
End TRIE_LAWS.

Module Type TRIE := TRIE_OPS <+ TRIE_SPEC <+ TRIE_LAWS.

Module Type TRIE_TIME (Import T : TRIE).
  Parameter T_is_empty : forall {A}, t A -> N.
  Parameter T_get : forall {A}, positive -> t A -> N.
  Parameter T_set : forall {A}, positive -> A -> t A -> N.
  Parameter T_remove : forall {A}, positive -> t A -> N.
  Parameter T_merge : forall {A B C}, (option A -> option B -> option C) ->
    (option A -> option B -> N) -> t A -> t B -> N.
  Parameter T_forall2b : forall {A B}, (option A -> option B -> bool) ->
    (option A -> option B -> N) -> t A -> t B -> N.
  Parameter T_existsb : forall {A}, (A -> bool) -> (A -> N) -> t A -> N.
  Parameter T_map : forall {A B}, (A -> B) -> (A -> N) -> t A -> N.
  Parameter T_fold : forall {A B}, (B -> positive -> A -> B) ->
    (B -> positive -> A -> N) -> t A -> B -> N.
  Parameter T_elements : forall {A}, t A -> N.
  Parameter c_trie : N.
  (** Emptiness testing takes constant time. *)
  Parameter T_is_empty_le : forall A (m : t A), (T_is_empty m <= c_trie)%N.
  (** Lookup takes time bounded by the key bit length. *)
  Parameter T_get_le : forall A p (m : t A),
    (T_get p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  (** Setting takes time bounded by the key bit length. *)
  Parameter T_set_le : forall A p (a : A) m,
    (T_set p a m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  (** Removal takes time bounded by the key bit length. *)
  Parameter T_remove_le : forall A p (m : t A),
    (T_remove p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  (** Merging charges bounded callbacks over both skeletons. *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_merge f T_f m1 m2 <= c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  (** Relational checking charges bounded callbacks over both skeletons. *)
  Parameter T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_forall2b f T_f m1 m2 <= c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  (** Existential checking charges bounded callbacks over one skeleton. *)
  Parameter T_existsb_le : forall A (f : A -> bool) T_f m k,
    ((forall a, T_f a <= k) -> T_existsb f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  (** Mapping charges bounded callbacks over one skeleton. *)
  Parameter T_map_le : forall A B (f : A -> B) T_f m k,
    ((forall a, T_f a <= k) -> T_map f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A B (f : B -> positive -> A -> B) T_f m b k,
    ((forall acc p a, T_f acc p a <= k) ->
    T_fold f T_f m b <= c_trie * ((k + 1) * N.of_nat (nodes m + 1) +
      N.of_nat (weight m)))%N.
  (** Enumeration charges the bits of the keys it returns. *)
  Parameter T_elements_le : forall A (m : t A),
    (T_elements m <= c_trie * N.of_nat (weight m + 1))%N.
  (** Lookup visits every key bit even below absent subtrees. *)
  Parameter get_tight : forall A p (m : t A), (N.of_nat (Pos.size_nat p) <= T_get p m)%N.
  Parameter T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Parameter T_forall2b_sum_le : forall A B (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Parameter T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_trie * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match get p m with Some a => T_f a | None => 0 end) (List.map fst (elements m)))))%N.
  Parameter T_fold_sum_le : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_trie * (N.of_nat (nodes m + 1) + N.of_nat (weight m) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
End TRIE_TIME.

Module Type TRIE_T := TRIE <+ TRIE_TIME.

Module Type TRIE_PLAN (Import T : TRIE_T).
  Parameter left : forall {A}, t A -> t A.
  Parameter value : forall {A}, t A -> option A.
  Parameter right : forall {A}, t A -> t A.
  Parameter node : forall {A}, t A -> option A -> t A -> t A.
  Parameter replace : forall {A}, positive -> option A -> t A -> t A.
  Parameter filter_map : forall {A B}, (A -> option B) -> t A -> t B.
  Parameter merge_with : forall {A B C}, (option A -> option B -> option C) ->
    (t A -> t C) -> (t B -> t C) -> t A -> t B -> t C.
  Parameter forall2 : forall {A B}, (A -> option B -> bool) -> t A -> t B -> bool.
  Parameter fold_values : forall {A B}, (B -> A -> B) -> t A -> B -> B.
  Parameter fold_path : forall {A B}, (B -> positive -> A -> B) ->
    (positive -> positive) -> t A -> B -> B.
  Parameter T_left : forall {A}, t A -> N.
  Parameter T_value : forall {A}, t A -> N.
  Parameter T_right : forall {A}, t A -> N.
  Parameter T_node : forall {A}, t A -> option A -> t A -> N.
  Parameter T_replace : forall {A}, positive -> option A -> t A -> N.
  Parameter T_filter_map : forall {A B}, (A -> option B) -> (A -> N) -> t A -> N.
  Parameter T_merge_with : forall {A B C}, (option A -> option B -> option C) ->
    (option A -> option B -> N) -> (t A -> t C) -> (t A -> N) ->
    (t B -> t C) -> (t B -> N) -> t A -> t B -> N.
  Parameter T_forall2 : forall {A B}, (A -> option B -> bool) ->
    (A -> option B -> N) -> t A -> t B -> N.
  Parameter T_fold_values : forall {A B}, (B -> A -> B) ->
    (B -> A -> N) -> t A -> B -> N.
  Parameter T_fold_path : forall {A B}, (B -> positive -> A -> B) ->
    (B -> positive -> A -> N) -> (positive -> positive) ->
    (positive -> N) -> t A -> B -> N.
  Parameter k_node k_replace k_filter k_merge k_check k_fold k_elements : N.

  (** Binding count ignores unary skeleton nodes without stored values. *)
  Definition bindings {A} (m : t A) : nat := length (elements m).

  (** Key mass counts every bit materialized when the traversal emits complete keys. *)
  Definition key_mass {A} (m : t A) : nat :=
    fold_right Nat.add 0 (List.map (fun kv => Pos.size_nat (fst kv)) (elements m)).

  (** Callback work uses each accumulator reached in enumeration order. *)
  Definition fold_work {A B} (f : B -> positive -> A -> B)
      (T_f : B -> positive -> A -> N) (m : t A) (b : B) : N :=
    snd (fold_left (fun bw kv =>
      (f (fst bw) (fst kv) (snd kv), (snd bw + T_f (fst bw) (fst kv) (snd kv))%N))
      (elements m) (b, 0%N)).

  (** Rebuilding from the three observations gives the original canonical trie. *)
  Parameter F1_node : forall A (m : t A), node (left m) (value m) (right m) = m.
  (** Rebuilding allocates at most one node beyond the children. *)
  Parameter F2_nodes_node : forall A (l r : t A) o,
    nodes (node l o r) <= S (nodes l + nodes r).
  (** Weight consists of materialized key bits and one unit per binding. *)
  Parameter F3_weight : forall A (m : t A), weight m = key_mass m + bindings m.
  (** Every binding occupies a skeleton node. *)
  Parameter F4_bindings : forall A (m : t A), bindings m <= nodes m.
  (** Path folding applies the supplied prefix function to each emitted key. *)
  Parameter F5_fold_path : forall A B (f : B -> positive -> A -> B) path m b,
    fold_path f path m b =
      fold_left (fun acc kv => f acc (path (fst kv)) (snd kv)) (elements m) b.
  (** A uniform callback bound bounds the sum at the reached accumulators. *)
  Parameter F6_fold_work : forall A B (f : B -> positive -> A -> B) T_f m b c,
    ((forall acc p a, T_f acc p a <= c) -> fold_work f T_f m b <= c * N.of_nat (bindings m))%N.
  (** Replacement changes precisely the selected key. *)
  Parameter F7_replace : forall A p q o (m : t A),
    get p (replace q o m) = if Pos.eqb p q then o else get p m.
  (** Filtering acts independently on present bindings. *)
  Parameter F8_filter : forall A B (f : A -> option B) m p,
    get p (filter_map f m) = match get p m with Some a => f a | None => None end.

  (** Value-only folding has the same order and avoids constructing keys. *)
  Parameter F9_fold_values : forall A B (f : B -> A -> B) m b,
    fold_values f m b =
      fold_left (fun acc kv => f acc (snd kv)) (elements m) b.

  (** Child observations and canonical rebuilding take constant time. *)
  Parameter T1_node : forall A (l r : t A) o,
    (T_left l + T_value l + T_right l + T_node l o r <= k_node)%N.
  (** Replacement descends once per bit and rebuilds the selected path. *)
  Parameter T2_replace : forall A p o (m : t A),
    (T_replace p o m <= k_replace * N.of_nat (Pos.size_nat p + 1))%N.
  (** Filtering visits one skeleton and charges its present-value callbacks. *)
  Parameter T3_filter : forall A B (f : A -> option B) T_f m c,
    ((forall a, T_f a <= c) ->
    T_filter_map f T_f m <= k_filter * (c + 1) * N.of_nat (nodes m + 1))%N.
  (** Filtering charges each callback at its present binding. *)
  Parameter T3_filter_sum : forall A B (f : A -> option B) T_f m,
    (T_filter_map f T_f m <= k_filter * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun ka => T_f (snd ka)) (elements m))))%N.
  (** General merging charges shared nodes and the delegated one-sided traversals. *)
  Parameter T4_merge_with : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u c cl cr,
    ((forall a b, T_f a b <= c) ->
    (forall a, T_fl a <= cl * N.of_nat (nodes a + 1)) ->
    (forall b, T_fr b <= cr * N.of_nat (nodes b + 1)) ->
    T_merge_with f T_f fl T_fl fr T_fr m u <=
      k_merge * (c + cl + cr + 1) * N.of_nat (nodes m + nodes u + 1))%N.
  (** Merging charges the callbacks at shared and one-sided bindings. *)
  Parameter T4_merge_with_sum : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u cl cr,
    (forall a, T_fl a <= cl * (N.of_nat (nodes a + 1) + fold_right N.add 0
       (List.map (fun ka => T_f (Some (snd ka)) None) (elements a))))%N ->
    (forall b, T_fr b <= cr * (N.of_nat (nodes b + 1) + fold_right N.add 0
       (List.map (fun kb => T_f None (Some (snd kb))) (elements b))))%N ->
    (T_merge_with f T_f fl T_fl fr T_fr m u <= k_merge * (cl + cr + 1) *
      ((T_f None None + 1) * N.of_nat (nodes m + nodes u + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m) (get p u))
         (List.map fst (elements m) ++ List.map fst (elements u)))))%N.
  (** One directional check visits the left skeleton and may stop early. *)
  Parameter T5_forall2 : forall A B (f : A -> option B -> bool) T_f m u c,
    ((forall a b, T_f a b <= c) ->
    T_forall2 f T_f m u <= k_check * (c + 1) * N.of_nat (nodes m + 1))%N.
  (** Directional checking charges each visited binding against its lookup result. *)
  Parameter T5_forall2_sum : forall A B (f : A -> option B -> bool) T_f m u,
    (T_forall2 f T_f m u <= k_check * (N.of_nat (nodes m + 1) +
      fold_right N.add 0
        (List.map (fun ka => T_f (snd ka) (get (fst ka) u)) (elements m))))%N.
  (** Path folding charges each reconstructed key and the supplied prefix callback. *)
  Parameter T6_fold_path : forall A B (f : B -> positive -> A -> B) T_f path T_path m b c d,
    ((forall acc p a, T_f acc p a <= c) -> (forall p, T_path p <= d) ->
    T_fold_path f T_f path T_path m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + (c + d + 1) * N.of_nat (bindings m) + 1))%N.
  (** Public folding retains the materialized-key charge of the landed algorithm. *)
  Parameter T7_fold_work : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + fold_work f T_f m b + 1))%N.
  (** Enumeration adds the final reversal to keyed fold work. *)
  Parameter T8_elements : forall A (m : t A),
    (T_elements m <= k_elements * N.of_nat (nodes m + key_mass m + bindings m + 1))%N.

  (** Value-only folding supports skeleton-linear map and set wrappers over stored keys. *)
  Parameter T9_fold_values : forall A B (f : B -> A -> B) T_f m b c,
    ((forall acc a, T_f acc a <= c) ->
    T_fold_values f T_f m b <= k_fold * (c + 1) * N.of_nat (nodes m + 1))%N.

  (** Value folding charges callbacks in enumeration order without constructing keys. *)
  Parameter T_fold_values_sum_le : forall A B (f : B -> A -> B) T_f m b,
    (T_fold_values f T_f m b <= c_trie * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (snd ka), snd bw + T_f (fst bw) (snd ka)))
        (elements m) (b, 0))))%N.
End TRIE_PLAN.

Module Type TRIE_ALL := TRIE_T <+ TRIE_PLAN.
