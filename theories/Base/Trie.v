(** * Canonical binary trie code

    Seven nonempty node shapes give finite positive-key maps a canonical representation.
    For example, removing the sole binding collapses its path to the empty trie.
    Builds on: TrieSig and Argent time derivation. *)

From Stdlib Require Import NArith PArith List Bool Sorting.Sorted.
From Argent Require Import Time Std.
From Galois.Base Require Import TrieSig.

Inductive trie_ne (A : Type) : Type :=
  | N001 (r : trie_ne A)
  | N010 (v : A)
  | N011 (v : A) (r : trie_ne A)
  | N100 (l : trie_ne A)
  | N101 (l r : trie_ne A)
  | N110 (l : trie_ne A) (v : A)
  | N111 (l : trie_ne A) (v : A) (r : trie_ne A).

Arguments N001 {A}.
Arguments N010 {A}.
Arguments N011 {A}.
Arguments N100 {A}.
Arguments N101 {A}.
Arguments N110 {A}.
Arguments N111 {A}.

Inductive ptrie (A : Type) : Type :=
  | Empty
  | Nodes (n : trie_ne A).

Arguments Empty {A}.
Arguments Nodes {A}.

Definition trie_left {A} (tr : ptrie A) : ptrie A :=
  match tr with
  | Nodes (N100 l) | Nodes (N101 l _) | Nodes (N110 l _) | Nodes (N111 l _ _) => Nodes l
  | _ => Empty
  end.

TimeFun trie_left.

Definition trie_value {A} (tr : ptrie A) : option A :=
  match tr with
  | Nodes (N010 v) | Nodes (N011 v _) | Nodes (N110 _ v) | Nodes (N111 _ v _) => Some v
  | _ => None
  end.

TimeFun trie_value.

Definition trie_right {A} (tr : ptrie A) : ptrie A :=
  match tr with
  | Nodes (N001 r) | Nodes (N011 _ r) | Nodes (N101 _ r) | Nodes (N111 _ _ r) => Nodes r
  | _ => Empty
  end.

TimeFun trie_right.

(** Lookup visits all key bits, including those below an absent subtree. *)
Fixpoint trie_get {A} (p : positive) (tr : ptrie A) : option A :=
  match p with
  | xH => trie_value tr
  | xO q => trie_get q (trie_left tr)
  | xI q => trie_get q (trie_right tr)
  end.

TimeFun trie_get.

Module PTrieCode <: TRIE_OPS.
  Definition t := ptrie.
  Definition ne := trie_ne.
  Definition empty {A} : t A := Empty.

  Definition is_empty {A} (tr : t A) : bool :=
    match tr with
    | Empty => true
    | Nodes _ => false
    end.

  Definition left := @trie_left.
  Definition value := @trie_value.
  Definition right := @trie_right.
  Definition get := @trie_get.
  Arguments left {A} tr.
  Arguments value {A} tr.
  Arguments right {A} tr.
  Arguments get {A} p tr.

  TimeFun left.
  TimeFun value.
  TimeFun right.
  TimeFun get.

  Definition node {A} (l : t A) (o : option A) (r : t A) : t A :=
    match l, o, r with
    | Empty, None, Empty => Empty
    | Empty, None, Nodes r => Nodes (N001 r)
    | Empty, Some v, Empty => Nodes (N010 v)
    | Empty, Some v, Nodes r => Nodes (N011 v r)
    | Nodes l, None, Empty => Nodes (N100 l)
    | Nodes l, None, Nodes r => Nodes (N101 l r)
    | Nodes l, Some v, Empty => Nodes (N110 l v)
    | Nodes l, Some v, Nodes r => Nodes (N111 l v r)
    end.

  TimeFun node.

  Fixpoint replace {A} (p : positive) (o : option A) (tr : t A) : t A :=
    match p with
    | xH => node (left tr) o (right tr)
    | xO q => node (replace q o (left tr)) (value tr) (right tr)
    | xI q => node (left tr) (value tr) (replace q o (right tr))
    end.

  TimeFun replace.

  Definition set {A} p (v : A) tr := replace p (Some v) tr.
  TimeFun set.
  Definition remove {A} p (tr : t A) := replace p None tr.
  TimeFun remove.

  Definition filter_value {A B} (f : A -> option B) (o : option A) : option B :=
    match o with
    | None => None
    | Some v => f v
    end.

  Fixpoint filter_ne {A B} (f : A -> option B) (n : ne A) : t B :=
    match n with
    | N001 r => node Empty None (filter_ne f r)
    | N010 v => node Empty (filter_value f (Some v)) Empty
    | N011 v r => node Empty (filter_value f (Some v)) (filter_ne f r)
    | N100 l => node (filter_ne f l) None Empty
    | N101 l r => node (filter_ne f l) None (filter_ne f r)
    | N110 l v => node (filter_ne f l) (filter_value f (Some v)) Empty
    | N111 l v r => node (filter_ne f l) (filter_value f (Some v)) (filter_ne f r)
    end.

  Definition filter_map {A B} (f : A -> option B) (tr : t A) : t B :=
    match tr with
    | Empty => Empty
    | Nodes n => filter_ne f n
    end.

  Definition map {A B} (f : A -> B) (tr : t A) :=
    filter_map (fun v => Some (f v)) tr.

  Definition merge_value {A B C} (f : option A -> option B -> option C) a b := f a b.

  Fixpoint merge_ne {A B C} (f : option A -> option B -> option C)
      (only_l : t A -> t C) (only_r : t B -> t C) (n : ne A) (tr : t B) : t C :=
    match tr with
    | Empty => only_l (Nodes n)
    | Nodes _ =>
      match n with
      | N001 r =>
        node (only_r (left tr)) (merge_value f None (value tr))
          (merge_ne f only_l only_r r (right tr))
      | N010 v =>
        node (only_r (left tr)) (merge_value f (Some v) (value tr)) (only_r (right tr))
      | N011 v r =>
        node (only_r (left tr)) (merge_value f (Some v) (value tr))
          (merge_ne f only_l only_r r (right tr))
      | N100 l =>
        node (merge_ne f only_l only_r l (left tr))
          (merge_value f None (value tr)) (only_r (right tr))
      | N101 l r =>
        node (merge_ne f only_l only_r l (left tr))
          (merge_value f None (value tr)) (merge_ne f only_l only_r r (right tr))
      | N110 l v =>
        node (merge_ne f only_l only_r l (left tr))
          (merge_value f (Some v) (value tr)) (only_r (right tr))
      | N111 l v r =>
        node (merge_ne f only_l only_r l (left tr))
          (merge_value f (Some v) (value tr)) (merge_ne f only_l only_r r (right tr))
      end
    end.

  Definition merge_with {A B C} (f : option A -> option B -> option C)
      (only_l : t A -> t C) (only_r : t B -> t C) (tr : t A) (u : t B) :=
    match tr with
    | Empty => only_r u
    | Nodes n => merge_ne f only_l only_r n u
    end.

  Definition merge {A B C} (f : option A -> option B -> option C) (tr : t A) (u : t B) :=
    merge_with f (filter_map (fun a => f (Some a) None))
      (filter_map (fun b => f None (Some b))) tr u.

  Definition test_value {A B} (rel : A -> option B -> bool) (a : option A) (b : option B) :=
    match a with
    | None => true
    | Some v => rel v b
    end.

  Fixpoint forall2_ne {A B} (rel : A -> option B -> bool) (n : ne A) (tr : t B) : bool :=
    match n with
    | N001 r => forall2_ne rel r (right tr)
    | N010 v => test_value rel (Some v) (value tr)
    | N011 v r => test_value rel (Some v) (value tr) && forall2_ne rel r (right tr)
    | N100 l => forall2_ne rel l (left tr)
    | N101 l r => forall2_ne rel l (left tr) && forall2_ne rel r (right tr)
    | N110 l v => forall2_ne rel l (left tr) && test_value rel (Some v) (value tr)
    | N111 l v r =>
      forall2_ne rel l (left tr) &&
        (test_value rel (Some v) (value tr) && forall2_ne rel r (right tr))
    end.

  Definition forall2 {A B} (rel : A -> option B -> bool) (tr : t A) (u : t B) :=
    match tr with
    | Empty => true
    | Nodes n => forall2_ne rel n u
    end.

  Definition forall2b {A B} (f : option A -> option B -> bool) (tr : t A) (u : t B) :=
    forall2 (fun a b => f (Some a) b) tr u &&
      forall2 (fun b a => match a with None => f None (Some b) | Some _ => true end) u tr.

  Definition existsb {A} (f : A -> bool) (tr : t A) :=
    negb (forall2 (fun a (_ : option unit) => negb (f a)) tr (@empty unit)).

  Definition emit {A B} (f : B -> positive -> A -> B)
      (path : positive -> positive) (b : B) (v : A) := f b (path xH) v.

  Definition extend (bit : positive -> positive) (path : positive -> positive) p := path (bit p).

  Fixpoint fold_ne {A B} (f : B -> positive -> A -> B)
      (path : positive -> positive) (n : ne A) (b : B) : B :=
    match n with
    | N001 r => fold_ne f (extend xI path) r b
    | N010 v => emit f path b v
    | N011 v r => let b' := emit f path b v in fold_ne f (extend xI path) r b'
    | N100 l => fold_ne f (extend xO path) l b
    | N101 l r =>
      let b' := fold_ne f (extend xO path) l b in fold_ne f (extend xI path) r b'
    | N110 l v => let b' := fold_ne f (extend xO path) l b in emit f path b' v
    | N111 l v r =>
      let b' := fold_ne f (extend xO path) l b in
      let b'' := emit f path b' v in fold_ne f (extend xI path) r b''
    end.

  Definition fold_path {A B} (f : B -> positive -> A -> B)
      (path : positive -> positive) (tr : t A) (b : B) :=
    match tr with
    | Empty => b
    | Nodes n => fold_ne f path n b
    end.

  Definition fold {A B} (f : B -> positive -> A -> B) (tr : t A) (b : B) :=
    fold_path f (fun p => p) tr b.

  Fixpoint fold_values_ne {A B} (f : B -> A -> B) (n : ne A) (b : B) : B :=
    match n with
    | N001 r => fold_values_ne f r b
    | N010 v => f b v
    | N011 v r => fold_values_ne f r (f b v)
    | N100 l => fold_values_ne f l b
    | N101 l r => fold_values_ne f r (fold_values_ne f l b)
    | N110 l v => f (fold_values_ne f l b) v
    | N111 l v r => fold_values_ne f r (f (fold_values_ne f l b) v)
    end.

  Definition fold_values {A B} (f : B -> A -> B) (tr : t A) (b : B) : B :=
    match tr with
    | Empty => b
    | Nodes n => fold_values_ne f n b
    end.

  Definition elements {A} (tr : t A) : list (positive * A) :=
    List.rev_append (fold (fun acc p v => (p, v) :: acc) tr nil) nil.
End PTrieCode.

Module PTrie <: TRIE.
  Include PTrieCode.
  Include TRIE_SPEC.

  Fixpoint nodes_ne {A} (n : trie_ne A) : nat :=
    match n with
    | N001 r => 1 + nodes_ne r
    | N010 _ => 1
    | N011 _ r => 1 + nodes_ne r
    | N100 l => 1 + nodes_ne l
    | N101 l r => 1 + nodes_ne l + nodes_ne r
    | N110 l _ => 1 + nodes_ne l
    | N111 l _ r => 1 + nodes_ne l + nodes_ne r
    end.

  Definition nodes {A} (tr : t A) : nat :=
    match tr with Empty => 0 | Nodes n => nodes_ne n end.


  Lemma get_empty : forall A p, get p (@empty A) = None.
  Proof.
    intros A p; induction p; cbn [get trie_get trie_left trie_right trie_value empty];
      assumption || reflexivity.
  Qed.
  Lemma left_node {A} (l r : t A) o : left (node l o r) = l.
  Proof. destruct l, o, r; reflexivity. Qed.
  Lemma value_node {A} (l r : t A) o : value (node l o r) = o.
  Proof. destruct l, o, r; reflexivity. Qed.
  Lemma right_node {A} (l r : t A) o : right (node l o r) = r.
  Proof. destruct l, o, r; reflexivity. Qed.
  Lemma get_node {A} (p : positive) (l r : t A) o :
    get p (node l o r) =
    match p with xH => o | xO q => get q l | xI q => get q r end.
  Proof. destruct p; cbn [get trie_get]; rewrite ?left_node, ?right_node, ?value_node; reflexivity. Qed.
  Lemma get_replace_same {A} (tr : t A) p o : get p (replace p o tr) = o.
  Proof. revert tr; induction p; intro tr; cbn [replace]; rewrite get_node; auto. Qed.
  Lemma get_replace_other {A} (tr : t A) p q o :
    p <> q -> get q (replace p o tr) = get q tr.
  Proof.
    revert tr q; induction p; intros tr q Hneq; destruct q;
      cbn [replace get trie_get]; rewrite ?left_node, ?right_node, ?value_node;
      try reflexivity; try congruence; apply IHp; congruence.
  Qed.
  Lemma get_set_same : forall A p (a : A) m, get p (set p a m) = Some a.
  Proof. intros; apply get_replace_same. Qed.
  Lemma get_set_other : forall A p q (a : A) m,
    p <> q -> get p (set q a m) = get p m.
  Proof. intros; apply get_replace_other; congruence. Qed.
  Lemma get_remove_same : forall A p (m : t A), get p (remove p m) = None.
  Proof. intros; apply get_replace_same. Qed.
  Lemma get_remove_other : forall A p q (m : t A),
    p <> q -> get p (remove q m) = get p m.
  Proof. intros; apply get_replace_other; congruence. Qed.
  Lemma get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
    f None None = None -> get p (merge f m1 m2) = f (get p m1) (get p m2).
  Proof. Admitted. (* CONVERT: get_combine: The variable get_merge_with was not found in the current environment. *)
  Lemma forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
    f None None = true ->
    (forall2b f m1 m2 = true <-> forall p, f (get p m1) (get p m2) = true).
  Proof. Admitted.
  Lemma existsb_spec : forall A (f : A -> bool) m,
    existsb f m = true <-> exists p a, get p m = Some a /\ f a = true.
  Proof. Admitted.
  Lemma get_map : forall A B (f : A -> B) m p,
    get p (map f m) = option_map f (get p m).
  Proof. Admitted. (* CONVERT: get_map: The variable get_filter was not found in the current environment. *)
  Lemma elements_spec : forall A (m : t A) p a,
    In (p, a) (elements m) <-> get p m = Some a.
  Proof. Admitted. (* CONVERT: elements_spec: The variable node_ind was not found in the current environment. *)
  Lemma elements_sorted : forall A (m : t A),
    StronglySorted (fun x y => trie_lt (fst x) (fst y)) (elements m).
  Proof. Admitted. (* CONVERT: elements_sorted: The variable node_ind was not found in the current environment. *)
  Lemma elements_nodup : forall A (m : t A), NoDup (List.map fst (elements m)).
  Proof.
    intros A m. pose proof (elements_sorted A m) as Hsort.
    induction Hsort as [|[p a] xs Hsort IH Hforall]; cbn [List.map fst].
    - constructor.
    - constructor; [|exact IH]. intro Hin.
      apply in_map_iff in Hin as [[q b] [Heq Hin]]. cbn [fst] in Heq. subst q.
      rewrite Forall_forall in Hforall. specialize (Hforall (p, b) Hin).
      assert (Hirr : forall p, ~ trie_lt p p).
      { intro q. induction q; cbn [trie_lt]; assumption || tauto. }
      exact (Hirr p Hforall).
  Qed.
  Lemma fold_spec : forall A B (f : B -> positive -> A -> B) m b,
    fold f m b = fold_left (fun acc kv => f acc (fst kv) (snd kv)) (elements m) b.
  Proof. Admitted. (* CONVERT: fold_elements: The variable elements_entries was not found in the current environment. *)
  Lemma ext : forall A (m n : t A), (forall p, get p m = get p n) -> m = n.
  Proof. Admitted. (* CONVERT: extensionality: The variable node_ind was not found in the current environment. *)
  Lemma nodes_set : forall A p (a : A) m,
    nodes (set p a m) <= nodes m + Pos.size_nat p.
  Proof. Admitted.
  Lemma nodes_le_weight : forall A (m : t A), nodes m <= weight m.
  Proof. Admitted.
Lemma is_empty_spec : forall A (m : t A), is_empty m = true <-> m = empty.
  Proof. Admitted.
Lemma nodes_remove : forall A p (m : t A), nodes (remove p m) <= nodes m.
  Proof. Admitted.
Lemma nodes_map : forall A B (f : A -> B) m, nodes (map f m) <= nodes m.
  Proof. Admitted.
Lemma nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
  nodes (merge f m1 m2) <= nodes m1 + nodes m2.
  Proof. Admitted.

End PTrie.

Module PTrieT <: TRIE_ALL.
  Include PTrie.

  TimeFun is_empty.
  TimeFun filter_value.
  TimeFun filter_ne.
  TimeFun filter_map.
  TimeFun merge_value.
  TimeFun merge_ne.
  TimeFun merge_with.
  TimeFun merge.
  TimeFun test_value.
  TimeFun forall2_ne.
  TimeFun forall2.
  TimeFun forall2b.
  TimeFun existsb.
  TimeFun emit.
  TimeFun extend.
  TimeFun fold_ne.
  TimeFun fold_path.
  TimeFun fold.
  TimeFun fold_values_ne.
  TimeFun fold_values.
  TimeFun map.
  TimeFun elements.

  Definition c_trie : N := 1. (* STUB *)

  Lemma T_is_empty_le : forall A (m : t A), (T_is_empty m <= c_trie)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_get_le : forall A p (m : t A),
    (T_get p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_set_le : forall A p (a : A) m,
    (T_set p a m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_remove_le : forall A p (m : t A),
    (T_remove p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_merge f T_f m1 m2 <= c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_forall2b f T_f m1 m2 <= c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_existsb_le : forall A (f : A -> bool) T_f m k,
    ((forall a, T_f a <= k) ->
    T_existsb f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_map_le : forall A B (f : A -> B) T_f m k,
    ((forall a, T_f a <= k) ->
    T_map f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fold_le : forall A B (f : B -> positive -> A -> B) T_f m b k,
    ((forall acc p a, T_f acc p a <= k) ->
    T_fold f T_f m b <= c_trie * ((k + 1) * N.of_nat (nodes m + 1) +
      N.of_nat (weight m)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_elements_le : forall A (m : t A),
    (T_elements m <= c_trie * N.of_nat (weight m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma get_tight : forall A p (m : t A), (N.of_nat (Pos.size_nat p) <= T_get p m)%N.
  Proof. Admitted. (* STUB *)

  Definition k_node : N := 1. (* STUB *)
  Definition k_replace : N := 1. (* STUB *)
  Definition k_filter : N := 1. (* STUB *)
  Definition k_merge : N := 1. (* STUB *)
  Definition k_check : N := 1. (* STUB *)
  Definition k_fold : N := 1. (* STUB *)
  Definition k_elements : N := 1. (* STUB *)

  Definition bindings {A} (m : t A) : nat := length (elements m).
  Definition key_mass {A} (m : t A) : nat :=
    fold_right Nat.add 0
      (List.map (fun kv => Pos.size_nat (fst kv)) (elements m)).
  Definition fold_work {A B} (f : B -> positive -> A -> B)
      (T_f : B -> positive -> A -> N) (m : t A) (b : B) : N :=
    snd (fold_left (fun bw kv =>
      (f (fst bw) (fst kv) (snd kv),
        (snd bw + T_f (fst bw) (fst kv) (snd kv))%N)) (elements m) (b, 0%N)).

  Lemma F1_node : forall A (m : t A), node (left m) (value m) (right m) = m.
  Proof. Admitted. (* STUB *)
  Lemma F2_nodes_node : forall A (l r : t A) o,
    nodes (node l o r) <= S (nodes l + nodes r).
  Proof. Admitted. (* STUB *)
  Lemma F3_weight : forall A (m : t A), weight m = key_mass m + bindings m.
  Proof. Admitted. (* STUB *)
  Lemma F4_bindings : forall A (m : t A), bindings m <= nodes m.
  Proof. Admitted. (* STUB *)
  Lemma F5_fold_path : forall A B (f : B -> positive -> A -> B) path m b,
    fold_path f path m b =
      fold_left (fun acc kv => f acc (path (fst kv)) (snd kv)) (elements m) b.
  Proof. Admitted. (* STUB *)
  Lemma F6_fold_work : forall A B (f : B -> positive -> A -> B) T_f m b c,
    ((forall acc p a, T_f acc p a <= c) -> fold_work f T_f m b <= c * N.of_nat (bindings m))%N.
  Proof. Admitted. (* STUB *)
  Lemma F7_replace : forall A p q o (m : t A),
    get p (replace q o m) = if Pos.eqb p q then o else get p m.
  Proof. Admitted. (* STUB *)
  Lemma F8_filter : forall A B (f : A -> option B) m p,
    get p (filter_map f m) =
      match get p m with Some a => f a | None => None end.
  Proof. Admitted. (* STUB *)
  Lemma F9_fold_values : forall A B (f : B -> A -> B) m b,
    fold_values f m b =
      fold_left (fun acc kv => f acc (snd kv)) (elements m) b.
  Proof. Admitted. (* STUB *)
  Lemma T1_node : forall A (l r : t A) o,
    (T_left l + T_value l + T_right l + T_node l o r <= k_node)%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_replace : forall A p o (m : t A),
    (T_replace p o m <= k_replace * N.of_nat (Pos.size_nat p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_filter : forall A B (f : A -> option B) T_f m c,
    ((forall a, T_f a <= c) ->
    T_filter_map f T_f m <= k_filter * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Filtering charges each callback at its present binding. *)
  Lemma T3_filter_sum : forall A B (f : A -> option B) T_f m,
    (T_filter_map f T_f m <= k_filter * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun ka => T_f (snd ka)) (elements m))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_merge_with : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u c cl cr,
    ((forall a b, T_f a b <= c) ->
    (forall a, T_fl a <= cl * N.of_nat (nodes a + 1)) ->
    (forall b, T_fr b <= cr * N.of_nat (nodes b + 1)) ->
    T_merge_with f T_f fl T_fl fr T_fr m u <=
      k_merge * (c + cl + cr + 1) * N.of_nat (nodes m + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Merging charges the callbacks at shared and one-sided bindings. *)
  Lemma T4_merge_with_sum : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u cl cr,
    (forall a, T_fl a <= cl * (N.of_nat (nodes a + 1) + fold_right N.add 0
       (List.map (fun ka => T_f (Some (snd ka)) None) (elements a))))%N ->
    (forall b, T_fr b <= cr * (N.of_nat (nodes b + 1) + fold_right N.add 0
       (List.map (fun kb => T_f None (Some (snd kb))) (elements b))))%N ->
    (T_merge_with f T_f fl T_fl fr T_fr m u <= k_merge * (cl + cr + 1) *
      ((T_f None None + 1) * N.of_nat (nodes m + nodes u + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m) (get p u))
         (List.map fst (elements m) ++ List.map fst (elements u)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_forall2 : forall A B (f : A -> option B -> bool) T_f m u c,
    ((forall a b, T_f a b <= c) ->
    T_forall2 f T_f m u <= k_check * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Directional checking charges each visited binding against its lookup result. *)
  Lemma T5_forall2_sum : forall A B (f : A -> option B -> bool) T_f m u,
    (T_forall2 f T_f m u <= k_check * (N.of_nat (nodes m + 1) +
      fold_right N.add 0
        (List.map (fun ka => T_f (snd ka) (get (fst ka) u)) (elements m))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T6_fold_path : forall A B (f : B -> positive -> A -> B) T_f path T_path m b c d,
    ((forall acc p a, T_f acc p a <= c) -> (forall p, T_path p <= d) ->
    T_fold_path f T_f path T_path m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + (c + d + 1) * N.of_nat (bindings m) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T7_fold_work : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + fold_work f T_f m b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T8_elements : forall A (m : t A),
    (T_elements m <= k_elements * N.of_nat (nodes m + key_mass m + bindings m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T9_fold_values : forall A B (f : B -> A -> B) T_f m b c,
    ((forall acc a, T_f acc a <= c) ->
    T_fold_values f T_f m b <= k_fold * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forall2b_sum_le : forall A B (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_trie * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match get p m with Some a => T_f a | None => 0 end) (List.map fst (elements m)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fold_sum_le : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_trie * (N.of_nat (nodes m + 1) + N.of_nat (weight m) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof. Admitted. (* STUB *)

  (** Value folding charges callbacks in enumeration order without constructing keys. *)
  Lemma T_fold_values_sum_le : forall A B (f : B -> A -> B) T_f m b,
    (T_fold_values f T_f m b <= c_trie * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (snd ka), snd bw + T_f (fst bw) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof. Admitted. (* STUB *)
End PTrieT.
