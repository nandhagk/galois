(** * Canonical binary trie code

    Seven nonempty node shapes give finite positive-key maps a canonical representation.
    For example, removing the sole binding collapses its path to the empty trie.

    Main results
    - [forall2b_spec] Relational checking covers every key when absence passes.
    - [existsb_spec] Existential checking finds a stored value satisfying the predicate.
    - [elements_spec] Enumeration contains precisely the bindings.
    - [fold_spec] Folding follows enumeration order.
    - [is_empty_spec] A trie is reported empty exactly when it is the empty trie.
    - [get_complexity] Lookup is linear in the key bit length, O(|p|) for a key p.
    - [get_worst_complexity] Some stored key of every length is read to its end, so the
      worst-case lookup time is Θ(|p|).
    - [set_complexity] Setting reads and rebuilds the whole key path, so its time is Θ(|p|).
    - [remove_complexity] Removal is linear in the key bit length, O(|p|).
    - [merge_complexity] Merging is linear in both skeletons for bounded callbacks,
      O((k + 1) (nodes m1 + nodes m2 + 1)) for callbacks that cost at most k.
    - [forall2b_complexity] Relational checking is linear in both skeletons for bounded
      callbacks, O((k + 1) (nodes m1 + nodes m2 + 1)).
    - [fold_complexity] Folding is linear in the skeleton and the key mass for bounded
      callbacks, O((k + 1) (nodes m + 1) + weight m).
    - [elements_complexity] Enumeration is linear in the binding weight, O(weight m).

    Builds on: TrieSig and Argent time derivation. *)

From Stdlib Require Import NArith PArith Arith List Bool Lia Sorting.Sorted.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import TrieSig.
Import ComplexityNotations.

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

(** Lookup reads one node for each key digit and stops at the first absent child.
    The recursion is structural on the key, so a lookup with an unknown key stays folded under
    conversion, whatever the trie. *)
Fixpoint trie_get {A} (p : positive) (tr : ptrie A) : option A :=
  match tr with
  | Empty => None
  | Nodes n =>
    match p, n with
    | xH, (N010 v | N011 v _ | N110 _ v | N111 _ v _) => Some v
    | xO q, (N100 l | N101 l _ | N110 l _ | N111 l _ _) => trie_get q (Nodes l)
    | xI q, (N001 r | N011 _ r | N101 _ r | N111 _ _ r) => trie_get q (Nodes r)
    | _, _ => None
    end
  end.

TimeFun trie_get.

(** Lookup in the empty trie fails. *)
Lemma trie_get_empty {A} (p : positive) : trie_get p (@Empty A) = None.
Proof.
  destruct p; reflexivity.
Qed.

(** Lookup of the root key reads the node value. *)
Lemma trie_get_xH {A} (tr : ptrie A) : trie_get xH tr = trie_value tr.
Proof.
  destruct tr as [|n]; [|destruct n]; reflexivity.
Qed.

(** Lookup below a left edge continues in the left child. *)
Lemma trie_get_xO {A} (q : positive) (tr : ptrie A) :
  trie_get (xO q) tr = trie_get q (trie_left tr).
Proof.
  destruct tr as [|n]; [|destruct n]; destruct q; reflexivity.
Qed.

(** Lookup below a right edge continues in the right child. *)
Lemma trie_get_xI {A} (q : positive) (tr : ptrie A) :
  trie_get (xI q) tr = trie_get q (trie_right tr).
Proof.
  destruct tr as [|n]; [|destruct n]; destruct q; reflexivity.
Qed.

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

  (** Two absent value slots do not call the relation. *)
  Definition test_values {A B} (f : option A -> option B -> bool) a b : bool :=
    match a, b with
    | None, None => true
    | _, _ => f a b
    end.

  (** Shared nodes are checked together, stopping before a later segment after failure. *)
  Fixpoint forall2b_ne {A B} (f : option A -> option B -> bool)
      (n : ne A) (u : t B) : bool :=
    match u with
    | Empty => forall2_ne (fun a _ => f (Some a) None) n (@empty B)
    | Nodes _ =>
      match n with
      | N001 r =>
        if forall2 (fun b _ => f None (Some b)) (left u) (@empty A) then
          if test_values f None (value u) then forall2b_ne f r (right u) else false
        else false
      | N010 v =>
        if forall2 (fun b _ => f None (Some b)) (left u) (@empty A) then
          if f (Some v) (value u) then
            forall2 (fun b _ => f None (Some b)) (right u) (@empty A)
          else false
        else false
      | N011 v r =>
        if forall2 (fun b _ => f None (Some b)) (left u) (@empty A) then
          if f (Some v) (value u) then forall2b_ne f r (right u) else false
        else false
      | N100 l =>
        if forall2b_ne f l (left u) then
          if test_values f None (value u) then
            forall2 (fun b _ => f None (Some b)) (right u) (@empty A)
          else false
        else false
      | N101 l r =>
        if forall2b_ne f l (left u) then
          if test_values f None (value u) then forall2b_ne f r (right u) else false
        else false
      | N110 l v =>
        if forall2b_ne f l (left u) then
          if f (Some v) (value u) then
            forall2 (fun b _ => f None (Some b)) (right u) (@empty A)
          else false
        else false
      | N111 l v r =>
        if forall2b_ne f l (left u) then
          if f (Some v) (value u) then forall2b_ne f r (right u) else false
        else false
      end
    end.

  (** A missing left trie delegates to the existing one-sided traversal. *)
  Definition forall2b {A B} (f : option A -> option B -> bool)
      (tr : t A) (u : t B) : bool :=
    match tr with
    | Empty => forall2 (fun b _ => f None (Some b)) u (@empty A)
    | Nodes n => forall2b_ne f n u
    end.

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

  (** Rebuilding preserves the unique canonical representation. *)
  Lemma node_eta {A} (tr : t A) : node (left tr) (value tr) (right tr) = tr.
  Proof.
    destruct tr as [|n]; [reflexivity|destruct n; reflexivity].
  Qed.

  (** Semantic induction exposes the two subtries and the optional root binding. *)
  Lemma node_ind {A} (P : t A -> Prop) :
    P Empty -> (forall l o r, P l -> P r -> P (node l o r)) -> forall tr, P tr.
  Proof.
    intros Hempty Hnode [|n]; [exact Hempty|].
    induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr].
    - exact (Hnode Empty None (Nodes r) Hempty IHr).
    - exact (Hnode Empty (Some v) Empty Hempty Hempty).
    - exact (Hnode Empty (Some v) (Nodes r) Hempty IHr).
    - exact (Hnode (Nodes l) None Empty IHl Hempty).
    - exact (Hnode (Nodes l) None (Nodes r) IHl IHr).
    - exact (Hnode (Nodes l) (Some v) Empty IHl Hempty).
    - exact (Hnode (Nodes l) (Some v) (Nodes r) IHl IHr).
  Qed.

  (** This specification list records the executable traversal's left-root-right order. *)
  Fixpoint entries_ne {A} (n : ne A) : list (positive * A) :=
    match n with
    | N001 r => List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
    | N010 v => (xH, v) :: nil
    | N011 v r => (xH, v) :: List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
    | N100 l => List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l)
    | N101 l r =>
      List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++
        List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
    | N110 l v => List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++ (xH, v) :: nil
    | N111 l v r =>
      List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++
        (xH, v) :: List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
    end.

  Definition entries {A} (tr : t A) : list (positive * A) :=
    match tr with Empty => nil | Nodes n => entries_ne n end.

  Local Lemma fold_left_map_values {X Y B} (f : B -> Y -> B) (g : X -> Y) xs b :
    fold_left f (List.map g xs) b = fold_left (fun acc x => f acc (g x)) xs b.
  Proof.
    revert b. induction xs as [|x xs IH]; intro b; cbn [List.map fold_left]; auto.
  Qed.

  Lemma fold_path_entries {A B} (f : B -> positive -> A -> B) (tr : t A) :
    forall path b, fold_path f path tr b =
      fold_left (fun acc pv => f acc (path (fst pv)) (snd pv)) (entries tr) b.
  Proof.
    destruct tr as [|n]; [reflexivity|].
    induction n; intros path b; cbn [fold_path fold_ne entries entries_ne emit];
      rewrite ?fold_left_app; cbn [fold_left]; rewrite ?fold_left_map_values;
      cbn [fst snd]; cbn [fold_path entries] in *;
      rewrite ?IHn, ?IHn1, ?IHn2; reflexivity.
  Qed.

  Lemma fold_values_entries {A B} (f : B -> A -> B) (tr : t A) :
    forall b, fold_values f tr b =
      fold_left (fun acc pv => f acc (snd pv)) (entries tr) b.
  Proof.
    destruct tr as [|n]; [reflexivity|].
    induction n; intro b; cbn [fold_values fold_values_ne entries entries_ne];
      rewrite ?fold_left_app; cbn [fold_left]; rewrite ?fold_left_map_values;
      cbn [fst snd]; cbn [fold_values entries] in *;
      rewrite ?IHn, ?IHn1, ?IHn2; reflexivity.
  Qed.

  Local Lemma fold_left_pairs {A} (xs acc : list (positive * A)) :
    fold_left (fun acc pv => (fst pv, snd pv) :: acc) xs acc = List.rev xs ++ acc.
  Proof.
    revert acc. induction xs as [|[p a] xs IH]; intro acc.
    - reflexivity.
    - cbn [fold_left rev fst snd]. rewrite IH, <- app_assoc. reflexivity.
  Qed.

  Lemma elements_entries {A} (tr : t A) : elements tr = entries tr.
  Proof.
    unfold elements, fold. rewrite rev_append_rev, app_nil_r, fold_path_entries.
    change (List.rev (fold_left (fun acc pv => (fst pv, snd pv) :: acc)
      (entries tr) nil) = entries tr).
    rewrite fold_left_pairs, app_nil_r, rev_involutive. reflexivity.
  Qed.

  Lemma elements_node {A} (l r : t A) o :
    elements (node l o r) =
      List.map (fun pv => (xO (fst pv), snd pv)) (elements l) ++
      (match o with Some v => (xH, v) :: nil | None => nil end) ++
      List.map (fun pv => (xI (fst pv), snd pv)) (elements r).
  Proof.
    rewrite !elements_entries. destruct l, o, r;
      cbn [node entries entries_ne]; rewrite ?app_nil_r; reflexivity.
  Qed.

  Lemma fold_path_elements {A B} (f : B -> positive -> A -> B) path m b :
    fold_path f path m b =
      fold_left (fun acc kv => f acc (path (fst kv)) (snd kv)) (elements m) b.
  Proof.
    rewrite elements_entries. apply fold_path_entries.
  Qed.

  Lemma fold_values_elements {A B} (f : B -> A -> B) m b :
    fold_values f m b = fold_left (fun acc kv => f acc (snd kv)) (elements m) b.
  Proof.
    rewrite elements_entries. apply fold_values_entries.
  Qed.

  Lemma elements_length_nodes {A} (m : t A) : length (elements m) <= nodes m.
  Proof.
    rewrite elements_entries. destruct m as [|n]; [reflexivity|].
    induction n; cbn [entries entries_ne nodes nodes_ne];
      rewrite ?length_app, ?length_map; cbn [length];
      rewrite ?length_map; cbn [entries nodes] in *; lia.
  Qed.

  Lemma nodes_node_le_aux {A} (l r : t A) o : nodes (node l o r) <= S (nodes l + nodes r).
  Proof.
    destruct l, o, r; cbn [node nodes nodes_ne]; lia.
  Qed.

  Lemma nodes_children_le {A} (m : t A) : nodes (left m) + nodes (right m) <= nodes m.
  Proof.
    destruct m as [|n]; [reflexivity|destruct n;
      cbn [left right trie_left trie_right nodes nodes_ne]; lia].
  Qed.

  Lemma get_empty : forall A p, get p (@empty A) = None.
  Proof.
    intros A p. destruct p; reflexivity.
  Qed.
  Lemma get_equation {A} p (tr : t A) :
    get p tr =
    match p with xH => value tr | xO q => get q (left tr) | xI q => get q (right tr) end.
  Proof.
    destruct p as [q|q|];
      [exact (trie_get_xI q tr)|exact (trie_get_xO q tr)|exact (trie_get_xH tr)].
  Qed.
  (** Lookup of the root key reads the node value. *)
  Lemma get_xH {A} (tr : t A) : get xH tr = value tr.
  Proof.
    exact (get_equation xH tr).
  Qed.
  (** Lookup below a left edge continues in the left child. *)
  Lemma get_xO {A} q (tr : t A) : get (xO q) tr = get q (left tr).
  Proof.
    exact (get_equation (xO q) tr).
  Qed.
  (** Lookup below a right edge continues in the right child. *)
  Lemma get_xI {A} q (tr : t A) : get (xI q) tr = get q (right tr).
  Proof.
    exact (get_equation (xI q) tr).
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
  Proof.
    rewrite get_equation, left_node, value_node, right_node. reflexivity.
  Qed.
  Lemma get_replace_same {A} (tr : t A) p o : get p (replace p o tr) = o.
  Proof. revert tr; induction p; intro tr; cbn [replace]; rewrite get_node; auto. Qed.
  Lemma get_replace_other {A} (tr : t A) p q o :
    p <> q -> get q (replace p o tr) = get q tr.
  Proof.
    revert tr q; induction p; intros tr q Hneq; destruct q;
      cbn [replace]; rewrite get_node, (get_equation _ tr); cbv iota;
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

  Lemma filter_node {A B} (f : A -> option B) (l r : t A) o :
    filter_map f (node l o r) =
      node (filter_map f l) (match o with Some v => f v | None => None end) (filter_map f r).
  Proof.
    destruct l, o, r; reflexivity.
  Qed.

  Lemma get_filter {A B} (f : A -> option B) (tr : t A) p :
    get p (filter_map f tr) = match get p tr with Some a => f a | None => None end.
  Proof.
    revert p. induction tr as [|l o r IHl IHr] using node_ind; intro p.
    - rewrite !get_empty. reflexivity.
    - rewrite filter_node, !get_node. destruct p; auto.
  Qed.

  Lemma get_merge_with {A B C} (f : option A -> option B -> option C) only_l only_r :
    (forall p tr, get p (only_l tr) = f (get p tr) None) ->
    (forall p tr, get p (only_r tr) = f None (get p tr)) ->
    forall p tr u, get p (merge_with f only_l only_r tr u) = f (get p tr) (get p u).
  Proof.
    intros Hl Hr p [|n] u.
    - cbn [merge_with]. rewrite get_empty. apply Hr.
    - revert p u.
      induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
        intros p [|other].
      all: try (cbn [merge_with merge_ne]; rewrite get_empty; apply Hl).
      all: try (cbn [merge_with] in IHl); try (cbn [merge_with] in IHr).
      all: destruct p; cbn [merge_with merge_ne merge_value]; rewrite get_node;
        match goal with
        | |- _ = ?callback (get ?p ?tr) _ => rewrite (get_equation p tr)
        end;
        rewrite (get_equation _ (Nodes other));
        cbn [left right value trie_left trie_right trie_value];
        rewrite ?IHl, ?IHr, ?Hr, ?get_empty; reflexivity.
  Qed.

  Lemma get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
    f None None = None -> get p (merge f m1 m2) = f (get p m1) (get p m2).
  Proof.
    intros A B C f m1 m2 p Hnone. unfold merge. apply get_merge_with;
      intros q tr; rewrite get_filter; destruct (get q tr); auto.
  Qed.

  Lemma forall2_node {A B} (rel : A -> option B -> bool) (l r : t A) o (u : t B) :
    forall2 rel (node l o r) u =
      (forall2 rel l (left u) && (test_value rel o (value u) &&
        forall2 rel r (right u)))%bool.
  Proof.
    destruct l, o, r; cbn [node forall2 forall2_ne test_value];
      rewrite ?andb_true_r; reflexivity.
  Qed.

  Lemma forall2_spec {A B} (rel : A -> option B -> bool) (tr : t A) (u : t B) :
    forall2 rel tr u = true <->
      forall p a, get p tr = Some a -> rel a (get p u) = true.
  Proof.
    revert u. induction tr as [|l o r IHl IHr] using node_ind; intro u.
    - split.
      + intros _ p a Hget. rewrite get_empty in Hget. discriminate.
      + reflexivity.
    - rewrite forall2_node, !andb_true_iff, IHl, IHr. split.
      + intros [Hl [Ho Hr]] p a Hget. rewrite get_node in Hget.
        destruct p; rewrite get_equation; [apply Hr|apply Hl|]; try exact Hget.
        subst o. exact Ho.
      + intro Htest. split.
        * intros p a Hget. rewrite <- get_xO. apply (Htest (xO p) a).
          rewrite get_node. exact Hget.
        * split.
          -- destruct o as [a|]; [apply (Htest xH a); apply get_node|reflexivity].
          -- intros p a Hget. rewrite <- get_xI. apply (Htest (xI p) a).
             rewrite get_node. exact Hget.
  Qed.

  (** An absent right trie leaves only the existing left-side check. *)
  Local Lemma forall2b_ne_empty {A B} (f : option A -> option B -> bool) (n : ne A) :
    forall2b_ne f n (@empty B) =
      forall2_ne (fun a _ => f (Some a) None) n (@empty B).
  Proof.
    destruct n; reflexivity.
  Qed.

  (** The paired traversal checks the two children and the root once each. *)
  Local Lemma forall2b_node {A B} (f : option A -> option B -> bool)
      (l r : t A) o (u : t B) :
    forall2b f (node l o r) u =
      forall2b f l (left u) &&
        (test_values f o (value u) && forall2b f r (right u)).
  Proof.
    destruct l as [|ln], o as [v|], r as [|rn], u as [|un];
      try destruct un;
      cbn [node forall2b forall2b_ne forall2 forall2_ne test_values test_value
        left value right trie_left trie_value trie_right empty];
      rewrite ?forall2b_ne_empty, ?andb_true_r.
    all: repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      end; reflexivity.
  Qed.

  (** The paired traversal checks the relation at every key of either trie. *)
  Lemma forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
    f None None = true ->
    (forall2b f m1 m2 = true <-> forall p, f (get p m1) (get p m2) = true).
  Proof.
    intros A B f m1 m2 Hnone. revert m2.
    induction m1 as [|l o r IHl IHr] using node_ind; intro m2.
    - cbn [forall2b]. rewrite forall2_spec. split.
      + intros Htest p. rewrite get_empty.
        destruct (get p m2) as [b|] eqn:Hlookup.
        * exact (Htest p b Hlookup).
        * exact Hnone.
      + intros Htest p b Hlookup. specialize (Htest p).
        rewrite get_empty, Hlookup in Htest. exact Htest.
    - rewrite forall2b_node, !andb_true_iff, IHl, IHr.
      assert (Hvalue : test_values f o (value m2) = f o (value m2)).
      { destruct o, (value m2); cbn [test_values]; try reflexivity.
        symmetry. exact Hnone. }
      rewrite Hvalue. split.
      + intros [Hl [Hroot Hr]] [p|p|].
        * rewrite get_node, get_xI. exact (Hr p).
        * rewrite get_node, get_xO. exact (Hl p).
        * rewrite get_node, get_xH. exact Hroot.
      + intro Htest. split.
        * intro p. specialize (Htest (xO p)).
          rewrite get_node, get_xO in Htest. exact Htest.
        * split.
          -- specialize (Htest xH). rewrite get_node, get_xH in Htest. exact Htest.
          -- intro p. specialize (Htest (xI p)).
             rewrite get_node, get_xI in Htest. exact Htest.
  Qed.

  Lemma get_map : forall A B (f : A -> B) m p,
    get p (map f m) = option_map f (get p m).
  Proof.
    intros A B f m p. unfold map. rewrite get_filter. destruct (get p m); reflexivity.
  Qed.
  Lemma elements_spec : forall A (m : t A) p a,
    In (p, a) (elements m) <-> get p m = Some a.
  Proof.
    intros A m. induction m as [|l o r IHl IHr] using node_ind; intros p a.
    - rewrite get_empty, elements_entries. cbn [entries].
      split; [contradiction|discriminate].
    - rewrite elements_node, !in_app_iff, get_node. destruct p.
      + split.
        * intros [Hl|[Ho|Hr]].
          -- apply in_map_iff in Hl as [[q b] [Heq _]]. discriminate Heq.
          -- destruct o; cbn in Ho; intuition discriminate.
          -- apply in_map_iff in Hr as [[q b] [Heq Hin]].
             injection Heq as -> ->. now apply IHr.
        * intro Hget. right. right. apply in_map_iff. exists (p, a).
          split; [reflexivity|now apply IHr].
      + split.
        * intros [Hl|[Ho|Hr]].
          -- apply in_map_iff in Hl as [[q b] [Heq Hin]].
             injection Heq as -> ->. now apply IHl.
          -- destruct o; cbn in Ho; intuition discriminate.
          -- apply in_map_iff in Hr as [[q b] [Heq _]]. discriminate Heq.
        * intro Hget. left. apply in_map_iff. exists (p, a).
          split; [reflexivity|now apply IHl].
      + split.
        * intros [Hl|[Ho|Hr]].
          -- apply in_map_iff in Hl as [[q b] [Heq _]]. discriminate Heq.
          -- destruct o; cbn in Ho; intuition congruence.
          -- apply in_map_iff in Hr as [[q b] [Heq _]]. discriminate Heq.
        * intro Hget. right. left. subst o. now left.
  Qed.

  Lemma forall2_elements {A B} (rel : A -> option B -> bool) m u :
    forall2 rel m u =
      List.forallb (fun kv => rel (snd kv) (get (fst kv) u)) (elements m).
  Proof.
    apply eq_true_iff_eq. rewrite forall2_spec, forallb_forall. split.
    - intros Htest [p a] Hin. apply Htest. now apply elements_spec.
    - intros Htest p a Hget. apply (Htest (p, a)). now apply elements_spec.
  Qed.

  Lemma existsb_spec : forall A (f : A -> bool) m,
    existsb f m = true <-> exists p a, get p m = Some a /\ f a = true.
  Proof.
    intros A f m. unfold existsb. rewrite forall2_elements.
    assert (Hneg : forall xs : list (positive * A),
      negb (List.forallb (fun kv => negb (f (snd kv))) xs) =
        List.existsb (fun kv => f (snd kv)) xs).
    { induction xs as [|[p a] xs IH]; cbn [List.forallb List.existsb snd].
      - reflexivity.
      - rewrite negb_andb, negb_involutive, IH. reflexivity. }
    change (negb (List.forallb (fun kv => negb (f (snd kv))) (elements m)) = true <->
      exists p a, get p m = Some a /\ f a = true).
    rewrite Hneg, existsb_exists. split.
    - intros [[p a] [Hin Htest]]. exists p, a. split; [now apply elements_spec|exact Htest].
    - intros [p [a [Hget Htest]]]. exists (p, a).
      split; [now apply elements_spec|exact Htest].
  Qed.

  Local Lemma strongly_sorted_app {X} (R : X -> X -> Prop) xs ys :
    StronglySorted R xs -> StronglySorted R ys ->
    (forall x y, In x xs -> In y ys -> R x y) -> StronglySorted R (xs ++ ys).
  Proof.
    intros Hxs Hys. induction Hxs as [|x xs Hsort IH Hforall]; intro Hcross.
    - exact Hys.
    - cbn [app]. constructor.
      + apply IH. intros a b Ha Hb. apply Hcross; [right; exact Ha|exact Hb].
      + apply Forall_app. split; [exact Hforall|]. apply Forall_forall.
        intros y Hy. apply Hcross; [left; reflexivity|exact Hy].
  Qed.

  Local Lemma strongly_sorted_map {X Y} (R : X -> X -> Prop) (S : Y -> Y -> Prop)
      (f : X -> Y) xs :
    (forall x y, R x y -> S (f x) (f y)) ->
    StronglySorted R xs -> StronglySorted S (List.map f xs).
  Proof.
    intros Hmap Hsort. induction Hsort as [|x xs Hsort IH Hforall]; cbn [List.map].
    - constructor.
    - constructor; [exact IH|]. apply Forall_forall. intros y Hy.
      apply in_map_iff in Hy. destruct Hy as [z [Heq Hin]]. subst y.
      apply Hmap. rewrite Forall_forall in Hforall. apply Hforall. exact Hin.
  Qed.

  Lemma elements_sorted : forall A (m : t A),
    StronglySorted (fun x y => trie_lt (fst x) (fst y)) (elements m).
  Proof.
    intros A m. induction m as [|l o r IHl IHr] using node_ind.
    - rewrite elements_entries. constructor.
    - rewrite elements_node.
      assert (Hl : StronglySorted (fun a b => trie_lt (fst a) (fst b))
        (List.map (fun pv => (xO (fst pv), snd pv)) (elements l))).
      { eapply strongly_sorted_map; [|exact IHl]. intros [p a] [q b] Hlt. exact Hlt. }
      assert (Hr : StronglySorted (fun a b => trie_lt (fst a) (fst b))
        (List.map (fun pv => (xI (fst pv), snd pv)) (elements r))).
      { eapply strongly_sorted_map; [|exact IHr]. intros [p a] [q b] Hlt. exact Hlt. }
      apply strongly_sorted_app; [exact Hl| |].
      + destruct o as [v|]; cbn [app]; [|exact Hr].
        constructor; [exact Hr|]. apply Forall_forall. intros [q b] Hin.
        apply in_map_iff in Hin as [[p a] [Heq _]]. inversion Heq. exact I.
      + intros [p a] [q b] Hinl Hinr.
        apply in_map_iff in Hinl as [[k c] [Heq _]]. inversion Heq; subst p a.
        apply in_app_iff in Hinr as [Hroot|Hright].
        * destruct o as [v|]; cbn in Hroot; [|contradiction].
          destruct Hroot as [Heqroot|Hfalse]; [|contradiction]. inversion Heqroot. exact I.
        * apply in_map_iff in Hright as [[j d] [Heqright _]].
          inversion Heqright. exact I.
  Qed.
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
  Proof.
    intros A B f m b. apply (fold_path_elements f (fun p => p)).
  Qed.

  Local Lemma all_absent_empty {A} (tr : t A) :
    (forall p, get p tr = None) -> tr = Empty.
  Proof.
    induction tr as [|l o r IHl IHr] using node_ind; intro Hnone.
    - reflexivity.
    - assert (Hl : l = Empty).
      { apply IHl. intro p. specialize (Hnone (xO p)). now rewrite get_node in Hnone. }
      assert (Hr : r = Empty).
      { apply IHr. intro p. specialize (Hnone (xI p)). now rewrite get_node in Hnone. }
      specialize (Hnone xH). rewrite get_node in Hnone.
      rewrite Hl, Hr, Hnone. reflexivity.
  Qed.

  Lemma ext : forall A (m n : t A), (forall p, get p m = get p n) -> m = n.
  Proof.
    intros A m. induction m as [|l o r IHl IHr] using node_ind; intros n Hagree.
    - symmetry. apply all_absent_empty. intro p. rewrite <- Hagree. apply get_empty.
    - assert (Hl : l = left n).
      { apply IHl. intro p. specialize (Hagree (xO p)).
        rewrite get_node, (get_equation (xO p) n) in Hagree. exact Hagree. }
      assert (Hr : r = right n).
      { apply IHr. intro p. specialize (Hagree (xI p)).
        rewrite get_node, (get_equation (xI p) n) in Hagree. exact Hagree. }
      specialize (Hagree xH). rewrite get_node, get_equation in Hagree.
      rewrite Hl, Hr, Hagree. apply node_eta.
  Qed.
  Lemma nodes_set : forall A p (a : A) m,
    nodes (set p a m) <= nodes m + Pos.size_nat p.
  Proof.
    intros A p a. induction p; intro m; cbn [set replace Pos.size_nat].
    all: eapply Nat.le_trans; [apply nodes_node_le_aux|].
    all: pose proof (nodes_children_le m) as Hchildren.
    - specialize (IHp (right m)). unfold set in IHp. lia.
    - specialize (IHp (left m)). unfold set in IHp. lia.
    - lia.
  Qed.

  Local Definition entry_weight {A} (xs : list (positive * A)) : nat :=
    fold_right Nat.add 0 (List.map (fun kv => Pos.size_nat (fst kv) + 1) xs).

  Local Lemma entry_weight_cons {A} p (a : A) xs :
    entry_weight ((p, a) :: xs) = Pos.size_nat p + 1 + entry_weight xs.
  Proof.
    reflexivity.
  Qed.

  Local Lemma entry_weight_app {A} (xs ys : list (positive * A)) :
    entry_weight (xs ++ ys) = entry_weight xs + entry_weight ys.
  Proof.
    unfold entry_weight. induction xs as [|[p a] xs IH];
      cbn [List.map fold_right app fst] in *; lia.
  Qed.

  Local Lemma entry_weight_lift {A} (bit : positive -> positive) xs :
    (forall p, Pos.size_nat (bit p) = S (Pos.size_nat p)) ->
    entry_weight (List.map (fun kv : positive * A => (bit (fst kv), snd kv)) xs) =
      entry_weight xs + length xs.
  Proof.
    intro Hbit. unfold entry_weight. induction xs as [|[p a] xs IH]; [reflexivity|].
    cbn [List.map fold_right length fst snd] in *.
    rewrite Hbit. lia.
  Qed.

  Local Lemma entries_ne_positive {A} (n : ne A) : 0 < length (entries_ne n).
  Proof.
    induction n; cbn [entries_ne length]; rewrite ?length_app, ?length_map;
      cbn [length]; rewrite ?length_map; lia.
  Qed.

  Lemma nodes_le_weight : forall A (m : t A), nodes m <= weight m.
  Proof.
    intros A m. unfold weight. rewrite elements_entries. destruct m as [|n]; [reflexivity|].
    change (nodes_ne n <= entry_weight (entries_ne n)).
    induction n; cbn [nodes_ne entries_ne]; rewrite ?entry_weight_app, ?entry_weight_cons,
      ?(entry_weight_lift xO _ (fun p => eq_refl)),
      ?(entry_weight_lift xI _ (fun p => eq_refl)).
    all: try pose proof (entries_ne_positive n) as Hpositive.
    all: try pose proof (entries_ne_positive n1) as Hpositive.
    all: unfold entry_weight in *; cbn [List.map fold_right fst Pos.size_nat] in *; lia.
  Qed.

  Lemma is_empty_spec : forall A (m : t A), is_empty m = true <-> m = empty.
  Proof.
    intros A [|n]; split; intro H; try reflexivity; discriminate H.
  Qed.

  Lemma remove_empty {A} p : remove p (@empty A) = empty.
  Proof.
    unfold remove, empty. induction p;
      cbn [replace left right value trie_left trie_right trie_value]; rewrite ?IHp; reflexivity.
  Qed.

  Lemma nodes_components_ne {A} (n : ne A) :
    nodes (Nodes n) = S (nodes (left (Nodes n)) + nodes (right (Nodes n))).
  Proof.
    destruct n; cbn [nodes nodes_ne left right trie_left trie_right]; lia.
  Qed.

  Lemma nodes_remove : forall A p (m : t A), nodes (remove p m) <= nodes m.
  Proof.
    intros A p. induction p; intro m.
    all: destruct m as [|n]; [rewrite remove_empty; reflexivity|].
    all: cbn [remove replace]; eapply Nat.le_trans; [apply nodes_node_le_aux|].
    all: pose proof (nodes_components_ne n) as Hnodes.
    - specialize (IHp (right (Nodes n))). unfold remove in IHp. lia.
    - specialize (IHp (left (Nodes n))). unfold remove in IHp. lia.
    - lia.
  Qed.

  Lemma nodes_filter {A B} (f : A -> option B) m : nodes (filter_map f m) <= nodes m.
  Proof.
    destruct m as [|n]; [reflexivity|].
    induction n; cbn [filter_map filter_ne].
    all: eapply Nat.le_trans; [apply nodes_node_le_aux|].
    all: cbn [filter_map nodes nodes_ne] in *; lia.
  Qed.

  Lemma nodes_map : forall A B (f : A -> B) m, nodes (map f m) <= nodes m.
  Proof.
    intros A B f m. apply nodes_filter.
  Qed.

  Lemma nodes_merge_with {A B C} (f : option A -> option B -> option C) fl fr m u :
    (forall tr, nodes (fl tr) <= nodes tr) ->
    (forall tr, nodes (fr tr) <= nodes tr) ->
    nodes (merge_with f fl fr m u) <= nodes m + nodes u.
  Proof.
    intros Hl Hr. destruct m as [|n].
    - cbn [merge_with nodes]. apply Hr.
    - revert u. induction n; intros [|other].
      all: try (cbn [merge_with merge_ne nodes]; rewrite Nat.add_0_r; apply Hl).
      all: cbn [merge_with merge_ne]; eapply Nat.le_trans; [apply nodes_node_le_aux|].
      all: cbn [merge_with] in *.
      all: try pose proof (IHn (left (Nodes other))) as Hleft.
      all: try pose proof (IHn (right (Nodes other))) as Hright.
      all: try pose proof (IHn1 (left (Nodes other))) as Hleft.
      all: try pose proof (IHn2 (right (Nodes other))) as Hright.
      all: pose proof (Hr (left (Nodes other))) as Honly_left.
      all: pose proof (Hr (right (Nodes other))) as Honly_right.
      all: pose proof (nodes_components_ne other) as Hother.
      all: cbn [nodes nodes_ne] in *; lia.
  Qed.

  Lemma nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
    nodes (merge f m1 m2) <= nodes m1 + nodes m2.
  Proof.
    intros A B C f m1 m2. apply nodes_merge_with; intro tr; apply nodes_filter.
  Qed.

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
  TimeFun test_values.
  TimeFun forall2b_ne.
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

  Definition c_trie : N := 1024.

  (** Lookup pays one unit for each node it reads, so at most one for each key digit. *)
  Lemma T_trie_get_size_le : forall A p (m : t A),
    (T_trie_get p m <= N.of_nat (Pos.size_nat p))%N.
  Proof.
    intros A p. induction p as [p IH|p IH|]; intro m.
    all: unfold T_trie_get; fold (@T_trie_get A); time_simpl; time_cbn.
    all: destruct m as [|n]; [|destruct n]; time_cbn.
    all: try match goal with
      | |- context [T_trie_get _ ?c] => pose proof (IH c) as Hchild
      end.
    all: cbn [Pos.size_nat]; lia.
  Qed.

  (** A lookup that finds a binding reads one node for each key digit. *)
  Lemma T_trie_get_hit : forall A p (m : t A),
    trie_get p m <> None -> T_trie_get p m = N.of_nat (Pos.size_nat p).
  Proof.
    intros A p. induction p as [p IH|p IH|]; intros m Hhit.
    all: destruct m as [|n]; [exfalso; apply Hhit; reflexivity|].
    all: destruct n; cbn [trie_get] in Hhit; try (exfalso; apply Hhit; reflexivity).
    all: unfold T_trie_get; fold (@T_trie_get A); time_simpl; time_cbn.
    all: try rewrite (IH _ Hhit).
    all: cbn [Pos.size_nat]; lia.
  Qed.

  (** Lookup pays at most two units for each key digit. *)
  Lemma T_trie_get_le : forall A p (m : t A),
    (T_trie_get p m <= 2 * N.of_nat (Pos.size_nat p))%N.
  Proof.
    intros A p m. pose proof (T_trie_get_size_le A p m) as Hsize. lia.
  Qed.

  (** Add the bound of [T_trie_get_le] for each lookup clock that the goal mentions. *)
  Ltac trie_get_le :=
    repeat match goal with
    | |- context [T_trie_get ?p ?m] =>
      lazymatch goal with
      | _ : (T_trie_get p m <= _)%N |- _ => fail
      | _ => pose proof (T_trie_get_le _ p m)
      end
    end.

  (** The bound tactic covers two lookups of the same key in different tries. *)
  Local Lemma trie_get_le_twice : forall A p (m n : t A),
    (T_trie_get p m + T_trie_get p n <= 4 * N.of_nat (Pos.size_nat p))%N.
  Proof.
    intros A p m n. trie_get_le. lia.
  Qed.

  (** Lookup reads the root and continues in the child that the first key digit selects. *)
  Lemma T_trie_get_cases : forall A p (m : t A),
    T_trie_get p m =
      if is_empty m then 1%N else
      (1 + match p with
        | xH => 0
        | xO q => if is_empty (left m) then 0 else T_trie_get q (left m)
        | xI q => if is_empty (right m) then 0 else T_trie_get q (right m)
        end)%N.
  Proof.
    intros A [q|q|] [|n]; try destruct n; reflexivity.
  Qed.

  (** Replacement with a value never yields the empty trie. *)
  Lemma replace_some_nonempty : forall A k (a : A) m,
    is_empty (replace k (Some a) m) = false.
  Proof.
    intros A k a. induction k as [k IH|k IH|]; intro m; cbn [replace].
    - specialize (IH (right m)).
      destruct (left m), (value m), (replace k (Some a) (right m));
        try discriminate IH; reflexivity.
    - specialize (IH (left m)).
      destruct (replace k (Some a) (left m)), (value m), (right m);
        try discriminate IH; reflexivity.
    - destruct (left m), (right m); reflexivity.
  Qed.

  (** Setting a key never shortens the path that a later lookup reads. *)
  Lemma T_trie_get_set_le : forall A k p (a : A) m,
    (T_trie_get p m <= T_trie_get p (set k a m))%N.
  Proof.
    intros A k. unfold set. induction k as [k IH|k IH|]; intros [q|q|] a m.
    all: rewrite (T_trie_get_cases _ _ (replace _ (Some a) m)), (T_trie_get_cases _ _ m),
      replace_some_nonempty; cbn [replace].
    all: rewrite ?left_node, ?right_node, ?replace_some_nonempty.
    all: try pose proof (IH q a (right m)) as Hright.
    all: try pose proof (IH q a (left m)) as Hleft.
    all: destruct (is_empty m), (is_empty (left m)), (is_empty (right m)); lia.
  Qed.

  (** Replacement pays for the three observations and canonical reconstruction. *)
  Lemma replace_clock_bound : forall A p o (m : t A),
    (T_replace p o m <= 8 * N.of_nat (Pos.size_nat p))%N.
  Proof.
    intros A p. induction p as [p IH|p IH|]; intros o m; time_step.
    all: unfold T_left, T_value, T_right, T_trie_left, T_trie_value, T_trie_right.
    all: time_cbn; time_pose; try pose proof (IH o (left m));
      try pose proof (IH o (right m)); nia.
  Qed.

  (** Replacement rebuilds one node for each key digit, so it pays at least one unit each. *)
  Lemma replace_clock_lower : forall A p o (m : t A),
    (N.of_nat (Pos.size_nat p) <= T_replace p o m)%N.
  Proof.
    intros A p. induction p as [p IH|p IH|]; intros o m; time_unfold @T_replace.
    all: try pose proof (IH o (left m)) as Hleft; try pose proof (IH o (right m)) as Hright.
    all: cbn [Pos.size_nat]; lia.
  Qed.

  (** Setting a key pays at least one unit for each key digit. *)
  Lemma T_set_ge : forall A p (a : A) m,
    (N.of_nat (Pos.size_nat p) <= T_set p a m)%N.
  Proof.
    intros A p a m. pose proof (replace_clock_lower A p (Some a) m) as Hreplace.
    time_unfold @T_set. lia.
  Qed.

  Lemma T_is_empty_le : forall A (m : t A), (T_is_empty m <= c_trie)%N.
  Proof.
    intros A m. unfold c_trie. time_step.
  Qed.
  Lemma T_get_le : forall A p (m : t A),
    (T_get p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof.
    intros A p m. pose proof (T_trie_get_le A p m) as Hget.
    unfold T_get, c_trie. time_cbn. nia.
  Qed.
  Lemma T_set_le : forall A p (a : A) m,
    (T_set p a m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof.
    intros A p a m. pose proof (replace_clock_bound A p (Some a) m).
    unfold c_trie. time_step.
  Qed.
  Lemma T_remove_le : forall A p (m : t A),
    (T_remove p m <= c_trie * N.of_nat (Pos.size_nat p + 1))%N.
  Proof.
    intros A p m. pose proof (replace_clock_bound A p None m).
    unfold c_trie. time_step.
  Qed.
  (** Callback accounting follows the accumulator reached at each list element. *)
  Local Fixpoint folding_work {X B} (f : B -> X -> B) (w : B -> X -> N)
      (xs : list X) (b : B) : N :=
    match xs with
    | nil => 0%N
    | x :: xs => (w b x + folding_work f w xs (f b x))%N
    end.

  Local Lemma folding_work_left {X B} (f : B -> X -> B) (w : B -> X -> N) xs :
    forall b total,
    snd (fold_left (fun bw x => (f (fst bw) x, (snd bw + w (fst bw) x)%N))
      xs (b, total)) = (total + folding_work f w xs b)%N.
  Proof.
    induction xs as [|x xs IH]; intros b total; cbn [fold_left folding_work fst snd].
    - nia.
    - rewrite IH. nia.
  Qed.

  Local Lemma folding_work_app {X B} (f : B -> X -> B) (w : B -> X -> N) xs ys :
    forall b, folding_work f w (xs ++ ys) b =
      (folding_work f w xs b + folding_work f w ys (fold_left f xs b))%N.
  Proof.
    induction xs as [|x xs IH]; intro b; cbn [app folding_work fold_left];
      rewrite ?IH; nia.
  Qed.

  Local Lemma folding_work_map {X Y B} (f : B -> Y -> B) (w : B -> Y -> N)
      (g : X -> Y) xs :
    forall b, folding_work f w (List.map g xs) b =
      folding_work (fun acc x => f acc (g x)) (fun acc x => w acc (g x)) xs b.
  Proof.
    induction xs as [|x xs IH]; intro b; cbn [List.map folding_work];
      rewrite ?IH; reflexivity.
  Qed.

  Local Lemma folding_work_uniform {X B} (f : B -> X -> B) (w : B -> X -> N) xs c :
    (forall b x, (w b x <= c)%N) ->
    forall b, (folding_work f w xs b <= c * N.of_nat (length xs))%N.
  Proof.
    intro Hbound. induction xs as [|x xs IH]; intro b.
    - cbn [folding_work length]. nia.
    - cbn [folding_work length]. rewrite Nat2N.inj_succ.
      pose proof (Hbound b x). specialize (IH (f b x)). nia.
  Qed.

  Local Lemma folding_left_map {X Y B} (f : B -> Y -> B) (g : X -> Y) xs b :
    fold_left f (List.map g xs) b = fold_left (fun acc x => f acc (g x)) xs b.
  Proof.
    revert b. induction xs as [|x xs IH]; intro b; cbn [List.map fold_left]; auto.
  Qed.

  Local Definition folding_keys {A} (xs : list (positive * A)) : nat :=
    fold_right Nat.add 0 (List.map (fun kv => Pos.size_nat (fst kv)) xs).

  Local Lemma folding_keys_cons {A} p (a : A) xs :
    folding_keys ((p, a) :: xs) = Pos.size_nat p + folding_keys xs.
  Proof.
    reflexivity.
  Qed.

  Local Lemma folding_keys_app {A} (xs ys : list (positive * A)) :
    folding_keys (xs ++ ys) = folding_keys xs + folding_keys ys.
  Proof.
    unfold folding_keys. induction xs as [|[p a] xs IH];
      cbn [List.map fold_right app fst] in *; lia.
  Qed.

  Local Lemma folding_keys_lift {A} (bit : positive -> positive) xs :
    (forall p, Pos.size_nat (bit p) = S (Pos.size_nat p)) ->
    folding_keys (List.map (fun kv : positive * A => (bit (fst kv), snd kv)) xs) =
      folding_keys xs + length xs.
  Proof.
    intro Hbit. unfold folding_keys. induction xs as [|[p a] xs IH]; [reflexivity|].
    cbn [List.map fold_right length fst snd] in *. rewrite Hbit. lia.
  Qed.

  Local Lemma folding_weight {A} (m : t A) :
    weight m = folding_keys (elements m) + length (elements m).
  Proof.
    unfold weight, folding_keys.
    induction (elements m) as [|[p a] xs IH]; cbn [List.map fold_right length fst]; lia.
  Qed.

  Local Lemma folding_state {A B} (f : B -> positive -> A -> B) path n b :
    fold_ne f path n b =
      fold_left (fun acc kv => f acc (path (fst kv)) (snd kv)) (entries_ne n) b.
  Proof.
    exact (fold_path_entries f (Nodes n) path b).
  Qed.

  Local Lemma folding_values_state {A B} (f : B -> A -> B) n b :
    fold_values_ne f n b =
      fold_left (fun acc kv => f acc (snd kv)) (entries_ne n) b.
  Proof.
    exact (fold_values_entries f (Nodes n) b).
  Qed.

  Local Lemma folding_collect_length {A} (m : t A) :
    length (fold (fun acc p a => (p, a) :: acc) m nil) = length (elements m).
  Proof.
    rewrite fold_spec.
    assert (Hlength : forall (xs acc : list (positive * A)),
      length (fold_left (fun acc kv => (fst kv, snd kv) :: acc) xs acc) =
        length xs + length acc).
    { intro xs. induction xs as [|[p a] xs IH]; intro acc; cbn [fold_left length fst snd].
      - reflexivity.
      - rewrite IH. cbn [length]. lia. }
    rewrite Hlength. cbn [length]. lia.
  Qed.

  Local Lemma folding_extend_bound bit T_bit path T_path q d :
    (forall p, (T_bit p <= 1)%N) -> (forall p, (T_path p <= d)%N) ->
    (T_extend bit T_bit path T_path q <= d + 4)%N.
  Proof.
    intros Hbit Hpath. time_step.
  Qed.

  Local Ltac folding_pose_child IH child d Hpath :=
    lazymatch goal with
    | |- context [T_fold_ne ?f ?Tf ?path ?Tp child ?acc] =>
      let Hchild := fresh "Hfold" in
      pose proof (IH path Tp acc (d + 4)%N) as Hchild;
      specialize (Hchild ltac:(intro q; apply folding_extend_bound;
        [intro p; reflexivity|exact Hpath]))
    end.

  (** Prefix extension is charged once for every bit of every emitted key. *)
  Local Lemma folding_ne_sum {A B} (f : B -> positive -> A -> B) T_f (n : ne A) :
    forall path T_path b d, (forall p, (T_path p <= d)%N) ->
    (T_fold_ne f T_f path T_path n b <=
      8 * N.of_nat (nodes_ne n + folding_keys (entries_ne n)) +
      (d + 4) * N.of_nat (length (entries_ne n)) +
      folding_work (fun acc kv => f acc (path (fst kv)) (snd kv))
        (fun acc kv => T_f acc (path (fst kv)) (snd kv)) (entries_ne n) b)%N.
  Proof.
    induction n; intros path T_path b d Hpath; time_unfold @T_fold_ne;
      try time_unfold @T_emit; time_simpl.
    all: tryif (let H := type of IHn in idtac)
      then folding_pose_child IHn n d Hpath else idtac.
    all: tryif (let H := type of IHn1 in idtac)
      then folding_pose_child IHn1 n1 d Hpath else idtac.
    all: tryif (let H := type of IHn2 in idtac)
      then folding_pose_child IHn2 n2 d Hpath else idtac.
    all: cbn [nodes_ne entries_ne].
    all: rewrite ?folding_keys_app, ?folding_keys_cons,
      ?(folding_keys_lift xO _ (fun p => eq_refl)),
      ?(folding_keys_lift xI _ (fun p => eq_refl)), ?folding_work_app.
    all: cbn [folding_work fold_left fst snd Pos.size_nat length].
    all: rewrite ?folding_work_map, ?folding_left_map, ?length_app, ?length_map.
    all: rewrite ?folding_state in *; unfold emit, extend in *.
    all: cbn [fst snd length] in *.
    all: rewrite ?length_map, ?Nat2N.inj_add, ?Nat2N.inj_succ in *.
    all: time_simpl; time_pose; time_cbn_all; nia.
  Qed.

  Local Lemma folding_path_sum {A B} (f : B -> positive -> A -> B) T_f path T_path m b d :
    (forall p, (T_path p <= d)%N) ->
    (T_fold_path f T_f path T_path m b <=
      8 * N.of_nat (nodes m + folding_keys (elements m)) +
      (d + 4) * N.of_nat (length (elements m)) +
      folding_work (fun acc kv => f acc (path (fst kv)) (snd kv))
        (fun acc kv => T_f acc (path (fst kv)) (snd kv)) (elements m) b + 1)%N.
  Proof.
    intro Hpath. destruct m as [|n]; rewrite !elements_entries.
    - time_unfold @T_fold_path. time_cbn. nia.
    - pose proof (folding_ne_sum f T_f n path T_path b d Hpath) as Hfold.
      time_unfold @T_fold_path. unfold folding_keys in *. time_cbn_all. nia.
  Qed.

  Local Lemma folding_public_sum {A B} (f : B -> positive -> A -> B) T_f m b :
    (T_fold f T_f m b <=
      8 * N.of_nat (nodes m + folding_keys (elements m)) +
      5 * N.of_nat (length (elements m)) +
      folding_work (fun acc kv => f acc (fst kv) (snd kv))
        (fun acc kv => T_f acc (fst kv) (snd kv)) (elements m) b + 2)%N.
  Proof.
    pose proof (folding_path_sum f T_f (fun p => p) (fun _ => 1%N) m b 1%N
      (fun _ => N.le_refl 1)) as Hfold.
    time_unfold @T_fold. unfold folding_keys in *. time_cbn_all. nia.
  Qed.

  Lemma T_fold_le : forall A B (f : B -> positive -> A -> B) T_f m b k,
    ((forall acc p a, T_f acc p a <= k) ->
    T_fold f T_f m b <= c_trie * ((k + 1) * N.of_nat (nodes m + 1) +
      N.of_nat (weight m)))%N.
  Proof.
    intros A B f T_f m b k Hcallback.
    pose proof (folding_public_sum f T_f m b) as Hfold.
    pose proof (folding_work_uniform (fun acc kv => f acc (fst kv) (snd kv))
      (fun acc kv => T_f acc (fst kv) (snd kv)) (elements m) k
      (fun acc kv => Hcallback acc (fst kv) (snd kv)) b) as Hwork.
    pose proof (elements_length_nodes m) as Hbindings. apply time_of_nat_le in Hbindings.
    rewrite folding_weight. unfold c_trie. rewrite !Nat2N.inj_add in *.
    nia.
  Qed.
  Local Lemma folding_elements_sum {A} (m : t A) :
    (T_elements m <=
      16 * N.of_nat (nodes m + folding_keys (elements m) + length (elements m) + 1))%N.
  Proof.
    pose proof (folding_public_sum (fun (acc : list (positive * A)) p a => (p, a) :: acc)
      (fun _ _ _ => 1%N) m nil) as Hfold.
    pose proof (folding_work_uniform
      (fun (acc : list (positive * A)) kv => (fst kv, snd kv) :: acc)
      (fun _ _ => 1%N) (elements m) 1%N (fun _ _ => N.le_refl 1) nil) as Hwork.
    time_unfold @T_elements. time_pose.
    rewrite ?folding_collect_length in *.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Lemma T_elements_le : forall A (m : t A),
    (T_elements m <= c_trie * N.of_nat (weight m + 1))%N.
  Proof.
    intros A m. pose proof (folding_elements_sum m) as Htime.
    pose proof (nodes_le_weight A m) as Hnodes.
    rewrite folding_weight in Hnodes |- *. apply time_of_nat_le in Hnodes.
    unfold c_trie. rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_get_hit_ge : forall A p (m : t A),
    get p m <> None -> (N.of_nat (Pos.size_nat p) <= T_get p m)%N.
  Proof.
    intros A p m Hhit. pose proof (T_trie_get_hit A p m Hhit) as Hclock.
    unfold T_get. time_cbn. lia.
  Qed.

  Definition k_node : N := 8.
  Definition k_replace : N := 16.
  Definition k_filter : N := 8.
  Definition k_merge : N := 16.
  Definition k_check : N := 16.
  Definition k_fold : N := 16.
  Definition k_elements : N := 64.

  Definition bindings {A} (m : t A) : nat := length (elements m).
  Definition key_mass {A} (m : t A) : nat :=
    fold_right Nat.add 0
      (List.map (fun kv => Pos.size_nat (fst kv)) (elements m)).
  Definition fold_work {A B} (f : B -> positive -> A -> B)
      (T_f : B -> positive -> A -> N) (m : t A) (b : B) : N :=
    snd (fold_left (fun bw kv =>
      (f (fst bw) (fst kv) (snd kv),
        (snd bw + T_f (fst bw) (fst kv) (snd kv))%N)) (elements m) (b, 0%N)).

  Lemma node_def : forall A (m : t A), node (left m) (value m) (right m) = m.
  Proof.
    intros A m. apply node_eta.
  Qed.
  Lemma nodes_node_le : forall A (l r : t A) o,
    nodes (node l o r) <= S (nodes l + nodes r).
  Proof.
    intros A l r o. apply nodes_node_le_aux.
  Qed.
  Lemma weight_def : forall A (m : t A), weight m = key_mass m + bindings m.
  Proof.
    intros A m. unfold weight, key_mass, bindings.
    induction (elements m) as [|[p a] xs IH]; cbn [List.map fold_right length fst]; lia.
  Qed.
  Lemma bindings_le_nodes : forall A (m : t A), bindings m <= nodes m.
  Proof.
    intros A m. apply elements_length_nodes.
  Qed.
  Lemma fold_path_def : forall A B (f : B -> positive -> A -> B) path m b,
    fold_path f path m b =
      fold_left (fun acc kv => f acc (path (fst kv)) (snd kv)) (elements m) b.
  Proof.
    intros A B f path m b. apply fold_path_elements.
  Qed.
  Lemma fold_work_le : forall A B (f : B -> positive -> A -> B) T_f m b c,
    ((forall acc p a, T_f acc p a <= c) -> fold_work f T_f m b <= c * N.of_nat (bindings m))%N.
  Proof.
    intros A B f T_f m b c Hcallback. unfold fold_work, bindings.
    assert (Hsum : forall xs acc total,
      (snd (fold_left (fun bw kv =>
        (f (fst bw) (fst kv) (snd kv), snd bw + T_f (fst bw) (fst kv) (snd kv)))
        xs (acc, total)) <= total + c * N.of_nat (length xs))%N).
    { induction xs as [|[p a] xs IH]; intros acc total.
      - change (total <= total + c * N.of_nat 0)%N. nia.
      - change (snd (fold_left (fun bw kv =>
          (f (fst bw) (fst kv) (snd kv), snd bw + T_f (fst bw) (fst kv) (snd kv)))
          xs (f acc p a, (total + T_f acc p a)%N)) <=
          total + c * N.of_nat (S (length xs)))%N.
        specialize (IH (f acc p a) (total + T_f acc p a)%N).
        pose proof (Hcallback acc p a). rewrite Nat2N.inj_succ. nia. }
    specialize (Hsum (elements m) b 0%N). nia.
  Qed.
  Lemma get_replace : forall A p q o (m : t A),
    get p (replace q o m) = if Pos.eqb p q then o else get p m.
  Proof.
    intros A p q o m. destruct (Pos.eqb p q) eqn:Heq.
    - apply Pos.eqb_eq in Heq. subst q. apply get_replace_same.
    - apply Pos.eqb_neq in Heq. apply get_replace_other. congruence.
  Qed.
  Lemma get_filter_map : forall A B (f : A -> option B) m p,
    get p (filter_map f m) =
      match get p m with Some a => f a | None => None end.
  Proof.
    intros A B f m p. apply get_filter.
  Qed.
  Lemma fold_values_def : forall A B (f : B -> A -> B) m b,
    fold_values f m b =
      fold_left (fun acc kv => f acc (snd kv)) (elements m) b.
  Proof.
    intros A B f m b. apply fold_values_elements.
  Qed.
  Lemma T_node_parts_le : forall A (l r : t A) o,
    (T_left l + T_value l + T_right l + T_node l o r <= k_node)%N.
  Proof.
    intros A l r o.
    unfold k_node, T_left, T_value, T_right, T_node,
      T_trie_left, T_trie_value, T_trie_right.
    time_cbn. nia.
  Qed.
  Lemma T_replace_le : forall A p o (m : t A),
    (T_replace p o m <= k_replace * N.of_nat (Pos.size_nat p + 1))%N.
  Proof.
    intros A p o m. pose proof (replace_clock_bound A p o m).
    unfold k_replace. nia.
  Qed.
  (** Each nonempty filtering node pays constant overhead and at most one callback. *)
  Local Lemma filter_ne_clock_bound : forall A B (f : A -> option B) T_f n c,
    (forall a, T_f a <= c)%N ->
    (T_filter_ne f T_f n <= 8 * (c + 1) * N.of_nat (nodes_ne n))%N.
  Proof.
    intros A B f T_f n c Hcallback. induction n; time_step.
    all: unfold T_filter_value; time_cbn; time_pose; nia.
  Qed.

  Lemma T_filter_map_le : forall A B (f : A -> option B) T_f m c,
    ((forall a, T_f a <= c) ->
    T_filter_map f T_f m <= k_filter * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A B f T_f [|n] c Hcallback; unfold k_filter.
    - time_step.
    - pose proof (filter_ne_clock_bound A B f T_f n c Hcallback).
      time_step.
  Qed.
  (** Sums over consecutive traversal segments add without duplicating callbacks. *)
  Local Lemma filtering_sum_app (xs ys : list N) :
    fold_right N.add 0%N (xs ++ ys) =
      (fold_right N.add 0 xs + fold_right N.add 0 ys)%N.
  Proof.
    induction xs as [|x xs IH]; cbn [app fold_right]; rewrite ?IH; lia.
  Qed.

  Local Lemma filtering_ne_sum {A B} (f : A -> option B) T_f (n : ne A) :
    (T_filter_ne f T_f n <= 8 * N.of_nat (nodes_ne n) +
      fold_right N.add 0
        (List.map (fun ka => T_f (snd ka)) (entries_ne n)))%N.
  Proof.
    induction n; time_unfold @T_filter_ne; time_unfold @T_filter_value; time_simpl.
    all: cbn [nodes_ne entries_ne].
    all: rewrite ?map_app, ?map_map, ?filtering_sum_app.
    all: cbn [List.map fold_right fst snd].
    all: rewrite ?map_map; cbn [fst snd].
    all: rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all; nia.
  Qed.

  (** Filtering charges each callback at its present binding. *)
  Lemma T_filter_map_sum_le : forall A B (f : A -> option B) T_f m,
    (T_filter_map f T_f m <= k_filter * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun ka => T_f (snd ka)) (elements m))))%N.
  Proof.
    intros A B f T_f [|n]; rewrite elements_entries; unfold k_filter.
    - time_step.
    - pose proof (filtering_ne_sum f T_f n) as Hfilter.
      time_unfold @T_filter_map. time_cbn_all. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Merge overhead is linear in the two skeletons, including one-sided handlers. *)
  Local Lemma merge_ne_clock_bound {A B C} (f : option A -> option B -> option C)
      T_f (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr c cl cr
      (Hcallback : forall a b, (T_f a b <= c)%N)
      (Hleft : forall a, (T_fl a <= cl * N.of_nat (nodes a + 1))%N)
      (Hright : forall b, (T_fr b <= cr * N.of_nat (nodes b + 1))%N)
      (n : ne A) : forall u,
    (T_merge_ne f T_f fl T_fl fr T_fr n u <=
      16 * (c + cl + cr + 1) * N.of_nat (nodes_ne n + nodes u))%N.
  Proof.
    remember (16 * (c + cl + cr + 1))%N as budget eqn:Hbudget.
    assert (Hleft_budget : (2 * cl + 1 <= budget)%N) by nia.
    assert (Hright_budget : (cr <= budget)%N) by nia.
    assert (Hroot_budget : (c + 2 * cr + 16 <= 2 * budget)%N) by nia.
    clear Hbudget.
    assert (Hright_linear : forall tr,
      (T_fr tr <= budget * N.of_nat (nodes tr) + cr)%N).
    { intro tr. pose proof (Hright tr) as Hraw.
      pose proof (N.mul_le_mono_r _ _ (N.of_nat (nodes tr)) Hright_budget) as Hscaled.
      rewrite Nat2N.inj_add in Hraw. time_cbn_all. nia. }
    assert (Hempty : forall mass run,
      (1 <= mass)%N -> (run <= cl * (mass + 1))%N ->
      (1 + run <= budget * mass)%N).
    { intros mass run Hpositive Hrun.
      pose proof (N.mul_le_mono_r _ _ mass Hleft_budget) as Hscaled. nia. }
    clear Hleft_budget Hright_budget Hright.
    induction n; intros [|other]; time_unfold @T_merge_ne.
    all: try solve [
      match goal with
      | |- context [?clock (Nodes ?tree)] =>
        pose proof (Hleft (Nodes tree)) as Honly;
        cbn [nodes] in Honly |- *; rewrite Nat.add_0_r;
        apply Hempty;
        [cbn [nodes_ne]; lia|rewrite Nat2N.inj_add in Honly; exact Honly]
      end].
    all: try pose proof (IHn (left (Nodes other))) as Hmergeleft.
    all: try pose proof (IHn (right (Nodes other))) as Hmergeright.
    all: try pose proof (IHn1 (left (Nodes other))) as Hmergeleft.
    all: try pose proof (IHn2 (right (Nodes other))) as Hmergeright.
    all: pose proof (Hright_linear (left (Nodes other))) as Honlyleft.
    all: pose proof (Hright_linear (right (Nodes other))) as Honlyright.
    all: pose proof (f_equal (fun count => budget * N.of_nat count)%N
      (nodes_components_ne other)) as Hnodes.
    all: unfold T_merge_value, T_left, T_value, T_right,
      T_trie_left, T_trie_value, T_trie_right; time_simpl; time_pose.
    all: cbn [nodes nodes_ne] in *;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all.
    all: repeat rewrite N.mul_add_distr_l in *.
    all: lia.
  Qed.

  Lemma T_merge_with_le : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u c cl cr,
    ((forall a b, T_f a b <= c) ->
    (forall a, T_fl a <= cl * N.of_nat (nodes a + 1)) ->
    (forall b, T_fr b <= cr * N.of_nat (nodes b + 1)) ->
    T_merge_with f T_f fl T_fl fr T_fr m u <=
      k_merge * (c + cl + cr + 1) * N.of_nat (nodes m + nodes u + 1))%N.
  Proof.
    intros A B C f T_f fl T_fl fr T_fr [|n] u c cl cr Hcallback Hleft Hright.
    - pose proof (Hright u). unfold k_merge. time_step.
    - pose proof (merge_ne_clock_bound f T_f fl T_fl fr T_fr c cl cr
        Hcallback Hleft Hright n u) as Hmerge.
      unfold k_merge. time_step.
  Qed.

  (** Constant one-sided handlers let either input skeleton pay for the traversal. *)
  Local Lemma merge_ne_clock_sides {A B C} (f : option A -> option B -> option C)
      T_f (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr c
      (Hcallback : forall a b, (T_f a b <= c)%N)
      (Hleft : forall a, (T_fl a <= c)%N)
      (Hright : forall b, (T_fr b <= c)%N)
      (n : ne A) : forall u,
    (T_merge_ne f T_f fl T_fl fr T_fr n u <=
      16 * (c + 1) * N.of_nat (nodes_ne n) + c + 1)%N /\
    (T_merge_ne f T_f fl T_fl fr T_fr n u <=
      16 * (c + 1) * N.of_nat (nodes u) + c + 1)%N.
  Proof.
    remember (16 * (c + 1))%N as budget eqn:Hbudget.
    assert (Hroot : (3 * c + 16 <= budget)%N) by nia.
    clear Hbudget.
    induction n; intros [|other].
    all: try solve [split; time_unfold @T_merge_ne; time_pose;
      cbn [nodes]; time_cbn; nia].
    all: try destruct (IHn (left (Nodes other))) as [Hll Hlr].
    all: try destruct (IHn (right (Nodes other))) as [Hrl Hrr].
    all: try destruct (IHn1 (left (Nodes other))) as [Hll Hlr].
    all: try destruct (IHn2 (right (Nodes other))) as [Hrl Hrr].
    all: pose proof (f_equal (fun count => budget * N.of_nat count)%N
      (nodes_components_ne other)) as Hnodes.
    all: split; time_unfold @T_merge_ne.
    all: unfold T_merge_value, T_left, T_value, T_right,
      T_trie_left, T_trie_value, T_trie_right; time_simpl; time_pose.
    all: cbn [nodes nodes_ne] in *;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all.
    all: repeat rewrite N.mul_add_distr_l in *.
    all: lia.
  Qed.

  (** A merge with constant handlers visits at most the smaller input skeleton. *)
  Lemma T_merge_with_min : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u c,
    ((forall a b, T_f a b <= c) ->
    (forall a, T_fl a <= c) -> (forall b, T_fr b <= c) ->
    T_merge_with f T_f fl T_fl fr T_fr m u <=
      2 * k_merge * (c + 1) * N.of_nat (Nat.min (nodes m) (nodes u) + 1))%N.
  Proof.
    intros A B C f T_f fl T_fl fr T_fr [|n] u c Hcallback Hleft Hright.
    - pose proof (Hright u). unfold k_merge. time_step.
    - destruct (merge_ne_clock_sides f T_f fl T_fl fr T_fr c
        Hcallback Hleft Hright n u) as [Hleft_bound Hright_bound].
      unfold k_merge. time_unfold @T_merge_with. cbn [nodes].
      destruct (Nat.le_ge_cases (nodes_ne n) (nodes u)) as [Hle|Hge].
      + rewrite Nat.min_l by exact Hle.
        rewrite Nat2N.inj_add. time_cbn_all. nia.
      + rewrite Nat.min_r by exact Hge.
        rewrite Nat2N.inj_add. time_cbn_all. nia.
  Qed.

  (** Merging charges the callbacks at shared and one-sided bindings. *)
  Local Lemma merging_sum_app (xs ys : list N) :
    fold_right N.add 0%N (xs ++ ys) =
      (fold_right N.add 0 xs + fold_right N.add 0 ys)%N.
  Proof.
    induction xs as [|x xs IH]; cbn [app fold_right]; rewrite ?IH; lia.
  Qed.

  Local Lemma merging_sum_add {X} (w : X -> N) (xs : list X) :
    fold_right N.add 0%N (List.map (fun x => 1 + w x)%N xs) =
      (N.of_nat (length xs) + fold_right N.add 0 (List.map w xs))%N.
  Proof.
    induction xs as [|x xs IH]; cbn [List.map fold_right length];
      rewrite ?Nat2N.inj_succ, ?IH; nia.
  Qed.

  Local Lemma merging_lookup_entries {A} (m : t A) (w : positive -> option A -> N) :
    List.map (fun p => w p (get p m)) (List.map fst (elements m)) =
      List.map (fun ka => w (fst ka) (Some (snd ka))) (elements m).
  Proof.
    rewrite map_map. apply map_ext_in. intros [p a] Hin.
    apply elements_spec in Hin. cbn [fst snd]. now rewrite Hin.
  Qed.

  Local Lemma merging_empty_left {A B} (w : option A -> option B -> N)
      (xs : list (positive * B)) :
    List.map (fun kb => w (get (fst kb) (@Empty A)) (Some (snd kb))) xs =
      List.map (fun kb => w None (Some (snd kb))) xs.
  Proof.
    apply map_ext. intros [p b]. cbn [fst snd]. now rewrite get_empty.
  Qed.

  Local Lemma merging_empty_right {A B} (w : option A -> option B -> N)
      (xs : list (positive * A)) :
    List.map (fun ka => w (Some (snd ka)) (get (fst ka) (@Empty B))) xs =
      List.map (fun ka => w (Some (snd ka)) None) xs.
  Proof.
    apply map_ext. intros [p a]. cbn [fst snd]. now rewrite get_empty.
  Qed.

  Local Lemma T_merge_ne_sum {A B C} (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr cl cr
      (Hfl : forall a, (T_fl a <= cl * (N.of_nat (nodes a + 1) + fold_right N.add 0
        (List.map (fun ka => T_f (Some (snd ka)) None) (elements a))))%N)
      (Hfr : forall b, (T_fr b <= cr * (N.of_nat (nodes b + 1) + fold_right N.add 0
        (List.map (fun kb => T_f None (Some (snd kb))) (elements b))))%N)
      (n : ne A) : forall u,
    (T_merge_ne f T_f fl T_fl fr T_fr n u <=
      16 * (cl + cr + 1) * (T_f None None + 1) * N.of_nat (nodes_ne n + nodes u) +
      16 * (cl + cr + 1) *
      (fold_right N.add 0 (List.map
         (fun ka => T_f (Some (snd ka)) (get (fst ka) u)) (entries_ne n)) +
       fold_right N.add 0 (List.map
         (fun kb => T_f (get (fst kb) (Nodes n)) (Some (snd kb))) (entries u))))%N.
  Proof.
    remember (16 * (cl + cr + 1))%N as scale eqn:Hscale.
    remember (scale * (T_f None None + 1))%N as budget eqn:Hbudget.
    assert (Hleft_budget : (2 * cl + 1 <= budget)%N) by nia.
    assert (Hleft_scale : (cl <= scale)%N) by nia.
    assert (Hright_scale : (cr <= scale)%N) by nia.
    assert (Hright_budget : (cr <= budget)%N) by nia.
    assert (Hroot_budget : (T_f None None + 2 * cr + 16 <= 2 * budget)%N) by nia.
    assert (Hscale_positive : (1 <= scale)%N) by nia.
    clear Hscale Hbudget.
    assert (Hleft_linear : forall tr,
      (T_fl tr <= cl * N.of_nat (nodes tr + 1) + scale * fold_right N.add 0
        (List.map (fun ka => T_f (Some (snd ka)) None) (entries tr)))%N).
    { intro tr. pose proof (Hfl tr) as Hraw. rewrite elements_entries in Hraw.
      pose proof (N.mul_le_mono_r _ _ (fold_right N.add 0%N
        (List.map (fun ka => T_f (Some (snd ka)) None) (entries tr))) Hleft_scale)
        as Hscaled.
      rewrite N.mul_add_distr_l in Hraw. lia. }
    assert (Hright_linear : forall tr,
      (T_fr tr <= budget * N.of_nat (nodes tr) + cr + scale * fold_right N.add 0
        (List.map (fun kb => T_f None (Some (snd kb))) (entries tr)))%N).
    { intro tr. pose proof (Hfr tr) as Hraw. rewrite elements_entries in Hraw.
      pose proof (N.mul_le_mono_r _ _ (N.of_nat (nodes tr)) Hright_budget) as Hnodes.
      pose proof (N.mul_le_mono_r _ _ (fold_right N.add 0%N
        (List.map (fun kb => T_f None (Some (snd kb))) (entries tr))) Hright_scale)
        as Hscaled.
      rewrite Nat2N.inj_add in Hraw. time_cbn_all.
      repeat rewrite N.mul_add_distr_l in Hraw. lia. }
    assert (Hempty : forall mass run work,
      (1 <= mass)%N -> (run <= cl * (mass + 1) + scale * work)%N ->
      (1 + run <= budget * mass + scale * work)%N).
    { intros mass run work Hpositive Hrun.
      pose proof (N.mul_le_mono_r _ _ mass Hleft_budget) as Hscaled. nia. }
    assert (Hroot : forall a b,
      (T_f a b + 2 * cr + 16 <= 2 * budget + scale *
        ((match a with Some _ => T_f a b | None => 0 end) +
         (match b with Some _ => T_f a b | None => 0 end)))%N).
    { intros a b.
      pose proof (N.mul_le_mono_r _ _ (T_f a b) Hscale_positive) as Hscaled.
      destruct a, b; time_cbn_all; repeat rewrite N.mul_add_distr_l; lia. }
    clear Hfl Hfr Hleft_budget Hleft_scale Hright_scale Hright_budget Hscale_positive.
    induction n; intros [|other]; time_unfold @T_merge_ne.
    all: try solve [
      match goal with
      | |- context [?clock (Nodes ?tree)] =>
        pose proof (Hleft_linear (Nodes tree)) as Honly;
        rewrite merging_empty_right;
        cbn [nodes entries List.map fold_right] in Honly |- *;
        rewrite Nat.add_0_r; repeat rewrite N.add_0_r;
        apply Hempty;
        [cbn [nodes_ne]; lia|rewrite Nat2N.inj_add in Honly; exact Honly]
      end].
    all: try pose proof (IHn (left (Nodes other))) as Hleft.
    all: try pose proof (IHn (right (Nodes other))) as Hright.
    all: try pose proof (IHn1 (left (Nodes other))) as Hleft.
    all: try pose proof (IHn2 (right (Nodes other))) as Hright.
    all: pose proof (Hright_linear (left (Nodes other))) as Honlyleft.
    all: pose proof (Hright_linear (right (Nodes other))) as Honlyright.
    all: match goal with
      | |- context [T_merge_value ?g ?T_g ?a ?b] => pose proof (Hroot a b) as Hrootcase
      end.
    all: unfold T_merge_value, T_left, T_value, T_right,
      T_trie_left, T_trie_value, T_trie_right; time_simpl.
    all: destruct other; cbn [nodes nodes_ne entries entries_ne] in *;
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      cbn [List.map fold_right fst snd get trie_get left right value
        trie_left trie_right trie_value] in *;
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      rewrite ?merging_empty_left, ?merging_empty_right in *;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *;
      time_cbn_all.
    all: repeat progress (
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      cbn [List.map fold_right fst snd get trie_get left right value
        trie_left trie_right trie_value] in *;
      rewrite ?merging_empty_left, ?merging_empty_right in *).
    all: repeat rewrite N.mul_add_distr_l in *; lia.
  Qed.

  Lemma T_merge_with_sum_le : forall A B C (f : option A -> option B -> option C) T_f
      (fl : t A -> t C) T_fl (fr : t B -> t C) T_fr m u cl cr,
    (forall a, T_fl a <= cl * (N.of_nat (nodes a + 1) + fold_right N.add 0
       (List.map (fun ka => T_f (Some (snd ka)) None) (elements a))))%N ->
    (forall b, T_fr b <= cr * (N.of_nat (nodes b + 1) + fold_right N.add 0
       (List.map (fun kb => T_f None (Some (snd kb))) (elements b))))%N ->
    (T_merge_with f T_f fl T_fl fr T_fr m u <= k_merge * (cl + cr + 1) *
      ((T_f None None + 1) * N.of_nat (nodes m + nodes u + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m) (get p u))
         (List.map fst (elements m) ++ List.map fst (elements u)))))%N.
  Proof.
    intros A B C f T_f fl T_fl fr T_fr m u cl cr Hfl Hfr.
    rewrite map_app, merging_sum_app.
    rewrite (merging_lookup_entries m (fun p a => T_f a (get p u))).
    rewrite (merging_lookup_entries u (fun p b => T_f (get p m) b)).
    destruct m as [|n].
    - pose proof (Hfr u) as Honly. rewrite !elements_entries in *.
      time_unfold @T_merge_with. rewrite merging_empty_left.
      unfold k_merge. cbn [entries nodes List.map fold_right].
      rewrite !Nat2N.inj_add. time_cbn_all. nia.
    - pose proof (T_merge_ne_sum f T_f fl T_fl fr T_fr cl cr Hfl Hfr n u) as Hsum.
      rewrite !elements_entries. time_unfold @T_merge_with.
      unfold k_merge. cbn [entries nodes]. rewrite !Nat2N.inj_add in *.
      time_cbn_all. nia.
  Qed.
  (** Directional checking pays for at most one callback at each stored value. *)
  Local Lemma forall2_ne_clock_bound : forall A B (f : A -> option B -> bool) T_f n u c,
    (forall a b, T_f a b <= c)%N ->
    (T_forall2_ne f T_f n u <= 16 * (c + 1) * N.of_nat (nodes_ne n))%N.
  Proof.
    intros A B f T_f n u c Hcallback. revert u.
    induction n; intro u; time_step.
    all: unfold T_test_value, T_left, T_value, T_right,
      T_trie_left, T_trie_value, T_trie_right;
      time_cbn; time_pose; nia.
  Qed.

  Lemma T_forall2_le : forall A B (f : A -> option B -> bool) T_f m u c,
    ((forall a b, T_f a b <= c) ->
    T_forall2 f T_f m u <= k_check * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A B f T_f [|n] u c Hcallback; unfold k_check.
    - time_step.
    - pose proof (forall2_ne_clock_bound A B f T_f n u c Hcallback).
      time_step.
  Qed.
  (** Directional checking charges each visited binding against its lookup result. *)
  Local Lemma checking_sum_app (xs ys : list N) :
    fold_right N.add 0%N (xs ++ ys) =
      (fold_right N.add 0 xs + fold_right N.add 0 ys)%N.
  Proof.
    induction xs as [|x xs IH]; cbn [app fold_right]; rewrite ?IH; lia.
  Qed.

  Local Lemma T_forall2_ne_sum {A B} (f : A -> option B -> bool) T_f (n : ne A) :
    forall u,
    (T_forall2_ne f T_f n u <= 16 * N.of_nat (nodes_ne n) +
      fold_right N.add 0
        (List.map (fun ka => T_f (snd ka) (get (fst ka) u)) (entries_ne n)))%N.
  Proof.
    induction n; intro u; time_unfold @T_forall2_ne; time_unfold @T_test_value;
      time_simpl; time_cbn.
    all: cbn [nodes_ne entries_ne].
    all: rewrite ?map_app, ?map_map, ?checking_sum_app; time_cbn.
    all: try pose proof (IHn (left u)) as Hleft.
    all: try pose proof (IHn (right u)) as Hright.
    all: try pose proof (IHn1 (left u)) as Hleft.
    all: try pose proof (IHn2 (right u)) as Hright.
    all: try setoid_rewrite get_xO; try setoid_rewrite get_xI;
      cbn [fst snd left right value] in *.
    all: time_unfold @T_left; time_unfold @T_value; time_unfold @T_right.
    all: time_simpl; time_cbn_all; rewrite ?Nat2N.inj_add in *.
    all: repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      end; time_cbn.
    all: repeat rewrite map_map in *.
    all: try setoid_rewrite get_xH; try setoid_rewrite get_xO; try setoid_rewrite get_xI;
      cbn [fst snd] in *.
    all: unfold left, right, value in *.
    all: lia.
  Qed.

  Lemma T_forall2_sum_le : forall A B (f : A -> option B -> bool) T_f m u,
    (T_forall2 f T_f m u <= k_check * (N.of_nat (nodes m + 1) +
      fold_right N.add 0
        (List.map (fun ka => T_f (snd ka) (get (fst ka) u)) (elements m))))%N.
  Proof.
    intros A B f T_f [|n] u; rewrite elements_entries.
    - time_unfold @T_forall2. unfold k_check. time_cbn. nia.
    - pose proof (T_forall2_ne_sum f T_f n u) as Hsum.
      time_unfold @T_forall2. unfold k_check. time_cbn_all.
      rewrite Nat2N.inj_add. nia.
  Qed.

  (** A one-sided check pays for its callback wrapper at each stored binding. *)
  Local Lemma checking_one_side_sum {A B} (f : A -> bool) T_f (m : t A) :
    (T_forall2 (fun a (_ : option B) => f a) (fun a _ => 1 + T_f a)%N
       m (@empty B) <=
     32 * N.of_nat (nodes m + 1) +
     16 * fold_right N.add 0
       (List.map (fun ka => T_f (snd ka)) (entries m)))%N.
  Proof.
    pose proof (@T_forall2_sum_le A B (fun a _ => f a)
      (fun a _ => 1 + T_f a)%N m (@empty B)) as Hcheck.
    cbn beta in Hcheck.
    rewrite (merging_sum_add (fun ka => T_f (snd ka)) (elements m)) in Hcheck.
    pose proof (elements_length_nodes m) as Hbindings.
    apply time_of_nat_le in Hbindings. unfold k_check in Hcheck.
    rewrite elements_entries in Hcheck, Hbindings.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  (** The lockstep recursion charges callbacks only at keys present in either trie. *)
  Local Lemma T_forall2b_ne_sum {A B} (f : option A -> option B -> bool) T_f
      (n : ne A) : forall u,
    (T_forall2b_ne f T_f n u <=
      64 * N.of_nat (nodes_ne n + nodes u) + 32 *
      (fold_right N.add 0 (List.map
         (fun ka => T_f (Some (snd ka)) (get (fst ka) u)) (entries_ne n)) +
       fold_right N.add 0 (List.map
         (fun kb => T_f (get (fst kb) (Nodes n)) (Some (snd kb))) (entries u))))%N.
  Proof.
    induction n; intros [|other]; time_unfold @T_forall2b_ne.
    all: try solve [
      match goal with
      | |- context [T_forall2_ne _ _ ?tree _] =>
        pose proof (@checking_one_side_sum A B (fun a => f (Some a) None)
          (fun a => T_f (Some a) None) (Nodes tree)) as Honly;
        assert (Hpositive : (1 <= N.of_nat (nodes_ne tree))%N) by
          (cbn [nodes_ne]; rewrite ?Nat2N.inj_add; lia);
        unfold T_forall2 in Honly;
        rewrite merging_empty_right;
        cbn [nodes entries List.map fold_right] in Honly |- *;
        rewrite ?Nat.add_0_r, ?Nat2N.inj_add in *;
        time_cbn_all; nia
      end].
    all: try pose proof (IHn (left (Nodes other))) as Hleft.
    all: try pose proof (IHn (right (Nodes other))) as Hright.
    all: try pose proof (IHn1 (left (Nodes other))) as Hleft.
    all: try pose proof (IHn2 (right (Nodes other))) as Hright.
    all: pose proof (@checking_one_side_sum B A (fun b => f None (Some b))
      (fun b => T_f None (Some b)) (left (Nodes other))) as Honlyleft.
    all: pose proof (@checking_one_side_sum B A (fun b => f None (Some b))
      (fun b => T_f None (Some b)) (right (Nodes other))) as Honlyright.
    all: unfold T_test_values, T_left, T_value, T_right,
      T_trie_left, T_trie_value, T_trie_right; time_simpl.
    all: destruct other; cbn [nodes nodes_ne entries entries_ne] in *;
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      cbn [List.map fold_right fst snd get trie_get left right value
        trie_left trie_right trie_value] in *;
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      rewrite ?merging_empty_left, ?merging_empty_right in *;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *;
      time_cbn_all.
    all: repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      end; time_cbn.
    all: repeat progress (
      rewrite ?map_app, ?map_map, ?merging_sum_app in *;
      cbn [List.map fold_right fst snd get trie_get left right value
        trie_left trie_right trie_value] in *;
      rewrite ?merging_empty_left, ?merging_empty_right in *).
    all: repeat rewrite N.mul_add_distr_l in *; lia.
  Qed.

  (** Paired checking pays for both skeletons and the callbacks at their stored keys. *)
  Local Lemma T_forall2b_sum {A B} (f : option A -> option B -> bool) T_f
      (m : t A) (u : t B) :
    (T_forall2b f T_f m u <=
      64 * N.of_nat (nodes m + nodes u + 1) +
      32 * fold_right N.add 0 (List.map (fun p => T_f (get p m) (get p u))
        (List.map fst (elements m) ++ List.map fst (elements u))))%N.
  Proof.
    rewrite map_app, merging_sum_app.
    rewrite (merging_lookup_entries m (fun p a => T_f a (get p u))).
    rewrite (merging_lookup_entries u (fun p b => T_f (get p m) b)).
    destruct m as [|n].
    - pose proof (@checking_one_side_sum B A (fun b => f None (Some b))
        (fun b => T_f None (Some b)) u) as Honly.
      rewrite !elements_entries. time_unfold @T_forall2b.
      rewrite merging_empty_left. cbn [entries nodes List.map fold_right].
      rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
    - pose proof (T_forall2b_ne_sum f T_f n u) as Hsum.
      rewrite !elements_entries. time_unfold @T_forall2b.
      cbn [entries nodes]. rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Lemma T_fold_path_le : forall A B (f : B -> positive -> A -> B) T_f path T_path m b c d,
    ((forall acc p a, T_f acc p a <= c) -> (forall p, T_path p <= d) ->
    T_fold_path f T_f path T_path m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + (c + d + 1) * N.of_nat (bindings m) + 1))%N.
  Proof.
    intros A B f T_f path T_path m b c d Hcallback Hpath.
    pose proof (folding_path_sum f T_f path T_path m b d Hpath) as Hfold.
    pose proof (folding_work_uniform
      (fun acc kv => f acc (path (fst kv)) (snd kv))
      (fun acc kv => T_f acc (path (fst kv)) (snd kv)) (elements m) c
      (fun acc kv => Hcallback acc (path (fst kv)) (snd kv)) b) as Hwork.
    unfold k_fold, key_mass, bindings. unfold folding_keys in Hfold.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_fold_work_le : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <=
      k_fold * (N.of_nat (nodes m + key_mass m) + fold_work f T_f m b + 1))%N.
  Proof.
    intros A B f T_f m b. pose proof (folding_public_sum f T_f m b) as Hfold.
    pose proof (elements_length_nodes m) as Hbindings. apply time_of_nat_le in Hbindings.
    unfold k_fold, key_mass, fold_work. unfold folding_keys in Hfold.
    rewrite (folding_work_left (fun acc kv => f acc (fst kv) (snd kv))
      (fun acc kv => T_f acc (fst kv) (snd kv)) (elements m) b 0%N).
    rewrite !Nat2N.inj_add in *. nia.
  Qed.
  Lemma T_elements_plan_le : forall A (m : t A),
    (T_elements m <= k_elements * N.of_nat (nodes m + key_mass m + bindings m + 1))%N.
  Proof.
    intros A m. pose proof (folding_elements_sum m) as Htime.
    unfold k_elements, key_mass, bindings. unfold folding_keys in Htime. nia.
  Qed.
  (** The value fold charges callbacks at the accumulator used by each recursive call. *)
  Local Lemma fold_values_ne_clock_bound : forall A B (f : B -> A -> B) T_f n b c,
    (forall acc a, T_f acc a <= c)%N ->
    (T_fold_values_ne f T_f n b <= 4 * (c + 1) * N.of_nat (nodes_ne n))%N.
  Proof.
    intros A B f T_f n b c Hcallback. revert b.
    induction n; intro b; time_step.
  Qed.

  Lemma T_fold_values_le : forall A B (f : B -> A -> B) T_f m b c,
    ((forall acc a, T_f acc a <= c) ->
    T_fold_values f T_f m b <= k_fold * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A B f T_f [|n] b c Hcallback; unfold k_fold.
    - time_step.
    - pose proof (fold_values_ne_clock_bound A B f T_f n b c Hcallback).
      time_step.
  Qed.

  Lemma T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_merge f T_f m1 m2 <= c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof.
    intros A B C f T_f m1 m2 k Hcallback.
    assert (Hleft : forall m,
      (T_filter_map (fun a => f (Some a) None) (fun a => 1 + T_f (Some a) None)%N m <=
        8 * (k + 2) * N.of_nat (nodes m + 1))%N).
    { intro m. pose proof (T_filter_map_le A C (fun a => f (Some a) None)
        (fun a => 1 + T_f (Some a) None)%N m (k + 1)%N
        ltac:(intro a; pose proof (Hcallback (Some a) None); time_cbn; nia)) as Hfilter.
      unfold k_filter in Hfilter. nia. }
    assert (Hright : forall m,
      (T_filter_map (fun b => f None (Some b)) (fun b => 1 + T_f None (Some b))%N m <=
        8 * (k + 2) * N.of_nat (nodes m + 1))%N).
    { intro m. pose proof (T_filter_map_le B C (fun b => f None (Some b))
        (fun b => 1 + T_f None (Some b))%N m (k + 1)%N
        ltac:(intro b; pose proof (Hcallback None (Some b)); time_cbn; nia)) as Hfilter.
      unfold k_filter in Hfilter. nia. }
    time_unfold @T_merge.
    lazymatch goal with
    | |- context [T_merge_with ?g ?T_g ?fl ?T_fl ?fr ?T_fr ?m ?u] =>
      pose proof (T_merge_with_le A B C g T_g fl T_fl fr T_fr m u k
        (8 * (k + 2))%N (8 * (k + 2))%N Hcallback Hleft Hright) as Hmerge
    end.
    unfold k_merge in Hmerge. unfold c_trie.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  (** A bounded relation check is linear in the combined input skeletons. *)
  Lemma T_forall2b_le : forall A B
      (f : option A -> option B -> bool) T_f m1 m2 k,
    ((forall a b, T_f a b <= k) ->
    T_forall2b f T_f m1 m2 <=
      c_trie * (k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof.
    intros A B f T_f m1 m2 k Hcallback.
    pose proof (T_forall2b_sum f T_f m1 m2) as Hcheck.
    assert (Hwork : forall ps : list positive,
      (fold_right N.add 0
        (List.map (fun p => T_f (get p m1) (get p m2)) ps) <=
       k * N.of_nat (length ps))%N).
    { induction ps as [|p ps IH]; cbn [List.map fold_right length].
      - nia.
      - pose proof (Hcallback (get p m1) (get p m2)) as Hhead.
        rewrite Nat2N.inj_succ. nia. }
    specialize (Hwork (List.map fst (elements m1) ++ List.map fst (elements m2))).
    rewrite length_app, !length_map in Hwork.
    pose proof (elements_length_nodes m1) as Hleft.
    pose proof (elements_length_nodes m2) as Hright.
    apply time_of_nat_le in Hleft. apply time_of_nat_le in Hright.
    unfold c_trie. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma T_existsb_le : forall A (f : A -> bool) T_f m k,
    ((forall a, T_f a <= k) ->
    T_existsb f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A f T_f m k Hcallback.
    pose proof (T_forall2_le A unit (fun a _ => negb (f a))
      (fun a _ => 1 + (T_f a + 1))%N m empty (k + 2)%N
      ltac:(intros a b; pose proof (Hcallback a); time_cbn; nia)) as Hcheck.
    unfold k_check in Hcheck. unfold c_trie.
    time_unfold @T_existsb. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Lemma T_map_le : forall A B (f : A -> B) T_f m k,
    ((forall a, T_f a <= k) ->
    T_map f T_f m <= c_trie * (k + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A B f T_f m k Hcallback.
    pose proof (T_filter_map_le A B (fun a => Some (f a)) (fun a => 1 + T_f a)%N
      m (k + 1)%N ltac:(intro a; pose proof (Hcallback a); time_cbn; nia)) as Hfilter.
    unfold k_filter in Hfilter. unfold c_trie.
    time_unfold @T_map. time_simpl.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Local Lemma merging_filter_sum {A B} (f : A -> option B) T_f (m : t A) :
    (T_filter_map f (fun a => 1 + T_f a)%N m <=
      16 * (N.of_nat (nodes m + 1) +
        fold_right N.add 0 (List.map (fun ka => T_f (snd ka)) (elements m))))%N.
  Proof.
    pose proof (@T_filter_map_sum_le A B f (fun a => 1 + T_f a)%N m) as Hfilter.
    cbn beta in Hfilter.
    rewrite (merging_sum_add (fun ka => T_f (snd ka)) (elements m)) in Hfilter.
    pose proof (elements_length_nodes m) as Hbindings.
    apply time_of_nat_le in Hbindings. unfold k_filter in Hfilter.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.

  Lemma T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Proof.
    intros A B C f T_f m1 m2. time_unfold @T_merge.
    lazymatch goal with
    | |- context [T_merge_with ?g ?T_g ?fl ?T_fl ?fr ?T_fr ?m ?u] =>
      pose proof (@T_merge_with_sum_le A B C g T_g fl T_fl fr T_fr m u 16 16) as Hmerge
    end.
    specialize (Hmerge
      (fun m => @merging_filter_sum A C (fun a => f (Some a) None)
        (fun a => T_f (Some a) None) m)
      (fun m => @merging_filter_sum B C (fun b => f None (Some b))
        (fun b => T_f None (Some b)) m)).
    unfold k_merge in Hmerge. unfold c_trie.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  Local Lemma checking_sum_bound {X} (xs : list X) (w v : X -> N) c :
    (forall x, In x xs -> (w x <= c + v x)%N) ->
    (fold_right N.add 0 (List.map w xs) <= c * N.of_nat (length xs) +
      fold_right N.add 0 (List.map v xs))%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound.
    - cbn [List.map fold_right length]. nia.
    - pose proof (Hbound x (or_introl eq_refl)) as Hhead.
      assert (Htail : forall y, In y xs -> (w y <= c + v y)%N).
      { intros y Hin. apply Hbound. now right. }
      specialize (IH Htail). cbn [List.map fold_right length].
      rewrite Nat2N.inj_succ. nia.
  Qed.

  (** Callback costs are charged at the corresponding keys of either input. *)
  Lemma T_forall2b_sum_le : forall A B
      (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_trie *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (get p m1) (get p m2))
         (List.map fst (elements m1) ++ List.map fst (elements m2)))))%N.
  Proof.
    intros A B f T_f m1 m2.
    pose proof (T_forall2b_sum f T_f m1 m2) as Hcheck.
    unfold c_trie. nia.
  Qed.

  Lemma T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_trie * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match get p m with Some a => T_f a | None => 0 end) (List.map fst (elements m)))))%N.
  Proof.
    intros A f T_f m.
    time_unfold @T_existsb. time_simpl.
    lazymatch goal with
    | |- context [T_forall2 ?g ?T_g ?tr ?u] =>
      pose proof (@T_forall2_sum_le A unit g T_g tr u) as Hcheck
    end.
    assert (Hsum : (fold_right N.add 0
      (List.map (fun ka => 1 + (T_f (snd ka) + 1)) (elements m)) <=
      2 * N.of_nat (length (elements m)) + fold_right N.add 0
        (List.map (fun ka => match get (fst ka) m with
          | Some a => T_f a | None => 0 end) (elements m)))%N).
    { apply checking_sum_bound. intros [p a] Hin.
      apply elements_spec in Hin. cbn [fst snd]. rewrite Hin. lia. }
    pose proof (elements_length_nodes m) as Hbindings.
    apply time_of_nat_le in Hbindings. rewrite map_map.
    unfold k_check in Hcheck. unfold c_trie.
    rewrite !Nat2N.inj_add in *. time_cbn_all. nia.
  Qed.
  Lemma T_fold_sum_le : forall A B (f : B -> positive -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_trie * (N.of_nat (nodes m + 1) + N.of_nat (weight m) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof.
    intros A B f T_f m b.
    change (T_fold f T_f m b <= c_trie *
      (N.of_nat (nodes m + 1) + N.of_nat (weight m) + fold_work f T_f m b))%N.
    pose proof (T_fold_work_le A B f T_f m b) as Hfold.
    rewrite weight_def. unfold c_trie, k_fold in *.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Lookup time is linear in the number of key bits. *)
  Lemma get_complexity : forall A,
    T_get (A := A) p m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, m).
  Proof.
    intro A. exists c_trie. intros [p m] _. cbn [fst snd].
    pose proof (T_get_le A p m) as Hget.
    now rewrite Nat2N.inj_add in Hget.
  Qed.

  (** The key [2^k] has [k + 1] bits. *)
  Lemma size_nat_iter_xO : forall k, Pos.size_nat (Nat.iter k xO 1%positive) = S k.
  Proof.
    induction k as [| k IH]; [reflexivity |].
    change (S (Pos.size_nat (Nat.iter k xO 1%positive)) = S (S k)).
    rewrite IH. reflexivity.
  Qed.

  (** A stored key of every length is read to its end, so the worst case of lookup is Θ of the
      key length. *)
  Lemma get_worst_complexity : forall A (a : A),
    T_get (A := A) p m ∈ Θ_worst(N.of_nat (Pos.size_nat p)) for (p, m).
  Proof.
    intros A a. split.
    - exact (get_complexity A).
    - exists 1%N. intros n.
      set (key := Nat.iter (N.to_nat n) xO 1%positive).
      exists (key, set key a empty). cbn [fst snd].
      pose proof (size_nat_iter_xO (N.to_nat n)) as Hsize.
      fold key in Hsize.
      pose proof (T_get_hit_ge A key (set key a empty)) as Hhit.
      rewrite get_set_same in Hhit.
      specialize (Hhit ltac:(discriminate)).
      rewrite Hsize in Hhit |- *. repeat split; lia.
  Qed.

  (** Setting reads and rebuilds the whole key path, so its time is Θ of the key length. *)
  Lemma set_complexity : forall A,
    T_set (A := A) p a m ∈ Θ(N.of_nat (Pos.size_nat p)) for (p, a, m).
  Proof.
    intro A. split.
    - exists c_trie. intros [[p a] m] _. cbn [fst snd].
      pose proof (T_set_le A p a m) as Hset.
      now rewrite Nat2N.inj_add in Hset.
    - exists 1%N. intros [[p a] m] _. cbn [fst snd].
      pose proof (T_set_ge A p a m) as Hlower.
      lia.
  Qed.

  (** Removal time is linear in the number of key bits. *)
  Lemma remove_complexity : forall A,
    T_remove (A := A) p m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, m).
  Proof.
    intro A. exists c_trie. intros [p m] _. cbn [fst snd].
    pose proof (T_remove_le A p m) as Hremove.
    now rewrite Nat2N.inj_add in Hremove.
  Qed.

  (** A bounded-callback merge is linear in the combined input skeletons. *)
  Lemma merge_complexity : forall A B C,
    T_merge (A := A) (B := B) (C := C) f T_f m1 m2 ∈
      𝑂(((k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N)
      for (f, T_f, k, m1, m2) | forall a b, (T_f a b <= k)%N.
  Proof.
    intros A B C. exists c_trie.
    intros [[[[f T_f] k] m1] m2] Hcallback.
    change (T_merge f T_f m1 m2 <=
      c_trie * ((k + 1) * N.of_nat (nodes m1 + nodes m2 + 1) + 1))%N.
    pose proof (T_merge_le A B C f T_f m1 m2 k Hcallback) as Hmerge.
    nia.
  Qed.

  (** A bounded relation check is linear in the combined input skeletons. *)
  Lemma forall2b_complexity : forall A B,
    T_forall2b (A := A) (B := B) f T_f m1 m2 ∈
      𝑂(((k + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N)
      for (f, T_f, k, m1, m2) | forall a b, (T_f a b <= k)%N.
  Proof.
    intros A B. exists c_trie.
    intros [[[[f T_f] k] m1] m2] Hcallback.
    change (T_forall2b f T_f m1 m2 <=
      c_trie * ((k + 1) * N.of_nat (nodes m1 + nodes m2 + 1) + 1))%N.
    pose proof (T_forall2b_le A B f T_f m1 m2 k Hcallback) as Hcheck.
    nia.
  Qed.

  (** A bounded fold pays for the skeleton and the bits of its enumerated keys. *)
  Lemma fold_complexity : forall A B,
    T_fold (A := A) (B := B) f T_f m b ∈
      𝑂(((k + 1) * N.of_nat (nodes m + 1) + N.of_nat (weight m))%N)
      for (f, T_f, k, m, b) | forall acc p a, (T_f acc p a <= k)%N.
  Proof.
    intros A B. exists c_trie.
    intros [[[[f T_f] k] m] b] Hcallback.
    change (T_fold f T_f m b <=
      c_trie * ((k + 1) * N.of_nat (nodes m + 1) + N.of_nat (weight m) + 1))%N.
    pose proof (T_fold_le A B f T_f m b k Hcallback) as Hfold.
    nia.
  Qed.

  (** Enumeration time is linear in the total binding weight. *)
  Lemma elements_complexity : forall A,
    T_elements (A := A) m ∈ 𝑂(N.of_nat (weight m)) for m.
  Proof.
    intro A. exists c_trie. intros m _.
    pose proof (T_elements_le A m) as Helements.
    now rewrite Nat2N.inj_add in Helements.
  Qed.

  (** Value folding charges callbacks in enumeration order without constructing keys. *)
  Local Ltac folding_pose_values_child IH child :=
    lazymatch goal with
    | |- context [T_fold_values_ne ?f ?Tf child ?acc] =>
      let Hchild := fresh "Hfold" in pose proof (IH acc) as Hchild
    end.

  Local Lemma folding_values_ne_sum {A B} (f : B -> A -> B) T_f (n : ne A) :
    forall b, (T_fold_values_ne f T_f n b <= 4 * N.of_nat (nodes_ne n) +
      folding_work (fun acc kv => f acc (snd kv)) (fun acc kv => T_f acc (snd kv))
        (entries_ne n) b)%N.
  Proof.
    induction n; intro b; time_unfold @T_fold_values_ne; time_simpl.
    all: tryif (let H := type of IHn in idtac)
      then folding_pose_values_child IHn n else idtac.
    all: tryif (let H := type of IHn1 in idtac)
      then folding_pose_values_child IHn1 n1 else idtac.
    all: tryif (let H := type of IHn2 in idtac)
      then folding_pose_values_child IHn2 n2 else idtac.
    all: cbn [nodes_ne entries_ne]; rewrite ?folding_work_app.
    all: cbn [folding_work fold_left fst snd].
    all: rewrite ?folding_work_map, ?folding_left_map.
    all: rewrite ?folding_values_state in *; cbn [fst snd] in *.
    all: rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ in *; time_cbn_all; nia.
  Qed.

  Lemma T_fold_values_sum_le : forall A B (f : B -> A -> B) T_f m b,
    (T_fold_values f T_f m b <= c_trie * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (snd ka), snd bw + T_f (fst bw) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof.
    intros A B f T_f m b. rewrite elements_entries. destruct m as [|n].
    - time_unfold @T_fold_values. unfold c_trie. time_cbn. nia.
    - pose proof (folding_values_ne_sum f T_f n b) as Hfold.
      time_unfold @T_fold_values. cbn [entries nodes].
      rewrite (folding_work_left (fun acc kv => f acc (snd kv))
        (fun acc kv => T_f acc (snd kv)) (entries_ne n) b 0%N).
      unfold c_trie. rewrite !Nat2N.inj_add. time_cbn_all. nia.
  Qed.
End PTrieT.
