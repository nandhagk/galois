(** * Canonical binary trie code

    Seven nonempty node shapes give finite positive-key maps a canonical representation.
    For example, removing the sole binding collapses its path to the empty trie.
    Builds on: TrieSig and Argent time derivation. *)

From Stdlib Require Import PArith List Bool.
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

  Fixpoint replace {A} (p : positive) (o : option A) (tr : t A) : t A :=
    match p with
    | xH => node (left tr) o (right tr)
    | xO q => node (replace q o (left tr)) (value tr) (right tr)
    | xI q => node (left tr) (value tr) (replace q o (right tr))
    end.

  Definition set {A} p (v : A) tr := replace p (Some v) tr.
  Definition remove {A} p (tr : t A) := replace p None tr.

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

  Definition elements {A} (tr : t A) : list (positive * A) :=
    List.rev (fold (fun acc p v => (p, v) :: acc) tr nil).
End PTrieCode.
