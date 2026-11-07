(** * Sharing and skipping trie merges

    A shared traversal delegates one-sided subtrees to operation-specific handlers.
    For example, intersection with an empty trie never visits the other trie's descendants.
    Builds on: BaseTrie and CostMonad. *)

From Stdlib Require Import NArith Arith List Bool Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseTrie.
Import Cost.Notations.

Module TrieMerge.

(** Rebuilding retains the complete charges of its three component computations. *)
Definition rebuild_c {A} (l : Cost.t (Trie.t A)) (o : Cost.t (option A))
    (r : Cost.t (Trie.t A)) : Cost.t (Trie.t A) :=
  let* l' := l in
  let* o' := o in
  let* r' := r in Cost.ret (Trie.node l' o' r').

(** Optional filtering invokes the callback only for a present binding. *)
Definition filter_value_c {A B} (f : A -> Cost.t (option B)) (o : option A) :=
  match o with
  | None => Cost.ret None
  | Some v => Cost.step ;; f v
  end.

(** Filtering charges every visited skeleton node and every callback invocation. *)
Fixpoint filter_ne_c {A B} (f : A -> Cost.t (option B)) (n : Trie.ne A)
    : Cost.t (Trie.t B) :=
  Cost.step ;;
  match n with
  | Trie.N001 r =>
    rebuild_c (Cost.ret Trie.Empty) (Cost.ret None) (filter_ne_c f r)
  | Trie.N010 v =>
    rebuild_c (Cost.ret Trie.Empty) (filter_value_c f (Some v)) (Cost.ret Trie.Empty)
  | Trie.N011 v r =>
    rebuild_c (Cost.ret Trie.Empty) (filter_value_c f (Some v)) (filter_ne_c f r)
  | Trie.N100 l =>
    rebuild_c (filter_ne_c f l) (Cost.ret None) (Cost.ret Trie.Empty)
  | Trie.N101 l r =>
    rebuild_c (filter_ne_c f l) (Cost.ret None) (filter_ne_c f r)
  | Trie.N110 l v =>
    rebuild_c (filter_ne_c f l) (filter_value_c f (Some v)) (Cost.ret Trie.Empty)
  | Trie.N111 l v r =>
    rebuild_c (filter_ne_c f l) (filter_value_c f (Some v)) (filter_ne_c f r)
  end.

Definition filter_map_c {A B} (f : A -> Cost.t (option B)) (tr : Trie.t A) :=
  match tr with
  | Trie.Empty => Cost.ret Trie.Empty
  | Trie.Nodes n => filter_ne_c f n
  end.

Definition filter_map {A B} (f : A -> option B) (tr : Trie.t A) :=
  Cost.value (filter_map_c (Cost.lift (fun _ => 1%N) f) tr).

(** The value of filtering a smart node is filtering each present component. *)
Theorem filter_node {A B} (f : A -> Cost.t (option B)) (l r : Trie.t A) o :
  Cost.value (filter_map_c f (Trie.node l o r)) =
  Trie.node (Cost.value (filter_map_c f l))
    (match o with Some v => Cost.value (f v) | None => None end)
    (Cost.value (filter_map_c f r)).
Proof.
  destruct l, o, r; reflexivity.
Qed.

(** Filtering acts independently at each lookup. *)
Theorem get_filter {A B} (f : A -> Cost.t (option B)) (tr : Trie.t A) p :
  Trie.get p (Cost.value (filter_map_c f tr)) =
  match Trie.get p tr with Some a => Cost.value (f a) | None => None end.
Proof.
  revert p. induction tr as [|l o r IHl IHr] using Trie.node_ind; intro p.
  - rewrite Trie.get_empty. apply Trie.get_empty.
  - rewrite filter_node, !Trie.get_node. destruct p; auto.
Qed.

(** Costed filtering depends only on callback results. *)
Theorem filter_map_c_value {A B} (f : A -> Cost.t (option B)) (tr : Trie.t A) :
  Cost.value (filter_map_c f tr) = filter_map (fun v => Cost.value (f v)) tr.
Proof.
  apply Trie.extensionality. intro p. unfold filter_map.
  rewrite !get_filter. destruct (Trie.get p tr); reflexivity.
Qed.

Definition map_c {A B} (f : A -> Cost.t B) (tr : Trie.t A) :=
  filter_map_c (fun v => Cost.map (@Some B) (f v)) tr.

Definition map {A B} (f : A -> B) (tr : Trie.t A) :=
  Cost.value (map_c (Cost.lift (fun _ => 1%N) f) tr).

(** Mapping retains support and maps every present value. *)
Theorem get_map {A B} (f : A -> Cost.t B) (tr : Trie.t A) p :
  Trie.get p (Cost.value (map_c f tr)) =
    option_map (fun v => Cost.value (f v)) (Trie.get p tr).
Proof.
  unfold map_c. rewrite get_filter. destruct (Trie.get p tr); reflexivity.
Qed.

(** Merging charges the optional callback's invocation and keeps all its callee ticks. *)
Definition merge_value_c {A B C}
    (f : option A -> option B -> Cost.t (option C)) a b :=
  Cost.step ;; f a b.

(** Each shared node recurses only on children present in the first operand. *)
Fixpoint merge_ne_c {A B C} (f : option A -> option B -> Cost.t (option C))
    (only_l : Trie.t A -> Cost.t (Trie.t C))
    (only_r : Trie.t B -> Cost.t (Trie.t C)) (n : Trie.ne A) (tr : Trie.t B)
    : Cost.t (Trie.t C) :=
  Cost.step ;;
  match tr with
  | Trie.Empty => only_l (Trie.Nodes n)
  | Trie.Nodes _ =>
    match n with
    | Trie.N001 r =>
      rebuild_c (only_r (Trie.left tr)) (merge_value_c f None (Trie.value tr))
        (merge_ne_c f only_l only_r r (Trie.right tr))
    | Trie.N010 v =>
      rebuild_c (only_r (Trie.left tr)) (merge_value_c f (Some v) (Trie.value tr))
        (only_r (Trie.right tr))
    | Trie.N011 v r =>
      rebuild_c (only_r (Trie.left tr)) (merge_value_c f (Some v) (Trie.value tr))
        (merge_ne_c f only_l only_r r (Trie.right tr))
    | Trie.N100 l =>
      rebuild_c (merge_ne_c f only_l only_r l (Trie.left tr))
        (merge_value_c f None (Trie.value tr)) (only_r (Trie.right tr))
    | Trie.N101 l r =>
      rebuild_c (merge_ne_c f only_l only_r l (Trie.left tr))
        (merge_value_c f None (Trie.value tr))
        (merge_ne_c f only_l only_r r (Trie.right tr))
    | Trie.N110 l v =>
      rebuild_c (merge_ne_c f only_l only_r l (Trie.left tr))
        (merge_value_c f (Some v) (Trie.value tr)) (only_r (Trie.right tr))
    | Trie.N111 l v r =>
      rebuild_c (merge_ne_c f only_l only_r l (Trie.left tr))
        (merge_value_c f (Some v) (Trie.value tr))
        (merge_ne_c f only_l only_r r (Trie.right tr))
    end
  end.

Definition merge_c {A B C} (f : option A -> option B -> Cost.t (option C))
    (only_l : Trie.t A -> Cost.t (Trie.t C))
    (only_r : Trie.t B -> Cost.t (Trie.t C)) (tr : Trie.t A) (u : Trie.t B) :=
  match tr with
  | Trie.Empty => Cost.step ;; only_r u
  | Trie.Nodes n => merge_ne_c f only_l only_r n u
  end.

(** Correct one-sided handlers make merging pointwise at every key. *)
Theorem get_merge {A B C} (f : option A -> option B -> Cost.t (option C))
    only_l only_r :
  (forall p tr, Trie.get p (Cost.value (only_l tr)) =
    Cost.value (f (Trie.get p tr) None)) ->
  (forall p tr, Trie.get p (Cost.value (only_r tr)) =
    Cost.value (f None (Trie.get p tr))) ->
  forall p tr u, Trie.get p (Cost.value (merge_c f only_l only_r tr u)) =
    Cost.value (f (Trie.get p tr) (Trie.get p u)).
Proof.
  intros Hl Hr p [|n] u.
  - cbn [merge_c]. autorewrite with galois_cost. rewrite Trie.get_empty. apply Hr.
  - revert p u.
    induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
      intros p [|other].
    all: try (cbn [merge_c merge_ne_c]; autorewrite with galois_cost;
      rewrite Trie.get_empty; apply Hl).
    all: try (cbn [merge_c] in IHl); try (cbn [merge_c] in IHr).
    all: destruct p; cbn [merge_c merge_ne_c];
      autorewrite with galois_cost; unfold rebuild_c, merge_value_c;
      autorewrite with galois_cost; rewrite Trie.get_node;
      match goal with
      | |- _ = Cost.value (?callback (Trie.get ?p ?tr) _) =>
        rewrite (Trie.get_equation p tr)
      end;
      rewrite (Trie.get_equation _ (Trie.Nodes other));
      cbn [Trie.left Trie.right Trie.value];
      rewrite ?IHl, ?IHr, ?Hr, ?Trie.get_empty; reflexivity.
Qed.

(** General combination transforms one-sided entries as well as shared entries. *)
Definition combine_c {A B C} (f : option A -> option B -> Cost.t (option C))
    (tr : Trie.t A) (u : Trie.t B) :=
  merge_c f (filter_map_c (fun a => f (Some a) None))
    (filter_map_c (fun b => f None (Some b))) tr u.

Definition combine {A B C} (f : option A -> option B -> option C)
    (tr : Trie.t A) (u : Trie.t B) :=
  Cost.value (combine_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) tr u).

(** Combination is pointwise when the callback cannot invent absent keys. *)
Theorem get_combine {A B C} (f : option A -> option B -> Cost.t (option C))
    (tr : Trie.t A) (u : Trie.t B) p :
  Cost.value (f None None) = None ->
  Trie.get p (Cost.value (combine_c f tr u)) =
    Cost.value (f (Trie.get p tr) (Trie.get p u)).
Proof.
  intro Hnone. unfold combine_c. apply get_merge; intros q t;
    rewrite get_filter; destruct (Trie.get q t); congruence.
Qed.

Local Lemma filter_value_ext {A B} (f g : A -> Cost.t (option B)) tr :
  (forall a, Cost.value (f a) = Cost.value (g a)) ->
  Cost.value (filter_map_c f tr) = Cost.value (filter_map_c g tr).
Proof.
  intro Hfg. apply Trie.extensionality. intro p. rewrite !get_filter.
  destruct (Trie.get p tr); auto.
Qed.

(** The merge result depends only on callback and one-sided handler values. *)
Theorem merge_value_ext {A B C}
    (f g : option A -> option B -> Cost.t (option C))
    (fl gl : Trie.t A -> Cost.t (Trie.t C))
    (fr gr : Trie.t B -> Cost.t (Trie.t C)) tr u :
  (forall a b, Cost.value (f a b) = Cost.value (g a b)) ->
  (forall t, Cost.value (fl t) = Cost.value (gl t)) ->
  (forall t, Cost.value (fr t) = Cost.value (gr t)) ->
  Cost.value (merge_c f fl fr tr u) = Cost.value (merge_c g gl gr tr u).
Proof.
  intros Hfg Hl Hr. destruct tr as [|n].
  - apply Hr.
  - revert u. induction n; intros [|other]; cbn [merge_c merge_ne_c];
      autorewrite with galois_cost; try apply Hl.
    all: unfold rebuild_c, merge_value_c; autorewrite with galois_cost;
      cbn [merge_c] in *; rewrite ?IHn, ?IHn1, ?IHn2, ?Hfg, ?Hl, ?Hr; reflexivity.
Qed.

(** Costed combination depends only on callback values, including on empty inputs. *)
Theorem combine_c_value {A B C} (f : option A -> option B -> Cost.t (option C))
    (tr : Trie.t A) (u : Trie.t B) :
  Cost.value (combine_c f tr u) = combine (fun a b => Cost.value (f a b)) tr u.
Proof.
  unfold combine, combine_c. apply merge_value_ext.
  - intros a b. reflexivity.
  - intro t. apply filter_value_ext. intro a. reflexivity.
  - intro t. apply filter_value_ext. intro b. reflexivity.
Qed.

Definition union_opt_c {A} (f : A -> A -> Cost.t A) (a b : option A) :=
  match a, b with
  | Some x, Some y => Cost.map (@Some A) (f x y)
  | Some x, None => Cost.ret (Some x)
  | None, Some y => Cost.ret (Some y)
  | None, None => Cost.ret None
  end.

Definition inter_opt_c {A B C} (f : A -> B -> Cost.t C) (a : option A) (b : option B) :=
  match a, b with
  | Some x, Some y => Cost.map (@Some C) (f x y)
  | _, _ => Cost.ret None
  end.

Definition diff_opt {A B} (a : option A) (b : option B) :=
  match b with
  | None => a
  | Some _ => None
  end.

(** Union returns each one-sided subtree unchanged. *)
Definition union_with_c {A} (f : A -> A -> Cost.t A) (tr u : Trie.t A) :=
  merge_c (union_opt_c f) Cost.ret Cost.ret tr u.

Definition union_with {A} (f : A -> A -> A) (tr u : Trie.t A) :=
  Cost.value (union_with_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) tr u).

(** Intersection immediately discards either one-sided subtree. *)
Definition inter_with_c {A B C} (f : A -> B -> Cost.t C)
    (tr : Trie.t A) (u : Trie.t B) :=
  merge_c (inter_opt_c f) (fun _ => Cost.ret Trie.Empty)
    (fun _ => Cost.ret Trie.Empty) tr u.

Definition inter_with {A B C} (f : A -> B -> C) (tr : Trie.t A) (u : Trie.t B) :=
  Cost.value (inter_with_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) tr u).

(** Difference shares left-only subtrees and discards right-only subtrees. *)
Definition diff_c {A B} (tr : Trie.t A) (u : Trie.t B) :=
  merge_c (fun a b => Cost.ret (diff_opt a b)) Cost.ret
    (fun _ => Cost.ret Trie.Empty) tr u.

Definition diff {A B} (tr : Trie.t A) (u : Trie.t B) := Cost.value (diff_c tr u).

(** Union lookup retains one-sided values and combines the shared values. *)
Theorem union_get {A} (f : A -> A -> Cost.t A) (tr u : Trie.t A) p :
  Trie.get p (Cost.value (union_with_c f tr u)) =
    Cost.value (union_opt_c f (Trie.get p tr) (Trie.get p u)).
Proof.
  apply get_merge; intros q t; rewrite Cost.value_ret;
    destruct (Trie.get q t); reflexivity.
Qed.

(** Intersection lookup is present exactly when both inputs are present. *)
Theorem inter_get {A B C} (f : A -> B -> Cost.t C) (tr : Trie.t A) (u : Trie.t B) p :
  Trie.get p (Cost.value (inter_with_c f tr u)) =
    Cost.value (inter_opt_c f (Trie.get p tr) (Trie.get p u)).
Proof.
  apply get_merge; intros q t; rewrite Cost.value_ret, Trie.get_empty;
    destruct (Trie.get q t); reflexivity.
Qed.

(** Difference lookup retains precisely the left-only values. *)
Theorem diff_get {A B} (tr : Trie.t A) (u : Trie.t B) p :
  Trie.get p (diff tr u) = diff_opt (Trie.get p tr) (Trie.get p u).
Proof.
  apply (get_merge (fun a b => Cost.ret (diff_opt a b)) Cost.ret
    (fun _ => Cost.ret Trie.Empty)); intros q t;
    rewrite Cost.value_ret; try rewrite Trie.get_empty;
    destruct (Trie.get q t); reflexivity.
Qed.

(** Testing an absent left binding invokes no callback. *)
Definition test_value_c {A B} (rel : A -> option B -> Cost.t bool)
    (a : option A) (b : option B) :=
  match a with
  | None => Cost.ret true
  | Some v => Cost.step ;; rel v b
  end.

(** Conjunction evaluates its second computation only after a successful first test. *)
Definition and_c (a : Cost.t bool) (b : unit -> Cost.t bool) :=
  let* yes := a in if yes then b tt else Cost.ret false.

Fixpoint forall2_ne_c {A B} (rel : A -> option B -> Cost.t bool)
    (n : Trie.ne A) (tr : Trie.t B) : Cost.t bool :=
  Cost.step ;;
  match n with
  | Trie.N001 r => forall2_ne_c rel r (Trie.right tr)
  | Trie.N010 v => test_value_c rel (Some v) (Trie.value tr)
  | Trie.N011 v r =>
    and_c (test_value_c rel (Some v) (Trie.value tr))
      (fun _ => forall2_ne_c rel r (Trie.right tr))
  | Trie.N100 l => forall2_ne_c rel l (Trie.left tr)
  | Trie.N101 l r =>
    and_c (forall2_ne_c rel l (Trie.left tr))
      (fun _ => forall2_ne_c rel r (Trie.right tr))
  | Trie.N110 l v =>
    and_c (forall2_ne_c rel l (Trie.left tr))
      (fun _ => test_value_c rel (Some v) (Trie.value tr))
  | Trie.N111 l v r =>
    and_c (forall2_ne_c rel l (Trie.left tr)) (fun _ =>
      and_c (test_value_c rel (Some v) (Trie.value tr))
        (fun _ => forall2_ne_c rel r (Trie.right tr)))
  end.

(** Relational checking traverses the first operand and stops at its first rejected binding. *)
Definition forall2_c {A B} (rel : A -> option B -> Cost.t bool)
    (tr : Trie.t A) (u : Trie.t B) :=
  match tr with
  | Trie.Empty => Cost.ret true
  | Trie.Nodes n => forall2_ne_c rel n u
  end.

Definition forall2 {A B} (rel : A -> option B -> bool) (tr : Trie.t A) (u : Trie.t B) :=
  Cost.value (forall2_c (fun a b => Cost.lift (fun _ => 1%N) (rel a) b) tr u).

Local Lemma value_and_c a b :
  Cost.value (and_c a b) = (Cost.value a && Cost.value (b tt))%bool.
Proof.
  unfold and_c. autorewrite with galois_cost. destruct (Cost.value a); reflexivity.
Qed.

(** Relational testing of a node checks its components in enumeration order. *)
Theorem forall2_node {A B} (rel : A -> option B -> Cost.t bool)
    (l r : Trie.t A) o (u : Trie.t B) :
  Cost.value (forall2_c rel (Trie.node l o r) u) =
    (Cost.value (forall2_c rel l (Trie.left u)) &&
      (Cost.value (test_value_c rel o (Trie.value u)) &&
        Cost.value (forall2_c rel r (Trie.right u))))%bool.
Proof.
  destruct l, o, r; cbn [Trie.node forall2_c forall2_ne_c];
    autorewrite with galois_cost; rewrite ?value_and_c;
    cbn [test_value_c]; autorewrite with galois_cost;
    rewrite ?andb_true_r; reflexivity.
Qed.

(** The checker accepts precisely when all bindings in its first operand pass. *)
Theorem forall2_spec {A B} (rel : A -> option B -> Cost.t bool)
    (tr : Trie.t A) (u : Trie.t B) :
  Cost.value (forall2_c rel tr u) = true <->
  forall p a, Trie.get p tr = Some a -> Cost.value (rel a (Trie.get p u)) = true.
Proof.
  revert u. induction tr as [|l o r IHl IHr] using Trie.node_ind; intro u.
  - split.
    + intros _ p a Hget. rewrite Trie.get_empty in Hget. discriminate.
    + reflexivity.
  - rewrite forall2_node, !andb_true_iff, IHl, IHr.
    split.
    + intros [Hl [Ho Hr]] p a Hget. rewrite Trie.get_node in Hget.
      destruct p; rewrite Trie.get_equation; [apply Hr|apply Hl|]; try exact Hget.
      subst o. exact Ho.
    + intro Htest. split.
      * intros p a Hget. apply (Htest (xO p) a). rewrite Trie.get_node. exact Hget.
      * split.
        -- destruct o as [a|]; [apply (Htest xH a); apply Trie.get_node|reflexivity].
        -- intros p a Hget. apply (Htest (xI p) a). rewrite Trie.get_node. exact Hget.
Qed.

(** Callback-result agreement gives the same relational test result. *)
Theorem forall2_c_value {A B} (rel : A -> option B -> Cost.t bool)
    (tr : Trie.t A) (u : Trie.t B) :
  Cost.value (forall2_c rel tr u) = forall2 (fun a b => Cost.value (rel a b)) tr u.
Proof.
  apply eq_true_iff_eq. unfold forall2. rewrite !forall2_spec. reflexivity.
Qed.

(** Equality checks both supports and keeps all charges of reached comparison callbacks. *)
Definition beq_c {A} (eq : A -> A -> Cost.t bool) (tr u : Trie.t A) :=
  let test := fun a b =>
    match b with
    | None => Cost.ret false
    | Some b => eq a b
    end in
  and_c (forall2_c test tr u) (fun _ => forall2_c test u tr).

Definition beq {A} (eq : A -> A -> bool) (tr u : Trie.t A) :=
  Cost.value (beq_c (fun a b => Cost.lift (fun _ => 1%N) (eq a) b) tr u).

(** A code-and-value list specifies traversal order without being used by executable traversals. *)
Fixpoint entries_ne {A} (n : Trie.ne A) : list (positive * A) :=
  match n with
  | Trie.N001 r => List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
  | Trie.N010 v => (xH, v) :: nil
  | Trie.N011 v r =>
    (xH, v) :: List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
  | Trie.N100 l => List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l)
  | Trie.N101 l r =>
    List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++
      List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
  | Trie.N110 l v =>
    List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++ (xH, v) :: nil
  | Trie.N111 l v r =>
    List.map (fun pv => (xO (fst pv), snd pv)) (entries_ne l) ++
      (xH, v) :: List.map (fun pv => (xI (fst pv), snd pv)) (entries_ne r)
  end.

Definition entries {A} (tr : Trie.t A) :=
  match tr with
  | Trie.Empty => nil
  | Trie.Nodes n => entries_ne n
  end.

(** Emission charges path construction and the callback's complete invocation. *)
Definition emit_c {A B} (f : B -> positive -> A -> Cost.t B)
    (path : positive -> Cost.t positive) (b : B) (v : A) :=
  let* p := path xH in Cost.step ;; f b p v.

(** A path extension charges one bit when its accumulated path is materialized. *)
Definition extend_c (bit : positive -> positive) (path : positive -> Cost.t positive) p :=
  Cost.step ;; path (bit p).

Fixpoint fold_ne_c {A B} (f : B -> positive -> A -> Cost.t B)
    (path : positive -> Cost.t positive) (n : Trie.ne A) (b : B) : Cost.t B :=
  Cost.step ;;
  match n with
  | Trie.N001 r => fold_ne_c f (extend_c xI path) r b
  | Trie.N010 v => emit_c f path b v
  | Trie.N011 v r =>
    let* b' := emit_c f path b v in fold_ne_c f (extend_c xI path) r b'
  | Trie.N100 l => fold_ne_c f (extend_c xO path) l b
  | Trie.N101 l r =>
    let* b' := fold_ne_c f (extend_c xO path) l b in
    fold_ne_c f (extend_c xI path) r b'
  | Trie.N110 l v =>
    let* b' := fold_ne_c f (extend_c xO path) l b in emit_c f path b' v
  | Trie.N111 l v r =>
    let* b' := fold_ne_c f (extend_c xO path) l b in
    let* b'' := emit_c f path b' v in fold_ne_c f (extend_c xI path) r b''
  end.

Definition fold_path_c {A B} (f : B -> positive -> A -> Cost.t B)
    (path : positive -> Cost.t positive) (tr : Trie.t A) (b : B) :=
  match tr with
  | Trie.Empty => Cost.ret b
  | Trie.Nodes n => fold_ne_c f path n b
  end.

(** Keyed folding accounts for every materialized key bit and every callback. *)
Definition fold_c {A B} (f : B -> positive -> A -> Cost.t B) (tr : Trie.t A) (b : B) :=
  fold_path_c f Cost.ret tr b.

Definition fold {A B} (f : B -> positive -> A -> B) (tr : Trie.t A) (b : B) :=
  Cost.value (fold_c (fun b p v => Cost.lift (fun _ => 1%N) (f b p) v) tr b).

Local Lemma fold_left_map_values {X Y B} (f : B -> Y -> B) (g : X -> Y) xs b :
  List.fold_left f (List.map g xs) b = List.fold_left (fun acc x => f acc (g x)) xs b.
Proof.
  revert b. induction xs as [|x xs IH]; intro b; cbn [List.map fold_left]; auto.
Qed.

(** Keyed folding follows the append-based specification in left-root-right order. *)
Theorem fold_path_entries {A B} (f : B -> positive -> A -> Cost.t B) (tr : Trie.t A) :
  forall path b, Cost.value (fold_path_c f path tr b) =
    List.fold_left (fun acc pv => Cost.value (f acc (Cost.value (path (fst pv))) (snd pv)))
      (entries tr) b.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n; intros path b; cbn [fold_path_c fold_ne_c entries entries_ne];
    autorewrite with galois_cost; unfold emit_c;
    autorewrite with galois_cost; rewrite ?fold_left_app;
    cbn [fold_left]; rewrite ?fold_left_map_values;
    cbn [fst snd]; cbn [fold_path_c entries] in *;
    rewrite ?IHn, ?IHn1, ?IHn2; reflexivity.
Qed.

(** Code-free folding does not construct paths that its callback cannot observe. *)
Fixpoint fold_values_ne_c {A B} (f : B -> A -> Cost.t B) (n : Trie.ne A) (b : B)
    : Cost.t B :=
  Cost.step ;;
  match n with
  | Trie.N001 r => fold_values_ne_c f r b
  | Trie.N010 v => Cost.step ;; f b v
  | Trie.N011 v r =>
    Cost.step ;; let* b' := f b v in fold_values_ne_c f r b'
  | Trie.N100 l => fold_values_ne_c f l b
  | Trie.N101 l r =>
    let* b' := fold_values_ne_c f l b in fold_values_ne_c f r b'
  | Trie.N110 l v =>
    let* b' := fold_values_ne_c f l b in Cost.step ;; f b' v
  | Trie.N111 l v r =>
    let* b' := fold_values_ne_c f l b in
    Cost.step ;; let* b'' := f b' v in fold_values_ne_c f r b''
  end.

Definition fold_values_c {A B} (f : B -> A -> Cost.t B) (tr : Trie.t A) (b : B) :=
  match tr with
  | Trie.Empty => Cost.ret b
  | Trie.Nodes n => fold_values_ne_c f n b
  end.

(** Code-free folding follows the same binding order as keyed folding. *)
Theorem fold_values_entries {A B} (f : B -> A -> Cost.t B) (tr : Trie.t A) :
  forall b, Cost.value (fold_values_c f tr b) =
    List.fold_left (fun acc pv => Cost.value (f acc (snd pv))) (entries tr) b.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n; intro b; cbn [fold_values_c fold_values_ne_c entries entries_ne];
    autorewrite with galois_cost; rewrite ?fold_left_app;
    cbn [fold_left]; rewrite ?fold_left_map_values;
    cbn [fst snd]; cbn [fold_values_c entries] in *;
    rewrite ?IHn, ?IHn1, ?IHn2; reflexivity.
Qed.

(** Enumeration collects keyed bindings in reverse order and reverses them once. *)
Definition elements_c {A} (tr : Trie.t A) :=
  let* rev := fold_c (fun acc p v => Cost.ret ((p, v) :: acc)) tr nil in
  rev_c rev.

Definition elements {A} (tr : Trie.t A) := Cost.value (elements_c tr).

(** Counting bindings uses the code-free traversal. *)
Definition size_c {A} (tr : Trie.t A) :=
  fold_values_c (fun acc _ => Cost.ret (S acc)) tr O.

Definition size {A} (tr : Trie.t A) := Cost.value (size_c tr).

Local Lemma fold_left_pairs {A} (xs acc : list (positive * A)) :
  List.fold_left (fun acc pv => (fst pv, snd pv) :: acc) xs acc = List.rev xs ++ acc.
Proof.
  revert acc. induction xs as [|[p a] xs IH]; intro acc.
  - reflexivity.
  - cbn [fold_left rev fst snd]. rewrite IH, <- app_assoc. reflexivity.
Qed.

(** The executable enumeration agrees with the order specification. *)
Theorem elements_entries {A} (tr : Trie.t A) : elements tr = entries tr.
Proof.
  unfold elements, elements_c. rewrite Cost.value_bind, value_rev_c.
  unfold fold_c. rewrite fold_path_entries.
  change (List.rev (fold_left (fun acc pv => (fst pv, snd pv) :: acc)
    (entries tr) nil) = entries tr).
  rewrite fold_left_pairs, app_nil_r, rev_involutive. reflexivity.
Qed.

(** The keyed fold follows the public element order. *)
Theorem fold_elements {A B} (f : B -> positive -> A -> Cost.t B) (tr : Trie.t A) b :
  Cost.value (fold_c f tr b) =
    List.fold_left (fun acc pv => Cost.value (f acc (fst pv) (snd pv))) (elements tr) b.
Proof.
  rewrite elements_entries. exact (fold_path_entries f tr Cost.ret b).
Qed.

(** Size counts the public enumerated bindings. *)
Theorem size_elements {A} (tr : Trie.t A) : size tr = length (elements tr).
Proof.
  unfold size, size_c. rewrite fold_values_entries, elements_entries.
  generalize (entries tr). intro xs.
  assert (H : forall acc, fold_left (fun acc (_ : positive * A) => S acc) xs acc =
    (length xs + acc)%nat).
  { induction xs as [|x xs IH]; intro acc; cbn [fold_left length].
    - reflexivity.
    - rewrite IH, Nat.add_succ_r. reflexivity. }
  rewrite H, Nat.add_0_r. reflexivity.
Qed.

(** Enumeration exposes the left-root-right code order of a smart node. *)
Theorem elements_node {A} (l r : Trie.t A) o :
  elements (Trie.node l o r) =
    List.map (fun pv => (xO (fst pv), snd pv)) (elements l) ++
    (match o with Some v => (xH, v) :: nil | None => nil end) ++
    List.map (fun pv => (xI (fst pv), snd pv)) (elements r).
Proof.
  rewrite !elements_entries. destruct l, o, r;
    cbn [Trie.node entries entries_ne]; rewrite ?app_nil_r; reflexivity.
Qed.

(** A binding is enumerated exactly when lookup returns it. *)
Theorem elements_spec {A} (tr : Trie.t A) p v :
  In (p, v) (elements tr) <-> Trie.get p tr = Some v.
Proof.
  revert p v. induction tr as [|l o r IHl IHr] using Trie.node_ind; intros p v.
  - rewrite Trie.get_empty, elements_entries. cbn [entries].
    split; [contradiction|discriminate].
  - rewrite elements_node, !in_app_iff, Trie.get_node.
    destruct p.
    + split.
      * intros [Hl|[Ho|Hr]].
        -- apply in_map_iff in Hl as [[q a] [Heq _]]. discriminate Heq.
        -- destruct o; cbn in Ho; intuition discriminate.
        -- apply in_map_iff in Hr as [[q a] [Heq Hin]].
           injection Heq as -> ->. now apply IHr.
      * intro Hget. right. right. apply in_map_iff. exists (p, v).
        split; [reflexivity|now apply IHr].
    + split.
      * intros [Hl|[Ho|Hr]].
        -- apply in_map_iff in Hl as [[q a] [Heq Hin]].
           injection Heq as -> ->. now apply IHl.
        -- destruct o; cbn in Ho; intuition discriminate.
        -- apply in_map_iff in Hr as [[q a] [Heq _]]. discriminate Heq.
      * intro Hget. left. apply in_map_iff. exists (p, v).
        split; [reflexivity|now apply IHl].
    + split.
      * intros [Hl|[Ho|Hr]].
        -- apply in_map_iff in Hl as [[q a] [Heq _]]. discriminate Heq.
        -- destruct o; cbn in Ho; intuition congruence.
        -- apply in_map_iff in Hr as [[q a] [Heq _]]. discriminate Heq.
      * intro Hget. right. left. subst o. now left.
Qed.

(** Trie order compares low bits first and places zero branches before the root. *)
Fixpoint key_lt (p q : positive) : Prop :=
  match p, q with
  | xO p, xO q => key_lt p q
  | xI p, xI q => key_lt p q
  | xO _, xH | xO _, xI _ | xH, xI _ => True
  | _, _ => False
  end.

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

(** Every canonical trie enumerates strictly increasing codes. *)
Theorem elements_sorted {A} (tr : Trie.t A) :
  StronglySorted (fun a b => key_lt (fst a) (fst b)) (elements tr).
Proof.
  induction tr as [|l o r IHl IHr] using Trie.node_ind.
  - rewrite elements_entries. constructor.
  - rewrite elements_node.
    assert (Hl : StronglySorted (fun a b => key_lt (fst a) (fst b))
      (List.map (fun pv => (xO (fst pv), snd pv)) (elements l))).
    { eapply strongly_sorted_map; [|exact IHl]. intros [p a] [q b] Hlt. exact Hlt. }
    assert (Hr : StronglySorted (fun a b => key_lt (fst a) (fst b))
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

(** Enumeration never repeats a code. *)
Theorem elements_nodup {A} (tr : Trie.t A) : NoDup (List.map fst (elements tr)).
Proof.
  pose proof (elements_sorted tr) as Hsort.
  induction Hsort as [|[p a] xs Hsort IH Hforall]; cbn [List.map fst].
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    apply in_map_iff in Hin as [[q b] [Heq Hin]]. cbn [fst] in Heq. subst q.
    rewrite Forall_forall in Hforall. specialize (Hforall (p, b) Hin).
    assert (Hirr : forall p, ~ key_lt p p).
    { intro q. induction q; cbn [key_lt]; assumption || tauto. }
    exact (Hirr p Hforall).
Qed.

End TrieMerge.
