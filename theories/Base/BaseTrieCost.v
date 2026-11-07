(** * Trie traversal costs

    Skeleton nodes measure physical traversal independently of binding cardinality.
    For example, a singleton at a deep key has one binding and many skeleton nodes.
    Builds on: BaseTrie, BaseTrieMerge and CostBound. *)

From Stdlib Require Import NArith Arith List Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseTrie BaseTrieMerge BaseMap.
Import List.ListNotations.

Module TrieCost.

(** The traversal constant covers descent, node reconstruction and callback overhead. *)
Definition trie_k : N := 4.

Fixpoint nodes_ne {A} (n : Trie.ne A) : N :=
  match n with
  | Trie.N001 r => 1 + nodes_ne r
  | Trie.N010 _ => 1
  | Trie.N011 _ r => 1 + nodes_ne r
  | Trie.N100 l => 1 + nodes_ne l
  | Trie.N101 l r => 1 + nodes_ne l + nodes_ne r
  | Trie.N110 l _ => 1 + nodes_ne l
  | Trie.N111 l _ r => 1 + nodes_ne l + nodes_ne r
  end.

(** Physical nodes include branching and unary path nodes without a binding. *)
Definition skeleton_nodes {A} (tr : Trie.t A) : N :=
  match tr with
  | Trie.Empty => 0
  | Trie.Nodes n => nodes_ne n
  end.

(** Weighted overlap counts only nodes at which both operands have a skeleton node. *)
Fixpoint overlap_ne {A B} (w : option A -> option B -> N)
    (n : Trie.ne A) (u : Trie.t B) : N :=
  match u with
  | Trie.Empty => 0
  | Trie.Nodes _ =>
    match n with
    | Trie.N001 r => w None (Trie.value u) + overlap_ne w r (Trie.right u)
    | Trie.N010 v => w (Some v) (Trie.value u)
    | Trie.N011 v r => w (Some v) (Trie.value u) + overlap_ne w r (Trie.right u)
    | Trie.N100 l => w None (Trie.value u) + overlap_ne w l (Trie.left u)
    | Trie.N101 l r =>
      w None (Trie.value u) + overlap_ne w l (Trie.left u) +
        overlap_ne w r (Trie.right u)
    | Trie.N110 l v => w (Some v) (Trie.value u) + overlap_ne w l (Trie.left u)
    | Trie.N111 l v r =>
      w (Some v) (Trie.value u) + overlap_ne w l (Trie.left u) +
        overlap_ne w r (Trie.right u)
    end
  end.

Definition overlap {A B} (w : option A -> option B -> N)
    (tr : Trie.t A) (u : Trie.t B) : N :=
  match tr with
  | Trie.Empty => 0
  | Trie.Nodes n => overlap_ne w n u
  end.

(** Shared nodes concern physical overlap, including a shared node without a binding. *)
Definition shared_nodes {A B} (tr : Trie.t A) (u : Trie.t B) : N :=
  overlap (fun _ _ => 1) tr u.

(** Equal node weights give equal overlap sums without function extensionality. *)
Theorem overlap_ext {A B} (w z : option A -> option B -> N) tr u :
  (forall a b, w a b = z a b) -> overlap w tr u = overlap z tr u.
Proof.
  intro Hweights. destruct tr as [|n]; [reflexivity|]. revert u.
  induction n; intros [|other]; cbn [overlap overlap_ne];
    cbn [overlap] in *; rewrite ?IHn, ?IHn1, ?IHn2, ?Hweights; reflexivity.
Qed.

(** Zero-cost one-sided handlers leave only shared-node overhead and callback work. *)
Theorem sharing_merge_cost {A B C}
    (f : option A -> option B -> Cost.t (option C))
    (fl : Trie.t A -> Cost.t (Trie.t C))
    (fr : Trie.t B -> Cost.t (Trie.t C)) tr u :
  (forall t, Cost.ticks (fl t) = 0) ->
  (forall t, Cost.ticks (fr t) = 0) ->
  (Cost.ticks (TrieMerge.merge_c f fl fr tr u) <=
    1 + 3 * shared_nodes tr u + overlap (fun a b => Cost.ticks (f a b)) tr u)%N.
Proof.
  intros Hl Hr. destruct tr as [|n].
  - cbn [TrieMerge.merge_c]. autorewrite with galois_cost.
    rewrite Hr. reflexivity.
  - revert u. induction n; intros [|other];
      cbn [TrieMerge.merge_c TrieMerge.merge_ne_c];
      autorewrite with galois_cost; try (rewrite Hl; reflexivity).
    all: unfold TrieMerge.rebuild_c, TrieMerge.merge_value_c;
      autorewrite with galois_cost; rewrite ?Hr;
      cbn [TrieMerge.merge_c shared_nodes overlap overlap_ne] in *.
    all: try pose proof (IHn (Trie.left (Trie.Nodes other))) as Hleft.
    all: try pose proof (IHn (Trie.right (Trie.Nodes other))) as Hright.
    all: try pose proof (IHn1 (Trie.left (Trie.Nodes other))) as Hleft.
    all: try pose proof (IHn2 (Trie.right (Trie.Nodes other))) as Hright.
    all: nia.
Qed.

(** Shared physical overlap cannot exceed the first operand's skeleton. *)
Theorem shared_nodes_left {A B} (tr : Trie.t A) (u : Trie.t B) :
  (shared_nodes tr u <= skeleton_nodes tr)%N.
Proof.
  destruct tr as [|n]; [reflexivity|]. revert u.
  induction n; intros [|other]; cbn [shared_nodes overlap overlap_ne skeleton_nodes nodes_ne];
    try solve [lia].
  all: cbn [shared_nodes overlap skeleton_nodes] in *.
  all: try pose proof (IHn (Trie.left (Trie.Nodes other))) as Hleft.
  all: try pose proof (IHn (Trie.right (Trie.Nodes other))) as Hright.
  all: try pose proof (IHn1 (Trie.left (Trie.Nodes other))) as Hleft.
  all: try pose proof (IHn2 (Trie.right (Trie.Nodes other))) as Hright.
  all: lia.
Qed.

(** Shared physical overlap cannot exceed the second operand's skeleton. *)
Theorem shared_nodes_right {A B} (tr : Trie.t A) (u : Trie.t B) :
  (shared_nodes tr u <= skeleton_nodes u)%N.
Proof.
  destruct tr as [|n]; [cbn [shared_nodes overlap]; lia|]. revert u.
  induction n; intros [|other]; cbn [shared_nodes overlap overlap_ne skeleton_nodes];
    try solve [lia].
  all: cbn [shared_nodes overlap skeleton_nodes] in *.
  all: try pose proof (IHn (Trie.left (Trie.Nodes other))) as Hl.
  all: try pose proof (IHn (Trie.right (Trie.Nodes other))) as Hr.
  all: try pose proof (IHn1 (Trie.left (Trie.Nodes other))) as Hl.
  all: try pose proof (IHn2 (Trie.right (Trie.Nodes other))) as Hr.
  all: destruct other; cbn [Trie.left Trie.right skeleton_nodes nodes_ne] in *; lia.
Qed.

(** Callback charges are summed independently of shared-node traversal overhead. *)
Definition callback_weight {A B} (w : A -> B -> N) (a : option A) (b : option B) : N :=
  match a, b with
  | Some x, Some y => w x y
  | _, _ => 0
  end.

(** Union shares one-sided subtrees and retains arbitrary invoked callback charges. *)
Theorem union_with_cost {A} (f : A -> A -> Cost.t A) (tr u : Trie.t A) :
  (Cost.ticks (TrieMerge.union_with_c f tr u) <=
    trie_k * (1 + shared_nodes tr u) +
      overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u)%N.
Proof.
  pose proof (sharing_merge_cost (TrieMerge.union_opt_c f) Cost.ret Cost.ret tr u
    (fun _ => eq_refl) (fun _ => eq_refl)) as H.
  assert (Hw : overlap (fun a b => Cost.ticks (TrieMerge.union_opt_c f a b)) tr u =
    overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u).
  { apply overlap_ext. intros [a|] [b|]; reflexivity. }
  rewrite Hw in H. unfold TrieMerge.union_with_c, trie_k. nia.
Qed.

(** Intersection skips one-sided subtrees and retains arbitrary callback charges. *)
Theorem inter_cost {A B C} (f : A -> B -> Cost.t C) (tr : Trie.t A) (u : Trie.t B) :
  (Cost.ticks (TrieMerge.inter_with_c f tr u) <=
    trie_k * (1 + N.min (skeleton_nodes tr) (skeleton_nodes u)) +
      overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u)%N.
Proof.
  pose proof (sharing_merge_cost (TrieMerge.inter_opt_c f)
    (fun _ => Cost.ret Trie.Empty) (fun _ => Cost.ret Trie.Empty) tr u
    (fun _ => eq_refl) (fun _ => eq_refl)) as H.
  pose proof (shared_nodes_left tr u) as Hl.
  pose proof (shared_nodes_right tr u) as Hr.
  assert (Hw : overlap (fun a b => Cost.ticks (TrieMerge.inter_opt_c f a b)) tr u =
    overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u).
  { apply overlap_ext. intros [a|] [b|]; reflexivity. }
  rewrite Hw in H. unfold TrieMerge.inter_with_c, trie_k.
  pose proof (N.min_glb _ _ _ Hl Hr). nia.
Qed.

(** Difference skips right-only subtrees and shares left-only subtrees in constant time. *)
Theorem diff_cost {A B} (tr : Trie.t A) (u : Trie.t B) :
  (Cost.ticks (TrieMerge.diff_c tr u) <=
    trie_k * (1 + N.min (skeleton_nodes tr) (skeleton_nodes u)))%N.
Proof.
  pose proof (sharing_merge_cost (fun a b => Cost.ret (TrieMerge.diff_opt a b))
    Cost.ret (fun _ => Cost.ret Trie.Empty) tr u
    (fun _ => eq_refl) (fun _ => eq_refl)) as H.
  assert (Hz : overlap (fun (_ : option A) (_ : option B) => 0) tr u = 0).
  { clear H. destruct tr as [|n]; [reflexivity|]. revert u.
    induction n; intros [|other]; cbn [overlap overlap_ne];
      cbn [overlap] in *; rewrite ?IHn, ?IHn1, ?IHn2; reflexivity. }
  change (Cost.ticks (TrieMerge.diff_c tr u) <=
    1 + 3 * shared_nodes tr u + overlap (fun _ _ => 0) tr u)%N in H.
  rewrite Hz in H.
  pose proof (shared_nodes_left tr u) as Hl.
  pose proof (shared_nodes_right tr u) as Hr.
  pose proof (N.min_glb _ _ _ Hl Hr). unfold trie_k. nia.
Qed.

(** Right-operand traversal bounds include the constant cost of each shared-subtree return. *)
Theorem diff_cost_small_right {A B} (tr : Trie.t A) (u : Trie.t B) :
  (Cost.ticks (TrieMerge.diff_c tr u) <= trie_k * (1 + skeleton_nodes u))%N.
Proof.
  pose proof (diff_cost tr u). pose proof (N.le_min_r (skeleton_nodes tr) (skeleton_nodes u)).
  nia.
Qed.

(** Lookup is asymptotically linear in the binary key width for every fixed trie. *)
Theorem get_bigO {A} (tr : Trie.t A) :
  bigO (fun p => N.pos (Pos.size p)) (fun p => Cost.ticks (Trie.get_c p tr)).
Proof.
  exists 1%N. intro p. rewrite Trie.get_cost. lia.
Qed.

(** Every nonempty canonical trie contains a binding. *)
Theorem nonempty_lookup {A} (n : Trie.ne A) :
  exists p v, Trie.get p (Trie.Nodes n) = Some v.
Proof.
  induction n.
  - destruct IHn as [p [v Hget]]. exists (xI p), v.
    rewrite Trie.get_equation. exact Hget.
  - exists xH, v. reflexivity.
  - exists xH, v. reflexivity.
  - destruct IHn as [p [v Hget]]. exists (xO p), v.
    rewrite Trie.get_equation. exact Hget.
  - destruct IHn1 as [p [v Hget]]. exists (xO p), v.
    rewrite Trie.get_equation. exact Hget.
  - exists xH, v. reflexivity.
  - exists xH, v. reflexivity.
Qed.

Local Lemma nodes_node_le {A} (l r : Trie.t A) o :
  (skeleton_nodes (Trie.node l o r) <= 1 + skeleton_nodes l + skeleton_nodes r)%N.
Proof.
  destruct l, o, r; cbn [Trie.node skeleton_nodes nodes_ne]; lia.
Qed.

(** A stored-key width bound connects physical skeleton size to binding cardinality. *)
Theorem skeleton_width {A} (tr : Trie.t A) B :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= B)%N) ->
  (skeleton_nodes tr <= N.of_nat (TrieMerge.size tr) * B)%N.
Proof.
  revert B. induction tr as [|l o r IHl IHr] using Trie.node_ind; intros B Hbits.
  - cbn [skeleton_nodes]. lia.
  - assert (Hleft : (skeleton_nodes l <= N.of_nat (TrieMerge.size l) * (B - 1))%N).
    { apply IHl. intros p v Hget.
      specialize (Hbits (xO p) v).
      rewrite Trie.get_node in Hbits. specialize (Hbits Hget).
      change (N.pos (Pos.succ (Pos.size p)) <= B)%N in Hbits.
      assert (Hsucc : N.pos (Pos.succ (Pos.size p)) = (1 + N.pos (Pos.size p))%N).
      { rewrite N.add_1_l. reflexivity. }
      rewrite Hsucc in Hbits. lia. }
    assert (Hright : (skeleton_nodes r <= N.of_nat (TrieMerge.size r) * (B - 1))%N).
    { apply IHr. intros p v Hget.
      specialize (Hbits (xI p) v).
      rewrite Trie.get_node in Hbits. specialize (Hbits Hget).
      change (N.pos (Pos.succ (Pos.size p)) <= B)%N in Hbits.
      assert (Hsucc : N.pos (Pos.succ (Pos.size p)) = (1 + N.pos (Pos.size p))%N).
      { rewrite N.add_1_l. reflexivity. }
      rewrite Hsucc in Hbits. lia. }
    destruct (Trie.node l o r) as [|n] eqn:Hnode.
    + cbn [skeleton_nodes]. lia.
    + destruct (nonempty_lookup n) as [p [v Hget]].
      assert (Hwidth : (1 <= B)%N).
      { specialize (Hbits _ _ Hget). lia. }
      assert (Hsize : (0 < TrieMerge.size (Trie.Nodes n))%nat).
      { rewrite TrieMerge.size_elements. apply TrieMerge.elements_spec in Hget.
        destruct (TrieMerge.elements (Trie.Nodes n)); [contradiction|cbn; lia]. }
      pose proof (nodes_node_le l r o) as Hnodes.
      rewrite Hnode in Hnodes.
      pose proof (TrieMerge.size_node l r o) as Hcard.
      rewrite Hnode in Hcard.
      assert (HcardN : N.of_nat (TrieMerge.size (Trie.Nodes n)) =
        (N.of_nat (TrieMerge.size l) +
          (match o with Some _ => 1 | None => 0 end) +
          N.of_nat (TrieMerge.size r))%N).
      { rewrite Hcard, !Nat2N.inj_add. destruct o; reflexivity. }
      assert (Hpositive : (1 <= N.of_nat (TrieMerge.size (Trie.Nodes n)))%N) by lia.
      destruct o; cbn in HcardN; nia.
Qed.

(** Intersection's physical overhead is bounded using either operand's binding-width product. *)
Theorem inter_cost_left {A B C} (f : A -> B -> Cost.t C)
    (tr : Trie.t A) (u : Trie.t B) bits :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.inter_with_c f tr u) <=
    trie_k * (1 + N.of_nat (TrieMerge.size tr)) * (1 + bits) +
      overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u)%N.
Proof.
  intro Hbits. pose proof (skeleton_width tr bits Hbits).
  pose proof (inter_cost f tr u).
  pose proof (N.le_min_l (skeleton_nodes tr) (skeleton_nodes u)).
  unfold trie_k in *. nia.
Qed.

(** Difference is bounded by the left binding-width product, including shared returns. *)
Theorem diff_cost_left {A B} (tr : Trie.t A) (u : Trie.t B) bits :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.diff_c tr u) <=
    trie_k * (1 + N.of_nat (TrieMerge.size tr)) * (1 + bits))%N.
Proof.
  intro Hbits. pose proof (skeleton_width tr bits Hbits).
  pose proof (diff_cost tr u).
  pose proof (N.le_min_l (skeleton_nodes tr) (skeleton_nodes u)).
  unfold trie_k in *. nia.
Qed.

(** A width bound on the right operand gives the symmetric intersection overhead bound. *)
Theorem inter_cost_right {A B C} (f : A -> B -> Cost.t C)
    (tr : Trie.t A) (u : Trie.t B) bits :
  (forall p v, Trie.get p u = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.inter_with_c f tr u) <=
    trie_k * (1 + N.of_nat (TrieMerge.size u)) * (1 + bits) +
      overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u)%N.
Proof.
  intro Hbits. pose proof (skeleton_width u bits Hbits).
  pose proof (inter_cost f tr u).
  pose proof (N.le_min_r (skeleton_nodes tr) (skeleton_nodes u)).
  unfold trie_k in *. nia.
Qed.

(** Only keys of the chosen smaller-cardinality operand need a width bound. *)
Theorem inter_cost_smaller {A B C} (f : A -> B -> Cost.t C)
    (tr : Trie.t A) (u : Trie.t B) bits :
  (if Nat.leb (TrieMerge.size tr) (TrieMerge.size u)
    then forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N
    else forall p v, Trie.get p u = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.inter_with_c f tr u) <=
    trie_k * (1 + N.of_nat (Nat.min (TrieMerge.size tr) (TrieMerge.size u))) * (1 + bits) +
      overlap (callback_weight (fun a b => Cost.ticks (f a b))) tr u)%N.
Proof.
  destruct (Nat.leb (TrieMerge.size tr) (TrieMerge.size u)) eqn:Hsmall; intro Hbits.
  - apply Nat.leb_le in Hsmall. rewrite Nat.min_l by exact Hsmall.
    now apply inter_cost_left.
  - apply Nat.leb_gt in Hsmall. rewrite Nat.min_r by lia.
    now apply inter_cost_right.
Qed.

(** A right binding-width bound includes every constant-time shared return in difference. *)
Theorem diff_cost_right {A B} (tr : Trie.t A) (u : Trie.t B) bits :
  (forall p v, Trie.get p u = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.diff_c tr u) <=
    trie_k * (1 + N.of_nat (TrieMerge.size u)) * (1 + bits))%N.
Proof.
  intro Hbits. pose proof (skeleton_width u bits Hbits).
  pose proof (diff_cost_small_right tr u). unfold trie_k in *. nia.
Qed.

(** Uniform node weights bound their sum without hiding an arbitrary callback cost. *)
Theorem overlap_bound {A B} (w : option A -> option B -> N) tr u k :
  (forall a b, (w a b <= k)%N) -> (overlap w tr u <= k * shared_nodes tr u)%N.
Proof.
  intro Hweights. destruct tr as [|n]; [cbn [overlap]; lia|]. revert u.
  induction n; intros [|other]; cbn [overlap shared_nodes overlap_ne]; try solve [lia].
  all: cbn [overlap shared_nodes] in *.
  all: try pose proof (IHn (Trie.left (Trie.Nodes other))) as Hl.
  all: try pose proof (IHn (Trie.right (Trie.Nodes other))) as Hr.
  all: try pose proof (IHn1 (Trie.left (Trie.Nodes other))) as Hl.
  all: try pose proof (IHn2 (Trie.right (Trie.Nodes other))) as Hr.
  all: pose proof (Hweights None (Trie.value (Trie.Nodes other))) as Habsent.
  all: try pose proof (Hweights (Some v) (Trie.value (Trie.Nodes other))) as Hpresent.
  all: nia.
Qed.

(** A numeric union bound requires a separate uniform callback bound. *)
Theorem union_with_cost_numeric {A} (f : A -> A -> Cost.t A) tr u c :
  (forall a b, (Cost.ticks (f a b) <= c)%N) ->
  (Cost.ticks (TrieMerge.union_with_c f tr u) <=
    (trie_k + c) * (1 + shared_nodes tr u))%N.
Proof.
  intro Hcallback. pose proof (union_with_cost f tr u) as Hcost.
  assert (Hweights : forall a b,
    (callback_weight (fun a b => Cost.ticks (f a b)) a b <= c)%N).
  { intros [a|] [b|]; cbn [callback_weight]; auto using N.le_0_l. }
  pose proof (overlap_bound _ tr u c Hweights). nia.
Qed.

(** Intersection's numeric bound has an explicit callback-charge premise. *)
Theorem inter_cost_numeric {A B C} (f : A -> B -> Cost.t C) tr u c :
  (forall a b, (Cost.ticks (f a b) <= c)%N) ->
  (Cost.ticks (TrieMerge.inter_with_c f tr u) <=
    (trie_k + c) * (1 + N.min (skeleton_nodes tr) (skeleton_nodes u)))%N.
Proof.
  intro Hcallback. pose proof (inter_cost f tr u) as Hcost.
  assert (Hweights : forall a b,
    (callback_weight (fun a b => Cost.ticks (f a b)) a b <= c)%N).
  { intros [a|] [b|]; cbn [callback_weight]; auto using N.le_0_l. }
  pose proof (overlap_bound _ tr u c Hweights).
  pose proof (shared_nodes_left tr u) as Hl. pose proof (shared_nodes_right tr u) as Hr.
  pose proof (N.min_glb _ _ _ Hl Hr). nia.
Qed.

(** Under a uniform callback bound, intersection is linear in the smaller physical skeleton. *)
Theorem inter_bigO {A B C} (f : A -> B -> Cost.t C) c :
  (forall a b, (Cost.ticks (f a b) <= c)%N) ->
  bigO (fun pair : Trie.t A * Trie.t B =>
      N.min (skeleton_nodes (fst pair)) (skeleton_nodes (snd pair)))
    (fun pair => Cost.ticks (TrieMerge.inter_with_c f (fst pair) (snd pair))).
Proof.
  intro Hcallback. exists (trie_k + c)%N. intros [tr u].
  apply inter_cost_numeric. exact Hcallback.
Qed.

(** A binding-weight sum visits present values and gives no weight to unary path nodes. *)
Fixpoint binding_weight_ne {A} (w : A -> N) (n : Trie.ne A) : N :=
  match n with
  | Trie.N001 r => binding_weight_ne w r
  | Trie.N010 v => w v
  | Trie.N011 v r => w v + binding_weight_ne w r
  | Trie.N100 l => binding_weight_ne w l
  | Trie.N101 l r => binding_weight_ne w l + binding_weight_ne w r
  | Trie.N110 l v => binding_weight_ne w l + w v
  | Trie.N111 l v r => binding_weight_ne w l + w v + binding_weight_ne w r
  end.

Definition binding_weight {A} (w : A -> N) (tr : Trie.t A) :=
  match tr with
  | Trie.Empty => 0%N
  | Trie.Nodes n => binding_weight_ne w n
  end.

(** Filtering's exact cost retains every callback charge and one overhead tick per invocation. *)
Theorem filter_cost {A B} (f : A -> Cost.t (option B)) tr :
  Cost.ticks (TrieMerge.filter_map_c f tr) =
    (skeleton_nodes tr + binding_weight (fun v => 1 + Cost.ticks (f v)) tr)%N.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n; cbn [TrieMerge.filter_map_c TrieMerge.filter_ne_c];
    autorewrite with galois_cost; unfold TrieMerge.rebuild_c, TrieMerge.filter_value_c;
    autorewrite with galois_cost;
    cbn [TrieMerge.filter_map_c skeleton_nodes binding_weight nodes_ne binding_weight_ne] in *;
    rewrite ?IHn, ?IHn1, ?IHn2; nia.
Qed.

Local Lemma binding_weight_ext {A} (w z : A -> N) tr :
  (forall v, w v = z v) -> binding_weight w tr = binding_weight z tr.
Proof.
  intro Hweights. destruct tr as [|n]; [reflexivity|].
  induction n; cbn [binding_weight binding_weight_ne] in *;
    rewrite ?IHn, ?IHn1, ?IHn2, ?Hweights; reflexivity.
Qed.

(** Binding-weight addition separates invocation overhead from arbitrary callee work. *)
Theorem binding_weight_add {A} (w z : A -> N) tr :
  binding_weight (fun v => w v + z v) tr =
    (binding_weight w tr + binding_weight z tr)%N.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n; cbn [binding_weight binding_weight_ne] in *;
    rewrite ?IHn, ?IHn1, ?IHn2; nia.
Qed.

(** A skeleton has at least one physical node per binding. *)
Theorem bindings_nodes {A} (tr : Trie.t A) :
  (binding_weight (fun _ => 1) tr <= skeleton_nodes tr)%N.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n; cbn [binding_weight binding_weight_ne skeleton_nodes nodes_ne] in *; lia.
Qed.

(** Filtering overhead is physical-node-linear after its full callback sum is separated. *)
Theorem filter_cost_relative {A B} (f : A -> Cost.t (option B)) tr :
  (Cost.ticks (TrieMerge.filter_map_c f tr) <=
    2 * skeleton_nodes tr + binding_weight (fun v => Cost.ticks (f v)) tr)%N.
Proof.
  rewrite filter_cost, binding_weight_add. pose proof (bindings_nodes tr). lia.
Qed.

(** Synchronized checking weights every possible first-operand callback at its matching subtree. *)
Fixpoint check_work_ne {A B} (w : A -> option B -> N) (n : Trie.ne A) (u : Trie.t B) : N :=
  match n with
  | Trie.N001 r => check_work_ne w r (Trie.right u)
  | Trie.N010 v => w v (Trie.value u)
  | Trie.N011 v r => w v (Trie.value u) + check_work_ne w r (Trie.right u)
  | Trie.N100 l => check_work_ne w l (Trie.left u)
  | Trie.N101 l r => check_work_ne w l (Trie.left u) + check_work_ne w r (Trie.right u)
  | Trie.N110 l v => check_work_ne w l (Trie.left u) + w v (Trie.value u)
  | Trie.N111 l v r =>
    check_work_ne w l (Trie.left u) + w v (Trie.value u) + check_work_ne w r (Trie.right u)
  end.

Definition check_work {A B} (w : A -> option B -> N) (tr : Trie.t A) (u : Trie.t B) :=
  match tr with
  | Trie.Empty => 0%N
  | Trie.Nodes n => check_work_ne w n u
  end.

(** Relational checking retains arbitrary callee work and may omit callbacks after failure. *)
Theorem forall2_cost_relative {A B} (rel : A -> option B -> Cost.t bool) tr u :
  (Cost.ticks (TrieMerge.forall2_c rel tr u) <= skeleton_nodes tr +
    check_work (fun a b => 1 + Cost.ticks (rel a b)) tr u)%N.
Proof.
  destruct tr as [|n]; [reflexivity|]. revert u.
  induction n; intro u; cbn [TrieMerge.forall2_c TrieMerge.forall2_ne_c];
    autorewrite with galois_cost; unfold TrieMerge.and_c, TrieMerge.test_value_c;
    autorewrite with galois_cost.
  all: cbn [TrieMerge.forall2_c skeleton_nodes check_work] in *.
  all: try pose proof (IHn (Trie.left u)) as Hl.
  all: try pose proof (IHn (Trie.right u)) as Hr.
  all: try pose proof (IHn1 (Trie.left u)) as Hl.
  all: try pose proof (IHn2 (Trie.right u)) as Hr.
  all: repeat (autorewrite with galois_cost;
    match goal with
    | |- context [if ?test then _ else _] => destruct test
    end).
  all: autorewrite with galois_cost; cbn [nodes_ne check_work_ne]; nia.
Qed.

Local Lemma check_work_bound {A B} (w : A -> option B -> N) tr u c :
  (forall a b, (w a b <= c)%N) ->
  (check_work w tr u <= c * binding_weight (fun _ => 1) tr)%N.
Proof.
  intro Hweight. destruct tr as [|n]; [cbn [check_work binding_weight]; lia|]. revert u.
  induction n; intro u; cbn [check_work check_work_ne binding_weight binding_weight_ne].
  all: cbn [check_work binding_weight] in *.
  all: try pose proof (IHn (Trie.left u)) as Hl.
  all: try pose proof (IHn (Trie.right u)) as Hr.
  all: try pose proof (IHn1 (Trie.left u)) as Hl.
  all: try pose proof (IHn2 (Trie.right u)) as Hr.
  all: try pose proof (Hweight v (Trie.value u)) as Hroot.
  all: nia.
Qed.

(** A numeric relational-check bound takes its callback bound as a separate premise. *)
Theorem forall2_cost {A B} (rel : A -> option B -> Cost.t bool) tr u c :
  (forall a b, (Cost.ticks (rel a b) <= c)%N) ->
  (Cost.ticks (TrieMerge.forall2_c rel tr u) <=
    (trie_k + c) * (1 + skeleton_nodes tr))%N.
Proof.
  intro Hcallback. pose proof (forall2_cost_relative rel tr u) as Hcost.
  assert (Hweight : forall a b, (1 + Cost.ticks (rel a b) <= 1 + c)%N) by
    (intros a b; specialize (Hcallback a b); lia).
  pose proof (check_work_bound _ tr u (1 + c)%N Hweight) as Hwork.
  pose proof (bindings_nodes tr). unfold trie_k. nia.
Qed.

(** Equality's short circuit keeps the full charges of both potentially reached relational tests. *)
Theorem beq_cost {A} (eq : A -> A -> Cost.t bool) tr u :
  let test := fun a b => match b with None => Cost.ret false | Some b => eq a b end in
  (Cost.ticks (TrieMerge.beq_c eq tr u) <=
    Cost.ticks (TrieMerge.forall2_c test tr u) +
      Cost.ticks (TrieMerge.forall2_c test u tr))%N.
Proof.
  cbn zeta. unfold TrieMerge.beq_c, TrieMerge.and_c.
  autorewrite with galois_cost.
  destruct (Cost.value (TrieMerge.forall2_c
    (fun a b => match b with None => Cost.ret false | Some b => eq a b end) tr u));
    autorewrite with galois_cost; lia.
Qed.

(** Equality has a both-operands numeric bound under an explicit comparison callback bound. *)
Theorem beq_cost_numeric {A} (eq : A -> A -> Cost.t bool) tr u c :
  (forall a b, (Cost.ticks (eq a b) <= c)%N) ->
  (Cost.ticks (TrieMerge.beq_c eq tr u) <=
    (trie_k + c) * (2 + skeleton_nodes tr + skeleton_nodes u))%N.
Proof.
  intro Hcallback.
  set (test := fun a b => match b with None => Cost.ret false | Some b => eq a b end).
  assert (Htest : forall a b, (Cost.ticks (test a b) <= c)%N).
  { intros a [b|]; [apply Hcallback|apply N.le_0_l]. }
  pose proof (forall2_cost test tr u c Htest) as Hl.
  pose proof (forall2_cost test u tr c Htest) as Hr.
  pose proof (beq_cost eq tr u) as Hcost. cbn zeta in Hcost.
  fold test in Hcost. nia.
Qed.

(** A general merge weight includes callbacks in the delegated one-sided subtrees. *)
Fixpoint merge_weight_ne {A B} (w : option A -> option B -> N)
    (wl : Trie.t A -> N) (wr : Trie.t B -> N) (n : Trie.ne A) (u : Trie.t B) : N :=
  match u with
  | Trie.Empty => wl (Trie.Nodes n)
  | Trie.Nodes _ =>
    match n with
    | Trie.N001 r =>
      wr (Trie.left u) + w None (Trie.value u) + merge_weight_ne w wl wr r (Trie.right u)
    | Trie.N010 v =>
      wr (Trie.left u) + w (Some v) (Trie.value u) + wr (Trie.right u)
    | Trie.N011 v r =>
      wr (Trie.left u) + w (Some v) (Trie.value u) +
        merge_weight_ne w wl wr r (Trie.right u)
    | Trie.N100 l =>
      merge_weight_ne w wl wr l (Trie.left u) + w None (Trie.value u) + wr (Trie.right u)
    | Trie.N101 l r =>
      merge_weight_ne w wl wr l (Trie.left u) + w None (Trie.value u) +
        merge_weight_ne w wl wr r (Trie.right u)
    | Trie.N110 l v =>
      merge_weight_ne w wl wr l (Trie.left u) + w (Some v) (Trie.value u) +
        wr (Trie.right u)
    | Trie.N111 l v r =>
      merge_weight_ne w wl wr l (Trie.left u) + w (Some v) (Trie.value u) +
        merge_weight_ne w wl wr r (Trie.right u)
    end
  end.

Definition merge_weight {A B} (w : option A -> option B -> N)
    (wl : Trie.t A -> N) (wr : Trie.t B -> N) (tr : Trie.t A) (u : Trie.t B) : N :=
  match tr with
  | Trie.Empty => wr u
  | Trie.Nodes n => merge_weight_ne w wl wr n u
  end.

(** General merge traversal depends on both operand skeletons and all delegated callee work. *)
Theorem merge_cost {A B C} (f : option A -> option B -> Cost.t (option C))
    (fl : Trie.t A -> Cost.t (Trie.t C)) (fr : Trie.t B -> Cost.t (Trie.t C))
    (wl : Trie.t A -> N) (wr : Trie.t B -> N) tr u :
  (forall t, (Cost.ticks (fl t) <= 2 * skeleton_nodes t + wl t)%N) ->
  (forall t, (Cost.ticks (fr t) <= 2 * skeleton_nodes t + wr t)%N) ->
  (Cost.ticks (TrieMerge.merge_c f fl fr tr u) <=
    1 + 3 * (skeleton_nodes tr + skeleton_nodes u) +
      merge_weight (fun a b => Cost.ticks (f a b)) wl wr tr u)%N.
Proof.
  intros Hl Hr. destruct tr as [|n].
  - cbn [TrieMerge.merge_c merge_weight skeleton_nodes].
    autorewrite with galois_cost. specialize (Hr u). nia.
  - revert u. induction n; intros [|other]; cbn [TrieMerge.merge_c TrieMerge.merge_ne_c];
      autorewrite with galois_cost;
      try solve [
        match goal with
        | |- context [Cost.ticks (?handler ?t)] => pose proof (Hl t) as Honly
        end;
        cbn [merge_weight merge_weight_ne skeleton_nodes] in *; nia].
    all: unfold TrieMerge.rebuild_c, TrieMerge.merge_value_c;
      autorewrite with galois_cost.
    all: cbn [TrieMerge.merge_c merge_weight skeleton_nodes] in *.
    all: try pose proof (IHn (Trie.left (Trie.Nodes other))) as Hleft.
    all: try pose proof (IHn (Trie.right (Trie.Nodes other))) as Hright.
    all: try pose proof (IHn1 (Trie.left (Trie.Nodes other))) as Hleft.
    all: try pose proof (IHn2 (Trie.right (Trie.Nodes other))) as Hright.
    all: pose proof (Hr (Trie.left (Trie.Nodes other))) as Honlyleft.
    all: pose proof (Hr (Trie.right (Trie.Nodes other))) as Honlyright.
    all: destruct other; cbn [Trie.left Trie.right skeleton_nodes nodes_ne merge_weight_ne] in *;
      nia.
Qed.

(** General combination sums callback work at shared and one-sided entries. *)
Definition combine_work {A B} (w : option A -> option B -> N) tr u :=
  merge_weight w (binding_weight (fun a => w (Some a) None))
    (binding_weight (fun b => w None (Some b))) tr u.

(** General combine has a both-operands overhead bound and retains arbitrary callback charges. *)
Theorem combine_cost {A B C} (f : option A -> option B -> Cost.t (option C)) tr u :
  (Cost.ticks (TrieMerge.combine_c f tr u) <=
    trie_k * (1 + skeleton_nodes tr + skeleton_nodes u) +
      combine_work (fun a b => Cost.ticks (f a b)) tr u)%N.
Proof.
  unfold TrieMerge.combine_c, combine_work.
  pose proof (merge_cost f
    (TrieMerge.filter_map_c (fun a => f (Some a) None))
    (TrieMerge.filter_map_c (fun b => f None (Some b)))
    (binding_weight (fun a => Cost.ticks (f (Some a) None)))
    (binding_weight (fun b => Cost.ticks (f None (Some b)))) tr u
    (fun t => filter_cost_relative _ t) (fun t => filter_cost_relative _ t)) as Hcost.
  unfold trie_k. nia.
Qed.

(** Binding count agrees with the public cardinality even when paths contain unary nodes. *)
Theorem binding_count_size {A} (tr : Trie.t A) :
  binding_weight (fun _ => 1) tr = N.of_nat (TrieMerge.size tr).
Proof.
  rewrite TrieMerge.size_elements, TrieMerge.elements_entries.
  destruct tr as [|n]; [reflexivity|].
  induction n; cbn [binding_weight binding_weight_ne TrieMerge.entries TrieMerge.entries_ne];
    rewrite ?length_app, ?length_map; cbn [length];
    rewrite ?length_map, ?Nat2N.inj_add, ?Nat2N.inj_succ;
    cbn [TrieMerge.entries binding_weight] in *; rewrite ?IHn, ?IHn1, ?IHn2; nia.
Qed.

(** Key mass counts every emitted binary digit, including each binding's leading digit. *)
Fixpoint key_mass_ne {A} (n : Trie.ne A) : N :=
  match n with
  | Trie.N001 r => key_mass_ne r + binding_weight_ne (fun _ => 1) r
  | Trie.N010 _ => 1
  | Trie.N011 _ r => 1 + key_mass_ne r + binding_weight_ne (fun _ => 1) r
  | Trie.N100 l => key_mass_ne l + binding_weight_ne (fun _ => 1) l
  | Trie.N101 l r =>
    key_mass_ne l + binding_weight_ne (fun _ => 1) l +
      key_mass_ne r + binding_weight_ne (fun _ => 1) r
  | Trie.N110 l _ => key_mass_ne l + binding_weight_ne (fun _ => 1) l + 1
  | Trie.N111 l _ r =>
    key_mass_ne l + binding_weight_ne (fun _ => 1) l + 1 +
      key_mass_ne r + binding_weight_ne (fun _ => 1) r
  end.

Definition key_mass {A} (tr : Trie.t A) :=
  match tr with
  | Trie.Empty => 0%N
  | Trie.Nodes n => key_mass_ne n
  end.

(** Stateful callback work is evaluated at the accumulators reached by the costed traversal. *)
Fixpoint fold_work_ne {A B} (w : B -> positive -> A -> N)
    (f : B -> positive -> A -> Cost.t B) (path : positive -> Cost.t positive)
    (n : Trie.ne A) (b : B) : N :=
  match n with
  | Trie.N001 r => fold_work_ne w f (TrieMerge.extend_c xI path) r b
  | Trie.N010 v => w b (Cost.value (path xH)) v
  | Trie.N011 v r =>
    w b (Cost.value (path xH)) v +
      fold_work_ne w f (TrieMerge.extend_c xI path) r
        (Cost.value (TrieMerge.emit_c f path b v))
  | Trie.N100 l => fold_work_ne w f (TrieMerge.extend_c xO path) l b
  | Trie.N101 l r =>
    fold_work_ne w f (TrieMerge.extend_c xO path) l b +
      fold_work_ne w f (TrieMerge.extend_c xI path) r
        (Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) l b))
  | Trie.N110 l v =>
    let b' := Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) l b) in
    fold_work_ne w f (TrieMerge.extend_c xO path) l b + w b' (Cost.value (path xH)) v
  | Trie.N111 l v r =>
    let b' := Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) l b) in
    fold_work_ne w f (TrieMerge.extend_c xO path) l b +
      w b' (Cost.value (path xH)) v +
      fold_work_ne w f (TrieMerge.extend_c xI path) r
        (Cost.value (TrieMerge.emit_c f path b' v))
  end.

Definition fold_work {A B} (w : B -> positive -> A -> N)
    (f : B -> positive -> A -> Cost.t B) (tr : Trie.t A) b :=
  match tr with
  | Trie.Empty => 0%N
  | Trie.Nodes n => fold_work_ne w f Cost.ret n b
  end.

Local Lemma fold_ne_cost {A B} (f : B -> positive -> A -> Cost.t B) n :
  forall path b d, (forall p, Cost.ticks (path p) = d) ->
  Cost.ticks (TrieMerge.fold_ne_c f path n b) =
    (nodes_ne n + key_mass_ne n + d * binding_weight_ne (fun _ => 1) n +
      fold_work_ne (fun b p v => Cost.ticks (f b p v)) f path n b)%N.
Proof.
  induction n; intros path b d Hpath; cbn [TrieMerge.fold_ne_c];
    autorewrite with galois_cost; unfold TrieMerge.emit_c;
    autorewrite with galois_cost.
  all: rewrite ?(IHn _ _ (1 + d)%N), ?(IHn1 _ _ (1 + d)%N),
    ?(IHn2 _ _ (1 + d)%N) by
      (intro p; unfold TrieMerge.extend_c; autorewrite with galois_cost;
        rewrite Hpath; reflexivity).
  all: cbn [nodes_ne key_mass_ne binding_weight_ne fold_work_ne];
    unfold TrieMerge.emit_c; autorewrite with galois_cost; rewrite ?Hpath; nia.
Qed.

(** Keyed folding separates physical traversal, all materialized key bits and exact callee work. *)
Theorem fold_cost {A B} (f : B -> positive -> A -> Cost.t B) tr b :
  Cost.ticks (TrieMerge.fold_c f tr b) =
    (skeleton_nodes tr + key_mass tr +
      fold_work (fun b p v => Cost.ticks (f b p v)) f tr b)%N.
Proof.
  destruct tr as [|n]; [reflexivity|].
  unfold TrieMerge.fold_c, TrieMerge.fold_path_c, skeleton_nodes, key_mass, fold_work.
  rewrite (fold_ne_cost f n Cost.ret b 0%N) by reflexivity. nia.
Qed.

(** A numeric fold callback bound is a separate premise on every reached accumulator. *)
Theorem fold_work_bound {A B} (w : B -> positive -> A -> N)
    (f : B -> positive -> A -> Cost.t B) tr b c :
  (forall b p v, (w b p v <= c)%N) ->
  (fold_work w f tr b <= c * binding_weight (fun _ => 1) tr)%N.
Proof.
  intro Hweight. destruct tr as [|n]; [cbn [fold_work binding_weight]; lia|].
  unfold fold_work, binding_weight. generalize (@Cost.ret positive) as path.
  revert b. induction n; intros b path; cbn [fold_work_ne binding_weight_ne].
  all: try pose proof (IHn b (TrieMerge.extend_c xI path)) as Hr.
  all: try pose proof (IHn b (TrieMerge.extend_c xO path)) as Hl.
  all: try pose proof (IHn
    (Cost.value (TrieMerge.emit_c f path b v)) (TrieMerge.extend_c xI path)) as Hrv.
  all: try pose proof (IHn1 b (TrieMerge.extend_c xO path)) as Hl.
  all: try pose proof (IHn2
    (Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) n1 b))
    (TrieMerge.extend_c xI path)) as Hr.
  all: try pose proof (IHn2
    (Cost.value (TrieMerge.emit_c f path
      (Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) n1 b)) v))
    (TrieMerge.extend_c xI path)) as Hrv.
  all: try pose proof (Hweight b (Cost.value (path xH)) v) as Hroot.
  all: try pose proof (Hweight
    (Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) n b))
    (Cost.value (path xH)) v) as Hroot'.
  all: try pose proof (Hweight
    (Cost.value (TrieMerge.fold_ne_c f (TrieMerge.extend_c xO path) n1 b))
    (Cost.value (path xH)) v) as Hroot'.
  all: nia.
Qed.

(** Numeric keyed-fold bounds charge physical nodes, key output size and bounded callbacks. *)
Theorem fold_cost_numeric {A B} (f : B -> positive -> A -> Cost.t B) tr b c :
  (forall b p v, (Cost.ticks (f b p v) <= c)%N) ->
  (Cost.ticks (TrieMerge.fold_c f tr b) <=
    skeleton_nodes tr + key_mass tr + c * N.of_nat (TrieMerge.size tr))%N.
Proof.
  intro Hcallback. rewrite fold_cost.
  pose proof (fold_work_bound
    (fun b p v => Cost.ticks (f b p v)) f tr b c Hcallback) as Hwork.
  rewrite binding_count_size in Hwork. lia.
Qed.

Local Lemma size_ne_cost {A} (n : Trie.ne A) :
  forall acc, Cost.ticks
    (TrieMerge.fold_values_ne_c (fun acc (_ : A) => Cost.ret (S acc)) n acc) =
      (nodes_ne n + binding_weight_ne (fun _ => 1) n)%N.
Proof.
  induction n; intro acc; cbn [TrieMerge.fold_values_ne_c];
    autorewrite with galois_cost;
    rewrite ?IHn, ?IHn1, ?IHn2; cbn [nodes_ne binding_weight_ne]; nia.
Qed.

(** Binding cardinality can be counted without constructing keys in physical-node-linear cost. *)
Theorem size_cost {A} (tr : Trie.t A) :
  (Cost.ticks (TrieMerge.size_c tr) <= trie_k * (1 + skeleton_nodes tr))%N.
Proof.
  assert (Hexact : Cost.ticks (TrieMerge.size_c tr) =
    (skeleton_nodes tr + binding_weight (fun _ => 1) tr)%N).
  { destruct tr as [|n]; [reflexivity|]. apply size_ne_cost. }
  rewrite Hexact. pose proof (bindings_nodes tr). unfold trie_k. nia.
Qed.

Local Lemma collect_length {A} (tr : Trie.t A) :
  length (Cost.value (TrieMerge.fold_c
    (fun acc p v => Cost.ret ((p, v) :: acc)) tr [])) = TrieMerge.size tr.
Proof.
  rewrite TrieMerge.fold_elements, TrieMerge.size_elements.
  generalize (TrieMerge.elements tr). intro xs.
  assert (Hlength : forall acc,
    length (fold_left (fun acc pv => (fst pv, snd pv) :: acc) xs acc) =
      (length xs + length acc)%nat).
  { induction xs as [|pv xs IH]; intro acc; [reflexivity|].
    cbn [fold_left length]. rewrite IH. cbn [length]. lia. }
  change (length (fold_left (fun acc pv => (fst pv, snd pv) :: acc) xs []) = length xs).
  rewrite Hlength. cbn [length]. lia.
Qed.

(** Enumeration overhead includes its complete final reversal and materialized key bits. *)
Theorem elements_cost_relative {A} (tr : Trie.t A) :
  (Cost.ticks (TrieMerge.elements_c tr) <= 2 * skeleton_nodes tr + key_mass tr)%N.
Proof.
  unfold TrieMerge.elements_c. rewrite Cost.ticks_bind, ticks_rev_c, collect_length.
  pose proof (fold_cost_numeric
    (fun acc p v => Cost.ret ((p, v) :: acc)) tr [] 0%N
    (fun _ _ _ => N.le_refl 0)) as Hfold.
  pose proof (bindings_nodes tr) as Hbindings.
  rewrite binding_count_size in Hbindings. nia.
Qed.

(** Enumeration is linear in physical nodes plus emitted key bits. *)
Theorem elements_cost {A} (tr : Trie.t A) :
  (Cost.ticks (TrieMerge.elements_c tr) <=
    trie_k * (1 + skeleton_nodes tr + key_mass tr))%N.
Proof.
  pose proof (elements_cost_relative tr). unfold trie_k. nia.
Qed.

(** The weight of an ordered entry list sums each occurrence's code weight. *)
Fixpoint entry_weight {A} (w : positive -> N) (xs : list (positive * A)) : N :=
  match xs with
  | [] => 0
  | (p, _) :: xs => w p + entry_weight w xs
  end.

Local Lemma entry_weight_app {A} w (xs ys : list (positive * A)) :
  entry_weight w (xs ++ ys) = (entry_weight w xs + entry_weight w ys)%N.
Proof.
  induction xs as [|[p v] xs IH]; cbn [app entry_weight]; rewrite ?IH; lia.
Qed.

Local Lemma entry_weight_lift {A} (bit : positive -> positive) xs :
  (forall p, N.pos (Pos.size (bit p)) = (1 + N.pos (Pos.size p))%N) ->
  entry_weight (fun p => N.pos (Pos.size p))
    (List.map (fun pv : positive * A => (bit (fst pv), snd pv)) xs) =
    (entry_weight (fun p => N.pos (Pos.size p)) xs + N.of_nat (length xs))%N.
Proof.
  intro Hbit. induction xs as [|[p v] xs IH]; [reflexivity|].
  cbn [List.map fst snd entry_weight length].
  rewrite Hbit, IH, Nat2N.inj_succ. nia.
Qed.

Local Lemma code_bit_size (bit : positive -> positive) :
  (bit = xO \/ bit = xI) ->
  forall p, N.pos (Pos.size (bit p)) = (1 + N.pos (Pos.size p))%N.
Proof.
  intros Hbit p. destruct Hbit as [Hzero|Hone]; subst bit;
    rewrite N.add_1_l; reflexivity.
Qed.

(** Key mass is the sum of the bit widths of the codes actually emitted by enumeration. *)
Theorem key_mass_elements {A} (tr : Trie.t A) :
  key_mass tr = entry_weight (fun p => N.pos (Pos.size p)) (TrieMerge.elements tr).
Proof.
  rewrite TrieMerge.elements_entries.
  assert (Hcount : forall n : Trie.ne A, binding_weight_ne (fun _ => 1) n =
    N.of_nat (length (TrieMerge.entries_ne n))).
  { intro n. pose proof (binding_count_size (Trie.Nodes n)) as H.
    rewrite TrieMerge.size_elements, TrieMerge.elements_entries in H. exact H. }
  destruct tr as [|n]; [reflexivity|].
  induction n; cbn [key_mass key_mass_ne TrieMerge.entries TrieMerge.entries_ne];
    rewrite ?entry_weight_app; cbn [entry_weight];
    rewrite ?(entry_weight_lift xO _ (code_bit_size xO (or_introl eq_refl))),
      ?(entry_weight_lift xI _ (code_bit_size xI (or_intror eq_refl)));
    cbn [entry_weight]; cbn [key_mass TrieMerge.entries] in *;
    rewrite ?IHn, ?IHn1, ?IHn2, ?Hcount; cbn [Pos.size]; nia.
Qed.

(** A stored-key width bound controls total output key size by binding cardinality. *)
Theorem key_mass_width {A} (tr : Trie.t A) bits :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (key_mass tr <= N.of_nat (TrieMerge.size tr) * bits)%N.
Proof.
  intro Hbits. rewrite key_mass_elements, TrieMerge.size_elements.
  assert (Hsum : forall xs : list (positive * A),
    (forall p v, In (p, v) xs -> (N.pos (Pos.size p) <= bits)%N) ->
    (entry_weight (fun p => N.pos (Pos.size p)) xs <= N.of_nat (length xs) * bits)%N).
  { intro xs. induction xs as [|[p v] xs IH]; intro Hwidth; [cbn; lia|].
    cbn [entry_weight length]. rewrite Nat2N.inj_succ.
    assert (Hhead : (N.pos (Pos.size p) <= bits)%N) by
      (apply (Hwidth p v); now left).
    assert (Htail : (entry_weight (fun p => N.pos (Pos.size p)) xs <=
      N.of_nat (length xs) * bits)%N).
    { apply IH. intros q w Hin. apply (Hwidth q w). now right. }
    nia. }
  apply Hsum. intros p v Hin. apply (Hbits p v). now apply TrieMerge.elements_spec.
Qed.

(** Numeric fold bounds require both the stored-key width and an independent callback bound. *)
Theorem fold_cost_width {A B} (f : B -> positive -> A -> Cost.t B) tr b bits c :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (forall b p v, (Cost.ticks (f b p v) <= c)%N) ->
  (Cost.ticks (TrieMerge.fold_c f tr b) <=
    (trie_k + c) * (1 + N.of_nat (TrieMerge.size tr)) * (1 + bits))%N.
Proof.
  intros Hbits Hcallback.
  pose proof (fold_cost_numeric f tr b c Hcallback) as Hcost.
  pose proof (skeleton_width tr bits Hbits) as Hnodes.
  pose proof (key_mass_width tr bits Hbits) as Hkeys.
  unfold trie_k. nia.
Qed.

(** Enumeration has the binding-cardinality times key-width corollary for bounded stored codes. *)
Theorem elements_cost_width {A} (tr : Trie.t A) bits :
  (forall p v, Trie.get p tr = Some v -> (N.pos (Pos.size p) <= bits)%N) ->
  (Cost.ticks (TrieMerge.elements_c tr) <=
    trie_k * (1 + N.of_nat (TrieMerge.size tr)) * (1 + bits))%N.
Proof.
  intro Hbits. pose proof (elements_cost_relative tr) as Hcost.
  pose proof (skeleton_width tr bits Hbits) as Hnodes.
  pose proof (key_mass_width tr bits Hbits) as Hkeys.
  unfold trie_k. nia.
Qed.

(** Code-free callback work follows the actual accumulator without constructing a path. *)
Fixpoint values_work_ne {A B} (w : B -> A -> N) (f : B -> A -> Cost.t B)
    (n : Trie.ne A) (b : B) : N :=
  match n with
  | Trie.N001 r => values_work_ne w f r b
  | Trie.N010 v => w b v
  | Trie.N011 v r => w b v + values_work_ne w f r (Cost.value (f b v))
  | Trie.N100 l => values_work_ne w f l b
  | Trie.N101 l r =>
    values_work_ne w f l b +
      values_work_ne w f r (Cost.value (TrieMerge.fold_values_ne_c f l b))
  | Trie.N110 l v =>
    values_work_ne w f l b + w (Cost.value (TrieMerge.fold_values_ne_c f l b)) v
  | Trie.N111 l v r =>
    let b' := Cost.value (TrieMerge.fold_values_ne_c f l b) in
    values_work_ne w f l b + w b' v +
      values_work_ne w f r (Cost.value (f b' v))
  end.

Definition values_work {A B} (w : B -> A -> N) (f : B -> A -> Cost.t B) tr b :=
  match tr with
  | Trie.Empty => 0%N
  | Trie.Nodes n => values_work_ne w f n b
  end.

(** Code-free folding separates physical nodes, callback overhead and arbitrary callee work. *)
Theorem fold_values_cost {A B} (f : B -> A -> Cost.t B) tr b :
  Cost.ticks (TrieMerge.fold_values_c f tr b) =
    (skeleton_nodes tr + N.of_nat (TrieMerge.size tr) +
      values_work (fun b v => Cost.ticks (f b v)) f tr b)%N.
Proof.
  rewrite <- binding_count_size. destruct tr as [|n]; [reflexivity|].
  unfold TrieMerge.fold_values_c, skeleton_nodes, binding_weight, values_work.
  revert b. induction n; intro b; cbn [TrieMerge.fold_values_ne_c];
    autorewrite with galois_cost; rewrite ?IHn, ?IHn1, ?IHn2;
    cbn [nodes_ne binding_weight_ne values_work_ne]; nia.
Qed.

(** Mapping keeps every callback charge and visits physical nodes independently of bindings. *)
Theorem map_cost_relative {A B} (f : A -> Cost.t B) tr :
  (Cost.ticks (TrieMerge.map_c f tr) <=
    2 * skeleton_nodes tr + binding_weight (fun v => Cost.ticks (f v)) tr)%N.
Proof.
  unfold TrieMerge.map_c. eapply N.le_trans; [apply filter_cost_relative|].
  rewrite (binding_weight_ext (fun v => Cost.ticks (Cost.map (@Some B) (f v)))
    (fun v => Cost.ticks (f v))) by (intro v; apply Cost.ticks_map).
  reflexivity.
Qed.

Local Lemma binding_weight_node {A} (w : A -> N) l o r :
  binding_weight w (Trie.node l o r) =
    (binding_weight w l + (match o with None => 0 | Some v => w v end) +
      binding_weight w r)%N.
Proof.
  destruct l, o, r; cbn [Trie.node binding_weight binding_weight_ne]; lia.
Qed.

Local Lemma weight_sum_app {A} (w : A -> N) (xs ys : list (positive * A)) :
  fold_right (fun pv n => (w (snd pv) + n)%N) 0%N (xs ++ ys) =
    (fold_right (fun pv n => (w (snd pv) + n)%N) 0%N xs +
      fold_right (fun pv n => (w (snd pv) + n)%N) 0%N ys)%N.
Proof.
  induction xs as [|x xs IH]; cbn [app fold_right]; rewrite ?IH; lia.
Qed.

Local Lemma weight_sum_shift {A} (w : A -> N) (bit : positive -> positive)
    (xs : list (positive * A)) :
  fold_right (fun pv n => (w (snd pv) + n)%N) 0%N
    (List.map (fun pv => (bit (fst pv), snd pv)) xs) =
  fold_right (fun pv n => (w (snd pv) + n)%N) 0%N xs.
Proof.
  induction xs as [|[p v] xs IH]; cbn [List.map fold_right snd fst];
    rewrite ?IH; reflexivity.
Qed.

(** Binding weights equal the sum over the actual public backend enumeration. *)
Theorem binding_weight_elements {A} (w : A -> N) (tr : Trie.t A) :
  binding_weight w tr =
    fold_right (fun pv n => (w (snd pv) + n)%N) 0%N (TrieMerge.elements tr).
Proof.
  induction tr as [|l o r IHl IHr] using Trie.node_ind.
  - rewrite TrieMerge.elements_entries. reflexivity.
  - rewrite binding_weight_node, TrieMerge.elements_node,
      !weight_sum_app, !weight_sum_shift.
    rewrite <- IHl, <- IHr. destruct o; cbn [fold_right snd]; lia.
Qed.

Local Lemma values_work_bound {A B} (w : B -> A -> N) (f : B -> A -> Cost.t B) tr b c :
  (forall b v, (w b v <= c)%N) ->
  (values_work w f tr b <= c * binding_weight (fun _ => 1) tr)%N.
Proof.
  intro Hweight. destruct tr as [|n]; [cbn [values_work binding_weight]; lia|].
  unfold values_work, binding_weight. revert b. induction n; intro b;
    cbn [values_work_ne binding_weight_ne].
  all: try pose proof (IHn b) as Hchild.
  all: try pose proof (IHn (Cost.value (f b v))) as Hchild'.
  all: try pose proof (IHn1 b) as Hl.
  all: try pose proof (IHn2 (Cost.value (TrieMerge.fold_values_ne_c f n1 b))) as Hr.
  all: try pose proof (IHn2
    (Cost.value (f (Cost.value (TrieMerge.fold_values_ne_c f n1 b)) v))) as Hr'.
  all: try pose proof (Hweight b v) as Hroot.
  all: try pose proof (Hweight (Cost.value (TrieMerge.fold_values_ne_c f n b)) v) as Hroot'.
  all: try pose proof (Hweight (Cost.value (TrieMerge.fold_values_ne_c f n1 b)) v) as Hroot'.
  all: nia.
Qed.

(** Numeric code-free folds have no emitted-key-size term. *)
Theorem fold_values_cost_numeric {A B} (f : B -> A -> Cost.t B) tr b c :
  (forall b v, (Cost.ticks (f b v) <= c)%N) ->
  (Cost.ticks (TrieMerge.fold_values_c f tr b) <=
    skeleton_nodes tr + (1 + c) * N.of_nat (TrieMerge.size tr))%N.
Proof.
  intro Hcallback. rewrite fold_values_cost.
  pose proof (values_work_bound (fun b v => Cost.ticks (f b v)) f tr b c Hcallback) as Hwork.
  rewrite binding_count_size in Hwork. nia.
Qed.

(** Map folding retains the actual callee work without materializing encoded keys. *)
Theorem map_fold_cost {K V B} (f : B -> K -> V -> Cost.t B) (m : Map.t K V) b :
  let g := fun b kv => f b (fst kv) (snd kv) in
  Cost.ticks (Map.fold_c f m b) =
    (skeleton_nodes m + N.of_nat (Map.size m) +
      values_work (fun b kv => Cost.ticks (g b kv)) g m b)%N.
Proof.
  cbn zeta. apply fold_values_cost.
Qed.

(** Numeric Map fold costs are physical-node-linear under a separate callback premise. *)
Theorem map_fold_cost_numeric {K V B} (f : B -> K -> V -> Cost.t B) (m : Map.t K V) b c :
  (forall b k v, (Cost.ticks (f b k v) <= c)%N) ->
  (Cost.ticks (Map.fold_c f m b) <=
    skeleton_nodes m + (1 + c) * N.of_nat (Map.size m))%N.
Proof.
  intro Hcallback. apply fold_values_cost_numeric. intros acc [k v]. apply Hcallback.
Qed.

Local Lemma collect_values_length {A} (tr : Trie.t A) :
  length (Cost.value (TrieMerge.fold_values_c
    (fun acc v => Cost.ret (v :: acc)) tr [])) = TrieMerge.size tr.
Proof.
  rewrite TrieMerge.fold_values_entries, TrieMerge.size_elements, TrieMerge.elements_entries.
  generalize (TrieMerge.entries tr). intro xs.
  assert (Hlength : forall acc,
    length (fold_left (fun acc pv => snd pv :: acc) xs acc) =
      (length xs + length acc)%nat).
  { induction xs as [|pv xs IH]; intro acc; [reflexivity|].
    cbn [fold_left length]. rewrite IH. cbn [length]. lia. }
  change (length (fold_left (fun acc pv => snd pv :: acc) xs []) = length xs).
  rewrite Hlength. cbn [length]. lia.
Qed.

(** Stored-pair Map enumeration is physical-node-linear and reconstructs no trie codes. *)
Theorem map_elements_cost {K V} (m : Map.t K V) :
  (Cost.ticks (Map.elements_c m) <= trie_k * (1 + skeleton_nodes m))%N.
Proof.
  unfold Map.elements_c. rewrite Cost.ticks_bind, ticks_rev_c, collect_values_length.
  pose proof (fold_values_cost_numeric
    (fun acc (v : K * V) => Cost.ret (v :: acc)) m [] 0%N
    (fun _ _ => N.le_refl 0)) as Hfold.
  pose proof (bindings_nodes m) as Hbindings.
  rewrite binding_count_size in Hbindings. unfold trie_k. nia.
Qed.

End TrieCost.
