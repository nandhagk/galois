(** * Trie traversal costs

    Skeleton nodes measure physical traversal independently of binding cardinality.
    For example, a singleton at a deep key has one binding and many skeleton nodes.
    Builds on: BaseTrie, BaseTrieMerge and CostBound. *)

From Stdlib Require Import NArith Arith List Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseTrie BaseTrieMerge.

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

End TrieCost.
