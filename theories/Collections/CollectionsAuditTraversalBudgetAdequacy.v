(** * Adapted traversal input budgets

    Callback laws apply to the actual arguments and retained callback bodies.
    For example, a fold prices its next call using the returned accumulator.
    Builds on: CollectionsAuditTraversalBudget and traversal adequacy. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsAuditCallback
  CollectionsAuditElements CollectionsAuditMapFold CollectionsAuditMapFoldAdequacy
  CollectionsAuditMapTraverse CollectionsAuditMapTraverseAdequacy CollectionsAuditTraversalBudget.

(** * Callback source and input bounds *)

Lemma audit_fold_budget_ne_adequate K V B E (call : B -> K -> V -> B * list E)
    work source budget
    (Hadapt : audit_external_callback_adapter
      (fun args => call (fst args) (fst (snd args)) (snd (snd args))) work source budget)
    (node : Trie.ne (K * V)) :
  forall path acc,
    fst (audit_map_fold_ne call path node acc) =
      fst (audit_map_fold_input_budget_ne call budget path node acc) /\
    audit_map_fold_calls_source work source (snd (audit_map_fold_ne call path node acc)) /\
    audit_map_fold_source_work work (snd (audit_map_fold_ne call path node acc)) <=
      snd (audit_map_fold_input_budget_ne call budget path node acc).
Proof.
  destruct Hadapt as [Hsource Hbudget].
  induction node as [r IHr | [k v] | [k v] r IHr | l IHl | l IHl r IHr |
    l IHl [k v] | l IHl [k v] r IHr]; intros path acc;
    cbn [audit_map_fold_ne audit_map_fold_input_budget_ne].
  all: try specialize (IHl (fun p => path (xO p)) acc).
  all: try (destruct (audit_map_fold_ne call (fun p => path (xO p)) l acc) as [lo le]).
  all: try (destruct (audit_map_fold_input_budget_ne call budget (fun p => path (xO p)) l acc)
    as [lb lc]).
  all: try (cbn in IHl; destruct IHl as [Heq [Hls Hlw]]; subst lb).
  all: try (destruct (call lo k v) as [co ce] eqn:Hresult;
    pose proof (Hsource (lo, (k, v)) co ce Hresult) as Hcall;
    pose proof (Hbudget (lo, (k, v)) co ce Hresult) as Hcost).
  all: try (destruct (call acc k v) as [co ce] eqn:Hresult;
    pose proof (Hsource (acc, (k, v)) co ce Hresult) as Hcall;
    pose proof (Hbudget (acc, (k, v)) co ce Hresult) as Hcost).
  all: cbn in *.
  all: try specialize (IHr (fun p => path (xI p)) co).
  all: cbn in *.
  all: try specialize (IHr (fun p => path (xI p)) lo).
  all: cbn in *.
  all: try specialize (IHr (fun p => path (xI p)) acc).
  all: try (destruct (audit_map_fold_ne call (fun p => path (xI p)) r co) as [ro re]).
  all: try (destruct (audit_map_fold_ne call (fun p => path (xI p)) r lo) as [ro re]).
  all: try (destruct (audit_map_fold_ne call (fun p => path (xI p)) r acc) as [ro re]).
  all: try (destruct (audit_map_fold_input_budget_ne call budget (fun p => path (xI p)) r co)
    as [rb rc]).
  all: try (destruct (audit_map_fold_input_budget_ne call budget (fun p => path (xI p)) r lo)
    as [rb rc]).
  all: try (destruct (audit_map_fold_input_budget_ne call budget (fun p => path (xI p)) r acc)
    as [rb rc]).
  all: cbn in *; unfold audit_map_fold_calls_source in *;
    repeat rewrite Forall_app in *;
    repeat rewrite (proj1 (audit_map_fold_work_app _ _ _ _ _ _ _)) in *;
    cbn in *; intuition; subst; try lia;
    try (repeat (first [assumption | constructor])).
  all: apply Forall_app; split; [assumption | repeat (first [assumption | constructor])].
Qed.

(** Fold budgets follow the exact accumulator and callback body at every call. *)
Theorem audit_map_fold_adapted_input_bound : audit_map_fold_adapted_input_bound_statement.
Proof.
  intros K V B E call work source budget [|node] acc Hadapt;
    cbn [audit_map_fold audit_map_fold_input_budget].
  - cbn; split; [constructor | lia].
  - exact (proj2 (audit_fold_budget_ne_adequate K V B E call work source budget Hadapt node _ acc)).
Qed.

Definition audit_transform_entries_budget {K V} (budget : V -> nat)
    (entries : list (positive * (K * V))) : nat :=
  fold_right (fun entry total => budget (snd (snd entry)) + total) 0 entries.

Lemma audit_transform_entries_budget_app K V (budget : V -> nat)
    (xs ys : list (positive * (K * V))) :
  audit_transform_entries_budget budget (xs ++ ys) =
    audit_transform_entries_budget budget xs + audit_transform_entries_budget budget ys.
Proof.
  unfold audit_transform_entries_budget.
  induction xs as [|x rest IH]; cbn; lia.
Qed.

Lemma audit_transform_entries_budget_lift K V (budget : V -> nat) path
    (xs : list (positive * (K * V))) :
  audit_transform_entries_budget budget (map (Trie.lift path) xs) =
    audit_transform_entries_budget budget xs.
Proof.
  unfold audit_transform_entries_budget.
  induction xs as [|[position [key value]] rest IH]; cbn [List.map Trie.lift] in *; cbn in *; lia.
Qed.

Lemma audit_transform_input_sum K V (budget : V -> nat) (input : Map.t K V) :
  fold_right (fun binding total => budget (snd binding) + total) 0 (Map.elements input) =
    audit_transform_entries_budget budget (Trie.entries input).
Proof.
  unfold Map.elements; rewrite Trie.elements_entries.
  unfold audit_transform_entries_budget.
  induction (Trie.entries input) as [|[position [key value]] rest IH]; cbn in *; lia.
Qed.

Lemma audit_transform_budget_ne_adequate K V W E (call : V -> W * list E)
    work source budget (Hadapt : audit_external_callback_adapter call work source budget)
    (node : Trie.ne (K * V)) :
  audit_map_transform_calls_source work source (snd (audit_map_transform_ne call node)) /\
  audit_map_transform_child_work work (snd (audit_map_transform_ne call node)) <=
    audit_transform_entries_budget budget (Trie.entries_ne node).
Proof.
  destruct Hadapt as [Hsource Hbudget].
  induction node as [r IHr | [k v] | [k v] r IHr | l IHl | l IHl r IHr |
    l IHl [k v] | l IHl [k v] r IHr]; cbn [audit_map_transform_ne Trie.entries_ne].
  all: try (destruct (audit_map_transform_ne call l) as [lo le]).
  all: try (destruct (audit_map_transform_ne call r) as [ro re]).
  all: try (destruct (call v) as [value ce] eqn:Hresult;
    pose proof (Hsource v value ce Hresult) as Hcall;
    pose proof (Hbudget v value ce Hresult) as Hcost).
  all: cbn in *; unfold audit_map_transform_calls_source in *;
    repeat rewrite Forall_app in *;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _)) in *;
    repeat rewrite audit_transform_entries_budget_app in *;
    repeat rewrite audit_transform_entries_budget_lift in *;
    cbn [audit_transform_entries_budget] in *; cbn in *; intuition; try lia;
    try (repeat (first [assumption | constructor])).
  all: try (fold (audit_transform_entries_budget budget) in *;
    repeat rewrite audit_transform_entries_budget_lift in *;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _)) in *; cbn in *; lia).
  all: repeat (first [assumption | progress (apply Forall_app; split) | constructor]).
  all: pose proof (audit_transform_entries_budget_lift K V budget xI (Trie.entries_ne r)) as Hlift;
    unfold audit_transform_entries_budget in Hlift; rewrite Hlift;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _)); cbn;
    unfold audit_transform_entries_budget in *; lia.
Qed.

(** Mapper budgets cover each actual callback and its source work. *)
Theorem audit_map_transform_adapted_input_bound :
  audit_map_transform_adapted_input_bound_statement.
Proof.
  intros K V W E call work source budget [|node] Hadapt;
    unfold audit_map_transform_input_budget; cbn [audit_map_transform audit_trie_nodes].
  - cbn [Map.elements Trie.elements Trie.fold Trie.fold_path audit_elements_work
      audit_map_transform_calls_source audit_map_transform_source_work]; cbn;
      split; [constructor | lia].
  - pose proof (audit_transform_budget_ne_adequate K V W E call work source budget Hadapt node)
      as [Hsource Hchild].
    pose proof (audit_map_transform_source_bound K V W E call work (Trie.Nodes node)) as Hwork.
    cbn [audit_map_transform audit_trie_nodes] in Hwork.
    rewrite audit_transform_input_sum; cbn [Trie.entries].
    split; [exact Hsource |].
    eapply Nat.le_trans; [exact Hwork |].
    apply Nat.add_le_mono_l; exact Hchild.
Qed.

Definition audit_pair_entries_budget {K V} (budget : V * V -> nat) (value : V)
    (entries : list (positive * (K * V))) : nat :=
  fold_right (fun entry total => budget (value, snd (snd entry)) + total) 0 entries.

Definition audit_cross_entries_budget {K V} (budget : V * V -> nat)
    (left right : list (positive * (K * V))) : nat :=
  fold_right (fun entry total =>
    audit_pair_entries_budget budget (snd (snd entry)) right + total) 0 left.

Lemma audit_pair_entries_budget_app K V (budget : V * V -> nat) value
    (xs ys : list (positive * (K * V))) :
  audit_pair_entries_budget budget value (xs ++ ys) =
    audit_pair_entries_budget budget value xs + audit_pair_entries_budget budget value ys.
Proof.
  unfold audit_pair_entries_budget; induction xs as [|x rest IH]; cbn; lia.
Qed.

Lemma audit_pair_entries_budget_lift K V (budget : V * V -> nat) value path
    (xs : list (positive * (K * V))) :
  audit_pair_entries_budget budget value (map (Trie.lift path) xs) =
    audit_pair_entries_budget budget value xs.
Proof.
  unfold audit_pair_entries_budget.
  induction xs as [|[position [key v]] rest IH]; cbn [List.map Trie.lift] in *; cbn in *; lia.
Qed.

Lemma audit_cross_entries_budget_app K V (budget : V * V -> nat) right
    (xs ys : list (positive * (K * V))) :
  audit_cross_entries_budget budget (xs ++ ys) right =
    audit_cross_entries_budget budget xs right + audit_cross_entries_budget budget ys right.
Proof.
  unfold audit_cross_entries_budget; induction xs as [|x rest IH]; cbn; lia.
Qed.

Lemma audit_cross_entries_budget_lift K V (budget : V * V -> nat) right path
    (xs : list (positive * (K * V))) :
  audit_cross_entries_budget budget (map (Trie.lift path) xs) right =
    audit_cross_entries_budget budget xs right.
Proof.
  unfold audit_cross_entries_budget.
  induction xs as [|[position [key v]] rest IH]; cbn [List.map Trie.lift] in *; cbn in *; lia.
Qed.

Lemma audit_cross_entries_budget_empty K V (budget : V * V -> nat)
    (xs : list (positive * (K * V))) : audit_cross_entries_budget budget xs nil = 0.
Proof.
  unfold audit_cross_entries_budget, audit_pair_entries_budget.
  induction xs as [|x rest IH]; cbn in *; lia.
Qed.

Lemma audit_pair_entries_children K V (budget : V * V -> nat) value
    (node : Trie.ne (K * V)) :
  audit_pair_entries_budget budget value (Trie.entries (Trie.left (Trie.Nodes node))) +
    audit_pair_entries_budget budget value (Trie.entries (Trie.right (Trie.Nodes node))) <=
      audit_pair_entries_budget budget value (Trie.entries_ne node) /\
  (forall key v, Trie.value (Trie.Nodes node) = Some (key, v) ->
    budget (value, v) <= audit_pair_entries_budget budget value (Trie.entries_ne node)).
Proof.
  destruct node as [r | [k v] | [k v] r | l | l r | l [k v] | l [k v] r];
    cbn [Trie.left Trie.right Trie.value Trie.entries Trie.entries_ne];
    repeat rewrite audit_pair_entries_budget_app;
    repeat rewrite audit_pair_entries_budget_lift;
    cbn [audit_pair_entries_budget]; cbn; split; try lia;
    try (intros key w Hvalue; inversion Hvalue; subst; lia).
  all: pose proof (audit_pair_entries_budget_lift K V budget value xI (Trie.entries_ne r)) as Hlift;
    unfold audit_pair_entries_budget in Hlift; rewrite Hlift;
    unfold audit_pair_entries_budget in *; lia.
Qed.

Lemma audit_cross_entries_mono K V (budget : V * V -> nat)
    (left right smaller : list (positive * (K * V))) :
  (forall value, audit_pair_entries_budget budget value smaller <=
    audit_pair_entries_budget budget value right) ->
  audit_cross_entries_budget budget left smaller <= audit_cross_entries_budget budget left right.
Proof.
  intro Hpoint; unfold audit_cross_entries_budget.
  induction left as [|[position [key value]] rest IH]; cbn; try lia.
  pose proof (Hpoint value); lia.
Qed.

Lemma audit_union_input_sum K V (budget : V * V -> nat) (left right : Map.t K V) :
  fold_right (fun first total =>
    fold_right (fun second subtotal => budget (snd first, snd second) + subtotal) 0
      (Map.elements right) + total) 0 (Map.elements left) =
  audit_cross_entries_budget budget (Trie.entries left) (Trie.entries right).
Proof.
  unfold Map.elements; repeat rewrite Trie.elements_entries.
  unfold audit_cross_entries_budget, audit_pair_entries_budget.
  induction (Trie.entries left) as [|[p [k v]] rest IH]; cbn; try reflexivity.
  rewrite IH; f_equal.
  clear IH; induction (Trie.entries right) as [|[q [j w]] tail IHright]; cbn; try congruence.
Qed.

Lemma audit_union_value_budget K V E (call : V -> V -> V * list E)
    work source budget
    (Hadapt : audit_external_callback_adapter (fun pair => call (fst pair) (snd pair))
      work source budget) (a : option (K * V)) (other : Map.t K V) :
  audit_map_union_calls_source work source
    (snd (audit_map_union_value call a (Trie.value other))) /\
  audit_map_union_child_work work (snd (audit_map_union_value call a (Trie.value other))) <=
    match a with
    | None => 0
    | Some (_, value) => audit_pair_entries_budget budget value (Trie.entries other)
    end.
Proof.
  destruct Hadapt as [Hsource Hbudget].
  destruct a as [[key value]|]; destruct other as [|node];
    cbn [Trie.entries].
  - cbn [audit_map_union_calls_source audit_map_union_child_work]; cbn; split; [constructor | lia].
  - destruct (Trie.value (Trie.Nodes node)) as [[other_key other_value]|] eqn:Hvalue.
    + destruct (call value other_value) as [result events] eqn:Hcall.
      pose proof (Hsource (value, other_value) result events Hcall) as Hsrc.
      pose proof (Hbudget (value, other_value) result events Hcall) as Hcost.
      pose proof (proj2 (audit_pair_entries_children K V budget value node)
        other_key other_value Hvalue) as Hpresent.
      cbn [audit_map_union_value]; rewrite Hcall;
        cbn [audit_map_union_calls_source audit_map_union_child_work]; cbn; split.
      * repeat constructor; exact Hsrc.
      * lia.
    + cbn [audit_map_union_calls_source audit_map_union_child_work]; cbn;
        split; [constructor | lia].
  - cbn [audit_map_union_calls_source audit_map_union_child_work]; cbn; split; [constructor | lia].
  - destruct (Trie.value (Trie.Nodes node)) as [[other_key other_value]|];
      cbn [audit_map_union_calls_source audit_map_union_child_work audit_map_union_value];
      cbn; split; [constructor | lia | constructor | lia].
Qed.

Lemma audit_union_budget_ne_adequate K V E (call : V -> V -> V * list E)
    work source budget
    (Hadapt : audit_external_callback_adapter (fun pair => call (fst pair) (snd pair))
      work source budget) (node : Trie.ne (K * V)) :
  forall other,
    audit_map_union_calls_source work source (snd (audit_map_union_ne call node other)) /\
    audit_map_union_child_work work (snd (audit_map_union_ne call node other)) <=
      audit_cross_entries_budget budget (Trie.entries_ne node) (Trie.entries other).
Proof.
  induction node as [r IHr | [k v] | [k v] r IHr | l IHl | l IHl r IHr |
    l IHl [k v] | l IHl [k v] r IHr]; intros [|other]; cbn [audit_map_union_ne].
  all: try (cbn [audit_map_union_calls_source audit_map_union_child_work]; cbn;
    split; [repeat constructor | lia]).
  all: assert (Hleft : forall entries,
      audit_cross_entries_budget budget entries (Trie.entries (Trie.left (Trie.Nodes other))) <=
      audit_cross_entries_budget budget entries (Trie.entries_ne other)) by
    (intro entries; apply audit_cross_entries_mono; intro value;
     pose proof (proj1 (audit_pair_entries_children K V budget value other)); lia).
  all: assert (Hright : forall entries,
      audit_cross_entries_budget budget entries (Trie.entries (Trie.right (Trie.Nodes other))) <=
      audit_cross_entries_budget budget entries (Trie.entries_ne other)) by
    (intro entries; apply audit_cross_entries_mono; intro value;
     pose proof (proj1 (audit_pair_entries_children K V budget value other)); lia).
  all: try specialize (IHl (Trie.left (Trie.Nodes other))).
  all: try specialize (IHr (Trie.right (Trie.Nodes other))).
  all: try (destruct (audit_map_union_ne call l (Trie.left (Trie.Nodes other))) as [lo le]).
  all: try (destruct (audit_map_union_ne call r (Trie.right (Trie.Nodes other))) as [ro re]).
  all:
    match goal with
    | |- context [audit_map_union_value ?f ?a (Trie.value ?input)] =>
      pose proof (audit_union_value_budget K V E f work source budget Hadapt a
        input) as Hvalue;
      destruct (audit_map_union_value f a (Trie.value input)) as [vo ve]
    end.
  all: cbn in Hvalue; cbn [Trie.entries_ne] in *;
    repeat rewrite audit_cross_entries_budget_app in *;
    repeat rewrite audit_cross_entries_budget_lift in *;
    cbn in *; unfold audit_map_union_calls_source in *;
    repeat rewrite Forall_app in *;
    repeat rewrite (proj2 (audit_map_union_work_app _ _ _ _ _ _)) in *;
    cbn in *; intuition; try lia;
    try (repeat (first [assumption | progress (apply Forall_app; split) | constructor])).
  all: try (pose proof (Hleft (Trie.entries_ne l)); pose proof (Hright (Trie.entries_ne r))).
  all: try (pose proof (Hleft (Trie.entries_ne l))).
  all: try (pose proof (Hright (Trie.entries_ne r))).
  all: try (repeat rewrite (proj2 (audit_map_union_work_app _ _ _ _ _ _)) in *;
    cbn in *; lia).
  all: pose proof (audit_cross_entries_budget_lift K V budget (Trie.entries_ne other) xI
      (Trie.entries_ne r)) as Hlift;
    unfold audit_cross_entries_budget, audit_pair_entries_budget in Hlift;
    rewrite Hlift; unfold audit_cross_entries_budget, audit_pair_entries_budget in *; lia.
Qed.

(** Union budgets cover each actual overlap callback using both original inputs. *)
Theorem audit_map_union_adapted_input_bound : audit_map_union_adapted_input_bound_statement.
Proof.
  intros K V E call work source budget [|node] right Hadapt;
    unfold audit_map_union_input_budget; cbn [audit_map_union audit_trie_nodes].
  - cbn [Map.elements Trie.elements Trie.fold Trie.fold_path audit_map_union_calls_source
      audit_map_union_source_work]; cbn; split; [repeat constructor | lia].
  - pose proof (audit_union_budget_ne_adequate K V E call work source budget Hadapt node right)
      as [Hsource Hchild].
    pose proof (audit_map_union_source_bound K V E call work (Trie.Nodes node) right) as Hwork.
    unfold audit_map_union in Hwork; cbn [audit_trie_nodes] in Hwork.
    rewrite audit_union_input_sum; cbn [Trie.entries].
    destruct (audit_map_union_ne call node right) as [out events].
    cbn in *.
    split.
    + unfold audit_map_union_calls_source in *; cbn; constructor; [exact I | exact Hsource].
    + eapply Nat.le_trans; [exact Hwork |].
      apply le_n_S; apply Nat.add_le_mono_l; exact Hchild.
Qed.
