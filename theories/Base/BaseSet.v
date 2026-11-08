(** * Finite sets over canonical maps

    Unit-valued maps represent finite sets without an additional invariant.
    For example, adding one key twice leaves a singleton.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module FinSet.

(** A finite set stores unit at each member's encoded position. *)
Definition t K := Map.t K unit.

(** Set well-formedness is precisely the underlying map invariant. *)
Definition wf {K} (E : encoding K) (s : t K) := Map.wf E s.

(** Empty construction has no traversal cost. *)
Definition empty_c {K} : Cost.t (t K) := Map.empty_c.

(** Empty sets contain no bindings. *)
Definition empty {K} : t K := Cost.value empty_c.

(** Membership retains the encoding and trie lookup charges. *)
Definition mem_c {K} (E : encoding K) k (s : t K) := Map.mem_c E k s.

(** Membership observes the costed presence test. *)
Definition mem {K} (E : encoding K) k (s : t K) := Cost.value (mem_c E k s).

(** Adding a member delegates to costed map insertion. *)
Definition add_c {K} (E : encoding K) k (s : t K) := Map.set_c E k tt s.

(** Adding a member stores unit at its encoded position. *)
Definition add {K} (E : encoding K) k (s : t K) := Cost.value (add_c E k s).

(** Removal retains all map traversal charges. *)
Definition remove_c {K} (E : encoding K) k (s : t K) := Map.remove_c E k s.

(** Removal deletes the queried member. *)
Definition remove {K} (E : encoding K) k (s : t K) := Cost.value (remove_c E k s).

(** Union uses the map's costed union with a constant unit callback. *)
Definition union_c {K} (s u : t K) :=
  Map.union_with_c (fun (_ _ : unit) => Cost.lift (fun _ => 1%N) (fun _ => tt) tt) s u.

(** Union retains members from either input. *)
Definition union {K} (s u : t K) := Cost.value (union_c s u).

(** Intersection uses the dedicated map intersection operation. *)
Definition inter_c {K} (s u : t K) :=
  Map.inter_with_c (fun (_ _ : unit) => Cost.lift (fun _ => 1%N) (fun _ => tt) tt) s u.

(** Intersection retains members shared by both inputs. *)
Definition inter {K} (s u : t K) := Cost.value (inter_c s u).

(** Difference retains the map's dedicated difference charges. *)
Definition diff_c {K} (s u : t K) := Map.diff_c s u.

(** Difference retains members present only on the left. *)
Definition diff {K} (s u : t K) := Cost.value (diff_c s u).

(** Inclusion checks right-hand presence for every left binding. *)
Definition subset_c {K} (s u : t K) :=
  Map.forall2_c (fun (_ : unit) o =>
    Cost.lift (fun _ => 1%N) (fun o =>
      match o with
      | Some _ => true
      | None => false
      end) o) s u.

(** Inclusion observes the short-circuit costed test. *)
Definition subset {K} (s u : t K) := Cost.value (subset_c s u).

(** Equality charges the two inclusion checks it performs. *)
Definition equal_c {K} (s u : t K) :=
  let* yes := subset_c s u in if yes then subset_c u s else Cost.ret false.

(** Equality tests inclusion in both directions. *)
Definition equal {K} (s u : t K) := Cost.value (equal_c s u).

(** Counting retains the map's per-binding charge. *)
Definition size_c {K} (s : t K) := Map.size_c s.

(** Size counts members. *)
Definition size {K} (s : t K) := Cost.value (size_c s).

(** Emptiness uses the map's constant-size root test. *)
Definition is_empty_c {K} (s : t K) := Map.is_empty_c s.

(** Emptiness observes whether the set has any member. *)
Definition is_empty {K} (s : t K) := Cost.value (is_empty_c s).

(** Key extraction charges every enumerated binding. *)
Fixpoint keys_c {K} (xs : list (K * unit)) : Cost.t (list K) :=
  match xs with
  | [] => Cost.ret []
  | (k, _) :: rest => Cost.step ;; Cost.map (cons k) (keys_c rest)
  end.

(** Enumeration includes both map enumeration and key extraction costs. *)
Definition elements_c {K} (s : t K) :=
  let* xs := Map.elements_c s in keys_c xs.

(** Enumeration retains the map's canonical key order. *)
Definition elements {K} (s : t K) := Cost.value (elements_c s).

(** Construction prepares one unit binding per input key and charges each cell. *)
Fixpoint pairs_c {K} (xs : list K) : Cost.t (list (K * unit)) :=
  match xs with
  | [] => Cost.ret []
  | k :: rest => Cost.step ;; Cost.map (cons (k, tt)) (pairs_c rest)
  end.

(** List construction composes pair preparation with map construction. *)
Definition of_list_c {K} (E : encoding K) xs :=
  let* pairs := pairs_c xs in Map.of_list_c E pairs.

(** List construction discards duplicate input keys. *)
Definition of_list {K} (E : encoding K) xs := Cost.value (of_list_c E xs).

(** Pair preparation pays exactly one tick for each original input cell. *)
Theorem pairs_cost_equation {K} (xs : list K) :
  Cost.ticks (pairs_c xs) =
    match xs with
    | [] => 0%N
    | _ :: rest => (1 + Cost.ticks (pairs_c rest))%N
    end.
Proof.
  destruct xs; [reflexivity|].
  cbn [pairs_c]. autorewrite with galois_cost. reflexivity.
Qed.

(** The pair-construction recurrence sums to exactly the input length. *)
Theorem pairs_cost {K} (xs : list K) :
  Cost.ticks (pairs_c xs) = N.of_nat (length xs).
Proof.
  induction xs as [|k rest IH]; rewrite pairs_cost_equation; [reflexivity|].
  rewrite IH. cbn [length]. rewrite Nat2N.inj_succ. lia.
Qed.

Local Lemma pairs_value {K} (xs : list K) :
  Cost.value (pairs_c xs) = List.map (fun k => (k, tt)) xs.
Proof.
  induction xs as [|k rest IH]; [reflexivity|].
  cbn [pairs_c List.map]. autorewrite with galois_cost. now rewrite IH.
Qed.

(** Set construction composes the exact pair recurrence with the actual map-list call. *)
Theorem of_list_cost_equation {K} (E : encoding K) (xs : list K) :
  Cost.ticks (of_list_c E xs) =
    (Cost.ticks (pairs_c xs) +
      Cost.ticks (Map.of_list_c E (List.map (fun k => (k, tt)) xs)))%N.
Proof.
  unfold of_list_c. rewrite Cost.ticks_bind, pairs_value. reflexivity.
Qed.

(** Construction retains pair preparation, map initialization and all insertion charges. *)
Theorem of_list_cost {K} (E : encoding K) (xs : list K) :
  Cost.ticks (of_list_c E xs) =
    (N.of_nat (length xs) + Cost.ticks (@Map.empty_c K unit) +
      Cost.ticks (fold_left_c
        (fun acc kv => Map.set_c E (fst kv) (snd kv) acc)
        (List.map (fun k => (k, tt)) xs) Map.empty))%N.
Proof.
  rewrite of_list_cost_equation, pairs_cost, Map.of_list_cost_equation. lia.
Qed.

(** The nonempty recurrence retains the first insertion and tail fold at its actual updated map. *)
Theorem of_list_cost_cons {K} (E : encoding K) k (xs : list K) :
  Cost.ticks (of_list_c E (k :: xs)) =
    (1 + Cost.ticks (pairs_c xs) + Cost.ticks (@Map.empty_c K unit) +
      1 + Cost.ticks (Map.set_c E k tt Map.empty) +
      Cost.ticks (fold_left_c
        (fun acc kv => Map.set_c E (fst kv) (snd kv) acc)
        (List.map (fun a => (a, tt)) xs) (Map.set E k tt Map.empty)))%N.
Proof.
  rewrite of_list_cost, pairs_cost. cbn [List.map length].
  rewrite ticks_fold_left_c_cons, Nat2N.inj_succ. cbn [fst snd].
  fold (Map.set E k tt Map.empty). lia.
Qed.

Local Lemma insertion_fold_cost {K} (E : encoding K) (xs : list K)
    (m : t K) e b :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N) ->
  (Cost.ticks (fold_left_c
    (fun acc kv => Map.set_c E (fst kv) (snd kv) acc)
    (List.map (fun k => (k, tt)) xs) m) <=
      N.of_nat (length xs) * (2 + e + b))%N.
Proof.
  revert m. induction xs as [|k rest IH]; intros m Hkeys.
  - cbn [List.map]. rewrite ticks_fold_left_c_nil. cbn [length]. lia.
  - cbn [List.map]. rewrite ticks_fold_left_c_cons. cbn [fst snd].
    assert (Htail : forall a, In a rest ->
      (Cost.ticks (encode_c E a) <= e)%N /\ (key_bits E a <= b)%N).
    { intros a Ha. apply Hkeys. now right. }
    specialize (IH (Map.set E k tt m) Htail).
    destruct (Hkeys k (or_introl eq_refl)) as [He Hb].
    rewrite Map.set_cost. fold (key_bits E k).
    cbn [length]. rewrite Nat2N.inj_succ. change
      (1 + (1 + Cost.ticks (encode_c E k) + key_bits E k) +
        Cost.ticks (fold_left_c
          (fun acc kv => Map.set_c E (fst kv) (snd kv) acc)
          (List.map (fun a => (a, tt)) rest) (Map.set E k tt m)) <=
        N.succ (N.of_nat (length rest)) * (2 + e + b))%N.
    nia.
Qed.

(** Finite input encoder and width budgets give a numeric linear set-construction bound. *)
Theorem of_list_numeric_cost {K} (HC : Map.cost_laws) (E : encoding K)
    (xs : list K) e b :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N) ->
  (Cost.ticks (of_list_c E xs) <= N.of_nat (length xs) * (3 + e + b))%N.
Proof.
  intro Hkeys. rewrite of_list_cost.
  assert (Hempty : Cost.ticks (@Map.empty_c K unit) = 0%N) by reflexivity.
  rewrite Hempty.
  pose proof (insertion_fold_cost E xs Map.empty e b Hkeys) as Hinsert. nia.
Qed.

(** Membership is the presence test of the underlying unit map. *)
Theorem mem_equation {K} (E : encoding K) k (s : t K) :
  mem E k s =
  match Map.get E k s with
  | Some _ => true
  | None => false
  end.
Proof.
  reflexivity.
Qed.

(** A successful lookup of unit is equivalent to membership. *)
Theorem mem_spec {K} (E : encoding K) k (s : t K) :
  mem E k s = true <-> Map.get E k s = Some tt.
Proof.
  rewrite mem_equation. destruct (Map.get E k s) as [[]|]; split; congruence.
Qed.

(** Empty sets have no members. *)
Theorem mem_empty {K} (E : encoding K) k : mem E k (@empty K) = false.
Proof.
  rewrite mem_equation. change (match Map.get E k (@Map.empty K unit) with
    Some _ => true | None => false end = false).
  now rewrite Map.get_empty.
Qed.

(** Adding a key takes the disjunction of equality and previous membership. *)
Theorem mem_add {K} (E : encoding K) k a (s : t K) :
  wf E s -> mem E k (add E a s) = (eqb E k a || mem E k s)%bool.
Proof.
  intro H. change (mem E k (Map.set E a tt s) = (eqb E k a || mem E k s)%bool).
  rewrite mem_equation, Map.get_set by exact H.
  rewrite mem_equation. destruct (eqb E k a), (Map.get E k s); reflexivity.
Qed.

(** Removing a key keeps exactly the other previous members. *)
Theorem mem_remove {K} (E : encoding K) k a (s : t K) :
  mem E k (remove E a s) = (negb (eqb E k a) && mem E k s)%bool.
Proof.
  change (mem E k (Map.remove E a s) = (negb (eqb E k a) && mem E k s)%bool).
  rewrite !mem_equation, Map.get_remove.
  destruct (eqb E k a), (Map.get E k s); reflexivity.
Qed.

(** Union contains exactly the keys in either input. *)
Theorem mem_union {K} (E : encoding K) k (s u : t K) :
  wf E s -> wf E u -> mem E k (union s u) = (mem E k s || mem E k u)%bool.
Proof.
  intros Hs Hu.
  change (mem E k (Map.union_with (fun _ _ => tt) s u) =
    (mem E k s || mem E k u)%bool).
  rewrite !mem_equation, Map.get_union_with by assumption.
  destruct (Map.get E k s), (Map.get E k u); reflexivity.
Qed.

(** Intersection contains exactly the shared keys. *)
Theorem mem_inter {K} (E : encoding K) k (s u : t K) :
  wf E s -> wf E u -> mem E k (inter s u) = (mem E k s && mem E k u)%bool.
Proof.
  intros Hs Hu.
  change (mem E k (Map.inter_with (fun _ _ => tt) s u) =
    (mem E k s && mem E k u)%bool).
  rewrite !mem_equation, Map.get_inter_with by assumption.
  destruct (Map.get E k s), (Map.get E k u); reflexivity.
Qed.

(** Difference contains exactly the left-only keys. *)
Theorem mem_diff {K} (E : encoding K) k (s u : t K) :
  wf E s -> wf E u -> mem E k (diff s u) = (mem E k s && negb (mem E k u))%bool.
Proof.
  intros Hs Hu.
  change (mem E k (Map.diff s u) = (mem E k s && negb (mem E k u))%bool).
  rewrite !mem_equation, Map.get_diff by assumption.
  destruct (Map.get E k s), (Map.get E k u); reflexivity.
Qed.

(** Empty sets satisfy the map invariant. *)
Theorem wf_empty {K} (E : encoding K) : wf E (@empty K).
Proof.
  apply Map.wf_empty.
Qed.

(** Adding a key maintains well-formedness. *)
Theorem wf_add {K} (E : encoding K) k (s : t K) : wf E s -> wf E (add E k s).
Proof.
  apply Map.wf_set.
Qed.

(** Removing a key maintains well-formedness. *)
Theorem wf_remove {K} (E : encoding K) k (s : t K) : wf E s -> wf E (remove E k s).
Proof.
  apply Map.wf_remove.
Qed.

(** Union maintains well-formedness. *)
Theorem wf_union {K} (E : encoding K) (s u : t K) :
  wf E s -> wf E u -> wf E (union s u).
Proof.
  apply Map.wf_union_with.
Qed.

(** Intersection maintains well-formedness. *)
Theorem wf_inter {K} (E : encoding K) (s u : t K) :
  wf E s -> wf E u -> wf E (inter s u).
Proof.
  apply Map.wf_inter_with.
Qed.

(** Difference maintains well-formedness. *)
Theorem wf_diff {K} (E : encoding K) (s u : t K) :
  wf E s -> wf E u -> wf E (diff s u).
Proof.
  apply Map.wf_diff.
Qed.

(** Enumeration extracts the unit map's keys in its existing order. *)
Theorem elements_equation {K} (s : t K) : elements s = List.map fst (Map.elements s).
Proof.
  unfold elements, elements_c. rewrite Cost.value_bind.
  fold (Map.elements s). generalize (Map.elements s). intro xs.
  induction xs as [|[k []] rest IH]; cbn [keys_c List.map fst];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

(** Enumeration lists exactly the members of a well-formed set. *)
Theorem elements_spec {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> (In k (elements s) <-> mem E k s = true).
Proof.
  intro H. rewrite elements_equation, mem_spec, <- (Map.elements_spec E HE k tt s H).
  split.
  - intro Hin. apply in_map_iff in Hin as [[a []] [Heq Hin]]. cbn in Heq. now subst a.
  - intro Hin. apply in_map_iff. exists (k, tt). now split.
Qed.

(** Set enumeration has strict canonical code order. *)
Theorem elements_sorted {K} (E : encoding K) (s : t K) :
  wf E s ->
  StronglySorted (fun a b => Map.code_compare (encode E a) (encode E b) = Lt)
    (elements s).
Proof.
  intro H. rewrite elements_equation.
  pose proof (Map.elements_sorted E s H) as Hsort.
  induction Hsort as [|[k []] xs Hsort IH Hafter]; cbn [List.map fst]; constructor.
  - exact IH.
  - rewrite Forall_forall in Hafter |- *. intros a Hin.
    apply in_map_iff in Hin as [[b []] [Heq Hin]]. cbn in Heq. subst b.
    exact (Hafter _ Hin).
Qed.

(** Well-formed set enumeration never repeats a key. *)
Theorem elements_nodup {K} (E : encoding K) (s : t K) :
  wf E s -> NoDup (elements s).
Proof.
  intro Hwf. rewrite elements_equation. now apply (Map.elements_nodup E).
Qed.

(** Subset tests precisely pointwise membership implication. *)
Theorem subset_spec {K} (E : encoding K) (HE : encoding_laws E) (s u : t K) :
  wf E s ->
  (subset s u = true <-> forall k, mem E k s = true -> mem E k u = true).
Proof.
  intro Hs. unfold subset, subset_c.
  change (Map.forall2 (fun (_ : unit) o =>
    match o with
    | Some _ => true
    | None => false
    end) s u = true <->
    forall k, mem E k s = true -> mem E k u = true).
  rewrite (Map.forall2_spec E HE) by exact Hs. split.
  - intros H k Hk. apply mem_spec in Hk.
    rewrite mem_equation. exact (H k tt Hk).
  - intros H k [] Hk. change (mem E k u = true).
    apply H, mem_spec. exact Hk.
Qed.

(** Equal well-formed memberships identify the same canonical set. *)
Theorem ext {K} (E : encoding K) (HE : encoding_laws E) (s u : t K) :
  wf E s -> wf E u -> (forall k, mem E k s = mem E k u) -> s = u.
Proof.
  intros Hs Hu Hmem. apply (Map.ext E HE); try assumption. intro k.
  specialize (Hmem k). rewrite !mem_equation in Hmem.
  destruct (Map.get E k s) as [[]|], (Map.get E k u) as [[]|]; congruence.
Qed.

(** Construction supplies unit-valued bindings in input order. *)
Theorem of_list_equation {K} (E : encoding K) xs :
  of_list E xs = Map.of_list E (List.map (fun k => (k, tt)) xs).
Proof.
  unfold of_list, of_list_c. rewrite Cost.value_bind.
  assert (H : Cost.value (pairs_c xs) = List.map (fun k => (k, tt)) xs).
  { induction xs as [|k rest IH]; cbn [pairs_c List.map];
      autorewrite with galois_cost; now rewrite ?IH. }
  now rewrite H.
Qed.

(** Construction produces a well-formed set. *)
Theorem wf_of_list {K} (E : encoding K) xs : wf E (of_list E xs).
Proof.
  rewrite of_list_equation. apply Map.wf_of_list.
Qed.

Local Lemma fold_members {K} (E : encoding K) k xs (o : option unit) :
  fold_left
    (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old)
    (List.map (fun a => (a, tt)) xs) o =
  if existsb (eqb E k) xs then Some tt else o.
Proof.
  revert o. induction xs as [|a rest IH]; intro o; [reflexivity|].
  cbn [List.map fold_left fst snd existsb]. rewrite IH.
  destruct (eqb E k a), (existsb (eqb E k) rest); reflexivity.
Qed.

(** Membership after construction tests the input list by encoded equality. *)
Theorem mem_of_list {K} (E : encoding K) k xs :
  mem E k (of_list E xs) = existsb (eqb E k) xs.
Proof.
  rewrite of_list_equation, mem_equation, Map.of_list_get, fold_members.
  destruct (existsb (eqb E k) xs); reflexivity.
Qed.

(** Set size equals the number of enumerated keys. *)
Theorem size_elements {K} (s : t K) : size s = length (elements s).
Proof.
  rewrite elements_equation, length_map. apply Map.size_elements.
Qed.

(** A well-formed set is empty exactly when every membership test is false. *)
Theorem is_empty_spec {K} (E : encoding K) (s : t K) :
  wf E s -> (is_empty s = true <-> forall k, mem E k s = false).
Proof.
  intro Hs. change (Map.is_empty s = true <-> forall k, mem E k s = false).
  rewrite Map.is_empty_spec by exact Hs. split; intros H k.
  - rewrite mem_equation, H. reflexivity.
  - specialize (H k). rewrite mem_equation in H.
    destruct (Map.get E k s); congruence.
Qed.

(** Set equality checks inclusion in both directions. *)
Theorem equal_spec {K} (E : encoding K) (HE : encoding_laws E) (s u : t K) :
  wf E s -> wf E u -> (equal s u = true <-> s = u).
Proof.
  intros Hs Hu.
  assert (Hvalue : equal s u = (subset s u && subset u s)%bool).
  { unfold equal, equal_c. autorewrite with galois_cost.
    fold (subset s u). destruct (subset s u); reflexivity. }
  rewrite Hvalue.
  rewrite andb_true_iff, (subset_spec E HE s u Hs), (subset_spec E HE u s Hu).
  split.
  - intros [Hsu Hus]. apply (ext E HE); try assumption. intro k.
    specialize (Hsu k). specialize (Hus k).
    destruct (mem E k s), (mem E k u); intuition discriminate.
  - intros ->. split; auto.
Qed.

(** Membership retains the sharp map encoder-plus-code-width equation. *)
Theorem mem_cost {K} (E : encoding K) k (s : t K) :
  Cost.ticks (mem_c E k s) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold mem_c. apply Map.mem_cost.
Qed.

(** Addition retains the sharp map encoder-plus-code-width equation. *)
Theorem add_cost {K} (E : encoding K) k (s : t K) :
  Cost.ticks (add_c E k s) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold add_c. apply Map.set_cost.
Qed.

(** Removal retains the sharp map encoder-plus-code-width equation. *)
Theorem remove_cost {K} (E : encoding K) k (s : t K) :
  Cost.ticks (remove_c E k s) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold remove_c. apply Map.remove_cost.
Qed.

#[export] Hint Rewrite @mem_empty @mem_add @mem_remove @mem_union @mem_inter @mem_diff
  @mem_of_list using solve [auto using wf_empty, wf_add, wf_remove, wf_union,
    wf_inter, wf_diff, wf_of_list] : galois_map.

Arguments empty_c {K} : simpl never.
Arguments empty {K} : simpl never.
Arguments mem_c {K} E k s : simpl never.
Arguments mem {K} E k s : simpl never.
Arguments add_c {K} E k s : simpl never.
Arguments add {K} E k s : simpl never.
Arguments remove_c {K} E k s : simpl never.
Arguments remove {K} E k s : simpl never.
Arguments union_c {K} s u : simpl never.
Arguments union {K} s u : simpl never.
Arguments inter_c {K} s u : simpl never.
Arguments inter {K} s u : simpl never.
Arguments diff_c {K} s u : simpl never.
Arguments diff {K} s u : simpl never.
Arguments subset_c {K} s u : simpl never.
Arguments subset {K} s u : simpl never.
Arguments equal_c {K} s u : simpl never.
Arguments equal {K} s u : simpl never.
Arguments elements_c {K} s : simpl never.
Arguments elements {K} s : simpl never.
Arguments size_c {K} s : simpl never.
Arguments size {K} s : simpl never.
Arguments is_empty_c {K} s : simpl never.
Arguments is_empty {K} s : simpl never.
Arguments of_list_c {K} E xs : simpl never.
Arguments of_list {K} E xs : simpl never.
Arguments keys_c {K} xs : simpl never.
Arguments pairs_c {K} xs : simpl never.

End FinSet.
