(** * Stable group-by cost bounds

    Collection budgets retain callback and encoder costs on the keys actually visited.
    For example, reversing all buckets visits at most the original number of input values.
    Builds on: BaseIndex, BaseMapCost and the public Map cost equations. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseMapCost BaseIndex.
Import List.ListNotations.

Module IndexCost.

Local Lemma matching_count_zero {K} (E : encoding K) (HE : encoding_laws E) a ks :
  ~ In a ks ->
  fold_right (fun k n => if eqb E a k then (1 + n)%N else n) 0%N ks = 0%N.
Proof.
  induction ks as [|k ks IH]; intro Habsent; [reflexivity|].
  cbn [fold_right]. destruct (eqb_spec E HE a k) as [Heq|Hne].
  - subst k. exfalso. apply Habsent. now left.
  - apply IH. intro Hin. apply Habsent. now right.
Qed.

Local Lemma matching_count_bound {K} (E : encoding K) (HE : encoding_laws E) a ks :
  NoDup ks ->
  (fold_right (fun k n => if eqb E a k then 1 + n else n)%N 0%N ks <= 1)%N.
Proof.
  intro Hnodup. induction Hnodup as [|k ks Habsent Hnodup IH].
  - cbn [fold_right]. lia.
  - cbn [fold_right]. destruct (eqb_spec E HE a k) as [Heq|Hne].
    + subst k. rewrite (matching_count_zero E HE a ks Habsent). lia.
    + exact IH.
Qed.

Local Lemma filter_mass_cons {K V} (E : encoding K) (key : V -> K) x xs ks :
  fold_right (fun k n =>
    N.of_nat (length (filter (fun a => eqb E (key a) k) (x :: xs))) + n)%N 0%N ks =
  (fold_right (fun k n =>
    N.of_nat (length (filter (fun a => eqb E (key a) k) xs)) + n)%N 0%N ks +
    fold_right (fun k n => if eqb E (key x) k then 1 + n else n)%N 0%N ks)%N.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  cbn [fold_right]. rewrite IH. cbn [filter]. destruct (eqb E (key x) k);
    cbn [length]; rewrite ?Nat2N.inj_succ; lia.
Qed.

Local Lemma filter_mass_bound {K V} (E : encoding K) (HE : encoding_laws E)
    (key : V -> K) xs ks :
  NoDup ks ->
  (fold_right (fun k n =>
    N.of_nat (length (filter (fun a => eqb E (key a) k) xs)) + n)%N 0%N ks <=
    N.of_nat (length xs))%N.
Proof.
  intro Hnodup. induction xs as [|x xs IH].
  - assert (Hzero : fold_right (fun k n =>
      N.of_nat (length (filter (fun a : V => eqb E (key a) k) [])) + n)%N 0%N ks = 0%N).
    { clear Hnodup. induction ks as [|k ks IHks];
        cbn [fold_right filter length]; [reflexivity|exact IHks]. }
    rewrite Hzero. reflexivity.
  - rewrite filter_mass_cons.
    pose proof (matching_count_bound E HE (key x) ks Hnodup) as Hcount.
    cbn [length]. rewrite Nat2N.inj_succ. lia.
Qed.

Local Lemma filter_mass_agrees {K V} (E : encoding K) (key : V -> K) xs
    (entries : list (K * list V)) :
  (forall k bucket, In (k, bucket) entries ->
    length bucket = length (filter (fun a => eqb E (key a) k) xs)) ->
  fold_right (fun kv n => N.of_nat (length (snd kv)) + n)%N 0%N entries =
    fold_right (fun k n =>
      N.of_nat (length (filter (fun a => eqb E (key a) k) xs)) + n)%N
      0%N (List.map fst entries).
Proof.
  induction entries as [|[k bucket] rest IH]; intro Hbucket; [reflexivity|].
  cbn [fold_right List.map fst snd].
  rewrite (Hbucket k bucket (or_introl eq_refl)), IH; [reflexivity|].
  intros a bs Hin. apply Hbucket. now right.
Qed.

(** All collected bucket lengths sum to at most the input length. *)
Theorem collected_mass {K V} (E : encoding K) (HE : encoding_laws E)
    (key_c : V -> Cost.t K) xs :
  (fold_right (fun kv n => N.of_nat (length (snd kv)) + n)%N 0%N
    (Map.elements (Cost.value (Index.collect_c E key_c xs Map.empty))) <=
    N.of_nat (length xs))%N.
Proof.
  set (idx := Cost.value (Index.collect_c E key_c xs Map.empty)).
  assert (Hwf : Map.wf E idx) by (apply Index.wf_collect_c; apply Map.wf_empty).
  rewrite (filter_mass_agrees E (fun a => Cost.value (key_c a)) xs (Map.elements idx)).
  - apply filter_mass_bound; [exact HE|now apply (Map.elements_nodup E)].
  - intros k bucket Hin. apply (Map.elements_spec E HE _ _ _ Hwf) in Hin.
    pose proof (Index.find_collect_c E key_c k xs Map.empty (Map.wf_empty E)) as Hfind.
    fold idx in Hfind.
    rewrite !Index.find_equation, Hin, Map.get_empty, app_nil_r in Hfind.
    cbn in Hfind. rewrite Hfind, length_rev. reflexivity.
Qed.

(** Every collected binding consumes at least one distinct input position. *)
Theorem collected_size {K V} (E : encoding K) (HE : encoding_laws E)
    (key_c : V -> Cost.t K) xs :
  (Map.size (Cost.value (Index.collect_c E key_c xs Map.empty)) <= length xs)%nat.
Proof.
  rewrite <- (length_map (fun x => Cost.value (key_c x)) xs).
  apply (Map.size_support_bound E HE (List.map (fun x => Cost.value (key_c x)) xs)).
  - apply Index.wf_collect_c, Map.wf_empty.
  - intros k bucket Hget. destruct (Index.collect_keys E HE key_c xs k bucket Hget)
      as [x [Hin Heq]].
    apply in_map_iff. now exists x.
Qed.

(** Numeric bucket lookup retains the actual queried-key encoding charge. *)
Theorem find_cost {K V} (HC : Map.cost_laws) (E : encoding K) k (idx : Index.t K V) :
  (Cost.ticks (Index.find_c E k idx) <=
    1 + Cost.ticks (encode_c E k) + key_bits E k)%N.
Proof.
  rewrite Index.find_cost, Map.get_cost. reflexivity.
Qed.

(** Collection is linear in finite visited-key encoder, width and callback budgets. *)
Theorem collect_cost {K V} (HC : Map.cost_laws) (E : encoding K)
    (key_c : V -> Cost.t K) xs idx e b c :
  (forall x, In x xs ->
    (Cost.ticks (key_c x) <= c)%N /\
    (Cost.ticks (encode_c E (Cost.value (key_c x))) <= e)%N /\
    (key_bits E (Cost.value (key_c x)) <= b)%N) ->
  (Cost.ticks (Index.collect_c E key_c xs idx) <=
    N.of_nat (length xs) * (5 + c + 2 * (e + b)))%N.
Proof.
  intro Hkeys.
  eapply N.le_trans; [apply (Index.collect_cost E key_c xs idx c (3 + 2 * (e + b)))|].
  - intros x Hin. exact (proj1 (Hkeys x Hin)).
  - intros x m Hin. destruct (Hkeys x Hin) as [Hc [He Hb]].
    rewrite Map.update_cost. autorewrite with galois_cost.
    rewrite Map.get_cost, Map.set_cost.
    fold (key_bits E (Cost.value (key_c x))). lia.
  - nia.
Qed.

Local Lemma reversal_sum {K V} (entries : list (K * list V)) :
  fold_right (fun kv n => Cost.ticks (Index.reverse_c (snd kv)) + n)%N 0%N entries =
    fold_right (fun kv n => N.of_nat (length (snd kv)) + n)%N 0%N entries.
Proof.
  induction entries as [|kv rest IH]; cbn [fold_right];
    rewrite ?Index.reverse_cost, ?IH; reflexivity.
Qed.

(** Grouping is linear in input size times map width, plus visited encoder and callback budgets. *)
Theorem group_by_cost {K V} (HC : Map.cost_laws) (E : encoding K)
    (HE : encoding_laws E) (key_c : V -> Cost.t K) xs e b c :
  (forall x, In x xs ->
    (Cost.ticks (key_c x) <= c)%N /\
    (Cost.ticks (encode_c E (Cost.value (key_c x))) <= e)%N /\
    (key_bits E (Cost.value (key_c x)) <= b)%N) ->
  (Cost.ticks (Index.group_by_c E key_c xs) <=
    1 + N.of_nat (length xs) * (6 + c + 2 * e + 4 * b))%N.
Proof.
  intro Hkeys. rewrite Index.group_by_cost_equation.
  set (idx := Cost.value (Index.collect_c E key_c xs Map.empty)).
  assert (Hwf : Map.wf E idx) by (apply Index.wf_collect_c; apply Map.wf_empty).
  assert (Hbits : forall k bucket, Map.get E k idx = Some bucket -> (key_bits E k <= b)%N).
  { intros k bucket Hget.
    destruct (Index.collect_keys E HE key_c xs k bucket Hget) as [x [Hin Heq]].
    rewrite <- Heq. exact (proj2 (proj2 (Hkeys x Hin))). }
  pose proof (MapCost.map_numeric_cost E (@Index.reverse_c V) idx b Hwf Hbits) as Hmap.
  rewrite reversal_sum in Hmap.
  pose proof (collected_mass E HE key_c xs) as Hmass.
  pose proof (collected_size E HE key_c xs) as Hsize.
  pose proof (collect_cost HC E key_c xs Map.empty e b c Hkeys) as Hcollect.
  fold idx in Hmap, Hmass, Hsize. nia.
Qed.

End IndexCost.
