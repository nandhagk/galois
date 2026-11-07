(** * Dense bidirectional interning

    A forward map and an inverse map assign consecutive positive IDs to keys.
    For example, interning [a; b; a] allocates only IDs one and two.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith PArith Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module Intern.

(** An interner stores two computational maps and the next unused positive ID. *)
Record t (K : Type) := Table {
  table : Map.t K positive;
  inverse : Map.t positive K;
  next : positive
}.
Arguments Table {K} table inverse next.
Arguments table {K} _.
Arguments inverse {K} _.
Arguments next {K} _.

(** Empty construction initializes both maps and starts allocating at one. *)
Definition empty_c {K} : Cost.t (t K) := Cost.ret (Table Map.empty Map.empty 1%positive).

(** An empty interner has no allocated IDs. *)
Definition empty {K} : t K := Cost.value empty_c.

(** Forward lookup retains the encoding callback and map costs. *)
Definition find_c {K} (E : encoding K) k (s : t K) := Map.get_c E k (table s).

(** Forward lookup returns an existing key's dense positive ID. *)
Definition find {K} (E : encoding K) k (s : t K) := Cost.value (find_c E k s).

(** Reverse lookup uses the landed positive scalar encoding. *)
Definition key_of_c {K} i (s : t K) := Map.get_c positive_encoding i (inverse s).

(** Reverse lookup returns the key stored at an allocated ID. *)
Definition key_of {K} i (s : t K) := Cost.value (key_of_c i s).

(** The reference size counts forward bindings through the costed map interface. *)
Definition size_c {K} (s : t K) := Map.size_c (table s).

(** Size counts allocated keys. *)
Definition size {K} (s : t K) := Cost.value (size_c s).

(** Tables are well formed, inverse, bounded by the frontier and dense below it. *)
Definition wf {K} (E : encoding K) (s : t K) : Prop :=
  Map.wf E (table s) /\
  Map.wf positive_encoding (inverse s) /\
  (forall k i, find E k s = Some i -> (i < next s)%positive) /\
  (forall k i, find E k s = Some i <-> key_of i s = Some k) /\
  (forall i, (i < next s)%positive -> exists k, find E k s = Some i).

(** Forward lookup is the public observation of the stored key-to-ID map. *)
Theorem find_equation {K} (E : encoding K) k (s : t K) :
  find E k s = Map.get E k (table s).
Proof.
  reflexivity.
Qed.

(** Reverse lookup is the public observation of the stored ID-to-key map. *)
Theorem key_of_equation {K} i (s : t K) :
  key_of i s = Map.get positive_encoding i (inverse s).
Proof.
  reflexivity.
Qed.

(** Well-formed interning supplies the invariant of each stored map. *)
Theorem wf_maps {K} (E : encoding K) (s : t K) :
  wf E s -> Map.wf E (table s) /\ Map.wf positive_encoding (inverse s).
Proof.
  intros [Htable [Hinverse _]]. now split.
Qed.

(** Interning charges forward lookup and both map insertions on a miss. *)
Definition intern_c {K} (E : encoding K) k (s : t K) :=
  let* old := find_c E k s in
  match old with
  | Some i => Cost.ret (i, s)
  | None =>
    let* forward := Map.set_c E k (next s) (table s) in
    let* backward := Map.set_c positive_encoding (next s) k (inverse s) in
    Cost.ret (next s, Table forward backward (Pos.succ (next s)))
  end.

(** Interning returns the existing or newly allocated ID and the resulting table. *)
Definition intern {K} (E : encoding K) k (s : t K) := Cost.value (intern_c E k s).

(** Interning reuses an old ID or allocates exactly the current frontier. *)
Theorem intern_equation {K} (E : encoding K) k (s : t K) :
  intern E k s =
  match find E k s with
  | Some i => (i, s)
  | None => (next s, Table (Map.set E k (next s) (table s))
      (Map.set positive_encoding (next s) k (inverse s)) (Pos.succ (next s)))
  end.
Proof.
  unfold intern, intern_c. autorewrite with galois_cost.
  fold (find E k s). destruct (find E k s); reflexivity.
Qed.

(** Empty interning starts with no IDs. *)
Theorem wf_empty {K} (E : encoding K) : wf E (@empty K).
Proof.
  assert (Hfind : forall k, find E k (@empty K) = None).
  { intro k. rewrite find_equation. apply Map.get_empty. }
  assert (Hkey : forall i, key_of i (@empty K) = None).
  { intro i. rewrite key_of_equation. apply Map.get_empty. }
  split; [apply Map.wf_empty|]. split; [apply Map.wf_empty|].
  split; [intros k i H; rewrite Hfind in H; discriminate H|].
  split; [intros k i; rewrite Hfind, Hkey; split; discriminate|].
  intros i Hi. change (i < 1)%positive in Hi. lia.
Qed.

(** A found key returns its old ID and the unchanged table. *)
Theorem intern_found {K} (E : encoding K) k i (s : t K) :
  find E k s = Some i -> intern E k s = (i, s).
Proof.
  intro H. rewrite intern_equation, H. reflexivity.
Qed.

(** A new key receives the old frontier and advances it by one. *)
Theorem intern_new {K} (E : encoding K) k (s : t K) :
  find E k s = None ->
  fst (intern E k s) = next s /\ next (snd (intern E k s)) = Pos.succ (next s).
Proof.
  intro H. rewrite intern_equation, H. split; reflexivity.
Qed.

(** The returned ID is readable at the interned key. *)
Theorem find_intern {K} (E : encoding K) k (s : t K) :
  wf E s -> find E k (snd (intern E k s)) = Some (fst (intern E k s)).
Proof.
  intros [Hm _]. rewrite intern_equation. destruct (find E k s) eqn:H.
  - exact H.
  - change (Map.get E k (Map.set E k (next s) (table s)) = Some (next s)).
    now apply Map.get_set_same.
Qed.

(** Interning retains every previously allocated key's ID. *)
Theorem find_intern_old {K} (E : encoding K) (HE : encoding_laws E) a k i (s : t K) :
  wf E s -> find E a s = Some i -> find E a (snd (intern E k s)) = Some i.
Proof.
  intros [Hm Hrest] Ha. rewrite intern_equation. destruct (find E k s) eqn:Hk.
  - exact Ha.
  - change (Map.get E a (Map.set E k (next s) (table s)) = Some i).
    rewrite (Map.get_set_other E HE) by
      (try assumption; intro Heq; subst a; congruence).
    exact Ha.
Qed.

(** Forward lookup has the advertised inverse in every well-formed table. *)
Theorem key_of_find {K} (E : encoding K) k i (s : t K) :
  wf E s -> find E k s = Some i -> key_of i s = Some k.
Proof.
  intros [_ [_ [_ [Hlink _]]]]. apply Hlink.
Qed.

(** Reverse lookup identifies the same key-to-ID binding in every well-formed table. *)
Theorem find_key_of {K} (E : encoding K) k i (s : t K) :
  wf E s -> key_of i s = Some k -> find E k s = Some i.
Proof.
  intros [_ [_ [_ [Hlink _]]]]. apply Hlink.
Qed.

Local Lemma fresh_inverse {K} (E : encoding K) (s : t K) :
  wf E s -> key_of (next s) s = None.
Proof.
  intros [_ [_ [Hbound [Hlink _]]]]. destruct (key_of (next s) s) as [k|] eqn:Hget.
  - apply Hlink in Hget. specialize (Hbound _ _ Hget). lia.
  - reflexivity.
Qed.

Local Lemma fresh_bound {K} (E : encoding K) k (s : t K) :
  wf E s ->
  forall a i,
  Map.get E a (Map.set E k (next s) (table s)) = Some i ->
  (i < Pos.succ (next s))%positive.
Proof.
  intros [Hm [_ [Hbound _]]] a i Hget.
  rewrite Map.get_set in Hget by exact Hm.
  destruct (eqb E a k); [injection Hget as <-; lia|].
  specialize (Hbound _ _ Hget). lia.
Qed.

Local Lemma fresh_link {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> find E k s = None ->
  forall a i,
  Map.get E a (Map.set E k (next s) (table s)) = Some i <->
  Map.get positive_encoding i (Map.set positive_encoding (next s) k (inverse s)) = Some a.
Proof.
  intros [Hm [Hinv [Hbound [Hlink Hdense]]]] Hmissing a i.
  pose proof positive_encoding_laws as HP.
  destruct (eqb_dec E HE a k) as [Heq|Hne];
    destruct (Pos.eq_dec i (next s)) as [Hi|Hi].
  - subst a i. rewrite !Map.get_set_same by assumption. split; reflexivity.
  - subst a. rewrite Map.get_set_same by exact Hm.
    rewrite Map.get_set_other by assumption.
    split.
    + intro H. injection H as H. congruence.
    + intro H. apply Hlink in H. change (find E k s = Some i) in H.
      congruence.
  - subst i. rewrite Map.get_set_other by assumption.
    rewrite Map.get_set_same by exact Hinv. split.
    + intro H. specialize (Hbound _ _ H). lia.
    + intro H. injection H as H. congruence.
  - rewrite !Map.get_set_other by assumption. apply Hlink.
Qed.

(** Interning maintains the forward/inverse bijection and dense frontier invariant. *)
Theorem intern_wf {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> wf E (snd (intern E k s)).
Proof.
  intro Hwf. pose proof Hwf as [Hm [Hinv [Hbound [Hlink Hdense]]]].
  rewrite intern_equation. destruct (find E k s) as [i|] eqn:Hmissing; [exact Hwf|].
  cbn [snd]. split; [now apply Map.wf_set|].
  split; [now apply Map.wf_set|]. split.
  - apply fresh_bound. exact Hwf.
  - split; [apply fresh_link; assumption|]. intros i Hi.
    cbn [next] in Hi. destruct (Pos.eq_dec i (next s)) as [Heq|Hne].
    + subst i. exists k. apply Map.get_set_same. exact Hm.
    + assert (Hlt : (i < next s)%positive) by lia.
      destruct (Hdense i Hlt) as [a Ha]. exists a.
      change (Map.get E a (Map.set E k (next s) (table s)) = Some i).
      rewrite (Map.get_set_other E HE) by
        (try assumption; intro Heq; subst a; congruence).
      exact Ha.
Qed.

(** The inverse lookup recovers the key at the returned ID. *)
Theorem key_of_intern {K} (E : encoding K) (HE : encoding_laws E) k (s : t K) :
  wf E s -> key_of (fst (intern E k s)) (snd (intern E k s)) = Some k.
Proof.
  intro Hwf. eapply key_of_find.
  - now apply intern_wf.
  - now apply find_intern.
Qed.

(** Every positive ID below the frontier belongs to an interned key. *)
Theorem ids_dense {K} (E : encoding K) i (s : t K) :
  wf E s -> ((i < next s)%positive <-> exists k, find E k s = Some i).
Proof.
  intros [_ [_ [Hbound [_ Hdense]]]]. split; [apply Hdense|].
  intros [k H]. exact (Hbound k i H).
Qed.

Local Lemma sorted_ids_nodup {K} (E : encoding K) (xs : list (K * positive)) :
  StronglySorted (fun a b => Map.code_compare (encode E (fst a)) (encode E (fst b)) = Lt)
    xs ->
  (forall k i a j, In (k, i) xs -> In (a, j) xs -> Pos.to_nat i = Pos.to_nat j -> k = a) ->
  NoDup (List.map (fun kv => Pos.to_nat (snd kv)) xs).
Proof.
  intro Hsort. induction Hsort as [|[k i] xs Hsort IH Hafter]; intro Hunique;
    cbn [List.map snd]; constructor.
  - intro Hin. apply in_map_iff in Hin as [[a j] [Heq Hin]].
    assert (Hka : k = a).
    { apply (Hunique k i a j); [now left|now right|symmetry; exact Heq]. }
    subst a. rewrite Forall_forall in Hafter.
    specialize (Hafter (k, j) Hin). cbn [fst] in Hafter.
    rewrite (proj2 (Map.code_compare_eq _ _) eq_refl) in Hafter. discriminate.
  - apply IH. intros a j b l Ha Hb Heq.
    apply (Hunique a j b l); [now right|now right|exact Heq].
Qed.

Local Lemma enumerated_ids_nodup {K} (E : encoding K) (HE : encoding_laws E) (s : t K) :
  wf E s -> NoDup (List.map (fun kv => Pos.to_nat (snd kv)) (Map.elements (table s))).
Proof.
  intro Hwf. pose proof (proj1 (wf_maps E s Hwf)) as Hmap.
  apply (sorted_ids_nodup E).
  - now apply Map.elements_sorted.
  - intros k i a j Hki Haj Hij. apply Pos2Nat.inj in Hij. subst j.
    apply (Map.elements_spec E HE k i _ Hmap) in Hki.
    apply (Map.elements_spec E HE a i _ Hmap) in Haj.
    rewrite <- find_equation in Hki, Haj.
    pose proof (key_of_find E k i s Hwf Hki) as Hk.
    pose proof (key_of_find E a i s Hwf Haj) as Ha. congruence.
Qed.

Local Lemma enumerated_ids_range {K} (E : encoding K) (HE : encoding_laws E) (s : t K) n :
  wf E s ->
  (In n (List.map (fun kv => Pos.to_nat (snd kv)) (Map.elements (table s))) <->
    1 <= n < Pos.to_nat (next s)).
Proof.
  intro Hwf. pose proof (proj1 (wf_maps E s Hwf)) as Hmap.
  split.
  - intro Hin. apply in_map_iff in Hin as [[k i] [Heq Hin]].
    cbn [snd] in Heq. subst n.
    apply (Map.elements_spec E HE k i _ Hmap) in Hin.
    rewrite <- find_equation in Hin.
    pose proof (proj2 (ids_dense E i s Hwf) (ex_intro _ k Hin)) as Hbound.
    apply Pos2Nat.inj_lt in Hbound. pose proof (Pos2Nat.is_pos i). lia.
  - intros [Hlower Hupper]. destruct n as [|n]; [lia|].
    assert (Hid : (Pos.of_succ_nat n < next s)%positive).
    { apply Pos2Nat.inj_lt. rewrite SuccNat2Pos.id_succ. exact Hupper. }
    destruct (proj1 (ids_dense E _ s Hwf) Hid) as [k Hfind].
    apply in_map_iff. exists (k, Pos.of_succ_nat n). split.
    + cbn [snd]. apply SuccNat2Pos.id_succ.
    + apply (Map.elements_spec E HE _ _ _ Hmap). now rewrite <- find_equation.
Qed.

(** The dense frontier is exactly one past the number of allocated keys in any well-formed table. *)
Theorem next_size {K} (E : encoding K) (HE : encoding_laws E) (s : t K) :
  wf E s -> Pos.to_nat (next s) = S (size s).
Proof.
  intro Hwf.
  set (ids := List.map (fun kv => Pos.to_nat (snd kv)) (Map.elements (table s))).
  assert (Hnodup : NoDup ids) by now apply (enumerated_ids_nodup E HE).
  assert (Hrange : forall n, In n ids <-> In n (seq 1 (Nat.pred (Pos.to_nat (next s))))).
  { intro n. unfold ids. rewrite (enumerated_ids_range E HE s n Hwf), in_seq.
    pose proof (Pos2Nat.is_pos (next s)). lia. }
  assert (Hupper : length ids <= length (seq 1 (Nat.pred (Pos.to_nat (next s))))).
  { apply NoDup_incl_length; [exact Hnodup|].
    intros n Hin. now apply Hrange. }
  assert (Hlower : length (seq 1 (Nat.pred (Pos.to_nat (next s)))) <= length ids).
  { apply NoDup_incl_length; [apply seq_NoDup|].
    intros n Hin. now apply Hrange. }
  unfold ids in Hupper, Hlower.
  rewrite length_map, length_seq in Hupper, Hlower.
  change (Pos.to_nat (next s) = S (Map.size (table s))).
  rewrite Map.size_elements. pose proof (Pos2Nat.is_pos (next s)). lia.
Qed.

(** An ID is allocated exactly when its natural value is at most the interner's size. *)
Theorem ids_size {K} (E : encoding K) (HE : encoding_laws E) i (s : t K) :
  wf E s -> (Pos.to_nat i <= size s <-> exists k, find E k s = Some i).
Proof.
  intro Hwf. rewrite <- (ids_dense E i s Hwf), Pos2Nat.inj_lt, (next_size E HE s Hwf).
  lia.
Qed.

(** List interning charges every input cell and threads allocation in input order. *)
Fixpoint intern_list_c {K} (E : encoding K) (xs : list K) (s : t K) : Cost.t (t K) :=
  match xs with
  | [] => Cost.ret s
  | k :: rest =>
    Cost.step ;;
    let* result := intern_c E k s in intern_list_c E rest (snd result)
  end.

(** List construction starts interning with the empty table. *)
Definition of_list_c {K} (E : encoding K) xs :=
  let* initial := @empty_c K in intern_list_c E xs initial.

(** List construction allocates IDs by first occurrence. *)
Definition of_list {K} (E : encoding K) xs := Cost.value (of_list_c E xs).

Local Lemma list_step {K} (E : encoding K) k rest (s : t K) :
  Cost.value (intern_list_c E (k :: rest) s) =
    Cost.value (intern_list_c E rest (snd (intern E k s))).
Proof.
  reflexivity.
Qed.

Local Lemma wf_list {K} (E : encoding K) (HE : encoding_laws E) xs (s : t K) :
  wf E s -> wf E (Cost.value (intern_list_c E xs s)).
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hwf; [exact Hwf|].
  rewrite list_step. apply IH. now apply intern_wf.
Qed.

(** Interning a list builds a well-formed dense table. *)
Theorem wf_of_list {K} (E : encoding K) (HE : encoding_laws E) xs :
  wf E (of_list E xs).
Proof.
  apply wf_list; [exact HE|apply wf_empty].
Qed.

(** The keys after interning are exactly the old keys and the supplied key. *)
Theorem intern_members {K} (E : encoding K) (HE : encoding_laws E) a k (s : t K) :
  wf E s ->
  ((exists i, find E a (snd (intern E k s)) = Some i) <->
    a = k \/ exists i, find E a s = Some i).
Proof.
  intros [Hm Hrest]. rewrite intern_equation.
  destruct (find E k s) as [j|] eqn:Hk; cbn [snd].
  - split.
    + intro H. now right.
    + intros [->|H]; [now exists j|exact H].
  - change ((exists i, Map.get E a (Map.set E k (next s) (table s)) = Some i) <->
      a = k \/ exists i, find E a s = Some i).
    rewrite Map.get_set by exact Hm.
    destruct (eqb_spec E HE a k) as [Heq|Hne].
    + split; [intro H; now left|intros _; exists (next s); reflexivity].
    + split.
      * intro H. now right.
      * intros [H|H]; [contradiction|exact H].
Qed.

Local Lemma list_members {K} (E : encoding K) (HE : encoding_laws E) xs a (s : t K) :
  wf E s ->
  ((exists i, find E a (Cost.value (intern_list_c E xs s)) = Some i) <->
    In a xs \/ exists i, find E a s = Some i).
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hwf.
  - cbn [intern_list_c]. rewrite Cost.value_ret. cbn [In]. tauto.
  - rewrite list_step, IH by now apply intern_wf.
    rewrite (intern_members E HE) by exact Hwf. cbn [In]. intuition congruence.
Qed.

(** The constructed table contains exactly the keys occurring in its input. *)
Theorem intern_list_spec {K} (E : encoding K) (HE : encoding_laws E) xs k :
  In k xs <-> exists i, find E k (of_list E xs) = Some i.
Proof.
  unfold of_list, of_list_c. rewrite Cost.value_bind. fold (@empty K).
  rewrite (list_members E HE) by apply wf_empty.
  assert (Hempty : ~ exists i, find E k (@empty K) = Some i).
  { intros [i H]. rewrite find_equation in H.
    change (Map.get E k Map.empty = Some i) in H.
    rewrite Map.get_empty in H. discriminate H. }
  tauto.
Qed.

Arguments empty_c {K} : simpl never.
Arguments empty {K} : simpl never.
(** Forward lookup has exactly the charge of the public forward-map lookup. *)
Theorem find_cost {K} (E : encoding K) k (s : t K) :
  Cost.ticks (find_c E k s) = Cost.ticks (Map.get_c E k (table s)).
Proof.
  reflexivity.
Qed.

(** Reverse lookup has exactly the charge of the public inverse-map lookup. *)
Theorem key_of_cost {K} i (s : t K) :
  Cost.ticks (key_of_c i s) =
    Cost.ticks (Map.get_c positive_encoding i (inverse s)).
Proof.
  reflexivity.
Qed.

(** A hit pays one lookup and a miss additionally pays the two public insertions. *)
Theorem intern_cost_equation {K} (E : encoding K) k (s : t K) :
  Cost.ticks (intern_c E k s) =
    (Cost.ticks (Map.get_c E k (table s)) +
      match find E k s with
      | Some _ => 0
      | None =>
        Cost.ticks (Map.set_c E k (next s) (table s)) +
        Cost.ticks (Map.set_c positive_encoding (next s) k (inverse s))
      end)%N.
Proof.
  unfold intern_c. autorewrite with galois_cost. fold (find E k s).
  destruct (find E k s); autorewrite with galois_cost;
    rewrite find_cost; lia.
Qed.

(** The three primitive map calls bound interning for every raw interner. *)
Theorem intern_cost {K} (E : encoding K) k (s : t K) :
  (Cost.ticks (intern_c E k s) <=
    Cost.ticks (Map.get_c E k (table s)) +
    Cost.ticks (Map.set_c E k (next s) (table s)) +
    Cost.ticks (Map.set_c positive_encoding (next s) k (inverse s)))%N.
Proof.
  rewrite intern_cost_equation. destruct (find E k s); lia.
Qed.

(** List interning charges one input cell and recurses on the actual updated table. *)
Theorem intern_list_cost_equation {K} (E : encoding K) xs (s : t K) :
  Cost.ticks (intern_list_c E xs s) =
    match xs with
    | [] => 0%N
    | k :: rest =>
      (1 + Cost.ticks (intern_c E k s) +
        Cost.ticks (intern_list_c E rest (snd (intern E k s))))%N
    end.
Proof.
  destruct xs; [reflexivity|].
  cbn [intern_list_c]. autorewrite with galois_cost. fold (intern E k s). lia.
Qed.

(** Empty initialization adds no ticks to list construction. *)
Theorem of_list_cost_equation {K} (E : encoding K) xs :
  Cost.ticks (of_list_c E xs) = Cost.ticks (intern_list_c E xs empty).
Proof.
  unfold of_list_c, empty_c. autorewrite with galois_cost. reflexivity.
Qed.

(** Primitive budgets on an invariant domain give a linear list-interning bound. *)
Theorem intern_list_cost {K} (E : encoding K) (I : t K -> Prop) g f b xs s :
  (forall k q, In k xs -> I q ->
    I (snd (intern E k q)) /\
    (Cost.ticks (Map.get_c E k (table q)) <= g)%N /\
    (Cost.ticks (Map.set_c E k (next q) (table q)) <= f)%N /\
    (Cost.ticks (Map.set_c positive_encoding (next q) k (inverse q)) <= b)%N) ->
  I s ->
  (Cost.ticks (intern_list_c E xs s) <= N.of_nat (length xs) * (1 + g + f + b))%N.
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hstep Hs.
  - rewrite intern_list_cost_equation. cbn [length]. lia.
  - destruct (Hstep k s (or_introl eq_refl) Hs) as [Hs' [Hg [Hf Hb]]].
    assert (Htail : forall a q, In a rest -> I q ->
      I (snd (intern E a q)) /\
      (Cost.ticks (Map.get_c E a (table q)) <= g)%N /\
      (Cost.ticks (Map.set_c E a (next q) (table q)) <= f)%N /\
      (Cost.ticks (Map.set_c positive_encoding (next q) a (inverse q)) <= b)%N).
    { intros a q Ha Hq. apply Hstep; [now right|exact Hq]. }
    specialize (IH _ Htail Hs').
    pose proof (intern_cost E k s) as Hcost.
    rewrite intern_list_cost_equation. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Primitive budgets from the empty state bound complete list construction. *)
Theorem of_list_cost {K} (E : encoding K) (I : t K -> Prop) g f b xs :
  (forall k q, In k xs -> I q ->
    I (snd (intern E k q)) /\
    (Cost.ticks (Map.get_c E k (table q)) <= g)%N /\
    (Cost.ticks (Map.set_c E k (next q) (table q)) <= f)%N /\
    (Cost.ticks (Map.set_c positive_encoding (next q) k (inverse q)) <= b)%N) ->
  I empty ->
  (Cost.ticks (of_list_c E xs) <= N.of_nat (length xs) * (1 + g + f + b))%N.
Proof.
  intros Hstep Hempty. rewrite of_list_cost_equation.
  exact (intern_list_cost E I g f b xs empty Hstep Hempty).
Qed.

Arguments find_c {K} E k s : simpl never.
Arguments find {K} E k s : simpl never.
Arguments key_of_c {K} i s : simpl never.
Arguments key_of {K} i s : simpl never.
Arguments size_c {K} s : simpl never.
Arguments size {K} s : simpl never.
Arguments intern_c {K} E k s : simpl never.
Arguments intern {K} E k s : simpl never.
Arguments of_list_c {K} E xs : simpl never.
Arguments of_list {K} E xs : simpl never.
Arguments intern_list_c {K} E xs s : simpl never.
Arguments table : simpl never.
Arguments inverse : simpl never.
Arguments next : simpl never.

End Intern.
