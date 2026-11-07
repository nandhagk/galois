(** * Dense slot maps

    Slot maps store values directly at interned positive IDs without storing client keys.
    For example, preparing a known key once lets later reads use its ID directly.
    Builds on: BaseTrie, BaseTrieMerge, BaseIntern and BaseMap. *)

From Stdlib Require Import NArith Arith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseTrie BaseTrieMerge BaseIntern BaseMap.
Import List.ListNotations Cost.Notations.

Module Slot.

(** Slot storage has no encoded client key beside its value. *)
Definition t (V : Type) := Trie.t V.
Definition empty {V} : t V := Trie.empty.
Definition get_c {V} i (m : t V) := Trie.get_c i m.
Definition get {V} i (m : t V) := Cost.value (get_c i m).
Definition set_c {V} i (v : V) (m : t V) := Trie.set_c i v m.
Definition set {V} i (v : V) (m : t V) := Cost.value (set_c i v m).
Definition remove_c {V} i (m : t V) := Trie.remove_c i m.
Definition remove {V} i (m : t V) := Cost.value (remove_c i m).
Definition elements_c {V} (m : t V) := TrieMerge.elements_c m.
Definition elements {V} (m : t V) := Cost.value (elements_c m).

(** Valid slots contain bindings only at IDs at most the interner's size. *)
Definition valid {K V} (u : Intern.t K) (m : t V) : Prop :=
  forall i v, get i m = Some v -> (Pos.to_nat i <= Intern.size u)%nat.

Definition prepare_slot_c {K} (E : encoding K) (u : Intern.t K) k := Intern.find_c E k u.
Definition prepare_slot {K} (E : encoding K) (u : Intern.t K) k :=
  Cost.value (prepare_slot_c E u k).

Definition lookup_c {K V} (E : encoding K) (u : Intern.t K) (m : t V) k :=
  let* i := prepare_slot_c E u k in
  match i with
  | None => Cost.ret None
  | Some i => get_c i m
  end.
Definition lookup {K V} (E : encoding K) (u : Intern.t K) (m : t V) k :=
  Cost.value (lookup_c E u m k).

Definition update_c {K V} (E : encoding K) (u : Intern.t K) (m : t V) k (v : V) :=
  let* i := prepare_slot_c E u k in
  match i with
  | None => Cost.ret None
  | Some i => Cost.map (@Some (t V)) (set_c i v m)
  end.
Definition update {K V} (E : encoding K) (u : Intern.t K) (m : t V) k (v : V) :=
  Cost.value (update_c E u m k v).

(** Refinement keeps slot validity, abstract well-formedness and all key lookups separate. *)
Definition refines {K V} (E : encoding K) (u : Intern.t K)
    (m : t V) (abstract : Map.t K V) : Prop :=
  valid u m /\ Map.wf E abstract /\ forall k, lookup E u m k = Map.get E k abstract.

(** Preparation returns precisely the public interner lookup. *)
Theorem prepare_equation {K} (E : encoding K) (u : Intern.t K) k :
  prepare_slot E u k = Intern.find E k u.
Proof.
  reflexivity.
Qed.

(** Key lookup uses an allocated slot and rejects an unknown key. *)
Theorem lookup_equation {K V} (E : encoding K) (u : Intern.t K) (m : t V) k :
  lookup E u m k =
    match Intern.find E k u with None => None | Some i => get i m end.
Proof.
  unfold lookup, lookup_c. autorewrite with galois_cost.
  fold (prepare_slot E u k). rewrite prepare_equation.
  destruct (Intern.find E k u); reflexivity.
Qed.

(** Updating an unknown key returns no changed slot map. *)
Theorem update_equation {K V} (E : encoding K) (u : Intern.t K) (m : t V) k v :
  update E u m k v =
    match Intern.find E k u with None => None | Some i => Some (set i v m) end.
Proof.
  unfold update, update_c. autorewrite with galois_cost.
  fold (prepare_slot E u k). rewrite prepare_equation.
  destruct (Intern.find E k u); reflexivity.
Qed.

(** Direct slot lookup charges every ID bit. *)
Theorem get_cost {V} i (m : t V) : Cost.ticks (get_c i m) = N.pos (Pos.size i).
Proof.
  apply Trie.get_cost.
Qed.

(** Direct slot insertion charges every ID bit. *)
Theorem set_cost {V} i (v : V) m : Cost.ticks (set_c i v m) = N.pos (Pos.size i).
Proof.
  apply Trie.set_cost.
Qed.

(** Direct slot removal charges every ID bit. *)
Theorem remove_cost {V} i (m : t V) : Cost.ticks (remove_c i m) = N.pos (Pos.size i).
Proof.
  apply Trie.remove_cost.
Qed.

Definition of_list_c {V} (xs : list (positive * V)) :=
  fold_left_c (fun m iv => set_c (fst iv) (snd iv) m) xs empty.
Definition of_list {V} (xs : list (positive * V)) := Cost.value (of_list_c xs).

(** List construction charges one input step and the exact ID width for every insertion. *)
Theorem of_list_cost {V} (xs : list (positive * V)) :
  Cost.ticks (of_list_c xs) =
    fold_right (fun iv total => (1 + N.pos (Pos.size (fst iv)) + total)%N) 0%N xs.
Proof.
  unfold of_list_c.
  assert (Hcost : forall ys (m : t V),
    Cost.ticks (fold_left_c (fun m iv => set_c (fst iv) (snd iv) m) ys m) =
      fold_right (fun iv total => (1 + N.pos (Pos.size (fst iv)) + total)%N) 0%N ys).
  { intro ys. induction ys as [|[i v] ys IH]; intro m.
    - apply ticks_fold_left_c_nil.
    - rewrite ticks_fold_left_c_cons, set_cost, IH. reflexivity. }
  apply Hcost.
Qed.

(** Empty slots satisfy the numeric range invariant for every interner. *)
Theorem slot_valid_empty {K V} (u : Intern.t K) : valid u (@empty V).
Proof.
  intros i v Hget. change (Trie.get i Trie.empty = Some v) in Hget.
  rewrite Trie.get_empty in Hget. discriminate.
Qed.

Local Lemma find_injective {K} (E : encoding K) (u : Intern.t K) k a i :
  Intern.wf E u -> Intern.find E k u = Some i -> Intern.find E a u = Some i -> k = a.
Proof.
  intros Hwf Hk Ha.
  pose proof (Intern.key_of_find E k i u Hwf Hk) as Hkey.
  pose proof (Intern.key_of_find E a i u Hwf Ha) as Hkey'.
  congruence.
Qed.

(** A prepared ID is in range and its direct read agrees with key lookup. *)
Theorem slot_prepare {K V} (E : encoding K) (HE : encoding_laws E) (u : Intern.t K)
    (m : t V) k i :
  Intern.wf E u -> valid u m -> prepare_slot E u k = Some i ->
  (Pos.to_nat i <= Intern.size u)%nat /\ get i m = lookup E u m k.
Proof.
  intros Hwf Hvalid Hi. rewrite prepare_equation in Hi. split.
  - apply (proj2 (Intern.ids_size E HE i u Hwf)). now exists k.
  - rewrite lookup_equation, Hi. reflexivity.
Qed.

(** Unknown keys have neither a slot lookup nor a successful update. *)
Theorem slot_outside {K V} (E : encoding K) (u : Intern.t K) (m : t V) k v :
  prepare_slot E u k = None -> lookup E u m k = None /\ update E u m k v = None.
Proof.
  rewrite prepare_equation, lookup_equation, update_equation. intro H.
  rewrite H. now split.
Qed.

(** A successful update stays in range, writes its key and frames every distinct key. *)
Theorem slot_update {K V} (E : encoding K) (HE : encoding_laws E) (u : Intern.t K)
    (m m' : t V) k v :
  Intern.wf E u -> valid u m -> update E u m k v = Some m' ->
  valid u m' /\ lookup E u m' k = Some v /\
    forall a, a <> k -> lookup E u m' a = lookup E u m a.
Proof.
  intros Hwf Hvalid Hupdate. rewrite update_equation in Hupdate.
  destruct (Intern.find E k u) as [i|] eqn:Hfind; [|discriminate].
  injection Hupdate as <-. split.
  - intros j w Hget. change (Trie.get j (Trie.set i v m) = Some w) in Hget.
    destruct (Pos.eq_dec i j) as [->|Hne].
    + apply (proj2 (Intern.ids_size E HE j u Hwf)). now exists k.
    + rewrite Trie.get_set_other in Hget by exact Hne. exact (Hvalid j w Hget).
  - split.
    + rewrite lookup_equation, Hfind. apply Trie.get_set_same.
    + intros a Hne. rewrite !lookup_equation.
      destruct (Intern.find E a u) as [j|] eqn:Ha; [|reflexivity].
      apply Trie.get_set_other. intro Heq. subst j.
      apply Hne. now apply (find_injective E u a k i).
Qed.

(** Every known key admits a successful update. *)
Theorem slot_present_update {K V} (E : encoding K) (u : Intern.t K) (m : t V) k v :
  (exists i, Intern.find E k u = Some i) -> exists m', update E u m k v = Some m'.
Proof.
  intros [i Hi]. rewrite update_equation, Hi. now exists (set i v m).
Qed.

(** Valid slots with the same key observations have the same canonical representation. *)
Theorem slot_canonical {K V} (E : encoding K) (HE : encoding_laws E) (u : Intern.t K)
    (a b : t V) :
  Intern.wf E u -> valid u a -> valid u b ->
  (forall k, lookup E u a k = lookup E u b k) -> a = b.
Proof.
  intros Hwf Ha Hb Hagree. apply Trie.extensionality. intro i.
  change (get i a = get i b).
  destruct (le_dec (Pos.to_nat i) (Intern.size u)) as [Hin|Hout].
  - destruct (proj1 (Intern.ids_size E HE i u Hwf) Hin) as [k Hfind].
    specialize (Hagree k). rewrite !lookup_equation, Hfind in Hagree. exact Hagree.
  - destruct (get i a) as [va|] eqn:Hga, (get i b) as [vb|] eqn:Hgb; try reflexivity;
      first [specialize (Ha i va Hga); lia|specialize (Hb i vb Hgb); lia].
Qed.

Definition prepare_slots_c {K} (E : encoding K) (u : Intern.t K) keys :=
  map_c (prepare_slot_c E u) keys.
Definition prepare_slots {K} (E : encoding K) (u : Intern.t K) keys :=
  Cost.value (prepare_slots_c E u keys).
Definition read_slots_c {V} (m : t V) slots :=
  map_c (fun slot => match slot with Some i => get_c i m | None => Cost.ret None end) slots.
Definition read_slots {V} (m : t V) slots := Cost.value (read_slots_c m slots).

(** Batch reads after preparation agree with key-by-key lookup on arbitrary slot maps. *)
Theorem slot_batch_refinement {K V} (E : encoding K) (u : Intern.t K) (m : t V) keys :
  read_slots m (prepare_slots E u keys) = List.map (lookup E u m) keys.
Proof.
  unfold read_slots, prepare_slots, read_slots_c, prepare_slots_c.
  rewrite !value_map_c, map_map. apply map_ext. intro k.
  fold (prepare_slot E u k). rewrite prepare_equation, lookup_equation.
  destruct (Intern.find E k u); reflexivity.
Qed.

(** Key enumeration translates raw slots through public inverse interner lookup. *)
Definition key_elements_c {K V} (u : Intern.t K) (m : t V) :=
  let* slots := elements_c m in
  filter_map_c (fun iv =>
    Cost.step ;;
    let* key := Intern.key_of_c (fst iv) u in
    Cost.ret (option_map (fun k => (k, snd iv)) key)) slots.
Definition key_elements {K V} (u : Intern.t K) (m : t V) :=
  Cost.value (key_elements_c u m).

Local Lemma slot_elements_equation {K V} (u : Intern.t K) (m : t V) :
  key_elements u m = filter_map
    (fun iv => option_map (fun k => (k, snd iv)) (Intern.key_of (fst iv) u))
    (TrieMerge.elements m).
Proof.
  unfold key_elements, key_elements_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma filter_map_members {A B} (f : A -> option B) xs b :
  In b (filter_map f xs) <-> exists a, In a xs /\ f a = Some b.
Proof.
  induction xs as [|a xs IH]; cbn [filter_map fold_right].
  - split; [contradiction|intros [x [H _]]; contradiction].
  - destruct (f a) as [v|] eqn:Hf; cbn [In].
    + rewrite IH. split.
      * intros [<-|[x [Hin Hx]]].
        -- exists a. split; [now left|exact Hf].
        -- exists x. split; [now right|exact Hx].
      * intros [x [[<-|Hin] Hx]]; [left; congruence|right; now exists x].
    + rewrite IH. split.
      * intros [x [Hin Hx]]. exists x. split; [now right|exact Hx].
      * intros [x [[<-|Hin] Hx]]; [congruence|now exists x].
Qed.

(** Key enumeration describes precisely the key lookups through allocated IDs. *)
Theorem slot_elements_spec {K V} (E : encoding K) (u : Intern.t K) (m : t V) k v :
  Intern.wf E u ->
  (In (k, v) (key_elements u m) <-> lookup E u m k = Some v).
Proof.
  intro Hwf. rewrite slot_elements_equation, filter_map_members, lookup_equation. split.
  - intros [[i w] [Hin Hkey]]. cbn [fst snd] in Hkey.
    destruct (Intern.key_of i u) as [a|] eqn:Hof; [|discriminate].
    injection Hkey as Hk Hv. subst a w.
    rewrite (Intern.find_key_of E k i u Hwf Hof). now apply TrieMerge.elements_spec.
  - destruct (Intern.find E k u) as [i|] eqn:Hfind; [|discriminate].
    intro Hget. exists (i, v). split.
    + now apply TrieMerge.elements_spec.
    + cbn [fst snd]. rewrite (Intern.key_of_find E k i u Hwf Hfind). reflexivity.
Qed.

Local Lemma slot_elements_nodup_list {K V} (E : encoding K) (u : Intern.t K)
    (xs : list (positive * V)) :
  Intern.wf E u -> NoDup (List.map fst xs) ->
  NoDup (List.map fst (filter_map
    (fun iv => option_map (fun k => (k, snd iv)) (Intern.key_of (fst iv) u)) xs)).
Proof.
  intros Hwf Hnodup. induction xs as [|[i v] xs IH]; [constructor|].
  cbn [List.map fst] in Hnodup.
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  cbn [filter_map fold_right fst snd].
  destruct (Intern.key_of i u) as [k|] eqn:Hkey; cbn [option_map List.map fst].
  - constructor; [|now apply IH]. intro Hin.
    apply in_map_iff in Hin as [[a w] [Heq Hin]]. cbn in Heq. subst a.
    apply filter_map_members in Hin as [[j z] [Hraw Hkey']].
    cbn [fst snd] in Hkey'. destruct (Intern.key_of j u) as [a|] eqn:Hj;
      [|discriminate]. injection Hkey' as Ha Hw. subst a z.
    pose proof (Intern.find_key_of E k i u Hwf Hkey) as Hi.
    pose proof (Intern.find_key_of E k j u Hwf Hj) as Hj'.
    assert (i = j) by congruence. subst j. apply Hfresh.
    apply in_map_iff. now exists (i, w).
  - now apply IH.
Qed.

(** Slot key enumeration has the lookup specification and no duplicate client keys. *)
Theorem slot_elements {K V} (E : encoding K) (u : Intern.t K) (m : t V) :
  Intern.wf E u -> valid u m ->
  (forall k v, In (k, v) (key_elements u m) <-> lookup E u m k = Some v) /\
    NoDup (List.map fst (key_elements u m)).
Proof.
  intros Hwf Hvalid. split; [intros k v; now apply (slot_elements_spec E)|].
  rewrite slot_elements_equation.
  apply (slot_elements_nodup_list E); [exact Hwf|apply TrieMerge.elements_nodup].
Qed.

(** Conversion enumerates known client keys and builds their canonical abstract map. *)
Definition to_map_c {K V} (E : encoding K) (u : Intern.t K) (m : t V) :=
  let* xs := key_elements_c u m in Map.of_list_c E xs.
Definition to_map {K V} (E : encoding K) (u : Intern.t K) (m : t V) :=
  Cost.value (to_map_c E u m).

Local Lemma matching_fold {A V} (test : A -> bool) (read : A -> V) xs v :
  (forall a, In a xs -> test a = true -> read a = v) ->
  forall old, fold_left (fun old a => if test a then Some (read a) else old) xs old =
    if existsb test xs then Some v else old.
Proof.
  intro Hvalues. induction xs as [|a xs IH]; intro old; [reflexivity|].
  cbn [fold_left existsb]. rewrite IH.
  - destruct (test a) eqn:Ha, (existsb test xs); cbn; try reflexivity.
    now rewrite (Hvalues a (or_introl eq_refl) Ha).
  - intros b Hin Hb. exact (Hvalues b (or_intror Hin) Hb).
Qed.

Local Lemma list_map_observation {K V} (E : encoding K) (HE : encoding_laws E)
    (xs : list (K * V)) (g : K -> option V) :
  (forall k v, In (k, v) xs <-> g k = Some v) ->
  forall k, Map.get E k (Map.of_list E xs) = g k.
Proof.
  intros Hspec k. rewrite Map.of_list_get.
  destruct (g k) as [v|] eqn:Hg.
  - assert (Hvalues : forall kv, In kv xs -> eqb E k (fst kv) = true -> snd kv = v).
    { intros [a w] Hin Hsame. cbn in Hsame |- *.
      apply (eqb_true_iff E HE) in Hsame. subst a.
      apply Hspec in Hin. congruence. }
    rewrite (matching_fold (fun kv => eqb E k (fst kv)) snd xs v Hvalues).
    assert (Hex : existsb (fun kv => eqb E k (fst kv)) xs = true).
    { apply existsb_exists. exists (k, v). split.
      - now apply Hspec.
      - apply eqb_refl. }
    now rewrite Hex.
  - assert (Hnone : forall kv, In kv xs -> eqb E k (fst kv) = false).
    { intros [a w] Hin. cbn [fst]. destruct (eqb E k a) eqn:Hsame; [|reflexivity].
      apply (eqb_true_iff E HE) in Hsame. subst a.
      apply Hspec in Hin. congruence. }
    assert (Hfold : forall old,
      fold_left (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old)
        xs old = old).
    { clear Hspec Hg. induction xs as [|a xs IH]; intro old; [reflexivity|].
      cbn [fold_left]. rewrite Hnone by now left.
      apply IH. intros b Hin. apply Hnone. now right. }
    apply Hfold.
Qed.

(** Converting valid slots yields a well-formed abstract map with every key lookup preserved. *)
Theorem slot_to_map_refines {K V} (E : encoding K) (HE : encoding_laws E)
    (u : Intern.t K) (m : t V) :
  Intern.wf E u -> valid u m -> refines E u m (to_map E u m).
Proof.
  intros Hwf Hvalid. unfold to_map, to_map_c. rewrite Cost.value_bind.
  change (refines E u m (Map.of_list E (key_elements u m))).
  split; [exact Hvalid|]. split; [apply Map.wf_of_list|].
  intro k. symmetry. apply (list_map_observation E HE).
  intros a v. now apply (slot_elements_spec E).
Qed.

(** Successful slot updates refine the corresponding abstract update. *)
Theorem slot_update_refines {K V} (E : encoding K) (HE : encoding_laws E)
    (u : Intern.t K) (m m' : t V) (abstract : Map.t K V) k v :
  Intern.wf E u -> refines E u m abstract -> update E u m k v = Some m' ->
  refines E u m' (Map.set E k v abstract).
Proof.
  intros Hwf [Hvalid [Hmap Hagree]] Hupdate.
  destruct (slot_update E HE u m m' k v Hwf Hvalid Hupdate) as [Hv [Hsame Hother]].
  split; [exact Hv|]. split; [now apply Map.wf_set|]. intro a.
  destruct (eqb_dec E HE a k) as [->|Hne].
  - rewrite Hsame, Map.get_set_same by exact Hmap. reflexivity.
  - rewrite Hother, (Map.get_set_other E HE) by assumption. apply Hagree.
Qed.

(** Raw list construction has the same ID lookup behavior as the positive-key abstract map. *)
Theorem of_list_get {V} (xs : list (positive * V)) i :
  get i (of_list xs) = Map.get positive_encoding i (Map.of_list positive_encoding xs).
Proof.
  unfold of_list, of_list_c. rewrite value_fold_left_c, Map.of_list_get.
  assert (Hcompare : forall j, eqb positive_encoding i j = Pos.eqb i j).
  { intro j. apply eq_true_iff_eq.
    rewrite (eqb_true_iff positive_encoding positive_encoding_laws), Pos.eqb_eq.
    reflexivity. }
  assert (Hcodes : forall (ys : list (positive * V)) (old : option V),
    fold_left (fun old iv => if eqb positive_encoding i (fst iv)
      then Some (snd iv) else old) ys old =
    fold_left (fun old iv => if Pos.eqb i (fst iv)
      then Some (snd iv) else old) ys old).
  { intro ys. induction ys as [|iv ys IH]; intro old; [reflexivity|].
    cbn [fold_left]. rewrite Hcompare. apply IH. }
  rewrite Hcodes.
  assert (Hfold : forall ys (m : t V),
    get i (fold_left (fun m iv => set (fst iv) (snd iv) m) ys m) =
      fold_left (fun old iv => if Pos.eqb i (fst iv) then Some (snd iv) else old)
        ys (get i m)).
  { intro ys. induction ys as [|[j v] ys IH]; intro m; [reflexivity|].
    cbn [fold_left fst snd]. rewrite IH.
    assert (Hset : get i (set j v m) = if Pos.eqb i j then Some v else get i m).
    { destruct (Pos.eqb i j) eqn:Hij.
      - apply Pos.eqb_eq in Hij. subst j. apply Trie.get_set_same.
      - apply Trie.get_set_other. apply Pos.eqb_neq in Hij. congruence. }
    now rewrite Hset. }
  change (get i (fold_left (fun m iv => set (fst iv) (snd iv) m) xs empty) =
    fold_left (fun old iv => if Pos.eqb i (fst iv) then Some (snd iv) else old) xs None).
  rewrite Hfold. assert (Hempty : get i (@empty V) = None) by apply Trie.get_empty.
  now rewrite Hempty.
Qed.

(** Abstract conversion prepares known bindings and ignores keys outside the interner. *)
Definition of_map_c {K V} (E : encoding K) (u : Intern.t K) (abstract : Map.t K V) :=
  let* xs := Map.elements_c abstract in
  let* prepared := filter_map_c (fun kv =>
    Cost.step ;;
    let* id := Intern.find_c E (fst kv) u in
    Cost.ret (option_map (fun i => (i, snd kv)) id)) xs in
  of_list_c prepared.
Definition of_map {K V} (E : encoding K) (u : Intern.t K) (abstract : Map.t K V) :=
  Cost.value (of_map_c E u abstract).

Local Lemma of_map_equation {K V} (E : encoding K) (u : Intern.t K)
    (abstract : Map.t K V) :
  of_map E u abstract = of_list (filter_map
    (fun kv => option_map (fun i => (i, snd kv)) (Intern.find E (fst kv) u))
    (Map.elements abstract)).
Proof.
  unfold of_map, of_map_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma prepared_elements_spec {K V} (E : encoding K) (HE : encoding_laws E)
    (u : Intern.t K) (abstract : Map.t K V) i v :
  Intern.wf E u -> Map.wf E abstract ->
  (In (i, v) (filter_map
    (fun kv => option_map (fun i => (i, snd kv)) (Intern.find E (fst kv) u))
    (Map.elements abstract)) <->
    match Intern.key_of i u with None => None | Some k => Map.get E k abstract end = Some v).
Proof.
  intros Hwf Hmap. rewrite filter_map_members. split.
  - intros [[k w] [Hin Hfind]]. cbn [fst snd] in Hfind.
    destruct (Intern.find E k u) as [j|] eqn:Hk; [|discriminate].
    injection Hfind as Hi Hw. subst j w.
    rewrite (Intern.key_of_find E k i u Hwf Hk). now apply (Map.elements_spec E HE).
  - destruct (Intern.key_of i u) as [k|] eqn:Hkey; [|discriminate].
    intro Hget. exists (k, v). split.
    + now apply (Map.elements_spec E HE).
    + cbn [fst snd]. rewrite (Intern.find_key_of E k i u Hwf Hkey). reflexivity.
Qed.

(** Conversion reads exactly the abstract binding associated with each known ID. *)
Theorem of_map_get {K V} (E : encoding K) (HE : encoding_laws E) (u : Intern.t K)
    (abstract : Map.t K V) i :
  Intern.wf E u -> Map.wf E abstract ->
  get i (of_map E u abstract) =
    match Intern.key_of i u with None => None | Some k => Map.get E k abstract end.
Proof.
  intros Hwf Hmap. rewrite of_map_equation, of_list_get.
  apply (list_map_observation positive_encoding positive_encoding_laws _
    (fun j => match Intern.key_of j u with
      | None => None | Some k => Map.get E k abstract end)).
  intros j v. now apply (prepared_elements_spec E HE).
Qed.

(** Conversion creates only allocated, in-range slots even for malformed abstract maps. *)
Theorem slot_of_map_valid {K V} (E : encoding K) (HE : encoding_laws E)
    (u : Intern.t K) (abstract : Map.t K V) :
  Intern.wf E u -> valid u (of_map E u abstract).
Proof.
  intro Hwf. rewrite of_map_equation. unfold of_list, of_list_c.
  rewrite value_fold_left_c.
  assert (Hrange : forall i v,
    In (i, v) (filter_map
      (fun kv => option_map (fun i => (i, snd kv)) (Intern.find E (fst kv) u))
      (Map.elements abstract)) -> (Pos.to_nat i <= Intern.size u)%nat).
  { intros i v Hin. apply filter_map_members in Hin as [[k w] [Hin Hfind]].
    cbn [fst snd] in Hfind. destruct (Intern.find E k u) as [j|] eqn:Hk;
      [|discriminate]. injection Hfind as Hi Hv. subst j w.
    apply (proj2 (Intern.ids_size E HE i u Hwf)). now exists k. }
  generalize dependent (filter_map
    (fun kv => option_map (fun i => (i, snd kv)) (Intern.find E (fst kv) u))
    (Map.elements abstract)).
  intros xs Hrange.
  assert (Hfold : forall m, valid u m ->
    valid u (fold_left (fun m iv => set (fst iv) (snd iv) m) xs m)).
  { induction xs as [|[i v] xs IH]; intros m Hvalid; [exact Hvalid|].
    cbn [fold_left fst snd]. apply IH.
    - intros j w Hin. apply (Hrange j w). now right.
    - intros j w Hget. change (Trie.get j (Trie.set i v m) = Some w) in Hget.
      destruct (Pos.eq_dec i j) as [Hij|Hne].
      + subst j. apply (Hrange i v). now left.
      + rewrite Trie.get_set_other in Hget by exact Hne. exact (Hvalid j w Hget). }
  apply Hfold. apply slot_valid_empty.
Qed.

(** Abstract conversion preserves precisely the key lookups inside the prepared universe. *)
Theorem slot_of_map_lookup {K V} (E : encoding K) (HE : encoding_laws E)
    (u : Intern.t K) (abstract : Map.t K V) k :
  Intern.wf E u -> Map.wf E abstract ->
  lookup E u (of_map E u abstract) k =
    match Intern.find E k u with None => None | Some _ => Map.get E k abstract end.
Proof.
  intros Hwf Hmap. rewrite lookup_equation.
  destruct (Intern.find E k u) as [i|] eqn:Hfind; [|reflexivity].
  rewrite (of_map_get E HE) by assumption.
  now rewrite (Intern.key_of_find E k i u Hwf Hfind).
Qed.

End Slot.
