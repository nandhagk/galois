(** * Trie maps

    Maps store client keys and values in a canonical trie.
    For example, enumeration returns the client key stored by insertion.
    Builds on: KeySig, TrieSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig TrieSig MapSig.
From Galois.Base Require Import Trie.


Module Datatypes.
  TimeFun option_map.
End Datatypes.

Module TrieMapCode (K : KEY_OPS) <: MAP_OPS K.
  Definition t := kmap K.t.
  Definition empty {A} : t A := PTrieCode.empty.
  Definition find {A} (p : positive) (m : t A) := option_map snd (PTrieCode.get p m).
  Definition get {A} (k : K.t) (m : t A) := option_map snd (PTrieCode.get (K.encode k) m).
  Definition set {A} (k : K.t) (a : A) (m : t A) := PTrieCode.set (K.encode k) (k, a) m.
  Definition remove {A} (k : K.t) (m : t A) := PTrieCode.remove (K.encode k) m.
  Definition merge {A B C} (f : option A -> option B -> option C) (x : t A) (y : t B) : t C :=
    PTrieCode.merge (fun a b =>
      match a, b with
      | Some (k, v), Some (_, w) => option_map (pair k) (f (Some v) (Some w))
      | Some (k, v), None => option_map (pair k) (f (Some v) None)
      | None, Some (k, w) => option_map (pair k) (f None (Some w))
      | None, None => None
      end) x y.
  Definition forall2b {A B} (f : option A -> option B -> bool) (x : t A) (y : t B) :=
    PTrieCode.forall2b (fun a b => f (option_map snd a) (option_map snd b)) x y.
  Definition existsb {A} (f : A -> bool) (x : t A) := PTrieCode.existsb (fun kv => f (snd kv)) x.
  Definition fold {A B} (f : B -> K.t -> A -> B) (x : t A) (b : B) :=
    PTrieCode.fold_values (fun acc kv => f acc (fst kv) (snd kv)) x b.
  Definition elements {A} (x : t A) : list (K.t * A) :=
    List.rev_append (fold (fun acc k a => (k, a) :: acc) x nil) nil.
End TrieMapCode.

Module TrieMapTimePilot (K : KEY_T).
  Include TrieMapCode K.
  TimeFun get.
  TimeFun set.
  Definition lookup_again {A} (k : K.t) (m : t A) := get k m.
  TimeFun lookup_again.
End TrieMapTimePilot.

Module TrieMap (K : KEY) <: MAP K.
  Include TrieMapCode K.
  Include MAP_SPEC K.
  Definition wf {A} (m : t A) : Prop :=
    forall p k a, PTrieCode.get p m = Some (k, a) -> K.encode k = p.
  Definition nodes {A} (m : t A) : nat := PTrie.nodes m.
  Definition codes {A} (m : t A) : list positive := List.map fst (PTrieCode.elements m).

  (** Enumeration drops the trie codes and retains the stored key-value pairs. *)
  Lemma elements_trie : forall A (m : t A),
    elements m = List.map snd (PTrieCode.elements m).
  Proof.
    intros A m. unfold elements, fold.
    rewrite PTrieT.F9_fold_values, rev_append_rev, app_nil_r.
    generalize (PTrieCode.elements m). intro entries.
    assert (Hfold : forall acc,
      fold_left (fun acc kv => (fst (snd kv), snd (snd kv)) :: acc) entries acc =
      List.rev (List.map snd entries) ++ acc).
    { induction entries as [|[p [k a]] rest IH]; intro acc;
        cbn [fold_left List.map List.rev fst snd].
      - reflexivity.
      - rewrite IH, <- app_assoc. reflexivity. }
    rewrite Hfold, app_nil_r, rev_involutive. reflexivity.
  Qed.

  (** Each enumerated binding occupies a skeleton node. *)
  Lemma elements_length : forall A (m : t A), length (elements m) <= nodes m.
  Proof.
    intros A m. rewrite elements_trie, length_map.
    apply PTrieT.F4_bindings.
  Qed.

  (** Stored codes count bindings even when the stored client labels are inconsistent. *)
  Lemma codes_length : forall A (m : t A), length (codes m) <= nodes m.
  Proof.
    intros A m. unfold codes. rewrite length_map.
    apply PTrieT.F4_bindings.
  Qed.

  Lemma wf_empty : forall A, wf (@empty A).
  Proof. Admitted. (* STUB *)
  Lemma wf_set : forall A k (a : A) m, wf m -> wf (set k a m).
  Proof. Admitted. (* STUB *)
  Lemma wf_remove : forall A k (m : t A), wf m -> wf (remove k m).
  Proof. Admitted. (* STUB *)
  Lemma wf_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
    wf m1 -> wf m2 -> wf (merge f m1 m2).
  Proof. Admitted. (* STUB *)
  Lemma get_empty : forall A k, get k (@empty A) = None.
  Proof. Admitted. (* STUB *)
  Lemma get_set_same : forall A k (a : A) m, get k (set k a m) = Some a.
  Proof. Admitted. (* STUB *)
  Lemma get_set_other : forall A k q (a : A) m,
    k <> q -> get k (set q a m) = get k m.
  Proof. Admitted. (* STUB *)
  Lemma get_remove_same : forall A k (m : t A), get k (remove k m) = None.
  Proof. Admitted. (* STUB *)
  Lemma get_remove_other : forall A k q (m : t A),
    k <> q -> get k (remove q m) = get k m.
  Proof. Admitted. (* STUB *)
  Lemma get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 k,
    f None None = None -> get k (merge f m1 m2) = f (get k m1) (get k m2).
  Proof. Admitted. (* STUB *)
  Lemma elements_spec : forall A (m : t A) k a, wf m ->
    (In (k, a) (elements m) <-> get k m = Some a).
  Proof. Admitted. (* STUB *)
  Lemma elements_nodup : forall A (m : t A), wf m -> NoDup (List.map fst (elements m)).
  Proof. Admitted. (* STUB *)
  Lemma fold_spec : forall A B (f : B -> K.t -> A -> B) m b,
    fold f m b = fold_left (fun acc ka => f acc (fst ka) (snd ka)) (elements m) b.
  Proof.
    intros A B f m b. unfold fold.
    rewrite PTrieT.F9_fold_values, elements_trie.
    generalize (PTrieCode.elements m). intro entries.
    revert b. induction entries as [|entry rest IH]; intro b;
      cbn [List.map fold_left]; [reflexivity|apply IH].
  Qed.
  Lemma ext : forall A (m n : t A), wf m -> wf n ->
    (forall k, get k m = get k n) -> m = n.
  Proof. Admitted. (* STUB *)
  Lemma get_find : forall A k (m : t A), get k m = find (K.encode k) m.
  Proof. Admitted. (* STUB *)
  Lemma find_empty : forall A p, find p (@empty A) = None.
  Proof. Admitted. (* STUB *)
  Lemma find_set : forall A p k (a : A) m,
  find p (set k a m) = if Pos.eqb p (K.encode k) then Some a else find p m.
  Proof. Admitted. (* STUB *)
  Lemma find_remove : forall A p k (m : t A),
  find p (remove k m) = if Pos.eqb p (K.encode k) then None else find p m.
  Proof. Admitted. (* STUB *)
  Lemma find_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
  f None None = None -> find p (merge f m1 m2) = f (find p m1) (find p m2).
  Proof. Admitted. (* STUB *)
  Lemma forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2,
  f None None = true ->
  (forall2b f m1 m2 = true <-> forall p, f (find p m1) (find p m2) = true).
  Proof. Admitted. (* STUB *)
  Lemma existsb_spec : forall A (f : A -> bool) m,
  existsb f m = true <-> exists p a, find p m = Some a /\ f a = true.
  Proof. Admitted. (* STUB *)
  Lemma wf_find : forall A (m : t A) p a, wf m -> find p m = Some a ->
  exists k, K.encode k = p.
  Proof. Admitted. (* STUB *)
  Lemma nodes_empty : forall A, nodes (@empty A) = 0.
  Proof. Admitted. (* STUB *)
  Lemma nodes_set : forall A k (a : A) m, nodes (set k a m) <= nodes m + K.bits k.
  Proof. Admitted. (* STUB *)
  Lemma nodes_remove : forall A k (m : t A), nodes (remove k m) <= nodes m.
  Proof. Admitted. (* STUB *)
  Lemma nodes_merge : forall A B C (f : option A -> option B -> option C) m1 m2,
  nodes (merge f m1 m2) <= nodes m1 + nodes m2.
  Proof. Admitted. (* STUB *)
  Lemma nodes_le_weight : forall A (m : t A), wf m -> nodes m <= weight m.
  Proof. Admitted. (* STUB *)
  Lemma codes_spec : forall A (m : t A) p, In p (codes m) <-> find p m <> None.
  Proof. Admitted. (* STUB *)
  Lemma codes_nodup : forall A (m : t A), NoDup (codes m).
  Proof. Admitted. (* STUB *)
  Lemma nodes_le_codes : forall A (m : t A),
    nodes m <= fold_right Nat.add 0 (List.map (fun p => Pos.size_nat p + 1) (codes m)).
  Proof.
    intros A m.
    unfold nodes, codes.
    rewrite List.map_map.
    exact (PTrie.nodes_le_weight (K.t * A) m).
  Qed.
  Lemma weight_set : forall A k (a : A) m, weight (set k a m) <= weight m + K.bits k + 1.
  Proof. Admitted. (* STUB *)
  Lemma weight_remove : forall A k (m : t A), weight (remove k m) <= weight m.
  Proof. Admitted. (* STUB *)
  Lemma weight_merge_l : forall A B C (f : option A -> option B -> option C) m1 m2,
    (forall b, f None b = None) -> weight (merge f m1 m2) <= weight m1.
  Proof. Admitted. (* STUB *)
End TrieMap.

Module TrieMapT (K : KEY_T) <: MAP_T K.
  Include TrieMap K.
  TimeFun find.
  TimeFun get.
  TimeFun set.
  TimeFun remove.
  TimeFun merge.
  TimeFun forall2b.
  TimeFun existsb.
  TimeFun fold.
  TimeFun elements.
  Definition c_map : N := 16 * (K.c_key + PTrieT.c_trie + PTrieT.k_fold + 1).
  Lemma T_get_le : forall A k (m : t A), (T_get k m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros A k m.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_get_le (K.t * A) (K.encode k) m) as Hget.
    unfold c_map, K.bits in *.
    time_step.
    unfold Datatypes.T_option_map.
    destruct (PTrieCode.get (K.encode k) m); time_cbn; nia.
  Qed.
  Lemma T_set_le : forall A k (a : A) m, (T_set k a m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros A k a m.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_set_le (K.t * A) (K.encode k) (k, a) m) as Hset.
    unfold c_map, K.bits in *.
    time_step.
  Qed.
  Lemma T_remove_le : forall A k (m : t A), (T_remove k m <= c_map * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros A k m.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_remove_le (K.t * A) (K.encode k) m) as Hremove.
    unfold c_map, K.bits in *.
    time_step.
  Qed.
  Lemma T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_merge f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof.
    intros A B C f T_f m1 m2 c Hf.
    unfold T_merge.
    eapply N.le_trans.
    - apply N.add_le_mono_l.
      apply PTrieT.T_merge_le with (k := (c + 4)%N).
      intros [[ka a]|] [[kb b]|]; time_cbn;
        unfold Datatypes.T_option_map;
        repeat match goal with |- context [match ?o with _ => _ end] => destruct o end;
        time_cbn; time_pose; nia.
    - unfold c_map, nodes. nia.
  Qed.
  Lemma T_forall2b_le : forall A B (f : option A -> option B -> bool) T_f m1 m2 c,
    ((forall a b, T_f a b <= c) ->
    T_forall2b f T_f m1 m2 <= c_map * (c + 1) * N.of_nat (nodes m1 + nodes m2 + 1))%N.
  Proof.
    intros A B f T_f m1 m2 c Hf.
    unfold T_forall2b.
    eapply N.le_trans.
    - apply N.add_le_mono_l.
      apply PTrieT.T_forall2b_le with (k := (c + 5)%N).
      intros [[ka a]|] [[kb b]|]; unfold Datatypes.T_option_map;
        time_simpl; time_cbn; time_pose; nia.
    - unfold c_map, nodes. nia.
  Qed.
  Lemma T_existsb_le : forall A (f : A -> bool) T_f m c,
    ((forall a, T_f a <= c) -> T_existsb f T_f m <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A f T_f m c Hf.
    unfold T_existsb.
    eapply N.le_trans.
    - apply N.add_le_mono_l.
      apply PTrieT.T_existsb_le with (k := (c + 2)%N).
      intros [k a]. time_simpl. time_cbn. specialize (Hf a). nia.
    - unfold c_map, nodes. nia.
  Qed.
  Lemma T_fold_le : forall A B (f : B -> K.t -> A -> B) T_f m b c,
    ((forall acc k a, T_f acc k a <= c) ->
    T_fold f T_f m b <= c_map * (c + 1) * N.of_nat (nodes m + 1))%N.
  Proof.
    intros A B f T_f m b c Hf.
    unfold T_fold.
    eapply N.le_trans.
    - apply N.add_le_mono_l.
      apply PTrieT.T9_fold_values with (c := (c + 3)%N).
      intros acc [k a]. time_simpl. time_cbn. specialize (Hf acc k a). nia.
    - unfold c_map, nodes. nia.
  Qed.
  Lemma T_elements_le : forall A (m : t A),
    (wf m -> T_elements m <= c_map * N.of_nat (weight m + 1))%N.
  Proof.
    intros A m Hwf.
    pose proof (PTrieT.T9_fold_values (K.t * A) (list (K.t * A))
      (fun acc kv => (fst kv, snd kv) :: acc) (fun _ _ => 4%N) m nil 4%N
      (fun _ _ => N.le_refl 4)) as Hfold.
    pose proof (List.T_rev_append_le (fold (fun acc k a => (k, a) :: acc) m nil) nil)
      as Hreverse.
    pose proof (elements_length A m) as Hlength.
    unfold elements in Hlength.
    rewrite rev_append_rev, length_app, length_rev in Hlength.
    pose proof (nodes_le_weight A m Hwf) as Hnodes.
    unfold T_elements, T_fold, c_map, nodes in *.
    time_simpl.
    change (1 + (1 + PTrieT.T_fold_values
      (fun (acc : list (K.t * A)) (kv : K.t * A) => (fst kv, snd kv) :: acc)
      (fun _ _ => 4%N) m nil +
      List.T_rev_append (fold (fun acc k a => (k, a) :: acc) m nil) nil) <=
      c_map * N.of_nat (weight m + 1))%N.
    unfold c_map. time_cbn_all. nia.
  Qed.

  (** Pointwise overhead sums to one charge per listed binding. *)
  Lemma sum_overhead {X} (f g : X -> N) (c : N) (xs : list X) :
    (forall x, (f x <= c + g x)%N) ->
    (fold_right N.add 0 (List.map f xs) <= c * N.of_nat (length xs) +
      fold_right N.add 0 (List.map g xs))%N.
  Proof.
    intro Hfg. induction xs as [|x rest IH]; time_cbn.
    - nia.
    - specialize (Hfg x). nia.
  Qed.

  (** Projecting list entries before folding agrees with projecting each callback argument. *)
  Lemma fold_left_map {X Y B} (f : B -> Y -> B) (g : X -> Y) xs b :
    fold_left f (List.map g xs) b = fold_left (fun acc x => f acc (g x)) xs b.
  Proof.
    revert b. induction xs as [|x rest IH]; intro b;
      cbn [List.map fold_left]; [reflexivity|apply IH].
  Qed.

  (** Adding a fixed callback overhead adds at most that amount per reached accumulator. *)
  Lemma fold_work_overhead {X B} (f : B -> X -> B) (T_f T_g : B -> X -> N) c :
    (forall b x, (T_g b x <= T_f b x + c)%N) ->
    forall xs b u v,
      (snd (fold_left (fun bw x => (f (fst bw) x, snd bw + T_g (fst bw) x)) xs (b, u)) + v <=
       snd (fold_left (fun bw x => (f (fst bw) x, snd bw + T_f (fst bw) x)) xs (b, v)) + u +
       c * N.of_nat (length xs))%N.
  Proof.
    intros Hfg xs. induction xs as [|x rest IH]; intros b u v; time_cbn.
    - nia.
    - specialize (IH (f b x) (u + T_g b x)%N (v + T_f b x)%N).
      specialize (Hfg b x). nia.
  Qed.

  (** Constant wrapper work is absorbed after the callback sum is bounded separately. *)
  Lemma clock_sum_bound (core wrapper absent callback n len raw work run : N) :
    (16 * (core + 1) <= wrapper)%N ->
    (callback <= absent + 5)%N -> (1 <= n)%N -> (len <= n)%N ->
    (raw <= 5 * len + work)%N ->
    (run <= core * ((callback + 1) * n + raw))%N ->
    (1 + run <= wrapper * ((absent + 1) * n + work))%N.
  Proof.
    intros Hwrapper Hcallback Hn Hlen Hraw Hrun.
    assert (Hbody : ((callback + 1) * n + raw <=
      11 * ((absent + 1) * n + work))%N) by nia.
    pose proof (N.mul_le_mono_l _ _ core Hbody) as Hscaled.
    pose proof (N.le_trans _ _ _ Hrun Hscaled) as Hrun_bound.
    assert (Hpositive : (1 <= (absent + 1) * n + work)%N) by nia.
    remember ((absent + 1) * n + work)%N as total in Hrun_bound, Hpositive |- *.
    clear Heqtotal Hcallback Hn Hlen Hraw Hrun Hbody Hscaled.
    pose proof (N.mul_le_mono_r _ _ total Hwrapper) as Hbudget.
    nia.
  Qed.

  Lemma T_merge_sum_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2,
    (T_merge f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Proof.
    intros A B C f T_f m1 m2.
    unfold T_merge.
    lazymatch goal with
    | |- context [PTrieT.T_merge ?callback ?T_callback m1 m2] =>
      pose proof (PTrieT.T_merge_sum_le (K.t * A) (K.t * B) (K.t * C)
        callback T_callback m1 m2) as Htrie;
      assert (Hcallback : forall a b,
        (T_callback a b <= T_f (option_map snd a) (option_map snd b) + 4)%N)
    end.
    { intros [[ka a]|] [[kb b]|]; time_cbn;
        unfold Datatypes.T_option_map;
        repeat match goal with |- context [match ?o with _ => _ end] => destruct o end;
        time_simpl; time_cbn; nia. }
    specialize (Hcallback None None) as Hnone.
    lazymatch type of Hcallback with
    | forall a b, (?T_callback a b <= _)%N =>
      pose proof (sum_overhead
        (fun p => T_callback (PTrieCode.get p m1) (PTrieCode.get p m2))
        (fun p => T_f (find p m1) (find p m2)) 4%N (codes m1 ++ codes m2)
        ltac:(intro p; unfold find; eapply N.le_trans;
          [exact (Hcallback (PTrieCode.get p m1) (PTrieCode.get p m2))|lia])) as Hsum
    end.
    pose proof (codes_length A m1) as Hleft.
    pose proof (codes_length B m2) as Hright.
    eapply clock_sum_bound with (core := PTrieT.c_trie)
      (len := N.of_nat (length (codes m1 ++ codes m2))).
    - unfold c_map. lia.
    - eapply N.le_trans; [exact Hnone|time_cbn; lia].
    - lia.
    - rewrite length_app. unfold nodes in *. lia.
    - eapply N.le_trans; [exact Hsum|lia].
    - exact Htrie.
  Qed.
  Lemma T_forall2b_sum_le : forall A B (f : option A -> option B -> bool) T_f m1 m2,
    (T_forall2b f T_f m1 m2 <= c_map *
      ((T_f None None + 1) * N.of_nat (nodes m1 + nodes m2 + 1) +
       fold_right N.add 0 (List.map (fun p => T_f (find p m1) (find p m2))
         (codes m1 ++ codes m2))))%N.
  Proof.
    intros A B f T_f m1 m2.
    unfold T_forall2b.
    lazymatch goal with
    | |- context [PTrieT.T_forall2b ?callback ?T_callback m1 m2] =>
      pose proof (PTrieT.T_forall2b_sum_le (K.t * A) (K.t * B)
        callback T_callback m1 m2) as Htrie;
      assert (Hcallback : forall a b,
        (T_callback a b <= T_f (option_map snd a) (option_map snd b) + 5)%N)
    end.
    { intros [[ka a]|] [[kb b]|]; unfold Datatypes.T_option_map;
        time_simpl; time_cbn; nia. }
    specialize (Hcallback None None) as Hnone.
    lazymatch type of Hcallback with
    | forall a b, (?T_callback a b <= _)%N =>
      pose proof (sum_overhead
        (fun p => T_callback (PTrieCode.get p m1) (PTrieCode.get p m2))
        (fun p => T_f (find p m1) (find p m2)) 5%N (codes m1 ++ codes m2)
        ltac:(intro p; unfold find; eapply N.le_trans;
          [exact (Hcallback (PTrieCode.get p m1) (PTrieCode.get p m2))|lia])) as Hsum
    end.
    pose proof (codes_length A m1) as Hleft.
    pose proof (codes_length B m2) as Hright.
    eapply clock_sum_bound with (core := PTrieT.c_trie)
      (len := N.of_nat (length (codes m1 ++ codes m2))).
    - unfold c_map. lia.
    - exact Hnone.
    - lia.
    - rewrite length_app. unfold nodes in *. lia.
    - exact Hsum.
    - exact Htrie.
  Qed.
  Lemma T_existsb_sum_le : forall A (f : A -> bool) T_f m,
    (T_existsb f T_f m <= c_map * (N.of_nat (nodes m + 1) +
      fold_right N.add 0 (List.map (fun p =>
        match find p m with Some a => T_f a | None => 0 end) (codes m))))%N.
  Proof.
    intros A f T_f m.
    unfold T_existsb.
    lazymatch goal with
    | |- context [PTrieT.T_existsb ?callback ?T_callback m] =>
      pose proof (PTrieT.T_existsb_sum_le (K.t * A) callback T_callback m) as Htrie;
      assert (Hcallback : forall ka, (T_callback ka <= T_f (snd ka) + 2)%N)
    end.
    { intros [k a]. time_simpl. time_cbn. nia. }
    lazymatch type of Hcallback with
    | forall ka, (?T_callback ka <= _)%N =>
      pose proof (sum_overhead
        (fun p => match PTrieCode.get p m with Some ka => T_callback ka | None => 0%N end)
        (fun p => match find p m with Some a => T_f a | None => 0%N end) 2%N (codes m)
        ltac:(intro p; unfold find; destruct (PTrieCode.get p m) as [[k a]|];
          time_cbn; [specialize (Hcallback (k, a)); time_cbn_all; nia|nia])) as Hsum
    end.
    pose proof (codes_length A m) as Hlength.
    unfold c_map, nodes, codes in *.
    nia.
  Qed.
  Lemma T_fold_sum_le : forall A B (f : B -> K.t -> A -> B) T_f m b,
    (T_fold f T_f m b <= c_map * (N.of_nat (nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (f (fst bw) (fst ka) (snd ka), snd bw + T_f (fst bw) (fst ka) (snd ka)))
        (elements m) (b, 0))))%N.
  Proof.
    intros A B f T_f m b.
    unfold T_fold.
    lazymatch goal with
    | |- context [PTrieT.T_fold_values ?callback ?T_callback m b] =>
      pose proof (PTrieT.T_fold_values_sum_le (K.t * A) B callback T_callback m b) as Htrie;
      assert (Hcallback : forall acc ka,
        (T_callback acc ka <= T_f acc (fst ka) (snd ka) + 3)%N)
    end.
    { intros acc [k a]. time_simpl. time_cbn. nia. }
    lazymatch type of Hcallback with
    | forall acc ka, (?T_callback acc ka <= _)%N =>
      pose proof (fold_work_overhead
        (fun acc ka => f acc (fst (snd ka)) (snd (snd ka)))
        (fun acc ka => T_f acc (fst (snd ka)) (snd (snd ka)))
        (fun acc ka => T_callback acc (snd ka)) 3%N
        ltac:(intros acc [p [k a]]; apply Hcallback)
        (PTrieCode.elements m) b 0%N 0%N) as Hwork
    end.
    pose proof (PTrieT.F4_bindings (K.t * A) m) as Hlength.
    rewrite elements_trie, fold_left_map.
    unfold c_map, nodes, PTrieT.bindings in *.
    nia.
  Qed.

End TrieMapT.
