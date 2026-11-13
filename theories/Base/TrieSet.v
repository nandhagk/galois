(** * Trie sets

    Unit-valued maps represent finite sets.
    For example, adding one key twice leaves a singleton.
    Builds on: SetSig and MapSig. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig TrieSig MapSig SetSig.
From Galois.Base Require Import Trie.

Module TrieSetCode (K : KEY_OPS) <: SET_OPS K.
  Definition t := PTrieCode.t K.t.
  Definition empty : t := PTrieCode.empty.
  Definition has (p : positive) (s : t) :=
    match PTrieCode.get p s with Some _ => true | None => false end.
  Definition mem (k : K.t) (s : t) :=
    match PTrieCode.get (K.encode k) s with Some _ => true | None => false end.
  Definition add (k : K.t) (s : t) := PTrieCode.set (K.encode k) k s.
  Definition remove (k : K.t) (s : t) := PTrieCode.remove (K.encode k) s.
  Definition union (s u : t) :=
    PTrieCode.merge (fun a b => match a with Some _ => a | None => b end) s u.
  Definition inter (s u : t) :=
    PTrieCode.merge (fun a b => match b with Some _ => a | None => None end) s u.
  Definition diff (s u : t) :=
    PTrieCode.merge (fun a b => match b with Some _ => None | None => a end) s u.
  Definition subset (s u : t) :=
    PTrieCode.forall2 (fun _ b => match b with Some _ => true | None => false end) s u.
  Definition equal (s u : t) := andb (subset s u) (subset u s).
  Definition fold {A} (f : A -> K.t -> A) (s : t) (a : A) :=
    PTrieCode.fold_values f s a.
  Definition elements (s : t) := List.rev_append (fold (fun acc k => k :: acc) s nil) nil.
End TrieSetCode.

Module TrieSet (K : KEY) <: SET K.
  Include TrieSetCode K.
  Include SET_SPEC K.
  Definition wf (s : t) : Prop :=
    forall p k, PTrieCode.get p s = Some k -> K.encode k = p.
  Definition nodes (s : t) : nat := PTrie.nodes s.

  (** Enumeration keeps stored keys in trie order without rebuilding their codes. *)
  Lemma elements_trie : forall s, elements s = List.map snd (PTrieCode.elements s).
  Proof.
    intro s. unfold elements, fold.
    rewrite PTrieT.F9_fold_values, rev_append_rev, app_nil_r.
    generalize (PTrieCode.elements s). intro entries.
    assert (Hfold : forall acc,
      fold_left (fun acc kv => snd kv :: acc) entries acc =
      List.rev (List.map snd entries) ++ acc).
    { induction entries as [|[p k] rest IH]; intro acc;
        cbn [fold_left List.map List.rev snd].
      - reflexivity.
      - rewrite IH, <- app_assoc. reflexivity. }
    rewrite Hfold, app_nil_r, rev_involutive. reflexivity.
  Qed.

  (** Each enumerated member occupies a skeleton node. *)
  Lemma elements_length : forall s, length (elements s) <= nodes s.
  Proof.
    intro s. rewrite elements_trie, length_map.
    apply PTrieT.F4_bindings.
  Qed.

  Lemma wf_empty : wf empty.
  Proof. Admitted. (* STUB *)
  Lemma wf_add : forall k s, wf s -> wf (add k s).
  Proof. Admitted. (* STUB *)
  Lemma wf_remove : forall k s, wf s -> wf (remove k s).
  Proof. Admitted. (* STUB *)
  Lemma wf_union : forall s u, wf s -> wf u -> wf (union s u).
  Proof. Admitted. (* STUB *)
  Lemma wf_inter : forall s u, wf s -> wf u -> wf (inter s u).
  Proof. Admitted. (* STUB *)
  Lemma wf_diff : forall s u, wf s -> wf u -> wf (diff s u).
  Proof. Admitted. (* STUB *)
  Lemma mem_empty : forall k, mem k empty = false.
  Proof. Admitted. (* STUB *)
  Lemma mem_add_same : forall k s, mem k (add k s) = true.
  Proof. Admitted. (* STUB *)
  Lemma mem_add_other : forall k q s, k <> q -> mem k (add q s) = mem k s.
  Proof. Admitted. (* STUB *)
  Lemma mem_remove_same : forall k s, mem k (remove k s) = false.
  Proof. Admitted. (* STUB *)
  Lemma mem_remove_other : forall k q s, k <> q -> mem k (remove q s) = mem k s.
  Proof. Admitted. (* STUB *)
  Lemma mem_union : forall k s u, mem k (union s u) = (mem k s || mem k u).
  Proof. Admitted. (* STUB *)
  Lemma mem_inter : forall k s u, mem k (inter s u) = (mem k s && mem k u).
  Proof. Admitted. (* STUB *)
  Lemma mem_diff : forall k s u, mem k (diff s u) = (mem k s && negb (mem k u)).
  Proof. Admitted. (* STUB *)
  Lemma elements_spec : forall s k, wf s -> (In k (elements s) <-> mem k s = true).
  Proof. Admitted. (* STUB *)
  Lemma elements_nodup : forall s, wf s -> NoDup (elements s).
  Proof. Admitted. (* STUB *)
  Lemma fold_spec : forall A (f : A -> K.t -> A) s a,
    fold f s a = fold_left f (elements s) a.
  Proof.
    intros A f s a. unfold fold.
    rewrite PTrieT.F9_fold_values, elements_trie.
    generalize (PTrieCode.elements s). intro entries.
    revert a. induction entries as [|entry rest IH]; intro a;
      cbn [List.map fold_left]; [reflexivity|apply IH].
  Qed.
  Lemma ext : forall s u, wf s -> wf u -> (forall k, mem k s = mem k u) -> s = u.
  Proof. Admitted. (* STUB *)
  Lemma mem_has : forall k s, mem k s = has (K.encode k) s.
  Proof. Admitted. (* STUB *)
  Lemma has_empty : forall p, has p empty = false.
  Proof. Admitted. (* STUB *)
  Lemma has_add : forall p k s, has p (add k s) = Pos.eqb p (K.encode k) || has p s.
  Proof. Admitted. (* STUB *)
  Lemma has_remove : forall p k s,
  has p (remove k s) = negb (Pos.eqb p (K.encode k)) && has p s.
  Proof. Admitted. (* STUB *)
  Lemma has_union : forall p s u, has p (union s u) = has p s || has p u.
  Proof. Admitted. (* STUB *)
  Lemma has_inter : forall p s u, has p (inter s u) = has p s && has p u.
  Proof. Admitted. (* STUB *)
  Lemma has_diff : forall p s u, has p (diff s u) = has p s && negb (has p u).
  Proof. Admitted. (* STUB *)
  Lemma subset_spec : forall s u,
  subset s u = true <-> forall p, has p s = true -> has p u = true.
  Proof. Admitted. (* STUB *)
  Lemma equal_spec : forall s u, equal s u = true <-> forall p, has p s = has p u.
  Proof. Admitted. (* STUB *)
  Lemma wf_has : forall s p, wf s -> has p s = true -> exists k, K.encode k = p.
  Proof. Admitted. (* STUB *)
  Lemma nodes_empty : nodes empty = 0.
  Proof. Admitted. (* STUB *)
  Lemma nodes_add : forall k s, nodes (add k s) <= nodes s + K.bits k.
  Proof. Admitted. (* STUB *)
  Lemma nodes_remove : forall k s, nodes (remove k s) <= nodes s.
  Proof. Admitted. (* STUB *)
  Lemma nodes_union : forall s u, nodes (union s u) <= nodes s + nodes u.
  Proof. Admitted. (* STUB *)
  Lemma nodes_inter : forall s u, nodes (inter s u) <= nodes s.
  Proof. Admitted. (* STUB *)
  Lemma nodes_diff : forall s u, nodes (diff s u) <= nodes s.
  Proof. Admitted. (* STUB *)

  (** Consistent labels give the same binding weight as the stored trie codes. *)
  Lemma weight_trie : forall s, wf s -> weight s = PTrie.weight s.
  Proof.
    intros s Hwf. unfold weight, PTrie.weight.
    rewrite elements_trie, List.map_map.
    f_equal. apply map_ext_in. intros [p k] Hin. cbn [fst snd].
    apply PTrie.elements_spec in Hin.
    rewrite (Hwf p k Hin). reflexivity.
  Qed.

  Lemma nodes_le_weight : forall s, wf s -> nodes s <= weight s.
  Proof.
    intros s Hwf. rewrite weight_trie by exact Hwf.
    apply PTrie.nodes_le_weight.
  Qed.
End TrieSet.

Module TrieSetT (K : KEY_T) <: SET_T K.
  Include TrieSet K.
  TimeFun has.
  TimeFun mem.
  TimeFun add.
  TimeFun remove.
  TimeFun union.
  TimeFun inter.
  TimeFun diff.
  TimeFun subset.
  TimeFun equal.
  TimeFun fold.
  TimeFun elements.
  Definition c_set : N :=
    16 * (K.c_key + PTrieT.c_trie + PTrieT.k_check + PTrieT.k_fold + 1).
  Lemma T_mem_le : forall k s, (T_mem k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k s.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_get_le K.t (K.encode k) s) as Hget.
    unfold c_set, K.bits in *. time_step.
  Qed.
  Lemma T_add_le : forall k s, (T_add k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k s.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_set_le K.t (K.encode k) k s) as Hset.
    unfold c_set, K.bits in *. time_step.
  Qed.
  Lemma T_remove_le : forall k s, (T_remove k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k s.
    pose proof (K.T_encode_le k) as Hencode.
    pose proof (PTrieT.T_remove_le K.t (K.encode k) s) as Hremove.
    unfold c_set, K.bits in *. time_step.
  Qed.
  Lemma T_union_le : forall s u, (T_union s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. unfold T_union.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_le with (k := 1%N).
      intros a b. destruct a; time_cbn; nia.
    - unfold c_set, nodes. nia.
  Qed.
  Lemma T_inter_le : forall s u, (T_inter s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. unfold T_inter.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_le with (k := 1%N).
      intros a b. destruct b; time_cbn; nia.
    - unfold c_set, nodes. nia.
  Qed.
  Lemma T_diff_le : forall s u, (T_diff s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. unfold T_diff.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_le with (k := 1%N).
      intros a b. destruct b; time_cbn; nia.
    - unfold c_set, nodes. nia.
  Qed.

  (** Inclusion needs only the left skeleton and a constant presence callback. *)
  Lemma T_subset_nodes : forall s u,
    (T_subset s u <= (2 * PTrieT.k_check + 1) * N.of_nat (nodes s + 1))%N.
  Proof.
    intros s u. unfold T_subset.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T5_forall2 with (c := 1%N).
      intros a b. destruct b; time_cbn; nia.
    - unfold nodes. nia.
  Qed.

  Lemma T_subset_le : forall s u, (T_subset s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. pose proof (T_subset_nodes s u) as Hsubset.
    unfold c_set. nia.
  Qed.
  Lemma T_equal_le : forall s u, (T_equal s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u.
    pose proof (T_subset_nodes s u) as Hleft.
    pose proof (T_subset_nodes u s) as Hright.
    unfold c_set. time_step.
  Qed.
  Lemma T_elements_le : forall s, (wf s -> T_elements s <= c_set * N.of_nat (weight s + 1))%N.
  Proof.
    intros s Hwf.
    pose proof (PTrieT.T9_fold_values K.t (list K.t)
      (fun acc k => k :: acc) (fun _ _ => 1%N) s nil 1%N
      (fun _ _ => N.le_refl 1)) as Hfold.
    pose proof (List.T_rev_append_le (fold (fun acc k => k :: acc) s nil) nil) as Hreverse.
    pose proof (elements_length s) as Hlength.
    unfold elements in Hlength.
    rewrite rev_append_rev, length_app, length_rev in Hlength.
    pose proof (nodes_le_weight s Hwf) as Hnodes.
    unfold T_elements, T_fold, c_set, nodes in *.
    time_simpl. time_cbn_all. nia.
  Qed.
  Lemma T_fold_le : forall A (f : A -> K.t -> A) T_f s a c,
    ((forall acc k, T_f acc k <= c) ->
    T_fold f T_f s a <= c_set * (c + 1) * N.of_nat (nodes s + 1))%N.
  Proof.
    intros A f T_f s a c Hf. unfold T_fold.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T9_fold_values with (c := c). exact Hf.
    - unfold c_set, nodes. nia.
  Qed.
End TrieSetT.
