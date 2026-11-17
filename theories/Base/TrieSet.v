(** * Trie sets

    Unit-valued maps represent finite sets.
    For example, adding one key twice leaves a singleton.
    Main results
    - [elements_spec] Consistent sets enumerate precisely their members.
    - [fold_spec] Folding follows enumeration order.
    - [subset_spec] Inclusion accepts exactly when every member of the left set is a member of
      the right set.
    - [equal_spec] Equality accepts exactly when two sets have the same members.
    - [mem_complexity] Membership is linear in the encoded key length.
    - [add_complexity] Adding a member is linear in the encoded key length.
    - [union_complexity] Union, intersection and difference visit the shared skeleton only.
    - [inter_complexity] Intersection visits the shared skeleton only, so its time is linear in
      the smaller tree.
    - [diff_complexity] Difference visits the shared skeleton only, so its time is linear in
      the smaller tree.
    - [subset_complexity] Inclusion visits the left skeleton only and stops at the first failure.

    Builds on: SetSig and MapSig. *)

From Stdlib Require Import List Bool NArith PeanoNat Lia Sorting.Sorted.
From Argent Require Import Time Tactics Std Complexity.
Import ComplexityNotations.
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
    PTrieCode.merge_with (fun a b => match a with Some _ => a | None => b end)
      (fun tr => tr) (fun tr => tr) s u.
  Definition inter (s u : t) :=
    PTrieCode.merge_with (fun a b => match b with Some _ => a | None => None end)
      (fun _ => PTrieCode.empty) (fun _ => PTrieCode.empty) s u.
  Definition diff (s u : t) :=
    PTrieCode.merge_with (fun a b => match b with Some _ => None | None => a end)
      (fun tr => tr) (fun _ => PTrieCode.empty) s u.
  Definition subset (s u : t) :=
    PTrieCode.forall2 (fun _ b => match b with Some _ => true | None => false end) s u.
  Definition equal (s u : t) :=
    PTrieCode.forall2b
      (fun a b => match a, b with
       | Some _, Some _ | None, None => true
       | _, _ => false
       end) s u.
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
    rewrite PTrieT.fold_values_def, rev_append_rev, app_nil_r.
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
    apply PTrieT.bindings_le_nodes.
  Qed.

  Lemma wf_empty : wf empty.
  Proof.
    intros p k Hget. unfold empty in Hget.
    rewrite PTrie.get_empty in Hget. discriminate.
  Qed.
  Lemma wf_add : forall k s, wf s -> wf (add k s).
  Proof.
    intros k s Hwf p q Hget. unfold add in Hget.
    destruct (Pos.eq_dec p (K.encode k)) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget. inversion Hget. reflexivity.
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      exact (Hwf p q Hget).
  Qed.
  Lemma wf_remove : forall k s, wf s -> wf (remove k s).
  Proof.
    intros k s Hwf p q Hget. unfold remove in Hget.
    destruct (Pos.eq_dec p (K.encode k)) as [->|Hneq].
    - rewrite PTrie.get_remove_same in Hget. discriminate.
    - rewrite PTrie.get_remove_other in Hget by exact Hneq.
      exact (Hwf p q Hget).
  Qed.
  Lemma wf_union : forall s u, wf s -> wf u -> wf (union s u).
  Proof.
    intros s u Hleft Hright p k Hget. unfold union in Hget.
    rewrite PTrie.get_merge_with in Hget by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p s) as [a|] eqn:Hfirst.
    - inversion Hget; subst. eapply Hleft. exact Hfirst.
    - exact (Hright p k Hget).
  Qed.
  Lemma wf_inter : forall s u, wf s -> wf u -> wf (inter s u).
  Proof.
    intros s u Hleft Hright p k Hget. unfold inter in Hget.
    rewrite PTrie.get_merge_with in Hget by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p u); [exact (Hleft p k Hget)|discriminate].
  Qed.
  Lemma wf_diff : forall s u, wf s -> wf u -> wf (diff s u).
  Proof.
    intros s u Hleft Hright p k Hget. unfold diff in Hget.
    rewrite PTrie.get_merge_with in Hget by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p u); [discriminate|exact (Hleft p k Hget)].
  Qed.
  Lemma mem_empty : forall k, mem k empty = false.
  Proof.
    intro k. unfold mem, empty. rewrite PTrie.get_empty. reflexivity.
  Qed.
  Lemma mem_add_same : forall k s, mem k (add k s) = true.
  Proof.
    intros k s. unfold mem, add. rewrite PTrie.get_set_same. reflexivity.
  Qed.
  Lemma mem_add_other : forall k q s, k <> q -> mem k (add q s) = mem k s.
  Proof.
    intros k q s Hneq. unfold mem, add.
    rewrite PTrie.get_set_other; [reflexivity|].
    intro Hcode. apply Hneq, K.encode_inj. exact Hcode.
  Qed.
  Lemma mem_remove_same : forall k s, mem k (remove k s) = false.
  Proof.
    intros k s. unfold mem, remove. rewrite PTrie.get_remove_same. reflexivity.
  Qed.
  Lemma mem_remove_other : forall k q s, k <> q -> mem k (remove q s) = mem k s.
  Proof.
    intros k q s Hneq. unfold mem, remove.
    rewrite PTrie.get_remove_other; [reflexivity|].
    intro Hcode. apply Hneq, K.encode_inj. exact Hcode.
  Qed.
  Lemma mem_union : forall k s u, mem k (union s u) = (mem k s || mem k u).
  Proof.
    intros k s u. unfold mem, union. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get (K.encode k) s), (PTrieCode.get (K.encode k) u); reflexivity.
  Qed.
  Lemma mem_inter : forall k s u, mem k (inter s u) = (mem k s && mem k u).
  Proof.
    intros k s u. unfold mem, inter. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get (K.encode k) s), (PTrieCode.get (K.encode k) u); reflexivity.
  Qed.
  Lemma mem_diff : forall k s u, mem k (diff s u) = (mem k s && negb (mem k u)).
  Proof.
    intros k s u. unfold mem, diff. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get (K.encode k) s), (PTrieCode.get (K.encode k) u); reflexivity.
  Qed.
  Lemma elements_spec : forall s k, wf s -> (In k (elements s) <-> mem k s = true).
  Proof.
    intros s k Hwf. rewrite elements_trie. split.
    - intro Hin. apply in_map_iff in Hin as [[p q] [Heq Hin]].
      cbn [snd] in Heq. subst q.
      apply PTrie.elements_spec in Hin. unfold mem.
      rewrite (Hwf p k Hin), Hin. reflexivity.
    - intro Hmem. unfold mem in Hmem.
      destruct (PTrieCode.get (K.encode k) s) as [q|] eqn:Hget; try discriminate.
      assert (Hkey : q = k) by (apply K.encode_inj; exact (Hwf _ _ Hget)).
      subst q. apply in_map_iff. exists (K.encode k, k).
      split; [reflexivity|apply PTrie.elements_spec; exact Hget].
  Qed.
  Lemma elements_nodup : forall s, wf s -> NoDup (elements s).
  Proof.
    intros s Hwf.
    assert (Hcodes : List.map K.encode (elements s) = List.map fst (PTrieCode.elements s)).
    { rewrite elements_trie, List.map_map.
      apply map_ext_in. intros [p k] Hin. cbn [fst snd].
      apply PTrie.elements_spec in Hin. exact (Hwf _ _ Hin). }
    apply (NoDup_map_inv K.encode). rewrite Hcodes.
    apply PTrie.elements_nodup.
  Qed.
  Lemma fold_spec : forall A (f : A -> K.t -> A) s a,
    fold f s a = fold_left f (elements s) a.
  Proof.
    intros A f s a. unfold fold.
    rewrite PTrieT.fold_values_def, elements_trie.
    generalize (PTrieCode.elements s). intro entries.
    revert a. induction entries as [|entry rest IH]; intro a;
      cbn [List.map fold_left]; [reflexivity|apply IH].
  Qed.
  Lemma ext : forall s u, wf s -> wf u -> (forall k, mem k s = mem k u) -> s = u.
  Proof.
    intros s u Hleft Hright Hmem. apply PTrie.ext. intro p.
    destruct (PTrieCode.get p s) as [k|] eqn:Hfirst;
      destruct (PTrieCode.get p u) as [q|] eqn:Hsecond; try reflexivity.
    - f_equal. apply K.encode_inj.
      rewrite (Hleft p k Hfirst), (Hright p q Hsecond). reflexivity.
    - specialize (Hmem k). unfold mem in Hmem.
      rewrite (Hleft p k Hfirst), Hfirst, Hsecond in Hmem. discriminate.
    - specialize (Hmem q). unfold mem in Hmem.
      rewrite (Hright p q Hsecond), Hfirst, Hsecond in Hmem. discriminate.
  Qed.
  Lemma mem_has : forall k s, mem k s = has (K.encode k) s.
  Proof.
    reflexivity.
  Qed.
  Lemma has_empty : forall p, has p empty = false.
  Proof.
    intro p. unfold has, empty. rewrite PTrie.get_empty. reflexivity.
  Qed.
  Lemma has_add : forall p k s, has p (add k s) = Pos.eqb p (K.encode k) || has p s.
  Proof.
    intros p k s. unfold has, add.
    destruct (Pos.eqb_spec p (K.encode k)) as [->|Hneq].
    - rewrite PTrie.get_set_same. reflexivity.
    - rewrite PTrie.get_set_other by exact Hneq. reflexivity.
  Qed.
  Lemma has_remove : forall p k s,
  has p (remove k s) = negb (Pos.eqb p (K.encode k)) && has p s.
  Proof.
    intros p k s. unfold has, remove.
    destruct (Pos.eqb_spec p (K.encode k)) as [->|Hneq].
    - rewrite PTrie.get_remove_same. reflexivity.
    - rewrite PTrie.get_remove_other by exact Hneq. reflexivity.
  Qed.
  Lemma has_union : forall p s u, has p (union s u) = has p s || has p u.
  Proof.
    intros p s u. unfold has, union. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p s), (PTrieCode.get p u); reflexivity.
  Qed.
  Lemma has_inter : forall p s u, has p (inter s u) = has p s && has p u.
  Proof.
    intros p s u. unfold has, inter. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p s), (PTrieCode.get p u); reflexivity.
  Qed.
  Lemma has_diff : forall p s u, has p (diff s u) = has p s && negb (has p u).
  Proof.
    intros p s u. unfold has, diff. rewrite PTrie.get_merge_with by
      (intros q tr; rewrite ?PTrie.get_empty; destruct (PTrieCode.get q tr); reflexivity).
    destruct (PTrieCode.get p s), (PTrieCode.get p u); reflexivity.
  Qed.
  Lemma subset_spec : forall s u,
  subset s u = true <-> forall p, has p s = true -> has p u = true.
  Proof.
    intros s u. unfold subset, has. rewrite PTrie.forall2_spec. split.
    - intros Htest p Hhas.
      destruct (PTrieCode.get p s) as [k|] eqn:Hget; try discriminate.
      exact (Htest p k Hget).
    - intros Htest p k Hget. apply (Htest p). rewrite Hget. reflexivity.
  Qed.
  Lemma equal_spec : forall s u, equal s u = true <-> forall p, has p s = has p u.
  Proof.
    intros s u. unfold equal. rewrite PTrie.forall2b_spec by reflexivity.
    split; intros Heq p; specialize (Heq p); unfold has in *;
      destruct (PTrieCode.get p s), (PTrieCode.get p u); congruence.
  Qed.
  Lemma wf_has : forall s p, wf s -> has p s = true -> exists k, K.encode k = p.
  Proof.
    intros s p Hwf Hhas. unfold has in Hhas.
    destruct (PTrieCode.get p s) as [k|] eqn:Hget; try discriminate.
    exists k. exact (Hwf _ _ Hget).
  Qed.
  Lemma nodes_empty : nodes empty = 0.
  Proof.
    reflexivity.
  Qed.
  Lemma nodes_add : forall k s, nodes (add k s) <= nodes s + K.bits k.
  Proof.
    intros k s. apply PTrie.nodes_set.
  Qed.
  Lemma nodes_remove : forall k s, nodes (remove k s) <= nodes s.
  Proof.
    intros k s. apply PTrie.nodes_remove.
  Qed.
  Lemma nodes_union : forall s u, nodes (union s u) <= nodes s + nodes u.
  Proof.
    intros s u. apply PTrie.nodes_merge_with; intro tr; apply Nat.le_refl.
  Qed.

  (** Dropping every right-only binding keeps the result inside the left skeleton. *)
  Lemma nodes_merge_left {A B C} (f : option A -> option B -> option C) fl m u :
    (forall tr, PTrie.nodes (fl tr) <= PTrie.nodes tr) ->
    PTrie.nodes (PTrieCode.merge_with f fl (fun _ => PTrieCode.empty) m u) <= PTrie.nodes m.
  Proof.
    intro Hleft_only. destruct m as [|n].
    - cbn [PTrieCode.merge_with]. reflexivity.
    - revert u. induction n; intros [|other].
      all: try (cbn [PTrieCode.merge_with PTrieCode.merge_ne]; apply Hleft_only).
      all: cbn [PTrieCode.merge_with PTrieCode.merge_ne].
      all: eapply Nat.le_trans; [apply PTrie.nodes_node_le_aux|].
      all: cbn [PTrieCode.merge_with] in *.
      all: try pose proof (IHn (PTrieCode.left (Nodes other))) as Hleft.
      all: try pose proof (IHn (PTrieCode.right (Nodes other))) as Hright_child.
      all: try pose proof (IHn1 (PTrieCode.left (Nodes other))) as Hleft.
      all: try pose proof (IHn2 (PTrieCode.right (Nodes other))) as Hright_child.
      all: cbn [PTrieCode.empty PTrie.nodes PTrie.nodes_ne] in *; lia.
  Qed.

  Lemma nodes_inter : forall s u, nodes (inter s u) <= nodes s.
  Proof.
    intros s u. apply nodes_merge_left. intro tr. apply Nat.le_0_l.
  Qed.
  Lemma nodes_diff : forall s u, nodes (diff s u) <= nodes s.
  Proof.
    intros s u. apply nodes_merge_left. intro tr. apply Nat.le_refl.
  Qed.

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
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_le with (c := 1%N)
        (cl := 1%N) (cr := 1%N).
      + intros a b. destruct a; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold c_set, nodes, PTrieT.k_merge, PTrieT.c_trie. nia.
  Qed.
  Lemma T_inter_le : forall s u, (T_inter s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. unfold T_inter.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_le with (c := 1%N)
        (cl := 1%N) (cr := 1%N).
      + intros a b. destruct b; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold c_set, nodes, PTrieT.k_merge, PTrieT.c_trie. nia.
  Qed.
  Lemma T_diff_le : forall s u, (T_diff s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof.
    intros s u. unfold T_diff.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_le with (c := 1%N)
        (cl := 1%N) (cr := 1%N).
      + intros a b. destruct b; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold c_set, nodes, PTrieT.k_merge, PTrieT.c_trie. nia.
  Qed.

  (** Inclusion needs only the left skeleton and a constant presence callback. *)
  Lemma T_subset_nodes : forall s u,
    (T_subset s u <= (2 * PTrieT.k_check + 1) * N.of_nat (nodes s + 1))%N.
  Proof.
    intros s u. unfold T_subset.
    eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_forall2_le with (c := 1%N).
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
    intros s u. unfold T_equal. eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_forall2b_le with (k := 2%N).
      intros a b. destruct a, b; time_cbn; nia.
    - unfold c_set, nodes. nia.
  Qed.
  Lemma T_elements_le : forall s, (wf s -> T_elements s <= c_set * N.of_nat (weight s + 1))%N.
  Proof.
    intros s Hwf.
    pose proof (PTrieT.T_fold_values_le K.t (list K.t)
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
    - apply N.add_le_mono_l. apply PTrieT.T_fold_values_le with (c := c). exact Hf.
    - unfold c_set, nodes. nia.
  Qed.

  (** Membership costs at most a constant per encoded key bit. *)
  Lemma mem_complexity :
    T_mem k s ∈ 𝑂(N.of_nat (K.bits k)) for (k, s).
  Proof.
    exists c_set. intros [k s] _. cbn [fst snd].
    pose proof (T_mem_le k s) as Hmem.
    rewrite Nat2N.inj_add in Hmem. exact Hmem.
  Qed.

  (** Adding a member costs at most a constant per encoded key bit. *)
  Lemma add_complexity :
    T_add k s ∈ 𝑂(N.of_nat (K.bits k)) for (k, s).
  Proof.
    exists c_set. intros [k s] _. cbn [fst snd].
    pose proof (T_add_le k s) as Hadd.
    rewrite Nat2N.inj_add in Hadd. exact Hadd.
  Qed.

  (** Union shares one-sided subtrees and visits at most the smaller skeleton. *)
  Lemma union_complexity :
    T_union s u ∈ 𝑂(N.of_nat (Nat.min (nodes s) (nodes u))) for (s, u).
  Proof.
    exists (4 * PTrieT.k_merge + 1)%N. intros [s u] _. cbn [fst snd].
    unfold T_union. eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_min with (c := 1%N).
      + intros a b. destruct a; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold nodes. rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.

  (** Intersection drops one-sided subtrees and visits at most the smaller skeleton. *)
  Lemma inter_complexity :
    T_inter s u ∈ 𝑂(N.of_nat (Nat.min (nodes s) (nodes u))) for (s, u).
  Proof.
    exists (4 * PTrieT.k_merge + 1)%N. intros [s u] _. cbn [fst snd].
    unfold T_inter. eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_min with (c := 1%N).
      + intros a b. destruct b; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold nodes. rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.

  (** Difference shares left-only subtrees and visits at most the smaller skeleton. *)
  Lemma diff_complexity :
    T_diff s u ∈ 𝑂(N.of_nat (Nat.min (nodes s) (nodes u))) for (s, u).
  Proof.
    exists (4 * PTrieT.k_merge + 1)%N. intros [s u] _. cbn [fst snd].
    unfold T_diff. eapply N.le_trans.
    - apply N.add_le_mono_l. apply PTrieT.T_merge_with_min with (c := 1%N).
      + intros a b. destruct b; time_cbn; nia.
      + intro tr. time_cbn. nia.
      + intro tr. time_cbn. nia.
    - unfold nodes. rewrite Nat2N.inj_add. time_cbn. nia.
  Qed.

  (** Inclusion visits the left skeleton only. *)
  Lemma subset_complexity :
    T_subset s u ∈ 𝑂(N.of_nat (nodes s)) for (s, u).
  Proof.
    exists (2 * PTrieT.k_check + 1)%N. intros [s u] _. cbn [fst snd].
    pose proof (T_subset_nodes s u) as Hsubset.
    rewrite Nat2N.inj_add in Hsubset. exact Hsubset.
  Qed.
End TrieSetT.
