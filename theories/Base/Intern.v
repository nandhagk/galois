(** * Interning and indexes

    Interners assign dense identifiers and indexes group values by key.
    For example, interning [a; b; a] allocates only two identifiers.
    Builds on: InternSig, MapSig and KeySig. *)

From Stdlib Require Import List Bool NArith PArith Lia Sorting.Sorted.
From Argent Require Import Time Std Tactics BigO.
From Galois.Base Require Import InternSig KeySig MapSig.
From Galois.Base Require Import Trie.

Record intern_table (K : Type) (M : Type -> Type) := InternTable {
  intern_forward : M positive;
  intern_inverse : PTrieCode.t K;
  intern_next : positive
}.
Arguments InternTable {K M} _ _ _.
Arguments intern_forward {K M} _.
Arguments intern_inverse {K M} _.
Arguments intern_next {K M} _.

TimeFun intern_forward.
TimeFun intern_inverse.
TimeFun intern_next.

Module InternCode (K : KEY_OPS) (M : MAP_OPS K) <: INTERN_OPS K.
  Definition t := intern_table K.t M.t.
  Definition empty : t := InternTable M.empty PTrieCode.empty 1%positive.
  Definition find (k : K.t) (s : t) := M.get k (intern_forward s).
  Definition name (i : positive) (s : t) := PTrieCode.get i (intern_inverse s).
  Definition size (s : t) := Pos.pred_N (intern_next s).
  Definition intern (k : K.t) (s : t) : positive * t :=
    match find k s with
    | Some i => (i, s)
    | None =>
      let i := intern_next s in
      (i, InternTable (M.set k i (intern_forward s))
            (PTrieCode.set i k (intern_inverse s)) (Pos.succ i))
    end.
End InternCode.

Module Intern (K : KEY) (M : MAP K) <: INTERN K.
  Include InternCode K M.
  Definition wf (s : t) : Prop :=
    M.wf (intern_forward s) /\
    (forall k i, find k s = Some i -> (i < intern_next s)%positive) /\
    (forall k i, find k s = Some i <-> name i s = Some k) /\
    (forall i, (i < intern_next s)%positive -> exists k, find k s = Some i).
  Lemma find_empty : forall k, find k empty = None.
  Proof. intro k; apply M.get_empty. Qed.
  Lemma name_empty : forall i, name i empty = None.
  Proof. intro i; apply PTrie.get_empty. Qed.
  Lemma wf_empty : wf empty.
  Proof.
    split; [apply M.wf_empty|]. split.
    - intros k i H; rewrite find_empty in H; discriminate.
    - split.
      + intros k i; rewrite find_empty, name_empty; split; discriminate.
      + intros i Hi; change (i < 1)%positive in Hi; lia.
  Qed.
  Lemma wf_intern : forall k s, wf s -> wf (snd (intern k s)).
  Proof.
    intros k s Hwf. unfold intern. destruct (find k s) as [i|] eqn:Hfind;
      cbn [snd]; [exact Hwf|].
    destruct Hwf as [Hmap [Hbound [Hlink Hdense]]].
    unfold wf. cbn [intern_forward intern_next intern_inverse].
    split; [apply M.wf_set; exact Hmap|]. split.
    - intros l j Hget. unfold find in Hget. cbn [intern_forward] in Hget.
      destruct (K.eqb_spec l k) as [Heq|Hneq].
      + subst l. rewrite M.get_set_same in Hget. injection Hget as Hj. subst j. lia.
      + rewrite M.get_set_other in Hget by exact Hneq.
        pose proof (Hbound l j Hget). lia.
    - split.
      + intros l j. unfold find, name. cbn [intern_forward intern_inverse].
        destruct (K.eqb_spec l k) as [Heq|Hneq].
        * subst l. rewrite M.get_set_same.
          destruct (Pos.eq_dec j (intern_next s)) as [Hj|Hj].
          -- subst j. rewrite PTrie.get_set_same. split; intros _; reflexivity.
          -- rewrite PTrie.get_set_other by exact Hj. split.
             ++ intro Heq. injection Heq as Heq. congruence.
             ++ intro Hname. apply (proj2 (Hlink k j)) in Hname.
                rewrite Hfind in Hname. discriminate.
        * rewrite M.get_set_other by exact Hneq.
          destruct (Pos.eq_dec j (intern_next s)) as [Hj|Hj].
          -- subst j. rewrite PTrie.get_set_same. split.
             ++ intro Hget. pose proof (Hbound l (intern_next s) Hget). lia.
             ++ intro Heq. injection Heq as Heq. congruence.
          -- rewrite PTrie.get_set_other by exact Hj. apply Hlink.
      + intros j Hj. destruct (Pos.eq_dec j (intern_next s)) as [Heq|Hneq].
        * subst j. exists k. unfold find. cbn [intern_forward]. apply M.get_set_same.
        * assert (Hlt : (j < intern_next s)%positive) by lia.
          destruct (Hdense j Hlt) as [l Hl]. exists l.
          unfold find. cbn [intern_forward]. rewrite M.get_set_other; [exact Hl|].
          intro Heq. subst l. rewrite Hfind in Hl. discriminate.
  Qed.
  Lemma size_empty : size empty = 0%N.
  Proof.
    reflexivity.
  Qed.
  Lemma find_name : forall k i s, wf s -> (find k s = Some i <-> name i s = Some k).
  Proof. intros k i s [_ [_ [Hlink _]]]; apply Hlink. Qed.
  Lemma find_inj : forall k l i s, wf s ->
    find k s = Some i -> find l s = Some i -> k = l.
  Proof.
    intros k l i s Hwf Hk Hl.
    apply (proj1 (find_name k i s Hwf)) in Hk.
    apply (proj1 (find_name l i s Hwf)) in Hl; congruence.
  Qed.
  Lemma find_range : forall k i s, wf s -> find k s = Some i ->
    (N.pos i <= size s)%N.
  Proof.
    intros k i s [_ [Hbound _]] Hfind. specialize (Hbound k i Hfind).
    unfold size. pose proof (N.succ_pos_pred (intern_next s)). lia.
  Qed.
  Lemma dense : forall i s, wf s -> (N.pos i <= size s)%N -> exists k, name i s = Some k.
  Proof.
    intros i s [_ [_ [Hlink Hdense]]] Hsize.
    assert (Hlt : (i < intern_next s)%positive).
    { unfold size in Hsize. pose proof (N.succ_pos_pred (intern_next s)). lia. }
    destruct (Hdense i Hlt) as [k Hfind]. exists k. apply (proj1 (Hlink k i)); exact Hfind.
  Qed.
  Lemma intern_found : forall k s i, find k s = Some i -> intern k s = (i, s).
  Proof. intros k s i H; unfold intern; rewrite H; reflexivity. Qed.
  Lemma intern_new : forall k s, wf s -> find k s = None ->
    N.pos (fst (intern k s)) = N.succ (size s).
  Proof.
    intros k s Hwf Hfind. unfold intern. rewrite Hfind. cbn [fst].
    unfold size. symmetry. apply N.succ_pos_pred.
  Qed.
  Lemma find_intern_same : forall k s, wf s ->
    find k (snd (intern k s)) = Some (fst (intern k s)).
  Proof.
    intros k s Hwf; unfold intern; destruct (find k s) eqn:H; cbn; [exact H|].
    apply M.get_set_same.
  Qed.
  Lemma find_intern_other : forall k l s, wf s -> k <> l ->
    find l (snd (intern k s)) = find l s.
  Proof.
    intros k l s Hwf Hneq; unfold intern; destruct (find k s) eqn:H; cbn; [reflexivity|].
    unfold find; cbn; apply M.get_set_other; congruence.
  Qed.
  Lemma name_intern : forall k s, wf s ->
    name (fst (intern k s)) (snd (intern k s)) = Some k.
  Proof.
    intros k s Hwf; apply (proj1 (find_name k (fst (intern k s)) (snd (intern k s)) (wf_intern k s Hwf))).
    apply find_intern_same; exact Hwf.
  Qed.
  Lemma name_stable : forall k s i l, wf s -> name i s = Some l ->
    name i (snd (intern k s)) = Some l.
  Proof.
    intros k s i l Hwf Hname.
    pose proof (proj2 (find_name l i s Hwf) Hname) as Hfind.
    pose proof (proj1 (proj2 Hwf) l i Hfind) as Hbound.
    unfold intern. destruct (find k s); cbn [snd]; [exact Hname|].
    unfold name. cbn [intern_inverse]. rewrite PTrie.get_set_other by lia. exact Hname.
  Qed.
  Lemma size_intern : forall k s, wf s ->
    size (snd (intern k s)) =
      match find k s with Some _ => size s | None => N.succ (size s) end.
  Proof.
    intros k s Hwf. unfold intern. destruct (find k s); cbn [snd]; [reflexivity|].
    unfold size. cbn [intern_next]. rewrite Pos.pred_N_succ, N.succ_pos_pred. reflexivity.
  Qed.
End Intern.

Module InternT (K : KEY_T) (M : MAP_T K) <: INTERN_T K.
  Include Intern K M.

  TimeFun find.
  TimeFun name.
  TimeFun size.
  TimeFun intern.

  Definition c_intern : N := (8 * (M.c_map + PTrieT.c_trie + 1))%N.

  (** The allocation frontier has at most one more bit than its predecessor. *)
  Local Lemma frontier_width (p : positive) :
    Pos.size_nat p <= N.size_nat (Pos.pred_N p) + 1.
  Proof.
    destruct (Pos.succ_pred_or p) as [Hone|Hsucc].
    - subst p. cbn [Pos.size_nat Pos.pred_N N.size_nat]. lia.
    - rewrite <- Hsucc, Pos.pred_N_succ. cbn [N.size_nat].
      apply Z.size_nat_succ.
  Qed.

  Local Lemma find_clock (k : K.t) (s : t) :
    (T_find k s <= M.c_map * N.of_nat (K.bits k + 1) + 2)%N.
  Proof.
    pose proof (M.T_get_le positive k (intern_forward s)) as Hget.
    time_unfold T_find. time_unfold @T_intern_forward. lia.
  Qed.

  Lemma T_intern_le : forall k s, (wf s ->
    T_intern k s <= c_intern * N.of_nat (K.bits k + N.size_nat (size s) + 1))%N.
  Proof.
    intros k s Hwf.
    pose proof (find_clock k s) as Hfind.
    pose proof (M.T_set_le positive k (intern_next s) (intern_forward s)) as Hforward.
    pose proof (PTrieT.T_set_le K.t (intern_next s) k (intern_inverse s)) as Hinverse.
    change (PTrieCode.T_set (intern_next s) k (intern_inverse s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat (intern_next s) + 1))%N in Hinverse.
    pose proof (Pos.T_succ_le (intern_next s)) as Hsucc.
    pose proof (frontier_width (intern_next s)) as Hwidth.
    change (Pos.size_nat (intern_next s) <= N.size_nat (size s) + 1) in Hwidth.
    apply time_of_nat_le in Hwidth.
    time_unfold T_intern. time_unfold @T_intern_next.
    time_unfold @T_intern_forward. time_unfold @T_intern_inverse.
    destruct (find k s); unfold c_intern, PTrieT.c_trie in *;
      repeat rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
  Qed.
  Lemma T_find_le : forall k s,
    (T_find k s <= c_intern * N.of_nat (K.bits k + N.size_nat (size s) + 1))%N.
  Proof.
    intros k s. pose proof (find_clock k s) as Hfind.
    unfold c_intern, PTrieT.c_trie.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.
  Lemma T_name_le : forall i s,
    (T_name i s <= c_intern * N.of_nat (Pos.size_nat i + N.size_nat (size s) + 1))%N.
  Proof.
    intros i s. pose proof (PTrieT.T_get_le K.t i (intern_inverse s)) as Hget.
    change (PTrieCode.T_get i (intern_inverse s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hget.
    time_unfold T_name. time_unfold @T_intern_inverse.
    unfold c_intern, PTrieT.c_trie in *.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.
  (** Reading size charges the allocation frontier width. *)
  Lemma T_size_le : forall s,
    (T_size s <= c_intern * N.of_nat (N.size_nat (size s) + 1))%N.
  Proof.
    intro s. pose proof (Pos.T_pred_N_le (intern_next s)) as Hpred.
    pose proof (frontier_width (intern_next s)) as Hwidth.
    change (Pos.size_nat (intern_next s) <= N.size_nat (size s) + 1) in Hwidth.
    apply time_of_nat_le in Hwidth.
    time_unfold T_size. time_unfold @T_intern_next.
    unfold c_intern, PTrieT.c_trie.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Interning is linear in the key width and allocation frontier width. *)
  Lemma intern_bigO : bigO (X := K.t * t) (fun xs => wf (snd xs))
    (fun xs => N.of_nat (K.bits (fst xs) + N.size_nat (size (snd xs))))
    (fun xs => T_intern (fst xs) (snd xs)).
  Proof.
    exists c_intern. intros [k s] Hwf. cbn [fst snd] in Hwf |- *.
    pose proof (T_intern_le k s Hwf) as Hintern.
    rewrite Nat2N.inj_add in Hintern. exact Hintern.
  Qed.

  (** Forward lookup fits the key and allocation frontier width budget. *)
  Lemma find_bigO : bigO (X := K.t * t) (fun _ => True)
    (fun xs => N.of_nat (K.bits (fst xs) + N.size_nat (size (snd xs))))
    (fun xs => T_find (fst xs) (snd xs)).
  Proof.
    exists c_intern. intros [k s] _. cbn [fst snd].
    pose proof (T_find_le k s) as Hfind.
    rewrite Nat2N.inj_add in Hfind. exact Hfind.
  Qed.

  (** Inverse lookup fits the identifier and allocation frontier width budget. *)
  Lemma name_bigO : bigO (X := positive * t) (fun _ => True)
    (fun xs => N.of_nat (Pos.size_nat (fst xs) + N.size_nat (size (snd xs))))
    (fun xs => T_name (fst xs) (snd xs)).
  Proof.
    exists c_intern. intros [i s] _. cbn [fst snd].
    pose proof (T_name_le i s) as Hname.
    rewrite Nat2N.inj_add in Hname. exact Hname.
  Qed.
End InternT.

(** A bucket lookup returns the values associated with the encoded key. *)
Definition find_group {K V} (encode : K -> positive) (k : K)
    (groups : PTrieCode.t (list V)) : list V :=
  match PTrieCode.get (encode k) groups with
  | Some xs => xs
  | None => nil
  end.

TimeFun find_group.

(** Collection prepends each value to its encoded key's bucket. *)
Fixpoint collect_groups {K V} (encode : K -> positive) (key : V -> K)
    (xs : list V) (groups : PTrieCode.t (list V)) : PTrieCode.t (list V) :=
  match xs with
  | nil => groups
  | x :: rest =>
    let p := encode (key x) in
    let bucket := match PTrieCode.get p groups with
                  | Some ys => ys
                  | None => nil
                  end in
    collect_groups encode key rest (PTrieCode.set p (x :: bucket) groups)
  end.

TimeFun collect_groups.

(** Grouping reverses each collected bucket to preserve input order. *)
Definition group_by {K V} (encode : K -> positive) (key : V -> K) (xs : list V) :=
  PTrieT.map (fun bucket => rev_append bucket nil) (collect_groups encode key xs PTrieCode.empty).

TimeFun group_by.

(** ** Group lookup proofs *)

(** Collection adds the matching values in reverse order before the previous bucket. *)
Local Lemma find_collect_groups {K V} (encode : K -> positive) (key : V -> K) k xs groups :
  find_group encode k (collect_groups encode key xs groups) =
    app (rev (filter (fun a => Pos.eqb (encode (key a)) (encode k)) xs))
      (find_group encode k groups).
Proof.
  revert groups. induction xs as [|x rest IH]; intro groups; [reflexivity|].
  cbn [collect_groups]. rewrite IH. cbn [filter].
  destruct (Pos.eqb (encode (key x)) (encode k)) eqn:Hkey.
  - apply Pos.eqb_eq in Hkey. unfold find_group at 1.
    rewrite Hkey, PTrie.get_set_same. cbn [rev].
    rewrite <- app_assoc. reflexivity.
  - apply Pos.eqb_neq in Hkey. unfold find_group at 1.
    rewrite PTrie.get_set_other by congruence. reflexivity.
Qed.

(** Group lookup returns the input values whose keys have the same encoding. *)
Lemma find_group_by {K V} (encode : K -> positive) (key : V -> K) k xs :
  find_group encode k (group_by encode key xs) =
  filter (fun a => Pos.eqb (encode (key a)) (encode k)) xs.
Proof.
  pose proof (find_collect_groups encode key k xs PTrieCode.empty) as Hcollect.
  unfold find_group in Hcollect. rewrite PTrie.get_empty, app_nil_r in Hcollect.
  unfold group_by, find_group. rewrite PTrie.get_map.
  destruct (PTrieCode.get (encode k)
    (collect_groups encode key xs PTrieCode.empty)) as [bucket|] eqn:Hget;
    cbn [option_map] in *.
  - rewrite rev_append_rev, app_nil_r, Hcollect, rev_involutive. reflexivity.
  - apply (f_equal (@rev V)) in Hcollect.
    rewrite rev_involutive in Hcollect. exact Hcollect.
Qed.

(** ** End group lookup proofs *)
