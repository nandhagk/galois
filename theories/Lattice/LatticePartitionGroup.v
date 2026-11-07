(** * Indexed reconstruction of finite classes

    A single group-by index supplies a classmate for each support key during reconstruction.
    For example, keys labelled [a; b; a] connect the first and third keys.
    Builds on: CostMonad, BaseEncoding, BaseEq, BaseMap, BaseIndex and BaseUnionFind. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseIndex BaseUnionFind.
Import List.ListNotations Cost.Notations.

Section Group.
Context {K J : Type} (E : encoding K) (F : encoding J)
  (label_c : K -> Cost.t J).

Let label x := Cost.value (label_c x).

(** Reconstruction looks up one bucket head per key and never rescans the support. *)
Fixpoint partition_rebuild_c (keys : list K) (idx : Index.t J K) : Cost.t (UnionFind.t K) :=
  match keys with
  | [] => UnionFind.make_c
  | x :: rest =>
    Cost.step ;;
    let* u := partition_rebuild_c rest idx in
    Cost.step ;;
    let* j := label_c x in
    let* bucket := Index.find_c F j idx in
    match bucket with
    | [] => Cost.ret u
    | r :: _ => UnionFind.union_c E x r u
    end
  end.

(** Pure reconstruction observes the costed forest. *)
Definition partition_rebuild keys idx := Cost.value (partition_rebuild_c keys idx).

(** The reconstruction equation exposes bucket lookup without exposing Base implementations. *)
Theorem partition_rebuild_equation keys idx :
  partition_rebuild keys idx =
  match keys with
  | [] => UnionFind.make
  | x :: rest =>
    let u := partition_rebuild rest idx in
    match Index.find F (label x) idx with
    | [] => u
    | r :: _ => UnionFind.union E x r u
    end
  end.
Proof.
  destruct keys as [|x rest]; [reflexivity|].
  unfold partition_rebuild at 1; cbn [partition_rebuild_c].
  autorewrite with galois_cost.
  change (Cost.value
    (match Index.find F (label x) idx with
     | [] => Cost.ret (partition_rebuild rest idx)
     | r :: _ => UnionFind.union_c E x r (partition_rebuild rest idx)
     end) =
    match Index.find F (label x) idx with
    | [] => partition_rebuild rest idx
    | r :: _ => UnionFind.union E x r (partition_rebuild rest idx)
    end).
  destruct (Index.find F (label x) idx); reflexivity.
Qed.

(** Grouping prepares one index before reconstructing all its classes. *)
Definition partition_group_c keys :=
  let* idx := Index.group_by_c F label_c keys in
  partition_rebuild_c keys idx.

(** The grouped forest is the value of its indexed reconstruction. *)
Definition partition_group keys := Cost.value (partition_group_c keys).

(** Grouping uses the public group-by value contract. *)
Theorem partition_group_equation keys :
  partition_group keys = partition_rebuild keys (Index.group_by F label keys).
Proof.
  unfold partition_group, partition_group_c.
  rewrite Cost.value_bind, Index.group_by_c_value; reflexivity.
Qed.

Context (HE : encoding_laws E) (HF : encoding_laws F).

(** Every reconstruction preserves forest and stored Map validity. *)
Theorem partition_rebuild_wf keys idx : UnionFind.wf E (partition_rebuild keys idx).
Proof.
  induction keys as [|x rest IH]; rewrite partition_rebuild_equation.
  - apply UnionFind.wf_make.
  - destruct (Index.find F (label x) idx) as [|r bucket]; [exact IH|].
    apply (UnionFind.wf_union E HE); exact IH.
Qed.

(** Every grouped forest is representation-valid. *)
Theorem partition_group_wf keys : UnionFind.wf E (partition_group keys).
Proof.
  rewrite partition_group_equation; apply partition_rebuild_wf.
Qed.

Local Lemma bucket_member keys x r :
  In r (Index.find F (label x) (Index.group_by F label keys)) ->
  In r keys /\ label r = label x.
Proof.
  rewrite Index.find_group_by, filter_In, (eqb_true_iff F HF); tauto.
Qed.

Local Lemma bucket_head keys x : In x keys ->
  exists r rest, Index.find F (label x) (Index.group_by F label keys) = r :: rest /\
    In r keys /\ label r = label x.
Proof.
  intro Hx.
  assert (Hin : In x (Index.find F (label x) (Index.group_by F label keys))).
  { rewrite Index.find_group_by, filter_In; split; [exact Hx|apply eqb_refl]. }
  destruct (Index.find F (label x) (Index.group_by F label keys)) as [|r rest] eqn:Hfind.
  - contradiction.
  - exists r, rest; split; [reflexivity|].
    apply (bucket_member keys x r); rewrite Hfind; now left.
Qed.

Local Definition grouped keys a b :=
  a = b \/ In a keys /\ In b keys /\ label a = label b.

Local Lemma grouped_sym keys a b : grouped keys a b -> grouped keys b a.
Proof.
  unfold grouped; intuition congruence.
Qed.

Local Lemma grouped_trans keys a b c :
  grouped keys a b -> grouped keys b c -> grouped keys a c.
Proof.
  unfold grouped; intuition congruence.
Qed.

Local Lemma rebuild_sound keys todo :
  (forall x, In x todo -> In x keys) ->
  forall a b, UnionFind.equiv E
    (partition_rebuild todo (Index.group_by F label keys)) a b -> grouped keys a b.
Proof.
  induction todo as [|x rest IH]; intros Hsub a b; rewrite partition_rebuild_equation.
  - rewrite UnionFind.make_equiv; intro Hab; now left.
  - destruct (bucket_head keys x (Hsub x (or_introl eq_refl)))
      as [r [bucket [Hfind [Hr Hlabel]]]]; rewrite Hfind.
    rewrite (UnionFind.union_equiv E HE) by apply partition_rebuild_wf.
    assert (Hxr : grouped keys x r).
    { right; repeat split; try assumption; [apply Hsub; now left|symmetry; exact Hlabel]. }
    assert (Htail : forall a b, UnionFind.equiv E
      (partition_rebuild rest (Index.group_by F label keys)) a b -> grouped keys a b).
    { apply IH; intros z Hz; apply Hsub; now right. }
    intros [Hab|[[Hax Hrb]|[Har Hxb]]].
    + now apply Htail.
    + eapply grouped_trans; [apply Htail; exact Hax|].
      eapply grouped_trans; [exact Hxr|apply Htail; exact Hrb].
    + eapply grouped_trans; [apply Htail; exact Har|].
      eapply grouped_trans; [apply grouped_sym; exact Hxr|apply Htail; exact Hxb].
Qed.

Local Lemma rebuild_complete keys todo :
  (forall x, In x todo -> In x keys) ->
  forall x r bucket, In x todo ->
    Index.find F (label x) (Index.group_by F label keys) = r :: bucket ->
    UnionFind.equiv E (partition_rebuild todo (Index.group_by F label keys)) x r.
Proof.
  induction todo as [|y rest IH]; intros Hsub x r bucket Hx Hfind.
  - contradiction.
  - rewrite partition_rebuild_equation.
    destruct (bucket_head keys y (Hsub y (or_introl eq_refl)))
      as [s [ys [Hlookup [Hs Hlabel]]]]; rewrite Hlookup.
    apply (UnionFind.union_equiv E HE); [apply partition_rebuild_wf|].
    destruct Hx as [Heq|Hx].
    + subst x; rewrite Hfind in Hlookup; injection Hlookup as Heq _; subst s.
      right; left; split; apply UnionFind.equiv_equation; reflexivity.
    + left; eapply IH; [|exact Hx|exact Hfind].
      intros z Hz; apply Hsub; now right.
Qed.

(** Group reconstruction connects exactly the supported keys that have equal labels. *)
Theorem partition_group_equiv keys a b :
  UnionFind.equiv E (partition_group keys) a b <->
  a = b \/ In a keys /\ In b keys /\ label a = label b.
Proof.
  rewrite partition_group_equation; split.
  - apply rebuild_sound; tauto.
  - intros [Heq|[Ha [Hb Hlabel]]].
    + subst b; apply UnionFind.equiv_equation; reflexivity.
    + destruct (bucket_head keys a Ha) as [r [bucket [Hfind _]]].
      pose proof (rebuild_complete keys keys ltac:(tauto) a r bucket Ha Hfind) as Har.
      rewrite Hlabel in Hfind.
      pose proof (rebuild_complete keys keys ltac:(tauto) b r bucket Hb Hfind) as Hbr.
      apply UnionFind.equiv_equation in Har, Hbr.
      apply UnionFind.equiv_equation; congruence.
Qed.
End Group.

(** Reconstruction overhead includes a list cell and one label callback invocation. *)
Definition partition_group_k : N := 2.

(** A proof-only account sums label, index and union charges along the actual reconstruction. *)
Fixpoint partition_rebuild_account {K J} (E : encoding K) (F : encoding J)
    (label_c : K -> Cost.t J) keys idx (charge : N) : Prop :=
  match keys with
  | [] => charge = Cost.ticks (@UnionFind.make_c K)
  | x :: rest =>
    let u := partition_rebuild E F label_c rest idx in
    let j := Cost.value (label_c x) in
    exists tail_charge, partition_rebuild_account E F label_c rest idx tail_charge /\
    charge = (Cost.ticks (label_c x) + Cost.ticks (Index.find_c F j idx) +
      match Index.find F j idx with
      | [] => 0
      | r :: _ => Cost.ticks (UnionFind.union_c E x r u)
      end + tail_charge)%N
  end.

(** Every reconstruction has a callee-relative account without any cost assumptions. *)
Theorem partition_rebuild_account_exists {K J} (E : encoding K) (F : encoding J)
    label_c keys idx : exists charge, partition_rebuild_account E F label_c keys idx charge.
Proof.
  induction keys as [|x rest [charge IH]].
  - exists (Cost.ticks (@UnionFind.make_c K)); reflexivity.
  - eexists; exists charge; split; [exact IH|reflexivity].
Qed.

(** The reconstruction bound retains every actual Base and label charge. *)
Theorem partition_rebuild_cost {K J} (E : encoding K) (F : encoding J)
    label_c keys idx charge : partition_rebuild_account E F label_c keys idx charge ->
  Cost.ticks (partition_rebuild_c E F label_c keys idx) =
  (partition_group_k * N.of_nat (length keys) + charge)%N.
Proof.
  revert charge; induction keys as [|x rest IH]; intros charge Haccount.
  - cbn [partition_rebuild_account] in Haccount; subst charge; reflexivity.
  - destruct Haccount as [tail_charge [Htail ->]].
    cbn [partition_rebuild_c length].
    autorewrite with galois_cost.
    fold (partition_rebuild E F label_c rest idx).
    fold (Index.find F (Cost.value (label_c x)) idx).
    rewrite (IH tail_charge Htail), Nat2N.inj_succ; unfold partition_group_k.
    destruct (Index.find F (Cost.value (label_c x)) idx);
      autorewrite with galois_cost; lia.
Qed.

(** Grouping charges one actual group-by call and the indexed reconstruction. *)
Theorem partition_group_cost {K J} (E : encoding K) (F : encoding J) label_c keys charge :
  partition_rebuild_account E F label_c keys
    (Index.group_by F (fun x => Cost.value (label_c x)) keys) charge ->
  Cost.ticks (partition_group_c E F label_c keys) =
  (Cost.ticks (Index.group_by_c F label_c keys) +
    partition_group_k * N.of_nat (length keys) + charge)%N.
Proof.
  intro Haccount; unfold partition_group_c.
  rewrite Cost.ticks_bind, Index.group_by_c_value.
  rewrite (partition_rebuild_cost _ _ _ _ _ _ Haccount); lia.
Qed.
