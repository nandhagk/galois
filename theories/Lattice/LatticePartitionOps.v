(** * Equality updates and forgetting

    Union adds an equality and forgetting rebuilds classes without the forgotten key.
    For example, forgetting 2 from the class [1; 2; 3] keeps 1 equal to 3.
    Builds on: BaseUnionFind, BaseEq, LatticePartition and LatticePartitionGroup. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseUnionFind BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticePartition
  LatticePartitionGroup.
Import List.ListNotations Cost.Notations.

Section Operations.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).

(** Union refines the public forest computation with its preservation certificate. *)
Definition partition_union_c (x y : K) (p : partition_t E) : Cost.t (partition_t E) :=
  Cost.step ;;
  match p with
  | None => Cost.ret None
  | Some u => Cost.map (@Some _)
      (Cost.refine (UnionFind.union_c E x y (proj1_sig u))
        (UnionFind.wf_union E HE _ x y (proj2_sig u)))
  end.

(** Union observes the value of the certificate-preserving computation. *)
Definition partition_union x y p := Cost.value (partition_union_c x y p).

(** Union adds exactly the equalities induced by its two merged classes. *)
Theorem partition_union_spec x y a b p :
  partition_equiv E (partition_union x y p) a b <->
  partition_equiv E p a b \/
  (partition_equiv E p a x /\ partition_equiv E p y b) \/
  (partition_equiv E p a y /\ partition_equiv E p x b).
Proof.
  destruct p as [[u Hu]|]; cbn [partition_union partition_union_c];
    autorewrite with galois_cost; cbn [partition_equiv proj1_sig].
  - apply (UnionFind.union_equiv E HE); exact Hu.
  - tauto.
Qed.

(** Filtering charges a list step and the actual encoded-key comparison for each support key. *)
Fixpoint partition_without_c (x : K) (keys : list K) : Cost.t (list K) :=
  match keys with
  | [] => Cost.ret []
  | k :: rest =>
    Cost.step ;;
    let* same := eqb_c E k x in
    let* tail := partition_without_c x rest in
    Cost.ret (if same then tail else k :: tail)
  end.

(** Filtering removes precisely the key being forgotten. *)
Theorem partition_without_value x keys :
  Cost.value (partition_without_c x keys) = filter (fun k => negb (eqb E k x)) keys.
Proof.
  induction keys as [|k rest IH]; cbn [partition_without_c filter];
    autorewrite with galois_cost; [reflexivity|].
  rewrite IH; fold (eqb E k x); destruct (eqb E k x); reflexivity.
Qed.

(** The support after filtering consists of the old support keys unequal to the forgotten key. *)
Theorem partition_without_spec x keys a :
  In a (Cost.value (partition_without_c x keys)) <-> In a keys /\ a <> x.
Proof.
  rewrite partition_without_value, filter_In, Bool.negb_true_iff, (eqb_false_iff E HE).
  reflexivity.
Qed.

(** Filtering retains at most the original support length. *)
Theorem partition_without_length x keys :
  length (Cost.value (partition_without_c x keys)) <= length keys.
Proof.
  rewrite partition_without_value.
  induction keys as [|k rest IH]; [reflexivity|].
  cbn [filter]; destruct (negb (eqb E k x)); cbn [length]; lia.
Qed.

(** Forgetting labels each retained key by its original representative. *)
Definition partition_forget_label_c u k := Cost.map fst (UnionFind.find_c E k u).

(** Forgetting rebuilds once over the retained support and one representative index. *)
Definition partition_forget_raw_c x u :=
  let* keys := UnionFind.keys_c E u in
  let* kept := partition_without_c x keys in
  partition_group_c E E (partition_forget_label_c u) kept.

(** The reconstructed forest satisfies every representation invariant. *)
Theorem partition_forget_wf x u :
  UnionFind.wf E (Cost.value (partition_forget_raw_c x u)).
Proof.
  unfold partition_forget_raw_c; rewrite !Cost.value_bind.
  apply (partition_group_wf E E _ HE).
Qed.

(** Forgetting attaches a certificate to the rebuilt forest and keeps None unreachable. *)
Definition partition_forget_c x (p : partition_t E) : Cost.t (partition_t E) :=
  Cost.step ;;
  match p with
  | None => Cost.ret None
  | Some u => Cost.map (@Some _)
      (Cost.refine (partition_forget_raw_c x (proj1_sig u)) (partition_forget_wf x _))
  end.

(** The pure forgetting operation observes its costed reconstruction. *)
Definition partition_forget x p := Cost.value (partition_forget_c x p).

(** Forgetting an unreachable state leaves it unreachable. *)
Theorem partition_forget_unreached x : partition_forget x None = None.
Proof.
  reflexivity.
Qed.

(** Forgetting isolates its key and retains every equality between other keys. *)
Theorem partition_forget_spec x a b p : p <> None ->
  (partition_equiv E (partition_forget x p) a b <->
    (partition_equiv E p a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
Proof.
  destruct p as [[u Hu]|]; [intro Hreached|contradiction].
  cbn [partition_forget partition_forget_c]; autorewrite with galois_cost.
  cbn [partition_equiv proj1_sig].
  unfold partition_forget_raw_c; autorewrite with galois_cost.
  change (UnionFind.equiv E
    (partition_group E E (partition_forget_label_c u)
      (Cost.value (partition_without_c x (UnionFind.keys E u)))) a b <->
    (UnionFind.equiv E u a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
  rewrite (partition_group_equiv E E _ HE HE), !partition_without_spec.
  unfold partition_forget_label_c; rewrite !Cost.value_map.
  fold (UnionFind.find E a u); fold (UnionFind.find E b u).
  rewrite <- UnionFind.equiv_equation.
  split.
  - intros [Heq|[[Ha Hax] [[Hb Hbx] Hab]]]; [|now left].
    subst b; destruct (eqb_dec E HE a x) as [Heq|Hne].
    + now right.
    + left; repeat split; try assumption; apply UnionFind.equiv_equation; reflexivity.
  - intros [[Hab [Hax Hbx]]|[Hax Hbx]]; [|left; congruence].
    destruct (eqb_dec E HE a b) as [Heq|Hne]; [now left|].
    destruct (partition_support_pair E HE u a b Hu Hab Hne) as [Ha Hb].
    right; tauto.
Qed.

(** Forgetting moves upward because it only removes equalities. *)
Theorem partition_forget_leb x p :
  leb (partition_lattice E HE) p (partition_forget x p) = true.
Proof.
  destruct p as [u|]; [|reflexivity].
  apply (partition_forest_leb_spec E HE); intros a b Hab.
  change (partition_equiv E (partition_forget x (Some u)) a b) in Hab.
  apply partition_forget_spec in Hab; [|discriminate].
  destruct Hab as [[Hab _]|[Hax Hbx]]; [exact Hab|subst; apply UnionFind.equiv_equation].
  reflexivity.
Qed.

(** Updating a valuation tests the public encoded-key equality. *)
Definition key_update {V} (x : K) (v : V) (s : K -> V) : K -> V :=
  fun k => if eqb E k x then v else s k.

(** A valuation update satisfies the partition after the updated key is forgotten. *)
Theorem partition_forget_gamma {V} x p (s : K -> V) v :
  gamma (partition_gamma E) p s ->
  gamma (partition_gamma E) (partition_forget x p) (key_update x v s).
Proof.
  destruct p as [u|]; [intro Hgamma|contradiction].
  intros a b Hab.
  change (partition_equiv E (partition_forget x (Some u)) a b) in Hab.
  apply partition_forget_spec in Hab; [|discriminate].
  destruct Hab as [[Hab [Hax Hbx]]|[Hax Hbx]].
  - unfold key_update.
    rewrite (proj2 (eqb_false_iff E HE a x) Hax), (proj2 (eqb_false_iff E HE b x) Hbx).
    exact (Hgamma a b Hab).
  - now subst.
Qed.

(** The test returns its boolean observation and a valid compressed partition. *)
Definition partition_test_c x y (p : partition_t E) : Cost.t (bool * partition_t E) :=
  Cost.step ;;
  match p with
  | None => Cost.ret (true, None)
  | Some u =>
    let result := UnionFind.equivb_c E x y (proj1_sig u) in
    let certified := Cost.refine (P := fun r => UnionFind.wf E (snd r)) result
      (proj1 (proj2 (UnionFind.equivb_correct E HE _ x y (proj2_sig u)))) in
    Cost.map (fun r : {r : bool * UnionFind.t K | UnionFind.wf E (snd r)} =>
      (fst (proj1_sig r), Some (exist _ (snd (proj1_sig r)) (proj2_sig r))))
      certified
  end.

(** The pure test observes the costed compressed result. *)
Definition partition_test x y p := Cost.value (partition_test_c x y p).

(** Testing recognises the original equality and preserves all classes in its returned fact. *)
Theorem partition_test_correct x y p :
  (fst (partition_test x y p) = true <-> partition_equiv E p x y) /\
  (forall a b, partition_equiv E (snd (partition_test x y p)) a b <->
    partition_equiv E p a b).
Proof.
  destruct p as [[u Hu]|]; cbn [partition_test partition_test_c];
    autorewrite with galois_cost; cbn [fst snd proj1_sig partition_equiv].
  - destruct (UnionFind.equivb_correct E HE u x y Hu) as [Htest [_ Hagrees]].
    split; assumption.
  - tauto.
Qed.

(** Union charges its actual UnionFind call and one option-case tick. *)
Theorem partition_union_cost x y p :
  Cost.ticks (partition_union_c x y p) =
  (1 + match p with
       | None => 0
       | Some u => Cost.ticks (UnionFind.union_c E x y (proj1_sig u))
       end)%N.
Proof.
  destruct p; cbn [partition_union_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Testing charges its actual UnionFind call and one option-case tick. *)
Theorem partition_test_cost x y p :
  Cost.ticks (partition_test_c x y p) =
  (1 + match p with
       | None => 0
       | Some u => Cost.ticks (UnionFind.equivb_c E x y (proj1_sig u))
       end)%N.
Proof.
  destruct p; cbn [partition_test_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Filtering accounts for one traversal tick and every actual equality comparison. *)
Theorem partition_without_cost x keys :
  Cost.ticks (partition_without_c x keys) =
    (N.of_nat (length keys) +
      fold_right (fun k n => Cost.ticks (eqb_c E k x) + n)%N 0%N keys)%N.
Proof.
  induction keys as [|k rest IH]; [reflexivity|].
  cbn [partition_without_c length fold_right]; autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ; lia.
Qed.

(** Forgetting retains support enumeration, filtering, group-by and reconstruction costs. *)
Theorem partition_forget_cost x u charge :
  let keys := UnionFind.keys E (proj1_sig u) in
  let kept := Cost.value (partition_without_c x keys) in
  let label := partition_forget_label_c (proj1_sig u) in
  partition_rebuild_account E E label kept
    (Index.group_by E (fun k => Cost.value (label k)) kept) charge ->
  Cost.ticks (partition_forget_c x (Some u)) =
    (1 + Cost.ticks (UnionFind.keys_c E (proj1_sig u)) +
      Cost.ticks (partition_without_c x keys) +
      Cost.ticks (Index.group_by_c E label kept) +
      partition_group_k * N.of_nat (length kept) + charge)%N.
Proof.
  cbn zeta; intro Haccount; unfold partition_forget_c, partition_forget_raw_c.
  autorewrite with galois_cost.
  fold (UnionFind.keys E (proj1_sig u)).
  rewrite (partition_group_cost _ _ _ _ _ Haccount); lia.
Qed.

(** Forgetting an unreachable state costs its single option-case tick. *)
Theorem partition_forget_unreached_cost x :
  Cost.ticks (partition_forget_c x None) = 1%N.
Proof.
  reflexivity.
Qed.
End Operations.
