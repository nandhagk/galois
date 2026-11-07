(** * Finite class witnesses for union-find ranks

    Rank-size certificates count distinct members of each class without enumerating the carrier.
    For example, an unknown key has rank zero and the singleton witness containing that key.
    Builds on: BaseUnionFind and its public support and compression contracts. *)

From Stdlib Require Import List NArith PeanoNat Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.
Import List.ListNotations.

Local Open Scope nat_scope.

Module UnionFindRank.

(** A class witness may contain its queried singleton outside support.
    Supported queries therefore have witnesses entirely inside the finite known-key set. *)
Record rank_size_inv {K} (E : encoding K) (uf : UnionFind.t K) : Prop := Rank_size_inv {
  forest_wf : UnionFind.wf E uf;
  class_witness : forall x, exists members,
    NoDup members /\
    Forall (UnionFind.equiv E uf x) members /\
    Forall (fun a => UnionFind.support E uf a \/ a = x) members /\
    2 ^ UnionFind.rank_of E uf x <= length members;
  maximum_attained : UnionFind.max_rank uf = 0 \/
    exists root, UnionFind.rank_of E uf root = UnionFind.max_rank uf
}.

(** Empty construction has singleton classes and a zero attained maximum. *)
Theorem rank_size_inv_make {K} (E : encoding K) :
  rank_size_inv E (@UnionFind.make K).
Proof.
  constructor.
  - apply UnionFind.wf_make.
  - intro x. exists [x]. split.
    + constructor; [intro H; contradiction|constructor].
    + split.
      * constructor; [apply UnionFind.equiv_equation; reflexivity|constructor].
      * split.
        -- constructor; [right; reflexivity|constructor].
        -- rewrite UnionFind.rank_of_equation, UnionFind.make_equation.
           cbn [UnionFind.ranks]. rewrite Map.get_empty. reflexivity.
  - left. rewrite UnionFind.make_equation. reflexivity.
Qed.

(** Compression transports the same distinct class witnesses and the same attained maximum. *)
Theorem find_rank_size_inv {K} (E : encoding K) (HE : encoding_laws E) uf x :
  rank_size_inv E uf -> rank_size_inv E (snd (UnionFind.find E x uf)).
Proof.
  intros [Hwf Hclasses Hmax]. constructor.
  - apply UnionFind.wf_find; assumption.
  - intro a. destruct (Hclasses a) as [members [Hnodup [Hequiv [Hsupport Hsize]]]].
    exists members. split; [exact Hnodup|]. split.
    + rewrite Forall_forall in *. intros b Hin.
      apply (proj2 (proj2 (UnionFind.find_equiv E HE uf x Hwf) a b)).
      exact (Hequiv b Hin).
    + split.
      * rewrite Forall_forall in *. intros b Hin.
        destruct (Hsupport b Hin) as [Hknown|Hequal]; [left|right; exact Hequal].
        apply (proj2 (UnionFind.find_support E HE x uf b Hwf)). exact Hknown.
      * rewrite UnionFind.find_rank_of. exact Hsize.
  - rewrite (proj2 (UnionFind.find_ranks E uf x)).
    destruct Hmax as [Hzero|[root Hroot]]; [left; exact Hzero|right].
    exists root. rewrite UnionFind.find_rank_of. exact Hroot.
Qed.

Local Lemma positive_rank_known {K} (E : encoding K) uf x :
  0 < UnionFind.rank_of E uf x -> UnionFind.support E uf x.
Proof.
  rewrite UnionFind.rank_of_equation. unfold UnionFind.support.
  destruct (Map.get E x (UnionFind.ranks uf)) as [r|] eqn:Hrank.
  - intros Hpositive. right. discriminate.
  - lia.
Qed.

(** Every rank is logarithmic in known support and unknown singleton queries have rank zero. *)
Theorem rank_le_log2_keys {K} (E : encoding K) (HE : encoding_laws E) uf x :
  rank_size_inv E uf ->
  UnionFind.rank_of E uf x <= Nat.log2 (length (UnionFind.keys E uf)).
Proof.
  intros [Hwf Hclasses Hmax].
  destruct (Nat.eq_dec (UnionFind.rank_of E uf x) 0) as [Hzero|Hpositive]; [lia|].
  assert (Hknown : UnionFind.support E uf x) by (apply positive_rank_known; lia).
  destruct (Hclasses x) as [members [Hnodup [Hequiv [Hsupport Hsize]]]].
  assert (Hincl : incl members (UnionFind.keys E uf)).
  { intros a Hin. apply (proj2 (UnionFind.keys_spec E HE uf a Hwf)).
    rewrite Forall_forall in Hsupport.
    destruct (Hsupport a Hin) as [Hknowna|Hequal]; [exact Hknowna|subst a; exact Hknown]. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  assert (Hnonzero : 0 < length (UnionFind.keys E uf)).
  { pose proof (Nat.pow_nonzero 2 (UnionFind.rank_of E uf x) ltac:(lia)). lia. }
  apply (proj1 (Nat.log2_le_pow2 _ _ Hnonzero)). lia.
Qed.

(** An attained maximum also obeys the finite-support logarithmic bound. *)
Theorem max_rank_le_log2_keys {K} (E : encoding K) (HE : encoding_laws E) uf :
  rank_size_inv E uf ->
  UnionFind.max_rank uf <= Nat.log2 (length (UnionFind.keys E uf)).
Proof.
  intro Hinv. destruct (maximum_attained E uf Hinv) as [Hzero|[root Hroot]].
  - lia.
  - rewrite <- Hroot. exact (rank_le_log2_keys E HE uf root Hinv).
Qed.

Local Lemma root_rep {K} (E : encoding K) uf root :
  Map.get E root (UnionFind.parents uf) = None ->
  fst (UnionFind.find E root uf) = root.
Proof.
  intro Hroot. rewrite UnionFind.find_equation, UnionFind.find_fuel_equation, Hroot.
  reflexivity.
Qed.

Local Lemma class_transport {K} (E : encoding K) old new x :
  (forall a b, UnionFind.equiv E old a b -> UnionFind.equiv E new a b) ->
  (forall a, UnionFind.support E old a -> UnionFind.support E new a) ->
  UnionFind.rank_of E new x = UnionFind.rank_of E old x ->
  (exists members, NoDup members /\
    Forall (UnionFind.equiv E old x) members /\
    Forall (fun a => UnionFind.support E old a \/ a = x) members /\
    2 ^ UnionFind.rank_of E old x <= length members) ->
  exists members, NoDup members /\
    Forall (UnionFind.equiv E new x) members /\
    Forall (fun a => UnionFind.support E new a \/ a = x) members /\
    2 ^ UnionFind.rank_of E new x <= length members.
Proof.
  intros Hequiv Hsupport Hrank [members [Hnodup [Hclass [Hknown Hsize]]]].
  exists members. split; [exact Hnodup|]. split.
  - eapply Forall_impl; [|exact Hclass]. intros a Ha. apply Hequiv. exact Ha.
  - split.
    + eapply Forall_impl; [|exact Hknown]. intros a [Ha|Ha]; auto.
    + rewrite Hrank. exact Hsize.
Qed.

Local Lemma double_class {K} (E : encoding K) old new child root :
  rank_size_inv E old ->
  child <> root ->
  Map.get E child (UnionFind.parents old) = None ->
  Map.get E root (UnionFind.parents old) = None ->
  UnionFind.rank_of E old child = UnionFind.rank_of E old root ->
  (forall a b, UnionFind.equiv E old a b -> UnionFind.equiv E new a b) ->
  (forall a, UnionFind.support E old a -> UnionFind.support E new a) ->
  UnionFind.equiv E new root child ->
  UnionFind.support E new root -> UnionFind.support E new child ->
  exists members, NoDup members /\
    Forall (UnionFind.equiv E new root) members /\
    Forall (fun a => UnionFind.support E new a \/ a = root) members /\
    2 ^ S (UnionFind.rank_of E old root) <= length members.
Proof.
  intros Hinv Hne Hchild Hroot Hr Hequiv Hsupport Hmerged Hsr Hsc.
  destruct (class_witness E old Hinv root) as [rs [Hnr [Her [Hsr' Hlr]]]].
  destruct (class_witness E old Hinv child) as [cs [Hnc [Hec [Hsc' Hlc]]]].
  exists (rs ++ cs). split.
  - apply NoDup_app; [exact Hnr|exact Hnc|].
    intros a Har Hac. rewrite Forall_forall in Her, Hec.
    specialize (Her a Har). specialize (Hec a Hac).
    rewrite UnionFind.equiv_equation, (root_rep E old root Hroot) in Her.
    rewrite UnionFind.equiv_equation, (root_rep E old child Hchild) in Hec. congruence.
  - split.
    + rewrite Forall_app. split.
      * eapply Forall_impl; [|exact Her]. intros a Ha. apply Hequiv. exact Ha.
      * eapply Forall_impl; [|exact Hec]. intros a Ha. apply Hequiv in Ha.
        rewrite UnionFind.equiv_equation in Hmerged, Ha |- *. congruence.
    + split.
      * rewrite Forall_app. split.
        -- eapply Forall_impl; [|exact Hsr']. intros a [Ha|Ha].
           ++ left. apply Hsupport. exact Ha.
           ++ subst a. left. exact Hsr.
        -- eapply Forall_impl; [|exact Hsc']. intros a [Ha|Ha].
           ++ left. apply Hsupport. exact Ha.
           ++ subst a. left. exact Hsc.
      * rewrite length_app, Nat.pow_succ_r by lia. rewrite Hr in Hlc. lia.
Qed.

(** Equal-rank root linking doubles a class witness and increments only the winner's rank. *)
Theorem link_rank_size_inv {K} (E : encoding K) (HE : encoding_laws E)
    uf child root (raise : bool) :
  rank_size_inv E uf ->
  child <> root ->
  Map.get E child (UnionFind.parents uf) = None ->
  Map.get E root (UnionFind.parents uf) = None ->
  (if raise then UnionFind.rank_of E uf child = UnionFind.rank_of E uf root
   else UnionFind.rank_of E uf child < UnionFind.rank_of E uf root) ->
  rank_size_inv E (UnionFind.link E child root raise uf).
Proof.
  intros Hinv Hne Hchild Hroot Hrank.
  pose proof (forest_wf E uf Hinv) as Hwf.
  assert (Hnew : UnionFind.wf E (UnionFind.link E child root raise uf)).
  { apply UnionFind.wf_link; try assumption. destruct raise; lia. }
  assert (Hequiv : forall a b, UnionFind.equiv E uf a b ->
    UnionFind.equiv E (UnionFind.link E child root raise uf) a b).
  { intros a b Hab. apply (proj2
      (UnionFind.link_equiv_equation E HE child root raise uf a b
        Hwf Hnew Hne Hchild Hroot)). left. exact Hab. }
  assert (Hsupport : forall a, UnionFind.support E uf a ->
    UnionFind.support E (UnionFind.link E child root raise uf) a).
  { intros a Ha. apply (proj2 (UnionFind.link_support_equation E HE child root raise uf a Hwf)).
    right. right. exact Ha. }
  constructor; [exact Hnew| |].
  - intro x. destruct raise.
    + destruct (eqb_dec E HE x root) as [Hequal|Hother].
      * subst x. rewrite (UnionFind.link_rank_equation E HE) by exact (proj1 (proj2 Hwf)).
        rewrite eqb_refl.
        apply (double_class E uf (UnionFind.link E child root true uf) child root Hinv
          Hne Hchild Hroot Hrank Hequiv Hsupport).
        -- apply (proj2 (UnionFind.link_equiv_equation E HE child root true uf root child
             Hwf Hnew Hne Hchild Hroot)).
           right. right. rewrite (root_rep E uf root Hroot), (root_rep E uf child Hchild).
           split; reflexivity.
        -- apply (proj2 (UnionFind.link_support_equation E HE child root true uf root Hwf)).
           right. left. auto.
        -- apply (proj2 (UnionFind.link_support_equation E HE child root true uf child Hwf)).
           left. reflexivity.
      * apply (class_transport E uf _ x Hequiv Hsupport).
        -- rewrite (UnionFind.link_rank_equation E HE) by exact (proj1 (proj2 Hwf)).
           destruct (eqb E x root) eqn:Heq; [|reflexivity].
           apply (eqb_true_iff E HE) in Heq. contradiction.
        -- exact (class_witness E uf Hinv x).
    + apply (class_transport E uf _ x Hequiv Hsupport).
      * rewrite (UnionFind.link_rank_equation E HE) by exact (proj1 (proj2 Hwf)).
        reflexivity.
      * exact (class_witness E uf Hinv x).
  - destruct raise.
    + rewrite UnionFind.link_equation. cbn [UnionFind.max_rank].
      destruct (Nat.le_gt_cases (UnionFind.max_rank uf) (S (UnionFind.rank_of E uf root)))
        as [Hnewmax|Holdmax].
      * right. exists root.
        change (UnionFind.rank_of E (UnionFind.link E child root true uf) root =
          Nat.max (UnionFind.max_rank uf) (S (UnionFind.rank_of E uf root))).
        rewrite (UnionFind.link_rank_equation E HE) by exact (proj1 (proj2 Hwf)).
        rewrite eqb_refl, Nat.max_r by lia. reflexivity.
      * destruct (maximum_attained E uf Hinv) as [Hzero|[a Ha]]; [lia|].
        right. exists a.
        change (UnionFind.rank_of E (UnionFind.link E child root true uf) a =
          Nat.max (UnionFind.max_rank uf) (S (UnionFind.rank_of E uf root))).
        rewrite (UnionFind.link_rank_equation E HE) by exact (proj1 (proj2 Hwf)).
        rewrite Nat.max_l by lia.
        destruct (eqb E a root) eqn:Heq; [|exact Ha].
        apply (eqb_true_iff E HE) in Heq. subst a. lia.
    + rewrite UnionFind.link_equation, UnionFind.redirect_equation. cbn [UnionFind.max_rank].
      destruct (maximum_attained E uf Hinv) as [Hzero|[a Ha]]; [left; exact Hzero|].
      right. exists a. exact Ha.
Qed.

Local Lemma touch_rank_size_inv {K} (E : encoding K) (HE : encoding_laws E) uf x :
  rank_size_inv E uf -> rank_size_inv E (UnionFind.touch E x uf).
Proof.
  intro Hinv.
  destruct (UnionFind.touch_spec E HE uf x (forest_wf E uf Hinv))
    as [Hnew [Hmax [Hranks [Hequiv Hsupport]]]].
  constructor; [exact Hnew| |].
  - intro a. apply (class_transport E uf _ a).
    + intros b c Hbc. apply (proj2 (Hequiv b c)). exact Hbc.
    + exact Hsupport.
    + apply Hranks.
    + exact (class_witness E uf Hinv a).
  - rewrite Hmax. destruct (maximum_attained E uf Hinv) as [Hzero|[a Ha]].
    + left. exact Hzero.
    + right. exists a. rewrite Hranks. exact Ha.
Qed.

Local Lemma reaches_root {K} (E : encoding K) uf a root :
  UnionFind.reaches E uf a root -> Map.get E root (UnionFind.parents uf) = None.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

Local Lemma compression_root {K} (E : encoding K) (HE : encoding_laws E) uf x root :
  UnionFind.wf E uf -> Map.get E root (UnionFind.parents uf) = None ->
  Map.get E root (UnionFind.parents (snd (UnionFind.find E x uf))) = None.
Proof.
  intros Hwf Hroot.
  apply (reaches_root E _ root root).
  apply (proj2 (proj2 (proj2 (UnionFind.find_correct E HE x uf Hwf)) root root)).
  apply UnionFind.Root. exact Hroot.
Qed.

(** Union preserves rank-size certificates through its two actual finds and root link. *)
Theorem union_rank_size_inv {K} (E : encoding K) (HE : encoding_laws E) uf x y :
  rank_size_inv E uf -> rank_size_inv E (UnionFind.union E x y uf).
Proof.
  intro Hinv. rewrite UnionFind.union_equation.
  pose proof (find_rank_size_inv E HE uf x Hinv) as Hinv1.
  pose proof (UnionFind.find_root E HE uf x (forest_wf E uf Hinv)) as Hrootx.
  destruct (UnionFind.find E x uf) as [rx u1] eqn:Hx. cbn [fst snd] in Hinv1, Hrootx.
  pose proof (find_rank_size_inv E HE u1 y Hinv1) as Hinv2.
  pose proof (UnionFind.find_root E HE u1 y (forest_wf E u1 Hinv1)) as Hrooty.
  pose proof (compression_root E HE u1 y rx (forest_wf E u1 Hinv1) (proj2 Hrootx))
    as Hrx.
  destruct (UnionFind.find E y u1) as [ry u2] eqn:Hy.
  cbn [fst snd] in Hinv2, Hrooty, Hrx.
  destruct (eqb E rx ry) eqn:Heq.
  - apply touch_rank_size_inv; assumption.
  - apply (eqb_false_iff E HE) in Heq.
    destruct (Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry))
      eqn:Hcmp.
    + apply Nat.compare_eq_iff in Hcmp.
      apply link_rank_size_inv; try assumption; try congruence. exact (proj2 Hrooty).
    + apply Nat.compare_lt_iff in Hcmp.
      apply link_rank_size_inv; try assumption. exact (proj2 Hrooty).
    + apply Nat.compare_gt_iff in Hcmp.
      apply link_rank_size_inv; try assumption; try congruence. exact (proj2 Hrooty).
Qed.

(** Known classes have the rank's required number of distinct known members, including at roots. *)
Theorem known_class_witness {K} (E : encoding K) (HE : encoding_laws E) uf x :
  rank_size_inv E uf -> UnionFind.support E uf x ->
  exists members, NoDup members /\ incl members (UnionFind.keys E uf) /\
    Forall (UnionFind.equiv E uf x) members /\
    2 ^ UnionFind.rank_of E uf x <= length members.
Proof.
  intros Hinv Hknown.
  destruct (class_witness E uf Hinv x) as [members [Hnodup [Hclass [Hsupport Hsize]]]].
  exists members. split; [exact Hnodup|]. split; [|split; assumption].
  intros a Hin. apply (proj2 (UnionFind.keys_spec E HE uf a (forest_wf E uf Hinv))).
  rewrite Forall_forall in Hsupport.
  destruct (Hsupport a Hin) as [Ha|Ha]; [exact Ha|subst a; exact Hknown].
Qed.

(** Pair-list initialization establishes rank-size certificates through every actual union. *)
Theorem of_unions_rank_size_inv {K} (E : encoding K) (HE : encoding_laws E) pairs :
  rank_size_inv E (UnionFind.of_unions E pairs).
Proof.
  rewrite UnionFind.of_unions_equation.
  assert (Hfold : forall uf, rank_size_inv E uf ->
    rank_size_inv E
      (fold_left (fun acc xy => UnionFind.union E (fst xy) (snd xy) acc) pairs uf)).
  { induction pairs as [|[x y] pairs IH]; intros uf Hinv; cbn [fold_left fst snd].
    - exact Hinv.
    - apply IH. apply union_rank_size_inv; assumption. }
  apply Hfold. apply rank_size_inv_make.
Qed.

End UnionFindRank.
