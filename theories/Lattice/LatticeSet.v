(** * May and must collections

    Well-formed finite sets model may facts and finite conjunctions model must facts.
    For example, a must join retains precisely the facts shared by its two inputs.
    Builds on: BaseSet, LatticeKitFamily and LatticeAdjoin. *)

From Stdlib Require Import Bool List Arith NArith Lia Sorting.Sorted Sorting.Permutation.
From Galois.Cost Require Import CostMonad CostList CostTactics.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit
  LatticeKitFamily LatticeSimple LatticeAdjoin.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

(** The public set carrier certifies representation validity without semantic laws. *)
Definition set_t {K} (E : encoding K) := {s : FinSet.t K | FinSet.wf E s}.

(** Raw projection forgets the erased representation certificate. *)
Definition set_raw {K} {E : encoding K} (s : set_t E) := proj1_sig s.

Definition set_empty {K} (E : encoding K) : set_t E :=
  exist _ FinSet.empty (FinSet.wf_empty E).

Definition set_of_list_c {K} (E : encoding K) xs : Cost.t (set_t E) :=
  Cost.refine (FinSet.of_list_c E xs) (FinSet.wf_of_list E xs).

Definition set_of_list {K} (E : encoding K) xs := Cost.value (set_of_list_c E xs).

(** List conversion retains exactly the underlying charged finite-set construction. *)
Theorem set_of_list_cost {K} (E : encoding K) xs :
  Cost.ticks (set_of_list_c E xs) = Cost.ticks (FinSet.of_list_c E xs).
Proof.
  unfold set_of_list_c; apply Cost.ticks_refine.
Qed.

Definition set_add_c {K} (E : encoding K) k (s : set_t E) : Cost.t (set_t E) :=
  Cost.refine (FinSet.add_c E k (set_raw s)) (FinSet.wf_add E k _ (proj2_sig s)).

Definition set_add {K} (E : encoding K) k s := Cost.value (set_add_c E k s).

Definition set_union_c {K} (E : encoding K) (s t : set_t E) : Cost.t (set_t E) :=
  Cost.refine (FinSet.union_c (set_raw s) (set_raw t))
    (FinSet.wf_union E _ _ (proj2_sig s) (proj2_sig t)).

(** Union retains exactly the finite-set operation on the actual valid stored sets. *)
Theorem set_union_cost {K} (E : encoding K) (s t : set_t E) :
  Cost.ticks (set_union_c E s t) =
    Cost.ticks (FinSet.union_c (set_raw s) (set_raw t)).
Proof.
  unfold set_union_c; apply Cost.ticks_refine.
Qed.

Definition set_inter_c {K} (E : encoding K) (s t : set_t E) : Cost.t (set_t E) :=
  Cost.refine (FinSet.inter_c (set_raw s) (set_raw t))
    (FinSet.wf_inter E _ _ (proj2_sig s) (proj2_sig t)).

(** Inclusion enumerates the left set once and retains every membership callback charge. *)
Definition set_leb_c {K} (E : encoding K) (s t : set_t E) :=
  let* keys := FinSet.elements_c (set_raw s) in
  forallb_c (fun k => Cost.step ;; FinSet.mem_c E k (set_raw t)) keys.

(** May facts use inclusion, union widening and left-preserving narrowing. *)
Definition may {K} (E : encoding K) : lattice (set_t E) :=
  {| leb_c := set_leb_c E;
     bot := set_empty E;
     join_c := set_union_c E;
     widen_c := set_union_c E;
     narrow_c := fun s _ => Cost.ret s |}.

(** May comparison is exactly implication between all key observations. *)
Theorem may_leb {K} (E : encoding K) (HE : encoding_laws E) s t :
  leb (may E) s t = true <->
  forall k, FinSet.mem E k (set_raw s) = true -> FinSet.mem E k (set_raw t) = true.
Proof.
  change (Cost.value (set_leb_c E s t) = true <->
    forall k, FinSet.mem E k (set_raw s) = true -> FinSet.mem E k (set_raw t) = true).
  unfold set_leb_c; rewrite Cost.value_bind, value_forallb_c.
  change (forallb (fun k => FinSet.mem E k (set_raw t))
    (FinSet.elements (set_raw s)) = true <->
    forall k, FinSet.mem E k (set_raw s) = true -> FinSet.mem E k (set_raw t) = true).
  rewrite forallb_forall; split; intros H k Hk; apply H.
  - apply (FinSet.elements_spec E HE), Hk; apply (proj2_sig s).
  - apply (FinSet.elements_spec E HE k _ (proj2_sig s)), Hk.
Qed.

(** Boolean membership supplies exact family bottom and operation equations. *)
Theorem may_family {K} (E : encoding K) (HE : encoding_laws E) :
  family (may E) bool_lattice (fun k s => FinSet.mem E k (set_raw s)).
Proof.
  constructor.
  - intros s t; rewrite (may_leb E HE); split; intros H k;
      specialize (H k); destruct (FinSet.mem E k (set_raw s)),
        (FinSet.mem E k (set_raw t)); cbn in *; intuition discriminate.
  - intro k; apply FinSet.mem_empty.
  - intros k s t; change (FinSet.mem E k
      (FinSet.union (set_raw s) (set_raw t)) =
      orb (FinSet.mem E k (set_raw s)) (FinSet.mem E k (set_raw t))).
    apply FinSet.mem_union; [exact (proj2_sig s) | exact (proj2_sig t)].
  - intros k s t; change (FinSet.mem E k
      (FinSet.union (set_raw s) (set_raw t)) =
      orb (FinSet.mem E k (set_raw s)) (FinSet.mem E k (set_raw t))).
    apply FinSet.mem_union; [exact (proj2_sig s) | exact (proj2_sig t)].
  - intros; reflexivity.
Qed.

(** May sets satisfy every weak lattice law under injective key encoding. *)
Theorem may_laws {K} (E : encoding K) : encoding_laws E -> lattice_laws (may E).
Proof.
  intro HE; exact (family_laws (may_family E HE) bool_laws).
Qed.

(** Union is the least upper bound of may facts. *)
Theorem may_lub {K} (E : encoding K) : encoding_laws E -> lub_laws (may E).
Proof.
  intro HE; exact (family_lub (may_family E HE) bool_lub).
Qed.

(** Supported sets have no member outside the supplied universe list. *)
Definition within_set {K} (E : encoding K) (U : list K) (s : set_t E) :=
  forall k, FinSet.mem E k (set_raw s) = true -> In k U.

(** Union and left-preserving narrowing maintain finite support. *)
Theorem within_set_closed {K} (E : encoding K) U :
  closed_on (may E) (within_set E U).
Proof.
  constructor.
  - intros k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
    rewrite FinSet.mem_empty in Hk; discriminate.
  - intros s t Hs Ht k Hk.
    change (FinSet.mem E k (FinSet.union (set_raw s) (set_raw t)) = true) in Hk.
    rewrite FinSet.mem_union in Hk by
      first [exact (proj2_sig s) | exact (proj2_sig t)].
    apply orb_true_iff in Hk; destruct Hk; [apply Hs | apply Ht]; assumption.
  - intros s t Hs Ht k Hk.
    change (FinSet.mem E k (FinSet.union (set_raw s) (set_raw t)) = true) in Hk.
    rewrite FinSet.mem_union in Hk by
      first [exact (proj2_sig s) | exact (proj2_sig t)].
    apply orb_true_iff in Hk; destruct Hk; [apply Hs | apply Ht]; assumption.
  - intros s t Hs _ _; exact Hs.
Qed.

Local Lemma strict_sorted_nodup {K} (f : K -> positive) xs :
  StronglySorted (fun a b => Map.code_compare (f a) (f b) = Lt) xs -> NoDup xs.
Proof.
  intro Hsort.
  induction Hsort as [|k ks Hsort IH Hafter]; constructor; [|exact IH].
  intro Hin; rewrite Forall_forall in Hafter; specialize (Hafter k Hin).
  assert (Heq : Map.code_compare (f k) (f k) = Eq).
  { apply Map.code_compare_eq; reflexivity. }
  congruence.
Qed.

Local Lemma set_elements_nodup {K} (E : encoding K) (s : set_t E) :
  NoDup (FinSet.elements (set_raw s)).
Proof.
  apply (strict_sorted_nodup (encode E)), FinSet.elements_sorted, (proj2_sig s).
Qed.

Local Lemma set_size_le {K} (E : encoding K) (HE : encoding_laws E) s t :
  leb (may E) s t = true -> FinSet.size (set_raw s) <= FinSet.size (set_raw t).
Proof.
  intro Hle; rewrite !FinSet.size_elements.
  apply NoDup_incl_length; [apply set_elements_nodup |].
  intros k Hk; apply (FinSet.elements_spec E HE k _ (proj2_sig t)).
  rewrite (may_leb E HE s t) in Hle; apply Hle.
  apply (FinSet.elements_spec E HE k _ (proj2_sig s)), Hk.
Qed.

Local Lemma set_size_strict {K} (E : encoding K) (HE : encoding_laws E) s t :
  leb (may E) s t = true -> leb (may E) t s = false ->
  FinSet.size (set_raw s) < FinSet.size (set_raw t).
Proof.
  intros Hst Hts.
  assert (Hle := set_size_le E HE s t Hst).
  destruct (Nat.eq_dec (FinSet.size (set_raw s)) (FinSet.size (set_raw t)))
    as [Heq | Hne]; [|lia].
  assert (Hincl : incl (FinSet.elements (set_raw t)) (FinSet.elements (set_raw s))).
  { apply NoDup_length_incl.
    - apply set_elements_nodup.
    - rewrite <- !FinSet.size_elements; lia.
    - intros k Hk; apply (FinSet.elements_spec E HE k _ (proj2_sig t)).
      rewrite (may_leb E HE s t) in Hst; apply Hst.
      apply (FinSet.elements_spec E HE k _ (proj2_sig s)), Hk. }
  assert (Hback : leb (may E) t s = true).
  { apply (may_leb E HE); intros k Hk.
    apply (FinSet.elements_spec E HE k _ (proj2_sig s)), Hincl.
    apply (FinSet.elements_spec E HE k _ (proj2_sig t)), Hk. }
  congruence.
Qed.

(** Cardinality bounds supported sets by the arbitrary universe list length. *)
Theorem within_set_size {K} (E : encoding K) (HE : encoding_laws E) U s :
  within_set E U s -> FinSet.size (set_raw s) <= length U.
Proof.
  intro Hs; rewrite FinSet.size_elements; apply NoDup_incl_length.
  - apply set_elements_nodup.
  - intros k Hk; apply Hs, (FinSet.elements_spec E HE k _ (proj2_sig s)), Hk.
Qed.

(** Cardinality grows at every strict supported may join. *)
Theorem may_height {K} (E : encoding K) (HE : encoding_laws E) U :
  height_on (may E) (within_set E U).
Proof.
  refine {| rank := fun s => FinSet.size (set_raw s);
            bound := length U |}.
  - apply within_set_size, HE.
  - intros s t _ _; apply set_size_le, HE.
  - intros s t _ _ Hstrict; apply (set_size_strict E HE); [|exact Hstrict].
    apply (join_upper_l (may_laws E HE)).
Defined.

(** May widening credits complement the supported cardinality height. *)
Theorem may_wrank {K} (E : encoding K) (HE : encoding_laws E) U :
  widening_rank_on (may E) (within_set E U).
Proof.
  exact (height_wrank (may E) (may_laws E HE) (may_lub E HE)
    (within_set_closed E U) (fun _ _ => eq_refl) (may_height E HE U)).
Defined.

Definition may_gamma {K} (E : encoding K) : concretisation (set_t E) K :=
  {| gamma := fun s k => FinSet.mem E k (set_raw s) = true |}.

Definition may_agree {K C} (E : encoding K) : agreement (set_t E) (K -> C) :=
  {| agree := fun s x y => forall k, FinSet.mem E k (set_raw s) = true -> x k = y k |}.

(** May membership is monotone in inclusion. *)
Theorem may_gamma_laws {K} (E : encoding K) (HE : encoding_laws E) :
  concretisation_laws (may E) (may_gamma E).
Proof.
  constructor; intros s t k Hst Hk.
  rewrite (may_leb E HE s t) in Hst; apply Hst, Hk.
Qed.

(** Empty may facts have empty meaning. *)
Theorem may_bot_empty {K} (E : encoding K) : bottom_empty (may E) (may_gamma E).
Proof.
  constructor; intros k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
  rewrite FinSet.mem_empty in Hk; discriminate.
Qed.

(** May needs give reflexive antitone indexed store agreement. *)
Theorem may_agree_laws {K C} (E : encoding K) (HE : encoding_laws E) :
  agreement_laws (may E) (@may_agree K C E).
Proof.
  constructor.
  - intros s x k _; reflexivity.
  - intros s t x y Hst Hxy k Hk; apply Hxy.
    rewrite (may_leb E HE s t) in Hst; apply Hst, Hk.
Qed.

(** May agreement on both inputs suffices at their union. *)
Theorem may_agree_join {K C} (E : encoding K) :
  agreement_join_law (may E) (@may_agree K C E).
Proof.
  constructor; intros s t x y Hs Ht k Hk.
  change (FinSet.mem E k (FinSet.union (set_raw s) (set_raw t)) = true) in Hk.
  rewrite FinSet.mem_union in Hk by
    first [exact (proj2_sig s) | exact (proj2_sig t)].
  apply orb_true_iff in Hk; destruct Hk; [apply Hs | apply Ht]; assumption.
Qed.

(** Empty may needs relate every pair of assignments. *)
Theorem may_agree_bot {K C} (E : encoding K) :
  agreement_bot (may E) (@may_agree K C E).
Proof.
  constructor; intros x y k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
  rewrite FinSet.mem_empty in Hk; discriminate.
Qed.

(** Equality on selected coordinates is symmetric and transitive. *)
Theorem may_agree_equivalence {K C} (E : encoding K) :
  agreement_equivalence (@may_agree K C E).
Proof.
  constructor.
  - intros s x y Hxy k Hk; symmetry; apply Hxy, Hk.
  - intros s x y z Hxy Hyz k Hk; transitivity (y k); [apply Hxy | apply Hyz]; exact Hk.
Qed.

(** Public list construction supplies finite support under injective key encoding. *)
Theorem set_of_list_within {K} (E : encoding K) (HE : encoding_laws E) U :
  within_set E U (set_of_list E U).
Proof.
  intros k Hk; change (FinSet.mem E k (FinSet.of_list E U) = true) in Hk.
  rewrite FinSet.mem_of_list in Hk; apply existsb_exists in Hk as [j [Hj Heq]].
  apply (BaseEq.eqb_true_iff E HE) in Heq; subst j; exact Hj.
Qed.

(** A finite list covering the whole key type supplies a representable may top. *)
Theorem may_top {K} (E : encoding K) (HE : encoding_laws E) (U : list K)
    (cover : forall k, In k U) : top (may E).
Proof.
  refine {| top_value := set_of_list E U |}; intro s; apply (may_leb E HE).
  intros k _; change (FinSet.mem E k (FinSet.of_list E U) = true).
  rewrite FinSet.mem_of_list; apply existsb_exists; exists k; split.
  - apply cover.
  - apply BaseEq.eqb_refl.
Defined.

(** A covering finite may top denotes every key. *)
Theorem may_top_full {K} (E : encoding K) (HE : encoding_laws E) U cover :
  top_full (may_top E HE U cover) (may_gamma E).
Proof.
  constructor; intro k; change (FinSet.mem E k (FinSet.of_list E U) = true).
  rewrite FinSet.mem_of_list; apply existsb_exists; exists k; split.
  - apply cover.
  - apply BaseEq.eqb_refl.
Qed.

(** Must facts distinguish unreachable All from every finite conjunction. *)
Inductive must_t {K} (E : encoding K) :=
  | All
  | Only (s : set_t E).

Arguments All {K E}.
Arguments Only {K E}.

Definition must_join_c {K} (E : encoding K) (s t : must_t E) :=
  match s, t with
  | All, _ => Cost.ret t
  | _, All => Cost.ret s
  | Only a, Only b => Cost.step ;; Cost.map Only (set_inter_c E a b)
  end.

(** Must order reverses finite inclusion and keeps the unreachable bottom distinct. *)
Definition must {K} (E : encoding K) : lattice (must_t E) :=
  {| leb_c := fun s t => Cost.step ;;
       match s, t with
       | All, _ => Cost.ret true
       | Only _, All => Cost.ret false
       | Only a, Only b => Cost.step ;; set_leb_c E b a
       end;
     bot := All;
     join_c := must_join_c E;
     widen_c := must_join_c E;
     narrow_c := fun s _ => Cost.ret s |}.

Local Lemma must_le {K} (E : encoding K) s t :
  leb (must E) s t =
  match s, t with
  | All, _ => true
  | Only _, All => false
  | Only a, Only b => leb (may E) b a
  end.
Proof.
  destruct s, t; reflexivity.
Qed.

(** Must comparison exposes fresh All and reverses inclusion between finite facts. *)
Theorem must_leb_equation {K} (E : encoding K) s t :
  leb (must E) s t =
  match s, t with
  | All, _ => true
  | Only _, All => false
  | Only a, Only b => leb (may E) b a
  end.
Proof.
  apply must_le.
Qed.

Local Lemma must_join {K} (E : encoding K) s t :
  join (must E) s t =
  match s, t with
  | All, _ => t
  | _, All => s
  | Only a, Only b => Only (Cost.value (set_inter_c E a b))
  end.
Proof.
  destruct s, t; reflexivity.
Qed.

Local Lemma inter_le {K} (E : encoding K) (HE : encoding_laws E) s t :
  leb (may E) (Cost.value (set_inter_c E s t)) s = true /\
  leb (may E) (Cost.value (set_inter_c E s t)) t = true.
Proof.
  split; apply (may_leb E HE); intros k Hk;
    change (FinSet.mem E k (FinSet.inter (set_raw s) (set_raw t)) = true) in Hk;
    rewrite FinSet.mem_inter in Hk by
      first [exact (proj2_sig s) | exact (proj2_sig t)];
    apply andb_true_iff in Hk; tauto.
Qed.

(** Reverse inclusion with a distinct unreachable value satisfies the weak laws. *)
Theorem must_laws {K} (E : encoding K) (HE : encoding_laws E) :
  lattice_laws (must E).
Proof.
  constructor.
  - intros [|s]; rewrite must_le; [reflexivity | apply (leb_refl (may_laws E HE))].
  - intros [|s] [|t] [|u]; rewrite !must_le; intros Hst Htu;
      try discriminate; try reflexivity; eapply (leb_trans (may_laws E HE)); eassumption.
  - intros [|s]; reflexivity.
  - intros [|s] [|t]; rewrite must_join, must_le; try reflexivity;
      [apply (leb_refl (may_laws E HE)) | apply (proj1 (inter_le E HE s t))].
  - intros [|s] [|t]; rewrite must_join, must_le; try reflexivity;
      [apply (leb_refl (may_laws E HE)) | apply (proj2 (inter_le E HE s t))].
  - change (forall s t, leb (must E) s (join (must E) s t) = true).
    intros [|s] [|t]; rewrite must_join, must_le; try reflexivity;
      [apply (leb_refl (may_laws E HE)) | apply (proj1 (inter_le E HE s t))].
  - change (forall s t, leb (must E) t (join (must E) s t) = true).
    intros [|s] [|t]; rewrite must_join, must_le; try reflexivity;
      [apply (leb_refl (may_laws E HE)) | apply (proj2 (inter_le E HE s t))].
  - intros s t _; change (leb (must E) s s = true).
    destruct s as [|s]; rewrite must_le;
      [reflexivity | apply (leb_refl (may_laws E HE))].
  - intros s t Hts; exact Hts.
Qed.

(** Intersection is the least upper bound in reverse inclusion. *)
Theorem must_lub {K} (E : encoding K) (HE : encoding_laws E) : lub_laws (must E).
Proof.
  constructor; intros [|s] [|t] [|u]; rewrite must_join, !must_le;
    intros Hsu Htu; try discriminate; try reflexivity; try assumption.
  apply (may_leb E HE); intros k Hk.
  change (FinSet.mem E k (FinSet.inter (set_raw s) (set_raw t)) = true).
  rewrite FinSet.mem_inter by first [exact (proj2_sig s) | exact (proj2_sig t)].
  rewrite andb_true_iff; split.
  - exact (proj1 (may_leb E HE u s) Hsu k Hk).
  - exact (proj1 (may_leb E HE u t) Htu k Hk).
Qed.

(** The empty conjunction is the greatest must fact. *)
Theorem must_top {K} (E : encoding K) (HE : encoding_laws E) : top (must E).
Proof.
  refine {| top_value := Only (set_empty E) |}; intros [|s]; rewrite must_le;
    [reflexivity | apply (bot_least (may_laws E HE))].
Defined.

(** Must support includes unreachable All and supported finite conjunctions. *)
Definition within_must {K} (E : encoding K) U (s : must_t E) :=
  match s with
  | All => True
  | Only s => within_set E U s
  end.

(** Intersection and left-preserving narrowing keep must facts within their universe. *)
Theorem within_must_closed {K} (E : encoding K) U :
  closed_on (must E) (within_must E U).
Proof.
  constructor; [exact I | | |].
  - intros [|s] [|t] Hs Ht; rewrite must_join; try assumption.
    intros k Hk; apply Hs.
    change (FinSet.mem E k (FinSet.inter (set_raw s) (set_raw t)) = true) in Hk.
    rewrite FinSet.mem_inter in Hk by
      first [exact (proj2_sig s) | exact (proj2_sig t)].
    apply andb_true_iff in Hk; tauto.
  - change (forall s t, within_must E U s -> within_must E U t ->
      within_must E U (join (must E) s t)).
    intros [|s] [|t] Hs Ht; rewrite must_join; try assumption.
    intros k Hk; apply Hs.
    change (FinSet.mem E k (FinSet.inter (set_raw s) (set_raw t)) = true) in Hk.
    rewrite FinSet.mem_inter in Hk by
      first [exact (proj2_sig s) | exact (proj2_sig t)].
    apply andb_true_iff in Hk; tauto.
  - intros s t Hs _ _; exact Hs.
Qed.

(** Must height includes the extra strict step from All to a reached conjunction. *)
Theorem must_height {K} (E : encoding K) (HE : encoding_laws E) U :
  height_on (must E) (within_must E U).
Proof.
  refine {| rank := fun s =>
              match s with
              | All => 0
              | Only s => S (length U - FinSet.size (set_raw s))
              end;
            bound := S (length U) |}.
  - intros [|s] Hs; cbn; lia.
  - intros [|s] [|t] Hs Ht Hle; rewrite must_le in Hle; cbn;
      try discriminate; try lia.
    pose proof (set_size_le E HE t s Hle); lia.
  - intros [|s] [|t] Hs Ht Hstrict; rewrite must_join, must_le in Hstrict;
      cbn; try discriminate; try lia.
    + rewrite (leb_refl (may_laws E HE)) in Hstrict; discriminate.
    + change (S (length U - FinSet.size (set_raw s)) <
        S (length U - FinSet.size (set_raw (Cost.value (set_inter_c E s t))))).
      pose proof (set_size_strict E HE _ _ (proj1 (inter_le E HE s t)) Hstrict).
      pose proof (within_set_size E HE U s Hs); lia.
Defined.

(** Must widening credits complement its reached-conjunction height. *)
Theorem must_wrank {K} (E : encoding K) (HE : encoding_laws E) U :
  widening_rank_on (must E) (within_must E U).
Proof.
  exact (height_wrank (must E) (must_laws E HE) (must_lub E HE)
    (within_must_closed E U) (fun _ _ => eq_refl) (must_height E HE U)).
Defined.

(** Finite must meaning requires each stored fact and makes All unreachable. *)
Definition must_gamma {K C} (E : encoding K) (holds : K -> C -> Prop) :
    concretisation (must_t E) C :=
  {| gamma := fun s c =>
       match s with
       | All => False
       | Only s => forall k, FinSet.mem E k (set_raw s) = true -> holds k c
       end |}.

(** Removing required facts enlarges must meaning. *)
Theorem must_gamma_laws {K C} (E : encoding K) (HE : encoding_laws E) holds :
  concretisation_laws (must E) (@must_gamma K C E holds).
Proof.
  constructor; intros [|s] [|t] c Hle Hc; rewrite must_le in Hle;
    cbn [must_gamma gamma] in *; try contradiction; try discriminate.
  intros k Hk; apply Hc; exact (proj1 (may_leb E HE t s) Hle k Hk).
Qed.

(** The fresh must bottom has empty meaning independently of the key universe. *)
Theorem must_bot_empty {K C} (E : encoding K) holds :
  bottom_empty (must E) (@must_gamma K C E holds).
Proof.
  constructor; intros c Hc; exact Hc.
Qed.

(** The empty conjunction denotes every concrete value. *)
Theorem must_top_full {K C} (E : encoding K) (HE : encoding_laws E) holds :
  top_full (must_top E HE) (@must_gamma K C E holds).
Proof.
  constructor; intros c k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
  rewrite FinSet.mem_empty in Hk; discriminate.
Qed.

(** Reverse-set agreement demands equality outside the stored facts and nothing at All. *)
Definition must_agree {K C} (E : encoding K) : agreement (must_t E) (K -> C) :=
  {| agree := fun s x y =>
       match s with
       | All => True
       | Only s => forall k, FinSet.mem E k (set_raw s) = false -> x k = y k
       end |}.

(** Complement needs are reflexive and antitone in reverse inclusion. *)
Theorem must_agree_laws {K C} (E : encoding K) (HE : encoding_laws E) :
  agreement_laws (must E) (@must_agree K C E).
Proof.
  constructor.
  - intros [|s] x; cbn [must_agree agree]; auto.
  - intros [|s] [|t] x y Hle Hxy; rewrite must_le in Hle;
      cbn [must_agree agree] in *; try exact I; try discriminate.
    intros k Hk; apply Hxy.
    destruct (FinSet.mem E k (set_raw t)) eqn:Ht; [|reflexivity].
    pose proof (proj1 (may_leb E HE t s) Hle k Ht); congruence.
Qed.

(** Unreachable must bottom imposes no agreement condition. *)
Theorem must_agree_bot {K C} (E : encoding K) :
  agreement_bot (must E) (@must_agree K C E).
Proof.
  constructor; intros; exact I.
Qed.

(** Agreement outside both fact sets suffices outside their intersection. *)
Theorem must_agree_join {K C} (E : encoding K) :
  agreement_join_law (must E) (@must_agree K C E).
Proof.
  constructor; intros [|s] [|t] x y Hs Ht; rewrite must_join;
    cbn [must_agree agree] in *; try assumption.
  intros k Hk.
  change (FinSet.mem E k (FinSet.inter (set_raw s) (set_raw t)) = false) in Hk.
  rewrite FinSet.mem_inter in Hk by
    first [exact (proj2_sig s) | exact (proj2_sig t)].
  destruct (FinSet.mem E k (set_raw s)) eqn:Ha.
  - apply Ht; exact Hk.
  - apply Hs, Ha.
Qed.

(** Equality outside a fact set is symmetric and transitive, including All. *)
Theorem must_agree_equivalence {K C} (E : encoding K) :
  agreement_equivalence (@must_agree K C E).
Proof.
  constructor.
  - intros [|s] x y Hxy; [exact I |]; intros k Hk; symmetry; apply Hxy, Hk.
  - intros [|s] x y z Hxy Hyz; [exact I |]; intros k Hk.
    transitivity (y k); [apply Hxy | apply Hyz]; exact Hk.
Qed.

(** Raw list construction retains precisely the public set construction result. *)
Theorem set_of_list_raw {K} (E : encoding K) xs :
  set_raw (set_of_list E xs) = FinSet.of_list E xs.
Proof.
  reflexivity.
Qed.

(** Valid insertion retains precisely the public raw insertion result. *)
Theorem set_add_raw {K} (E : encoding K) k s :
  set_raw (set_add E k s) = FinSet.add E k (set_raw s).
Proof.
  reflexivity.
Qed.

(** Valid union retains precisely the public raw union result. *)
Theorem set_union_raw {K} (E : encoding K) a b :
  set_raw (Cost.value (set_union_c E a b)) = FinSet.union (set_raw a) (set_raw b).
Proof.
  reflexivity.
Qed.

(** Inclusion cost retains enumeration charges and each charged membership callback. *)
Theorem set_leb_cost {K} (E : encoding K) s t m :
  (forall k, (Cost.ticks (FinSet.mem_c E k (set_raw t)) <= m)%N) ->
  (Cost.ticks (set_leb_c E s t) <=
    Cost.ticks (FinSet.elements_c (set_raw s)) +
    N.of_nat (FinSet.size (set_raw s)) * (m + 2))%N.
Proof.
  intro Hmem; unfold set_leb_c; rewrite Cost.ticks_bind.
  pose proof (ticks_forallb_c_le
    (fun k => Cost.step ;; FinSet.mem_c E k (set_raw t)) (m + 1)%N
    (FinSet.elements (set_raw s))) as Hcost.
  assert (Hcallback : forall k,
    (Cost.ticks (Cost.step ;; FinSet.mem_c E k (set_raw t)) <= m + 1)%N).
  { intro k; cost_simpl; specialize (Hmem k); lia. }
  specialize (Hcost Hcallback).
  change (Cost.ticks (FinSet.elements_c (set_raw s)) +
    Cost.ticks (forallb_c (fun k => Cost.step ;; FinSet.mem_c E k (set_raw t))
      (FinSet.elements (set_raw s))) <=
    Cost.ticks (FinSet.elements_c (set_raw s)) +
    N.of_nat (FinSet.size (set_raw s)) * (m + 2))%N.
  rewrite FinSet.size_elements; nia.
Qed.
