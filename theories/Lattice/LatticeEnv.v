(** * Sparse environments with explicit defaults

    Valid maps use bottom or top at absent keys and top-default maps add fresh bottom.
    For example, joining top-default maps drops a binding present on just one side.
    Builds on: BaseMap, LatticeKitFamily and LatticeAdjoin. *)

From Stdlib Require Import Bool List Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostTactics.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit
  LatticeKitFamily LatticeAdjoin.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

(** Policies distinguish absent-bottom maps from absent-top reached maps. *)
Inductive default_policy :=
  | Bottom_default
  | Top_default.

(** Valid environments carry representation certificates without component laws. *)
Definition env_map {K} (E : encoding K) A := {m : Map.t K A | Map.wf E m}.

Definition env_raw {K A} {E : encoding K} (m : env_map E A) := proj1_sig m.

Definition env_empty {K A} (E : encoding K) : env_map E A :=
  exist _ Map.empty (Map.wf_empty E).

Definition env_of_list_c {K A} (E : encoding K) xs : Cost.t (env_map E A) :=
  Cost.refine (Map.of_list_c E xs) (Map.wf_of_list E xs).

Definition env_of_list {K A} (E : encoding K) xs : env_map E A :=
  Cost.value (env_of_list_c E xs).

Definition env_update_c {K A} (E : encoding K) k v (m : env_map E A) :=
  Cost.refine (Map.set_c E k v (env_raw m)) (Map.wf_set E k v _ (proj2_sig m)).

Definition env_update {K A} (E : encoding K) k v m : env_map E A :=
  Cost.value (env_update_c E k v m).

Definition env_default {A} (d : A) (a : option A) :=
  match a with
  | Some a => a
  | None => d
  end.

(** Default order identifies the least or greatest value needed by sparse comparison. *)
Definition env_default_order {A} pol d (L : lattice A) :=
  match pol with
  | Bottom_default => forall a, leb L d a = true
  | Top_default => forall a, leb L a d = true
  end.

(** Operator tags share optional-binding handling without erasing callback charges. *)
Inductive env_op :=
  | Env_join
  | Env_widen
  | Env_narrow.

Definition env_callback {A} (L : lattice A) op :=
  match op with
  | Env_join => join_c L
  | Env_widen => widen_c L
  | Env_narrow => narrow_c L
  end.

(** Optional operations retain the legacy one-sided choices for each default policy. *)
Definition env_optional_c {A} pol (d : A) (L : lattice A) op (a b : option A) :=
  match a, b with
  | Some a, Some b => Cost.step ;; Cost.map Some (env_callback L op a b)
  | None, None => Cost.ret None
  | Some a, None =>
    match pol, op with
    | Top_default, Env_join => Cost.ret None
    | Top_default, Env_widen => Cost.ret None
    | _, _ => Cost.ret (Some a)
    end
  | None, Some b =>
    match pol, op with
    | Bottom_default, Env_join => Cost.ret (Some b)
    | Bottom_default, Env_widen => Cost.step ;; Cost.map Some (widen_c L d b)
    | Bottom_default, Env_narrow => Cost.ret None
    | Top_default, Env_narrow => Cost.ret (Some b)
    | _, _ => Cost.ret None
    end
  end.

Definition env_optional {A} pol (d : A) L op a b :=
  Cost.value (env_optional_c pol d L op a b).

(** The raw core computes without representation, semantic or termination proofs. *)
Definition env_core {K A} pol (d : A) (L : lattice A) : lattice (Map.t K A) :=
  {| leb_c := fun a b =>
       match pol with
       | Bottom_default => Map.forall2_c
           (fun a b => Cost.step ;; leb_c L a (env_default d b)) a b
       | Top_default => Map.forall2_c
           (fun b a => Cost.step ;; leb_c L (env_default d a) b) b a
       end;
     bot := Map.empty;
     join_c := Map.combine_c (env_optional_c pol d L Env_join);
     widen_c := Map.combine_c (env_optional_c pol d L Env_widen);
     narrow_c := Map.combine_c (env_optional_c pol d L Env_narrow) |}.

Definition env_read {K A} (E : encoding K) d k (m : env_map E A) :=
  Map.find_or E d k (env_raw m).

(** Literal default compatibility is separate from weak order and least-join laws. *)
Record env_default_laws {A} pol (d : A) (L : lattice A) : Prop := {
  env_optional_exact : forall op a b,
    env_default d (env_optional pol d L op a b) =
    Cost.value (env_callback L op (env_default d a) (env_default d b))
}.

Arguments env_optional_exact {A pol d L}.

Local Lemma env_combine_value {K A} pol d (L : lattice A) op (a b : Map.t K A) :
  Cost.value (Map.combine_c (env_optional_c pol d L op) a b) =
  Map.combine (env_optional pol d L op) a b.
Proof.
  apply Map.combine_c_value.
Qed.

Local Lemma env_combine_wf {K A} (E : encoding K) pol d L op
    (a b : Map.t K A) :
  Map.wf E a -> Map.wf E b ->
  Map.wf E (Cost.value (Map.combine_c (env_optional_c pol d L op) a b)).
Proof.
  intros Ha Hb; rewrite env_combine_value; apply Map.wf_combine; assumption.
Qed.

Definition env_merge_c {K A} (E : encoding K) pol d L op
    (a b : env_map E A) : Cost.t (env_map E A) :=
  Cost.refine (Map.combine_c (env_optional_c pol d L op) (env_raw a) (env_raw b))
    (env_combine_wf E pol d L op _ _ (proj2_sig a) (proj2_sig b)).

(** The valid core refines raw operations without a narrowing guard or lost charges. *)
Definition env_valid_core {K A} (E : encoding K) pol d (L : lattice A) :
    lattice (env_map E A) :=
  {| leb_c := fun a b => leb_c (env_core pol d L) (env_raw a) (env_raw b);
     bot := env_empty E;
     join_c := env_merge_c E pol d L Env_join;
     widen_c := env_merge_c E pol d L Env_widen;
     narrow_c := env_merge_c E pol d L Env_narrow |}.

(** Core comparison reflects all key reads under the appropriate least or greatest default. *)
Theorem env_core_leb {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (Hdefault : match pol with
      | Bottom_default => forall a, leb L d a = true
      | Top_default => forall a, leb L a d = true
      end) (a b : env_map E A) :
  leb (env_valid_core E pol d L) a b = true <->
  forall k, leb L (env_read E d k a) (env_read E d k b) = true.
Proof.
  unfold env_read; rewrite ?Map.find_or_equation.
  destruct pol.
  - change (Cost.value (Map.forall2_c
      (fun a b => Cost.step ;; leb_c L a (env_default d b))
      (env_raw a) (env_raw b)) = true <->
      forall k, leb L (env_default d (Map.get E k (env_raw a)))
        (env_default d (Map.get E k (env_raw b))) = true).
    rewrite Map.forall2_c_value, (Map.forall2_spec E HE) by exact (proj2_sig a).
    split.
    + intros H k; specialize (H k); destruct (Map.get E k (env_raw a)) eqn:Ha.
      * exact (H _ eq_refl).
      * apply Hdefault.
    + intros H k v Ha; specialize (H k); rewrite Ha in H; exact H.
  - change (Cost.value (Map.forall2_c
      (fun b a => Cost.step ;; leb_c L (env_default d a) b)
      (env_raw b) (env_raw a)) = true <->
      forall k, leb L (env_default d (Map.get E k (env_raw a)))
        (env_default d (Map.get E k (env_raw b))) = true).
    rewrite Map.forall2_c_value, (Map.forall2_spec E HE) by exact (proj2_sig b).
    split.
    + intros H k; specialize (H k); destruct (Map.get E k (env_raw b)) eqn:Hb.
      * exact (H _ eq_refl).
      * apply Hdefault.
    + intros H k v Hb; specialize (H k); rewrite Hb in H; exact H.
Qed.

(** Every valid merged read equals its component operation under literal compatibility. *)
Theorem env_merge_read {K A} (E : encoding K) pol d L
    (D : env_default_laws pol d L) op k (a b : env_map E A) :
  env_read E d k (Cost.value (env_merge_c E pol d L op a b)) =
  Cost.value (env_callback L op (env_read E d k a) (env_read E d k b)).
Proof.
  unfold env_read; rewrite !Map.find_or_equation.
  change (env_default d (Map.get E k
    (Cost.value (Map.combine_c (env_optional_c pol d L op) (env_raw a) (env_raw b)))) =
    Cost.value (env_callback L op
      (env_default d (Map.get E k (env_raw a)))
      (env_default d (Map.get E k (env_raw b))))).
  rewrite env_combine_value, Map.get_combine by
    first [exact (proj2_sig a) | exact (proj2_sig b) | reflexivity].
  apply (env_optional_exact D).
Qed.

(** Raw optional observations hold independently of literal component-default identities. *)
Theorem env_merge_observe {K A} (E : encoding K) pol d L op k (a b : env_map E A) :
  env_read E d k (Cost.value (env_merge_c E pol d L op a b)) =
  env_default d (env_optional pol d L op
    (Map.get E k (env_raw a)) (Map.get E k (env_raw b))).
Proof.
  unfold env_read; rewrite Map.find_or_equation.
  change (env_default d (Map.get E k
    (Cost.value (Map.combine_c (env_optional_c pol d L op) (env_raw a) (env_raw b)))) =
    env_default d (env_optional pol d L op
      (Map.get E k (env_raw a)) (Map.get E k (env_raw b)))).
  rewrite env_combine_value, Map.get_combine by
    first [exact (proj2_sig a) | exact (proj2_sig b) | reflexivity].
  reflexivity.
Qed.

Local Lemma env_optional_bounds {A} pol d (L : lattice A)
    (H : lattice_laws L) (Hd : env_default_order pol d L) op a b :
  let x := env_default d a in let y := env_default d b in
  let z := env_default d (env_optional pol d L op a b) in
  match op with
  | Env_join | Env_widen => leb L x z = true /\ leb L y z = true
  | Env_narrow => leb L y x = true -> leb L z x = true /\ leb L y z = true
  end.
Proof.
  destruct H as [Hr Ht Hb Hj1 Hj2 Hw1 Hw2 Hn1 Hn2].
  clear Ht Hb.
  destruct pol, op, a as [a|], b as [b|];
    unfold env_default_order in Hd;
    unfold env_optional, env_optional_c, env_callback;
    autorewrite with galois_cost; cbn [env_default];
    intros; split; eauto 2.
Qed.

Local Lemma env_core_bounds {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (H : lattice_laws L) (Hd : env_default_order pol d L) op (a b : env_map E A) :
  let P := env_valid_core E pol d L in
  let z := Cost.value (env_merge_c E pol d L op a b) in
  match op with
  | Env_join | Env_widen => leb P a z = true /\ leb P b z = true
  | Env_narrow => leb P b a = true -> leb P z a = true /\ leb P b z = true
  end.
Proof.
  destruct op; cbn zeta.
  - split; apply (env_core_leb E HE pol d L Hd); intro k;
      rewrite env_merge_observe;
      first [exact (proj1 (env_optional_bounds pol d L H Hd Env_join
        (Map.get E k (env_raw a)) (Map.get E k (env_raw b)))) |
        exact (proj2 (env_optional_bounds pol d L H Hd Env_join
        (Map.get E k (env_raw a)) (Map.get E k (env_raw b))))].
  - split; apply (env_core_leb E HE pol d L Hd); intro k;
      rewrite env_merge_observe;
      first [exact (proj1 (env_optional_bounds pol d L H Hd Env_widen
        (Map.get E k (env_raw a)) (Map.get E k (env_raw b)))) |
        exact (proj2 (env_optional_bounds pol d L H Hd Env_widen
        (Map.get E k (env_raw a)) (Map.get E k (env_raw b))))].
  - intro Hba; split; apply (env_core_leb E HE pol d L Hd); intro k;
      rewrite env_merge_observe;
      pose proof (env_optional_bounds pol d L H Hd Env_narrow
        (Map.get E k (env_raw a)) (Map.get E k (env_raw b))
        (proj1 (env_core_leb E HE pol d L Hd b a) Hba k)) as Hz;
      first [exact (proj1 Hz) | exact (proj2 Hz)].
Qed.

(** Exact join observations require the separately stated literal default contract. *)
Theorem env_join_read {K A} (E : encoding K) pol d L
    (D : env_default_laws pol d L) k (a b : env_map E A) :
  env_read E d k (join (env_valid_core E pol d L) a b) =
  join L (env_read E d k a) (env_read E d k b).
Proof.
  exact (env_merge_read E pol d L D Env_join k a b).
Qed.

(** Exact widening observations require the separately stated literal default contract. *)
Theorem env_widen_read {K A} (E : encoding K) pol d L
    (D : env_default_laws pol d L) k (a b : env_map E A) :
  env_read E d k (widen (env_valid_core E pol d L) a b) =
  widen L (env_read E d k a) (env_read E d k b).
Proof.
  exact (env_merge_read E pol d L D Env_widen k a b).
Qed.

(** Exact narrowing observations require the separately stated literal default contract. *)
Theorem env_narrow_read {K A} (E : encoding K) pol d L
    (D : env_default_laws pol d L) k (a b : env_map E A) :
  env_read E d k (narrow (env_valid_core E pol d L) a b) =
  narrow L (env_read E d k a) (env_read E d k b).
Proof.
  exact (env_merge_read E pol d L D Env_narrow k a b).
Qed.

(** Bottom-default valid maps form an exact family when their literal defaults commute. *)
Theorem env_core_family {K A} (E : encoding K) (HE : encoding_laws E) (L : lattice A)
    (H : lattice_laws L) (D : env_default_laws Bottom_default (bot L) L) :
  family (env_valid_core E Bottom_default (bot L) L) L
    (fun k m => env_read E (bot L) k m).
Proof.
  constructor.
  - exact (env_core_leb E HE Bottom_default (bot L) L (bot_least H)).
  - intro k; change (Map.find_or E (bot L) k (@Map.empty K A) = bot L).
    rewrite Map.find_or_equation, Map.get_empty; reflexivity.
  - intros k a b; exact (env_merge_read E _ _ L D Env_join k a b).
  - intros k a b; exact (env_merge_read E _ _ L D Env_widen k a b).
  - intros k a b; exact (env_merge_read E _ _ L D Env_narrow k a b).
Qed.

(** The policy carrier adds a fresh unreachable value only for top default. *)
Definition env_carrier {K} pol (E : encoding K) A :=
  match pol with
  | Bottom_default => env_map E A
  | Top_default => option (env_map E A)
  end.

Definition env {K A} pol (E : encoding K) (L : lattice A) (T : top L) :
    lattice (env_carrier pol E A) :=
  match pol with
  | Bottom_default => env_valid_core E Bottom_default (bot L) L
  | Top_default => lift_bot (env_valid_core E Top_default (top_value T) L)
  end.

Definition policy_default {A} pol (L : lattice A) (T : top L) :=
  match pol with
  | Bottom_default => bot L
  | Top_default => top_value T
  end.

Definition env_component_carrier pol A :=
  match pol with
  | Bottom_default => A
  | Top_default => option A
  end.

Definition env_component {A} pol (L : lattice A) :
    lattice (env_component_carrier pol A) :=
  match pol with
  | Bottom_default => L
  | Top_default => lift_bot L
  end.

(** A top-default read retains None so fresh bottom cannot be confused with a missing key. *)
Definition env_get {K A} pol (E : encoding K) (L : lattice A) (T : top L) k :
    env_carrier pol E A -> env_component_carrier pol A :=
  match pol with
  | Bottom_default => env_read E (bot L) k
  | Top_default => fun m => option_map (env_read E (top_value T) k) m
  end.

(** Inhabited keys make top-default option observations reflect fresh-bottom comparisons. *)
Theorem env_top_family {K A} (E : encoding K) (HE : encoding_laws E) (key : K)
    (L : lattice A) (T : top L)
    (D : env_default_laws Top_default (top_value T) L) :
  family (env Top_default E L T) (lift_bot L) (env_get Top_default E L T).
Proof.
  change (family (lift_bot (env_valid_core E Top_default (top_value T) L))
    (lift_bot L) (env_get Top_default E L T)).
  constructor.
  - intros [a|] [b|]; rewrite leb_lift_bot; cbn [env_get option_map].
    + rewrite (env_core_leb E HE Top_default _ L (top_greatest T)).
      split; intros H k; specialize (H k); rewrite ?leb_lift_bot in *; exact H.
    + split; [discriminate |].
      intro H; specialize (H key); rewrite leb_lift_bot in H; discriminate.
    + split; [intros _ k; rewrite leb_lift_bot; reflexivity | intros _; reflexivity].
    + split; [intros _ k; rewrite leb_lift_bot; reflexivity | intros _; reflexivity].
  - intro k; reflexivity.
  - intros k [a|] [b|]; rewrite join_lift_bot; cbn [env_get option_map];
      rewrite join_lift_bot; try reflexivity.
    f_equal; exact (env_merge_read E _ _ L D Env_join k a b).
  - intros k [a|] [b|]; rewrite widen_lift_bot; cbn [env_get option_map];
      rewrite widen_lift_bot; try reflexivity.
    f_equal; exact (env_merge_read E _ _ L D Env_widen k a b).
  - intros k [a|] [b|]; rewrite narrow_lift_bot; cbn [env_get option_map];
      rewrite narrow_lift_bot; try reflexivity.
    f_equal; exact (env_merge_read E _ _ L D Env_narrow k a b).
Qed.

(** This normalization exposes option cases without inspecting map representations. *)
Local Ltac env_lift_reduce :=
  repeat first [rewrite leb_lift_bot | rewrite join_lift_bot |
    rewrite widen_lift_bot | rewrite narrow_lift_bot]; cbn beta iota.

(** Fresh-bottom weak laws use core bounds without requiring a core bottom. *)
Local Theorem env_lift_weak {B} (P : lattice B)
    (Hr : forall a, leb P a a = true)
    (Ht : forall a b c, leb P a b = true -> leb P b c = true -> leb P a c = true)
    (Hj : forall a b, leb P a (join P a b) = true /\ leb P b (join P a b) = true)
    (Hw : forall a b, leb P a (widen P a b) = true /\ leb P b (widen P a b) = true)
    (Hn : forall a b, leb P b a = true ->
      leb P (narrow P a b) a = true /\ leb P b (narrow P a b) = true) :
  lattice_laws (lift_bot P).
Proof.
  constructor.
  - intros [a|]; env_lift_reduce; auto.
  - intros [a|] [b|] [c|]; env_lift_reduce; intros Hab Hbc;
      try discriminate; try reflexivity; eauto.
  - intros [a|]; reflexivity.
  - intros [a|] [b|]; env_lift_reduce; try reflexivity; auto; apply (proj1 (Hj a b)).
  - intros [a|] [b|]; env_lift_reduce; try reflexivity; auto; apply (proj2 (Hj a b)).
  - intros [a|] [b|]; env_lift_reduce; try reflexivity; auto; apply (proj1 (Hw a b)).
  - intros [a|] [b|]; env_lift_reduce; try reflexivity; auto; apply (proj2 (Hw a b)).
  - intros [a|] [b|]; env_lift_reduce; intro Hba; try reflexivity; auto.
    apply (proj1 (Hn a b Hba)).
  - intros [a|] [b|]; env_lift_reduce; intro Hba; try reflexivity; try discriminate.
    apply (proj2 (Hn a b Hba)).
Qed.

(** Both policies satisfy total weak laws without literal default identities or inhabited keys. *)
Theorem env_laws {K A} pol (E : encoding K) (HE : encoding_laws E) L T :
  lattice_laws L -> lattice_laws (@env K A pol E L T).
Proof.
  intro H; set (d := policy_default pol L T).
  assert (Hd : env_default_order pol d L).
  { destruct pol; [exact (bot_least H) | exact (top_greatest T)]. }
  set (P := env_valid_core E pol d L).
  assert (Hr : forall a, leb P a a = true).
  { intro a; apply (env_core_leb E HE pol d L Hd); intro k; apply (leb_refl H). }
  assert (Ht : forall a b c, leb P a b = true -> leb P b c = true -> leb P a c = true).
  { intros a b c Hab Hbc; apply (env_core_leb E HE pol d L Hd); intro k.
    eapply (leb_trans H); [exact (proj1 (env_core_leb E HE pol d L Hd a b) Hab k) |
      exact (proj1 (env_core_leb E HE pol d L Hd b c) Hbc k)]. }
  pose proof (env_core_bounds E HE pol d L H Hd Env_join) as Hj.
  pose proof (env_core_bounds E HE pol d L H Hd Env_widen) as Hw.
  pose proof (env_core_bounds E HE pol d L H Hd Env_narrow) as Hn.
  destruct pol.
  - constructor; try exact Hr; try exact Ht.
    + intro a; apply (env_core_leb E HE Bottom_default _ L (bot_least H)); intro k.
      change (leb L (Map.find_or E (bot L) k (@Map.empty K A))
        (env_read E (bot L) k a) = true).
      rewrite Map.find_or_equation, Map.get_empty; apply (bot_least H).
    + intros a b; exact (proj1 (Hj a b)).
    + intros a b; exact (proj2 (Hj a b)).
    + intros a b; exact (proj1 (Hw a b)).
    + intros a b; exact (proj2 (Hw a b)).
    + intros a b Hba; exact (proj1 (Hn a b Hba)).
    + intros a b Hba; exact (proj2 (Hn a b Hba)).
  - exact (env_lift_weak P Hr Ht Hj Hw Hn).
Qed.

Local Lemma env_optional_join_least {A} pol d (L : lattice A) (J : lub_laws L) a b c :
  leb L (env_default d a) c = true -> leb L (env_default d b) c = true ->
  leb L (env_default d (env_optional pol d L Env_join a b)) c = true.
Proof.
  destruct pol, a as [a|], b as [b|];
    cbn [env_default env_optional env_optional_c env_callback]; cost_simpl;
    intros Ha Hb; auto; apply (join_least J); assumption.
Qed.

(** Both policies inherit least joins without assuming literal component-default identities. *)
Theorem env_lub {K A} pol (E : encoding K) (HE : encoding_laws E) L T :
  lattice_laws L -> lub_laws L -> lub_laws (@env K A pol E L T).
Proof.
  intros H J; set (d := policy_default pol L T).
  assert (Hd : env_default_order pol d L).
  { destruct pol; [exact (bot_least H) | exact (top_greatest T)]. }
  assert (HJ : lub_laws (env_valid_core E pol d L)).
  { constructor; intros a b c Ha Hb; apply (env_core_leb E HE pol d L Hd); intro k.
    change (leb L
      (env_read E d k (Cost.value (env_merge_c E pol d L Env_join a b)))
      (env_read E d k c) = true).
    rewrite env_merge_observe; apply (env_optional_join_least pol d L J).
    - exact (proj1 (env_core_leb E HE pol d L Hd a c) Ha k).
    - exact (proj1 (env_core_leb E HE pol d L Hd b c) Hb k). }
  destruct pol; [exact HJ | exact (lift_bot_lub _ HJ)].
Qed.

(** Supported maps have invariant reads and default-equivalent reads outside the universe. *)
Definition env_support {K A} (E : encoding K) (L : lattice A) d U inv :=
  family_inv L (fun k m => env_read E d k m) U d inv.

(** Top-default support includes the fresh None independently of the universe. *)
Definition within_env {K A} pol (E : encoding K) (L : lattice A) (T : top L) U inv :
    env_carrier pol E A -> Prop :=
  match pol with
  | Bottom_default => env_support E L (bot L) U inv
  | Top_default => lift_bot_inv (env_support E L (top_value T) U inv)
  end.

(** This core support proof uses the actual default, including an absorbing top default. *)
Local Theorem env_core_closed {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (Hd : match pol with
      | Bottom_default => forall a, leb L d a = true
      | Top_default => forall a, leb L a d = true
      end) (D : env_default_laws pol d L) U inv
    (H : lattice_laws L) (J : lub_laws L) (C : closed_on L inv) (Id : inv d)
    (Wd : forall a b, inv a -> inv b -> equivalent L a d -> equivalent L b d ->
      equivalent L (widen L a b) d) :
  closed_on (@env_valid_core K A E pol d L) (env_support E L d U inv).
Proof.
  assert (Hempty : forall k, env_read E d k (env_empty E) = d).
  { intro k; change (Map.find_or E d k (@Map.empty K A) = d).
    rewrite Map.find_or_equation, Map.get_empty; reflexivity. }
  constructor.
  - change (env_support E L d U inv (env_empty E)).
    split; intro k; rewrite Hempty.
    + exact Id.
    + intros _; split; apply (leb_refl H).
  - intros a b [Ia Sa] [Ib Sb]; split.
    + intro k; rewrite (env_join_read E _ _ L D); apply (join_inv C); auto.
    + intros k Hk; rewrite (env_join_read E _ _ L D).
      destruct (Sa k Hk) as [Had Hda], (Sb k Hk) as [Hbd Hdb]; split.
      * apply (join_least J); assumption.
      * eapply (leb_trans H); [exact Hda | apply (join_upper_l H)].
  - intros a b [Ia Sa] [Ib Sb]; split.
    + intro k; rewrite (env_widen_read E _ _ L D); apply (widen_inv C); auto.
    + intros k Hk; rewrite (env_widen_read E _ _ L D); apply Wd; auto.
  - intros a b [Ia Sa] [Ib Sb] Hba.
    pose proof (proj1 (env_core_leb E HE pol d L Hd b a) Hba) as Hslots; split.
    + intro k; rewrite (env_narrow_read E _ _ L D); apply (narrow_inv C); auto.
    + intros k Hk; rewrite (env_narrow_read E _ _ L D).
      apply (narrow_equivalent L _ _ d H); auto.
Qed.

(** Both policies maintain support with a separate widening-default stability premise. *)
Theorem env_closed {K A} pol (E : encoding K) (HE : encoding_laws E) L T U inv
    (H : lattice_laws L) (J : lub_laws L) (C : closed_on L inv)
    (D : env_default_laws pol (policy_default pol L T) L)
    (Id : inv (policy_default pol L T))
    (Wd : forall a b, inv a -> inv b ->
      equivalent L a (policy_default pol L T) ->
      equivalent L b (policy_default pol L T) ->
      equivalent L (widen L a b) (policy_default pol L T)) :
  closed_on (@env K A pol E L T) (within_env pol E L T U inv).
Proof.
  destruct pol.
  - apply (family_support_closed (env_core_family E HE L H D) U (bot L) H J C).
    + split; apply (leb_refl H).
    + exact Wd.
  - apply lift_bot_closed.
    exact (env_core_closed E HE Top_default _ L (top_greatest T) D U inv H J C Id Wd).
Qed.

Local Lemma finite_false {I} (f : I -> bool) U :
  forallb f U = false -> exists i, In i U /\ f i = false.
Proof.
  induction U as [|i U IH]; cbn; [discriminate |].
  destruct (f i) eqn:Hi; intro Hfalse.
  - destruct (IH Hfalse) as [j [Hj Hbad]]; exists j; auto.
  - exists i; auto.
Qed.

Local Lemma env_false_in {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (Hd : env_default_order pol d L) U
    (a b : env_map E A) :
  (forall k, ~ In k U -> leb L (env_read E d k a) (env_read E d k b) = true) ->
  leb (env_valid_core E pol d L) a b = false ->
  exists k, In k U /\ leb L (env_read E d k a) (env_read E d k b) = false.
Proof.
  intros Hout Hfalse.
  destruct (forallb (fun k => leb L (env_read E d k a) (env_read E d k b)) U)
    eqn:Hall; [|apply finite_false, Hall].
  rewrite forallb_forall in Hall.
  assert (Htrue : leb (env_valid_core E pol d L) a b = true).
  { apply (env_core_leb E HE pol d L Hd); intro k.
    destruct (leb L (env_read E d k a) (env_read E d k b)) eqn:Hk;
      [reflexivity |].
    assert (Hnot : ~ In k U) by (intro Hin; specialize (Hall k Hin); congruence).
    specialize (Hout k Hnot); congruence. }
  congruence.
Qed.

(** Core heights use the observation equations without claiming a least core bottom. *)
Local Theorem env_core_height {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (Hd : env_default_order pol d L)
    (D : env_default_laws pol d L) U inv (H : lattice_laws L) (J : lub_laws L)
    (C : closed_on L inv) (R : height_on L inv) :
  height_on (@env_valid_core K A E pol d L) (env_support E L d U inv).
Proof.
  refine {| rank := fun a => msum U (fun k => rank R (env_read E d k a));
            bound := length U * bound R |}.
  - intros a [Ia _]; rewrite <- msum_constant; apply msum_bounded.
    intros k _; apply (rank_bounded R), Ia.
  - intros a b [Ia _] [Ib _] Hab; apply msum_bounded; intros k _.
    apply (rank_monotone R); auto.
    exact (proj1 (env_core_leb E HE pol d L Hd a b) Hab k).
  - intros a b [Ia Sa] [Ib Sb] Hstrict.
    assert (Hout : forall k, ~ In k U ->
      leb L (env_read E d k (join (env_valid_core E pol d L) a b))
        (env_read E d k a) = true).
    { intros k Hk; rewrite (env_join_read E _ _ L D).
      apply (join_least J); [apply (leb_refl H) |].
      destruct (Sa k Hk), (Sb k Hk); eapply (leb_trans H); eassumption. }
    destruct (env_false_in E HE pol d L Hd U _ _ Hout Hstrict) as [k [Hk Hbad]].
    apply msum_grows.
    + intros j _; rewrite (env_join_read E _ _ L D).
      apply (rank_monotone R); [apply Ia | apply (join_inv C); auto |].
      apply (join_upper_l H).
    + exists k; split; [exact Hk |].
      rewrite (env_join_read E _ _ L D) in Hbad |- *.
      apply (join_rank_grows R); auto.
Defined.

(** Summed core credits need reflected order and widening observations, without core leastness. *)
Local Theorem env_core_wrank {K A} (E : encoding K) (HE : encoding_laws E) pol d L
    (Hd : env_default_order pol d L)
    (D : env_default_laws pol d L) U inv (H : lattice_laws L)
    (W : widening_rank_on L inv) :
  widening_rank_on (@env_valid_core K A E pol d L) (env_support E L d U inv).
Proof.
  refine {| wrank := fun a => msum U (fun k => wrank W (env_read E d k a));
            wbound := length U * wbound W |}.
  - intros a [Ia _]; rewrite <- msum_constant; apply msum_bounded.
    intros k _; apply (wrank_bounded W), Ia.
  - intros a b [Ia _] [Ib _] _; apply msum_bounded; intros k _.
    rewrite (env_widen_read E _ _ L D).
    apply (widening_rank_nonincreasing W); auto.
  - intros a b [Ia Sa] [Ib Sb] Hstrict.
    assert (Hout : forall k, ~ In k U ->
      leb L (env_read E d k b) (env_read E d k a) = true).
    { intros k Hk; destruct (Sa k Hk), (Sb k Hk); eapply (leb_trans H); eassumption. }
    destruct (env_false_in E HE pol d L Hd U b a Hout Hstrict) as [k [Hk Hbad]].
    apply msum_grows.
    + intros j _; rewrite (env_widen_read E _ _ L D).
      apply (widening_rank_nonincreasing W); auto.
    + exists k; split; [exact Hk |].
      rewrite (env_widen_read E _ _ L D); apply (widen_rank_progress W); auto.
Defined.

(** Lifted height needs core reflexivity, rather than a nonexistent least top-default map. *)
Local Theorem env_lift_height {B} (P : lattice B) inv
    (Hr : forall a, leb P a a = true) (R : height_on P inv) :
  height_on (lift_bot P) (lift_bot_inv inv).
Proof.
  refine {| rank := fun a =>
              match a with
              | None => 0
              | Some a => S (rank R a)
              end;
            bound := S (bound R) |}.
  - intros [a|] Ha; cbn [lift_bot_inv] in *;
      [pose proof (rank_bounded R a Ha) |]; cbn; lia.
  - intros [a|] [b|] Ha Hb Hab; rewrite leb_lift_bot in Hab;
      cbn [lift_bot_inv] in *; cbn; try discriminate; try lia.
    pose proof (rank_monotone R a b Ha Hb Hab); lia.
  - intros [a|] [b|] Ha Hb Hstrict; rewrite join_lift_bot;
      rewrite join_lift_bot, leb_lift_bot in Hstrict;
      cbn [lift_bot_inv] in *; cbn; try discriminate; try lia.
    + pose proof (join_rank_grows R a b Ha Hb Hstrict); lia.
    + rewrite Hr in Hstrict; discriminate.
Defined.

(** Environment heights sum component heights and add one for a top-policy fresh bottom. *)
Theorem env_height {K A} pol (E : encoding K) (HE : encoding_laws E) L T U inv
    (H : lattice_laws L) (J : lub_laws L) (C : closed_on L inv)
    (D : env_default_laws pol (policy_default pol L T) L) (R : height_on L inv) :
  height_on (@env K A pol E L T) (within_env pol E L T U inv).
Proof.
  destruct pol.
  - exact (family_height (env_core_family E HE L H D) U (bot L) H J C R).
  - apply env_lift_height.
    + intro a; apply (env_core_leb E HE Top_default _ L (top_greatest T)).
      intro k; apply (leb_refl H).
    + exact (env_core_height E HE Top_default _ L (top_greatest T) D U inv H J C R).
Defined.

(** Environment widening credits include a separate credit at fresh None. *)
Theorem env_wrank {K A} pol (E : encoding K) (HE : encoding_laws E) L T U inv
    (H : lattice_laws L) (D : env_default_laws pol (policy_default pol L T) L)
    (W : widening_rank_on L inv) :
  widening_rank_on (@env K A pol E L T) (within_env pol E L T U inv).
Proof.
  destruct pol.
  - exact (family_wrank (env_core_family E HE L H D) U (bot L) H W).
  - apply lift_bot_wrank.
    exact (env_core_wrank E HE Top_default _ L (top_greatest T) D U inv H W).
Defined.

(** The advertised height bound counts every universe occurrence and the policy lift overhead. *)
Theorem env_height_bound {K A} pol (E : encoding K) (HE : encoding_laws E) L T U inv
    (H : lattice_laws L) (J : lub_laws L) (C : closed_on L inv)
    (D : env_default_laws pol (policy_default pol L T) L) (R : height_on L inv) :
  bound (@env_height K A pol E HE L T U inv H J C D R) =
  match pol with
  | Bottom_default => length U * bound R
  | Top_default => S (length U * bound R)
  end.
Proof.
  destruct pol; [apply msum_constant | reflexivity].
Qed.

(** The advertised widening bound adds one credit for fresh None only in the top policy. *)
Theorem env_wrank_bound {K A} pol (E : encoding K) (HE : encoding_laws E) L T U inv
    (H : lattice_laws L) (D : env_default_laws pol (policy_default pol L T) L)
    (W : widening_rank_on L inv) :
  wbound (@env_wrank K A pol E HE L T U inv H D W) =
  match pol with
  | Bottom_default => length U * wbound W
  | Top_default => S (length U * wbound W)
  end.
Proof.
  destruct pol; [apply msum_constant | reflexivity].
Qed.

(** Indexed component meanings interpret each assignment coordinate at its own key. *)
Definition env_map_gamma {K A C} (E : encoding K) d
    (G : K -> concretisation A C) : concretisation (env_map E A) (K -> C) :=
  family_gamma (fun k => {| gamma := fun a s => gamma (G k) a (s k) |})
    (fun k m => env_read E d k m).

Definition env_gamma {K A C} pol (E : encoding K) (L : lattice A) (T : top L)
    (G : K -> concretisation A C) :
    concretisation (env_carrier pol E A) (K -> C) :=
  match pol with
  | Bottom_default => env_map_gamma E (bot L) G
  | Top_default => lift_bot_gamma (env_map_gamma E (top_value T) G)
  end.

(** Indexed environment meaning is monotone without an inhabited-key premise. *)
Theorem env_gamma_laws {K A C} pol (E : encoding K) (HE : encoding_laws E) L T G :
  lattice_laws L -> (forall k, concretisation_laws L (G k)) ->
  concretisation_laws (@env K A pol E L T) (@env_gamma K A C pol E L T G).
Proof.
  intros H HG; destruct pol.
  - constructor; intros a b s Hab Hs k.
    eapply (gamma_monotone (HG k)); [|apply Hs].
    exact (proj1 (env_core_leb E HE Bottom_default _ L (bot_least H) a b) Hab k).
  - apply lift_bot_gamma_laws; constructor; intros a b s Hab Hs k.
    eapply (gamma_monotone (HG k)); [|apply Hs].
    exact (proj1 (env_core_leb E HE Top_default _ L (top_greatest T) a b) Hab k).
Qed.

(** Bottom-policy emptiness needs a rejecting index for each concrete assignment. *)
Theorem env_bottom_empty {K A C} (E : encoding K) L T G :
  (forall s : K -> C, exists k, ~ gamma (G k) (bot L) (s k)) ->
  bottom_empty (@env K A Bottom_default E L T) (env_gamma Bottom_default E L T G).
Proof.
  intro Hr; constructor; intros s Hs; destruct (Hr s) as [k Hk].
  apply Hk; specialize (Hs k); cbn [env_gamma env_map_gamma family_gamma gamma] in Hs.
  change (gamma (G k) (Map.find_or E (bot L) k (@Map.empty K A)) (s k)) in Hs.
  rewrite Map.find_or_equation, Map.get_empty in Hs; exact Hs.
Qed.

(** Top-policy fresh bottom has empty meaning even when the index type is empty. *)
Theorem env_top_bottom_empty {K A C} (E : encoding K) L T G :
  bottom_empty (@env K A Top_default E L T) (@env_gamma K A C Top_default E L T G).
Proof.
  apply lift_bot_bot_empty.
Qed.

Definition env_map_agree {K A C} (E : encoding K) d (R : K -> agreement A C) :
    agreement (env_map E A) (K -> C) :=
  family_agree (fun k => {| agree := fun a x y => agree (R k) a (x k) (y k) |})
    (fun k m => env_read E d k m).

Definition env_agree {K A C} pol (E : encoding K) (L : lattice A) (T : top L)
    (R : K -> agreement A C) :
    agreement (env_carrier pol E A) (K -> C) :=
  match pol with
  | Bottom_default => env_map_agree E (bot L) R
  | Top_default => lift_bot_agree (env_map_agree E (top_value T) R)
  end.

(** Indexed environment agreement is reflexive and antitone coordinate by coordinate. *)
Theorem env_agree_laws {K A C} pol (E : encoding K) (HE : encoding_laws E) L T R :
  lattice_laws L -> (forall k, agreement_laws L (R k)) ->
  agreement_laws (@env K A pol E L T) (@env_agree K A C pol E L T R).
Proof.
  intros H HR; destruct pol.
  - constructor.
    + intros a s k; apply (agree_refl (HR k)).
    + intros a b x y Hab Hxy k; eapply (agree_antitone (HR k)); [|apply Hxy].
      exact (proj1 (env_core_leb E HE Bottom_default _ L (bot_least H) a b) Hab k).
  - apply lift_bot_agree_laws; constructor.
    + intros a s k; apply (agree_refl (HR k)).
    + intros a b x y Hab Hxy k; eapply (agree_antitone (HR k)); [|apply Hxy].
      exact (proj1 (env_core_leb E HE Top_default _ L (top_greatest T) a b) Hab k).
Qed.

(** Indexed join agreement transports through the applicable exact join observations. *)
Theorem env_agree_join {K A C} pol (E : encoding K) L T R
    (D : env_default_laws pol (policy_default pol L T) L) :
  (forall k, agreement_join_law L (R k)) ->
  agreement_join_law (@env K A pol E L T) (@env_agree K A C pol E L T R).
Proof.
  intro HR; destruct pol.
  - constructor; intros a b x y Ha Hb k.
    change (agree (R k)
      (env_read E (bot L) k (join (env_valid_core E Bottom_default (bot L) L) a b))
      (x k) (y k)).
    rewrite (env_join_read E _ _ L D); apply (agree_join (HR k)); [apply Ha | apply Hb].
  - apply lift_bot_agree_join; constructor; intros a b x y Ha Hb k.
    change (agree (R k)
      (env_read E (top_value T) k
        (join (env_valid_core E Top_default (top_value T) L) a b)) (x k) (y k)).
    rewrite (env_join_read E _ _ L D); apply (agree_join (HR k)); [apply Ha | apply Hb].
Qed.

(** Bottom-policy agreement needs nothing when every component bottom needs nothing. *)
Theorem env_agree_bot {K A C} (E : encoding K) L T R :
  (forall k, agreement_bot L (R k)) ->
  agreement_bot (@env K A Bottom_default E L T) (@env_agree K A C Bottom_default E L T R).
Proof.
  intro HR; constructor; intros x y k.
  change (agree (R k) (Map.find_or E (bot L) k (@Map.empty K A)) (x k) (y k)).
  rewrite Map.find_or_equation, Map.get_empty; apply (agree_bot (HR k)).
Qed.

(** Fresh None always needs no agreement information. *)
Theorem env_agree_bot_top {K A C} (E : encoding K) L T R :
  agreement_bot (@env K A Top_default E L T) (@env_agree K A C Top_default E L T R).
Proof.
  apply lift_bot_agree_bot.
Qed.

(** Pointwise indexed equivalences remain symmetric and transitive under either policy. *)
Theorem env_agree_equivalence {K A C} pol (E : encoding K) L T R :
  (forall k, agreement_equivalence (R k)) ->
  agreement_equivalence (@env_agree K A C pol E L T R).
Proof.
  intro HR; destruct pol; constructor.
  - intros a x y Hxy k; apply (agree_sym (HR k)), Hxy.
  - intros a x y z Hxy Hyz k; eapply (agree_trans (HR k)); [apply Hxy | apply Hyz].
  - intros [a|] x y Hxy; [|exact I]; intro k; apply (agree_sym (HR k)), Hxy.
  - intros [a|] x y z Hxy Hyz; [|exact I]; intro k.
    eapply (agree_trans (HR k)); [apply Hxy | apply Hyz].
Qed.

(** A supplied finite map of greatest reads gives top in either policy. *)
Theorem env_top {K A} pol (E : encoding K) (HE : encoding_laws E) L T
    (H : lattice_laws L)
    (m : env_map E A)
    (Ht : forall k, env_read E (policy_default pol L T) k m = top_value T) :
  top (@env K A pol E L T).
Proof.
  destruct pol.
  - refine {| top_value := m |}; intro a.
    apply (env_core_leb E HE Bottom_default _ L).
    + exact (bot_least H).
    + intro k; rewrite Ht; apply (top_greatest T).
  - change (top (lift_bot (env_valid_core E Top_default (top_value T) L))).
    refine {| top_value := Some m |}; intros [a|]; rewrite leb_lift_bot; [|reflexivity].
    apply (env_core_leb E HE Top_default _ L (top_greatest T)).
    intro k; rewrite Ht; apply (top_greatest T).
Defined.

(** Full indexed component tops give full meaning to a representable environment top. *)
Theorem env_top_full {K A C} pol (E : encoding K) (HE : encoding_laws E) L T
    (H : lattice_laws L) (m : env_map E A) Ht G :
  (forall k, top_full T (G k)) ->
  top_full (env_top pol E HE L T H m Ht) (@env_gamma K A C pol E L T G).
Proof.
  intro HG; destruct pol; constructor; intros s k.
  - change (gamma (G k) (env_read E (bot L) k m) (s k)).
    rewrite Ht; apply (gamma_top_full (HG k)).
  - change (gamma (G k) (env_read E (top_value T) k m) (s k)).
    rewrite Ht; apply (gamma_top_full (HG k)).
Qed.

(** Raw list projection is exactly the public Map list constructor. *)
Theorem env_of_list_raw {K A} (E : encoding K) (xs : list (K * A)) :
  env_raw (env_of_list E xs) = Map.of_list E xs.
Proof.
  reflexivity.
Qed.

(** Raw update projection is exactly the public Map insertion operation. *)
Theorem env_update_raw {K A} (E : encoding K) k v (m : env_map E A) :
  env_raw (env_update E k v m) = Map.set E k v (env_raw m).
Proof.
  reflexivity.
Qed.

(** Updating a fresh unreachable environment leaves it unreachable. *)
Definition env_set_c {K A} pol (E : encoding K) k v :
    env_carrier pol E A -> Cost.t (env_carrier pol E A) :=
  match pol with
  | Bottom_default => env_update_c E k v
  | Top_default => fun m =>
      match m with
      | None => Cost.ret None
      | Some m => Cost.step ;; Cost.map Some (env_update_c E k v m)
      end
  end.

Definition env_set {K A} pol (E : encoding K) k v m : env_carrier pol E A :=
  Cost.value (env_set_c pol E k v m).

(** Top-policy update preserves the unreachable constructor and updates reached maps. *)
Theorem env_set_top_equation {K A} (E : encoding K) k (v : A) m :
  env_set Top_default E k v m = option_map (env_update E k v) m.
Proof.
  destruct m; reflexivity.
Qed.

(** Valid updates set their own key to the supplied value. *)
Theorem env_read_update_same {K A} (E : encoding K) d k v (m : env_map E A) :
  env_read E d k (env_update E k v m) = v.
Proof.
  unfold env_read; rewrite Map.find_or_equation.
  change (env_default d (Map.get E k (Map.set E k v (env_raw m))) = v).
  rewrite Map.get_set_same by exact (proj2_sig m); reflexivity.
Qed.

(** Valid updates leave other key reads unchanged under injective encoding. *)
Theorem env_read_update_other {K A} (E : encoding K) (HE : encoding_laws E)
    d k j v (m : env_map E A) :
  k <> j -> env_read E d k (env_update E j v m) = env_read E d k m.
Proof.
  intro Hkj; unfold env_read; rewrite !Map.find_or_equation.
  change (env_default d (Map.get E k (Map.set E j v (env_raw m))) =
    env_default d (Map.get E k (env_raw m))).
  rewrite (Map.get_set_other E HE) by assumption || exact (proj2_sig m); reflexivity.
Qed.

(** Bottom-policy setters satisfy an unconditional same-key equation. *)
Theorem env_get_set_same {K A} (E : encoding K) (L : lattice A) (T : top L)
    k v (m : env_map E A) :
  env_get Bottom_default E L T k (env_set Bottom_default E k v m) = v.
Proof.
  apply env_read_update_same.
Qed.

(** Top-policy setters satisfy the same-key equation on reached inputs. *)
Theorem env_get_set_same_top {K A} (E : encoding K) (L : lattice A) (T : top L)
    k v (m : env_map E A) :
  env_get Top_default E L T k (env_set Top_default E k v (Some m)) = Some v.
Proof.
  change (Some (env_read E (top_value T) k (env_update E k v m)) = Some v).
  rewrite env_read_update_same; reflexivity.
Qed.

(** Both policy setters preserve observations at every different key. *)
Theorem env_get_set_other {K A} pol (E : encoding K) (HE : encoding_laws E)
    (L : lattice A) (T : top L)
    k j v (m : env_carrier pol E A) :
  k <> j -> env_get pol E L T k (env_set pol E j v m) = env_get pol E L T k m.
Proof.
  intro Hkj; destruct pol; [apply env_read_update_other; assumption |].
  destruct m as [m|]; [|reflexivity].
  change (Some (env_read E (top_value T) k (env_update E j v m)) =
    Some (env_read E (top_value T) k m)).
  rewrite (env_read_update_other E HE) by exact Hkj; reflexivity.
Qed.

(** Valid updates are monotone for either default when both inputs update to the same value. *)
Theorem env_set_monotone {K A} pol (E : encoding K) (HE : encoding_laws E)
    (L : lattice A) (T : top L) :
  lattice_laws L -> forall k v (a b : env_carrier pol E A),
  leb (env pol E L T) a b = true ->
  leb (env pol E L T) (env_set pol E k v a) (env_set pol E k v b) = true.
Proof.
  intro H; destruct pol.
  - intros k v a b Hab.
    change (leb (env_valid_core E Bottom_default (bot L) L)
      (env_update E k v a) (env_update E k v b) = true).
    apply (env_core_leb E HE Bottom_default _ L (bot_least H)); intro j.
    destruct (Bool.bool_dec (eqb E j k) true) as [Heq|Hne].
    + apply (eqb_true_iff E HE) in Heq; subst j.
      rewrite !env_read_update_same; apply (leb_refl H).
    + assert (Hjk : j <> k).
      { intro Heq; subst j; apply Hne, eqb_refl. }
      rewrite !(env_read_update_other E HE) by exact Hjk.
      exact (proj1 (env_core_leb E HE Bottom_default _ L (bot_least H) a b) Hab j).
  - intros k v a b Hab.
    change (leb (lift_bot (env_valid_core E Top_default (top_value T) L)) a b = true)
      in Hab.
    rewrite !env_set_top_equation.
    change (leb (lift_bot (env_valid_core E Top_default (top_value T) L))
      (option_map (env_update E k v) a) (option_map (env_update E k v) b) = true).
    destruct a as [a|], b as [b|]; cbn [option_map]; env_lift_reduce;
      try discriminate; try reflexivity.
    apply (env_core_leb E HE Top_default _ L (top_greatest T)); intro j.
    destruct (Bool.bool_dec (eqb E j k) true) as [Heq|Hne].
    + apply (eqb_true_iff E HE) in Heq; subst j.
      rewrite !env_read_update_same; apply (leb_refl H).
    + assert (Hjk : j <> k).
      { intro Heq; subst j; apply Hne, eqb_refl. }
      rewrite !(env_read_update_other E HE) by exact Hjk.
      exact (proj1 (env_core_leb E HE Top_default _ L (top_greatest T) a b) Hab j).
Qed.

(** A key-bit bound concerns stored bindings and permits arbitrary finite map supports. *)
Definition env_key_bound {K A} (E : encoding K) bits (m : Map.t K A) :=
  forall k v, Map.get E k m = Some v -> (key_bits E k <= bits)%N.

Definition env_keys_bounded {K A} pol (E : encoding K) bits :
    env_carrier pol E A -> Prop :=
  match pol with
  | Bottom_default => fun m => env_key_bound E bits (env_raw m)
  | Top_default => lift_bot_inv (fun m => env_key_bound E bits (env_raw m))
  end.

Local Lemma list_key_bound {K A} (E : encoding K) (xs : list (K * A)) k v :
  In (k, v) xs ->
  (key_bits E k <= fold_right
    (fun kv n => N.max (key_bits E (fst kv)) n) 0%N xs)%N.
Proof.
  induction xs as [|[j w] xs IH]; intros Hin; [contradiction |].
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->; apply N.le_max_l.
  - eapply N.le_trans; [apply IH, Hin | apply N.le_max_r].
Qed.

(** Every valid finite map admits a finite stored-key bit bound. *)
Theorem env_key_bound_exists {K A} (E : encoding K) (HE : encoding_laws E)
    (m : env_map E A) : exists bits, env_key_bound E bits (env_raw m).
Proof.
  exists (fold_right (fun kv n => N.max (key_bits E (fst kv)) n) 0%N
    (Map.elements (env_raw m))).
  intros k v Hget; apply (list_key_bound E _ k v).
  apply (Map.elements_spec E HE k v _ (proj2_sig m)), Hget.
Qed.

(** Producer traversal premises bound primitive Map calls on explicitly bit-bounded inputs. *)
Record env_traversal_laws {K A} (E : encoding K) (inv : A -> Prop) bits
    (work : nat -> nat -> N) : Prop := {
  env_scan_charge : forall r (a b : Map.t K A) c,
    Map.wf E a -> Map.wf E b ->
    env_key_bound E bits a -> env_key_bound E bits b ->
    (forall k v, Map.get E k a = Some v -> inv v) ->
    (forall k v, Map.get E k b = Some v -> inv v) ->
    (forall v o, inv v -> lift_bot_inv inv o ->
      (Cost.ticks (r v o) <= c)%N) ->
    (Cost.ticks (Map.forall2_c r a b) <= work (Map.size a) (Map.size b) * (c + 1))%N;
  env_merge_charge : forall (f : option A -> option A -> Cost.t (option A))
    (a b : Map.t K A) c,
    Map.wf E a -> Map.wf E b ->
    env_key_bound E bits a -> env_key_bound E bits b ->
    (forall k v, Map.get E k a = Some v -> inv v) ->
    (forall k v, Map.get E k b = Some v -> inv v) ->
    (forall x y,
      lift_bot_inv inv x -> lift_bot_inv inv y ->
      (Cost.ticks (f x y) <= c)%N) ->
    (Cost.ticks (Map.combine_c f a b) <= work (Map.size a) (Map.size b) * (c + 1))%N
}.

Arguments env_scan_charge {K A E inv bits work}.
Arguments env_merge_charge {K A E inv bits work}.

(** Core charges equal their primitive Map calls, including the supplied costed callbacks. *)
Theorem env_core_cost_relative {K A} (E : encoding K) pol d (L : lattice A)
    (a b : env_map E A) :
  Cost.ticks (leb_c (env_valid_core E pol d L) a b) =
    match pol with
    | Bottom_default => Cost.ticks (Map.forall2_c
        (fun a b => Cost.step ;; leb_c L a (env_default d b)) (env_raw a) (env_raw b))
    | Top_default => Cost.ticks (Map.forall2_c
        (fun b a => Cost.step ;; leb_c L (env_default d a) b) (env_raw b) (env_raw a))
    end /\
  Cost.ticks (join_c (env_valid_core E pol d L) a b) =
    Cost.ticks (Map.combine_c (env_optional_c pol d L Env_join) (env_raw a) (env_raw b)) /\
  Cost.ticks (widen_c (env_valid_core E pol d L) a b) =
    Cost.ticks (Map.combine_c (env_optional_c pol d L Env_widen) (env_raw a) (env_raw b)) /\
  Cost.ticks (narrow_c (env_valid_core E pol d L) a b) =
    Cost.ticks (Map.combine_c (env_optional_c pol d L Env_narrow) (env_raw a) (env_raw b)).
Proof.
  destruct pol; repeat split; reflexivity.
Qed.

Local Lemma env_stored_inv {K A} (E : encoding K) d (inv : A -> Prop)
    (a : env_map E A) :
  (forall k, inv (env_read E d k a)) ->
  forall k v, Map.get E k (env_raw a) = Some v -> inv v.
Proof.
  intros Ha k v Hget; specialize (Ha k); unfold env_read in Ha.
  rewrite Map.find_or_equation, Hget in Ha; exact Ha.
Qed.

Local Lemma env_callback_cost {A} pol d (L : lattice A) inv c :
  inv d -> cost_bounded_on L inv c -> forall op a b,
  lift_bot_inv inv a -> lift_bot_inv inv b ->
  (Cost.ticks (env_optional_c pol d L op a b) <= c + 1)%N.
Proof.
  intros Hd HC op [a|] [b|] Ha Hb; destruct pol, op;
    cbn [env_optional_c env_callback]; cost_simpl; try lia;
    first [destruct (HC a b Ha Hb) as [? [? [? ?]]]; lia |
      destruct (HC d b Hd Hb) as [? [? [? ?]]]; lia].
Qed.

(** Core cost includes the producer traversal function and all component callback charges. *)
Theorem env_core_cost {K A} (E : encoding K) pol d (L : lattice A) inv bits work
    (M : env_traversal_laws E inv bits work) c (a b : env_map E A) :
  inv d -> cost_bounded_on L inv c ->
  env_key_bound E bits (env_raw a) -> env_key_bound E bits (env_raw b) ->
  (forall k, inv (env_read E d k a)) -> (forall k, inv (env_read E d k b)) ->
  let n := Map.size (env_raw a) in let m := Map.size (env_raw b) in
  (Cost.ticks (leb_c (env_valid_core E pol d L) a b) <=
    N.max (work n m) (work m n) * (c + 2))%N /\
  (Cost.ticks (join_c (env_valid_core E pol d L) a b) <= work n m * (c + 2))%N /\
  (Cost.ticks (widen_c (env_valid_core E pol d L) a b) <= work n m * (c + 2))%N /\
  (Cost.ticks (narrow_c (env_valid_core E pol d L) a b) <= work n m * (c + 2))%N.
Proof.
  intros Hd HC Ba Bb Ha Hb; cbn zeta.
  assert (Hmerge : forall op,
    (Cost.ticks (Map.combine_c (env_optional_c pol d L op) (env_raw a) (env_raw b)) <=
      work (Map.size (env_raw a)) (Map.size (env_raw b)) * (c + 2))%N).
  { intro op; replace (c + 2)%N with (c + 1 + 1)%N by lia.
    apply (env_merge_charge M _ _ _ (c + 1)%N).
    - exact (proj2_sig a).
    - exact (proj2_sig b).
    - exact Ba.
    - exact Bb.
    - exact (env_stored_inv E d inv a Ha).
    - exact (env_stored_inv E d inv b Hb).
    - apply (env_callback_cost pol d L inv c Hd HC). }
  assert (Hscan : forall (x y : env_map E A),
    env_key_bound E bits (env_raw x) -> env_key_bound E bits (env_raw y) ->
    (forall k, inv (env_read E d k x)) ->
    (forall k, inv (env_read E d k y)) ->
    forall r, (forall v o, inv v ->
      lift_bot_inv inv o ->
      (Cost.ticks (r v o) <= c + 1)%N) ->
    (Cost.ticks (Map.forall2_c r (env_raw x) (env_raw y)) <=
      work (Map.size (env_raw x)) (Map.size (env_raw y)) * (c + 2))%N).
  { intros x y Bx By Hx Hy r Hr; replace (c + 2)%N with (c + 1 + 1)%N by lia.
    apply (env_scan_charge M _ _ _ (c + 1)%N).
    - exact (proj2_sig x).
    - exact (proj2_sig y).
    - exact Bx.
    - exact By.
    - exact (env_stored_inv E d inv x Hx).
    - exact (env_stored_inv E d inv y Hy).
    - exact Hr. }
  repeat split; try exact (Hmerge Env_join); try exact (Hmerge Env_widen);
    try exact (Hmerge Env_narrow).
  destruct pol; cbn [env_valid_core env_core leb_c].
  - eapply N.le_trans; [apply (Hscan a b Ba Bb Ha Hb) | apply N.mul_le_mono_r, N.le_max_l].
    intros v [w|] Hv Hw; cbn [env_default]; cost_simpl.
    + destruct (HC v w Hv Hw) as [Hle _]; lia.
    + destruct (HC v d Hv Hd) as [Hle _]; lia.
  - eapply N.le_trans; [apply (Hscan b a Bb Ba Hb Ha) | apply N.mul_le_mono_r, N.le_max_r].
    intros v [w|] Hv Hw; cbn [env_default]; cost_simpl.
    + destruct (HC w v Hw Hv) as [Hle _]; lia.
    + destruct (HC d v Hd Hv) as [Hle _]; lia.
Qed.

(** Size observes stored bindings and assigns zero to fresh bottom. *)
Definition env_size {K A} pol (E : encoding K) : env_carrier pol E A -> nat :=
  match pol with
  | Bottom_default => fun m => Map.size (env_raw m)
  | Top_default => fun m =>
      match m with
      | None => 0
      | Some m => Map.size (env_raw m)
      end
  end.

(** Numeric environment bounds retain primitive traversal and component callback premises. *)
Theorem env_cost {K A} pol (E : encoding K) L T U inv bits work
    (M : env_traversal_laws E inv bits work) c (a b : env_carrier pol E A) :
  inv (policy_default pol L T) -> cost_bounded_on L inv c ->
  env_keys_bounded pol E bits a -> env_keys_bounded pol E bits b ->
  within_env pol E L T U inv a -> within_env pol E L T U inv b ->
  let n := env_size pol E a in let m := env_size pol E b in
  let q := (N.max (work n m) (work m n) * (c + 2) + 2)%N in
  (Cost.ticks (leb_c (env pol E L T) a b) <= q)%N /\
  (Cost.ticks (join_c (env pol E L T) a b) <= q)%N /\
  (Cost.ticks (widen_c (env pol E L T) a b) <= q)%N /\
  (Cost.ticks (narrow_c (env pol E L T) a b) <= q)%N.
Proof.
  intros Hd HC Ba Bb Ha Hb; destruct pol.
  - destruct (env_core_cost E Bottom_default _ L inv bits work M c a b Hd HC Ba Bb
      (proj1 Ha) (proj1 Hb)) as [Hle [Hj [Hw Hn]]].
    pose proof (N.le_max_l (work (Map.size (env_raw a)) (Map.size (env_raw b)))
      (work (Map.size (env_raw b)) (Map.size (env_raw a)))).
    unfold policy_default in Hle, Hj, Hw, Hn.
    cbn [env_size env env_valid_core env_merge_c] in Hle, Hj, Hw, Hn |- *.
    assert (Hq :
      (work (Map.size (env_raw a)) (Map.size (env_raw b)) * (c + 2) <=
      N.max (work (Map.size (env_raw a)) (Map.size (env_raw b)))
        (work (Map.size (env_raw b)) (Map.size (env_raw a))) * (c + 2) + 2)%N).
    { eapply N.le_trans; [apply N.mul_le_mono_r; exact H | apply N.le_add_r]. }
    split; [eapply N.le_trans; [exact Hle | apply N.le_add_r] |].
    split; [eapply N.le_trans; [exact Hj | exact Hq] |].
    split; eapply N.le_trans; [exact Hw | exact Hq | exact Hn | exact Hq].
  - destruct a as [a|], b as [b|]; cbn [env_size env lift_bot leb_c join_c widen_c narrow_c];
      cost_simpl; try (repeat split; lia).
    destruct (env_core_cost E Top_default _ L inv bits work M c a b Hd HC Ba Bb
      (proj1 Ha) (proj1 Hb)) as [Hle [Hj [Hw Hn]]].
    pose proof (N.le_max_l (work (Map.size (env_raw a)) (Map.size (env_raw b)))
      (work (Map.size (env_raw b)) (Map.size (env_raw a)))).
    unfold policy_default in Hle, Hj, Hw, Hn.
    cbn [env_valid_core env_merge_c] in Hle, Hj, Hw, Hn |- *.
    autorewrite with galois_cost in *; repeat split; nia.
Qed.

(** Finite fill charges pair preparation and the public Map list construction. *)
Definition env_fill_c {K A} (E : encoding K) U (v : A) :=
  let* xs := map_c (fun k => Cost.ret (k, v)) U in env_of_list_c E xs.

Definition env_fill {K A} (E : encoding K) U (v : A) := Cost.value (env_fill_c E U v).

(** Finite fill projects to a constant-valued public Map construction. *)
Theorem env_fill_raw {K A} (E : encoding K) U (v : A) :
  env_raw (env_fill E U v) = Map.of_list E (List.map (fun k => (k, v)) U).
Proof.
  unfold env_fill, env_fill_c; rewrite Cost.value_bind, value_map_c.
  change (env_raw (env_of_list E (List.map (fun k => (k, v)) U)) =
    Map.of_list E (List.map (fun k => (k, v)) U)).
  apply env_of_list_raw.
Qed.

Local Lemma constant_lookup_fold {K A} (E : encoding K) k U (v : A) old :
  fold_left (fun o kv => if eqb E k (fst kv) then Some (snd kv) else o)
    (List.map (fun k => (k, v)) U) old =
  if existsb (eqb E k) U then Some v else old.
Proof.
  revert old; induction U as [|j U IH]; intro old; [reflexivity |].
  cbn [List.map fold_left fst snd existsb]; rewrite IH.
  destruct (eqb E k j), (existsb (eqb E k) U); reflexivity.
Qed.

(** Finite fill reads the chosen value at encoded members and the default elsewhere. *)
Theorem env_fill_read {K A} (E : encoding K) d U (v : A) k :
  env_read E d k (env_fill E U v) =
  if existsb (eqb E k) U then v else d.
Proof.
  unfold env_read; rewrite Map.find_or_equation, env_fill_raw, Map.of_list_get.
  rewrite constant_lookup_fold; destruct (existsb (eqb E k) U); reflexivity.
Qed.

(** Every universe key reads the filled value under injective key encoding. *)
Theorem env_fill_inside {K A} (E : encoding K) (HE : encoding_laws E) d U (v : A) k :
  In k U -> env_read E d k (env_fill E U v) = v.
Proof.
  intro Hin; rewrite env_fill_read.
  assert (Hmem : existsb (eqb E k) U = true).
  { apply existsb_exists; exists k; split; [exact Hin | apply eqb_refl]. }
  rewrite Hmem; reflexivity.
Qed.

(** Finite fill is supported when its default and filled value satisfy the component invariant. *)
Theorem env_fill_supported {K A} (E : encoding K) (HE : encoding_laws E) (L : lattice A)
    (H : lattice_laws L) d U inv v :
  inv d -> inv v -> env_support E L d U inv (env_fill E U v).
Proof.
  intros Hd Hv; split.
  - intro k; rewrite env_fill_read; destruct (existsb (eqb E k) U); assumption.
  - intros k Hout; rewrite env_fill_read.
    destruct (existsb (eqb E k) U) eqn:Hmem.
    + apply existsb_exists in Hmem as [j [Hj Heq]].
      apply (eqb_true_iff E HE) in Heq; subst j; contradiction.
    + split; apply (leb_refl H).
Qed.

(** Finite fill charges every input-list cell even when Map construction deduplicates keys. *)
Theorem env_fill_cost {K A} (E : encoding K) U (v : A) :
  Cost.ticks (env_fill_c E U v) =
  (N.of_nat (length U) +
    Cost.ticks (env_of_list_c E (List.map (fun k => (k, v)) U)))%N.
Proof.
  unfold env_fill_c; rewrite Cost.ticks_bind, value_map_c.
  assert (Hprep : Cost.ticks (map_c (fun k => Cost.ret (k, v)) U) =
    N.of_nat (length U)).
  { rewrite ticks_map_c; induction U as [|k U IH]; [reflexivity |].
    cbn [fold_right length]; rewrite Cost.ticks_ret, Nat2N.inj_succ; lia. }
  rewrite Hprep; reflexivity.
Qed.
