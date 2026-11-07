(** * Bounded collection carriers

    Supported collection values carry total heights through invariant restriction.
    For example, a bounded may set can add at most the number of universe keys.
    Builds on: LatticeSet, LatticeEnv and LatticeSub. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeSub
  LatticeSet LatticeEnv.

(** Bounded sets refine valid sets with their finite support certificate. *)
Definition bounded_set {K} (E : encoding K) U :=
  sub_lattice (may E) (within_set E U) (within_set_closed E U).

(** Bounded environments refine policy-specific support and component invariants. *)
Definition bounded_env {K A} pol (E : encoding K) (HE : encoding_laws E)
    (L : lattice A) T U inv H J C D Id Wd :=
  sub_lattice (env pol E L T) (within_env pol E L T U inv)
    (env_closed pol E HE L T U inv H J C D Id Wd).

(** Restriction turns any invariant-relative collection height into a total height. *)
Theorem bounded_height {A} (L : lattice A) inv (C : closed_on L inv)
    (H : height_on L inv) : height (sub_lattice L inv C).
Proof.
  exact (sub_height L inv C H).
Defined.

(** Forgetting bounded evidence preserves and reflects boolean comparison exactly. *)
Theorem bounded_inject {A} (L : lattice A) inv (C : closed_on L inv) :
  order_embedding L (sub_lattice L inv C) (@proj1_sig A inv).
Proof.
  intros a b; apply leb_sub.
Qed.

(** Bounded may sets have total cardinality height with the universe-list bound. *)
Theorem bounded_set_height {K} (E : encoding K) (HE : encoding_laws E) U :
  height (bounded_set E U).
Proof.
  exact (bounded_height (may E) (within_set E U) (within_set_closed E U)
    (may_height E HE U)).
Defined.

(** The universe set is top among bounded may sets without covering the whole key type. *)
Theorem bounded_set_top {K} (E : encoding K) (HE : encoding_laws E) U :
  top (bounded_set E U).
Proof.
  change (top (sub_lattice (may E) (within_set E U) (within_set_closed E U))).
  refine {| top_value := exist _ (set_of_list E U) (set_of_list_within E HE U) |}.
  intros a; rewrite leb_sub; apply (may_leb E HE); intros k Hk.
  change (FinSet.mem E k (FinSet.of_list E U) = true).
  rewrite FinSet.mem_of_list; apply existsb_exists; exists k; split.
  - exact (proj2_sig a k Hk).
  - apply BaseEq.eqb_refl.
Defined.

(** Any bounded collection inherits the total weak laws of its underlying lattice. *)
Theorem bounded_laws {A} (L : lattice A) inv (C : closed_on L inv) :
  lattice_laws L -> lattice_laws (sub_lattice L inv C).
Proof.
  apply sub_laws.
Qed.

(** Bounded operations include the ordered-narrowing comparison guard in their bound. *)
Theorem bounded_cost {A} (L : lattice A) inv (C : closed_on L inv) k :
  cost_bounded_on L inv k ->
  cost_bounded_on (sub_lattice L inv C) (fun _ => True) (2 * k + 2)%N.
Proof.
  apply sub_cost.
Qed.

(** A supported candidate with top reads inside U is greatest among bounded bottom-default maps. *)
Theorem bounded_env_top {K A} (E : encoding K) (HE : encoding_laws E)
    (L : lattice A) (T : top L) (H : lattice_laws L) U inv
    (C : closed_on (env Bottom_default E L T) (within_env Bottom_default E L T U inv))
    (m : env_map E A) (Hm : within_env Bottom_default E L T U inv m)
    (Ht : forall k, List.In k U -> env_read E (bot L) k m = top_value T) :
  top (sub_lattice (env Bottom_default E L T) (within_env Bottom_default E L T U inv) C).
Proof.
  refine {| top_value := exist _ m Hm |}; intro a; rewrite leb_sub.
  apply (env_core_leb E HE Bottom_default _ L (bot_least H)); intro k.
  change (leb L (env_read E (bot L) k (proj1_sig a)) (env_read E (bot L) k m) = true).
  destruct (leb L (env_read E (bot L) k (proj1_sig a)) (env_read E (bot L) k m))
    eqn:Hle; [reflexivity |].
  assert (Hout : ~ List.In k U).
  { intro Hin; rewrite (Ht k Hin) in Hle.
    pose proof (top_greatest T (env_read E (bot L) k (proj1_sig a))); congruence. }
  destruct (proj2 (proj2_sig a) k Hout) as [Had Hda].
  destruct (proj2 Hm k Hout) as [Hmd Hdm].
  pose proof (leb_trans H _ _ _ Had Hdm); congruence.
Defined.

(** A value with an outside member cannot be the projection of a bounded set. *)
Theorem bounded_set_rejects {K} (E : encoding K) U s k :
  FinSet.mem E k (set_raw s) = true -> ~ List.In k U ->
  forall b : {s | within_set E U s}, proj1_sig b <> s.
Proof.
  intros Hmem Hout b Heq; apply Hout.
  rewrite <- Heq in Hmem; exact (proj2_sig b k Hmem).
Qed.
