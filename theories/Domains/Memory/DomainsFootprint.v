(** * Byte footprints indexed by site

    Each site maps to a canonical set of half-open byte ranges.
    For example, inserting adjacent writes at one site joins their ranges.
    Builds on: BaseMap and BaseIntervalSet. *)

From Stdlib Require Import List Bool ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIntervalSet.
Import Cost.Notations.
Local Open Scope Z_scope.

(** A footprint associates one site with a half-open interval of bytes. *)
Record footprint (T : Type) := Footprint {
  footprint_site : T;
  footprint_lower : Z;
  footprint_upper : Z
}.
Arguments Footprint {T}.
Arguments footprint_site {T}.
Arguments footprint_lower {T}.
Arguments footprint_upper {T}.

(** An index stores the represented intervals at their encoded sites. *)
Definition footprint_index (T : Type) := Map.t T IntervalSet.t.

(** The representation invariant covers both map labels and interval payloads. *)
Definition footprint_index_wf {T} (E : encoding T) (m : footprint_index T) : Prop :=
  Map.wf E m /\
  forall site ranges, Map.get E site m = Some ranges -> IntervalSet.wf ranges.

(** An absent site denotes the empty interval set. *)
Definition footprint_lookup_c {T} (E : encoding T) site (m : footprint_index T) :=
  Map.find_or_c E IntervalSet.empty site m.

Definition footprint_lookup {T} (E : encoding T) site (m : footprint_index T) :=
  Cost.value (footprint_lookup_c E site m).

(** An empty map has no malformed site or interval entries. *)
Theorem footprint_index_empty_wf {T} (E : encoding T) :
  footprint_index_wf E (@Map.empty T IntervalSet.t).
Proof.
  split.
  - apply Map.wf_empty.
  - intros site ranges Hget. rewrite Map.get_empty in Hget. discriminate.
Qed.

(** Every lookup from a well-formed index returns canonical intervals. *)
Theorem footprint_lookup_wf {T} (E : encoding T) site m :
  footprint_index_wf E m -> IntervalSet.wf (footprint_lookup E site m).
Proof.
  intros [_ Hinterval].
  change (IntervalSet.wf (Map.find_or E IntervalSet.empty site m)).
  rewrite Map.find_or_equation.
  destruct (Map.get E site m) as [ranges|] eqn:Hget.
  - exact (Hinterval site ranges Hget).
  - apply IntervalSet.wf_empty.
Qed.

(** Inserting one write charges both map accesses and the interval-set union. *)
Definition footprint_add_c {T} (E : encoding T) (f : footprint T) (m : footprint_index T) :=
  let* ranges := footprint_lookup_c E (footprint_site f) m in
  let* updated := IntervalSet.add_c (footprint_lower f, footprint_upper f) ranges in
  Map.set_c E (footprint_site f) updated m.

Definition footprint_add {T} (E : encoding T) f m :=
  Cost.value (footprint_add_c E f m).

(** Insertion changes the interval set stored at the write's encoded site. *)
Theorem footprint_add_equation {T} (E : encoding T) (f : footprint T) m :
  footprint_add E f m =
    Map.set E (footprint_site f)
      (IntervalSet.add (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m.
Proof.
  reflexivity.
Qed.

(** Inserting into a valid index retains the map and interval invariants. *)
Theorem footprint_add_wf {T} (E : encoding T) (f : footprint T) m :
  footprint_index_wf E m -> footprint_index_wf E (footprint_add E f m).
Proof.
  intros Hwf. destruct Hwf as [Hmap Hinterval].
  rewrite footprint_add_equation. split.
  - now apply Map.wf_set.
  - intros site ranges Hget.
    rewrite Map.get_set_raw in Hget.
    destruct (eqb E site (footprint_site f)) eqn:Heq.
    + inversion Hget; subst ranges. apply IntervalSet.wf_add.
      apply footprint_lookup_wf. split; assumption.
    + eapply Hinterval. exact Hget.
Qed.

(** A write adds its byte range at its own site. *)
Theorem footprint_add_lookup_same {T} (E : encoding T) (f : footprint T) m :
  footprint_lookup E (footprint_site f) (footprint_add E f m) =
    IntervalSet.add (footprint_lower f, footprint_upper f)
      (footprint_lookup E (footprint_site f) m).
Proof.
  rewrite footprint_add_equation.
  change (Map.find_or E IntervalSet.empty (footprint_site f)
    (Map.set E (footprint_site f)
      (IntervalSet.add (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m) =
    IntervalSet.add (footprint_lower f, footprint_upper f)
      (footprint_lookup E (footprint_site f) m)).
  rewrite Map.find_or_equation, Map.get_set_raw.
  rewrite eqb_refl. reflexivity.
Qed.

(** A write leaves every site with a different encoding unchanged. *)
Theorem footprint_add_lookup_other {T} (E : encoding T) (HE : encoding_laws E)
    (f : footprint T) m site :
  site <> footprint_site f ->
  footprint_lookup E site (footprint_add E f m) = footprint_lookup E site m.
Proof.
  intro Hne. rewrite footprint_add_equation.
  change (Map.find_or E IntervalSet.empty site
    (Map.set E (footprint_site f)
      (IntervalSet.add (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m) =
    Map.find_or E IntervalSet.empty site m).
  rewrite !Map.find_or_equation, Map.get_set_raw.
  rewrite (proj2 (eqb_false_iff E HE _ _) Hne). reflexivity.
Qed.

(** At the written site, membership gains exactly the bytes of the half-open write. *)
Theorem footprint_add_member_same {T} (E : encoding T) (f : footprint T) m b :
  footprint_index_wf E m ->
  IntervalSet.mem (footprint_lookup E (footprint_site f) (footprint_add E f m)) b =
    (((footprint_lower f <=? b) && (b <? footprint_upper f)) ||
      IntervalSet.mem (footprint_lookup E (footprint_site f) m) b)%bool.
Proof.
  intro Hwf. rewrite footprint_add_lookup_same.
  apply IntervalSet.mem_add, footprint_lookup_wf, Hwf.
Qed.

(** The insertion price includes the encoding twice and the visited interval ranges. *)
Theorem footprint_add_cost {T} (E : encoding T) (f : footprint T) m :
  (Cost.ticks (footprint_add_c E f m) <=
    2 * (1 + Cost.ticks (encode_c E (footprint_site f)) +
      N.pos (Pos.size (encode E (footprint_site f)))) +
    2 * (1 + N.of_nat (length (footprint_lookup E (footprint_site f) m))))%N.
Proof.
  unfold footprint_add_c.
  rewrite !Cost.ticks_bind.
  fold (footprint_lookup E (footprint_site f) m).
  unfold footprint_lookup_c at 1.
  unfold Map.find_or_c.
  rewrite Cost.ticks_map, Map.get_cost, Map.set_cost.
  pose proof (IntervalSet.add_cost (footprint_lower f, footprint_upper f)
    (footprint_lookup E (footprint_site f) m)) as Hcost.
  lia.
Qed.

(** Removing one write range charges the map accesses and interval subtraction. *)
Definition footprint_remove_c {T} (E : encoding T) (f : footprint T)
    (m : footprint_index T) :=
  let* ranges := footprint_lookup_c E (footprint_site f) m in
  let* updated := IntervalSet.remove_c (footprint_lower f, footprint_upper f) ranges in
  Map.set_c E (footprint_site f) updated m.

Definition footprint_remove {T} (E : encoding T) f m :=
  Cost.value (footprint_remove_c E f m).

(** Removal subtracts from the intervals stored at the write's encoded site. *)
Theorem footprint_remove_equation {T} (E : encoding T) (f : footprint T) m :
  footprint_remove E f m =
    Map.set E (footprint_site f)
      (IntervalSet.remove (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m.
Proof.
  reflexivity.
Qed.

(** Removal retains the map and interval invariants. *)
Theorem footprint_remove_wf {T} (E : encoding T) (f : footprint T) m :
  footprint_index_wf E m -> footprint_index_wf E (footprint_remove E f m).
Proof.
  intros [Hmap Hinterval]. rewrite footprint_remove_equation. split.
  - now apply Map.wf_set.
  - intros site ranges Hget. rewrite Map.get_set_raw in Hget.
    destruct (eqb E site (footprint_site f)) eqn:Heq.
    + inversion Hget; subst ranges. apply IntervalSet.wf_remove.
      apply footprint_lookup_wf. split; assumption.
    + eapply Hinterval. exact Hget.
Qed.

(** The removal price includes the encoding twice and the visited interval ranges. *)
Theorem footprint_remove_cost {T} (E : encoding T) (f : footprint T) m :
  (Cost.ticks (footprint_remove_c E f m) <=
    2 * (1 + Cost.ticks (encode_c E (footprint_site f)) +
      N.pos (Pos.size (encode E (footprint_site f)))) +
    (2 * N.of_nat (length (footprint_lookup E (footprint_site f) m)) + 1))%N.
Proof.
  unfold footprint_remove_c.
  rewrite !Cost.ticks_bind.
  fold (footprint_lookup E (footprint_site f) m).
  unfold footprint_lookup_c at 1.
  unfold Map.find_or_c.
  rewrite Cost.ticks_map, Map.get_cost, Map.set_cost.
  pose proof (IntervalSet.remove_cost (footprint_lower f, footprint_upper f)
    (footprint_lookup E (footprint_site f) m)) as Hcost.
  lia.
Qed.
