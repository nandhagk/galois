(** * Byte footprints indexed by site

    Each site maps to a canonical set of half-open byte ranges.
    For example, inserting adjacent writes at one site joins their ranges.
    Builds on: BaseMap and BaseIntervalSet. *)

From Stdlib Require Import List Bool ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseTrieCost BaseMap BaseMapCost BaseIntervalSet.
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

(** Two indexes have the same observation when each site denotes the same interval set. *)
Definition footprint_equiv {T} (E : encoding T) (m n : footprint_index T) : Prop :=
  forall site, footprint_lookup E site m = footprint_lookup E site n.

(** An explicitly stored empty set is observationally identical to an absent site. *)
Theorem footprint_empty_binding_equiv {T} (E : encoding T) (site : T)
    (m : footprint_index T) :
  footprint_lookup E site m = IntervalSet.empty ->
  footprint_equiv E (Map.set E site IntervalSet.empty m) m.
Proof.
  intros Hempty query. unfold footprint_lookup, footprint_lookup_c in *.
  change (Map.find_or E IntervalSet.empty site m = IntervalSet.empty) in Hempty.
  change (Map.find_or E IntervalSet.empty query (Map.set E site IntervalSet.empty m) =
    Map.find_or E IntervalSet.empty query m).
  rewrite !Map.find_or_equation, Map.get_set_raw.
  destruct (eqb E query site) eqn:Heq.
  - rewrite eqb_equation in Heq. apply Pos.eqb_eq in Heq.
    rewrite !Map.get_equation.
    rewrite Heq.
    rewrite Map.find_or_equation in Hempty.
    rewrite Map.get_equation in Hempty.
    symmetry. exact Hempty.
  - reflexivity.
Qed.

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

(** One insertion increases any site's range count by at most one. *)
Theorem footprint_add_lookup_length {T} (E : encoding T) (HE : encoding_laws E)
    (f : footprint T) m site :
  (length (footprint_lookup E site (footprint_add E f m)) <=
    S (length (footprint_lookup E site m)))%nat.
Proof.
  destruct (eqb_spec E HE site (footprint_site f)) as [Heq|Hne].
  - subst site. rewrite footprint_add_lookup_same. apply IntervalSet.add_length.
  - rewrite footprint_add_lookup_other by assumption. lia.
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

(** Removing a write subtracts exactly that interval at its own site. *)
Theorem footprint_remove_lookup_same {T} (E : encoding T) (f : footprint T) m :
  footprint_lookup E (footprint_site f) (footprint_remove E f m) =
    IntervalSet.remove (footprint_lower f, footprint_upper f)
      (footprint_lookup E (footprint_site f) m).
Proof.
  rewrite footprint_remove_equation.
  change (Map.find_or E IntervalSet.empty (footprint_site f)
    (Map.set E (footprint_site f)
      (IntervalSet.remove (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m) =
    IntervalSet.remove (footprint_lower f, footprint_upper f)
      (footprint_lookup E (footprint_site f) m)).
  rewrite Map.find_or_equation, Map.get_set_raw, eqb_refl. reflexivity.
Qed.

(** Removing a write does not affect a distinct site under an injective encoding. *)
Theorem footprint_remove_lookup_other {T} (E : encoding T) (HE : encoding_laws E)
    (f : footprint T) m site :
  site <> footprint_site f ->
  footprint_lookup E site (footprint_remove E f m) = footprint_lookup E site m.
Proof.
  intro Hne. rewrite footprint_remove_equation.
  change (Map.find_or E IntervalSet.empty site
    (Map.set E (footprint_site f)
      (IntervalSet.remove (footprint_lower f, footprint_upper f)
        (footprint_lookup E (footprint_site f) m)) m) =
    Map.find_or E IntervalSet.empty site m).
  rewrite !Map.find_or_equation, Map.get_set_raw.
  rewrite (proj2 (eqb_false_iff E HE _ _) Hne). reflexivity.
Qed.

(** A removal excludes exactly the bytes in its half-open range. *)
Theorem footprint_remove_member_same {T} (E : encoding T) (f : footprint T) m b :
  footprint_index_wf E m ->
  IntervalSet.mem (footprint_lookup E (footprint_site f) (footprint_remove E f m)) b =
    (IntervalSet.mem (footprint_lookup E (footprint_site f) m) b &&
      negb ((footprint_lower f <=? b) && (b <? footprint_upper f)))%bool.
Proof.
  intro Hwf. rewrite footprint_remove_lookup_same.
  apply IntervalSet.mem_remove, footprint_lookup_wf, Hwf.
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

(** A charged fold normalizes a list of writes into an existing index. *)
Fixpoint footprints_add_c {T} (E : encoding T) (fs : list (footprint T))
    (m : footprint_index T) : Cost.t (footprint_index T) :=
  match fs with
  | nil => Cost.ret m
  | f :: rest =>
    Cost.step ;;
    let* next := footprint_add_c E f m in
    footprints_add_c E rest next
  end.

Definition footprints_add {T} (E : encoding T) fs m :=
  Cost.value (footprints_add_c E fs m).

(** Normalization begins with an empty map. *)
Definition footprints_normalise_c {T} (E : encoding T) (fs : list (footprint T)) :=
  footprints_add_c E fs Map.empty.

Definition footprints_normalise {T} (E : encoding T) fs :=
  Cost.value (footprints_normalise_c E fs).

(** The normalization fold returns its input on an empty list. *)
Theorem footprints_add_nil {T} (E : encoding T) m :
  footprints_add E nil m = m.
Proof.
  reflexivity.
Qed.

(** The normalization fold processes the first write before the tail. *)
Theorem footprints_add_cons {T} (E : encoding T) f fs m :
  footprints_add E (f :: fs) m = footprints_add E fs (footprint_add E f m).
Proof.
  reflexivity.
Qed.

(** Each fold step keeps every indexed interval canonical. *)
Theorem footprints_add_wf {T} (E : encoding T) fs m :
  footprint_index_wf E m -> footprint_index_wf E (footprints_add E fs m).
Proof.
  revert m. induction fs as [|f rest IH]; intros m Hwf.
  - rewrite footprints_add_nil. exact Hwf.
  - rewrite footprints_add_cons. apply IH, footprint_add_wf, Hwf.
Qed.

(** Normalizing arbitrary input writes produces a well-formed index. *)
Theorem footprints_normalise_wf {T} (E : encoding T) fs :
  footprint_index_wf E (footprints_normalise E fs).
Proof.
  change (footprint_index_wf E (footprints_add E fs Map.empty)).
  apply footprints_add_wf, footprint_index_empty_wf.
Qed.

(** A footprint contains a byte when both its site and half-open range match. *)
Definition footprint_contains_c {T} (E : encoding T) (f : footprint T) site b :=
  let* same := eqb_c E site (footprint_site f) in
  Cost.ret (same && (footprint_lower f <=? b) && (b <? footprint_upper f))%bool.

Definition footprint_contains {T} (E : encoding T) f site b :=
  Cost.value (footprint_contains_c E f site b).

(** The byte test pays for the encoded site comparison. *)
Theorem footprint_contains_cost {T} (E : encoding T) (f : footprint T) site b :
  (Cost.ticks (footprint_contains_c E f site b) <=
    2 + Cost.ticks (encode_c E site) + Cost.ticks (encode_c E (footprint_site f)) +
      N.min (key_bits E site) (key_bits E (footprint_site f)))%N.
Proof.
  unfold footprint_contains_c. rewrite Cost.ticks_bind, Cost.ticks_ret, N.add_0_r.
  apply eqb_cost.
Qed.

(** A matching write adds its bytes and leaves all other bytes unchanged. *)
Theorem footprint_add_member {T} (E : encoding T) (HE : encoding_laws E)
    (f : footprint T) m site b :
  footprint_index_wf E m ->
  IntervalSet.mem (footprint_lookup E site (footprint_add E f m)) b =
    (footprint_contains E f site b || IntervalSet.mem (footprint_lookup E site m) b)%bool.
Proof.
  intro Hwf. destruct (eqb_spec E HE site (footprint_site f)) as [Heq|Hne].
  - subst site. rewrite footprint_add_member_same by exact Hwf.
    unfold footprint_contains, footprint_contains_c.
    rewrite Cost.value_bind. fold (eqb E (footprint_site f) (footprint_site f)).
    rewrite eqb_refl. cbn. destruct (footprint_lower f <=? b), (b <? footprint_upper f);
      reflexivity.
  - rewrite footprint_add_lookup_other by assumption.
    unfold footprint_contains, footprint_contains_c.
    rewrite Cost.value_bind. fold (eqb E site (footprint_site f)).
    rewrite (proj2 (eqb_false_iff E HE _ _) Hne). reflexivity.
Qed.

(** Normalizing a list includes exactly its writes and the original index. *)
Theorem footprints_add_member {T} (E : encoding T) (HE : encoding_laws E)
    fs m site b :
  footprint_index_wf E m ->
  IntervalSet.mem (footprint_lookup E site (footprints_add E fs m)) b =
    (existsb (fun f => footprint_contains E f site b) fs ||
      IntervalSet.mem (footprint_lookup E site m) b)%bool.
Proof.
  revert m. induction fs as [|f rest IH]; intros m Hwf.
  - rewrite footprints_add_nil. reflexivity.
  - rewrite footprints_add_cons, IH by now apply footprint_add_wf.
    rewrite footprint_add_member by assumption.
    change ((existsb (fun g => footprint_contains E g site b) rest ||
      (footprint_contains E f site b || IntervalSet.mem (footprint_lookup E site m) b))%bool =
      ((footprint_contains E f site b ||
        existsb (fun g => footprint_contains E g site b) rest) ||
        IntervalSet.mem (footprint_lookup E site m) b)%bool).
    destruct (footprint_contains E f site b),
      (existsb (fun f => footprint_contains E f site b) rest); reflexivity.
Qed.

(** A normalized index contains a byte exactly when an input footprint contains it. *)
Theorem footprints_normalise_member {T} (E : encoding T) (HE : encoding_laws E)
    fs site b :
  IntervalSet.mem (footprint_lookup E site (footprints_normalise E fs)) b =
    existsb (fun f => footprint_contains E f site b) fs.
Proof.
  change (IntervalSet.mem (footprint_lookup E site (footprints_add E fs Map.empty)) b =
    existsb (fun f => footprint_contains E f site b) fs).
  rewrite footprints_add_member by (try exact HE; apply footprint_index_empty_wf).
  assert (Hempty : footprint_lookup E site Map.empty = IntervalSet.empty).
  { change (Map.find_or E IntervalSet.empty site Map.empty = IntervalSet.empty).
    rewrite Map.find_or_equation, Map.get_empty. reflexivity. }
  rewrite Hempty, IntervalSet.mem_empty, Bool.orb_false_r. reflexivity.
Qed.

(** Intersect two optional site payloads without inventing an absent site. *)
Definition footprint_inter_payload_c (left right : option IntervalSet.t) :
    Cost.t (option IntervalSet.t) :=
  match left, right with
  | Some xs, Some ys => Cost.map (@Some IntervalSet.t) (IntervalSet.inter_c xs ys)
  | _, _ => Cost.ret None
  end.

Definition footprint_inter_payload left right :=
  Cost.value (footprint_inter_payload_c left right).

(** Intersection traverses the maps and charges each interval intersection. *)
Definition footprint_inter_c {T} (m n : footprint_index T) :=
  Map.combine_c footprint_inter_payload_c m n.

Definition footprint_inter {T} (m n : footprint_index T) :=
  Cost.value (footprint_inter_c m n).

(** Intersection charges both physical map skeletons and each interval callback. *)
Theorem footprint_inter_cost {T} (m n : footprint_index T) :
  (Cost.ticks (footprint_inter_c m n) <=
    TrieCost.trie_k * (1 + MapCost.skeleton_nodes m + MapCost.skeleton_nodes n) +
      TrieCost.combine_work
        (fun a b => Cost.ticks (Map.combine_pair_c footprint_inter_payload_c a b)) m n)%N.
Proof.
  unfold footprint_inter_c. apply MapCost.combine_cost.
Qed.

(** Map combination exposes the payload's value at each site. *)
Theorem footprint_inter_get {T} (E : encoding T) m n site :
  footprint_index_wf E m -> footprint_index_wf E n ->
  Map.get E site (footprint_inter m n) =
    footprint_inter_payload (Map.get E site m) (Map.get E site n).
Proof.
  intros [Hm _] [Hn _]. unfold footprint_inter, footprint_inter_c.
  rewrite Map.combine_c_value.
  apply Map.get_combine; try assumption; reflexivity.
Qed.

(** Pointwise intersection preserves both representation invariants. *)
Theorem footprint_inter_wf {T} (E : encoding T) m n :
  footprint_index_wf E m -> footprint_index_wf E n ->
  footprint_index_wf E (footprint_inter m n).
Proof.
  intros Hm Hn. split.
  - unfold footprint_inter, footprint_inter_c. rewrite Map.combine_c_value.
    apply Map.wf_combine; [exact (proj1 Hm)|exact (proj1 Hn)].
  - intros site ranges Hget. rewrite footprint_inter_get in Hget by assumption.
    destruct (Map.get E site m) as [xs|] eqn:Hx;
      destruct (Map.get E site n) as [ys|] eqn:Hy;
      cbn [footprint_inter_payload footprint_inter_payload_c] in Hget;
      try discriminate.
    inversion Hget; subst ranges. apply IntervalSet.wf_inter.
    + exact (proj2 Hm site xs Hx).
    + exact (proj2 Hn site ys Hy).
Qed.

(** An intersection contains exactly the bytes present in both input indexes. *)
Theorem footprint_inter_member {T} (E : encoding T) m n site b :
  footprint_index_wf E m -> footprint_index_wf E n ->
  IntervalSet.mem (footprint_lookup E site (footprint_inter m n)) b =
    (IntervalSet.mem (footprint_lookup E site m) b &&
      IntervalSet.mem (footprint_lookup E site n) b)%bool.
Proof.
  intros Hm Hn.
  change (IntervalSet.mem (Map.find_or E IntervalSet.empty site (footprint_inter m n)) b =
    (IntervalSet.mem (Map.find_or E IntervalSet.empty site m) b &&
      IntervalSet.mem (Map.find_or E IntervalSet.empty site n) b)%bool).
  rewrite !Map.find_or_equation, footprint_inter_get by assumption.
  destruct (Map.get E site m) as [xs|] eqn:Hx;
    destruct (Map.get E site n) as [ys|] eqn:Hy;
    cbn [footprint_inter_payload footprint_inter_payload_c].
  - apply IntervalSet.mem_inter.
    + exact (proj2 Hm site xs Hx).
    + exact (proj2 Hn site ys Hy).
  - rewrite IntervalSet.mem_empty, Bool.andb_false_r. reflexivity.
  - rewrite IntervalSet.mem_empty. reflexivity.
  - rewrite IntervalSet.mem_empty. reflexivity.
Qed.

(** A missing right-hand site denotes an empty set in an inclusion query. *)
Definition footprint_subset_payload_c (xs : IntervalSet.t) (right : option IntervalSet.t) :=
  IntervalSet.subset_c xs
    (match right with
     | Some ys => ys
     | None => IntervalSet.empty
     end).

(** Inclusion checks all occupied sites and charges the interval comparisons. *)
Definition footprint_subset_c {T} (m n : footprint_index T) :=
  Map.forall2_c footprint_subset_payload_c m n.

Definition footprint_subset {T} (m n : footprint_index T) :=
  Cost.value (footprint_subset_c m n).

(** Inclusion means every byte in the left index also belongs to the right index. *)
Theorem footprint_subset_spec {T} (E : encoding T) (HE : encoding_laws E) m n :
  footprint_index_wf E m -> footprint_index_wf E n ->
  (footprint_subset m n = true <->
    forall site b, IntervalSet.mem (footprint_lookup E site m) b = true ->
      IntervalSet.mem (footprint_lookup E site n) b = true).
Proof.
  intros Hm Hn. unfold footprint_subset, footprint_subset_c.
  rewrite Map.forall2_c_value, (Map.forall2_spec E HE) by exact (proj1 Hm).
  split.
  - intros Hsubset site b Hmember.
    change (IntervalSet.mem (Map.find_or E IntervalSet.empty site m) b = true) in Hmember.
    change (IntervalSet.mem (Map.find_or E IntervalSet.empty site n) b = true).
    rewrite !Map.find_or_equation in *.
    destruct (Map.get E site m) as [xs|] eqn:Hx.
    + specialize (Hsubset site xs Hx).
      unfold footprint_subset_payload_c in Hsubset.
      change (IntervalSet.subset xs
        (match Map.get E site n with Some ys => ys | None => IntervalSet.empty end) = true)
        in Hsubset.
      apply (proj1 (IntervalSet.subset_spec xs
        (match Map.get E site n with Some ys => ys | None => IntervalSet.empty end)
        (proj2 Hm site xs Hx) _)) in Hsubset.
      * now apply Hsubset.
      * destruct (Map.get E site n) as [ys|] eqn:Hy.
        -- exact (proj2 Hn site ys Hy).
        -- apply IntervalSet.wf_empty.
    + rewrite IntervalSet.mem_empty in Hmember. discriminate.
  - intros Hsubset site xs Hx.
    unfold footprint_subset_payload_c.
    change (IntervalSet.subset xs
      (match Map.get E site n with Some ys => ys | None => IntervalSet.empty end) = true).
    apply (proj2 (IntervalSet.subset_spec xs
      (match Map.get E site n with Some ys => ys | None => IntervalSet.empty end)
      (proj2 Hm site xs Hx) _)).
    + intros b Hmember.
      specialize (Hsubset site b).
      change (IntervalSet.mem (Map.find_or E IntervalSet.empty site m) b = true ->
        IntervalSet.mem (Map.find_or E IntervalSet.empty site n) b = true) in Hsubset.
      rewrite !Map.find_or_equation, Hx in Hsubset. now apply Hsubset.
    + destruct (Map.get E site n) as [ys|] eqn:Hy.
      * exact (proj2 Hn site ys Hy).
      * apply IntervalSet.wf_empty.
Qed.

(** Coverage checks the entire half-open query range at one site. *)
Definition footprint_covers_c {T} (E : encoding T) (m : footprint_index T)
    (f : footprint T) :=
  let* ranges := footprint_lookup_c E (footprint_site f) m in
  IntervalSet.covers_c ranges (footprint_lower f, footprint_upper f).

Definition footprint_covers {T} (E : encoding T) m f :=
  Cost.value (footprint_covers_c E m f).

(** Coverage agrees with membership at each byte, including an empty query. *)
Theorem footprint_covers_spec {T} (E : encoding T) m (f : footprint T) :
  footprint_index_wf E m ->
  (footprint_covers E m f = true <->
    forall b, footprint_lower f <= b < footprint_upper f ->
      IntervalSet.mem (footprint_lookup E (footprint_site f) m) b = true).
Proof.
  intro Hwf.
  change (IntervalSet.covers (footprint_lookup E (footprint_site f) m)
    (footprint_lower f, footprint_upper f) = true <->
    forall b, footprint_lower f <= b < footprint_upper f ->
      IntervalSet.mem (footprint_lookup E (footprint_site f) m) b = true).
  apply IntervalSet.covers_spec, footprint_lookup_wf, Hwf.
Qed.

(** Coverage pays for one encoded lookup and the traversed site ranges. *)
Theorem footprint_covers_cost {T} (E : encoding T) m (f : footprint T) :
  (Cost.ticks (footprint_covers_c E m f) <=
    1 + Cost.ticks (encode_c E (footprint_site f)) +
    N.pos (Pos.size (encode E (footprint_site f))) +
    3 + N.of_nat (length (footprint_lookup E (footprint_site f) m)))%N.
Proof.
  unfold footprint_covers_c. rewrite Cost.ticks_bind.
  fold (footprint_lookup E (footprint_site f) m).
  unfold footprint_lookup_c at 1. unfold Map.find_or_c.
  rewrite Cost.ticks_map, Map.get_cost.
  pose proof (IntervalSet.covers_cost (footprint_lookup E (footprint_site f) m)
    (footprint_lower f, footprint_upper f)) as Hcost.
  lia.
Qed.

(** A family bound follows from encoder price, encoded key width and stored range count. *)
Theorem footprint_add_family_cost {T} (E : encoding T) k
    (Henc : encoding_cost_laws E k) (f : footprint T) m width ranges :
  (key_bits E (footprint_site f) <= width)%N ->
  (N.of_nat (length (footprint_lookup E (footprint_site f) m)) <= ranges)%N ->
  (Cost.ticks (footprint_add_c E f m) <=
    2 * (1 + k * width + width) + 2 * (1 + ranges))%N.
Proof.
  intros Hwidth Hranges.
  pose proof (footprint_add_cost E f m) as Hcost.
  pose proof (encode_cost_bound Henc (footprint_site f)) as Hencode.
  unfold key_bits in Hwidth, Hencode.
  nia.
Qed.

(** The same primitive duties bound coverage uniformly over a family of queries. *)
Theorem footprint_covers_family_cost {T} (E : encoding T) k
    (Henc : encoding_cost_laws E k) (f : footprint T) m width ranges :
  (key_bits E (footprint_site f) <= width)%N ->
  (N.of_nat (length (footprint_lookup E (footprint_site f) m)) <= ranges)%N ->
  (Cost.ticks (footprint_covers_c E m f) <=
    1 + k * width + width + 3 + ranges)%N.
Proof.
  intros Hwidth Hranges.
  pose proof (footprint_covers_cost E m f) as Hcost.
  pose proof (encode_cost_bound Henc (footprint_site f)) as Hencode.
  unfold key_bits in Hwidth, Hencode.
  nia.
Qed.

(** A range-count budget bounds every site's current list representation. *)
Definition footprint_range_cap {T} (E : encoding T) (m : footprint_index T) (cap : N) : Prop :=
  forall site, (N.of_nat (length (footprint_lookup E site m)) <= cap)%N.

(** One insertion increases a uniform site budget by at most one. *)
Theorem footprint_add_range_cap {T} (E : encoding T) (HE : encoding_laws E)
    f m cap :
  footprint_range_cap E m cap -> footprint_range_cap E (footprint_add E f m) (cap + 1)%N.
Proof.
  intros Hcap site.
  pose proof (footprint_add_lookup_length E HE f m site) as Hlength.
  pose proof (Hcap site) as Hprior.
  assert (Hconverted :
    (N.of_nat (length (footprint_lookup E site (footprint_add E f m))) <=
      N.of_nat (S (length (footprint_lookup E site m))))%N) by lia.
  rewrite Nat2N.inj_succ in Hconverted. lia.
Qed.

(** A uniform family of writes pays linear traversal and a quadratic range budget. *)
Theorem footprints_add_family_cost {T} (E : encoding T) (HE : encoding_laws E) k
    (Henc : encoding_cost_laws E k) fs m width cap :
  (forall f, In f fs -> (key_bits E (footprint_site f) <= width)%N) ->
  footprint_range_cap E m cap ->
  (Cost.ticks (footprints_add_c E fs m) <=
    N.of_nat (length fs) *
      (1 + 2 * (1 + k * width + width) +
        2 * (1 + cap + N.of_nat (length fs))))%N.
Proof.
  revert m cap. induction fs as [|f rest IH]; intros m cap Hwidth Hcap.
  - cbn [footprints_add_c length]. rewrite Cost.ticks_ret. lia.
  - cbn [footprints_add_c]. rewrite !Cost.ticks_bind, Cost.ticks_step.
    fold (footprint_add E f m).
    pose proof (footprint_add_family_cost E k Henc f m width cap
      (Hwidth f (or_introl eq_refl)) (Hcap (footprint_site f))) as Hfirst.
    pose proof (IH (footprint_add E f m) (cap + 1)%N
      (fun g Hg => Hwidth g (or_intror Hg))
      (footprint_add_range_cap E HE f m cap Hcap)) as Hrest.
    cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** An empty index has a zero range-count budget. *)
Theorem footprint_empty_range_cap {T} (E : encoding T) :
  footprint_range_cap E (@Map.empty T IntervalSet.t) 0.
Proof.
  intro site.
  change (N.of_nat (length (Map.find_or E IntervalSet.empty site Map.empty)) <= 0)%N.
  rewrite Map.find_or_equation, Map.get_empty, IntervalSet.empty_equation. reflexivity.
Qed.

(** Normalization has a uniform quadratic range bound under primitive encoding duties. *)
Theorem footprints_normalise_family_cost {T} (E : encoding T) (HE : encoding_laws E) k
    (Henc : encoding_cost_laws E k) fs width :
  (forall f, In f fs -> (key_bits E (footprint_site f) <= width)%N) ->
  (Cost.ticks (footprints_normalise_c E fs) <=
    N.of_nat (length fs) *
      (1 + 2 * (1 + k * width + width) +
        2 * (1 + N.of_nat (length fs))))%N.
Proof.
  intro Hwidth. unfold footprints_normalise_c.
  pose proof (footprints_add_family_cost E HE k Henc fs Map.empty width 0
    Hwidth (footprint_empty_range_cap E)) as Hcost.
  lia.
Qed.
