(** * Static system index accounting

    Preparation budgets retain each row occurrence and all metadata, encoding and bucket work.
    For example, repeating a constraint pays for preparing that constraint again.
    Builds on: FixpointIndex and the public Base set, map and bucket contracts. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseMapCost BaseSet BaseIndex
  BaseTrieCost.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex.
Import List.ListNotations.

Module SystemIndexCost.

(** Distinct preparation cannot create more key occurrences than it consumes. *)
Theorem distinct_length {X} (EX : encoding X) (HE : encoding_laws EX) xs :
  (length (distinct EX xs) <= length xs)%nat.
Proof.
  apply NoDup_incl_length; [apply distinct_nodup|].
  intros x Hx; apply (distinct_spec EX HE), Hx.
Qed.

(** The cardinality of a constructed set is bounded by its input occurrence count. *)
Theorem of_list_size {X} (EX : encoding X) (HE : encoding_laws EX) xs :
  (FinSet.size (FinSet.of_list EX xs) <= length xs)%nat.
Proof.
  rewrite FinSet.size_elements, <- distinct_equation; apply distinct_length, HE.
Qed.

(** A single bucket insertion pays for both encodings and the actual previous-bucket lookup. *)
Theorem push_cost {X C} (EX : encoding X) (c : C) x m e bits :
  (Cost.ticks (encode_c EX x) <= e)%N -> (key_bits EX x <= bits)%N ->
  (Cost.ticks (push_c EX c x m) <= 2 + 2 * (e + bits))%N.
Proof.
  intros Henc Hbits; rewrite FixpointIndex.push_cost, Index.find_cost, Map.get_cost, Map.set_cost.
  fold (key_bits EX x); lia.
Qed.

(** Multiple insertions pay once per distinct-key occurrence, on their actual suffix maps. *)
Theorem push_many_cost {X C} (EX : encoding X) (c : C) xs m e bits :
  (forall x, In x xs ->
    (Cost.ticks (encode_c EX x) <= e)%N /\ (key_bits EX x <= bits)%N) ->
  (Cost.ticks (push_many_c EX c xs m) <=
    N.of_nat (length xs) * (3 + 2 * (e + bits)))%N.
Proof.
  revert m; induction xs as [|x xs IH]; intros m Hkeys;
    rewrite push_many_cost_equation.
  - cbn [length]; lia.
  - pose proof (IH m (fun y Hy => Hkeys y (or_intror Hy))) as Htail.
    destruct (Hkeys x (or_introl eq_refl)) as [Henc Hbits].
    pose proof (push_cost EX c x (push_many EX c xs m) e bits Henc Hbits) as Hpush.
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Distinct construction separates the actual enumeration cost from the bounded insertion work. *)
Theorem distinct_callee_cost {X} (EX : encoding X) xs e bits :
  (forall x, In x xs ->
    (Cost.ticks (encode_c EX x) <= e)%N /\ (key_bits EX x <= bits)%N) ->
  (Cost.ticks (distinct_c EX xs) <= N.of_nat (length xs) * (3 + e + bits) +
    Cost.ticks (FinSet.elements_c (FinSet.of_list EX xs)))%N.
Proof.
  intro Hkeys; rewrite distinct_cost.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold EX xs e bits Hkeys); lia.
Qed.

(** Distinct bucket insertion uses the input length and retains the actual suffix-map calls. *)
Theorem distinct_push_cost {X C} (EX : encoding X) (HE : encoding_laws EX)
    (c : C) xs m e bits :
  (forall x, In x xs ->
    (Cost.ticks (encode_c EX x) <= e)%N /\ (key_bits EX x <= bits)%N) ->
  (Cost.ticks (push_many_c EX c (distinct EX xs) m) <=
    N.of_nat (length xs) * (3 + 2 * (e + bits)))%N.
Proof.
  intro Hkeys.
  assert (Hdistinct : forall x, In x (distinct EX xs) ->
    (Cost.ticks (encode_c EX x) <= e)%N /\ (key_bits EX x <= bits)%N).
  { intros x Hx; apply Hkeys, (distinct_spec EX HE), Hx. }
  pose proof (push_many_cost EX c (distinct EX xs) m e bits Hdistinct) as Hcost.
  pose proof (distinct_length EX HE xs) as Hlength; nia.
Qed.

(** Enumeration pays for physical map traversal and the stored-key projection traversal. *)
Theorem distinct_numeric_cost {X} (EX : encoding X) (HE : encoding_laws EX) xs e bits :
  (forall x, In x xs ->
    (Cost.ticks (encode_c EX x) <= e)%N /\ (key_bits EX x <= bits)%N) ->
  (Cost.ticks (distinct_c EX xs) <=
    N.of_nat (length xs) * (3 + e + bits) +
    TrieCost.trie_k * (1 + N.of_nat (length xs) * bits) + N.of_nat (length xs))%N.
Proof.
  intro Hkeys.
  set (keys := FinSet.of_list EX xs).
  assert (Hwf : Map.wf EX keys) by apply FinSet.wf_of_list.
  assert (Hbits : forall x value, Map.get EX x keys = Some value -> (key_bits EX x <= bits)%N).
  { intros x value Hget.
    assert (Hmem : FinSet.mem EX x keys = true) by
      (rewrite FinSet.mem_equation, Hget; reflexivity).
    unfold keys in Hmem; rewrite FinSet.mem_of_list, existsb_exists in Hmem.
    destruct Hmem as [y [Hy Heq]]; apply (eqb_true_iff EX HE) in Heq; subst y.
    exact (proj2 (Hkeys x Hy)). }
  pose proof (MapCost.elements_numeric_cost EX keys bits Hwf Hbits) as Hmap.
  assert (Hsize : (Map.size keys <= length xs)%nat).
  { rewrite Map.size_elements, <- (length_map (@fst X unit)).
    rewrite <- FinSet.elements_equation, <- FinSet.size_elements.
    apply of_list_size, HE. }
  assert (Hcount : Map.size keys = FinSet.size keys).
  { rewrite FinSet.size_elements, FinSet.elements_equation, length_map, Map.size_elements.
    reflexivity. }
  assert (HsizeN : (N.of_nat (Map.size keys) <= N.of_nat (length xs))%N) by lia.
  assert (Hmap_bound : (Cost.ticks (Map.elements_c keys) <=
    TrieCost.trie_k * (1 + N.of_nat (length xs) * bits))%N).
  { eapply N.le_trans; [exact Hmap|].
    apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r, HsizeN. }
  pose proof (distinct_callee_cost EX xs e bits Hkeys) as Hconstruct.
  fold keys in Hconstruct.
  rewrite FinSet.elements_cost_equation in Hconstruct.
  rewrite <- Hcount in Hconstruct; lia.
Qed.

Module Budget.

(** Preparation measures bound primitive metadata callbacks and per-row declared list lengths. *)
Record t := Make {
  encoder_ticks : N;
  key_digits : N;
  target_ticks : N;
  deps_ticks : N;
  sides_ticks : N;
  read_count : nat;
  output_count : nat
}.

Definition pushes (b : t) count : N :=
  (N.of_nat count * (3 + 2 * (encoder_ticks b + key_digits b)))%N.

Definition distinct (b : t) count : N :=
  (N.of_nat count * (3 + encoder_ticks b + key_digits b) +
    TrieCost.trie_k * (1 + N.of_nat count * key_digits b) + N.of_nat count)%N.

Definition row (b : t) : N :=
  (4 + target_ticks b + deps_ticks b + sides_ticks b +
    distinct b (output_count b) + distinct b (read_count b) +
    pushes b (output_count b) + pushes b (read_count b))%N.

Definition preparation (b : t) count : N := (N.of_nat count * row b)%N.

(** Distinct-key numeric budgets are monotone in their input occurrence count. *)
Theorem distinct_monotone b n m :
  (n <= m)%nat -> (distinct b n <= distinct b m)%N.
Proof.
  intro Hle; assert (HN : (N.of_nat n <= N.of_nat m)%N) by lia.
  unfold distinct; apply N.add_le_mono; [|exact HN].
  apply N.add_le_mono.
  - apply N.mul_le_mono_r, HN.
  - apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r, HN.
Qed.

(** Bucket insertion budgets are monotone in the number of visited keys. *)
Theorem pushes_monotone b n m :
  (n <= m)%nat -> (pushes b n <= pushes b m)%N.
Proof.
  intro Hle; unfold pushes; apply N.mul_le_mono_r; lia.
Qed.

End Budget.
Import Budget.

(** The finite metadata domain includes primary targets, side declarations and read declarations. *)
Record cost_model {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cs : list C) (b : Budget.t) : Prop := {
  key_budget : forall c, In c cs -> forall x,
    In x (System.target S c :: side_targets SS c) \/ In x (deps SS c) ->
    (Cost.ticks (encode_c EX x) <= Budget.encoder_ticks b)%N /\
    (key_bits EX x <= Budget.key_digits b)%N;
  callback_budget : forall c, In c cs ->
    (Cost.ticks (System.target_c S c) <= Budget.target_ticks b)%N /\
    (Cost.ticks (System.deps_c SS c) <= Budget.deps_ticks b)%N /\
    (Cost.ticks (System.side_targets_c SS c) <= Budget.sides_ticks b)%N;
  count_budget : forall c, In c cs ->
    (length (deps SS c) <= Budget.read_count b)%nat /\
    (length (System.target S c :: side_targets SS c) <= Budget.output_count b)%nat
}.

Arguments key_budget {X C A EX S SS cs b}.
Arguments callback_budget {X C A EX S SS cs b}.
Arguments count_budget {X C A EX S SS cs b}.

(** Preparation composes actual callback and distinct costs with numeric primitive bucket bounds. *)
Theorem index_rows_relative_cost {X C A} (EX : encoding X) (HE : encoding_laws EX)
    (S : System.t X C A) (SS : System.static S) cs (b : Budget.t) :
  (forall c, In c cs -> forall x,
    In x (System.target S c :: side_targets SS c) \/ In x (deps SS c) ->
    (Cost.ticks (encode_c EX x) <= Budget.encoder_ticks b)%N /\
    (key_bits EX x <= Budget.key_digits b)%N) ->
  (Cost.ticks (index_rows_c EX S SS cs) <=
    fold_right (fun c total =>
      4 + Cost.ticks (System.target_c S c) +
      Cost.ticks (System.side_targets_c SS c) +
      Cost.ticks (System.deps_c SS c) +
      Cost.ticks (distinct_c EX (System.target S c :: side_targets SS c)) +
      Cost.ticks (distinct_c EX (deps SS c)) +
      Budget.pushes b (length (System.target S c :: side_targets SS c)) +
      Budget.pushes b (length (deps SS c)) + total)%N 0%N cs)%N.
Proof.
  induction cs as [|c cs IH]; intro Hkeys; rewrite index_rows_cost_equation.
  - reflexivity.
  - cbn zeta; cbn [fold_right].
    pose proof (IH (fun d Hd x Hx => Hkeys d (or_intror Hd) x Hx)) as Htail.
    pose proof (distinct_push_cost EX HE c (System.target S c :: side_targets SS c)
      (contributors (Cost.value (index_rows_c EX S SS cs)))
      (Budget.encoder_ticks b) (Budget.key_digits b)
      (fun x Hx => Hkeys c (or_introl eq_refl) x (or_introl Hx))) as Houtputs.
    pose proof (distinct_push_cost EX HE c (deps SS c)
      (readers (Cost.value (index_rows_c EX S SS cs)))
      (Budget.encoder_ticks b) (Budget.key_digits b)
      (fun x Hx => Hkeys c (or_introl eq_refl) x (or_intror Hx))) as Hreads.
    unfold Budget.pushes in Htail |- *; nia.
Qed.

(** Finite primitive budgets give a closed numeric bound on the actual index constructor. *)
Theorem index_rows_cost {X C A} (EX : encoding X) (HE : encoding_laws EX)
    (S : System.t X C A) (SS : System.static S) cs (b : Budget.t) :
  cost_model EX S SS cs b ->
  (Cost.ticks (index_rows_c EX S SS cs) <= Budget.preparation b (length cs))%N.
Proof.
  induction cs as [|c cs IH]; intro HB; rewrite index_rows_cost_equation.
  - reflexivity.
  - cbn zeta.
    assert (Htail : cost_model EX S SS cs b).
    { constructor.
      - intros d Hd; exact (key_budget HB d (or_intror Hd)).
      - intros d Hd; exact (callback_budget HB d (or_intror Hd)).
      - intros d Hd; exact (count_budget HB d (or_intror Hd)). }
    specialize (IH Htail).
    destruct (callback_budget HB c (or_introl eq_refl)) as [Htarget [Hdeps Hsides]].
    destruct (count_budget HB c (or_introl eq_refl)) as [Hreads_count Houtputs_count].
    assert (Houtputs : forall x, In x (System.target S c :: side_targets SS c) ->
      (Cost.ticks (encode_c EX x) <= Budget.encoder_ticks b)%N /\
      (key_bits EX x <= Budget.key_digits b)%N).
    { intros x Hx; exact (key_budget HB c (or_introl eq_refl) x (or_introl Hx)). }
    assert (Hreads : forall x, In x (deps SS c) ->
      (Cost.ticks (encode_c EX x) <= Budget.encoder_ticks b)%N /\
      (key_bits EX x <= Budget.key_digits b)%N).
    { intros x Hx; exact (key_budget HB c (or_introl eq_refl) x (or_intror Hx)). }
    pose proof (distinct_numeric_cost EX HE _ _ _ Houtputs) as Hout_distinct.
    pose proof (distinct_numeric_cost EX HE _ _ _ Hreads) as Hread_distinct.
    pose proof (distinct_push_cost EX HE c _ (contributors (Cost.value (index_rows_c EX S SS cs)))
      _ _ Houtputs) as Hout_push.
    pose proof (distinct_push_cost EX HE c _ (readers (Cost.value (index_rows_c EX S SS cs)))
      _ _ Hreads) as Hread_push.
    assert (Hout_bound : (Cost.ticks
      (distinct_c EX (System.target S c :: side_targets SS c)) <=
      Budget.distinct b (Budget.output_count b))%N).
    { eapply N.le_trans; [exact Hout_distinct|apply Budget.distinct_monotone, Houtputs_count]. }
    assert (Hread_bound : (Cost.ticks (distinct_c EX (deps SS c)) <=
      Budget.distinct b (Budget.read_count b))%N).
    { eapply N.le_trans; [exact Hread_distinct|apply Budget.distinct_monotone, Hreads_count]. }
    assert (Hout_insert : (Cost.ticks (push_many_c EX c
      (FixpointIndex.distinct EX (System.target S c :: side_targets SS c))
      (contributors (Cost.value (index_rows_c EX S SS cs)))) <=
      Budget.pushes b (Budget.output_count b))%N).
    { eapply N.le_trans; [exact Hout_push|apply Budget.pushes_monotone, Houtputs_count]. }
    assert (Hread_insert : (Cost.ticks (push_many_c EX c
      (FixpointIndex.distinct EX (deps SS c))
      (readers (Cost.value (index_rows_c EX S SS cs)))) <=
      Budget.pushes b (Budget.read_count b))%N).
    { eapply N.le_trans; [exact Hread_push|apply Budget.pushes_monotone, Hreads_count]. }
    unfold Budget.preparation in IH |- *; cbn [length]; rewrite Nat2N.inj_succ.
    unfold Budget.row in IH |- *; nia.
Qed.

(** System preparation retains the original constraint occurrence count in its numeric bound. *)
Theorem index_system_cost {X C A} (EX : encoding X) (HE : encoding_laws EX)
    (S : System.t X C A) (SS : System.static S) b :
  cost_model EX S SS (System.constraints S) b ->
  (Cost.ticks (index_system_c EX S SS) <=
    Budget.preparation b (length (System.constraints S)))%N.
Proof.
  apply index_rows_cost, HE.
Qed.

End SystemIndexCost.
Import SystemIndexCost.
