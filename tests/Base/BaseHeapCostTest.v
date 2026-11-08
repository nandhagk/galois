(** * Binomial and stale-entry accounting fixtures

    These observations exercise carrying, cached-code ties and repeated stale discards.
    For example, removing a decreased key leaves two obsolete entries for a later pop.
    Builds on: BaseHeapCost and BaseHeapBinomialCost. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseHeapCost BaseHeapBinomial
  BaseHeapBinomialCost.
Import List.ListNotations.

Definition stale_queue :=
  Heap.push positive_encoding 10%positive 2%positive
    (Heap.push positive_encoding 1%positive 1%positive
      (Heap.push positive_encoding 5%positive 1%positive
        (Heap.push positive_encoding 9%positive 1%positive Heap.empty))).

Definition stale_after_live :=
  match Heap.pop positive_encoding stale_queue with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Definition stale_after_discards :=
  match Heap.pop positive_encoding stale_after_live with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Example heap_pending_before :
  (Heap.pending_count stale_queue, Heap.live_count stale_queue, Heap.stale stale_queue) =
    (4, 2, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_first_live :
  option_map (fun e => (fst (fst e), snd (fst e)))
    (Heap.pop positive_encoding stale_queue) = Some (1, 1)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pending_after_live :
  (Heap.pending_count stale_after_live, Heap.live_count stale_after_live,
    Heap.stale stale_after_live) = (3, 1, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pop_discards_two :
  option_map (fun e => (fst (fst e), snd (fst e)))
    (Heap.pop positive_encoding stale_after_live) = Some (10, 2)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pending_after_discards :
  (Heap.pending_count stale_after_discards, Heap.live_count stale_after_discards,
    Heap.stale stale_after_discards) = (0, 0, 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_live_pop_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_queue) = 22%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_stale_pop_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_after_live) = 39%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_empty_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_after_discards) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_stale_potential_credit :
  N.leb
    (Cost.ticks (Heap.pop_c positive_encoding stale_after_live) +
      Heap.heap_potential 4 2 stale_after_discards)
    (Heap.heap_cost 4 2 + Heap.heap_potential 4 2 stale_after_live) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_empty_forest :
  HeapBinomial.remove_min ([] : HeapBinomial.heap positive) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_cached_tie :
  HeapBinomial.precedesb ((5, 1, 2)%positive) ((5, 2, 1)%positive) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_ignored_push_ticks :
  Cost.ticks (Heap.push_c positive_encoding 10%positive 1%positive stale_queue) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition many_decreases :=
  List.fold_left
    (fun q n => Heap.push positive_encoding (Pos.of_nat (S (128 - n))) 1%positive q)
    (List.seq 0 128) Heap.empty.

Definition many_stale :=
  match Heap.pop positive_encoding many_decreases with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Example heap_many_stale_count :
  (Heap.pending_count many_stale, Heap.live_count many_stale, Heap.stale many_stale) =
    (127, 0, 127).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pop_exceeds_operation_budget :
  N.ltb (Heap.heap_cost 128 1) (Cost.ticks (Heap.pop_c positive_encoding many_stale)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_ticks :
  Cost.ticks (Heap.pop_c positive_encoding many_stale) = 2199%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding many_stale))
    (Heap.heap_cost 128 1 + Heap.heap_potential 128 1 many_stale) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_pop_below_operation_budget :
  N.ltb (Cost.ticks (Heap.pop_c positive_encoding (@Heap.empty positive)))
    (Heap.heap_cost 128 1) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_pop_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding (@Heap.empty positive)) +
    Heap.heap_potential 128 1 (@Heap.empty positive))
    (Heap.heap_cost 128 1 + Heap.heap_potential 128 1 (@Heap.empty positive)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_operation_budget :
  HeapCost.heap_cost 128 1 = 1024%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_potential :
  HeapCost.heap_potential 128 1 many_stale = 65024%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition raw_counter_queue :=
  Heap.Queue [Some (HeapBinomial.Tree ((1, 1, 1)%positive) [])]
    (Map.set positive_encoding 1%positive 1%positive Map.empty) 99 1.

Example heap_raw_counter_removal :
  match Heap.pop positive_encoding raw_counter_queue with
  | None => false
  | Some (_, _, rest) =>
    match Heap.priority positive_encoding 1%positive rest with
    | None => true
    | Some _ => false
    end
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition successful_stale_setup :=
  Heap.push positive_encoding 257%positive 3%positive
    (Heap.push positive_encoding 256%positive 2%positive many_decreases).

Definition successful_stale_input :=
  match Heap.pop positive_encoding successful_stale_setup with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Definition successful_stale_result := Heap.pop positive_encoding successful_stale_input.

Definition successful_stale_rest :=
  match successful_stale_result with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Definition subsequent_result := Heap.pop positive_encoding successful_stale_rest.

Definition subsequent_rest :=
  match subsequent_result with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Example heap_decreases_keep_stale_credit_on_first_live_pop :
  (Heap.stale successful_stale_setup, Heap.stale successful_stale_input) = (127, 127).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_decreases_charge_fuel_spine :
  (Cost.value (HeapBinomial.sufficient_fuel_c (Heap.pending successful_stale_setup)),
    Cost.ticks (HeapBinomial.sufficient_fuel_c (Heap.pending successful_stale_setup))) =
    (256%positive, 8%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_stale_pop :
  option_map (fun e => (fst (fst e), snd (fst e))) successful_stale_result =
    Some (256, 2)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_subsequent_pop :
  option_map (fun e => (fst (fst e), snd (fst e))) subsequent_result =
    Some (257, 3)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_stale_exact_costs :
  (Cost.ticks (Heap.pop_c positive_encoding successful_stale_input),
    Cost.ticks (Heap.pop_c positive_encoding successful_stale_rest)) = (2500, 14)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_stale_residual_potentials :
  (Heap.heap_potential 130 2 successful_stale_input,
    Heap.heap_potential 130 2 successful_stale_rest,
    Heap.heap_potential 130 2 subsequent_rest) = (97536, 0, 0)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_pop_exceeds_budget :
  N.ltb (Heap.heap_cost 130 2)
    (Cost.ticks (Heap.pop_c positive_encoding successful_stale_input)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_subsequent_pop_below_budget :
  N.ltb (Cost.ticks (Heap.pop_c positive_encoding successful_stale_rest))
    (Heap.heap_cost 130 2) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_stale_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding successful_stale_input) +
    Heap.heap_potential 130 2 successful_stale_rest)
    (Heap.heap_cost 130 2 + Heap.heap_potential 130 2 successful_stale_input) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_successful_subsequent_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding successful_stale_rest) +
    Heap.heap_potential 130 2 subsequent_rest)
    (Heap.heap_cost 130 2 + Heap.heap_potential 130 2 successful_stale_rest) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** * Symbolic clients for absent-only worklist queues *)

(** Empty construction establishes the maintained zero-stale and finite-key-budget facts. *)
Theorem heap_empty_no_stale_client {K} (E : encoding K) w :
  Heap.wf E (@Heap.empty K) /\ Heap.stale (@Heap.empty K) = 0%nat /\
  Heap.key_budget E w (@Heap.empty K).
Proof.
  split; [apply Heap.wf_empty|].
  split; [apply Heap.stale_empty|apply Heap.key_budget_empty].
Qed.

(** An absent-row insertion preserves the caller's no-stale invariant and raises pending count. *)
Theorem heap_absent_push_no_stale_client {K} (E : encoding K) p k q :
  Heap.wf E q -> Heap.stale q = 0%nat -> Heap.priority E k q = None ->
  Heap.wf E (Heap.push E p k q) /\ Heap.stale (Heap.push E p k q) = 0%nat /\
  Heap.pending_count (Heap.push E p k q) = S (Heap.pending_count q).
Proof.
  intros Hwf Hzero Habsent. split; [apply Heap.wf_push; exact Hwf|].
  split.
  - rewrite (Heap.stale_push_absent E p k q Habsent). exact Hzero.
  - exact (Heap.pending_count_push_absent E p k q Habsent).
Qed.

(** The actual returned queue after an absent push and successful pop regains the old count. *)
Theorem heap_absent_push_pop_no_stale_client {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) q p k q' popped_priority popped_key P w :
  Heap.wf E q -> Heap.stale q = 0%nat -> Heap.key_budget E w q ->
  Heap.priority E k q = None ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (S (Heap.pending_count q) <= P)%nat ->
  Heap.pop E (Heap.push E p k q) = Some (popped_priority, popped_key, q') ->
  Heap.wf E q' /\ Heap.stale q' = 0%nat /\
  Heap.pending_count q' = Heap.pending_count q /\
  (Cost.ticks (Heap.pop_c E (Heap.push E p k q)) <= HeapCost.heap_cost P w)%N.
Proof.
  intros Hwf Hzero Hbudget Habsent Hencode Hbits HP Hpop.
  destruct (heap_absent_push_no_stale_client E p k q Hwf Hzero Habsent)
    as [Hwf_push [Hzero_push Hpending]].
  pose proof (Heap.key_budget_push_absent E p k q w Habsent Hbudget Hencode Hbits)
    as Hbudget_push.
  assert (Hcap : (Heap.pending_count (Heap.push E p k q) <= P)%nat) by lia.
  destruct (HeapCost.pop_cost_no_stale_result E HE laws (Heap.push E p k q) q'
    popped_priority popped_key P w Hwf_push Hbudget_push Hzero_push Hcap Hpop)
    as [Hwf' [Hzero' [Hpending' Hcost]]].
  split; [exact Hwf'|]. split; [exact Hzero'|]. split; [lia|exact Hcost].
Qed.

(** A failed actual pop exposes absence at every key without inspecting the private live Map. *)
Theorem heap_pop_none_priority_client {K} (E : encoding K) (HE : encoding_laws E) q :
  Heap.wf E q -> Heap.pop E q = None -> forall k, Heap.priority E k q = None.
Proof.
  exact (Heap.pop_none_priority E HE q).
Qed.

(** The public emptiness characterization also needs no injectivity premise. *)
Theorem heap_is_empty_priority_client {K} (E : encoding K) q :
  Heap.wf E q -> (Heap.is_empty q = true <-> forall k, Heap.priority E k q = None).
Proof.
  exact (Heap.is_empty_spec E q).
Qed.

(** A finite support client uses only public priorities and the public size observation. *)
Theorem heap_size_support_client {K} (E : encoding K) (HE : encoding_laws E) U q :
  Heap.wf E q ->
  (forall k p, Heap.priority E k q = Some p -> In k U) ->
  (Heap.size q <= length U)%nat.
Proof.
  exact (Heap.size_support_bound E HE U q).
Qed.

(** Empty size and zero potential are available without inspecting either queue representation. *)
Theorem heap_empty_size_potential_client {K} P w :
  Heap.size (@Heap.empty K) = 0%nat /\
  HeapCost.heap_potential P w (@Heap.empty K) = 0%N.
Proof.
  split; [apply Heap.size_empty|].
  apply HeapCost.heap_potential_zero. apply Heap.stale_empty.
Qed.

(** Live-priority premises establish the public key budget without inspecting pending trees. *)
Theorem heap_live_priority_budget_client {K} (E : encoding K) (HE : encoding_laws E) U q w :
  Heap.wf E q -> Heap.stale q = 0%nat ->
  (forall k p, Heap.priority E k q = Some p -> In k U) ->
  (forall k, In k U ->
    (Cost.ticks (encode_c E k) <= w /\
      N.pos (Pos.size (encode E k)) <= w)%N) ->
  Heap.key_budget E w q.
Proof.
  intros Hwf Hzero Hsupport Hkeys.
  apply (Heap.key_budget_live E HE q w Hwf Hzero).
  intros k p Hpriority. apply Hkeys. exact (Hsupport k p Hpriority).
Qed.

(** A live-support client couples the returned queue, zero potential and worst-case pop cost. *)
Theorem heap_live_support_pop_client {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) U q q' p k P w :
  Heap.wf E q -> Heap.stale q = 0%nat ->
  (forall key priority, Heap.priority E key q = Some priority -> In key U) ->
  (forall key, In key U ->
    (Cost.ticks (encode_c E key) <= w /\
      N.pos (Pos.size (encode E key)) <= w)%N) ->
  (Heap.pending_count q <= P)%nat -> Heap.pop E q = Some (p, k, q') ->
  (Heap.size q <= length U)%nat /\ Heap.wf E q' /\ Heap.stale q' = 0%nat /\
  HeapCost.heap_potential P w q' = 0%N /\
  (Heap.pending_count q' + 1 = Heap.pending_count q)%nat /\
  (Cost.ticks (Heap.pop_c E q) <= HeapCost.heap_cost P w)%N.
Proof.
  intros Hwf Hzero Hsupport Hkeys HP Hpop.
  pose proof (Heap.size_support_bound E HE U q Hwf Hsupport) as Hsize.
  pose proof (heap_live_priority_budget_client E HE U q w Hwf Hzero Hsupport Hkeys)
    as Hbudget.
  destruct (HeapCost.pop_cost_no_stale_result E HE laws q q' p k P w
    Hwf Hbudget Hzero HP Hpop) as [Hwf' [Hzero' [Hcount Hcost]]].
  split; [exact Hsize|]. split; [exact Hwf'|]. split; [exact Hzero'|].
  split; [exact (HeapCost.heap_potential_zero P w q' Hzero')|].
  split; assumption.
Qed.
