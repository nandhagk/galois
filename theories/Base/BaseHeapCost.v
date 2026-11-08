(** * Client-facing heap cost corollaries

    Clients can instantiate the finite pending-entry budget independently on each persistent branch.
    For example, a known pending cap pays for a pop that discards several obsolete entries.
    Builds on: BaseHeap and the public Map cost laws. *)

From Stdlib Require Import List NArith PeanoNat.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Export BaseHeap.
From Galois.Base Require Import BaseEncoding BaseMap BaseHeapBinomial BaseHeapBinomialCost.
Import List.ListNotations.

Module HeapCost.

(** Staleness is the pending count minus the live count. *)
Definition stale {K} (q : Heap.t K) := Heap.stale q.

(** The public numeric operation constant is shared by every cost corollary. *)
Definition heap_k := Heap.heap_k.

(** A fixed cap gives each stale entry a fixed amount of credit. *)
Definition heap_w := Heap.heap_w.

(** The operation budget includes work and any newly created stale credit. *)
Definition heap_cost := Heap.heap_cost.

(** The potential is a per-version observation and does not track a global history. *)
Definition heap_potential {K} P w (q : Heap.t K) := Heap.heap_potential P w q.

(** Push pays for its work and its returned queue's potential along every persistent branch. *)
Theorem push_cost {K} (E : encoding K) (laws : Map.cost_laws) p k q P w :
  Heap.wf E q -> Heap.key_budget E w q -> (Heap.pending_count q < P)%nat ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (Cost.ticks (Heap.push_c E p k q) + heap_potential P w (Heap.push E p k q) <=
    heap_cost P w + heap_potential P w q)%N.
Proof.
  apply Heap.push_cost. exact laws.
Qed.

(** Push also has a worst-case bound without any potential. *)
Theorem push_cost_worst {K} (E : encoding K) (laws : Map.cost_laws) p k q P w :
  Heap.wf E q -> Heap.key_budget E w q -> (Heap.pending_count q < P)%nat ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (Cost.ticks (Heap.push_c E p k q) <= heap_w P w)%N.
Proof.
  apply Heap.push_cost_worst. exact laws.
Qed.

(** A successful pop refunds the potential of the queue it actually returns. *)
Theorem pop_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) q q' p k P w :
  Heap.wf E q -> Heap.key_budget E w q -> (Heap.pending_count q <= P)%nat ->
  Heap.pop E q = Some (p, k, q') ->
  (Cost.ticks (Heap.pop_c E q) + Heap.heap_potential P w q' <=
    Heap.heap_cost P w + Heap.heap_potential P w q)%N.
Proof.
  intros Hwf Hbudget HP Hpop.
  pose proof (Heap.pop_cost E HE laws q P w Hwf Hbudget HP) as Hcost.
  rewrite Hpop in Hcost. exact Hcost.
Qed.

(** The total pop inequality also covers failure after discarding every remaining stale entry. *)
Theorem pop_cost_total {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) q P w :
  Heap.wf E q -> Heap.key_budget E w q -> (Heap.pending_count q <= P)%nat ->
  (Cost.ticks (Heap.pop_c E q) + Heap.pop_output_potential P w (Heap.pop E q) <=
    heap_cost P w + heap_potential P w q)%N.
Proof.
  apply Heap.pop_cost; assumption.
Qed.

(** The trace bound counts actual operation charges along any capped persistent branch. *)
Theorem heap_amortised {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) P w count ticks last N :
  Heap.operation_trace E P w (@Heap.empty K) count ticks last -> (count <= N)%nat ->
  (ticks <= N.of_nat N * heap_cost P w)%N.
Proof.
  apply Heap.heap_amortised; assumption.
Qed.

(** Callee-relative pop credit ranges only over the finite entries that the operation can visit. *)
Theorem pop_cost_callee {K} (E : encoding K) (HE : encoding_laws E) q P w g r W :
  Heap.wf E q -> (Heap.pending_count q <= P)%nat ->
  HeapBinomialCost.bounded w (HeapBinomial.entries (Heap.pending q)) ->
  (forall e, In e (HeapBinomial.entries (Heap.pending q)) ->
    (Cost.ticks (Map.get_c E (snd e) (Heap.live q)) <= g /\
     Cost.ticks (Map.remove_c E (snd e) (Heap.live q)) <= r)%N) ->
  (16 * N.of_nat (S (Nat.log2 P)) * (1 + w) + g + r + 3 <= W)%N ->
  (Cost.ticks (Heap.pop_c E q) + N.of_nat (Heap.output_stale (Heap.pop E q)) * W <=
    Cost.ticks (HeapBinomial.sufficient_fuel_c (Heap.pending q)) +
    W + N.of_nat (stale q) * W +
    N.pos (Pos.size (HeapBinomial.sufficient_fuel (Heap.pending q))))%N.
Proof.
  apply Heap.pop_cost_callee. exact HE.
Qed.

(** Callee-relative push retains the new key's encoder and every reached forest and Map call. *)
Theorem push_cost_callee {K} (E : encoding K) p k q W :
  (Cost.ticks (Heap.push_c E p k q) + N.of_nat (stale (Heap.push E p k q)) * W <=
    Cost.ticks (Map.get_c E k (Heap.live q)) + 2 + Cost.ticks (encode_c E k) +
    Cost.ticks (HeapBinomial.insert_c
      (HeapBinomial.Tree (p, encode E k, k) []) (Heap.pending q)) +
    Cost.ticks (Map.set_c E k p (Heap.live q)) + W + N.of_nat (stale q) * W)%N.
Proof.
  apply Heap.push_cost_callee.
Qed.

End HeapCost.
