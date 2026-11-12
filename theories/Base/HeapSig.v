(** * Priority queue signatures

    A priority queue keeps the least priority assigned to each live positive item.
    For example, pushing a larger priority for a live item leaves its priority unchanged.
    Builds on: Stdlib lists and binary arithmetic, and Argent time interfaces. *)

From Stdlib Require Import List PArith NArith Arith.
From Argent Require Import Time.

Module Type PQ_OPS.
  Parameter t : Type.
  Parameter empty : t.
  Parameter push : N -> positive -> t -> t.
  Parameter pop : t -> option (N * positive * t).
  Parameter size : t -> N.
End PQ_OPS.

Module Type PQ_LAWS (Import Q : PQ_OPS).
  (* spec: wf prio pending *)
  Parameter wf : t -> Prop.
  Parameter prio : t -> positive -> option N.
  Parameter pending : t -> nat.
  (** Empty queues have consistent live and pending entries. *)
  Parameter wf_empty : wf empty.
  (** Pushing retains consistency of live and pending entries. *)
  Parameter wf_push : forall p x q, wf q -> wf (push p x q).
  (** Successful popping retains consistency of the returned queue. *)
  Parameter wf_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) -> wf q1.
  (** Empty queues have no live item. *)
  Parameter prio_empty : forall x, prio empty x = None.
  (** Pushing keeps the smaller of the new and previously live priorities. *)
  Parameter prio_push : forall p x q,
    prio (push p x q) x = Some (match prio q x with Some old => N.min p old | None => p end).
  (** Pushing leaves other live priorities unchanged. *)
  Parameter prio_push_other : forall p x y q, x <> y -> prio (push p x q) y = prio q y.
  (** Popping returns a least live priority and removes that item. *)
  Parameter pop_min : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    prio q x = Some p /\ (forall y r, prio q y = Some r -> (p <= r)%N) /\
    prio q1 x = None /\ (forall y, y <> x -> prio q1 y = prio q y).
  (** Popping fails precisely when no live item exists. *)
  Parameter pop_none : forall q, wf q -> (pop q = None <-> forall x, prio q x = None).
  (** Empty queues have zero live size. *)
  Parameter size_empty : size empty = 0%N.
  (** Pushing increases live size only for an absent item. *)
  Parameter size_push : forall p x q, wf q ->
    size (push p x q) = match prio q x with Some _ => size q | None => N.succ (size q) end.
  (** Successful popping removes one live item. *)
  Parameter size_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    size q = N.succ (size q1).
  (** Empty queues have no pending entry. *)
  Parameter pending_empty : pending empty = 0.
  (** A push adds at most one pending entry. *)
  Parameter pending_push : forall p x q, wf q -> pending (push p x q) <= S (pending q).
  (** A successful pop consumes at least one pending entry. *)
  Parameter pending_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    pending q1 < pending q.
  (** Every live item has a pending entry. *)
  Parameter size_pending : forall q, wf q -> N.to_nat (size q) <= pending q.
End PQ_LAWS.

Module Type PQ := PQ_OPS <+ PQ_LAWS.

Module Type PQ_TIME (Import Q : PQ).
  Parameter T_push : N -> positive -> t -> N.
  Parameter T_pop : t -> N.
  Parameter T_size : t -> N.
  (* spec: phi *)
  Parameter phi : nat -> nat -> t -> N.
  Parameter c_pq : N.
  (** One operation pays for logarithmically many comparisons of bounded width. *)
  Definition unit_pq (P w : nat) : nat := (Nat.log2 P + 1) * (w + 1).
  (** Push pays for its work and the potential of its returned queue. *)
  Parameter T_push_amort : forall P w p x q, (wf q -> (pending q < P)%nat ->
    (Pos.size_nat x + N.size_nat p <= w)%nat ->
    T_push p x q + phi P w (push p x q) <= c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  (** Pop pays for discarded stale entries by refunding input potential. *)
  Parameter T_pop_amort : forall P w q, (wf q -> (pending q <= P)%nat ->
    T_pop q + match pop q with Some (_, _, q1) => phi P w q1 | None => 0 end
      <= c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  (** Empty queues carry zero potential. *)
  Parameter phi_empty : forall P w, (phi P w empty = 0)%N.
  (** Reading cached live size takes constant time. *)
  Parameter T_size_le : forall q, (T_size q <= c_pq)%N.
End PQ_TIME.

Module Type PQ_T := PQ <+ PQ_TIME.

Module Type PQ_PLAN (Import Q : PQ_T).
  Parameter heap : Type.
  (* spec: forest entries ranks *)
  Parameter forest : t -> heap.
  Parameter entries : heap -> list (N * positive).
  Parameter ranks : heap -> nat.
  Parameter insert : N -> positive -> heap -> heap.
  Parameter remove_min : heap -> option (N * positive * heap).
  Parameter pop_step : t -> t + option (N * positive * t).
  Parameter T_insert : N -> positive -> heap -> N.
  Parameter T_remove_min : heap -> N.
  Parameter T_pop_step : t -> N.
  Parameter k_insert k_remove k_step k_credit k_driver : N.

  (** Width budgets include stale entries because removal compares their cached keys. *)
  Definition bounded (w : nat) (q : t) : Prop :=
    forall p x, In (p, x) (entries (forest q)) -> N.size_nat p + Pos.size_nat x <= w.

  (** Staleness counts pending entries in excess of the live cardinality. *)
  Definition stale (q : t) : nat := pending q - N.to_nat (size q).

  (** Each stale entry carries the cost of one removal and one live lookup. *)
  Definition credit (P w : nat) : N := (k_credit * N.of_nat (unit_pq P w))%N.

  (** The landed potential charges each stale entry at a fixed branch-local budget. *)
  Definition stale_phi (P w : nat) (q : t) : N :=
    (N.of_nat (stale q) * credit P w)%N.

  (** Stopping exposes the potential of the returned queue or zero on failure. *)
  Definition output_phi (P w : nat) (r : option (N * positive * t)) : N :=
    match r with
    | Some (_, _, q1) => phi P w q1
    | None => 0
    end.

  (** Forest enumeration agrees with the pending counter. *)
  Parameter F1_pending : forall q, wf q -> length (entries (forest q)) = pending q.
  (** Binomial ranks are logarithmic in the pending cap. *)
  Parameter F2_ranks : forall P q, wf q -> pending q <= P ->
    ranks (forest q) <= Nat.log2 P + 1.
  (** Pushing creates at most one stale entry. *)
  Parameter F3_stale_push : forall p x q, wf q -> stale (push p x q) <= S (stale q).
  (** Skipping a stale entry retains live size and consumes a pending entry. *)
  Parameter F4_skip : forall q q1, wf q -> pop_step q = inl q1 ->
    wf q1 /\ size q1 = size q /\ pending q = S (pending q1).
  (** Skipping retains the finite entry-width budget. *)
  Parameter F5_skip_bounded : forall w q q1, wf q -> bounded w q ->
    pop_step q = inl q1 -> bounded w q1.
  (** The public potential agrees with the landed stale potential on width-bounded queues. *)
  Parameter F6_phi_bounded : forall P w q, wf q -> bounded w q ->
    phi P w q = stale_phi P w q.
  (** A stopping step returns the public pop result. *)
  Parameter F7_stop : forall q r, wf q -> pop_step q = inr r -> pop q = r.
  (** Pushing retains the stored-entry width budget when the new entry fits. *)
  Parameter F8_push_bounded : forall w p x q, wf q -> bounded w q ->
    N.size_nat p + Pos.size_nat x <= w -> bounded w (push p x q).

  (** Insertion traverses the occupied rank positions and compares bounded entries. *)
  Parameter T1_insert : forall P w p x q, (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_insert p x (forest q) <= k_insert * N.of_nat (unit_pq P w))%N.
  (** Removing a minimum scans and melds logarithmically many rank positions. *)
  Parameter T2_remove_min : forall P w q, (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_remove_min (forest q) <= k_remove * N.of_nat (unit_pq P w))%N.
  (** A skipped stale entry pays for its step and the strict loop decrease. *)
  Parameter T3_skip_credit : forall P w q q1, (wf q -> bounded w q -> (pending q <= P)%nat ->
    pop_step q = inl q1 ->
    T_pop_step q + phi P w q1 + 1 <= phi P w q)%N.
  (** A stopping step pays its work and its actual output potential. *)
  Parameter T4_stop_credit : forall P w q r, (wf q -> bounded w q -> (pending q <= P)%nat ->
    pop_step q = inr r ->
    T_pop_step q + output_phi P w r <= k_step * N.of_nat (unit_pq P w) + phi P w q)%N.
  (** The binary loop driver absorbs initial fuel width into the operation budget. *)
  Parameter T5_pop_bounded : forall P w q, (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_pop q + output_phi P w (pop q) <=
      k_driver * N.of_nat (unit_pq P w) + phi P w q)%N.
  (** Width-bounded pushing pays its returned stale credit. *)
  Parameter T6_push_bounded : forall P w p x q, (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_push p x q + phi P w (push p x q) <=
      (k_insert + k_step + k_credit) * N.of_nat (unit_pq P w) + phi P w q)%N.

  (* The landed chain above requires bounded w q. The public amortised contracts omit
     that premise. A potential accounting for stored widths outside bounded queues may
     close the gap. The stale-only source proof does not establish that extension. *)
End PQ_PLAN.

Module Type PQ_ALL := PQ_T <+ PQ_PLAN.
