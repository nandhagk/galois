(** * Priority queues

    A binomial forest indexes a live map and retains obsolete entries after decreases.
    For example, pushing priorities five and two for one key leaves priority two live.
    Builds on: HeapSig, MapSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith PArith PeanoNat Lia.
From Argent Require Import Time Std.
From Galois.Base Require Import HeapSig KeySig MapSig.
From Stdlib Require Import List NArith PArith.
From Galois.Base Require Import Trie Loop.
Import List.ListNotations.

Definition heap_entry := (N * positive)%type.
Scheme All for list.

Inductive heap_tree := HeapTree (root_entry : heap_entry) (children : list heap_tree).
Definition heap_forest := list (option heap_tree).
Record priority_queue := Queue {
  pending : heap_forest;
  live : PTrieCode.t N;
  live_count : N;
  pending_count : N
}.

Definition heap_pending (q : priority_queue) : heap_forest :=
  match q with Queue h _ _ _ => h end.
TimeFun heap_pending.

Definition heap_root (t : heap_tree) := match t with HeapTree e _ => e end.
TimeFun pending.
TimeFun live.
TimeFun live_count.
TimeFun pending_count.
TimeFun heap_root.

Definition heap_before (a b : heap_entry) :=
  if N.ltb (fst a) (fst b) then true
  else if N.eqb (fst a) (fst b) then Pos.leb (snd a) (snd b) else false.
TimeFun heap_before.
Definition heap_link (a b : heap_tree) :=
  match a, b with
  | HeapTree e cs, HeapTree e' cs' =>
    if heap_before e e' then HeapTree e (b :: cs) else HeapTree e' (a :: cs')
  end.
TimeFun heap_link.
Definition heap_digit (s : option heap_tree) (hs : heap_forest) :=
  match s, hs with None, [] => [] | _, _ => s :: hs end.
TimeFun heap_digit.
Fixpoint heap_insert (t : heap_tree) (h : heap_forest) : heap_forest :=
  match h with
  | [] => [Some t]
  | None :: hs => Some t :: hs
  | Some u :: hs => None :: heap_insert (heap_link t u) hs
  end.
TimeFun heap_insert.
Fixpoint heap_meld (a b : heap_forest) (carry : option heap_tree) {struct a} : heap_forest :=
  match a with
  | [] => match carry with None => b | Some t => heap_insert t b end
  | x :: xs =>
    match b with
    | [] => match carry with None => a | Some t => heap_insert t a end
    | y :: ys =>
      match x, y, carry with
      | None, None, c => heap_digit c (heap_meld xs ys None)
      | Some t, None, None | None, Some t, None => heap_digit (Some t) (heap_meld xs ys None)
      | Some t, Some u, None | Some t, None, Some u | None, Some t, Some u =>
        heap_digit None (heap_meld xs ys (Some (heap_link t u)))
      | Some t, Some u, Some c => heap_digit (Some c) (heap_meld xs ys (Some (heap_link t u)))
      end
    end
  end.
TimeFun heap_meld.
Fixpoint heap_select (h : heap_forest) : option (heap_tree * heap_forest) :=
  match h with
  | [] => None
  | x :: xs =>
    match heap_select xs with
    | None => match x with None => None | Some t => Some (t, []) end
    | Some (t, rest) =>
      match x with
      | None => Some (t, heap_digit None rest)
      | Some u => if heap_before (heap_root u) (heap_root t)
                  then Some (u, heap_digit None xs) else Some (t, heap_digit (Some u) rest)
      end
    end
  end.
TimeFun heap_select.
Definition heap_remove_min (h : heap_forest) : option (heap_entry * heap_forest) :=
  match heap_select h with
  | None => None
  | Some (HeapTree e cs, rest) => Some (e, heap_meld (map (@Some heap_tree) (rev cs)) rest None)
  end.
TimeFun heap_remove_min.
Fixpoint heap_fuel (h : heap_forest) : positive :=
  match h with [] => xH | _ :: rest => xO (heap_fuel rest) end.

TimeFun heap_fuel.

Module HeapCode <: PQ_OPS.
  Definition t := priority_queue.
  Definition empty : t := Queue [] PTrieCode.empty 0%N 0%N.
  Definition size (q : t) := live_count q.
  Definition enqueue (p : N) (k : positive) (q : t) (n : N) : t :=
    Queue (heap_insert (HeapTree (p, k) []) (pending q))
      (PTrieCode.set k p (live q)) n (N.succ (pending_count q)).
  Definition push (p : N) (k : positive) (q : t) : t :=
    match PTrieCode.get k (live q) with
    | None => enqueue p k q (N.succ (live_count q))
    | Some old => if N.ltb p old then enqueue p k q (live_count q) else q
    end.
  Definition heap_pop_step (m : PTrieCode.t N) (n : N) (s : heap_forest * N) :
      heap_forest * N + option (N * positive * t) :=
    let '(h, total) := s in
    match heap_remove_min h with
    | None => inr None
    | Some ((p, k), rest) =>
      match PTrieCode.get k m with
      | Some current =>
        if N.eqb p current then
          inr (Some (p, k, Queue rest (PTrieCode.remove k m) (N.pred n) (N.pred total)))
        else inl (rest, N.pred total)
      | None => inl (rest, N.pred total)
      end
    end.
  TimeFun heap_pop_step.
  Definition pop (q : t) : option (N * positive * t) :=
    match loopN (heap_pop_step (live q) (live_count q)) (N.pos (heap_fuel (pending q)))
      (pending q, pending_count q) with
    | inl _ => None
    | inr result => result
    end.
  TimeFun pop.
End HeapCode.

Fixpoint heap_tree_entries (tr : heap_tree) : list heap_entry :=
  match tr with HeapTree e cs => e :: flat_map heap_tree_entries cs end.

Definition heap_precedes (a b : heap_entry) : Prop :=
  (fst a < fst b)%N \/ (fst a = fst b /\ (snd a <= snd b)%positive).

Inductive heap_valid : nat -> heap_tree -> Prop :=
  | HeapValid_zero e : heap_valid 0 (HeapTree e [])
  | HeapValid_link r e cs b :
      heap_valid r (HeapTree e cs) -> heap_valid r b ->
      (forall x, In x (heap_tree_entries b) -> heap_precedes e x) ->
      heap_valid (S r) (HeapTree e (b :: cs)).

Fixpoint heap_entries (h : heap_forest) : list heap_entry :=
  match h with
  | [] => []
  | s :: hs => (match s with None => [] | Some tr => heap_tree_entries tr end) ++ heap_entries hs
  end.

Fixpoint heap_forest_valid (r : nat) (h : heap_forest) : Prop :=
  match h with
  | [] => True
  | s :: hs =>
    (match s with None => True | Some tr => heap_valid r tr end) /\
    heap_forest_valid (S r) hs /\ (s <> None \/ hs <> [])
  end.

Module Heap <: PQ.
  Include HeapCode.
  Definition prio (q : t) (x : positive) := PTrieCode.get x (live q).
  Definition wf (q : t) : Prop :=
    heap_forest_valid 0 (pending q) /\
    (forall k p, prio q k = Some p -> In (p, k) (heap_entries (pending q))) /\
    live_count q = N.of_nat (length (PTrieCode.elements (live q))) /\
    pending_count q = N.of_nat (length (heap_entries (pending q))).
  Definition pending (q : t) : nat := N.to_nat (pending_count q).
  Lemma wf_empty : wf empty.
  Proof.
    split; [exact I|]; split.
    - intros k p Hget; unfold prio, empty in Hget; cbn in Hget.
      rewrite PTrie.get_empty in Hget; discriminate.
    - split; reflexivity.
  Qed.
  Lemma prio_empty : forall x, prio empty x = None.
  Proof. intro x; apply PTrie.get_empty. Qed.
  Lemma size_empty : size empty = 0%N.
  Proof. reflexivity. Qed.
  Lemma pending_empty : pending empty = 0.
  Proof. reflexivity. Qed.
  Lemma wf_push : forall p x q, wf q -> wf (push p x q).
  Proof. Admitted. (* CONVERT: wf_push: The variable wf_inserted was not found in the current environment. *)
  Lemma wf_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) -> wf q1.
  Proof. Admitted. (* CONVERT: wf_pop: The variable pop_correct was not found in the current environment. *)
  Lemma prio_push : forall p x q,
    prio (push p x q) x = Some (match prio q x with Some old => N.min p old | None => p end).
  Proof. Admitted. (* SIG-QUESTION: landed priority_push assumes wf. *)
  Lemma prio_push_other : forall p x y q, x <> y -> prio (push p x q) y = prio q y.
  Proof. Admitted. (* SIG-QUESTION: landed priority_push assumes wf. *)
  Lemma pop_min : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    prio q x = Some p /\ (forall y r, prio q y = Some r -> (p <= r)%N) /\
    prio q1 x = None /\ (forall y, y <> x -> prio q1 y = prio q y).
  Proof. Admitted. (* CONVERT: pop_min: The variable pop_correct was not found in the current environment. *)
  Lemma pop_none : forall q, wf q -> (pop q = None <-> forall x, prio q x = None).
  Proof. Admitted. (* CONVERT: pop_none_empty: The variable pop_correct was not found in the current environment. *)
  Lemma size_push : forall p x q, wf q ->
    size (push p x q) = match prio q x with Some _ => size q | None => N.succ (size q) end.
  Proof.
    intros p x q Hwf; unfold push, prio, size; destruct (PTrieCode.get x (live q));
      [destruct (N.ltb p n)|]; reflexivity.
  Qed.
  Lemma size_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    size q = N.succ (size q1).
  Proof. Admitted. (* CONVERT: size_pop: The variable pop_correct was not found in the current environment. *)
  Lemma pending_push : forall p x q, wf q -> pending (push p x q) <= S (pending q).
  Proof. Admitted.
  Lemma pending_pop : forall q p x q1, wf q -> pop q = Some (p, x, q1) ->
    pending q1 < pending q.
  Proof. Admitted.
  Lemma size_pending : forall q, wf q -> N.to_nat (size q) <= pending q.
  Proof. Admitted. (* CONVERT: live_pending_bound: The variable live_pending_bound was not found in the current environment. *)
End Heap.

Module HeapT <: PQ_ALL.
  Include Heap.

  TimeFun size.
  TimeFun enqueue.
  TimeFun push.

  Definition unit_pq (P w : nat) : nat := (Nat.log2 P + 1) * (w + 1).
  Definition c_pq : N := 1. (* STUB *)
  Definition k_insert : N := 1. (* STUB *)
  Definition k_remove : N := 1. (* STUB *)
  Definition k_step : N := 1. (* STUB *)
  Definition k_credit : N := 1. (* STUB *)
  Definition k_driver : N := 1. (* STUB *)
  Definition stale (q : t) : nat := pending q - N.to_nat (size q).
  Definition credit (P w : nat) : N := (k_credit * N.of_nat (unit_pq P w))%N.
  Definition stale_phi (P w : nat) (q : t) : N :=
    (N.of_nat (stale q) * credit P w)%N.
  Definition phi (P w : nat) (q : t) : N := stale_phi P w q.

  Lemma T_push_amort : forall P w p x q,
    (wf q -> (pending q < P)%nat ->
    (Pos.size_nat x + N.size_nat p <= w)%nat ->
    T_push p x q + phi P w (push p x q) <=
      c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_pop_amort : forall P w q,
    (wf q -> (pending q <= P)%nat ->
    T_pop q + match pop q with Some (_, _, q1) => phi P w q1 | None => 0 end
      <= c_pq * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof. Admitted. (* STUB *)
  Lemma phi_empty : forall P w, (phi P w empty = 0)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_size_le : forall q, (T_size q <= c_pq)%N.
  Proof. Admitted. (* STUB *)

  Definition heap := heap_forest.
  Definition forest (q : t) : heap := heap_pending q.
  Definition entries := heap_entries.
  Definition ranks (h : heap) : nat := length h.
  Definition insert (p : N) (x : positive) (h : heap) : heap :=
    heap_insert (HeapTree (p, x) []) h.
  Definition remove_min := heap_remove_min.
  Definition pop_step (q : t) : t + option (N * positive * t) :=
    match HeapCode.heap_pop_step (live q) (live_count q) (heap_pending q, pending_count q) with
    | inl (h, n) => inl (Queue h (live q) (live_count q) n)
    | inr result => inr result
    end.

  TimeFun insert.
  TimeFun remove_min.
  TimeFun pop_step.

  Definition bounded (w : nat) (q : t) : Prop :=
    forall p x, In (p, x) (entries (forest q)) -> N.size_nat p + Pos.size_nat x <= w.
  Definition output_phi (P w : nat) (r : option (N * positive * t)) : N :=
    match r with Some (_, _, q1) => phi P w q1 | None => 0%N end.

  Lemma F1_pending : forall q, wf q -> length (entries (forest q)) = pending q.
  Proof. Admitted. (* STUB *)
  Lemma F2_ranks : forall P q, wf q -> pending q <= P ->
    ranks (forest q) <= Nat.log2 P + 1.
  Proof. Admitted. (* STUB *)
  Lemma F3_stale_push : forall p x q, wf q -> stale (push p x q) <= S (stale q).
  Proof. Admitted. (* STUB *)
  Lemma F4_skip : forall q q1, wf q -> pop_step q = inl q1 ->
    wf q1 /\ size q1 = size q /\ pending q = S (pending q1).
  Proof. Admitted. (* STUB *)
  Lemma F5_skip_bounded : forall w q q1, wf q -> bounded w q ->
    pop_step q = inl q1 -> bounded w q1.
  Proof. Admitted. (* STUB *)
  Lemma F6_phi_bounded : forall P w q, wf q -> bounded w q ->
    phi P w q = stale_phi P w q.
  Proof. Admitted. (* STUB *)
  Lemma F7_stop : forall q r, wf q -> pop_step q = inr r -> pop q = r.
  Proof. Admitted. (* STUB *)
  Lemma F8_push_bounded : forall w p x q, wf q -> bounded w q ->
    N.size_nat p + Pos.size_nat x <= w -> bounded w (push p x q).
  Proof. Admitted. (* STUB *)

  Lemma T1_insert : forall P w p x q,
    (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_insert p x (forest q) <= k_insert * N.of_nat (unit_pq P w))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_remove_min : forall P w q,
    (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_remove_min (forest q) <= k_remove * N.of_nat (unit_pq P w))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_skip_credit : forall P w q q1,
    (wf q -> bounded w q -> (pending q <= P)%nat -> pop_step q = inl q1 ->
    T_pop_step q + phi P w q1 + 1 <= phi P w q)%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_stop_credit : forall P w q r,
    (wf q -> bounded w q -> (pending q <= P)%nat -> pop_step q = inr r ->
    T_pop_step q + output_phi P w r <= k_step * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_pop_bounded : forall P w q,
    (wf q -> bounded w q -> (pending q <= P)%nat ->
    T_pop q + output_phi P w (pop q) <=
      k_driver * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof. Admitted. (* STUB *)
  Lemma T6_push_bounded : forall P w p x q,
    (wf q -> bounded w q -> (pending q < P)%nat ->
    (N.size_nat p + Pos.size_nat x <= w)%nat ->
    T_push p x q + phi P w (push p x q) <=
      (k_insert + k_step + k_credit) * N.of_nat (unit_pq P w) + phi P w q)%N.
  Proof. Admitted. (* STUB *)
End HeapT.
