(** * Priority worklist computation

    The solver prepares row and reader indexes and tracks live queue entries.
    For example, repeated reads by one row enqueue that row once per change.
    Builds on: Fixpoint.WorklistSig and Base.Loop. *)
From Stdlib Require Import List NArith PArith.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import Code MapSig Trie HeapSig Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import DigraphSig WtoSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig PolicySig ScheduleSig WorklistSig.
Import List.ListNotations.
Import Code.List.

Module Pos.
  TimeFun Stdlib.PArith.BinPos.Pos.max.
  TimeFun Stdlib.PArith.BinPos.Pos.min.
End Pos.

Module WorklistCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (P : POLICY_OPS L) (Q : PQ_OPS) <: SOLVER_OPS L S.
  Definition state := worklist_state S.key L.t S.row Q.t.
  Definition row_at (s : state) id := trie_get id (ws_rows s).
  Definition readers (s : state) c :=
    match trie_get c (ws_readers s) with Some ids => ids | None => [] end.
  Definition arm (c : positive) (s : state) : state :=
    WorklistState (ws_store s) (ws_counters s) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (PTrieCode.set c tt (ws_armed s)) (ws_ranks s).
  Definition after_pop p (s : state) (id : positive) (q : Q.t) : state :=
    let armed := match row_at s id with
      | None => ws_armed s
      | Some r => fold_left (fun acc x => PTrieCode.remove (S.key_code x) acc)
          (S.deps p r) (ws_armed s)
      end in
    WorklistState (ws_store s) (ws_counters s) q
      (PTrieCode.remove id (ws_live s)) (ws_rows s) (ws_readers s) armed (ws_ranks s).
  Definition row_ids p := wl_ids_from (length (S.rows p)) 1%positive.
  Definition priority (pol : policy L.wparam) c :=
    match trie_get c (prio pol) with Some n => n | None => 1%positive end.
  Definition top_rank_code p (pol : policy L.wparam) :=
    Pos.succ (fold_right (fun x acc => Pos.max (priority pol (S.key_code x)) acc)
      1%positive (flat_map (fun r => S.target p r :: S.sides p r ++ S.deps p r) (S.rows p))).
  Definition rank_with_top p (pol : policy L.wparam) top (r : S.row) :=
    fold_right (fun y acc =>
      let c := S.key_code y in
      match trie_get c (heads pol) with
      | Some _ => acc
      | None => Pos.min (priority pol c) acc
      end) top (S.target p r :: S.sides p r).
  Definition add_reader (id c : positive) (m : ptrie (list positive)) :=
    PTrieCode.set c (id :: match trie_get c m with Some ids => ids | None => [] end) m.
  Definition index_row p (ir : positive * S.row) (idx : ptrie S.row * ptrie (list positive)) :=
    let '(id, r) := ir in
    let keys := fold_left (fun seen x =>
      let c := S.key_code x in
      match trie_get c seen with Some _ => seen | None => PTrieCode.set c tt seen end)
      (S.deps p r) Empty in
    (PTrieCode.set id r (fst idx),
     fold_right (fun kv m => add_reader id (fst kv) m) (snd idx) (PTrieCode.elements keys)).
  Definition enqueue (p : S.prog) (pol : policy L.wparam) ids (s : state) : state :=
    let ql := fold_left (fun ql id =>
      match trie_get id (snd ql), row_at s id with
      | None, Some r =>
        (Q.push (N.pos (match trie_get id (ws_ranks s) with
          | Some rank => rank
          | None => 1%positive
          end)) id (fst ql),
         PTrieCode.set id tt (snd ql))
      | _, _ => ql
      end) ids (ws_queue s, ws_live s) in
    WorklistState (ws_store s) (ws_counters s) (fst ql) (snd ql)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s).
  Definition prepare p pol : state :=
    let ids := row_ids p in
    let idx := fold_right (index_row p) (Empty, Empty) (combine ids (S.rows p)) in
    let top := top_rank_code p pol in
    let ranks := fold_right (fun ir acc =>
      PTrieCode.set (fst ir) (rank_with_top p pol top (snd ir)) acc)
      Empty (combine ids (S.rows p)) in
    enqueue p pol ids
      (WorklistState Empty Empty Q.empty Empty (fst idx) (snd idx) Empty ranks).
  Definition eval_row p r m :=
    eval_query (S.resume p) (look_or S.key_code L.bot m)
      (Datatypes.S (length (S.deps p r))) (S.start p r).
  Definition update_one p pol (s : state) (xa : S.key * L.t) : state :=
    let '(x, a) := xa in
    let c := S.key_code x in
    let old := look_or S.key_code L.bot (ws_store s) x in
    if L.leb a old then s else
    let cnt := match trie_get c (ws_counters s) with Some n => n | None => 0%N end in
    let ac := P.update pol c cnt old a in
    let s1 := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
        (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
        (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s) in
    match trie_get c (ws_armed s) with
    | Some _ => s1
    | None => arm c (enqueue p pol (readers s c) s1)
    end.
  Definition step p pol (s : state) : state + outcome (kmap S.key L.t) :=
    match Q.pop (ws_queue s) with
    | None => inr (Solved (ws_store s))
    | Some (_, id, q) =>
      match row_at s id with
      | None => inr (Rejected Bad_policy)
      | Some r =>
        match eval_row p r (ws_store s) with
        | None => inr (Rejected Check_failed)
        | Some (a, ss) => inl (fold_left (update_one p pol)
            ((S.target p r, a) :: ss)
            (after_pop p s id q))
        end
      end
    end.
  Definition run p pol fuel :=
    match loopN (step p pol) fuel (prepare p pol) with
    | inl s => OutOfFuel (ws_store s)
    | inr result => result
    end.
End WorklistCode.

Module WorklistT (L : WLATTICE_T) (S : SYSTEM_T L) (P : POLICY_T L)
    (Q : PQ_T) (G : DIGRAPH_T) (W : WTO_T)
    (Sched : SCHEDULE_T L S G W) (B : BUDGET L S)
    <: WORKLIST_ALL L S P Q G W Sched B.
  Include WorklistCode L S P Q.
  Definition reference_state := wl_state S.key L.t Q.t.
  Definition source_row (p : S.prog) (id : positive) : option S.row :=
    nth_error (S.rows p) (Pos.to_nat id - 1).
  Definition source_readers (p : S.prog) (c : positive) : list positive :=
    filter (fun id => match source_row p id with
      | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      | None => false
      end) (row_ids p).
  Definition reference_enqueue (p : S.prog) (pol : policy L.wparam)
      (ids : list positive) (s : reference_state) : reference_state :=
    WlState (wl_store s) (wl_counters s)
      (fold_left (fun q id =>
        match Q.prio q id, source_row p id with
        | None, Some r => Q.push (N.pos (rank_with_top p pol (top_rank_code p pol) r)) id q
        | _, _ => q
        end) ids (wl_queue s)).
  Definition reference_update (p : S.prog) (pol : policy L.wparam)
      (s : reference_state) (xa : S.key * L.t) : reference_state :=
    let '(x, a) := xa in
    let c := S.key_code x in
    let old := look_or S.key_code L.bot (wl_store s) x in
    if L.leb a old then s else
    let cnt := match trie_get c (wl_counters s) with
      | Some n => n
      | None => 0%N
    end in
    let ac := P.update pol c cnt old a in
    let s1 := WlState (PTrieCode.set c (x, fst ac) (wl_store s))
      (PTrieCode.set c (snd ac) (wl_counters s)) (wl_queue s) in
    reference_enqueue p pol (source_readers p c) s1.
  Definition reference_step (p : S.prog) (pol : policy L.wparam)
      (s : reference_state) : reference_state + outcome (kmap S.key L.t) :=
    match Q.pop (wl_queue s) with
    | None => inr (Solved (wl_store s))
    | Some (_, id, q) =>
      match source_row p id with
      | None => inr (Rejected Bad_policy)
      | Some r =>
        match eval_row p r (wl_store s) with
        | None => inr (Rejected Check_failed)
        | Some (a, ss) => inl (fold_left (reference_update p pol)
            ((S.target p r, a) :: ss) (WlState (wl_store s) (wl_counters s) q))
        end
      end
    end.
  TimeFun row_at.
  TimeFun readers.
  TimeFun arm.
  TimeFun after_pop.
  TimeFun row_ids.
  TimeFun priority.
  TimeFun top_rank_code.
  TimeFun rank_with_top.
  TimeFun add_reader.
  TimeFun index_row.
  TimeFun enqueue.
  TimeFun prepare.
  TimeFun eval_row.
  TimeFun update_one.
  TimeFun step.
  TimeFun run.

  Definition C (p : S.prog) : nat := length (S.rows p).
  Definition D (p : S.prog) : nat := fold_right Nat.add 0
    (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
      (S.rows p)).
  Definition unit (p : S.prog) : N :=
    (S.row_work p (B.vsize p) + L.c_lat * N.of_nat (B.vsize p + 1) +
      N.of_nat ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)))%N.
  Definition prep (p : S.prog) : nat :=
    (C p + D p) * (S.kw p + Nat.log2 (C p) + 1).
  Definition rounds (p : S.prog) (pol : policy L.wparam) : nat :=
    1 + fold_right Nat.add 0
      (List.map (fun ch => N.to_nat (delay (snd ch)) + B.wmax p (wp pol) + 2)
        (PTrieCode.elements (heads pol))).

  Definition widening_free (pol : policy L.wparam) : Prop :=
    forall c, trie_get c (heads pol) = None.
  Definition key_support (p : S.prog) : list positive :=
    nodup Pos.eq_dec (List.map S.key_code
      (flat_map (fun r => S.writes p r ++ S.deps p r) (S.rows p))).
  Definition top_rank (p : S.prog) (pol : policy L.wparam) : positive :=
    Pos.succ (fold_right Pos.max 1%positive (List.map (priority pol) (key_support p))).
  Definition row_rank (p : S.prog) (pol : policy L.wparam) (r : S.row) : positive :=
    fold_right (fun y acc =>
      let c := S.key_code y in
      match trie_get c (heads pol) with
      | Some _ => acc
      | None => Pos.min (priority pol c) acc
      end) (top_rank p pol) (S.writes p r).
  Definition prio_ok (p : S.prog) (pol : policy L.wparam) : Prop :=
    forall c, In c (key_support p) ->
      Pos.size_nat (match trie_get c (prio pol) with Some n => n | None => 1%positive end)
        <= S.kw p + 1.
  Definition fits (p : S.prog) (pol : policy L.wparam) : Prop :=
    S.wf p /\ Sched.cuts p pol = true /\ prio_ok p pol.
  Definition DW (p : S.prog) : nat := fold_right Nat.add 0
    (List.map (fun r => (length (S.deps p r) + 1) *
      (length (S.deps p r) + length (S.sides p r) + 1)) (S.rows p)).
  Definition reader_weight (p : S.prog) (x : positive) : nat :=
    fold_right Nat.add 0 (List.map
      (fun r => if existsb (fun y => Pos.eqb x (S.key_code y)) (S.deps p r)
        then length (S.deps p r) + length (S.sides p r) + 1 else 0) (S.rows p)).
  Definition reader_degree (p : S.prog) (x : positive) : nat :=
    length (filter (fun r => existsb
      (fun y => Pos.eqb x (S.key_code y)) (S.deps p r)) (S.rows p)).
  Definition head_allowance (p : S.prog) (pol : policy L.wparam)
      (x : positive) : nat :=
    match trie_get x (heads pol) with
    | Some cfg => N.to_nat (delay cfg) + B.wmax p (wp pol) + 2
    | None => 0
    end.
  Definition all_heads (p : S.prog) (pol : policy L.wparam) : Prop :=
    forall x, In x (key_support p) ->
      exists cfg, trie_get x (heads pol) = Some cfg.
  Definition all_head_work (p : S.prog) (pol : policy L.wparam) : N :=
    (N.of_nat (prep p) + N.of_nat ((D p + fold_right Nat.add 0
      (List.map (fun x => head_allowance p pol x * reader_weight p x)
        (key_support p)))%nat) * unit p +
      N.of_nat (rounds p pol) * (N.of_nat (Nat.log2 (rounds p pol) + 1) +
        L.c_lat * N.of_nat ((2 * B.wunits p + 1) * L.wsize (wp pol))))%N.
  Definition c_wl : N := 1%N. (* STUB *)
  Definition k_prepare : N := 1%N. (* STUB *)
  Definition k_eval : N := 1%N. (* STUB *)
  Definition k_update : N := 1%N. (* STUB *)
  Definition k_credit : N := 1%N. (* STUB *)
  Definition k_round : N := 1%N. (* STUB *)
  Definition k_loop : N := 1%N. (* STUB *)
  Definition k_fuel : N := 1%N. (* STUB *)
  Definition c_solve : N := c_wl.

  Definition work (p : S.prog) (pol : policy L.wparam) : N :=
    (N.of_nat (prep p) + N.of_nat ((C p + D p) * rounds p pol) * unit p +
      N.of_nat (rounds p pol) * (N.of_nat (Nat.log2 (rounds p pol) + 1) +
        L.c_lat * N.of_nat ((2 * B.wunits p + 1) * L.wsize (wp pol))))%N.
  Definition fuel_for (p : S.prog) (pol : policy L.wparam) : N :=
    (k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Definition look (s : state) (x : S.key) : L.t :=
    look_or S.key_code L.bot (ws_store s) x.
  Definition counter (s : state) (c : positive) : N :=
    match trie_get c (ws_counters s) with Some n => n | None => 0%N end.
  Definition reference_look (s : reference_state) (x : S.key) : L.t :=
    look_or S.key_code L.bot (wl_store s) x.
  Definition reference_counter (s : reference_state) (c : positive) : N :=
    match trie_get c (wl_counters s) with Some n => n | None => 0%N end.
  Definition metadata (p : S.prog) (s : state) : Prop :=
    (forall id, row_at s id = source_row p id) /\
    (forall c, readers s c = source_readers p c).
  Definition live_agrees (s : state) : Prop :=
    forall id, trie_get id (ws_live s) = Some tt <->
      exists pr, Q.prio (ws_queue s) id = Some pr.
  Definition queue_exact (s : state) : Prop :=
    Q.pending (ws_queue s) = N.to_nat (Q.size (ws_queue s)).
  Definition prepared (p : S.prog) (pol : policy L.wparam) (s : state) : Prop :=
    metadata p s /\ live_agrees s /\ Q.wf (ws_queue s) /\ queue_exact s /\
    (forall c id, trie_get c (ws_armed s) = Some tt -> In id (readers s c) ->
      exists pr, Q.prio (ws_queue s) id = Some pr) /\
    (forall id r, row_at s id = Some r ->
      trie_get id (ws_ranks s) = Some (row_rank p pol r)).
  Definition view_result (result : state + outcome (kmap S.key L.t))
      : reference_state + outcome (kmap S.key L.t) :=
    match result with
    | inl s => inl (wl_view s)
    | inr result => inr result
    end.
  Definition weight (p : S.prog) (id : positive) : nat :=
    match source_row p id with
    | Some r => length (S.deps p r) + length (S.sides p r) + 1
    | None => 0%nat
    end.
  Definition degree (p : S.prog) (x : positive) : nat := length (source_readers p x).
  (** Only an unarmed key's strict change pushes its reader bucket. *)
  Definition push_work (p : S.prog) (s : state) (x : S.key) (a : L.t) : nat :=
    if L.leb a (look s x) then 0 else
    match trie_get (S.key_code x) (ws_armed s) with
    | Some _ => 0
    | None => degree p (S.key_code x)
    end.
  Definition weighted_degree (p : S.prog) (x : positive) : nat :=
    fold_right Nat.add 0 (List.map (weight p) (source_readers p x)).
  Definition queue_credit (p : S.prog) (s : state) : nat :=
    fold_right Nat.add 0 (List.map
      (fun id => match Q.prio (ws_queue s) id with
        | Some _ => weight p id
        | None => 0
        end) (row_ids p)).
  Definition queue_phi (p : S.prog) (s : state) : N :=
    Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) (ws_queue s).
  Definition structural (p : S.prog) (pol : policy L.wparam) (s : state) : Prop :=
    Q.wf (ws_queue s) /\
    Q.fits (S.kw p + Nat.log2 (C p) + 3) (ws_queue s) /\ Q.pending (ws_queue s) <= C p /\
    (forall pr id, Q.prio (ws_queue s) id = Some pr ->
      In id (row_ids p) /\ exists r, source_row p id = Some r /\
        pr = N.pos (row_rank p pol r)).
  Definition invariant (p : S.prog) (pol : policy L.wparam) (s : state) : Prop :=
    structural p pol s /\ (forall x, B.inv p (look s x)) /\ prepared p pol s.
  Definition reachable (p : S.prog) (pol : policy L.wparam) (s : state) : Prop :=
    exists xs, wl_path (step p pol) (prepare p pol) xs s.
  (** Every row outside the queue accepts the current store. *)
  Definition accepted (p : S.prog) (s : state) : Prop :=
    forall id r, source_row p id = Some r -> Q.prio (ws_queue s) id = None ->
      row_ok L.leb (look s) (S.target p r) (S.eval p r (look s)) = true.
  Definition trace_cost (p : S.prog) (pol : policy L.wparam) (xs : list state) : N :=
    fold_right N.add 0%N (List.map (T_step p pol) xs).
  Definition popped_ids (xs : list state) : list positive :=
    flat_map (fun s => match Q.pop (ws_queue s) with
      | Some (_, id, _) => id :: nil
      | None => nil
      end) xs.
  Definition popped_ranks (xs : list state) : list N :=
    flat_map (fun s => match Q.pop (ws_queue s) with
      | Some (pr, _, _) => pr :: nil
      | None => nil
      end) xs.
  Definition heads_unchanged (pol : policy L.wparam) (s s1 : state) : Prop :=
    forall c cfg, trie_get c (heads pol) = Some cfg -> counter s1 c = counter s c.
  Definition stable_segment (p : S.prog) (pol : policy L.wparam)
      (xs : list state) : Prop :=
    forall s s1, In s xs -> step p pol s = inl s1 -> heads_unchanged pol s s1.
  Definition head_events (pol : policy L.wparam) (s s1 : state) : nat :=
    fold_right Nat.add 0 (List.map
      (fun ch => N.to_nat (counter s1 (fst ch) - counter s (fst ch)))
      (PTrieCode.elements (heads pol))).
  Definition head_unit (p : S.prog) (pol : policy L.wparam) : N :=
    (N.of_nat (Nat.log2 (rounds p pol) + 1) +
      L.c_lat * N.of_nat ((2 * B.wunits p + 1) * L.wsize (wp pol)))%N.
  Definition strict_head_work (pol : policy L.wparam) (s : state)
      (x : S.key) (a : L.t) : N :=
    if L.leb a (look s x) then 0%N else
      match trie_get (S.key_code x) (heads pol) with
      | Some _ => (N.of_nat (N.size_nat (counter s (S.key_code x))) +
          L.c_lat * N.of_nat ((L.wunits (look s x) + L.wunits a + 1) *
            L.wsize (wp pol)))%N
      | None => 0%N
      end.
  Definition height_phi (p : S.prog) (rk : L.t -> nat) (h : nat) (s : state) : N :=
    (k_credit * N.of_nat ((queue_credit p s + fold_right Nat.add 0
      (List.map (fun c =>
        let a := match trie_get c (ws_store s) with
          | Some (_, a) => a
          | None => L.bot
          end in
        (h - rk a) * weighted_degree p c) (key_support p)))%nat) *
      unit p + queue_phi p s)%N.
  Definition all_head_phi (p : S.prog) (pol : policy L.wparam) (s : state) : N :=
    (k_credit * N.of_nat ((queue_credit p s + fold_right Nat.add 0
      (List.map (fun c => (head_allowance p pol c - N.to_nat (counter s c)) *
        weighted_degree p c) (key_support p)))%nat) * unit p + queue_phi p s +
      k_credit * N.of_nat ((fold_right Nat.add 0
        (List.map (fun c => head_allowance p pol c - N.to_nat (counter s c))
          (key_support p)))%nat) * head_unit p pol)%N.
  Definition round_phi (p : S.prog) (pol : policy L.wparam)
      (used : nat) (s : state) : N :=
    (k_round * N.of_nat ((rounds p pol - used) * (C p + D p) + queue_credit p s) *
      unit p + queue_phi p s)%N.
  Definition output_cost (p : S.prog) (pol : policy L.wparam)
      (outs : list (S.key * L.t)) (s : state) : N :=
    snd (fold_left (fun sn xa =>
      (update_one p pol (fst sn) xa,
        (snd sn + T_update_one p pol (fst sn) xa)%N)) outs (s, 0%N)).
  (** Binary enumeration retains the original observable identifiers and occurrence order. *)
  Lemma F0_row_ids : forall p,
    row_ids p = List.map Pos.of_succ_nat (seq 0 (C p)).
  Proof. Admitted. (* STUB *)
  (** Projecting a prepared state retains every lookup in the original store. *)
  Lemma F0_view_look : forall s x, reference_look (wl_view s) x = look s x.
  Proof. Admitted. (* STUB *)
  (** Projecting a prepared state retains every strict-update counter. *)
  Lemma F0_view_counter : forall s c, reference_counter (wl_view s) c = counter s c.
  Proof. Admitted. (* STUB *)
  (** Numbered lookup agrees with the corresponding original row occurrence. *)
  Lemma F1_numbering : forall p n,
    source_row p (Pos.of_succ_nat n) = nth_error (S.rows p) n.
  Proof. Admitted. (* STUB *)
  (** Reader buckets retain every reading row occurrence once. *)
  Lemma F2_readers : forall p c,
    source_readers p c = filter (fun id => match source_row p id with
      | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      | None => false
      end) (row_ids p).
  Proof. Admitted. (* STUB *)
  (** Evaluation observes the current store through the system's public evaluator. *)
  Lemma F3_eval : forall p r m,
    eval_row p r m = S.eval p r (look_or S.key_code L.bot m).
  Proof. Admitted. (* STUB *)
  (** Preparation starts at bottom and zero counters and establishes queue and value invariants. *)
  Lemma F4_prepare : forall p pol, S.wf p -> prio_ok p pol ->
    invariant p pol (prepare p pol) /\
    (forall x, look (prepare p pol) x = L.bot) /\
    (forall c, counter (prepare p pol) c = 0%N) /\
    (forall id, In id (row_ids p) ->
      exists pr, Q.prio (ws_queue (prepare p pol)) id = Some pr).
  Proof. Admitted. (* STUB *)
  (** Enqueue changes the queue alone and guards every push by live absence. *)
  Lemma F5_enqueue : forall p pol ids s,
    wl_store (reference_enqueue p pol ids s) = wl_store s /\
    wl_counters (reference_enqueue p pol ids s) = wl_counters s /\
    wl_queue (reference_enqueue p pol ids s) = fold_left
      (fun q id => match Q.prio q id, source_row p id with
        | None, Some r => Q.push (N.pos (row_rank p pol r)) id q
        | _, _ => q
        end) ids (wl_queue s).
  Proof. Admitted. (* STUB *)
  (** An update writes the policy result and enqueues its readers after a strict value change. *)
  Lemma F6_update : forall p pol s x a,
    let c := S.key_code x in
    let ac := P.update pol c (reference_counter s c) (reference_look s x) a in
    let s1 := WlState (PTrieCode.set c (x, fst ac) (wl_store s))
      (PTrieCode.set c (snd ac) (wl_counters s)) (wl_queue s) in
    reference_update p pol s (x, a) =
      if L.leb a (reference_look s x) then s else
        reference_enqueue p pol (source_readers p c) s1.
  Proof. Admitted. (* STUB *)
  (** Each callback pops one row and processes its primary and side outputs in occurrence order. *)
  Lemma F7_step : forall p pol s,
    reference_step p pol s = match Q.pop (wl_queue s) with
    | None => inr (Solved (wl_store s))
    | Some (_, id, q1) =>
      match source_row p id with
      | None => inr (Rejected Bad_policy)
      | Some r =>
        match eval_row p r (wl_store s) with
        | None => inr (Rejected Check_failed)
        | Some (a, ss) => inl (fold_left (reference_update p pol)
            ((S.target p r, a) :: ss) (WlState (wl_store s) (wl_counters s) q1))
        end
      end
    end.
  Proof. Admitted. (* STUB *)
  (** Indexed lookup reads the prepared row table without traversing the source rows. *)
  Lemma F1_row_at : forall s id, row_at s id = trie_get id (ws_rows s).
  Proof. Admitted. (* STUB *)
  (** Reader lookup reads the prepared bucket and maps an absent bucket to the empty list. *)
  Lemma F2_reader_at : forall s c,
    readers s c = match trie_get c (ws_readers s) with Some ids => ids | None => nil end.
  Proof. Admitted. (* STUB *)
  (** Preparation establishes all cache and live facts within the solver. *)
  Lemma F4_metadata : forall p pol, prepared p pol (prepare p pol).
  Proof. Admitted. (* STUB *)
  (** Enqueue preserves the immutable indexes and the original value components. *)
  Lemma F5_fields : forall p pol ids s,
    ws_store (enqueue p pol ids s) = ws_store s /\
    ws_counters (enqueue p pol ids s) = ws_counters s /\
    ws_rows (enqueue p pol ids s) = ws_rows s /\
    ws_readers (enqueue p pol ids s) = ws_readers s /\
    ws_armed (enqueue p pol ids s) = ws_armed s /\
    ws_ranks (enqueue p pol ids s) = ws_ranks s.
  Proof. Admitted. (* STUB *)
  (** Guarded pushes update the queue and live set together in occurrence order. *)
  Lemma F5_indexed : forall p pol ids s,
    (ws_queue (enqueue p pol ids s), ws_live (enqueue p pol ids s)) =
    fold_left (fun ql id => match trie_get id (snd ql), row_at s id with
      | None, Some r =>
        (Q.push (N.pos (match trie_get id (ws_ranks s) with
            | Some rank => rank
            | None => 1%positive
            end)) id (fst ql),
          PTrieCode.set id tt (snd ql))
      | _, _ => ql
      end) ids (ws_queue s, ws_live s).
  Proof. Admitted. (* STUB *)
  (** Enqueue agrees with the original helper after projection from prepared states. *)
  Lemma F5_agreement : forall p pol ids s, prepared p pol s ->
    wl_view (enqueue p pol ids s) = reference_enqueue p pol ids (wl_view s).
  Proof. Admitted. (* STUB *)
  (** Enqueue maintains the metadata and live facts that justify projected agreement. *)
  Lemma F5_prepared : forall p pol ids s, prepared p pol s ->
    prepared p pol (enqueue p pol ids s).
  Proof. Admitted. (* STUB *)
  (** Indexed updates retain metadata while writing the policy result and enqueueing readers. *)
  Lemma F6_indexed : forall p pol s x a,
    let c := S.key_code x in
    let ac := P.update pol c (counter s c) (look s x) a in
    let s1 := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
      (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s) in
    update_one p pol s (x, a) =
      if L.leb a (look s x) then s else
      match trie_get c (ws_armed s) with
      | Some _ => s1
      | None => arm c (enqueue p pol (readers s c) s1)
      end.
  Proof. Admitted. (* STUB *)
  (** Indexed updates preserve both tables independently of the input cache validity. *)
  Lemma F6_tables : forall p pol s xa,
    ws_rows (update_one p pol s xa) = ws_rows s /\
    ws_readers (update_one p pol s xa) = ws_readers s.
  Proof. Admitted. (* STUB *)
  (** Every update has the original projected behavior on prepared states. *)
  Lemma F6_agreement : forall p pol s xa, prepared p pol s ->
    wl_view (update_one p pol s xa) = reference_update p pol (wl_view s) xa.
  Proof. Admitted. (* STUB *)
  (** Every intermediate update maintains prepared-state agreement without client duties. *)
  Lemma F6_prepared : forall p pol s xa, prepared p pol s ->
    prepared p pol (update_one p pol s xa).
  Proof. Admitted. (* STUB *)
  (** A pop removes its live identifier and clears every reader flag used by that row. *)
  Lemma F7_indexed : forall p pol s,
    step p pol s = match Q.pop (ws_queue s) with
    | None => inr (Solved (ws_store s))
    | Some (_, id, q1) =>
      match row_at s id with
      | None => inr (Rejected Bad_policy)
      | Some r =>
        match eval_row p r (ws_store s) with
        | None => inr (Rejected Check_failed)
        | Some (a, ss) => inl (fold_left (update_one p pol)
            ((S.target p r, a) :: ss) (after_pop p s id q1))
        end
      end
    end.
  Proof. Admitted. (* STUB *)
  (** Popping preserves cache agreement and restores live agreement for the residual queue. *)
  Lemma F7_pop_prepared : forall p pol s pr id q1, prepared p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) ->
    prepared p pol (after_pop p s id q1).
  Proof. Admitted. (* STUB *)
  (** The full callback retains every observable behavior of the original callback. *)
  Lemma F7_agreement : forall p pol s, prepared p pol s ->
    view_result (step p pol s) = reference_step p pol (wl_view s).
  Proof. Admitted. (* STUB *)
  (** Continuing callbacks retain both tables and all prepared-state facts. *)
  Lemma F7_prepared : forall p pol s s1, prepared p pol s -> step p pol s = inl s1 ->
    prepared p pol s1 /\ ws_rows s1 = ws_rows s /\ ws_readers s1 = ws_readers s.
  Proof. Admitted. (* STUB *)
  (** The public solver is the binary-fuel loop over these callbacks. *)
  Lemma F8_run : forall p pol fuel,
    run p pol fuel = match loopN (step p pol) fuel (prepare p pol) with
    | inl s => OutOfFuel (ws_store s)
    | inr result => result
    end.
  Proof. Admitted. (* STUB *)
  (** The original three-field loop has the same public result for every fuel. *)
  Lemma F8_reference_run : forall p pol fuel,
    run p pol fuel =
    match loopN (reference_step p pol) fuel (wl_view (prepare p pol)) with
    | inl s => OutOfFuel (wl_store s)
    | inr result => result
    end.
  Proof. Admitted. (* STUB *)
  (** Every state reached by the public solver satisfies its internal preparation duties. *)
  Lemma F9_reachable_prepared : forall p pol s, reachable p pol s -> prepared p pol s.
  Proof. Admitted. (* STUB *)
  (** Prepared ranks equal each row's least non-head write priority. *)
  Lemma F4_rank_cache : forall p pol id r, row_at (prepare p pol) id = Some r ->
    trie_get id (ws_ranks (prepare p pol)) = Some (row_rank p pol r).
  Proof. Admitted. (* STUB *)
  (** Every continuing callback keeps the structural and client value invariants. *)
  Lemma F9_step_inv : forall p pol s s1, S.wf p -> invariant p pol s ->
    step p pol s = inl s1 -> invariant p pol s1.
  Proof. Admitted. (* STUB *)
  (** Each intermediate primary or side update keeps the same invariant. *)
  Lemma F9_update_inv : forall p pol s x a, S.wf p -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
    invariant p pol (update_one p pol s (x, a)).
  Proof. Admitted. (* STUB *)
  (** Reachable states satisfy every row outside their queue. *)
  Lemma F9_accepted : forall p pol s, S.wf p -> reachable p pol s -> accepted p s.
  Proof. Admitted. (* STUB *)

  (** W1 charges indexing, numbering and initial guarded enqueue to preparation. *)
  Lemma W1_prepare : forall p pol, fits p pol ->
    (T_prepare p pol <= k_prepare * (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Initial guarded pushes supply the potential consumed by later queue operations. *)
  Lemma W1_queue_phi : forall p pol, fits p pol ->
    (queue_phi p (prepare p pol) <= k_prepare * N.of_nat (C p + D p) * unit p)%N.
  Proof. Admitted. (* STUB *)
  (** W2 charges every dependency-resume occurrence on invariant stores. *)
  Lemma W2_eval : forall p pol r s, S.wf p -> In r (S.rows p) -> invariant p pol s ->
    (T_eval_row p r (ws_store s) <=
      k_eval * N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) * unit p)%N.
  Proof. Admitted. (* STUB *)
  (** Guarded enqueue pays each supplied reader occurrence even when it is already live. *)
  Lemma W3_enqueue : forall p pol ids s, S.wf p -> invariant p pol s ->
    incl ids (row_ids p) ->
    (T_enqueue p pol ids s + queue_phi p (enqueue p pol ids s) <=
      k_update * N.of_nat (length ids + 1) * unit p + queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** W3 keeps the value invariant and charges reader pushes against queue potential. *)
  Lemma W3_update : forall p pol s x a, S.wf p -> invariant p pol s -> B.inv p a ->
    In (S.key_code x) (key_support p) ->
    B.inv p (look (update_one p pol s (x, a)) x) /\
    (T_update_one p pol s (x, a) + queue_phi p (update_one p pol s (x, a)) <=
      k_update * N.of_nat (1 + push_work p s x a) * unit p +
      k_update * strict_head_work pol s x a + queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** Callback accounting retains every emitted occurrence and every intermediate update cost. *)
  Lemma W3_step : forall p pol s pr id q1 r a ss, S.wf p -> invariant p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) -> source_row p id = Some r ->
    eval_row p r (ws_store s) = Some (a, ss) ->
    (T_step p pol s <= k_loop * (Q.T_pop (ws_queue s) + T_row_at s id +
      T_eval_row p r (ws_store s) + S.T_target p r +
      N.of_nat ((length (S.deps p r) + 1) * (S.kw p + Nat.log2 (C p) + 1)) +
      output_cost p pol ((S.target p r, a) :: ss)
        (after_pop p s id q1) + N.of_nat (length ss) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** W4 spends weighted rank credit for each callback in a widening-free run. *)
  Lemma W4_credit : forall p pol rk h s s1, S.wf p -> prio_ok p pol -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    reachable p pol s -> step p pol s = inl s1 ->
    (T_step p pol s + height_phi p rk h s1 + 1 <= height_phi p rk h s)%N.
  Proof. Admitted. (* STUB *)
  (** Weighted source credit fits the public weighted incidence budget. *)
  Lemma W4_initial : forall p pol rk h, S.wf p -> prio_ok p pol -> widening_free pol ->
    (height_phi p rk h (prepare p pol) <=
      k_credit * N.of_nat (D p + h * DW p) * unit p + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)
  (** Cut edges make popped row ranks nondecreasing in a stable segment. *)
  Lemma W5_priority : forall p pol s xs last i j a b,
    fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> stable_segment p pol xs ->
    i < j -> nth_error (popped_ranks xs) i = Some a ->
    nth_error (popped_ranks xs) j = Some b -> (a <= b)%N.
  Proof. Admitted. (* STUB *)
  (** W5 uses cuts to bound each numbered row's visits between strict head updates. *)
  Lemma W5_round : forall p pol s xs last,
    fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> stable_segment p pol xs ->
    (forall id, count_occ Pos.eq_dec (popped_ids xs) id <= 1) /\
    (trace_cost p pol xs + queue_phi p last <=
      k_round * N.of_nat (C p + D p) * unit p + queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** A callback that ends a stable segment is charged to its strict head events. *)
  Lemma W5_boundary : forall p pol s s1, fits p pol -> reachable p pol s ->
    step p pol s = inl s1 -> 0 < head_events pol s s1 ->
    (T_step p pol s + 1 + queue_phi p s1 <=
      k_round * N.of_nat (head_events pol s s1) * N.of_nat (C p + D p) * unit p +
      k_round * N.of_nat (head_events pol s s1) * head_unit p pol +
      queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** W6 bounds every finite prefix's strict head events by the advertised round count. *)
  Lemma W6_rounds : forall p pol xs last, S.wf p -> prio_ok p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    head_events pol (prepare p pol) last + 1 <= rounds p pol /\
    (forall c, In c (key_support p) ->
      N.to_nat (counter last c) <= head_allowance p pol c).
  Proof. Admitted. (* STUB *)
  (** W7 charges arbitrary finite prefixes by partitioning at strict head events. *)
  Lemma W7_trace : forall p pol xs last, fits p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    (trace_cost p pol xs + N.of_nat (length xs) + queue_phi p last <=
      k_loop * work p pol + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)
  (** The visit count supplies fuel without charging abstract value sizes to fuel construction. *)
  Lemma W7_visits : forall p pol xs last, fits p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    (N.of_nat (length xs) < k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Stopping callbacks must solve and must fit the final driver budget. *)
  Lemma W7_stop : forall p pol s result, S.wf p -> prio_ok p pol -> reachable p pol s ->
    step p pol s = inr result ->
    (exists m, result = Solved m) /\ (T_step p pol s <= k_loop * (unit p + 1) + queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** Binary fuel charges the loop from finite-prefix accounting and the final callback. *)
  Lemma W7_loop : forall p pol fuel, fits p pol ->
    (T_loopN (step p pol) (T_step p pol) fuel (prepare p pol) <= k_loop *
      (work p pol + queue_phi p (prepare p pol) +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Fuel is chosen from the row-visit budget and includes the final empty pop. *)
  Lemma W7_fuel : forall p pol,
    (fuel_for p pol = k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Proof. Admitted. (* STUB *)
  (** W7 connects the derived solver time to preparation and the derived binary-loop time. *)
  Lemma W7_run : forall p pol fuel,
    (T_run p pol fuel <= k_loop * (T_prepare p pol +
      T_loopN (step p pol) (T_step p pol) fuel (prepare p pol) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** All-head credit decreases per callback without the stable-segment lemma. *)
  Lemma W7_all_heads_credit : forall p pol s s1, S.wf p -> prio_ok p pol -> all_heads p pol ->
    reachable p pol s -> step p pol s = inl s1 ->
    (T_step p pol s + all_head_phi p pol s1 + 1 <= all_head_phi p pol s)%N.
  Proof. Admitted. (* STUB *)
  (** The independent widening fallback needs weighted degree absorbed by its public budget. *)
  Lemma W7_all_heads_initial : forall p pol, S.wf p -> prio_ok p pol -> all_heads p pol ->
    (all_head_phi p pol (prepare p pol) <=
      k_credit * all_head_work p pol + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)
  (** Solved candidates satisfy every row. *)
  Lemma run_post : forall p pol fuel m, fits p pol -> run p pol fuel = Solved m ->
    S.post_solution p (look_or S.key_code L.bot m).
  Proof. Admitted. (* STUB *)
  (** Solved candidates satisfy the client value budget. *)
  Lemma run_inv : forall p pol fuel m, S.wf p -> run p pol fuel = Solved m ->
    forall x, B.inv p (look_or S.key_code L.bot m x).
  Proof. Admitted. (* STUB *)
  Lemma T_run_le : forall p pol fuel, fits p pol ->
    (T_run p pol fuel <= c_wl * (work p pol + N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma run_enough : forall p pol fuel, fits p pol -> (fuel_for p pol <= fuel)%N ->
    exists m, run p pol fuel = Solved m.
  Proof. Admitted. (* STUB *)
  Lemma T_run_height_le : forall p pol fuel (rk : L.t -> nat) h,
    S.wf p -> prio_ok p pol -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    (T_run p pol fuel <= c_wl *
      (N.of_nat (prep p) + N.of_nat (D p + h * DW p) * unit p +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_run_all_heads_le : forall p pol fuel, S.wf p -> prio_ok p pol -> all_heads p pol ->
    (T_run p pol fuel <= c_wl *
      (all_head_work p pol + N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma run_bigO : bigO
    (fun x : S.prog * policy L.wparam => fits (fst x) (snd x))
    (fun x => work (fst x) (snd x))
    (fun x => T_run (fst x) (snd x) (fuel_for (fst x) (snd x))).
  Proof. Admitted. (* STUB *)
End WorklistT.

(** The least-run proof needs queue and live-set agreement, well-formed stores and heaps,
    stable rows outside the queue, and agreement of the prepared index with the system. *)
