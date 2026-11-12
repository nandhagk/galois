(** * Priority worklist computation

    The solver prepares row and reader indexes and tracks live queue entries.
    For example, repeated reads by one row enqueue that row once per change.
    Builds on: Fixpoint.WorklistSig and Base.Loop. *)
From Stdlib Require Import List NArith PArith.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import MapSig Trie HeapSig Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import DigraphSig WtoSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig PolicySig ScheduleSig WorklistSig.
Import List.ListNotations.

Module WorklistCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (P : POLICY_OPS L) (Q : PQ_OPS) <: SOLVER_OPS L S.
  Definition state := worklist_state S.key L.t S.row Q.t.
  Definition row_at (s : state) id := trie_get id (ws_rows s).
  Definition readers (s : state) c :=
    match trie_get c (ws_readers s) with Some ids => ids | None => [] end.
  Definition after_pop (s : state) (id : positive) (q : Q.t) : state :=
    WorklistState (ws_store s) (ws_counters s) q
      (PTrieCode.remove id (ws_live s)) (ws_rows s) (ws_readers s).
  Definition row_ids p := wl_ids_from (length (S.rows p)) 1%positive.
  Definition priority (pol : policy L.wparam) c :=
    match trie_get c (prio pol) with Some n => n | None => 1%positive end.
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
  Definition enqueue p pol ids (s : state) : state :=
    let ql := fold_left (fun ql id =>
      match trie_get id (snd ql), row_at s id with
      | None, Some r =>
        (Q.push (N.pos (priority pol (S.key_code (S.target p r)))) id (fst ql),
         PTrieCode.set id tt (snd ql))
      | _, _ => ql
      end) ids (ws_queue s, ws_live s) in
    WorklistState (ws_store s) (ws_counters s) (fst ql) (snd ql)
      (ws_rows s) (ws_readers s).
  Definition prepare p pol : state :=
    let ids := row_ids p in
    let idx := fold_right (index_row p) (Empty, Empty) (combine ids (S.rows p)) in
    enqueue p pol ids
      (WorklistState Empty Empty Q.empty Empty (fst idx) (snd idx)).
  Definition eval_row p r m :=
    eval_query (S.resume p) (look_or S.key_code L.bot m)
      (Datatypes.S (length (S.deps p r))) (S.start p r).
  Definition update_one p pol (s : state) (xa : S.key * L.t) : state :=
    let '(x, a) := xa in
    let c := S.key_code x in
    let old := look_or S.key_code L.bot (ws_store s) x in
    if L.leb a old then s else
    let cnt := match trie_get c (ws_counters s) with Some n => n | None => 0 end in
    let ac := P.update pol c cnt old a in
    let ids := readers s c in
    enqueue p pol ids
      (WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
        (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
        (ws_rows s) (ws_readers s)).
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
            (after_pop s id q))
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
    <: WORKLIST_T L S Sched B.
  Include WorklistCode L S P Q.
  TimeFun row_at.
  TimeFun readers.
  TimeFun after_pop.
  TimeFun row_ids.
  TimeFun priority.
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
      N.of_nat ((Nat.log2 (C p) + 1) * (S.kw p + 1)))%N.
  Definition prep (p : S.prog) : nat :=
    (C p + D p) * (S.kw p + Nat.log2 (C p) + 1).
  Definition rounds (p : S.prog) (pol : policy L.wparam) : nat :=
    1 + fold_right Nat.add 0
      (List.map (fun ch => delay (snd ch) + B.wmax p (wp pol) + 2)
        (PTrieCode.elements (heads pol))).
  Definition fits (p : S.prog) (pol : policy L.wparam) : Prop :=
    S.wf p /\ Sched.cuts p pol = true.
  Definition work (p : S.prog) (pol : policy L.wparam) : N :=
    (N.of_nat (prep p) + N.of_nat ((C p + D p) * rounds p pol) * unit p)%N.
  Definition widening_free (pol : policy L.wparam) : Prop :=
    forall c, trie_get c (heads pol) = None.
  Definition key_support (p : S.prog) : list positive :=
    nodup Pos.eq_dec (List.map S.key_code
      (flat_map (fun r => S.writes p r ++ S.deps p r) (S.rows p))).
  Definition reader_degree (p : S.prog) (x : positive) : nat :=
    length (filter (fun r => existsb
      (fun y => Pos.eqb x (S.key_code y)) (S.deps p r)) (S.rows p)).
  Definition head_allowance (p : S.prog) (pol : policy L.wparam)
      (x : positive) : nat :=
    match trie_get x (heads pol) with
    | Some cfg => delay cfg + B.wmax p (wp pol) + 2
    | None => 0
    end.
  Definition all_heads (p : S.prog) (pol : policy L.wparam) : Prop :=
    forall x, In x (key_support p) ->
      exists cfg, trie_get x (heads pol) = Some cfg.
  Definition all_head_work (p : S.prog) (pol : policy L.wparam) : N :=
    (N.of_nat (prep p) + N.of_nat ((C p + fold_right Nat.add 0
      (List.map (fun x => head_allowance p pol x * reader_degree p x)
        (key_support p)))%nat) * unit p)%N.
  Definition fuel_for (p : S.prog) (pol : policy L.wparam) : N := work p pol.
  Definition c_wl : N := 1%N. (* STUB *)
  Definition c_solve : N := c_wl.

  Lemma T_run_le : forall p pol fuel, fits p pol ->
    (T_run p pol fuel <= c_wl * (work p pol + N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma run_enough : forall p pol fuel, fits p pol -> (fuel_for p pol <= fuel)%N ->
    exists m, run p pol fuel = Solved m.
  Proof. Admitted. (* STUB *)
  Lemma T_run_height_le : forall p pol fuel (rk : L.t -> nat) h,
    S.wf p -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    (T_run p pol fuel <= c_wl *
      (N.of_nat (prep p) + N.of_nat (C p + h * D p) * unit p +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_run_all_heads_le : forall p pol fuel, S.wf p -> all_heads p pol ->
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
