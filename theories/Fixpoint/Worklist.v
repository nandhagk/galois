(** * Priority worklist computation

    The solver prepares row and reader indexes and tracks live queue entries.
    For example, repeated reads by one row enqueue that row once per change.
    Builds on: Fixpoint.WorklistSig and Base.Loop. *)
From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import Code MapSig Trie HeapSig Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import DigraphSig WtoSig.
From Galois.Fixpoint Require Import Query SystemSig SolverSig PolicySig ScheduleSig WorklistSig.
Import List.ListNotations.
Import Code.List.

(** * Binary-loop and numbering facts *)

(** A positive identifier's bit width is its logarithm plus the leading bit. *)
Lemma pos_size_log2 : forall p,
  Pos.size_nat p = Nat.log2 (Pos.to_nat p) + 1.
Proof.
  induction p as [p IH|p IH|].
  - rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat p)) with (2 * Pos.to_nat p + 1) by lia.
    rewrite Nat.log2_succ_double by apply Pos2Nat.is_pos.
    cbn [Pos.size_nat]; lia.
  - rewrite Pos2Nat.inj_xO, Nat.log2_double by apply Pos2Nat.is_pos.
    cbn [Pos.size_nat]; lia.
  - reflexivity.
Qed.

(** The accessibility driver has the same outcomes as the corresponding unary fuel. *)
Lemma loopN_acc_fuel {St R : Type} (step : St -> St + R) :
  forall fs (H : Acc (@loopN_lt St) fs),
    loop loopN_lt (loopN_step step) fs H =
      loop_fuel step (N.to_nat (fst fs)) (snd fs).
Proof.
  intros fs H; induction H as [[fuel s] Hacc IH] using Acc_ind_dep.
  destruct fuel as [|p].
  - reflexivity.
  - assert (Hpos : 0 < N.to_nat (N.pos p)) by apply Pos2Nat.is_pos.
    assert (Hfuel : N.to_nat (N.pos p) = S (N.to_nat (N.pred (N.pos p)))).
    { rewrite N2Nat.inj_pred; lia. }
    cbn [fst snd]; rewrite Hfuel.
    cbn [loop loopN_step loop_fuel].
    destruct (step s) as [s1|result] eqn:Hstep; [apply IH|reflexivity].
Qed.

(** Binary and unary fuel select exactly the same callback outcomes. *)
Lemma loopN_fuel {St R : Type} (step : St -> St + R) : forall fuel s,
  loopN step fuel s = loop_fuel step (N.to_nat fuel) s.
Proof.
  intros fuel s; unfold loopN; apply loopN_acc_fuel.
Qed.

(** A state projection commutes with a fuelled loop when callbacks preserve its invariant. *)
Lemma loop_fuel_view {St Ref R : Type} (step : St -> St + R)
    (reference : Ref -> Ref + R) (view : St -> Ref) (Inv : St -> Prop) :
  (forall s, Inv s ->
    match step s with inl s1 => inl (view s1) | inr r => inr r end = reference (view s)) ->
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1) ->
  forall fuel s, Inv s ->
    match loop_fuel step fuel s with inl s1 => inl (view s1) | inr r => inr r end =
      loop_fuel reference fuel (view s).
Proof.
  intros Hview Hinv fuel; induction fuel as [|fuel IH]; intros s Hs.
  - reflexivity.
  - cbn [loop_fuel]; rewrite <- (Hview s Hs).
    destruct (step s) as [s1|result] eqn:Hstep; cbn.
    + apply IH; eapply Hinv; eassumption.
    + reflexivity.
Qed.

(** The same projection law applies to the binary-fuel public driver. *)
Lemma loopN_view {St Ref R : Type} (step : St -> St + R)
    (reference : Ref -> Ref + R) (view : St -> Ref) (Inv : St -> Prop) :
  (forall s, Inv s ->
    match step s with inl s1 => inl (view s1) | inr r => inr r end = reference (view s)) ->
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1) ->
  forall fuel s, Inv s ->
    match loopN step fuel s with inl s1 => inl (view s1) | inr r => inr r end =
      loopN reference fuel (view s).
Proof.
  intros Hview Hinv fuel s Hs; rewrite !loopN_fuel.
  eapply loop_fuel_view; eassumption.
Qed.

(** Continuing paths concatenate in callback order. *)
Lemma wl_path_append {St R : Type} (step : St -> St + R) : forall s xs mid ys last,
  wl_path step s xs mid -> wl_path step mid ys last -> wl_path step s (xs ++ ys) last.
Proof.
  intros s xs mid ys last Hfirst; revert ys last.
  induction Hfirst as [s|s s1 xs mid Hstep Hpath IH]; intros ys last Htail.
  - exact Htail.
  - cbn; econstructor; [exact Hstep|now apply IH].
Qed.

(** Exhausting unary fuel yields a continuing path with exactly that many callbacks. *)
Lemma loop_fuel_path {St R : Type} (step : St -> St + R) : forall fuel s last,
  loop_fuel step fuel s = inl last ->
  exists xs, wl_path step s xs last /\ length xs = fuel.
Proof.
  intro fuel; induction fuel as [|fuel IH]; intros s last Hrun.
  - cbn [loop_fuel] in Hrun; inversion Hrun; subst.
    exists []; split; [constructor|reflexivity].
  - cbn [loop_fuel] in Hrun; destruct (step s) as [s1|result] eqn:Hstep;
      [|discriminate].
    destruct (IH s1 last Hrun) as [xs [Hpath Hlength]].
    exists (s :: xs); split; [econstructor; eassumption|cbn; now rewrite Hlength].
Qed.

(** Returning a result exposes a continuing prefix and its final stopping callback. *)
Lemma loop_fuel_stop_path {St R : Type} (step : St -> St + R) : forall fuel s result,
  loop_fuel step fuel s = inr result ->
  exists xs last, wl_path step s xs last /\ step last = inr result /\ length xs < fuel.
Proof.
  intro fuel; induction fuel as [|fuel IH]; intros s result Hrun; [discriminate|].
  cbn [loop_fuel] in Hrun; destruct (step s) as [s1|out] eqn:Hstep.
  - destruct (IH s1 result Hrun) as [xs [last [Hpath [Hstop Hlength]]]].
    exists (s :: xs), last; split; [econstructor; eassumption|].
    split; [exact Hstop|cbn; lia].
  - inversion Hrun; subst; exists [], s.
    split; [constructor|split; [exact Hstep|cbn; lia]].
Qed.

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
  Definition c_lookup : N := (S.c_sys + PTrieT.c_trie + 2)%N.
  Definition c_step : N := (64 * (S.c_sys + PTrieT.c_trie + 1))%N.
  Definition c_wl : N := 1%N. (* STUB *)
  Definition k_prepare : N := 1%N. (* STUB *)
  Definition k_eval : N := (64 * (c_lookup + S.c_sys + 1))%N.
  Definition k_update : N :=
    (512 * (c_lookup + P.c_pol + Q.c_pq + c_loopN + 1))%N.
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
    N.to_nat (Q.size (ws_queue s)) = length (filter (fun id =>
      match Q.prio (ws_queue s) id with Some _ => true | None => false end) (row_ids p)) /\
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
        (h - rk a) * (weighted_degree p c + degree p c)) (key_support p)))%nat) *
      unit p + queue_phi p s)%N.
  Definition all_head_phi (p : S.prog) (pol : policy L.wparam) (s : state) : N :=
    (k_credit * N.of_nat ((queue_credit p s + fold_right Nat.add 0
      (List.map (fun c => (head_allowance p pol c - N.to_nat (counter s c)) *
        (weighted_degree p c + degree p c)) (key_support p)))%nat) * unit p + queue_phi p s +
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

  (** * Enumeration and cached metadata *)

  (** Binary succession agrees with numbering the corresponding natural interval. *)
  Lemma ids_from_seq : forall n start,
    wl_ids_from n (Pos.of_succ_nat start) =
      List.map Pos.of_succ_nat (seq start n).
  Proof.
    intro n; induction n as [|n IH]; intro start; cbn [wl_ids_from seq List.map].
    - reflexivity.
    - rewrite <- SuccNat2Pos.inj_succ; now rewrite IH.
  Qed.

  (** Binary enumeration retains the original observable identifiers and occurrence order. *)
  Lemma F0_row_ids : forall p,
    row_ids p = List.map Pos.of_succ_nat (seq 0 (C p)).
  Proof.
    intro p; apply (ids_from_seq (C p) 0).
  Qed.

  (** Projecting a prepared state retains every lookup in the original store. *)
  Lemma F0_view_look : forall s x, reference_look (wl_view s) x = look s x.
  Proof.
    reflexivity.
  Qed.

  (** Projecting a prepared state retains every strict-update counter. *)
  Lemma F0_view_counter : forall s c, reference_counter (wl_view s) c = counter s c.
  Proof.
    reflexivity.
  Qed.

  (** Numbered lookup agrees with the corresponding original row occurrence. *)
  Lemma F1_numbering : forall p n,
    source_row p (Pos.of_succ_nat n) = nth_error (S.rows p) n.
  Proof.
    intros p n; unfold source_row; rewrite SuccNat2Pos.id_succ.
    now replace (Datatypes.S n - 1) with n by lia.
  Qed.

  (** Reader buckets retain every reading row occurrence once. *)
  Lemma F2_readers : forall p c,
    source_readers p c = filter (fun id => match source_row p id with
      | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      | None => false
      end) (row_ids p).
  Proof.
    reflexivity.
  Qed.

  (** Evaluation observes the current store through the system's public evaluator. *)
  Lemma F3_eval : forall p r m,
    eval_row p r m = S.eval p r (look_or S.key_code L.bot m).
  Proof.
    reflexivity.
  Qed.

  (** There is one identifier per source row occurrence. *)
  Lemma row_ids_length : forall p, length (row_ids p) = C p.
  Proof.
    intro p; rewrite F0_row_ids, length_map, length_seq; reflexivity.
  Qed.

  (** Numbered row occurrences have distinct identifiers even when rows repeat. *)
  Lemma row_ids_nodup : forall p, NoDup (row_ids p).
  Proof.
    intro p; rewrite F0_row_ids.
    pose proof (seq_NoDup (C p) 0) as Hids.
    induction Hids as [|n ns Hfresh Hids IH]; cbn [List.map].
    - constructor.
    - constructor; [|exact IH].
      intros [m [Heq Hin]]%in_map_iff; apply SuccNat2Pos.inj in Heq.
      subst m; now apply Hfresh.
  Qed.

  (** The row identifiers are exactly the positive numbers up to the row count. *)
  Lemma row_ids_member : forall p id,
    In id (row_ids p) <-> Pos.to_nat id <= C p.
  Proof.
    intros p id; rewrite F0_row_ids, in_map_iff; split.
    - intros [n [<- Hin]]; apply in_seq in Hin; rewrite SuccNat2Pos.id_succ; lia.
    - intro Hid; exists (Pos.to_nat id - 1); split.
      + apply SuccNat2Pos.inv; pose proof (Pos2Nat.is_pos id); lia.
      + apply in_seq; pose proof (Pos2Nat.is_pos id); lia.
  Qed.

  (** Successful source lookup identifies a listed row and its numbered occurrence. *)
  Lemma source_row_member : forall p id r,
    source_row p id = Some r -> In id (row_ids p) /\ In r (S.rows p).
  Proof.
    intros p id r Hrow; unfold source_row in Hrow; split.
    - apply row_ids_member; unfold C.
      assert (Hlt : Pos.to_nat id - 1 < length (S.rows p)).
      { apply nth_error_Some; congruence. }
      pose proof (Pos2Nat.is_pos id); lia.
    - eapply nth_error_In; exact Hrow.
  Qed.

  (** Every enumerated row identifier has a source row. *)
  Lemma source_row_total : forall p id, In id (row_ids p) ->
    exists r, source_row p id = Some r.
  Proof.
    intros p id Hid; apply row_ids_member in Hid; unfold source_row.
    destruct (nth_error (S.rows p) (Pos.to_nat id - 1)) as [r|] eqn:Hrow.
    - now exists r.
    - apply nth_error_None in Hrow; unfold C in Hid.
      pose proof (Pos2Nat.is_pos id); lia.
  Qed.

  (** A reader bucket names exactly the source occurrences that declare that read code. *)
  Lemma source_readers_spec : forall p c id,
    In id (source_readers p c) <-> exists r x,
      source_row p id = Some r /\ In x (S.deps p r) /\ S.key_code x = c.
  Proof.
    intros p c id; unfold source_readers; rewrite filter_In; split.
    - intros [Hid Hread]; destruct (source_row p id) as [r|] eqn:Hrow;
        [|discriminate].
      apply existsb_exists in Hread as [x [Hin Heq]].
      apply Pos.eqb_eq in Heq; exists r, x; repeat split; assumption || congruence.
    - intros [r [x [Hrow [Hin Heq]]]]; split.
      + exact (proj1 (source_row_member p id r Hrow)).
      + rewrite Hrow; apply existsb_exists; exists x; split; [exact Hin|].
        apply Pos.eqb_eq; symmetry; exact Heq.
  Qed.

  (** The declared key support contains exactly the codes of listed reads and writes. *)
  Lemma key_support_spec : forall p c,
    In c (key_support p) <-> exists r x,
      In r (S.rows p) /\ In x (S.writes p r ++ S.deps p r) /\ S.key_code x = c.
  Proof.
    intros p c; unfold key_support; rewrite nodup_In, in_map_iff; split.
    - intros [x [Heq Hin]]; apply in_flat_map in Hin as [r [Hrow Hkey]].
      exists r, x; repeat split; assumption.
    - intros [r [x [Hrow [Hkey Heq]]]]; exists x; split; [exact Heq|].
      apply in_flat_map; exists r; now split.
  Qed.

  (** A guarded enqueue update reads immutable row and rank tables from the input state. *)
  Definition enqueue_pair (s : state) (ql : Q.t * ptrie Datatypes.unit) id :=
    match trie_get id (snd ql), row_at s id with
    | None, Some r =>
      (Q.push (N.pos (match trie_get id (ws_ranks s) with
        | Some rank => rank | None => 1%positive end)) id (fst ql),
       PTrieCode.set id tt (snd ql))
    | _, _ => ql
    end.

  (** A fold can introduce only identifiers passed to its individual queue updates. *)
  Lemma queue_fold_support {A : Type} (update : A -> positive -> A) (queue : A -> Q.t) :
    (forall acc y id pr, Q.prio (queue (update acc y)) id = Some pr ->
      (exists old, Q.prio (queue acc) id = Some old) \/ id = y) ->
    forall ids acc id pr, Q.prio (queue (fold_left update ids acc)) id = Some pr ->
      (exists old, Q.prio (queue acc) id = Some old) \/ In id ids.
  Proof.
    intros Hupdate ids; induction ids as [|y ids IH]; intros acc id pr Hprio.
    - left; now exists pr.
    - cbn [fold_left] in Hprio.
      destruct (IH (update acc y) id pr Hprio) as [[old Hold]|Hin].
      + destruct (Hupdate acc y id old Hold) as [Hprior|Heq].
        * now left.
        * right; left; symmetry; exact Heq.
      + right; now right.
  Qed.

  (** Enqueue can add only identifiers from its requested list, without cache assumptions. *)
  Lemma enqueue_support : forall p pol ids s id pr,
    Q.prio (ws_queue (enqueue p pol ids s)) id = Some pr ->
      (exists old, Q.prio (ws_queue s) id = Some old) \/ In id ids.
  Proof.
    intros p pol ids s id pr Hprio.
    change (Q.prio (fst (fold_left (enqueue_pair s) ids (ws_queue s, ws_live s))) id =
      Some pr) in Hprio.
    eapply (queue_fold_support (enqueue_pair s) (@fst Q.t (ptrie Datatypes.unit)))
      in Hprio; [exact Hprio|].
    intros [q live] y target out Hpush; unfold enqueue_pair in Hpush.
    cbn [fst snd] in Hpush |- *.
    destruct (trie_get y live), (row_at s y);
      try (left; now exists out).
    cbn [fst snd] in Hpush.
    destruct (Pos.eq_dec y target) as [Heq|Hneq].
    - right; symmetry; exact Heq.
    - rewrite Q.prio_push_other in Hpush by exact Hneq; left; now exists out.
  Qed.

  (** Trie insertion exposes one code and retains every other lookup. *)
  Lemma trie_get_set {A : Type} : forall c key (a : A) m,
    trie_get c (PTrieCode.set key a m) =
      if Pos.eqb c key then Some a else trie_get c m.
  Proof.
    intros c key a m; destruct (Pos.eqb c key) eqn:Heq.
    - apply Pos.eqb_eq in Heq; subst c; apply PTrie.get_set_same.
    - apply Pos.eqb_neq in Heq; now apply PTrie.get_set_other.
  Qed.

  (** Trie removal clears one code and retains every other lookup. *)
  Lemma trie_get_remove {A : Type} : forall c key (m : ptrie A),
    trie_get c (PTrieCode.remove key m) =
      if Pos.eqb c key then None else trie_get c m.
  Proof.
    intros c key m; destruct (Pos.eqb c key) eqn:Heq.
    - apply Pos.eqb_eq in Heq; subst c; apply PTrie.get_remove_same.
    - apply Pos.eqb_neq in Heq; now apply PTrie.get_remove_other.
  Qed.

  (** An empty trie has no binding at any positive code. *)
  Lemma trie_get_empty {A : Type} : forall c, trie_get c (@Empty A) = None.
  Proof.
    apply PTrie.get_empty.
  Qed.

  (** A push keeps every previously live identifier live. *)
  Lemma queue_push_retains : forall priority fresh q id pr,
    Q.prio q id = Some pr -> exists next, Q.prio (Q.push priority fresh q) id = Some next.
  Proof.
    intros priority fresh q id pr Hprio; destruct (Pos.eq_dec fresh id) as [->|Hneq].
    - eexists; apply Q.prio_push.
    - rewrite Q.prio_push_other by exact Hneq; now exists pr.
  Qed.

  (** A guarded absent push preserves equality between pending and live cardinality. *)
  Lemma queue_exact_push : forall q priority id,
    Q.wf q -> Q.pending q = N.to_nat (Q.size q) -> Q.prio q id = None ->
    Q.pending (Q.push priority id q) = N.to_nat (Q.size (Q.push priority id q)).
  Proof.
    intros q priority id Hwf Hexact Hnone.
    pose proof (Q.pending_push priority id q Hwf) as Hupper.
    pose proof (Q.size_pending (Q.push priority id q) (Q.wf_push priority id q Hwf))
      as Hlower.
    rewrite Q.size_push by exact Hwf; rewrite Hnone, N2Nat.inj_succ.
    rewrite Q.size_push in Hlower by exact Hwf; rewrite Hnone, N2Nat.inj_succ in Hlower.
    lia.
  Qed.

  (** A pop preserves equality between pending and live cardinality. *)
  Lemma queue_exact_pop : forall q priority id q1,
    Q.wf q -> Q.pending q = N.to_nat (Q.size q) ->
    Q.pop q = Some (priority, id, q1) -> Q.pending q1 = N.to_nat (Q.size q1).
  Proof.
    intros q priority id q1 Hwf Hexact Hpop.
    pose proof (Q.pending_pop q priority id q1 Hwf Hpop) as Hupper.
    pose proof (Q.size_pending q1 (Q.wf_pop q priority id q1 Hwf Hpop)) as Hlower.
    rewrite (Q.size_pop q priority id q1 Hwf Hpop), N2Nat.inj_succ in Hexact; lia.
  Qed.

  (** A live-map absence is a queue absence whenever the two representations agree. *)
  Lemma live_absent : forall s id, live_agrees s ->
    trie_get id (ws_live s) = None -> Q.prio (ws_queue s) id = None.
  Proof.
    intros s id Hlive Hnone; destruct (Q.prio (ws_queue s) id) as [pr|] eqn:Hprio;
      [|reflexivity].
    assert (Hpresent : trie_get id (ws_live s) = Some tt).
    { apply Hlive; now exists pr. }
    congruence.
  Qed.

  (** One absent enqueue installs a queue entry and its matching live marker. *)
  Definition enqueue_push (s : state) id rank : state :=
    WorklistState (ws_store s) (ws_counters s) (Q.push (N.pos rank) id (ws_queue s))
      (PTrieCode.set id tt (ws_live s)) (ws_rows s) (ws_readers s)
      (ws_armed s) (ws_ranks s).

  (** Installing matching queue and live entries preserves their lookup agreement. *)
  Lemma live_agrees_push : forall s id rank, live_agrees s ->
    live_agrees (enqueue_push s id rank).
  Proof.
    intros s id rank Hlive x; unfold enqueue_push; cbn [ws_live ws_queue].
    rewrite trie_get_set; destruct (Pos.eqb x id) eqn:Heq.
    - apply Pos.eqb_eq in Heq; subst x; split.
      + intro H; eexists; apply Q.prio_push.
      + intro H; reflexivity.
    - apply Pos.eqb_neq in Heq; rewrite Q.prio_push_other by congruence; apply Hlive.
  Qed.

  (** A genuinely new queue entry preserves every prepared-state property. *)
  Lemma prepared_push : forall p pol s id rank, prepared p pol s ->
    Q.prio (ws_queue s) id = None -> prepared p pol (enqueue_push s id rank).
  Proof.
    intros p pol s id rank [Hmeta [Hlive [Hwf [Hexact [Harmed Hranks]]]]] Hnone.
    split; [exact Hmeta|]; split; [now apply live_agrees_push|].
    split; [now apply Q.wf_push|]; split.
    - apply queue_exact_push; assumption.
    - split; [|exact Hranks].
      intros c target Hflag Hreader; destruct (Harmed c target Hflag Hreader) as [pr Hprio].
      eapply queue_push_retains; exact Hprio.
  Qed.

  (** Enqueueing nothing leaves the complete state unchanged. *)
  Lemma enqueue_nil : forall p pol s, enqueue p pol [] s = s.
  Proof.
    intros p pol s; destruct s; reflexivity.
  Qed.

  (** A singleton enqueue performs one guarded push against the cached row and rank. *)
  Lemma enqueue_single : forall p pol id s,
    enqueue p pol [id] s =
      match trie_get id (ws_live s), row_at s id with
      | None, Some r => enqueue_push s id
          (match trie_get id (ws_ranks s) with Some rank => rank | None => 1%positive end)
      | _, _ => s
      end.
  Proof.
    intros p pol id [store counts queue live rows readers armed ranks].
    unfold enqueue, enqueue_push, row_at.
    cbn [fold_left fst snd ws_store ws_counters ws_queue ws_live ws_rows ws_readers
      ws_armed ws_ranks].
    destruct (trie_get id live), (trie_get id rows); reflexivity.
  Qed.

  (** Enqueueing a list can be split after its first guarded push. *)
  Lemma enqueue_cons : forall p pol id ids s,
    enqueue p pol (id :: ids) s = enqueue p pol ids (enqueue p pol [id] s).
  Proof.
    intros p pol id ids [store counts queue live rows readers armed ranks].
    unfold enqueue, row_at.
    cbn [fold_left fst snd ws_store ws_counters ws_queue ws_live ws_rows ws_readers
      ws_armed ws_ranks].
    destruct (trie_get id live), (trie_get id rows); reflexivity.
  Qed.

  (** Every queue-fold prefix is represented by an ordinary enqueue state. *)
  Lemma enqueue_state_fold : forall p pol ids s,
    enqueue p pol ids s = fold_left (fun acc id => enqueue p pol [id] acc) ids s.
  Proof.
    intros p pol ids; induction ids as [|id ids IH]; intro s.
    - apply enqueue_nil.
    - rewrite enqueue_cons, IH; reflexivity.
  Qed.

  (** A singleton enqueue retains every old live identifier. *)
  Lemma enqueue_single_retains : forall p pol s fresh id pr,
    Q.prio (ws_queue s) id = Some pr ->
    exists next, Q.prio (ws_queue (enqueue p pol [fresh] s)) id = Some next.
  Proof.
    intros p pol s fresh id pr Hprio; rewrite enqueue_single.
    destruct (trie_get fresh (ws_live s)), (row_at s fresh); try (now exists pr).
    eapply queue_push_retains; exact Hprio.
  Qed.

  (** Enqueue retains every old live identifier without cache assumptions. *)
  Lemma enqueue_retains : forall p pol ids s id pr,
    Q.prio (ws_queue s) id = Some pr ->
    exists next, Q.prio (ws_queue (enqueue p pol ids s)) id = Some next.
  Proof.
    intros p pol ids; induction ids as [|fresh ids IH]; intros s id pr Hprio.
    - rewrite enqueue_nil; now exists pr.
    - rewrite enqueue_cons.
      destruct (enqueue_single_retains p pol s fresh id pr Hprio) as [next Hnext].
      eapply IH; exact Hnext.
  Qed.

  (** Each guarded singleton enqueue preserves the cache, queue and live invariants. *)
  Lemma enqueue_single_prepared : forall p pol id s, prepared p pol s ->
    prepared p pol (enqueue p pol [id] s).
  Proof.
    intros p pol id s Hprepared; rewrite enqueue_single.
    destruct (trie_get id (ws_live s)) eqn:Hlive, (row_at s id);
      try exact Hprepared.
    apply prepared_push; [exact Hprepared|].
    apply live_absent; [exact (proj1 (proj2 Hprepared))|exact Hlive].
  Qed.

  (** Every enqueue prefix preserves prepared-state agreement. *)
  Lemma enqueue_prepared : forall p pol ids s, prepared p pol s ->
    prepared p pol (enqueue p pol ids s).
  Proof.
    intros p pol ids; induction ids as [|id ids IH]; intros s Hprepared.
    - now rewrite enqueue_nil.
    - rewrite enqueue_cons; apply IH, enqueue_single_prepared, Hprepared.
  Qed.

  (** A listed source row is live after its own enqueue. *)
  Lemma enqueue_single_contains : forall p pol s id r,
    prepared p pol s -> source_row p id = Some r ->
    exists pr, Q.prio (ws_queue (enqueue p pol [id] s)) id = Some pr.
  Proof.
    intros p pol s id r Hprepared Hsource; rewrite enqueue_single.
    pose proof (proj1 (proj1 Hprepared) id) as Hrow; rewrite Hrow, Hsource.
    destruct (trie_get id (ws_live s)) as [[]|] eqn:Hlive.
    - apply (proj1 (proj1 (proj2 Hprepared) id)); exact Hlive.
    - eexists; apply Q.prio_push.
  Qed.

  (** Every requested source row is live after enqueue, including repeated identifiers. *)
  Lemma enqueue_contains : forall p pol ids s id r,
    prepared p pol s -> In id ids -> source_row p id = Some r ->
    exists pr, Q.prio (ws_queue (enqueue p pol ids s)) id = Some pr.
  Proof.
    intros p pol ids; induction ids as [|fresh ids IH]; intros s id r Hprepared Hin Hsource.
    - contradiction.
    - rewrite enqueue_cons; destruct Hin as [Heq|Hin].
      + subst fresh; destruct (enqueue_single_contains p pol s id r Hprepared Hsource)
          as [pr Hprio]; eapply enqueue_retains; exact Hprio.
      + eapply IH; [apply enqueue_single_prepared, Hprepared|exact Hin|exact Hsource].
  Qed.

  (** Every member is bounded by a positive maximum fold. *)
  Lemma cache_maximum_member : forall xs x, In x xs ->
    (x <= fold_right Pos.max 1%positive xs)%positive.
  Proof.
    intro xs; induction xs as [|y xs IH]; intros x Hin; [contradiction|].
    cbn [fold_right]; destruct Hin as [<-|Hin]; [apply Pos.le_max_l|].
    eapply Pos.le_trans; [apply IH; exact Hin|apply Pos.le_max_r].
  Qed.

  (** A positive maximum fold is bounded by every common upper bound of its members. *)
  Lemma cache_maximum_bound : forall xs bound,
    (1 <= bound)%positive -> (forall x, In x xs -> (x <= bound)%positive) ->
    (fold_right Pos.max 1%positive xs <= bound)%positive.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros bound Hone Hmembers; [exact Hone|].
    cbn [fold_right]; apply Pos.max_lub.
    - apply Hmembers; now left.
    - apply IH; [exact Hone|intros y Hy; apply Hmembers; now right].
  Qed.

  (** Positive maximum folds depend only on list membership, including duplicate keys. *)
  Lemma cache_maximum_ext : forall xs ys,
    (forall x, In x xs <-> In x ys) ->
    fold_right Pos.max 1%positive xs = fold_right Pos.max 1%positive ys.
  Proof.
    intros xs ys Hmembers; apply Pos.le_antisym; apply cache_maximum_bound.
    - apply Pos.le_1_l.
    - intros x Hin; apply cache_maximum_member, Hmembers, Hin.
    - apply Pos.le_1_l.
    - intros x Hin; apply cache_maximum_member, Hmembers, Hin.
  Qed.

  (** Mapping priorities commutes with their maximum fold. *)
  Lemma cache_maximum_map {A : Type} (priority : A -> positive) : forall xs,
    fold_right (fun x acc => Pos.max (priority x) acc) 1%positive xs =
      fold_right Pos.max 1%positive (List.map priority xs).
  Proof.
    intro xs; induction xs as [|x xs IH]; cbn [fold_right List.map]; [reflexivity|].
    now rewrite IH.
  Qed.

  (** The executable fallback rank agrees with the support-based specification. *)
  Lemma top_rank_code_agrees : forall p pol, top_rank_code p pol = top_rank p pol.
  Proof.
    intros p pol; unfold top_rank_code, top_rank; rewrite cache_maximum_map.
    f_equal; apply cache_maximum_ext; intro rank; rewrite !in_map_iff; split.
    - intros [x [Hrank Hin]]; exists (S.key_code x); split; [exact Hrank|].
      apply key_support_spec; apply in_flat_map in Hin as [r [Hrow Hkey]].
      exists r, x; repeat split; try assumption; reflexivity.
    - intros [c [Hrank Hin]]; apply key_support_spec in Hin as [r [x [Hrow [Hkey Hcode]]]].
      exists x; split; [now rewrite Hcode|].
      apply in_flat_map; exists r; now split.
  Qed.

  (** The executable rank fold uses the specified fallback and write sequence. *)
  Lemma rank_with_top_agrees : forall p pol r,
    rank_with_top p pol (top_rank_code p pol) r = row_rank p pol r.
  Proof.
    intros p pol r; unfold rank_with_top, row_rank; now rewrite top_rank_code_agrees.
  Qed.

  (** Combining lists pairs their corresponding optional nth entries. *)
  Lemma cache_nth_combine {A B : Type} : forall (xs : list A) (ys : list B) n,
    nth_error (combine xs ys) n =
      match nth_error xs n, nth_error ys n with
      | Some x, Some y => Some (x, y)
      | _, _ => None
      end.
  Proof.
    intros xs ys n; revert xs ys; induction n as [|n IH]; intros [|x xs] [|y ys];
      cbn [nth_error combine]; try reflexivity.
    - now destruct (nth_error xs n).
    - apply IH.
  Qed.

  (** Equal-length combination retains the complete identifier sequence. *)
  Lemma cache_combine_fst {A B : Type} : forall (xs : list A) (ys : list B),
    length xs = length ys -> List.map fst (combine xs ys) = xs.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros [|y ys] Hlength;
      cbn [length combine List.map fst] in *; try discriminate; [reflexivity|].
    f_equal; apply IH; lia.
  Qed.

  (** Numbering gives the expected positive identifier at every source index. *)
  Lemma row_ids_nth : forall p n, n < C p ->
    nth_error (row_ids p) n = Some (Pos.of_succ_nat n).
  Proof.
    intros p n Hn; rewrite F0_row_ids, nth_error_map, nth_error_seq.
    rewrite (proj2 (Nat.ltb_lt n (C p)) Hn); reflexivity.
  Qed.

  (** Numbered row pairs are precisely the successful source lookups. *)
  Lemma numbered_rows_spec : forall p id r,
    In (id, r) (combine (row_ids p) (S.rows p)) <-> source_row p id = Some r.
  Proof.
    intros p id r; split.
    - intros Hin; apply In_nth_error in Hin as [n Hpair]; rewrite cache_nth_combine in Hpair.
      destruct (nth_error (S.rows p) n) as [row|] eqn:Hrow.
      + assert (Hn : n < C p) by (apply nth_error_Some; congruence).
        rewrite (row_ids_nth p n Hn) in Hpair; injection Hpair as Hid Hr.
        subst id row; rewrite F1_numbering; exact Hrow.
      + destruct (nth_error (row_ids p) n); discriminate.
    - intro Hrow; unfold source_row in Hrow.
      assert (Hn : Pos.to_nat id - 1 < C p) by (apply nth_error_Some; congruence).
      assert (Hid : Pos.of_succ_nat (Pos.to_nat id - 1) = id).
      { apply SuccNat2Pos.inv; pose proof (Pos2Nat.is_pos id); lia. }
      apply nth_error_In with (n := Pos.to_nat id - 1).
      now rewrite cache_nth_combine, (row_ids_nth p (Pos.to_nat id - 1) Hn), Hrow, Hid.
  Qed.

  (** A right fold of distinct key bindings has exactly the listed bindings. *)
  Lemma cache_pairs_lookup {A : Type} : forall (pairs : list (positive * A)) id a,
    NoDup (List.map fst pairs) ->
    (trie_get id (fold_right (fun kv m => PTrieCode.set (fst kv) (snd kv) m)
      Empty pairs) = Some a <-> In (id, a) pairs).
  Proof.
    intro pairs; induction pairs as [|[key value] pairs IH]; intros id a Hnodup.
    - cbn [fold_right]; rewrite trie_get_empty; cbn [In].
      split; [discriminate|contradiction].
    - inversion Hnodup as [|head tail Hfresh Htail]; subst head tail.
      cbn [fold_right fst snd]; rewrite trie_get_set.
      destruct (Pos.eqb id key) eqn:Heq.
      + apply Pos.eqb_eq in Heq; subst id; split.
        * intro H; injection H as <-; now left.
        * intros [Hpair|Hin]; [now injection Hpair as <-|].
          exfalso; apply Hfresh, in_map_iff; exists (key, a); now split.
      + apply Pos.eqb_neq in Heq; rewrite IH by exact Htail; split.
        * intro Hin; now right.
        * intros [Hpair|Hin]; [injection Hpair as Hkey; congruence|exact Hin].
  Qed.

  (** The row component of indexing is the right fold of numbered row bindings. *)
  Lemma index_rows_first : forall p pairs,
    fst (fold_right (index_row p) (Empty, Empty) pairs) =
      fold_right (fun kv m => PTrieCode.set (fst kv) (snd kv) m) Empty pairs.
  Proof.
    intros p pairs; induction pairs as [|[id r] pairs IH]; cbn [fold_right index_row fst snd].
    - reflexivity.
    - now rewrite IH.
  Qed.

  (** The constructed row table agrees with every successful or absent source lookup. *)
  Lemma index_rows_source : forall p id,
    trie_get id (fst (fold_right (index_row p) (Empty, Empty)
      (combine (row_ids p) (S.rows p)))) = source_row p id.
  Proof.
    intros p id; rewrite index_rows_first.
    assert (Hnodup : NoDup (List.map fst (combine (row_ids p) (S.rows p)))).
    { rewrite cache_combine_fst; [apply row_ids_nodup|apply row_ids_length]. }
    destruct (source_row p id) as [r|] eqn:Hsource.
    - apply cache_pairs_lookup; [exact Hnodup|now apply numbered_rows_spec].
    - destruct (trie_get id (fold_right
        (fun kv m => PTrieCode.set (fst kv) (snd kv) m) Empty
        (combine (row_ids p) (S.rows p)))) as [r|] eqn:Hget; [|reflexivity].
      apply cache_pairs_lookup in Hget; [|exact Hnodup].
      apply numbered_rows_spec in Hget; congruence.
  Qed.

  (** Applying a function to each stored value commutes with numbered lookup. *)
  Lemma cache_pairs_map {A B : Type} (f : A -> B) : forall pairs id,
    trie_get id (fold_right (fun kv m => PTrieCode.set (fst kv) (f (snd kv)) m)
      Empty pairs) =
    option_map f (trie_get id
      (fold_right (fun kv m => PTrieCode.set (fst kv) (snd kv) m) Empty pairs)).
  Proof.
    intro pairs; induction pairs as [|[key value] pairs IH]; intro id.
    - cbn [fold_right]; now rewrite !trie_get_empty.
    - cbn [fold_right fst snd]; rewrite !trie_get_set.
      destruct (Pos.eqb id key); [reflexivity|apply IH].
  Qed.

  (** The constructed rank table contains precisely the specified rank of each source row. *)
  Lemma index_ranks_source : forall p pol id,
    trie_get id (fold_right (fun ir acc => PTrieCode.set (fst ir)
      (rank_with_top p pol (top_rank_code p pol) (snd ir)) acc)
      Empty (combine (row_ids p) (S.rows p))) = option_map (row_rank p pol) (source_row p id).
  Proof.
    intros p pol id; rewrite cache_pairs_map.
    rewrite <- (index_rows_first p (combine (row_ids p) (S.rows p))), index_rows_source.
    destruct (source_row p id) as [r|]; cbn [option_map]; [|reflexivity].
    f_equal; apply rank_with_top_agrees.
  Qed.

  (** Reader buckets interpret an absent trie binding as an empty list. *)
  Definition reader_bucket (m : ptrie (list positive)) c :=
    match trie_get c m with Some ids => ids | None => [] end.

  (** Adding a reader prepends it only to the selected code's bucket. *)
  Lemma reader_bucket_add : forall id key m c,
    reader_bucket (add_reader id key m) c =
      if Pos.eqb c key then id :: reader_bucket m c else reader_bucket m c.
  Proof.
    intros id key m c; unfold reader_bucket, add_reader; rewrite trie_get_set.
    destruct (Pos.eqb c key) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; now subst c.
  Qed.

  (** Marking a declared read retains one unit binding per code. *)
  Definition mark_read (seen : ptrie Datatypes.unit) (x : S.key) :=
    let c := S.key_code x in
    match trie_get c seen with Some _ => seen | None => PTrieCode.set c tt seen end.

  (** Marking a read makes exactly its own code present. *)
  Lemma mark_read_lookup : forall seen x c,
    trie_get c (mark_read seen x) =
      if Pos.eqb c (S.key_code x) then Some tt else trie_get c seen.
  Proof.
    intros seen x c; unfold mark_read.
    destruct (trie_get (S.key_code x) seen) as [[]|] eqn:Hget.
    - destruct (Pos.eqb c (S.key_code x)) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq; now subst c.
    - apply trie_get_set.
  Qed.

  (** A read-marking fold records whether its input list contains each code. *)
  Lemma mark_reads_lookup : forall xs seen c,
    trie_get c (fold_left mark_read xs seen) =
      if existsb (fun x => Pos.eqb c (S.key_code x)) xs
      then Some tt else trie_get c seen.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros seen c; [reflexivity|].
    cbn [fold_left existsb]; rewrite IH, mark_read_lookup.
    destruct (existsb (fun y => Pos.eqb c (S.key_code y)) xs),
      (Pos.eqb c (S.key_code x)); reflexivity.
  Qed.

  (** The dependency set is the exact deduplicated read-code trie used by indexing. *)
  Definition read_set (xs : list S.key) := fold_left mark_read xs Empty.

  (** Dependency-set lookup is exactly the Boolean declared-code test. *)
  Lemma read_set_lookup : forall xs c,
    trie_get c (read_set xs) =
      if existsb (fun x => Pos.eqb c (S.key_code x)) xs then Some tt else None.
  Proof.
    intros xs c; unfold read_set; now rewrite mark_reads_lookup, trie_get_empty.
  Qed.

  (** Dependency-set enumeration contains exactly the declared read codes. *)
  Lemma read_set_member : forall xs c,
    In (c, tt) (PTrieCode.elements (read_set xs)) <->
      exists x, In x xs /\ S.key_code x = c.
  Proof.
    intros xs c; rewrite PTrie.elements_spec; change
      (trie_get c (read_set xs) = Some tt <-> exists x, In x xs /\ S.key_code x = c).
    rewrite read_set_lookup; split.
    - destruct (existsb (fun x => Pos.eqb c (S.key_code x)) xs) eqn:Hread;
        [|discriminate].
      intro H; apply existsb_exists in Hread as [x [Hin Heq]].
      apply Pos.eqb_eq in Heq; exists x; split; [exact Hin|symmetry; exact Heq].
    - intros [x [Hin Hcode]].
      assert (Hread : existsb (fun y => Pos.eqb c (S.key_code y)) xs = true).
      { apply existsb_exists; exists x; split; [exact Hin|].
        apply Pos.eqb_eq; symmetry; exact Hcode. }
      now rewrite Hread.
  Qed.

  (** Enumerating deduplicated read codes preserves the declared Boolean membership test. *)
  Lemma read_set_exists : forall xs c,
    existsb (fun kv => Pos.eqb c (fst kv)) (PTrieCode.elements (read_set xs)) =
      existsb (fun x => Pos.eqb c (S.key_code x)) xs.
  Proof.
    intros xs c; apply Bool.eq_true_iff_eq; rewrite !existsb_exists; split.
    - intros [[key []] [Hin Heq]]; cbn [fst] in Heq; apply Pos.eqb_eq in Heq; subst key.
      apply read_set_member in Hin as [x [Hin Hcode]].
      exists x; split; [exact Hin|apply Pos.eqb_eq; symmetry; exact Hcode].
    - intros [x [Hin Heq]]; apply Pos.eqb_eq in Heq.
      exists (c, tt); split.
      + apply read_set_member; exists x; split; [exact Hin|symmetry; exact Heq].
      + apply Pos.eqb_refl.
  Qed.

  (** Distinct reader codes prepend a row at most once to each observed bucket. *)
  Lemma reader_bucket_fold : forall id (entries : list (positive * Datatypes.unit)) m c,
    NoDup (List.map fst entries) ->
    reader_bucket (fold_right (fun kv acc => add_reader id (fst kv) acc) m entries) c =
      if existsb (fun kv => Pos.eqb c (fst kv)) entries
      then id :: reader_bucket m c else reader_bucket m c.
  Proof.
    intros id entries; induction entries as [|[key value] entries IH]; intros m c Hnodup;
      [reflexivity|].
    inversion Hnodup as [|head tail Hfresh Htail]; subst head tail.
    cbn [fold_right existsb fst]; rewrite reader_bucket_add, IH by exact Htail.
    destruct (Pos.eqb c key) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; subst c.
    assert (Habsent : existsb (fun kv => Pos.eqb key (fst kv)) entries = false).
    { apply Bool.not_true_iff_false; intros Hpresent.
      apply existsb_exists in Hpresent as [kv [Hin Heq]]; apply Pos.eqb_eq in Heq.
      apply Hfresh, in_map_iff; exists kv; split; [symmetry; exact Heq|exact Hin]. }
    now rewrite Habsent.
  Qed.

  (** Indexing one row prepends its identifier exactly once for each declared read code. *)
  Lemma index_row_readers : forall p id r idx c,
    reader_bucket (snd (index_row p (id, r) idx)) c =
      if existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      then id :: reader_bucket (snd idx) c else reader_bucket (snd idx) c.
  Proof.
    intros p id r idx c.
    change (reader_bucket (fold_right (fun kv acc => add_reader id (fst kv) acc)
      (snd idx) (PTrieCode.elements (read_set (S.deps p r)))) c =
      if existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      then id :: reader_bucket (snd idx) c else reader_bucket (snd idx) c).
    rewrite reader_bucket_fold by apply PTrie.elements_nodup; now rewrite read_set_exists.
  Qed.

  (** Folding row indexes retains the exact ordered list of reading row occurrences. *)
  Lemma index_rows_readers : forall p pairs c,
    reader_bucket (snd (fold_right (index_row p) (Empty, Empty) pairs)) c =
      List.map fst (filter (fun ir =>
        existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p (snd ir))) pairs).
  Proof.
    intros p pairs; induction pairs as [|[id r] pairs IH]; intro c.
    - unfold reader_bucket; cbn [fold_right snd filter List.map]; now rewrite trie_get_empty.
    - cbn [fold_right]; rewrite index_row_readers, IH.
      cbn [filter List.map fst snd].
      destruct (existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)); reflexivity.
  Qed.

  (** Numbered-pair filtering agrees with source-row filtering when each pair is accurate. *)
  Lemma source_filter_pairs : forall p c pairs,
    (forall id r, In (id, r) pairs -> source_row p id = Some r) ->
    List.map fst (filter (fun ir =>
      existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p (snd ir))) pairs) =
    filter (fun id => match source_row p id with
      | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
      | None => false
      end) (List.map fst pairs).
  Proof.
    intros p c pairs; induction pairs as [|[id r] pairs IH]; intro Hsource; [reflexivity|].
    assert (Htail : forall id r, In (id, r) pairs -> source_row p id = Some r).
    { intros other row Hin; apply Hsource; now right. }
    cbn [filter List.map fst snd]; rewrite (Hsource id r (or_introl eq_refl)).
    destruct (existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r));
      cbn [List.map fst]; now rewrite IH by exact Htail.
  Qed.

  (** The constructed reader table agrees with the full ordered source reader bucket. *)
  Lemma index_readers_source : forall p c,
    reader_bucket (snd (fold_right (index_row p) (Empty, Empty)
      (combine (row_ids p) (S.rows p)))) c = source_readers p c.
  Proof.
    intros p c; rewrite index_rows_readers, source_filter_pairs.
    - rewrite cache_combine_fst by apply row_ids_length; reflexivity.
    - intros id r Hin; now apply numbered_rows_spec.
  Qed.

  (** The preparation seed is the fixed indexed state immediately before initial enqueue. *)
  Definition prepare_seed p pol : state :=
    let ids := row_ids p in
    let idx := fold_right (index_row p) (Empty, Empty) (combine ids (S.rows p)) in
    let top := top_rank_code p pol in
    let ranks := fold_right (fun ir acc =>
      PTrieCode.set (fst ir) (rank_with_top p pol top (snd ir)) acc)
      Empty (combine ids (S.rows p)) in
    WorklistState Empty Empty Q.empty Empty (fst idx) (snd idx) Empty ranks.

  (** Preparation enqueues the numbered rows into its indexed seed. *)
  Lemma prepare_eq : forall p pol,
    prepare p pol = enqueue p pol (row_ids p) (prepare_seed p pol).
  Proof.
    reflexivity.
  Qed.

  (** Seed row lookups agree with source row lookups. *)
  Lemma prepare_seed_row : forall p pol id,
    row_at (prepare_seed p pol) id = source_row p id.
  Proof.
    intros p pol id; apply index_rows_source.
  Qed.

  (** Seed reader buckets retain their exact source order and multiplicity. *)
  Lemma prepare_seed_readers : forall p pol c,
    readers (prepare_seed p pol) c = source_readers p c.
  Proof.
    intros p pol c; apply index_readers_source.
  Qed.

  (** Seed rank lookups contain the specified rank for precisely the source identifiers. *)
  Lemma prepare_seed_ranks : forall p pol id,
    trie_get id (ws_ranks (prepare_seed p pol)) =
      option_map (row_rank p pol) (source_row p id).
  Proof.
    intros p pol id; apply index_ranks_source.
  Qed.

  (** The indexed seed establishes every prepared-state property before enqueue. *)
  Lemma prepare_seed_prepared : forall p pol, prepared p pol (prepare_seed p pol).
  Proof.
    intros p pol; split.
    - split; [apply prepare_seed_row|apply prepare_seed_readers].
    - split.
      + intro id; change (trie_get id (@Empty Datatypes.unit) = Some tt <->
          exists pr, Q.prio Q.empty id = Some pr).
        rewrite trie_get_empty, Q.prio_empty; split; [discriminate|intros [pr H]; discriminate].
      + split; [apply Q.wf_empty|]; split.
        * change (Q.pending Q.empty = N.to_nat (Q.size Q.empty)).
          now rewrite Q.pending_empty, Q.size_empty.
        * split.
          -- intros c id Hflag Hin; change (trie_get c (@Empty Datatypes.unit) = Some tt)
               in Hflag; rewrite trie_get_empty in Hflag; discriminate.
          -- intros id r Hrow; rewrite prepare_seed_row in Hrow.
             now rewrite prepare_seed_ranks, Hrow.
  Qed.

  (** Initial queue construction preserves the complete indexed seed invariant. *)
  Lemma prepare_prepared : forall p pol, prepared p pol (prepare p pol).
  Proof.
    intros p pol; rewrite prepare_eq; apply enqueue_prepared, prepare_seed_prepared.
  Qed.

  (** Initial preparation queues every row without requiring system or priority premises. *)
  Lemma prepare_queued : forall p pol id, In id (row_ids p) ->
    exists pr, Q.prio (ws_queue (prepare p pol)) id = Some pr.
  Proof.
    intros p pol id Hid; rewrite prepare_eq; destruct (source_row_total p id Hid) as [r Hrow].
    eapply enqueue_contains; [apply prepare_seed_prepared|exact Hid|exact Hrow].
  Qed.

  (** Enqueue preserves every store lookup. *)
  Lemma enqueue_look : forall p pol ids s x, look (enqueue p pol ids s) x = look s x.
  Proof.
    reflexivity.
  Qed.

  (** Enqueue preserves every strict-update counter. *)
  Lemma enqueue_counter : forall p pol ids s c,
    counter (enqueue p pol ids s) c = counter s c.
  Proof.
    reflexivity.
  Qed.

  (** The preparation seed starts every lookup at bottom. *)
  Lemma prepare_seed_look : forall p pol x, look (prepare_seed p pol) x = L.bot.
  Proof.
    intros p pol x; change (look_or S.key_code L.bot Empty x = L.bot).
    unfold look_or; now rewrite trie_get_empty.
  Qed.

  (** The preparation seed starts every strict-update counter at zero. *)
  Lemma prepare_seed_counter : forall p pol c, counter (prepare_seed p pol) c = 0%N.
  Proof.
    intros p pol c.
    change (match trie_get c (@Empty N) with Some n => n | None => 0%N end = 0%N).
    now rewrite trie_get_empty.
  Qed.

  (** Reference enqueue of an empty list leaves the complete view unchanged. *)
  Lemma reference_enqueue_nil : forall p pol s, reference_enqueue p pol [] s = s.
  Proof.
    intros p pol s; destruct s; reflexivity.
  Qed.

  (** Reference enqueue splits after its first guarded queue update. *)
  Lemma reference_enqueue_cons : forall p pol id ids s,
    reference_enqueue p pol (id :: ids) s =
      reference_enqueue p pol ids (reference_enqueue p pol [id] s).
  Proof.
    intros p pol id ids [store counts queue]; unfold reference_enqueue.
    cbn [fold_left wl_store wl_counters wl_queue]; reflexivity.
  Qed.

  (** Reference singleton enqueue uses the specified source row rank. *)
  Lemma reference_enqueue_single : forall p pol id s,
    reference_enqueue p pol [id] s =
      match Q.prio (wl_queue s) id, source_row p id with
      | None, Some r => WlState (wl_store s) (wl_counters s)
          (Q.push (N.pos (row_rank p pol r)) id (wl_queue s))
      | _, _ => s
      end.
  Proof.
    intros p pol id [store counts queue]; unfold reference_enqueue.
    cbn [fold_left wl_store wl_counters wl_queue].
    destruct (Q.prio queue id), (source_row p id); try reflexivity.
    now rewrite rank_with_top_agrees.
  Qed.

  (** A reader bucket already represented in the queue makes reference enqueue a no-op. *)
  Lemma reference_enqueue_existing : forall p pol ids s,
    (forall id, In id ids -> exists pr, Q.prio (wl_queue s) id = Some pr) ->
    reference_enqueue p pol ids s = s.
  Proof.
    intros p pol ids [store counts queue] Hall; unfold reference_enqueue.
    cbn [wl_store wl_counters wl_queue] in *; f_equal.
    revert Hall; induction ids as [|id ids IH]; intro Hall; [reflexivity|].
    cbn [fold_left]; destruct (Hall id (or_introl eq_refl)) as [pr Hprio].
    rewrite Hprio; apply IH; intros target Hin; apply Hall; now right.
  Qed.

  (** A prepared singleton enqueue performs exactly the same queue operation as its view. *)
  Lemma enqueue_single_agreement : forall p pol id s, prepared p pol s ->
    wl_view (enqueue p pol [id] s) = reference_enqueue p pol [id] (wl_view s).
  Proof.
    intros p pol id s Hprepared; rewrite enqueue_single, reference_enqueue_single.
    cbn [wl_view wl_store wl_counters wl_queue].
    destruct Hprepared as [[Hrows Hreaders] [Hlive [Hwf [Hexact [Harmed Hranks]]]]].
    rewrite <- Hrows.
    destruct (trie_get id (ws_live s)) as [[]|] eqn:Hmarker.
    - destruct (proj1 (Hlive id) Hmarker) as [pr Hprio]; rewrite Hprio.
      destruct (row_at s id); reflexivity.
    - assert (Hnone : Q.prio (ws_queue s) id = None) by
        (apply live_absent; [exact Hlive|exact Hmarker]).
      rewrite Hnone; destruct (row_at s id) as [r|] eqn:Hrow; [|reflexivity].
      rewrite (Hranks id r Hrow); reflexivity.
  Qed.

  (** Every prepared enqueue retains exact reference behavior through all prefixes. *)
  Lemma enqueue_agreement : forall p pol ids s, prepared p pol s ->
    wl_view (enqueue p pol ids s) = reference_enqueue p pol ids (wl_view s).
  Proof.
    intros p pol ids; induction ids as [|id ids IH]; intros s Hprepared.
    - now rewrite enqueue_nil, reference_enqueue_nil.
    - rewrite enqueue_cons, reference_enqueue_cons.
      rewrite IH by (apply enqueue_single_prepared; exact Hprepared).
      now rewrite enqueue_single_agreement by exact Hprepared.
  Qed.

  (** * Identifier and priority widths *)

  (** Increasing a positive number cannot shorten its bit representation. *)
  Lemma positive_bits_mono : forall a b, (a <= b)%positive ->
    Pos.size_nat a <= Pos.size_nat b.
  Proof.
    intros a b Hle; rewrite !pos_size_log2.
    apply Nat.add_le_mono_r, Nat.log2_le_mono.
    now apply Pos2Nat.inj_le.
  Qed.

  (** A binary successor adds at most one bit. *)
  Lemma positive_succ_bits : forall a,
    Pos.size_nat (Pos.succ a) <= Pos.size_nat a + 1.
  Proof.
    intro a; induction a; cbn [Pos.succ Pos.size_nat]; lia.
  Qed.

  (** Taking a maximum retains one operand's bit width. *)
  Lemma positive_max_bits : forall a b,
    Pos.size_nat (Pos.max a b) <= Nat.max (Pos.size_nat a) (Pos.size_nat b).
  Proof.
    intros a b; destruct (Pos.compare_spec a b) as [Heq|Hab|Hba].
    - subst b; rewrite Pos.max_l by apply Pos.le_refl; apply Nat.le_max_l.
    - rewrite Pos.max_r by (apply Pos.lt_le_incl; exact Hab); apply Nat.le_max_r.
    - rewrite Pos.max_l by (apply Pos.lt_le_incl; exact Hba); apply Nat.le_max_l.
  Qed.

  (** A maximum of width-bounded identifiers remains within their common width. *)
  Lemma positive_maximum_bits : forall xs w, 1 <= w ->
    (forall x, In x xs -> Pos.size_nat x <= w) ->
    Pos.size_nat (fold_right Pos.max 1%positive xs) <= w.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros w Hw Hbits.
    - exact Hw.
    - cbn [fold_right]; eapply Nat.le_trans; [apply positive_max_bits|].
      apply Nat.max_lub; [apply Hbits; now left|].
      apply IH; [exact Hw|intros y Hy; apply Hbits; now right].
  Qed.

  (** Numbered rows fit the logarithmic occurrence-index width. *)
  Lemma row_ids_bits : forall p id, In id (row_ids p) ->
    Pos.size_nat id <= Nat.log2 (C p) + 1.
  Proof.
    intros p id Hin; rewrite F0_row_ids in Hin.
    apply in_map_iff in Hin as [n [<- Hin]]; apply in_seq in Hin.
    rewrite pos_size_log2, SuccNat2Pos.id_succ.
    apply Nat.add_le_mono_r, Nat.log2_le_mono; lia.
  Qed.

  (** Every declared support code fits the system's key-width bound. *)
  Lemma key_support_bits : forall p c, S.wf p -> In c (key_support p) ->
    Pos.size_nat c <= S.kw p.
  Proof.
    intros p c Hwf Hin; unfold key_support in Hin; apply nodup_In in Hin.
    apply in_map_iff in Hin as [x [<- Hin]].
    apply in_flat_map in Hin as [r [Hr Hx]].
    exact (S.key_bits_le p r x Hwf Hr Hx).
  Qed.

  (** A fitting policy bounds each support priority by one more than the key width. *)
  Lemma priority_bits : forall p pol c, prio_ok p pol -> In c (key_support p) ->
    Pos.size_nat (priority pol c) <= S.kw p + 1.
  Proof.
    intros p pol c Hprio Hin; exact (Hprio c Hin).
  Qed.

  (** The fallback rank adds only the successor bit to the maximum support priority. *)
  Lemma top_rank_bits : forall p pol, prio_ok p pol ->
    Pos.size_nat (top_rank p pol) <= S.kw p + 2.
  Proof.
    intros p pol Hprio; unfold top_rank.
    eapply Nat.le_trans; [apply positive_succ_bits|].
    assert (Hmax : Pos.size_nat
      (fold_right Pos.max 1%positive (List.map (priority pol) (key_support p))) <=
      S.kw p + 1).
    { apply positive_maximum_bits; [lia|].
      intros x Hin; apply in_map_iff in Hin as [c [<- Hc]].
      exact (priority_bits p pol c Hprio Hc). }
    lia.
  Qed.

  (** Skipping heads and taking minima never raises a row above its fallback rank. *)
  Lemma row_rank_top : forall p pol r, (row_rank p pol r <= top_rank p pol)%positive.
  Proof.
    intros p pol r; unfold row_rank.
    induction (S.writes p r) as [|x xs IH]; [apply Pos.le_refl|].
    cbn [fold_right]; destruct (trie_get (S.key_code x) (heads pol)); [exact IH|].
    eapply Pos.le_trans; [apply Pos.le_min_r|exact IH].
  Qed.

  (** Every cached row priority fits the fallback's bit-width bound. *)
  Lemma row_rank_bits : forall p pol r, prio_ok p pol ->
    Pos.size_nat (row_rank p pol r) <= S.kw p + 2.
  Proof.
    intros p pol r Hprio; eapply Nat.le_trans.
    - apply positive_bits_mono, row_rank_top.
    - now apply top_rank_bits.
  Qed.

  (** A row identifier and its priority fit the queue's declared key width. *)
  Lemma row_queue_width : forall p pol id r, prio_ok p pol -> In id (row_ids p) ->
    Pos.size_nat id + N.size_nat (N.pos (row_rank p pol r)) <=
      S.kw p + Nat.log2 (C p) + 3.
  Proof.
    intros p pol id r Hprio Hid.
    pose proof (row_ids_bits p id Hid) as Hbits.
    pose proof (row_rank_bits p pol r Hprio) as Hrank.
    cbn [N.size_nat]; lia.
  Qed.

  (** Turning on one previously absent entry increases a duplicate-free live count once. *)
  Lemma filter_count_set : forall ids id (before after : positive -> bool),
    NoDup ids -> In id ids -> before id = false -> after id = true ->
    (forall other, other <> id -> after other = before other) ->
    length (filter after ids) = Datatypes.S (length (filter before ids)).
  Proof.
    intros ids; induction ids as [|first ids IH]; intros id before after Hnodup Hin Hb Ha Hsame.
    - contradiction.
    - inversion Hnodup as [|first' ids' Hfresh Htail]; subst.
      destruct Hin as [Heq|Hin].
      + subst first; cbn [filter]; rewrite Hb, Ha; cbn [length].
        f_equal; f_equal; apply filter_ext_in; intros other Hother.
        apply Hsame; intro Heq; subst other; contradiction.
      + assert (Hneq : first <> id) by (intro Heq; subst first; contradiction).
        cbn [filter]; rewrite (Hsame first Hneq).
        destruct (before first); cbn [length];
          rewrite (IH id before after Htail Hin Hb Ha Hsame); reflexivity.
  Qed.

  (** The live count over source identifiers follows an absent guarded push. *)
  Lemma queue_count_push : forall p q id pr,
    In id (row_ids p) -> Q.prio q id = None ->
    length (filter (fun c => match Q.prio (Q.push pr id q) c with
      Some _ => true | None => false end) (row_ids p)) =
    Datatypes.S (length (filter (fun c => match Q.prio q c with
      Some _ => true | None => false end) (row_ids p))).
  Proof.
    intros p q id pr Hin Hnone; eapply filter_count_set.
    - apply row_ids_nodup.
    - exact Hin.
    - now rewrite Hnone.
    - now rewrite Q.prio_push.
    - intros other Hother; now rewrite Q.prio_push_other by congruence.
  Qed.

  (** A completely empty queue satisfies every structural bound. *)
  Lemma structural_empty : forall p pol s, ws_queue s = Q.empty -> structural p pol s.
  Proof.
    intros p pol s Hempty; unfold structural; rewrite Hempty.
    split; [apply Q.wf_empty|]; split; [apply Q.fits_empty|].
    split; [rewrite Q.pending_empty; lia|]; split.
    - rewrite Q.size_empty; cbn [N.to_nat].
      induction (row_ids p) as [|id ids IH]; [reflexivity|].
      cbn [filter]; rewrite Q.prio_empty; exact IH.
    - intros pr id Hprio; rewrite Q.prio_empty in Hprio; discriminate.
  Qed.

  (** An absent source row is inserted with its declared rank and within the row cap. *)
  Lemma enqueue_push_structural : forall p pol s id r,
    prio_ok p pol -> structural p pol s -> prepared p pol s ->
    In id (row_ids p) -> source_row p id = Some r -> Q.prio (ws_queue s) id = None ->
    structural p pol (enqueue_push s id (row_rank p pol r)).
  Proof.
    intros p pol s id r Hprio Hstruct Hprepared Hin Hsource Hnone.
    destruct Hstruct as [Hwf [Hfits [Hpending [Hcount Hsupport]]]].
    assert (Hexact : Q.pending (ws_queue s) = N.to_nat (Q.size (ws_queue s))).
    { exact (proj1 (proj2 (proj2 (proj2 Hprepared)))). }
    assert (Hnewcount : N.to_nat (Q.size (Q.push (N.pos (row_rank p pol r)) id (ws_queue s))) =
      length (filter (fun c => match
        Q.prio (Q.push (N.pos (row_rank p pol r)) id (ws_queue s)) c with
        Some _ => true | None => false end) (row_ids p))).
    { rewrite Q.size_push by exact Hwf; rewrite Hnone, N2Nat.inj_succ, Hcount.
      symmetry; now apply queue_count_push. }
    unfold structural, enqueue_push; cbn [ws_queue].
    split; [now apply Q.wf_push|]; split.
    - apply Q.fits_push; [exact Hwf|exact Hfits|].
      now apply row_queue_width.
    - split.
      + rewrite (queue_exact_push _ _ _ Hwf Hexact Hnone), Hnewcount.
        rewrite <- row_ids_length; apply filter_length_le.
      + split; [exact Hnewcount|].
        intros pr other Hother; destruct (Pos.eq_dec other id) as [->|Hneq].
        * rewrite Q.prio_push, Hnone in Hother; injection Hother as <-.
          split; [exact Hin|]; exists r; now split.
        * rewrite Q.prio_push_other in Hother by congruence.
          exact (Hsupport pr other Hother).
  Qed.

  (** One guarded enqueue retains the complete invariant. *)
  Lemma enqueue_single_invariant : forall p pol id s,
    prio_ok p pol -> invariant p pol s -> In id (row_ids p) ->
    invariant p pol (enqueue p pol [id] s).
  Proof.
    intros p pol id s Hprio Hinv Hin.
    pose proof Hinv as [Hstruct [Hvalues Hprepared]].
    rewrite enqueue_single.
    destruct (trie_get id (ws_live s)) as [u|] eqn:Hlive;
      destruct (row_at s id) as [r|] eqn:Hrow; try exact Hinv.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hprepared)))) id r Hrow) as Hrank.
    rewrite Hrank.
    assert (Hnone : Q.prio (ws_queue s) id = None).
    { apply live_absent; [exact (proj1 (proj2 Hprepared))|exact Hlive]. }
    split.
    - eapply enqueue_push_structural; try eassumption.
      rewrite <- (proj1 (proj1 Hprepared) id); exact Hrow.
    - split; [exact Hvalues|now apply prepared_push].
  Qed.

  (** Every enqueue prefix stays within the same structural and client bounds. *)
  Lemma enqueue_invariant : forall p pol ids s, S.wf p -> prio_ok p pol ->
    invariant p pol s -> (forall id, In id ids -> In id (row_ids p)) ->
    invariant p pol (enqueue p pol ids s).
  Proof.
    intros p pol ids; induction ids as [|id ids IH]; intros s Hwf Hprio Hinv Hids.
    - now rewrite enqueue_nil.
    - rewrite enqueue_cons; apply IH; try assumption.
      + apply enqueue_single_invariant; try assumption; apply Hids; now left.
      + intros other Hother; apply Hids; now right.
  Qed.

  (** Preparation starts at bottom and zero counters and establishes queue and value invariants. *)
  Lemma F4_prepare : forall p pol, S.wf p -> prio_ok p pol ->
    invariant p pol (prepare p pol) /\
    (forall x, look (prepare p pol) x = L.bot) /\
    (forall c, counter (prepare p pol) c = 0%N) /\
    (forall id, In id (row_ids p) ->
      exists pr, Q.prio (ws_queue (prepare p pol)) id = Some pr).
  Proof.
    intros p pol Hwf Hprio.
    assert (Hseed : invariant p pol (prepare_seed p pol)).
    { split; [apply structural_empty; reflexivity|]; split.
      - intro x; rewrite prepare_seed_look; apply B.inv_bot.
      - apply prepare_seed_prepared. }
    split.
    - rewrite prepare_eq; apply enqueue_invariant; try assumption.
      intros id Hin; exact Hin.
    - split.
      + intro x; now rewrite prepare_eq, enqueue_look, prepare_seed_look.
      + split.
        * intro c; now rewrite prepare_eq, enqueue_counter, prepare_seed_counter.
        * intros id Hin; now apply prepare_queued.
  Qed.
  (** Enqueue changes the queue alone and guards every push by live absence. *)
  Lemma F5_enqueue : forall p pol ids s,
    wl_store (reference_enqueue p pol ids s) = wl_store s /\
    wl_counters (reference_enqueue p pol ids s) = wl_counters s /\
    wl_queue (reference_enqueue p pol ids s) = fold_left
      (fun q id => match Q.prio q id, source_row p id with
        | None, Some r => Q.push (N.pos (row_rank p pol r)) id q
        | _, _ => q
        end) ids (wl_queue s).
  Proof.
    intros p pol ids s; split; [reflexivity|]; split; [reflexivity|].
    unfold reference_enqueue; cbn [wl_queue].
    generalize (wl_queue s); induction ids as [|id ids IH]; intro q; [reflexivity|].
    cbn [fold_left]; destruct (Q.prio q id), (source_row p id);
      rewrite ?rank_with_top_agrees; apply IH.
  Qed.
  (** An update writes the policy result and enqueues its readers after a strict value change. *)
  Lemma F6_update : forall p pol s x a,
    let c := S.key_code x in
    let ac := P.update pol c (reference_counter s c) (reference_look s x) a in
    let s1 := WlState (PTrieCode.set c (x, fst ac) (wl_store s))
      (PTrieCode.set c (snd ac) (wl_counters s)) (wl_queue s) in
    reference_update p pol s (x, a) =
      if L.leb a (reference_look s x) then s else
        reference_enqueue p pol (source_readers p c) s1.
  Proof.
    reflexivity.
  Qed.
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
  Proof.
    reflexivity.
  Qed.
  (** Indexed lookup reads the prepared row table without traversing the source rows. *)
  Lemma F1_row_at : forall s id, row_at s id = trie_get id (ws_rows s).
  Proof.
    reflexivity.
  Qed.
  (** Reader lookup reads the prepared bucket and maps an absent bucket to the empty list. *)
  Lemma F2_reader_at : forall s c,
    readers s c = match trie_get c (ws_readers s) with Some ids => ids | None => nil end.
  Proof.
    reflexivity.
  Qed.
  (** Preparation establishes all cache and live facts within the solver. *)
  Lemma F4_metadata : forall p pol, prepared p pol (prepare p pol).
  Proof.
    apply prepare_prepared.
  Qed.
  (** Enqueue preserves the immutable indexes and the original value components. *)
  Lemma F5_fields : forall p pol ids s,
    ws_store (enqueue p pol ids s) = ws_store s /\
    ws_counters (enqueue p pol ids s) = ws_counters s /\
    ws_rows (enqueue p pol ids s) = ws_rows s /\
    ws_readers (enqueue p pol ids s) = ws_readers s /\
    ws_armed (enqueue p pol ids s) = ws_armed s /\
    ws_ranks (enqueue p pol ids s) = ws_ranks s.
  Proof.
    intros p pol ids s; unfold enqueue; repeat split; reflexivity.
  Qed.
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
  Proof.
    intros p pol ids s; unfold enqueue; cbn [ws_queue ws_live].
    match goal with |- (fst ?pair, snd ?pair) = ?pair => destruct pair end.
    reflexivity.
  Qed.
  (** Enqueue agrees with the original helper after projection from prepared states. *)
  Lemma F5_agreement : forall p pol ids s, prepared p pol s ->
    wl_view (enqueue p pol ids s) = reference_enqueue p pol ids (wl_view s).
  Proof.
    apply enqueue_agreement.
  Qed.
  (** Enqueue maintains the metadata and live facts that justify projected agreement. *)
  Lemma F5_prepared : forall p pol ids s, prepared p pol s ->
    prepared p pol (enqueue p pol ids s).
  Proof.
    apply enqueue_prepared.
  Qed.
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
  Proof.
    reflexivity.
  Qed.
  (** Indexed updates preserve both tables independently of the input cache validity. *)
  Lemma F6_tables : forall p pol s xa,
    ws_rows (update_one p pol s xa) = ws_rows s /\
    ws_readers (update_one p pol s xa) = ws_readers s.
  Proof.
    intros p pol s [x a]; unfold update_one.
    destruct (L.leb a (look_or S.key_code L.bot (ws_store s) x));
      [split; reflexivity|].
    destruct (trie_get (S.key_code x) (ws_armed s));
      unfold arm, enqueue; split; reflexivity.
  Qed.
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
  Proof.
    reflexivity.
  Qed.
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
  Proof.
    reflexivity.
  Qed.
  (** The original three-field loop has the same public result for every fuel. *)
  Lemma F8_reference_run : forall p pol fuel,
    run p pol fuel =
    match loopN (reference_step p pol) fuel (wl_view (prepare p pol)) with
    | inl s => OutOfFuel (wl_store s)
    | inr result => result
    end.
  Proof. Admitted. (* STUB *)

  (** * Reachable-state invariants *)

  (** A continuing callback appends one state to a reachable prefix. *)
  Lemma reachable_step : forall p pol s s1, reachable p pol s ->
    step p pol s = inl s1 -> reachable p pol s1.
  Proof.
    intros p pol s s1 [xs Hpath] Hstep; exists (xs ++ [s]).
    eapply wl_path_append; [exact Hpath|].
    econstructor; [exact Hstep|constructor].
  Qed.

  (** Every suffix of a reachable continuing path remains reachable. *)
  Lemma reachable_path : forall p pol s xs last, reachable p pol s ->
    wl_path (step p pol) s xs last -> reachable p pol last.
  Proof.
    intros p pol s xs last [prefix Hprefix] Hpath.
    exists (prefix ++ xs); eapply wl_path_append; eassumption.
  Qed.

  (** Policy choices preserve the client's value invariant. *)
  Lemma policy_update_inv : forall p pol c cnt a b,
    B.inv p a -> B.inv p b -> B.inv p (fst (P.update pol c cnt a b)).
  Proof.
    intros p pol c cnt a b Ha Hb; rewrite P.update_spec.
    destruct (L.leb b a); [exact Ha|].
    destruct (trie_get c (heads pol)) as [cfg|].
    - destruct (N.ltb cnt (delay cfg)); cbn [fst].
      + now apply B.inv_join.
      + now apply B.inv_widen.
    - cbn [fst]; now apply B.inv_join.
  Qed.

  (** Encoded values also include keys that have never occurred in the program. *)
  Definition raw_value (s : state) (c : positive) : L.t :=
    match trie_get c (ws_store s) with Some (_, a) => a | None => L.bot end.

  Lemma raw_value_look : forall s x, raw_value s (S.key_code x) = look s x.
  Proof. reflexivity. Qed.

  Lemma raw_value_enqueue : forall p pol ids s c,
    raw_value (enqueue p pol ids s) c = raw_value s c.
  Proof. reflexivity. Qed.

  Lemma raw_value_arm : forall s c d, raw_value (arm c s) d = raw_value s d.
  Proof. reflexivity. Qed.

  Lemma raw_value_after_pop : forall p s id q c,
    raw_value (after_pop p s id q) c = raw_value s c.
  Proof. reflexivity. Qed.

  (** An update stores exactly its policy value at the selected encoding. *)
  Lemma raw_value_update_same : forall p pol s x a,
    raw_value (update_one p pol s (x, a)) (S.key_code x) =
      fst (P.update pol (S.key_code x) (counter s (S.key_code x)) (look s x) a).
  Proof.
    intros p pol s x a; rewrite F6_indexed; cbn beta iota zeta.
    destruct (L.leb a (look s x)) eqn:Hcovered.
    - rewrite (P.update_stable pol (S.key_code x) (counter s (S.key_code x))
        (look s x) a Hcovered); apply raw_value_look.
    - destruct (trie_get (S.key_code x) (ws_armed s)) as [u|].
      + unfold raw_value; cbn [ws_store]; rewrite PTrie.get_set_same; reflexivity.
      + rewrite raw_value_arm, raw_value_enqueue.
        unfold raw_value; cbn [ws_store]; rewrite PTrie.get_set_same; reflexivity.
  Qed.

  (** Other encodings retain their prior value. *)
  Lemma raw_value_update_other : forall p pol s x a c, c <> S.key_code x ->
    raw_value (update_one p pol s (x, a)) c = raw_value s c.
  Proof.
    intros p pol s x a c Hother; rewrite F6_indexed; cbn beta iota zeta.
    destruct (L.leb a (look s x)); [reflexivity|].
    destruct (trie_get (S.key_code x) (ws_armed s)) as [u|].
    - unfold raw_value; cbn [ws_store]; now rewrite PTrie.get_set_other.
    - rewrite raw_value_arm, raw_value_enqueue.
      unfold raw_value; cbn [ws_store]; now rewrite PTrie.get_set_other.
  Qed.

  Lemma raw_value_prepare : forall p pol c, raw_value (prepare p pol) c = L.bot.
  Proof.
    intros p pol c; unfold prepare; rewrite raw_value_enqueue.
    unfold raw_value; cbn [ws_store]; now rewrite PTrie.get_empty.
  Qed.

  (** Encoded invariant values remain invariant after any invariant contribution. *)
  Lemma raw_inv_update : forall p pol s x a,
    (forall c, B.inv p (raw_value s c)) -> B.inv p a ->
    forall c, B.inv p (raw_value (update_one p pol s (x, a)) c).
  Proof.
    intros p pol s x a Hs Ha c; destruct (Pos.eq_dec c (S.key_code x)) as [->|Hother].
    - rewrite raw_value_update_same; apply policy_update_inv; [|exact Ha].
      rewrite <- raw_value_look; apply Hs.
    - rewrite raw_value_update_other by exact Hother; apply Hs.
  Qed.

  Lemma raw_inv_fold : forall p pol outs s,
    (forall c, B.inv p (raw_value s c)) ->
    Forall (fun xa => B.inv p (snd xa)) outs ->
    forall c, B.inv p (raw_value (fold_left (update_one p pol) outs s) c).
  Proof.
    intros p pol outs; induction outs as [|[x a] outs IH]; intros s Hs Houts c.
    - exact (Hs c).
    - inversion Houts; subst; cbn [fold_left].
      apply IH; [now apply raw_inv_update|assumption].
  Qed.

  (** A continuing callback evaluates a listed row on invariant lookups. *)
  Lemma raw_inv_step : forall p pol s s1, S.wf p -> prepared p pol s ->
    (forall c, B.inv p (raw_value s c)) -> step p pol s = inl s1 ->
    forall c, B.inv p (raw_value s1 c).
  Proof.
    intros p pol s s1 Hwf Hprepared Hinv Hstep c.
    unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop; [|discriminate].
    destruct (row_at s id) as [r|] eqn:Hrow; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    assert (Hr : In r (S.rows p)).
    { destruct Hprepared as [[Hrows _] _].
      rewrite Hrows in Hrow; exact (proj2 (source_row_member p id r Hrow)). }
    assert (Hlook : forall x, B.inv p (look s x)).
    { intro x; rewrite <- raw_value_look; apply Hinv. }
    change (S.eval p r (look s) = Some (a, ss)) in Heval.
    destruct (B.inv_rows p r (look s) a ss Hwf Hr Hlook Heval) as [Ha Hss].
    apply (raw_inv_fold p pol ((S.target p r, a) :: ss) (after_pop p s id q)).
    - intro d; exact (Hinv d).
    - constructor; assumption.
  Qed.

  (** Both cached preparation and raw client values hold along every reachable prefix. *)
  Lemma reachable_raw_inv : forall p pol s, S.wf p -> reachable p pol s ->
    forall c, B.inv p (raw_value s c).
  Proof.
    intros p pol s Hwf [xs Hpath].
    assert (Hpres : forall start ys last,
      wl_path (step p pol) start ys last -> prepared p pol start ->
      (forall c, B.inv p (raw_value start c)) ->
      forall c, B.inv p (raw_value last c)).
    { intros start ys last Hys; induction Hys as [st|st st1 zs final Hstep Hys IH];
        intros Hp Hi c; [exact (Hi c)|].
      apply IH.
      - exact (proj1 (F7_prepared p pol st st1 Hp Hstep)).
      - eapply raw_inv_step; eassumption. }
    eapply Hpres; [exact Hpath|apply F4_metadata|].
    intro c; rewrite raw_value_prepare; apply B.inv_bot.
  Qed.



  (** The source-row live count drops once after a successful pop. *)
  Lemma queue_count_pop : forall p q pr id q1,
    Q.wf q -> Q.pop q = Some (pr, id, q1) -> In id (row_ids p) ->
    length (filter (fun c => match Q.prio q c with Some _ => true | None => false end)
      (row_ids p)) = Datatypes.S (length (filter
      (fun c => match Q.prio q1 c with Some _ => true | None => false end) (row_ids p))).
  Proof.
    intros p q pr id q1 Hwf Hpop Hin.
    destruct (Q.pop_min q pr id q1 Hwf Hpop) as [Hid [Hmin [Hnone Hother]]].
    eapply filter_count_set.
    - apply row_ids_nodup.
    - exact Hin.
    - now rewrite Hnone.
    - now rewrite Hid.
    - intros other Hneq; now rewrite Hother by exact Hneq.
  Qed.

  (** Popping preserves the row cap, rank support and declared queue width. *)
  Lemma after_pop_structural : forall p pol s pr id q1,
    structural p pol s -> Q.pop (ws_queue s) = Some (pr, id, q1) ->
    structural p pol (after_pop p s id q1).
  Proof.
    intros p pol s pr id q1 [Hwf [Hfits [Hpending [Hcount Hsupport]]]] Hpop.
    destruct (Q.pop_min _ _ _ _ Hwf Hpop) as [Hid [Hmin [Hnone Hother]]].
    pose proof (proj1 (Hsupport pr id Hid)) as Hin.
    pose proof (queue_count_pop p _ _ _ _ Hwf Hpop Hin) as Hcount_pop.
    pose proof (Q.size_pop _ _ _ _ Hwf Hpop) as Hsize.
    pose proof (Q.pending_pop _ _ _ _ Hwf Hpop) as Hpending_pop.
    unfold structural; cbn [after_pop ws_queue].
    split; [eapply Q.wf_pop; eassumption|]; split.
    - eapply Q.fits_pop; eassumption.
    - split; [lia|]; split.
      + rewrite Hsize, N2Nat.inj_succ in Hcount; lia.
      + intros rank other Hprio.
        assert (Hneq : other <> id) by (intro Heq; subst other; congruence).
        rewrite Hother in Hprio by exact Hneq; now apply Hsupport in Hprio.
  Qed.

  (** A pop retains invariant values and the prepared metadata. *)
  Lemma after_pop_invariant : forall p pol s pr id q1,
    invariant p pol s -> Q.pop (ws_queue s) = Some (pr, id, q1) ->
    invariant p pol (after_pop p s id q1).
  Proof.
    intros p pol s pr id q1 [Hstruct [Hvalues Hprepared]] Hpop.
    split; [eapply after_pop_structural; eassumption|].
    split; [exact Hvalues|eapply F7_pop_prepared; eassumption].
  Qed.

  (** Replacing a stored value and its counter affects no queue or metadata property. *)
  Lemma stored_value_invariant : forall p pol s x a count,
    invariant p pol s -> B.inv p a ->
    invariant p pol (WorklistState
      (PTrieCode.set (S.key_code x) (x, a) (ws_store s))
      (PTrieCode.set (S.key_code x) count (ws_counters s))
      (ws_queue s) (ws_live s) (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s)).
  Proof.
    intros p pol s x a count [Hstruct [Hvalues Hprepared]] Ha.
    split; [exact Hstruct|]; split; [|exact Hprepared].
    intro y; unfold look, look_or; cbn [ws_store]; rewrite trie_get_set.
    destruct (Pos.eqb (S.key_code y) (S.key_code x)); [exact Ha|exact (Hvalues y)].
  Qed.

  (** Any invariant contribution preserves the full state invariant. *)
  Lemma update_invariant : forall p pol s x a, S.wf p -> prio_ok p pol ->
    invariant p pol s -> B.inv p a -> invariant p pol (update_one p pol s (x, a)).
  Proof.
    intros p pol s x a Hwf Hprio Hinv Ha.
    pose proof Hinv as [Hstruct [Hvalues Hprepared]].
    pose (ac := P.update pol (S.key_code x) (counter s (S.key_code x)) (look s x) a).
    pose (base := WorklistState (PTrieCode.set (S.key_code x) (x, fst ac) (ws_store s))
      (PTrieCode.set (S.key_code x) (snd ac) (ws_counters s))
      (ws_queue s) (ws_live s) (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s)).
    assert (Hbase : invariant p pol base).
    { unfold base; apply stored_value_invariant; [exact Hinv|].
      unfold ac; apply policy_update_inv; [apply Hvalues|exact Ha]. }
    assert (Hshape : update_one p pol s (x, a) =
      if L.leb a (look s x) then s else
      match trie_get (S.key_code x) (ws_armed s) with
      | Some _ => base | None => arm (S.key_code x) (enqueue p pol (readers s (S.key_code x)) base)
      end) by reflexivity.
    pose proof (F6_prepared p pol s (x, a) Hprepared) as Hfinal.
    rewrite Hshape in Hfinal |- *.
    destruct (L.leb a (look s x)); [exact Hinv|].
    destruct (trie_get (S.key_code x) (ws_armed s)); [exact Hbase|].
    assert (Henqueue : invariant p pol (enqueue p pol (readers s (S.key_code x)) base)).
    { apply enqueue_invariant; try assumption.
      intros id Hid; rewrite (proj2 (proj1 Hprepared)) in Hid.
      apply source_readers_spec in Hid as [r [y [Hsource _]]].
      exact (proj1 (source_row_member p id r Hsource)). }
    destruct Henqueue as [Hqueue [Hvals Hprep]].
    split; [exact Hqueue|]; split; [exact Hvals|exact Hfinal].
  Qed.

  (** Sequential primary and side contributions retain the full invariant. *)
  Lemma fold_invariant : forall p pol outs s, S.wf p -> prio_ok p pol ->
    invariant p pol s -> Forall (fun xa => B.inv p (snd xa)) outs ->
    invariant p pol (fold_left (update_one p pol) outs s).
  Proof.
    intros p pol outs; induction outs as [|[x a] outs IH]; intros s Hwf Hprio Hinv Houts.
    - exact Hinv.
    - inversion Houts; subst; cbn [fold_left]; apply IH; try assumption.
      now apply update_invariant.
  Qed.

  (** Every old queue entry stays live while contributions are processed. *)
  Lemma update_queue_retains : forall p pol s x a id pr,
    Q.prio (ws_queue s) id = Some pr ->
    exists next, Q.prio (ws_queue (update_one p pol s (x, a))) id = Some next.
  Proof.
    intros p pol s x a id pr Hprio; rewrite F6_indexed; cbn beta iota zeta.
    destruct (L.leb a (look s x)); [now exists pr|].
    destruct (trie_get (S.key_code x) (ws_armed s)); [now exists pr|].
    eapply enqueue_retains; exact Hprio.
  Qed.

  (** A strict key change leaves every declared reader live. *)
  Lemma update_reader_live : forall p pol s x a id,
    prepared p pol s -> L.leb a (look s x) = false ->
    In id (readers s (S.key_code x)) ->
    exists pr, Q.prio (ws_queue (update_one p pol s (x, a))) id = Some pr.
  Proof.
    intros p pol s x a id Hprepared Hstrict Hreader.
    rewrite F6_indexed; cbn beta iota zeta; rewrite Hstrict.
    destruct (trie_get (S.key_code x) (ws_armed s)) as [[]|] eqn:Harmed.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 Hprepared))))
        (S.key_code x) id Harmed Hreader).
    - pose proof Hreader as Hsource.
      rewrite (proj2 (proj1 Hprepared)) in Hsource.
      apply source_readers_spec in Hsource as [r [y [Hsource _]]].
      eapply enqueue_contains with (r := r); [exact Hprepared|exact Hreader|exact Hsource].
  Qed.

  (** Every state reached by the public solver satisfies its internal preparation duties. *)
  Lemma F9_reachable_prepared : forall p pol s, reachable p pol s -> prepared p pol s.
  Proof.
    intros p pol s [xs Hpath].
    assert (Hpres : forall start ys last,
      wl_path (step p pol) start ys last -> prepared p pol start -> prepared p pol last).
    { intros start ys last Hys; induction Hys as [st|st st1 zs final Hstep Hys IH];
        intro Hp; [exact Hp|].
      apply IH; exact (proj1 (F7_prepared p pol st st1 Hp Hstep)). }
    eapply Hpres; [exact Hpath|apply F4_metadata].
  Qed.
  (** Every reachable store satisfies the client invariant with arbitrary priorities. *)
  Lemma F9_reachable_inv : forall p pol s, S.wf p -> reachable p pol s ->
    forall x, B.inv p (look s x).
  Proof.
    intros p pol s Hwf Hreachable x; rewrite <- raw_value_look.
    eapply reachable_raw_inv; eassumption.
  Qed.
  (** Prepared ranks equal each row's least non-head write priority. *)
  Lemma F4_rank_cache : forall p pol id r, row_at (prepare p pol) id = Some r ->
    trie_get id (ws_ranks (prepare p pol)) = Some (row_rank p pol r).
  Proof.
    intros p pol id r Hrow.
    destruct (prepare_prepared p pol) as [_ [_ [_ [_ [_ Hranks]]]]].
    now apply Hranks.
  Qed.
  (** Every continuing callback keeps the structural and client value invariants. *)
  Lemma F9_step_inv : forall p pol s s1, S.wf p -> prio_ok p pol -> invariant p pol s ->
    step p pol s = inl s1 -> invariant p pol s1.
  Proof.
    intros p pol s s1 Hwf Hprio Hinv Hstep.
    pose proof Hinv as [Hstruct [Hvalues Hprepared]].
    unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop; [|discriminate].
    destruct (row_at s id) as [r|] eqn:Hrow; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    assert (Hr : In r (S.rows p)).
    { rewrite (proj1 (proj1 Hprepared)) in Hrow.
      exact (proj2 (source_row_member p id r Hrow)). }
    change (S.eval p r (look s) = Some (a, ss)) in Heval.
    destruct (B.inv_rows p r (look s) a ss Hwf Hr Hvalues Heval) as [Ha Hss].
    apply (fold_invariant p pol ((S.target p r, a) :: ss) (after_pop p s id q));
      try assumption.
    - eapply after_pop_invariant; eassumption.
    - constructor; assumption.
  Qed.
  (** Each intermediate primary or side update keeps the same invariant. *)
  Lemma F9_update_inv : forall p pol s x a, S.wf p -> prio_ok p pol -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
    invariant p pol (update_one p pol s (x, a)).
  Proof.
    intros p pol s x a Hwf Hprio Hinv Ha Hkey.
    now apply update_invariant.
  Qed.
  (** Reachable states satisfy every row outside their queue. *)
  Lemma F9_accepted : forall p pol s, S.wf p -> reachable p pol s -> accepted p s.
  Proof. Admitted. (* STUB *)



  (** Legal priorities give the stronger structural invariant along reachable paths. *)
  Lemma reachable_invariant : forall p pol s, S.wf p -> prio_ok p pol ->
    reachable p pol s -> invariant p pol s.
  Proof.
    intros p pol s Hwf Hprio [xs Hpath].
    assert (Hpres : forall start ys last,
      wl_path (step p pol) start ys last -> invariant p pol start -> invariant p pol last).
    { intros start ys last Hys; induction Hys as [st|st st1 zs final Hstep Hys IH];
        intro Hinv; [exact Hinv|].
      apply IH; eapply F9_step_inv; eassumption. }
    eapply Hpres; [exact Hpath|].
    exact (proj1 (F4_prepare p pol Hwf Hprio)).
  Qed.

  (** * Operation costs and height credit *)

  (** Structural work pays for a key traversal, an identifier traversal and one call. *)
  Lemma time_unit_bounds : forall p,
    (1 <= unit p)%N /\
    (N.of_nat (S.kw p + 1) <= unit p)%N /\
    (N.of_nat (Nat.log2 (C p) + 1) <= unit p)%N /\
    (L.c_lat * N.of_nat (B.vsize p + 1) <= unit p)%N /\
    (S.row_work p 0 + 1 <= unit p)%N.
  Proof.
    intro p.
    pose proof (S.row_work_mono p 0 (B.vsize p) ltac:(lia)) as Hwork.
    assert (Hpositive : (1 <= N.of_nat
      ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)))%N).
    { assert (1 <= (Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)) by nia.
      lia. }
    assert (Hkey : (N.of_nat (S.kw p + 1) <= N.of_nat
      ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)))%N).
    { assert (S.kw p + 1 <=
        (Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)) by nia.
      lia. }
    assert (Hid : (N.of_nat (Nat.log2 (C p) + 1) <= N.of_nat
      ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)))%N).
    { assert (Nat.log2 (C p) + 1 <=
        (Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)) by nia.
      lia. }
    unfold unit; repeat split; lia.
  Qed.

  (** Store lookup pays once for encoding and once for trie traversal. *)
  Lemma T_lookup_bound : forall m x,
    (T_look_or S.key_code S.T_key_code L.bot m x <=
      c_lookup * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros m x; pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) m) as Hget.
    unfold T_look_or, PTrieT.T_get in *; unfold c_lookup, S.key_bits in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** The invariant bounds every store value used by query evaluation. *)
  Lemma invariant_sizes : forall p pol s, invariant p pol s ->
    forall x, L.size (look s x) <= B.vsize p.
  Proof.
    intros p pol s [_ [Hvalues _]] x; apply B.size_le; apply Hvalues.
  Qed.

  (** Reachable frames pay only for their actual resume and declared key lookup. *)
  Lemma T_query_bound : forall p r m, S.wf p -> In r (S.rows p) ->
    (forall x, L.size (look_or S.key_code L.bot m x) <= B.vsize p) ->
    (T_eval_query (S.resume p) (S.T_resume p) (look_or S.key_code L.bot m)
      (T_look_or S.key_code S.T_key_code L.bot m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) <=
      20 * (c_lookup + S.c_sys + 1) *
        N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) * unit p)%N.
  Proof.
    intros p r m Hwf Hr Hsize.
    destruct (S.eval p r (look_or S.key_code L.bot m)) as [[a ss]|] eqn:Heval.
    2: { exfalso; exact (S.eval_total p r (look_or S.key_code L.bot m) Hwf Hr Heval). }
    pose proof (S.sides_count p r (look_or S.key_code L.bot m) a ss Hwf Hr Heval)
      as Hcount.
    assert (Hread : forall n q acc x f,
      loop_fuel (eval_step (S.resume p) (look_or S.key_code L.bot m)) n
        (S.start p r, nil) = inl (q, acc) ->
      fst (peel q acc) = inr (x, f) ->
      (T_look_or S.key_code S.T_key_code L.bot m x +
        S.T_resume p f (look_or S.key_code L.bot m x) <=
        (c_lookup + S.c_sys) * unit p)%N).
    { intros n q acc x f Hprefix Hask.
      pose proof (S.asks_within p r (look_or S.key_code L.bot m) n q acc x f
        Hwf Hr Hprefix Hask) as Hdep.
      assert (Hbits : S.key_bits x <= S.kw p).
      { apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
      pose proof (T_lookup_bound m x) as Hlook.
      pose proof (S.T_resume_le p r (look_or S.key_code L.bot m) (B.vsize p)
        n q acc x f Hwf Hr Hsize Hprefix Hask) as Hresume.
      destruct (time_unit_bounds p) as [_ [Hkey [_ [_ Hwork0]]]].
      assert (HkeyN : (N.of_nat (S.key_bits x + 1) <= unit p)%N).
      { eapply N.le_trans; [|exact Hkey]; lia. }
      assert (Hwork : (S.row_work p (B.vsize p) + 1 <= unit p)%N).
      { destruct (time_unit_bounds p) as [Hpositive _].
        unfold unit in *.
        assert (1 <= N.of_nat
          ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)))%N.
        { assert (1 <= (Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)) by nia.
          lia. }
        nia. }
      assert (Hlook_bound : (T_look_or S.key_code S.T_key_code L.bot m x <=
        c_lookup * unit p)%N).
      { eapply N.le_trans; [exact Hlook|]; now apply N.mul_le_mono_l. }
      assert (Hresume_bound :
        (S.T_resume p f (look_or S.key_code L.bot m x) <= S.c_sys * unit p)%N).
      { eapply N.le_trans; [exact Hresume|]; now apply N.mul_le_mono_l. }
      clear -Hlook_bound Hresume_bound; nia. }
    pose proof (T_eval_query_le (S.resume p) (S.T_resume p)
      (look_or S.key_code L.bot m) (T_look_or S.key_code S.T_key_code L.bot m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) a ss
      ((c_lookup + S.c_sys) * unit p)%N Heval Hread) as Heval_cost.
    assert (HcountN : (N.of_nat (length ss) <= N.of_nat (length (S.sides p r)))%N)
      by lia.
    destruct (time_unit_bounds p) as [Hunit _].
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
    clear -Heval_cost HcountN Hunit; nia.
  Qed.

  (** Evaluation adds its dependency enumeration and starting-frame overhead. *)
  Lemma T_eval_row_bound : forall p r m, S.wf p -> In r (S.rows p) ->
    (forall x, L.size (look_or S.key_code L.bot m x) <= B.vsize p) ->
    (T_eval_row p r m <= k_eval *
      N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) * unit p)%N.
  Proof.
    intros p r m Hwf Hr Hsize.
    pose proof (T_query_bound p r m Hwf Hr Hsize) as Hquery.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (Datatypes.T_length_le (S.deps p r)) as Hlength.
    pose proof (S.T_start_le p r Hwf Hr) as Hstart.
    destruct (time_unit_bounds p) as [Hu [Hkey [_ [_ Hwork]]]].
    set (u := unit p) in *.
    set (d := N.of_nat (length (S.deps p r) + length (S.sides p r) + 1)) in *.
    set (chunk := (d * u)%N).
    assert (Hd : (1 <= d)%N) by (unfold d; lia).
    assert (Hdeps_size : (N.of_nat (length (S.deps p r) + 1) <= d)%N)
      by (unfold d; lia).
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; clear -Hd Hu; nia).
    assert (Hunit_chunk : (u <= chunk)%N) by (unfold chunk; clear -Hd; nia).
    assert (Hstart_bound : (S.T_start p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hstart|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hdeps_bound : (S.T_deps p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hdeps|].
      unfold chunk; rewrite N.mul_assoc.
      apply N.mul_le_mono; [now apply N.mul_le_mono_l|exact Hkey]. }
    assert (Hlength_bound : (Datatypes.T_length (S.deps p r) <= chunk)%N).
    { rewrite Nat2N.inj_add in Hdeps_size; unfold chunk.
      clear -Hlength Hdeps_size Hu; nia. }
    replace (20 * (c_lookup + S.c_sys + 1) * d * u)%N with
      (20 * (c_lookup + S.c_sys + 1) * chunk)%N in Hquery by (unfold chunk; ring).
    replace (k_eval * d * u)%N with (k_eval * chunk)%N by (unfold chunk; ring).
    unfold T_eval_row.
    change (fun f a => S.T_resume p f a) with (S.T_resume p).
    change (fun x => T_look_or S.key_code (fun y => S.T_key_code y) L.bot m x)
      with (T_look_or S.key_code S.T_key_code L.bot m).
    time_simpl; time_cbn.
    clear -Hquery Hstart_bound Hdeps_bound Hlength_bound Hchunk.
    unfold k_eval; nia.
  Qed.

  (** Reading a prepared row table is independent of the source row-list length. *)
  Lemma T_row_at_bits : forall s id,
    (T_row_at s id <= (PTrieT.c_trie + 2) * N.of_nat (Pos.size_nat id + 1))%N.
  Proof.
    intros s id; pose proof (PTrieT.T_get_le S.row id (ws_rows s)) as Hget.
    unfold T_row_at, PTrieT.T_get in *; time_simpl; time_cbn.
    rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** Reading an absent or present bucket uses the same key traversal. *)
  Lemma T_readers_bits : forall s c,
    (T_readers s c <= (PTrieT.c_trie + 2) * N.of_nat (Pos.size_nat c + 1))%N.
  Proof.
    intros s c; pose proof (PTrieT.T_get_le (list positive) c (ws_readers s)) as Hget.
    unfold T_readers, PTrieT.T_get in *; time_simpl; time_cbn.
    destruct (trie_get c (ws_readers s)); rewrite Nat2N.inj_add in *; nia.
  Qed.

  (** The output-cost accumulator adds its initial credit without affecting callbacks. *)
  Lemma output_cost_acc : forall p pol outs s n,
    snd (fold_left (fun sn xa =>
      (update_one p pol (fst sn) xa,
        (snd sn + T_update_one p pol (fst sn) xa)%N)) outs (s, n)) =
      (n + output_cost p pol outs s)%N.
  Proof.
    intros p pol outs; induction outs as [|xa outs IH]; intros s n.
    - unfold output_cost; cbn [fold_left snd]; lia.
    - cbn [fold_left fst snd].
      rewrite IH; unfold output_cost at 2; cbn [fold_left fst snd].
      rewrite IH; lia.
  Qed.

  (** One emitted occurrence adds exactly its callback clock before processing the suffix. *)
  Lemma output_cost_cons : forall p pol xa outs s,
    output_cost p pol (xa :: outs) s =
      (T_update_one p pol s xa + output_cost p pol outs (update_one p pol s xa))%N.
  Proof.
    intros p pol xa outs s; unfold output_cost at 1; cbn [fold_left fst snd].
    rewrite output_cost_acc; lia.
  Qed.

  (** The derived fold clock adds one list step to every recorded output callback. *)
  Lemma T_output_fold_le : forall p pol outs s,
    (List.T_fold_left (update_one p pol) (T_update_one p pol) outs s <=
      output_cost p pol outs s + N.of_nat (length outs) + 1)%N.
  Proof.
    intros p pol outs; induction outs as [|xa outs IH]; intro s.
    - unfold output_cost; time_step.
    - specialize (IH (update_one p pol s xa)).
      time_unfold @List.T_fold_left; time_cbn.
      rewrite output_cost_cons; nia.
  Qed.

  (** The queue's one-larger pending cap changes its logarithmic unit by at most two. *)
  Lemma queue_unit_le : forall p,
    (N.of_nat (Q.unit_pq (C p + 1) (S.kw p + Nat.log2 (C p) + 3)) <=
      2 * unit p)%N.
  Proof.
    intro p; pose proof (Nat.log2_succ_le (C p)) as Hlog.
    assert (Hnat : Q.unit_pq (C p + 1) (S.kw p + Nat.log2 (C p) + 3) <=
      2 * ((Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4))).
    { unfold Q.unit_pq; replace (C p + 1) with (S (C p)) by lia; nia. }
    assert (Hcost : (N.of_nat (Q.unit_pq (C p + 1)
      (S.kw p + Nat.log2 (C p) + 3)) <=
      2 * N.of_nat ((Nat.log2 (C p) + 1) *
        (S.kw p + Nat.log2 (C p) + 4)))%N).
    { lia. }
    unfold unit; lia.
  Qed.

  (** A bounded guarded push keeps the coefficient of queue potential equal to one. *)
  Lemma T_queue_push_bound : forall p pr id q,
    Q.wf q -> Q.fits (S.kw p + Nat.log2 (C p) + 3) q -> Q.pending q <= C p ->
    Pos.size_nat id + N.size_nat pr <= S.kw p + Nat.log2 (C p) + 3 ->
    (Q.T_push pr id q +
      Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) (Q.push pr id q) <=
      2 * Q.c_pq * unit p + Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) q)%N.
  Proof.
    intros p pr id q Hwf Hfits Hpending Hwidth.
    pose proof (Q.T_push_amort (C p + 1) (S.kw p + Nat.log2 (C p) + 3)
      pr id q Hwf Hfits ltac:(lia) Hwidth) as Hpush.
    eapply N.le_trans; [exact Hpush|].
    apply N.add_le_mono_r.
    eapply N.le_trans; [apply N.mul_le_mono_l; apply queue_unit_le|].
    nia.
  Qed.

  (** A pop refunds the potential of every discarded stale queue entry. *)
  Lemma T_queue_pop_bound : forall p pol s, structural p pol s ->
    (Q.T_pop (ws_queue s) +
      match Q.pop (ws_queue s) with
      | Some (_, _, q1) => Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) q1
      | None => 0
      end <= 2 * Q.c_pq * unit p + queue_phi p s)%N.
  Proof.
    intros p pol s [Hwf [Hfits [Hpending _]]].
    pose proof (Q.T_pop_amort (C p + 1) (S.kw p + Nat.log2 (C p) + 3)
      (ws_queue s) Hwf Hfits ltac:(lia)) as Hpop.
    eapply N.le_trans; [exact Hpop|].
    unfold queue_phi; apply N.add_le_mono_r.
    eapply N.le_trans; [apply N.mul_le_mono_l; apply queue_unit_le|].
    nia.
  Qed.


  (** A fold preserves its invariant while telescoping callback potential refunds. *)
  Lemma fold_left_inv_credit {St X : Type} (f : St -> X -> St) (T_f : St -> X -> N)
      (Inv : St -> Prop) (Phi : St -> N) (budget : X -> N) : forall xs a,
    Inv a ->
    (forall st x, Inv st -> In x xs -> Inv (f st x) /\
      (T_f st x + Phi (f st x) <= budget x + Phi st)%N) ->
    Inv (fold_left f xs a) /\
    (List.T_fold_left f T_f xs a + Phi (fold_left f xs a) <=
      fold_right (fun x total => budget x + 2 + total)%N 1%N xs + Phi a)%N.
  Proof.
    induction xs as [|x xs IH]; intros a Hinv Hstep.
    - split; [exact Hinv|time_step].
    - destruct (Hstep a x Hinv (or_introl eq_refl)) as [Hnext Hcost].
      destruct (IH (f a x) Hnext
        (fun st y Hst Hin => Hstep st y Hst (or_intror Hin))) as [Hfinal Htail].
      split; [exact Hfinal|].
      time_unfold @List.T_fold_left; time_cbn; nia.
  Qed.

  (** A constant callback budget is charged once for every supplied occurrence. *)
  Lemma fold_constant_cost {A : Type} : forall (xs : list A) t,
    fold_right (fun _ total => t + 2 + total)%N 1%N xs =
      ((t + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intro t; time_cbn.
    - lia.
    - rewrite IH; nia.
  Qed.

  (** Clearing dependency flags traverses each declared key and removes its code once. *)
  Lemma T_clear_dependencies_le : forall p xs (armed : ptrie Datatypes.unit),
    (forall x, In x xs -> S.key_bits x <= S.kw p) ->
    (List.T_fold_left
      (fun acc x => PTrieCode.remove (S.key_code x) acc)
      (fun acc x => 1 + (S.T_key_code x + PTrieCode.T_remove (S.key_code x) acc))%N
      xs armed <=
      (S.c_sys + PTrieT.c_trie + 4) * N.of_nat (length xs + 1) *
        N.of_nat (S.kw p + 1))%N.
  Proof.
    intros p xs armed Hkeys.
    assert (Hstep : forall (st : ptrie Datatypes.unit) x, True -> In x xs -> True /\
      (1 + (S.T_key_code x + PTrieCode.T_remove (S.key_code x) st) <=
        (S.c_sys + PTrieT.c_trie + 1) * N.of_nat (S.kw p + 1))%N).
    { intros st x _ Hx; split; [exact I|].
      pose proof (Hkeys x Hx) as Hbits.
      pose proof (S.T_key_code_le x) as Hcode.
      pose proof (PTrieT.T_remove_le Datatypes.unit (S.key_code x) st) as Hremove.
      change (@PTrieT.T_remove Datatypes.unit) with (@PTrieCode.T_remove Datatypes.unit) in Hremove.
      unfold S.key_bits in Hcode.
      assert (HbitsN : (N.of_nat (Pos.size_nat (S.key_code x) + 1) <=
        N.of_nat (S.kw p + 1))%N) by (unfold S.key_bits in Hbits; lia).
      assert (Hkeypos : (1 <= N.of_nat (S.kw p + 1))%N) by lia.
      assert (Hcode_bound : (S.T_key_code x <= S.c_sys * N.of_nat (S.kw p + 1))%N).
      { eapply N.le_trans; [exact Hcode|]; now apply N.mul_le_mono_l. }
      assert (Hremove_bound : (PTrieCode.T_remove (S.key_code x) st <=
        PTrieT.c_trie * N.of_nat (S.kw p + 1))%N).
      { eapply N.le_trans; [exact Hremove|]; now apply N.mul_le_mono_l. }
      clear -Hcode_bound Hremove_bound Hkeypos; nia. }
    destruct (fold_left_inv_time
      (fun acc x => PTrieCode.remove (S.key_code x) acc)
      (fun acc x => 1 + (S.T_key_code x + PTrieCode.T_remove (S.key_code x) acc))%N
      (fun _ => True)
      (fun _ => (S.c_sys + PTrieT.c_trie + 1) * N.of_nat (S.kw p + 1))%N
      xs armed I Hstep) as [_ Hfold].
    rewrite fold_constant_cost in Hfold.
    assert (Hkeypos : (1 <= N.of_nat (S.kw p + 1))%N) by lia.
    rewrite Nat2N.inj_add; clear -Hfold Hkeypos; nia.
  Qed.

  (** Popping clears dependency flags and removes one live identifier. *)
  Lemma T_after_pop_bound : forall p s id q r, S.wf p -> In r (S.rows p) ->
    row_at s id = Some r ->
    (T_after_pop p s id q <= T_row_at s id +
      16 * (S.c_sys + PTrieT.c_trie + 1) *
        N.of_nat ((length (S.deps p r) + 1) * (S.kw p + Pos.size_nat id + 1)))%N.
  Proof.
    intros p s id q r Hwf Hr Hrow.
    assert (Hkeys : forall x, In x (S.deps p r) -> S.key_bits x <= S.kw p).
    { intros x Hx; apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
    pose proof (T_clear_dependencies_le p (S.deps p r) (ws_armed s) Hkeys) as Hclear.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (PTrieT.T_remove_le Datatypes.unit id (ws_live s)) as Hremove.
    change (@PTrieT.T_remove Datatypes.unit) with (@PTrieCode.T_remove Datatypes.unit) in Hremove.
    set (chunk := N.of_nat
      ((length (S.deps p r) + 1) * (S.kw p + Pos.size_nat id + 1))).
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; nia).
    assert (Hkeys_chunk : (N.of_nat (length (S.deps p r) + 1) *
      N.of_nat (S.kw p + 1) <= chunk)%N).
    { unfold chunk; rewrite Nat2N.inj_mul; apply N.mul_le_mono_l; lia. }
    assert (Hid_chunk : (N.of_nat (Pos.size_nat id + 1) <= chunk)%N).
    { unfold chunk; assert (Pos.size_nat id + 1 <=
        (length (S.deps p r) + 1) * (S.kw p + Pos.size_nat id + 1)) by nia.
      lia. }
    assert (Hclear_bound : (List.T_fold_left
      (fun acc x => PTrieCode.remove (S.key_code x) acc)
      (fun acc x => 1 + (S.T_key_code x + PTrieCode.T_remove (S.key_code x) acc))%N
      (S.deps p r) (ws_armed s) <= (S.c_sys + PTrieT.c_trie + 4) * chunk)%N).
    { eapply N.le_trans; [exact Hclear|].
      rewrite <- N.mul_assoc; now apply N.mul_le_mono_l. }
    assert (Hdeps_bound : (S.T_deps p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hdeps|].
      rewrite <- N.mul_assoc; now apply N.mul_le_mono_l. }
    assert (Hremove_bound : (PTrieCode.T_remove id (ws_live s) <=
      PTrieT.c_trie * chunk)%N).
    { eapply N.le_trans; [exact Hremove|]; now apply N.mul_le_mono_l. }
    unfold T_after_pop; rewrite Hrow; time_simpl; time_cbn.
    clear -Hclear_bound Hdeps_bound Hremove_bound Hchunk; nia.
  Qed.

  (** Additive callback accounting preserves the coefficient of amortized queue clocks. *)
  Lemma T_step_accounting : forall p pol s pr id q1 r a ss, S.wf p -> invariant p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) -> source_row p id = Some r ->
    eval_row p r (ws_store s) = Some (a, ss) ->
    (T_step p pol s <= Q.T_pop (ws_queue s) + T_eval_row p r (ws_store s) +
      output_cost p pol ((S.target p r, a) :: ss) (after_pop p s id q1) +
      S.T_target p r + 2 * T_row_at s id +
      c_step * N.of_nat
        ((length (S.deps p r) + 1) * (S.kw p + Nat.log2 (C p) + 1)) +
      N.of_nat (length ss) + c_step)%N.
  Proof.
    intros p pol s pr id q1 r a ss Hwf Hinv Hpop Hsource Heval.
    destruct (source_row_member p id r Hsource) as [Hid Hr].
    pose proof (row_ids_bits p id Hid) as Hbits.
    assert (Hrow : row_at s id = Some r).
    { destruct Hinv as [_ [_ [[Hrows _] _]]]; now rewrite Hrows. }
    pose proof (T_after_pop_bound p s id q1 r Hwf Hr Hrow) as Hafter.
    pose proof (T_output_fold_le p pol ((S.target p r, a) :: ss)
      (after_pop p s id q1)) as Hfold.
    assert (Hwidth : (N.of_nat
      ((length (S.deps p r) + 1) * (S.kw p + Pos.size_nat id + 1)) <=
      2 * N.of_nat ((length (S.deps p r) + 1) *
        (S.kw p + Nat.log2 (C p) + 1)))%N).
    { assert ((length (S.deps p r) + 1) * (S.kw p + Pos.size_nat id + 1) <=
        2 * ((length (S.deps p r) + 1) * (S.kw p + Nat.log2 (C p) + 1))) by nia.
      lia. }
    assert (Hafter_bound : (T_after_pop p s id q1 <= T_row_at s id +
      c_step * N.of_nat ((length (S.deps p r) + 1) *
        (S.kw p + Nat.log2 (C p) + 1)))%N).
    { eapply N.le_trans; [exact Hafter|].
      apply N.add_le_mono_l.
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hwidth|].
      unfold c_step; nia. }
    unfold T_step; rewrite Hpop, Hrow, Heval.
    change (fun st xa => T_update_one p pol st xa) with (T_update_one p pol).
    time_simpl; time_cbn.
    time_cbn_all.
    clear -Hafter_bound Hfold; unfold c_step in *; nia.
  Qed.

  (** W1 charges indexing, numbering and initial guarded enqueue to preparation. *)
  Lemma W1_prepare : forall p pol, S.wf p -> prio_ok p pol ->
    (T_prepare p pol <= k_prepare * (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Initial guarded pushes supply the potential consumed by later queue operations. *)
  Lemma W1_queue_phi : forall p pol, S.wf p -> prio_ok p pol ->
    (queue_phi p (prepare p pol) <= k_prepare * N.of_nat (C p + D p) * unit p)%N.
  Proof. Admitted. (* STUB *)
  (** W2 charges every dependency-resume occurrence on invariant stores. *)
  Lemma W2_eval : forall p pol r s, S.wf p -> In r (S.rows p) -> invariant p pol s ->
    (T_eval_row p r (ws_store s) <=
      k_eval * N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) * unit p)%N.
  Proof.
    intros p pol r s Hwf Hr Hinv.
    apply T_eval_row_bound; [exact Hwf|exact Hr|].
    exact (invariant_sizes p pol s Hinv).
  Qed.
  (** Reading a numbered row pays for the bits of its identifier. *)
  Lemma W2_row_at : forall p s id, In id (row_ids p) ->
    (T_row_at s id <= k_eval * unit p)%N.
  Proof.
    intros p s id Hid; pose proof (row_ids_bits p id Hid) as Hbits.
    pose proof (T_row_at_bits s id) as Htime.
    destruct (time_unit_bounds p) as [Hu [_ [Hid_unit _]]].
    assert (HbitsN : (N.of_nat (Pos.size_nat id + 1) <= 2 * unit p)%N).
    { rewrite Nat2N.inj_add in Hid_unit |- *; lia. }
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact HbitsN|].
    unfold k_eval, c_lookup; nia.
  Qed.
  (** Reading a reader bucket pays for the bits of its declared key code. *)
  Lemma W2_readers : forall p s c, S.wf p -> In c (key_support p) ->
    (T_readers s c <= k_update * unit p)%N.
  Proof.
    intros p s c Hwf Hc; pose proof (key_support_bits p c Hwf Hc) as Hbits.
    pose proof (T_readers_bits s c) as Htime.
    destruct (time_unit_bounds p) as [_ [Hkey _]].
    assert (HbitsN : (N.of_nat (Pos.size_nat c + 1) <= unit p)%N).
    { eapply N.le_trans; [|exact Hkey]; lia. }
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact HbitsN|].
    unfold k_update, c_lookup; nia.
  Qed.
  (** Guarded enqueue pays each supplied reader occurrence even when it is already live. *)
  Lemma W3_enqueue : forall p pol ids s, S.wf p -> prio_ok p pol -> invariant p pol s ->
    incl ids (row_ids p) ->
    (T_enqueue p pol ids s + queue_phi p (enqueue p pol ids s) <=
      k_update * N.of_nat (length ids + 1) * unit p + queue_phi p s)%N.
  Proof. Admitted. (* STUB *)
  (** W3 keeps the value invariant and charges reader pushes against queue potential. *)
  Lemma W3_update : forall p pol s x a, S.wf p -> prio_ok p pol -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
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
    (T_step p pol s + height_phi p rk h s1 + c_loopN <= height_phi p rk h s)%N.
  Proof. Admitted. (* STUB *)
  (** Weighted source credit fits the public weighted incidence budget. *)
  Lemma W4_initial : forall p pol rk h, S.wf p -> prio_ok p pol -> widening_free pol ->
    (height_phi p rk h (prepare p pol) <=
      k_credit * N.of_nat (D p + h * DW p) * unit p + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)

  (** * Stable segments and row visits *)

  (** Every support priority lies below the sentinel used for all-head rows. *)
  Lemma priority_lt_top_rank : forall p pol c, In c (key_support p) ->
    (priority pol c < top_rank p pol)%positive.
  Proof.
    intros p pol c Hin; unfold top_rank; apply Pos.lt_succ_r.
    revert Hin; induction (key_support p) as [|d ds IH]; intros Hin.
    - contradiction.
    - cbn [List.map fold_right]; destruct Hin as [<-|Hin].
      + apply Pos.le_max_l.
      + eapply Pos.le_trans; [apply IH; exact Hin|apply Pos.le_max_r].
  Qed.

  (** A non-head output bounds its producing row's queue rank from above. *)
  Lemma row_rank_write_le : forall p pol r x, In x (S.writes p r) ->
    trie_get (S.key_code x) (heads pol) = None ->
    (row_rank p pol r <= priority pol (S.key_code x))%positive.
  Proof.
    intros p pol r x Hin Hhead; unfold row_rank.
    revert Hin; induction (S.writes p r) as [|y ys IH]; intros Hin.
    - contradiction.
    - cbn [fold_right]; destruct Hin as [<-|Hin].
      + rewrite Hhead; apply Pos.le_min_l.
      + destruct (trie_get (S.key_code y) (heads pol)) as [cfg|].
        * apply IH; exact Hin.
        * eapply Pos.le_trans; [apply Pos.le_min_r|apply IH; exact Hin].
  Qed.

  (** Cut dependencies lie strictly below the rank of every row that reads them. *)
  Lemma row_rank_read_lt : forall p pol r x, Sched.cuts p pol = true ->
    In r (S.rows p) -> In x (S.deps p r) ->
    (priority pol (S.key_code x) < row_rank p pol r)%positive.
  Proof.
    intros p pol r x Hcuts Hr Hread.
    assert (Hsupport : In (S.key_code x) (key_support p)).
    { unfold key_support; apply nodup_In, in_map.
      apply in_flat_map; exists r; split; [exact Hr|].
      apply in_or_app; now right. }
    pose proof (priority_lt_top_rank p pol (S.key_code x) Hsupport) as Htop.
    assert (Hwrites : forall y, In y (S.writes p r) ->
      trie_get (S.key_code y) (heads pol) = None ->
      (priority pol (S.key_code x) < priority pol (S.key_code y))%positive).
    { intros y Hy Hhead.
      assert (Hedge : Sched.dependency_edge p (S.key_code x) (S.key_code y)).
      { exists r, x, y; repeat split; assumption || reflexivity. }
      destruct (proj1 (Sched.cuts_spec p pol) Hcuts _ _ Hedge)
        as [Hrank|[cfg Hcfg]].
      - exact Hrank.
      - rewrite Hhead in Hcfg; discriminate. }
    unfold row_rank; revert Hwrites.
    induction (S.writes p r) as [|y ys IH]; intros Hwrites.
    - exact Htop.
    - cbn [fold_right].
      destruct (trie_get (S.key_code y) (heads pol)) as [cfg|] eqn:Hhead.
      + apply IH; intros z Hz; apply Hwrites; now right.
      + apply Pos.min_glb_lt.
        * apply Hwrites; [now left|exact Hhead].
        * apply IH; intros z Hz; apply Hwrites; now right.
  Qed.

  (** Enqueue leaves every strict-update counter unchanged. *)
  Lemma counter_enqueue : forall p pol ids s c,
    counter (enqueue p pol ids s) c = counter s c.
  Proof.
    intros p pol ids s c; unfold counter.
    now rewrite (proj1 (proj2 (F5_fields p pol ids s))).
  Qed.

  (** Arming a reader bucket leaves every strict-update counter unchanged. *)
  Lemma counter_arm : forall s c d, counter (arm c s) d = counter s d.
  Proof.
    reflexivity.
  Qed.

  (** Popping changes no strict-update counter. *)
  Lemma counter_after_pop : forall p s id q c,
    counter (after_pop p s id q) c = counter s c.
  Proof.
    reflexivity.
  Qed.

  (** Updating a key retains exactly the counter returned by the policy. *)
  Lemma counter_update_same : forall p pol s x a,
    counter (update_one p pol s (x, a)) (S.key_code x) =
      snd (P.update pol (S.key_code x) (counter s (S.key_code x)) (look s x) a).
  Proof.
    intros p pol s x a; rewrite F6_indexed; cbn beta iota zeta.
    destruct (L.leb a (look s x)) eqn:Hcovered.
    - rewrite (P.update_stable pol (S.key_code x) (counter s (S.key_code x))
        (look s x) a Hcovered); reflexivity.
    - destruct (trie_get (S.key_code x) (ws_armed s)) as [u|].
      + unfold counter; cbn [ws_counters]; rewrite PTrie.get_set_same; reflexivity.
      + rewrite counter_arm, counter_enqueue.
        unfold counter; cbn [ws_counters]; rewrite PTrie.get_set_same; reflexivity.
  Qed.

  (** Updating another encoded key preserves the selected counter. *)
  Lemma counter_update_other : forall p pol s x a c, c <> S.key_code x ->
    counter (update_one p pol s (x, a)) c = counter s c.
  Proof.
    intros p pol s x a c Hother; rewrite F6_indexed; cbn beta iota zeta.
    destruct (L.leb a (look s x)); [reflexivity|].
    destruct (trie_get (S.key_code x) (ws_armed s)) as [u|].
    - unfold counter; cbn [ws_counters].
      now rewrite PTrie.get_set_other by exact Hother.
    - rewrite counter_arm, counter_enqueue.
      unfold counter; cbn [ws_counters].
      now rewrite PTrie.get_set_other by exact Hother.
  Qed.

  (** Every contribution leaves all counters unchanged or increases its configured head. *)
  Lemma counter_update_mono : forall p pol s xa c,
    (counter s c <= counter (update_one p pol s xa) c)%N.
  Proof.
    intros p pol s [x a] c; destruct (Pos.eq_dec c (S.key_code x)) as [->|Hother].
    - rewrite counter_update_same, P.update_spec.
      destruct (L.leb a (look s x)); [cbn [snd]; lia|].
      destruct (trie_get (S.key_code x) (heads pol)) as [cfg|]; [|cbn [snd]; lia].
      destruct (N.ltb (counter s (S.key_code x)) (delay cfg)); cbn [snd]; lia.
    - rewrite counter_update_other by exact Hother; lia.
  Qed.

  (** A strict update to a configured head increments its counter exactly once. *)
  Lemma counter_update_head : forall p pol s x a cfg,
    trie_get (S.key_code x) (heads pol) = Some cfg -> L.leb a (look s x) = false ->
    counter (update_one p pol s (x, a)) (S.key_code x) =
      N.succ (counter s (S.key_code x)).
  Proof.
    intros p pol s x a cfg Hhead Hstrict.
    rewrite counter_update_same, P.update_spec, Hstrict, Hhead.
    destruct (N.ltb (counter s (S.key_code x)) (delay cfg)); reflexivity.
  Qed.

  (** Processing a list of contributions never decreases any counter. *)
  Lemma counter_fold_mono : forall p pol outs s c,
    (counter s c <= counter (fold_left (update_one p pol) outs s) c)%N.
  Proof.
    intros p pol outs; induction outs as [|xa outs IH]; intros s c.
    - cbn [fold_left]; lia.
    - cbn [fold_left].
      pose proof (counter_update_mono p pol s xa c) as Hfirst.
      specialize (IH (update_one p pol s xa) c); lia.
  Qed.

  (** Head stability of a complete fold holds at its first update and remaining suffix. *)
  Lemma heads_unchanged_fold_cons : forall p pol xa outs s,
    heads_unchanged pol s (fold_left (update_one p pol) (xa :: outs) s) ->
    heads_unchanged pol s (update_one p pol s xa) /\
    heads_unchanged pol (update_one p pol s xa)
      (fold_left (update_one p pol) outs (update_one p pol s xa)).
  Proof.
    intros p pol xa outs s Hstable.
    split; intros c cfg Hhead;
      pose proof (Hstable c cfg Hhead) as Htotal;
      cbn [fold_left] in Htotal;
      pose proof (counter_update_mono p pol s xa c) as Hfirst;
      pose proof (counter_fold_mono p pol outs (update_one p pol s xa) c) as Htail;
      lia.
  Qed.

  (** A stable update can strictly change only a key without a configured head. *)
  Lemma stable_update_nonhead : forall p pol s x a,
    heads_unchanged pol s (update_one p pol s (x, a)) ->
    L.leb a (look s x) = false -> trie_get (S.key_code x) (heads pol) = None.
  Proof.
    intros p pol s x a Hstable Hstrict.
    destruct (trie_get (S.key_code x) (heads pol)) as [cfg|] eqn:Hhead; [|reflexivity].
    pose proof (Hstable (S.key_code x) cfg Hhead) as Hequal.
    pose proof (counter_update_head p pol s x a cfg Hhead Hstrict) as Hnext.
    lia.
  Qed.
  (** A newly queued row comes from the reader bucket of a strict contribution. *)
  Lemma update_queue_sources : forall p pol s x a id pr,
    prepared p pol s -> Q.prio (ws_queue (update_one p pol s (x, a))) id = Some pr ->
    (exists old, Q.prio (ws_queue s) id = Some old) \/
      L.leb a (look s x) = false /\ In id (source_readers p (S.key_code x)).
  Proof.
    intros p pol s x a id pr Hprepared Hlive.
    rewrite F6_indexed in Hlive; cbn beta iota zeta in Hlive.
    destruct (L.leb a (look s x)) eqn:Hcovered.
    - left; exists pr; exact Hlive.
    - destruct (trie_get (S.key_code x) (ws_armed s)) as [u|].
      + left; exists pr; exact Hlive.
      + cbn [arm ws_queue] in Hlive.
        apply enqueue_support in Hlive; destruct Hlive as [Hold|Hreader].
        * left; exact Hold.
        * right; split; [reflexivity|].
          now rewrite <- (proj2 (proj1 Hprepared) (S.key_code x)).
  Qed.

  (** In a stable output fold, every new queue member reads a non-head output key. *)
  Lemma stable_fold_sources : forall p pol outs s,
    prepared p pol s ->
    heads_unchanged pol s (fold_left (update_one p pol) outs s) ->
    forall id pr, Q.prio (ws_queue (fold_left (update_one p pol) outs s)) id = Some pr ->
    (exists old, Q.prio (ws_queue s) id = Some old) \/
      exists x a, In (x, a) outs /\ trie_get (S.key_code x) (heads pol) = None /\
        In id (source_readers p (S.key_code x)).
  Proof.
    intros p pol outs; induction outs as [|[x a] outs IH];
      intros s Hprepared Hstable id pr Hlive.
    - left; exists pr; exact Hlive.
    - destruct (heads_unchanged_fold_cons p pol (x, a) outs s Hstable)
        as [Hfirst Htail].
      cbn [fold_left] in Hlive.
      destruct (IH (update_one p pol s (x, a)) (F6_prepared p pol s (x, a) Hprepared)
        Htail id pr Hlive) as [[old Hold]|[y [b [Hin [Hhead Hreader]]]]].
      + destruct (update_queue_sources p pol s x a id old Hprepared Hold)
          as [Hbefore|[Hstrict Hreader]].
        * now left.
        * right; exists x, a; split; [now left|].
          split; [eapply stable_update_nonhead; eassumption|exact Hreader].
      + right; exists y, b; split; [now right|].
        now split.
  Qed.

  (** Every emitted primary or side occurrence has a declared write key. *)
  Lemma eval_outputs_writes : forall p r m a ss x b,
    S.wf p -> In r (S.rows p) -> eval_row p r m = Some (a, ss) ->
    In (x, b) ((S.target p r, a) :: ss) -> In x (S.writes p r).
  Proof.
    intros p r m a ss x b Hwf Hr Heval Hin.
    destruct Hin as [Hequal|Hin].
    - injection Hequal as <- <-; now left.
    - right; rewrite F3_eval in Heval.
      exact (S.sides_within p r (look_or S.key_code L.bot m) a ss x b Hwf Hr Heval Hin).
  Qed.

  (** A residual live item retains its original queue priority. *)
  Lemma pop_residual_live : forall q pr id q1 j pj, Q.wf q ->
    Q.pop q = Some (pr, id, q1) -> Q.prio q1 j = Some pj -> Q.prio q j = Some pj.
  Proof.
    intros q pr id q1 j pj Hwf Hpop Hlive.
    destruct (Q.pop_min q pr id q1 Hwf Hpop) as [_ [_ [Hremoved Hothers]]].
    destruct (Pos.eq_dec j id) as [->|Hother].
    - rewrite Hremoved in Hlive; discriminate.
    - now rewrite <- (Hothers j Hother).
  Qed.

  (** Every reachable live occurrence has its fixed source row and cached priority. *)
  Lemma reachable_live_row : forall p pol s id pr, S.wf p -> prio_ok p pol ->
    reachable p pol s -> Q.prio (ws_queue s) id = Some pr ->
    exists r, source_row p id = Some r /\ In r (S.rows p) /\
      pr = N.pos (row_rank p pol r).
  Proof.
    intros p pol s id pr Hwf Hprio Hreach Hlive.
    pose proof (reachable_invariant p pol s Hwf Hprio Hreach) as Hinv.
    destruct Hinv as [[_ [_ [_ [_ Hlisted]]]] _].
    destruct (Hlisted pr id Hlive) as [_ [r [Hrow Hrank]]].
    exists r; split; [exact Hrow|].
    split; [exact (proj2 (source_row_member p id r Hrow))|exact Hrank].
  Qed.

  (** A fixed row occurrence has the same priority in every reachable queue. *)
  Lemma reachable_priority_same : forall p pol s t id a b, S.wf p -> prio_ok p pol ->
    reachable p pol s -> reachable p pol t ->
    Q.prio (ws_queue s) id = Some a -> Q.prio (ws_queue t) id = Some b -> a = b.
  Proof.
    intros p pol s t id a b Hwf Hprio Hs Ht Ha Hb.
    destruct (reachable_live_row p pol s id a Hwf Hprio Hs Ha)
      as [r [Hr [_ Hrank]]].
    destruct (reachable_live_row p pol t id b Hwf Hprio Ht Hb)
      as [r1 [Hr1 [_ Hrank1]]].
    congruence.
  Qed.

  (** Stable callbacks can add only readers of their declared non-head writes. *)
  Lemma stable_step_sources : forall p pol s s1 pr id q r,
    S.wf p -> prio_ok p pol -> reachable p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q) -> source_row p id = Some r ->
    step p pol s = inl s1 -> heads_unchanged pol s s1 ->
    forall j pj, Q.prio (ws_queue s1) j = Some pj ->
    (exists old, Q.prio q j = Some old) \/
      exists x, In x (S.writes p r) /\ trie_get (S.key_code x) (heads pol) = None /\
        In j (source_readers p (S.key_code x)).
  Proof.
    intros p pol s s1 pr id q r Hwf Hprio Hreach Hpop Hrow Hstep Hstable j pj Hlive.
    pose proof (proj2 (proj2 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hprepared.
    rewrite F7_indexed, Hpop in Hstep.
    rewrite (proj1 (proj1 Hprepared) id), Hrow in Hstep.
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    assert (Hfold : heads_unchanged pol (after_pop p s id q)
      (fold_left (update_one p pol) ((S.target p r, a) :: ss) (after_pop p s id q))).
    { intros c cfg Hhead; rewrite counter_after_pop; exact (Hstable c cfg Hhead). }
    destruct (stable_fold_sources p pol ((S.target p r, a) :: ss) (after_pop p s id q)
      (F7_pop_prepared p pol s pr id q Hprepared Hpop) Hfold j pj Hlive)
      as [Hold|[x [b [Hin [Hhead Hreader]]]]].
    - left; exact Hold.
    - right; exists x; split.
      + eapply eval_outputs_writes; [exact Hwf| |exact Heval|exact Hin].
        exact (proj2 (source_row_member p id r Hrow)).
      + now split.
  Qed.

  (** Each newly queued reader has rank strictly above the row just popped. *)
  Lemma stable_step_support : forall p pol s s1 pr id q, fits p pol ->
    reachable p pol s -> step p pol s = inl s1 -> heads_unchanged pol s s1 ->
    Q.pop (ws_queue s) = Some (pr, id, q) ->
    forall j pj, Q.prio (ws_queue s1) j = Some pj ->
      Q.prio q j = Some pj \/ (pr < pj)%N.
  Proof.
    intros p pol s s1 pr id q [Hwf [Hcuts Hprio]] Hreach Hstep Hstable Hpop j pj Hlive.
    pose proof (reachable_step p pol s s1 Hreach Hstep) as Hreach1.
    pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
    pose proof (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop)) as Hpopped.
    destruct (reachable_live_row p pol s id pr Hwf Hprio Hreach Hpopped)
      as [r [Hrow [Hr Hrank]]].
    destruct (stable_step_sources p pol s s1 pr id q r Hwf Hprio Hreach Hpop Hrow
      Hstep Hstable j pj Hlive) as [[old Hold]|[x [Hwrite [Hhead Hreader]]]].
    - left.
      pose proof (pop_residual_live (ws_queue s) pr id q j old Hqueue Hpop Hold) as Hbefore.
      pose proof (reachable_priority_same p pol s s1 j old pj Hwf Hprio Hreach Hreach1
        Hbefore Hlive) as Hequal.
      now rewrite <- Hequal.
    - right.
      destruct (reachable_live_row p pol s1 j pj Hwf Hprio Hreach1 Hlive)
        as [r1 [Hrow1 [Hr1 Hrank1]]].
      apply source_readers_spec in Hreader.
      destruct Hreader as [r2 [y [Hrow2 [Hread Hcode]]]].
      rewrite Hrow1 in Hrow2; injection Hrow2 as <-.
      pose proof (row_rank_write_le p pol r x Hwrite Hhead) as Hwriter.
      pose proof (row_rank_read_lt p pol r1 y Hcuts Hr1 Hread) as Hreader.
      rewrite Hcode in Hreader; rewrite Hrank, Hrank1.
      change (row_rank p pol r < row_rank p pol r1)%positive.
      eapply Pos.le_lt_trans; eassumption.
  Qed.

  (** After a stable pop, its occurrence is absent and all remaining priorities are no smaller. *)
  Lemma stable_step_frontier : forall p pol s s1 pr id q, fits p pol ->
    reachable p pol s -> step p pol s = inl s1 -> heads_unchanged pol s s1 ->
    Q.pop (ws_queue s) = Some (pr, id, q) ->
    Q.prio (ws_queue s1) id = None /\
      forall j pj, Q.prio (ws_queue s1) j = Some pj -> (pr <= pj)%N.
  Proof.
    intros p pol s s1 pr id q Hfits Hreach Hstep Hstable Hpop.
    destruct Hfits as [Hwf [Hcuts Hprio]].
    assert (Hfits : fits p pol) by now repeat split.
    pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
    destruct (Q.pop_min (ws_queue s) pr id q Hqueue Hpop)
      as [Hpopped [Hminimum [Hremoved Hothers]]].
    pose proof (reachable_step p pol s s1 Hreach Hstep) as Hreach1.
    split.
    - destruct (Q.prio (ws_queue s1) id) as [pj|] eqn:Hlive; [|reflexivity].
      destruct (stable_step_support p pol s s1 pr id q Hfits Hreach Hstep Hstable Hpop
        id pj Hlive) as [Hold|Hgreater].
      + rewrite Hremoved in Hold; discriminate.
      + pose proof (reachable_priority_same p pol s s1 id pr pj Hwf Hprio Hreach Hreach1
          Hpopped Hlive); lia.
    - intros j pj Hlive.
      destruct (stable_step_support p pol s s1 pr id q Hfits Hreach Hstep Hstable Hpop
        j pj Hlive) as [Hold|Hgreater]; [|lia].
      apply (Hminimum j pj).
      exact (pop_residual_live (ws_queue s) pr id q j pj Hqueue Hpop Hold).
  Qed.
  (** Every continuing callback has popped one queue occurrence. *)
  Lemma continuing_pop : forall p pol s s1, step p pol s = inl s1 ->
    exists pr id q, Q.pop (ws_queue s) = Some (pr, id, q).
  Proof.
    intros p pol s s1 Hstep; unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop; [|discriminate].
    now exists pr, id, q.
  Qed.

  (** A stable callback preserves every lower bound on its live priorities. *)
  Lemma stable_step_lower : forall p pol s s1 lo, fits p pol -> reachable p pol s ->
    step p pol s = inl s1 -> heads_unchanged pol s s1 ->
    (forall id pr, Q.prio (ws_queue s) id = Some pr -> (lo <= pr)%N) ->
    forall id pr, Q.prio (ws_queue s1) id = Some pr -> (lo <= pr)%N.
  Proof.
    intros p pol s s1 lo Hfits Hreach Hstep Hstable Hlower j pj Hlive.
    destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
    destruct Hfits as [Hwf [Hcuts Hprio]].
    assert (Hfits : fits p pol) by now repeat split.
    pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
    destruct (stable_step_support p pol s s1 pr id q Hfits Hreach Hstep Hstable Hpop
      j pj Hlive) as [Hold|Hgreater].
    - apply (Hlower j pj).
      exact (pop_residual_live (ws_queue s) pr id q j pj Hqueue Hpop Hold).
    - pose proof (Hlower id pr (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop))).
      lia.
  Qed.

  (** An absent row below the live frontier cannot be reinserted by a stable callback. *)
  Lemma stable_step_absent_low : forall p pol s s1 lo id r,
    fits p pol -> reachable p pol s -> step p pol s = inl s1 ->
    heads_unchanged pol s s1 -> source_row p id = Some r ->
    (N.pos (row_rank p pol r) <= lo)%N -> Q.prio (ws_queue s) id = None ->
    (forall j pj, Q.prio (ws_queue s) j = Some pj -> (lo <= pj)%N) ->
    Q.prio (ws_queue s1) id = None.
  Proof.
    intros p pol s s1 lo id r Hfits Hreach Hstep Hstable Hrow Hrank Habsent Hlower.
    destruct (continuing_pop p pol s s1 Hstep) as [pr [popped [q Hpop]]].
    destruct Hfits as [Hwf [Hcuts Hprio]].
    assert (Hfits : fits p pol) by now repeat split.
    pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
    destruct (Q.prio (ws_queue s1) id) as [pj|] eqn:Hlive; [|reflexivity].
    destruct (stable_step_support p pol s s1 pr popped q Hfits Hreach Hstep Hstable Hpop
      id pj Hlive) as [Hold|Hgreater].
    - pose proof (pop_residual_live (ws_queue s) pr popped q id pj Hqueue Hpop Hold).
      congruence.
    - pose proof (Hlower popped pr
        (proj1 (Q.pop_min (ws_queue s) pr popped q Hqueue Hpop))) as Hpop_lower.
      destruct (reachable_live_row p pol s1 id pj Hwf Hprio
        (reachable_step p pol s s1 Hreach Hstep) Hlive) as [r1 [Hrow1 [_ Hrank1]]].
      rewrite Hrow in Hrow1; injection Hrow1 as <-; lia.
  Qed.

  (** Every later stable pop respects the current lower bound on live priorities. *)
  Lemma stable_path_ranks_lower : forall p pol s xs last lo,
    fits p pol -> reachable p pol s -> wl_path (step p pol) s xs last ->
    stable_segment p pol xs ->
    (forall id pr, Q.prio (ws_queue s) id = Some pr -> (lo <= pr)%N) ->
    forall pr, In pr (popped_ranks xs) -> (lo <= pr)%N.
  Proof.
    intros p pol s xs last lo Hfits Hreach Hpath.
    revert Hreach; induction Hpath as [s|s s1 xs last Hstep Hpath IH];
      intros Hreach Hstable Hlower pj Hin.
    - contradiction.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
      assert (Hfirst : heads_unchanged pol s s1).
      { apply (Hstable s s1); [now left|exact Hstep]. }
      assert (Htail : stable_segment p pol xs).
      { intros t t1 Ht Hnext; apply (Hstable t t1); [now right|exact Hnext]. }
      cbn [popped_ranks flat_map] in Hin; rewrite Hpop in Hin; cbn [app] in Hin.
      destruct Hin as [<-|Hin].
      + destruct Hfits as [Hwf [_ Hprio]].
        pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
        apply (Hlower id pr); exact (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop)).
      + apply (IH (reachable_step p pol s s1 Hreach Hstep) Htail
          (stable_step_lower p pol s s1 lo Hfits Hreach Hstep Hfirst Hlower) pj Hin).
  Qed.

  (** A row absent below the current frontier is never popped in the stable suffix. *)
  Lemma stable_path_avoids : forall p pol s xs last lo id r,
    fits p pol -> reachable p pol s -> wl_path (step p pol) s xs last ->
    stable_segment p pol xs -> source_row p id = Some r ->
    (N.pos (row_rank p pol r) <= lo)%N -> Q.prio (ws_queue s) id = None ->
    (forall j pj, Q.prio (ws_queue s) j = Some pj -> (lo <= pj)%N) ->
    ~ In id (popped_ids xs).
  Proof.
    intros p pol s xs last lo id r Hfits Hreach Hpath.
    revert Hreach; induction Hpath as [s|s s1 xs last Hstep Hpath IH];
      intros Hreach Hstable Hrow Hrank Habsent Hlower.
    - intros Hin; contradiction.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [popped [q Hpop]]].
      assert (Hfirst : heads_unchanged pol s s1).
      { apply (Hstable s s1); [now left|exact Hstep]. }
      assert (Htail : stable_segment p pol xs).
      { intros t t1 Ht Hnext; apply (Hstable t t1); [now right|exact Hnext]. }
      assert (Habsent1 : Q.prio (ws_queue s1) id = None).
      { eapply (stable_step_absent_low p pol s s1 lo id r); eassumption. }
      assert (Hlower1 : forall j pj, Q.prio (ws_queue s1) j = Some pj -> (lo <= pj)%N).
      { eapply stable_step_lower; eassumption. }
      cbn [popped_ids flat_map]; rewrite Hpop; cbn [app].
      intros [Hequal|Hin].
      + subst popped; destruct Hfits as [Hwf [_ Hprio]].
        pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
        pose proof (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop)); congruence.
      + apply (IH (reachable_step p pol s s1 Hreach Hstep) Htail Hrow Hrank Habsent1 Hlower1).
        exact Hin.
  Qed.

  (** Stable segments pop each numbered occurrence at most once. *)
  Lemma stable_no_repeat : forall p pol s xs last, fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> stable_segment p pol xs -> NoDup (popped_ids xs).
  Proof.
    intros p pol s xs last Hfits Hreach Hpath.
    revert Hreach; induction Hpath as [s|s s1 xs last Hstep Hpath IH];
      intros Hreach Hstable.
    - constructor.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
      assert (Hfirst : heads_unchanged pol s s1).
      { apply (Hstable s s1); [now left|exact Hstep]. }
      assert (Htail : stable_segment p pol xs).
      { intros t t1 Ht Hnext; apply (Hstable t t1); [now right|exact Hnext]. }
      pose proof (reachable_step p pol s s1 Hreach Hstep) as Hreach1.
      destruct (stable_step_frontier p pol s s1 pr id q Hfits Hreach Hstep Hfirst Hpop)
        as [Habsent Hlower].
      cbn [popped_ids flat_map]; rewrite Hpop; cbn [app]; constructor.
      + destruct Hfits as [Hwf [Hcuts Hprio]].
        assert (Hfits : fits p pol) by now repeat split.
        pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
        destruct (reachable_live_row p pol s id pr Hwf Hprio Hreach
          (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop))) as [r [Hrow [_ Hrank]]].
        apply (stable_path_avoids p pol s1 xs last pr id r Hfits Hreach1 Hpath Htail Hrow).
        * lia.
        * exact Habsent.
        * exact Hlower.
      + apply IH; assumption.
  Qed.

  (** A continuing trace records exactly one popped identifier per callback. *)
  Lemma popped_ids_length : forall p pol s xs last,
    wl_path (step p pol) s xs last -> length (popped_ids xs) = length xs.
  Proof.
    intros p pol s xs last Hpath; induction Hpath as [s|s s1 xs last Hstep Hpath IH].
    - reflexivity.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
      cbn [popped_ids flat_map]; rewrite Hpop; cbn [app length]; f_equal; exact IH.
  Qed.

  (** Every identifier popped on a reachable path is a listed occurrence. *)
  Lemma popped_ids_supported : forall p pol s xs last, fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> incl (popped_ids xs) (row_ids p).
  Proof.
    intros p pol s xs last Hfits Hreach Hpath.
    revert Hreach; induction Hpath as [s|s s1 xs last Hstep Hpath IH]; intros Hreach j Hin.
    - contradiction.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
      cbn [popped_ids flat_map] in Hin; rewrite Hpop in Hin; cbn [app] in Hin.
      destruct Hin as [<-|Hin].
      + destruct Hfits as [Hwf [_ Hprio]].
        pose proof (proj1 (proj1 (reachable_invariant p pol s Hwf Hprio Hreach))) as Hqueue.
        destruct (reachable_live_row p pol s id pr Hwf Hprio Hreach
          (proj1 (Q.pop_min (ws_queue s) pr id q Hqueue Hpop))) as [r [Hrow _]].
        exact (proj1 (source_row_member p id r Hrow)).
      + exact (IH (reachable_step p pol s s1 Hreach Hstep) j Hin).
  Qed.

  (** A stable segment performs at most one callback per listed occurrence. *)
  Lemma stable_length_le : forall p pol s xs last, fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> stable_segment p pol xs -> length xs <= C p.
  Proof.
    intros p pol s xs last Hfits Hreach Hpath Hstable.
    pose proof (stable_no_repeat p pol s xs last Hfits Hreach Hpath Hstable) as Hunique.
    pose proof (popped_ids_supported p pol s xs last Hfits Hreach Hpath) as Hsupport.
    assert (Hlength : length (popped_ids xs) <= length (row_ids p)).
    { eapply NoDup_incl_length; eassumption. }
    now rewrite (popped_ids_length p pol s xs last Hpath), row_ids_length in Hlength.
  Qed.

  (** Cut edges make popped row ranks nondecreasing in a stable segment. *)
  Lemma W5_priority : forall p pol s xs last i j a b,
    fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last -> stable_segment p pol xs ->
    i < j -> nth_error (popped_ranks xs) i = Some a ->
    nth_error (popped_ranks xs) j = Some b -> (a <= b)%N.
  Proof.
    intros p pol s xs last i j a b Hfits Hreach Hpath.
    revert i j a b Hreach; induction Hpath as [s|s s1 xs last Hstep Hpath IH];
      intros i j a b Hreach Hstable Hij Hia Hjb.
    - destruct i; discriminate.
    - destruct (continuing_pop p pol s s1 Hstep) as [pr [id [q Hpop]]].
      assert (Hfirst : heads_unchanged pol s s1).
      { apply (Hstable s s1); [now left|exact Hstep]. }
      assert (Htail : stable_segment p pol xs).
      { intros t t1 Ht Hnext; apply (Hstable t t1); [now right|exact Hnext]. }
      pose proof (reachable_step p pol s s1 Hreach Hstep) as Hreach1.
      cbn [popped_ranks flat_map] in Hia, Hjb; rewrite Hpop in Hia, Hjb.
      cbn [app] in Hia, Hjb.
      destruct i as [|i], j as [|j]; try lia.
      + cbn [nth_error] in Hia, Hjb; injection Hia as <-.
        pose proof (proj2 (stable_step_frontier p pol s s1 pr id q Hfits Hreach Hstep
          Hfirst Hpop)) as Hlower.
        apply (stable_path_ranks_lower p pol s1 xs last pr Hfits Hreach1 Hpath Htail
          Hlower b).
        eapply nth_error_In; exact Hjb.
      + cbn [nth_error] in Hia, Hjb.
        apply (IH i j a b Hreach1 Htail); [lia|exact Hia|exact Hjb].
  Qed.
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
    (T_step p pol s + c_loopN + queue_phi p s1 <=
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
    (trace_cost p pol xs + c_loopN * N.of_nat (length xs) + queue_phi p last <=
      k_loop * work p pol + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)
  (** The visit count supplies fuel without charging abstract value sizes to fuel construction. *)
  Lemma W7_visits : forall p pol xs last, fits p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    (N.of_nat (length xs) < k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Proof. Admitted. (* STUB *)

  (** * Driver outcomes and global bounds *)

  (** Stopping callbacks must solve and must fit the final driver budget. *)
  Lemma W7_stop : forall p pol s result, S.wf p -> prio_ok p pol -> reachable p pol s ->
    step p pol s = inr result ->
    (exists m, result = Solved m) /\
    (T_step p pol s <= k_loop * (N.of_nat (C p) * unit p + 1) + queue_phi p s)%N.
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
    (T_step p pol s + all_head_phi p pol s1 + c_loopN <= all_head_phi p pol s)%N.
  Proof. Admitted. (* STUB *)
  (** The independent widening fallback needs weighted degree absorbed by its public budget. *)
  Lemma W7_all_heads_initial : forall p pol, S.wf p -> prio_ok p pol -> all_heads p pol ->
    (all_head_phi p pol (prepare p pol) <=
      2 * k_credit * all_head_work p pol + queue_phi p (prepare p pol))%N.
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

Module WorklistLeast (L : WLATTICE_T) (LB : LUB L) (S : SYSTEM_T L)
    (P : POLICY_T L) (Q : PQ_T) (G : DIGRAPH_T) (W : WTO_T)
    (Sched : SCHEDULE_T L S G W) (B : BUDGET L S)
    (V : WORKLIST_ALL L S P Q G W Sched B)
    <: SOLVER_LEAST L LB S V
    <: WORKLIST_LEAST_PLAN L LB S P Q G W Sched B V.
  Definition widening_free (pol : policy L.wparam) : Prop :=
    forall c, trie_get c (heads pol) = None.
  (** Widening-free reachable stores lie below every post-solution of a monotone system. *)
  Lemma F10_least : forall p pol s s', S.wf p -> S.monotone p -> widening_free pol ->
    V.reachable p pol s -> S.post_solution p s' ->
    forall x, L.leb (V.look s x) (s' x) = true.
  Proof. Admitted. (* STUB *)
  (** A solved widening-free candidate lies below every post-solution. *)
  Lemma run_least : forall p pol fuel m s', S.wf p -> S.monotone p ->
    widening_free pol -> V.run p pol fuel = Solved m -> S.post_solution p s' ->
    forall x, L.leb (look_or S.key_code L.bot m x) (s' x) = true.
  Proof. Admitted. (* STUB *)
End WorklistLeast.
