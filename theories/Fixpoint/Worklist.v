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

(** Every zero bit supplies one unit of credit for a later binary borrow. *)
Fixpoint fuel_zero_bits_positive (p : positive) : N :=
  match p with
  | xI p => fuel_zero_bits_positive p
  | xO p => (1 + fuel_zero_bits_positive p)%N
  | xH => 0%N
  end.

(** Zero fuel has no remaining borrow credit. *)
Definition fuel_zero_bits (fuel : N) : N :=
  match fuel with
  | N0 => 0%N
  | N.pos p => fuel_zero_bits_positive p
  end.

(** The binary representation bounds its number of zero bits. *)
Lemma fuel_zero_bits_positive_le : forall p,
  (fuel_zero_bits_positive p <= N.of_nat (Pos.size_nat p))%N.
Proof.
  induction p as [p IH|p IH|]; cbn [fuel_zero_bits_positive Pos.size_nat];
    rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Initial borrow credit is bounded by the supplied fuel's bit length. *)
Lemma fuel_zero_bits_le : forall fuel,
  (fuel_zero_bits fuel <= N.of_nat (N.size_nat fuel))%N.
Proof.
  intros [|p]; [reflexivity|apply fuel_zero_bits_positive_le].
Qed.

(** The recursive part of a borrow spends one unit for each zero bit it clears. *)
Lemma fuel_zero_bits_pred_double : forall p,
  (Pos.T_pred_double p + fuel_zero_bits_positive (Pos.pred_double p) <=
    fuel_zero_bits_positive p + 2)%N.
Proof.
  induction p as [p IH|p IH|]; time_unfold @Pos.T_pred_double;
    cbn [Pos.pred_double fuel_zero_bits_positive]; lia.
Qed.

(** The positive predecessor uses constant work after accounting for cleared zero bits. *)
Lemma fuel_zero_bits_pred_positive : forall p,
  (Pos.T_pred_N p + fuel_zero_bits (Pos.pred_N p) <=
    fuel_zero_bits_positive p + 2)%N.
Proof.
  intros [p|p|]; time_unfold @Pos.T_pred_N;
    cbn [Pos.pred_N fuel_zero_bits fuel_zero_bits_positive].
  - lia.
  - pose proof (fuel_zero_bits_pred_double p); lia.
  - lia.
Qed.

(** Each binary decrement costs at most three units plus the zero-bit credit it spends. *)
Lemma fuel_zero_bits_pred : forall fuel,
  (N.T_pred fuel + fuel_zero_bits (N.pred fuel) <= fuel_zero_bits fuel + 3)%N.
Proof.
  intros [|p]; time_unfold @N.T_pred; cbn [N.pred fuel_zero_bits].
  - lia.
  - pose proof (fuel_zero_bits_pred_positive p); lia.
Qed.

(** A continuing binary callback exposes its underlying step and amortised borrow cost. *)
Lemma loopN_step_continue_clock {St R : Type} (step : St -> St + R)
    (T_step : St -> N) : forall fs fs1 Hlt,
  loopN_step step fs = inl (exist _ fs1 Hlt) ->
  step (snd fs) = inl (snd fs1) /\
  (T_loopN_step step T_step fs + fuel_zero_bits (fst fs1) <=
    T_step (snd fs) + fuel_zero_bits (fst fs) + 4)%N.
Proof.
  intros [fuel s] [fuel1 s1] Hlt Hgo.
  destruct fuel as [|p]; [discriminate|].
  cbn [loopN_step] in Hgo.
  destruct (step s) as [next|result] eqn:Hstep; [|discriminate].
  assert (Hpair : (N.pred (N.pos p), next) = (fuel1, s1)).
  { exact (f_equal (fun answer =>
      match answer with inl smaller => proj1_sig smaller | inr _ => (0%N, s) end) Hgo). }
  injection Hpair as Hfuel Hstate; subst fuel1 s1.
  split; [exact Hstep|].
  time_unfold @T_loopN_step; cbn [fst snd]; rewrite Hstep.
  change (1 + (T_step s + N.T_pred (N.pos p)) +
    fuel_zero_bits (N.pred (N.pos p)) <=
    T_step s + fuel_zero_bits (N.pos p) + 4)%N.
  pose proof (fuel_zero_bits_pred (N.pos p)) as Hborrow; lia.
Qed.

(** A stopping binary callback either exhausts fuel or executes its final source callback. *)
Lemma loopN_step_stop_clock {St R : Type} (step : St -> St + R)
    (T_step : St -> N) : forall fs result,
  loopN_step step fs = inr result ->
  (T_loopN_step step T_step fs <= 1 +
    match step (snd fs) with inl _ => 0 | inr _ => T_step (snd fs) end)%N.
Proof.
  intros [fuel s] result Hstop; destruct fuel as [|p].
  - time_unfold @T_loopN_step; cbn [snd]; lia.
  - cbn [loopN_step] in Hstop.
    destruct (step s) as [next|out] eqn:Hstep; [discriminate|].
    time_unfold @T_loopN_step; cbn [snd]; rewrite Hstep; lia.
Qed.

(** The accessibility clock follows a real path and pays five units per continuing callback. *)
Lemma loopN_acc_trace_clock {St R : Type} (step : St -> St + R)
    (T_step : St -> N) : forall fs (H : Acc (@loopN_lt St) fs),
  exists xs last, wl_path step (snd fs) xs last /\
    (T_loop loopN_lt (loopN_step step) (T_loopN_step step T_step) fs H <=
      fold_right N.add 0%N (List.map T_step xs) + 5 * N.of_nat (length xs) +
      fuel_zero_bits (fst fs) + 2 +
      match step last with inl _ => 0 | inr _ => T_step last end)%N.
Proof.
  intros fs H; induction H as [fs Hacc IH] using Acc_ind_dep.
  destruct (loopN_step step fs) as [[fs1 Hlt]|result] eqn:Hdriver.
  - destruct (IH fs1 Hlt) as [xs [last [Hpath Hclock]]].
    destruct (loopN_step_continue_clock step T_step fs fs1 Hlt Hdriver)
      as [Hstep Hborrow].
    exists (snd fs :: xs), last; split; [econstructor; eassumption|].
    time_unfold @T_loop; cbn [Acc_inv]; rewrite Hdriver.
    cbn [List.map fold_right length]; rewrite Nat2N.inj_succ; lia.
  - exists [], (snd fs); split; [constructor|].
    pose proof (loopN_step_stop_clock step T_step fs result Hdriver) as Hstop.
    time_unfold @T_loop; cbn [Acc_inv]; rewrite Hdriver.
    cbn [List.map fold_right length]; lia.
Qed.

(** The public binary driver adds only its own call and the initial fuel's bit length. *)
Lemma loopN_trace_clock {St R : Type} (step : St -> St + R)
    (T_step : St -> N) : forall fuel initial,
  exists xs last, wl_path step initial xs last /\
    (T_loopN step T_step fuel initial <=
      fold_right N.add 0%N (List.map T_step xs) + 5 * N.of_nat (length xs) +
      N.of_nat (N.size_nat fuel) + 3 +
      match step last with inl _ => 0 | inr _ => T_step last end)%N.
Proof.
  intros fuel initial.
  pose (Hfuel := Acc_intro_generator 32
    (Inverse_Image.wf_inverse_image (N * St) N N.lt fst N.lt_wf_0)
    (fuel, initial)).
  destruct (loopN_acc_trace_clock step T_step (fuel, initial) Hfuel)
    as [xs [last [Hpath Hclock]]].
  exists xs, last; split; [exact Hpath|].
  pose proof (fuel_zero_bits_le fuel) as Hbits.
  change (T_loop loopN_lt (loopN_step step) (T_loopN_step step T_step)
    (fuel, initial) Hfuel <=
    fold_right N.add 0%N (List.map T_step xs) + 5 * N.of_nat (length xs) +
    fuel_zero_bits fuel + 2 +
    match step last with inl _ => 0 | inr _ => T_step last end)%N in Hclock.
  time_unfold @T_loopN.
  change (1 + T_loop loopN_lt (loopN_step step) (T_loopN_step step T_step)
    (fuel, initial) Hfuel <=
    fold_right N.add 0%N (List.map T_step xs) + 5 * N.of_nat (length xs) +
    N.of_nat (N.size_nat fuel) + 3 +
    match step last with inl _ => 0 | inr _ => T_step last end)%N.
  lia.
Qed.

(** Positive source callback costs pay one unit for every entry of a finite trace. *)
Lemma loop_trace_length_le {St : Type} (T_step : St -> N) :
  (forall s, (1 <= T_step s)%N) -> forall xs,
  (N.of_nat (length xs) <= fold_right N.add 0%N (List.map T_step xs))%N.
Proof.
  intros Hpositive xs; induction xs as [|s xs IH].
  - reflexivity.
  - cbn [length List.map fold_right]; rewrite Nat2N.inj_succ.
    pose proof (Hpositive s); lia.
Qed.

(** Finite-prefix and stopping budgets bound the actual binary clock without a fuel factor. *)
Lemma T_loopN_prefix_bound {St R : Type} (step : St -> St + R)
    (T_step : St -> N) (Phi : St -> N) initial fuel Budget Stop :
  (forall s, (1 <= T_step s)%N) ->
  (forall xs last, wl_path step initial xs last ->
    (fold_right N.add 0%N (List.map T_step xs) + Phi last <= Budget)%N) ->
  (forall xs last result, wl_path step initial xs last -> step last = inr result ->
    (T_step last <= Stop + Phi last)%N) ->
  (T_loopN step T_step fuel initial <=
    6 * Budget + Stop + N.of_nat (N.size_nat fuel) + 3)%N.
Proof.
  intros Hpositive Hprefix Hstop.
  destruct (loopN_trace_clock step T_step fuel initial) as [xs [last [Hpath Hclock]]].
  pose proof (Hprefix xs last Hpath) as Hbudget.
  pose proof (loop_trace_length_le T_step Hpositive xs) as Hlength.
  destruct (step last) as [next|result] eqn:Hlast; [lia|].
  pose proof (Hstop xs last result Hpath Hlast); lia.
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

  (** Use the proved loop equations without expanding its accessibility proof. *)
  Local Opaque loopN.

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
  Definition k_prepare : N :=
    (4096 * (c_lookup + P.c_pol + Q.c_pq + c_loopN + 1))%N.
  Definition k_eval : N := (64 * (c_lookup + S.c_sys + 1))%N.
  Definition c_enqueue : N :=
    (128 * (c_lookup + P.c_pol + Q.c_pq + c_loopN + 1))%N.
  Definition k_update : N :=
    (512 * (c_lookup + P.c_pol + Q.c_pq + c_loopN + 1))%N.
  Definition k_credit : N :=
    (64 * (k_eval + k_update + c_step + S.c_sys + PTrieT.c_trie + Q.c_pq + c_loopN + 1))%N.
  Definition k_round : N := (2 * k_credit)%N.
  Definition k_loop : N :=
    (64 * (k_prepare + k_eval + k_update + k_credit + k_round +
      c_step + c_loopN + Q.c_pq + 1))%N.
  Definition k_fuel : N := 1%N.
  Definition c_wl : N :=
    (16 * (k_prepare + k_credit + k_loop * (k_prepare + 1) +
      c_loopN + Q.c_pq + 1))%N.
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
  (** A strict value update changes the store and counter before touching queue metadata. *)
  Definition update_base pol (s : state) (x : S.key) (a : L.t) : state :=
    let c := S.key_code x in
    let ac := P.update pol c (counter s c) (look s x) a in
    WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
      (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s).

  (** Store and counter writes do not change the prepared cache properties. *)
  Lemma update_base_prepared : forall p pol s x a, prepared p pol s ->
    prepared p pol (update_base pol s x a).
  Proof.
    intros p pol s x a Hprepared; exact Hprepared.
  Qed.

  (** Arming a fully live reader bucket preserves prepared-state coverage. *)
  Lemma arm_prepared : forall p pol c s, prepared p pol s ->
    (forall id, In id (readers s c) -> exists pr, Q.prio (ws_queue s) id = Some pr) ->
    prepared p pol (arm c s).
  Proof.
    intros p pol c s [Hmeta [Hlive [Hwf [Hexact [Harmed Hranks]]]]] Hcovered.
    split; [exact Hmeta|]; split; [exact Hlive|]; split; [exact Hwf|].
    split; [exact Hexact|]; split; [|exact Hranks].
    intros key id Hflag Hin.
    change (trie_get key (PTrieCode.set c tt (ws_armed s)) = Some tt) in Hflag.
    rewrite trie_get_set in Hflag; destruct (Pos.eqb key c) eqn:Heq.
    - apply Pos.eqb_eq in Heq; subst key; now apply Hcovered.
    - eapply Harmed; [exact Hflag|exact Hin].
  Qed.

  (** Arming a bucket preserves all components of the reference view. *)
  Lemma arm_view : forall c s, wl_view (arm c s) = wl_view s.
  Proof.
    reflexivity.
  Qed.

  (** Indexed updates decompose into a store write and a guarded reader enqueue. *)
  Lemma update_one_core : forall p pol s x a,
    update_one p pol s (x, a) =
      if L.leb a (look s x) then s else
      match trie_get (S.key_code x) (ws_armed s) with
      | Some _ => update_base pol s x a
      | None => arm (S.key_code x)
          (enqueue p pol (readers s (S.key_code x)) (update_base pol s x a))
      end.
  Proof.
    reflexivity.
  Qed.

  (** Reference updates use the same store and counter write as the indexed operation. *)
  Lemma reference_update_view : forall p pol s x a,
    reference_update p pol (wl_view s) (x, a) =
      if L.leb a (look s x) then wl_view s else
        reference_enqueue p pol (source_readers p (S.key_code x))
          (wl_view (update_base pol s x a)).
  Proof.
    reflexivity.
  Qed.

  (** Each intermediate update keeps the cache, queue and armed-reader invariants. *)
  Lemma update_prepared : forall p pol s x a, prepared p pol s ->
    prepared p pol (update_one p pol s (x, a)).
  Proof.
    intros p pol s x a Hprepared; rewrite update_one_core.
    destruct (L.leb a (look s x)); [exact Hprepared|].
    destruct (trie_get (S.key_code x) (ws_armed s)).
    - now apply update_base_prepared.
    - apply arm_prepared; [apply enqueue_prepared, update_base_prepared, Hprepared|].
      intros id Hin; change (In id (readers s (S.key_code x))) in Hin.
      pose proof Hin as Hrequested; rewrite (proj2 (proj1 Hprepared)) in Hin.
      apply source_readers_spec in Hin as [r [y [Hsource Hread]]].
      eapply enqueue_contains.
      + apply update_base_prepared, Hprepared.
      + exact Hrequested.
      + exact Hsource.
  Qed.

  (** Armed buckets skip exactly the reference enqueue that would leave the queue unchanged. *)
  Lemma update_agreement : forall p pol s x a, prepared p pol s ->
    wl_view (update_one p pol s (x, a)) = reference_update p pol (wl_view s) (x, a).
  Proof.
    intros p pol s x a Hprepared; rewrite update_one_core, reference_update_view.
    destruct (L.leb a (look s x)); [reflexivity|].
    destruct (trie_get (S.key_code x) (ws_armed s)) as [[]|] eqn:Hflag.
    - symmetry; apply reference_enqueue_existing; intros id Hin.
      rewrite <- (proj2 (proj1 Hprepared)) in Hin.
      destruct Hprepared as [Hmeta [Hlive [Hwf [Hexact [Harmed Hranks]]]]].
      eapply Harmed; [exact Hflag|exact Hin].
    - rewrite arm_view, enqueue_agreement by (apply update_base_prepared; exact Hprepared).
      now rewrite (proj2 (proj1 Hprepared)).
  Qed.

  (** Every update has the original projected behavior on prepared states. *)
  Lemma F6_agreement : forall p pol s xa, prepared p pol s ->
    wl_view (update_one p pol s xa) = reference_update p pol (wl_view s) xa.
  Proof.
    intros p pol s [x a] Hprepared; now apply update_agreement.
  Qed.
  (** Every intermediate update maintains prepared-state agreement without client duties. *)
  Lemma F6_prepared : forall p pol s xa, prepared p pol s ->
    prepared p pol (update_one p pol s xa).
  Proof.
    intros p pol s [x a] Hprepared; now apply update_prepared.
  Qed.
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
  (** Clearing a dependency list removes precisely its declared read codes. *)
  Lemma clear_reads_lookup : forall xs (marked : ptrie Datatypes.unit) c,
    trie_get c (fold_left (fun acc x => PTrieCode.remove (S.key_code x) acc) xs marked) =
      if existsb (fun x => Pos.eqb c (S.key_code x)) xs then None else trie_get c marked.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros marked c; [reflexivity|].
    cbn [fold_left existsb]; rewrite IH, trie_get_remove.
    destruct (existsb (fun y => Pos.eqb c (S.key_code y)) xs),
      (Pos.eqb c (S.key_code x)); reflexivity.
  Qed.

  (** Every flag surviving a pop was already armed and does not name the popped reader. *)
  Lemma pop_flag_readers : forall p s id q c, metadata p s ->
    trie_get c (ws_armed (after_pop p s id q)) = Some tt ->
    trie_get c (ws_armed s) = Some tt /\ ~ In id (readers s c).
  Proof.
    intros p s id q c [Hrows Hreaders] Hflag; unfold after_pop in Hflag.
    cbn [ws_armed] in Hflag; destruct (row_at s id) as [r|] eqn:Hrow.
    - rewrite clear_reads_lookup in Hflag.
      destruct (existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)) eqn:Hclear;
        [discriminate|].
      split; [exact Hflag|]; intro Hin; rewrite Hreaders in Hin.
      apply source_readers_spec in Hin as [row [x [Hsource [Hread Hcode]]]].
      rewrite <- (Hrows id), Hrow in Hsource; injection Hsource as Heq; subst row.
      assert (Hpresent : existsb (fun y => Pos.eqb c (S.key_code y)) (S.deps p r) = true).
      { apply existsb_exists; exists x; split; [exact Hread|].
        apply Pos.eqb_eq; symmetry; exact Hcode. }
      congruence.
    - split; [exact Hflag|]; intro Hin; rewrite Hreaders in Hin.
      apply source_readers_spec in Hin as [r [x [Hsource Hread]]].
      rewrite <- (Hrows id), Hrow in Hsource; discriminate.
  Qed.

  (** Removing the popped live marker restores agreement with the residual queue. *)
  Lemma after_pop_live : forall p s pr id q1, live_agrees s -> Q.wf (ws_queue s) ->
    Q.pop (ws_queue s) = Some (pr, id, q1) -> live_agrees (after_pop p s id q1).
  Proof.
    intros p s pr id q1 Hlive Hwf Hpop x.
    destruct (Q.pop_min (ws_queue s) pr id q1 Hwf Hpop)
      as [Hselected [Hleast [Hremoved Hothers]]].
    change (trie_get x (PTrieCode.remove id (ws_live s)) = Some tt <->
      exists priority, Q.prio q1 x = Some priority).
    rewrite trie_get_remove; destruct (Pos.eqb x id) eqn:Heq.
    - apply Pos.eqb_eq in Heq; subst x; rewrite Hremoved.
      split; [discriminate|intros [priority H]; discriminate].
    - apply Pos.eqb_neq in Heq; rewrite Hothers by exact Heq; apply Hlive.
  Qed.

  (** Popping preserves prepared metadata, exact queue size and surviving armed coverage. *)
  Lemma pop_prepared : forall p pol s pr id q1, prepared p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) -> prepared p pol (after_pop p s id q1).
  Proof.
    intros p pol s pr id q1 [Hmeta [Hlive [Hwf [Hexact [Harmed Hranks]]]]] Hpop.
    destruct (Q.pop_min (ws_queue s) pr id q1 Hwf Hpop)
      as [Hselected [Hleast [Hremoved Hothers]]].
    split; [exact Hmeta|]; split; [eapply after_pop_live; eassumption|].
    split; [eapply Q.wf_pop; eassumption|]; split.
    - eapply queue_exact_pop; eassumption.
    - split; [|exact Hranks]; intros c target Hflag Hin.
      destruct (pop_flag_readers p s id q1 c Hmeta Hflag) as [Hbefore Hnotin].
      destruct (Harmed c target Hbefore Hin) as [priority Hprio].
      assert (Hother : target <> id) by (intro Heq; subst target; now apply Hnotin).
      exists priority; change (Q.prio q1 target = Some priority).
      now rewrite Hothers by exact Hother.
  Qed.

  (** Ordered output application preserves preparation and both immutable index tables. *)
  Lemma updates_prepared : forall p pol outs s, prepared p pol s ->
    prepared p pol (fold_left (update_one p pol) outs s) /\
    ws_rows (fold_left (update_one p pol) outs s) = ws_rows s /\
    ws_readers (fold_left (update_one p pol) outs s) = ws_readers s.
  Proof.
    intros p pol outs; induction outs as [|xa outs IH]; intros s Hprepared.
    - split; [exact Hprepared|split; reflexivity].
    - cbn [fold_left].
      destruct (IH (update_one p pol s xa) (F6_prepared p pol s xa Hprepared))
        as [Hfinal [Hrows Hreaders]].
      destruct (F6_tables p pol s xa) as [Hrow_step Hreader_step].
      split; [exact Hfinal|]; split; congruence.
  Qed.

  (** Ordered output application commutes with the reference-state projection. *)
  Lemma updates_agreement : forall p pol outs s, prepared p pol s ->
    wl_view (fold_left (update_one p pol) outs s) =
      fold_left (reference_update p pol) outs (wl_view s).
  Proof.
    intros p pol outs; induction outs as [|xa outs IH]; intros s Hprepared;
      [reflexivity|].
    cbn [fold_left]; rewrite IH by (apply F6_prepared; exact Hprepared).
    now rewrite F6_agreement by exact Hprepared.
  Qed.

  (** Popping preserves cache agreement and restores live agreement for the residual queue. *)
  Lemma F7_pop_prepared : forall p pol s pr id q1, prepared p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) ->
    prepared p pol (after_pop p s id q1).
  Proof.
    apply pop_prepared.
  Qed.
  (** The full callback retains every observable behavior of the original callback. *)
  Lemma F7_agreement : forall p pol s, prepared p pol s ->
    view_result (step p pol s) = reference_step p pol (wl_view s).
  Proof.
    intros p pol s Hprepared; unfold step, reference_step, view_result.
    cbn [wl_view wl_store wl_counters wl_queue].
    destruct (Q.pop (ws_queue s)) as [[[pr id] q1]|] eqn:Hpop; [|reflexivity].
    rewrite <- (proj1 (proj1 Hprepared) id).
    destruct (row_at s id) as [r|] eqn:Hrow; [|reflexivity].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|reflexivity].
    f_equal; rewrite updates_agreement by (eapply F7_pop_prepared; eassumption).
    reflexivity.
  Qed.
  (** Continuing callbacks retain both tables and all prepared-state facts. *)
  Lemma F7_prepared : forall p pol s s1, prepared p pol s -> step p pol s = inl s1 ->
    prepared p pol s1 /\ ws_rows s1 = ws_rows s /\ ws_readers s1 = ws_readers s.
  Proof.
    intros p pol s s1 Hprepared Hstep; unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q1]|] eqn:Hpop; [|discriminate].
    destruct (row_at s id) as [r|] eqn:Hrow; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    exact (updates_prepared p pol ((S.target p r, a) :: ss) (after_pop p s id q1)
      (F7_pop_prepared p pol s pr id q1 Hprepared Hpop)).
  Qed.
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
  Proof.
    intros p pol fuel.
    assert (Hview :
      match loopN (step p pol) fuel (prepare p pol) with
      | inl s => inl (wl_view s)
      | inr result => inr result
      end = loopN (reference_step p pol) fuel (wl_view (prepare p pol))).
    { apply (loopN_view (step p pol) (reference_step p pol) wl_view (prepared p pol)).
      - intros s Hprepared; exact (F7_agreement p pol s Hprepared).
      - intros s s1 Hprepared Hstep; exact (proj1 (F7_prepared p pol s s1 Hprepared Hstep)).
      - apply F4_metadata. }
    unfold run; rewrite <- Hview.
    destruct (loopN (step p pol) fuel (prepare p pol)); reflexivity.
  Qed.

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
  (** An update covers the supplied contribution. *)
  Lemma look_update_covers : forall p pol s x a,
    L.leb a (look (update_one p pol s (x, a)) x) = true.
  Proof.
    intros p pol s x a; rewrite <- raw_value_look, raw_value_update_same.
    apply (proj2 (P.update_ub _ _ _ _ _)).
  Qed.

  (** Every lookup grows monotonically while contributions are processed. *)
  Lemma look_update_mono : forall p pol s x a y,
    L.leb (look s y) (look (update_one p pol s (x, a)) y) = true.
  Proof.
    intros p pol s x a y; rewrite <- !raw_value_look.
    destruct (Pos.eq_dec (S.key_code y) (S.key_code x)) as [Heq|Hneq].
    - rewrite Heq, raw_value_update_same, raw_value_look.
      apply (proj1 (P.update_ub _ _ _ _ _)).
    - rewrite raw_value_update_other by exact Hneq; apply L.leb_refl.
  Qed.

  Lemma look_fold_mono : forall p pol outs s x,
    L.leb (look s x) (look (fold_left (update_one p pol) outs s) x) = true.
  Proof.
    intros p pol outs; induction outs as [|[y a] outs IH]; intros s x.
    - apply L.leb_refl.
    - cbn [fold_left]; eapply L.leb_trans; [apply look_update_mono|apply IH].
  Qed.

  (** The final store covers every output occurrence, including repeated keys. *)
  Lemma fold_outputs_cover : forall p pol outs s x a, In (x, a) outs ->
    L.leb a (look (fold_left (update_one p pol) outs s) x) = true.
  Proof.
    intros p pol outs; induction outs as [|[y b] outs IH]; intros s x a Hin.
    - contradiction.
    - cbn [fold_left]; destruct Hin as [Heq|Hin].
      + inversion Heq; subst; eapply L.leb_trans.
        * apply look_update_covers.
        * apply look_fold_mono.
      + now apply IH.
  Qed.

  (** Increasing lookups preserves acceptance of a fixed row result. *)
  Lemma row_ok_lookup_mono : forall (before after : S.key -> L.t) target out,
    (forall x, L.leb (before x) (after x) = true) ->
    row_ok L.leb before target out = true -> row_ok L.leb after target out = true.
  Proof.
    intros before after target [[a ss]|] Hmono Hrow; [|discriminate].
    cbn [row_ok] in Hrow |- *; apply andb_true_iff in Hrow as [Hmain Hsides].
    apply andb_true_iff; split.
    - eapply L.leb_trans; [exact Hmain|apply Hmono].
    - apply forallb_forall; intros [x b] Hin; cbn [fst snd].
      eapply L.leb_trans; [|apply Hmono].
      apply (proj1 (forallb_forall _ _) Hsides (x, b) Hin).
  Qed.

  (** An absent reader cannot have been live before a contribution. *)
  Lemma update_outside_before : forall p pol s x a id,
    Q.prio (ws_queue (update_one p pol s (x, a))) id = None ->
    Q.prio (ws_queue s) id = None.
  Proof.
    intros p pol s x a id Hnone.
    destruct (Q.prio (ws_queue s) id) as [pr|] eqn:Hprio; [|reflexivity].
    destruct (update_queue_retains p pol s x a id pr Hprio) as [next Hnext]; congruence.
  Qed.

  (** Every declared dependency of an absent reader retains its old value. *)
  Lemma update_outside_reads : forall p pol s x a id r,
    prepared p pol s -> source_row p id = Some r ->
    Q.prio (ws_queue (update_one p pol s (x, a))) id = None ->
    forall y, In y (S.deps p r) ->
      look (update_one p pol s (x, a)) y = look s y.
  Proof.
    intros p pol s x a id r Hprepared Hsource Hnone y Hy.
    destruct (L.leb a (look s x)) eqn:Hstrict.
    - rewrite F6_indexed; cbn beta iota zeta; now rewrite Hstrict.
    - assert (Hneq : S.key_code y <> S.key_code x).
      { intro Heq.
        assert (Hreader : In id (readers s (S.key_code x))).
        { rewrite (proj2 (proj1 Hprepared)); apply source_readers_spec.
          exists r, y; split; [exact Hsource|]; split; [exact Hy|exact Heq]. }
        destruct (update_reader_live p pol s x a id Hprepared Hstrict Hreader)
          as [pr Hprio]; congruence. }
      rewrite <- !raw_value_look; now rewrite raw_value_update_other.
  Qed.

  (** A reader absent after a fold was absent throughout, with unchanged dependencies. *)
  Lemma fold_outside_reads : forall p pol outs s id r,
    prepared p pol s -> source_row p id = Some r ->
    Q.prio (ws_queue (fold_left (update_one p pol) outs s)) id = None ->
    Q.prio (ws_queue s) id = None /\
    (forall y, In y (S.deps p r) ->
      look (fold_left (update_one p pol) outs s) y = look s y).
  Proof.
    intros p pol outs; induction outs as [|[x a] outs IH]; intros s id r Hp Hr Hnone.
    - split; [exact Hnone|intros; reflexivity].
    - cbn [fold_left] in Hnone |- *.
      destruct (IH (update_one p pol s (x, a)) id r
        (F6_prepared p pol s (x, a) Hp) Hr Hnone) as [Hbefore Hreads].
      split.
      + eapply update_outside_before; exact Hbefore.
      + intros y Hy; rewrite (Hreads y Hy).
        eapply update_outside_reads; eassumption.
  Qed.

  (** A continuing callback establishes acceptance of every row left outside its queue. *)
  Lemma accepted_step : forall p pol s s1, S.wf p -> prepared p pol s ->
    accepted p s -> step p pol s = inl s1 -> accepted p s1.
  Proof.
    intros p pol s s1 Hwf Hprepared Haccepted Hstep.
    unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr popped] q]|] eqn:Hpop; [|discriminate].
    destruct (row_at s popped) as [producer|] eqn:Hrow; [|discriminate].
    destruct (eval_row p producer (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    intros id r Hsource Hnone.
    pose proof (F7_pop_prepared p pol s pr popped q Hprepared Hpop) as Hafter.
    destruct (fold_outside_reads p pol ((S.target p producer, a) :: ss)
      (after_pop p s popped q) id r Hafter Hsource Hnone) as [Hbefore Hreads].
    assert (Hr : In r (S.rows p)) by exact (proj2 (source_row_member p id r Hsource)).
    assert (Hequal : S.eval p r
      (look (fold_left (update_one p pol) ((S.target p producer, a) :: ss)
        (after_pop p s popped q))) = S.eval p r (look s)).
    { apply S.reads_within; [exact Hwf|exact Hr|].
      intros y Hy; exact (Hreads y Hy). }
    change (row_ok L.leb
      (look (fold_left (update_one p pol) ((S.target p producer, a) :: ss)
        (after_pop p s popped q))) (S.target p r)
      (S.eval p r (look (fold_left (update_one p pol) ((S.target p producer, a) :: ss)
        (after_pop p s popped q)))) = true).
    rewrite Hequal.
    destruct (Pos.eq_dec id popped) as [->|Hother].
    - rewrite (proj1 (proj1 Hprepared)), Hsource in Hrow; injection Hrow as <-.
      change (S.eval p r (look s) = Some (a, ss)) in Heval; rewrite Heval.
      cbn [row_ok]; apply andb_true_iff; split.
      + apply (fold_outputs_cover p pol ((S.target p r, a) :: ss)
          (after_pop p s popped q) (S.target p r) a); now left.
      + apply forallb_forall; intros [x b] Hin; cbn [fst snd].
        apply (fold_outputs_cover p pol ((S.target p r, a) :: ss)
          (after_pop p s popped q) x b); now right.
    - destruct (Q.pop_min _ _ _ _ (proj1 (proj2 (proj2 Hprepared))) Hpop)
        as [Hlive [Hmin [Hgone Hrest]]].
      change (Q.prio q id = None) in Hbefore; rewrite Hrest in Hbefore by exact Hother.
      eapply row_ok_lookup_mono; [|exact (Haccepted id r Hsource Hbefore)].
      intro x; apply (look_fold_mono p pol ((S.target p producer, a) :: ss)
        (after_pop p s popped q) x).
  Qed.

  (** Reachable states satisfy every row outside their queue. *)
  Lemma F9_accepted : forall p pol s, S.wf p -> reachable p pol s -> accepted p s.
  Proof.
    intros p pol s Hwf [xs Hpath].
    assert (Hinitial : accepted p (prepare p pol)).
    { intros id r Hsource Hnone.
      destruct (prepare_queued p pol id (proj1 (source_row_member p id r Hsource)))
        as [pr Hprio]; congruence. }
    assert (Hpres : forall start ys last,
      wl_path (step p pol) start ys last -> prepared p pol start ->
      accepted p start -> accepted p last).
    { intros start ys last Hys; induction Hys as [st|st st1 zs final Hstep Hys IH];
        intros Hp Ha; [exact Ha|].
      apply IH.
      - exact (proj1 (F7_prepared p pol st st1 Hp Hstep)).
      - eapply accepted_step; eassumption. }
    eapply Hpres; [exact Hpath|apply F4_metadata|exact Hinitial].
  Qed.



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

  (** Enqueue charges every supplied identifier while preserving queue potential refunds. *)
  Lemma T_enqueue_bound : forall p pol ids s, S.wf p -> prio_ok p pol -> invariant p pol s ->
    (forall id, In id ids -> In id (row_ids p)) ->
    (T_enqueue p pol ids s + queue_phi p (enqueue p pol ids s) <=
      c_enqueue * N.of_nat (length ids + 1) * unit p + queue_phi p s)%N.
  Proof.
    intros p pol ids s Hwf Hprio Hinv Hids.
    set (f := fun (ql : Q.t * ptrie Datatypes.unit) id =>
      match trie_get id (snd ql) with
      | Some _ => ql
      | None => match row_at s id with
        | Some _ =>
          (Q.push (N.pos (match trie_get id (ws_ranks s) with
            | Some rank => rank | None => 1%positive end)) id (fst ql),
           PTrieCode.set id tt (snd ql))
        | None => ql
        end
      end).
    set (Tf := fun (ql : Q.t * ptrie Datatypes.unit) id =>
      (1 + (Datatypes.T_snd ql + T_trie_get id (snd ql) +
        match trie_get id (snd ql) with
        | Some _ => 0
        | None => T_row_at s id +
          match row_at s id with
          | Some _ => T_ws_ranks s + T_trie_get id (ws_ranks s) + Datatypes.T_fst ql +
            Q.T_push (N.pos (match trie_get id (ws_ranks s) with
              | Some rank => rank | None => 1%positive end)) id (fst ql) +
            (Datatypes.T_snd ql + PTrieCode.T_set id tt (snd ql))
          | None => 0
          end
        end))%N).
    set (Inv := fun (ql : Q.t * ptrie Datatypes.unit) => exists st,
      invariant p pol st /\ fst ql = ws_queue st /\ snd ql = ws_live st /\
      ws_rows st = ws_rows s /\ ws_ranks st = ws_ranks s).
    set (Phi := fun (ql : Q.t * ptrie Datatypes.unit) =>
      Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) (fst ql)).
    set (budget := (32 * (c_lookup + Q.c_pq + 1) * unit p)%N).
    assert (Hinitial : Inv (ws_queue s, ws_live s)).
    { exists s; split; [exact Hinv|]; repeat split; reflexivity. }
    assert (Hstep : forall ql id, Inv ql -> In id ids ->
      Inv (f ql id) /\ (Tf ql id + Phi (f ql id) <= budget + Phi ql)%N).
    { intros [queue live] id [st [Hst [Hqueue [Hlive [Hrows Hranks]]]]] Hin.
      cbn [fst snd] in Hqueue, Hlive; subst queue live.
      pose proof (Hids id Hin) as Hid.
      set (next := enqueue p pol [id] st).
      assert (Hnext : invariant p pol next).
      { unfold next; apply enqueue_invariant; auto.
        intros id1 [Heq|[]]; now subst id1. }
      assert (Hpair : (ws_queue next, ws_live next) = f (ws_queue st, ws_live st) id).
      { unfold next; rewrite F5_indexed; cbn [fold_left fst snd].
        unfold f, row_at; now rewrite Hrows, Hranks. }
      split.
      - exists next; split; [exact Hnext|].
        split; [rewrite <- Hpair; reflexivity|].
        split; [rewrite <- Hpair; reflexivity|].
        destruct (F5_fields p pol [id] st) as [_ [_ [Hnext_rows [_ [_ Hnext_ranks]]]]].
        unfold next; split; congruence.
      - destruct (source_row_total p id Hid) as [r Hsource].
        pose proof (proj2 (proj2 Hinv)) as Hprepared.
        assert (Hrow : row_at s id = Some r).
        { rewrite (proj1 (proj1 Hprepared) id); exact Hsource. }
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hprepared)))) id r Hrow) as Hrank.
        pose proof (row_ids_bits p id Hid) as Hbits.
        destruct (time_unit_bounds p) as [Hu [_ [Hid_unit _]]].
        assert (HbitsN : (N.of_nat (Pos.size_nat id + 1) <= 2 * unit p)%N).
        { rewrite Nat2N.inj_add in Hid_unit |- *; lia. }
        pose proof (PTrieT.T_get_le Datatypes.unit id (ws_live st)) as Hget_live.
        pose proof (PTrieT.T_get_le positive id (ws_ranks s)) as Hget_rank.
        unfold PTrieT.T_get in Hget_live, Hget_rank.
        pose proof (PTrieT.T_set_le Datatypes.unit id tt (ws_live st)) as Hset.
        change (@PTrieT.T_set Datatypes.unit) with (@PTrieCode.T_set Datatypes.unit) in Hset.
        pose proof (T_row_at_bits s id) as Hrow_cost.
        assert (Hget_live_bound : (T_trie_get id (ws_live st) <=
          2 * PTrieT.c_trie * unit p)%N).
        { assert (Hmul : (PTrieT.c_trie * N.of_nat (Pos.size_nat id + 1) <=
            PTrieT.c_trie * (2 * unit p))%N) by now apply N.mul_le_mono_l.
          clear -Hget_live Hmul; nia. }
        assert (Hget_rank_bound : (T_trie_get id (ws_ranks s) <=
          2 * PTrieT.c_trie * unit p)%N).
        { assert (Hmul : (PTrieT.c_trie * N.of_nat (Pos.size_nat id + 1) <=
            PTrieT.c_trie * (2 * unit p))%N) by now apply N.mul_le_mono_l.
          clear -Hget_rank Hmul; nia. }
        assert (Hset_bound : (PTrieCode.T_set id tt (ws_live st) <=
          2 * PTrieT.c_trie * unit p)%N).
        { eapply N.le_trans; [exact Hset|].
          eapply N.le_trans; [apply N.mul_le_mono_l; exact HbitsN|]; nia. }
        assert (Hrow_bound : (T_row_at s id <= 2 * (PTrieT.c_trie + 2) * unit p)%N).
        { eapply N.le_trans; [exact Hrow_cost|].
          eapply N.le_trans; [apply N.mul_le_mono_l; exact HbitsN|]; nia. }
        unfold Tf, f, Phi; cbn [fst snd].
        destruct (trie_get id (ws_live st)) as [[]|] eqn:Hpresent.
        + time_simpl; time_cbn.
          clear -Hget_live_bound Hu; unfold budget, c_lookup; nia.
        + rewrite Hrow, Hrank.
          destruct Hst as [[Hqwf [Hqfits [Hqpending _]]] _].
          pose proof (T_queue_push_bound p (N.pos (row_rank p pol r)) id (ws_queue st)
            Hqwf Hqfits Hqpending (row_queue_width p pol id r Hprio Hid)) as Hpush.
          time_simpl; time_cbn; time_cbn_all.
          clear -Hget_live_bound Hget_rank_bound Hset_bound Hrow_bound Hpush Hu.
          unfold budget, c_lookup; nia. }
    destruct (fold_left_inv_credit f Tf Inv Phi (fun _ => budget)
      ids (ws_queue s, ws_live s) Hinitial Hstep) as [_ Hfold].
    rewrite fold_constant_cost in Hfold.
    assert (Hpair : (ws_queue (enqueue p pol ids s), ws_live (enqueue p pol ids s)) =
      fold_left f ids (ws_queue s, ws_live s)).
    { unfold f; apply F5_indexed. }
    assert (Hphi : queue_phi p (enqueue p pol ids s) =
      Phi (fold_left f ids (ws_queue s, ws_live s))).
    { unfold queue_phi, Phi; rewrite <- Hpair; reflexivity. }
    unfold T_enqueue; fold f Tf.
    rewrite Hphi; time_simpl; time_cbn.
    change (Phi (ws_queue s, ws_live s)) with (queue_phi p s) in Hfold.
    destruct (time_unit_bounds p) as [Hu _].
    set (n := N.of_nat (length ids)) in *.
    set (chunk := ((n + 1) * unit p)%N).
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; clear -Hu; nia).
    assert (Hn : (n <= chunk)%N) by (unfold chunk; clear -Hu; nia).
    assert (Hbudget : (budget * n <= 32 * (c_lookup + Q.c_pq + 1) * chunk)%N).
    { unfold budget; rewrite <- N.mul_assoc.
      replace (unit p * n)%N with (n * unit p)%N by ring.
      apply N.mul_le_mono_l; unfold chunk; nia. }
    rewrite Nat2N.inj_add; fold n.
    replace (c_enqueue * (n + N.of_nat 1) * unit p)%N with
      (c_enqueue * chunk)%N by (unfold chunk; change (N.of_nat 1) with 1%N; ring).
    clear -Hfold Hbudget Hn Hchunk.
    unfold c_enqueue, c_lookup in *; nia.
  Qed.

  (** Arming one encoded bucket performs one bounded trie insertion. *)
  Lemma T_arm_bound : forall p c s, Pos.size_nat c <= S.kw p ->
    (T_arm c s <= (PTrieT.c_trie + 10) * unit p)%N.
  Proof.
    intros p c s Hbits.
    pose proof (PTrieT.T_set_le Datatypes.unit c tt (ws_armed s)) as Hset.
    change (@PTrieT.T_set Datatypes.unit) with (@PTrieCode.T_set Datatypes.unit) in Hset.
    destruct (time_unit_bounds p) as [Hu [Hkey _]].
    assert (Hwidth : (N.of_nat (Pos.size_nat c + 1) <= unit p)%N) by lia.
    assert (Hset_bound : (PTrieCode.T_set c tt (ws_armed s) <=
      PTrieT.c_trie * unit p)%N).
    { eapply N.le_trans; [exact Hset|]; now apply N.mul_le_mono_l. }
    unfold T_arm; time_simpl; time_cbn.
    clear -Hset_bound Hu; nia.
  Qed.

  (** Policy timing separates its strict head allowance from ordinary value work. *)
  Lemma T_policy_update_bound : forall p pol s x a, S.wf p -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
    (P.T_update pol (S.key_code x) (counter s (S.key_code x)) (look s x) a <=
      4 * P.c_pol * unit p + P.c_pol * strict_head_work pol s x a)%N.
  Proof.
    intros p pol s x a Hwf Hinv Ha Hsupport.
    pose proof (key_support_bits p (S.key_code x) Hwf Hsupport) as Hbits.
    pose proof (invariant_sizes p pol s Hinv x) as Hold.
    pose proof (B.size_le p a Ha) as Hnew.
    pose proof (P.T_update_le pol (S.key_code x) (counter s (S.key_code x))
      (look s x) a) as Hcost.
    destruct (time_unit_bounds p) as [Hu [Hkey [_ [Hlat _]]]].
    assert (Hvalues : (L.c_lat * N.of_nat (L.size (look s x) + L.size a + 1) <=
      2 * unit p)%N).
    { assert (Hsize : (N.of_nat (L.size (look s x) + L.size a + 1) <=
        2 * N.of_nat (B.vsize p + 1))%N) by lia.
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hsize|].
      clear -Hlat; nia. }
    fold (strict_head_work pol s x a) in Hcost.
    eapply N.le_trans; [exact Hcost|].
    clear -Hu Hkey Hbits Hvalues; nia.
  Qed.

  (** Ordinary update work has a fixed unit cost apart from a possible reader enqueue. *)
  Lemma T_update_one_bound : forall p pol s x a, S.wf p -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
    let c := S.key_code x in
    let ac := P.update pol c (counter s c) (look s x) a in
    let s1 := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
      (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s) in
    (T_update_one p pol s (x, a) <=
      64 * (c_lookup + P.c_pol + 1) * unit p + P.c_pol * strict_head_work pol s x a +
      if L.leb a (look s x) then 0 else
        match trie_get c (ws_armed s) with
        | Some _ => 0
        | None => T_enqueue p pol (readers s c) s1
        end)%N.
  Proof.
    intros p pol s x a Hwf Hinv Ha Hsupport.
    cbn beta iota zeta.
    set (c := S.key_code x).
    set (ac := P.update pol c (counter s c) (look s x) a).
    set (s1 := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
      (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s)).
    pose proof (key_support_bits p c Hwf Hsupport) as Hbits.
    pose proof (invariant_sizes p pol s Hinv x) as Hold.
    pose proof (B.size_le p a Ha) as Hnew.
    destruct (time_unit_bounds p) as [Hu [Hkey [_ [Hlat _]]]].
    assert (Hwidth : (N.of_nat (Pos.size_nat c + 1) <= unit p)%N) by lia.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (T_lookup_bound (ws_store s) x) as Hlook.
    pose proof (L.T_leb_le a (look s x)) as Hleb.
    pose proof (PTrieT.T_get_le N c (ws_counters s)) as Hcount.
    pose proof (PTrieT.T_get_le Datatypes.unit c (ws_armed s)) as Harmed.
    pose proof (PTrieT.T_set_le (S.key * L.t) c (x, fst ac) (ws_store s)) as Hstore.
    pose proof (PTrieT.T_set_le N c (snd ac) (ws_counters s)) as Hcounter.
    pose proof (T_readers_bits s c) as Hreaders.
    pose proof (T_arm_bound p c (enqueue p pol (readers s c) s1) Hbits) as Harm.
    pose proof (T_policy_update_bound p pol s x a Hwf Hinv Ha Hsupport) as Hpolicy.
    change (@PTrieT.T_set (S.key * L.t)) with (@PTrieCode.T_set (S.key * L.t)) in Hstore.
    change (@PTrieT.T_set N) with (@PTrieCode.T_set N) in Hcounter.
    unfold PTrieT.T_get in Hcount, Harmed.
    unfold S.key_bits in Hcode, Hlook; fold c in Hcode, Hlook, Hpolicy.
    fold ac in Hpolicy.
    assert (Hcount_bound : (T_trie_get c (ws_counters s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N) by lia.
    assert (Harmed_bound : (T_trie_get c (ws_armed s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N) by lia.
    assert (Hcommon : (S.T_key_code x +
      T_look_or S.key_code S.T_key_code L.bot (ws_store s) x + L.T_leb a (look s x) +
      T_trie_get c (ws_counters s) + T_trie_get c (ws_armed s) +
      PTrieCode.T_set c (x, fst ac) (ws_store s) +
      PTrieCode.T_set c (snd ac) (ws_counters s) + T_readers s c +
      T_arm c (enqueue p pol (readers s c) s1) <=
      32 * (c_lookup + 1) * unit p)%N).
    { assert (Hvalues : (L.c_lat * N.of_nat (L.size a + L.size (look s x) + 1) <=
        2 * unit p)%N).
      { assert (Hsize : (N.of_nat (L.size a + L.size (look s x) + 1) <=
          2 * N.of_nat (B.vsize p + 1))%N) by lia.
        eapply N.le_trans; [apply N.mul_le_mono_l; exact Hsize|].
        clear -Hlat; nia. }
      eapply N.le_trans.
      - apply N.add_le_mono; [apply N.add_le_mono; [apply N.add_le_mono;
          [apply N.add_le_mono; [apply N.add_le_mono; [apply N.add_le_mono;
            [apply N.add_le_mono; [apply N.add_le_mono; [exact Hcode|exact Hlook]|
              eapply N.le_trans; [exact Hleb|exact Hvalues]]|exact Hcount_bound]|
              exact Harmed_bound]|
            exact Hstore]|exact Hcounter]|exact Hreaders]|exact Harm].
      - unfold c_lookup in *; clear -Hwidth Hu; nia. }
    unfold T_update_one.
    change (fun y => S.T_key_code y) with S.T_key_code.
    cbn beta iota zeta; fold c; fold (look s x); fold (counter s c); fold ac; fold s1.
    destruct (L.leb a (look s x)); [|destruct (trie_get c (ws_armed s)) as [[]|]];
      time_simpl; time_cbn;
      clear -Hcommon Hpolicy Hu; unfold c_lookup in *; nia.
  Qed.

  (** An update spends ordinary credit and its exact strict-head allowance. *)
  Lemma T_update_queue_bound : forall p pol s x a, S.wf p -> prio_ok p pol ->
    invariant p pol s -> B.inv p a -> In (S.key_code x) (key_support p) ->
    (T_update_one p pol s (x, a) + queue_phi p (update_one p pol s (x, a)) <=
      k_update * N.of_nat (1 + push_work p s x a) * unit p +
      k_update * strict_head_work pol s x a + queue_phi p s)%N.
  Proof.
    intros p pol s x a Hwf Hprio Hinv Ha Hsupport.
    pose proof (T_update_one_bound p pol s x a Hwf Hinv Ha Hsupport) as Hbase.
    cbn beta iota zeta in Hbase.
    set (c := S.key_code x) in *.
    set (ac := P.update pol c (counter s c) (look s x) a) in *.
    set (s1 := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
      (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
      (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s)) in *.
    assert (Hs1 : invariant p pol s1).
    { unfold s1; apply stored_value_invariant; [exact Hinv|].
      unfold ac; apply policy_update_inv; [exact (proj1 (proj2 Hinv) x)|exact Ha]. }
    assert (Hids : forall id, In id (readers s c) -> In id (row_ids p)).
    { destruct (proj1 (proj2 (proj2 Hinv))) as [_ Hreaders].
      rewrite Hreaders; intros id Hin; unfold source_readers in Hin.
      now apply filter_In in Hin. }
    pose proof (T_enqueue_bound p pol (readers s c) s1 Hwf Hprio Hs1 Hids) as Henqueue.
    assert (Hdegree : length (readers s c) = degree p c).
    { unfold degree; now rewrite (proj2 (proj1 (proj2 (proj2 Hinv))) c). }
    change (queue_phi p s1) with (queue_phi p s) in Henqueue.
    rewrite Hdegree in Henqueue.
    rewrite F6_indexed; cbn beta iota zeta; fold c ac s1.
    unfold push_work; fold c.
    destruct (L.leb a (look s x)) eqn:Hstable.
    - cbn beta iota zeta in Hbase |- *.
      unfold k_update, c_lookup in *; clear -Hbase; nia.
    - destruct (trie_get c (ws_armed s)) as [[]|] eqn:Harmed.
      + cbn beta iota zeta in Hbase |- *.
        change (queue_phi p s1) with (queue_phi p s).
        unfold k_update, c_lookup in *; clear -Hbase; nia.
      + cbn beta iota zeta in Hbase |- *.
        change (queue_phi p (arm c (enqueue p pol (readers s c) s1)))
          with (queue_phi p (enqueue p pol (readers s c) s1)).
        rewrite !Nat2N.inj_add in Henqueue |- *.
        clear -Hbase Henqueue; unfold k_update, c_enqueue, c_lookup in *; nia.
  Qed.

  (** Preparation traversals use one shared key-and-identifier width. *)
  Definition prep_width (p : S.prog) : N :=
    N.of_nat (S.kw p + Nat.log2 (C p) + 1).

  (** A row pays for declared occurrences and its target accessor. *)
  Definition prep_row (p : S.prog) (r : S.row) : N :=
    (N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) *
      prep_width p + unit p)%N.

  (** Width includes the leading bit, key width and identifier width. *)
  Lemma prep_width_bounds : forall p,
    (1 <= prep_width p)%N /\
    (N.of_nat (S.kw p + 1) <= prep_width p)%N /\
    (N.of_nat (Nat.log2 (C p) + 1) <= prep_width p)%N.
  Proof.
    intro p; unfold prep_width; repeat split; lia.
  Qed.

  (** A right fold charges each callback only at a member of its input list. *)
  Lemma fold_right_budget {A X : Type} (f : X -> A -> A) (Tf : X -> A -> N)
      (budget : X -> N) : forall xs a,
    (forall x acc, In x xs -> (Tf x acc + 1 <= budget x)%N) ->
    (List.T_fold_right f Tf a xs <=
      fold_right (fun x total => budget x + total)%N 1%N xs)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros a Hcost.
    - time_step.
    - pose proof (Hcost x (fold_right f a xs) (or_introl eq_refl)) as Hhead.
      pose proof (IH a (fun y acc Hin => Hcost y acc (or_intror Hin))) as Htail.
      time_unfold @List.T_fold_right; time_cbn; nia.
  Qed.

  (** A uniform callback bound pays once per input occurrence. *)
  Lemma fold_right_member_bound {A X : Type} (f : X -> A -> A)
      (Tf : X -> A -> N) : forall xs a k,
    (forall x acc, In x xs -> (Tf x acc <= k)%N) ->
    (List.T_fold_right f Tf a xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros a k Hcost.
    - time_step.
    - pose proof (Hcost x (fold_right f a xs) (or_introl eq_refl)) as Hhead.
      pose proof (IH a k (fun y acc Hin => Hcost y acc (or_intror Hin))) as Htail.
      time_unfold @List.T_fold_right; time_cbn; nia.
  Qed.

  (** Flattening charges its callback and the append of that callback's output. *)
  Lemma flat_map_budget {A X : Type} (f : X -> list A) (Tf : X -> N)
      (budget : X -> N) : forall xs,
    (forall x, In x xs ->
      (Tf x + N.of_nat (length (f x)) + 2 <= budget x)%N) ->
    (Code.List.T_flat_map f Tf xs <=
      fold_right (fun x total => budget x + total)%N 1%N xs)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intro Hcost.
    - time_step.
    - pose proof (Hcost x (or_introl eq_refl)) as Hhead.
      pose proof (IH (fun y Hin => Hcost y (or_intror Hin))) as Htail.
      pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happ.
      time_unfold @Code.List.T_flat_map; time_cbn; nia.
  Qed.

  (** Summing row budgets gives the declared occurrence and row totals. *)
  Lemma prep_row_sum : forall p rs k,
    fold_right (fun r total => k * prep_row p r + total)%N 1%N rs =
      (k * (N.of_nat (fold_right Nat.add 0%nat (List.map
        (fun r => (length (S.deps p r) + length (S.sides p r) + 1)%nat) rs)) *
        prep_width p + N.of_nat (length rs) * unit p) + 1)%N.
  Proof.
    intros p rs; induction rs as [|r rs IH]; intro k.
    - unfold prep_row; time_cbn; nia.
    - cbn [fold_right List.map length]; rewrite IH.
      unfold prep_row; rewrite !Nat2N.inj_add, !Nat2N.inj_succ; time_cbn; nia.
  Qed.

  (** Numbering preserves the sum of costs depending only on the row. *)
  Lemma prep_combine_sum {A X : Type} : forall (ids : list A) (xs : list X) g,
    length ids = length xs ->
    fold_right (fun ix total => g (snd ix) + total)%N 1%N (combine ids xs) =
      fold_right (fun x total => g x + total)%N 1%N xs.
  Proof.
    intro ids; induction ids as [|id ids IH]; intros [|x xs] g Hlength;
      cbn [length combine fold_right snd] in *; try discriminate; [reflexivity|].
    f_equal; apply IH; lia.
  Qed.

  (** The seed has empty queue potential and already satisfies the state invariant. *)
  Lemma prepare_seed_invariant : forall p pol, invariant p pol (prepare_seed p pol).
  Proof.
    intros p pol; split; [apply structural_empty; reflexivity|]; split.
    - intro x; rewrite prepare_seed_look; apply B.inv_bot.
    - apply prepare_seed_prepared.
  Qed.

  (** Before initial enqueue, the queue is empty and has zero potential. *)
  Lemma prepare_seed_phi : forall p pol, queue_phi p (prepare_seed p pol) = 0%N.
  Proof.
    intros p pol; unfold queue_phi; change
      (Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) Q.empty = 0%N).
    apply Q.phi_empty.
  Qed.

  (** Deduplicating dependencies never increases their occurrence count. *)
  Lemma read_set_length : forall xs,
    length (PTrieCode.elements (read_set xs)) <= length xs.
  Proof.
    intro xs; rewrite <- (length_map fst (PTrieCode.elements (read_set xs))).
    rewrite <- (length_map S.key_code xs); apply NoDup_incl_length.
    - apply PTrie.elements_nodup.
    - intros c Hin; apply in_map_iff in Hin as [[key []] [Heq Hin]].
      cbn [fst] in Heq; subst key; apply read_set_member in Hin as [x [Hx Hcode]].
      apply in_map_iff; exists x; split; assumption.
  Qed.

  (** A deduplicated read code retains the width of one declared dependency. *)
  Lemma read_set_bits : forall xs b,
    (forall x, In x xs -> S.key_bits x <= b) ->
    forall kv, In kv (PTrieCode.elements (read_set xs)) -> Pos.size_nat (fst kv) <= b.
  Proof.
    intros xs b Hbits [c []] Hin; cbn [fst].
    apply read_set_member in Hin as [x [Hx <-]]; exact (Hbits x Hx).
  Qed.

  (** Enumerating a read set costs at most its declared occurrences times key width. *)
  Lemma read_set_weight : forall xs b,
    (forall x, In x xs -> S.key_bits x <= b) ->
    PTrieT.weight (read_set xs) <= length xs * (b + 1).
  Proof.
    intros xs b Hbits; pose proof (read_set_length xs) as Hlength.
    pose proof (read_set_bits xs b Hbits) as Hkeys.
    unfold PTrieT.weight.
    assert (Hsum : forall (entries : list (positive * Datatypes.unit)),
      (forall kv, In kv entries -> Pos.size_nat (fst kv) <= b) ->
      fold_right Nat.add 0 (List.map (fun kv => Pos.size_nat (fst kv) + 1) entries)
        <= length entries * (b + 1)).
    { intro entries; induction entries as [|kv entries IH]; intro Hentry;
        cbn [fold_right List.map length]; [lia|].
      pose proof (Hentry kv (or_introl eq_refl)).
      pose proof (IH (fun x Hin => Hentry x (or_intror Hin))); nia. }
    eapply Nat.le_trans; [apply Hsum; exact Hkeys|]; nia.
  Qed.

  TimeFun mark_read.

  (** Marking one dependency pays for encoding, lookup and at most one insertion. *)
  Lemma T_mark_read_bound : forall p seen x, S.key_bits x <= S.kw p ->
    (T_mark_read seen x <= 3 * c_lookup * prep_width p)%N.
  Proof.
    intros p seen x Hbits.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le Datatypes.unit (S.key_code x) seen) as Hget.
    pose proof (PTrieT.T_set_le Datatypes.unit (S.key_code x) tt seen) as Hset.
    unfold PTrieT.T_get in Hget.
    change (@PTrieT.T_set Datatypes.unit) with (@PTrieCode.T_set Datatypes.unit) in Hset.
    assert (Hwidth : (N.of_nat (S.key_bits x + 1) <= prep_width p)%N)
      by (unfold prep_width; lia).
    assert (Hcode' : (S.T_key_code x <= S.c_sys * prep_width p)%N)
      by (eapply N.le_trans; [exact Hcode|now apply N.mul_le_mono_l]).
    assert (Hget' : (T_trie_get (S.key_code x) seen <= PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans with
        (m := (PTrieT.c_trie * N.of_nat (S.key_bits x + 1))%N);
        [unfold S.key_bits; lia|now apply N.mul_le_mono_l]).
    assert (Hset' : (PTrieCode.T_set (S.key_code x) tt seen <=
      PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans; [exact Hset|now apply N.mul_le_mono_l]).
    destruct (prep_width_bounds p) as [Hpositive _].
    unfold T_mark_read; destruct (trie_get (S.key_code x) seen); time_cbn;
      clear -Hcode' Hget' Hset' Hpositive; unfold c_lookup; nia.
  Qed.

  (** Building a dependency set charges the original list, including repeated reads. *)
  Lemma T_read_set_fold : forall p xs,
    (forall x, In x xs -> S.key_bits x <= S.kw p) ->
    (List.T_fold_left mark_read T_mark_read xs Empty <=
      8 * c_lookup * N.of_nat (length xs + 1) * prep_width p)%N.
  Proof.
    intros p xs Hbits.
    destruct (fold_left_inv_time mark_read T_mark_read (fun _ => True)
      (fun _ => (3 * c_lookup * prep_width p)%N) xs Empty I) as [_ Hfold].
    - intros seen x _ Hin; split; [exact I|apply T_mark_read_bound; now apply Hbits].
    - rewrite fold_constant_cost in Hfold.
      destruct (prep_width_bounds p) as [Hwidth _].
      rewrite Nat2N.inj_add; clear -Hfold Hwidth; unfold c_lookup in *; time_cbn; nia.
  Qed.

  (** Adding one reader traverses its dependency code twice. *)
  Lemma T_add_reader_bound : forall p id c m, Pos.size_nat c <= S.kw p ->
    (T_add_reader id c m <= 3 * c_lookup * prep_width p)%N.
  Proof.
    intros p id c m Hbits; pose proof (PTrieT.T_get_le (list positive) c m) as Hget.
    pose proof (PTrieT.T_set_le (list positive) c
      (id :: match trie_get c m with Some ids => ids | None => [] end) m) as Hset.
    unfold PTrieT.T_get in Hget.
    change (@PTrieT.T_set (list positive)) with (@PTrieCode.T_set (list positive)) in Hset.
    assert (Hwidth : (N.of_nat (Pos.size_nat c + 1) <= prep_width p)%N)
      by (unfold prep_width; lia).
    assert (Hget' : (T_trie_get c m <= PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans with
        (m := (PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N);
        [lia|now apply N.mul_le_mono_l]).
    assert (Hset' : (PTrieCode.T_set c
      (id :: match trie_get c m with Some ids => ids | None => [] end) m <=
      PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans; [exact Hset|now apply N.mul_le_mono_l]).
    destruct (prep_width_bounds p) as [Hpositive _].
    unfold T_add_reader; clear -Hget' Hset' Hpositive; unfold c_lookup; nia.
  Qed.

  (** Initial enqueue starts from zero potential and charges only actual row identifiers. *)
  Lemma prepare_enqueue_cost : forall p pol, S.wf p -> prio_ok p pol ->
    (T_enqueue p pol (row_ids p) (prepare_seed p pol) + queue_phi p (prepare p pol) <=
      2 * c_enqueue * N.of_nat (C p) * unit p + 32)%N.
  Proof.
    intros p pol Hwf Hprio; destruct (Nat.eq_dec (C p) 0) as [Hzero|Hpositive].
    - assert (Hids : row_ids p = []).
      { apply length_zero_iff_nil; now rewrite row_ids_length. }
      rewrite prepare_eq, Hids, enqueue_nil, prepare_seed_phi.
      unfold T_enqueue; time_unfold @List.T_fold_left; time_simpl; time_cbn; nia.
    - pose proof (T_enqueue_bound p pol (row_ids p) (prepare_seed p pol)
        Hwf Hprio (prepare_seed_invariant p pol) (fun id Hin => Hin)) as Hcost.
      rewrite <- prepare_eq, prepare_seed_phi, row_ids_length in Hcost.
      assert (Hcount : (N.of_nat (C p + 1) <= 2 * N.of_nat (C p))%N) by lia.
      assert (Hmul : (c_enqueue * N.of_nat (C p + 1) * unit p <=
        c_enqueue * (2 * N.of_nat (C p)) * unit p)%N).
      { apply N.mul_le_mono_r; now apply N.mul_le_mono_l. }
      clear -Hcost Hmul; nia.
  Qed.

  (** Numbering spends one successor traversal for each emitted identifier. *)
  Lemma T_wl_ids_from_bits : forall n id b,
    (forall c, In c (wl_ids_from n id) -> Pos.size_nat c <= b) ->
    (T_wl_ids_from n id <= (N.of_nat b + 2) * N.of_nat n + 1)%N.
  Proof.
    intro n; induction n as [|n IH]; intros id b Hbits.
    - time_unfold @T_wl_ids_from; lia.
    - assert (Hhead : Pos.size_nat id <= b).
      { apply Hbits; now left. }
      assert (Htail : forall c, In c (wl_ids_from n (Pos.succ id)) ->
        Pos.size_nat c <= b).
      { intros c Hin; apply Hbits; now right. }
      specialize (IH (Pos.succ id) b Htail).
      pose proof (Std.Pos.T_succ_le id) as Hsucc.
      assert (Hwidth : (N.of_nat (Pos.size_nat id) <= N.of_nat b)%N) by lia.
      time_unfold @T_wl_ids_from; rewrite Nat2N.inj_succ; nia.
  Qed.

  (** Row numbering pays the row-list scan and the logarithmic width of each occurrence. *)
  Lemma T_row_ids_bits : forall p, S.wf p ->
    (T_row_ids p <= S.c_sys * N.of_nat (C p + 1) +
      N.of_nat (Nat.log2 (C p) + 4) * N.of_nat (C p) + 3)%N.
  Proof.
    intros p Hwf.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    change (S.T_rows p <= S.c_sys * N.of_nat (C p + 1))%N in Hrows.
    pose proof (Datatypes.T_length_le (S.rows p)) as Hlength.
    change (Datatypes.T_length (S.rows p) <= N.of_nat (C p) + 1)%N in Hlength.
    assert (Hbits : forall c, In c (wl_ids_from (C p) 1%positive) ->
      Pos.size_nat c <= Nat.log2 (C p) + 1).
    { intros c Hin; exact (row_ids_bits p c Hin). }
    pose proof (T_wl_ids_from_bits (C p) 1%positive (Nat.log2 (C p) + 1) Hbits)
      as Hids.
    assert (Hwidth : (N.of_nat (Nat.log2 (C p) + 4) =
      N.of_nat (Nat.log2 (C p) + 1) + 3)%N).
    { rewrite !Nat2N.inj_add; lia. }
    time_unfold @T_row_ids.
    change (1 + (S.T_rows p + Datatypes.T_length (S.rows p) +
      T_wl_ids_from (C p) 1%positive) <= S.c_sys * N.of_nat (C p + 1) +
      N.of_nat (Nat.log2 (C p) + 4) * N.of_nat (C p) + 3)%N.
    rewrite Hwidth; nia.
  Qed.

  (** The public preparation budget absorbs row enumeration, including its empty-list cost. *)
  Lemma T_row_ids_prep : forall p, S.wf p ->
    (T_row_ids p <= (S.c_sys + 4) * (N.of_nat (prep p) + 1))%N.
  Proof.
    intros p Hwf; pose proof (T_row_ids_bits p Hwf) as Htime.
    assert (Hcount_nat : C p <= prep p) by (unfold prep; nia).
    assert (Hcount : (N.of_nat (C p) <= N.of_nat (prep p))%N) by lia.
    assert (Hbits_nat : (Nat.log2 (C p) + 4) * C p <= 4 * prep p).
    { unfold prep; nia. }
    assert (Hbits : (N.of_nat (Nat.log2 (C p) + 4) * N.of_nat (C p) <=
      4 * N.of_nat (prep p))%N).
    { rewrite <- Nat2N.inj_mul; lia. }
    replace (N.of_nat (C p + 1)) with (N.of_nat (C p) + 1)%N in Htime.
    - nia.
    - rewrite Nat2N.inj_add; reflexivity.
  Qed.

  (** Each component of a row's preparation budget is available separately. *)
  Lemma prep_row_bounds : forall p r,
    (1 <= prep_row p r)%N /\ (prep_width p <= prep_row p r)%N /\
    (unit p <= prep_row p r)%N /\
    (N.of_nat (length (S.deps p r) + 1) * prep_width p <= prep_row p r)%N /\
    (N.of_nat (length (S.sides p r) + 1) * prep_width p <= prep_row p r)%N.
  Proof.
    intros p r; destruct (prep_width_bounds p) as [Hw _].
    unfold prep_row; rewrite !Nat2N.inj_add; time_cbn; repeat split; nia.
  Qed.

  (** System accessors fit their row's occurrence and transfer budgets. *)
  Lemma prep_accessors : forall p r, S.wf p -> In r (S.rows p) ->
    (S.T_target p r <= S.c_sys * prep_row p r)%N /\
    (S.T_deps p r <= S.c_sys * prep_row p r)%N /\
    (S.T_sides p r <= S.c_sys * prep_row p r)%N.
  Proof.
    intros p r Hwf Hr; destruct (prep_row_bounds p r) as [_ [_ [Hu [Hd Hs]]]].
    destruct (time_unit_bounds p) as [_ [_ [_ [_ Hwork]]]].
    destruct (prep_width_bounds p) as [_ [Hkey _]].
    split; [|split].
    - eapply N.le_trans; [exact (S.T_target_le p r Hwf Hr)|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption.
    - eapply N.le_trans; [exact (S.T_deps_le p r Hwf Hr)|].
      rewrite <- N.mul_assoc; apply N.mul_le_mono_l.
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hkey|exact Hd].
    - eapply N.le_trans; [exact (S.T_sides_le p r Hwf Hr)|].
      rewrite <- N.mul_assoc; apply N.mul_le_mono_l.
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hkey|exact Hs].
  Qed.

  (** A cached identifier insertion uses the shared preparation width. *)
  Lemma T_prep_set {A : Type} : forall p id (a : A) m, In id (row_ids p) ->
    (PTrieCode.T_set id a m <= 2 * PTrieT.c_trie * prep_width p)%N.
  Proof.
    intros p id a m Hid; pose proof (row_ids_bits p id Hid) as Hbits.
    pose proof (PTrieT.T_set_le A id a m) as Htime.
    change (@PTrieT.T_set A) with (@PTrieCode.T_set A) in Htime.
    assert (Hwidth : (N.of_nat (Pos.size_nat id + 1) <= 2 * prep_width p)%N)
      by (unfold prep_width; lia).
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hwidth|]; nia.
  Qed.

  (** Enumerating a row's distinct read codes is charged to its declared dependencies. *)
  Lemma T_read_elements : forall p r, S.wf p -> In r (S.rows p) ->
    (PTrieT.T_elements (read_set (S.deps p r)) <=
      2 * PTrieT.c_trie * prep_row p r)%N.
  Proof.
    intros p r Hwf Hr.
    assert (Hkeys : forall x, In x (S.deps p r) -> S.key_bits x <= S.kw p).
    { intros x Hx; apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
    pose proof (read_set_weight (S.deps p r) (S.kw p) Hkeys) as Hweight.
    pose proof (PTrieT.T_elements_le Datatypes.unit (read_set (S.deps p r))) as Htime.
    destruct (prep_row_bounds p r) as [Hpositive [_ [_ [Hdeps _]]]].
    destruct (prep_width_bounds p) as [_ [Hkey _]].
    assert (Hwidth : (N.of_nat (PTrieT.weight (read_set (S.deps p r)) + 1) <=
      2 * prep_row p r)%N).
    { assert (HweightN : (N.of_nat (PTrieT.weight (read_set (S.deps p r))) <=
        N.of_nat (length (S.deps p r)) * N.of_nat (S.kw p + 1))%N)
        by (rewrite <- Nat2N.inj_mul; lia).
      rewrite Nat2N.inj_add in *; time_cbn_all; nia. }
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hwidth|]; nia.
  Qed.

  (** Inserting reader buckets visits every distinct read code once. *)
  Lemma T_readers_fold : forall p r id m, S.wf p -> In r (S.rows p) ->
    (List.T_fold_right (fun kv acc => add_reader id (fst kv) acc)
      (fun kv acc => 1 + (Datatypes.T_fst kv + T_add_reader id (fst kv) acc))%N
      m (PTrieCode.elements (read_set (S.deps p r))) <=
      8 * c_lookup * prep_row p r)%N.
  Proof.
    intros p r id m Hwf Hr.
    assert (Hkeys : forall x, In x (S.deps p r) -> S.key_bits x <= S.kw p).
    { intros x Hx; apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
    pose proof (read_set_bits (S.deps p r) (S.kw p) Hkeys) as Hbits.
    pose proof (read_set_length (S.deps p r)) as Hlength.
    assert (Hstep : forall kv acc, In kv (PTrieCode.elements (read_set (S.deps p r))) ->
      (1 + (Datatypes.T_fst kv + T_add_reader id (fst kv) acc) <=
        3 * c_lookup * prep_width p + 2)%N).
    { intros kv acc Hin; pose proof (T_add_reader_bound p id (fst kv) acc (Hbits kv Hin)).
      pose proof (Datatypes.T_fst_le kv); lia. }
    pose proof (fold_right_member_bound
      (fun kv acc => add_reader id (fst kv) acc)
      (fun kv acc => 1 + (Datatypes.T_fst kv + T_add_reader id (fst kv) acc))%N
      _ m _ Hstep) as Hfold.
    destruct (prep_row_bounds p r) as [Hpositive [_ [_ [Hdeps _]]]].
    destruct (prep_width_bounds p) as [Hwidth _].
    assert (Hcount : (N.of_nat (length (PTrieCode.elements (read_set (S.deps p r)))) <=
      N.of_nat (length (S.deps p r)))%N) by lia.
    assert (Hmass : (N.of_nat (length (PTrieCode.elements (read_set (S.deps p r)))) *
      prep_width p <= prep_row p r)%N).
    { eapply N.le_trans; [|exact Hdeps].
      apply N.mul_le_mono_r; lia. }
    assert (Hcount_row : (N.of_nat
      (length (PTrieCode.elements (read_set (S.deps p r)))) <= prep_row p r)%N)
      by (clear -Hmass Hwidth; nia).
    assert (Hscaled : (3 * c_lookup *
      (N.of_nat (length (PTrieCode.elements (read_set (S.deps p r)))) * prep_width p) <=
      3 * c_lookup * prep_row p r)%N) by now apply N.mul_le_mono_l.
    assert (Hlarge : (prep_row p r <= c_lookup * prep_row p r)%N)
      by (unfold c_lookup; nia).
    clear -Hfold Hpositive Hcount_row Hscaled Hlarge; nia.
  Qed.

  (** One index callback pays for the row entry and its deduplicated reader buckets. *)
  Lemma T_index_row_bound : forall p id r idx, S.wf p ->
    In id (row_ids p) -> In r (S.rows p) ->
    (T_index_row p (id, r) idx + 1 <= 64 * c_lookup * prep_row p r)%N.
  Proof.
    intros p id r idx Hwf Hid Hr.
    destruct (prep_accessors p r Hwf Hr) as [_ [Hdeps _]].
    assert (Hkeys : forall x, In x (S.deps p r) -> S.key_bits x <= S.kw p).
    { intros x Hx; apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
    pose proof (T_read_set_fold p (S.deps p r) Hkeys) as Hmarks.
    pose proof (T_prep_set p id r (fst idx) Hid) as Hset.
    pose proof (T_read_elements p r Hwf Hr) as Helements.
    pose proof (T_readers_fold p r id (snd idx) Hwf Hr) as Hreaders.
    destruct (prep_row_bounds p r) as [Hpositive [Hwidth [_ [Hdepwidth _]]]].
    assert (Hmarks' : (List.T_fold_left mark_read T_mark_read (S.deps p r) Empty <=
      8 * c_lookup * prep_row p r)%N).
    { eapply N.le_trans; [exact Hmarks|].
      rewrite <- N.mul_assoc; now apply N.mul_le_mono_l. }
    assert (Hset' : (PTrieCode.T_set id r (fst idx) <=
      2 * PTrieT.c_trie * prep_row p r)%N).
    { eapply N.le_trans; [exact Hset|]; now apply N.mul_le_mono_l. }
    pose proof (Datatypes.T_fst_le idx) as Hfst.
    pose proof (Datatypes.T_snd_le idx) as Hsnd.
    unfold T_index_row; cbn beta iota zeta.
    change (fun seen x => 1 + (S.T_key_code x +
      (T_trie_get (S.key_code x) seen + match trie_get (S.key_code x) seen with
        | Some _ => 0 | None => PTrieCode.T_set (S.key_code x) tt seen end)))%N
      with T_mark_read.
    change (fun seen x => match trie_get (S.key_code x) seen with
      | Some _ => seen | None => PTrieCode.set (S.key_code x) tt seen end) with mark_read.
    fold (read_set (S.deps p r)).
    clear -Hdeps Hmarks' Hset' Helements Hreaders Hpositive Hfst Hsnd.
    unfold c_lookup in *; nia.
  Qed.

  (** Priority lookup traverses one declared key code. *)
  Lemma T_priority_bound : forall p pol c, Pos.size_nat c <= S.kw p ->
    (T_priority pol c <= 3 * c_lookup * prep_width p)%N.
  Proof.
    intros p pol c Hbits; pose proof (PTrieT.T_get_le positive c (prio pol)) as Hget.
    unfold PTrieT.T_get in Hget.
    assert (Hwidth : (N.of_nat (Pos.size_nat c + 1) <= prep_width p)%N)
      by (unfold prep_width; lia).
    assert (Hget' : (T_trie_get c (prio pol) <= PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans with
        (m := (PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N);
        [lia|now apply N.mul_le_mono_l]).
    destruct (prep_width_bounds p) as [Hpositive _].
    unfold T_priority; time_simpl; time_cbn.
    clear -Hget' Hpositive; unfold c_lookup; nia.
  Qed.

  (** Maximum and minimum compare only the bits of their first priority. *)
  Lemma T_priority_extrema : forall p pol c acc, prio_ok p pol ->
    In c (key_support p) ->
    (Pos.T_max (priority pol c) acc <= 4 * prep_width p)%N /\
    (Pos.T_min (priority pol c) acc <= 4 * prep_width p)%N.
  Proof.
    intros p pol c acc Hprio Hc.
    pose proof (priority_bits p pol c Hprio Hc) as Hbits.
    pose proof (Std.Pos.T_compare_le (priority pol c) acc) as Hcompare.
    destruct (prep_width_bounds p) as [Hpositive [Hkey _]].
    split; [unfold Pos.T_max|unfold Pos.T_min]; time_cbn;
      clear -Hbits Hcompare Hpositive Hkey; nia.
  Qed.

  (** The maximum scan has a width bound independent of its accumulated priority. *)
  Lemma T_priority_max_callback : forall p pol x acc, S.wf p -> prio_ok p pol ->
    In (S.key_code x) (key_support p) ->
    (1 + ((S.T_key_code x + T_priority pol (S.key_code x)) +
      Pos.T_max (priority pol (S.key_code x)) acc) <=
      12 * c_lookup * prep_width p)%N.
  Proof.
    intros p pol x acc Hwf Hprio Hx.
    pose proof (key_support_bits p (S.key_code x) Hwf Hx) as Hbits.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (T_priority_bound p pol (S.key_code x) Hbits) as Hprio_time.
    destruct (T_priority_extrema p pol (S.key_code x) acc Hprio Hx) as [Hmax _].
    assert (Hwidth : (N.of_nat (S.key_bits x + 1) <= prep_width p)%N)
      by (unfold prep_width, S.key_bits; lia).
    assert (Hcode' : (S.T_key_code x <= S.c_sys * prep_width p)%N)
      by (eapply N.le_trans; [exact Hcode|now apply N.mul_le_mono_l]).
    destruct (prep_width_bounds p) as [Hpositive _].
    clear -Hprio_time Hmax Hcode' Hpositive; unfold c_lookup in *; nia.
  Qed.

  (** A row-rank callback either skips a head or compares one width-bounded priority. *)
  Lemma T_rank_callback : forall p pol y acc, S.wf p -> prio_ok p pol ->
    In (S.key_code y) (key_support p) ->
    (1 + S.T_key_code y + (T_heads pol + T_trie_get (S.key_code y) (heads pol)) +
      match trie_get (S.key_code y) (heads pol) with
      | Some _ => 0 | None => T_priority pol (S.key_code y) +
        Pos.T_min (priority pol (S.key_code y)) acc end <=
      16 * c_lookup * prep_width p)%N.
  Proof.
    intros p pol y acc Hwf Hprio Hy.
    pose proof (key_support_bits p (S.key_code y) Hwf Hy) as Hbits.
    pose proof (S.T_key_code_le y) as Hcode.
    pose proof (PTrieT.T_get_le _ (S.key_code y) (heads pol)) as Hget.
    unfold PTrieT.T_get in Hget.
    pose proof (T_priority_bound p pol (S.key_code y) Hbits) as Hprio_time.
    destruct (T_priority_extrema p pol (S.key_code y) acc Hprio Hy) as [_ Hmin].
    assert (Hwidth : (N.of_nat (S.key_bits y + 1) <= prep_width p)%N)
      by (unfold prep_width, S.key_bits; lia).
    assert (Hcode' : (S.T_key_code y <= S.c_sys * prep_width p)%N)
      by (eapply N.le_trans; [exact Hcode|now apply N.mul_le_mono_l]).
    assert (Hget' : (T_trie_get (S.key_code y) (heads pol) <=
      PTrieT.c_trie * prep_width p)%N)
      by (eapply N.le_trans with
        (m := (PTrieT.c_trie * N.of_nat (S.key_bits y + 1))%N);
        [unfold S.key_bits; lia|now apply N.mul_le_mono_l]).
    destruct (prep_width_bounds p) as [Hpositive _].
    destruct (trie_get (S.key_code y) (heads pol)); time_simpl; time_cbn;
      clear -Hprio_time Hmin Hcode' Hget' Hpositive; unfold c_lookup in *; nia.
  Qed.

  (** A row rank charges each declared write occurrence and its target accessor. *)
  Lemma T_rank_with_top_bound : forall p pol top r, S.wf p -> prio_ok p pol ->
    In r (S.rows p) -> (T_rank_with_top p pol top r <= 32 * c_lookup * prep_row p r)%N.
  Proof.
    intros p pol top r Hwf Hprio Hr.
    destruct (prep_accessors p r Hwf Hr) as [Htarget [_ Hsides]].
    assert (Hstep : forall y acc, In y (S.target p r :: S.sides p r) ->
      (1 + (S.T_key_code y + ((T_heads pol + T_trie_get (S.key_code y) (heads pol)) +
        match trie_get (S.key_code y) (heads pol) with
        | Some _ => 0 | None => T_priority pol (S.key_code y) +
          Pos.T_min (priority pol (S.key_code y)) acc end)) <=
        16 * c_lookup * prep_width p)%N).
    { intros y acc Hy; pose proof (T_rank_callback p pol y acc Hwf Hprio) as Hcallback.
      assert (Hsupport : In (S.key_code y) (key_support p)).
      { apply key_support_spec; exists r, y; split; [exact Hr|].
        split; [apply in_or_app; now left|reflexivity]. }
      specialize (Hcallback Hsupport); lia. }
    pose proof (fold_right_member_bound
      (fun y acc => match trie_get (S.key_code y) (heads pol) with
        | Some _ => acc | None => Pos.min (priority pol (S.key_code y)) acc end)
      (fun y acc => 1 + (S.T_key_code y +
        ((T_heads pol + T_trie_get (S.key_code y) (heads pol)) +
        match trie_get (S.key_code y) (heads pol) with
        | Some _ => 0 | None => T_priority pol (S.key_code y) +
          Pos.T_min (priority pol (S.key_code y)) acc end)))%N
      _ top _ Hstep) as Hfold.
    destruct (prep_row_bounds p r) as [Hpositive [_ [_ [_ Hwrites]]]].
    destruct (prep_width_bounds p) as [Hwidth _].
    cbn [length] in Hfold; rewrite Nat2N.inj_succ in Hfold.
    rewrite Nat2N.inj_add in Hwrites.
    unfold T_rank_with_top; time_cbn.
    clear -Htarget Hsides Hfold Hpositive Hwrites Hwidth; unfold c_lookup in *; nia.
  Qed.

  (** The shared preparation width is paid by every listed row or key occurrence. *)
  Lemma prep_totals : forall p,
    (N.of_nat (C p) <= N.of_nat (prep p))%N /\
    (N.of_nat (D p) * prep_width p <= N.of_nat (prep p))%N /\
    (C p <> 0 -> (prep_width p <= N.of_nat (prep p))%N).
  Proof.
    intro p; unfold prep, prep_width; rewrite Nat2N.inj_mul.
    assert (Hwidth : (1 <= N.of_nat (S.kw p + Nat.log2 (C p) + 1))%N) by lia.
    rewrite Nat2N.inj_add; split; [nia|split; [nia|]].
    intro Hpositive; assert (0 < N.of_nat (C p))%N by lia; nia.
  Qed.

  (** Reader-index construction sums the budgets of its numbered source rows. *)
  Lemma T_index_rows_bound : forall p, S.wf p ->
    (List.T_fold_right (index_row p) (fun ir idx => T_index_row p ir idx)
      (Empty, Empty) (combine (row_ids p) (S.rows p)) <=
      64 * c_lookup * (N.of_nat (prep p) + N.of_nat (C p) * unit p) + 1)%N.
  Proof.
    intros p Hwf.
    assert (Hstep : forall ir idx, In ir (combine (row_ids p) (S.rows p)) ->
      (T_index_row p ir idx + 1 <= 64 * c_lookup * prep_row p (snd ir))%N).
    { intros [id r] idx Hin; apply T_index_row_bound; [exact Hwf| |].
      - eapply in_combine_l; exact Hin.
      - eapply in_combine_r; exact Hin. }
    pose proof (fold_right_budget (index_row p) (fun ir idx => T_index_row p ir idx)
      (fun ir => 64 * c_lookup * prep_row p (snd ir))%N
      _ (Empty, Empty) Hstep) as Hfold.
    cbn beta in Hfold.
    rewrite (prep_combine_sum (row_ids p) (S.rows p)
      (fun r => (64 * c_lookup * prep_row p r)%N) (row_ids_length p)) in Hfold.
    rewrite prep_row_sum in Hfold; fold (C p) (D p) in Hfold.
    destruct (prep_totals p) as [_ [Hmass _]].
    eapply N.le_trans; [exact Hfold|].
    apply N.add_le_mono_r, N.mul_le_mono_l, N.add_le_mono_r; exact Hmass.
  Qed.

  (** Inserting a cached rank adds one identifier traversal to its row-rank computation. *)
  Lemma T_rank_insert_bound : forall p pol top ir acc, S.wf p -> prio_ok p pol ->
    In ir (combine (row_ids p) (S.rows p)) ->
    (1 + ((Datatypes.T_fst ir + (Datatypes.T_snd ir +
      T_rank_with_top p pol top (snd ir))) +
      PTrieCode.T_set (fst ir) (rank_with_top p pol top (snd ir)) acc) + 1 <=
      64 * c_lookup * prep_row p (snd ir))%N.
  Proof.
    intros p pol top [id r] acc Hwf Hprio Hin.
    assert (Hid : In id (row_ids p)) by (eapply in_combine_l; exact Hin).
    assert (Hr : In r (S.rows p)) by (eapply in_combine_r; exact Hin).
    pose proof (T_rank_with_top_bound p pol top r Hwf Hprio Hr) as Hrank.
    pose proof (T_prep_set p id (rank_with_top p pol top r) acc Hid) as Hset.
    destruct (prep_row_bounds p r) as [Hpositive [Hwidth _]].
    assert (Hset' : (PTrieCode.T_set id (rank_with_top p pol top r) acc <=
      2 * PTrieT.c_trie * prep_row p r)%N).
    { eapply N.le_trans; [exact Hset|]; now apply N.mul_le_mono_l. }
    cbn beta iota zeta delta [fst snd]; time_simpl.
    clear -Hrank Hset' Hpositive; unfold c_lookup in *; nia.
  Qed.

  (** Rank-table construction sums the same numbered-row preparation budgets. *)
  Lemma T_rank_rows_bound : forall p pol top, S.wf p -> prio_ok p pol ->
    (List.T_fold_right
      (fun ir acc => PTrieCode.set (fst ir) (rank_with_top p pol top (snd ir)) acc)
      (fun ir acc => 1 + ((Datatypes.T_fst ir + (Datatypes.T_snd ir +
        T_rank_with_top p pol top (snd ir))) +
        PTrieCode.T_set (fst ir) (rank_with_top p pol top (snd ir)) acc))%N
      Empty (combine (row_ids p) (S.rows p)) <=
      64 * c_lookup * (N.of_nat (prep p) + N.of_nat (C p) * unit p) + 1)%N.
  Proof.
    intros p pol top Hwf Hprio.
    pose proof (fold_right_budget
      (fun ir acc => PTrieCode.set (fst ir) (rank_with_top p pol top (snd ir)) acc)
      (fun ir acc => 1 + ((Datatypes.T_fst ir + (Datatypes.T_snd ir +
        T_rank_with_top p pol top (snd ir))) +
        PTrieCode.T_set (fst ir) (rank_with_top p pol top (snd ir)) acc))%N
      (fun ir => 64 * c_lookup * prep_row p (snd ir))%N
      _ Empty (fun ir acc Hin => T_rank_insert_bound p pol top ir acc Hwf Hprio Hin))
      as Hfold.
    cbn beta in Hfold.
    rewrite (prep_combine_sum (row_ids p) (S.rows p)
      (fun r => (64 * c_lookup * prep_row p r)%N) (row_ids_length p)) in Hfold.
    rewrite prep_row_sum in Hfold; fold (C p) (D p) in Hfold.
    destruct (prep_totals p) as [_ [Hmass _]].
    eapply N.le_trans; [exact Hfold|].
    apply N.add_le_mono_r, N.mul_le_mono_l, N.add_le_mono_r; exact Hmass.
  Qed.

  (** The fallback-priority scan uses the primary write, side writes and reads. *)
  Definition prep_keys p r := S.target p r :: S.sides p r ++ S.deps p r.

  TimeFun prep_keys.

  (** Listing one row's priority keys fits that row's preparation budget. *)
  Lemma T_prep_keys_bound : forall p r, S.wf p -> In r (S.rows p) ->
    (T_prep_keys p r + N.of_nat (length (prep_keys p r)) + 2 <=
      16 * c_lookup * prep_row p r)%N.
  Proof.
    intros p r Hwf Hr.
    destruct (prep_accessors p r Hwf Hr) as [Htarget [Hdeps Hsides]].
    pose proof (Datatypes.T_app_le (S.sides p r) (S.deps p r)) as Happ.
    destruct (prep_row_bounds p r) as [Hpositive [_ [_ [_ Hwrites]]]].
    destruct (prep_width_bounds p) as [Hwidth _].
    assert (Hcount : (N.of_nat (length (prep_keys p r)) <= prep_row p r)%N).
    { unfold prep_keys; cbn [length]; rewrite length_app.
      unfold prep_row; rewrite !Nat2N.inj_add, Nat2N.inj_succ; time_cbn; nia. }
    assert (Happ' : (Datatypes.T_app (S.sides p r) (S.deps p r) <= prep_row p r)%N).
    { rewrite Nat2N.inj_add in Hwrites.
      clear -Happ Hwrites Hwidth; nia. }
    unfold T_prep_keys; cbn beta zeta.
    clear -Htarget Hdeps Hsides Happ' Hcount Hpositive; unfold c_lookup; nia.
  Qed.

  (** The flattened priority scan has exactly the declared occurrence count. *)
  Lemma prep_keys_length : forall p,
    length (flat_map (prep_keys p) (S.rows p)) = D p.
  Proof.
    intro p; unfold D; induction (S.rows p) as [|r rs IH];
      cbn [flat_map fold_right List.map length]; [reflexivity|].
    rewrite length_app, IH; unfold prep_keys; cbn [length]; rewrite length_app; lia.
  Qed.

  (** Every flattened priority key belongs to the declared system support. *)
  Lemma prep_keys_support : forall p x,
    In x (flat_map (prep_keys p) (S.rows p)) -> In (S.key_code x) (key_support p).
  Proof.
    intros p x Hin; apply in_flat_map in Hin as [r [Hr Hx]].
    apply key_support_spec; exists r, x; split; [exact Hr|].
    split; [exact Hx|reflexivity].
  Qed.

  (** Listing all priority keys sums the row budgets before computing the maximum. *)
  Lemma T_prep_keys_rows : forall p, S.wf p ->
    (Code.List.T_flat_map (prep_keys p) (T_prep_keys p) (S.rows p) <=
      16 * c_lookup * (N.of_nat (prep p) + N.of_nat (C p) * unit p) + 1)%N.
  Proof.
    intros p Hwf.
    pose proof (flat_map_budget (prep_keys p) (T_prep_keys p)
      (fun r => 16 * c_lookup * prep_row p r)%N (S.rows p)
      (fun r Hr => T_prep_keys_bound p r Hwf Hr)) as Hflat.
    cbn beta in Hflat.
    rewrite prep_row_sum in Hflat; fold (C p) (D p) in Hflat.
    destruct (prep_totals p) as [_ [Hmass _]].
    eapply N.le_trans; [exact Hflat|].
    apply N.add_le_mono_r, N.mul_le_mono_l, N.add_le_mono_r; exact Hmass.
  Qed.

  (** Scanning the fallback maximum pays once for every declared occurrence. *)
  Lemma T_top_scan_bound : forall p pol, S.wf p -> prio_ok p pol ->
    (List.T_fold_right
      (fun x acc => Pos.max (priority pol (S.key_code x)) acc)
      (fun x acc => 1 + ((S.T_key_code x + T_priority pol (S.key_code x)) +
        Pos.T_max (priority pol (S.key_code x)) acc))%N
      1%positive (flat_map (prep_keys p) (S.rows p)) <=
      16 * c_lookup * (N.of_nat (prep p) + 1))%N.
  Proof.
    intros p pol Hwf Hprio.
    pose proof (fold_right_member_bound
      (fun x acc => Pos.max (priority pol (S.key_code x)) acc)
      (fun x acc => 1 + ((S.T_key_code x + T_priority pol (S.key_code x)) +
        Pos.T_max (priority pol (S.key_code x)) acc))%N
      _ 1%positive _ (fun x acc Hin =>
        T_priority_max_callback p pol x acc Hwf Hprio (prep_keys_support p x Hin))) as Hfold.
    cbn beta in Hfold.
    rewrite prep_keys_length in Hfold.
    destruct (prep_totals p) as [_ [Hmass _]].
    destruct (prep_width_bounds p) as [Hwidth _].
    clear -Hfold Hmass Hwidth; unfold c_lookup in *; nia.
  Qed.

  (** Taking the successor of the maximum uses at most the supported priority width. *)
  Lemma T_top_successor_bound : forall p pol, prio_ok p pol ->
    (Std.Pos.T_succ (fold_right
      (fun x acc => Pos.max (priority pol (S.key_code x)) acc)
      1%positive (flat_map (prep_keys p) (S.rows p))) <= 2 * prep_width p)%N.
  Proof.
    intros p pol Hprio.
    set (maximum := fold_right
      (fun x acc => Pos.max (priority pol (S.key_code x)) acc)
      1%positive (flat_map (prep_keys p) (S.rows p))).
    pose proof (top_rank_bits p pol Hprio) as Htop.
    rewrite <- top_rank_code_agrees in Htop.
    change (Pos.size_nat (Pos.succ maximum) <= S.kw p + 2) in Htop.
    assert (Hless : (maximum <= Pos.succ maximum)%positive)
      by (apply Pos.lt_le_incl, Pos.lt_succ_diag_r).
    pose proof (positive_bits_mono maximum (Pos.succ maximum) Hless) as Hbits.
    pose proof (Std.Pos.T_succ_le maximum) as Htime.
    assert (Hwidth : (N.of_nat (Pos.size_nat maximum) <= 2 * prep_width p)%N)
      by (unfold prep_width; lia).
    eapply N.le_trans; eassumption.
  Qed.

  (** Computing the fallback rank is paid by declared occurrences and row target accessors. *)
  Lemma T_top_rank_code_bound : forall p pol, S.wf p -> prio_ok p pol ->
    (T_top_rank_code p pol <=
      128 * c_lookup * (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1))%N.
  Proof.
    intros p pol Hwf Hprio; pose proof (S.T_rows_le p Hwf) as Hrows.
    change (S.T_rows p <= S.c_sys * N.of_nat (C p + 1))%N in Hrows.
    destruct (Nat.eq_dec (C p) 0) as [Hzero|Hpositive].
    - assert (Hnil : S.rows p = []) by (apply length_zero_iff_nil; exact Hzero).
      unfold T_top_rank_code; rewrite Hnil.
      time_unfold @Code.List.T_flat_map; time_unfold @List.T_fold_right.
      time_cbn; time_unfold @Std.Pos.T_succ; time_simpl; time_cbn.
      rewrite Hzero in Hrows.
      clear -Hrows; unfold c_lookup; nia.
    - pose proof (T_prep_keys_rows p Hwf) as Hkeys.
      pose proof (T_top_scan_bound p pol Hwf Hprio) as Hscan.
      pose proof (T_top_successor_bound p pol Hprio) as Hsucc.
      destruct (prep_totals p) as [Hcount [_ Hwidth]]; specialize (Hwidth Hpositive).
      unfold T_top_rank_code; fold (prep_keys p).
      change (fun r => 1 + (S.T_target p r + ((S.T_sides p r + S.T_deps p r) +
        Datatypes.T_app (S.sides p r) (S.deps p r))))%N with (T_prep_keys p).
      set (mass := (N.of_nat (prep p) + N.of_nat (C p) * unit p)%N) in *.
      assert (Hrows' : (S.T_rows p <= c_lookup * (mass + 1))%N).
      { eapply N.le_trans; [exact Hrows|].
        apply N.mul_le_mono; [unfold c_lookup; lia|].
        unfold mass; rewrite Nat2N.inj_add; lia. }
      assert (Hscan' : (16 * c_lookup * (N.of_nat (prep p) + 1) <=
        16 * c_lookup * (mass + 1))%N).
      { apply N.mul_le_mono_l; unfold mass; lia. }
      assert (Hsucc' : (2 * prep_width p <= 2 * (mass + 1))%N).
      { apply N.mul_le_mono_l; unfold mass; lia. }
      assert (Hcoefficient : (2 <= c_lookup)%N) by (unfold c_lookup; lia).
      clear -Hrows' Hkeys Hscan Hscan' Hsucc Hsucc' Hcoefficient; nia.
  Qed.

  (** Repeated row enumeration and pairing use the linear preparation budget. *)
  Lemma T_prepare_list_overhead : forall p, S.wf p ->
    (T_row_ids p + 2 * S.T_rows p + 2 * List.T_combine (row_ids p) (S.rows p) <=
      16 * c_lookup * (N.of_nat (prep p) + 1))%N.
  Proof.
    intros p Hwf; pose proof (T_row_ids_prep p Hwf) as Hids.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    change (S.T_rows p <= S.c_sys * N.of_nat (C p + 1))%N in Hrows.
    pose proof (List.T_combine_le (row_ids p) (S.rows p)) as Hcombine.
    rewrite row_ids_length in Hcombine.
    destruct (prep_totals p) as [Hcount _].
    assert (Hids' : (T_row_ids p <= 3 * c_lookup * (N.of_nat (prep p) + 1))%N).
    { eapply N.le_trans; [exact Hids|].
      apply N.mul_le_mono_r; unfold c_lookup; lia. }
    assert (Hrows' : (S.T_rows p <= c_lookup * (N.of_nat (prep p) + 1))%N).
    { eapply N.le_trans; [exact Hrows|].
      apply N.mul_le_mono; [unfold c_lookup; lia|rewrite Nat2N.inj_add; lia]. }
    assert (Hcoefficient : (2 <= c_lookup)%N) by (unfold c_lookup; lia).
    clear -Hids' Hrows' Hcombine Hcount Hcoefficient; nia.
  Qed.

  (** All construction before initial enqueue fits a single preparation budget. *)
  Lemma T_prepare_construction_bound : forall p pol, S.wf p -> prio_ok p pol ->
    (T_prepare p pol <=
      512 * c_lookup * (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1) +
      T_enqueue p pol (row_ids p) (prepare_seed p pol))%N.
  Proof.
    intros p pol Hwf Hprio.
    pose proof (T_prepare_list_overhead p Hwf) as Hlists.
    pose proof (T_index_rows_bound p Hwf) as Hindex.
    pose proof (T_top_rank_code_bound p pol Hwf Hprio) as Htop.
    pose proof (T_rank_rows_bound p pol (top_rank_code p pol) Hwf Hprio) as Hranks.
    set (idx := fold_right (index_row p) (Empty, Empty)
      (combine (row_ids p) (S.rows p))).
    pose proof (Datatypes.T_fst_le idx) as Hfst.
    pose proof (Datatypes.T_snd_le idx) as Hsnd.
    set (mass := (N.of_nat (prep p) + N.of_nat (C p) * unit p)%N) in *.
    assert (Hlists' : (T_row_ids p + 2 * S.T_rows p +
      2 * List.T_combine (row_ids p) (S.rows p) <= 16 * c_lookup * (mass + 1))%N).
    { eapply N.le_trans; [exact Hlists|].
      apply N.mul_le_mono_l; unfold mass; lia. }
    assert (Hcoefficient : (2 <= c_lookup)%N) by (unfold c_lookup; lia).
    unfold T_prepare, prepare_seed; cbn beta zeta; fold idx.
    clear -Hlists' Hindex Htop Hranks Hfst Hsnd Hcoefficient; nia.
  Qed.

  (** W1 charges indexing, numbering and initial guarded enqueue to preparation. *)
  Lemma W1_prepare : forall p pol, S.wf p -> prio_ok p pol ->
    (T_prepare p pol <= k_prepare * (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1))%N.
  Proof.
    intros p pol Hwf Hprio.
    pose proof (T_prepare_construction_bound p pol Hwf Hprio) as Htables.
    pose proof (prepare_enqueue_cost p pol Hwf Hprio) as Henqueue.
    set (total := (N.of_nat (prep p) + N.of_nat (C p) * unit p + 1)%N) in *.
    set (scale := (c_lookup + P.c_pol + Q.c_pq + c_loopN + 1)%N).
    assert (Htotal : (1 <= total)%N) by (unfold total; lia).
    assert (Hscale : (1 <= scale)%N) by (unfold scale; lia).
    assert (Htable_scale : (512 * c_lookup * total <= 512 * scale * total)%N).
    { apply N.mul_le_mono_r, N.mul_le_mono_l; unfold scale; lia. }
    assert (Hqueue_scale : (2 * c_enqueue * N.of_nat (C p) * unit p <=
      256 * scale * total)%N).
    { replace (2 * c_enqueue * N.of_nat (C p) * unit p)%N with
        (256 * scale * (N.of_nat (C p) * unit p))%N by
        (unfold c_enqueue, scale; ring).
      apply N.mul_le_mono_l; unfold total; lia. }
    replace (k_prepare * total)%N with (4096 * scale * total)%N by
      (unfold k_prepare, scale; ring).
    clear -Htables Henqueue Htable_scale Hqueue_scale Htotal Hscale; nia.
  Qed.
  (** Initial guarded pushes supply the potential consumed by later queue operations. *)
  Lemma W1_queue_phi : forall p pol, S.wf p -> prio_ok p pol ->
    (queue_phi p (prepare p pol) <= k_prepare * N.of_nat (C p + D p) * unit p)%N.
  Proof.
    intros p pol Hwf Hprio; destruct (Nat.eq_dec (C p) 0) as [Hzero|Hpositive].
    - assert (Hids : row_ids p = []).
      { apply length_zero_iff_nil; now rewrite row_ids_length. }
      rewrite prepare_eq, Hids, enqueue_nil, prepare_seed_phi; apply N.le_0_l.
    - pose proof (T_enqueue_bound p pol (row_ids p) (prepare_seed p pol)
        Hwf Hprio (prepare_seed_invariant p pol) (fun id Hin => Hin)) as Hcost.
      rewrite <- prepare_eq, prepare_seed_phi, row_ids_length in Hcost.
      assert (Hcount : (N.of_nat (C p + 1) <= 2 * N.of_nat (C p + D p))%N) by lia.
      assert (Hmul : (c_enqueue * N.of_nat (C p + 1) * unit p <=
        c_enqueue * (2 * N.of_nat (C p + D p)) * unit p)%N).
      { apply N.mul_le_mono_r; now apply N.mul_le_mono_l. }
      eapply N.le_trans with
        (m := (2 * c_enqueue * N.of_nat (C p + D p) * unit p)%N).
      + clear -Hcost Hmul; nia.
      + apply N.mul_le_mono_r, N.mul_le_mono_r; unfold c_enqueue, k_prepare; nia.
  Qed.
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
  Proof.
    intros p pol ids s Hwf Hprio Hinv Hids.
    pose proof (T_enqueue_bound p pol ids s Hwf Hprio Hinv Hids) as Hcost.
    eapply N.le_trans; [exact Hcost|].
    unfold c_enqueue, k_update; nia.
  Qed.
  (** W3 keeps the value invariant and charges reader pushes against queue potential. *)
  Lemma W3_update : forall p pol s x a, S.wf p -> prio_ok p pol -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) ->
    B.inv p (look (update_one p pol s (x, a)) x) /\
    (T_update_one p pol s (x, a) + queue_phi p (update_one p pol s (x, a)) <=
      k_update * N.of_nat (1 + push_work p s x a) * unit p +
      k_update * strict_head_work pol s x a + queue_phi p s)%N.
  Proof.
    intros p pol s x a Hwf Hprio Hinv Ha Hsupport; split.
    - exact (proj1 (proj2 (F9_update_inv p pol s x a Hwf Hprio Hinv Ha Hsupport)) x).
    - now apply T_update_queue_bound.
  Qed.
  (** Callback accounting retains every emitted occurrence and every intermediate update cost. *)
  Lemma W3_step : forall p pol s pr id q1 r a ss, S.wf p -> invariant p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) -> source_row p id = Some r ->
    eval_row p r (ws_store s) = Some (a, ss) ->
    (T_step p pol s <= k_loop * (Q.T_pop (ws_queue s) + T_row_at s id +
      T_eval_row p r (ws_store s) + S.T_target p r +
      N.of_nat ((length (S.deps p r) + 1) * (S.kw p + Nat.log2 (C p) + 1)) +
      output_cost p pol ((S.target p r, a) :: ss)
        (after_pop p s id q1) + N.of_nat (length ss) + 1))%N.
  Proof.
    intros p pol s pr id q1 r a ss Hwf Hinv Hpop Hrow Heval.
    pose proof (T_step_accounting p pol s pr id q1 r a ss Hwf Hinv Hpop Hrow Heval)
      as Hcost.
    assert (Hloop : (c_step + 2 <= k_loop)%N) by (unfold k_loop; nia).
    clear -Hcost Hloop; nia.
  Qed.
  (** Pointwise bounds are preserved by finite natural-number sums. *)
  Lemma incidence_sum_bound : forall A (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) ->
    fold_right Nat.add 0 (List.map f xs) <= fold_right Nat.add 0 (List.map g xs).
  Proof.
    intros A f g xs; induction xs as [|x xs IH]; intros Hbound.
    - reflexivity.
    - cbn [List.map fold_right].
      pose proof (Hbound x (or_introl eq_refl)) as Hhead.
      assert (Htail : forall y, In y xs -> f y <= g y).
      { intros y Hy; apply Hbound; now right. }
      specialize (IH Htail); lia.
  Qed.

  (** Finite sums distribute over pointwise addition. *)
  Lemma incidence_sum_plus : forall A (f g : A -> nat) xs,
    fold_right Nat.add 0 (List.map (fun x => f x + g x) xs) =
      fold_right Nat.add 0 (List.map f xs) + fold_right Nat.add 0 (List.map g xs).
  Proof.
    intros A f g xs; induction xs; cbn [List.map fold_right]; lia.
  Qed.

  (** Finite incidence sums may be transposed without changing their value. *)
  Lemma incidence_sum_swap : forall A B (f : A -> B -> nat) xs ys,
    fold_right Nat.add 0 (List.map
      (fun x => fold_right Nat.add 0 (List.map (f x) ys)) xs) =
    fold_right Nat.add 0 (List.map
      (fun y => fold_right Nat.add 0 (List.map (fun x => f x y) xs)) ys).
  Proof.
    intros A B f xs; induction xs as [|x xs IH]; intro ys.
    - induction ys; cbn [List.map fold_right] in *; lia.
    - cbn [List.map fold_right]; rewrite incidence_sum_plus, IH; reflexivity.
  Qed.

  (** Filtering a finite sum is equivalent to assigning zero to excluded occurrences. *)
  Lemma incidence_sum_filter : forall A (test : A -> bool) (f : A -> nat) xs,
    fold_right Nat.add 0 (List.map f (filter test xs)) =
      fold_right Nat.add 0 (List.map (fun x => if test x then f x else 0) xs).
  Proof.
    intros A test f xs; induction xs as [|x xs IH]; [reflexivity|].
    cbn [filter List.map fold_right]; destruct (test x); cbn [List.map fold_right]; lia.
  Qed.

  (** A fixed contribution summed over selected codes is their count times that contribution. *)
  Lemma incidence_sum_constant : forall A (test : A -> bool) xs k,
    fold_right Nat.add 0 (List.map (fun x => if test x then k else 0) xs) =
      length (filter test xs) * k.
  Proof.
    intros A test xs; induction xs as [|x xs IH]; intro k; [reflexivity|].
    cbn [List.map fold_right filter]; destruct (test x); cbn [length]; rewrite IH; lia.
  Qed.

  (** Adding one per occurrence converts a bucket length into its weighted sum. *)
  Lemma incidence_sum_length : forall A (f : A -> nat) xs,
    fold_right Nat.add 0 (List.map f xs) + length xs =
      fold_right Nat.add 0 (List.map (fun x => f x + 1) xs).
  Proof.
    intros A f xs; induction xs; cbn [List.map fold_right length]; lia.
  Qed.

  (** Summing indexed lookups over the complete index interval reproduces the source sum. *)
  Lemma incidence_sum_nth : forall A (f : A -> nat) xs,
    fold_right Nat.add 0 (List.map (fun n =>
      match nth_error xs n with Some x => f x | None => 0 end) (seq 0 (length xs))) =
    fold_right Nat.add 0 (List.map f xs).
  Proof.
    intros A f xs; induction xs as [|x xs IH]; [reflexivity|].
    cbn [length seq List.map fold_right nth_error].
    rewrite <- seq_shift, map_map; f_equal; exact IH.
  Qed.

  (** Numbered row occurrences preserve sums over the original occurrence list. *)
  Lemma incidence_numbered_rows : forall p (f : S.row -> nat),
    fold_right Nat.add 0 (List.map (fun id =>
      match source_row p id with Some r => f r | None => 0 end) (row_ids p)) =
    fold_right Nat.add 0 (List.map f (S.rows p)).
  Proof.
    intros p f; transitivity (fold_right Nat.add 0 (List.map (fun n =>
      match nth_error (S.rows p) n with Some r => f r | None => 0 end)
      (seq 0 (length (S.rows p))))).
    - rewrite F0_row_ids, map_map; f_equal; apply map_ext; intro n.
      now rewrite F1_numbering.
    - apply incidence_sum_nth.
  Qed.

  (** A row matches at most one distinct support code per declared dependency occurrence. *)
  Lemma incidence_codes_count : forall p r,
    length (filter (fun c => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r))
      (key_support p)) <= length (S.deps p r).
  Proof.
    intros p r; rewrite <- (length_map S.key_code (S.deps p r)).
    apply NoDup_incl_length.
    - apply NoDup_filter; unfold key_support; apply NoDup_nodup.
    - intros c Hin; apply filter_In in Hin as [_ Hread].
      apply existsb_exists in Hread as [x [Hin Hequal]].
      apply Pos.eqb_eq in Hequal; apply in_map_iff; exists x; split; [congruence|exact Hin].
  Qed.

  (** Weighted reader degree plus degree charges one weighted unit per reading occurrence. *)
  Lemma incidence_bucket : forall p c,
    weighted_degree p c + degree p c =
    fold_right Nat.add 0 (List.map (fun id =>
      if match source_row p id with
        | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
        | None => false
        end then weight p id + 1 else 0) (row_ids p)).
  Proof.
    intros p c; unfold weighted_degree, degree; rewrite incidence_sum_length.
    unfold source_readers; apply incidence_sum_filter.
  Qed.

  (** Distinct source codes charge at most the public weighted dependency incidence budget. *)
  Lemma support_incidence_bound : forall p,
    fold_right Nat.add 0 (List.map
      (fun c => weighted_degree p c + degree p c) (key_support p)) <= DW p.
  Proof.
    intro p.
    assert (Hswap :
      fold_right Nat.add 0 (List.map
        (fun c => weighted_degree p c + degree p c) (key_support p)) =
      fold_right Nat.add 0 (List.map (fun id =>
        fold_right Nat.add 0 (List.map (fun c =>
          if match source_row p id with
            | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
            | None => false
            end then weight p id + 1 else 0) (key_support p))) (row_ids p))).
    { transitivity (fold_right Nat.add 0 (List.map (fun c =>
        fold_right Nat.add 0 (List.map (fun id =>
          if match source_row p id with
            | Some r => existsb (fun x => Pos.eqb c (S.key_code x)) (S.deps p r)
            | None => false
            end then weight p id + 1 else 0) (row_ids p))) (key_support p))).
      - f_equal; apply map_ext; intro c; apply incidence_bucket.
      - apply incidence_sum_swap. }
    rewrite Hswap.
    transitivity (fold_right Nat.add 0 (List.map (fun id =>
      match source_row p id with
      | Some r => (length (S.deps p r) + 1) *
          (length (S.deps p r) + length (S.sides p r) + 1)
      | None => 0
      end) (row_ids p))).
    - apply incidence_sum_bound; intros id Hid.
      destruct (source_row_total p id Hid) as [r Hrow].
      rewrite Hrow; unfold weight; rewrite Hrow, incidence_sum_constant.
      pose proof (incidence_codes_count p r); nia.
    - rewrite incidence_numbered_rows; reflexivity.
  Qed.

  (** A single changed member accounts for the entire difference of two finite sums. *)
  Lemma credit_sum_change : forall A (eq_dec : forall x y : A, {x = y} + {x <> y})
      (f g : A -> nat) xs x, NoDup xs -> In x xs ->
    (forall y, In y xs -> y <> x -> f y = g y) ->
    fold_right Nat.add 0 (List.map f xs) + g x =
      fold_right Nat.add 0 (List.map g xs) + f x.
  Proof.
    intros A eq_dec f g xs; induction xs as [|y ys IH]; intros x Hnodup Hin Hother.
    - contradiction.
    - inversion Hnodup as [|? ? Hfresh Htail]; subst.
      destruct (eq_dec y x) as [->|Hneq].
      + assert (Hsum : List.map f ys = List.map g ys).
        { apply map_ext_in; intros z Hz; apply Hother; [now right|].
          intro Heq; subst z; contradiction. }
        cbn [List.map fold_right]; rewrite Hsum; lia.
      + assert (Hxin : In x ys) by (destruct Hin; [congruence|assumption]).
        pose proof (IH x Htail Hxin
          (fun z Hz Hne => Hother z (or_intror Hz) Hne)) as Hsum.
        cbn [List.map fold_right]; rewrite (Hother y (or_introl eq_refl) Hneq); lia.
  Qed.

  (** A guarded insertion creates at most the selected row's weighted queue credit. *)
  Lemma queue_credit_enqueue_single : forall p pol s id, In id (row_ids p) ->
    queue_credit p (enqueue p pol [id] s) <= queue_credit p s + weight p id.
  Proof.
    intros p pol s id Hid; rewrite enqueue_single.
    destruct (trie_get id (ws_live s)) as [[]|]; [lia|].
    destruct (row_at s id) as [r|]; [|lia].
    set (rank := match trie_get id (ws_ranks s) with
      | Some rank => rank | None => 1%positive end).
    unfold queue_credit, enqueue_push; cbn [ws_queue].
    pose proof (credit_sum_change positive Pos.eq_dec
      (fun other => match Q.prio (Q.push (N.pos rank) id (ws_queue s)) other with
        | Some _ => weight p other | None => 0 end)
      (fun other => match Q.prio (ws_queue s) other with
        | Some _ => weight p other | None => 0 end)
      (row_ids p) id (row_ids_nodup p) Hid) as Hsum.
    assert (Hother : forall other, In other (row_ids p) -> other <> id ->
      match Q.prio (Q.push (N.pos rank) id (ws_queue s)) other with
      | Some _ => weight p other | None => 0 end =
      match Q.prio (ws_queue s) other with Some _ => weight p other | None => 0 end).
    { intros other _ Hneq; now rewrite Q.prio_push_other by congruence. }
    specialize (Hsum Hother); cbn beta in Hsum; rewrite Q.prio_push in Hsum.
    destruct (Q.prio (ws_queue s) id); lia.
  Qed.

  (** Enqueue creates no more credit than the weights of its supplied occurrences. *)
  Lemma queue_credit_enqueue : forall p pol ids s,
    (forall id, In id ids -> In id (row_ids p)) ->
    queue_credit p (enqueue p pol ids s) <= queue_credit p s +
      fold_right Nat.add 0 (List.map (weight p) ids).
  Proof.
    intros p pol ids; induction ids as [|id ids IH]; intros s Hids.
    - rewrite enqueue_nil; cbn; lia.
    - rewrite enqueue_cons; cbn [List.map fold_right].
      pose proof (queue_credit_enqueue_single p pol s id (Hids id (or_introl eq_refl)))
        as Hhead.
      specialize (IH (enqueue p pol [id] s)
        (fun other Hin => Hids other (or_intror Hin))); lia.
  Qed.

  (** A successful pop consumes exactly the popped row's weighted queue credit. *)
  Lemma queue_credit_pop : forall p pol s pr id q1, structural p pol s ->
    Q.pop (ws_queue s) = Some (pr, id, q1) ->
    queue_credit p s = queue_credit p (after_pop p s id q1) + weight p id.
  Proof.
    intros p pol s pr id q1 [Hwf [_ [_ [_ Hsupport]]]] Hpop.
    destruct (Q.pop_min _ _ _ _ Hwf Hpop) as [Hid [_ [Hnone Hother]]].
    pose proof (proj1 (Hsupport pr id Hid)) as Hin.
    unfold queue_credit; cbn [after_pop ws_queue].
    pose proof (credit_sum_change positive Pos.eq_dec
      (fun other => match Q.prio (ws_queue s) other with
        | Some _ => weight p other | None => 0 end)
      (fun other => match Q.prio q1 other with
        | Some _ => weight p other | None => 0 end)
      (row_ids p) id (row_ids_nodup p) Hin) as Hsum.
    assert (Hsame : forall other, In other (row_ids p) -> other <> id ->
      match Q.prio (ws_queue s) other with Some _ => weight p other | None => 0 end =
      match Q.prio q1 other with Some _ => weight p other | None => 0 end).
    { intros other _ Hneq; now rewrite Hother by exact Hneq. }
    specialize (Hsum Hsame); cbn beta in Hsum; rewrite Hid, Hnone in Hsum; lia.
  Qed.

  (** Rank debt reserves reader weight and one queue operation per remaining strict increase. *)
  Definition height_debt (p : S.prog) (rk : L.t -> nat) (h : nat) (s : state) : nat :=
    fold_right Nat.add 0 (List.map
      (fun c => (h - rk (raw_value s c)) * (weighted_degree p c + degree p c))
      (key_support p)).

  (** The public height potential is the sum of weighted row credit and rank debt. *)
  Lemma height_phi_debt : forall p rk h s,
    height_phi p rk h s =
      (k_credit * N.of_nat (queue_credit p s + height_debt p rk h s) * unit p +
        queue_phi p s)%N.
  Proof.
    reflexivity.
  Qed.

  (** Queue operations preserve every rank-debt term because they leave the store unchanged. *)
  Lemma height_debt_after_pop : forall p rk h s id q,
    height_debt p rk h (after_pop p s id q) = height_debt p rk h s.
  Proof.
    reflexivity.
  Qed.

  (** A strict invariant increase consumes at least one complete reader incidence allowance. *)
  Lemma height_debt_strict_update : forall p pol rk h s x a,
    invariant p pol s -> B.inv p a -> In (S.key_code x) (key_support p) ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) -> L.leb a (look s x) = false ->
    height_debt p rk h (update_one p pol s (x, a)) +
      weighted_degree p (S.key_code x) + degree p (S.key_code x) <=
      height_debt p rk h s.
  Proof.
    intros p pol rk h s x a Hinv Ha Hsupport Hrank Hstrict.
    set (c := S.key_code x).
    set (next := update_one p pol s (x, a)).
    set (old := look s x).
    set (value := fst (P.update pol c (counter s c) old a)).
    change (L.leb a old = false) in Hstrict.
    assert (Hvalue : raw_value next c = value) by apply raw_value_update_same.
    assert (Hold : raw_value s c = old) by apply raw_value_look.
    assert (Hold_inv : B.inv p old) by exact (proj1 (proj2 Hinv) x).
    assert (Hvalue_inv : B.inv p value) by (unfold value; now apply policy_update_inv).
    destruct (P.update_ub pol c (counter s c) old a) as [Hup Hcontribution].
    fold value in Hup, Hcontribution.
    assert (Hback : L.leb value old = false).
    { destruct (L.leb value old) eqn:Hback; [|reflexivity].
      pose proof (L.leb_trans a value old Hcontribution Hback); congruence. }
    destruct (Hrank old value Hold_inv Hvalue_inv Hup Hback) as [Hgrow Hcap].
    assert (Hdebt : h - rk value + 1 <= h - rk old) by lia.
    assert (Hother : forall d, In d (key_support p) -> d <> c ->
      (h - rk (raw_value s d)) * (weighted_degree p d + degree p d) =
      (h - rk (raw_value next d)) * (weighted_degree p d + degree p d)).
    { intros d _ Hneq; unfold next; now rewrite raw_value_update_other by exact Hneq. }
    pose proof (credit_sum_change positive Pos.eq_dec
      (fun d => (h - rk (raw_value s d)) * (weighted_degree p d + degree p d))
      (fun d => (h - rk (raw_value next d)) * (weighted_degree p d + degree p d))
      (key_support p) c (NoDup_nodup Pos.eq_dec _) Hsupport Hother) as Hsum.
    cbn beta in Hsum; fold (height_debt p rk h s) (height_debt p rk h next) in Hsum.
    rewrite Hold, Hvalue in Hsum; fold c next; clear -Hsum Hdebt; nia.
  Qed.

  (** Every reader push is paid by rank debt after accounting for new queued row weight. *)
  Lemma height_credit_update : forall p pol rk h s x a,
    invariant p pol s -> B.inv p a -> In (S.key_code x) (key_support p) ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    queue_credit p (update_one p pol s (x, a)) +
      height_debt p rk h (update_one p pol s (x, a)) + push_work p s x a <=
      queue_credit p s + height_debt p rk h s.
  Proof.
    intros p pol rk h s x a Hinv Ha Hsupport Hrank.
    destruct (L.leb a (look s x)) eqn:Hstable.
    - assert (Hsame : update_one p pol s (x, a) = s).
      { rewrite F6_indexed; cbn beta iota zeta; now rewrite Hstable. }
      rewrite Hsame; unfold push_work; rewrite Hstable; lia.
    - pose proof (height_debt_strict_update p pol rk h s x a Hinv Ha Hsupport Hrank Hstable)
        as Hdebt.
      set (c := S.key_code x) in *.
      set (ac := P.update pol c (counter s c) (look s x) a).
      set (base := WorklistState (PTrieCode.set c (x, fst ac) (ws_store s))
        (PTrieCode.set c (snd ac) (ws_counters s)) (ws_queue s) (ws_live s)
        (ws_rows s) (ws_readers s) (ws_armed s) (ws_ranks s)).
      assert (Hshape : update_one p pol s (x, a) =
        match trie_get c (ws_armed s) with
        | Some _ => base | None => arm c (enqueue p pol (readers s c) base)
        end).
      { rewrite F6_indexed; cbn beta iota zeta; now rewrite Hstable. }
      unfold push_work; rewrite Hstable; fold c.
      destruct (trie_get c (ws_armed s)) as [[]|] eqn:Harmed.
      + assert (Hqueue : queue_credit p (update_one p pol s (x, a)) = queue_credit p s).
        { rewrite Hshape; reflexivity. }
        rewrite Hqueue; lia.
      + assert (Hqueue : queue_credit p (update_one p pol s (x, a)) <=
          queue_credit p s + weighted_degree p c).
        { rewrite Hshape.
          change (queue_credit p (enqueue p pol (readers s c) base) <=
            queue_credit p s + weighted_degree p c).
          destruct (proj1 (proj2 (proj2 Hinv))) as [_ Hreaders].
          eapply Nat.le_trans; [apply queue_credit_enqueue|].
          - rewrite Hreaders; intros id Hin; unfold source_readers in Hin.
            now apply filter_In in Hin.
          - change (queue_credit p s +
              fold_right Nat.add 0 (List.map (weight p) (readers s c)) <=
              queue_credit p s + weighted_degree p c).
            unfold weighted_degree; now rewrite Hreaders. }
        lia.
  Qed.

  (** Widening-free policies have no strict-head timing allowance. *)
  Lemma strict_head_work_free : forall pol s x a, widening_free pol ->
    strict_head_work pol s x a = 0%N.
  Proof.
    intros pol s x a Hfree; unfold strict_head_work.
    destruct (L.leb a (look s x)); [reflexivity|now rewrite Hfree].
  Qed.

  (** One output callback spends only its ordinary unit after credit refunds. *)
  Lemma T_update_height : forall p pol rk h s x a,
    S.wf p -> prio_ok p pol -> widening_free pol -> invariant p pol s ->
    B.inv p a -> In (S.key_code x) (key_support p) -> (k_update <= k_credit)%N ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    (T_update_one p pol s (x, a) + height_phi p rk h (update_one p pol s (x, a)) <=
      k_update * unit p + height_phi p rk h s)%N.
  Proof.
    intros p pol rk h s x a Hwf Hprio Hfree Hinv Ha Hsupport Hcoeff Hrank.
    pose proof (T_update_queue_bound p pol s x a Hwf Hprio Hinv Ha Hsupport) as Hcost.
    rewrite strict_head_work_free in Hcost by exact Hfree.
    pose proof (height_credit_update p pol rk h s x a Hinv Ha Hsupport Hrank) as Hcredit.
    assert (HcreditN : (N.of_nat (queue_credit p (update_one p pol s (x, a))) +
      N.of_nat (height_debt p rk h (update_one p pol s (x, a))) +
      N.of_nat (push_work p s x a) <=
      N.of_nat (queue_credit p s) + N.of_nat (height_debt p rk h s))%N) by lia.
    rewrite !height_phi_debt, !Nat2N.inj_add.
    rewrite Nat2N.inj_add in Hcost.
    set (next := update_one p pol s (x, a)) in *.
    set (before := (N.of_nat (queue_credit p s) + N.of_nat (height_debt p rk h s))%N)
      in *.
    set (after := (N.of_nat (queue_credit p next) +
      N.of_nat (height_debt p rk h next))%N) in *.
    set (push := N.of_nat (push_work p s x a)) in *.
    assert (Hscale : (k_credit * (after + push) * unit p <=
      k_credit * before * unit p)%N).
    { apply N.mul_le_mono_r; now apply N.mul_le_mono_l. }
    assert (Hpush : (k_update * push * unit p <= k_credit * push * unit p)%N).
    { apply N.mul_le_mono_r; now apply N.mul_le_mono_r. }
    clear -Hcost Hscale Hpush; nia.
  Qed.

  (** Every emitted occurrence receives one ordinary callback unit along its actual state. *)
  Lemma output_cost_height : forall p pol rk h outs s,
    S.wf p -> prio_ok p pol -> widening_free pol -> invariant p pol s ->
    Forall (fun xa => B.inv p (snd xa) /\ In (S.key_code (fst xa)) (key_support p)) outs ->
    (k_update <= k_credit)%N ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    (output_cost p pol outs s +
      height_phi p rk h (fold_left (update_one p pol) outs s) <=
      k_update * N.of_nat (length outs) * unit p + height_phi p rk h s)%N.
  Proof.
    intros p pol rk h outs; induction outs as [|[x a] outs IH];
      intros s Hwf Hprio Hfree Hinv Houts Hcoeff Hrank.
    - unfold output_cost; cbn [fold_left snd length]; nia.
    - inversion Houts as [|? ? [Ha Hsupport] Htail]; subst.
      pose proof (T_update_height p pol rk h s x a
        Hwf Hprio Hfree Hinv Ha Hsupport Hcoeff Hrank) as Hhead.
      specialize (IH (update_one p pol s (x, a)) Hwf Hprio Hfree
        (F9_update_inv p pol s x a Hwf Hprio Hinv Ha Hsupport) Htail Hcoeff Hrank).
      rewrite output_cost_cons; cbn [fold_left length]; rewrite Nat2N.inj_succ; nia.
  Qed.


  (** Every evaluated output has an invariant value and a declared support encoding. *)
  Lemma eval_outputs_invariant : forall p pol s r a ss,
    S.wf p -> invariant p pol s -> In r (S.rows p) ->
    eval_row p r (ws_store s) = Some (a, ss) ->
    Forall (fun xa => B.inv p (snd xa) /\ In (S.key_code (fst xa)) (key_support p))
      ((S.target p r, a) :: ss).
  Proof.
    intros p pol s r a ss Hwf Hinv Hr Heval.
    assert (Hlook : forall x, B.inv p (look s x)) by exact (proj1 (proj2 Hinv)).
    pose proof Heval as Hsystem; change (S.eval p r (look s) = Some (a, ss)) in Hsystem.
    destruct (B.inv_rows p r (look s) a ss Hwf Hr Hlook Hsystem) as [Ha Hss].
    assert (Hvalues : Forall (fun xa => B.inv p (snd xa)) ((S.target p r, a) :: ss)).
    { constructor; assumption. }
    apply Forall_forall; intros [x b] Hin; cbn [fst snd]; split.
    - rewrite Forall_forall in Hvalues; exact (Hvalues (x, b) Hin).
    - apply key_support_spec; exists r, x; split; [exact Hr|]; split; [|reflexivity].
      apply in_or_app; left; eapply eval_outputs_writes; eassumption.
  Qed.

  (** A popped row pays its evaluator and bookkeeping in proportion to its declared weight. *)
  Lemma T_step_weighted : forall p pol s pr id q1 r a ss,
    S.wf p -> invariant p pol s -> Q.pop (ws_queue s) = Some (pr, id, q1) ->
    source_row p id = Some r -> eval_row p r (ws_store s) = Some (a, ss) ->
    (T_step p pol s <= Q.T_pop (ws_queue s) +
      output_cost p pol ((S.target p r, a) :: ss) (after_pop p s id q1) +
      16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) *
        N.of_nat (weight p id) * unit p)%N.
  Proof.
    intros p pol s pr id q1 r a ss Hwf Hinv Hpop Hsource Heval.
    destruct (source_row_member p id r Hsource) as [Hid Hr].
    pose proof (T_step_accounting p pol s pr id q1 r a ss Hwf Hinv Hpop Hsource Heval)
      as Hstep.
    pose proof (W2_eval p pol r s Hwf Hr Hinv) as Heval_cost.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (T_row_at_bits s id) as Hrow.
    pose proof (row_ids_bits p id Hid) as Hidbits.
    pose proof Heval as Hsystem; change (S.eval p r (look s) = Some (a, ss)) in Hsystem.
    pose proof (S.sides_count p r (look s) a ss Hwf Hr Hsystem) as Hsides.
    destruct (time_unit_bounds p) as [Hu [_ [Hids [_ Hwork]]]].
    assert (Hweight : weight p id = length (S.deps p r) + length (S.sides p r) + 1).
    { unfold weight; now rewrite Hsource. }
    assert (Hwidth : (N.of_nat (S.kw p + Nat.log2 (C p) + 1) <= unit p)%N).
    { assert (Hnat : S.kw p + Nat.log2 (C p) + 1 <=
        (Nat.log2 (C p) + 1) * (S.kw p + Nat.log2 (C p) + 4)) by nia.
      unfold unit; lia. }
    set (budget := (N.of_nat (weight p id) * unit p)%N).
    assert (Hu_budget : (unit p <= budget)%N).
    { unfold budget; rewrite <- (N.mul_1_l (unit p)) at 1.
      apply N.mul_le_mono_r; rewrite Hweight; lia. }
    assert (Hone_budget : (1 <= budget)%N) by lia.
    assert (Hchunk : (N.of_nat ((length (S.deps p r) + 1) *
      (S.kw p + Nat.log2 (C p) + 1)) <= budget)%N).
    { unfold budget; rewrite Nat2N.inj_mul; apply N.mul_le_mono; [rewrite Hweight; lia|].
      exact Hwidth. }
    assert (Heval_bound : (T_eval_row p r (ws_store s) <= k_eval * budget)%N).
    { unfold budget; rewrite N.mul_assoc, Hweight; exact Heval_cost. }
    assert (Htarget_bound : (S.T_target p r <= S.c_sys * budget)%N).
    { eapply N.le_trans; [exact Htarget|]; apply N.mul_le_mono_l; lia. }
    assert (Hrow_bound : (T_row_at s id <= 2 * (PTrieT.c_trie + 2) * budget)%N).
    { assert (Hbits : (N.of_nat (Pos.size_nat id + 1) <= 2 * budget)%N) by lia.
      eapply N.le_trans; [exact Hrow|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hbits|]; nia. }
    assert (Hclear_bound : (c_step * N.of_nat ((length (S.deps p r) + 1) *
      (S.kw p + Nat.log2 (C p) + 1)) <= c_step * budget)%N).
    { now apply N.mul_le_mono_l. }
    assert (Hsides_bound : (N.of_nat (length ss) <= budget)%N).
    { assert (Hlen : (N.of_nat (length ss) <= N.of_nat (weight p id))%N)
        by (rewrite Hweight; lia).
      unfold budget; clear -Hlen Hu; nia. }
    replace (16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) *
      N.of_nat (weight p id) * unit p)%N with
      (16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) * budget)%N
      by (unfold budget; ring).
    assert (Hfixed : (c_step <= c_step * budget)%N).
    { rewrite <- (N.mul_1_r c_step) at 1; now apply N.mul_le_mono_l. }
    assert (Hsum : (k_eval * budget + S.c_sys * budget +
      2 * (2 * (PTrieT.c_trie + 2) * budget) + c_step * budget + budget +
      c_step * budget <=
      16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) * budget)%N).
    { replace (k_eval * budget + S.c_sys * budget +
        2 * (2 * (PTrieT.c_trie + 2) * budget) + c_step * budget + budget +
        c_step * budget)%N with
        ((k_eval + S.c_sys + 4 * (PTrieT.c_trie + 2) + 2 * c_step + 1) * budget)%N
        by ring.
      apply N.mul_le_mono_r; lia. }
    clear -Hstep Heval_bound Htarget_bound Hrow_bound Hclear_bound Hsides_bound Hfixed Hsum;
      lia.
  Qed.

  (** Pop refunds queue potential and consumes exactly one weighted row allowance. *)
  Lemma T_pop_height : forall p pol rk h s pr id q1,
    structural p pol s -> Q.pop (ws_queue s) = Some (pr, id, q1) ->
    (Q.T_pop (ws_queue s) + height_phi p rk h (after_pop p s id q1) +
      k_credit * N.of_nat (weight p id) * unit p <=
      height_phi p rk h s + 2 * Q.c_pq * unit p)%N.
  Proof.
    intros p pol rk h s pr id q1 Hstruct Hpop.
    pose proof (T_queue_pop_bound p pol s Hstruct) as Hcost; rewrite Hpop in Hcost.
    pose proof (queue_credit_pop p pol s pr id q1 Hstruct Hpop) as Hcredit.
    rewrite !height_phi_debt, height_debt_after_pop, Hcredit, !Nat2N.inj_add.
    change (queue_phi p (after_pop p s id q1)) with
      (Q.phi (C p + 1) (S.kw p + Nat.log2 (C p) + 3) q1).
    clear -Hcost; nia.
  Qed.

  (** A continuing row spends less than the credit removed by its pop. *)
  Lemma T_step_height : forall p pol rk h s s1,
    S.wf p -> prio_ok p pol -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    invariant p pol s -> step p pol s = inl s1 ->
    (T_step p pol s + height_phi p rk h s1 + c_loopN <= height_phi p rk h s)%N.
  Proof.
    intros p pol rk h s s1 Hwf Hprio Hfree Hrank Hinv Hstep.
    unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q1]|] eqn:Hpop; [|discriminate].
    destruct (row_at s id) as [r|] eqn:Hrow; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    change (T_step p pol s + height_phi p rk h
      (fold_left (update_one p pol) ((S.target p r, a) :: ss) (after_pop p s id q1)) +
      c_loopN <= height_phi p rk h s)%N.
    assert (Hsource : source_row p id = Some r).
    { rewrite <- (proj1 (proj1 (proj2 (proj2 Hinv))) id); exact Hrow. }
    destruct (source_row_member p id r Hsource) as [Hid Hr].
    pose proof (after_pop_invariant p pol s pr id q1 Hinv Hpop) as Hafter.
    pose proof (eval_outputs_invariant p pol s r a ss Hwf Hinv Hr Heval) as Houts.
    assert (Hcoeff : (k_update <= k_credit)%N) by (unfold k_credit; nia).
    pose proof (output_cost_height p pol rk h ((S.target p r, a) :: ss)
      (after_pop p s id q1) Hwf Hprio Hfree Hafter Houts Hcoeff Hrank) as Houtput.
    pose proof (T_step_weighted p pol s pr id q1 r a ss Hwf Hinv Hpop Hsource Heval)
      as Htime.
    pose proof (T_pop_height p pol rk h s pr id q1 (proj1 Hinv) Hpop) as Hpop_time.
    pose proof Heval as Hsystem; change (S.eval p r (look s) = Some (a, ss)) in Hsystem.
    pose proof (S.sides_count p r (look s) a ss Hwf Hr Hsystem) as Hsides.
    assert (Hweight : weight p id = length (S.deps p r) + length (S.sides p r) + 1).
    { unfold weight; now rewrite Hsource. }
    set (budget := (N.of_nat (weight p id) * unit p)%N).
    assert (Houtput_bound : (k_update * N.of_nat (length ((S.target p r, a) :: ss)) *
      unit p <= k_update * budget)%N).
    { unfold budget; rewrite N.mul_assoc; apply N.mul_le_mono_r; apply N.mul_le_mono_l.
      cbn [length]; rewrite Hweight; lia. }
    destruct (time_unit_bounds p) as [Hu _].
    assert (Hu_budget : (unit p <= budget)%N).
    { unfold budget; rewrite <- (N.mul_1_l (unit p)) at 1.
      apply N.mul_le_mono_r; rewrite Hweight; lia. }
    assert (Hpayment :
      (16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) * budget +
        k_update * budget + 2 * Q.c_pq * unit p + c_loopN <= k_credit * budget)%N).
    { unfold k_credit; clear -Hu Hu_budget; nia. }
    replace (16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) *
      N.of_nat (weight p id) * unit p)%N with
      (16 * (k_eval + c_step + S.c_sys + PTrieT.c_trie + 1) * budget)%N in Htime
      by (unfold budget; ring).
    replace (k_credit * N.of_nat (weight p id) * unit p)%N with
      (k_credit * budget)%N in Hpop_time by (unfold budget; ring).
    clear -Houtput Houtput_bound Htime Hpop_time Hpayment; lia.
  Qed.

  (** Scaling each term scales its finite sum by the same factor. *)
  Lemma credit_sum_scale : forall A (f : A -> nat) xs k,
    fold_right Nat.add 0 (List.map (fun x => k * f x) xs) =
      k * fold_right Nat.add 0 (List.map f xs).
  Proof.
    intros A f xs; induction xs as [|x xs IH]; intros k; cbn [List.map fold_right].
    - nia.
    - rewrite IH; nia.
  Qed.

  (** Complete row numbering preserves the total declared occurrence weight. *)
  Lemma row_weight_sum : forall p,
    fold_right Nat.add 0 (List.map (weight p) (row_ids p)) = D p.
  Proof.
    intro p; unfold weight, D; apply incidence_numbered_rows.
  Qed.

  (** A live subset of the numbered rows never carries more than the total row weight. *)
  Lemma queue_credit_le_D : forall p s, queue_credit p s <= D p.
  Proof.
    intros p s; unfold queue_credit; rewrite <- row_weight_sum.
    apply incidence_sum_bound; intros id _; destruct (Q.prio (ws_queue s) id); lia.
  Qed.

  (** Remaining rank debt is bounded by height times the declared incidence budget. *)
  Lemma height_debt_bound : forall p rk h s, height_debt p rk h s <= h * DW p.
  Proof.
    intros p rk h s; unfold height_debt.
    eapply Nat.le_trans.
    - apply (incidence_sum_bound positive _
        (fun c => h * (weighted_degree p c + degree p c))).
      intros c _; nia.
    - rewrite credit_sum_scale; apply Nat.mul_le_mono_l; apply support_incidence_bound.
  Qed.

  (** W4 spends weighted rank credit for each callback in a widening-free run. *)
  Lemma W4_credit : forall p pol rk h s s1, S.wf p -> prio_ok p pol -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    reachable p pol s -> step p pol s = inl s1 ->
    (T_step p pol s + height_phi p rk h s1 + c_loopN <= height_phi p rk h s)%N.
  Proof.
    intros p pol rk h s s1 Hwf Hprio Hfree Hrank Hreachable Hstep.
    apply (T_step_height p pol rk h s s1 Hwf Hprio Hfree Hrank).
    - now apply reachable_invariant.
    - exact Hstep.
  Qed.
  (** Weighted source credit fits the public weighted incidence budget. *)
  Lemma W4_initial : forall p pol rk h, S.wf p -> prio_ok p pol -> widening_free pol ->
    (height_phi p rk h (prepare p pol) <=
      k_credit * N.of_nat (D p + h * DW p) * unit p + queue_phi p (prepare p pol))%N.
  Proof.
    intros p pol rk h Hwf Hprio Hfree; rewrite height_phi_debt.
    apply N.add_le_mono_r; apply N.mul_le_mono_r; apply N.mul_le_mono_l.
    pose proof (queue_credit_le_D p (prepare p pol)) as Hqueue.
    pose proof (height_debt_bound p rk h (prepare p pol)) as Hdebt; lia.
  Qed.

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
  (** Preparation initializes every encoded counter to zero. *)
  Lemma counter_prepare_zero : forall p pol c, counter (prepare p pol) c = 0%N.
  Proof.
    intros p pol c; unfold prepare; rewrite counter_enqueue.
    unfold counter; cbn [ws_counters].
    now rewrite PTrie.get_empty.
  Qed.

  (** A policy fold exposes its first contribution to the remaining suffix. *)
  Lemma policy_updates_cons : forall pol c cnt a b news,
    P.run_updates pol c cnt a (b :: news) =
      P.run_updates pol c (snd (P.update pol c cnt a b))
        (fst (P.update pol c cnt a b)) news.
  Proof.
    intros pol c cnt a b news; unfold P.run_updates; cbn [fold_left fst snd].
    destruct (P.update pol c cnt a b); reflexivity.
  Qed.

  (** Appending histories composes the corresponding policy folds. *)
  Lemma policy_updates_app : forall pol c cnt a news more,
    P.run_updates pol c cnt a (news ++ more) =
      P.run_updates pol c (snd (P.run_updates pol c cnt a news))
        (fst (P.run_updates pol c cnt a news)) more.
  Proof.
    intros pol c cnt a news more; unfold P.run_updates; rewrite fold_left_app.
    destruct (fold_left (fun ac new => P.update pol c (snd ac) (fst ac) new)
      news (a, cnt)); reflexivity.
  Qed.

  (** The selected history retains contributions at one encoded key in occurrence order. *)
  Definition code_news (c : positive) (outs : list (S.key * L.t)) : list L.t :=
    fold_right (fun xa news =>
      if Pos.eqb c (S.key_code (fst xa)) then snd xa :: news else news) nil outs.

  (** Selecting a key's history retains the invariant of every emitted value. *)
  Lemma code_news_inv : forall p c outs,
    Forall (fun xa => B.inv p (snd xa)) outs -> Forall (B.inv p) (code_news c outs).
  Proof.
    intros p c outs Houts; induction Houts as [|[x a] outs Ha Houts IH].
    - constructor.
    - cbn [code_news fold_right fst snd].
      destruct (Pos.eqb c (S.key_code x)); [constructor|]; assumption.
  Qed.

  (** Each output fold is the policy fold over the selected key's actual contributions. *)
  Lemma fold_code_news : forall p pol outs s c,
    (raw_value (fold_left (update_one p pol) outs s) c,
      counter (fold_left (update_one p pol) outs s) c) =
    P.run_updates pol c (counter s c) (raw_value s c) (code_news c outs).
  Proof.
    intros p pol outs; induction outs as [|[x a] outs IH]; intros s c.
    - reflexivity.
    - cbn [fold_left code_news fold_right fst snd]; rewrite IH.
      destruct (Pos.eqb c (S.key_code x)) eqn:Hcode.
      + apply Pos.eqb_eq in Hcode; subst c; rewrite policy_updates_cons.
        rewrite counter_update_same, raw_value_update_same; reflexivity.
      + apply Pos.eqb_neq in Hcode.
        rewrite counter_update_other, raw_value_update_other by exact Hcode; reflexivity.
  Qed.

  (** Stopping at a delay boundary retains the invariant of the evolving policy value. *)
  Lemma value_at_counter_inv : forall p pol c limit news cnt a,
    B.inv p a -> Forall (B.inv p) news ->
    B.inv p (value_at_counter P.update pol c limit cnt a news).
  Proof.
    intros p pol c limit news; induction news as [|b news IH]; intros cnt a Ha Hnews.
    - cbn [value_at_counter]; destruct (N.leb limit cnt); exact Ha.
    - inversion Hnews as [|b0 news0 Hb Htail]; subst.
      cbn [value_at_counter]; destruct (N.leb limit cnt); [exact Ha|].
      apply IH; [apply policy_update_inv; assumption|exact Htail].
  Qed.

  (** A key with no widening head keeps its counter through every policy history. *)
  Lemma policy_nonhead_counter : forall pol c news cnt a,
    trie_get c (heads pol) = None -> snd (P.run_updates pol c cnt a news) = cnt.
  Proof.
    intros pol c news; induction news as [|b news IH]; intros cnt a Hhead.
    - reflexivity.
    - rewrite policy_updates_cons, IH by exact Hhead.
      rewrite P.update_spec; destruct (L.leb b a); [reflexivity|].
      now rewrite Hhead.
  Qed.

  (** A reachable callback contributes only invariant values to every encoded history. *)
  Lemma step_code_news : forall p pol s s1, S.wf p -> reachable p pol s ->
    step p pol s = inl s1 -> exists outs,
    Forall (fun xa => B.inv p (snd xa)) outs /\
    forall c, (raw_value s1 c, counter s1 c) =
      P.run_updates pol c (counter s c) (raw_value s c) (code_news c outs).
  Proof.
    intros p pol s s1 Hwf Hreach Hstep.
    pose proof (F9_reachable_prepared p pol s Hreach) as Hprepared.
    rewrite F7_indexed in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop; [|discriminate].
    rewrite (proj1 (proj1 Hprepared) id) in Hstep.
    destruct (source_row p id) as [r|] eqn:Hrow; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|discriminate].
    injection Hstep as <-.
    assert (Hlook : forall x, B.inv p (look s x)).
    { exact (F9_reachable_inv p pol s Hwf Hreach). }
    pose proof Heval as Hsystem; rewrite F3_eval in Hsystem.
    destruct (B.inv_rows p r (look s) a ss Hwf
      (proj2 (source_row_member p id r Hrow)) Hlook Hsystem) as [Ha Hss].
    exists ((S.target p r, a) :: ss); split; [now constructor|].
    intro c; exact (fold_code_news p pol ((S.target p r, a) :: ss) (after_pop p s id q) c).
  Qed.

  (** A finite path extends each existing per-code policy history. *)
  Lemma path_code_history : forall p pol s xs last, S.wf p -> reachable p pol s ->
    wl_path (step p pol) s xs last ->
    (forall c, exists news, Forall (B.inv p) news /\
      (raw_value s c, counter s c) = P.run_updates pol c 0%N L.bot news) ->
    forall c, exists news, Forall (B.inv p) news /\
      (raw_value last c, counter last c) = P.run_updates pol c 0%N L.bot news.
  Proof.
    intros p pol s xs last Hwf Hreach Hpath; revert Hreach.
    induction Hpath as [s|s s1 xs last Hstep Hpath IH]; intros Hreach Hhistory.
    - exact Hhistory.
    - apply (IH (reachable_step p pol s s1 Hreach Hstep)).
      destruct (step_code_news p pol s s1 Hwf Hreach Hstep) as [outs [Houts Hnext]].
      intro c; destruct (Hhistory c) as [news [Hnews Hpair]].
      exists (news ++ code_news c outs); split.
      + apply Forall_app; split; [exact Hnews|apply code_news_inv; exact Houts].
      + rewrite Hnext, policy_updates_app.
        pose proof (f_equal fst Hpair) as Hvalue.
        pose proof (f_equal snd Hpair) as Hcounter.
        cbn [fst snd] in Hvalue, Hcounter; now rewrite Hvalue, Hcounter.
  Qed.

  (** Every reachable encoded value and counter come from an invariant contribution history. *)
  Lemma reachable_code_history : forall p pol s, S.wf p -> reachable p pol s ->
    forall c, exists news, Forall (B.inv p) news /\
      (raw_value s c, counter s c) = P.run_updates pol c 0%N L.bot news.
  Proof.
    intros p pol s Hwf [xs Hpath].
    apply (path_code_history p pol (prepare p pol) xs s Hwf).
    - exists nil; constructor.
    - exact Hpath.
    - intro c; exists nil; split; [constructor|].
      rewrite raw_value_prepare, counter_prepare_zero; reflexivity.
  Qed.

  (** Every reachable head counter is bounded by its delay and invariant widening rank. *)
  Lemma reachable_head_counter : forall p pol s c cfg, S.wf p -> reachable p pol s ->
    trie_get c (heads pol) = Some cfg ->
    N.to_nat (counter s c) <= N.to_nat (delay cfg) + B.wmax p (wp pol) + 1.
  Proof.
    intros p pol s c cfg Hwf Hreach Hhead.
    destruct (reachable_code_history p pol s Hwf Hreach c) as [news [Hnews Hpair]].
    pose proof (P.head_updates_le pol c cfg news L.bot Hhead) as Hsteps.
    assert (Hvalue : B.inv p (P.value_after_delay pol c cfg L.bot news)).
    { unfold P.value_after_delay; apply value_at_counter_inv; [apply B.inv_bot|exact Hnews]. }
    pose proof (B.wrank_le p (wp pol) (P.value_after_delay pol c cfg L.bot news) Hvalue)
      as Hrank.
    pose proof (f_equal snd Hpair) as Hcounter; cbn [snd] in Hcounter.
    unfold P.strict_count in Hsteps; rewrite Hcounter; lia.
  Qed.

  (** Every reachable non-head counter remains zero. *)
  Lemma reachable_nonhead_counter : forall p pol s c, S.wf p -> reachable p pol s ->
    trie_get c (heads pol) = None -> counter s c = 0%N.
  Proof.
    intros p pol s c Hwf Hreach Hhead.
    destruct (reachable_code_history p pol s Hwf Hreach c) as [news [_ Hpair]].
    pose proof (f_equal snd Hpair) as Hcounter; cbn [snd] in Hcounter.
    rewrite Hcounter; apply policy_nonhead_counter; exact Hhead.
  Qed.

  (** Pointwise head allowances bound the sum of finite head-event contributions. *)
  Lemma head_sum_bound : forall A (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) ->
    fold_right Nat.add 0 (List.map f xs) <= fold_right Nat.add 0 (List.map g xs).
  Proof.
    intros A f g xs; induction xs as [|x xs IH]; intros Hbound.
    - reflexivity.
    - cbn [List.map fold_right].
      pose proof (Hbound x (or_introl eq_refl)) as Hhead.
      assert (Htail : forall y, In y xs -> f y <= g y).
      { intros y Hy; apply Hbound; now right. }
      specialize (IH Htail); lia.
  Qed.

  (** W6 bounds every finite prefix's strict head events by the advertised round count. *)
  Lemma W6_rounds : forall p pol xs last, S.wf p -> prio_ok p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    head_events pol (prepare p pol) last + 1 <= rounds p pol /\
    (forall c, In c (key_support p) ->
      N.to_nat (counter last c) <= head_allowance p pol c).
  Proof.
    intros p pol xs last Hwf Hprio Hpath.
    assert (Hreach : reachable p pol last) by (exists xs; exact Hpath).
    split.
    - unfold head_events, rounds.
      assert (Hsum :
        fold_right Nat.add 0 (List.map
          (fun ch => N.to_nat (counter last (fst ch) - counter (prepare p pol) (fst ch)))
          (PTrieCode.elements (heads pol))) <=
        fold_right Nat.add 0 (List.map
          (fun ch => N.to_nat (delay (snd ch)) + B.wmax p (wp pol) + 2)
          (PTrieCode.elements (heads pol)))).
      { apply head_sum_bound; intros [c cfg] Hin; cbn [fst snd].
        apply PTrie.elements_spec in Hin.
        rewrite counter_prepare_zero, N.sub_0_r.
        pose proof (reachable_head_counter p pol last c cfg Hwf Hreach Hin); lia. }
      lia.
    - intros c Hsupport; unfold head_allowance.
      destruct (trie_get c (heads pol)) as [cfg|] eqn:Hhead.
      + pose proof (reachable_head_counter p pol last c cfg Hwf Hreach Hhead); lia.
      + rewrite (reachable_nonhead_counter p pol last c Hwf Hreach Hhead); reflexivity.
  Qed.
  (** W7 charges arbitrary finite prefixes by partitioning at strict head events. *)
  Lemma W7_trace : forall p pol xs last, fits p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    (trace_cost p pol xs + c_loopN * N.of_nat (length xs) + queue_phi p last <=
      k_loop * work p pol + queue_phi p (prepare p pol))%N.
  Proof. Admitted. (* STUB *)
  (** Every continuing callback preserves the monotonicity of every encoded counter. *)
  Lemma counter_step_mono : forall p pol s s1 c, step p pol s = inl s1 ->
    (counter s c <= counter s1 c)%N.
  Proof.
    intros p pol s s1 c Hstep; rewrite F7_indexed in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|]; [|discriminate].
    destruct (row_at s id) as [r|]; [|discriminate].
    destruct (eval_row p r (ws_store s)) as [[a ss]|]; [|discriminate].
    injection Hstep as <-.
    pose proof (counter_fold_mono p pol ((S.target p r, a) :: ss) (after_pop p s id q) c)
      as Hmono.
    now rewrite counter_after_pop in Hmono.
  Qed.

  (** Encoded counters are monotone along every continuing path. *)
  Lemma counter_path_mono : forall p pol s xs last c,
    wl_path (step p pol) s xs last -> (counter s c <= counter last c)%N.
  Proof.
    intros p pol s xs last c Hpath; induction Hpath as [s|s s1 xs last Hstep Hpath IH].
    - lia.
    - pose proof (counter_step_mono p pol s s1 c Hstep); lia.
  Qed.

  (** A listed head contributes at most the total event count. *)
  Lemma head_sum_member : forall A (f : A -> nat) xs x, In x xs ->
    f x <= fold_right Nat.add 0 (List.map f xs).
  Proof.
    intros A f xs; induction xs as [|y xs IH]; intros x Hin.
    - contradiction.
    - cbn [List.map fold_right]; destruct Hin as [<-|Hin].
      + lia.
      + specialize (IH x Hin); lia.
  Qed.

  (** Zero head events force unchanged head counters when counters are monotone. *)
  Lemma head_events_zero_stable : forall pol s t,
    (forall c, (counter s c <= counter t c)%N) -> head_events pol s t = 0 ->
    heads_unchanged pol s t.
  Proof.
    intros pol s t Hmono Hzero c cfg Hhead.
    assert (Hin : In (c, cfg) (PTrieCode.elements (heads pol))).
    { now apply PTrie.elements_spec. }
    pose proof (head_sum_member (positive * head_cfg)
      (fun ch => N.to_nat (counter t (fst ch) - counter s (fst ch)))
      (PTrieCode.elements (heads pol)) (c, cfg) Hin) as Hpart.
    change (N.to_nat (counter t c - counter s c) <= head_events pol s t) in Hpart.
    rewrite Hzero in Hpart.
    assert (Hzero_difference : (counter t c - counter s c = 0)%N).
    { apply N2Nat.inj; cbn [N.to_nat]; lia. }
    specialize (Hmono c); lia.
  Qed.

  (** Monotone head counters make event counts additive across adjacent paths. *)
  Lemma head_events_add : forall pol s t u,
    (forall c, (counter s c <= counter t c)%N) ->
    (forall c, (counter t c <= counter u c)%N) ->
    head_events pol s u = head_events pol s t + head_events pol t u.
  Proof.
    intros pol s t u Hst Htu; unfold head_events.
    induction (PTrieCode.elements (heads pol)) as [|[c cfg] hs IH].
    - reflexivity.
    - cbn [List.map fold_right fst].
      assert (Hdifference : (counter u c - counter s c =
        (counter t c - counter s c) + (counter u c - counter t c))%N).
      { pose proof (Hst c); pose proof (Htu c); lia. }
      rewrite Hdifference, N2Nat.inj_add, IH; lia.
  Qed.

  (** A stable first callback and stable suffix form one stable segment. *)
  Lemma stable_segment_cons : forall p pol s s1 xs,
    step p pol s = inl s1 -> heads_unchanged pol s s1 -> stable_segment p pol xs ->
    stable_segment p pol (s :: xs).
  Proof.
    intros p pol s s1 xs Hstep Hfirst Htail t t1 Hin Hnext.
    destruct Hin as [<-|Hin].
    - rewrite Hstep in Hnext; injection Hnext as <-; exact Hfirst.
    - exact (Htail t t1 Hin Hnext).
  Qed.

  (** Every nonstable path has a first positive-event callback after a stable prefix. *)
  Lemma path_first_event : forall p pol s xs last, wl_path (step p pol) s xs last ->
    stable_segment p pol xs \/
      exists prefix before after suffix, xs = prefix ++ before :: suffix /\
        wl_path (step p pol) s prefix before /\ step p pol before = inl after /\
        wl_path (step p pol) after suffix last /\ stable_segment p pol prefix /\
        0 < head_events pol before after.
  Proof.
    intros p pol s xs last Hpath; induction Hpath as [s|s s1 xs last Hstep Hpath IH].
    - left; intros t t1 Hin; contradiction.
    - destruct (Nat.eq_dec (head_events pol s s1) 0) as [Hzero|Hpositive].
      + assert (Hfirst : heads_unchanged pol s s1).
        { apply head_events_zero_stable; [intro c; eapply counter_step_mono; exact Hstep|].
          exact Hzero. }
        destruct IH as [Htail|[prefix [before [after [suffix
          [Hxs [Hprefix [Hevent [Hsuffix [Hstable Hcount]]]]]]]]]].
        * left; eapply stable_segment_cons; eassumption.
        * right; exists (s :: prefix), before, after, suffix.
          split; [now rewrite Hxs|].
          split; [econstructor; eassumption|].
          split; [exact Hevent|].
          split; [exact Hsuffix|].
          split; [eapply stable_segment_cons; eassumption|exact Hcount].
      + right; exists nil, s, s1, xs.
        split; [reflexivity|].
        split; [constructor|].
        split; [exact Hstep|].
        split; [exact Hpath|].
        split; [intros t t1 Hin; contradiction|lia].
  Qed.

  (** At most one row sweep separates successive positive head-event callbacks. *)
  Lemma path_visit_bound_fuel : forall p pol fuel s xs last,
    length xs <= fuel -> fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last ->
    length xs <= C p * (head_events pol s last + 1) + head_events pol s last.
  Proof.
    intros p pol fuel; induction fuel as [|fuel IH];
      intros s xs last Hlength Hfits Hreach Hpath.
    - lia.
    - destruct (path_first_event p pol s xs last Hpath) as [Hstable|
        [prefix [before [after [suffix [Hxs [Hprefix [Hevent [Hsuffix [Hstable Hpositive]]]]]]]]]].
      + pose proof (stable_length_le p pol s xs last Hfits Hreach Hpath Hstable); nia.
      + pose proof (reachable_path p pol s prefix before Hreach Hprefix) as Hbefore.
        pose proof (reachable_step p pol before after Hbefore Hevent) as Hafter.
        assert (Hsuffix_length : length suffix <= fuel).
        { rewrite Hxs, length_app in Hlength; cbn [length] in Hlength; lia. }
        pose proof (IH after suffix last Hsuffix_length Hfits Hafter Hsuffix) as Htail_bound.
        pose proof (stable_length_le p pol s prefix before Hfits Hreach Hprefix Hstable)
          as Hprefix_bound.
        assert (Hrest : forall c, (counter before c <= counter last c)%N).
        { intro c; pose proof (counter_step_mono p pol before after c Hevent).
          pose proof (counter_path_mono p pol after suffix last c Hsuffix); lia. }
        pose proof (head_events_add pol s before last
          (fun c => counter_path_mono p pol s prefix before c Hprefix) Hrest) as Hadd1.
        pose proof (head_events_add pol before after last
          (fun c => counter_step_mono p pol before after c Hevent)
          (fun c => counter_path_mono p pol after suffix last c Hsuffix)) as Hadd2.
        rewrite Hxs, length_app; cbn [length]; nia.
  Qed.

  (** The finite visit bound is independent of the representation size of abstract values. *)
  Lemma path_visit_bound : forall p pol s xs last, fits p pol -> reachable p pol s ->
    wl_path (step p pol) s xs last ->
    length xs <= C p * (head_events pol s last + 1) + head_events pol s last.
  Proof.
    intros p pol s xs last Hfits Hreach Hpath.
    apply (path_visit_bound_fuel p pol (length xs) s xs last); assumption || lia.
  Qed.

  (** Every source row contributes at least one declared occurrence. *)
  Lemma visits_C_le_D : forall p, C p <= D p.
  Proof.
    intro p; unfold C, D; induction (S.rows p) as [|r rs IH];
      cbn [List.map fold_right length]; lia.
  Qed.

  (** The visit count supplies fuel without charging abstract value sizes to fuel construction. *)
  Lemma W7_visits : forall p pol xs last, fits p pol ->
    wl_path (step p pol) (prepare p pol) xs last ->
    (N.of_nat (length xs) < k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Proof.
    intros p pol xs last Hfits Hpath.
    assert (Hinitial : reachable p pol (prepare p pol)) by (exists nil; constructor).
    pose proof (path_visit_bound p pol (prepare p pol) xs last Hfits Hinitial Hpath) as Hvisits.
    destruct Hfits as [Hwf [Hcuts Hprio]].
    assert (Hfits : fits p pol) by now repeat split.
    pose proof (proj1 (W6_rounds p pol xs last Hwf Hprio Hpath)) as Hrounds.
    pose proof (visits_C_le_D p) as Hoccurrences.
    assert (Hnumeric : length xs < (C p + D p) * rounds p pol + 1).
    { destruct (Nat.eq_dec (C p) 0) as [Hempty|Hnonempty]; [|nia].
      assert (Hids : row_ids p = nil).
      { apply length_zero_iff_nil; now rewrite row_ids_length. }
      pose proof (popped_ids_supported p pol (prepare p pol) xs last Hfits Hinitial Hpath)
        as Hsupport.
      assert (Hpopped : popped_ids xs = nil).
      { destruct (popped_ids xs) as [|id ids]; [reflexivity|].
        exfalso; pose proof (Hsupport id (or_introl eq_refl)) as Hin.
        rewrite Hids in Hin; contradiction. }
      pose proof (popped_ids_length p pol (prepare p pol) xs last Hpath) as Hlength.
      rewrite Hpopped in Hlength; cbn [length] in Hlength; lia. }
    unfold k_fuel; rewrite N.mul_1_l; lia.
  Qed.

  (** The advertised work contains preparation and at least one complete row round. *)
  Lemma driver_work_bounds : forall p pol,
    (N.of_nat (prep p) <= work p pol)%N /\
    (N.of_nat (C p + D p) * unit p <= work p pol)%N /\
    (N.of_nat (C p) * unit p <= work p pol)%N /\
    (N.of_nat ((C p + D p) * rounds p pol) <= work p pol)%N.
  Proof.
    intros p pol.
    assert (Hrounds : 1 <= rounds p pol) by (unfold rounds; lia).
    assert (Hfactor_nat : C p + D p <= (C p + D p) * rounds p pol) by nia.
    assert (Hfactor : (N.of_nat (C p + D p) <=
      N.of_nat ((C p + D p) * rounds p pol))%N) by lia.
    assert (Hrow : (N.of_nat ((C p + D p) * rounds p pol) * unit p <= work p pol)%N).
    { unfold work; lia. }
    assert (Hqueue : (N.of_nat (C p + D p) * unit p <= work p pol)%N).
    { eapply N.le_trans; [apply N.mul_le_mono_r; exact Hfactor|exact Hrow]. }
    split; [unfold work; lia|]; split; [exact Hqueue|]; split.
    - eapply N.le_trans; [|exact Hqueue]; apply N.mul_le_mono_r; lia.
    - pose proof (proj1 (time_unit_bounds p)) as Hunit.
      eapply N.le_trans; [|exact Hrow].
      clear -Hunit; nia.
  Qed.

  (** The global loop envelope has the same single work-and-bit-width bound. *)
  Lemma driver_global_absorb : forall b bits,
    (k_prepare * (2 * b + 1) + k_loop * ((k_prepare + 1) * b + bits + 1) + 2 <=
      c_wl * (b + bits + 1))%N.
  Proof.
    intros b bits.
    assert (Hwork : (2 * k_prepare + k_loop * (k_prepare + 1) <= c_wl)%N).
    { unfold c_wl; nia. }
    assert (Hbits : (k_loop <= c_wl)%N) by (unfold c_wl; nia).
    assert (Hone : (k_prepare + k_loop + 2 <= c_wl)%N) by (unfold c_wl; nia).
    replace (k_prepare * (2 * b + 1) + k_loop * ((k_prepare + 1) * b + bits + 1) + 2)%N
      with ((2 * k_prepare + k_loop * (k_prepare + 1)) * b +
        k_loop * bits + (k_prepare + k_loop + 2))%N by ring.
    replace (c_wl * (b + bits + 1))%N with (c_wl * b + c_wl * bits + c_wl)%N by ring.
    repeat apply N.add_le_mono; try assumption; apply N.mul_le_mono_r; assumption.
  Qed.

  (** Bit width never exceeds the represented positive value. *)
  Lemma positive_bits_value : forall n, Pos.size_nat n <= Pos.to_nat n.
  Proof.
    intro n; induction n as [n IH|n IH|].
    - rewrite Pos2Nat.inj_xI; cbn [Pos.size_nat]; lia.
    - rewrite Pos2Nat.inj_xO; cbn [Pos.size_nat].
      pose proof (Pos2Nat.is_pos n); lia.
    - reflexivity.
  Qed.

  Lemma N_bits_value : forall n, (N.of_nat (N.size_nat n) <= n)%N.
  Proof.
    intros [|n]; [reflexivity|]; cbn [N.size_nat].
    pose proof (positive_bits_value n); lia.
  Qed.

  (** Constructed fuel has bit width bounded by the already-advertised row work. *)
  Lemma fuel_for_bits_le : forall p pol,
    (N.of_nat (N.size_nat (fuel_for p pol)) <= work p pol + 1)%N.
  Proof.
    intros p pol; eapply N.le_trans; [apply N_bits_value|].
    pose proof (proj2 (proj2 (proj2 (driver_work_bounds p pol)))) as Hwork.
    unfold fuel_for, k_fuel; rewrite N.mul_1_l, Nat2N.inj_add.
    change (N.of_nat 1) with 1%N; lia.
  Qed.

  (** * Driver outcomes and global bounds *)

  (** A solved callback exposes its exact store and an empty live queue. *)
  Lemma step_solved_queue : forall p pol s m,
    step p pol s = inr (Solved m) -> Q.pop (ws_queue s) = None /\ m = ws_store s.
  Proof.
    intros p pol s m Hstep; unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop.
    - destruct (row_at s id) as [r|]; [|discriminate].
      destruct (eval_row p r (ws_store s)) as [[a ss]|]; discriminate.
    - injection Hstep as <-; now split.
  Qed.

  (** A legal reachable state can stop only by solving its empty queue. *)
  Lemma step_stop_solved : forall p pol s result,
    S.wf p -> invariant p pol s -> step p pol s = inr result ->
    result = Solved (ws_store s) /\ Q.pop (ws_queue s) = None.
  Proof.
    intros p pol s result Hwf [Hstruct [Hvalues Hprepared]] Hstep.
    pose proof Hstruct as [Hqueue [Hfits [Hpending [Hcount Hsupport]]]].
    unfold step in Hstep.
    destruct (Q.pop (ws_queue s)) as [[[pr id] q]|] eqn:Hpop.
    - pose proof (proj1 (Q.pop_min _ _ _ _ Hqueue Hpop)) as Hlive.
      destruct (Hsupport pr id Hlive) as [Hin [r [Hsource Hrank]]].
      rewrite (proj1 (proj1 Hprepared)), Hsource in Hstep.
      destruct (eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [discriminate|].
      exfalso; eapply S.eval_total; [exact Hwf|exact (proj2 (source_row_member p id r Hsource))|].
      exact Heval.
    - injection Hstep as <-; now split.
  Qed.

  (** Empty programs prepare the actual empty queue. *)
  Lemma prepare_empty_queue : forall p pol, C p = 0 -> ws_queue (prepare p pol) = Q.empty.
  Proof.
    intros p pol Hempty.
    assert (Hrows : S.rows p = []) by (apply length_zero_iff_nil; exact Hempty).
    unfold prepare, row_ids; rewrite Hrows; reflexivity.
  Qed.

  Lemma prepare_empty_step : forall p pol, C p = 0 ->
    step p pol (prepare p pol) = inr (Solved (ws_store (prepare p pol))).
  Proof.
    intros p pol Hempty; unfold step; rewrite prepare_empty_queue by exact Hempty.
    rewrite (proj2 (Q.pop_none Q.empty Q.wf_empty) Q.prio_empty); reflexivity.
  Qed.

  (** An empty program has no continuing path and retains its initial state. *)
  Lemma reachable_empty : forall p pol s, C p = 0 -> reachable p pol s -> s = prepare p pol.
  Proof.
    intros p pol s Hempty [xs Hpath]; inversion Hpath; subst; [reflexivity|].
    pose proof (prepare_empty_step p pol Hempty); congruence.
  Qed.

  (** Solved public outcomes expose a reachable final callback. *)
  Lemma run_solved_path : forall p pol fuel m, run p pol fuel = Solved m ->
    exists s, reachable p pol s /\ step p pol s = inr (Solved m).
  Proof.
    intros p pol fuel m Hrun; unfold run in Hrun; rewrite loopN_fuel in Hrun.
    destruct (loop_fuel (step p pol) (N.to_nat fuel) (prepare p pol))
      as [s|result] eqn:Hloop; [discriminate|].
    subst result.
    destruct (loop_fuel_stop_path (step p pol) (N.to_nat fuel) (prepare p pol)
      (Solved m) Hloop) as [xs [last [Hpath [Hstop Hlength]]]].
    exists last; split; [now exists xs|exact Hstop].
  Qed.

  (** The stopping branch performs only a pop and constant field access. *)
  Lemma T_step_empty : forall p pol s, Q.pop (ws_queue s) = None ->
    (T_step p pol s = Q.T_pop (ws_queue s) + 3)%N.
  Proof.
    intros p pol s Hempty; unfold T_step; rewrite Hempty; time_simpl; time_cbn; ring.
  Qed.

  (** Width zero gives an input-independent cost for the actual empty queue. *)
  Lemma T_pop_empty_le : (Q.T_pop Q.empty <= Q.c_pq)%N.
  Proof.
    assert (Hpop : Q.pop Q.empty = None).
    { apply (proj2 (Q.pop_none Q.empty Q.wf_empty)); apply Q.prio_empty. }
    pose proof (Q.T_pop_amort 1 0 Q.empty Q.wf_empty (Q.fits_empty 0)
      ltac:(rewrite Q.pending_empty; lia)) as Hcost.
    rewrite Hpop, Q.phi_empty in Hcost.
    change (Q.T_pop Q.empty + 0 <= Q.c_pq * 1 + 0)%N in Hcost; lia.
  Qed.

  (** The final callback has a bound independent of the public loop constant. *)
  Lemma T_stop_budget : forall p pol s result, S.wf p -> prio_ok p pol ->
    reachable p pol s -> step p pol s = inr result ->
    (T_step p pol s + c_loopN <=
      (2 * Q.c_pq + c_loopN + 3) * (N.of_nat (C p) * unit p + 1) + queue_phi p s)%N.
  Proof.
    intros p pol s result Hwf Hprio Hreachable Hstop.
    pose proof (reachable_invariant p pol s Hwf Hprio Hreachable) as Hinv.
    destruct (step_stop_solved p pol s result Hwf Hinv Hstop) as [Hresult Hempty].
    rewrite (T_step_empty p pol s Hempty).
    destruct (Nat.eq_dec (C p) 0) as [Hzero|Hpositive].
    - rewrite (reachable_empty p pol s Hzero Hreachable),
        (prepare_empty_queue p pol Hzero).
      pose proof T_pop_empty_le; lia.
    - pose proof (T_queue_pop_bound p pol s (proj1 Hinv)) as Hpop.
      rewrite Hempty in Hpop.
      assert (Hcount : (1 <= N.of_nat (C p))%N) by lia.
      nia.
  Qed.

  (** The public wrapper adds only constant work to preparation and its binary loop. *)
  Lemma T_run_additive : forall p pol fuel,
    (T_run p pol fuel <= T_prepare p pol +
      T_loopN (step p pol) (T_step p pol) fuel (prepare p pol) + 2)%N.
  Proof.
    intros p pol fuel; unfold T_run.
    change (fun st => T_step p pol st) with (T_step p pol).
    destruct (loopN (step p pol) fuel (prepare p pol)); time_simpl; time_cbn; lia.
  Qed.

  (** Any reachable-state credit can pay the binary driver with a separate stop reserve. *)
  Lemma T_run_credit : forall p pol fuel (Phi : state -> N) stop,
    (forall s s1, reachable p pol s -> step p pol s = inl s1 ->
      (T_step p pol s + c_loopN + Phi s1 <= Phi s)%N) ->
    (forall s result, reachable p pol s -> step p pol s = inr result ->
      (T_step p pol s + c_loopN <= Phi s + stop)%N) ->
    (T_run p pol fuel <= T_prepare p pol + Phi (prepare p pol) + stop +
      c_loopN * N.of_nat (N.size_nat fuel + 1) + 2)%N.
  Proof.
    intros p pol fuel Phi stop Hcontinue Hstop.
    pose proof (T_loopN_amort state (outcome (kmap S.key L.t))
      (step p pol) (T_step p pol) (reachable p pol)
      (fun s => (Phi s + stop)%N) (fun _ => 0%N) fuel (prepare p pol)) as Hloop.
    assert (Hgo : forall s s1, reachable p pol s -> step p pol s = inl s1 ->
      reachable p pol s1 /\
      (T_step p pol s + c_loopN + (Phi s1 + stop) <= Phi s + stop)%N).
    { intros s s1 Hreachable Hstep; split.
      - eapply reachable_step; eassumption.
      - pose proof (Hcontinue s s1 Hreachable Hstep); lia. }
    assert (Hdone : forall s result, reachable p pol s -> step p pol s = inr result ->
      (T_step p pol s + c_loopN + 0 <= Phi s + stop)%N).
    { intros s result Hreachable Hstep; pose proof (Hstop s result Hreachable Hstep); lia. }
    assert (Hinitial : reachable p pol (prepare p pol)) by (exists []; constructor).
    specialize (Hloop Hgo Hdone Hinitial).
    destruct (loopN (step p pol) fuel (prepare p pol)); cbn beta iota in Hloop;
      pose proof (T_run_additive p pol fuel); lia.
  Qed.

  (** Stopping callbacks must solve and must fit the final driver budget. *)
  Lemma W7_stop : forall p pol s result, S.wf p -> prio_ok p pol -> reachable p pol s ->
    step p pol s = inr result ->
    (exists m, result = Solved m) /\
    (T_step p pol s <= k_loop * (N.of_nat (C p) * unit p + 1) + queue_phi p s)%N.
  Proof.
    intros p pol s result Hwf Hprio Hreachable Hstop.
    pose proof (reachable_invariant p pol s Hwf Hprio Hreachable) as Hinv.
    destruct (step_stop_solved p pol s result Hwf Hinv Hstop) as [Hresult Hempty].
    split; [now exists (ws_store s)|].
    pose proof (T_stop_budget p pol s result Hwf Hprio Hreachable Hstop) as Hcost.
    assert (Hconstant : (2 * Q.c_pq + c_loopN + 3 <= k_loop)%N).
    { unfold k_loop; nia. }
    nia.
  Qed.
  (** Binary fuel charges the loop from finite-prefix accounting and the final callback. *)
  Lemma W7_loop : forall p pol fuel, fits p pol ->
    (T_loopN (step p pol) (T_step p pol) fuel (prepare p pol) <= k_loop *
      (work p pol + queue_phi p (prepare p pol) +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Fuel is chosen from the row-visit budget and includes the final empty pop. *)
  Lemma W7_fuel : forall p pol,
    (fuel_for p pol = k_fuel * N.of_nat ((C p + D p) * rounds p pol + 1))%N.
  Proof. reflexivity. Qed.
  (** W7 connects the derived solver time to preparation and the derived binary-loop time. *)
  Lemma W7_run : forall p pol fuel,
    (T_run p pol fuel <= k_loop * (T_prepare p pol +
      T_loopN (step p pol) (T_step p pol) fuel (prepare p pol) + 1))%N.
  Proof.
    intros p pol fuel; pose proof (T_run_additive p pol fuel) as Hcost.
    assert (Hconstant : (2 <= k_loop)%N) by (unfold k_loop; nia).
    nia.
  Qed.
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
  Proof.
    intros p pol fuel m [Hwf [Hcuts Hprio]] Hrun.
    destruct (run_solved_path p pol fuel m Hrun) as [s [Hreachable Hstop]].
    destruct (step_solved_queue p pol s m Hstop) as [Hempty ->].
    pose proof (F9_reachable_prepared p pol s Hreachable) as Hprepared.
    pose proof (proj1 (Q.pop_none (ws_queue s)
      (proj1 (proj2 (proj2 Hprepared)))) Hempty) as Hnone.
    intros r Hr; apply In_nth_error in Hr as [n Hnth].
    eapply (F9_accepted p pol s Hwf Hreachable (Pos.of_succ_nat n) r).
    - now rewrite F1_numbering.
    - apply Hnone.
  Qed.
  (** Solved candidates satisfy the client value budget. *)
  Lemma run_inv : forall p pol fuel m, S.wf p -> run p pol fuel = Solved m ->
    forall x, B.inv p (look_or S.key_code L.bot m x).
  Proof.
    intros p pol fuel m Hwf Hrun x.
    destruct (run_solved_path p pol fuel m Hrun) as [s [Hreachable Hstop]].
    destruct (step_solved_queue p pol s m Hstop) as [Hempty ->].
    eapply F9_reachable_inv; eassumption.
  Qed.
  (** Height credit always includes the queue's own amortized potential. *)
  Lemma driver_height_queue : forall p rk h s,
    (queue_phi p s <= height_phi p rk h s)%N.
  Proof. intros; unfold height_phi; lia. Qed.

  (** The widening fallback also retains the complete queue potential. *)
  Lemma driver_all_head_queue : forall p pol s,
    (queue_phi p s <= all_head_phi p pol s)%N.
  Proof. intros; unfold all_head_phi; lia. Qed.

  (** One public constant absorbs preparation, state credit and binary-driver overhead. *)
  Lemma driver_credit_absorb : forall a b bits,
    (k_prepare * (a + b + 1) + 2 * k_credit * b + 2 * k_prepare * b +
      k_loop * (b + 1) + c_loopN + c_loopN * (bits + 1) + 2 <=
      c_wl * (a + b + bits + 1))%N.
  Proof.
    intros a b bits.
    assert (Ha : (k_prepare <= c_wl)%N) by (unfold c_wl; nia).
    assert (Hb : (3 * k_prepare + 2 * k_credit + k_loop <= c_wl)%N).
    { unfold c_wl; nia. }
    assert (Hbits : (c_loopN <= c_wl)%N) by (unfold c_wl; nia).
    assert (Hone : (k_prepare + k_loop + 2 * c_loopN + 2 <= c_wl)%N).
    { unfold c_wl; nia. }
    replace (k_prepare * (a + b + 1) + 2 * k_credit * b + 2 * k_prepare * b +
      k_loop * (b + 1) + c_loopN + c_loopN * (bits + 1) + 2)%N with
      (k_prepare * a + (3 * k_prepare + 2 * k_credit + k_loop) * b +
        c_loopN * bits + (k_prepare + k_loop + 2 * c_loopN + 2))%N by ring.
    replace (c_wl * (a + b + bits + 1))%N with
      (c_wl * a + c_wl * b + c_wl * bits + c_wl)%N by ring.
    repeat apply N.add_le_mono; try assumption; apply N.mul_le_mono_r; assumption.
  Qed.

  (** A bounded initial credit gives the solver's public cost envelope. *)
  Lemma T_run_budget : forall p pol fuel (Phi : state -> N) budget,
    S.wf p -> prio_ok p pol -> (N.of_nat (C p) * unit p <= budget)%N ->
    (Phi (prepare p pol) <= 2 * k_credit * budget + 2 * k_prepare * budget)%N ->
    (forall s, (queue_phi p s <= Phi s)%N) ->
    (forall s s1, reachable p pol s -> step p pol s = inl s1 ->
      (T_step p pol s + c_loopN + Phi s1 <= Phi s)%N) ->
    (T_run p pol fuel <= c_wl *
      (N.of_nat (prep p) + budget + N.of_nat (N.size_nat fuel) + 1))%N.
  Proof.
    intros p pol fuel Phi budget Hwf Hprio Hcount Hinitial Hqueue Hcontinue.
    assert (Hstop : forall s result, reachable p pol s -> step p pol s = inr result ->
      (T_step p pol s + c_loopN <= Phi s +
        (k_loop * (N.of_nat (C p) * unit p + 1) + c_loopN))%N).
    { intros s result Hreachable Hstep.
      pose proof (proj2 (W7_stop p pol s result Hwf Hprio Hreachable Hstep)) as Hcost.
      pose proof (Hqueue s); lia. }
    pose proof (T_run_credit p pol fuel Phi
      (k_loop * (N.of_nat (C p) * unit p + 1) + c_loopN)%N Hcontinue Hstop) as Hcost.
    pose proof (W1_prepare p pol Hwf Hprio) as Hprepare.
    rewrite Nat2N.inj_add in Hcost; change (N.of_nat 1) with 1%N in Hcost.
    set (queued_work := (N.of_nat (C p) * unit p)%N) in *.
    eapply N.le_trans; [|apply driver_credit_absorb].
    clear -Hcost Hprepare Hcount Hinitial; nia.
  Qed.

  Lemma T_run_le : forall p pol fuel, fits p pol ->
    (T_run p pol fuel <= c_wl * (work p pol + N.of_nat (N.size_nat fuel) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma run_enough : forall p pol fuel, fits p pol -> (fuel_for p pol <= fuel)%N ->
    exists m, run p pol fuel = Solved m.
  Proof.
    intros p pol fuel Hfits Hfuel; unfold run; rewrite loopN_fuel.
    destruct (loop_fuel (step p pol) (N.to_nat fuel) (prepare p pol))
      as [s|result] eqn:Hloop.
    - destruct (loop_fuel_path (step p pol) (N.to_nat fuel) (prepare p pol) s Hloop)
        as [xs [Hpath Hlength]].
      pose proof (W7_visits p pol xs s Hfits Hpath) as Hbound.
      rewrite Hlength, N2Nat.id in Hbound; unfold fuel_for in Hfuel; lia.
    - destruct (loop_fuel_stop_path (step p pol) (N.to_nat fuel) (prepare p pol)
        result Hloop) as [xs [last [Hpath [Hstop Hlength]]]].
      destruct Hfits as [Hwf [Hcuts Hprio]].
      assert (Hinv : invariant p pol last).
      { apply reachable_invariant; [exact Hwf|exact Hprio|now exists xs]. }
      destruct (step_stop_solved p pol last result Hwf Hinv Hstop) as [-> Hempty].
      now exists (ws_store last).
  Qed.
  Lemma T_run_height_le : forall p pol fuel (rk : L.t -> nat) h,
    S.wf p -> prio_ok p pol -> widening_free pol ->
    (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false ->
      rk a < rk b /\ rk b <= h) ->
    (T_run p pol fuel <= c_wl *
      (N.of_nat (prep p) + N.of_nat (D p + h * DW p) * unit p +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof.
    intros p pol fuel rk h Hwf Hprio Hfree Hrank.
    set (budget := (N.of_nat (D p + h * DW p) * unit p)%N).
    assert (Hcount : (N.of_nat (C p) * unit p <= budget)%N).
    { unfold budget; apply N.mul_le_mono_r.
      pose proof (visits_C_le_D p); lia. }
    assert (Hincidence : (N.of_nat (C p + D p) * unit p <= 2 * budget)%N).
    { unfold budget; replace (2 * (N.of_nat (D p + h * DW p) * unit p))%N with
        ((2 * N.of_nat (D p + h * DW p)) * unit p)%N by ring.
      apply N.mul_le_mono_r; pose proof (visits_C_le_D p); lia. }
    apply (T_run_budget p pol fuel (height_phi p rk h) budget); try assumption.
    - pose proof (W4_initial p pol rk h Hwf Hprio Hfree) as Hheight.
      pose proof (W1_queue_phi p pol Hwf Hprio) as Hqueue.
      assert (Hq : (queue_phi p (prepare p pol) <= 2 * k_prepare * budget)%N).
      { eapply N.le_trans; [exact Hqueue|].
        replace (k_prepare * N.of_nat (C p + D p) * unit p)%N with
          (k_prepare * (N.of_nat (C p + D p) * unit p))%N by ring.
        replace (2 * k_prepare * budget)%N with (k_prepare * (2 * budget))%N by ring.
        apply N.mul_le_mono_l; exact Hincidence. }
      replace (k_credit * N.of_nat (D p + h * DW p) * unit p)%N with
        (k_credit * budget)%N in Hheight by (unfold budget; ring).
      clear -Hheight Hq; nia.
    - intro s; apply driver_height_queue.
    - intros s s1 Hreachable Hstep.
      pose proof (W4_credit p pol rk h s s1 Hwf Hprio Hfree Hrank Hreachable Hstep).
      lia.
  Qed.

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
