(** * Low-high dominator certificates

    The checker validates preorder intervals and low-high witnesses independently of production.
    For example, a direct parent edge supplies the low-high witness of its child.
    Builds on: first-order graphs, canonical tries and dominator certificate signatures. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Sorting.Sorted Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig DomProducer DomOrder.
Import List.ListNotations.

Module N.
  TimeFun N.min.
  TimeFun N.max.
End N.

Fixpoint dom_key_fits (width : nat) (v : positive) : bool :=
  match width, v with
  | O, _ => false
  | S _, xH => true
  | S rest, xO tail | S rest, xI tail => dom_key_fits rest tail
  end.
TimeFun dom_key_fits.

(** Structural comparison recurses on the bounded reconstructed candidate. *)
Fixpoint dom_map_eq_ne (expected candidate : trie_ne positive) : bool :=
  match expected, candidate with
  | N001 r, N001 r' => dom_map_eq_ne r r'
  | N010 v, N010 v' => Pos.eqb v v'
  | N011 v r, N011 v' r' => Pos.eqb v v' && dom_map_eq_ne r r'
  | N100 l, N100 l' => dom_map_eq_ne l l'
  | N101 l r, N101 l' r' => dom_map_eq_ne l l' && dom_map_eq_ne r r'
  | N110 l v, N110 l' v' => dom_map_eq_ne l l' && Pos.eqb v v'
  | N111 l v r, N111 l' v' r' =>
    dom_map_eq_ne l l' && Pos.eqb v v' && dom_map_eq_ne r r'
  | _, _ => false
  end.
TimeFun dom_map_eq_ne.

Definition dom_map_eq (expected candidate : ptrie positive) : bool :=
  match expected, candidate with
  | Empty, Empty => true
  | Nodes a, Nodes b => dom_map_eq_ne a b
  | _, _ => false
  end.
TimeFun dom_map_eq.

Definition dom_scan (g : prepared) : dom_scan_data :=
  DomScanData (fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty)
    (graph_n (base g)) (graph_e (base g)) (graph_width (base g)).
TimeFun dom_scan.

Record dom_read_state := DomReadState {
  read_remaining : list positive;
  read_budget : N;
  read_next : N;
  read_positions : ptrie N
}.
TimeFun read_remaining.
TimeFun read_budget.
TimeFun read_next.
TimeFun read_positions.

Definition dom_read_step (width : nat) (listed : ptrie bool) (s : dom_read_state)
    : dom_read_state + option (ptrie N) :=
  match s with
  | DomReadState [] _ _ pos => inr (Some pos)
  | DomReadState (v :: rest) budget next pos =>
    if N.eqb budget 0%N then inr None else
      if dom_key_fits width v then
        match trie_get v listed, trie_get v pos with
        | Some _, None => inl (DomReadState rest (N.pred budget) (N.succ next)
            (PTrieCode.set v next pos))
        | _, _ => inr None
        end
      else inr None
  end.
TimeFun dom_read_step.

Definition dom_read_order (count width : nat) (listed : ptrie bool) (o : list positive)
    (next : N) (pos : ptrie N) : option (ptrie N) :=
  let budget := N.of_nat count in
  match loopN (dom_read_step width listed) (N.succ budget) (DomReadState o budget next pos) with
  | inl _ => None
  | inr result => result
  end.
TimeFun dom_read_order.


Definition dom_read_known (info : dom_scan_data) (r : positive)
    (o : list positive) : option (ptrie N) :=
  match o with
  | [] => None
  | h :: _ =>
    if dom_key_fits (dom_width info) r then
      if Pos.eqb h r then
        dom_read_order (dom_count info) (dom_width info) (dom_listed info) o 0%N Empty
      else None
    else None
  end.
TimeFun dom_read_known.

Definition dom_read (g : prepared) (r : positive) (o : list positive) :=
  dom_read_known (dom_scan g) r o.
TimeFun dom_read.

(** Positive equality may be charged to either of its operands. *)
Local Lemma dom_time_pos_eqb_right p q :
  (Pos.T_eqb p q <= N.of_nat (Pos.size_nat q))%N.
Proof.
  revert p. induction q as [q IH|q IH|]; intros [p|p|]; time_step.
Qed.

(** Width checking stops after the supplied width even on an oversized key. *)
Local Lemma dom_time_key_fits width v :
  (T_dom_key_fits width v <= N.of_nat width + 1)%N.
Proof.
  revert v. induction width as [|width IH]; intros [v|v|]; time_step.
Qed.

(** A successful width check bounds every subsequent trie traversal of that key. *)
Local Lemma dom_key_fits_width width v : dom_key_fits width v = true ->
  Pos.size_nat v <= width.
Proof.
  revert v. induction width as [|width IH]; intros [v|v|];
    cbn [dom_key_fits Pos.size_nat]; try discriminate; intros Hfits;
    try specialize (IH v Hfits); lia.
Qed.

(** Each remaining entry carries its callback charge and both counter potentials. *)
Local Definition dom_read_credit width (s : dom_read_state) : N :=
  (8 * (PTrieT.c_trie + c_loopN + 16) * N.of_nat (width + 1) * (read_budget s + 1) +
    loopN_zero_bits (read_budget s) + dom_counter_credit (read_next s))%N.

(** A successful reader step consumes one entry charge and amortizes both counters. *)
Local Lemma dom_time_read_step_go width listed s s1 :
  dom_read_step width listed s = inl s1 ->
  (T_dom_read_step width listed s + c_loopN + dom_read_credit width s1 <=
    dom_read_credit width s)%N.
Proof.
  destruct s as [remaining budget next pos]. intros Hstep.
  destruct remaining as [|v rest]; [discriminate Hstep|].
  destruct budget as [|budget]; [discriminate Hstep|].
  cbn [dom_read_step N.eqb] in Hstep.
  destruct (dom_key_fits width v) eqn:Hfits; [|discriminate Hstep].
  destruct (trie_get v listed) as [flag|] eqn:Hlisted; [|discriminate Hstep].
  destruct (trie_get v pos) as [old|] eqn:Hfresh; [discriminate Hstep|].
  injection Hstep as Hstate. subst s1.
  pose proof (dom_key_fits_width width v Hfits) as Hwidth.
  pose proof (dom_time_key_fits width v) as Hfits_time.
  pose proof (PTrieT.T_set_le N v next pos) as Hset.
  change (PTrieCode.T_set v next pos <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
  pose proof (loopN_pred_credit (N.pos budget)) as Hpred.
  pose proof (dom_time_counter_succ next) as Hsucc.
  unfold T_dom_read_step. cbn beta iota zeta.
  time_unfold N.T_eqb. cbn [N.eqb]. rewrite Hfits, Hlisted, Hfresh.
  PTrieT.trie_get_le. time_simpl.
  unfold dom_read_credit. cbn [read_budget read_next].
  fold (N.pred (N.pos budget)).
  rewrite !Nat2N.inj_add in *.
  set (charge := (8 * (PTrieT.c_trie + c_loopN + 16) *
    (N.of_nat width + N.of_nat 1))%N).
  assert (Hcharge : (T_dom_key_fits width v + 4 * N.of_nat (Pos.size_nat v) +
    PTrieCode.T_set v next pos + c_loopN + 8 <= charge)%N).
  { unfold charge. clear -Hwidth Hfits_time Hset. nia. }
  assert (Hpay : (charge * (N.pos budget + 1) =
    charge * (N.pred (N.pos budget) + 1) + charge)%N) by nia.
  rewrite Hpay. clearbody charge.
  lia.
Qed.

(** Early rejection pays only the bounded prefix of a reader step. *)
Local Lemma dom_time_read_step_stop width listed s answer :
  dom_read_step width listed s = inr answer ->
  (T_dom_read_step width listed s + c_loopN <= dom_read_credit width s)%N.
Proof.
  destruct s as [remaining budget next pos]. intro Hstep.
  unfold T_dom_read_step, dom_read_credit. cbn [read_budget read_next].
  destruct remaining as [|v rest].
  - time_simpl. nia.
  - destruct budget as [|budget].
    + time_unfold N.T_eqb. cbn [N.eqb]. time_simpl. nia.
    + pose proof (dom_time_key_fits width v) as Hfits_time.
      time_unfold N.T_eqb. cbn [N.eqb]. cbn [dom_read_step N.eqb] in Hstep.
      destruct (dom_key_fits width v) eqn:Hfits.
      * pose proof (dom_key_fits_width width v Hfits) as Hwidth.
        destruct (trie_get v listed) as [flag|] eqn:Hlisted;
          destruct (trie_get v pos) as [old|] eqn:Hfresh;
          try discriminate Hstep;
          PTrieT.trie_get_le; time_simpl;
          rewrite !Nat2N.inj_add in *; nia.
      * time_simpl. rewrite !Nat2N.inj_add in *. nia.
Qed.

Local Opaque loop Acc_intro_generator T_loopN.

(** Carry and borrow credits make the budgeted reader linear in count and key width. *)
Local Lemma dom_time_read_order count width listed o :
  (T_dom_read_order count width listed o 0 Empty <=
    (16 * (PTrieT.c_trie + c_loopN + 16) + 32 * c_loopN + 32) *
      N.of_nat ((count + 1) * (width + 1)))%N.
Proof.
  pose proof (@T_loopN_amort dom_read_state (option (ptrie N))
    (dom_read_step width listed) (T_dom_read_step width listed) (fun _ => True)
    (dom_read_credit width) (fun _ => 0%N) (N.succ (N.of_nat count))
    (DomReadState o (N.of_nat count) 0 Empty)
    ltac:(intros s s1 _ Hstep; split; [exact I|now apply dom_time_read_step_go])
    ltac:(intros s result _ Hstep; cbn beta; rewrite N.add_0_r;
      eapply dom_time_read_step_stop; exact Hstep) I) as Hloop.
  destruct (loopN (dom_read_step width listed) (N.succ (N.of_nat count))
    (DomReadState o (N.of_nat count) 0 Empty)) as [state|answer] eqn:Hresult;
    cbn beta iota zeta in Hloop.
  all: pose proof (dom_time_of_nat count) as Hconvert;
    pose proof (N.T_succ_le (N.of_nat count)) as Hsucc;
    pose proof (loopN_zero_bits_le_size (N.of_nat count)) as Hzeros;
    pose proof (dom_size_value (N.of_nat count)) as Hbits;
    pose proof (dom_size_value (N.succ (N.of_nat count))) as Hfuel.
  all: unfold T_dom_read_order; rewrite ?Hresult; time_simpl;
    unfold dom_read_credit in Hloop; cbn [read_budget read_next dom_counter_credit] in Hloop;
    rewrite Nat2N.inj_mul, !Nat2N.inj_add in *.
  all: change (fun H : dom_read_state => T_dom_read_step width listed H)
    with (T_dom_read_step width listed).
  all: set (running := T_loopN (dom_read_step width listed)
    (T_dom_read_step width listed) (N.succ (N.of_nat count))
    (DomReadState o (N.of_nat count) 0 Empty)) in *; clearbody running.
  all: clear -Hloop Hconvert Hsucc Hzeros Hbits Hfuel; nia.
Qed.

Definition dom_rebuild (width : nat) (r : positive) (m : ptrie positive)
    (pos : ptrie N) (acc : option (ptrie positive)) (v : positive)
    : option (ptrie positive) :=
  match acc with
  | None => None
  | Some built =>
    if Pos.eqb v r then
      match trie_get v m with None => Some built | Some _ => None end
    else
      match trie_get v m with
      | None => None
      | Some p =>
        if dom_key_fits width p then
          match trie_get p pos, trie_get v pos with
          | Some pp, Some pv => if N.ltb pp pv then Some (PTrieCode.set v p built) else None
          | _, _ => None
          end
        else None
      end
  end.
TimeFun dom_rebuild.

(** A previously checked order supplies the positions for the parent-map check. *)
Definition dom_map_check_pos (info : dom_scan_data) (r : positive) (m : ptrie positive)
    (o : list positive) (pos : ptrie N) : bool :=
  match fold_left (dom_rebuild (dom_width info) r m pos) o (Some Empty) with
  | None => false
  | Some built => dom_map_eq built m
  end.
TimeFun dom_map_check_pos.

Definition dom_map_check_known (info : dom_scan_data) (r : positive) (m : ptrie positive)
    (o : list positive) : bool :=
  match dom_read_known info r o with
  | None => false
  | Some pos =>
    match fold_left (dom_rebuild (dom_width info) r m pos) o (Some Empty) with
    | None => false
    | Some built => dom_map_eq built m
    end
  end.
TimeFun dom_map_check_known.

(** Reusing a successful read leaves the parent-map check unchanged. *)
Local Lemma dom_map_check_known_pos : forall info r m o pos,
  dom_read_known info r o = Some pos ->
  dom_map_check_known info r m o = dom_map_check_pos info r m o pos.
Proof.
  intros info r m o pos Hread. unfold dom_map_check_known. now rewrite Hread.
Qed.

(** The reused-position phase costs no more than reading the order and then checking it. *)
Local Lemma dom_time_map_check_pos : forall info r m o pos,
  dom_read_known info r o = Some pos ->
  (T_dom_map_check_pos info r m o pos <= T_dom_map_check_known info r m o)%N.
Proof.
  intros info r m o pos Hread.
  unfold T_dom_map_check_pos, T_dom_map_check_known. time_simpl.
  rewrite Hread. time_simpl. lia.
Qed.

Definition dom_map_check (g : prepared) (r : positive) (m : ptrie positive)
    (o : list positive) := dom_map_check_known (dom_scan g) r m o.
TimeFun dom_map_check.

Definition dom_size_get (sizes : ptrie N) (v : positive) : N :=
  match trie_get v sizes with Some n => n | None => 1%N end.
TimeFun dom_size_get.

Definition dom_add_size (m : ptrie positive) (sizes : ptrie N) (v : positive) : ptrie N :=
  let own := dom_size_get sizes v in
  let sizes := PTrieCode.set v own sizes in
  match trie_get v m with
  | None => sizes
  | Some p => PTrieCode.set p (N.add (dom_size_get sizes p) own) sizes
  end.
TimeFun dom_add_size.

Definition dom_sizes (m : ptrie positive) (o : list positive) : ptrie N :=
  fold_left (dom_add_size m) (rev_append o []) Empty.
TimeFun dom_sizes.

Definition dom_interval (pos sizes : ptrie N) (u v : positive) : bool :=
  match trie_get u pos, trie_get v pos with
  | Some pu, Some pv => N.leb pu pv &&
      N.leb (N.add pv (dom_size_get sizes v)) (N.add pu (dom_size_get sizes u))
  | _, _ => false
  end.
TimeFun dom_interval.

Definition dom_sizes_ok (m : ptrie positive) (pos sizes : ptrie N) (o : list positive)
    : bool :=
  forallb (fun v => match trie_get v m with
    | None => true
    | Some p => dom_interval pos sizes p v
    end) o.
TimeFun dom_sizes_ok.

Definition dom_edge_update (r : positive) (m : ptrie positive) (pos sizes : ptrie N)
    (u : positive) (acc : option (ptrie (bool * N * N))) (v : positive)
    : option (ptrie (bool * N * N)) :=
  match acc, trie_get u pos, trie_get v pos with
  | Some flags, Some pu, Some _ =>
    if Pos.eqb v r then Some flags else
      match trie_get v m with
      | None => None
      | Some p =>
        if dom_interval pos sizes p u then
          let '(direct, lo, hi) := match trie_get v flags with
            | None => (false, pu, pu)
            | Some info => info
            end in
          Some (PTrieCode.set v (direct || Pos.eqb u p, N.min lo pu, N.max hi pu) flags)
        else None
      end
  | _, _, _ => None
  end.
TimeFun dom_edge_update.

Definition dom_edges_from (g : prepared) (r : positive) (m : ptrie positive)
    (pos sizes : ptrie N) (acc : option (ptrie (bool * N * N))) (u : positive)
    : option (ptrie (bool * N * N)) :=
  fold_left (dom_edge_update r m pos sizes u) (succs (base g) u) acc.
TimeFun dom_edges_from.

Definition dom_low_high (r : positive) (pos sizes : ptrie N)
    (flags : ptrie (bool * N * N)) (v : positive) : bool :=
  if Pos.eqb v r then true else
    match trie_get v pos, trie_get v flags with
    | Some pv, Some (direct, lo, hi) =>
      direct || (N.ltb lo pv && N.leb (N.add pv (dom_size_get sizes v)) hi)
    | _, _ => false
    end.
TimeFun dom_low_high.

Definition dom_edges (g : prepared) (r : positive) (m : ptrie positive)
    (o : list positive) (pos sizes : ptrie N) : bool :=
  match fold_left (dom_edges_from g r m pos sizes) o (Some Empty) with
  | None => false
  | Some flags => forallb (dom_low_high r pos sizes flags) o
  end.
TimeFun dom_edges.

(** Accepted orders can be numbered directly without inspecting the graph again. *)
Definition dom_positions (o : list positive) : ptrie N :=
  snd (fold_left (fun acc v =>
    let '(next, pos) := acc in
    (N.succ next, PTrieCode.set v next pos)) o (0%N, Empty)).
TimeFun dom_positions.

(** Numbering preserves keys that occur outside the processed list. *)
Local Lemma dom_number_preserves : forall vs next pos v,
  ~ In v vs ->
  trie_get v (snd (fold_left (fun acc u =>
    let '(next, pos) := acc in (N.succ next, PTrieCode.set u next pos))
    vs (next, pos))) = trie_get v pos.
Proof.
  intros vs. induction vs as [| u rest IH]; intros next pos v Habsent.
  - reflexivity.
  - cbn [fold_left]. rewrite IH.
    + apply PTrie.get_set_other. intro Heq. subst u. apply Habsent. now left.
    + intro Hin. apply Habsent. now right.
Qed.

(** Every numbered key was present initially or occurs in the processed list. *)
Local Lemma dom_number_domain : forall vs next pos v,
  (exists i, trie_get v (snd (fold_left (fun acc u =>
    let '(next, pos) := acc in (N.succ next, PTrieCode.set u next pos))
    vs (next, pos))) = Some i) <->
  In v vs \/ exists i, trie_get v pos = Some i.
Proof.
  intros vs. induction vs as [| u rest IH]; intros next pos v; cbn [fold_left In].
  - tauto.
  - rewrite IH. destruct (Pos.eq_dec v u) as [Heq | Hneq].
    + subst v. rewrite PTrie.get_set_same. split.
      * intros _. left. now left.
      * intros _. right. exists next. reflexivity.
    + rewrite PTrie.get_set_other by exact Hneq. intuition congruence.
Qed.

(** Distinct input vertices receive their exact offset from the initial number. *)
Local Lemma dom_number_nth : forall vs next pos i v,
  NoDup vs -> nth_error vs i = Some v ->
  trie_get v (snd (fold_left (fun acc u =>
    let '(next, pos) := acc in (N.succ next, PTrieCode.set u next pos))
    vs (next, pos))) = Some (N.add next (N.of_nat i)).
Proof.
  intros vs. induction vs as [| u rest IH]; intros next pos i v Hdistinct Hnth.
  - destruct i; discriminate Hnth.
  - inversion Hdistinct as [| u' rest' Hfresh Hrest]; subst u' rest'.
    destruct i as [| i].
    + cbn [nth_error] in Hnth. injection Hnth as Heq. subst v.
      cbn [fold_left]. rewrite dom_number_preserves by exact Hfresh.
      rewrite PTrie.get_set_same. f_equal. lia.
    + cbn [nth_error] in Hnth. cbn [fold_left].
      rewrite (IH (N.succ next) (PTrieCode.set u next pos) i v Hrest Hnth).
      rewrite Nat2N.inj_succ. f_equal. lia.
Qed.

Local Lemma dom_positions_domain : forall o v,
  (exists i, trie_get v (dom_positions o) = Some i) <-> In v o.
Proof.
  intros o v. unfold dom_positions. rewrite dom_number_domain.
  split; [| intro Hin; now left].
  intros [Hin | [i Hget]]; [exact Hin |].
  rewrite PTrie.get_empty in Hget. discriminate Hget.
Qed.

Local Lemma dom_positions_nth : forall o i v,
  NoDup o -> nth_error o i = Some v ->
  trie_get v (dom_positions o) = Some (N.of_nat i).
Proof.
  intros o i v Hdistinct Hnth. unfold dom_positions.
  exact (dom_number_nth o 0%N Empty i v Hdistinct Hnth).
Qed.

Local Lemma dom_positions_value : forall o v i,
  NoDup o -> trie_get v (dom_positions o) = Some i ->
  exists j, nth_error o j = Some v /\ i = N.of_nat j.
Proof.
  intros o v i Hdistinct Hget.
  assert (Hin : In v o) by (apply dom_positions_domain; now exists i).
  apply In_nth_error in Hin as [j Hnth].
  pose proof (dom_positions_nth o j v Hdistinct Hnth) as Hnumber.
  exists j. split; [exact Hnth |]. congruence.
Qed.

(** A vertex on a path has a prefix using only vertices of that path. *)
Local Lemma dom_path_prefix : forall g a vs b, path g a vs b ->
  forall y, In y vs -> exists prefix, path g a prefix y /\ incl prefix vs.
Proof.
  intros g a vs b Hpath.
  induction Hpath as [v | u v vs w Huv Hpath IH]; intros y Hin.
  - destruct Hin as [<- | Hin]; [| contradiction].
    exists [v]. split; [constructor | intros z Hz; exact Hz].
  - destruct Hin as [<- | Hin].
    + exists [u]. split; [constructor |].
      intros z [<- | Hz]; [now left | contradiction].
    + destruct (IH y Hin) as [prefix [Hprefix Hincl]].
      exists (u :: prefix). split.
      * eapply path_step; eassumption.
      * intros z [<- | Hz]; [now left | right; now apply Hincl].
Qed.

(** Structural comparison accepts precisely the reconstructed parent map. *)
Local Lemma dom_map_eq_ne_spec : forall expected candidate,
  dom_map_eq_ne expected candidate = true <-> expected = candidate.
Proof.
  intros expected.
  induction expected as [r IHr | v | v r IHr | l IHl | l IHl r IHr |
      l IHl v | l IHl v r IHr];
    intros candidate; destruct candidate; cbn [dom_map_eq_ne];
    rewrite ?andb_true_iff, ?Pos.eqb_eq, ?IHl, ?IHr;
    split; intro H; try discriminate; intuition congruence.
Qed.

Local Lemma dom_map_eq_spec : forall expected candidate,
  dom_map_eq expected candidate = true <-> expected = candidate.
Proof.
  intros [| expected] [| candidate]; cbn [dom_map_eq];
    rewrite ?dom_map_eq_ne_spec; split; intro H; try discriminate; congruence.
Qed.

(** Reading inserts each remaining vertex once and preserves earlier positions. *)
Local Definition dom_read_success (listed : ptrie bool) (s : dom_read_state)
    (result : ptrie N) : Prop :=
  NoDup (read_remaining s) /\
  (N.of_nat (length (read_remaining s)) <= read_budget s)%N /\
  (forall v, In v (read_remaining s) ->
    (exists b, trie_get v listed = Some b) /\
    trie_get v (read_positions s) = None /\
    exists i, trie_get v result = Some i) /\
  (forall v i, trie_get v (read_positions s) = Some i -> trie_get v result = Some i) /\
  result = snd (fold_left (fun acc v =>
    let '(next, pos) := acc in (N.succ next, PTrieCode.set v next pos))
    (read_remaining s) (read_next s, read_positions s)).

Local Lemma dom_read_step_success : forall width listed s s1 result,
  dom_read_step width listed s = inl s1 ->
  dom_read_success listed s1 result -> dom_read_success listed s result.
Proof.
  intros width listed [remaining budget next pos] s1 result Hstep Hrest.
  destruct remaining as [| v rest]; [discriminate Hstep |].
  cbn [dom_read_step] in Hstep.
  destruct (N.eqb budget 0) eqn:Hbudget; [discriminate Hstep |].
  destruct (dom_key_fits width v); [| discriminate Hstep].
  destruct (trie_get v listed) as [flag |] eqn:Hlisted; [| discriminate Hstep].
  destruct (trie_get v pos) as [old |] eqn:Hnew; [discriminate Hstep |].
  injection Hstep as Hstate. subst s1.
  cbn [dom_read_success read_remaining read_budget read_positions] in Hrest |- *.
  destruct Hrest as [Hdistinct [Hlength [Hmembers [Hpreserved Hnumber]]]].
  assert (Hfresh : ~ In v rest).
  { intro Hin. destruct (Hmembers v Hin) as [_ [Hnone _]].
    change (trie_get v (PTrieCode.set v next pos) = None) in Hnone.
    rewrite PTrie.get_set_same in Hnone. discriminate Hnone. }
  split; [now constructor |]. split.
  - change (N.of_nat (S (length rest)) <= budget)%N. rewrite Nat2N.inj_succ.
    change (N.of_nat (length rest) <= N.pred budget)%N in Hlength.
    apply N.eqb_neq in Hbudget. lia.
  - split.
    + intros q [Heq | Hin].
      * subst q. split; [now exists flag |]. split; [exact Hnew |].
        exists next. apply Hpreserved. apply PTrie.get_set_same.
      * destruct (Hmembers q Hin) as [Hlistedq [Hnone Hresult]].
        assert (Hneq : q <> v) by (intro Heq; subst q; contradiction).
        change (trie_get q (PTrieCode.set v next pos) = None) in Hnone.
        rewrite PTrie.get_set_other in Hnone by exact Hneq.
        exact (conj Hlistedq (conj Hnone Hresult)).
    + split.
      * intros q i Hget. change (trie_get q pos = Some i) in Hget. apply Hpreserved.
        change (trie_get q (PTrieCode.set v next pos) = Some i).
        rewrite PTrie.get_set_other; [exact Hget |].
        intro Heq. subst q. rewrite Hnew in Hget. discriminate Hget.
      * exact Hnumber.
Qed.

Local Lemma dom_read_stop_success : forall width listed s result,
  dom_read_step width listed s = inr (Some result) -> dom_read_success listed s result.
Proof.
  intros width listed [remaining budget next pos] result Hstep.
  destruct remaining as [| v rest].
  - cbn [dom_read_step] in Hstep. injection Hstep as Hresult. subst result.
    cbn [dom_read_success read_remaining read_budget read_positions].
    split; [constructor |]. split; [change (0 <= budget)%N; lia |].
    split; [intros v Hin; contradiction |].
    split; [intros v i Hget; exact Hget | reflexivity].
  - cbn [dom_read_step] in Hstep.
    destruct (N.eqb budget 0); [discriminate Hstep |].
    destruct (dom_key_fits width v); [| discriminate Hstep].
    destruct (trie_get v listed), (trie_get v pos); discriminate Hstep.
Qed.

Local Lemma dom_read_loop_success : forall width listed fs
    (Hacc : Acc (@loopN_lt dom_read_state) fs) result,
  loop loopN_lt (loopN_step (dom_read_step width listed)) fs Hacc = inr (Some result) ->
  dom_read_success listed (snd fs) result.
Proof.
  intros width listed fs Hacc.
  induction Hacc as [[fuel s] Hacc IH] using Acc_ind_dep.
  intros result Hrun. destruct fuel as [| p]; [discriminate Hrun |].
  cbn [loop loopN_step Acc_inv] in Hrun.
  destruct (dom_read_step width listed s) as [s1 | answer] eqn:Hstep.
  - eapply dom_read_step_success; [exact Hstep |].
    eapply (IH (N.pred (N.pos p), s1) _ result). exact Hrun.
  - destruct answer as [final |]; [| discriminate Hrun].
    injection Hrun as Hresult. subst final.
    eapply dom_read_stop_success. exact Hstep.
Qed.

(** Abstract loop equations do not require expanding the accessibility generator. *)
Local Opaque loop Acc_intro_generator.

(** A successful optional result cannot come from exhausted fuel. *)
Local Lemma dom_read_return_some (run : dom_read_state + option (ptrie N)) result :
  (match run with inl _ => None | inr answer => answer end) = Some result ->
  run = inr (Some result).
Proof.
  destruct run as [state | answer]; intro Hresult; [discriminate Hresult |].
  now subst answer.
Qed.

Local Lemma dom_read_order_success : forall count width listed o next pos result,
  dom_read_order count width listed o next pos = Some result ->
  dom_read_success listed (DomReadState o (N.of_nat count) next pos) result.
Proof.
  intros count width listed o next pos result Hread.
  unfold dom_read_order in Hread.
  apply dom_read_return_some in Hread. unfold loopN in Hread.
  lazymatch type of Hread with
  | loop _ _ ?state ?Hacc = _ =>
    exact (dom_read_loop_success width listed state Hacc result Hread)
  end.
Qed.

Local Lemma dom_listed_fold : forall vs acc v,
  (exists b, trie_get v (fold_left (fun seen u => PTrieCode.set u true seen) vs acc) = Some b)
  <-> In v vs \/ exists b, trie_get v acc = Some b.
Proof.
  intros vs. induction vs as [| u rest IH]; intros acc v; cbn [fold_left In].
  - tauto.
  - rewrite IH. destruct (Pos.eq_dec v u) as [Heq | Hneq].
    + subst v. rewrite PTrie.get_set_same. split.
      * intros _. left. now left.
      * intros _. right. exists true. reflexivity.
    + rewrite PTrie.get_set_other by exact Hneq. intuition congruence.
Qed.

Local Lemma dom_scan_listed : forall g v,
  (exists b, trie_get v (dom_listed (dom_scan g)) = Some b) <-> In v (nodes g).
Proof.
  intros g v. unfold dom_scan. cbn [dom_listed]. rewrite dom_listed_fold.
  split.
  - intros [Hin | [b Hget]]; [exact Hin |].
    rewrite PTrie.get_empty in Hget. discriminate Hget.
  - intro Hin. now left.
Qed.

Local Lemma dom_read_known_success : forall g r o pos,
  dom_read_known (dom_scan g) r o = Some pos ->
  NoDup o /\ length o <= graph_n (base g) /\ hd_error o = Some r /\
  (forall v, In v o -> In v (nodes g)) /\
  (forall v, In v o -> exists i, trie_get v pos = Some i).
Proof.
  intros g r [| h rest] pos Hread; [discriminate Hread |].
  unfold dom_read_known in Hread.
  destruct (dom_key_fits (dom_width (dom_scan g)) r); [| discriminate Hread].
  destruct (Pos.eqb h r) eqn:Hroot; [| discriminate Hread].
  apply Pos.eqb_eq in Hroot. subst h.
  apply dom_read_order_success in Hread.
  cbn [dom_read_success read_remaining read_budget read_positions dom_scan dom_count]
    in Hread.
  destruct Hread as [Hdistinct [Hlength [Hmembers [Hpreserved Hresult]]]].
  change (N.of_nat (length (r :: rest)) <= N.of_nat (graph_n (base g)))%N in Hlength.
  split; [exact Hdistinct |]. split; [lia |]. split; [reflexivity |]. split.
  - intros v Hin. apply dom_scan_listed. exact (proj1 (Hmembers v Hin)).
  - intros v Hin. exact (proj2 (proj2 (Hmembers v Hin))).
Qed.

Local Lemma dom_read_known_positions : forall info r o pos,
  dom_read_known info r o = Some pos -> pos = dom_positions o.
Proof.
  intros info r [| h rest] pos Hread; [discriminate Hread |].
  unfold dom_read_known in Hread.
  destruct (dom_key_fits (dom_width info) r); [| discriminate Hread].
  destruct (Pos.eqb h r); [| discriminate Hread].
  apply dom_read_order_success in Hread.
  destruct Hread as [_ [_ [_ [_ Hresult]]]]. exact Hresult.
Qed.

(** Reconstructed entries either omit the root or name an earlier positioned parent. *)
Local Definition dom_parent_valid r m pos v : Prop :=
  (v = r -> trie_get v m = None) /\
  (v <> r -> exists p pp pv, trie_get v m = Some p /\
    trie_get p pos = Some pp /\ trie_get v pos = Some pv /\ (pp < pv)%N).

Local Lemma dom_rebuild_valid : forall width r m pos acc v out,
  dom_rebuild width r m pos acc v = Some out -> dom_parent_valid r m pos v.
Proof.
  intros width r m pos [built |] v out Hstep; [| discriminate Hstep].
  unfold dom_rebuild in Hstep. destruct (Pos.eqb v r) eqn:Hroot.
  - apply Pos.eqb_eq in Hroot. destruct (trie_get v m) eqn:Hparent;
      [discriminate Hstep |].
    split; [intros _; exact Hparent |]. intro Hneq. contradiction.
  - apply Pos.eqb_neq in Hroot.
    destruct (trie_get v m) as [p |] eqn:Hparent; [| discriminate Hstep].
    destruct (dom_key_fits width p); [| discriminate Hstep].
    destruct (trie_get p pos) as [pp |] eqn:Hp; [| discriminate Hstep].
    destruct (trie_get v pos) as [pv |] eqn:Hv; [| discriminate Hstep].
    destruct (N.ltb pp pv) eqn:Hbefore; [| discriminate Hstep].
    apply N.ltb_lt in Hbefore. split; [intro Heq; contradiction |].
    intros _. exists p, pp, pv. repeat split; assumption.
Qed.

Local Lemma dom_rebuild_domain : forall width r m pos acc v out,
  dom_rebuild width r m pos acc v = Some out ->
  forall q p, trie_get q out = Some p ->
    (exists before, acc = Some before /\ trie_get q before = Some p) \/ q = v.
Proof.
  intros width r m pos [built |] v out Hstep; [| discriminate Hstep].
  unfold dom_rebuild in Hstep. destruct (Pos.eqb v r).
  - destruct (trie_get v m); [discriminate Hstep |].
    injection Hstep as Heq. subst out. intros q p Hget.
    left. exists built. now split.
  - destruct (trie_get v m) as [parent |]; [| discriminate Hstep].
    destruct (dom_key_fits width parent); [| discriminate Hstep].
    destruct (trie_get parent pos) as [pp |]; [| discriminate Hstep].
    destruct (trie_get v pos) as [pv |]; [| discriminate Hstep].
    destruct (N.ltb pp pv); [| discriminate Hstep].
    injection Hstep as Heq. subst out. intros q p Hget.
    destruct (Pos.eq_dec q v) as [Heq | Hneq]; [now right |].
    rewrite PTrie.get_set_other in Hget by exact Hneq.
    left. exists built. now split.
Qed.

Local Lemma dom_rebuild_fold_none : forall width r m pos vs,
  fold_left (dom_rebuild width r m pos) vs None = None.
Proof.
  intros width r m pos vs. induction vs as [| v rest IH];
    cbn [fold_left dom_rebuild]; assumption || reflexivity.
Qed.

Local Lemma dom_rebuild_fold_valid : forall width r m pos vs acc out,
  fold_left (dom_rebuild width r m pos) vs acc = Some out ->
  (forall v, In v vs -> dom_parent_valid r m pos v) /\
  (forall q p, trie_get q out = Some p ->
    (exists before, acc = Some before /\ trie_get q before = Some p) \/ In q vs).
Proof.
  intros width r m pos vs. induction vs as [| v rest IH]; intros acc out Hfold.
  - cbn [fold_left] in Hfold. subst acc. split.
    + intros q Hin. contradiction.
    + intros q p Hget. left. exists out. now split.
  - cbn [fold_left] in Hfold.
    destruct (dom_rebuild width r m pos acc v) as [built |] eqn:Hstep.
    2: rewrite dom_rebuild_fold_none in Hfold; discriminate Hfold.
    destruct (IH (Some built) out Hfold) as [Hvalid Hdomain]. split.
    + intros q [Heq | Hin].
      * subst q. eapply dom_rebuild_valid. exact Hstep.
      * now apply Hvalid.
    + intros q p Hget. destruct (Hdomain q p Hget) as [[before [Heq Hbefore]] | Hin].
      * injection Heq as Heq. subst before.
        destruct (dom_rebuild_domain width r m pos acc v built Hstep q p Hbefore)
          as [Hinitial | Heq].
        -- now left.
        -- right. now left.
      * right. now right.
Qed.

(** Successful structural comparison excludes bindings outside the accepted order. *)
Local Lemma dom_map_check_structure : forall g r m o,
  dom_map_check_known (dom_scan g) r m o = true ->
  NoDup o /\ hd_error o = Some r /\ trie_get r m = None /\
  (forall v, In v o -> v <> r -> exists p,
    trie_get v m = Some p /\ order_before o p v) /\
  (forall v p, trie_get v m = Some p -> In v o).
Proof.
  intros g r m o Hcheck. unfold dom_map_check_known in Hcheck.
  destruct (dom_read_known (dom_scan g) r o) as [pos |] eqn:Hread;
    [| discriminate Hcheck].
  destruct (fold_left (dom_rebuild (dom_width (dom_scan g)) r m pos) o (Some Empty))
    as [built |] eqn:Hfold; [| discriminate Hcheck].
  apply dom_map_eq_spec in Hcheck. subst built.
  destruct (dom_read_known_success g r o pos Hread) as
    [Hdistinct [_ [Hhead _]]].
  pose proof (dom_read_known_positions (dom_scan g) r o pos Hread) as Hpositions.
  destruct (dom_rebuild_fold_valid (dom_width (dom_scan g)) r m pos o (Some Empty) m
    Hfold) as [Hvalid Hdomain].
  assert (Hroot : In r o).
  { destruct o as [| h rest]; [discriminate Hhead |].
    injection Hhead as Heq. subst h. now left. }
  split; [exact Hdistinct |]. split; [exact Hhead |].
  split; [exact (proj1 (Hvalid r Hroot) eq_refl) |]. split.
  - intros v Hin Hneq.
    destruct (proj2 (Hvalid v Hin) Hneq) as [p [pp [pv [Hparent [Hp [Hv Hbefore]]]]]].
    subst pos.
    destruct (dom_positions_value o p pp Hdistinct Hp) as [ip [Hip Hpp]].
    destruct (dom_positions_value o v pv Hdistinct Hv) as [iv [Hiv Hpv]].
    exists p. split; [exact Hparent |]. exists ip, iv. repeat split; try assumption.
    subst pp pv. lia.
  - intros v p Hget. destruct (Hdomain v p Hget) as [[before [Heq Hbefore]] | Hin].
    + injection Heq as Heq. subst before. rewrite PTrie.get_empty in Hbefore.
      discriminate Hbefore.
    + exact Hin.
Qed.

Local Lemma dom_nodes_verts : forall g, nodes g = verts (base g).
Proof.
  intros [[vs adjacency] predecessors count_v count_e]. reflexivity.
Qed.

(** Writing back a size's default value leaves every size observation unchanged. *)
Lemma dom_size_set_own : forall sizes v x,
  dom_size_get (PTrieCode.set v (dom_size_get sizes v) sizes) x = dom_size_get sizes x.
Proof.
  intros sizes v x. unfold dom_size_get at 1.
  destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite PTrie.get_set_same. reflexivity.
  - rewrite PTrie.get_set_other by exact Hne. reflexivity.
Qed.

(** One aggregation step only adds the current vertex's mass to its parent. *)
Lemma dom_add_size_value : forall m sizes v x,
  dom_size_get (dom_add_size m sizes v) x =
    match trie_get v m with
    | None => dom_size_get sizes x
    | Some p => if Pos.eqb x p
        then (dom_size_get sizes p + dom_size_get sizes v)%N
        else dom_size_get sizes x
    end.
Proof.
  intros m sizes v x. unfold dom_add_size.
  destruct (trie_get v m) as [p|] eqn:Hparent.
  - rewrite dom_size_set_own. unfold dom_size_get at 1.
    destruct (Pos.eqb x p) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst x. now rewrite PTrie.get_set_same.
    + apply Pos.eqb_neq in Heq. rewrite PTrie.get_set_other by exact Heq.
      apply dom_size_set_own.
  - apply dom_size_set_own.
Qed.

(** Every aggregation cell is positive, including cells absent from the trie. *)
Lemma dom_add_size_positive : forall m sizes v,
  (forall x, (1 <= dom_size_get sizes x)%N) ->
  forall x, (1 <= dom_size_get (dom_add_size m sizes v) x)%N.
Proof.
  intros m sizes v Hpositive x. rewrite dom_add_size_value.
  destruct (trie_get v m) as [p|]; [destruct (Pos.eqb x p)|];
    pose proof (Hpositive x); pose proof (Hpositive v); try lia.
Qed.

Lemma dom_sizes_positive : forall m o x, (1 <= dom_size_get (dom_sizes m o) x)%N.
Proof.
  intros m o. unfold dom_sizes.
  assert (Hfold : forall xs sizes,
    (forall x, (1 <= dom_size_get sizes x)%N) ->
    forall x, (1 <= dom_size_get (fold_left (dom_add_size m) xs sizes) x)%N).
  { intro xs. induction xs as [|v rest IH]; intros sizes Hpositive x.
    - apply Hpositive.
    - cbn [fold_left]. apply IH. now apply dom_add_size_positive. }
  apply Hfold. intro x. unfold dom_size_get. rewrite PTrie.get_empty. lia.
Qed.

(** Weighted mass tracks the unprocessed cells without enumerating trie bindings. *)
Definition dom_size_mass (weight : positive -> N) (xs : list positive) (sizes : ptrie N) : N :=
  fold_right (fun x total => (weight x * dom_size_get sizes x + total)%N) 0%N xs.

Lemma dom_size_mass_absent : forall weight xs m sizes v,
  (forall p, trie_get v m = Some p -> ~ In p xs) ->
  dom_size_mass weight xs (dom_add_size m sizes v) = dom_size_mass weight xs sizes.
Proof.
  intros weight xs. induction xs as [|x rest IH]; intros m sizes v Habsent.
  - reflexivity.
  - change ((weight x * dom_size_get (dom_add_size m sizes v) x +
      dom_size_mass weight rest (dom_add_size m sizes v))%N =
      (weight x * dom_size_get sizes x + dom_size_mass weight rest sizes)%N).
    rewrite IH.
    + rewrite dom_add_size_value. destruct (trie_get v m) as [p|] eqn:Hparent;
        [|reflexivity].
      destruct (Pos.eqb x p) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq. subst x. exfalso. apply (Habsent p eq_refl). now left.
    + intros p Hparent Hin. apply (Habsent p Hparent). now right.
Qed.

Lemma dom_size_mass_present : forall weight xs m sizes v p,
  NoDup xs -> trie_get v m = Some p -> In p xs ->
  dom_size_mass weight xs (dom_add_size m sizes v) =
    (dom_size_mass weight xs sizes + weight p * dom_size_get sizes v)%N.
Proof.
  intros weight xs. induction xs as [|x rest IH]; intros m sizes v p Hunique Hparent Hin.
  - contradiction.
  - inversion Hunique as [|head tail Hfresh Hrest]; subst head tail.
    change ((weight x * dom_size_get (dom_add_size m sizes v) x +
      dom_size_mass weight rest (dom_add_size m sizes v))%N =
      (weight x * dom_size_get sizes x + dom_size_mass weight rest sizes +
        weight p * dom_size_get sizes v)%N).
    destruct Hin as [<-|Hin].
    + rewrite dom_size_mass_absent.
      * rewrite dom_add_size_value, Hparent, Pos.eqb_refl, N.mul_add_distr_l. lia.
      * intros p Hget. rewrite Hparent in Hget. injection Hget as <-. exact Hfresh.
    + rewrite (IH m sizes v p Hrest Hparent Hin), dom_add_size_value, Hparent.
      assert (Hne : x <> p) by (intro Heq; subst x; contradiction).
      rewrite (proj2 (Pos.eqb_neq x p) Hne). lia.
Qed.

(** Moving a cell to its remaining parent preserves mass when both have the same weight. *)
Lemma dom_size_mass_transfer : forall weight remaining m sizes v p,
  NoDup remaining -> trie_get v m = Some p -> In p remaining -> weight v = weight p ->
  dom_size_mass weight remaining (dom_add_size m sizes v) =
    dom_size_mass weight (v :: remaining) sizes.
Proof.
  intros weight remaining m sizes v p Hunique Hparent Hin Heq.
  rewrite (dom_size_mass_present weight remaining m sizes v p Hunique Hparent Hin).
  change ((dom_size_mass weight remaining sizes + weight p * dom_size_get sizes v)%N =
    (weight v * dom_size_get sizes v + dom_size_mass weight remaining sizes)%N).
  rewrite Heq. apply N.add_comm.
Qed.

(** No later update can change a cell when no remaining vertex points to it. *)
Lemma dom_size_fold_preserves : forall m xs sizes x,
  (forall v, In v xs -> trie_get v m <> Some x) ->
  dom_size_get (fold_left (dom_add_size m) xs sizes) x = dom_size_get sizes x.
Proof.
  intros m xs. induction xs as [|v rest IH]; intros sizes x Houtside.
  - reflexivity.
  - cbn [fold_left]. rewrite IH.
    + rewrite dom_add_size_value. destruct (trie_get v m) as [p|] eqn:Hparent;
        [|reflexivity].
      destruct (Pos.eqb x p) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq. subst p. exfalso. apply (Houtside v); [now left|exact Hparent].
    + intros u Hin. apply Houtside. now right.
Qed.

Lemma dom_size_fold_mass : forall weight done remaining m sizes,
  NoDup (done ++ remaining) ->
  (forall before v after, done = before ++ v :: after ->
    exists p, trie_get v m = Some p /\ In p (after ++ remaining) /\ weight v = weight p) ->
  dom_size_mass weight remaining (fold_left (dom_add_size m) done sizes) =
    dom_size_mass weight (done ++ remaining) sizes.
Proof.
  intros weight done. induction done as [|v rest IH]; intros remaining m sizes Hunique Hparents.
  - reflexivity.
  - cbn [app] in Hunique. inversion Hunique as [|head tail Hfresh Hrest]; subst head tail.
    cbn [fold_left]. rewrite (IH remaining m (dom_add_size m sizes v) Hrest).
    + destruct (Hparents [] v rest eq_refl) as [p [Hparent [Hin Heq]]].
      exact (dom_size_mass_transfer weight (rest ++ remaining) m sizes v p Hrest Hparent Hin Heq).
    + intros before u after Heq. apply (Hparents (v :: before) u after). cbn. now rewrite Heq.
Qed.

(** Nested half-open intervals compose transitively. *)
Lemma dom_interval_trans : forall pos sizes u v w,
  dom_interval pos sizes u v = true -> dom_interval pos sizes v w = true ->
  dom_interval pos sizes u w = true.
Proof.
  intros pos sizes u v w Huv Hvw. unfold dom_interval in *.
  destruct (trie_get u pos) as [pu|] eqn:Hu;
    destruct (trie_get v pos) as [pv|] eqn:Hv;
    destruct (trie_get w pos) as [pw|] eqn:Hw; try discriminate.
  apply andb_true_iff in Huv as [Huv Hvu].
  apply andb_true_iff in Hvw as [Hvw Hwv].
  apply andb_true_iff. split; apply N.leb_le;
    apply N.leb_le in Huv; apply N.leb_le in Hvu;
    apply N.leb_le in Hvw; apply N.leb_le in Hwv; lia.
Qed.

Lemma dom_sizes_ok_parent : forall m pos sizes o v p,
  dom_sizes_ok m pos sizes o = true -> In v o -> trie_get v m = Some p ->
  dom_interval pos sizes p v = true.
Proof.
  intros m pos sizes o v p Hsizes Hin Hparent.
  unfold dom_sizes_ok in Hsizes. apply forallb_forall with (x := v) in Hsizes;
    [now rewrite Hparent in Hsizes|exact Hin].
Qed.

(** Parent interval checks imply interval inclusion along every ancestry chain. *)
Lemma dom_interval_ancestors : forall m pos sizes o,
  (forall v, In v o -> exists i, trie_get v pos = Some i) ->
  (forall v p, trie_get v m = Some p -> In p o) ->
  dom_sizes_ok m pos sizes o = true ->
  forall u v, tree_anc m u v -> In v o -> dom_interval pos sizes u v = true.
Proof.
  intros m pos sizes o Hpositions Hparents Hsizes u v Hanc.
  induction Hanc as [|p v Hparent Hanc IH]; intro Hin.
  - destruct (Hpositions u Hin) as [position Hposition].
    unfold dom_interval. rewrite Hposition, !N.leb_refl. reflexivity.
  - eapply dom_interval_trans; [apply IH; eapply Hparents; exact Hparent|].
    eapply dom_sizes_ok_parent; eassumption.
Qed.

(** A point at or beyond a subtree's upper endpoint cannot be its descendant. *)
Lemma dom_interval_high_not_ancestor : forall m pos sizes o u v pu pv,
  (forall x, In x o -> exists i, trie_get x pos = Some i) ->
  (forall x p, trie_get x m = Some p -> In p o) ->
  dom_sizes_ok m pos sizes o = true -> In v o ->
  trie_get u pos = Some pu -> trie_get v pos = Some pv ->
  (1 <= dom_size_get sizes v)%N -> (pu + dom_size_get sizes u <= pv)%N ->
  ~ tree_anc m u v.
Proof.
  intros m pos sizes o u v pu pv Hpositions Hparents Hsizes Hv Huget Hvget Hpositive Hhigh Hanc.
  pose proof (dom_interval_ancestors m pos sizes o Hpositions Hparents Hsizes u v Hanc Hv)
    as Hinterval.
  unfold dom_interval in Hinterval. rewrite Huget, Hvget in Hinterval.
  apply andb_true_iff in Hinterval as [_ Hend]. apply N.leb_le in Hend. lia.
Qed.


(** Optional folds cannot recover after a rejecting callback. *)
Local Lemma dom_optional_fold_none {A B : Type} (step : option B -> A -> option B) :
  (forall x, step None x = None) ->
  forall xs, fold_left step xs None = None.
Proof.
  intros Hnone xs. induction xs as [| x rest IH]; [reflexivity |].
  cbn [fold_left]. rewrite Hnone. exact IH.
Qed.

(** A successful optional fold has a successful callback at every input occurrence. *)
Local Lemma dom_optional_fold_entries {A B : Type} (step : option B -> A -> option B) :
  (forall x, step None x = None) ->
  forall xs initial result, fold_left step xs (Some initial) = Some result ->
  forall x, In x xs -> exists before after, step (Some before) x = Some after.
Proof.
  intros Hnone xs. induction xs as [| head rest IH]; intros initial result Hrun x Hin.
  - contradiction.
  - cbn [fold_left] in Hrun.
    destruct (step (Some initial) head) as [next |] eqn:Hstep.
    2: rewrite (dom_optional_fold_none step Hnone rest) in Hrun; discriminate Hrun.
    destruct Hin as [<- | Hin].
    + exists initial, next. exact Hstep.
    + eapply IH; eassumption.
Qed.

Local Lemma dom_optional_fold_preserves {A B : Type}
    (step : option B -> A -> option B) (Inv : B -> Prop) (Valid : A -> Prop) :
  (forall x, step None x = None) ->
  (forall x before after, Valid x -> Inv before ->
    step (Some before) x = Some after -> Inv after) ->
  forall xs initial result, Forall Valid xs -> Inv initial ->
    fold_left step xs (Some initial) = Some result -> Inv result.
Proof.
  intros Hnone Hstep xs. induction xs as [| x rest IH];
    intros initial result Hvalid Hinv Hrun.
  - cbn [fold_left] in Hrun. injection Hrun as Heq. now subst result.
  - inversion Hvalid as [| head tail Hx Hrest]; subst head tail.
    cbn [fold_left] in Hrun.
    destruct (step (Some initial) x) as [next |] eqn:Hnext.
    + eapply IH; [exact Hrest | | exact Hrun]. eapply Hstep; eassumption.
    + rewrite (dom_optional_fold_none step Hnone rest) in Hrun. discriminate Hrun.
Qed.

(** Every stored extreme is witnessed by a real processed incoming edge. *)
Local Definition dom_flag_valid g m (pos : ptrie N) o v direct lo hi : Prop :=
  (direct = true -> exists p, trie_get v m = Some p /\ edge (base g) p v) /\
  (exists u, In u o /\ edge (base g) u v /\ trie_get u pos = Some lo) /\
  exists w, In w o /\ edge (base g) w v /\ trie_get w pos = Some hi.

Local Definition dom_flags_valid g m pos o flags : Prop :=
  forall v direct lo hi, trie_get v flags = Some (direct, lo, hi) ->
    dom_flag_valid g m pos o v direct lo hi.

Local Lemma dom_flags_set : forall g m pos o flags v direct lo hi,
  dom_flags_valid g m pos o flags -> dom_flag_valid g m pos o v direct lo hi ->
  dom_flags_valid g m pos o (PTrieCode.set v (direct, lo, hi) flags).
Proof.
  intros g m pos o flags v direct lo hi Hflags Hnew q d l h Hget.
  destruct (Pos.eq_dec q v) as [Heq | Hneq].
  - subst q. rewrite PTrie.get_set_same in Hget. inversion Hget; subst. exact Hnew.
  - rewrite PTrie.get_set_other in Hget by exact Hneq. eapply Hflags. exact Hget.
Qed.

Local Lemma dom_flag_initial : forall g m pos o u v pu,
  In u o -> edge (base g) u v -> trie_get u pos = Some pu ->
  dom_flag_valid g m pos o v false pu pu.
Proof.
  intros g m pos o u v pu Hin Huv Hpu. split; [discriminate |].
  split; exists u; repeat split; assumption.
Qed.

Local Lemma dom_flag_merge : forall g m pos o u v p pu direct lo hi,
  In u o -> edge (base g) u v -> trie_get u pos = Some pu -> trie_get v m = Some p ->
  dom_flag_valid g m pos o v direct lo hi ->
  dom_flag_valid g m pos o v (direct || Pos.eqb u p) (N.min lo pu) (N.max hi pu).
Proof.
  intros g m pos o u v p pu direct lo hi Hin Huv Hpu Hparent
    [Hdirect [Hlo Hhi]].
  split.
  - intro Hnew. apply orb_true_iff in Hnew as [Hold | Hsame].
    + now apply Hdirect.
    + apply Pos.eqb_eq in Hsame. subst u. exists p. now split.
  - split.
    + destruct (N.le_ge_cases lo pu) as [Hle | Hle].
      * rewrite (N.min_l _ _ Hle). exact Hlo.
      * rewrite (N.min_r _ _ Hle). exists u. repeat split; assumption.
    + destruct (N.le_ge_cases hi pu) as [Hle | Hle].
      * rewrite (N.max_r _ _ Hle). exists u. repeat split; assumption.
      * rewrite (N.max_l _ _ Hle). exact Hhi.
Qed.

Local Lemma dom_edge_update_flags : forall g r m pos sizes o u v flags result,
  In u o -> edge (base g) u v -> dom_flags_valid g m pos o flags ->
  dom_edge_update r m pos sizes u (Some flags) v = Some result ->
  dom_flags_valid g m pos o result.
Proof.
  intros g r m pos sizes o u v flags result Hin Huv Hflags Hstep.
  unfold dom_edge_update in Hstep.
  destruct (trie_get u pos) as [pu |] eqn:Hpu; [| discriminate Hstep].
  destruct (trie_get v pos) as [pv |]; [| discriminate Hstep].
  destruct (Pos.eqb v r).
  - injection Hstep as Heq. now subst result.
  - destruct (trie_get v m) as [p |] eqn:Hparent; [| discriminate Hstep].
    destruct (dom_interval pos sizes p u); [| discriminate Hstep].
    destruct (trie_get v flags) as [[[direct lo] hi] |] eqn:Hprior.
    + injection Hstep as Heq. subst result. apply dom_flags_set; [exact Hflags |].
      eapply dom_flag_merge; try eassumption. eapply Hflags. exact Hprior.
    + injection Hstep as Heq. subst result. apply dom_flags_set; [exact Hflags |].
      exact (dom_flag_merge g m pos o u v p pu false pu pu Hin Huv Hpu Hparent
        (dom_flag_initial g m pos o u v pu Hin Huv Hpu)).
Qed.

Local Lemma dom_edges_from_none : forall g r m pos sizes u,
  dom_edges_from g r m pos sizes None u = None.
Proof.
  intros g r m pos sizes u. unfold dom_edges_from.
  apply dom_optional_fold_none. intro v. reflexivity.
Qed.

Local Lemma dom_edges_from_flags : forall g r m pos sizes o u flags result,
  In u o -> dom_flags_valid g m pos o flags ->
  dom_edges_from g r m pos sizes (Some flags) u = Some result ->
  dom_flags_valid g m pos o result.
Proof.
  intros g r m pos sizes o u flags result Hin Hflags Hrun.
  unfold dom_edges_from in Hrun.
  eapply (dom_optional_fold_preserves (dom_edge_update r m pos sizes u)
    (dom_flags_valid g m pos o) (edge (base g) u)); try eassumption.
  - intro v. reflexivity.
  - intros v before after Huv Hbefore Hstep. eapply dom_edge_update_flags; eassumption.
  - apply Forall_forall. intros v Huv. exact Huv.
Qed.

Local Lemma dom_edges_flags : forall g r m pos sizes o flags,
  fold_left (dom_edges_from g r m pos sizes) o (Some Empty) = Some flags ->
  dom_flags_valid g m pos o flags.
Proof.
  intros g r m pos sizes o flags Hrun.
  eapply (dom_optional_fold_preserves (dom_edges_from g r m pos sizes)
    (dom_flags_valid g m pos o) (fun u => In u o)); try eassumption.
  - apply dom_edges_from_none.
  - intros u before after Hin Hbefore Hstep. eapply dom_edges_from_flags; eassumption.
  - apply Forall_forall. intros u Hin. exact Hin.
  - intros v direct lo hi Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
Qed.

Local Lemma dom_edge_update_checked : forall r m pos sizes u v flags result,
  dom_edge_update r m pos sizes u (Some flags) v = Some result ->
  (exists pv, trie_get v pos = Some pv) /\
  (v = r \/ exists p, trie_get v m = Some p /\ dom_interval pos sizes p u = true).
Proof.
  intros r m pos sizes u v flags result Hstep. unfold dom_edge_update in Hstep.
  destruct (trie_get u pos) as [pu |]; [| discriminate Hstep].
  destruct (trie_get v pos) as [pv |] eqn:Hpv; [| discriminate Hstep].
  split; [now exists pv |]. destruct (Pos.eqb v r) eqn:Hroot.
  - left. now apply Pos.eqb_eq.
  - destruct (trie_get v m) as [p |] eqn:Hparent; [| discriminate Hstep].
    destruct (dom_interval pos sizes p u) eqn:Hinterval; [| discriminate Hstep].
    right. exists p. now split.
Qed.

Local Lemma dom_edges_checked : forall g r m pos sizes o flags,
  fold_left (dom_edges_from g r m pos sizes) o (Some Empty) = Some flags ->
  forall u v, In u o -> edge (base g) u v ->
    (exists pv, trie_get v pos = Some pv) /\
    (v = r \/ exists p, trie_get v m = Some p /\ dom_interval pos sizes p u = true).
Proof.
  intros g r m pos sizes o flags Hrun u v Hin Huv.
  destruct (dom_optional_fold_entries (dom_edges_from g r m pos sizes)
    (dom_edges_from_none g r m pos sizes) o Empty flags Hrun u Hin)
    as [before [after Hrow]].
  unfold dom_edges_from in Hrow.
  destruct (dom_optional_fold_entries (dom_edge_update r m pos sizes u)
    (fun x => eq_refl) (succs (base g) u) before after Hrow v Huv)
    as [flags0 [flags1 Hstep]].
  eapply dom_edge_update_checked. exact Hstep.
Qed.

(** Numeric positions recover the certificate's strict list order. *)
Local Lemma dom_positions_before : forall o u v pu pv,
  NoDup o -> trie_get u (dom_positions o) = Some pu ->
  trie_get v (dom_positions o) = Some pv -> (pu < pv)%N -> order_before o u v.
Proof.
  intros o u v pu pv Hunique Hu Hv Hlt.
  destruct (dom_positions_value o u pu Hunique Hu) as [i [Hi Hpu]].
  destruct (dom_positions_value o v pv Hunique Hv) as [j [Hj Hpv]].
  exists i, j. split; [exact Hi |]. split; [exact Hj |]. subst pu pv. lia.
Qed.

(** Accepted parent maps contain only ordered children and ordered parents. *)
Local Lemma dom_map_check_domain : forall g r m o,
  dom_map_check_known (dom_scan g) r m o = true ->
  forall v p, trie_get v m = Some p -> In v o /\ In p o.
Proof.
  intros g r m o Hcheck v p Hget.
  destruct (dom_map_check_structure g r m o Hcheck) as
    [_ [_ [Hroot [Hparents Hdomain]]]].
  pose proof (Hdomain v p Hget) as Hin. split; [exact Hin |].
  destruct (Pos.eq_dec v r) as [Heq | Hneq].
  - subst v. rewrite Hroot in Hget. discriminate Hget.
  - destruct (Hparents v Hin Hneq) as [parent [Hparent [i [j [Hi [Hj Hlt]]]]]].
    rewrite Hget in Hparent. injection Hparent as Heq. subst parent.
    eapply nth_error_In. exact Hi.
Qed.

(** Witness flags and parent containment establish the graph portions of a certificate. *)
Local Lemma dom_edges_certificate : forall g r m o sizes,
  NoDup o -> trie_get r m = None ->
  (forall v p, trie_get v m = Some p -> In v o /\ In p o) ->
  (forall v, In v o -> (1 <= dom_size_get sizes v)%N) ->
  dom_sizes_ok m (dom_positions o) sizes o = true ->
  (forall u v, In u o -> In v o ->
    dom_interval (dom_positions o) sizes u v = true -> tree_anc m u v) ->
  dom_edges g r m o (dom_positions o) sizes = true ->
  cert_parent (base g) m o /\ cert_low_high (base g) m o.
Proof.
  intros g r m o sizes Hunique Hroot Hdomain Hpositive Hsizes Hreflect Hedges.
  unfold dom_edges in Hedges.
  destruct (fold_left (dom_edges_from g r m (dom_positions o) sizes) o (Some Empty))
    as [flags |] eqn:Hrun; [| discriminate Hedges].
  pose proof (dom_edges_flags g r m (dom_positions o) sizes o flags Hrun) as Hflags.
  pose proof (dom_edges_checked g r m (dom_positions o) sizes o flags Hrun) as Hchecked.
  assert (Hpositioned : forall v, In v o -> exists i,
    trie_get v (dom_positions o) = Some i).
  { intros v Hin. now apply (proj2 (dom_positions_domain o v)). }
  assert (Hparents : forall v p, trie_get v m = Some p -> In p o).
  { intros v p Hget. exact (proj2 (Hdomain v p Hget)). }
  split.
  - intros u v Hin Huv.
    destruct (Hchecked u v Hin Huv) as [Hposition [Heq | [p [Hparent Hinterval]]]].
    + split; [now apply (proj1 (dom_positions_domain o v)) |].
      intros p Hget. subst v. rewrite Hroot in Hget. discriminate Hget.
    + split; [now apply (proj1 (dom_positions_domain o v)) |].
      intros q Hget. rewrite Hget in Hparent. injection Hparent as Heq. subst q.
      eapply Hreflect; [eapply Hparents; exact Hget | exact Hin | exact Hinterval].
  - intros v p Hget.
    destruct (Hdomain v p Hget) as [Hin Hpin].
    assert (Hneq : v <> r).
    { intro Heq. subst v. rewrite Hroot in Hget. discriminate Hget. }
    pose proof (proj1 (forallb_forall (dom_low_high r (dom_positions o) sizes flags) o)
      Hedges v Hin) as Hlowhigh.
    unfold dom_low_high in Hlowhigh.
    rewrite (proj2 (Pos.eqb_neq v r) Hneq) in Hlowhigh.
    destruct (trie_get v (dom_positions o)) as [pv |] eqn:Hpv;
      [| discriminate Hlowhigh].
    destruct (trie_get v flags) as [[[direct lo] hi] |] eqn:Hflag;
      [| discriminate Hlowhigh].
    destruct (Hflags v direct lo hi Hflag) as [Hdirect [Hlo Hhi]].
    apply orb_true_iff in Hlowhigh as [Hdirect_true | Hbounds].
    + left. destruct (Hdirect Hdirect_true) as [parent [Hparent Hedge]].
      rewrite Hget in Hparent. injection Hparent as Heq. now subst parent.
    + apply andb_true_iff in Hbounds as [Hlow Hhigh].
      apply N.ltb_lt in Hlow. apply N.leb_le in Hhigh.
      destruct Hlo as [u [Hu [Huv Hpu]]].
      destruct Hhi as [w [Hw [Hwv Hpw]]].
      right. exists u, w. split; [exact Hu |]. split; [exact Hw |].
      split; [exact Huv |]. split; [exact Hwv |]. split.
      * eapply dom_positions_before; eassumption.
      * split.
        -- eapply dom_positions_before; try eassumption.
           pose proof (Hpositive v Hin). lia.
        -- eapply dom_interval_high_not_ancestor; try eassumption.
           exact (Hpositive w Hw).
Qed.

(** Reversing the list reverses every strict position comparison. *)
Lemma dom_order_reverse : forall o u v,
  order_before o u v -> order_before (rev o) v u.
Proof.
  intros o u v [i [j [Hi [Hj Hij]]]].
  assert (Hi_bound : i < length o) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (Hj_bound : j < length o) by (apply nth_error_Some; rewrite Hj; discriminate).
  exists (length o - S j), (length o - S i). split.
  - rewrite nth_error_rev.
    rewrite (proj2 (Nat.ltb_lt (length o - S j) (length o)) ltac:(lia)).
    replace (length o - S (length o - S j)) with j by lia. exact Hj.
  - split.
    + rewrite nth_error_rev.
      rewrite (proj2 (Nat.ltb_lt (length o - S i) (length o)) ltac:(lia)).
      replace (length o - S (length o - S i)) with i by lia. exact Hi.
    + lia.
Qed.

Lemma dom_order_cut_index : forall (before : list positive) v after,
  nth_error (before ++ v :: after) (length before) = Some v.
Proof.
  intros before v after. rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma dom_order_before_cut : forall before v after u,
  NoDup (before ++ v :: after) -> order_before (before ++ v :: after) u v -> In u before.
Proof.
  intros before v after u Hunique [i [j [Hi [Hj Hij]]]].
  pose proof (dom_cert_position_nth _ Hunique j v Hj) as Hj_position.
  pose proof (dom_cert_position_nth _ Hunique (length before) v
    (dom_order_cut_index before v after)) as Hcut_position.
  assert (Hi_bound : i < length before) by lia.
  rewrite nth_error_app1 in Hi by exact Hi_bound. now apply nth_error_In in Hi.
Qed.

Lemma dom_order_after_cut : forall before v after u,
  NoDup (before ++ v :: after) -> order_before (before ++ v :: after) v u -> In u after.
Proof.
  intros before v after u Hunique [i [j [Hi [Hj Hij]]]].
  pose proof (dom_cert_position_nth _ Hunique i v Hi) as Hi_position.
  pose proof (dom_cert_position_nth _ Hunique (length before) v
    (dom_order_cut_index before v after)) as Hcut_position.
  assert (Hj_bound : length before < j) by lia.
  rewrite nth_error_app2 in Hj by lia.
  replace (j - length before) with (S (j - S (length before))) in Hj by lia.
  cbn [nth_error] in Hj. now apply nth_error_In in Hj.
Qed.

Lemma dom_order_cut_before : forall before v after u,
  In u before -> order_before (before ++ v :: after) u v.
Proof.
  intros before v after u Hin. apply In_nth_error in Hin as [i Hi].
  assert (Hbound : i < length before) by (apply nth_error_Some; rewrite Hi; discriminate).
  exists i, (length before). split.
  - now rewrite nth_error_app1.
  - split; [apply dom_order_cut_index|exact Hbound].
Qed.

Lemma dom_order_parent_wf : forall m o,
  NoDup o -> (forall v p, trie_get v m = Some p -> order_before o p v) ->
  well_founded (fun u v => trie_get v m = Some u).
Proof.
  intros m o Hunique Hparents. apply (well_founded_lt_compat positive (dom_cert_position o)).
  intros v p Hparent. apply dom_cert_before_positions; [exact Hunique|now apply Hparents].
Qed.

Lemma dom_order_anc_before : forall m o,
  NoDup o -> (forall v p, trie_get v m = Some p -> order_before o p v) ->
  forall u v, tree_anc m u v -> u <> v -> order_before o u v.
Proof.
  intros m o Hunique Hparents u v Hanc. induction Hanc as [|p v Hparent Hanc IH]; intro Hne.
  - contradiction.
  - pose proof (Hparents v p Hparent) as Hpv.
    destruct (Pos.eq_dec u p) as [->|Hup]; [exact Hpv|].
    eapply dom_cert_before_trans; [exact Hunique|now apply IH|exact Hpv].
Qed.

(** Ranked parent links decide ancestry constructively. *)
Lemma dom_order_anc_dec : forall m o,
  NoDup o -> (forall v p, trie_get v m = Some p -> order_before o p v) ->
  forall u v, {tree_anc m u v} + {~ tree_anc m u v}.
Proof.
  intros m o Hunique Hparents u.
  apply (well_founded_induction_type (dom_order_parent_wf m o Hunique Hparents)).
  intros v IH. destruct (Pos.eq_dec u v) as [->|Hne].
  - left. constructor.
  - destruct (trie_get v m) as [p|] eqn:Hget.
    + destruct (IH p eq_refl) as [Hanc|Hnot].
      * left. eapply tree_anc_step; eassumption.
      * right. intro Hanc. apply Hnot. eapply dom_cert_anc_parent; eassumption.
    + right. intro Hanc. apply dom_cert_anc_cases in Hanc.
      destruct Hanc as [Heq|[p [Hp Hanc]]]; congruence.
Qed.

Lemma dom_size_mass_app : forall weight xs ys sizes,
  dom_size_mass weight (xs ++ ys) sizes =
    (dom_size_mass weight xs sizes + dom_size_mass weight ys sizes)%N.
Proof.
  intros weight xs. induction xs as [|x rest IH]; intros ys sizes.
  - reflexivity.
  - change ((weight x * dom_size_get sizes x + dom_size_mass weight (rest ++ ys) sizes)%N =
      (weight x * dom_size_get sizes x + dom_size_mass weight rest sizes +
        dom_size_mass weight ys sizes)%N).
    rewrite IH. lia.
Qed.

Lemma dom_size_mass_rev : forall weight xs sizes,
  dom_size_mass weight (rev xs) sizes = dom_size_mass weight xs sizes.
Proof.
  intros weight xs. induction xs as [|x rest IH]; intro sizes; [reflexivity|].
  cbn [rev]. rewrite dom_size_mass_app, IH.
  change ((dom_size_mass weight rest sizes +
    (weight x * dom_size_get sizes x + 0))%N =
    (weight x * dom_size_get sizes x + dom_size_mass weight rest sizes)%N). lia.
Qed.

Lemma dom_size_mass_empty_count : forall (test : positive -> bool) xs,
  dom_size_mass (fun x => if test x then 1%N else 0%N) xs Empty =
    N.of_nat (length (filter test xs)).
Proof.
  intros test xs. induction xs as [|x rest IH]; [reflexivity|].
  change (((if test x then 1 else 0) * dom_size_get Empty x +
    dom_size_mass (fun y => if test y then 1 else 0) rest Empty)%N =
    N.of_nat (length (filter test (x :: rest)))).
  unfold dom_size_get. rewrite PTrie.get_empty, IH.
  cbn [filter]. destruct (test x).
  - change ((1 + N.of_nat (length (filter test rest)))%N =
      N.of_nat (S (length (filter test rest)))).
    rewrite Nat2N.inj_succ. lia.
  - change ((0 + N.of_nat (length (filter test rest)))%N =
      N.of_nat (length (filter test rest))). lia.
Qed.

Lemma dom_size_mass_zero : forall weight xs sizes,
  (forall x, In x xs -> weight x = 0%N) -> dom_size_mass weight xs sizes = 0%N.
Proof.
  intros weight xs. induction xs as [|x rest IH]; intros sizes Hzero; [reflexivity|].
  change ((weight x * dom_size_get sizes x + dom_size_mass weight rest sizes)%N = 0%N).
  rewrite (Hzero x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hin. apply Hzero. now right.
Qed.

(** A zero-weight root may be removed; every other processed cell transfers to its parent. *)
Lemma dom_size_fold_mass_cases : forall weight done remaining m sizes,
  NoDup (done ++ remaining) ->
  (forall before v after, done = before ++ v :: after ->
    match trie_get v m with
    | None => weight v = 0%N
    | Some p => In p (after ++ remaining) /\ weight v = weight p
    end) ->
  dom_size_mass weight remaining (fold_left (dom_add_size m) done sizes) =
    dom_size_mass weight (done ++ remaining) sizes.
Proof.
  intros weight done. induction done as [|v rest IH]; intros remaining m sizes Hunique Hparents.
  - reflexivity.
  - cbn [app] in Hunique. inversion Hunique as [|head tail Hfresh Hrest]; subst head tail.
    cbn [fold_left]. rewrite (IH remaining m (dom_add_size m sizes v) Hrest).
    + pose proof (Hparents [] v rest eq_refl) as Hparent.
      destruct (trie_get v m) as [p|] eqn:Hget.
      * destruct Hparent as [Hin Heq].
        exact (dom_size_mass_transfer weight (rest ++ remaining) m sizes v p Hrest Hget Hin Heq).
      * rewrite dom_size_mass_absent by (intros p Hbad; rewrite Hget in Hbad; discriminate).
        change (dom_size_mass weight (rest ++ remaining) sizes =
          (weight v * dom_size_get sizes v + dom_size_mass weight (rest ++ remaining) sizes)%N).
        now rewrite Hparent.
    + intros before u after Heq. apply (Hparents (v :: before) u after). cbn. now rewrite Heq.
Qed.

Lemma dom_subtree_parent_weights : forall m o v test u p,
  (forall x, In x o -> (test x = true <-> tree_anc m v x)) ->
  In u o -> In p o -> v <> u -> trie_get u m = Some p ->
  (if test u then 1%N else 0%N) = (if test p then 1%N else 0%N).
Proof.
  intros m o v test u p Hselected Hu Hp Hne Hparent.
  destruct (test u) eqn:Hut; destruct (test p) eqn:Hpt; try reflexivity.
  - assert (Hanc : tree_anc m v u) by (apply (proj1 (Hselected u Hu)); exact Hut).
    pose proof (dom_cert_anc_parent m v u p Hparent Hanc Hne) as Hparanc.
    apply (proj2 (Hselected p Hp)) in Hparanc. congruence.
  - assert (Hanc : tree_anc m v p) by (apply (proj1 (Hselected p Hp)); exact Hpt).
    assert (Hchild : tree_anc m v u) by (eapply tree_anc_step; eassumption).
    apply (proj2 (Hselected u Hu)) in Hchild. congruence.
Qed.

Lemma dom_subtree_root_weight : forall m o v test u,
  (forall x, In x o -> (test x = true <-> tree_anc m v x)) ->
  In u o -> v <> u -> trie_get u m = None -> (if test u then 1%N else 0%N) = 0%N.
Proof.
  intros m o v test u Hselected Hu Hne Hnone. destruct (test u) eqn:Htest; [|reflexivity].
  assert (Hanc : tree_anc m v u) by (apply (proj1 (Hselected u Hu)); exact Htest).
  destruct (dom_cert_anc_cases m v u Hanc) as [Heq|[p [Hparent Hancp]]]; congruence.
Qed.

(** Before a vertex is processed, all descendant mass stays among the remaining cells. *)
Lemma dom_subtree_suffix_parents : forall m o v test before after,
  NoDup o -> (forall u p, trie_get u m = Some p -> order_before o p u) ->
  o = before ++ v :: after ->
  (forall x, In x o -> (test x = true <-> tree_anc m v x)) ->
  forall prefix u suffix, rev after = prefix ++ u :: suffix ->
    match trie_get u m with
    | None => (if test u then 1%N else 0%N) = 0%N
    | Some p => In p (suffix ++ v :: rev before) /\
        (if test u then 1%N else 0%N) = (if test p then 1%N else 0%N)
    end.
Proof.
  intros m o v test before after Hunique Hparents Ho Hselected prefix u suffix Hcut.
  assert (Hafter : In u after).
  { apply (proj2 (in_rev after u)). rewrite Hcut. apply in_or_app. now right; left. }
  assert (Hu : In u o) by (rewrite Ho; apply in_or_app; right; now right).
  assert (Hne : v <> u).
  { intro Heq. subst u. apply (NoDup_remove_2 before after v).
    - now rewrite <- Ho.
    - apply in_or_app. now right. }
  destruct (trie_get u m) as [p|] eqn:Hparent.
  - pose proof (Hparents u p Hparent) as Hbefore.
    pose proof (proj1 (dom_cert_before_members o p u Hbefore)) as Hp.
    split.
    + assert (Hwhole : rev o = prefix ++ u :: (suffix ++ v :: rev before)).
      { rewrite Ho, rev_app_distr. cbn [rev]. rewrite <- app_assoc.
        rewrite Hcut, <- app_assoc. reflexivity. }
      apply (dom_order_after_cut prefix u (suffix ++ v :: rev before) p).
      * rewrite <- Hwhole. now apply NoDup_rev.
      * rewrite <- Hwhole. now apply dom_order_reverse.
    + exact (dom_subtree_parent_weights m o v test u p Hselected Hu Hp Hne Hparent).
  - exact (dom_subtree_root_weight m o v test u Hselected Hu Hne Hparent).
Qed.

Lemma dom_subtree_prefix_zero : forall m o v test before after,
  NoDup o -> (forall u p, trie_get u m = Some p -> order_before o p u) ->
  o = before ++ v :: after ->
  (forall x, In x o -> (test x = true <-> tree_anc m v x)) ->
  forall x, In x (rev before) -> (if test x then 1%N else 0%N) = 0%N.
Proof.
  intros m o v test before after Hunique Hparents Ho Hselected x Hin.
  assert (Hx_before : order_before o x v).
  { rewrite Ho. apply dom_order_cut_before. now apply (proj2 (in_rev before x)). }
  assert (Hx : In x o) by (exact (proj1 (dom_cert_before_members o x v Hx_before))).
  pose proof (dom_cert_before_positions o x v Hunique Hx_before) as Hx_position.
  destruct (test x) eqn:Htest; [|reflexivity].
  assert (Hanc : tree_anc m v x) by (apply (proj1 (Hselected x Hx)); exact Htest).
  assert (Hne : v <> x) by (intro Heq; subst x; lia).
  pose proof (dom_order_anc_before m o Hunique Hparents v x Hanc Hne) as Hv_before.
  pose proof (dom_cert_before_positions o v x Hunique Hv_before). lia.
Qed.

(** A vertex's value is final once the reverse traversal reaches it. *)
Lemma dom_sizes_at_cut : forall m o before v after,
  NoDup o -> (forall u p, trie_get u m = Some p -> order_before o p u) ->
  o = before ++ v :: after ->
  dom_size_get (dom_sizes m o) v =
    dom_size_get (fold_left (dom_add_size m) (rev after) Empty) v.
Proof.
  intros m o before v after Hunique Hparents Ho.
  assert (Hrev : rev_append o [] = rev after ++ v :: rev before).
  { rewrite rev_append_rev, app_nil_r, Ho, rev_app_distr. cbn [rev].
    now rewrite <- app_assoc. }
  unfold dom_sizes. rewrite Hrev, fold_left_app. cbn [fold_left].
  rewrite dom_size_fold_preserves.
  - rewrite dom_add_size_value. destruct (trie_get v m) as [p|] eqn:Hparent;
      [|reflexivity].
    destruct (Pos.eqb v p) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq. subst p.
    pose proof (dom_cert_before_positions o v v Hunique (Hparents v v Hparent)). lia.
  - intros u Hin Hparent. apply (proj2 (in_rev before u)) in Hin.
    assert (Hbefore : order_before o u v) by (rewrite Ho; now apply dom_order_cut_before).
    pose proof (dom_cert_before_positions o u v Hunique Hbefore).
    pose proof (dom_cert_before_positions o v u Hunique (Hparents u v Hparent)). lia.
Qed.

(** Reverse aggregation counts exactly the descendants selected from the original order. *)
Lemma dom_sizes_cardinality : forall m o v (test : positive -> bool),
  NoDup o -> (forall u p, trie_get u m = Some p -> order_before o p u) -> In v o ->
  (forall x, In x o -> (test x = true <-> tree_anc m v x)) ->
  dom_size_get (dom_sizes m o) v = N.of_nat (length (filter test o)).
Proof.
  intros m o v test Hunique Hparents Hv Hselected.
  destruct (in_split v o Hv) as [before [after Ho]].
  assert (Hrev : rev o = rev after ++ v :: rev before).
  { rewrite Ho, rev_app_distr. cbn [rev]. now rewrite <- app_assoc. }
  assert (Hrev_unique : NoDup (rev after ++ v :: rev before)).
  { rewrite <- Hrev. now apply NoDup_rev. }
  pose proof (dom_size_fold_mass_cases (fun x => if test x then 1%N else 0%N)
    (rev after) (v :: rev before) m Empty Hrev_unique
    (dom_subtree_suffix_parents m o v test before after Hunique Hparents Ho Hselected))
    as Hmass.
  rewrite <- Hrev, dom_size_mass_rev, dom_size_mass_empty_count in Hmass.
  assert (Htest : test v = true) by (apply (proj2 (Hselected v Hv)); constructor).
  rewrite (dom_sizes_at_cut m o before v after Hunique Hparents Ho).
  change (((if test v then 1 else 0) *
    dom_size_get (fold_left (dom_add_size m) (rev after) Empty) v +
    dom_size_mass (fun x => if test x then 1 else 0) (rev before)
      (fold_left (dom_add_size m) (rev after) Empty))%N =
    N.of_nat (length (filter test o))) in Hmass.
  rewrite Htest, dom_size_mass_zero in Hmass.
  - now rewrite N.mul_1_l, N.add_0_r in Hmass.
  - exact (dom_subtree_prefix_zero m o v test before after Hunique Hparents Ho Hselected).
Qed.


Local Lemma dom_nat_N_le : forall a b, a <= b <-> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intros a b. symmetry. unfold N.le. rewrite <- Nat2N.inj_compare. apply Nat.compare_le_iff.
Qed.

Local Lemma dom_nat_N_lt : forall a b, a < b <-> (N.of_nat a < N.of_nat b)%N.
Proof.
  intros a b. symmetry. unfold N.lt. rewrite <- Nat2N.inj_compare. apply Nat.compare_lt_iff.
Qed.

Lemma dom_positions_rank : forall o v,
  NoDup o -> In v o -> trie_get v (dom_positions o) = Some (N.of_nat (dom_cert_position o v)).
Proof.
  intros o v Hunique Hin. apply In_nth_error in Hin as [i Hi].
  rewrite (dom_cert_position_nth o Hunique i v Hi). now apply dom_positions_nth.
Qed.

Lemma dom_rank_map_distinct : forall o xs,
  NoDup o -> NoDup xs -> incl xs o -> NoDup (map (dom_cert_position o) xs).
Proof.
  intros o xs Hunique Hdistinct. revert xs Hdistinct.
  intros xs Hdistinct. induction Hdistinct as [|x rest Hfresh Hdistinct IH]; intro Hincl.
  - constructor.
  - cbn [map]. constructor.
    + intro Hin. apply in_map_iff in Hin as [y [Heq Hy]].
      assert (Hsame : y = x).
      { apply (dom_cert_positions_eq o y x Hunique); [apply Hincl; now right|apply Hincl; now left|].
        exact Heq. }
      subst y. contradiction.
    + apply IH. intros y Hy. apply Hincl. now right.
Qed.

Lemma dom_sizes_ancestry_interval : forall m o,
  (forall v p, trie_get v m = Some p -> order_before o p v) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true ->
  forall u v, tree_anc m u v -> In v o ->
  dom_interval (dom_positions o) (dom_sizes m o) u v = true.
Proof.
  intros m o Hparents Hsizes u v Hanc Hv.
  eapply dom_interval_ancestors; [| |exact Hsizes|exact Hanc|exact Hv].
  - intros x Hx. now apply (proj2 (dom_positions_domain o x)).
  - intros x p Hparent. exact (proj1 (dom_cert_before_members o p x (Hparents x p Hparent))).
Qed.

Lemma dom_sizes_ancestry_point : forall m o u v,
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true ->
  In u o -> In v o -> tree_anc m u v ->
  (N.of_nat (dom_cert_position o u) <= N.of_nat (dom_cert_position o v) /\
   N.of_nat (dom_cert_position o v) <
     N.of_nat (dom_cert_position o u) + dom_size_get (dom_sizes m o) u)%N.
Proof.
  intros m o u v Hunique Hparents Hsizes Hu Hv Hanc.
  pose proof (dom_sizes_ancestry_interval m o Hparents Hsizes u v Hanc Hv) as Hinterval.
  unfold dom_interval in Hinterval.
  rewrite (dom_positions_rank o u Hunique Hu), (dom_positions_rank o v Hunique Hv) in Hinterval.
  apply andb_true_iff in Hinterval as [Hstart Hend].
  apply N.leb_le in Hstart. apply N.leb_le in Hend.
  pose proof (dom_sizes_positive m o v). split; [exact Hstart|lia].
Qed.

(** Distinct descendants fill every integer position in their subtree's half-open interval. *)
Lemma dom_sizes_cover_positions : forall m o u (test : positive -> bool),
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true -> In u o ->
  (forall x, In x o -> (test x = true <-> tree_anc m u x)) ->
  incl (seq (dom_cert_position o u) (length (filter test o)))
    (map (dom_cert_position o) (filter test o)).
Proof.
  intros m o u test Hunique Hparents Hsizes Hu Hselected.
  pose proof (dom_sizes_cardinality m o u test Hunique Hparents Hu Hselected) as Hcount.
  apply NoDup_length_incl.
  - apply dom_rank_map_distinct; [exact Hunique|now apply NoDup_filter|].
    intros x Hx. now apply filter_In in Hx as [Hx Htest].
  - rewrite length_seq, length_map. lia.
  - intros i Hin. apply in_map_iff in Hin as [x [<- Hx]].
    apply filter_In in Hx as [Hx Htest].
    pose proof (dom_sizes_ancestry_point m o u x Hunique Hparents Hsizes Hu Hx
      (proj1 (Hselected x Hx) Htest)) as [Hlow Hhigh].
    rewrite Hcount, <- Nat2N.inj_add in Hhigh.
    apply dom_nat_N_le in Hlow. apply dom_nat_N_lt in Hhigh.
    apply in_seq. split; assumption.
Qed.

(** Point coverage is exactly ancestry, using sizes computed by reverse aggregation. *)
Lemma dom_sizes_point_anc : forall m o u v,
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true -> In u o -> In v o ->
  (tree_anc m u v <->
    (N.of_nat (dom_cert_position o u) <= N.of_nat (dom_cert_position o v) /\
     N.of_nat (dom_cert_position o v) <
       N.of_nat (dom_cert_position o u) + dom_size_get (dom_sizes m o) u)%N).
Proof.
  intros m o u v Hunique Hparents Hsizes Hu Hv. split.
  - now apply dom_sizes_ancestry_point.
  - intros [Hlow Hhigh].
    set (test := fun x => if dom_order_anc_dec m o Hunique Hparents u x then true else false).
    assert (Hselected : forall x, In x o -> (test x = true <-> tree_anc m u x)).
    { intros x Hx. unfold test. destruct (dom_order_anc_dec m o Hunique Hparents u x);
        split; intro H; try assumption; try reflexivity; try discriminate; contradiction. }
    pose proof (dom_sizes_cardinality m o u test Hunique Hparents Hu Hselected) as Hcount.
    pose proof (dom_sizes_cover_positions m o u test Hunique Hparents Hsizes Hu Hselected) as Hcover.
    rewrite Hcount, <- Nat2N.inj_add in Hhigh.
    apply dom_nat_N_le in Hlow. apply dom_nat_N_lt in Hhigh.
    assert (Hin : In (dom_cert_position o v)
      (map (dom_cert_position o) (filter test o))).
    { apply Hcover, in_seq. split; assumption. }
    apply in_map_iff in Hin as [x [Heq Hx]]. apply filter_In in Hx as [Hx Htest].
    assert (Hsame : x = v) by (eapply dom_cert_positions_eq; eassumption).
    subst x. now apply (proj1 (Hselected v Hv)).
Qed.

(** Full interval inclusion and ancestry agree for every pair of listed vertices. *)
Lemma dom_sizes_interval_anc : forall m o u v,
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true -> In u o -> In v o ->
  (dom_interval (dom_positions o) (dom_sizes m o) u v = true <-> tree_anc m u v).
Proof.
  intros m o u v Hunique Hparents Hsizes Hu Hv. split.
  - intro Hinterval. apply (proj2 (dom_sizes_point_anc m o u v Hunique Hparents Hsizes Hu Hv)).
    unfold dom_interval in Hinterval.
    rewrite (dom_positions_rank o u Hunique Hu), (dom_positions_rank o v Hunique Hv) in Hinterval.
    apply andb_true_iff in Hinterval as [Hstart Hend].
    apply N.leb_le in Hstart. apply N.leb_le in Hend.
    pose proof (dom_sizes_positive m o v). split; [exact Hstart|lia].
  - intro Hanc. now apply dom_sizes_ancestry_interval.
Qed.

(** The accepted parent intervals make the supplied order a contiguous tree preorder. *)
Lemma dom_sizes_preorder : forall r m o,
  NoDup o -> hd_error o = Some r -> trie_get r m = None ->
  (forall v, In v o -> v <> r -> exists p, trie_get v m = Some p /\ order_before o p v) ->
  (forall v p, trie_get v m = Some p -> In v o) ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true -> cert_preorder r m o.
Proof.
  intros r m o Hunique Hhead Hroot Hparents Hdomain Hsizes.
  assert (Hordered : forall v p, trie_get v m = Some p -> order_before o p v).
  { intros v p Hparent. assert (Hv : In v o) by (eapply Hdomain; exact Hparent).
    assert (Hne : v <> r) by (intro Heq; subst v; congruence).
    destruct (Hparents v Hv Hne) as [q [Hq Hbefore]].
    rewrite Hparent in Hq. injection Hq as <-. exact Hbefore. }
  split; [exact Hunique|]. split; [exact Hhead|]. split; [exact Hroot|].
  split; [exact Hparents|]. split; [exact Hdomain|].
  intros u v w Hanc Huv Hvw.
  destruct (dom_cert_before_members o u v Huv) as [Hu Hv].
  destruct (dom_cert_before_members o v w Hvw) as [_ Hw].
  pose proof (proj1 (dom_sizes_point_anc m o u w Hunique Hordered Hsizes Hu Hw) Hanc)
    as [Hlow Hhigh].
  pose proof (dom_cert_before_positions o u v Hunique Huv) as Huv_position.
  pose proof (dom_cert_before_positions o v w Hunique Hvw) as Hvw_position.
  apply dom_nat_N_lt in Huv_position. apply dom_nat_N_lt in Hvw_position.
  apply (proj2 (dom_sizes_point_anc m o u v Hunique Hordered Hsizes Hu Hv)). split; lia.
Qed.

(** All descendants follow their header, so its endpoint stays within the supplied order. *)
Lemma dom_sizes_end_bound : forall m o v,
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) -> In v o ->
  (N.of_nat (dom_cert_position o v) + dom_size_get (dom_sizes m o) v <=
    N.of_nat (length o))%N.
Proof.
  intros m o v Hunique Hparents Hv.
  set (test := fun x => if dom_order_anc_dec m o Hunique Hparents v x then true else false).
  assert (Hselected : forall x, In x o -> (test x = true <-> tree_anc m v x)).
  { intros x Hx. unfold test. destruct (dom_order_anc_dec m o Hunique Hparents v x);
      split; intro H; try assumption; try reflexivity; try discriminate; contradiction. }
  pose proof (dom_sizes_cardinality m o v test Hunique Hparents Hv Hselected) as Hcount.
  destruct (in_split v o Hv) as [before [after Ho]].
  assert (Hsubset : incl (filter test o) (v :: after)).
  { intros x Hx. apply filter_In in Hx as [Hx Htest].
    destruct (Pos.eq_dec x v) as [->|Hne]; [now left|].
    right. apply (dom_order_after_cut before v after x).
    - now rewrite <- Ho.
    - rewrite <- Ho. apply (dom_order_anc_before m o Hunique Hparents v x);
        [now apply (proj1 (Hselected x Hx))|congruence]. }
  pose proof (@NoDup_incl_length positive (filter test o) (v :: after)
    (@NoDup_filter positive test o Hunique) Hsubset) as Hlength.
  assert (Hposition : dom_cert_position o v = length before).
  { apply (dom_cert_position_nth o Hunique (length before) v).
    rewrite Ho. apply dom_order_cut_index. }
  assert (Htotal : length o = length before + S (length after)).
  { rewrite Ho, length_app. reflexivity. }
  rewrite Hposition, Hcount, Htotal. cbn [length] in Hlength.
  rewrite <- Nat2N.inj_add. apply dom_nat_N_le. lia.
Qed.

Lemma dom_sizes_position_end_bound : forall m o v i,
  NoDup o -> (forall x p, trie_get x m = Some p -> order_before o p x) ->
  trie_get v (dom_positions o) = Some i ->
  (i + dom_size_get (dom_sizes m o) v <= N.of_nat (length o))%N.
Proof.
  intros m o v i Hunique Hparents Hget.
  assert (Hv : In v o) by (apply (proj1 (dom_positions_domain o v)); now exists i).
  pose proof (dom_positions_rank o v Hunique Hv) as Hrank.
  rewrite Hget in Hrank. injection Hrank as ->. now apply dom_sizes_end_bound.
Qed.


Lemma dom_preorder_parent_before : forall r m o,
  cert_preorder r m o -> forall v p, trie_get v m = Some p -> order_before o p v.
Proof.
  intros r m o [_ [_ [Hroot [Hparents [Hdomain Hcontiguous]]]]] v p Hparent.
  assert (Hv : In v o) by (eapply Hdomain; exact Hparent).
  assert (Hne : v <> r) by (intro Heq; subst v; congruence).
  destruct (Hparents v Hv Hne) as [q [Hq Hbefore]].
  rewrite Hparent in Hq. injection Hq as <-. exact Hbefore.
Qed.

Lemma dom_preorder_between_ancestor : forall r m o u w i x,
  cert_preorder r m o -> In u o -> In w o -> tree_anc m u w ->
  nth_error o i = Some x -> dom_cert_position o u <= i -> i <= dom_cert_position o w ->
  tree_anc m u x.
Proof.
  intros r m o u w i x [Hunique [_ [_ [_ [_ Hcontiguous]]]]] Hu Hw Hanc Hnth Hlo Hhi.
  assert (Hx : In x o) by (eapply nth_error_In; exact Hnth).
  pose proof (dom_cert_position_nth o Hunique i x Hnth) as Hposition.
  destruct (Nat.eq_dec i (dom_cert_position o u)) as [Heq|Hne].
  - assert (Hsame : x = u) by (eapply dom_cert_positions_eq; eassumption || lia).
    subst x. constructor.
  - destruct (Nat.eq_dec i (dom_cert_position o w)) as [Heq|Hne'].
    + assert (Hsame : x = w) by (eapply dom_cert_positions_eq; eassumption || lia).
      now subst x.
    + apply (Hcontiguous u x w Hanc).
      * apply dom_cert_positions_before; try assumption; lia.
      * apply dom_cert_positions_before; try assumption; lia.
Qed.

(** Contiguity bounds each descendant by the cardinality of its header's subtree. *)
Lemma dom_preorder_ancestry_point : forall r m o u v,
  cert_preorder r m o -> In u o -> In v o -> tree_anc m u v ->
  (N.of_nat (dom_cert_position o u) <= N.of_nat (dom_cert_position o v) /\
   N.of_nat (dom_cert_position o v) <
     N.of_nat (dom_cert_position o u) + dom_size_get (dom_sizes m o) u)%N.
Proof.
  intros r m o u v Hpre Hu Hv Hanc.
  pose proof (proj1 Hpre) as Hunique.
  pose proof (dom_preorder_parent_before r m o Hpre) as Hparents.
  assert (Hstart : dom_cert_position o u <= dom_cert_position o v).
  { destruct (Pos.eq_dec u v) as [->|Hne]; [lia|].
    pose proof (dom_order_anc_before m o Hunique Hparents u v Hanc Hne) as Hbefore.
    pose proof (dom_cert_before_positions o u v Hunique Hbefore). lia. }
  set (test := fun x => if dom_order_anc_dec m o Hunique Hparents u x then true else false).
  assert (Hselected : forall x, In x o -> (test x = true <-> tree_anc m u x)).
  { intros x Hx. unfold test. destruct (dom_order_anc_dec m o Hunique Hparents u x);
      split; intro H; try assumption; try reflexivity; try discriminate; contradiction. }
  pose proof (dom_sizes_cardinality m o u test Hunique Hparents Hu Hselected) as Hcount.
  assert (Hrange : incl (seq (dom_cert_position o u)
    (S (dom_cert_position o v) - dom_cert_position o u))
    (map (dom_cert_position o) (filter test o))).
  { intros i Hin. apply in_seq in Hin as [Hlow Hhigh].
    pose proof (dom_cert_position_bound o v Hunique Hv) as Hv_bound.
    destruct (nth_error o i) as [x|] eqn:Hnth.
    - assert (Hx : In x o) by (eapply nth_error_In; exact Hnth).
      apply in_map_iff. exists x. split; [now apply dom_cert_position_nth|].
      apply filter_In. split; [exact Hx|]. apply (proj2 (Hselected x Hx)).
      exact (dom_preorder_between_ancestor r m o u v i x Hpre Hu Hv Hanc Hnth Hlow ltac:(lia)).
    - exfalso. apply nth_error_None in Hnth. lia. }
  assert (Hrange_unique : NoDup (seq (dom_cert_position o u)
    (S (dom_cert_position o v) - dom_cert_position o u))) by apply seq_NoDup.
  pose proof (@NoDup_incl_length nat _ _ Hrange_unique Hrange) as Hlength.
  rewrite length_seq, length_map in Hlength.
  split; [now apply dom_nat_N_le|].
  rewrite Hcount, <- Nat2N.inj_add. apply dom_nat_N_lt. lia.
Qed.

(** A contained descendant set cannot extend beyond its ancestor's contiguous interval. *)
Lemma dom_preorder_ancestry_interval : forall r m o u v,
  cert_preorder r m o -> In u o -> In v o -> tree_anc m u v ->
  dom_interval (dom_positions o) (dom_sizes m o) u v = true.
Proof.
  intros r m o u v Hpre Hu Hv Hanc.
  pose proof (proj1 Hpre) as Hunique.
  pose proof (dom_preorder_parent_before r m o Hpre) as Hparents.
  pose proof (dom_preorder_ancestry_point r m o u v Hpre Hu Hv Hanc) as [Hstart Hinside].
  set (test := fun x => if dom_order_anc_dec m o Hunique Hparents v x then true else false).
  assert (Hselected : forall x, In x o -> (test x = true <-> tree_anc m v x)).
  { intros x Hx. unfold test. destruct (dom_order_anc_dec m o Hunique Hparents v x);
      split; intro H; try assumption; try reflexivity; try discriminate; contradiction. }
  pose proof (dom_sizes_cardinality m o v test Hunique Hparents Hv Hselected) as Hcount.
  set (stop := dom_cert_position o u + N.to_nat (dom_size_get (dom_sizes m o) u)).
  assert (Hstop : dom_cert_position o v < stop).
  { unfold stop. apply dom_nat_N_lt. rewrite Nat2N.inj_add, N2Nat.id. exact Hinside. }
  assert (Hsubset : incl (map (dom_cert_position o) (filter test o))
    (seq (dom_cert_position o v) (stop - dom_cert_position o v))).
  { intros i Hin. apply in_map_iff in Hin as [x [<- Hx]].
    apply filter_In in Hx as [Hx Htest].
    pose proof (proj1 (Hselected x Hx) Htest) as Hvx.
    assert (Hux : tree_anc m u x) by (eapply dom_cert_anc_trans; eassumption).
    pose proof (dom_preorder_ancestry_point r m o v x Hpre Hv Hx Hvx) as [Hlow _].
    pose proof (dom_preorder_ancestry_point r m o u x Hpre Hu Hx Hux) as [_ Hhigh].
    assert (Hend : dom_cert_position o x < stop).
    { unfold stop. apply dom_nat_N_lt. rewrite Nat2N.inj_add, N2Nat.id. exact Hhigh. }
    apply dom_nat_N_le in Hlow. apply in_seq. split; lia. }
  assert (Hdistinct : NoDup (map (dom_cert_position o) (filter test o))).
  { apply dom_rank_map_distinct; [exact Hunique|now apply NoDup_filter|].
    intros x Hx. now apply filter_In in Hx as [Hx Htest]. }
  pose proof (@NoDup_incl_length nat _ _ Hdistinct Hsubset) as Hlength.
  rewrite length_map, length_seq in Hlength.
  assert (Hends : dom_cert_position o v + length (filter test o) <= stop) by lia.
  apply dom_nat_N_le in Hends. unfold stop in Hends.
  rewrite !Nat2N.inj_add, N2Nat.id, <- Hcount in Hends.
  unfold dom_interval. rewrite (dom_positions_rank o u Hunique Hu),
    (dom_positions_rank o v Hunique Hv).
  apply andb_true_iff. split; apply N.leb_le; assumption.
Qed.

(** Every semantic tree preorder passes the computed parent-interval checks. *)
Lemma dom_preorder_sizes_ok : forall r m o, cert_preorder r m o ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true.
Proof.
  intros r m o Hpre. unfold dom_sizes_ok. apply forallb_forall. intros v Hv.
  destruct (trie_get v m) as [p|] eqn:Hparent; [|reflexivity].
  pose proof (dom_preorder_parent_before r m o Hpre v p Hparent) as Hbefore.
  pose proof (proj1 (dom_cert_before_members o p v Hbefore)) as Hp.
  apply (dom_preorder_ancestry_interval r m o p v Hpre Hp Hv).
  eapply tree_anc_step; [exact Hparent|constructor].
Qed.

Lemma dom_cert_sizes_ok : forall g r m o, dom_cert g r m o ->
  dom_sizes_ok m (dom_positions o) (dom_sizes m o) o = true.
Proof.
  intros g r m o Hcert. exact (dom_preorder_sizes_ok r m o (proj1 Hcert)).
Qed.


(** The original phase composition specifies the checker independently of order reuse. *)
Local Definition dom_check_spec (g : prepared) (r : positive) (m : ptrie positive)
    (o : list positive) : bool :=
  let info := dom_scan g in
  match dom_read_known info r o with
  | None => false
  | Some pos =>
    if dom_map_check_known info r m o then
      let sizes := dom_sizes m o in
      dom_sizes_ok m pos sizes o && dom_edges g r m o pos sizes
    else false
  end.

Module DomCode <: DOM_OPS.
  Definition build := dom_build_candidate.

  Definition check (g : prepared) (r : positive) (m : ptrie positive)
      (o : list positive) : bool :=
    let info := dom_scan g in
    match dom_read_known info r o with
    | None => false
    | Some pos =>
      if dom_map_check_pos info r m o pos then
        let sizes := dom_sizes m o in
        dom_sizes_ok m pos sizes o && dom_edges g r m o pos sizes
      else false
    end.

  Definition tree (g : prepared) (r : positive) (m : ptrie positive)
      (o : list positive) : domtree :=
      let pos := dom_positions o in
      let sizes := dom_sizes m o in
      let children := fold_left (fun rows v => match trie_get v m with
        | None => rows
        | Some p => let old := match trie_get p rows with None => [] | Some vs => vs end in
            PTrieCode.set p (v :: old) rows
        end) o Empty in
      let ends := fold_left (fun ends v => match trie_get v pos with
        | None => ends
        | Some pv => PTrieCode.set v (N.pred (N.add pv (dom_size_get sizes v))) ends
        end) o Empty in
      DomTree m (PTrieCode.map (fun vs => rev_append vs []) children) pos ends.

  Definition dominates_b (t : domtree) (u v : positive) : bool :=
    match trie_get u (pre t), trie_get u (post t),
        trie_get v (pre t), trie_get v (post t) with
    | Some a, Some b, Some c, Some d => N.leb a c && N.leb d b
    | _, _, _, _ => false
    end.
End DomCode.

(** Reading the order once preserves acceptance for every candidate. *)
Local Lemma dom_check_agrees : forall g r m o,
  DomCode.check g r m o = dom_check_spec g r m o.
Proof.
  intros g r m o. unfold DomCode.check, dom_check_spec.
  destruct (dom_read_known (dom_scan g) r o) as [pos|] eqn:Hread; [|reflexivity].
  now rewrite (dom_map_check_known_pos (dom_scan g) r m o pos Hread).
Qed.

(** All accepted phases combine into the semantic low-high certificate. *)
Local Lemma dom_check_certificate : forall g r m o,
  DomCode.check g r m o = true -> dom_cert (base g) r m o.
Proof.
  intros g r m o Hcheck. rewrite dom_check_agrees in Hcheck.
  unfold dom_check_spec in Hcheck.
  destruct (dom_read_known (dom_scan g) r o) as [pos |] eqn:Hread;
    [| discriminate Hcheck].
  destruct (dom_map_check_known (dom_scan g) r m o) eqn:Hmap;
    [| discriminate Hcheck].
  apply andb_true_iff in Hcheck as [Hsizes Hedges].
  pose proof (dom_read_known_positions (dom_scan g) r o pos Hread) as Hpositions.
  subst pos.
  destruct (dom_map_check_structure g r m o Hmap) as
    [Hunique [Hhead [Hroot [Hparents Hdomain]]]].
  assert (Hordered : forall v p, trie_get v m = Some p -> order_before o p v).
  { intros v p Hparent. pose proof (Hdomain v p Hparent) as Hv.
    assert (Hneq : v <> r) by (intro Heq; subst v; congruence).
    destruct (Hparents v Hv Hneq) as [q [Hq Hbefore]].
    rewrite Hparent in Hq. injection Hq as Heq. now subst q. }
  split.
  - eapply dom_sizes_preorder; eassumption.
  - apply (dom_edges_certificate g r m o (dom_sizes m o) Hunique Hroot
      (dom_map_check_domain g r m o Hmap)).
    + intros v _. apply dom_sizes_positive.
    + exact Hsizes.
    + intros u v Hu Hv Hinterval.
      exact (proj1 (dom_sizes_interval_anc m o u v Hunique Hordered Hsizes Hu Hv) Hinterval).
    + exact Hedges.
Qed.

(** Child grouping is stable filtering by the parent map. *)
Local Definition dom_child_matches (m : ptrie positive) (p v : positive) : bool :=
  match trie_get v m with Some parent => Pos.eqb p parent | None => false end.
TimeFun dom_child_matches.

Local Definition dom_child_row (rows : ptrie (list positive)) (p : positive)
    : list positive :=
  match trie_get p rows with Some row => row | None => [] end.
TimeFun dom_child_row.

Local Definition dom_child_push (m : ptrie positive) (rows : ptrie (list positive))
    (v : positive) : ptrie (list positive) :=
  match trie_get v m with
  | None => rows
  | Some p => PTrieCode.set p
      (v :: match trie_get p rows with Some vs => vs | None => [] end) rows
  end.
TimeFun dom_child_push.

Local Definition dom_child_rows m o := fold_left (dom_child_push m) o Empty.
TimeFun dom_child_rows.

Local Lemma dom_child_matches_spec : forall m p v,
  dom_child_matches m p v = true <-> trie_get v m = Some p.
Proof.
  intros m p v. unfold dom_child_matches. destruct (trie_get v m) as [parent |].
  - rewrite Pos.eqb_eq. split; intro H; congruence.
  - split; discriminate.
Qed.

Local Lemma dom_child_fold_row : forall m vs rows p,
  dom_child_row (fold_left (dom_child_push m) vs rows) p =
    rev (filter (dom_child_matches m p) vs) ++ dom_child_row rows p.
Proof.
  intros m vs. induction vs as [| v rest IH]; intros rows p.
  - reflexivity.
  - cbn [fold_left]. rewrite IH. cbn [filter].
    unfold dom_child_matches, dom_child_push.
    destruct (trie_get v m) as [parent |] eqn:Hparent; [| reflexivity].
    destruct (Pos.eq_dec p parent) as [Heq | Hneq].
    + subst parent. rewrite Pos.eqb_refl.
      unfold dom_child_row at 1. rewrite PTrie.get_set_same.
      cbn [rev]. now rewrite <- app_assoc.
    + rewrite (proj2 (Pos.eqb_neq p parent) Hneq).
      unfold dom_child_row at 1. rewrite PTrie.get_set_other by exact Hneq. reflexivity.
Qed.

Local Lemma dom_child_row_reverse : forall rows p,
  dom_child_row (PTrieCode.map (fun vs => rev_append vs []) rows) p =
    rev (dom_child_row rows p).
Proof.
  intros rows p. unfold dom_child_row. rewrite PTrie.get_map.
  change (PTrie.get p rows) with (trie_get p rows).
  destruct (trie_get p rows) as [vs |]; [| reflexivity].
  cbn [option_map]. symmetry. apply rev_alt.
Qed.

Local Lemma dom_tree_pre : forall g r m o,
  pre (DomCode.tree g r m o) = dom_positions o.
Proof. reflexivity. Qed.

Local Lemma dom_tree_children : forall g r m o p,
  children (DomCode.tree g r m o) p = filter (dom_child_matches m p) o.
Proof.
  intros g r m o p.
  change (dom_child_row (PTrieCode.map (fun vs => rev_append vs [])
    (dom_child_rows m o)) p = filter (dom_child_matches m p) o).
  rewrite dom_child_row_reverse. unfold dom_child_rows. rewrite dom_child_fold_row.
  unfold dom_child_row. rewrite PTrie.get_empty, app_nil_r, rev_involutive. reflexivity.
Qed.

Local Lemma dom_tree_children_member : forall g r m o p v,
  In v (children (DomCode.tree g r m o) p) <-> In v o /\ trie_get v m = Some p.
Proof.
  intros g r m o p v. rewrite dom_tree_children, filter_In, dom_child_matches_spec.
  reflexivity.
Qed.

Local Lemma dom_sorted_weaken {A : Type} (R S : A -> A -> Prop) :
  (forall x y, R x y -> S x y) -> forall xs,
  StronglySorted R xs -> StronglySorted S xs.
Proof.
  intros Hrel xs Hsorted. induction Hsorted as [| x rest Hsorted IH Hall].
  - constructor.
  - constructor; [exact IH |].
    apply Forall_forall. intros y Hy. apply Hrel.
    exact (proj1 (Forall_forall (R x) rest) Hall y Hy).
Qed.

Local Lemma dom_sorted_filter {A : Type} (R : A -> A -> Prop) (keep : A -> bool) :
  forall xs, StronglySorted R xs -> StronglySorted R (filter keep xs).
Proof.
  intros xs Hsorted. induction Hsorted as [| x rest Hsorted IH Hall].
  - constructor.
  - cbn [filter]. destruct (keep x); [| exact IH]. constructor; [exact IH |].
    apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _].
    exact (proj1 (Forall_forall (R x) rest) Hall y Hy).
Qed.

Local Lemma dom_order_sorted : forall o, StronglySorted (order_before o) o.
Proof.
  intro o. induction o as [| v rest IH]; [constructor |]. constructor.
  - eapply dom_sorted_weaken; [| exact IH].
    intros x y [i [j [Hi [Hj Hij]]]]. exists (S i), (S j).
    cbn [nth_error]. split; [exact Hi |]. split; [exact Hj | lia].
  - apply Forall_forall. intros x Hin. apply In_nth_error in Hin as [i Hi].
    exists O, (S i). cbn [nth_error]. split; [reflexivity |]. split; [exact Hi | lia].
Qed.

Local Lemma dom_tree_preorder_order : forall g r m o x y,
  NoDup o -> order_before o x y -> preorder_before (DomCode.tree g r m o) x y.
Proof.
  intros g r m o x y Hunique [i [j [Hi [Hj Hij]]]].
  exists (N.of_nat i), (N.of_nat j). rewrite dom_tree_pre.
  split; [now apply dom_positions_nth |].
  split; [now apply dom_positions_nth | lia].
Qed.

Local Lemma dom_tree_children_sorted : forall g r m o p,
  NoDup o -> NoDup (children (DomCode.tree g r m o) p) /\
  StronglySorted (preorder_before (DomCode.tree g r m o))
    (children (DomCode.tree g r m o) p).
Proof.
  intros g r m o p Hunique. rewrite dom_tree_children. split.
  - now apply NoDup_filter.
  - apply dom_sorted_filter. eapply dom_sorted_weaken; [| apply dom_order_sorted].
    intros x y Hbefore. now apply dom_tree_preorder_order.
Qed.

(** Endpoint installation assigns a fixed inclusive endpoint to each positioned key. *)
Local Definition dom_end_push (pos sizes ends : ptrie N) (v : positive) : ptrie N :=
  match trie_get v pos with
  | None => ends
  | Some pv => PTrieCode.set v (N.pred (pv + dom_size_get sizes v)) ends
  end.
TimeFun dom_end_push.

Local Definition dom_end_map pos sizes o := fold_left (dom_end_push pos sizes) o Empty.
TimeFun dom_end_map.

Local Lemma dom_end_fold_keeps : forall pos sizes vs ends v pv,
  trie_get v pos = Some pv -> trie_get v ends = Some (N.pred (pv + dom_size_get sizes v)) ->
  trie_get v (fold_left (dom_end_push pos sizes) vs ends) =
    Some (N.pred (pv + dom_size_get sizes v)).
Proof.
  intros pos sizes vs. induction vs as [| x rest IH]; intros ends v pv Hpos Hend.
  - exact Hend.
  - cbn [fold_left]. apply IH; [exact Hpos |]. unfold dom_end_push.
    destruct (trie_get x pos) as [px |] eqn:Hx; [| exact Hend].
    destruct (Pos.eq_dec v x) as [Heq | Hneq].
    + subst x. rewrite Hpos in Hx. injection Hx as Heq. subst px.
      apply PTrie.get_set_same.
    + rewrite PTrie.get_set_other by exact Hneq. exact Hend.
Qed.

Local Lemma dom_end_fold_member : forall pos sizes vs ends v pv,
  In v vs -> trie_get v pos = Some pv ->
  trie_get v (fold_left (dom_end_push pos sizes) vs ends) =
    Some (N.pred (pv + dom_size_get sizes v)).
Proof.
  intros pos sizes vs. induction vs as [| x rest IH]; intros ends v pv Hin Hpos.
  - contradiction.
  - cbn [fold_left]. destruct Hin as [Heq | Hin].
    + subst x. unfold dom_end_push. rewrite Hpos.
      apply dom_end_fold_keeps; [exact Hpos | apply PTrie.get_set_same].
    + now apply IH.
Qed.

Local Lemma dom_end_fold_domain : forall pos sizes vs ends v value,
  trie_get v (fold_left (dom_end_push pos sizes) vs ends) = Some value ->
  In v vs \/ trie_get v ends = Some value.
Proof.
  intros pos sizes vs. induction vs as [| x rest IH]; intros ends v value Hget.
  - right. exact Hget.
  - cbn [fold_left] in Hget. apply IH in Hget as [Hin | Hget].
    + left. now right.
    + unfold dom_end_push in Hget.
      destruct (trie_get x pos) as [px |]; [| now right].
      destruct (Pos.eq_dec v x) as [Heq | Hneq].
      * left. now left.
      * rewrite PTrie.get_set_other in Hget by exact Hneq. now right.
Qed.

Local Lemma dom_tree_post : forall g r m o,
  post (DomCode.tree g r m o) = dom_end_map (dom_positions o) (dom_sizes m o) o.
Proof. reflexivity. Qed.

Local Lemma dom_tree_post_number : forall g r m o v pv,
  trie_get v (dom_positions o) = Some pv ->
  trie_get v (post (DomCode.tree g r m o)) =
    Some (N.pred (pv + dom_size_get (dom_sizes m o) v)).
Proof.
  intros g r m o v pv Hpos. rewrite dom_tree_post. unfold dom_end_map.
  apply dom_end_fold_member; [| exact Hpos].
  apply (proj1 (dom_positions_domain o v)). now exists pv.
Qed.

Local Lemma dom_tree_post_domain : forall g r m o v,
  (exists value, trie_get v (post (DomCode.tree g r m o)) = Some value) <-> In v o.
Proof.
  intros g r m o v. split.
  - intros [value Hget]. rewrite dom_tree_post in Hget. unfold dom_end_map in Hget.
    apply dom_end_fold_domain in Hget as [Hin | Hget]; [exact Hin |].
    rewrite PTrie.get_empty in Hget. discriminate Hget.
  - intro Hin. destruct (proj2 (dom_positions_domain o v) Hin) as [pv Hpos].
    exists (N.pred (pv + dom_size_get (dom_sizes m o) v)).
    now apply dom_tree_post_number.
Qed.

Local Lemma dom_tree_post_value : forall g r m o v value,
  trie_get v (post (DomCode.tree g r m o)) = Some value ->
  exists pv, trie_get v (dom_positions o) = Some pv /\
    value = N.pred (pv + dom_size_get (dom_sizes m o) v).
Proof.
  intros g r m o v value Hget.
  assert (Hin : In v o) by (apply (proj1 (dom_tree_post_domain g r m o v)); now exists value).
  destruct (proj2 (dom_positions_domain o v) Hin) as [pv Hpos].
  pose proof (dom_tree_post_number g r m o v pv Hpos) as Hend.
  exists pv. split; [exact Hpos | congruence].
Qed.

Local Lemma dom_positions_bound : forall o v value,
  NoDup o -> trie_get v (dom_positions o) = Some value ->
  (value < N.of_nat (length o))%N.
Proof.
  intros o v value Hunique Hget.
  destruct (dom_positions_value o v value Hunique Hget) as [i [Hi Heq]]. subst value.
  assert (Hindex : i < length o).
  { apply nth_error_Some. rewrite Hi. discriminate. }
  now apply dom_nat_N_lt.
Qed.

(** The numbered accepted tree exposes exactly the semantic reachable domain. *)
Local Lemma dom_tree_checked_exact : forall g r m o,
  DomCode.check g r m o = true -> domtree_exact g r (DomCode.tree g r m o).
Proof.
  intros g r m o Hcheck.
  pose proof (dom_check_certificate g r m o Hcheck) as Hcert.
  pose proof (proj1 Hcert) as Hpreorder.
  destruct Hpreorder as [Hunique [Hhead [Hroot [Hparents [Hdomain Hcontiguous]]]]].
  assert (Hordered : forall v p, trie_get v m = Some p -> order_before o p v).
  { intros v p Hparent. exact (dom_cert_parent_before (base g) r m o v p Hcert Hparent). }
  pose proof Hcheck as Hphases. rewrite dom_check_agrees in Hphases.
  unfold dom_check_spec in Hphases.
  destruct (dom_read_known (dom_scan g) r o) as [pos |] eqn:Hread;
    [| discriminate Hphases].
  destruct (dom_map_check_known (dom_scan g) r m o); [| discriminate Hphases].
  apply andb_true_iff in Hphases as [Hsizes Hedges].
  pose proof (dom_read_known_positions (dom_scan g) r o pos Hread) as Hpositions.
  destruct (dom_read_known_success g r o pos Hread) as [_ [_ [_ [Hlisted _]]]].
  subst pos.
  assert (Hwidth : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
  { intros v Hin. apply dom_listed_key_width. now apply Hlisted. }
  unfold domtree_exact. split.
  - rewrite <- (dom_nodes_verts g). apply Hlisted.
    exact (dom_cert_root_listed (base g) r m o Hcert).
  - split.
    + change (dom_exact g r m). exact (dom_cert_exact g r m o Hcert).
    + split.
      * intros v a [Hpre | Hpost].
        -- rewrite dom_tree_pre in Hpre.
           pose proof (dom_positions_bound o v a Hunique Hpre) as Hbound.
           apply (dom_distinct_value_width o (graph_width (base g)) a Hunique Hwidth). lia.
        -- destruct (dom_tree_post_value g r m o v a Hpost) as [pv [Hpv Ha]]. subst a.
           pose proof (dom_sizes_position_end_bound m o v pv Hunique Hordered Hpv) as Hbound.
           apply (dom_distinct_value_width o (graph_width (base g))
             (N.pred (pv + dom_size_get (dom_sizes m o) v)) Hunique Hwidth). lia.
      * split.
        -- change (forall u v, In v (children (DomCode.tree g r m o) u) <->
             trie_get v m = Some u).
           intros u v. rewrite dom_tree_children_member. split.
           ++ intros [_ Hparent]. exact Hparent.
           ++ intro Hparent. split; [eapply Hdomain; exact Hparent | exact Hparent].
        -- split.
           ++ intro u. now apply dom_tree_children_sorted.
           ++ split.
              ** intro v. rewrite dom_tree_pre, dom_positions_domain. split.
                 --- intro Hv. exact (dom_cert_listed_reach (base g) r m o v Hcert Hv).
                 --- intro Hv. exact (dom_cert_reach_listed (base g) r m o v Hcert Hv).
              ** split.
                 --- intro v. rewrite dom_tree_post_domain. split.
                     +++ intro Hv. exact (dom_cert_listed_reach (base g) r m o v Hcert Hv).
                     +++ intro Hv. exact (dom_cert_reach_listed (base g) r m o v Hcert Hv).
                 --- intros u v Hreach.
                     pose proof (dom_cert_reach_listed (base g) r m o v Hcert Hreach) as Hv.
                     split.
                     +++ intro Hdom.
                         pose proof (dom_cert_dominates_anc (base g) r m o u v Hcert Hv Hdom)
                           as Hanc.
                         pose proof (dom_cert_anc_listed (base g) r m o u v Hcert Hanc Hv) as Hu.
                         destruct (proj2 (dom_positions_domain o u) Hu) as [a Ha].
                         destruct (proj2 (dom_positions_domain o v) Hv) as [c Hc].
                         pose proof (proj2 (dom_sizes_interval_anc m o u v Hunique Hordered
                           Hsizes Hu Hv) Hanc) as Hinterval.
                         unfold dom_interval in Hinterval. rewrite Ha, Hc in Hinterval.
                         apply andb_true_iff in Hinterval as [Hac Hend].
                         apply N.leb_le in Hac. apply N.leb_le in Hend.
                         exists a, (N.pred (a + dom_size_get (dom_sizes m o) u)),
                           c, (N.pred (c + dom_size_get (dom_sizes m o) v)).
                         split; [now rewrite dom_tree_pre |].
                         split; [now apply dom_tree_post_number |].
                         split; [now rewrite dom_tree_pre |].
                         split; [now apply dom_tree_post_number |]. split; [exact Hac | lia].
                     +++ intros [a [b [c [d [Ha [Hb [Hc [Hd [Hac Hdb]]]]]]]]].
                         rewrite dom_tree_pre in Ha, Hc.
                         assert (Hu : In u o).
                         { apply (proj1 (dom_positions_domain o u)). now exists a. }
                         pose proof (dom_tree_post_number g r m o u a Ha) as Hpostu.
                         pose proof (dom_tree_post_number g r m o v c Hc) as Hpostv.
                         rewrite Hb in Hpostu. injection Hpostu as Hbvalue. subst b.
                         rewrite Hd in Hpostv. injection Hpostv as Hdvalue. subst d.
                         apply (dom_cert_anc_dominates (base g) r m o u v Hcert Hv).
                         apply (proj1 (dom_sizes_interval_anc m o u v Hunique Hordered
                           Hsizes Hu Hv)).
                         unfold dom_interval. rewrite Ha, Hc. apply andb_true_iff.
                         split; apply N.leb_le; [exact Hac |].
                         pose proof (dom_sizes_positive m o u).
                         pose proof (dom_sizes_positive m o v). lia.
Qed.

Module Dom <: DOM.
  Include DomCode.
  Include DOM_SPEC.

  Lemma check_sound : forall g r m o, check g r m o = true -> dom_exact g r m.
  Proof.
    intros g r m o Hcheck.
    exact (dom_cert_exact g r m o (dom_check_certificate g r m o Hcheck)).
  Qed.

  Lemma tree_idom : forall g r m o, check g r m o = true -> idom (tree g r m o) = m.
  Proof.
    intros g r m o _. reflexivity.
  Qed.

  Lemma tree_exact : forall g r m o, check g r m o = true -> domtree_exact g r (tree g r m o).
  Proof.
    intros g r m o Hcheck. exact (dom_tree_checked_exact g r m o Hcheck).
  Qed.

  Lemma dominates_b_spec : forall g r m o u v,
    check g r m o = true -> reach (base g) [r] v ->
    reflect (dominates (base g) r u v) (dominates_b (tree g r m o) u v).
  Proof.
    intros g r m o u v Hcheck Hreach.
    destruct (tree_exact g r m o Hcheck) as
      [_ [_ [_ [_ [_ [_ [_ Hinterval]]]]]]].
    apply iff_reflect. split.
    - intro Hdom. apply (proj1 (Hinterval u v Hreach)) in Hdom.
      destruct Hdom as [a [b [c [d [Ha [Hb [Hc [Hd [Hac Hdb]]]]]]]]].
      unfold dominates_b. rewrite Ha, Hb, Hc, Hd.
      apply andb_true_iff. split; apply N.leb_le; assumption.
    - intro Hquery. unfold dominates_b in Hquery.
      destruct (trie_get u (pre (tree g r m o))) as [a |] eqn:Ha;
        destruct (trie_get u (post (tree g r m o))) as [b |] eqn:Hb;
        destruct (trie_get v (pre (tree g r m o))) as [c |] eqn:Hc;
        destruct (trie_get v (post (tree g r m o))) as [d |] eqn:Hd;
        try discriminate Hquery.
      apply andb_true_iff in Hquery as [Hac Hdb].
      apply N.leb_le in Hac. apply N.leb_le in Hdb.
      apply (proj2 (Hinterval u v Hreach)). exists a, b, c, d.
      repeat split; assumption.
  Qed.

  Lemma kids_spec : forall g r m o, check g r m o = true -> forall u,
    (forall v, In v (children (tree g r m o) u) <-> trie_get v m = Some u) /\
    NoDup (children (tree g r m o) u) /\
    StronglySorted (preorder_before (tree g r m o)) (children (tree g r m o) u).
  Proof.
    intros g r m o Hcheck u.
    pose proof (dom_check_certificate g r m o Hcheck) as Hcert.
    destruct Hcert as [[Hunique [_ [_ [_ [Hdomain _]]]]] _].
    split.
    - intro v. rewrite dom_tree_children_member. split.
      + intros [_ Hparent]. exact Hparent.
      + intro Hparent. split; [eapply Hdomain; exact Hparent | exact Hparent].
    - now apply dom_tree_children_sorted.
  Qed.
End Dom.

(** Scanning past keys other than the query preserves its recorded position. *)
Local Lemma dom_position_fold_absent : forall vs v found next,
  ~ In v vs ->
  fst (fold_left (fun acc u => let '(found, next) := acc in
    (if Pos.eqb u v then next else found, N.succ next)) vs (found, next)) = found.
Proof.
  intro vs. induction vs as [| u rest IH]; intros v found next Habsent.
  - reflexivity.
  - cbn [fold_left].
    assert (Hneq : u <> v) by (intro Heq; subst u; apply Habsent; now left).
    rewrite (proj2 (Pos.eqb_neq u v) Hneq). apply IH.
    intro Hin. apply Habsent. now right.
Qed.

Local Lemma dom_position_fold_nth : forall vs v found next i,
  NoDup vs -> nth_error vs i = Some v ->
  fst (fold_left (fun acc u => let '(found, next) := acc in
    (if Pos.eqb u v then next else found, N.succ next)) vs (found, next)) =
      (next + N.of_nat i)%N.
Proof.
  intro vs. induction vs as [| u rest IH]; intros v found next i Hunique Hnth.
  - destruct i; discriminate Hnth.
  - inversion Hunique as [| head tail Hfresh Hrest]; subst head tail.
    destruct i as [| i].
    + cbn [nth_error] in Hnth. injection Hnth as Heq. subst u.
      cbn [fold_left]. rewrite Pos.eqb_refl.
      rewrite dom_position_fold_absent by exact Hfresh. lia.
    + cbn [nth_error] in Hnth. cbn [fold_left].
      assert (Hneq : u <> v).
      { intro Heq. subst u. apply Hfresh. eapply nth_error_In. exact Hnth. }
      rewrite (proj2 (Pos.eqb_neq u v) Hneq).
      rewrite (IH v found (N.succ next) i Hrest Hnth), Nat2N.inj_succ. lia.
Qed.

Local Lemma dom_position_fold_rank : forall o v,
  NoDup o -> In v o ->
  fst (fold_left (fun acc u => let '(found, next) := acc in
    (if Pos.eqb u v then next else found, N.succ next)) o (0%N, 0%N)) =
      N.of_nat (dom_cert_position o v).
Proof.
  intros o v Hunique Hin. apply In_nth_error in Hin as [i Hi].
  rewrite (dom_cert_position_nth o Hunique i v Hi).
  exact (dom_position_fold_nth o v 0%N 0%N i Hunique Hi).
Qed.

(** Unit weights expose each remaining cell's ordinary additive contribution. *)
Local Lemma dom_size_mass_cons_one sizes v xs :
  dom_size_mass (fun _ => 1%N) (v :: xs) sizes =
    (dom_size_get sizes v + dom_size_mass (fun _ => 1%N) xs sizes)%N.
Proof.
  unfold dom_size_mass. cbn [fold_right]. now rewrite N.mul_1_l.
Qed.

(** A cell in a remaining list contributes its entire value to that list's mass. *)
Local Lemma dom_size_mass_member xs sizes x : In x xs ->
  (dom_size_get sizes x <= dom_size_mass (fun _ => 1%N) xs sizes)%N.
Proof.
  induction xs as [|v xs IH]; intros Hin; [contradiction|].
  rewrite dom_size_mass_cons_one.
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

(** Remaining cells hold at most the original mass; retired cells may retain one extra copy. *)
Local Definition dom_size_budget (limit : N) remaining sizes : Prop :=
  (dom_size_mass (fun _ => 1%N) remaining sizes <= limit)%N /\
  forall x, ~ In x remaining ->
    (dom_size_get sizes x + dom_size_mass (fun _ => 1%N) remaining sizes <=
      2 * limit + 1)%N.

(** The mass invariant bounds every cell, including cells outside the candidate order. *)
Local Lemma dom_size_budget_value limit remaining sizes x :
  dom_size_budget limit remaining sizes ->
  (dom_size_get sizes x <= 2 * limit + 1)%N.
Proof.
  intros [Hmass Hretired]. destruct (in_dec Pos.eq_dec x remaining) as [Hin|Houtside].
  - pose proof (dom_size_mass_member remaining sizes x Hin). lia.
  - specialize (Hretired x Houtside). lia.
Qed.

(** The remaining-parent case conserves mass and retires a cell without duplicating its pool. *)
Local Lemma dom_size_budget_transfer limit remaining m sizes v p :
  NoDup (v :: remaining) -> dom_size_budget limit (v :: remaining) sizes ->
  trie_get v m = Some p -> In p remaining ->
  dom_size_budget limit remaining (dom_add_size m sizes v).
Proof.
  intros Hunique [Hmass Hretired] Hparent Hp.
  inversion Hunique as [|head tail Hfresh Htail]; subst head tail.
  pose proof (dom_size_mass_transfer (fun _ => 1%N) remaining m sizes v p
    Htail Hparent Hp eq_refl) as Htransfer.
  split; [now rewrite Htransfer|]. intros x Houtside.
  rewrite Htransfer, dom_add_size_value, Hparent.
  assert (Hxp : x <> p) by (intro Heq; subst x; contradiction).
  rewrite (proj2 (Pos.eqb_neq x p) Hxp).
  destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite dom_size_mass_cons_one in Hmass |- *. nia.
  - apply Hretired. intros [Heq|Hin]; [congruence|exact (Houtside Hin)].
Qed.

(** Retiring a cell releases enough mass to pay a late write, including a self-parent. *)
Local Lemma dom_size_budget_retire limit remaining m sizes v :
  dom_size_budget limit (v :: remaining) sizes ->
  (forall p, trie_get v m = Some p -> ~ In p remaining) ->
  dom_size_budget limit remaining (dom_add_size m sizes v).
Proof.
  intros [Hmass Hretired] Houtside.
  pose proof (dom_size_mass_absent (fun _ => 1%N) remaining m sizes v Houtside) as Hsame.
  rewrite dom_size_mass_cons_one in Hmass.
  split; [rewrite Hsame; lia|]. intros x Hx.
  rewrite Hsame, dom_add_size_value.
  destruct (Pos.eq_dec x v) as [->|Hne].
  - destruct (trie_get v m) as [p|] eqn:Hparent; [|lia].
    destruct (Pos.eqb v p) eqn:Heq; [|lia]. apply Pos.eqb_eq in Heq. subst p. nia.
  - assert (Hnot : ~ In x (v :: remaining)).
    { intros [Heq|Hin]; [congruence|exact (Hx Hin)]. }
    specialize (Hretired x Hnot).
    rewrite dom_size_mass_cons_one in Hretired.
    destruct (trie_get v m) as [p|] eqn:Hparent; [|lia].
    destruct (Pos.eqb x p) eqn:Heq; [|lia]. apply Pos.eqb_eq in Heq. subst p. nia.
Qed.

(** Distinct processing preserves the mass bound even when candidate parents form cycles. *)
Local Lemma dom_size_budget_step limit remaining m sizes v :
  NoDup (v :: remaining) -> dom_size_budget limit (v :: remaining) sizes ->
  dom_size_budget limit remaining (dom_add_size m sizes v).
Proof.
  intros Hunique Hbudget. destruct (trie_get v m) as [p|] eqn:Hparent.
  - destruct (in_dec Pos.eq_dec p remaining) as [Hin|Houtside].
    + eapply dom_size_budget_transfer; eassumption.
    + apply dom_size_budget_retire; [exact Hbudget|].
      intros q Hget. rewrite Hparent in Hget. injection Hget as <-. exact Houtside.
  - apply dom_size_budget_retire; [exact Hbudget|].
    intros p Hget. rewrite Hparent in Hget. discriminate Hget.
Qed.

(** Empty storage gives one unit to each candidate occurrence. *)
Local Lemma dom_size_mass_empty xs :
  dom_size_mass (fun _ => 1%N) xs Empty = N.of_nat (length xs).
Proof.
  induction xs as [|v xs IH]; [reflexivity|].
  rewrite dom_size_mass_cons_one, IH. cbn [length].
  unfold dom_size_get. rewrite PTrie.get_empty, Nat2N.inj_succ. lia.
Qed.

(** The original number of distinct entries initializes the remaining-mass budget. *)
Local Lemma dom_size_budget_empty xs :
  dom_size_budget (N.of_nat (length xs)) xs Empty.
Proof.
  split; [rewrite dom_size_mass_empty; reflexivity|].
  intros x Houtside. rewrite dom_size_mass_empty. unfold dom_size_get.
  rewrite PTrie.get_empty. lia.
Qed.

(** Distinct processing bounds every final size even for cyclic or unclosed maps. *)
Lemma dom_sizes_value_bound m o x : NoDup o ->
  (dom_size_get (dom_sizes m o) x <= 2 * N.of_nat (length o) + 1)%N.
Proof.
  intro Hunique.
  assert (Hfold : forall remaining sizes limit, NoDup remaining ->
    dom_size_budget limit remaining sizes ->
    dom_size_budget limit [] (fold_left (dom_add_size m) remaining sizes)).
  { intro remaining. induction remaining as [|v rest IH]; intros sizes limit Hnodup Hbudget.
    - exact Hbudget.
    - inversion Hnodup as [|head tail Hfresh Hrest]; subst head tail.
      cbn [fold_left]. apply IH; [exact Hrest|].
      eapply dom_size_budget_step; eassumption. }
  unfold dom_sizes. rewrite rev_append_rev, app_nil_r.
  eapply dom_size_budget_value. apply Hfold.
  - now apply NoDup_rev.
  - rewrite <- length_rev. apply dom_size_budget_empty.
Qed.

(* BEGIN G2-G ANCHOR SUPPORT *)
(** * Anchor interval bounds

    Distinct removed keys let each anchor transfer reuse the retired-cell budget.
    The resulting bounds also cover cyclic and self anchors. *)

(** This named callback has exactly the body of the existing anchor-size fold. *)
Definition dom_order_anchor_transfer (parents : ptrie N) (sizes : ptrie N)
    (entry : N * N * N) : ptrie N :=
  let '(v, anchor, _) := entry in
  let own := dom_anchor_size sizes v in
  let sizes := PTrieCode.set (dom_lt_key v) own sizes in
  if N.eqb anchor (dom_lt_identity parents v) then sizes else
    PTrieCode.set (dom_lt_key anchor) (N.add own (dom_anchor_size sizes anchor)) sizes.
TimeFun dom_order_anchor_transfer.

(** This named callback has exactly the body of the existing anchor-capacity fold. *)
Definition dom_order_anchor_capacity_step (parents sizes caps : ptrie N)
    (entry : N * N * N) : ptrie N :=
  let '(v, anchor, _) := entry in
  let p := dom_lt_identity parents v in
  if N.eqb anchor p then PTrieCode.set (dom_lt_key p)
    (N.add (dom_order_number caps p) (dom_anchor_size sizes v)) caps else caps.
TimeFun dom_order_anchor_capacity_step.

(** Every anchor transfer is a raw size transfer under an empty or singleton parent map. *)
Lemma dom_anchor_transfer_as_size parents sizes vertex anchor witness :
  dom_order_anchor_transfer parents sizes (vertex, anchor, witness) =
  dom_add_size
    (if N.eqb anchor (dom_lt_identity parents vertex) then Empty else
      PTrieCode.set (dom_lt_key vertex) (dom_lt_key anchor) Empty)
    sizes (dom_lt_key vertex).
Proof.
  unfold dom_order_anchor_transfer. cbn beta iota zeta.
  unfold dom_add_size, dom_anchor_size, dom_size_get.
  destruct (N.eqb anchor (dom_lt_identity parents vertex)).
  - now rewrite PTrie.get_empty.
  - rewrite PTrie.get_set_same, N.add_comm. reflexivity.
Qed.

(** Distinct retirement preserves the size budget even when anchors are cyclic. *)
Lemma dom_order_anchor_transfer_budget limit parents (remaining : list (N * N * N))
    sizes v anchor witness :
  NoDup (dom_lt_key v :: map (fun entry => dom_lt_key (fst (fst entry))) remaining) ->
  dom_size_budget limit
    (dom_lt_key v :: map (fun entry => dom_lt_key (fst (fst entry))) remaining) sizes ->
  dom_size_budget limit (map (fun entry => dom_lt_key (fst (fst entry))) remaining)
    (dom_order_anchor_transfer parents sizes (v, anchor, witness)).
Proof.
  intros Hunique Hbudget. rewrite dom_anchor_transfer_as_size.
  eapply dom_size_budget_step; eassumption.
Qed.

(** The full size fold retires every input key while retaining its original budget. *)
Lemma dom_order_anchor_sizes_fold_budget limit parents entries sizes :
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) entries) ->
  dom_size_budget limit (map (fun entry => dom_lt_key (fst (fst entry))) entries) sizes ->
  dom_size_budget limit [] (fold_left (dom_order_anchor_transfer parents) entries sizes).
Proof.
  revert sizes. induction entries as [|[[v anchor] witness] rest IH];
    intros sizes Hunique Hbudget; [exact Hbudget|].
  cbn [map fst] in Hunique, Hbudget.
  inversion Hunique as [|head tail Hfresh Hrest]; subst head tail.
  cbn [fold_left]. apply IH; [exact Hrest|].
  now apply dom_order_anchor_transfer_budget.
Qed.

(** Every anchor-size observation is bounded by twice the distinct retirement count plus one. *)
Lemma dom_anchor_sizes_value_bound parents removed vertex :
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) removed) ->
  (dom_anchor_size (dom_anchor_sizes parents removed) vertex <=
    2 * N.of_nat (length removed) + 1)%N.
Proof.
  intro Hunique.
  change (dom_size_get
    (fold_left (dom_order_anchor_transfer parents) (rev_append removed []) Empty)
    (dom_lt_key vertex) <= 2 * N.of_nat (length removed) + 1)%N.
  eapply dom_size_budget_value. apply dom_order_anchor_sizes_fold_budget.
  - rewrite rev_append_rev, app_nil_r, map_rev. now apply NoDup_rev.
  - replace (N.of_nat (length removed)) with
      (N.of_nat (length (map (fun entry => dom_lt_key (fst (fst entry)))
        (rev_append removed [])))).
    + apply dom_size_budget_empty.
    + rewrite length_map, rev_append_rev, app_nil_r, length_rev. reflexivity.
Qed.

(** A capacity lookup returns a stored bounded value or zero. *)
Lemma dom_order_anchor_number_bound bound caps v :
  dom_lt_trie_all (fun n => (n <= bound)%N) caps ->
  (dom_order_number caps v <= bound)%N.
Proof.
  intro Hcaps. unfold dom_order_number.
  destruct (trie_get (dom_lt_key v) caps) as [value|] eqn:Hget; [|lia].
  exact (Hcaps _ _ Hget).
Qed.

(** Enlarging a numeric payload budget preserves the trie invariant. *)
Lemma dom_order_anchor_values_mono smaller larger values :
  (smaller <= larger)%N -> dom_lt_trie_all (fun n => (n <= smaller)%N) values ->
  dom_lt_trie_all (fun n => (n <= larger)%N) values.
Proof.
  intros Hle Hvalues key value Hget.
  eapply N.le_trans; [exact (Hvalues _ _ Hget)|exact Hle].
Qed.

(** A capacity callback adds at most one bounded anchor size to its old payload maximum. *)
Lemma dom_order_anchor_capacity_step_bound unit current parents sizes caps entry :
  (forall v, (dom_anchor_size sizes v <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= current)%N) caps ->
  dom_lt_trie_all (fun n => (n <= current + unit)%N)
    (dom_order_anchor_capacity_step parents sizes caps entry).
Proof.
  intros Hsizes Hcaps. destruct entry as [[v anchor] witness].
  pose proof (dom_order_anchor_values_mono current (current + unit)%N caps ltac:(lia) Hcaps)
    as Hlarger.
  unfold dom_order_anchor_capacity_step. cbn beta iota zeta.
  destruct (N.eqb anchor (dom_lt_identity parents v)); [|exact Hlarger].
  apply dom_lt_trie_all_set; [exact Hlarger|].
  pose proof (dom_order_anchor_number_bound current caps (dom_lt_identity parents v) Hcaps)
    as Hnumber.
  pose proof (Hsizes v) as Hsize. lia.
Qed.

(** A capacity fold adds at most one size budget per processed record. *)
Lemma dom_order_anchor_capacity_fold_bound unit parents sizes entries caps current :
  (forall v, (dom_anchor_size sizes v <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= current)%N) caps ->
  dom_lt_trie_all (fun n => (n <= current + N.of_nat (length entries) * unit)%N)
    (fold_left (dom_order_anchor_capacity_step parents sizes) entries caps).
Proof.
  intros Hsizes. revert caps current. induction entries as [|entry rest IH];
    intros caps current Hcaps.
  - change (dom_lt_trie_all (fun n => (n <= current + 0)%N) caps).
    rewrite N.add_0_r. exact Hcaps.
  - cbn [fold_left length]. rewrite Nat2N.inj_succ.
    replace (current + N.succ (N.of_nat (length rest)) * unit)%N with
      ((current + unit) + N.of_nat (length rest) * unit)%N by nia.
    apply IH. now apply dom_order_anchor_capacity_step_bound.
Qed.

(** Initial empty capacities are bounded by the number of records times one size budget. *)
Lemma dom_order_anchor_capacity_bound unit parents sizes removed :
  (forall v, (dom_anchor_size sizes v <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= N.of_nat (length removed) * unit)%N)
    (dom_anchor_capacity parents sizes removed).
Proof.
  intro Hsizes.
  change (dom_lt_trie_all (fun n => (n <= 0 + N.of_nat (length removed) * unit)%N)
    (fold_left (dom_order_anchor_capacity_step parents sizes) removed Empty)).
  apply dom_order_anchor_capacity_fold_bound; [exact Hsizes|apply dom_lt_trie_all_empty].
Qed.

(** Both interval endpoints and free-block endpoints share one numeric upper bound. *)
Definition dom_order_anchor_state_bound (bound : N) (st : dom_anchor_state) : Prop :=
  dom_lt_trie_all (fun pair => (fst pair <= bound /\ snd pair <= bound)%N)
    (anchor_intervals st) /\
  dom_lt_trie_all (fun pair => (fst pair <= bound /\ snd pair <= bound)%N)
    (anchor_free st).

(** Enlarging an endpoint budget preserves both anchor maps. *)
Lemma dom_order_anchor_state_mono smaller larger st :
  (smaller <= larger)%N -> dom_order_anchor_state_bound smaller st ->
  dom_order_anchor_state_bound larger st.
Proof.
  intros Hle [Hintervals Hfree]. split; intros key [lo hi] Hget.
  - destruct (Hintervals _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in *. split; lia.
  - destruct (Hfree _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in *. split; lia.
Qed.

(** Parent placement increases the largest observed endpoint by at most the new size. *)
Lemma dom_order_anchor_at_parent_bound unit current capacity caps st v p size :
  (size <= unit)%N -> (capacity <= current)%N ->
  dom_lt_trie_all (fun n => (n <= capacity)%N) caps ->
  dom_order_anchor_state_bound current st ->
  dom_order_anchor_state_bound (current + unit)%N (dom_anchor_at_parent caps st v p size).
Proof.
  intros Hsize Hcapacity Hcaps Hstate.
  destruct (dom_order_anchor_state_mono current (current + unit)%N st ltac:(lia) Hstate)
    as [Hintervals Hfree].
  unfold dom_anchor_at_parent.
  destruct (trie_get (dom_lt_key p) (anchor_free st)) as [[lo hi]|] eqn:Hget.
  - destruct (proj2 Hstate _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in Hlo, Hhi.
    split; cbn [anchor_intervals anchor_free]; apply dom_lt_trie_all_set;
      try assumption; cbn [fst snd]; split; lia.
  - pose proof (dom_order_anchor_number_bound capacity caps p Hcaps) as Hnumber.
    split; cbn [anchor_intervals anchor_free]; apply dom_lt_trie_all_set;
      try assumption; cbn [fst snd]; split; lia.
Qed.

(** Interior placement increases an endpoint by at most its size or the single successor. *)
Lemma dom_order_anchor_insert_bound unit current capacity parents sizes caps st entry :
  (1 <= unit)%N -> (capacity <= current)%N ->
  (forall v, (dom_anchor_size sizes v <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= capacity)%N) caps ->
  dom_order_anchor_state_bound current st ->
  dom_order_anchor_state_bound (current + unit)%N
    (dom_anchor_insert parents sizes caps st entry).
Proof.
  intros Hunit Hcapacity Hsizes Hcaps Hstate. destruct entry as [[v anchor] witness].
  pose proof (Hsizes v) as Hsize.
  unfold dom_anchor_insert. cbn beta iota zeta.
  destruct (N.eqb anchor (dom_lt_identity parents v)).
  - eapply dom_order_anchor_at_parent_bound; eassumption.
  - destruct (trie_get (dom_lt_key anchor) (anchor_intervals st)) as [[lo hi]|] eqn:Hget.
    + destruct (proj1 Hstate _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in Hlo, Hhi.
      destruct (dom_order_anchor_state_mono current (current + unit)%N st ltac:(lia) Hstate)
        as [Hintervals Hfree].
      destruct (N.ltb (dom_anchor_start (anchor_intervals st) witness) lo);
        split; cbn [anchor_intervals anchor_free]; try exact Hfree.
      all: apply dom_lt_trie_all_set;
        [apply dom_lt_trie_all_set; [exact Hintervals|]|]; cbn [fst snd]; split; lia.
    + eapply dom_order_anchor_at_parent_bound; eassumption.
Qed.

(** A fold of insertions pays one endpoint increment per record. *)
Lemma dom_order_anchor_insert_fold_bound unit capacity parents sizes caps entries st current :
  (1 <= unit)%N -> (capacity <= current)%N ->
  (forall v, (dom_anchor_size sizes v <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= capacity)%N) caps ->
  dom_order_anchor_state_bound current st ->
  dom_order_anchor_state_bound (current + N.of_nat (length entries) * unit)%N
    (fold_left (dom_anchor_insert parents sizes caps) entries st).
Proof.
  intros Hunit Hcapacity Hsizes Hcaps. revert st current Hcapacity.
  induction entries as [|entry rest IH]; intros st current Hcapacity Hstate.
  - change (dom_order_anchor_state_bound (current + 0)%N st).
    rewrite N.add_0_r. exact Hstate.
  - cbn [fold_left length]. rewrite Nat2N.inj_succ.
    replace (current + N.succ (N.of_nat (length rest)) * unit)%N with
      ((current + unit) + N.of_nat (length rest) * unit)%N by nia.
    apply IH; [lia|]. eapply dom_order_anchor_insert_bound; eassumption.
Qed.

(** Every constructed anchor interval has polynomially bounded numeric endpoints. *)
Lemma dom_order_anchor_endpoints bound parents removed :
  dom_lt_trie_all (fun n => (n <= bound)%N) parents ->
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) removed ->
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) removed) ->
  (N.of_nat (length removed) <= bound)%N ->
  dom_lt_trie_all (fun pair => let '(lo, hi) := pair in
    (lo <= 8 * (bound + 1) * (bound + 1) /\
     hi <= 8 * (bound + 1) * (bound + 1))%N) (dom_anchor_order parents removed).
Proof.
  intros Hparents Hrecords Hunique Hcount.
  set (count := N.of_nat (length removed)).
  set (unit := (2 * count + 1)%N).
  set (sizes := dom_anchor_sizes parents removed).
  set (caps := dom_anchor_capacity parents sizes removed).
  assert (Hsizes : forall v, (dom_anchor_size sizes v <= unit)%N).
  { intro v. now apply dom_anchor_sizes_value_bound. }
  assert (Hcaps : dom_lt_trie_all (fun n => (n <= count * unit)%N) caps).
  { apply dom_order_anchor_capacity_bound. exact Hsizes. }
  assert (Hinitial : dom_order_anchor_state_bound (count * unit)%N (DomAnchorState Empty Empty)).
  { split; apply dom_lt_trie_all_empty. }
  pose proof (dom_order_anchor_insert_fold_bound unit (count * unit)%N parents sizes caps
    removed (DomAnchorState Empty Empty) (count * unit)%N ltac:(unfold unit; lia)
    (N.le_refl _) Hsizes Hcaps Hinitial) as Hfinal.
  fold count in Hfinal.
  destruct Hfinal as [Hintervals Hfree].
  unfold dom_anchor_order. fold sizes caps.
  intros key [lo hi] Hget. destruct (Hintervals _ _ Hget) as [Hlo Hhi].
  cbn [fst snd] in Hlo, Hhi. fold count in Hcount. unfold unit in Hlo, Hhi.
  assert (Hsquare : (count * count <= bound * bound)%N).
  { apply N.mul_le_mono; exact Hcount. }
  clearbody count sizes caps. clear -Hlo Hhi Hcount Hsquare. split; nia.
Qed.

(** * Anchor callback clocks

    Public trie clock bounds and binary operand budgets account for each callback. *)

(** Subtraction reads no more than both binary operands and its outer branch. *)
Lemma dom_order_anchor_sub_clock left right :
  (N.T_sub left right <= N.of_nat (N.size_nat left + N.size_nat right) + 1)%N.
Proof.
  destruct left as [|left], right as [|right];
    try pose proof (proj1 (Pos.T_sub_mask_both left right)); time_step.
Qed.

(** A write through a numeric key pays for its encoded key and the trie traversal. *)
Lemma dom_order_anchor_set_clock {A : Type} width rank (value : A) table :
  N.size_nat rank <= width ->
  (PTrieCode.T_set (dom_lt_key rank) value table <=
    2 * PTrieT.c_trie * N.of_nat (width + 1))%N.
Proof.
  intro Hrank. pose proof (dom_lt_key_width rank) as Hkey.
  pose proof (PTrieT.T_set_le A (dom_lt_key rank) value table) as Hset.
  change (PTrieCode.T_set (dom_lt_key rank) value table <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat (dom_lt_key rank) + 1))%N in Hset.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** A size lookup has the same bounded-key traversal as an identity lookup. *)
Lemma dom_order_anchor_size_clock width sizes v :
  N.size_nat v <= width ->
  (T_dom_anchor_size sizes v <= 16 * N.of_nat (width + 1))%N.
Proof.
  intro Hv. pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  unfold T_dom_anchor_size. time_simpl. PTrieT.trie_get_le.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** A zero-default numeric lookup spends only its encoded input-key width. *)
Lemma dom_order_anchor_number_clock width table v :
  N.size_nat v <= width ->
  (T_dom_order_number table v <= 16 * N.of_nat (width + 1))%N.
Proof.
  intro Hv. pose proof (dom_lt_time_key v) as Hkey.
  pose proof (dom_lt_key_width v) as Hwidth.
  unfold T_dom_order_number. time_simpl. PTrieT.trie_get_le.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Reinstalling a size observation preserves every later size observation. *)
Lemma dom_order_anchor_size_set_own sizes v x :
  dom_anchor_size (PTrieCode.set (dom_lt_key v) (dom_anchor_size sizes v) sizes) x =
    dom_anchor_size sizes x.
Proof.
  change (dom_size_get
    (PTrieCode.set (dom_lt_key v) (dom_size_get sizes (dom_lt_key v)) sizes)
    (dom_lt_key x) = dom_size_get sizes (dom_lt_key x)).
  apply dom_size_set_own.
Qed.

(** One size transfer performs two bounded lookups and at most two bounded writes. *)
Lemma dom_order_anchor_transfer_clock width parents sizes v anchor witness :
  N.size_nat v <= width -> N.size_nat anchor <= width ->
  (forall x, N.size_nat (dom_anchor_size sizes x) <= width) ->
  (T_dom_order_anchor_transfer parents sizes (v, anchor, witness) <=
    256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hanchor Hvalues.
  set (own := dom_anchor_size sizes v).
  set (stored := PTrieCode.set (dom_lt_key v) own sizes).
  pose proof (dom_order_anchor_size_clock width sizes v Hv) as Hsize.
  pose proof (dom_lt_time_key v) as Hvkey.
  pose proof (dom_lt_time_key anchor) as Hakey.
  pose proof (dom_lt_time_identity parents v) as Hparent.
  pose proof (N.T_eqb_le anchor (dom_lt_identity parents v)) as Hcompare.
  pose proof (dom_order_anchor_set_clock width v own sizes Hv) as Hsetv.
  unfold T_dom_order_anchor_transfer. cbn beta iota zeta. fold own stored.
  destruct (N.eqb anchor (dom_lt_identity parents v)).
  - time_simpl. fold own stored. rewrite !Nat2N.inj_add in *.
    clear -Hv Hanchor Hsize Hvkey Hparent Hcompare Hsetv. nia.
  - pose proof (dom_order_anchor_size_clock width stored anchor Hanchor) as Hanchor_size.
    pose proof (dom_order_anchor_set_clock width anchor
      (own + dom_anchor_size stored anchor)%N stored Hanchor) as Hseta.
    pose proof (N.T_add_le own (dom_anchor_size stored anchor)) as Hadd.
    assert (Hown : N.size_nat own <= width) by (apply Hvalues).
    assert (Hstored : N.size_nat (dom_anchor_size stored anchor) <= width).
    { unfold stored, own. rewrite dom_order_anchor_size_set_own. apply Hvalues. }
    time_simpl. fold own stored. rewrite !Nat2N.inj_add in *.
    clearbody own stored. clear -Hv Hanchor Hown Hstored Hsize Hanchor_size
      Hvkey Hakey Hparent Hcompare Hsetv Hseta Hadd. nia.
Qed.

(** One capacity transfer reads one parent and adds one bounded size to one bounded capacity. *)
Lemma dom_order_anchor_capacity_step_clock width parents sizes caps v anchor witness :
  N.size_nat v <= width -> N.size_nat anchor <= width ->
  N.size_nat (dom_lt_identity parents v) <= width ->
  N.size_nat (dom_order_number caps (dom_lt_identity parents v)) <= width ->
  N.size_nat (dom_anchor_size sizes v) <= width ->
  (T_dom_order_anchor_capacity_step parents sizes caps (v, anchor, witness) <=
    256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hanchor Hp Hcapacity Hsize.
  set (p := dom_lt_identity parents v).
  fold p in Hp, Hcapacity.
  pose proof (dom_lt_time_identity parents v) as Hparent.
  pose proof (N.T_eqb_le anchor p) as Hcompare.
  pose proof (dom_lt_time_key p) as Hkey.
  pose proof (dom_order_anchor_number_clock width caps p Hp) as Hnumber.
  pose proof (dom_order_anchor_size_clock width sizes v Hv) as Hsize_clock.
  pose proof (N.T_add_le (dom_order_number caps p) (dom_anchor_size sizes v)) as Hadd.
  pose proof (dom_order_anchor_set_clock width p
    (dom_order_number caps p + dom_anchor_size sizes v)%N caps Hp) as Hset.
  unfold T_dom_order_anchor_capacity_step. cbn beta iota zeta. fold p.
  destruct (N.eqb anchor p); time_simpl; fold p;
    rewrite !Nat2N.inj_add in *; clearbody p;
    clear -Hv Hanchor Hp Hcapacity Hsize Hparent Hcompare Hkey Hnumber Hsize_clock Hadd Hset;
    nia.
Qed.

(** Every observed interval start is within its endpoint budget. *)
Lemma dom_order_anchor_start_bound bound intervals v :
  dom_lt_trie_all (fun pair => (fst pair <= bound /\ snd pair <= bound)%N) intervals ->
  (dom_anchor_start intervals v <= bound)%N.
Proof.
  intro Hintervals. unfold dom_anchor_start.
  destruct (trie_get (dom_lt_key v) intervals) as [[lo hi]|] eqn:Hget; [|lia].
  exact (proj1 (Hintervals _ _ Hget)).
Qed.

(** Parent insertion reads and writes bounded keys and endpoint arithmetic operands. *)
Lemma dom_order_anchor_at_parent_clock width current unit caps st v p size :
  N.size_nat v <= width -> N.size_nat p <= width -> (size <= unit)%N ->
  dom_lt_trie_all (fun n => (n <= current)%N) caps ->
  dom_order_anchor_state_bound current st ->
  (forall n, (n <= current + unit + 1)%N -> N.size_nat n <= width) ->
  (T_dom_anchor_at_parent caps st v p size <=
    512 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hp Hsize Hcaps Hstate Hwidth.
  pose proof (dom_lt_time_key v) as Hvkey.
  pose proof (dom_lt_time_key p) as Hpkey.
  pose proof (dom_lt_key_width p) as Hpwidth.
  assert (Hsize_width : N.size_nat size <= width) by (apply Hwidth; lia).
  unfold T_dom_anchor_at_parent. time_simpl.
  pose proof (PTrieT.T_trie_get_le _ (dom_lt_key p) (anchor_free st)) as Hfree_get.
  destruct (trie_get (dom_lt_key p) (anchor_free st)) as [[lo hi]|] eqn:Hget.
  - destruct (proj2 Hstate _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in Hlo, Hhi.
    assert (Hlo_width : N.size_nat lo <= width) by (apply Hwidth; lia).
    assert (Hsum_width : N.size_nat (lo + size) <= width) by (apply Hwidth; lia).
    pose proof (N.T_add_le lo size) as Hadd.
    pose proof (N.T_pred_le (lo + size)) as Hpred.
    pose proof (dom_order_anchor_set_clock width v (lo, N.pred (lo + size))
      (anchor_intervals st) Hv) as Hsetv.
    pose proof (dom_order_anchor_set_clock width p (lo + size, hi)%N
      (anchor_free st) Hp) as Hsetp.
    time_simpl. rewrite !Nat2N.inj_add in *.
    set (v_bits := N.size_nat v) in *.
    set (p_bits := N.size_nat p) in *.
    set (key_bits := Pos.size_nat (dom_lt_key p)) in *.
    set (size_bits := N.size_nat size) in *.
    set (lo_bits := N.size_nat lo) in *.
    set (sum_bits := N.size_nat (lo + size)) in *.
    set (key_v_work := T_dom_lt_key v) in *.
    set (key_p_work := T_dom_lt_key p) in *.
    set (add_work := N.T_add lo size) in *.
    set (pred_work := N.T_pred (lo + size)) in *.
    set (set_v_work := PTrieCode.T_set (dom_lt_key v)
      (lo, N.pred (lo + size)) (anchor_intervals st)) in *.
    set (set_p_work := PTrieCode.T_set (dom_lt_key p)
      (lo + size, hi)%N (anchor_free st)) in *.
    set (trie_coefficient := PTrieT.c_trie) in *.
    clearbody v_bits p_bits key_bits size_bits lo_bits sum_bits key_v_work key_p_work
      add_work pred_work set_v_work set_p_work trie_coefficient.
    clear -Hv Hp Hsize_width Hlo_width Hsum_width Hvkey Hpkey Hpwidth Hadd Hpred Hsetv Hsetp
      Hfree_get.
    change (N.of_nat 1) with 1%N in *.
    set (write_budget := (trie_coefficient * (N.of_nat width + 1))%N).
    replace (2 * trie_coefficient * (N.of_nat width + 1))%N with
      (2 * write_budget)%N in Hsetv, Hsetp by (unfold write_budget; ring).
    replace (512 * (trie_coefficient + 1) * (N.of_nat width + 1))%N with
      (512 * write_budget + 512 * (N.of_nat width + 1))%N
      by (unfold write_budget; ring).
    clearbody write_budget. lia.
  - pose proof (dom_order_anchor_number_bound current caps p Hcaps) as Hnumber_bound.
    assert (Hnumber_width : N.size_nat (dom_order_number caps p) <= width).
    { apply Hwidth. lia. }
    pose proof (dom_order_anchor_number_clock width caps p Hp) as Hnumber.
    pose proof (N.T_pred_le (dom_order_number caps p)) as Hcapacity_pred.
    pose proof (N.T_add_le 0 size) as Hadd.
    pose proof (N.T_pred_le (0 + size)) as Hpred.
    pose proof (dom_order_anchor_set_clock width v (0%N, N.pred (0 + size))
      (anchor_intervals st) Hv) as Hsetv.
    pose proof (dom_order_anchor_set_clock width p (0 + size, N.pred (dom_order_number caps p))%N
      (anchor_free st) Hp) as Hsetp.
    time_simpl.
    change (0 + size)%N with size in *.
    change (N.T_add 0 size <= N.of_nat (N.size_nat size) + 1)%N in Hadd.
    change (N.T_pred size <= N.of_nat (N.size_nat size) + 2)%N in Hpred.
    rewrite !Nat2N.inj_add in *.
    set (v_bits := N.size_nat v) in *.
    set (p_bits := N.size_nat p) in *.
    set (key_bits := Pos.size_nat (dom_lt_key p)) in *.
    set (size_bits := N.size_nat size) in *.
    set (number_bits := N.size_nat (dom_order_number caps p)) in *.
    set (key_v_work := T_dom_lt_key v) in *.
    set (key_p_work := T_dom_lt_key p) in *.
    set (number_work := T_dom_order_number caps p) in *.
    set (capacity_pred_work := N.T_pred (dom_order_number caps p)) in *.
    set (add_work := N.T_add 0 size) in *.
    set (pred_work := N.T_pred size) in *.
    set (set_v_work := PTrieCode.T_set (dom_lt_key v)
      (0%N, N.pred size) (anchor_intervals st)) in *.
    set (set_p_work := PTrieCode.T_set (dom_lt_key p)
      (size, N.pred (dom_order_number caps p)) (anchor_free st)) in *.
    set (trie_coefficient := PTrieT.c_trie) in *.
    clearbody v_bits p_bits key_bits size_bits number_bits key_v_work key_p_work
      number_work capacity_pred_work add_work pred_work set_v_work set_p_work trie_coefficient.
    clear -Hv Hp Hsize_width Hnumber_width Hvkey Hpkey Hpwidth Hnumber
      Hcapacity_pred Hadd Hpred Hsetv Hsetp Hfree_get.
    change (N.of_nat 1) with 1%N in *.
    set (write_budget := (trie_coefficient * (N.of_nat width + 1))%N).
    replace (2 * trie_coefficient * (N.of_nat width + 1))%N with
      (2 * write_budget)%N in Hsetv, Hsetp by (unfold write_budget; ring).
    replace (512 * (trie_coefficient + 1) * (N.of_nat width + 1))%N with
      (512 * write_budget + 512 * (N.of_nat width + 1))%N
      by (unfold write_budget; ring).
    clearbody write_budget. lia.
Qed.

Local Opaque dom_anchor_at_parent T_dom_anchor_at_parent.

(** One anchor insertion has bounded lookup, comparison, arithmetic and write costs. *)
Lemma dom_order_anchor_insert_clock width current unit parents sizes caps st v anchor witness :
  N.size_nat v <= width -> N.size_nat anchor <= width -> N.size_nat witness <= width ->
  N.size_nat (dom_lt_identity parents v) <= width ->
  (forall x, (dom_anchor_size sizes x <= unit)%N) ->
  dom_lt_trie_all (fun n => (n <= current)%N) caps ->
  dom_order_anchor_state_bound current st ->
  (forall n, (n <= current + unit + 1)%N -> N.size_nat n <= width) ->
  (T_dom_anchor_insert parents sizes caps st (v, anchor, witness) <=
    1024 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hanchor Hw Hp Hsizes Hcaps Hstate Hwidth.
  set (p := dom_lt_identity parents v).
  fold p in Hp.
  set (size := dom_anchor_size sizes v).
  pose proof (Hsizes v) as Hsize. fold size in Hsize.
  pose proof (dom_lt_time_identity parents v) as Hparent.
  pose proof (dom_order_anchor_size_clock width sizes v Hv) as Hsize_clock.
  pose proof (N.T_eqb_le anchor p) as Hcompare.
  pose proof (dom_order_anchor_at_parent_clock width current unit caps st v p size
    Hv Hp Hsize Hcaps Hstate Hwidth) as Hatparent.
  pose proof (dom_lt_time_key anchor) as Hakey.
  pose proof (dom_lt_key_width anchor) as Hawidth.
  unfold T_dom_anchor_insert. cbn beta iota zeta. fold p size.
  destruct (N.eqb anchor p).
  - time_simpl. fold p size. rewrite !Nat2N.inj_add in *.
    clearbody p size. clear -Hv Hanchor Hparent Hsize_clock Hcompare Hatparent.
    change (N.of_nat 1) with 1%N in *.
    set (write_budget := (PTrieT.c_trie * (N.of_nat width + 1))%N).
    replace (512 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
      (512 * write_budget + 512 * (N.of_nat width + 1))%N
      in Hatparent by (unfold write_budget; ring).
    replace (1024 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
      (1024 * write_budget + 1024 * (N.of_nat width + 1))%N
      by (unfold write_budget; ring).
    clearbody write_budget. lia.
  - destruct (trie_get (dom_lt_key anchor) (anchor_intervals st)) as [[lo hi]|] eqn:Hget.
    2: { time_simpl. fold p size.
         rewrite !Nat2N.inj_add in *. clearbody p size.
         clear -Hv Hanchor Hparent Hsize_clock Hcompare Hatparent Hakey Hawidth.
         PTrieT.trie_get_le.
         change (N.of_nat 1) with 1%N in *.
         set (write_budget := (PTrieT.c_trie * (N.of_nat width + 1))%N).
         replace (512 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
           (512 * write_budget + 512 * (N.of_nat width + 1))%N
           in Hatparent by (unfold write_budget; ring).
         replace (1024 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
           (1024 * write_budget + 1024 * (N.of_nat width + 1))%N
           by (unfold write_budget; ring).
         clearbody write_budget. lia. }
    destruct (proj1 Hstate _ _ Hget) as [Hlo Hhi]. cbn [fst snd] in Hlo, Hhi.
    pose proof (dom_order_anchor_start_bound current (anchor_intervals st) witness
      (proj1 Hstate)) as Hwstart.
    assert (Hstart_width : N.size_nat (dom_anchor_start (anchor_intervals st) witness) <= width)
      by (apply Hwidth; lia).
    assert (Hlo_width : N.size_nat lo <= width) by (apply Hwidth; lia).
    assert (Hhi_width : N.size_nat hi <= width) by (apply Hwidth; lia).
    assert (Hsize_width : N.size_nat size <= width) by (apply Hwidth; lia).
    assert (Hsum_width : N.size_nat (lo + size) <= width) by (apply Hwidth; lia).
    assert (Hsucc_width : N.size_nat (N.succ hi) <= width) by (apply Hwidth; lia).
    pose proof (dom_order_anchor_start_clock width (anchor_intervals st) witness Hw) as Hstart.
    pose proof (dom_lt_time_ltb (dom_anchor_start (anchor_intervals st) witness) lo) as Hltb.
    pose proof (dom_lt_time_key v) as Hvkey.
    destruct (N.ltb (dom_anchor_start (anchor_intervals st) witness) lo).
    + pose proof (N.T_add_le lo size) as Hadd.
      pose proof (N.T_pred_le (lo + size)) as Hpred.
      pose proof (dom_order_anchor_set_clock width anchor (lo + size, hi)%N
        (anchor_intervals st) Hanchor) as Hseta.
      pose proof (dom_order_anchor_set_clock width v (lo, N.pred (lo + size))
        (PTrieCode.set (dom_lt_key anchor) (lo + size, hi)%N (anchor_intervals st)) Hv) as Hsetv.
      time_simpl. fold p size.
      rewrite !Nat2N.inj_add in *. clearbody p size.
      clear -Hv Hanchor Hparent Hsize_clock Hcompare Hakey Hawidth Hstart Hltb Hvkey
        Hstart_width Hlo_width Hsize_width Hsum_width Hadd Hpred Hseta Hsetv.
      PTrieT.trie_get_le.
      change (N.of_nat 1) with 1%N in *.
      set (write_budget := (PTrieT.c_trie * (N.of_nat width + 1))%N).
      replace (2 * PTrieT.c_trie * (N.of_nat width + 1))%N with
        (2 * write_budget)%N in Hseta, Hsetv by (unfold write_budget; ring).
      replace (1024 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
        (1024 * write_budget + 1024 * (N.of_nat width + 1))%N
        by (unfold write_budget; ring).
      clearbody write_budget. lia.
    + pose proof (N.T_succ_le hi) as Hsucc.
      pose proof (dom_order_anchor_sub_clock (N.succ hi) size) as Hsubown.
      pose proof (dom_order_anchor_sub_clock hi size) as Hsubrest.
      pose proof (dom_order_anchor_set_clock width anchor (lo, hi - size)%N
        (anchor_intervals st) Hanchor) as Hseta.
      pose proof (dom_order_anchor_set_clock width v (N.succ hi - size, hi)%N
        (PTrieCode.set (dom_lt_key anchor) (lo, hi - size)%N (anchor_intervals st)) Hv) as Hsetv.
      time_simpl. fold p size.
      rewrite !Nat2N.inj_add in *. clearbody p size.
      clear -Hv Hanchor Hparent Hsize_clock Hcompare Hakey Hawidth Hstart Hltb Hvkey
        Hstart_width Hhi_width Hsize_width Hsucc_width Hsucc Hsubown Hsubrest Hseta Hsetv.
      PTrieT.trie_get_le.
      change (N.of_nat 1) with 1%N in *.
      set (write_budget := (PTrieT.c_trie * (N.of_nat width + 1))%N).
      replace (2 * PTrieT.c_trie * (N.of_nat width + 1))%N with
        (2 * write_budget)%N in Hseta, Hsetv by (unfold write_budget; ring).
      replace (1024 * (PTrieT.c_trie + 1) * (N.of_nat width + 1))%N with
        (1024 * write_budget + 1024 * (N.of_nat width + 1))%N
        by (unfold write_budget; ring).
      clearbody write_budget. lia.
Qed.

(** * Complete anchor clock composition

    All three linear anchor passes share one polynomial numeric value budget. *)

(** A bounded callback fold pays one uniform callback charge and one list-cell charge. *)
Lemma dom_order_anchor_fold_linear {A B : Type} (step : A -> B -> A)
    (T_step : A -> B -> N) (Valid : B -> Prop) (Bound : N -> A -> Prop)
    increment limit charge :
  (forall current st value, (current + increment <= limit)%N ->
    Valid value -> Bound current st -> Bound (current + increment)%N (step st value)) ->
  (forall current st value, (current + increment <= limit)%N ->
    Valid value -> Bound current st -> (T_step st value <= charge)%N) ->
  forall entries st current, Forall Valid entries ->
  (current + N.of_nat (length entries) * increment <= limit)%N -> Bound current st ->
  (List.T_fold_left step T_step entries st <=
    (charge + 1) * N.of_nat (length entries) + 1)%N.
Proof.
  intros Hpreserve Hclock entries. induction entries as [|value rest IH];
    intros st current Hentries Htotal Hbound.
  - cbn [length]. time_unfold @List.T_fold_left. nia.
  - inversion Hentries as [|head tail Hvalue Hrest]; subst head tail.
    assert (Hhead : (current + increment <= limit)%N).
    { cbn [length] in Htotal. rewrite Nat2N.inj_succ in Htotal. nia. }
    pose proof (Hclock current st value Hhead Hvalue Hbound) as Hstep.
    pose proof (Hpreserve current st value Hhead Hvalue Hbound) as Hnext.
    assert (Htail : (current + increment + N.of_nat (length rest) * increment <= limit)%N).
    { cbn [length] in Htotal. rewrite Nat2N.inj_succ in Htotal. nia. }
    specialize (IH (step st value) (current + increment)%N Hrest Htail Hnext).
    time_unfold @List.T_fold_left. fold (List.T_fold_left step T_step).
    cbn [length]. rewrite Nat2N.inj_succ. clear -Hstep IH. nia.
Qed.

(** The anchor-size wrapper is its reversal and the generated transfer-fold clock. *)
Lemma dom_order_anchor_sizes_clock_equation parents removed :
  T_dom_anchor_sizes parents removed =
    (1 + (List.T_rev_append removed [] +
      List.T_fold_left (dom_order_anchor_transfer parents)
        (T_dom_order_anchor_transfer parents) (rev_append removed []) Empty))%N.
Proof.
  unfold T_dom_anchor_sizes, T_dom_order_anchor_transfer, dom_order_anchor_transfer.
  time_simpl. reflexivity.
Qed.

(** The capacity wrapper is the generated capacity-fold clock and its own call. *)
Lemma dom_order_anchor_capacity_clock_equation parents sizes removed :
  T_dom_anchor_capacity parents sizes removed =
    (1 + List.T_fold_left (dom_order_anchor_capacity_step parents sizes)
      (T_dom_order_anchor_capacity_step parents sizes) removed Empty)%N.
Proof.
  unfold T_dom_anchor_capacity, T_dom_order_anchor_capacity_step,
    dom_order_anchor_capacity_step.
  time_simpl. reflexivity.
Qed.

Local Opaque dom_order_anchor_transfer T_dom_order_anchor_transfer
  dom_order_anchor_capacity_step T_dom_order_anchor_capacity_step
  dom_anchor_insert T_dom_anchor_insert.

(** Distinct retirement keeps every intermediate size operand within the original budget. *)
Lemma dom_order_anchor_size_fold_clock width limit bound parents entries sizes :
  (forall value, (value <= bound)%N -> N.size_nat value <= width) ->
  (forall value, (value <= 2 * limit + 1)%N -> N.size_nat value <= width) ->
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) entries ->
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) entries) ->
  dom_size_budget limit (map (fun entry => dom_lt_key (fst (fst entry))) entries) sizes ->
  (List.T_fold_left (dom_order_anchor_transfer parents)
    (T_dom_order_anchor_transfer parents) entries sizes <=
    (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) + 1) *
      N.of_nat (length entries) + 1)%N.
Proof.
  intros Hkeys Hvalues Hentries Hunique Hbudget.
  set (Inv := fun remaining state =>
    Forall (fun entry => let '(v, anchor, witness) := entry in
      (v <= bound /\ anchor <= bound /\ witness <= bound)%N) remaining /\
    NoDup (map (fun entry => dom_lt_key (fst (fst entry))) remaining) /\
    dom_size_budget limit
      (map (fun entry => dom_lt_key (fst (fst entry))) remaining) state).
  assert (Hpreserve : forall entry rest state, Inv (entry :: rest) state ->
    Inv rest (dom_order_anchor_transfer parents state entry)).
  { intros [[v anchor] witness] rest state [Hr [Hu Hb]].
    inversion Hr as [|head tail Hhead Hrest]; subst head tail.
    cbn [map fst] in Hu, Hb. inversion Hu as [|head tail Hfresh Htail]; subst head tail.
    split; [exact Hrest|]. split; [exact Htail|].
    now apply dom_order_anchor_transfer_budget. }
  assert (Hcost : forall entry rest state, Inv (entry :: rest) state ->
    (T_dom_order_anchor_transfer parents state entry + 0 <=
      0 + 256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  { intros [[v anchor] witness] rest state [Hr [Hu Hb]].
    inversion Hr as [|head tail Hhead Hrest]; subst head tail.
    cbn beta iota zeta in Hhead. destruct Hhead as [Hv [Ha Hw]].
    rewrite N.add_0_r, N.add_0_l. apply dom_order_anchor_transfer_clock;
      [now apply Hkeys|now apply Hkeys|].
    intro x. apply Hvalues.
    change (dom_size_get state (dom_lt_key x) <= 2 * limit + 1)%N.
    eapply dom_size_budget_value; exact Hb. }
  pose proof (dom_lt_fold_credit (dom_order_anchor_transfer parents)
    (T_dom_order_anchor_transfer parents) Inv (fun _ => 0%N)
    (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N entries Hpreserve Hcost sizes
    (conj Hentries (conj Hunique Hbudget))) as Hfold.
  cbn beta in Hfold. destruct Hfold as [Hfinal Htime].
  rewrite N.add_0_r, N.add_0_l in Htime. exact Htime.
Qed.

(** The public polynomial budget covers input ranks, sizes, capacities and endpoint successors. *)
Lemma dom_order_anchor_budget_arithmetic bound count : (count <= bound)%N ->
  (bound <= 8 * (bound + 1) * (bound + 1) /\
   2 * count + 1 <= 8 * (bound + 1) * (bound + 1) /\
   2 * count * (2 * count + 1) + (2 * count + 1) + 1 <=
     8 * (bound + 1) * (bound + 1))%N.
Proof.
  intro Hcount.
  assert (Hsquare : (count * count <= bound * bound)%N).
  { apply N.mul_le_mono; exact Hcount. }
  nia.
Qed.

(** Constructing anchor sizes takes linear work at the polynomial operand width. *)
Lemma dom_order_anchor_sizes_clock bound width parents removed :
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) removed ->
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) removed) ->
  (N.of_nat (length removed) <= bound)%N ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N ->
    N.size_nat value <= width) ->
  (T_dom_anchor_sizes parents removed <=
    512 * (PTrieT.c_trie + 1) * N.of_nat ((length removed + 1) * (width + 1)))%N.
Proof.
  intros Hrecords Hunique Hcount Hwidth.
  destruct (dom_order_anchor_budget_arithmetic bound (N.of_nat (length removed)) Hcount)
    as [Hbound [Hunit Hendpoints]].
  assert (Hkeys : forall value, (value <= bound)%N -> N.size_nat value <= width).
  { intros value Hvalue. apply Hwidth. eapply N.le_trans; eassumption. }
  assert (Hvalues : forall value, (value <= 2 * N.of_nat (length removed) + 1)%N ->
    N.size_nat value <= width).
  { intros value Hvalue. apply Hwidth. eapply N.le_trans; eassumption. }
  assert (Hreverse : Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) (rev_append removed [])).
  { rewrite rev_append_rev, app_nil_r. now apply Forall_rev. }
  assert (Hreverse_unique : NoDup
    (map (fun entry => dom_lt_key (fst (fst entry))) (rev_append removed []))).
  { rewrite rev_append_rev, app_nil_r, map_rev. now apply NoDup_rev. }
  assert (Hbudget : dom_size_budget (N.of_nat (length removed))
    (map (fun entry => dom_lt_key (fst (fst entry))) (rev_append removed [])) Empty).
  { replace (N.of_nat (length removed)) with
      (N.of_nat (length (map (fun entry => dom_lt_key (fst (fst entry)))
        (rev_append removed [])))); [apply dom_size_budget_empty|].
    now rewrite length_map, rev_append_rev, app_nil_r, length_rev. }
  pose proof (dom_order_anchor_size_fold_clock width (N.of_nat (length removed)) bound
    parents (rev_append removed []) Empty Hkeys Hvalues Hreverse Hreverse_unique Hbudget)
    as Hfold.
  replace (length (rev_append removed [])) with (length removed) in Hfold
    by (rewrite rev_append_rev, app_nil_r, length_rev; reflexivity).
  pose proof (List.T_rev_append_le removed []) as Hreverse_clock.
  rewrite dom_order_anchor_sizes_clock_equation.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  clear -Hfold Hreverse_clock. nia.
Qed.

(** Constructing capacities adds at most one bounded size per removal. *)
Lemma dom_order_anchor_capacity_clock bound width parents sizes removed :
  dom_lt_trie_all (fun n => (n <= bound)%N) parents ->
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) removed ->
  (N.of_nat (length removed) <= bound)%N ->
  (forall v, (dom_anchor_size sizes v <= 2 * N.of_nat (length removed) + 1)%N) ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N ->
    N.size_nat value <= width) ->
  (T_dom_anchor_capacity parents sizes removed <=
    512 * (PTrieT.c_trie + 1) * N.of_nat ((length removed + 1) * (width + 1)))%N.
Proof.
  intros Hparents Hrecords Hcount Hsizes Hwidth.
  set (count := N.of_nat (length removed)). set (unit := (2 * count + 1)%N).
  fold count in Hcount, Hsizes.
  destruct (dom_order_anchor_budget_arithmetic bound count Hcount)
    as [Hbound [Hunit Hendpoints]].
  assert (Hkeys : forall value, (value <= bound)%N -> N.size_nat value <= width).
  { intros value Hvalue. apply Hwidth. eapply N.le_trans; eassumption. }
  pose proof (dom_order_anchor_fold_linear
    (dom_order_anchor_capacity_step parents sizes)
    (T_dom_order_anchor_capacity_step parents sizes)
    (fun entry => let '(v, anchor, witness) := entry in
      (v <= bound /\ anchor <= bound /\ witness <= bound)%N)
    (fun current caps => dom_lt_trie_all (fun n => (n <= current)%N) caps)
    unit (count * unit)%N (256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N)
    as Hfold.
  assert (Hpreserve : forall current caps entry, (current + unit <= count * unit)%N ->
    (let '(v, anchor, witness) := entry in (v <= bound /\ anchor <= bound /\ witness <= bound)%N) ->
    dom_lt_trie_all (fun n => (n <= current)%N) caps ->
    dom_lt_trie_all (fun n => (n <= current + unit)%N)
      (dom_order_anchor_capacity_step parents sizes caps entry)).
  { intros current caps entry Hcurrent Hentry Hcaps.
    apply dom_order_anchor_capacity_step_bound; [exact Hsizes|exact Hcaps]. }
  assert (Hclock : forall current caps entry, (current + unit <= count * unit)%N ->
    (let '(v, anchor, witness) := entry in (v <= bound /\ anchor <= bound /\ witness <= bound)%N) ->
    dom_lt_trie_all (fun n => (n <= current)%N) caps ->
    (T_dom_order_anchor_capacity_step parents sizes caps entry <=
      256 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  { intros current caps [[v anchor] witness] Hcurrent [Hv [Ha Hw]] Hcaps.
    pose proof (dom_lt_identity_bounded bound parents v Hparents Hv) as Hp.
    apply dom_order_anchor_capacity_step_clock; try now apply Hkeys.
    - apply Hwidth. pose proof (dom_order_anchor_number_bound current caps
        (dom_lt_identity parents v) Hcaps) as Hnumber.
      fold unit in Hendpoints. nia.
    - apply Hwidth. pose proof (Hsizes v) as Hsize. fold unit in Hsize, Hunit. nia. }
  specialize (Hfold Hpreserve Hclock removed Empty 0%N Hrecords ltac:(unfold count; nia)
    (dom_lt_trie_all_empty _)).
  rewrite dom_order_anchor_capacity_clock_equation.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  clear -Hfold. nia.
Qed.

(** The insertion fold has linear cost while its endpoint budget grows by one size per record. *)
Lemma dom_order_anchor_insert_fold_clock bound width parents sizes caps removed :
  dom_lt_trie_all (fun n => (n <= bound)%N) parents ->
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) removed ->
  (N.of_nat (length removed) <= bound)%N ->
  (forall v, (dom_anchor_size sizes v <= 2 * N.of_nat (length removed) + 1)%N) ->
  dom_lt_trie_all (fun n =>
    (n <= N.of_nat (length removed) * (2 * N.of_nat (length removed) + 1))%N) caps ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N ->
    N.size_nat value <= width) ->
  (List.T_fold_left (dom_anchor_insert parents sizes caps)
    (T_dom_anchor_insert parents sizes caps) removed (DomAnchorState Empty Empty) <=
    2048 * (PTrieT.c_trie + 1) * N.of_nat ((length removed + 1) * (width + 1)))%N.
Proof.
  intros Hparents Hrecords Hcount Hsizes Hcaps Hwidth.
  set (count := N.of_nat (length removed)). set (unit := (2 * count + 1)%N).
  fold count in Hcount, Hsizes, Hcaps.
  destruct (dom_order_anchor_budget_arithmetic bound count Hcount)
    as [Hbound [Hunit Hendpoints]].
  fold unit in Hsizes, Hcaps, Hunit, Hendpoints.
  assert (Hkeys : forall value, (value <= bound)%N -> N.size_nat value <= width).
  { intros value Hvalue. apply Hwidth. eapply N.le_trans; eassumption. }
  set (Bound := fun current st =>
    (count * unit <= current)%N /\ dom_order_anchor_state_bound current st).
  assert (Hpreserve : forall current st entry, (current + unit <= 2 * count * unit)%N ->
    (let '(v, anchor, witness) := entry in (v <= bound /\ anchor <= bound /\ witness <= bound)%N) ->
    Bound current st -> Bound (current + unit)%N (dom_anchor_insert parents sizes caps st entry)).
  { intros current st entry Hcurrent Hentry [Hlower Hstate]. split; [lia|].
    eapply dom_order_anchor_insert_bound with (capacity := (count * unit)%N);
      try eassumption. unfold unit. lia. }
  assert (Hclock : forall current st entry, (current + unit <= 2 * count * unit)%N ->
    (let '(v, anchor, witness) := entry in (v <= bound /\ anchor <= bound /\ witness <= bound)%N) ->
    Bound current st ->
    (T_dom_anchor_insert parents sizes caps st entry <=
      1024 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N).
  { intros current st [[v anchor] witness] Hcurrent [Hv [Ha Hw]] [Hlower Hstate].
    apply (dom_order_anchor_insert_clock width current unit parents sizes caps st
      v anchor witness).
    - exact (Hkeys v Hv).
    - exact (Hkeys anchor Ha).
    - exact (Hkeys witness Hw).
    - apply Hkeys. exact (dom_lt_identity_bounded bound parents v Hparents Hv).
    - exact Hsizes.
    - exact (dom_order_anchor_values_mono (count * unit)%N current caps Hlower Hcaps).
    - exact Hstate.
    - intros value Hvalue. apply Hwidth.
      clear -Hvalue Hcurrent Hendpoints. nia. }
  assert (Hinitial : Bound (count * unit)%N (DomAnchorState Empty Empty)).
  { split; [reflexivity|]. split; apply dom_lt_trie_all_empty. }
  pose proof (dom_order_anchor_fold_linear (dom_anchor_insert parents sizes caps)
    (T_dom_anchor_insert parents sizes caps)
    (fun entry => let '(v, anchor, witness) := entry in
      (v <= bound /\ anchor <= bound /\ witness <= bound)%N)
    Bound unit (2 * count * unit)%N
    (1024 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N Hpreserve Hclock
    removed (DomAnchorState Empty Empty) (count * unit)%N Hrecords
    ltac:(unfold count; nia) Hinitial) as Hfold.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  clear -Hfold. nia.
Qed.

(** The anchor constructor has one closed coefficient for all three linear passes. *)
Definition dom_order_anchor_coefficient : N := (8192 * (PTrieT.c_trie + 1))%N.

(** Full anchor construction is linear in removals at the polynomial operand width. *)
Lemma dom_order_anchor_time bound width parents removed :
  dom_lt_trie_all (fun n => (n <= bound)%N) parents ->
  Forall (fun entry => let '(v, anchor, witness) := entry in
    (v <= bound /\ anchor <= bound /\ witness <= bound)%N) removed ->
  NoDup (map (fun entry => dom_lt_key (fst (fst entry))) removed) ->
  (N.of_nat (length removed) <= bound)%N ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N ->
    N.size_nat value <= width) ->
  (T_dom_anchor_order parents removed <= dom_order_anchor_coefficient *
    N.of_nat ((length removed + 1) * (width + 1)))%N.
Proof.
  intros Hparents Hrecords Hunique Hcount Hwidth.
  set (sizes := dom_anchor_sizes parents removed).
  set (caps := dom_anchor_capacity parents sizes removed).
  assert (Hsizes : forall v, (dom_anchor_size sizes v <= 2 * N.of_nat (length removed) + 1)%N).
  { intro v. now apply dom_anchor_sizes_value_bound. }
  pose proof (dom_order_anchor_capacity_bound (2 * N.of_nat (length removed) + 1)%N
    parents sizes removed Hsizes) as Hcaps. fold caps in Hcaps.
  pose proof (dom_order_anchor_sizes_clock bound width parents removed
    Hrecords Hunique Hcount Hwidth) as Hsize_clock.
  pose proof (dom_order_anchor_capacity_clock bound width parents sizes removed
    Hparents Hrecords Hcount Hsizes Hwidth) as Hcapacity_clock.
  pose proof (dom_order_anchor_insert_fold_clock bound width parents sizes caps removed
    Hparents Hrecords Hcount Hsizes Hcaps Hwidth) as Hinsert_clock.
  unfold T_dom_anchor_order. time_simpl. fold sizes caps.
  change (fun (st : dom_anchor_state) (entry : N * N * N) =>
    T_dom_anchor_insert parents sizes caps st entry) with
    (T_dom_anchor_insert parents sizes caps).
  unfold dom_order_anchor_coefficient. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
  clearbody sizes caps. clear -Hsize_clock Hcapacity_clock Hinsert_clock. nia.
Qed.

Local Transparent dom_order_anchor_transfer T_dom_order_anchor_transfer
  dom_order_anchor_capacity_step T_dom_order_anchor_capacity_step
  dom_anchor_insert T_dom_anchor_insert dom_anchor_at_parent T_dom_anchor_at_parent.

(* END G2-G ANCHOR SUPPORT *)

(** The assembly proof keeps its already-bounded executable phases abstract. *)
Local Opaque dom_lt_numeric_of dom_lt_semidominators dom_lt_buckets dom_lt_correct.
Local Opaque dom_order_source_maps T_dom_order_source_maps
  dom_order_removal T_dom_order_removal dom_anchor_order T_dom_anchor_order
  dom_order_sorted_rows T_dom_order_sorted_rows dom_order_emit T_dom_order_emit.

(** * Composition from the two remaining phase clocks *)

(** Raw finite inventories suffice for the complete order-of-result clock. *)
Lemma dom_order_of_result_composition (source_coefficient removal_coefficient : N) width result :
  let numeric := result_numeric result in
  let semi := result_semi result in
  let bucket := result_bucket result in
  let parents := result_parent result in
  let count := length (lt_numeric_order numeric) in
  let bound := N.of_nat count in
  let sources := dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents in
  NoDup (lt_numeric_order numeric) ->
  dom_lt_numeric_ranges bound numeric ->
  (lt_numeric_limit numeric <= N.of_nat (count + 1))%N ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_semis semi) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_minimizer semi) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_relative bucket) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N -> N.size_nat value <= width) ->
  (T_dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents <= source_coefficient *
      N.of_nat (dom_order_body_budget count
        (dom_lt_row_mass (map dom_lt_key (lt_numeric_order numeric)) (lt_numeric_pred numeric)) width))%N ->
  (T_dom_order_removal (lt_numeric_limit numeric) parents (lt_numeric_order numeric) sources <=
    removal_coefficient * N.of_nat ((count + 1) * (width + 1)))%N ->
  (T_dom_order_of_result result <= (source_coefficient + removal_coefficient + dom_order_anchor_coefficient +
      dom_order_sorted_rows_coefficient + 3 * dom_order_emit_coefficient + 64) *
    N.of_nat (dom_order_body_budget count
      (dom_lt_row_mass (map dom_lt_key (lt_numeric_order numeric)) (lt_numeric_pred numeric)) width))%N.
Proof.
  intros numeric semi bucket parents count bound sources Hunique Hranges Hlimit
    Hsemis Hminimizer Hrelative Hparents Hwidth Hsource_clock Hremove_clock.
  set (order := lt_numeric_order numeric) in *.
  set (predecessors := dom_lt_row_mass (map dom_lt_key order) (lt_numeric_pred numeric)) in *.
  set (budget := N.of_nat (dom_order_body_budget count predecessors width)) in *.
  assert (Horder : Forall (fun value => (value <= bound)%N) order).
  { exact (dom_lt_numeric_order_range _ _ Hranges). }
  assert (Hrank_width : forall value, (value <= bound)%N -> N.size_nat value <= width).
  { intros value Hvalue. eapply dom_order_linear_value_width; [exact Hwidth|].
    clear -Hvalue. lia. }
  assert (Hparents_width : dom_lt_trie_all (fun value => N.size_nat value <= width) parents).
  { now apply (dom_order_table_width bound width). }
  assert (Hsources : dom_order_sources_range bound sources).
  { exact (dom_order_source_maps_range bound numeric (lt_semis semi) (lt_minimizer semi)
      (lt_relative bucket) parents Horder Hparents). }
  set (removed := dom_order_removal (lt_numeric_limit numeric) parents order sources).
  assert (Hrecords : Forall (fun entry => let '(vertex, anchor, witness) := entry in
    (vertex <= bound /\ anchor <= bound /\ witness <= bound)%N) removed).
  { exact (dom_order_removal_records_range bound (lt_numeric_limit numeric) parents order
      sources Hparents Horder Hsources). }
  assert (Hremoved_unique : NoDup (map (fun entry => dom_lt_key (fst (fst entry))) removed)).
  { exact (dom_order_removal_keys_unique (lt_numeric_limit numeric) parents order sources). }
  assert (Hremoved_length : length removed <= count).
  { exact (dom_order_removal_length (lt_numeric_limit numeric) parents order sources). }
  assert (Hremoved_count : (N.of_nat (length removed) <= bound)%N).
  { apply time_of_nat_le. exact Hremoved_length. }
  set (positions := dom_anchor_order parents removed).
  pose proof (dom_order_anchor_endpoints bound parents removed Hparents Hrecords
    Hremoved_unique Hremoved_count) as Hendpoints. fold positions in Hendpoints.
  assert (Hpositions : dom_lt_trie_all (fun interval =>
    (fst interval <= 8 * (bound + 1) * (bound + 1) /\
      snd interval <= 8 * (bound + 1) * (bound + 1))%N) positions).
  { intros key [lower upper] Hget. exact (Hendpoints key (lower, upper) Hget). }
  assert (Hoperands : Forall (dom_order_merge_operand width positions) order).
  { apply Forall_forall. intros vertex Hin. split.
    - apply Hrank_width. exact (proj1 (Forall_forall _ _) Horder vertex Hin).
    - apply Hwidth. now apply dom_order_anchor_start_bound. }
  set (rows := dom_order_sorted_rows order parents positions).
  assert (Hrows_range : dom_lt_trie_all (Forall (fun value => (value <= bound)%N)) rows).
  { exact (dom_order_sorted_rows_forall (fun value => (value <= bound)%N)
      order parents positions Horder). }
  set (keys := dom_order_key_universe count).
  assert (Hkeys_unique : NoDup keys) by apply dom_order_key_universe_unique.
  assert (Hkeys_length : length keys = count + 2) by apply dom_order_key_universe_length.
  assert (Hroot : In (dom_lt_key 1%N) keys) by apply dom_order_key_universe_root.
  assert (Hrows_keys : dom_lt_trie_all (Forall (fun vertex => In (dom_lt_key vertex) keys)) rows).
  { exact (dom_order_key_universe_rows count rows Hrows_range). }
  assert (Hkeys_width : forall vertex, In (dom_lt_key vertex) keys -> N.size_nat vertex <= width).
  { intros vertex Hin. apply dom_order_key_universe_bound in Hin.
    eapply dom_order_linear_value_width; [exact Hwidth|].
    rewrite Nat2N.inj_add in Hin. change (N.of_nat 1) with 1%N in Hin.
    fold bound in Hin. clear -Hin. lia. }
  assert (Hlimit_width : N.size_nat (lt_numeric_limit numeric) <= width).
  { eapply dom_order_linear_value_width; [exact Hwidth|].
    rewrite Nat2N.inj_add in Hlimit. change (N.of_nat 1) with 1%N in Hlimit.
    fold bound in Hlimit. clear -Hlimit. lia. }
  assert (Hmass : dom_lt_row_mass keys rows <= count).
  { exact (dom_order_sorted_rows_mass keys order parents positions Hkeys_unique). }
  assert (Hremove_paid :
    (T_dom_order_removal (lt_numeric_limit numeric) parents order sources <=
      removal_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hremove_clock|]. apply N.mul_le_mono_l.
    unfold budget. apply time_of_nat_le. apply dom_order_body_budget_linear. }
  pose proof (dom_order_anchor_time bound width parents removed Hparents Hrecords
    Hremoved_unique Hremoved_count Hwidth) as Hanchor_clock.
  assert (Hanchor_paid : (T_dom_anchor_order parents removed <=
    dom_order_anchor_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hanchor_clock|]. apply N.mul_le_mono_l.
    unfold budget. apply time_of_nat_le.
    eapply Nat.le_trans with ((count + 1) * (width + 1)).
    - apply Nat.mul_le_mono_r. clear -Hremoved_length. lia.
    - apply dom_order_body_budget_linear. }
  pose proof (dom_order_sorted_rows_time width order parents positions
    Hoperands Hparents_width) as Hrows_clock.
  assert (Hrows_paid : (T_dom_order_sorted_rows order parents positions <=
    dom_order_sorted_rows_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hrows_clock|]. apply N.mul_le_mono_l.
    unfold budget. apply time_of_nat_le. apply dom_order_body_budget_rows. }
  pose proof (dom_order_emit_clock keys numeric rows width Hkeys_unique Hroot Hrows_keys
    Hkeys_width Hlimit_width) as Hemit_clock.
  rewrite Hkeys_length in Hemit_clock.
  assert (Hemit_paid : (T_dom_order_emit numeric rows <=
    3 * dom_order_emit_coefficient * budget)%N).
  { eapply N.le_trans; [exact Hemit_clock|].
    replace (3 * dom_order_emit_coefficient * budget)%N with
      (dom_order_emit_coefficient * (3 * budget))%N by ring.
    apply N.mul_le_mono_l. unfold budget.
    change (N.of_nat ((dom_lt_row_mass keys rows + (count + 2) + 1) * (width + 1)) <=
      N.of_nat 3 * N.of_nat (dom_order_body_budget count predecessors width))%N.
    rewrite <- Nat2N.inj_mul. apply time_of_nat_le.
    now apply dom_order_body_budget_emit. }
  pose proof (dom_order_result_phase_clocks result) as Htotal.
  cbn zeta in Htotal. fold numeric semi bucket parents order sources removed positions rows in Htotal.
  assert (Hpositive : (1 <= budget)%N).
  { unfold budget. pose proof (dom_order_body_budget_positive count predecessors width) as Hpositive.
    now apply time_of_nat_le in Hpositive. }
  eapply dom_order_phase_sum_budget;
    [exact Hpositive|exact Hsource_clock|exact Hremove_paid|exact Hanchor_paid|
     exact Hrows_paid|exact Hemit_paid|exact Htotal].
Qed.
(** * Closed coefficient for the complete raw ordering body *)

Definition dom_order_body_coefficient : N :=
  (dom_order_source_maps_coefficient + dom_order_removal_coefficient +
    dom_order_anchor_coefficient + dom_order_sorted_rows_coefficient +
    3 * dom_order_emit_coefficient + 64)%N.

(** The actual source and removal bounds discharge the two phase premises. *)
Lemma dom_order_of_result_time width result :
  let numeric := result_numeric result in
  let semi := result_semi result in
  let bucket := result_bucket result in
  let parents := result_parent result in
  let count := length (lt_numeric_order numeric) in
  let bound := N.of_nat count in
  NoDup (lt_numeric_order numeric) ->
  dom_lt_numeric_ranges bound numeric ->
  (lt_numeric_limit numeric <= N.of_nat (count + 1))%N ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_semis semi) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_minimizer semi) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) (lt_relative bucket) ->
  dom_lt_trie_all (fun value => (value <= bound)%N) parents ->
  (forall value, (value <= 8 * (bound + 1) * (bound + 1))%N -> N.size_nat value <= width) ->
  (T_dom_order_of_result result <= dom_order_body_coefficient *
    N.of_nat (dom_order_body_budget count
      (dom_lt_row_mass (map dom_lt_key (lt_numeric_order numeric)) (lt_numeric_pred numeric)) width))%N.
Proof.
  intros numeric semi bucket parents count bound Hunique Hranges Hlimit
    Hsemis Hminimizer Hrelative Hparents Hwidth.
  pose proof (dom_order_source_maps_time width numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents Hunique Hranges Hlimit Hsemis Hminimizer Hrelative
    Hparents Hwidth) as Hsource.
  pose proof (dom_lt_numeric_order_range bound numeric Hranges) as Horder.
  pose proof (dom_order_source_maps_range bound numeric (lt_semis semi) (lt_minimizer semi)
    (lt_relative bucket) parents Horder Hparents) as Hsources.
  pose proof (dom_order_removal_time count width (lt_numeric_limit numeric) parents
    (lt_numeric_order numeric)
    (dom_order_source_maps numeric (lt_semis semi) (lt_minimizer semi) (lt_relative bucket) parents)
    (Nat.le_refl count) Horder Hparents Hsources Hlimit Hwidth) as Hremove.
  unfold dom_order_body_coefficient.
  exact (dom_order_of_result_composition dom_order_source_maps_coefficient
    dom_order_removal_coefficient width result Hunique Hranges Hlimit Hsemis Hminimizer
    Hrelative Hparents Hwidth Hsource Hremove).
Qed.
(** * The ordering body on an actual prepared graph *)

(** All numeric inventories and quadratic anchor ranks fit the graph's ordering budget. *)
Lemma dom_order_graph_body_time g r : prepared_ok g ->
  (T_dom_order_of_result (dom_lt_pipeline g r) <= 5 * dom_order_body_coefficient *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
Proof.
  intro Hprepared.
  set (numeric := dom_lt_numeric_of g r).
  set (semi := dom_lt_semidominators numeric).
  set (bucket := dom_lt_buckets numeric (lt_semis semi)).
  set (parents := dom_lt_correct numeric (lt_semis semi) (lt_relative bucket)).
  set (count := length (lt_numeric_order numeric)).
  set (bound := N.of_nat count).
  set (predecessors := dom_lt_row_mass (map dom_lt_key (lt_numeric_order numeric))
    (lt_numeric_pred numeric)).
  assert (Hcount : count = length (dom_lt_dfs g r)) by apply dom_lt_numeric_order_length.
  assert (Hnumeric : dom_lt_numeric_ranges bound numeric).
  { unfold bound. rewrite Hcount. apply dom_lt_numeric_of_ranges. }
  assert (Hunique : NoDup (lt_numeric_order numeric)) by apply dom_lt_numeric_order_unique.
  assert (Hlimit : (lt_numeric_limit numeric <= N.of_nat (count + 1))%N).
  { unfold numeric. rewrite dom_lt_numeric_limit_count, Hcount. apply N.le_refl. }
  pose proof (dom_lt_semidominators_range bound numeric Hnumeric) as Hsemi.
  fold semi in Hsemi.
  pose proof (dom_lt_pipeline_buckets_range bound numeric (lt_semis semi) Hnumeric) as Hbucket.
  fold bucket in Hbucket.
  pose proof (dom_lt_pipeline_correct_range bound numeric (lt_semis semi)
    (lt_relative bucket) (proj2 Hbucket)) as Hparents.
  fold parents in Hparents.
  destruct (dom_lt_dfs_inventory g r) as [Hdiscover_unique [Hlisted [Hvertices Hedges]]].
  assert (Hwidth : forall value, (value <= 8 * (bound + 1) * (bound + 1))%N ->
    N.size_nat value <= 2 * graph_width (base g) + 4).
  { intros value Hvalue.
    apply (dom_distinct_quadratic_width (dom_lt_dfs g r) (graph_width (base g)) value
      Hdiscover_unique).
    - intros key Hin. apply dom_listed_key_width. now apply Hlisted.
    - unfold bound in Hvalue. now rewrite Hcount in Hvalue. }
  assert (Hraw : (T_dom_order_of_result (dom_lt_pipeline g r) <=
    dom_order_body_coefficient * N.of_nat (dom_order_body_budget count predecessors
      (2 * graph_width (base g) + 4)))%N).
  { apply (dom_order_of_result_time (2 * graph_width (base g) + 4)).
    - exact Hunique.
    - exact Hnumeric.
    - exact Hlimit.
    - exact (proj1 Hsemi).
    - exact (proj1 (proj2 Hsemi)).
    - exact (proj2 Hbucket).
    - exact Hparents.
    - exact Hwidth. }
  assert (Hpredecessors : predecessors <= graph_e (base g)).
  { unfold predecessors, dom_lt_row_mass. rewrite dom_lt_sum_map.
    exact (dom_lt_numeric_pred_total g r Hprepared). }
  assert (Hbudget : dom_order_body_budget count predecessors (2 * graph_width (base g) + 4) <=
    5 * ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1))).
  { unfold dom_order_body_budget. apply dom_order_graph_product; [now rewrite Hcount|exact Hpredecessors]. }
  eapply N.le_trans; [exact Hraw|].
  replace (5 * dom_order_body_coefficient *
    N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N with
    (dom_order_body_coefficient * N.of_nat (5 *
      ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1))))%N by
    (rewrite !Nat2N.inj_mul; change (N.of_nat 5) with 5%N; ring).
  apply N.mul_le_mono_l. now apply time_of_nat_le.
Qed.

Local Transparent dom_lt_numeric_of dom_lt_semidominators dom_lt_buckets dom_lt_correct.
Local Transparent dom_order_source_maps T_dom_order_source_maps
  dom_order_removal T_dom_order_removal dom_anchor_order T_dom_anchor_order
  dom_order_sorted_rows T_dom_order_sorted_rows dom_order_emit T_dom_order_emit.

(** A size observation traverses at most one key and adds its default-value branch. *)
Local Lemma dom_time_size_get sizes v :
  (T_dom_size_get sizes v <= 1 + 2 * N.of_nat (Pos.size_nat v))%N.
Proof.
  unfold T_dom_size_get. PTrieT.trie_get_le. lia.
Qed.

(** A size transfer charges two bounded keys and the bits of two bounded values. *)
Local Lemma dom_time_add_size m sizes v width :
  Pos.size_nat v <= width ->
  (forall p, trie_get v m = Some p -> Pos.size_nat p <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  (T_dom_add_size m sizes v <=
    (4 * PTrieT.c_trie + 64) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hparents Hvalues.
  pose proof (PTrieT.T_set_le N v (dom_size_get sizes v) sizes) as Hset.
  change (PTrieCode.T_set v (dom_size_get sizes v) sizes <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
  unfold T_dom_add_size. time_simpl.
  pose proof (dom_time_size_get sizes v) as Hsize_own.
  pose proof (PTrieT.T_trie_get_le _ v m) as Hparent_get.
  destruct (trie_get v m) as [p|] eqn:Hparent.
  - specialize (Hparents p eq_refl).
    pose proof (dom_time_size_get (PTrieCode.set v (dom_size_get sizes v) sizes) p)
      as Hsize_parent.
    rewrite dom_size_set_own.
    pose proof (PTrieT.T_set_le N p
      (dom_size_get sizes p + dom_size_get sizes v)%N
      (PTrieCode.set v (dom_size_get sizes v) sizes)) as Hsetp.
    change (PTrieCode.T_set p (dom_size_get sizes p + dom_size_get sizes v)%N
      (PTrieCode.set v (dom_size_get sizes v) sizes) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat p + 1))%N in Hsetp.
    pose proof (N.T_add_le (dom_size_get sizes p) (dom_size_get sizes v)) as Hadd.
    pose proof (Hvalues p) as Hp. pose proof (Hvalues v) as Hown.
    assert (Hv_trie : (PTrieT.c_trie * N.of_nat (Pos.size_nat v) <=
      PTrieT.c_trie * N.of_nat width)%N) by (apply N.mul_le_mono_l; lia).
    assert (Hp_trie : (PTrieT.c_trie * N.of_nat (Pos.size_nat p) <=
      PTrieT.c_trie * N.of_nat width)%N) by (apply N.mul_le_mono_l; lia).
    rewrite !Nat2N.inj_add in *.
    clear -Hv Hparents Hp Hown Hset Hsetp Hadd Hsize_own Hsize_parent Hparent_get
      Hv_trie Hp_trie.
    lia.
  - rewrite !Nat2N.inj_add in *. clear -Hv Hset Hsize_own Hparent_get. nia.
Qed.

(** Distinct reverse processing keeps intermediate values within the original size budget. *)
Local Lemma dom_time_size_fold m whole width :
  NoDup whole ->
  (forall v, In v whole -> Pos.size_nat v <= width) ->
  (forall v p, In v whole -> trie_get v m = Some p -> In p whole) ->
  forall remaining sizes,
  NoDup remaining -> incl remaining whole ->
  dom_size_budget (N.of_nat (length whole)) remaining sizes ->
  (List.T_fold_left (dom_add_size m) (T_dom_add_size m) remaining sizes <=
    ((4 * PTrieT.c_trie + 64) * N.of_nat (width + 1) + 1) *
      N.of_nat (length remaining) + 1)%N.
Proof.
  intros Hwhole Hkeys Hparents remaining.
  induction remaining as [|v rest IH]; intros sizes Hunique Hincl Hbudget.
  - time_step.
  - inversion Hunique as [|head tail Hfresh Hrest]; subst head tail.
    assert (Hv : In v whole) by (apply Hincl; now left).
    assert (Hvalues : forall x, N.size_nat (dom_size_get sizes x) <= width + 1).
    { intro x. eapply dom_distinct_twice_width; [exact Hwhole|exact Hkeys|].
      now apply (dom_size_budget_value (N.of_nat (length whole)) (v :: rest)). }
    pose proof (dom_time_add_size m sizes v width (Hkeys v Hv)
      (fun p Hp => Hkeys p (Hparents v p Hv Hp)) Hvalues) as Hstep.
    specialize (IH (dom_add_size m sizes v) Hrest
      (fun x Hx => Hincl x (or_intror Hx))
      (dom_size_budget_step (N.of_nat (length whole)) rest m sizes v Hunique Hbudget)).
    time_unfold @List.T_fold_left. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** A structural equality check spends the expected trie's reconstruction credit. *)
Local Lemma dom_time_map_eq_ne expected candidate :
  (T_dom_map_eq_ne expected candidate <=
    4 * N.of_nat (dom_rebuilt_weight_ne expected))%N.
Proof.
  revert candidate.
  induction expected as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
    intro candidate;
    destruct candidate as [r'|v'|v' r'|l'|l' r'|l' v'|l' v' r'];
    time_unfold T_dom_map_eq_ne; time_simpl;
    cbn [dom_rebuilt_weight_ne].
  all: try specialize (IHl l'); try specialize (IHr r');
    try pose proof (Pos.T_eqb_le v v') as Hcompare.
  all: rewrite !Nat2N.inj_add; lia.
Qed.

(** Empty-tree comparisons add only their outer branch charge. *)
Local Lemma dom_time_map_eq expected candidate :
  (T_dom_map_eq expected candidate <=
    4 * N.of_nat (dom_rebuilt_weight expected) + 2)%N.
Proof.
  destruct expected as [|expected], candidate as [|candidate];
    unfold T_dom_map_eq; cbn [dom_rebuilt_weight]; time_simpl; try lia.
  pose proof (dom_time_map_eq_ne expected candidate). lia.
Qed.

(** Strict numeric comparison examines at most its first operand's bits. *)
Local Lemma dom_time_N_ltb a b :
  (N.T_ltb a b <= N.of_nat (N.size_nat a) + 3)%N.
Proof.
  pose proof (N.T_compare_le a b). time_unfold N.T_ltb. lia.
Qed.

(** Every reconstructed binding pays once for its key and checked parent value. *)
Local Lemma dom_rebuild_weight width r m pos before v after :
  Pos.size_nat v <= width ->
  dom_rebuild width r m pos (Some before) v = Some after ->
  dom_rebuilt_weight after <= dom_rebuilt_weight before + 2 * width.
Proof.
  intros Hwidth Hstep. unfold dom_rebuild in Hstep.
  destruct (Pos.eqb v r).
  - destruct (trie_get v m); [discriminate Hstep|]. injection Hstep as <-. lia.
  - destruct (trie_get v m) as [p|]; [|discriminate Hstep].
    destruct (dom_key_fits width p) eqn:Hfits; [|discriminate Hstep].
    destruct (trie_get p pos) as [pp|]; [|discriminate Hstep].
    destruct (trie_get v pos) as [pv|]; [|discriminate Hstep].
    destruct (N.ltb pp pv); [|discriminate Hstep]. injection Hstep as <-.
    pose proof (dom_key_fits_width width p Hfits).
    pose proof (dom_rebuilt_weight_set v p before). lia.
Qed.

(** Reconstruction accumulates credit only along the bounded accepted input list. *)
Local Lemma dom_rebuild_fold_weight width r m pos vs before after :
  (forall v, In v vs -> Pos.size_nat v <= width) ->
  fold_left (dom_rebuild width r m pos) vs (Some before) = Some after ->
  dom_rebuilt_weight after <= dom_rebuilt_weight before + length vs * (2 * width).
Proof.
  revert before after. induction vs as [|v vs IH]; intros before after Hwidth Hfold.
  - cbn [fold_left] in Hfold. injection Hfold as <-. cbn [length]. lia.
  - cbn [fold_left] in Hfold.
    destruct (dom_rebuild width r m pos (Some before) v) as [next|] eqn:Hstep.
    + pose proof (dom_rebuild_weight width r m pos before v next
        (Hwidth v (or_introl eq_refl)) Hstep) as Hnext.
      specialize (IH next after (fun x Hx => Hwidth x (or_intror Hx)) Hfold).
      cbn [length]. nia.
    + rewrite dom_rebuild_fold_none in Hfold. discriminate Hfold.
Qed.

(** Each reconstruction callback bounds foreign parent keys before traversing them. *)
Local Lemma dom_time_rebuild width r m pos acc v :
  Pos.size_nat v <= width ->
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  (T_dom_rebuild width r m pos acc v <=
    (PTrieT.c_trie + 64) * N.of_nat (width + 1))%N.
Proof.
  intros Hwidth Hvalues. destruct acc as [before|].
  2: { unfold T_dom_rebuild. time_simpl. rewrite Nat2N.inj_add. nia. }
  pose proof (Pos.T_eqb_le v r) as Hroot.
  unfold T_dom_rebuild. destruct (Pos.eqb v r) eqn:Eroot.
  - destruct (trie_get v m); PTrieT.trie_get_le;
      time_simpl; rewrite !Nat2N.inj_add; nia.
  - destruct (trie_get v m) as [p|] eqn:Hparent.
    2: { PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia. }
    pose proof (dom_time_key_fits width p) as Hfits_time.
    destruct (dom_key_fits width p) eqn:Hfits.
    2: { PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia. }
    pose proof (dom_key_fits_width width p Hfits) as Hparent_width.
    destruct (trie_get p pos) as [pp|] eqn:Hpp;
      destruct (trie_get v pos) as [pv|] eqn:Hpv.
    + pose proof (Hvalues p pp Hpp) as Hpp_width.
      pose proof (dom_time_N_ltb pp pv) as Hcompare.
      pose proof (PTrieT.T_set_le positive v p before) as Hset.
      change (PTrieCode.T_set v p before <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
      destruct (N.ltb pp pv); PTrieT.trie_get_le; time_simpl;
        rewrite !Nat2N.inj_add in *; nia.
    + PTrieT.trie_get_le. time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + PTrieT.trie_get_le. time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + PTrieT.trie_get_le. time_simpl. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Distinct accepted keys also bound every reconstructed numeric position. *)
Local Lemma dom_read_positions_width g r o pos :
  dom_read_known (dom_scan g) r o = Some pos ->
  forall v i, trie_get v pos = Some i -> N.size_nat i <= graph_width (base g).
Proof.
  intro Hread. pose proof (dom_read_known_positions (dom_scan g) r o pos Hread) as ->.
  destruct (dom_read_known_success g r o (dom_positions o) Hread)
    as [Hunique [_ [_ [Hlisted _]]]].
  intros v i Hget. apply (dom_distinct_value_width o (graph_width (base g)) i Hunique).
  - intros x Hx. apply dom_listed_key_width. now apply Hlisted.
  - apply N.lt_le_incl. exact (dom_positions_bound o v i Hunique Hget).
Qed.

(** Every interval comparison reads bounded keys and adds bounded position and size values. *)
Local Lemma dom_time_interval pos sizes u v width :
  Pos.size_nat u <= width -> Pos.size_nat v <= width ->
  (forall x n, trie_get x pos = Some n -> N.size_nat n <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  (T_dom_interval pos sizes u v <= 64 * N.of_nat (width + 1))%N.
Proof.
  intros Hu Hv Hpositions Hsizes. unfold T_dom_interval.
  destruct (trie_get u pos) as [pu|] eqn:Hpu;
    destruct (trie_get v pos) as [pv|] eqn:Hpv.
  - pose proof (Hpositions u pu Hpu) as Hpu_width.
    pose proof (Hpositions v pv Hpv) as Hpv_width.
    pose proof (Hsizes u) as Hsu_width. pose proof (Hsizes v) as Hsv_width.
    pose proof (N.T_leb_le pu pv) as Hstarts.
    pose proof (N.T_add_le pv (dom_size_get sizes v)) as Hendv.
    pose proof (N.T_add_le pu (dom_size_get sizes u)) as Hendu.
    pose proof (dom_add_width pv (dom_size_get sizes v)) as Hsum.
    pose proof (N.T_leb_le (N.add pv (dom_size_get sizes v))
      (N.add pu (dom_size_get sizes u))) as Hends.
    unfold T_dom_size_get. PTrieT.trie_get_le.
    time_simpl. rewrite !Nat2N.inj_add in *. nia.
  - PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
  - PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
  - PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
Qed.

(** Containment checks spend one bounded parent lookup and interval test per entry. *)
Local Lemma dom_time_sizes_ok m pos sizes o width :
  (forall v, In v o -> Pos.size_nat v <= width) ->
  (forall v p, In v o -> trie_get v m = Some p -> Pos.size_nat p <= width) ->
  (forall x n, trie_get x pos = Some n -> N.size_nat n <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  (T_dom_sizes_ok m pos sizes o <=
    96 * N.of_nat ((length o + 1) * (width + 1)))%N.
Proof.
  intros Hkeys Hparents Hpositions Hsizes.
  unfold T_dom_sizes_ok. time_simpl.
  lazymatch goal with
  | |- context [List.T_forallb ?f ?T_f o] =>
    assert (Hcallback : forall v, In v o ->
      (T_f v <= 80 * N.of_nat (width + 1))%N)
  end.
  { intros v Hv. cbn beta iota zeta.
    pose proof (Hkeys v Hv) as Hwidth.
    destruct (trie_get v m) as [p|] eqn:Hparent.
    - pose proof (dom_time_interval pos sizes p v width
        (Hparents v p Hv Hparent) Hwidth Hpositions Hsizes) as Hinterval.
      PTrieT.trie_get_le. rewrite Nat2N.inj_add in *. nia.
    - PTrieT.trie_get_le. rewrite Nat2N.inj_add. nia. }
  lazymatch goal with
  | |- context [List.T_forallb ?f ?T_f o] =>
    pose proof (@dom_time_forallb positive f T_f
      (80 * N.of_nat (width + 1))%N o Hcallback) as Hfold
  end.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

(** Trie shape and stored child occurrences jointly pay for reversing every row. *)
Fixpoint dom_child_weight_ne (t : trie_ne (list positive)) : nat :=
  match t with
  | N001 r => 1 + dom_child_weight_ne r
  | N010 vs => 1 + length vs
  | N011 vs r => 1 + length vs + dom_child_weight_ne r
  | N100 l => 1 + dom_child_weight_ne l
  | N101 l r => 1 + dom_child_weight_ne l + dom_child_weight_ne r
  | N110 l vs => 1 + dom_child_weight_ne l + length vs
  | N111 l vs r => 1 + dom_child_weight_ne l + length vs + dom_child_weight_ne r
  end.

Definition dom_child_weight (t : ptrie (list positive)) : nat :=
  match t with Empty => 0 | Nodes n => dom_child_weight_ne n end.

Local Lemma dom_child_weight_node l o r :
  dom_child_weight (PTrieCode.node l o r) <=
    1 + dom_child_weight l +
      (match o with None => 0 | Some vs => length vs end) + dom_child_weight r.
Proof.
  destruct l, o, r; cbn [PTrieCode.node dom_child_weight dom_child_weight_ne]; lia.
Qed.

Local Lemma dom_child_weight_parts t :
  dom_child_weight (trie_left t) +
    (match trie_value t with None => 0 | Some vs => length vs end) +
    dom_child_weight (trie_right t) <= dom_child_weight t.
Proof.
  destruct t as [|t]; [reflexivity|]. destruct t;
    cbn [trie_left trie_value trie_right dom_child_weight dom_child_weight_ne]; lia.
Qed.

(** Replacement refunds the old row rather than charging it again. *)
Local Lemma dom_child_weight_set p vs t :
  dom_child_weight (PTrieCode.set p vs t) +
    (match trie_get p t with None => 0 | Some old => length old end) <=
    dom_child_weight t + Pos.size_nat p + length vs.
Proof.
  revert t. induction p as [p IH|p IH|]; intro t;
    cbn [PTrieCode.set PTrieCode.replace Pos.size_nat];
    rewrite ?trie_get_xO, ?trie_get_xI, ?trie_get_xH.
  all: eapply Nat.le_trans;
    [apply Nat.add_le_mono_r; apply dom_child_weight_node|].
  all: pose proof (dom_child_weight_parts t) as Hparts.
  - specialize (IH (trie_right t)). unfold PTrieCode.set in IH.
    unfold PTrieCode.left, PTrieCode.value, PTrieCode.right in *. lia.
  - specialize (IH (trie_left t)). unfold PTrieCode.set in IH.
    unfold PTrieCode.left, PTrieCode.value, PTrieCode.right in *. lia.
  - unfold PTrieCode.left, PTrieCode.right in *. lia.
Qed.

(** One child insertion introduces one occurrence and at most one key path. *)
Local Lemma dom_child_weight_push m rows v width :
  (forall p, trie_get v m = Some p -> Pos.size_nat p <= width) ->
  dom_child_weight (dom_child_push m rows v) <= dom_child_weight rows + width + 1.
Proof.
  intro Hparents. unfold dom_child_push, dom_child_row.
  destruct (trie_get v m) as [p|] eqn:Hparent; [|lia].
  specialize (Hparents p eq_refl).
  pose proof (dom_child_weight_set p
    (v :: match trie_get p rows with None => [] | Some vs => vs end) rows) as Hset.
  destruct (trie_get p rows) as [old|]; cbn [length] in Hset; lia.
Qed.

(** Grouping charges each input occurrence once, even when parents have many children. *)
Local Lemma dom_child_weight_fold m xs rows width :
  (forall v p, In v xs -> trie_get v m = Some p -> Pos.size_nat p <= width) ->
  dom_child_weight (fold_left (dom_child_push m) xs rows) <=
    dom_child_weight rows + length xs * (width + 1).
Proof.
  revert rows. induction xs as [|v rest IH]; intros rows Hparents;
    cbn [fold_left length]; [lia|].
  pose proof (dom_child_weight_push m rows v width
    (fun p Hp => Hparents v p (or_introl eq_refl) Hp)) as Hstep.
  specialize (IH (dom_child_push m rows v)
    (fun x p Hx Hp => Hparents x p (or_intror Hx) Hp)). lia.
Qed.

(** The derived filter clock pays exactly once for each stored row's reversal. *)
Local Lemma dom_time_child_filter_ne n :
  (PTrieT.T_filter_ne
    (fun vs : list positive => Some (rev_append vs []))
    (fun vs : list positive => (1 + (1 + List.T_rev_append vs []))%N) n <=
    32 * N.of_nat (dom_child_weight_ne n))%N.
Proof.
  induction n as [r IHr|vs|vs r IHr|l IHl|l IHl r IHr|l IHl vs|l IHl vs r IHr];
    time_unfold @PTrieT.T_filter_ne; time_unfold @PTrieT.T_filter_value; time_simpl;
    cbn [dom_child_weight_ne].
  all: try pose proof (List.T_rev_append_le vs []) as Hreverse.
  all: rewrite !Nat2N.inj_add in *; nia.
Qed.

Local Lemma dom_time_child_map rows :
  (PTrieT.T_map (fun vs : list positive => rev_append vs [])
    (fun vs : list positive => (1 + List.T_rev_append vs [])%N) rows <=
    32 * N.of_nat (dom_child_weight rows + 1))%N.
Proof.
  destruct rows as [|n]; unfold PTrieT.T_map,
    PTrieT.T_filter_map; time_simpl; [cbn [dom_child_weight]; lia|].
  pose proof (dom_time_child_filter_ne n) as Hfilter.
  cbn [dom_child_weight]. rewrite Nat2N.inj_add. lia.
Qed.

(** The numbering callback shares the producer's amortized binary counter credit. *)
Local Definition dom_number_push (state : N * ptrie N) (v : positive) : N * ptrie N :=
  let '(next, positions) := state in
    (N.succ next, PTrieCode.set v next positions).
TimeFun dom_number_push.

Local Lemma dom_time_number_push state v width : Pos.size_nat v <= width ->
  (T_dom_number_push state v + dom_counter_credit (fst (dom_number_push state v)) <=
    (PTrieT.c_trie + 8) * N.of_nat (width + 1) +
      dom_counter_credit (fst state))%N.
Proof.
  destruct state as [next positions]. intro Hwidth.
  pose proof (PTrieT.T_set_le N v next positions) as Hset.
  change (PTrieCode.T_set v next positions <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
  pose proof (dom_time_counter_succ next) as Hcounter.
  unfold T_dom_number_push, dom_number_push. time_simpl. cbn [fst].
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Local Lemma dom_time_number_fold xs next positions width :
  (forall v, In v xs -> Pos.size_nat v <= width) ->
  (List.T_fold_left dom_number_push T_dom_number_push xs (next, positions) <=
    ((PTrieT.c_trie + 8) * N.of_nat (width + 1) + 1) * N.of_nat (length xs) +
      dom_counter_credit next + 1)%N.
Proof.
  revert next positions. induction xs as [|v rest IH]; intros next positions Hkeys.
  - time_step.
  - pose proof (dom_time_number_push (next, positions) v width
      (Hkeys v (or_introl eq_refl))) as Hstep.
    specialize (IH (N.succ next) (PTrieCode.set v next positions)
      (fun x Hx => Hkeys x (or_intror Hx))).
    time_unfold @List.T_fold_left. cbn [dom_number_push fst length] in *.
    rewrite Nat2N.inj_succ, N.mul_succ_r.
    set (charge := ((PTrieT.c_trie + 8) * N.of_nat (width + 1))%N) in *.
    set (running := List.T_fold_left dom_number_push T_dom_number_push rest
      (N.succ next, PTrieCode.set v next positions)) in *.
    set (step_cost := T_dom_number_push (next, positions) v) in *.
    set (before_credit := dom_counter_credit next) in *.
    set (after_credit := dom_counter_credit (N.succ next)) in *.
    change (running <= (charge + 1) * N.of_nat (length rest) + after_credit + 1)%N in IH.
    clearbody charge running step_cost before_credit after_credit.
    clear -IH Hstep. lia.
Qed.

Local Lemma dom_time_positions o width :
  (forall v, In v o -> Pos.size_nat v <= width) ->
  (T_dom_positions o <=
    (4 * PTrieT.c_trie + 64) * N.of_nat ((length o + 1) * (width + 1)))%N.
Proof.
  intro Hkeys. pose proof (dom_time_number_fold o 0%N Empty width Hkeys) as Hfold.
  unfold T_dom_positions. time_simpl.
  change (1 + (List.T_fold_left dom_number_push T_dom_number_push o (0%N, Empty) + 1) <=
    (4 * PTrieT.c_trie + 64) * N.of_nat ((length o + 1) * (width + 1)))%N.
  cbn [dom_counter_credit] in Hfold.
  rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

Local Lemma dom_time_child_push m rows v width :
  Pos.size_nat v <= width ->
  (forall p, trie_get v m = Some p -> Pos.size_nat p <= width) ->
  (T_dom_child_push m rows v <= (PTrieT.c_trie + 8) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hparents. unfold T_dom_child_push. time_simpl.
  destruct (trie_get v m) as [p|] eqn:Hparent.
  - specialize (Hparents p eq_refl).
    pose proof (PTrieT.T_set_le (list positive) p
      (v :: match trie_get p rows with None => [] | Some vs => vs end) rows) as Hset.
    change (PTrieCode.T_set p
      (v :: match trie_get p rows with None => [] | Some vs => vs end) rows <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat p + 1))%N in Hset.
    PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
  - PTrieT.trie_get_le. rewrite Nat2N.inj_add. nia.
Qed.

Local Lemma dom_time_end_push pos sizes ends v width :
  Pos.size_nat v <= width ->
  (forall n, trie_get v pos = Some n -> N.size_nat n <= width) ->
  N.size_nat (dom_size_get sizes v) <= width + 1 ->
  (T_dom_end_push pos sizes ends v <=
    (PTrieT.c_trie + 32) * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hpositions Hsizes. unfold T_dom_end_push. time_simpl.
  destruct (trie_get v pos) as [pv|] eqn:Hposition.
  - specialize (Hpositions pv eq_refl).
    pose proof (N.T_add_le pv (dom_size_get sizes v)) as Hadd.
    pose proof (dom_add_width pv (dom_size_get sizes v)) as Hsum.
    pose proof (N.T_pred_le (pv + dom_size_get sizes v)%N) as Hpred.
    pose proof (PTrieT.T_set_le N v (N.pred (pv + dom_size_get sizes v)) ends) as Hset.
    change (PTrieCode.T_set v (N.pred (pv + dom_size_get sizes v)) ends <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
    pose proof (dom_time_size_get sizes v) as Hsize_get. PTrieT.trie_get_le.
    rewrite !Nat2N.inj_add in *. nia.
  - PTrieT.trie_get_le. rewrite Nat2N.inj_add. nia.
Qed.

(** Minima retain the width bound of their two possible results. *)
Local Lemma dom_min_width width a b :
  N.size_nat a <= width -> N.size_nat b <= width ->
  N.size_nat (N.min a b) <= width.
Proof.
  intros Ha Hb. destruct (N.le_ge_cases a b) as [Hab|Hba].
  - now rewrite N.min_l.
  - now rewrite N.min_r.
Qed.

(** Maxima also retain the common width bound of their operands. *)
Local Lemma dom_max_width width a b :
  N.size_nat a <= width -> N.size_nat b <= width ->
  N.size_nat (N.max a b) <= width.
Proof.
  intros Ha Hb. destruct (N.le_ge_cases a b) as [Hab|Hba].
  - now rewrite N.max_r.
  - now rewrite N.max_l.
Qed.

(** Each accumulated low-high extremum is a position from the accepted order. *)
Local Definition dom_flags_width width (acc : option (ptrie (bool * N * N))) : Prop :=
  match acc with
  | None => True
  | Some flags => forall v direct lo hi, trie_get v flags = Some (direct, lo, hi) ->
      N.size_nat lo <= width /\ N.size_nat hi <= width
  end.

(** A fresh flag table contains no extrema to bound. *)
Local Lemma dom_flags_width_empty width : dom_flags_width width (Some Empty).
Proof.
  intros v direct lo hi Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
Qed.

(** Updating one flag record preserves every other bounded record. *)
Local Lemma dom_flags_width_set width flags v direct lo hi :
  dom_flags_width width (Some flags) -> N.size_nat lo <= width -> N.size_nat hi <= width ->
  dom_flags_width width (Some (PTrieCode.set v (direct, lo, hi) flags)).
Proof.
  intros Hflags Hlo Hhi x direct1 lo1 hi1 Hget.
  destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite PTrie.get_set_same in Hget. injection Hget as <- <- <-. auto.
  - rewrite PTrie.get_set_other in Hget by exact Hne. now apply (Hflags x direct1).
Qed.

(** An edge update stores only minima and maxima of previously bounded positions. *)
Local Lemma dom_edge_update_width width r m pos sizes u acc v :
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  dom_flags_width width acc ->
  dom_flags_width width (dom_edge_update r m pos sizes u acc v).
Proof.
  intros Hpositions Hflags. unfold dom_edge_update.
  destruct acc as [flags|]; [|exact I].
  destruct (trie_get u pos) as [pu|] eqn:Hpu; [|exact I].
  destruct (trie_get v pos) as [pv|] eqn:Hpv; [|exact I].
  destruct (Pos.eqb v r); [exact Hflags|].
  destruct (trie_get v m) as [p|]; [|exact I].
  destruct (dom_interval pos sizes p u); [|exact I].
  pose proof (Hpositions u pu Hpu) as Hwidth.
  destruct (trie_get v flags) as [[[direct lo] hi]|] eqn:Hold.
  - destruct (Hflags v direct lo hi Hold) as [Hlo Hhi].
    apply dom_flags_width_set; [exact Hflags|apply dom_min_width|apply dom_max_width]; assumption.
  - apply dom_flags_width_set; [exact Hflags|apply dom_min_width|apply dom_max_width]; assumption.
Qed.

(** Minimum and maximum comparisons have the first operand's linear bit cost. *)
Local Lemma dom_time_min a b : (N.T_min a b <= N.of_nat (N.size_nat a) + 3)%N.
Proof.
  pose proof (N.T_compare_le a b). unfold N.T_min.
  destruct (N.compare a b); time_simpl; lia.
Qed.

Local Lemma dom_time_max a b : (N.T_max a b <= N.of_nat (N.size_nat a) + 3)%N.
Proof.
  pose proof (N.T_compare_le a b). unfold N.T_max.
  destruct (N.compare a b); time_simpl; lia.
Qed.

(** Edge checking traverses bounded keys and stores only bounded position extrema. *)
Local Lemma dom_time_edge_update width r m pos sizes u acc v :
  Pos.size_nat u <= width -> Pos.size_nat v <= width ->
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  (forall x p i, trie_get x pos = Some i -> trie_get x m = Some p ->
    Pos.size_nat p <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  dom_flags_width width acc ->
  (T_dom_edge_update r m pos sizes u acc v <=
    (PTrieT.c_trie + 128) * N.of_nat (width + 1))%N.
Proof.
  intros Hu Hv Hpositions Hparents Hsizes Hflags.
  unfold T_dom_edge_update. destruct acc as [flags|].
  2: { time_simpl. rewrite Nat2N.inj_add. nia. }
  destruct (trie_get u pos) as [pu|] eqn:Hpu.
  2: { destruct (trie_get v pos); PTrieT.trie_get_le;
      time_simpl; rewrite Nat2N.inj_add; nia. }
  destruct (trie_get v pos) as [pv|] eqn:Hpv.
  2: { PTrieT.trie_get_le; time_simpl; rewrite Nat2N.inj_add; nia. }
  pose proof (Pos.T_eqb_le v r) as Hroot.
  destruct (Pos.eqb v r).
  - PTrieT.trie_get_le; time_simpl; rewrite Nat2N.inj_add; nia.
  - destruct (trie_get v m) as [p|] eqn:Hparent.
    2: { PTrieT.trie_get_le; time_simpl; rewrite Nat2N.inj_add; nia. }
    pose proof (Hparents v p pv Hpv Hparent) as Hp.
    pose proof (dom_time_interval pos sizes p u width Hp Hu Hpositions Hsizes) as Hinterval.
    destruct (dom_interval pos sizes p u).
    2: { PTrieT.trie_get_le; time_simpl; rewrite Nat2N.inj_add in *; nia. }
    pose proof (Pos.T_eqb_le u p) as Hdirect.
    pose proof (Hpositions u pu Hpu) as Hpu_width.
    assert (Hset_width : (PTrieT.c_trie * N.of_nat (Pos.size_nat v) <=
      PTrieT.c_trie * N.of_nat width)%N) by (apply N.mul_le_mono_l; lia).
    destruct (trie_get v flags) as [[[direct lo] hi]|] eqn:Hrecord.
    + destruct (Hflags v direct lo hi Hrecord) as [Hlo Hhi].
      pose proof (dom_time_min lo pu) as Hmin.
      pose proof (dom_time_max hi pu) as Hmax.
      pose proof (PTrieT.T_set_le (bool * N * N) v
        (direct || Pos.eqb u p, N.min lo pu, N.max hi pu) flags) as Hset.
      change (PTrieCode.T_set v
        (direct || Pos.eqb u p, N.min lo pu, N.max hi pu) flags <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
      PTrieT.trie_get_le. time_simpl. rewrite !Nat2N.inj_add in *. lia.
    + pose proof (dom_time_min pu pu) as Hmin.
      pose proof (dom_time_max pu pu) as Hmax.
      pose proof (PTrieT.T_set_le (bool * N * N) v
        (false || Pos.eqb u p, N.min pu pu, N.max pu pu) flags) as Hset.
      change (PTrieCode.T_set v
        (false || Pos.eqb u p, N.min pu pu, N.max pu pu) flags <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat v + 1))%N in Hset.
      PTrieT.trie_get_le. time_simpl. rewrite !Nat2N.inj_add in *. lia.
Qed.

(** Low-high final checks compare only stored extrema and bounded interval endpoints. *)
Local Lemma dom_time_low_high width r pos sizes flags v :
  Pos.size_nat v <= width ->
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  dom_flags_width width (Some flags) ->
  (T_dom_low_high r pos sizes flags v <= 64 * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hpositions Hsizes Hflags.
  pose proof (Pos.T_eqb_le v r) as Hroot.
  unfold T_dom_low_high. destruct (Pos.eqb v r).
  - time_simpl. rewrite Nat2N.inj_add. nia.
  - destruct (trie_get v pos) as [pv|] eqn:Hpv;
      destruct (trie_get v flags) as [[[direct lo] hi]|] eqn:Hflag.
    + pose proof (Hpositions v pv Hpv) as Hpv_width.
      destruct (Hflags v direct lo hi Hflag) as [Hlo Hhi].
      pose proof (Hsizes v) as Hsize_width.
      pose proof (dom_time_N_ltb lo pv) as Hlow.
      pose proof (N.T_add_le pv (dom_size_get sizes v)) as Hadd.
      pose proof (dom_add_width pv (dom_size_get sizes v)) as Hsum_width.
      pose proof (N.T_leb_le (N.add pv (dom_size_get sizes v)) hi) as Hhigh.
      unfold T_dom_size_get. PTrieT.trie_get_le.
      time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
    + PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
    + PTrieT.trie_get_le. time_simpl. rewrite Nat2N.inj_add. nia.
Qed.

(** A successor row preserves bounded flags and charges its length and source lookup. *)
Local Lemma dom_time_edges_from width g r m pos sizes acc u :
  Pos.size_nat u <= width ->
  (forall v, In v (succs (base g) u) -> Pos.size_nat v <= width) ->
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  (forall x p i, trie_get x pos = Some i -> trie_get x m = Some p ->
    Pos.size_nat p <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  dom_flags_width width acc ->
  dom_flags_width width (dom_edges_from g r m pos sizes acc u) /\
  (T_dom_edges_from g r m pos sizes acc u <=
    (PTrieT.c_trie + 256) * N.of_nat (width + 1) *
      N.of_nat (length (succs (base g) u) + 1))%N.
Proof.
  intros Hu Hrow Hpositions Hparents Hsizes Hflags.
  pose proof (@dom_time_fold_left_state (option (ptrie (bool * N * N))) positive
    (dom_edge_update r m pos sizes u) (T_dom_edge_update r m pos sizes u)
    (dom_flags_width width) (fun _ => 0%nat)
    ((PTrieT.c_trie + 128) * N.of_nat (width + 1))%N
    (succs (base g) u) acc Hflags
    ltac:(intros v Hv flags Hbounded; split;
      [now apply dom_edge_update_width|
       rewrite N.mul_1_r; apply dom_time_edge_update; try assumption; now apply Hrow]))
    as [Hfinal Hfold_time].
  assert (Hzero : fold_right (fun (_ : positive) total => (0 + total)%nat)
    0 (succs (base g) u) = 0).
  { generalize (succs (base g) u). intro row.
    induction row as [|x xs IH]; cbn [fold_right]; [reflexivity|now rewrite IH]. }
  rewrite Hzero, Nat.add_0_l in Hfold_time.
  split; [exact Hfinal|].
  pose proof (dom_time_succs (base g) u) as Hlookup.
  unfold T_dom_edges_from. time_simpl.
  change (fun (H : option (ptrie (bool * N * N))) (H0 : positive) =>
    T_dom_edge_update r m pos sizes u H H0) with (T_dom_edge_update r m pos sizes u).
  set (running := List.T_fold_left (dom_edge_update r m pos sizes u)
    (T_dom_edge_update r m pos sizes u) (succs (base g) u) acc) in *; clearbody running.
  clear -Hu Hfold_time Hlookup. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** The edge phase visits each selected row once and checks its bounded flag summary. *)
Local Lemma dom_time_edges width g r m o pos sizes :
  (forall u, In u o -> Pos.size_nat u <= width) ->
  (forall u v, In u o -> In v (succs (base g) u) -> Pos.size_nat v <= width) ->
  (forall x i, trie_get x pos = Some i -> N.size_nat i <= width) ->
  (forall x p i, trie_get x pos = Some i -> trie_get x m = Some p ->
    Pos.size_nat p <= width) ->
  (forall x, N.size_nat (dom_size_get sizes x) <= width + 1) ->
  (T_dom_edges g r m o pos sizes <=
    (PTrieT.c_trie + 512) * N.of_nat
      ((length o + fold_right (fun u total => (length (succs (base g) u) + total)%nat)
        0%nat o + 1) * (width + 1)))%N.
Proof.
  intros Hkeys Hrows Hpositions Hparents Hsizes.
  pose proof (@dom_time_fold_left_state (option (ptrie (bool * N * N))) positive
    (dom_edges_from g r m pos sizes) (T_dom_edges_from g r m pos sizes)
    (dom_flags_width width) (fun u => length (succs (base g) u))
    ((PTrieT.c_trie + 256) * N.of_nat (width + 1))%N o (Some Empty)
    (dom_flags_width_empty width)
    ltac:(intros u Hu acc Hflags; apply dom_time_edges_from;
      [now apply Hkeys|intros v Hv; now apply (Hrows u)|exact Hpositions|
       exact Hparents|exact Hsizes|exact Hflags])) as [Hfinal Hfold_time].
  unfold T_dom_edges.
  destruct (fold_left (dom_edges_from g r m pos sizes) o (Some Empty))
    as [flags|] eqn:Hresult; cbn [dom_flags_width] in Hfinal.
  - pose proof (@dom_time_forallb positive (dom_low_high r pos sizes flags)
      (T_dom_low_high r pos sizes flags) (64 * N.of_nat (width + 1))%N o
      ltac:(intros v Hv; apply dom_time_low_high;
        [now apply Hkeys|exact Hpositions|exact Hsizes|exact Hfinal])) as Hchecks.
    time_simpl.
    change (fun (H : option (ptrie (bool * N * N))) (H0 : positive) =>
      T_dom_edges_from g r m pos sizes H H0) with (T_dom_edges_from g r m pos sizes).
    change (fun H : positive => T_dom_low_high r pos sizes flags H)
      with (T_dom_low_high r pos sizes flags).
    set (running := List.T_fold_left (dom_edges_from g r m pos sizes)
      (T_dom_edges_from g r m pos sizes) o (Some Empty)) in *; clearbody running.
    set (checking := List.T_forallb (dom_low_high r pos sizes flags)
      (T_dom_low_high r pos sizes flags) o) in *; clearbody checking.
    clear -Hfold_time Hchecks. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  - time_simpl.
    change (fun (H : option (ptrie (bool * N * N))) (H0 : positive) =>
      T_dom_edges_from g r m pos sizes H H0) with (T_dom_edges_from g r m pos sizes).
    set (running := List.T_fold_left (dom_edges_from g r m pos sizes)
      (T_dom_edges_from g r m pos sizes) o (Some Empty)) in *; clearbody running.
    clear -Hfold_time. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
Qed.

Module DomT <: DOM_ALL.
  Include Dom.
  TimeFun build.
  TimeFun check.
  TimeFun tree.
  TimeFun dominates_b.
  Definition scan := dom_scan.
  TimeFun scan.
  Definition read := dom_read_known.
  TimeFun read.
  Definition map_check := dom_map_check_known.
  TimeFun map_check.
  Definition sizes := dom_sizes.
  TimeFun sizes.
  Definition sizes_ok := dom_sizes_ok.
  TimeFun sizes_ok.
  Definition edges g m o :=
    match dom_read g (match o with [] => 1%positive | h :: _ => h end) o with
    | None => false
    | Some pos =>
      dom_edges g (match o with [] => 1%positive | h :: _ => h end) m o pos (dom_sizes m o)
    end.
  TimeFun edges.
  Definition pos_of (o : list positive) (v : positive) : N :=
    fst (fold_left (fun acc u =>
      let '(found, next) := acc in
      (if Pos.eqb u v then next else found, N.succ next)) o (0%N, 0%N)).
  TimeFun pos_of.
  Definition size_of m o v := dom_size_get (dom_sizes m o) v.
  TimeFun size_of.
  Definition lt_dfs := dom_lt_dfs.
  TimeFun lt_dfs.
  Definition lt_semi := dom_lt_parents.
  TimeFun lt_semi.
  Definition lt_order := dom_build_order.
  TimeFun lt_order.
  Definition lt_ops := dom_lt_ops.
  TimeFun lt_ops.
  Definition lt_forest := dom_lt_replay.
  Definition lt_init := dom_lt_replay_initial.
  TimeFun lt_init.
  Definition run_ops := dom_lt_run_ops.
  TimeFun run_ops.
  Definition k_scan : N := (8 * PTrieT.c_trie + 512)%N.
  Definition k_read : N :=
    (32 * (PTrieT.c_trie + c_loopN + 16) + 64 * c_loopN + 128)%N.
  Definition k_map : N := (2 * k_read + 16 * PTrieT.c_trie + 512)%N.
  Definition k_size : N := (16 * PTrieT.c_trie + 256)%N.
  Definition k_edge : N :=
    (4 * (k_scan + k_read + k_size + PTrieT.c_trie + 1024))%N.
  Definition k_tree : N := (2 * k_size + 16 * PTrieT.c_trie + 512)%N.
  Definition k_dfs : N := dom_lt_dfs_coefficient.
  Definition k_semi : N := dom_lt_semi_coefficient.
  Definition k_le : N := (32 * 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N.
  Definition k_order : N :=
    (5 * dom_order_body_coefficient + k_semi + 4 * k_le)%N.
  Definition k_build : N := 32%N.
  Definition k_check : N := 32%N.

  Definition c_dom : N :=
    (64 + k_tree + k_check * (k_scan + k_read + k_map + 2 * k_size + k_edge + 1) +
      k_dfs + k_semi + 4 * k_le + k_order + k_build)%N.

  Lemma F0_path_last : forall g a vs b, path g a vs b ->
  (vs = [b] /\ a = b) \/
  exists vs' c, path g a vs' c /\ edge g c b /\ vs = vs' ++ [b].
  Proof.
    intros g a vs b Hpath.
    induction Hpath as [v | u v vs w Huv Hpath IH].
    - left. split; reflexivity.
    - destruct IH as [[Hvs Hvw] | [prefix [c [Hprefix [Hcw Hvs]]]]].
      + subst vs w. right. exists [u], u.
        split; [constructor | split; [exact Huv | reflexivity]].
      + right. exists (u :: prefix), c. split.
        * eapply path_step; eassumption.
        * split; [exact Hcw | now rewrite Hvs].
  Qed.

  Lemma F1_dominates_trans : forall g r x y v,
  dominates g r x y -> dominates g r y v -> dominates g r x v.
  Proof.
    intros g r x y v Hxy Hyv vs Hpath.
    destruct (dom_path_prefix g r vs v Hpath y (Hyv vs Hpath)) as
      [prefix [Hprefix Hincl]].
    apply Hincl. exact (Hxy prefix Hprefix).
  Qed.

  Lemma F2_check_cert : forall g r m o, check g r m o = true -> dom_cert (base g) r m o.
  Proof.
    intros g r m o Hcheck. exact (dom_check_certificate g r m o Hcheck).
  Qed.

  (** An accepted order holds listed vertices only. *)
  Lemma F2b_check_listed : forall g r m o, check g r m o = true ->
    forall v, In v o -> In v (verts (base g)).
  Proof.
    intros g r m o Hcheck v Hin. unfold check in Hcheck.
    destruct (dom_read_known (dom_scan g) r o) as [pos |] eqn:Hread;
      [| discriminate Hcheck].
    destruct (dom_read_known_success g r o pos Hread) as [_ [_ [_ [Hlisted _]]]].
    rewrite <- (dom_nodes_verts g).
    exact (Hlisted v Hin).
  Qed.

  Lemma F3_anc_before : forall g r m o u v, dom_cert g r m o ->
  tree_anc m u v -> u <> v -> order_before o u v.
  Proof.
    intros g r m o u v Hcert Hanc Hneq.
    exact (dom_cert_anc_before g r m o u v Hcert Hanc Hneq).
  Qed.

  Lemma F4_root_anc : forall g r m o v, dom_cert g r m o -> In v o -> tree_anc m r v.
  Proof.
    intros g r m o v Hcert Hin. exact (dom_cert_root_anc g r m o v Hcert Hin).
  Qed.

  Lemma F5_reach_listed : forall g r m o v, dom_cert g r m o ->
  reach g [r] v -> In v o.
  Proof.
    intros g r m o v Hcert Hreach. exact (dom_cert_reach_listed g r m o v Hcert Hreach).
  Qed.

  Lemma F6_listed_reach : forall g r m o v, dom_cert g r m o ->
  In v o -> reach g [r] v.
  Proof.
    intros g r m o v Hcert Hin. exact (dom_cert_listed_reach g r m o v Hcert Hin).
  Qed.

  Lemma F7_anc_dominates : forall g r m o u v, dom_cert g r m o ->
  In v o -> tree_anc m u v -> dominates g r u v.
  Proof.
    intros g r m o u v Hcert Hin Hanc.
    exact (dom_cert_anc_dominates g r m o u v Hcert Hin Hanc).
  Qed.

  Lemma F8_anc_dec : forall g r m o u v, dom_cert g r m o -> In v o ->
  tree_anc m u v \/ ~ tree_anc m u v.
  Proof.
    intros g r m o u v Hcert _. exact (dom_cert_anc_dec g r m o u v Hcert).
  Qed.

  Lemma F9a_low_path : forall g r m o v, dom_cert g r m o -> In v o ->
  exists vs, path g r vs v /\ forall y, In y vs -> y = v \/ order_before o y v.
  Proof.
    intros g r m o v Hcert Hin. exact (dom_cert_low_path g r m o v Hcert Hin).
  Qed.

  Lemma F9b_high_path : forall g r m o v p, dom_cert g r m o -> trie_get v m = Some p ->
  exists vs, path g p vs v /\
    forall y, In y vs -> y = p \/ y = v \/ order_before o v y.
  Proof.
    intros g r m o v p Hcert Hget. exact (dom_cert_high_path g r m o v p Hcert Hget).
  Qed.

  Lemma F9c_avoid : forall g r m o x v, dom_cert g r m o -> In v o ->
  ~ tree_anc m x v -> exists vs, path g r vs v /\ ~ In x vs.
  Proof.
    intros g r m o x v Hcert Hin Hnot. exact (dom_cert_avoid g r m o x v Hcert Hin Hnot).
  Qed.

  Lemma F9_dominates_anc : forall g r m o x v, dom_cert g r m o ->
  In v o -> dominates g r x v -> tree_anc m x v.
  Proof.
    intros g r m o x v Hcert Hin Hdom.
    exact (dom_cert_dominates_anc g r m o x v Hcert Hin Hdom).
  Qed.

  Lemma F10_cert_exact : forall g r m o, dom_cert (base g) r m o -> dom_exact g r m.
  Proof.
    intros g r m o Hcert. exact (dom_cert_exact g r m o Hcert).
  Qed.

  Lemma F11_intervals : forall g r m o u v, dom_cert g r m o -> In u o -> In v o ->
  (tree_anc m u v <->
   (pos_of o u <= pos_of o v /\ pos_of o v + size_of m o v <= pos_of o u + size_of m o u)%N).
  Proof.
    intros g r m o u v Hcert Hu Hv.
    pose proof (proj1 (proj1 Hcert)) as Hunique.
    pose proof (dom_preorder_parent_before r m o (proj1 Hcert)) as Hordered.
    pose proof (dom_cert_sizes_ok g r m o Hcert) as Hsizes.
    pose proof (dom_sizes_interval_anc m o u v Hunique Hordered Hsizes Hu Hv) as Hinterval.
    unfold dom_interval in Hinterval.
    rewrite (dom_positions_rank o u Hunique Hu), (dom_positions_rank o v Hunique Hv)
      in Hinterval.
    rewrite andb_true_iff, !N.leb_le in Hinterval.
    unfold pos_of, size_of.
    rewrite (dom_position_fold_rank o u Hunique Hu), (dom_position_fold_rank o v Hunique Hv).
    symmetry. exact Hinterval.
  Qed.

  Lemma F12_tree_exact : forall g r m o, check g r m o = true ->
  domtree_exact g r (tree g r m o).
  Proof.
    intros g r m o Hcheck. exact (tree_exact g r m o Hcheck).
  Qed.

  (** A successful read lists distinct listed vertices within the budget, headed by the root. *)
  Lemma F2c_read : forall g r o pos, read (scan g) r o = Some pos ->
    NoDup o /\ length o <= graph_n (base g) /\ hd_error o = Some r /\
    (forall v, In v o -> In v (nodes g)) /\
    (forall v, In v o -> exists i, trie_get v pos = Some i).
  Proof.
    intros g r o pos Hread. exact (dom_read_known_success g r o pos Hread).
  Qed.

  (** A successful parent check keeps every parent of an ordered vertex in the order. *)
  Lemma F2d_map : forall g r m o, map_check (scan g) r m o = true ->
    forall v p, In v o -> trie_get v m = Some p -> In p o.
  Proof.
    intros g r m o Hcheck v p Hin Hget.
    destruct (dom_map_check_structure g r m o Hcheck) as
      [_ [_ [Hroot [Hparents _]]]].
    destruct (Pos.eq_dec v r) as [Heq | Hneq].
    - subst v. rewrite Hroot in Hget. discriminate Hget.
    - destruct (Hparents v Hin Hneq) as [parent [Hparent [ip [iv [Hp [Hv Hlt]]]]]].
      rewrite Hget in Hparent. injection Hparent as Heq. subst parent.
      eapply nth_error_In. exact Hp.
  Qed.

  Lemma T1_scan : forall g,
    (T_scan g <= k_scan * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intro g.
    pose proof (dom_time_graph_observations (base g)) as Hobservations.
    pose proof (dom_time_fold_left
      (fun acc v => PTrieCode.set v true acc)
      (fun acc v => 1 + PTrieT.T_set v true acc)%N
      ((PTrieT.c_trie + 2) * N.of_nat (graph_width (base g) + 1))%N
      (nodes g) Empty) as Hlisted.
    assert (Hnodes : nodes g = verts (base g)).
    { destruct g as [[vs adjacency] predecessors count_v count_e]. reflexivity. }
    specialize (Hlisted ltac:(intros v Hv acc;
      pose proof (PTrieT.T_set_le bool v true acc) as Hset;
      pose proof (proj1 (dom_time_graph_width (base g) v
        ltac:(now rewrite <- Hnodes))) as Hwidth;
      clear -Hset Hwidth; rewrite !Nat2N.inj_add in *; nia)).
    unfold T_scan, T_dom_scan, scan, k_scan. time_simpl.
    assert (Hlength : length (nodes g) = graph_n (base g)).
    { rewrite Hnodes. destruct (base g). reflexivity. }
    rewrite Hlength in Hlisted. rewrite Nat2N.inj_mul. nia.
  Qed.

  Lemma T2_read : forall g r o,
    (T_read (scan g) r o <= k_read * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g r o. unfold T_read, read, T_dom_read_known.
    destruct o as [|h rest].
    - time_simpl. unfold k_read. nia.
    - pose proof (dom_time_key_fits (graph_width (base g)) r) as Hfits_time.
      cbn [scan dom_scan dom_width dom_count dom_listed].
      destruct (dom_key_fits (graph_width (base g)) r) eqn:Hfits.
      + pose proof (dom_key_fits_width (graph_width (base g)) r Hfits) as Hwidth.
        pose proof (dom_time_pos_eqb_right h r) as Hcompare.
        destruct (Pos.eqb h r) eqn:Hroot.
        * pose proof (dom_time_read_order (graph_n (base g)) (graph_width (base g))
            (fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty)
            (h :: rest)) as Horder.
          time_simpl. unfold k_read. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
        * time_simpl. unfold k_read. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
      + time_simpl. unfold k_read. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  Lemma T3_map : forall g r m o,
    (T_map_check (scan g) r m o <= k_map * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g r m o. pose proof (T2_read g r o) as Hread_time.
    unfold T_read in Hread_time. cbn beta iota zeta in Hread_time.
    unfold T_map_check, T_dom_map_check_known. time_simpl.
    destruct (dom_read_known (scan g) r o) as [pos|] eqn:Hread.
    - change (dom_read_known (dom_scan g) r o = Some pos) in Hread.
      destruct (dom_read_known_success g r o pos Hread)
        as [Hunique [Hlength [_ [Hlisted _]]]].
      assert (Hkeys : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
      { intros v Hv. apply dom_listed_key_width. now apply Hlisted. }
      pose proof (dom_read_positions_width g r o pos Hread) as Hvalues.
      cbn [scan dom_scan dom_width].
      pose proof (@dom_time_fold_left (option (ptrie positive)) positive
        (dom_rebuild (graph_width (base g)) r m pos)
        (T_dom_rebuild (graph_width (base g)) r m pos)
        ((PTrieT.c_trie + 64) * N.of_nat (graph_width (base g) + 1))%N o (Some Empty)
        ltac:(intros v Hv acc; apply dom_time_rebuild; [now apply Hkeys|exact Hvalues]))
        as Hfold_time.
      destruct (fold_left (dom_rebuild (graph_width (base g)) r m pos) o (Some Empty))
        as [built|] eqn:Hfold.
      + pose proof (dom_rebuild_fold_weight (graph_width (base g)) r m pos o Empty built
          Hkeys Hfold) as Hweight.
        pose proof (dom_time_map_eq built m) as Hequal.
        cbn [dom_rebuilt_weight] in Hweight.
        time_simpl. unfold k_map.
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
        change (fun (H : option (ptrie positive)) (H0 : positive) =>
          T_dom_rebuild (graph_width (base g)) r m pos H H0)
          with (T_dom_rebuild (graph_width (base g)) r m pos).
        set (running := List.T_fold_left (dom_rebuild (graph_width (base g)) r m pos)
          (T_dom_rebuild (graph_width (base g)) r m pos) o (Some Empty)) in *;
          clearbody running.
        clear -Hlength Hread_time Hfold_time Hweight Hequal. nia.
      + time_simpl. unfold k_map.
        change (fun (H : option (ptrie positive)) (H0 : positive) =>
          T_dom_rebuild (graph_width (base g)) r m pos H H0)
          with (T_dom_rebuild (graph_width (base g)) r m pos).
        set (running := List.T_fold_left (dom_rebuild (graph_width (base g)) r m pos)
          (T_dom_rebuild (graph_width (base g)) r m pos) o (Some Empty)) in *;
          clearbody running.
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
        clear -Hlength Hread_time Hfold_time. nia.
    - time_simpl. unfold k_map. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  Lemma T4_sizes : forall g m o, NoDup o -> length o <= graph_n (base g) ->
    (forall v, In v o -> In v (nodes g)) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_sizes m o <= k_size * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g m o Hunique Hlength Hlisted Hparents.
    assert (Hkeys : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
    { intros v Hv. apply dom_listed_key_width. now apply Hlisted. }
    pose proof (dom_time_size_fold m o (graph_width (base g))
      Hunique Hkeys Hparents (rev o) Empty (@NoDup_rev positive o Hunique)
      (fun x Hx => proj2 (in_rev o x) Hx)
      ltac:(rewrite <- length_rev; apply dom_size_budget_empty)) as Hfold.
    pose proof (List.T_rev_append_le o []) as Hreverse.
    unfold T_sizes, T_dom_sizes. time_simpl.
    rewrite rev_append_rev, app_nil_r.
    change (fun (H : ptrie N) (H0 : positive) => T_dom_add_size m H H0)
      with (T_dom_add_size m).
    rewrite length_rev in Hfold. unfold k_size.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    set (running := List.T_fold_left (dom_add_size m) (T_dom_add_size m) (rev o) Empty) in *.
    clearbody running. clear -Hlength Hfold Hreverse. nia.
  Qed.

  Lemma T5_edges : forall g m o, length o <= graph_n (base g) ->
    (forall v, In v o -> In v (verts (base g))) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_edges g m o <= k_edge * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g m o Hlength Hlisted Hclosed.
    set (root := match o with [] => 1%positive | h :: _ => h end).
    set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))).
    pose proof (T1_scan g) as Hscan_time.
    pose proof (T2_read g root o) as Hread_time.
    unfold T_scan in Hscan_time. unfold T_read, scan in Hread_time.
    cbn beta iota zeta in Hscan_time, Hread_time.
    fold budget in Hscan_time.
    assert (Hsmall : (N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)) <= budget)%N).
    { assert (Hnatural : (graph_n (base g) + 1) * (graph_width (base g) + 1) <=
        (graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)).
      { apply Nat.mul_le_mono_r. lia. }
      unfold budget. lia. }
    assert (Hread_big : (1 + T_dom_read_known (dom_scan g) root o <= k_read * budget)%N).
    { eapply N.le_trans; [exact Hread_time|]. now apply N.mul_le_mono_l. }
    unfold T_edges. fold root. unfold T_dom_read, dom_read. time_simpl.
    destruct (dom_read_known (dom_scan g) root o) as [pos|] eqn:Hread.
    - destruct (dom_read_known_success g root o pos Hread)
        as [Hunique [_ [_ [Haccepted _]]]].
      pose proof (dom_read_known_positions (dom_scan g) root o pos Hread) as Hpositions.
      pose proof (dom_read_positions_width g root o pos Hread) as Hvalues.
      assert (Hkeys : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
      { intros v Hv. exact (proj1 (dom_time_graph_width (base g) v (Hlisted v Hv))). }
      assert (Hdomain : forall v i, trie_get v pos = Some i -> In v o).
      { intros v i Hget. rewrite Hpositions in Hget.
        apply (proj1 (dom_positions_domain o v)). now exists i. }
      assert (Hparents : forall v p i, trie_get v pos = Some i ->
        trie_get v m = Some p -> Pos.size_nat p <= graph_width (base g)).
      { intros v p i Hget Hparent. apply Hkeys. apply (Hclosed v p).
        - now apply (Hdomain v i).
        - exact Hparent. }
      assert (Hsizes : forall x,
        N.size_nat (dom_size_get (dom_sizes m o) x) <= graph_width (base g) + 1).
      { intro x. apply (dom_distinct_twice_width o (graph_width (base g))
          (dom_size_get (dom_sizes m o) x) Hunique Hkeys).
        now apply dom_sizes_value_bound. }
      assert (Hrows : forall u v, In u o -> In v (succs (base g) u) ->
        Pos.size_nat v <= graph_width (base g)).
      { intros u v Hu Hv. eapply Nat.le_trans.
        - exact (dom_time_width_member (succs (base g) u) v Hv).
        - exact (proj2 (dom_time_graph_width (base g) u (Hlisted u Hu))). }
      pose proof (dom_time_edges (graph_width (base g)) g root m o pos (dom_sizes m o)
        Hkeys Hrows Hvalues Hparents Hsizes) as Hedges_time.
      pose proof (T4_sizes g m o Hunique Hlength Haccepted Hclosed) as Hsizes_time.
      unfold T_sizes in Hsizes_time. cbn beta iota zeta in Hsizes_time.
      pose proof (@dom_nodup_sum_incl positive (fun u => length (succs (base g) u))
        o (verts (base g)) Hunique Hlisted) as Hrows_total.
      assert (Hrow_bound : fold_right (fun u total => length (succs (base g) u) + total)
        0 o <= graph_e (base g)).
      { destruct (base g) in Hrows_total |- *. exact Hrows_total. }
      clear Hrows_total. rename Hrow_bound into Hrows_total.
      assert (Hsizes_big : (1 + T_dom_sizes m o <= k_size * budget)%N).
      { eapply N.le_trans; [exact Hsizes_time|]. now apply N.mul_le_mono_l. }
      assert (Hedges_big : (T_dom_edges g root m o pos (dom_sizes m o) <=
        (PTrieT.c_trie + 512) * budget)%N).
      { eapply N.le_trans; [exact Hedges_time|]. apply N.mul_le_mono_l.
        assert (Hnatural : (length o +
          fold_right (fun u total => length (succs (base g) u) + total) 0 o + 1) *
            (graph_width (base g) + 1) <=
          (graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)).
        { apply Nat.mul_le_mono_r. lia. }
        unfold budget. lia. }
      time_simpl. unfold k_edge.
      clear -Hscan_time Hread_big Hsizes_big Hedges_big. clearbody budget.
      nia.
    - time_simpl. unfold k_edge.
      clear -Hscan_time Hread_big. clearbody budget.
      nia.
  Qed.

  Lemma T6_tree : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= k_tree * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g r m o Hcheck. change (DomCode.check g r m o = true) in Hcheck.
    rewrite dom_check_agrees in Hcheck. unfold dom_check_spec in Hcheck.
    destruct (dom_read_known (dom_scan g) r o) as [pos|] eqn:Hread;
      [|discriminate Hcheck].
    destruct (dom_map_check_known (dom_scan g) r m o) eqn:Hmap;
      [|discriminate Hcheck].
    destruct (dom_read_known_success g r o pos Hread)
      as [Hunique [Hlength [_ [Hlisted _]]]].
    assert (Hkeys : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
    { intros v Hv. apply dom_listed_key_width. now apply Hlisted. }
    pose proof (dom_map_check_domain g r m o Hmap) as Hdomain.
    assert (Hparents : forall v p, In v o -> trie_get v m = Some p -> In p o).
    { intros v p Hv Hp. exact (proj2 (Hdomain v p Hp)). }
    pose proof (dom_read_positions_width g r o pos Hread) as Hpositions.
    rewrite (dom_read_known_positions (dom_scan g) r o pos Hread) in Hpositions.
    assert (Hvalues : forall x,
      N.size_nat (dom_size_get (dom_sizes m o) x) <= graph_width (base g) + 1).
    { intro x. eapply dom_distinct_twice_width; [exact Hunique|exact Hkeys|].
      now apply dom_sizes_value_bound. }
    pose proof (dom_time_positions o (graph_width (base g)) Hkeys) as Hnumber.
    pose proof (T4_sizes g m o Hunique Hlength Hlisted Hparents) as Hsizes_time.
    unfold T_sizes in Hsizes_time.
    pose proof (@dom_time_fold_left (ptrie (list positive)) positive
      (dom_child_push m) (T_dom_child_push m)
      ((PTrieT.c_trie + 8) * N.of_nat (graph_width (base g) + 1))%N o Empty
      ltac:(intros v Hv rows; apply dom_time_child_push;
        [now apply Hkeys|intros p Hp; apply Hkeys; now apply (Hparents v p)])) as Hchildren.
    pose proof (@dom_time_fold_left (ptrie N) positive
      (dom_end_push (dom_positions o) (dom_sizes m o))
      (T_dom_end_push (dom_positions o) (dom_sizes m o))
      ((PTrieT.c_trie + 32) * N.of_nat (graph_width (base g) + 1))%N o Empty
      ltac:(intros v Hv ends; apply dom_time_end_push;
        [now apply Hkeys|intros n Hn; now apply (Hpositions v n)|apply Hvalues])) as Hends.
    pose proof (dom_child_weight_fold m o Empty (graph_width (base g))
      (fun v p Hv Hp => Hkeys p (Hparents v p Hv Hp))) as Hweight.
    pose proof (dom_time_child_map (dom_child_rows m o)) as Hreverse.
    change (dom_child_weight (dom_child_rows m o) <=
      length o * (graph_width (base g) + 1)) in Hweight.
    unfold T_tree. time_simpl.
    set (child_cost := List.T_fold_left (dom_child_push m) (T_dom_child_push m) o Empty) in *.
    change (1 + (T_dom_positions o + (T_dom_sizes m o +
      (child_cost +
      (List.T_fold_left (dom_end_push (dom_positions o) (dom_sizes m o))
        (T_dom_end_push (dom_positions o) (dom_sizes m o)) o Empty +
      PTrieT.T_map (fun vs : list positive => rev_append vs [])
        (fun vs : list positive => (1 + List.T_rev_append vs [])%N)
        (dom_child_rows m o))))) <=
      k_tree * N.of_nat ((graph_n (base g) + 1) * (graph_width (base g) + 1)))%N.
    set (end_cost := List.T_fold_left (dom_end_push (dom_positions o) (dom_sizes m o))
      (T_dom_end_push (dom_positions o) (dom_sizes m o)) o Empty) in *.
    set (reverse_cost := PTrieT.T_map (fun vs : list positive => rev_append vs [])
      (fun vs : list positive => (1 + List.T_rev_append vs [])%N)
      (dom_child_rows m o)) in *.
    change (child_cost <=
      ((PTrieT.c_trie + 8) * N.of_nat (graph_width (base g) + 1) + 1) *
        N.of_nat (length o) + 1)%N in Hchildren.
    change (end_cost <=
      ((PTrieT.c_trie + 32) * N.of_nat (graph_width (base g) + 1) + 1) *
        N.of_nat (length o) + 1)%N in Hends.
    change (reverse_cost <= 32 * N.of_nat (dom_child_weight (dom_child_rows m o) + 1))%N
      in Hreverse.
    clearbody child_cost end_cost reverse_cost.
    set (budget := N.of_nat ((graph_n (base g) + 1) * (graph_width (base g) + 1))).
    assert (Hsmall : (N.of_nat ((length o + 1) * (graph_width (base g) + 1)) <= budget)%N).
    { assert (Hnatural : (length o + 1) * (graph_width (base g) + 1) <=
        (graph_n (base g) + 1) * (graph_width (base g) + 1)).
      { apply Nat.mul_le_mono_r. lia. }
      unfold budget. lia. }
    assert (Hnumber_big : (T_dom_positions o <= (4 * PTrieT.c_trie + 64) * budget)%N).
    { eapply N.le_trans; [exact Hnumber|]. now apply N.mul_le_mono_l. }
    assert (Hsizes_big : (T_dom_sizes m o <= k_size * budget)%N).
    { change (1 + T_dom_sizes m o <= k_size * budget)%N in Hsizes_time. lia. }
    assert (Hchildren_big : (child_cost <= (PTrieT.c_trie + 16) * budget)%N).
    { eapply N.le_trans; [exact Hchildren|].
      eapply N.le_trans; [|apply N.mul_le_mono_l; exact Hsmall].
      clear -Hchildren. rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    assert (Hends_big : (end_cost <= (PTrieT.c_trie + 64) * budget)%N).
    { eapply N.le_trans; [exact Hends|].
      eapply N.le_trans; [|apply N.mul_le_mono_l; exact Hsmall].
      clear -Hends. rewrite !Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    assert (Hreverse_big : (reverse_cost <= 32 * budget)%N).
    { eapply N.le_trans; [exact Hreverse|]. apply N.mul_le_mono_l.
      assert (Hnatural : dom_child_weight (dom_child_rows m o) + 1 <=
        (graph_n (base g) + 1) * (graph_width (base g) + 1)).
      { clear -Hweight Hlength. nia. }
      unfold budget. lia. }
    assert (Hpositive : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    fold budget. unfold k_tree.
    clear -Hnumber_big Hsizes_big Hchildren_big Hends_big Hreverse_big Hpositive.
    clearbody budget.
    nia.
  Qed.

  Lemma T7_dfs : forall g r, prepared_ok g ->
    (T_lt_dfs g r <= k_dfs * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof.
    intros g r Hprepared.
    change (1 + T_dom_lt_dfs g r <= dom_lt_dfs_coefficient *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (graph_width (base g) + 1)))%N.
    rewrite (N.add_comm 1 (T_dom_lt_dfs g r)).
    apply dom_time_lt_dfs.
  Qed.

  Lemma F13_ops_length : forall g r, prepared_ok g ->
    length (lt_ops g r) <= 2 * (graph_n (base g) + graph_e (base g)) + 1.
  Proof.
    intros g r Hprepared. apply dom_lt_operations_length. exact Hprepared.
  Qed.

  Lemma T8_link_eval : forall g r, prepared_ok g ->
    (T_run_ops (lt_ops g r) (lt_init g r) <= k_le *
      N.of_nat ((length (lt_ops g r) + graph_n (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof.
    intros g r Hprepared.
    change (1 + T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r) <=
      (32 * 1024 * (c_loopN + 1) * (PTrieT.c_trie + 1)) *
        N.of_nat ((length (dom_lt_ops g r) + graph_n (base g) + 1) *
          (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
    rewrite N.add_comm. apply dom_lt_replay_time.
  Qed.

  Lemma T9_semi : forall g r, prepared_ok g ->
    (T_lt_semi g r <= k_semi * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)) + T_run_ops (lt_ops g r) (lt_init g r))%N.
  Proof.
    intros g r Hprepared.
    pose proof (dom_lt_parents_replay_clock g r Hprepared) as Hclock.
    change (1 + T_dom_lt_parents g r <= dom_lt_semi_coefficient *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (graph_width (base g) + 1)) +
      (1 + T_dom_lt_run_ops (dom_lt_ops g r) (dom_lt_replay_initial g r)))%N.
    lia.
  Qed.

  Lemma T10_order : forall g r, prepared_ok g ->
    (T_lt_order g r <= k_order *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof.
    intros g r Hprepared.
    change (1 + T_dom_build_order g r <=
      (5 * dom_order_body_coefficient + k_semi + 4 * k_le) *
        N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
          (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
    rewrite (N.add_comm 1 (T_dom_build_order g r)).
    apply dom_order_graph_wrapper.
    - exact Hprepared.
    - now apply dom_order_graph_body_time.
    - apply dom_lt_replay_time.
  Qed.

  (** Parent containment tests charge each accepted order entry. *)
  Lemma T4b_sizes_ok : forall g r m o pos,
      read (scan g) r o = Some pos -> map_check (scan g) r m o = true ->
      (T_sizes_ok m pos (sizes m o) o <= k_size * N.of_nat ((graph_n (base g) + 1) *
        (graph_width (base g) + 1)))%N.
  Proof.
    intros g r m o pos Hread Hmap.
    change (dom_read_known (dom_scan g) r o = Some pos) in Hread.
    change (dom_map_check_known (dom_scan g) r m o = true) in Hmap.
    destruct (dom_read_known_success g r o pos Hread)
      as [Hunique [Hlength [_ [Hlisted _]]]].
    assert (Hkeys : forall v, In v o -> Pos.size_nat v <= graph_width (base g)).
    { intros v Hv. apply dom_listed_key_width. now apply Hlisted. }
    pose proof (dom_map_check_domain g r m o Hmap) as Hdomain.
    pose proof (dom_read_positions_width g r o pos Hread) as Hpositions.
    assert (Hvalues : forall x,
      N.size_nat (dom_size_get (dom_sizes m o) x) <= graph_width (base g) + 1).
    { intro x. eapply dom_distinct_twice_width; [exact Hunique|exact Hkeys|].
      now apply dom_sizes_value_bound. }
    pose proof (dom_time_sizes_ok m pos (dom_sizes m o) o (graph_width (base g))
      Hkeys (fun v p Hv Hp => Hkeys p (proj2 (Hdomain v p Hp)))
      Hpositions Hvalues) as Htime.
    unfold T_sizes_ok, sizes. unfold k_size.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  (** The checker runs its phases in order and stops at the first rejection. *)
  Lemma T11_check : forall g r m o,
      (T_check g r m o <= k_check * (T_scan g + T_read (scan g) r o +
        T_map_check (scan g) r m o +
        match read (scan g) r o with
        | Some pos => if map_check (scan g) r m o
            then T_sizes m o + T_sizes_ok m pos (sizes m o) o + T_edges g m o else 0
        | None => 0
        end + 1))%N.
  Proof.
    intros g r m o.
    unfold T_check, T_scan, T_read, T_map_check, T_sizes, T_sizes_ok, T_edges.
    unfold scan, read, map_check, sizes, sizes_ok, k_check.
    time_simpl.
    destruct (dom_read_known (dom_scan g) r o) as [pos|] eqn:Hread.
    - pose proof (F2c_read g r o pos Hread) as [_ [_ [Hhead Hrest]]].
      pose proof (dom_time_map_check_pos (dom_scan g) r m o pos Hread) as Hmap_time.
      rewrite <- (dom_map_check_known_pos (dom_scan g) r m o pos Hread).
      destruct o as [|h rest]; [discriminate|]. cbn in Hhead. injection Hhead as Hhead.
      subst h.
      unfold dom_read. cbn beta iota zeta.
      rewrite Hread.
      destruct (dom_map_check_known (dom_scan g) r m (r :: rest)) eqn:Hmap.
      all: time_simpl; nia.
    - time_simpl. nia.
  Qed.

  Lemma T_check_le : forall g r m o,
    (T_check g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g r m o.
    set (budget := N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))).
    assert (Hsmall_nat : (graph_n (base g) + 1) * (graph_width (base g) + 1) <=
      (graph_n (base g) + graph_e (base g) + 1) * (graph_width (base g) + 1)).
    { apply Nat.mul_le_mono_r. lia. }
    assert (Hsmall : (N.of_nat ((graph_n (base g) + 1) * (graph_width (base g) + 1))
      <= budget)%N) by (unfold budget; lia).
    assert (Hpositive : (1 <= budget)%N) by (unfold budget; nia).
    pose proof (T1_scan g) as Hscan. fold budget in Hscan.
    assert (Hread : (T_read (scan g) r o <= k_read * budget)%N).
    { eapply N.le_trans; [apply T2_read|]. now apply N.mul_le_mono_l. }
    assert (Hmap : (T_map_check (scan g) r m o <= k_map * budget)%N).
    { eapply N.le_trans; [apply T3_map|]. now apply N.mul_le_mono_l. }
    assert (Hextras :
      (match read (scan g) r o with
       | Some pos => if map_check (scan g) r m o then
           T_sizes m o + T_sizes_ok m pos (sizes m o) o + T_edges g m o else 0
       | None => 0
       end <= (2 * k_size + k_edge) * budget)%N).
    { destruct (read (scan g) r o) as [pos|] eqn:Hpositions; [|nia].
      destruct (map_check (scan g) r m o) eqn:Hparents; [|nia].
      destruct (F2c_read g r o pos Hpositions) as
        [Hunique [Hlength [Hhead [Hlisted Hpositioned]]]].
      pose proof (F2d_map g r m o Hparents) as Hclosed.
      assert (Hsizes : (T_sizes m o <= k_size * budget)%N).
      { eapply N.le_trans; [eapply T4_sizes; eassumption|].
        now apply N.mul_le_mono_l. }
      assert (Hintervals : (T_sizes_ok m pos (sizes m o) o <= k_size * budget)%N).
      { eapply N.le_trans; [eapply T4b_sizes_ok; eassumption|].
        now apply N.mul_le_mono_l. }
      assert (Hnodes : nodes g = verts (base g)).
      { destruct g as [[vertices adjacency] predecessors count_v count_e]. reflexivity. }
      rewrite Hnodes in Hlisted.
      pose proof (T5_edges g m o Hlength Hlisted Hclosed) as Hedges.
      fold budget in Hedges. nia. }
    pose proof (T11_check g r m o) as Hcheck.
    assert (Hconstant :
      (k_check * (k_scan + k_read + k_map + 2 * k_size + k_edge + 1) <= c_dom)%N).
    { unfold c_dom. nia. }
    rewrite <- N.mul_assoc, <- Nat2N.inj_mul. fold budget.
    nia.
  Qed.

  Lemma T_tree_le : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g r m o Hcheck.
    pose proof (T6_tree g r m o Hcheck) as Htree.
    rewrite Nat2N.inj_mul in Htree.
    assert (Hconstant : (k_tree <= c_dom)%N) by (unfold c_dom; nia).
    assert (Hsize : (N.of_nat (graph_n (base g) + 1) <=
      N.of_nat (graph_n (base g) + graph_e (base g) + 1))%N) by lia.
    eapply N.le_trans; [exact Htree|].
    rewrite <- N.mul_assoc. apply N.mul_le_mono; [exact Hconstant|].
    apply N.mul_le_mono_r. exact Hsize.
  Qed.

  Lemma T_dominates_b_le : forall t u v,
    (T_dominates_b t u v <= c_dom * N.of_nat (query_width t u v + 1))%N.
  Proof.
    assert (Hconstant : (64 <= c_dom)%N) by (unfold c_dom; nia).
    intros [parents rows positions ends] u v.
    unfold T_dominates_b, query_width. time_simpl.
    change graph_max with Nat.max.
    cbn [pre post]. PTrieT.trie_get_le.
    destruct (trie_get u positions) as [a|] eqn:Ha;
      destruct (trie_get u ends) as [b|] eqn:Hb;
      destruct (trie_get v positions) as [c|] eqn:Hc;
      destruct (trie_get v ends) as [d|] eqn:Hd.
    all: cbn beta iota zeta; time_simpl; time_pose; time_cbn_all; nia.
  Qed.

  (** Building runs the search, the semidominator phases and the order phase. *)
  Lemma T11b_build : forall g r, prepared_ok g ->
      (T_build g r <= T_lt_dfs g r + T_lt_semi g r + T_lt_order g r + k_build)%N.
  Proof.
    intros g r Hready.
    pose proof (T_dom_build_candidate_phases g r) as Hphases.
    unfold T_build, T_lt_semi, T_lt_order, k_build.
    time_simpl. lia.
  Qed.

  Lemma T_build_le : forall g r, prepared_ok g ->
    (T_build g r <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (Nat.log2 (graph_n (base g)) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g r Hready.
    pose proof (T11b_build g r Hready) as Hbuild.
    pose proof (T7_dfs g r Hready) as Hdfs.
    pose proof (T9_semi g r Hready) as Hsemi.
    pose proof (T8_link_eval g r Hready) as Heval.
    pose proof (F13_ops_length g r Hready) as Hlength.
    pose proof (T10_order g r Hready) as Horder.
    rewrite !Nat2N.inj_mul in Hdfs, Hsemi, Heval, Horder.
    set (a := N.of_nat (graph_n (base g) + graph_e (base g) + 1)) in *.
    set (w := N.of_nat (graph_width (base g) + 1)) in *.
    set (l := N.of_nat (Nat.log2 (graph_n (base g)) + 1)) in *.
    assert (Ha : (1 <= a)%N) by (unfold a; lia).
    assert (Hw : (1 <= w)%N) by (unfold w; lia).
    assert (Hl : (1 <= l)%N) by (unfold l; lia).
    assert (Hoperations : (N.of_nat (length (lt_ops g r) + graph_n (base g) + 1)
      <= 4 * a)%N) by (unfold a; lia).
    assert (Heval_bound : (T_run_ops (lt_ops g r) (lt_init g r) <=
      4 * k_le * (a * l * w))%N) by nia.
    assert (Hbase : (a * w <= a * l * w)%N) by nia.
    assert (Hunit : (1 <= a * l * w)%N) by nia.
    assert (Hconstant : (k_dfs + k_semi + 4 * k_le + k_order + k_build <= c_dom)%N).
    { unfold c_dom. nia. }
    nia.
  Qed.

  Lemma check_bigO : bigO (fun _ : prepared * positive * ptrie positive * list positive => True)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_check g r m o).
  Proof.
    exists c_dom. intros [[[g r] m] o] Htrue.
    pose proof (T_check_le g r m o) as Hbound.
    rewrite Nat2N.inj_mul. nia.
  Qed.

  (** Tree numbering pays only for the listed vertices and their key width. *)
  Lemma tree_bigO : bigO (fun '(g, r, m, o) => check g r m o = true)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + 1) * (graph_width (base g) + 1)))
    (fun '(g, r, m, o) => T_tree g r m o).
  Proof.
    exists k_tree. intros [[[g r] m] o] Hcheck.
    pose proof (T6_tree g r m o Hcheck) as Htree. nia.
  Qed.

  Lemma dominates_b_bigO : bigO (fun _ : domtree * positive * positive => True)
    (fun '(t, u, v) => N.of_nat (query_width t u v + 1))
    (fun '(t, u, v) => T_dominates_b t u v).
  Proof.
    exists c_dom. intros [[t u] v] Htrue.
    pose proof (T_dominates_b_le t u v) as Hbound. nia.
  Qed.

  Lemma build_bigO : bigO (fun '(g, _) => prepared_ok g)
    (fun '(g, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))
    (fun '(g, r) => T_build g r).
  Proof.
    exists c_dom. intros [g r] Hready.
    pose proof (T_build_le g r Hready) as Hbound.
    rewrite !Nat2N.inj_mul. nia.
  Qed.

End DomT.
