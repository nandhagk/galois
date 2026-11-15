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


Module DomCode <: DOM_OPS.
  Definition build := dom_build_candidate.

  Definition check (g : prepared) (r : positive) (m : ptrie positive)
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
  | Some p => PTrieCode.set p (v :: dom_child_row rows p) rows
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

Module Dom <: DOM.
  Include DomCode.
  Include DOM_SPEC.

  Lemma check_sound : forall g r m o, check g r m o = true -> dom_exact g r m.
  Proof. Admitted. (* STUB *)

  Lemma tree_idom : forall g r m o, check g r m o = true -> idom (tree g r m o) = m.
  Proof.
    intros g r m o _. reflexivity.
  Qed.

  Lemma tree_exact : forall g r m o, check g r m o = true -> domtree_exact g r (tree g r m o).
  Proof. Admitted. (* STUB *)

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
    destruct (tree_exact g r m o Hcheck) as [_ [_ [_ [Hchildren [Hsorted _]]]]].
    split.
    - intro v. rewrite Hchildren, (tree_idom g r m o Hcheck). reflexivity.
    - exact (Hsorted u).
  Qed.
End Dom.

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
  Definition k_read : N := 1%N. (* STUB *)
  Definition k_map : N := 1%N. (* STUB *)
  Definition k_size : N := 1%N. (* STUB *)
  Definition k_edge : N := 1%N. (* STUB *)
  Definition k_tree : N := 1%N. (* STUB *)
  Definition k_dfs : N := 1%N. (* STUB *)
  Definition k_semi : N := 1%N. (* STUB *)
  Definition k_le : N := 1%N. (* STUB *)
  Definition k_order : N := 1%N. (* STUB *)
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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma F12_tree_exact : forall g r m o, check g r m o = true ->
  domtree_exact g r (tree g r m o).
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma T3_map : forall g r m o,
    (T_map_check (scan g) r m o <= k_map * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_sizes : forall g m o, NoDup o -> length o <= graph_n (base g) ->
    (forall v, In v o -> In v (nodes g)) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_sizes m o <= k_size * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_edges : forall g m o, length o <= graph_n (base g) ->
    (forall v, In v o -> In v (verts (base g))) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_edges g m o <= k_edge * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_tree : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= k_tree * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_dfs : forall g r, prepared_ok g ->
    (T_lt_dfs g r <= k_dfs * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma F13_ops_length : forall g r, prepared_ok g ->
    length (lt_ops g r) <= 2 * (graph_n (base g) + graph_e (base g)) + 1.
  Proof. Admitted. (* STUB *)

  Lemma T8_link_eval : forall g r, prepared_ok g ->
    (T_run_ops (lt_ops g r) (lt_init g r) <= k_le *
      N.of_nat ((length (lt_ops g r) + graph_n (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T9_semi : forall g r, prepared_ok g ->
    (T_lt_semi g r <= k_semi * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)) + T_run_ops (lt_ops g r) (lt_init g r))%N.
  Proof. Admitted. (* STUB *)

  Lemma T10_order : forall g r, prepared_ok g ->
    (T_lt_order g r <= k_order *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Parent containment tests charge each accepted order entry. *)
  Lemma T4b_sizes_ok : forall g r m o pos,
      read (scan g) r o = Some pos -> map_check (scan g) r m o = true ->
      (T_sizes_ok m pos (sizes m o) o <= k_size * N.of_nat ((graph_n (base g) + 1) *
        (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

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
    cbn [pre post]. rewrite !PTrieT.trie_get_clock.
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

  Lemma tree_bigO : bigO (fun '(g, r, m, o) => check g r m o = true)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_tree g r m o).
  Proof.
    exists c_dom. intros [[[g r] m] o] Hcheck.
    pose proof (T_tree_le g r m o Hcheck) as Hbound.
    rewrite Nat2N.inj_mul. nia.
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
