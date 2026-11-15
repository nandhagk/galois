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

Local Lemma dom_nodes_verts : forall g, nodes g = verts (base g).
Proof.
  intros [[vs adjacency] predecessors count_v count_e]. reflexivity.
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
  Definition k_scan : N := 1%N. (* STUB *)
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
  Proof. Admitted. (* STUB *)

  Lemma T1_scan : forall g,
    (T_scan g <= k_scan * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

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
