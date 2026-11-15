(** * Weak topological order production and checking

    The producer recursively removes an entry header from each cyclic component.
    For example, a singleton self edge produces an empty loop body.
    Builds on: Tarjan search, first-order graph data and the WTO signature. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Sorting.Permutation
  Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search SccSig Scc WtoSig.
Import List.ListNotations.

Module TimeHelpers.
  Module List.
    TimeFun List.concat.
  End List.
End TimeHelpers.

Definition wto_member (v : positive) xs := existsb (Pos.eqb v) xs.
TimeFun wto_member.

(** Boolean membership recognizes exactly the supplied vertex list. *)
Lemma wto_member_spec : forall v vs, wto_member v vs = true <-> In v vs.
Proof.
  intros v vs. unfold wto_member. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hin. exists v. split; [exact Hin|apply Pos.eqb_refl].
Qed.

Definition wto_scoped (g : prepared) (within : option (list positive)) : prepared :=
  match within with
  | None => g
  | Some vs =>
    let listed := fold_left (fun acc v => PTrieCode.set v true acc) vs Empty in
    let adjacency := fold_left (fun acc v =>
      PTrieCode.set v (filter (fun u =>
        match trie_get u listed with Some _ => true | None => false end)
        (succs (base g) v)) acc) vs Empty in
    Prepared (Digraph vs adjacency) Empty (nv g) (ne g)
  end.
TimeFun wto_scoped.

(** Materialization keeps exactly the selected vertices and their selected successors. *)
Lemma wto_scoped_spec : forall g vs,
  nodes (wto_scoped g (Some vs)) = vs /\
  forall v, In v vs -> succs (base (wto_scoped g (Some vs))) v =
    filter (fun u => wto_member u vs) (succs (base g) v).
Proof.
  intros g vs. split; [reflexivity|]. intros v Hin.
  unfold wto_scoped. cbn [base succs]. rewrite scc_rows_lookup.
  assert (Hmember : existsb (Pos.eqb v) vs = true) by (now apply wto_member_spec).
  rewrite Hmember. apply filter_ext. intro u. apply scc_listed_test.
Qed.

Definition wto_components g roots :=
  let ready := scc_graph g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev_append (tarjan_emitted s) []).
TimeFun wto_components.

Definition wto_offer i v (entries : ptrie positive) :=
  match trie_get i entries with Some _ => entries | None => PTrieCode.set i v entries end.
TimeFun wto_offer.

Definition wto_root_entry owners entries v :=
  match trie_get v owners with None => entries | Some i => wto_offer i v entries end.
TimeFun wto_root_entry.

Definition wto_edge_entry owners source entries v :=
  match source, trie_get v owners with
  | Some i, Some j => if Pos.eqb i j then entries else wto_offer j v entries
  | _, _ => entries
  end.
TimeFun wto_edge_entry.

Definition wto_entries g roots r :=
  let owners := comp r in
  let seeded := fold_left (wto_root_entry owners) roots Empty in
  fold_left (fun entries c => fold_left (fun entries u =>
    fold_left (wto_edge_entry owners (trie_get u owners)) (succs (base g) u) entries)
    c entries) (comps r) seeded.
TimeFun wto_entries.

Definition wto_preferred (owners entries : ptrie positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: _ => match trie_get v owners with None => None | Some i => trie_get i entries end
  end.
TimeFun wto_preferred.

Fixpoint wto_select (preferred : option positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: rest =>
    if match preferred with None => false | Some h => Pos.eqb v h end
    then Some (v, rest)
    else match wto_select preferred rest with
      | None => Some (v, rest)
      | Some (h, body) => Some (h, v :: body)
      end
  end.
TimeFun wto_select.

(** Selection moves one header occurrence to the front and preserves all other occurrences. *)
Lemma wto_select_spec : forall preferred c h body,
  wto_select preferred c = Some (h, body) -> Permutation c (h :: body).
Proof.
  intros preferred c. induction c as [|v rest IH]; intros h body Hselect.
  - discriminate.
  - cbn [wto_select] in Hselect.
    destruct (match preferred with None => false | Some head => Pos.eqb v head end).
    + inversion Hselect; subst. apply Permutation_refl.
    + destruct (wto_select preferred rest) as [[head tail]|] eqn:Htail.
      * inversion Hselect; subst. eapply Permutation_trans.
        -- apply perm_skip. now apply IH.
        -- apply perm_swap.
      * inversion Hselect; subst. apply Permutation_refl.
Qed.

Fixpoint wto_reverse_into (w tail : wto) : wto :=
  match w with
  | WNil => tail
  | WVertex v rest => wto_reverse_into rest (WVertex v tail)
  | WLoop h body rest => wto_reverse_into rest (WLoop h body tail)
  end.
TimeFun wto_reverse_into.

Definition wto_expand_tasks within entries owners cs :=
  map (fun c => WtoExpand within entries owners c) cs.
TimeFun wto_expand_tasks.

Definition wto_step (g : prepared) (s : wto_state) : wto_state + wto :=
  match s with
  | WtoState [] partial _ => inr (wto_reverse_into partial WNil)
  | WtoState (WtoClose h :: tasks) partial (parent :: parents) =>
    inl (WtoState tasks (WLoop h (wto_reverse_into partial WNil) parent) parents)
  | WtoState (WtoClose _ :: tasks) partial [] => inl (WtoState tasks partial [])
  | WtoState (WtoExpand within entries owners c :: tasks) partial parents =>
    match wto_select (wto_preferred owners entries c) c with
    | None => inl (WtoState tasks partial parents)
    | Some (h, []) =>
      let tree := if wto_member h (succs (base g) h)
        then WLoop h WNil partial else WVertex h partial in
      inl (WtoState tasks tree parents)
    | Some (h, body) =>
      let child := Some body in
      let scoped := wto_scoped g child in
      let roots := rev_append body [] in
      let r := wto_components scoped roots in
      let entries' := wto_entries scoped roots r in
      inl (WtoState
        (wto_expand_tasks child entries' (comp r) (rev_append (comps r) []) ++
          WtoClose h :: tasks)
        WNil (partial :: parents))
    end
  end.
TimeFun wto_step.

Fixpoint wto_unique (xs : list positive) :=
  match xs with
  | [] => true
  | v :: rest => negb (wto_member v rest) && wto_unique rest
  end.
TimeFun wto_unique.

(** Duplicate checking reflects uniqueness of the vertex occurrences. *)
Lemma wto_unique_spec : forall vs, wto_unique vs = true <-> NoDup vs.
Proof.
  induction vs as [|v rest IH]; cbn [wto_unique].
  - split; [intro H; constructor|intro H; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, wto_member_spec, IH.
    split; [intros [Hfresh Hrest]; now constructor|intro H; now inversion H].
Qed.

Fixpoint wto_annotate (stack : list positive) (w : wto) :
    list (positive * list positive) :=
  match w with
  | WNil => []
  | WVertex v rest => (v, stack) :: wto_annotate stack rest
  | WLoop h body rest =>
    (h, h :: stack) :: (wto_annotate (h :: stack) body ++ wto_annotate stack rest)
  end.
TimeFun wto_annotate.

Fixpoint wto_positions (rows : list (positive * list positive)) :
    ptrie (list positive * list positive) :=
  match rows with
  | [] => Empty
  | (v, stack) :: rest => PTrieCode.set v (map fst rest, stack) (wto_positions rest)
  end.
TimeFun wto_positions.

Definition wto_edge_b index a b :=
  match trie_get a index with
  | None => false
  | Some (after, stack) => wto_member b after || wto_member b stack
  end.
TimeFun wto_edge_b.

Fixpoint wto_rank_rows (start : positive) (vs : list positive) : ptrie positive :=
  match vs with
  | [] => Empty
  | v :: rest => PTrieCode.set v start (wto_rank_rows (Pos.succ start) rest)
  end.
TimeFun wto_rank_rows.

(** Width rejection stops before traversing an oversized candidate key. *)
Fixpoint wto_key_fits (width : nat) (v : positive) : bool :=
  match width, v with
  | O, _ => false
  | S _, xH => true
  | S rest, xO tail | S rest, xI tail => wto_key_fits rest tail
  end.
TimeFun wto_key_fits.

(** Each candidate transition visits one constructor or closes one loop interval. *)
Definition wto_check_step (width : nat) (listed : ptrie bool) (s : wto_check_state)
    : wto_check_state + option (ptrie N * ptrie (N * N) * list positive) :=
  match s with
  | WtoCheckState [] _ ranks intervals vs =>
    inr (Some (ranks, intervals, rev_append vs []))
  | WtoCheckState (task :: rest) next ranks intervals vs =>
    match task with
    | WtoCheckClose h =>
      match trie_get h ranks with
      | None => inr None
      | Some lo => inl (WtoCheckState rest next ranks
          (PTrieCode.set h (lo, next) intervals) vs)
      end
    | WtoCheckVisit WNil => inl (WtoCheckState rest next ranks intervals vs)
    | WtoCheckVisit (WVertex v tail) =>
      if wto_key_fits width v then
        match trie_get v listed, trie_get v ranks with
        | Some _, None => inl (WtoCheckState (WtoCheckVisit tail :: rest) (N.succ next)
            (PTrieCode.set v next ranks) intervals (v :: vs))
        | _, _ => inr None
        end
      else inr None
    | WtoCheckVisit (WLoop h body tail) =>
      if wto_key_fits width h then
        match trie_get h listed, trie_get h ranks with
        | Some _, None => inl (WtoCheckState
            (WtoCheckVisit body :: WtoCheckClose h :: WtoCheckVisit tail :: rest)
            (N.succ next) (PTrieCode.set h next ranks) intervals (h :: vs))
        | _, _ => inr None
        end
      else inr None
    end
  end.
TimeFun wto_check_step.

Definition wto_check_index (fuel : N) (width : nat) (listed : ptrie bool)
    (tasks : list wto_check_task) (next : N) (ranks : ptrie N)
    (intervals : ptrie (N * N)) (vs : list positive)
    : option (ptrie N * ptrie (N * N) * list positive) :=
  match loopN (wto_check_step width listed) fuel (WtoCheckState tasks next ranks intervals vs) with
  | inl _ => None
  | inr result => result
  end.
TimeFun wto_check_index.

(** The candidate index records exactly its distinct, listed processed vertices. *)
Definition wto_check_seen (listed : ptrie bool) (s : wto_check_state) : Prop :=
  NoDup (wto_check_vertices s) /\
  (forall v, In v (wto_check_vertices s) <->
    exists r, trie_get v (wto_check_ranks s) = Some r) /\
  forall v, In v (wto_check_vertices s) -> exists b, trie_get v listed = Some b.

(** Successful index results contain distinct listed vertices. *)
Definition wto_check_seen_result (listed : ptrie bool)
    (result : option (ptrie N * ptrie (N * N) * list positive)) : Prop :=
  match result with
  | None => True
  | Some (_, _, vs) => NoDup vs /\
      forall v, In v vs -> exists b, trie_get v listed = Some b
  end.

(** A fresh listed vertex preserves the index's processed-vertex invariant. *)
Lemma wto_check_seen_add : forall listed tasks next ranks intervals vs v b,
  wto_check_seen listed (WtoCheckState tasks next ranks intervals vs) ->
  trie_get v ranks = None -> trie_get v listed = Some b ->
  forall tasks' intervals', wto_check_seen listed
    (WtoCheckState tasks' (N.succ next) (PTrieCode.set v next ranks) intervals' (v :: vs)).
Proof.
  intros listed tasks next ranks intervals vs v b [Hunique [Hrank Hlisted]] Hfresh Hvalid
    tasks' intervals'. unfold wto_check_seen.
  cbn [wto_check_vertices wto_check_ranks] in *.
  split.
  - constructor; [|exact Hunique]. intro Hin.
    destruct (proj1 (Hrank v) Hin) as [r Hget]. congruence.
  - split.
    + intro u. cbn [In]. destruct (Pos.eq_dec u v) as [->|Hne].
      * rewrite PTrie.get_set_same. split; [intro H; eauto|intro H; now left].
      * rewrite PTrie.get_set_other by exact Hne. rewrite <- Hrank. split.
        -- intros [Heq|Hin]; [congruence|exact Hin].
        -- intro Hin. now right.
    + intros u [Heq|Hin].
      * subst u. now exists b.
      * now apply Hlisted.
Qed.

(** Every checker transition preserves the vertex invariant or returns a valid result. *)
Lemma wto_check_seen_step : forall width listed s,
  wto_check_seen listed s ->
  match wto_check_step width listed s with
  | inl next => wto_check_seen listed next
  | inr result => wto_check_seen_result listed result
  end.
Proof.
  intros width listed [tasks next ranks intervals vs] Hseen.
  destruct tasks as [|task tasks].
  - cbn [wto_check_step wto_check_seen_result]. rewrite rev_append_rev, app_nil_r.
    destruct Hseen as [Hunique [Hrank Hlisted]]. split.
    + now apply NoDup_rev.
    + intros v Hin. apply Hlisted. now apply in_rev in Hin.
  - destruct task as [w|h].
    + destruct w as [|v tail|h body tail].
      * exact Hseen.
      * cbn [wto_check_step]. destruct (wto_key_fits width v); [|exact I].
        destruct (trie_get v listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get v ranks) as [r|] eqn:Hrank; [exact I|].
        eapply wto_check_seen_add; eassumption.
      * cbn [wto_check_step]. destruct (wto_key_fits width h); [|exact I].
        destruct (trie_get h listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get h ranks) as [r|] eqn:Hrank; [exact I|].
        eapply wto_check_seen_add; eassumption.
    + cbn [wto_check_step]. destruct (trie_get h ranks); [exact Hseen|exact I].
Qed.

(** The fuel driver preserves checker invariants for every accessibility witness. *)
Lemma wto_check_seen_loop : forall width listed fs (Hacc : Acc loopN_lt fs),
  wto_check_seen listed (snd fs) ->
  match loop loopN_lt (loopN_step (wto_check_step width listed)) fs Hacc with
  | inl _ => True
  | inr result => wto_check_seen_result listed result
  end.
Proof.
  intros width listed fs Hacc.
  induction Hacc as [[fuel s] Hacc IH] using Acc_ind_dep.
  cbn [snd]. intro Hseen. destruct fuel as [|p]; [exact I|].
  cbn [loop loopN_step Acc_inv].
  pose proof (wto_check_seen_step width listed s Hseen) as Hstep.
  destruct (wto_check_step width listed s) as [next|result] eqn:Hnext.
  - apply IH. exact Hstep.
  - exact Hstep.
Qed.

(** The supplied fuel cannot turn an invariant run into an invalid successful result. *)
Lemma wto_check_seen_run : forall fuel width listed s,
  wto_check_seen listed s ->
  match loopN (wto_check_step width listed) fuel s with
  | inl _ => True
  | inr result => wto_check_seen_result listed result
  end.
Proof.
  intros fuel width listed s Hseen. unfold loopN. now apply wto_check_seen_loop.
Qed.

Local Opaque loopN.

(** Indexing from empty maps returns only distinct keys present in its listed map. *)
Lemma wto_check_index_seen : forall fuel width listed w ranks intervals vs,
  wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
    Some (ranks, intervals, vs) ->
  NoDup vs /\ forall v, In v vs -> exists b, trie_get v listed = Some b.
Proof.
  intros fuel width listed w ranks intervals vs Hindex.
  assert (Hseen : wto_check_seen listed
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty [])).
  { split; [constructor|]. split.
    - intro v. split; [contradiction|]. intros [r Hget].
      rewrite PTrie.get_empty in Hget. discriminate.
    - intros v Hin. contradiction. }
  pose proof (wto_check_seen_run fuel width listed
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty []) Hseen) as Hresult.
  unfold wto_check_index in Hindex.
  destruct (loopN (wto_check_step width listed) fuel
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty [])) as [s|result]; [discriminate|].
  destruct result as [[[ranks' intervals'] vs']|]; [|discriminate].
  inversion Hindex; subst. exact Hresult.
Qed.

Local Transparent loopN.



Definition wto_interval_edge (ranks : ptrie N) (intervals : ptrie (N * N))
    (u v : positive) : bool :=
  match trie_get u ranks, trie_get v ranks with
  | Some ru, Some rv =>
    N.ltb ru rv ||
      match trie_get v intervals with
      | Some (lo, hi) => N.leb lo ru && N.ltb ru hi
      | None => false
      end
  | _, _ => false
  end.
TimeFun wto_interval_edge.

(** The edge scan is the final conjunct of the checker. *)
Definition wto_edges_ok (b : digraph) (ranks : ptrie N) (intervals : ptrie (N * N))
    (vs : list positive) : bool :=
  forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs b u)) vs.
TimeFun wto_edges_ok.

(** The checker builds its own listed-row graph and never reads prepared caches. *)
Definition wto_check_linear (g : prepared) (roots : list positive) (w : wto) : bool :=
  let b := base g in
  let listed := listed_of g in
  if forallb (fun v => match trie_get v listed with Some _ => true | None => false end) roots
  then
    match wto_check_index (check_fuel g) (graph_width b) listed
        [WtoCheckVisit w] 0%N Empty Empty [] with
    | None => false
    | Some (ranks, intervals, vs) =>
      let ready := scc_graph g in
      let live := entered (prepared_search_trace ready roots) in
      let reached := fold_left (fun acc v => PTrieCode.set v true acc) live Empty in
      forallb (fun v => match trie_get v reached with Some _ => true | None => false end) vs &&
      forallb (fun v => match trie_get v ranks with Some _ => true | None => false end) live &&
      wto_edges_ok b ranks intervals vs
    end
  else false.
TimeFun wto_check_linear.

Fixpoint wto_heads_into (w : wto) (acc : list positive) : list positive :=
  match w with
  | WNil => acc
  | WVertex _ rest => wto_heads_into rest acc
  | WLoop h inside rest => h :: wto_heads_into inside (wto_heads_into rest acc)
  end.
TimeFun wto_heads_into.

Fixpoint wto_order_into (w : wto) (acc : list positive) : list positive :=
  match w with
  | WNil => acc
  | WVertex v rest => v :: wto_order_into rest acc
  | WLoop h inside rest => h :: wto_order_into inside (wto_order_into rest acc)
  end.
TimeFun wto_order_into.

(** Accumulation appends the caller's suffix to each structural traversal. *)
Lemma wto_into_spec : forall w acc,
  wto_heads_into w acc = wto_heads w ++ acc /\
  wto_order_into w acc = wto_order w ++ acc.
Proof.
  induction w as [|v rest IH|h body IHbody rest IHrest]; intro acc.
  - split; reflexivity.
  - cbn [wto_heads_into wto_order_into wto_heads wto_order].
    destruct (IH acc) as [Hheads Horder]. now rewrite Hheads, Horder.
  - cbn [wto_heads_into wto_order_into wto_heads wto_order].
    destruct (IHrest acc) as [Hheads Horder]. rewrite Hheads, Horder.
    rewrite (proj1 (IHbody (wto_heads rest ++ acc))).
    rewrite (proj2 (IHbody (wto_order rest ++ acc))).
    now rewrite !app_assoc.
Qed.

(** A rank-row lookup at a unique list position returns its starting rank plus that position. *)
Lemma wto_rank_rows_at : forall vs start,
  NoDup vs -> forall i v, nth_error vs i = Some v ->
  exists p, trie_get v (wto_rank_rows start vs) = Some p /\
    Pos.to_nat p = Pos.to_nat start + i.
Proof.
  induction vs as [|x rest IH]; intros start Hunique i v Hnth.
  - rewrite nth_error_nil in Hnth. discriminate.
  - inversion Hunique as [|head tail Hfresh Hrest]; subst.
    destruct i as [|i].
    + cbn [nth_error] in Hnth. inversion Hnth; subst v.
      exists start. split.
      * apply PTrie.get_set_same.
      * lia.
    + cbn [nth_error] in Hnth.
      assert (Hneq : v <> x).
      { intro Heq. subst v. apply Hfresh. now apply nth_error_In in Hnth. }
      destruct (IH (Pos.succ start) Hrest i v Hnth) as [p [Hget Hcount]].
      exists p. split.
      * cbn [wto_rank_rows]. rewrite PTrie.get_set_other by exact Hneq. exact Hget.
      * rewrite Pos2Nat.inj_succ in Hcount. lia.
Qed.

(** Rank rows never create a binding for an absent vertex. *)
Lemma wto_rank_rows_absent : forall vs start v,
  ~ In v vs -> trie_get v (wto_rank_rows start vs) = None.
Proof.
  induction vs as [|x rest IH]; intros start v Habsent.
  - apply PTrie.get_empty.
  - cbn [wto_rank_rows]. rewrite PTrie.get_set_other.
    + apply IH. intro Hin. apply Habsent. now right.
    + intro Heq. apply Habsent. now left.
Qed.

(** Every enclosing head occurs in both structural projections. *)
Lemma wto_encloses_member : forall w h v,
  wto_encloses h v w -> In h (wto_heads w) /\ In h (wto_order w).
Proof.
  intros w h v Hencloses. induction Hencloses; cbn [wto_heads wto_order].
  - split; now left.
  - destruct IHHencloses as [Hheads Horder]. split; [exact Hheads|now right].
  - destruct IHHencloses as [Hheads Horder]. split; right;
      apply in_or_app; now left.
  - destruct IHHencloses as [Hheads Horder]. split; right;
      apply in_or_app; now right.
Qed.

(** Textual precedence is strict comparison between two occurrence positions. *)
Lemma graph_before_indices : forall vs u v,
  graph_before vs u v <-> exists i j,
    i < j /\ nth_error vs i = Some u /\ nth_error vs j = Some v.
Proof.
  intros vs u v. split.
  - intros [prefix [middle [suffix ->]]].
    exists (length prefix), (length prefix + S (length middle)). split; [lia|]. split.
    + rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    + rewrite nth_error_app2 by lia.
      replace (length prefix + S (length middle) - length prefix) with
        (S (length middle)) by lia.
      cbn [nth_error]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros [i [j [Hlt [Hu Hv]]]]. revert i j Hlt Hu Hv.
    induction vs as [|x rest IH]; intros [|i] [|j] Hlt Hu Hv;
      cbn [nth_error] in *; try lia; try discriminate.
    + inversion Hu; subst x.
      destruct (nth_error_split rest j Hv) as [middle [suffix [Heq Hlength]]].
      exists [], middle, suffix. now rewrite Heq.
    + destruct (IH i j ltac:(lia) Hu Hv) as [prefix [middle [suffix Heq]]].
      exists (x :: prefix), middle, suffix. cbn. now rewrite Heq.
Qed.

(** Unique lists give a unique position to each present vertex. *)
Lemma wto_nth_unique : forall (vs : list positive) i j v,
  NoDup vs -> nth_error vs i = Some v -> nth_error vs j = Some v -> i = j.
Proof.
  intros vs i j v Hunique Hi Hj.
  apply (proj1 (NoDup_nth_error _) Hunique).
  - apply nth_error_Some. congruence.
  - congruence.
Qed.

(** Strict list order cannot precede the same unique vertex. *)
Lemma graph_before_irrefl : forall vs v, NoDup vs -> ~ graph_before vs v v.
Proof.
  intros vs v Hunique Hbefore.
  apply graph_before_indices in Hbefore. destruct Hbefore as [i [j [Hlt [Hi Hj]]]].
  pose proof (wto_nth_unique vs i j v Hunique Hi Hj). lia.
Qed.

(** Strict list order composes on duplicate-free vertex lists. *)
Lemma graph_before_trans : forall vs u v z,
  NoDup vs -> graph_before vs u v -> graph_before vs v z -> graph_before vs u z.
Proof.
  intros vs u v z Hunique Huv Hvz.
  apply graph_before_indices in Huv. apply graph_before_indices in Hvz.
  destruct Huv as [i [j [Hij [Hi Hj]]]].
  destruct Hvz as [k [l [Hkl [Hk Hl]]]].
  pose proof (wto_nth_unique vs j k v Hunique Hj Hk) as Heq.
  apply graph_before_indices. exists i, l. repeat split; auto; lia.
Qed.

(** Adding a prefix preserves textual precedence. *)
Lemma wto_before_prefix : forall prefix vs u v,
  graph_before vs u v -> graph_before (prefix ++ vs) u v.
Proof.
  intros prefix vs u v [first [middle [last ->]]].
  exists (prefix ++ first), middle, last. now rewrite app_assoc.
Qed.

(** Adding a suffix preserves textual precedence. *)
Lemma wto_before_suffix : forall vs suffix u v,
  graph_before vs u v -> graph_before (vs ++ suffix) u v.
Proof.
  intros vs suffix u v [first [middle [last ->]]].
  exists first, middle, (last ++ suffix). rewrite <- !app_assoc.
  cbn [app]. now rewrite <- !app_assoc.
Qed.

(** A loop head is either its enclosed vertex or occurs before that vertex. *)
Lemma wto_encloses_before : forall w h v,
  wto_encloses h v w -> h = v \/ graph_before (wto_order w) h v.
Proof.
  intros w h v Hencloses. induction Hencloses; cbn [wto_order].
  - destruct H as [Heq|Hin]; [now left|right].
    destruct (in_split v _ Hin) as [first [last Hbody]].
    exists [], first, (last ++ wto_order rest). cbn [app].
    rewrite Hbody. now rewrite <- app_assoc.
  - destruct IHHencloses as [Heq|Hbefore]; [now left|right].
    exact (wto_before_prefix [u] _ h v Hbefore).
  - destruct IHHencloses as [Heq|Hbefore]; [now left|right].
    apply (wto_before_prefix [u]). now apply wto_before_suffix.
  - destruct IHHencloses as [Heq|Hbefore]; [now left|right].
    apply (wto_before_prefix [u]). now apply wto_before_prefix.
Qed.

(** A path contains its initial vertex. *)
Lemma wto_path_first : forall g u vs v, path g u vs v -> In u vs.
Proof.
  intros g u vs v Hpath. destruct Hpath; now left.
Qed.

(** Appending an edge extends the path at its recorded endpoint. *)
Lemma wto_path_snoc : forall g u vs v,
  path g u vs v -> forall z, edge g v z -> path g u (vs ++ [z]) z.
Proof.
  intros g u vs v Hpath. induction Hpath; intros z Hedge; cbn [app].
  - econstructor; [exact Hedge|constructor].
  - econstructor; [eassumption|now apply IHHpath].
Qed.

(** Rooted reachability is closed under a successor edge. *)
Lemma wto_reach_step : forall g roots u v,
  reach g roots u -> edge g u v -> reach g roots v.
Proof.
  intros g roots u v [r [vs [Hroot Hpath]]] Hedge.
  exists r, (vs ++ [v]). split; [exact Hroot|]. now apply wto_path_snoc with (v := u).
Qed.

(** A head-free rooted path advances through the unique structural order. *)
Lemma wto_path_forward : forall g roots w,
  is_wto g roots w -> forall u vs v, path (base g) u vs v ->
  reach (base g) roots u ->
  (forall x, In x vs -> ~ In x (wto_heads w)) ->
  u = v \/ graph_before (wto_order w) u v.
Proof.
  intros g roots w [Hunique [Hcover Hedges]] u vs v Hpath.
  induction Hpath as [v|u v vs z Hedge Hpath IH]; intros Hreach Hnoheads.
  - now left.
  - assert (Hbefore : graph_before (wto_order w) u v).
    { destruct (Hedges u v Hedge Hreach) as [Hbefore|Hencloses]; [exact Hbefore|].
      exfalso. apply (Hnoheads v).
      - right. now apply wto_path_first in Hpath.
      - exact (proj1 (wto_encloses_member w v u Hencloses)). }
    assert (Hreachv : reach (base g) roots v).
    { eapply wto_reach_step; eassumption. }
    destruct (IH Hreachv ltac:(intros x Hin; apply Hnoheads; now right)) as [Heq|Hlater].
    + subst z. now right.
    + right. eapply graph_before_trans; eassumption.
Qed.

(** Every reachable cycle in a structural weak order visits a loop head. *)
Lemma wto_cycle_head : forall g roots w,
  is_wto g roots w -> forall vs, cycle (base g) vs ->
  (forall v, In v vs -> reach (base g) roots v) ->
  exists h, In h vs /\ In h (wto_heads w).
Proof.
  intros g roots w Hvalid vs Hcycle Hreachable.
  destruct (existsb (fun v => wto_member v (wto_heads w)) vs) eqn:Hheads.
  - apply existsb_exists in Hheads. destruct Hheads as [h [Hin Hhead]].
    exists h. split; [exact Hin|now apply wto_member_spec in Hhead].
  - assert (Hnoheads : forall v, In v vs -> ~ In v (wto_heads w)).
    { intros v Hin Hhead. assert (Hyes : existsb (fun v =>
        wto_member v (wto_heads w)) vs = true).
      { apply existsb_exists. exists v. split; [exact Hin|now apply wto_member_spec]. }
      congruence. }
    destruct Hcycle as [u [v [tail [Heq [Hedge Hpath]]]]]. subst vs.
    destruct Hvalid as [Hunique [Hcover Hedges]].
    assert (Hreachu : reach (base g) roots u) by (apply Hreachable; now left).
    assert (Hreachv : reach (base g) roots v) by (apply Hreachable; now right; left).
    destruct (Hedges u v Hedge Hreachu) as [Hbefore|Hencloses].
    + destruct (wto_path_forward g roots w (conj Hunique (conj Hcover Hedges))
        v (v :: tail) u Hpath Hreachv
        ltac:(intros x Hin; apply Hnoheads; now right)) as [Heq|Hback].
      * subst v. exfalso. exact (graph_before_irrefl _ _ Hunique Hbefore).
      * exfalso. apply (graph_before_irrefl _ u Hunique).
        eapply graph_before_trans; eassumption.
    + exfalso. apply (Hnoheads v); [now right; left|].
      exact (proj1 (wto_encloses_member w v u Hencloses)).
Qed.

Module WtoCode <: WTO_OPS.
  Definition build (g : prepared) (roots : list positive) : wto :=
    let r := wto_components g roots in
    let entries := wto_entries g roots r in
    let cs := comps r in
    let size := length (concat cs) in
    let initial := WtoState
      (wto_expand_tasks None entries (comp r) (rev_append cs [])) WNil [] in
    match loopN (wto_step g) (N.of_nat (3 * size + 1)) initial with
    | inl s => wto_reverse_into (wto_partial s) WNil
    | inr w => w
    end.

  Definition check := wto_check_linear.

  Definition heads w := wto_heads_into w [].
  Definition ranks w := wto_rank_rows 1%positive (wto_order_into w []).
End WtoCode.

Module Wto <: WTO.
  Include WtoCode.

  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Lemma check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  Proof. Admitted. (* CONVERT: WtoCheck.check_correct: interval checker requires the new proof. *)

  (** Heads are the structural loop heads in traversal order. *)
  Lemma heads_spec : forall w, heads w = wto_heads w.
  Proof.
    intro w. unfold heads. rewrite (proj1 (wto_into_spec w [])).
    apply app_nil_r.
  Qed.

  (** Ranks number the unique linear order starting at one. *)
  Lemma ranks_spec : forall w, NoDup (wto_order w) -> forall v i,
    nth_error (wto_order w) i = Some v ->
    trie_get v (ranks w) = Some (Pos.of_succ_nat i).
  Proof.
    intros w Hunique v i Hnth. unfold ranks.
    rewrite (proj2 (wto_into_spec w [])), app_nil_r.
    destruct (wto_rank_rows_at (wto_order w) 1%positive Hunique i v Hnth)
      as [p [Hget Hcount]].
    rewrite Hget. f_equal. apply Pos2Nat.inj.
    rewrite SuccNat2Pos.id_succ. cbn [Pos.to_nat] in Hcount. lia.
  Qed.

  (** Vertices outside the linear order have no rank. *)
  Lemma ranks_absent : forall w v,
    ~ In v (wto_order w) -> trie_get v (ranks w) = None.
  Proof.
    intros w v Habsent. unfold ranks.
    rewrite (proj2 (wto_into_spec w [])), app_nil_r.
    now apply wto_rank_rows_absent.
  Qed.

  (** Textually ordered vertices have increasing rank bindings. *)
  Lemma ranks_before : forall w u v,
    NoDup (wto_order w) -> graph_before (wto_order w) u v ->
    exists ru rv, trie_get u (ranks w) = Some ru /\
      trie_get v (ranks w) = Some rv /\ (ru < rv)%positive.
  Proof.
    intros w u v Hunique Hbefore. apply graph_before_indices in Hbefore.
    destruct Hbefore as [i [j [Hij [Hi Hj]]]].
    exists (Pos.of_succ_nat i), (Pos.of_succ_nat j). split.
    - now apply ranks_spec.
    - split; [now apply ranks_spec|].
      apply Pos2Nat.inj_lt. rewrite !SuccNat2Pos.id_succ. lia.
  Qed.

  (** Every vertex in the structural order has a rank binding. *)
  Lemma ranks_present : forall w v,
    NoDup (wto_order w) -> In v (wto_order w) ->
    exists r, trie_get v (ranks w) = Some r.
  Proof.
    intros w v Hunique Hin. apply In_nth_error in Hin. destruct Hin as [i Hi].
    exists (Pos.of_succ_nat i). now apply ranks_spec.
  Qed.

  (** Every reachable cycle contains a structural loop head. *)
  Lemma check_cuts : forall g roots w,
    check g roots w = true -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (heads w).
  Proof.
    intros g roots w Hcheck vs Hcycle Hreachable. rewrite heads_spec.
    exact (wto_cycle_head g roots w (check_sound g roots w Hcheck) vs Hcycle Hreachable).
  Qed.

  (** Edges increase rank unless their target is a backward loop head. *)
  Lemma ranks_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
  Proof.
    intros g roots w u v Hcheck Hedge Hreach.
    destruct (check_sound g roots w Hcheck) as [Hunique [Hcover Hedges]].
    destruct (Hedges u v Hedge Hreach) as [Hbefore|Hencloses].
    - destruct (ranks_before w u v Hunique Hbefore) as [ru [rv [Hu [Hv Hlt]]]].
      exists ru, rv. auto.
    - pose proof (proj1 (wto_encloses_member w v u Hencloses)) as Hhead.
      rewrite <- heads_spec in Hhead.
      destruct (wto_encloses_before w v u Hencloses) as [Heq|Hbefore].
      + subst v. destruct (ranks_present w u Hunique (proj2 (Hcover u) Hreach)) as [r Hr].
        exists r, r. repeat split; auto. right. split; [exact Hhead|apply Pos.le_refl].
      + destruct (ranks_before w v u Hunique Hbefore) as [rv [ru [Hv [Hu Hlt]]]].
        exists ru, rv. repeat split; auto. right. split; [exact Hhead|].
        now apply Pos.lt_le_incl.
  Qed.
End Wto.

Module WtoT <: WTO_ALL.
  Include Wto.
  Definition wto_key_fits := wto_key_fits.
  TimeFun wto_key_fits.
  Definition wto_check_index := wto_check_index.
  TimeFun wto_check_index.
  Definition wto_interval_edge := wto_interval_edge.
  TimeFun wto_interval_edge.
  Definition wto_edges_ok := wto_edges_ok.
  TimeFun wto_edges_ok.
  TimeFun build.
  TimeFun check.
  TimeFun heads.
  TimeFun ranks.
  Definition c_wto : N := 1%N. (* STUB *)

  Lemma T_check_le : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_build_le : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_heads_le : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_ranks_le : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma check_bigO : bigO (fun _ : prepared * list positive * wto => True)
    (fun '(g, roots, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots, w) => T_check g roots w).
  Proof. Admitted. (* STUB *)

  Lemma build_bigO : bigO (fun _ : prepared * list positive => True)
    (fun '(g, roots) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (wto_depth (build g roots) + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots) => T_build g roots).
  Proof. Admitted. (* STUB *)

  Definition wto_member := wto_member.
  TimeFun wto_member.
  Definition wto_unique := wto_unique.
  TimeFun wto_unique.
  Definition wto_annotate := wto_annotate.
  TimeFun wto_annotate.
  Definition wto_positions := wto_positions.
  TimeFun wto_positions.
  Definition wto_edge_b := wto_edge_b.
  TimeFun wto_edge_b.
  Definition wto_rank_rows := wto_rank_rows.
  TimeFun wto_rank_rows.
  Definition wto_heads_into := wto_heads_into.
  TimeFun wto_heads_into.
  Definition wto_order_into := wto_order_into.
  TimeFun wto_order_into.
  Definition wto_scoped := wto_scoped.
  TimeFun wto_scoped.
  Definition wto_components := wto_components.
  TimeFun wto_components.
  Definition wto_entries := wto_entries.
  TimeFun wto_entries.
  Definition wto_preferred := wto_preferred.
  TimeFun wto_preferred.
  Definition wto_select := wto_select.
  TimeFun wto_select.
  Definition wto_reverse_into := wto_reverse_into.
  TimeFun wto_reverse_into.
  Definition wto_expand_tasks := wto_expand_tasks.
  TimeFun wto_expand_tasks.
  Definition wto_step := wto_step.
  TimeFun wto_step.
  Definition search_trace := search_trace.
  TimeFun search_trace.

  Definition k_member : N := 1%N. (* STUB *)
  Definition k_index : N := 1%N. (* STUB *)
  Definition k_check : N := 1%N. (* STUB *)
  Definition k_scope : N := 1%N. (* STUB *)
  Definition k_expand : N := 1%N. (* STUB *)
  Definition k_build : N := 1%N. (* STUB *)
  Definition k_heads : N := 1%N. (* STUB *)
  Definition k_ranks : N := 1%N. (* STUB *)

  Definition live (g : prepared) roots := entered (search_trace (base g) roots).
  Definition checked_index w := wto_positions (wto_annotate [] w).
  Definition index_correct w : Prop :=
    forall u,
      (trie_get u (checked_index w) = None <-> ~ In u (wto_order w)) /\
      forall after stack, trie_get u (checked_index w) = Some (after, stack) ->
        In u (wto_order w) /\
        (forall v, In v after <-> graph_before (wto_order w) u v) /\
        (forall h, In h stack <-> wto_encloses h u w).
  Definition checked g roots w : Prop :=
    (forall v, In v roots -> In v (nodes g)) /\
    (forall v, In v (wto_order w) -> In v (nodes g)) /\
    NoDup (wto_order w) /\
    (forall v, In v (wto_order w) <-> In v (live g roots)) /\
    forall u v, In u (wto_order w) -> edge (base g) u v ->
      wto_edge_b (checked_index w) u v = true.
  Definition source_mass (g : prepared) (vs : list positive) : nat :=
    fold_right (fun v n => 1 + length (succs (base g) v) + n) 0 vs.
  Definition scope_work g vs :=
    (source_mass g vs + 1) *
      (graph_max (graph_width (base g)) (vertex_width vs) + 1).
  Definition task_members (task : wto_task) : list positive :=
    match task with WtoExpand _ _ _ c => c | WtoClose _ => [] end.
  Definition task_mass (g : prepared) task :=
    match task with WtoExpand _ _ _ c => 3 * length c | WtoClose _ => 1 end.
  Definition potential g st :=
    fold_right (fun task n => task_mass g task + n) 0 (wto_tasks st).
  Definition initial g roots :=
    let r := wto_components g roots in
    WtoState (wto_expand_tasks None (wto_entries g roots r) (comp r) (rev (comps r))) WNil [].
  Definition advance g st :=
    match wto_step g st with inl next => next | inr _ => st end.
  Definition inventory (vertices : list positive) (st : wto_state) : Prop :=
    Permutation vertices
      (concat (map task_members (wto_tasks st)) ++ wto_order (wto_partial st) ++
        concat (map wto_order (wto_parents st)) ++
        fold_right (fun task hs =>
          match task with WtoClose h => h :: hs | _ => hs end) [] (wto_tasks st)) /\
    length (wto_parents st) =
      length (filter (fun task => match task with WtoClose _ => true | _ => false end)
        (wto_tasks st)).
  Definition invariant g roots st : Prop :=
    (exists n, Nat.iter n (advance g) (initial g roots) = st) /\
    inventory (concat (comps (wto_components g roots))) st.
  Definition level_mass g level states :=
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then
        match wto_tasks st with
        | WtoExpand _ _ _ c :: _ => source_mass g c + n
        | _ => n
        end
      else n) 0 states.
  Definition scope_charge g states :=
    fold_right (fun st n =>
      match wto_tasks st with
      | WtoExpand _ entries owners c :: _ =>
        match wto_select (wto_preferred owners entries c) c with
        | Some (_, body) => scope_work g body + n
        | None => n
        end
      | _ => n
      end) 0 states.
  Definition execution_cost g states : N :=
    fold_right (fun st n => (T_wto_step g st + n)%N) 0%N states.
  Definition check_work g roots (w : wto) :=
    N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)).

  Fixpoint history_from (g : prepared) (fuel : nat) (st : wto_state) : list wto_state :=
    match wto_step g st with
    | inr _ => [st]
    | inl next =>
      match fuel with
      | O => [st]
      | S remaining => st :: history_from g remaining next
      end
    end.
  Definition history (g : prepared) (roots : list positive) : list wto_state :=
    history_from g (3 * length (concat (comps (wto_components g roots))) + 1)
      (initial g roots).

  Lemma F1_lists :
    (forall v vs, wto_member v vs = true <-> In v vs) /\
    (forall vs, wto_unique vs = true <-> NoDup vs).
  Proof.
    split; [apply wto_member_spec|apply wto_unique_spec].
  Qed.

  Lemma F2_annotation : forall w, NoDup (wto_order w) ->
    map fst (wto_annotate [] w) = wto_order w /\
    forall u stack, In (u, stack) (wto_annotate [] w) ->
      forall h, In h stack <-> wto_encloses h u w.
  Proof. Admitted. (* STUB *)

  Lemma F3_index : forall w, NoDup (wto_order w) -> index_correct w.
  Proof. Admitted. (* STUB *)

  Lemma F4_check : forall g roots w, check g roots w = true <-> checked g roots w.
  Proof. Admitted. (* STUB *)

  Lemma F5_live : forall g roots v, In v (live g roots) <-> reach (base g) roots v.
  Proof. Admitted. (* STUB *)

  Lemma F6_sound : forall g roots w, check g roots w = true -> is_wto g roots w.
  Proof. Admitted. (* STUB *)

  Lemma F7_encloses : forall w h v,
    wto_encloses h v w -> In h (wto_heads w) /\ In h (wto_order w).
  Proof.
    apply wto_encloses_member.
  Qed.

  Lemma F8_cycle : forall g roots w,
    is_wto g roots w -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (wto_heads w).
  Proof.
    apply wto_cycle_head.
  Qed.

  Lemma F9_ranks : forall w,
    ranks w = wto_rank_rows 1%positive (wto_order w) /\
    (forall v, ~ In v (wto_order w) -> trie_get v (ranks w) = None) /\
    (NoDup (wto_order w) -> forall v i,
      nth_error (wto_order w) i = Some v ->
      trie_get v (ranks w) = Some (Pos.of_succ_nat i)).
  Proof.
    intro w. split.
    - unfold ranks. rewrite (proj2 (wto_into_spec w [])), app_nil_r. reflexivity.
    - split; [apply ranks_absent|apply ranks_spec].
  Qed.

  Lemma F10_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
  Proof.
    apply ranks_forward.
  Qed.

  Lemma F11_select : forall preferred c h body,
    wto_select preferred c = Some (h, body) -> Permutation c (h :: body).
  Proof.
    apply wto_select_spec.
  Qed.

  Lemma F12_scope : forall g vs,
    nodes (wto_scoped g (Some vs)) = vs /\
    forall v, In v vs -> succs (base (wto_scoped g (Some vs))) v =
      filter (fun u => wto_member u vs) (succs (base g) v).
  Proof.
    apply wto_scoped_spec.
  Qed.

  Lemma F13_partition : forall g body,
    NoDup body ->
    let r := wto_components (wto_scoped g (Some body)) (rev body) in
    Permutation (concat (comps r)) body /\
    fold_right (fun c n => source_mass g c + n) 0 (comps r) = source_mass g body.
  Proof. Admitted. (* STUB *)

  Lemma F14_initial : forall g roots,
    invariant g roots (initial g roots) /\
    potential g (initial g roots) = 3 * length (concat (comps (wto_components g roots))).
  Proof. Admitted. (* STUB *)

  Lemma F15_step : forall g roots st next,
    invariant g roots st -> wto_step g st = inl next ->
    invariant g roots next /\ potential g next < potential g st.
  Proof. Admitted. (* STUB *)

  Lemma F16_done : forall g roots,
    exists w, loopN (wto_step g)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots) = inr w.
  Proof. Admitted. (* STUB *)

  Lemma F17_history : forall g roots,
    exists terminal prefix, history g roots = prefix ++ [terminal] /\
      (match prefix with [] => terminal | first :: _ => first end) = initial g roots /\
      Forall2 (fun before after => wto_step g before = inl after)
        prefix (tl (history g roots)) /\
      wto_step g terminal = inr (build g roots).
  Proof. Admitted. (* STUB *)

  Lemma F18_level_mass : forall g roots level,
    level_mass g level (history g roots) <=
      source_mass g (concat (comps (wto_components g roots))).
  Proof. Admitted. (* STUB *)

  Lemma F19_depth : forall g roots st within entries owners c tasks,
    In st (history g roots) ->
    wto_tasks st = WtoExpand within entries owners c :: tasks ->
    length (wto_parents st) <= wto_depth (build g roots).
  Proof. Admitted. (* STUB *)

  Lemma T1_member : forall v vs,
    (T_wto_member v vs <= k_member * N.of_nat (length vs + 1) *
      N.of_nat (graph_max (Pos.size_nat v) (vertex_width vs) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_scope : forall g vs,
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.
  Proof. Admitted. (* STUB *)

  (** The index loop checks each key's width and listing before it reads a trie. *)
  Lemma T4a_index : forall g w,
    (T_wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] <=
    k_index * N.of_nat (graph_n (base g) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Local Opaque loopN.

  (** An index result lists distinct listed vertices. *)
  Lemma F4a_index : forall g w ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
    NoDup vs /\ (forall v, In v vs -> In v (nodes g)).
  Proof.
    intros g w ranks intervals vs Hindex.
    destruct (wto_check_index_seen (check_fuel g) (graph_width (base g)) (listed_of g)
      w ranks intervals vs Hindex) as [Hunique Hlisted].
    split; [exact Hunique|]. intros v Hin.
    apply (proj1 (scc_listed_lookup (nodes g) v)). now apply Hlisted.
  Qed.

  Local Transparent loopN.

  (** The edge scan is the final conjunct of the checker. *)
  Lemma F4b_edges : forall b ranks intervals vs,
    wto_edges_ok b ranks intervals vs =
      forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs b u)) vs.
  Proof.
    reflexivity.
  Qed.

  (** The edge scan reads the rows of distinct listed vertices once each. *)
  Lemma T4b_edges : forall g w ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
    (T_wto_edges_ok (base g) ranks intervals vs <=
     k_check * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
       N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_check_public : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_expand : forall g within entries owners c tasks partial parents h body,
    wto_select (wto_preferred owners entries c) c = Some (h, body) -> body <> [] ->
    (T_wto_step g (WtoState (WtoExpand within entries owners c :: tasks) partial parents) <=
      k_expand * (T_wto_preferred owners entries c +
        T_wto_select (wto_preferred owners entries c) c + T_wto_scoped g (Some body) +
        T_wto_components (wto_scoped g (Some body)) (rev body) +
        T_wto_entries (wto_scoped g (Some body)) (rev body)
          (wto_components (wto_scoped g (Some body)) (rev body)) +
        N.of_nat (length body) + N.of_nat (length c) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_build_public : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T8_heads_source : forall w,
    (T_heads w <= k_heads * (T_wto_heads_into w [] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T9_heads_public : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T10_ranks_source : forall w,
    (T_ranks w <= k_ranks *
      (T_wto_order_into w [] + T_wto_rank_rows 1%positive (wto_order w) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T11_ranks_public : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Accumulating traversals compute the structural lists. *)
  Lemma F20_into : forall w acc,
      wto_heads_into w acc = wto_heads w ++ acc /\
      wto_order_into w acc = wto_order w ++ acc.
  Proof.
    apply wto_into_spec.
  Qed.

  (** An accumulating traversal visits each constructor once. *)
  Lemma T8b_heads_into : forall w acc,
      (T_wto_heads_into w acc <= k_heads * N.of_nat (2 * length (wto_order w) + 2))%N.
  Proof. Admitted. (* STUB *)

  (** Flattening by accumulation visits each constructor once. *)
  Lemma T10b_order_into : forall w acc,
      (T_wto_order_into w acc <= k_ranks * N.of_nat (2 * length (wto_order w) + 2))%N.
  Proof. Admitted. (* STUB *)

  (** Rank insertion pays each key and an amortised binary successor. *)
  Lemma T10c_rank_rows : forall vs,
      (T_wto_rank_rows 1%positive vs <= k_ranks * N.of_nat (length vs + 1) *
        N.of_nat (vertex_width vs + Nat.log2 (length vs) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Scoped components and entries read the materialized rows once. *)
  Lemma T12_scoped : forall g vs, NoDup vs -> (forall v, In v vs -> In v (nodes g)) ->
      (T_wto_components (wto_scoped g (Some vs)) (rev vs) +
        T_wto_entries (wto_scoped g (Some vs)) (rev vs)
          (wto_components (wto_scoped g (Some vs)) (rev vs)) <=
      k_scope * N.of_nat (scope_work g vs))%N.
  Proof. Admitted. (* STUB *)

  (** Initial components and entries pay the listed graph and the supplied roots. *)
  Lemma T13_initial : forall g roots,
      (T_wto_components g roots + T_wto_entries g roots (wto_components g roots) <=
        k_build * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
        N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Preference and selection scan an actual component once. *)
  Lemma T14_select : forall g roots st within entries owners c tasks,
      In st (history g roots) -> wto_tasks st = WtoExpand within entries owners c :: tasks ->
      (T_wto_preferred owners entries c + T_wto_select (wto_preferred owners entries c) c <=
        k_expand * N.of_nat (scope_work g c))%N.
  Proof. Admitted. (* STUB *)

  (** Close, terminal and singleton steps pay the reversed partial order and one row. *)
  Lemma T15_short_step : forall g roots st,
      In st (history g roots) ->
      (forall within entries owners c tasks h body,
        wto_tasks st = WtoExpand within entries owners c :: tasks ->
        wto_select (wto_preferred owners entries c) c = Some (h, body) -> body = []) ->
      (T_wto_step g st <= k_expand *
        N.of_nat (length (wto_order (wto_partial st)) +
          source_mass g (concat (map task_members (firstn 1 (wto_tasks st)))) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Building pays the initial phases, the task list and each recorded step once. *)
  Lemma T16_build : forall g roots,
    (T_build g roots <= k_build * (T_wto_components g roots +
      T_wto_entries g roots (wto_components g roots) +
      N.of_nat (length (concat (comps (wto_components g roots)))) +
      execution_cost g (history g roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Close and terminal steps at one depth reverse disjoint partial outputs. *)
  Lemma F21_partial_mass : forall g roots level,
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then
        match wto_tasks st with
        | [] | WtoClose _ :: _ => length (wto_order (wto_partial st)) + n
        | _ => n
        end
      else n) 0 (history g roots) <=
    length (concat (comps (wto_components g roots))).
  Proof. Admitted. (* STUB *)

End WtoT.
