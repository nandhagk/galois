(** * Weak topological order production and checking

    The producer recursively removes an entry header from each cyclic component.
    For example, a singleton self edge produces an empty loop body.
    Builds on: Tarjan search, first-order graph data and the WTO signature. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Sorting.Permutation
  Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig Digraph SearchSig Search SccSig Scc WtoSig.
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

(** Membership compares each candidate at most once using the sought key's width. *)
Lemma wto_member_clock : forall v vs,
  (T_wto_member v vs <=
    (N.of_nat (Pos.size_nat v) + 2) * N.of_nat (length vs) + 2)%N.
Proof.
  intros v vs. pose proof (List.T_existsb_le (Pos.eqb v) (fun u => Pos.T_eqb v u)
    (N.of_nat (Pos.size_nat v)) vs (Pos.T_eqb_le v)) as Hscan.
  time_unfold @T_wto_member. time_cbn. lia.
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

Definition wto_components_spec g roots :=
  let ready := scc_graph g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev_append (tarjan_emitted s) []).

Definition wto_components g roots :=
  let ready := scc_graph_counted g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev_append (tarjan_emitted s) []).
TimeFun wto_components.

(** Counting while rebuilding preserves component order and owner assignments. *)
Lemma wto_components_agrees g roots :
  wto_components g roots = wto_components_spec g roots.
Proof.
  unfold wto_components, wto_components_spec. now rewrite scc_graph_counted_agrees.
Qed.

(** A scoped search refreshes only its count caches, preserving its materialized rows. *)
Definition wto_recount (g : prepared) : prepared :=
  let b := base g in
  Prepared b Empty (N.of_nat (graph_n b)) (N.of_nat (graph_e b)).
TimeFun wto_recount.

(** Rebuilding a materialized scope is equal to refreshing just its two count caches. *)
Lemma wto_scoped_recount g vs :
  scc_graph (wto_scoped g (Some vs)) = wto_recount (wto_scoped g (Some vs)).
Proof.
  exact (scc_graph_filtered (base g) vs (nv g) (ne g)).
Qed.

(** A scope has already rebuilt all rows and removed every external successor. *)
Lemma wto_scoped_graph g vs :
  base (scc_graph (wto_scoped g (Some vs))) = base (wto_scoped g (Some vs)).
Proof.
  exact (f_equal base (wto_scoped_recount g vs)).
Qed.

(** Refreshing scoped counts costs no more than the former graph rebuild. *)
Lemma wto_recount_clock g vs :
  (T_wto_recount (wto_scoped g (Some vs)) <=
    T_scc_graph (wto_scoped g (Some vs)))%N.
Proof.
  pose proof (scc_graph_cache_clock (wto_scoped g (Some vs))) as Hcache.
  rewrite wto_scoped_graph in Hcache.
  time_unfold @T_wto_recount. unfold T_base. lia.
Qed.

(** The count-only scoped shortcut also fits the counted preprocessing clock. *)
Lemma wto_recount_counted_clock g vs :
  (T_wto_recount (wto_scoped g (Some vs)) <=
    T_scc_graph_counted (wto_scoped g (Some vs)))%N.
Proof.
  pose proof (scc_graph_counted_cache_clock (wto_scoped g (Some vs))
    (wto_scoped_graph g vs)) as Hcache.
  time_unfold @T_wto_recount. unfold T_base. lia.
Qed.

(** Component production on a materialized scope skips rebuilding its row tries. *)
Definition wto_components_ready g roots :=
  let ready := wto_recount g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev_append (tarjan_emitted s) []).
TimeFun wto_components_ready.

(** The scoped component shortcut has exactly the same component order and owner table. *)
Lemma wto_components_ready_agrees g vs roots :
  wto_components_ready (wto_scoped g (Some vs)) roots =
    wto_components (wto_scoped g (Some vs)) roots.
Proof.
  unfold wto_components_ready, wto_components.
  now rewrite scc_graph_counted_agrees, wto_scoped_recount.
Qed.

(** The component shortcut fits the public component clock on every materialized scope. *)
Lemma wto_components_ready_clock g vs roots :
  (T_wto_components_ready (wto_scoped g (Some vs)) roots <=
    T_wto_components (wto_scoped g (Some vs)) roots)%N.
Proof.
  pose proof (wto_recount_counted_clock g vs) as Hcache.
  time_unfold @T_wto_components_ready. time_unfold @T_wto_components.
  rewrite scc_graph_counted_agrees, wto_scoped_recount. lia.
Qed.

(** Reversing the component list preserves its multiset of vertices. *)
Lemma wto_components_reverse : forall (cs : list (list positive)),
  Permutation (concat cs) (concat (rev cs)).
Proof.
  intro cs. change (Permutation (flat_map (fun c : list positive => c) cs)
    (flat_map (fun c : list positive => c) (rev cs))).
  apply Permutation_flat_map. apply Permutation_rev.
Qed.

(** The rebuilt graph has a row exactly at its listed source vertices. *)
Lemma wto_scc_root_test : forall g v,
  (match trie_get v (succ (base (scc_graph g))) with Some _ => true | None => false end) =
    wto_member v (nodes g).
Proof.
  intros g v. unfold scc_graph. cbn [base succ].
  rewrite scc_rows_lookup, PTrie.get_empty. unfold wto_member.
  destruct (existsb (Pos.eqb v) (nodes g)); reflexivity.
Qed.

Local Opaque loopN.

(** Every component supplied to the builder contains a vertex, for any graph and roots. *)
Lemma wto_components_nonempty : forall g roots,
  Forall (fun c => c <> []) (comps (wto_components g roots)).
Proof.
  intros g roots. unfold wto_components. cbn [comps].
  rewrite rev_append_rev, app_nil_r. apply Forall_rev. apply tarjan_emitted_nonempty.
Qed.

(** A component collection never repeats an entered vertex, even on malformed raw graphs. *)
Lemma wto_components_unique : forall g roots,
  NoDup (concat (comps (wto_components g roots))).
Proof.
  intros g roots. unfold wto_components. cbn [comps].
  rewrite rev_append_rev, app_nil_r.
  apply (Permutation_NoDup (wto_components_reverse _)).
  apply tarjan_emitted_unique. apply prepared_search_unique_raw.
Qed.

(** The component search visits only sources listed by the original graph. *)
Lemma wto_component_trace_listed : forall g roots v,
  In v (entered (prepared_search_trace (scc_graph g)
    (filter (fun r => match trie_get r (succ (base (scc_graph g))) with
      Some _ => true | None => false end) roots))) -> In v (nodes g).
Proof.
  intros g roots v Hentered. set (ready := scc_graph g) in *.
  set (listed_roots := filter (fun r =>
    match trie_get r (succ (base ready)) with Some _ => true | None => false end) roots) in *.
  assert (Hroots : forall r, In r listed_roots -> In r (nodes g)).
  { intros r Hr. unfold listed_roots in Hr. apply filter_In in Hr.
    destruct Hr as [Hr Hlisted]. unfold ready in Hlisted.
    rewrite wto_scc_root_test in Hlisted. now apply wto_member_spec in Hlisted. }
  assert (Hclosed : forall u v,
    In u (nodes ready) -> edge (base ready) u v -> In v (nodes ready)).
  { intros u z Hu Hedge. unfold ready. rewrite scc_graph_nodes.
    now apply (scc_graph_closed g u). }
  assert (Hroots_ready : forall r, In r listed_roots -> In r (nodes ready)).
  { intros r Hr. unfold ready. rewrite scc_graph_nodes. now apply Hroots. }
  apply (proj1 (prepared_search_reach_closed ready listed_roots (scc_graph_counts g)
    Hclosed Hroots_ready v)) in Hentered.
  destruct Hentered as [r [vertices [Hroot Hpath]]].
  pose proof (Hroots r Hroot) as Hlisted. clear Hroot. revert Hlisted.
  induction Hpath as [v|u v vertices z Hedge Hpath IH]; intro Hlisted.
  - exact Hlisted.
  - apply IH. now apply (scc_graph_closed g u).
Qed.

(** Every emitted component vertex belongs to the listed source domain. *)
Lemma wto_components_listed : forall g roots v,
  In v (concat (comps (wto_components g roots))) -> In v (nodes g).
Proof.
  intros g roots v Hin. rewrite wto_components_agrees in Hin.
  set (ready := scc_graph g).
  set (listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots).
  change (In v (concat (rev_append
    (tarjan_emitted (TarjanSearch.dfs ready listed_roots tarjan_initial)) []))) in Hin.
  rewrite rev_append_rev, app_nil_r in Hin.
  apply (wto_component_trace_listed g roots v).
  change (In v (entered (prepared_search_trace ready listed_roots))).
  eapply Permutation_in.
  - apply tarjan_bag_inventory.
  - unfold tarjan_bag. apply in_or_app. right.
    change (In v (concat (tarjan_emitted
      (TarjanSearch.dfs ready listed_roots tarjan_initial)))).
    exact (Permutation_in v (Permutation_sym (wto_components_reverse
      (tarjan_emitted (TarjanSearch.dfs ready listed_roots tarjan_initial)))) Hin).
Qed.

(** Every listed key fits the raw graph's source-width envelope. *)
Lemma wto_listed_width : forall g v,
  In v (nodes g) -> Pos.size_nat v <= graph_width (base g).
Proof.
  intros [[vs rows] predecessors n e] v Hin. change (In v vs) in Hin.
  cbn [base graph_width]. rewrite search_graph_max.
  eapply Nat.le_trans; [exact (search_vertex_width_member vs v Hin)|apply Nat.le_max_l].
Qed.

(** Component identifiers fit the width of any envelope for the listed source keys. *)
Lemma wto_components_owner_bound : forall g roots width,
  Forall (fun v => Pos.size_nat v <= width) (nodes g) -> forall v i,
  trie_get v (comp (wto_components g roots)) = Some i -> Pos.size_nat i <= width + 1.
Proof.
  intros g roots width Hwidth v i Howner. rewrite wto_components_agrees in Howner.
  unfold wto_components_spec in Howner. cbn [comp] in Howner.
  set (es := prepared_search_trace (scc_graph g)
    (filter (fun r => match trie_get r (succ (base (scc_graph g))) with
      Some _ => true | None => false end) roots)).
  change (trie_get v (tarjan_owners (fold_events TarjanVisitor.enter
    TarjanVisitor.leave TarjanVisitor.edge es tarjan_initial)) = Some i) in Howner.
  apply (tarjan_owner_width width es v i).
  - apply prepared_search_unique_raw.
  - apply Forall_forall. intros u Hu. rewrite Forall_forall in Hwidth.
    apply Hwidth. exact (wto_component_trace_listed g roots u Hu).
  - exact Howner.
Qed.

(** Every component identifier needs at most one bit beyond a listed graph key. *)
Lemma wto_components_owner_width : forall g roots v i,
  trie_get v (comp (wto_components g roots)) = Some i ->
    Pos.size_nat i <= graph_width (base g) + 1.
Proof.
  intros g roots v i Howner. eapply (wto_components_owner_bound g roots).
  - apply Forall_forall. intros u Hu. now apply wto_listed_width.
  - exact Howner.
Qed.

(** Component production cannot emit more vertices than its listed input domain. *)
Lemma wto_components_size : forall g roots,
  length (concat (comps (wto_components g roots))) <= length (nodes g).
Proof.
  intros g roots. rewrite wto_components_agrees. set (ready := scc_graph g).
  set (listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots).
  change (length (concat (rev_append
    (tarjan_emitted (TarjanSearch.dfs ready listed_roots tarjan_initial)) [])) <=
      length (nodes g)).
  rewrite rev_append_rev, app_nil_r.
  rewrite <- (Permutation_length (wto_components_reverse _)).
  eapply Nat.le_trans; [apply tarjan_emitted_length|].
  apply NoDup_incl_length; [apply prepared_search_unique_raw|].
  assert (Hroots : forall r, In r listed_roots -> In r (nodes g)).
  { intros r Hin. unfold listed_roots in Hin. apply filter_In in Hin.
    destruct Hin as [Hin Hlisted]. unfold ready in Hlisted.
    rewrite wto_scc_root_test in Hlisted. now apply wto_member_spec in Hlisted. }
  assert (Hclosed : forall u v,
    In u (nodes ready) -> edge (base ready) u v -> In v (nodes ready)).
  { intros u v Hu Hedge. unfold ready. rewrite scc_graph_nodes.
    now apply (scc_graph_closed g u). }
  assert (Hroots_ready : forall r, In r listed_roots -> In r (nodes ready)).
  { intros r Hin. unfold ready. rewrite scc_graph_nodes. now apply Hroots. }
  intros v Hin.
  apply (proj1 (prepared_search_reach_closed ready listed_roots (scc_graph_counts g)
    Hclosed Hroots_ready v)) in Hin.
  destruct Hin as [r [vertices [Hroot Hpath]]].
  pose proof (Hroots r Hroot) as Hlisted. clear Hroot. revert Hlisted.
  induction Hpath as [v|u v vertices z Hedge Hpath IH]; intro Hlisted.
  - exact Hlisted.
  - apply IH. now apply (scc_graph_closed g u).
Qed.

Local Transparent loopN.

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

(** Selection scans each candidate with a comparison bounded by that candidate's width. *)
Lemma wto_select_clock : forall preferred c width,
  Forall (fun v => Pos.size_nat v <= width) c ->
  (T_wto_select preferred c <=
    2 * N.of_nat (length c + 1) * N.of_nat (width + 1))%N.
Proof.
  intros preferred c. induction c as [|v rest IH]; intros width Hwidth.
  - time_step.
  - inversion Hwidth as [|? ? Hvertex Hrest]; subst. specialize (IH width Hrest).
    destruct preferred as [h|].
    + pose proof (Pos.T_eqb_le v h) as Hequal. time_step.
    + time_step.
Qed.

(** Preference reads a graph key and, when present, a bounded component identifier. *)
Lemma wto_preferred_clock : forall owners entries c width,
  Forall (fun v => Pos.size_nat v <= width) c ->
  (forall v i, trie_get v owners = Some i -> Pos.size_nat i <= width + 1) ->
  (T_wto_preferred owners entries c <= 8 * N.of_nat (width + 1))%N.
Proof.
  intros owners entries [|v rest] width Hwidth Howners.
  - time_step.
  - inversion Hwidth as [|? ? Hvertex Hrest]; subst.
    pose proof (PTrieT.T_trie_get_le positive v owners) as Hget.
    time_unfold @T_wto_preferred. cbn beta iota zeta.
    destruct (trie_get v owners) as [i|] eqn:Howner.
    + pose proof (Howners v i Howner) as Hidentifier.
      pose proof (PTrieT.T_trie_get_le positive i entries) as Hentry.
      time_simpl. rewrite !Nat2N.inj_add in *. nia.
    + time_simpl. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Preference and selection together cost a constant multiple of component key occurrences. *)
Lemma wto_selection_clock : forall owners entries c width,
  Forall (fun v => Pos.size_nat v <= width) c ->
  (forall v i, trie_get v owners = Some i -> Pos.size_nat i <= width + 1) ->
  (T_wto_preferred owners entries c +
    T_wto_select (wto_preferred owners entries c) c <=
    16 * N.of_nat (length c + 1) * N.of_nat (width + 1))%N.
Proof.
  intros owners entries c width Hwidth Howners.
  pose proof (wto_preferred_clock owners entries c width Hwidth Howners) as Hpreferred.
  pose proof (wto_select_clock (wto_preferred owners entries c) c width Hwidth) as Hselect.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Fixpoint wto_reverse_into (w tail : wto) : wto :=
  match w with
  | WNil => tail
  | WVertex v rest => wto_reverse_into rest (WVertex v tail)
  | WLoop h body rest => wto_reverse_into rest (WLoop h body tail)
  end.
TimeFun wto_reverse_into.

(** Reversing sibling order visits no more constructors than the flattened vertex order. *)
Lemma wto_reverse_clock : forall w tail,
  (T_wto_reverse_into w tail <= 2 * N.of_nat (length (wto_order w)) + 1)%N.
Proof.
  intro w. induction w as [|v rest IH|h body IHbody rest IHrest]; intro tail.
  - time_step.
  - pose proof (IH (WVertex v tail)) as Hrest.
    time_unfold @T_wto_reverse_into. time_simpl. cbn [wto_order length].
    rewrite !Nat2N.inj_succ. nia.
  - pose proof (IHrest (WLoop h body tail)) as Hrest.
    time_unfold @T_wto_reverse_into. time_simpl. cbn [wto_order length].
    rewrite length_app, !Nat2N.inj_succ, !Nat2N.inj_add. nia.
Qed.

Definition wto_expand_tasks within entries owners cs :=
  map (fun c => WtoExpand within entries owners c) cs.
TimeFun wto_expand_tasks.

(** Reversing a list pays one call per cons and its empty stopping call. *)
Lemma wto_rev_append_clock : forall A (xs ys : list A),
  List.T_rev_append xs ys = N.of_nat (length xs + 1).
Proof.
  intros A xs. induction xs as [|x rest IH]; intro ys;
    time_unfold @List.T_rev_append; time_cbn; cbn [length]; rewrite ?IH; lia.
Qed.

Local Opaque loopN.

(** Component production already pays for traversing its returned component list. *)
Lemma wto_components_output_clock : forall g roots,
  (N.of_nat (length (comps (wto_components g roots))) <= T_wto_components g roots)%N.
Proof.
  intros g roots. unfold wto_components at 1. cbn [comps].
  rewrite rev_append_rev, app_nil_r, length_rev.
  time_unfold @T_wto_components. rewrite wto_rev_append_clock. lia.
Qed.

Local Transparent loopN.

(** Expansion-task construction traverses the outer component list once. *)
Lemma wto_expand_tasks_clock : forall within entries owners cs,
  (T_wto_expand_tasks within entries owners cs <= 2 * N.of_nat (length cs) + 2)%N.
Proof.
  intros within entries owners cs.
  pose proof (ListDef.T_map_le (fun c => WtoExpand within entries owners c)
    (fun _ => 1%N) 1%N cs ltac:(intro c; reflexivity)) as Hmap.
  time_unfold @T_wto_expand_tasks. time_cbn. lia.
Qed.

(** The former expansion step remains the behavioral specification. *)
Definition wto_step_spec (g : prepared) (s : wto_state) : wto_state + wto :=
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
      let r := wto_components_ready scoped roots in
      let entries' := wto_entries scoped roots r in
      inl (WtoState
        (wto_expand_tasks child entries' (comp r) (rev_append (comps r) []) ++
          WtoClose h :: tasks)
        WNil (partial :: parents))
    end
  end.
TimeFun wto_step.

(** The optimized transition preserves the complete former builder state. *)
Lemma wto_step_agrees g st : wto_step g st = wto_step_spec g st.
Proof.
  destruct st as [tasks partial parents].
  destruct tasks as [|task tasks]; [reflexivity|].
  destruct task as [within entries owners c|h]; [|reflexivity].
  cbn [wto_step wto_step_spec].
  destruct (wto_select (wto_preferred owners entries c) c) as [[h body]|];
    [destruct body as [|first body]|]; try reflexivity.
  now rewrite wto_components_ready_agrees.
Qed.

(** A nontrivial expansion pays its scoped phases and their already charged output lists. *)
Lemma wto_expand_step_clock : forall g within entries owners c tasks partial parents h body,
  wto_select (wto_preferred owners entries c) c = Some (h, body) -> body <> [] ->
  (T_wto_step g (WtoState (WtoExpand within entries owners c :: tasks) partial parents) <=
    32 * (T_wto_preferred owners entries c +
      T_wto_select (wto_preferred owners entries c) c + T_wto_scoped g (Some body) +
      T_wto_components (wto_scoped g (Some body)) (rev body) +
      T_wto_entries (wto_scoped g (Some body)) (rev body)
        (wto_components (wto_scoped g (Some body)) (rev body)) +
      N.of_nat (length body) + N.of_nat (length c) + 1))%N.
Proof.
  intros g within entries owners c tasks partial parents h [|first body] Hselect Hnonempty;
    [contradiction|].
  set (members := first :: body).
  set (scoped := wto_scoped g (Some members)).
  set (r := wto_components scoped (rev members)).
  set (entries' := wto_entries scoped (rev members) r).
  pose proof (wto_components_ready_clock g members (rev members)) as Hready.
  fold scoped in Hready.
  pose proof (wto_components_output_clock scoped (rev members)) as Houtput.
  pose proof (List.T_rev_append_le members []) as Hroots.
  pose proof (List.T_rev_append_le (comps r) []) as Hreverse.
  pose proof (wto_expand_tasks_clock (Some members) entries' (comp r) (rev (comps r)))
    as Htasks.
  pose proof (Datatypes.T_app_le
    (wto_expand_tasks (Some members) entries' (comp r) (rev (comps r)))
    (WtoClose h :: tasks)) as Happ.
  assert (Hlength :
    length (wto_expand_tasks (Some members) entries' (comp r) (rev (comps r))) =
      length (comps r)).
  { unfold wto_expand_tasks. rewrite length_map, length_rev. reflexivity. }
  rewrite Hlength in Happ. rewrite length_rev in Htasks. fold r in Houtput.
  time_unfold @T_wto_step. rewrite Hselect. cbn beta iota zeta.
  rewrite !rev_append_rev, !app_nil_r, wto_components_ready_agrees.
  fold members scoped r entries'.
  time_simpl. nia.
Qed.

Local Opaque loopN wto_components.

(** Pending expansions always represent nonempty components. *)
Definition wto_expansions_nonempty (tasks : list wto_task) : Prop :=
  Forall (fun task => match task with
    | WtoExpand _ _ _ c => c <> []
    | WtoClose _ => True
    end) tasks.

(** Nonempty components produce only nonempty expansion tasks. *)
Lemma wto_expand_nonempty : forall within entries owners cs,
  Forall (fun c => c <> []) cs ->
  wto_expansions_nonempty (wto_expand_tasks within entries owners cs).
Proof.
  intros within entries owners cs Hcomponents.
  unfold wto_expansions_nonempty, wto_expand_tasks.
  induction Hcomponents; cbn [map]; constructor; assumption.
Qed.

(** Every continuing builder transition preserves nonempty pending components. *)
Lemma wto_step_nonempty : forall g st next,
  wto_expansions_nonempty (wto_tasks st) -> wto_step g st = inl next ->
  wto_expansions_nonempty (wto_tasks next).
Proof.
  intros g [tasks partial parents] next Htasks Hstep.
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Htasks as [|task' tasks' Hhead Htail]; subst task' tasks'.
  destruct task as [within entries owners c|h].
  - rewrite wto_step_agrees in Hstep. cbn [wto_step_spec] in Hstep.
    destruct (wto_select (wto_preferred owners entries c) c) as [[h body]|].
    + destruct body as [|first body].
      * inversion Hstep; subst next. exact Htail.
      * inversion Hstep; subst next. cbn [wto_tasks].
        unfold wto_expansions_nonempty. apply Forall_app. split.
        -- apply wto_expand_nonempty.
           rewrite rev_append_rev, app_nil_r. apply Forall_rev.
           apply wto_components_nonempty.
        -- constructor; [exact I|exact Htail].
    + inversion Hstep; subst next. exact Htail.
  - destruct parents as [|parent parents]; inversion Hstep; subst next; exact Htail.
Qed.

(** Selection can fail only for an empty component. *)
Lemma wto_select_empty : forall preferred c,
  wto_select preferred c = None -> c = [].
Proof.
  intros preferred [|v rest] Hselect; [reflexivity|].
  cbn [wto_select] in Hselect.
  destruct (match preferred with None => false | Some h => Pos.eqb v h end);
    [discriminate|].
  destruct (wto_select preferred rest) as [[h body]|]; discriminate.
Qed.

(** Pending components reserve three transitions per vertex and one per close task. *)
Definition wto_pending_credit (tasks : list wto_task) : nat :=
  fold_right (fun task n =>
    (match task with WtoExpand _ _ _ c => 3 * length c | WtoClose _ => 1 end) + n)
    0 tasks.

(** Appending task lists adds their pending termination credit. *)
Lemma wto_credit_app : forall first rest,
  wto_pending_credit (first ++ rest) = wto_pending_credit first + wto_pending_credit rest.
Proof.
  intros first rest. unfold wto_pending_credit.
  induction first as [|task first IH]; cbn [app fold_right]; [reflexivity|].
  rewrite IH. lia.
Qed.

(** A component expansion list has exactly three credits per component vertex. *)
Lemma wto_expand_credit : forall within entries owners cs,
  wto_pending_credit (wto_expand_tasks within entries owners cs) = 3 * length (concat cs).
Proof.
  intros within entries owners cs. unfold wto_pending_credit, wto_expand_tasks.
  induction cs as [|c rest IH]; cbn [map fold_right concat]; [reflexivity|].
  rewrite IH, length_app. lia.
Qed.

(** Every continuing transition spends positive credit when pending components are nonempty. *)
Lemma wto_step_credit : forall g st next,
  wto_expansions_nonempty (wto_tasks st) -> wto_step g st = inl next ->
  wto_pending_credit (wto_tasks next) < wto_pending_credit (wto_tasks st).
Proof.
  intros g [tasks partial parents] next Htasks Hstep.
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Htasks as [|task' tasks' Hhead Htail]; subst task' tasks'.
  destruct task as [within entries owners c|h].
  - rewrite wto_step_agrees in Hstep. cbn [wto_step_spec] in Hstep.
    destruct (wto_select (wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
    + pose proof (Permutation_length (wto_select_spec _ _ _ _ Hselect)) as Hlength.
      cbn [length] in Hlength. destruct body as [|first body].
      * inversion Hstep; subst next. cbn [wto_tasks wto_pending_credit fold_right].
        cbn [length] in Hlength. lia.
      * inversion Hstep; subst next. cbn [wto_tasks].
        rewrite wto_credit_app, wto_expand_credit.
        rewrite rev_append_rev, app_nil_r.
        rewrite <- (Permutation_length (wto_components_reverse _)).
        pose proof (wto_components_size (wto_scoped g (Some (first :: body)))
          (rev_append (first :: body) [])) as Hsize.
        change (length (concat (comps (wto_components
          (wto_scoped g (Some (first :: body))) (rev_append (first :: body) [])))) <=
          length (first :: body)) in Hsize.
        change (3 * length (concat (comps (wto_components
          (wto_scoped g (Some (first :: body))) (rev_append (first :: body) [])))) +
          (1 + wto_pending_credit tasks) < 3 * length c + wto_pending_credit tasks).
        cbn [length] in Hsize, Hlength. lia.
    + apply wto_select_empty in Hselect. subst c. contradiction.
  - destruct parents as [|parent parents]; inversion Hstep; subst next;
      cbn [wto_tasks wto_pending_credit fold_right]; lia.
Qed.

(** Credit bounds termination independently of the stronger inventory invariant. *)
Lemma wto_fuel_complete : forall g fuel st,
  wto_expansions_nonempty (wto_tasks st) ->
  wto_pending_credit (wto_tasks st) < fuel ->
  exists w, loop_fuel (wto_step g) fuel st = inr w.
Proof.
  intros g fuel. induction fuel as [|fuel IH]; intros st Htasks Hcredit; [lia|].
  cbn [loop_fuel]. destruct (wto_step g st) as [next|w] eqn:Hstep.
  - apply IH.
    + eapply wto_step_nonempty; eassumption.
    + pose proof (wto_step_credit g st next Htasks Hstep). lia.
  - now exists w.
Qed.

Local Transparent loopN wto_components.

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

(** A row shares its source rank and reads an interval only for a non-forward edge. *)
Definition wto_interval_edge_from (ranks : ptrie N) (intervals : ptrie (N * N))
    (ru : N) (v : positive) : bool :=
  match trie_get v ranks with
  | Some rv =>
    if N.ltb ru rv then true else
      match trie_get v intervals with
      | Some (lo, hi) => N.leb lo ru && N.ltb ru hi
      | None => false
      end
  | None => false
  end.
TimeFun wto_interval_edge_from.

(** An unranked sink has no edge to reject; a nonempty unranked row does. *)
Definition wto_edges_row (ranks : ptrie N) (intervals : ptrie (N * N))
    (b : digraph) (u : positive) : bool :=
  match trie_get u ranks with
  | Some ru => forallb (wto_interval_edge_from ranks intervals ru) (succs b u)
  | None => match succs b u with [] => true | _ => false end
  end.
TimeFun wto_edges_row.

(** Reading the source rank once preserves every row's old Boolean result. *)
Lemma wto_edges_row_agrees ranks intervals b u :
  wto_edges_row ranks intervals b u =
    forallb (wto_interval_edge ranks intervals u) (succs b u).
Proof.
  unfold wto_edges_row.
  destruct (trie_get u ranks) as [ru|] eqn:Hrank.
  - induction (succs b u) as [|v rest IH]; [reflexivity|].
    cbn [forallb]. rewrite IH. unfold wto_interval_edge_from, wto_interval_edge.
    rewrite Hrank. destruct (trie_get v ranks); reflexivity.
  - destruct (succs b u) as [|v rest]; [reflexivity|].
    cbn [forallb]. unfold wto_interval_edge. now rewrite Hrank.
Qed.

(** The original edge scan remains the functional specification. *)
Definition wto_edges_ok_spec (b : digraph) (ranks : ptrie N) (intervals : ptrie (N * N))
    (vs : list positive) : bool :=
  forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs b u)) vs.

(** The checker's final scan shares a source-rank lookup across each row. *)
Definition wto_edges_ok (b : digraph) (ranks : ptrie N) (intervals : ptrie (N * N))
    (vs : list positive) : bool :=
  forallb (wto_edges_row ranks intervals b) vs.
TimeFun wto_edges_ok.

(** Hoisting a source rank preserves the original edge predicate on every row. *)
Lemma wto_edges_ok_agrees b ranks intervals vs :
  wto_edges_ok b ranks intervals vs = wto_edges_ok_spec b ranks intervals vs.
Proof.
  unfold wto_edges_ok, wto_edges_ok_spec.
  induction vs as [|u vs IH]; [reflexivity|].
  cbn [forallb]. now rewrite wto_edges_row_agrees, IH.
Qed.

(** The original checker remains the reference for full acceptance equivalence. *)
Definition wto_check_linear_spec (g : prepared) (roots : list positive) (w : wto) : bool :=
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

(** Listed keys bound candidate widths, and unique coverage lists are compared by length. *)
Definition wto_check_linear (g : prepared) (roots : list positive) (w : wto) : bool :=
  let b := base g in
  let listed := listed_of g in
  if forallb (fun v => match trie_get v listed with Some _ => true | None => false end) roots
  then
    match wto_check_index (check_fuel g) (vertex_width (nodes g)) listed
        [WtoCheckVisit w] 0%N Empty Empty [] with
    | None => false
    | Some (ranks, intervals, vs) =>
      let ready := scc_graph_counted g in
      let live := entered (prepared_search_trace ready roots) in
      if Nat.leb (length vs) (length live) then
        if forallb (fun v => match trie_get v ranks with Some _ => true | None => false end) live
        then wto_edges_ok b ranks intervals vs else false
      else false
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

(** Head accumulation charges one visit per constructor. *)
Lemma wto_heads_into_clock : forall w acc,
  (T_wto_heads_into w acc <= N.of_nat (2 * length (wto_order w) + 1))%N.
Proof.
  induction w as [|v rest IH|h body IHbody rest IHrest]; intro acc;
    cbn [wto_order length]; rewrite ?length_app; time_step.
Qed.

(** Order accumulation charges one visit per constructor. *)
Lemma wto_order_into_clock : forall w acc,
  (T_wto_order_into w acc <= N.of_nat (2 * length (wto_order w) + 1))%N.
Proof.
  induction w as [|v rest IH|h body IHbody rest IHrest]; intro acc;
    cbn [wto_order length]; rewrite ?length_app; time_step.
Qed.

(** A positive index below a natural bound uses at most its logarithmic number of bits. *)
Lemma wto_rank_width : forall rank bound,
  Pos.to_nat rank <= bound -> Pos.size_nat rank <= Nat.log2 bound + 1.
Proof.
  intros rank bound Hbound. apply Pos.size_nat_least.
  pose proof (Pos2Nat.is_pos rank) as Hpositive.
  pose proof (Nat.log2_spec bound ltac:(lia)) as Hlog.
  replace (Nat.log2 bound + 1) with (S (Nat.log2 bound)) by lia. lia.
Qed.

(** Ranking a suffix pays its keys and each binary rank within a fixed final bound. *)
Lemma wto_rank_rows_clock : forall vs start width bound,
  Forall (fun v => Pos.size_nat v <= width) vs ->
  Pos.to_nat start + length vs <= bound + 1 ->
  (T_wto_rank_rows start vs <=
    (PTrieT.c_trie + 3) * N.of_nat (length vs + 1) *
      N.of_nat (width + Nat.log2 bound + 1))%N.
Proof.
  induction vs as [|v rest IH]; intros start width bound Hwidth Hbound.
  - time_step.
  - inversion Hwidth as [|v' rest' Hkey Hrest]; subst.
    cbn [length] in Hbound.
    pose proof (IH (Pos.succ start) width bound Hrest
      ltac:(rewrite Pos2Nat.inj_succ; lia)) as Htail.
    pose proof (wto_rank_width start bound ltac:(lia)) as Hrank.
    pose proof (Pos.T_succ_le start) as Hsucc.
    pose proof (PTrieT.T_set_le positive v start (wto_rank_rows (Pos.succ start) rest))
      as Hset.
    time_unfold @T_wto_rank_rows. time_cbn. cbn [length].
    rewrite !Nat2N.inj_add in *. nia.
Qed.

(** The graph maximum agrees with the standard natural maximum. *)
Lemma wto_graph_max_nat : forall a b, graph_max a b = Nat.max a b.
Proof.
  induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.

(** Structural width bounds every emitted vertex key. *)
Lemma wto_vertex_width_all : forall vs,
  Forall (fun v => Pos.size_nat v <= vertex_width vs) vs.
Proof.
  induction vs as [|v rest IH]; [constructor|]. cbn [vertex_width fold_right]. rewrite wto_graph_max_nat.
  constructor.
  - apply Nat.le_max_l.
  - eapply Forall_impl; [|exact IH]. intros u Hu.
    eapply Nat.le_trans; [exact Hu|apply Nat.le_max_r].
Qed.

(** Ranking from one has the advertised key-width and logarithmic-position bound. *)
Lemma wto_rank_rows_one_clock : forall vs,
  (T_wto_rank_rows 1%positive vs <=
    (PTrieT.c_trie + 3) * N.of_nat (length vs + 1) *
      N.of_nat (vertex_width vs + Nat.log2 (length vs) + 1))%N.
Proof.
  intro vs. apply wto_rank_rows_clock; [apply wto_vertex_width_all|].
  cbn [Pos.to_nat]. lia.
Qed.

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

(** Annotation preserves the structural vertex order for every enclosing stack. *)
Lemma wto_annotation_order : forall w stack,
  map fst (wto_annotate stack w) = wto_order w.
Proof.
  induction w as [|v rest IH|h body IHbody rest IHrest]; intro stack;
    cbn [wto_annotate wto_order map fst]; try reflexivity.
  - now rewrite IH.
  - rewrite map_app, IHbody, IHrest. reflexivity.
Qed.

(** Each annotated stack contains the stack inherited at the subtree root. *)
Lemma wto_annotation_inherits : forall w stack u stored,
  In (u, stored) (wto_annotate stack w) -> forall h, In h stack -> In h stored.
Proof.
  induction w as [|v rest IH|head body IHbody rest IHrest];
    intros stack u stored Hin h Hstack; cbn [wto_annotate] in Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. exact Hstack.
    + eapply IH; eassumption.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. now right.
    + apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * eapply IHbody; [exact Hin|now right].
      * eapply IHrest; eassumption.
Qed.

(** Heads added to an annotated stack enclose the corresponding occurrence. *)
Lemma wto_annotation_sound : forall w stack u stored,
  In (u, stored) (wto_annotate stack w) -> forall h,
  In h stored -> In h stack \/ wto_encloses h u w.
Proof.
  induction w as [|v rest IH|head body IHbody rest IHrest];
    intros stack u stored Hin h Hstored; cbn [wto_annotate] in Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. now left.
    + destruct (IH stack u stored Hin h Hstored) as [Hstack|Hencloses].
      * now left.
      * right. now apply encloses_vertex.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. destruct Hstored as [Hhead|Hstack].
      * subst h. right. apply encloses_here. now left.
      * now left.
    + apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * destruct (IHbody (head :: stack) u stored Hin h Hstored)
          as [[Heq|Hstack]|Hencloses].
        -- subst h. right. apply encloses_here. right.
           rewrite <- (wto_annotation_order body (head :: stack)).
           exact (in_map fst _ _ Hin).
        -- now left.
        -- right. now apply encloses_body.
      * destruct (IHrest stack u stored Hin h Hstored) as [Hstack|Hencloses].
        -- now left.
        -- right. now apply encloses_rest.
Qed.

(** Every structural enclosure appears in an annotated row for its vertex. *)
Lemma wto_annotation_complete : forall w h u,
  wto_encloses h u w -> forall stack,
  exists stored, In (u, stored) (wto_annotate stack w) /\ In h stored.
Proof.
  intros w h u Hencloses.
  induction Hencloses as [inside rest Hmember|v rest Hencloses IH|
    head inside rest Hencloses IH|head inside rest Hencloses IH];
    intro stack; cbn [wto_annotate].
  - destruct Hmember as [Heq|Hin].
    + subst u. exists (h :: stack). split; now left.
    + rewrite <- (wto_annotation_order inside (h :: stack)) in Hin.
      apply in_map_iff in Hin. destruct Hin as [[v stored] [Heq Hin]].
      cbn [fst] in Heq. subst v. exists stored. split.
      * right. apply in_app_iff. now left.
      * eapply wto_annotation_inherits; [exact Hin|now left].
  - destruct (IH stack) as [stored [Hin Hhead]].
    exists stored. split; [now right|exact Hhead].
  - destruct (IH (head :: stack)) as [stored [Hin Hhead]].
    exists stored. split; [right; apply in_app_iff; now left|exact Hhead].
  - destruct (IH stack) as [stored [Hin Hhead]].
    exists stored. split; [right; apply in_app_iff; now right|exact Hhead].
Qed.

(** Rows with distinct first projections have a unique value at every key. *)
Lemma wto_rows_unique : forall (rows : list (positive * list positive)) u first second,
  NoDup (map fst rows) -> In (u, first) rows -> In (u, second) rows -> first = second.
Proof.
  induction rows as [|[v stored] rest IH]; intros u first second Hunique Hfirst Hsecond.
  - contradiction.
  - cbn [map fst] in Hunique. inversion Hunique as [|v' rest' Hfresh Hrest]; subst.
    destruct Hfirst as [Hfirst|Hfirst]; destruct Hsecond as [Hsecond|Hsecond].
    + congruence.
    + inversion Hfirst; subst. exfalso. apply Hfresh. exact (in_map fst _ _ Hsecond).
    + inversion Hsecond; subst. exfalso. apply Hfresh. exact (in_map fst _ _ Hfirst).
    + eapply IH; eassumption.
Qed.

(** Unique annotations store exactly the structural enclosing heads. *)
Lemma wto_annotation_spec : forall w,
  NoDup (wto_order w) -> forall u stored,
  In (u, stored) (wto_annotate [] w) ->
  forall h, In h stored <-> wto_encloses h u w.
Proof.
  intros w Hunique u stored Hin h. split.
  - intro Hhead. destruct (wto_annotation_sound w [] u stored Hin h Hhead)
      as [Hempty|Hencloses]; [contradiction|exact Hencloses].
  - intro Hencloses.
    destruct (wto_annotation_complete w h u Hencloses []) as [other [Hother Hhead]].
    assert (Heq : stored = other).
    { eapply wto_rows_unique; [rewrite wto_annotation_order; exact Hunique|exact Hin|exact Hother]. }
    now rewrite Heq.
Qed.

(** Prepending a vertex creates precedence from that vertex and preserves later precedence. *)
Lemma wto_before_cons : forall x u v rest,
  graph_before (x :: rest) u v <->
    (x = u /\ In v rest) \/ graph_before rest u v.
Proof.
  intros x u v rest. unfold graph_before. split.
  - intros [[|y prefix] [middle [suffix Heq]]].
    + cbn in Heq. injection Heq as Hx Hrest. left. split; [exact Hx|].
      rewrite Hrest. apply in_app_iff. right. now left.
    + cbn in Heq. injection Heq as Hx Hrest.
      right. exists prefix, middle, suffix. exact Hrest.
  - intros [[Heq Hin]|[prefix [middle [suffix Heq]]]].
    + subst x. apply in_split in Hin. destruct Hin as [middle [suffix Heq]].
      exists [], middle, suffix. now rewrite Heq.
    + exists (x :: prefix), middle, suffix. now cbn; rewrite Heq.
Qed.

(** Every predecessor occurs in its list. *)
Lemma wto_before_member : forall vs u v,
  graph_before vs u v -> In u vs.
Proof.
  intros vs u v [prefix [middle [suffix Heq]]]. rewrite Heq.
  apply in_app_iff. right. now left.
Qed.

(** Position rows contain exactly each key's strict suffix and supplied stack. *)
Lemma wto_positions_spec : forall rows,
  NoDup (map fst rows) -> forall u,
  (trie_get u (wto_positions rows) = None <-> ~ In u (map fst rows)) /\
  forall after stack, trie_get u (wto_positions rows) = Some (after, stack) ->
    In (u, stack) rows /\
    forall v, In v after <-> graph_before (map fst rows) u v.
Proof.
  induction rows as [|[head stored] rest IH]; intros Hunique u.
  - cbn [wto_positions map]. rewrite PTrie.get_empty. split.
    + split; [intros H Hin; contradiction|intro H; reflexivity].
    + intros after stack Hget. discriminate.
  - cbn [map fst] in Hunique. inversion Hunique as [|v vs Hfresh Hrest]; subst.
    cbn [wto_positions map fst].
    destruct (Pos.eq_dec u head) as [Heq|Hneq].
    + subst u. rewrite PTrie.get_set_same. split.
      * split; [discriminate|intro H; exfalso; apply H; now left].
      * intros after stack Hget. injection Hget as Hafter Hstack. subst after stack.
        split; [now left|]. intro v. rewrite wto_before_cons. split.
        -- intro Hin. left. auto.
        -- intros [[Heq Hin]|Hbefore]; [exact Hin|].
           exfalso. apply Hfresh. eapply wto_before_member; eassumption.
    + rewrite PTrie.get_set_other by exact Hneq.
      destruct (IH Hrest u) as [Habsent Hpresent]. split.
      * rewrite Habsent. cbn [In]. intuition congruence.
      * intros after stack Hget. destruct (Hpresent after stack Hget) as [Hin Hafter].
        split; [now right|]. intro v. rewrite wto_before_cons, <- Hafter. intuition congruence.
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

(** A pending visit refers to a structural subtree of the original candidate. *)
Inductive wto_subtree (whole : wto) : wto -> Prop :=
  | subtree_root : wto_subtree whole whole
  | subtree_vertex : forall v rest,
      wto_subtree whole (WVertex v rest) -> wto_subtree whole rest
  | subtree_body : forall h body rest,
      wto_subtree whole (WLoop h body rest) -> wto_subtree whole body
  | subtree_rest : forall h body rest,
      wto_subtree whole (WLoop h body rest) -> wto_subtree whole rest.

(** Enclosure in a pending subtree remains enclosure in the original candidate. *)
Lemma wto_subtree_encloses : forall whole tree,
  wto_subtree whole tree -> forall h v,
  wto_encloses h v tree -> wto_encloses h v whole.
Proof.
  intros whole tree Htree. induction Htree; intros head x Hencloses.
  - exact Hencloses.
  - apply IHHtree. now apply encloses_vertex.
  - apply IHHtree. now apply encloses_body.
  - apply IHHtree. now apply encloses_rest.
Qed.

(** Pending visits retain their unprocessed vertices; close tasks retain none. *)
Fixpoint wto_check_remaining (tasks : list wto_check_task) : list positive :=
  match tasks with
  | [] => []
  | WtoCheckVisit tree :: rest => wto_order tree ++ wto_check_remaining rest
  | WtoCheckClose _ :: rest => wto_check_remaining rest
  end.

(** Every pending visit lies inside every loop that closes after that visit. *)
Fixpoint wto_check_scopes (whole : wto) (tasks : list wto_check_task) : Prop :=
  match tasks with
  | [] => True
  | WtoCheckVisit tree :: rest =>
      (forall h, In (WtoCheckClose h) rest -> forall v, In v (wto_order tree) ->
        wto_encloses h v whole) /\ wto_check_scopes whole rest
  | WtoCheckClose _ :: rest => wto_check_scopes whole rest
  end.

(** The interval index relates processed positions, open scopes and closed intervals. *)
Record wto_index_invariant (whole : wto) (listed : ptrie bool) (s : wto_check_state) : Prop := {
  index_seen : wto_check_seen listed s;
  index_next : wto_check_next s = N.of_nat (length (wto_check_vertices s));
  index_order : rev (wto_check_vertices s) ++ wto_check_remaining (wto_check_tasks s) =
    wto_order whole;
  index_ranks : forall v r, trie_get v (wto_check_ranks s) = Some r ->
    exists i, nth_error (wto_order whole) i = Some v /\ r = N.of_nat i /\
      i < length (wto_check_vertices s);
  index_origins : forall tree, In (WtoCheckVisit tree) (wto_check_tasks s) ->
    wto_subtree whole tree;
  index_scopes : wto_check_scopes whole (wto_check_tasks s);
  index_active : forall h, In (WtoCheckClose h) (wto_check_tasks s) ->
    exists lo, trie_get h (wto_check_ranks s) = Some lo /\
      forall v r, trie_get v (wto_check_ranks s) = Some r -> (lo <= r)%N ->
        wto_encloses h v whole;
  index_intervals : forall h lo hi,
    trie_get h (wto_check_intervals s) = Some (lo, hi) ->
    (hi <= wto_check_next s)%N /\
    forall v r, trie_get v (wto_check_ranks s) = Some r -> (lo <= r < hi)%N ->
      wto_encloses h v whole
}.

(** Updating a key either returns its new binding or preserves another key's binding. *)
Lemma wto_get_set_cases : forall A (ranks : ptrie A) v next u r,
  trie_get u (PTrieCode.set v next ranks) = Some r ->
  (u = v /\ r = next) \/ (u <> v /\ trie_get u ranks = Some r).
Proof.
  intros A ranks v next u r Hget. destruct (Pos.eq_dec u v) as [->|Hne].
  - rewrite PTrie.get_set_same in Hget. inversion Hget; subst. now left.
  - rewrite PTrie.get_set_other in Hget by exact Hne. now right.
Qed.

(** Emitting a fresh listed vertex preserves the index when the task rewrite preserves scopes. *)
Lemma wto_index_emit : forall whole listed tasks next ranks intervals vs v b tasks',
  wto_index_invariant whole listed (WtoCheckState tasks next ranks intervals vs) ->
  trie_get v ranks = None -> trie_get v listed = Some b ->
  wto_check_remaining tasks = v :: wto_check_remaining tasks' ->
  (forall tree, In (WtoCheckVisit tree) tasks' -> wto_subtree whole tree) ->
  wto_check_scopes whole tasks' ->
  (forall h, In (WtoCheckClose h) tasks' ->
    (In (WtoCheckClose h) tasks /\ wto_encloses h v whole) \/
    (h = v /\ wto_encloses v v whole)) ->
  wto_index_invariant whole listed
    (WtoCheckState tasks' (N.succ next) (PTrieCode.set v next ranks) intervals (v :: vs)).
Proof.
  intros whole listed tasks next ranks intervals vs v b tasks' Hinv Hfresh Hlisted Hremaining
    Horigins' Hscopes' Hactive'.
  destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  cbn [wto_check_next wto_check_vertices wto_check_tasks wto_check_ranks
    wto_check_intervals] in *.
  assert (Hposition : nth_error (wto_order whole) (length vs) = Some v).
  { rewrite <- Horder, Hremaining.
    replace (length vs) with (length (rev vs)) by apply length_rev.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  constructor; cbn [wto_check_next wto_check_vertices wto_check_tasks wto_check_ranks
    wto_check_intervals].
  - eapply wto_check_seen_add; eassumption.
  - cbn [length]. rewrite Hnext, Nat2N.inj_succ. reflexivity.
  - cbn [rev]. rewrite <- app_assoc. cbn [app]. now rewrite <- Hremaining.
  - intros u r Hget. destruct (wto_get_set_cases _ _ _ _ _ _ Hget) as [[-> ->]|[Hne Hold]].
    + exists (length vs). repeat split; auto; cbn [length]; lia.
    + destruct (Hranks u r Hold) as [i [Hi [Hr Hlt]]].
      exists i. repeat split; auto; cbn [length]; lia.
  - exact Horigins'.
  - exact Hscopes'.
  - intros h Hclose. destruct (Hactive' h Hclose) as [[Hold Henclosed]|[-> Hself]].
    + destruct (Hactive h Hold) as [lo [Hlo Hinside]].
      assert (Hne : h <> v) by congruence.
      exists lo. split; [now rewrite PTrie.get_set_other|].
      intros u r Hget Hle.
      destruct (wto_get_set_cases _ _ _ _ _ _ Hget) as [[-> ->]|[Hune Hgetold]].
      * exact Henclosed.
      * now apply (Hinside u r).
    + exists next. split; [apply PTrie.get_set_same|].
      intros u r Hget Hle.
      destruct (wto_get_set_cases _ _ _ _ _ _ Hget) as [[-> ->]|[Hune Hgetold]].
      * exact Hself.
      * destruct (Hranks u r Hgetold) as [i [Hi [Hr Hlt]]].
        assert (Hbelow : (r < next)%N).
        { rewrite Hnext, Hr. lia. }
        lia.
  - intros h lo hi Hget. destruct (Hintervals h lo hi Hget) as [Hhi Hinside]. split.
    + lia.
    + intros u r Hrank Hrange.
      destruct (wto_get_set_cases _ _ _ _ _ _ Hrank) as [[-> ->]|[Hne Hold]].
      * lia.
      * now apply (Hinside u r).
Qed.

(** A successful checker result is the reversal of an invariant terminal state's vertices. *)
Definition wto_index_result (whole : wto) (listed : ptrie bool)
    (result : option (ptrie N * ptrie (N * N) * list positive)) : Prop :=
  match result with
  | None => True
  | Some (ranks, intervals, vs) => exists s,
      wto_index_invariant whole listed s /\ wto_check_tasks s = [] /\
      wto_check_ranks s = ranks /\ wto_check_intervals s = intervals /\
      rev (wto_check_vertices s) = vs
  end.

(** Every index transition preserves positions and the open and closed nesting scopes. *)
Lemma wto_index_step : forall whole width listed s,
  wto_index_invariant whole listed s ->
  match wto_check_step width listed s with
  | inl next => wto_index_invariant whole listed next
  | inr result => wto_index_result whole listed result
  end.
Proof.
  intros whole width listed [tasks next ranks intervals vs] Hinv.
  pose proof Hinv as Hparts.
  destruct Hparts as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  cbn [wto_check_next wto_check_vertices wto_check_tasks wto_check_ranks
    wto_check_intervals] in *.
  destruct tasks as [|task tasks].
  - cbn [wto_check_step wto_index_result].
    exists (WtoCheckState [] next ranks intervals vs). split; [exact Hinv|].
    repeat split; try reflexivity. now rewrite rev_append_rev, app_nil_r.
  - destruct task as [tree|h].
    + destruct tree as [|v tail|h body tail].
      * cbn [wto_check_step]. constructor; cbn [wto_check_next wto_check_vertices
          wto_check_tasks wto_check_ranks wto_check_intervals].
        -- exact Hseen.
        -- exact Hnext.
        -- exact Horder.
        -- exact Hranks.
        -- intros tree Hin. apply Horigins. now right.
        -- exact (proj2 Hscopes).
        -- intros h Hin. apply Hactive. now right.
        -- exact Hintervals.
      * cbn [wto_check_step]. destruct (wto_key_fits width v); [|exact I].
        destruct (trie_get v listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get v ranks) as [r|] eqn:Hfresh; [exact I|].
        eapply wto_index_emit; [exact Hinv|exact Hfresh|exact Hlisted|reflexivity| | |].
        -- intros tree [Heq|Hin].
           ++ injection Heq as Heq. subst tree. eapply subtree_vertex.
              apply Horigins. now left.
           ++ apply Horigins. now right.
        -- split.
           ++ intros h Hclose u Hin. apply (proj1 Hscopes h Hclose u). now right.
           ++ exact (proj2 Hscopes).
        -- intros h [Heq|Hin]; [discriminate|]. left. split; [now right|].
           apply (proj1 Hscopes h Hin v). now left.
      * cbn [wto_check_step]. destruct (wto_key_fits width h); [|exact I].
        destruct (trie_get h listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get h ranks) as [r|] eqn:Hfresh; [exact I|].
        assert (Hloop : wto_subtree whole (WLoop h body tail)).
        { apply Horigins. now left. }
        eapply wto_index_emit; [exact Hinv|exact Hfresh|exact Hlisted| | | |].
        -- cbn [wto_check_remaining wto_order]. now rewrite app_assoc.
        -- intros tree [Heq|[Heq|[Heq|Hin]]].
           ++ injection Heq as Heq. subst tree. now apply subtree_body in Hloop.
           ++ discriminate.
           ++ injection Heq as Heq. subst tree. now apply subtree_rest in Hloop.
           ++ apply Horigins. now right.
        -- split.
           ++ intros head [Heq|[Heq|Hin]] u Hu.
              ** injection Heq as Heq. subst head.
                 eapply wto_subtree_encloses; [exact Hloop|].
                 apply encloses_here. now right.
              ** discriminate.
              ** apply (proj1 Hscopes head Hin u). right. apply in_or_app. now left.
           ++ split.
              ** intros head Hin u Hu. apply (proj1 Hscopes head Hin u).
                 right. apply in_or_app. now right.
              ** exact (proj2 Hscopes).
        -- intros head [Heq|[Heq|[Heq|Hin]]].
           ++ discriminate.
           ++ injection Heq as Heq. subst head. right. split; [reflexivity|].
              eapply wto_subtree_encloses; [exact Hloop|].
              apply encloses_here. now left.
           ++ discriminate.
           ++ left. split; [now right|]. apply (proj1 Hscopes head Hin h). now left.
    + cbn [wto_check_step]. destruct (trie_get h ranks) as [lo|] eqn:Hlo; [|exact I].
      destruct (Hactive h (or_introl eq_refl)) as [start [Hstart Hinside]].
      assert (Hstartlo : start = lo) by congruence. subst start.
      constructor; cbn [wto_check_next wto_check_vertices wto_check_tasks wto_check_ranks
        wto_check_intervals].
      * exact Hseen.
      * exact Hnext.
      * exact Horder.
      * exact Hranks.
      * intros tree Hin. apply Horigins. now right.
      * exact Hscopes.
      * intros head Hin. apply Hactive. now right.
      * intros head first last Hget.
        destruct (wto_get_set_cases _ _ _ _ _ _ Hget) as [[Heq Hpair]|[Hne Hold]].
        -- subst head. injection Hpair as Heqfirst Heqlast. subst first last.
           split; [lia|]. intros u r Hr Hrange. apply (Hinside u r Hr). lia.
        -- now apply (Hintervals head first last).
Qed.

(** The binary driver carries the index invariant through every completed transition. *)
Lemma wto_index_loop : forall whole width listed fs (Hacc : Acc loopN_lt fs),
  wto_index_invariant whole listed (snd fs) ->
  match loop loopN_lt (loopN_step (wto_check_step width listed)) fs Hacc with
  | inl _ => True
  | inr result => wto_index_result whole listed result
  end.
Proof.
  intros whole width listed fs Hacc.
  induction Hacc as [[fuel s] Hacc IH] using Acc_ind_dep.
  cbn [snd]. intro Hinv. destruct fuel as [|p]; [exact I|].
  cbn [loop loopN_step Acc_inv].
  pose proof (wto_index_step whole width listed s Hinv) as Hstep.
  destruct (wto_check_step width listed s) as [next|result] eqn:Hnext.
  - apply IH. exact Hstep.
  - exact Hstep.
Qed.

(** The empty index starts at the first vertex of the whole candidate. *)
Lemma wto_index_initial : forall whole listed,
  wto_index_invariant whole listed
    (WtoCheckState [WtoCheckVisit whole] 0 Empty Empty []).
Proof.
  intros whole listed. constructor; cbn [wto_check_next wto_check_vertices wto_check_tasks
    wto_check_ranks wto_check_intervals].
  - split; [constructor|]. split.
    + intro v. split; [contradiction|]. intros [r Hget].
      rewrite PTrie.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
  - reflexivity.
  - cbn [rev app wto_check_remaining]. now rewrite app_nil_r.
  - intros v r Hget. rewrite PTrie.get_empty in Hget. discriminate.
  - intros tree [Heq|Hin]; [|contradiction]. injection Heq as Heq. subst tree. constructor.
  - split; [intros h Hin; contradiction|exact I].
  - intros h [Heq|Hin]; [discriminate|contradiction].
  - intros h lo hi Hget. rewrite PTrie.get_empty in Hget. discriminate.
Qed.

(** Fuel exhaustion cannot manufacture a successful index result. *)
Lemma wto_index_run : forall whole fuel width listed s,
  wto_index_invariant whole listed s ->
  match loopN (wto_check_step width listed) fuel s with
  | inl _ => True
  | inr result => wto_index_result whole listed result
  end.
Proof.
  intros whole fuel width listed s Hinv. unfold loopN. now apply wto_index_loop.
Qed.

Local Opaque loopN.

(** Successful candidate indexing exposes an invariant terminal state. *)
Lemma wto_check_index_result : forall fuel width listed w ranks intervals vs,
  wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
    Some (ranks, intervals, vs) ->
  wto_index_result w listed (Some (ranks, intervals, vs)).
Proof.
  intros fuel width listed w ranks intervals vs Hindex.
  pose proof (wto_index_run w fuel width listed
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty []) (wto_index_initial w listed)) as Hresult.
  unfold wto_check_index in Hindex.
  destruct (loopN (wto_check_step width listed) fuel
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty [])) as [s|result]; [discriminate|].
  destruct result as [[[ranks' intervals'] vs']|]; [|discriminate].
  inversion Hindex; subst. exact Hresult.
Qed.

Local Transparent loopN.

(** The completed numeric index recognizes the candidate's unique order and enclosing edges. *)
Lemma wto_check_index_spec : forall fuel width listed w ranks intervals vs,
  wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
    Some (ranks, intervals, vs) ->
  NoDup (wto_order w) /\ vs = wto_order w /\
  (forall v, (exists r, trie_get v ranks = Some r) <-> In v (wto_order w)) /\
  forall u v, wto_interval_edge ranks intervals u v = true ->
    graph_before (wto_order w) u v \/ wto_encloses v u w.
Proof.
  intros fuel width listed w ranks intervals vs Hindex.
  destruct (wto_check_index_result fuel width listed w ranks intervals vs Hindex)
    as [[tasks next ranks' intervals' seen] [Hinv [Htasks [Hranks [Hintervals Hvs]]]]].
  cbn [wto_check_tasks wto_check_ranks wto_check_intervals wto_check_vertices] in *.
  subst tasks ranks' intervals' vs.
  destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  cbn [wto_check_tasks wto_check_ranks wto_check_intervals wto_check_vertices
    wto_check_next wto_check_remaining] in *.
  rewrite app_nil_r in Horder.
  destruct Hseen as [Hunique [Hlookup Hlisted]].
  cbn [wto_check_vertices wto_check_ranks] in *.
  split; [rewrite <- Horder; now apply NoDup_rev|]. split; [exact Horder|]. split.
  - intro v. rewrite <- Horder, <- in_rev. symmetry. apply Hlookup.
  - intros u v Hedge. unfold wto_interval_edge in Hedge.
    destruct (trie_get u ranks) as [ru|] eqn:Hu; [|discriminate].
    destruct (trie_get v ranks) as [rv|] eqn:Hv; [|discriminate].
    apply orb_true_iff in Hedge. destruct Hedge as [Hforward|Hback].
    + apply N.ltb_lt in Hforward.
      destruct (Hranks u ru Hu) as [i [Hi [Hri Hboundi]]].
      destruct (Hranks v rv Hv) as [j [Hj [Hrj Hboundj]]].
      left. apply graph_before_indices. exists i, j. repeat split; auto; lia.
    + destruct (trie_get v intervals) as [[lo hi]|] eqn:Hinterval; [|discriminate].
      apply andb_true_iff in Hback. destruct Hback as [Hlo Hhi].
      apply N.leb_le in Hlo. apply N.ltb_lt in Hhi.
      right. apply (proj2 (Hintervals v lo hi Hinterval) u ru Hu). now split.
Qed.

Local Opaque loopN.

(** Every key within the declared width passes the candidate width guard. *)
Lemma wto_key_fits_complete width v :
  Pos.size_nat v <= width -> wto_key_fits width v = true.
Proof.
  revert v. induction width as [|width IH]; intros v Hwidth;
    destruct v; cbn [Pos.size_nat wto_key_fits] in *; try lia; try reflexivity; apply IH; lia.
Qed.

Lemma wto_key_fits_width width v : wto_key_fits width v = true -> Pos.size_nat v <= width.
Proof.
  revert v. induction width as [|width IH]; intro v; destruct v;
    cbn [wto_key_fits Pos.size_nat]; try discriminate; intros Hfit; try lia;
    specialize (IH _ Hfit); lia.
Qed.

(** Omitting edge occurrences can only reduce the maximum key width. *)
Lemma vertex_width_le_graph_width g :
  vertex_width (nodes g) <= graph_width (base g).
Proof.
  destruct g as [[vertices adjacency] predecessors n e].
  cbn [nodes base graph_width]. rewrite search_graph_max. apply Nat.le_max_l.
Qed.

(** A key that passes a smaller width guard also passes any larger guard. *)
Lemma wto_key_fits_mono small large v :
  small <= large -> wto_key_fits small v = true -> wto_key_fits large v = true.
Proof.
  intros Hwidth Hfits. apply wto_key_fits_complete.
  pose proof (wto_key_fits_width small v Hfits). lia.
Qed.

(** The smaller guard examines no more key bits than the larger guard. *)
Lemma wto_key_fits_clock_mono small large v :
  small <= large -> (T_wto_key_fits small v <= T_wto_key_fits large v)%N.
Proof.
  revert large v. induction small as [|small IH]; intros [|large] v Hwidth;
    destruct v; time_unfold @T_wto_key_fits; time_cbn; try lia;
    specialize (IH large v ltac:(lia)); lia.
Qed.

(** Any key rejected only by the smaller guard is absent from the listed table. *)
Lemma wto_check_step_vertices g st :
  wto_check_step (vertex_width (nodes g)) (listed_of g) st =
    wto_check_step (graph_width (base g)) (listed_of g) st.
Proof.
  assert (Hfits : forall v b, trie_get v (listed_of g) = Some b ->
      wto_key_fits (vertex_width (nodes g)) v = true /\
      wto_key_fits (graph_width (base g)) v = true).
  { intros v b Hget.
    assert (Hin : In v (nodes g)).
    { apply (proj1 (scc_listed_lookup (nodes g) v)). now exists b. }
    split; apply wto_key_fits_complete.
    - now apply search_vertex_width_member.
    - now apply scc_node_width. }
  destruct st as [tasks next ranks intervals vs].
  destruct tasks as [|task rest]; [reflexivity|].
  destruct task as [w|h]; [destruct w as [|v tail|h body tail]|];
    cbn [wto_check_step]; try reflexivity.
  - destruct (trie_get v (listed_of g)) as [b|] eqn:Hget.
    + destruct (Hfits v b Hget) as [Hsmall Hlarge]. now rewrite Hsmall, Hlarge.
    + destruct (wto_key_fits (vertex_width (nodes g)) v),
        (wto_key_fits (graph_width (base g)) v); now rewrite ?Hget.
  - destruct (trie_get h (listed_of g)) as [b|] eqn:Hget.
    + destruct (Hfits h b Hget) as [Hsmall Hlarge]. now rewrite Hsmall, Hlarge.
    + destruct (wto_key_fits (vertex_width (nodes g)) h),
        (wto_key_fits (graph_width (base g)) h); now rewrite ?Hget.
Qed.

(** Pointwise equal transitions produce equal binary-fuel loop results. *)
Lemma wto_loopN_agrees {St Out} (first second : St -> St + Out) :
  (forall st, first st = second st) -> forall fuel st,
  loopN first fuel st = loopN second fuel st.
Proof.
  intros Hagrees fuel st. rewrite !search_loopN_fuel.
  generalize (N.to_nat fuel) as count. intro count. revert st.
  induction count as [|count IH]; intro st; [reflexivity|].
  cbn [loop_fuel]. rewrite Hagrees. destruct (second st); [apply IH|reflexivity].
Qed.

(** The complete index result is independent of edge-occurrence widths. *)
Lemma wto_check_index_vertices g fuel tasks next ranks intervals vs :
  wto_check_index fuel (vertex_width (nodes g)) (listed_of g)
    tasks next ranks intervals vs =
  wto_check_index fuel (graph_width (base g)) (listed_of g)
    tasks next ranks intervals vs.
Proof.
  unfold wto_check_index.
  rewrite (wto_loopN_agrees _ _ (wto_check_step_vertices g)). reflexivity.
Qed.

(** Early width rejection can only shorten an index transition. *)
Lemma wto_check_step_clock_mono small large listed st :
  small <= large ->
  (T_wto_check_step small listed st <= T_wto_check_step large listed st)%N.
Proof.
  intro Hwidth. destruct st as [tasks next ranks intervals vs].
  destruct tasks as [|task rest]; [apply N.le_refl|].
  destruct task as [w|h]; [destruct w as [|v tail|h body tail]|];
    try apply N.le_refl.
  - pose proof (wto_key_fits_clock_mono small large v Hwidth) as Hfits.
    time_unfold @T_wto_check_step. time_cbn.
    destruct (wto_key_fits small v) eqn:Hsmall.
    + rewrite (wto_key_fits_mono small large v Hwidth Hsmall). lia.
    + destruct (wto_key_fits large v); lia.
  - pose proof (wto_key_fits_clock_mono small large h Hwidth) as Hfits.
    time_unfold @T_wto_check_step. time_cbn.
    destruct (wto_key_fits small h) eqn:Hsmall.
    + rewrite (wto_key_fits_mono small large h Hwidth Hsmall). lia.
    + destruct (wto_key_fits large h); lia.
Qed.


(** With reverse inclusion and unique lists, forward coverage is exactly a length bound. *)
Lemma wto_coverage_length_agrees (test : positive -> bool) vs live :
  NoDup vs -> NoDup live -> (forall v, test v = true <-> In v vs) ->
  (Nat.leb (length vs) (length live) && forallb test live) =
  (forallb (fun v => match trie_get v
    (fold_left (fun acc u => PTrieCode.set u true acc) live Empty) with
    | Some _ => true | None => false end) vs && forallb test live).
Proof.
  intros Hvs Hlive Hdomain.
  destruct (forallb test live) eqn:Hreverse; [|now rewrite !andb_false_r].
  rewrite !andb_true_r. apply eq_true_iff_eq.
  rewrite Nat.leb_le, forallb_forall.
  assert (Hincluded : incl live vs).
  { intros v Hin. apply (proj1 (Hdomain v)).
    rewrite forallb_forall in Hreverse. now apply Hreverse. }
  split.
  - intros Hlength v Hin. rewrite scc_listed_test. apply wto_member_spec.
    exact (NoDup_length_incl Hlive Hlength Hincluded v Hin).
  - intro Hforward. apply (NoDup_incl_length Hvs). intros v Hin.
    specialize (Hforward v Hin). rewrite scc_listed_test in Hforward.
    now apply wto_member_spec in Hforward.
Qed.

(** The width and coverage shortcuts preserve acceptance on every candidate. *)
Lemma wto_check_linear_agrees g roots w :
  wto_check_linear g roots w = wto_check_linear_spec g roots w.
Proof.
  unfold wto_check_linear, wto_check_linear_spec.
  rewrite scc_graph_counted_agrees, wto_check_index_vertices.
  destruct (forallb (fun v => match trie_get v (listed_of g) with
    Some _ => true | None => false end) roots); [|reflexivity].
  destruct (wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
    [WtoCheckVisit w] 0 Empty Empty []) as [[[ranks intervals] vs]|] eqn:Hindex;
    [|reflexivity].
  destruct (wto_check_index_spec _ _ _ _ _ _ _ Hindex)
    as [Hunique [Hvs [Hdomain _]]].
  assert (Hvs_unique : NoDup vs) by (now rewrite Hvs).
  assert (Htest : forall v,
    (match trie_get v ranks with Some _ => true | None => false end) = true <-> In v vs).
  { intro v. rewrite Hvs, <- (Hdomain v).
    destruct (trie_get v ranks) as [rank|].
    - split; [intro H; now exists rank|intro H; reflexivity].
    - split; [discriminate|intros [rank Hrank]; discriminate]. }
  cbn beta iota zeta.
  set (live := entered (prepared_search_trace (scc_graph g) roots)).
  pose proof (wto_coverage_length_agrees
    (fun v => match trie_get v ranks with Some _ => true | None => false end) vs live
    Hvs_unique (prepared_search_unique_raw (scc_graph g) roots) Htest) as Hcoverage.
  rewrite <- Hcoverage.
  destruct (Nat.leb (length vs) (length live));
    destruct (forallb (fun v => match trie_get v ranks with Some _ => true | None => false end)
      live); reflexivity.
Qed.

(** Distinct concatenated lists have no shared element. *)
Lemma wto_index_disjoint (first last : list positive) v :
  NoDup (first ++ last) -> In v first -> In v last -> False.
Proof.
  induction first as [|x first IH]; cbn [app In]; [contradiction|].
  intros Hunique [Heq|Hin] Hlast. apply NoDup_cons_iff in Hunique.
  - destruct Hunique as [Hfresh Hunique]. subst x. apply Hfresh.
    apply in_app_iff. now right.
  - apply NoDup_cons_iff in Hunique. eapply IH; eauto. exact (proj2 Hunique).
Qed.

(** A remaining distinct candidate vertex has not yet received a rank. *)
Lemma wto_index_future_unseen whole listed s v :
  NoDup (wto_order whole) -> wto_index_invariant whole listed s ->
  In v (wto_check_remaining (wto_check_tasks s)) ->
  trie_get v (wto_check_ranks s) = None.
Proof.
  intros Hunique Hinv Hfuture.
  pose proof (index_order _ _ _ Hinv) as Horder.
  pose proof (index_seen _ _ _ Hinv) as [_ [Hrank Hlisted]].
  destruct (trie_get v (wto_check_ranks s)) as [rank|] eqn:Hget; [|reflexivity].
  exfalso. eapply wto_index_disjoint; [rewrite Horder; exact Hunique| |exact Hfuture].
  apply (proj1 (in_rev (wto_check_vertices s) v)). apply (proj2 (Hrank v)). now exists rank.
Qed.

(** A valid candidate never takes a rejecting index transition. *)
Lemma wto_index_no_reject whole width listed s :
  NoDup (wto_order whole) ->
  (forall v, In v (wto_order whole) -> exists b, trie_get v listed = Some b) ->
  (forall v, In v (wto_order whole) -> Pos.size_nat v <= width) ->
  wto_index_invariant whole listed s ->
  wto_check_step width listed s <> inr None.
Proof.
  intros Hunique Hlisted Hwidth Hinv.
  destruct s as [tasks next ranks intervals vs].
  pose proof (index_order _ _ _ Hinv) as Horder.
  pose proof (index_active _ _ _ Hinv) as Hactive.
  cbn [wto_check_tasks wto_check_vertices wto_check_ranks] in Horder, Hactive.
  destruct tasks as [|task tasks]; [discriminate|].
  destruct task as [tree|h].
  - destruct tree as [|v tail|h body tail]; [discriminate| |].
    + assert (Hfuture : In v (wto_check_remaining (WtoCheckVisit (WVertex v tail) :: tasks))).
      { cbn [wto_check_remaining wto_order app In]. now left. }
      assert (Hin : In v (wto_order whole)).
      { rewrite <- Horder. apply in_app_iff. now right. }
      pose proof (wto_index_future_unseen _ _ _ _ Hunique Hinv Hfuture) as Hfresh.
      cbn [wto_check_ranks] in Hfresh. destruct (Hlisted v Hin) as [b Hget].
      cbn [wto_check_step]. rewrite wto_key_fits_complete by now apply Hwidth.
      rewrite Hget, Hfresh. discriminate.
    + assert (Hfuture : In h (wto_check_remaining (WtoCheckVisit (WLoop h body tail) :: tasks))).
      { cbn [wto_check_remaining wto_order app In]. now left. }
      assert (Hin : In h (wto_order whole)).
      { rewrite <- Horder. apply in_app_iff. now right. }
      pose proof (wto_index_future_unseen _ _ _ _ Hunique Hinv Hfuture) as Hfresh.
      cbn [wto_check_ranks] in Hfresh. destruct (Hlisted h Hin) as [b Hget].
      cbn [wto_check_step]. rewrite wto_key_fits_complete by now apply Hwidth.
      rewrite Hget, Hfresh. discriminate.
  - destruct (Hactive h (or_introl eq_refl)) as [lo [Hget Hscope]].
    cbn [wto_check_step]. rewrite Hget. discriminate.
Qed.

(** Constructor work includes the close transition generated by a loop. *)
Fixpoint wto_index_tree_weight (w : wto) : nat :=
  match w with
  | WNil => 1
  | WVertex _ rest => 1 + wto_index_tree_weight rest
  | WLoop _ body rest => 2 + wto_index_tree_weight body + wto_index_tree_weight rest
  end.

Fixpoint wto_index_tasks_weight (tasks : list wto_check_task) : nat :=
  match tasks with
  | [] => 0
  | WtoCheckVisit w :: rest => wto_index_tree_weight w + wto_index_tasks_weight rest
  | WtoCheckClose _ :: rest => 1 + wto_index_tasks_weight rest
  end.

Lemma wto_index_tree_weight_bound w :
  wto_index_tree_weight w <= 3 * length (wto_order w) + 1.
Proof.
  induction w; cbn [wto_index_tree_weight wto_order length];
    try rewrite length_app; lia.
Qed.

(** Each continuing transition consumes one unit of constructor work. *)
Lemma wto_index_weight_step width listed s next :
  wto_check_step width listed s = inl next ->
  wto_index_tasks_weight (wto_check_tasks next) <
    wto_index_tasks_weight (wto_check_tasks s).
Proof.
  destruct s as [[|task tasks] count ranks intervals vs]; [discriminate|].
  destruct task as [tree|h].
  - destruct tree as [|v rest|h body rest]; cbn [wto_check_step].
    + intros Hnext; injection Hnext as Hnext; subst next;
        cbn [wto_check_tasks wto_index_tasks_weight wto_index_tree_weight]; lia.
    + destruct (wto_key_fits width v); [|discriminate].
      destruct (trie_get v listed); [|discriminate].
      destruct (trie_get v ranks); [discriminate|].
      intros Hnext; injection Hnext as Hnext; subst next;
        cbn [wto_check_tasks wto_index_tasks_weight wto_index_tree_weight]; lia.
    + destruct (wto_key_fits width h); [|discriminate].
      destruct (trie_get h listed); [|discriminate].
      destruct (trie_get h ranks); [discriminate|].
      intros Hnext; injection Hnext as Hnext; subst next;
        cbn [wto_check_tasks wto_index_tasks_weight wto_index_tree_weight]; lia.
  - cbn [wto_check_step]. destruct (trie_get h ranks); [|discriminate].
    intros Hnext; injection Hnext as Hnext; subst next;
      cbn [wto_check_tasks wto_index_tasks_weight]; lia.
Qed.

(** Preservation and nonrejection exclude a rejecting result at every fuel level. *)
Lemma wto_index_fuel_no_reject whole width listed fuel s :
  NoDup (wto_order whole) ->
  (forall v, In v (wto_order whole) -> exists b, trie_get v listed = Some b) ->
  (forall v, In v (wto_order whole) -> Pos.size_nat v <= width) ->
  wto_index_invariant whole listed s ->
  loop_fuel (wto_check_step width listed) fuel s <> inr None.
Proof.
  intros Hunique Hlisted Hwidth. revert s.
  induction fuel as [|fuel IH]; intros s Hinv; [discriminate|].
  cbn [loop_fuel].
  pose proof (wto_index_step whole width listed s Hinv) as Hpreserve.
  pose proof (wto_index_no_reject _ _ _ _ Hunique Hlisted Hwidth Hinv) as Hreject.
  destruct (wto_check_step width listed s) as [next|result] eqn:Hstep.
  - now apply IH.
  - exact Hreject.
Qed.

(** Sufficient fuel accepts every distinct candidate whose vertices are listed. *)
Lemma wto_check_index_complete fuel width listed w :
  NoDup (wto_order w) ->
  (forall v, In v (wto_order w) -> exists b, trie_get v listed = Some b) ->
  (forall v, In v (wto_order w) -> Pos.size_nat v <= width) ->
  (N.of_nat (3 * length (wto_order w) + 1) < fuel)%N ->
  exists ranks intervals vs,
    wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
      Some (ranks, intervals, vs).
Proof.
  intros Hunique Hlisted Hwidth Hfuel.
  assert (Hstep : forall s next, wto_index_invariant w listed s ->
      wto_check_step width listed s = inl next ->
      wto_index_invariant w listed next /\
      wto_index_tasks_weight (wto_check_tasks next) <
        wto_index_tasks_weight (wto_check_tasks s)).
  { intros s next Hinv Hstep. split.
    - pose proof (wto_index_step w width listed s Hinv) as Hnext.
      now rewrite Hstep in Hnext.
    - now apply (wto_index_weight_step width listed s next). }
  pose proof (wto_index_tree_weight_bound w) as Hweight.
  destruct (loopN_done _ _ (wto_check_step width listed) (wto_index_invariant w listed)
    (fun s => wto_index_tasks_weight (wto_check_tasks s)) fuel
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty []) Hstep
    (wto_index_initial w listed)) as [result Hrun].
  - cbn [wto_check_tasks wto_index_tasks_weight]. lia.
  - destruct result as [[[ranks intervals] vs]|].
    + exists ranks, intervals, vs. unfold wto_check_index. now rewrite Hrun.
    + exfalso. rewrite search_loopN_fuel in Hrun.
      exact (wto_index_fuel_no_reject _ _ _ _ _ Hunique Hlisted Hwidth
        (wto_index_initial w listed) Hrun).
Qed.

(** The public checker fuel covers every distinct listed candidate, even with stale caches. *)
Lemma wto_check_index_listed_complete g w :
  NoDup (wto_order w) -> incl (wto_order w) (nodes g) ->
  exists ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs).
Proof.
  intros Hunique Hlisted. apply wto_check_index_complete; [exact Hunique| | |].
  - intros v Hin. unfold listed_of. apply (proj2 (scc_listed_lookup (nodes g) v)).
    now apply Hlisted.
  - intros v Hin. apply scc_node_width. now apply Hlisted.
  - pose proof (NoDup_incl_length Hunique Hlisted) as Hlength.
    assert (Hnodes : length (nodes g) = graph_n (base g)) by (destruct g as [[vs rows] pred nv ne]; reflexivity).
    unfold check_fuel. rewrite !N.double_spec. rewrite Hnodes in Hlength. nia.
Qed.

Local Transparent loopN.

(** A successful presence test is exactly an inhabited optional lookup. *)
Lemma wto_present_test : forall A v (table : ptrie A),
  (match trie_get v table with Some _ => true | None => false end) = true <->
  exists value, trie_get v table = Some value.
Proof.
  intros A v table. destruct (trie_get v table) as [value|].
  - split; [intro H; now exists value|intro H; reflexivity].
  - split; [discriminate|intros [value Hvalue]; discriminate].
Qed.

(** Every edge retained by graph filtering was already an original edge. *)
Lemma wto_filtered_path : forall g u vs v,
  path (base (scc_graph g)) u vs v -> path (base g) u vs v.
Proof.
  intros g u vs v Hpath. induction Hpath as [v|u v vs z Hedge Hpath IH].
  - constructor.
  - econstructor; [|exact IH]. unfold edge in *.
    rewrite scc_graph_succs in Hedge.
    destruct (existsb (Pos.eqb u) (nodes g)); [|contradiction].
    apply filter_In in Hedge. exact (proj1 Hedge).
Qed.

(** Filtering cannot introduce rooted reachability absent from the original graph. *)
Lemma wto_filtered_reach : forall g roots v,
  reach (base (scc_graph g)) roots v -> reach (base g) roots v.
Proof.
  intros g roots v [r [vs [Hroot Hpath]]]. exists r, vs.
  split; [exact Hroot|now apply wto_filtered_path].
Qed.

Local Opaque loopN.

(** The annotation index recognizes exactly textual forward edges and enclosing heads. *)
Lemma wto_positions_edge_spec w u v :
  NoDup (wto_order w) -> In u (wto_order w) ->
  (wto_edge_b (wto_positions (wto_annotate [] w)) u v = true <->
    graph_before (wto_order w) u v \/ wto_encloses v u w).
Proof.
  intros Hunique Hu.
  destruct (wto_positions_spec (wto_annotate [] w)
    ltac:(rewrite wto_annotation_order; exact Hunique) u) as [Habsent Hpresent].
  rewrite wto_annotation_order in Habsent.
  destruct (trie_get u (wto_positions (wto_annotate [] w))) as [[after stack]|] eqn:Hget.
  - destruct (Hpresent after stack eq_refl) as [Hrow Hafter].
    rewrite wto_annotation_order in Hafter.
    unfold wto_edge_b. rewrite Hget, orb_true_iff, !wto_member_spec, Hafter.
    rewrite (wto_annotation_spec w Hunique u stack Hrow v). reflexivity.
  - exfalso. exact (proj1 Habsent eq_refl Hu).
Qed.

(** Filtering preserves every path inside a listed successor-closed domain. *)
Lemma wto_filter_path_domain g vertices :
  incl vertices (nodes g) ->
  (forall u v, In u vertices -> edge (base g) u v -> In v vertices) ->
  forall u path_vs v, path (base g) u path_vs v -> In u vertices ->
    path (base (scc_graph g)) u path_vs v.
Proof.
  intros Hlisted Hclosed u path_vs v Hpath.
  induction Hpath as [u|u v path_vs z Hedge Hpath IH]; intro Hu.
  - constructor.
  - assert (Hv : In v vertices) by (eapply Hclosed; eassumption).
    econstructor; [|now apply IH]. unfold edge.
    rewrite scc_graph_succs_listed by now apply Hlisted.
    apply filter_In. split; [exact Hedge|].
    apply existsb_exists. exists v. split; [now apply Hlisted|apply Pos.eqb_refl].
Qed.

(** Exact listed rooted coverage is unchanged by the checker's graph filtering. *)
Lemma wto_filter_coverage g roots vertices :
  incl vertices (nodes g) ->
  (forall v, In v vertices <-> reach (base g) roots v) ->
  forall v, In v vertices <-> reach (base (scc_graph g)) roots v.
Proof.
  intros Hlisted Hcover v. split.
  - intro Hv. destruct (proj1 (Hcover v) Hv) as [r [path_vs [Hr Hpath]]].
    exists r, path_vs. split; [exact Hr|].
    eapply wto_filter_path_domain; [exact Hlisted| |exact Hpath|].
    + intros u z Hu Hedge. apply Hcover.
      exact (wto_reach_step (base g) roots u z (proj1 (Hcover u) Hu) Hedge).
    + apply Hcover. exists r, [r]. split; [exact Hr|constructor].
  - intro Hreach. apply Hcover. now apply wto_filtered_reach.
Qed.

(** Completed numeric ranks preserve every textual forward edge. *)
Lemma wto_check_index_forward fuel width listed w ranks intervals vs u v :
  wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
    Some (ranks, intervals, vs) ->
  graph_before (wto_order w) u v -> wto_interval_edge ranks intervals u v = true.
Proof.
  intros Hindex Hbefore.
  destruct (wto_check_index_spec _ _ _ _ _ _ _ Hindex) as [Hunique [_ [Hdomain Hlegal]]].
  apply graph_before_indices in Hbefore. destruct Hbefore as [i [j [Hij [Hi Hj]]]].
  assert (Huin : In u (wto_order w)) by (now apply nth_error_In in Hi).
  assert (Hvin : In v (wto_order w)) by (now apply nth_error_In in Hj).
  destruct (proj2 (Hdomain u) Huin) as [ru Hu].
  destruct (proj2 (Hdomain v) Hvin) as [rv Hv].
  destruct (wto_check_index_result _ _ _ _ _ _ _ Hindex)
    as [s [Hinv [Htasks [Hranks [Hintervals Hvs]]]]].
  pose proof (index_ranks _ _ _ Hinv) as Hpositions. rewrite Hranks in Hpositions.
  destruct (Hpositions u ru Hu) as [i' [Hi' [Hru Hbi]]].
  destruct (Hpositions v rv Hv) as [j' [Hj' [Hrv Hbj]]].
  pose proof (wto_nth_unique _ i' i u Hunique Hi' Hi) as Hii.
  pose proof (wto_nth_unique _ j' j v Hunique Hj' Hj) as Hjj.
  unfold wto_interval_edge. rewrite Hu, Hv. apply orb_true_iff. left.
  apply N.ltb_lt. subst i' j' ru rv. lia.
Qed.

(** A successful complete numeric index and exact coverage pass the remaining checker scans. *)
Lemma wto_check_from_coverage g roots w ranks intervals vs :
  (forall v, In v roots -> In v (nodes g)) ->
  incl (wto_order w) (nodes g) ->
  (forall v, In v (wto_order w) <-> reach (base g) roots v) ->
  wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
    [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
  (forall u v, In u (wto_order w) -> edge (base g) u v ->
    wto_interval_edge ranks intervals u v = true) ->
  wto_check_linear g roots w = true.
Proof.
  intros Hroots Hlisted Hcover Hindex Hedges.
  destruct (wto_check_index_spec _ _ _ _ _ _ _ Hindex) as [_ [Hvs [Hranks Hlegal]]].
  assert (Hroot_test : forallb (fun v => match trie_get v (listed_of g) with
    Some _ => true | None => false end) roots = true).
  { apply forallb_forall. intros v Hin. apply wto_present_test.
    apply (proj2 (scc_listed_lookup (nodes g) v)). now apply Hroots. }
  assert (Hlive : forall v,
      In v (entered (prepared_search_trace (scc_graph g) roots)) <-> In v (wto_order w)).
  { intro v. rewrite (prepared_search_reach_closed (scc_graph g) roots
      (scc_graph_counts g)).
    - symmetry. now apply wto_filter_coverage.
    - intros u z Hu Hedge. rewrite scc_graph_nodes. now apply (scc_graph_closed g u).
    - intros r Hin. rewrite scc_graph_nodes. now apply Hroots. }
  rewrite wto_check_linear_agrees. unfold wto_check_linear_spec.
  rewrite Hroot_test, Hindex.
  apply andb_true_iff. split.
  - apply andb_true_iff. split; apply forallb_forall; intros v Hin.
    + apply wto_present_test. apply (proj2 (scc_listed_lookup _ v)).
      apply Hlive. now rewrite <- Hvs.
    + apply wto_present_test, (proj2 (Hranks v)). now apply Hlive.
  - rewrite wto_edges_ok_agrees. unfold wto_edges_ok_spec.
    apply forallb_forall. intros u Hu.
    apply forallb_forall. intros v Hedge. apply Hedges; [now rewrite <- Hvs|exact Hedge].
Qed.


Local Transparent loopN.

(** A successor-closed vertex list contains every endpoint reached from one of its vertices. *)
Lemma wto_path_domain : forall g vertices,
  (forall u v, In u vertices -> edge g u v -> In v vertices) ->
  forall u vs v, path g u vs v -> In u vertices -> In v vertices.
Proof.
  intros g vertices Hclosed u vs v Hpath. induction Hpath; intro Hin.
  - exact Hin.
  - apply IHHpath. eapply Hclosed; eassumption.
Qed.

(** An accepting checker has already established that each supplied root is listed. *)
Lemma wto_check_roots : forall g roots w,
  wto_check_linear g roots w = true -> forall v, In v roots -> In v (nodes g).
Proof.
  intros g roots w Hcheck v Hin. unfold wto_check_linear in Hcheck.
  destruct (forallb (fun v =>
    match trie_get v (listed_of g) with Some _ => true | None => false end) roots)
    eqn:Hroots; [|discriminate].
  rewrite forallb_forall in Hroots. specialize (Hroots v Hin).
  apply wto_present_test in Hroots. now apply (proj1 (scc_listed_lookup (nodes g) v)).
Qed.

Local Opaque loopN.

(** A complete filtered trace and accepted edge checks establish raw rooted coverage. *)
Lemma wto_check_sound_from_reach : forall g roots w,
  (forall v, In v (entered (prepared_search_trace (scc_graph g) roots)) <->
    reach (base (scc_graph g)) roots v) ->
  wto_check_linear g roots w = true -> is_wto g roots w.
Proof.
  intros g roots w Htrace Hcheck. rewrite wto_check_linear_agrees in Hcheck.
  unfold wto_check_linear_spec in Hcheck.
  destruct (forallb (fun v =>
    match trie_get v (listed_of g) with Some _ => true | None => false end) roots);
    [|discriminate].
  destruct (wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
    [WtoCheckVisit w] 0 Empty Empty []) as [[[ranks intervals] vs]|] eqn:Hindex;
    [|discriminate].
  set (live := entered (prepared_search_trace (scc_graph g) roots)) in *.
  apply andb_true_iff in Hcheck. destruct Hcheck as [Hcoverage Hedges].
  apply andb_true_iff in Hcoverage. destruct Hcoverage as [Hinside Houtside].
  destruct (wto_check_index_spec (check_fuel g) (graph_width (base g)) (listed_of g)
    w ranks intervals vs Hindex) as [Hunique [Hvs [Hdomain Hlegal]]].
  rewrite forallb_forall in Hinside. rewrite forallb_forall in Houtside.
  rewrite wto_edges_ok_agrees in Hedges. unfold wto_edges_ok_spec in Hedges.
  rewrite forallb_forall in Hedges.
  assert (Hedge_order : forall u v, In u (wto_order w) -> edge (base g) u v ->
    graph_before (wto_order w) u v \/ wto_encloses v u w).
  { intros u v Hu Hedge. apply Hlegal.
    specialize (Hedges u ltac:(now rewrite Hvs)). rewrite forallb_forall in Hedges.
    now apply Hedges. }
  assert (Hclosed : forall u v, In u (wto_order w) -> edge (base g) u v ->
    In v (wto_order w)).
  { intros u v Hu Hedge. destruct (Hedge_order u v Hu Hedge) as [Hbefore|Hencloses].
    - apply graph_before_indices in Hbefore. destruct Hbefore as [i [j [Hlt [Hi Hj]]]].
      now apply nth_error_In in Hj.
    - exact (proj2 (wto_encloses_member w v u Hencloses)). }
  assert (Hroots : forall r, In r roots -> In r (wto_order w)).
  { intros r Hr. apply (proj1 (Hdomain r)), wto_present_test, Houtside.
    apply Htrace. exists r, [r]. split; [exact Hr|constructor]. }
  assert (Hcover : forall v, In v (wto_order w) <-> reach (base g) roots v).
  { intro v. split.
    - intro Hin. apply wto_filtered_reach, Htrace.
      apply (proj1 (scc_listed_lookup live v)), wto_present_test, Hinside.
      now rewrite Hvs.
    - intros [r [path_vs [Hr Hpath]]].
      eapply wto_path_domain; [exact Hclosed|exact Hpath|now apply Hroots]. }
  split; [exact Hunique|]. split; [exact Hcover|].
  intros u v Hedge Hreach. apply Hedge_order; [now apply Hcover|exact Hedge].
Qed.

Local Transparent loopN.

(** Width rejection reads at most the permitted prefix of a candidate identifier. *)
Lemma wto_key_fits_clock width v :
  (T_wto_key_fits width v <= 2 * N.of_nat (width + 1))%N.
Proof.
  revert v. induction width as [|width IH]; intro v; destruct v;
    time_step; specialize (IH v); lia.
Qed.

(** Every processed index vertex is listed, even for a rejected or truncated candidate. *)
Lemma wto_index_vertices g whole st :
  wto_index_invariant whole (listed_of g) st ->
  NoDup (wto_check_vertices st) /\
  incl (wto_check_vertices st) (nodes g) /\
  Forall (fun v => Pos.size_nat v <= graph_width (base g)) (wto_check_vertices st).
Proof.
  intros Hinv. destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  destruct Hseen as [Hunique [Hrank Hlisted]].
  assert (Hincl : incl (wto_check_vertices st) (nodes g)).
  { intros v Hin. destruct (Hlisted v Hin) as [b Hget].
    apply (proj1 (scc_listed_lookup (nodes g) v)). exists b. exact Hget. }
  split; [exact Hunique|]. split; [exact Hincl|].
  apply Forall_forall. intros v Hin. apply scc_node_width. now apply Hincl.
Qed.

Lemma wto_index_vertex_count g whole st :
  wto_index_invariant whole (listed_of g) st ->
  length (wto_check_vertices st) <= graph_n (base g).
Proof.
  intro Hinv. destruct (wto_index_vertices g whole st Hinv) as [Hunique [Hincl Hwidth]].
  pose proof (NoDup_incl_length Hunique Hincl) as Hlength.
  destruct g as [[vertices adjacency] predecessors n e]. exact Hlength.
Qed.

(** A processed-vertex counter needs at most one bit beyond its distinct identifier keys. *)
Lemma wto_counter_width width vertices n :
  NoDup vertices -> Forall (fun v => Pos.size_nat v <= width) vertices ->
  (n <= N.of_nat (S (length vertices)))%N -> N.size_nat n <= width + 1.
Proof.
  intros Hunique Hwidth Hcount. destruct n as [|p]; [cbn; lia|].
  cbn [N.size_nat]. apply (tarjan_counter_width width vertices p Hunique Hwidth).
  change (N.to_nat (N.pos p) <= S (length vertices)). lia.
Qed.

Lemma wto_index_counter_width g whole st :
  wto_index_invariant whole (listed_of g) st ->
  N.size_nat (wto_check_next st) <= graph_width (base g) + 1.
Proof.
  intro Hinv. destruct (wto_index_vertices g whole st Hinv) as [Hunique [Hincl Hwidth]].
  destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  apply (wto_counter_width _ _ _ Hunique Hwidth). rewrite Hnext. lia.
Qed.

Lemma wto_index_rank_width g whole st v r :
  wto_index_invariant whole (listed_of g) st ->
  trie_get v (wto_check_ranks st) = Some r -> N.size_nat r <= graph_width (base g) + 1.
Proof.
  intros Hinv Hget.
  destruct (wto_index_vertices g whole st Hinv) as [Hunique [Hincl Hwidth]].
  destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  destruct (Hranks v r Hget) as [i [Hnth [Heq Hbound]]].
  apply (wto_counter_width _ _ _ Hunique Hwidth). rewrite Heq. lia.
Qed.

Lemma wto_index_close_width g whole st h :
  wto_index_invariant whole (listed_of g) st ->
  In (WtoCheckClose h) (wto_check_tasks st) -> Pos.size_nat h <= graph_width (base g).
Proof.
  intros Hinv Hclose.
  destruct (wto_index_vertices g whole st Hinv) as [Hunique [Hincl Hwidth]].
  destruct Hinv as [Hseen Hnext Horder Hranks Horigins Hscopes Hactive Hintervals].
  destruct (Hactive h Hclose) as [lo [Hget Hencloses]].
  destruct Hseen as [_ [Hpresent _]].
  apply scc_node_width. apply Hincl. apply (proj2 (Hpresent h)). now exists lo.
Qed.

(** Nonterminal candidate transitions read bounded keys and one bounded counter. *)
Lemma wto_check_nonempty_clock g whole st :
  wto_index_invariant whole (listed_of g) st -> wto_check_tasks st <> [] ->
  (T_wto_check_step (graph_width (base g)) (listed_of g) st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hinv Hnonempty.
  pose proof (wto_index_counter_width g whole st Hinv) as Hcounter.
  destruct st as [[|task tasks] next ranks intervals vs]; [contradiction Hnonempty; reflexivity|].
  cbn [wto_check_next] in Hcounter. destruct task as [tree|h].
  - destruct tree as [|v tail|h body tail].
    + time_unfold @T_wto_check_step. time_cbn. nia.
    + pose proof (wto_key_fits_clock (graph_width (base g)) v) as Hfit.
      destruct (wto_key_fits (graph_width (base g)) v) eqn:Hfits.
      * pose proof (wto_key_fits_width _ _ Hfits) as Hv.
        pose proof (PTrieT.T_trie_get_le bool v (listed_of g)) as Hlisted.
        pose proof (PTrieT.T_trie_get_le N v ranks) as Hranks.
        pose proof (PTrieT.T_set_le N v next ranks) as Hset.
        pose proof (N.T_succ_le next) as Hsucc.
        time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        destruct (trie_get v (listed_of g)); destruct (trie_get v ranks);
          time_cbn; rewrite ?Hlisted, ?Hranks; rewrite !Nat2N.inj_add in *; nia.
      * time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        rewrite !Nat2N.inj_add in *. nia.
    + pose proof (wto_key_fits_clock (graph_width (base g)) h) as Hfit.
      destruct (wto_key_fits (graph_width (base g)) h) eqn:Hfits.
      * pose proof (wto_key_fits_width _ _ Hfits) as Hh.
        pose proof (PTrieT.T_trie_get_le bool h (listed_of g)) as Hlisted.
        pose proof (PTrieT.T_trie_get_le N h ranks) as Hranks.
        pose proof (PTrieT.T_set_le N h next ranks) as Hset.
        pose proof (N.T_succ_le next) as Hsucc.
        time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        destruct (trie_get h (listed_of g)); destruct (trie_get h ranks);
          time_cbn; rewrite ?Hlisted, ?Hranks; rewrite !Nat2N.inj_add in *; nia.
      * time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        rewrite !Nat2N.inj_add in *. nia.
  - pose proof (wto_index_close_width g whole _ h Hinv (or_introl eq_refl)) as Hh.
    pose proof (PTrieT.T_trie_get_le N h ranks) as Hget.
    destruct (trie_get h ranks) as [lo|] eqn:Hlo.
    + pose proof (PTrieT.T_set_le (N * N) h (lo, next) intervals) as Hset.
      time_unfold @T_wto_check_step. rewrite Hlo. time_cbn.
      rewrite !Nat2N.inj_add in *. nia.
    + time_unfold @T_wto_check_step. rewrite Hlo. time_cbn.
      rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma wto_check_continuing_clock g whole st next :
  wto_index_invariant whole (listed_of g) st ->
  wto_check_step (graph_width (base g)) (listed_of g) st = inl next ->
  (T_wto_check_step (graph_width (base g)) (listed_of g) st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hinv Hstep. apply (wto_check_nonempty_clock g whole st Hinv).
  destruct st as [tasks next0 ranks intervals vs]. cbn [wto_check_tasks].
  intros Heq. subst tasks. discriminate Hstep.
Qed.

Lemma wto_check_terminal_clock g whole st :
  wto_index_invariant whole (listed_of g) st ->
  (T_wto_check_step (graph_width (base g)) (listed_of g) st <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1) +
    4 * N.of_nat (graph_n (base g) + 1))%N.
Proof.
  intro Hinv. destruct (wto_check_tasks st) as [|task tasks] eqn:Htasks.
  - pose proof (wto_index_vertex_count g whole st Hinv) as Hvertices.
    destruct st as [tasks0 next ranks intervals vs]. cbn [wto_check_tasks] in Htasks.
    subst tasks0. cbn [wto_check_vertices] in Hvertices.
    pose proof (List.T_rev_append_le vs []) as Hrev.
    time_unfold @T_wto_check_step. time_cbn. nia.
  - pose proof (wto_check_nonempty_clock g whole st Hinv
      ltac:(rewrite Htasks; discriminate)) as Hstep. lia.
Qed.

(** A recorded path preserves the existing index invariant at every transition and at its end. *)
Lemma wto_index_path g whole st states last :
  search_machine_path (wto_check_step (graph_width (base g)) (listed_of g)) st states last ->
  wto_index_invariant whole (listed_of g) st ->
  Forall (fun current => wto_index_invariant whole (listed_of g) current /\
    exists next, wto_check_step (graph_width (base g)) (listed_of g) current = inl next) states /\
  wto_index_invariant whole (listed_of g) last.
Proof.
  intro Hpath. induction Hpath as [st|st next states last Hstep Hpath IH]; intro Hinv.
  - split; [constructor|exact Hinv].
  - pose proof (wto_index_step whole (graph_width (base g)) (listed_of g) st Hinv) as Hnext.
    rewrite Hstep in Hnext. destruct (IH Hnext) as [Hstates Hlast].
    split; [constructor|exact Hlast]; [split; [exact Hinv|now exists next]|exact Hstates].
Qed.

Local Opaque loopN.

(** The fuel-bounded index pays for at most four transitions per listed occurrence. *)
Lemma wto_check_index_clock_from_steps g whole width :
  (forall st, wto_check_step width (listed_of g) st =
    wto_check_step (graph_width (base g)) (listed_of g) st) ->
  (forall st, (T_wto_check_step width (listed_of g) st <=
    T_wto_check_step (graph_width (base g)) (listed_of g) st)%N) ->
  (1 + T_wto_check_index (check_fuel g) width (listed_of g)
      [WtoCheckVisit whole] 0 Empty Empty [] <=
    4096 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hagrees Hsmaller.
  destruct (search_loop_trace_clock (wto_check_step width (listed_of g))
    (fun st => T_wto_check_step width (listed_of g) st)
    (check_fuel g) (WtoCheckState [WtoCheckVisit whole] 0 Empty Empty []))
    as [states [last [Hpath [Hlength Hclock]]]].
  assert (Hpath_old : search_machine_path
      (wto_check_step (graph_width (base g)) (listed_of g))
      (WtoCheckState [WtoCheckVisit whole] 0 Empty Empty []) states last).
  { clear -Hagrees Hpath. induction Hpath as [st|st next states last Hstep Hpath IH].
    - constructor.
    - econstructor; [rewrite <- Hagrees; exact Hstep|exact IH]. }
  destruct (wto_index_path g whole _ _ _ Hpath_old (wto_index_initial whole (listed_of g)))
    as [Hstates Hlast].
  assert (Hcost : forall st, In st states ->
      (T_wto_check_step width (listed_of g) st <=
        128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N).
  { intros st Hin. rewrite Forall_forall in Hstates.
    destruct (Hstates st Hin) as [Hinv [next Hstep]].
    eapply N.le_trans; [apply Hsmaller|].
    now apply (wto_check_continuing_clock g whole st next). }
  assert (Hcostall : Forall (fun st =>
    (T_wto_check_step width (listed_of g) st <=
      128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N) states).
  { apply Forall_forall. exact Hcost. }
  pose proof (search_sum_clock_bound
    (fun st => T_wto_check_step width (listed_of g) st) states
    (128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N Hcostall) as Hsum.
  pose proof (wto_check_terminal_clock g whole last Hlast) as Hterminal_old.
  assert (Hterminal : (T_wto_check_step width (listed_of g) last <=
    128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1) +
    4 * N.of_nat (graph_n (base g) + 1))%N).
  { eapply N.le_trans; [apply Hsmaller|exact Hterminal_old]. }
  pose proof (search_N_size_value (check_fuel g)) as Hbits.
  assert (Hfuel : N.to_nat (check_fuel g) = 4 * graph_n (base g) + 2).
  { unfold check_fuel. rewrite !N.double_spec. lia. }
  rewrite Hfuel in Hlength, Hbits.
  assert (HlengthN : (N.of_nat (length states) <= 4 * N.of_nat (graph_n (base g) + 1))%N)
    by lia.
  assert (Hsum_scaled :
    (fold_right N.add 0%N (map
      (fun st => T_wto_check_step width (listed_of g) st) states) <=
      512 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N).
  { eapply N.le_trans; [exact Hsum|]. clear - HlengthN. nia. }
  clear Hpath Hpath_old Hstates Hlast Hcost Hcostall Hsum Hfuel Hterminal_old.
  time_unfold @T_wto_check_index. time_cbn.
  destruct (wto_check_step width (listed_of g) last);
    rewrite !Nat2N.inj_add in *; nia.
Qed.

(** The original index call retains its public time envelope. *)
Lemma wto_check_index_clock g whole :
  (1 + T_wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit whole] 0 Empty Empty [] <=
    4096 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  apply wto_check_index_clock_from_steps; [reflexivity|].
  intro st. apply N.le_refl.
Qed.

(** Equal transitions with smaller clocks retain the frozen index allowance. *)
Lemma wto_check_index_vertices_clock g whole :
  (1 + T_wto_check_index (check_fuel g) (vertex_width (nodes g)) (listed_of g)
      [WtoCheckVisit whole] 0 Empty Empty [] <=
    4096 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  apply wto_check_index_clock_from_steps.
  - apply wto_check_step_vertices.
  - intro st. apply wto_check_step_clock_mono, vertex_width_le_graph_width.
Qed.

Local Transparent loopN.

(** Binary comparison stops at the shorter operand, so either operand bounds its cost. *)
Lemma wto_positive_compare_right p q :
  (Pos.T_compare p q <= N.of_nat (Pos.size_nat q) + 1)%N.
Proof.
  assert (Hcont : forall q p order,
    (Pos.T_compare_cont order p q <= N.of_nat (Pos.size_nat q))%N).
  { intro q0. induction q0 as [q0 IH|q0 IH|]; intros p0 order; destruct p0; time_step. }
  pose proof (Hcont q p Eq) as Htime. time_unfold @Pos.T_compare. lia.
Qed.

Lemma wto_N_leb_right a b : (N.T_leb a b <= N.of_nat (N.size_nat b) + 4)%N.
Proof.
  assert (Hcompare : (N.T_compare a b <= N.of_nat (N.size_nat b) + 2)%N).
  { destruct a as [|p], b as [|q]; time_unfold @N.T_compare; time_cbn; try lia.
    pose proof (wto_positive_compare_right p q) as Htime. lia. }
  time_unfold @N.T_leb. time_cbn. lia.
Qed.

Lemma wto_N_ltb_clock a b : (N.T_ltb a b <= N.of_nat (N.size_nat a) + 4)%N.
Proof.
  pose proof (N.T_compare_le a b) as Hcompare. time_unfold @N.T_ltb. time_cbn. lia.
Qed.

(** Comparing interval endpoints can be charged to the bounded source rank. *)
Lemma wto_interval_edge_clock width ranks intervals u v :
  Pos.size_nat u <= width -> Pos.size_nat v <= width ->
  (forall r, trie_get u ranks = Some r -> N.size_nat r <= width + 1) ->
  (T_wto_interval_edge ranks intervals u v <= 64 * N.of_nat (width + 1))%N.
Proof.
  intros Hu Hv Hrank.
  pose proof (PTrieT.T_trie_get_le N u ranks) as Hgetu.
  pose proof (PTrieT.T_trie_get_le N v ranks) as Hgetv.
  pose proof (PTrieT.T_trie_get_le (N * N) v intervals) as Hgetinterval.
  destruct (trie_get u ranks) as [ru|] eqn:Hru.
  - destruct (trie_get v ranks) as [rv|] eqn:Hrv.
    + pose proof (Hrank ru eq_refl) as Hrwidth.
      pose proof (wto_N_ltb_clock ru rv) as Hforward.
      destruct (trie_get v intervals) as [[lo hi]|] eqn:Hinterval.
      * pose proof (wto_N_leb_right lo ru) as Hlower.
        pose proof (wto_N_ltb_clock ru hi) as Hupper.
        time_unfold @T_wto_interval_edge. rewrite ?Hru, ?Hrv, ?Hinterval. time_cbn.
        rewrite ?Hgetu, ?Hgetv, ?Hgetinterval. rewrite !Nat2N.inj_add in *.
        destruct (N.ltb ru rv), (N.leb lo ru);
          unfold Datatypes.T_andb, Datatypes.T_orb; time_cbn; lia.
      * time_unfold @T_wto_interval_edge. rewrite ?Hru, ?Hrv, ?Hinterval. time_cbn.
        rewrite ?Hgetu, ?Hgetv, ?Hgetinterval. rewrite !Nat2N.inj_add in *.
        destruct (N.ltb ru rv); unfold Datatypes.T_orb; time_cbn; lia.
    + time_unfold @T_wto_interval_edge. rewrite ?Hru, ?Hrv. time_cbn.
      rewrite ?Hgetu, ?Hgetv. rewrite !Nat2N.inj_add in *. lia.
  - time_unfold @T_wto_interval_edge. rewrite ?Hru. time_cbn.
    rewrite ?Hgetu, ?Hgetv. rewrite !Nat2N.inj_add in *. lia.
Qed.

(** A list scan needs callback bounds only for its actual elements. *)
Lemma wto_forallb_clock {A} (f : A -> bool) T_f xs rate :
  Forall (fun x => (T_f x <= rate)%N) xs ->
  (List.T_forallb f T_f xs <= (rate + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; intro Hbound.
  - time_unfold @List.T_forallb. cbn [length]. lia.
  - inversion Hbound as [|x0 xs0 Hx Hrest]; subst x0 xs0. specialize (IH Hrest).
    time_unfold @List.T_forallb. time_cbn. destruct (f x); unfold Datatypes.T_andb; time_cbn;
      cbn [length]; rewrite ?Nat2N.inj_succ; nia.
Qed.

Lemma wto_listed_target_width g u v :
  In u (nodes g) -> In v (succs (base g) u) -> Pos.size_nat v <= graph_width (base g).
Proof.
  intros Hu Hv. eapply Nat.le_trans.
  - apply (search_row_width_member (base g) (nodes g) u v Hu Hv).
  - destruct g as [[vertices adjacency] predecessors n e].
    cbn [nodes base graph_width]. rewrite search_graph_max. apply Nat.le_max_r.
Qed.

(** The edge scan pays each selected source and each occurrence in its row once. *)
Lemma wto_edge_rows_clock g ranks intervals vs :
  Forall (fun u => In u (nodes g)) vs ->
  (forall u r, trie_get u ranks = Some r -> N.size_nat r <= graph_width (base g) + 1) ->
  (List.T_forallb (fun u => forallb (wto_interval_edge ranks intervals u) (succs (base g) u))
    (fun u => 1 + (T_succs (base g) u +
      List.T_forallb (wto_interval_edge ranks intervals u)
        (fun v => T_wto_interval_edge ranks intervals u v) (succs (base g) u)))%N vs <=
    256 * N.of_nat (length vs +
      fold_right (fun u n => (length (succs (base g) u) + n)%nat) 0%nat vs + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hlisted Hrank. induction Hlisted as [|u vs Hu Hlisted IH].
  - time_unfold @List.T_forallb. cbn [length fold_right]. nia.
  - assert (Hrow : Forall (fun v =>
        (T_wto_interval_edge ranks intervals u v <=
          64 * N.of_nat (graph_width (base g) + 1))%N) (succs (base g) u)).
    { apply Forall_forall. intros v Hv. apply wto_interval_edge_clock.
      - now apply scc_node_width.
      - now apply (wto_listed_target_width g u v).
      - intros r Hr. now apply (Hrank u r). }
    pose proof (wto_forallb_clock (wto_interval_edge ranks intervals u)
      (fun v => T_wto_interval_edge ranks intervals u v) (succs (base g) u)
      (64 * N.of_nat (graph_width (base g) + 1))%N Hrow) as Hinner.
    pose proof (search_succs_clock (base g) u) as Hread.
    pose proof (scc_node_width g u Hu) as Hwidth.
    time_unfold @List.T_forallb. cbn beta. time_cbn.
    destruct (forallb (wto_interval_edge ranks intervals u) (succs (base g) u));
      unfold Datatypes.T_andb; time_cbn; cbn [length fold_right];
      rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *; nia.
Qed.

(** A shared-rank edge pays only target lookups and source-width comparisons. *)
Lemma wto_interval_edge_from_clock width ranks intervals ru v :
  Pos.size_nat v <= width -> N.size_nat ru <= width + 1 ->
  (T_wto_interval_edge_from ranks intervals ru v <= 64 * N.of_nat (width + 1))%N.
Proof.
  intros Hv Hrank.
  pose proof (PTrieT.T_trie_get_le N v ranks) as Hgetv.
  pose proof (PTrieT.T_trie_get_le (N * N) v intervals) as Hgetinterval.
  destruct (trie_get v ranks) as [rv|] eqn:Hrv.
  - pose proof (wto_N_ltb_clock ru rv) as Hforward.
    destruct (N.ltb ru rv) eqn:Hforward_value.
    + time_unfold @T_wto_interval_edge_from. rewrite Hrv, Hforward_value.
      time_cbn. rewrite !Nat2N.inj_add in *. lia.
    + destruct (trie_get v intervals) as [[lo hi]|] eqn:Hinterval.
      * pose proof (wto_N_leb_right lo ru) as Hlower.
        pose proof (wto_N_ltb_clock ru hi) as Hupper.
        time_unfold @T_wto_interval_edge_from. rewrite Hrv, Hforward_value, Hinterval.
        time_cbn. rewrite !Nat2N.inj_add in *.
        destruct (N.leb lo ru); unfold Datatypes.T_andb; time_cbn; lia.
      * time_unfold @T_wto_interval_edge_from. rewrite Hrv, Hforward_value, Hinterval.
        time_cbn. rewrite !Nat2N.inj_add in *. lia.
  - time_unfold @T_wto_interval_edge_from. rewrite Hrv.
    time_cbn. rewrite !Nat2N.inj_add in *. lia.
Qed.

(** One source lookup and a successor scan fit the existing per-row allowance. *)
Lemma wto_edges_row_clock g ranks intervals u :
  In u (nodes g) ->
  (forall r, trie_get u ranks = Some r -> N.size_nat r <= graph_width (base g) + 1) ->
  (T_wto_edges_row ranks intervals (base g) u <=
    128 * N.of_nat (length (succs (base g) u) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hu Hrank.
  pose proof (PTrieT.T_trie_get_le N u ranks) as Hget.
  pose proof (search_succs_clock (base g) u) as Hread.
  pose proof (scc_node_width g u Hu) as Hwidth.
  destruct (trie_get u ranks) as [ru|] eqn:Hru.
  - assert (Hrow : Forall (fun v =>
        (T_wto_interval_edge_from ranks intervals ru v <=
          64 * N.of_nat (graph_width (base g) + 1))%N) (succs (base g) u)).
    { apply Forall_forall. intros v Hv. apply wto_interval_edge_from_clock.
      - now apply (wto_listed_target_width g u v).
      - now apply Hrank. }
    pose proof (wto_forallb_clock (wto_interval_edge_from ranks intervals ru)
      (fun v => T_wto_interval_edge_from ranks intervals ru v) (succs (base g) u)
      (64 * N.of_nat (graph_width (base g) + 1))%N Hrow) as Hinner.
    time_unfold @T_wto_edges_row. rewrite Hru. time_cbn.
    rewrite !Nat2N.inj_add in *. nia.
  - time_unfold @T_wto_edges_row. rewrite Hru. time_cbn.
    destruct (succs (base g) u); cbn [length]; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Hoisted row scans retain the old source-and-edge time envelope. *)
Lemma wto_edge_rows_from_clock g ranks intervals vs :
  Forall (fun u => In u (nodes g)) vs ->
  (forall u r, trie_get u ranks = Some r -> N.size_nat r <= graph_width (base g) + 1) ->
  (List.T_forallb (wto_edges_row ranks intervals (base g))
    (fun u => T_wto_edges_row ranks intervals (base g) u) vs <=
    256 * N.of_nat (length vs +
      fold_right (fun u n => (length (succs (base g) u) + n)%nat) 0%nat vs + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros Hlisted Hrank. induction Hlisted as [|u vs Hu Hlisted IH].
  - time_unfold @List.T_forallb. cbn [length fold_right]. nia.
  - pose proof (wto_edges_row_clock g ranks intervals u Hu (Hrank u)) as Hrow.
    time_unfold @List.T_forallb. time_cbn.
    destruct (wto_edges_row ranks intervals (base g) u);
      unfold Datatypes.T_andb; time_cbn; cbn [length fold_right];
      rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *; nia.
Qed.

(** Successful indexing limits the final scan to distinct listed rows and bounded source ranks. *)
Lemma wto_checked_edges_clock g w ranks intervals vs :
  wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
    [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
  (1 + T_wto_edges_ok (base g) ranks intervals vs <=
    512 * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intro Hindex.
  destruct (wto_check_index_seen _ _ _ _ _ _ _ Hindex) as [Hunique Hlisted].
  assert (Hincl : incl vs (nodes g)).
  { intros v Hin. apply (proj1 (scc_listed_lookup (nodes g) v)). now apply Hlisted. }
  destruct (wto_check_index_result _ _ _ _ _ _ _ Hindex)
    as [st [Hinv [Htasks [Hranks [Hintervals Hvs]]]]].
  assert (Hrank : forall u r, trie_get u ranks = Some r ->
      N.size_nat r <= graph_width (base g) + 1).
  { intros u r Hget. apply (wto_index_rank_width g w st u r Hinv).
    now rewrite Hranks. }
  assert (Hlistedall : Forall (fun u => In u (nodes g)) vs).
  { apply Forall_forall. exact Hincl. }
  pose proof (wto_edge_rows_from_clock g ranks intervals vs Hlistedall Hrank) as Hscan.
  pose proof (NoDup_incl_length Hunique Hincl) as Hvertices.
  pose proof (scc_weight_incl (fun u => length (succs (base g) u))
    vs (nodes g) Hunique Hincl) as Hrows.
  assert (Hnodecount : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  assert (Hedgecount : fold_right (fun u n => length (succs (base g) u) + n)
      0 (nodes g) = graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodecount in Hvertices. cbn beta in Hrows. rewrite Hedgecount in Hrows.
  time_unfold @T_wto_edges_ok. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** The unary maximum only reads as far as its first argument. *)
Lemma wto_graph_max_clock a b : (T_graph_max a b <= 4 * N.of_nat (a + 1))%N.
Proof.
  revert b. induction a as [|a IH]; intros [|b]; time_step.
Qed.

Lemma wto_width_value vs width :
  Forall (fun v => Pos.size_nat v <= width) vs -> vertex_width vs <= width.
Proof.
  intro Hwidth. unfold vertex_width. induction Hwidth as [|v vs Hv Hwidth IH];
    cbn [fold_right]; [lia|]. rewrite search_graph_max. lia.
Qed.

Lemma wto_fold_right_clock {A B} (f : A -> B -> B) T_f initial xs rate :
  Forall (fun x => forall acc, (T_f x acc <= rate)%N) xs ->
  (List.T_fold_right f T_f initial xs <= (rate + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intro Hbound. induction Hbound as [|x xs Hx Hbound IH].
  - time_unfold @List.T_fold_right. cbn [length]. lia.
  - specialize (Hx (fold_right f initial xs)). time_unfold @List.T_fold_right.
    time_cbn. cbn [length]. rewrite ?Nat2N.inj_succ. nia.
Qed.

(** Computing an identifier-width maximum scans each actual key once. *)
Lemma wto_vertex_width_time vs width :
  Forall (fun v => Pos.size_nat v <= width) vs ->
  (T_vertex_width vs <= 16 * N.of_nat (length vs + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth.
  assert (Hcallback : Forall (fun v => forall acc,
      (1 + (Pos.T_size_nat v + T_graph_max (Pos.size_nat v) acc) <=
        8 * N.of_nat (width + 1))%N) vs).
  { rewrite Forall_forall in *. intros v Hv acc.
    specialize (Hwidth v Hv). pose proof (Pos.T_size_nat_le v) as Hsize.
    pose proof (wto_graph_max_clock (Pos.size_nat v) acc) as Hmax.
    rewrite !Nat2N.inj_add in *. nia. }
  pose proof (wto_fold_right_clock (fun v acc => graph_max (Pos.size_nat v) acc)
    (fun v acc => 1 + (Pos.T_size_nat v + T_graph_max (Pos.size_nat v) acc))%N
    0%nat vs (8 * N.of_nat (width + 1))%N Hcallback) as Hfold.
  time_unfold @T_vertex_width. rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma wto_graph_width_occurrences b :
  Forall (fun u => Pos.size_nat u <= graph_width b /\
    Forall (fun v => Pos.size_nat v <= graph_width b) (succs b u)) (verts b).
Proof.
  destruct b as [vertices adjacency]. apply Forall_forall. intros u Hu. split.
  - eapply Nat.le_trans; [apply search_vertex_width_member; exact Hu|].
    cbn [graph_width]. rewrite search_graph_max. apply Nat.le_max_l.
  - apply Forall_forall. intros v Hv. eapply Nat.le_trans.
    + exact (search_row_width_member (Digraph vertices adjacency) vertices u v Hu Hv).
    + cbn [graph_width]. rewrite search_graph_max. apply Nat.le_max_r.
Qed.

(** Row-width computation charges source occurrences and all targets in those rows. *)
Lemma wto_width_rows_time b vs width :
  Forall (fun u => Pos.size_nat u <= width /\
    Forall (fun v => Pos.size_nat v <= width) (succs b u)) vs ->
  (List.T_fold_right (fun u acc => graph_max (vertex_width (succs b u)) acc)
    (fun u acc => 1 + ((T_succs b u + T_vertex_width (succs b u)) +
      T_graph_max (vertex_width (succs b u)) acc))%N 0%nat vs <=
    64 * N.of_nat (length vs +
      fold_right (fun u n => (length (succs b u) + n)%nat) 0%nat vs + 1) *
      N.of_nat (width + 1))%N.
Proof.
  intro Hwidth. induction Hwidth as [|u vs [Hu Hrow] Hwidth IH].
  - time_unfold @List.T_fold_right. cbn [length fold_right]. nia.
  - pose proof (search_succs_clock b u) as Hread.
    pose proof (wto_vertex_width_time (succs b u) width Hrow) as Hrowtime.
    pose proof (wto_width_value (succs b u) width Hrow) as Hrowvalue.
    pose proof (wto_graph_max_clock (vertex_width (succs b u))
      (fold_right (fun v acc => graph_max (vertex_width (succs b v)) acc) 0 vs)) as Hmax.
    time_unfold @List.T_fold_right. time_cbn. cbn [length fold_right].
    rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *. nia.
Qed.

Lemma wto_graph_width_time b :
  (T_graph_width b <= 128 * N.of_nat (graph_n b + graph_e b + 1) *
    N.of_nat (graph_width b + 1))%N.
Proof.
  pose proof (wto_graph_width_occurrences b) as Hwidth.
  assert (Hnodes : Forall (fun v => Pos.size_nat v <= graph_width b) (verts b)).
  { eapply Forall_impl; [|exact Hwidth]. intros u [Hu Hrow]. exact Hu. }
  pose proof (wto_vertex_width_time (verts b) (graph_width b) Hnodes) as Hvertices.
  pose proof (wto_width_rows_time b (verts b) (graph_width b) Hwidth) as Hrows.
  pose proof (wto_width_value (verts b) (graph_width b) Hnodes) as Hvalue.
  pose proof (wto_graph_max_clock (vertex_width (verts b))
    (fold_right (fun v acc => graph_max (vertex_width (succs b v)) acc) 0 (verts b))) as Hmax.
  destruct b as [vertices adjacency]. cbn [verts graph_n graph_e] in *.
  time_unfold @T_graph_width. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Fuel computation scans the listed vertices and converts their count once. *)
Lemma wto_check_fuel_time g : (T_check_fuel g <= 64 * N.of_nat (graph_n (base g) + 1))%N.
Proof.
  pose proof (digraph_vertex_count_time (base g)) as Hcount.
  pose proof (graph_of_nat_time (graph_n (base g))) as Hconvert.
  pose proof (search_double_clock (N.of_nat (graph_n (base g)))) as Hdouble.
  pose proof (search_double_clock (N.double (N.of_nat (graph_n (base g))))) as Htwice.
  pose proof (N.T_add_le (N.double (N.double (N.of_nat (graph_n (base g))))) 2) as Hadd.
  pose proof (search_N_size_value (N.double (N.double (N.of_nat (graph_n (base g)))))) as Hsize.
  rewrite !N2Nat.inj_double, Nat2N.id in Hsize.
  cbn [N.size_nat Pos.size_nat] in Hadd.
  time_unfold @T_check_fuel. unfold T_base. time_cbn.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Membership tables pay only their inserted keys, independently of previous bindings. *)
Lemma wto_set_members_time vs width acc :
  Forall (fun v => Pos.size_nat v <= width) vs ->
  (List.T_fold_left (fun table v => PTrieCode.set v true table)
    (fun table v => 1 + PTrieCode.T_set v true table)%N vs acc <=
    16 * (PTrieT.c_trie + 1) * N.of_nat (length vs + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth. revert acc. induction Hwidth as [|v vs Hv Hwidth IH]; intro acc.
  - time_unfold @List.T_fold_left. cbn [length]. nia.
  - specialize (IH (PTrieCode.set v true acc)).
    pose proof (PTrieT.T_set_le bool v true acc) as Hset.
    time_unfold @List.T_fold_left. time_cbn. cbn [length].
    rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *. nia.
Qed.

Lemma wto_listed_time g :
  (T_listed_of g <= 32 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
    N.of_nat (graph_width (base g) + 1))%N.
Proof.
  assert (Hwidth : Forall (fun v => Pos.size_nat v <= graph_width (base g)) (nodes g)).
  { apply Forall_forall. intros v Hv. now apply scc_node_width. }
  pose proof (wto_set_members_time (nodes g) (graph_width (base g)) Empty Hwidth) as Hfold.
  assert (Hnodecount : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
  rewrite Hnodecount in Hfold.
  time_unfold @T_listed_of. unfold T_nodes. time_cbn. nia.
Qed.

Lemma wto_presence_time {A} (table : ptrie A) vs width :
  Forall (fun v => Pos.size_nat v <= width) vs ->
  (List.T_forallb (fun v => match trie_get v table with Some _ => true | None => false end)
    (fun v => 1 + T_trie_get v table)%N vs <=
    8 * N.of_nat (length vs + 1) * N.of_nat (width + 1))%N.
Proof.
  intro Hwidth.
  assert (Hcallback : Forall (fun v => (1 + T_trie_get v table <=
      4 * N.of_nat (width + 1))%N) vs).
  { eapply Forall_impl; [|exact Hwidth]. intros v Hv.
    cbn beta in Hv.
    rewrite Nat2N.inj_add. PTrieT.trie_get_le. nia. }
  pose proof (wto_forallb_clock
    (fun v => match trie_get v table with Some _ => true | None => false end)
    (fun v => 1 + T_trie_get v table)%N vs (4 * N.of_nat (width + 1))%N Hcallback) as Hscan.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma wto_entered_time es : (T_entered es <= 4 * N.of_nat (length es + 1))%N.
Proof.
  induction es as [|e es IH]; [time_step|]. destruct e; time_step.
Qed.

Definition wto_check_work g roots : N :=
  (N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
    N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.

Definition wto_check_coefficient : N :=
  (262144 * (c_loopN + 1) * (PTrieT.c_trie + 1))%N.

Lemma wto_check_work_bounds g roots :
  (1 <= wto_check_work g roots)%N /\
  (N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
    N.of_nat (graph_width (base g) + 1) <= wto_check_work g roots)%N /\
  (N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
    N.of_nat (graph_width (base g) + 1) <= wto_check_work g roots)%N /\
  (N.of_nat (length roots + 1) * N.of_nat (vertex_width roots + 1) <=
    wto_check_work g roots)%N.
Proof.
  pose proof (Nat.le_max_l (graph_width (base g)) (vertex_width roots)) as Hgraph.
  pose proof (Nat.le_max_r (graph_width (base g)) (vertex_width roots)) as Hroots.
  unfold wto_check_work. rewrite search_graph_max. rewrite !Nat2N.inj_add in *.
  repeat split; nia.
Qed.

Lemma wto_check_coefficient_envelope :
  (2 * search_trace_coefficient + 8192 * (PTrieT.c_trie + 1) + 32768 <=
    wto_check_coefficient)%N.
Proof.
  unfold search_trace_coefficient, wto_check_coefficient. nia.
Qed.

Local Opaque loopN scc_graph scc_graph_counted prepared_search_trace wto_check_work.

(** Every checker phase is bounded on arbitrary prepared values and candidate trees. *)
Lemma wto_check_linear_time g roots w :
  (1 + T_wto_check_linear g roots w <= wto_check_coefficient * wto_check_work g roots)%N.
Proof.
  destruct (wto_check_work_bounds g roots) as [Hpositive [Hbase [Hsearchwork Hrootwork]]].
  pose proof wto_check_coefficient_envelope as Henvelope.
  pose proof (wto_listed_time g) as Hlisted0.
  pose proof (wto_presence_time (listed_of g) roots (vertex_width roots)
    (wto_vertex_width_all roots)) as Hroots0.
  assert (Hlisted : (T_listed_of g <=
      32 * (PTrieT.c_trie + 1) * wto_check_work g roots)%N).
  { eapply N.le_trans; [exact Hlisted0|]. clear - Hbase.
    rewrite !Nat2N.inj_add in *. nia. }
  assert (Hrootscan : (List.T_forallb
      (fun v => match trie_get v (listed_of g) with Some _ => true | None => false end)
      (fun v => 1 + T_trie_get v (listed_of g))%N roots <= 8 * wto_check_work g roots)%N).
  { eapply N.le_trans; [exact Hroots0|]. clear - Hrootwork. nia. }
  time_unfold @T_wto_check_linear. unfold T_nodes, T_base, T_verts.
  rewrite scc_graph_counted_agrees, wto_check_index_vertices.
  destruct (forallb
    (fun v => match trie_get v (listed_of g) with Some _ => true | None => false end) roots)
    eqn:Hroot_test.
  - assert (Hroot_listed : forall r, In r roots -> In r (nodes g)).
    { intros r Hr. rewrite forallb_forall in Hroot_test.
      specialize (Hroot_test r Hr). apply (proj1 (scc_listed_lookup (nodes g) r)).
      destruct (trie_get r (listed_of g)) as [b|] eqn:Hget; [now exists b|discriminate]. }
    pose proof (wto_check_fuel_time g) as Hfuel0.
    assert (Hnodewidth : Forall (fun v => Pos.size_nat v <= graph_width (base g)) (nodes g)).
    { apply Forall_forall. intros v Hv. now apply scc_node_width. }
    pose proof (wto_vertex_width_time (nodes g) (graph_width (base g)) Hnodewidth) as Hwidth0.
    assert (Hnodesize : length (nodes g) = graph_n (base g)).
    { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
    rewrite Hnodesize in Hwidth0.
    pose proof (wto_check_index_vertices_clock g w) as Hindex0.
    assert (Hfuel : (T_check_fuel g <= 64 * wto_check_work g roots)%N).
    { eapply N.le_trans; [exact Hfuel0|]. clear - Hbase.
      rewrite !Nat2N.inj_add in *. nia. }
    assert (Hwidth : (T_vertex_width (nodes g) <= 128 * wto_check_work g roots)%N).
    { eapply N.le_trans; [exact Hwidth0|]. clear - Hbase.
      rewrite !Nat2N.inj_add in *. nia. }
    assert (Hindex_time : (T_wto_check_index (check_fuel g) (vertex_width (nodes g))
        (listed_of g) [WtoCheckVisit w] 0 Empty Empty [] <=
        4096 * (PTrieT.c_trie + 1) * wto_check_work g roots)%N).
    { eapply N.le_trans; [apply N.le_add_l|]. eapply N.le_trans; [exact Hindex0|].
      clear - Hbase. rewrite !Nat2N.inj_add in *. nia. }
    destruct (wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty []) as [[[ranks intervals] vs]|] eqn:Hindex.
    + pose proof (scc_graph_counted_time g) as Hready0.
      pose proof (scc_search_time g roots Hroot_listed) as Hsearch0.
      destruct (scc_search_sizes g roots Hroot_listed) as [Hlive_size Hrow_size].
      pose proof (prepared_search_event_bound (scc_graph g) roots) as Hevents.
      rewrite search_event_supply_entered in Hevents.
      assert (Htrace_size : length (prepared_search_trace (scc_graph g) roots) <=
          2 * graph_n (base g) + graph_e (base g)).
      { clear - Hlive_size Hrow_size Hevents. lia. }
      assert (Hlive_width : Forall (fun v => Pos.size_nat v <= graph_width (base g))
          (entered (prepared_search_trace (scc_graph g) roots))).
      { apply Forall_forall. intros v Hv. apply scc_node_width.
        now apply (scc_search_entered g roots Hroot_listed). }
      destruct (wto_check_index_seen _ _ _ _ _ _ _ Hindex) as [Hvs_unique Hvs_listed].
      assert (Hvs_incl : incl vs (nodes g)).
      { intros v Hv. apply (proj1 (scc_listed_lookup (nodes g) v)). now apply Hvs_listed. }
      pose proof (NoDup_incl_length Hvs_unique Hvs_incl) as Hvs_size.
      assert (Hnodecount : length (nodes g) = graph_n (base g)).
      { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
      rewrite Hnodecount in Hvs_size.
      pose proof (wto_entered_time (prepared_search_trace (scc_graph g) roots)) as Hentered0.
      pose proof (Datatypes.T_length_le vs) as Hcandidate_length.
      pose proof (Datatypes.T_length_le (entered (prepared_search_trace (scc_graph g) roots)))
        as Hlive_length.
      pose proof (Nat.T_leb_le (length vs)
        (length (entered (prepared_search_trace (scc_graph g) roots)))) as Hcomparison.
      pose proof (wto_presence_time ranks (entered (prepared_search_trace (scc_graph g) roots))
        (graph_width (base g)) Hlive_width) as Hreverse0.
      pose proof (wto_checked_edges_clock g w ranks intervals vs Hindex) as Hedges0.
      assert (Hready : (T_scc_graph_counted g <= 16384 * wto_check_work g roots)%N).
      { eapply N.le_trans; [exact Hready0|]. clear - Hbase. nia. }
      assert (Hsearch : (T_prepared_search_trace (scc_graph g) roots <=
          2 * search_trace_coefficient * wto_check_work g roots)%N).
      { eapply N.le_trans; [apply N.le_add_l|]. eapply N.le_trans; [exact Hsearch0|].
        clear - Hsearchwork. nia. }
      assert (Hentered : (T_entered (prepared_search_trace (scc_graph g) roots) <=
          8 * wto_check_work g roots)%N).
      { eapply N.le_trans; [exact Hentered0|]. clear - Htrace_size Hbase.
        rewrite !Nat2N.inj_add in *. nia. }
      assert (Hcover : (Datatypes.T_length vs +
          Datatypes.T_length (entered (prepared_search_trace (scc_graph g) roots)) +
          Nat.T_leb (length vs) (length (entered (prepared_search_trace (scc_graph g) roots))) <=
          8 * wto_check_work g roots)%N).
      { clear - Hcandidate_length Hlive_length Hcomparison Hvs_size Hlive_size Hbase.
        rewrite !Nat2N.inj_add in *. nia. }
      assert (Hreverse : (List.T_forallb
          (fun v => match trie_get v ranks with Some _ => true | None => false end)
          (fun v => 1 + T_trie_get v ranks)%N
          (entered (prepared_search_trace (scc_graph g) roots)) <=
          8 * wto_check_work g roots)%N).
      { eapply N.le_trans; [exact Hreverse0|]. clear - Hlive_size Hbase.
        rewrite !Nat2N.inj_add in *. nia. }
      assert (Hedges : (T_wto_edges_ok (base g) ranks intervals vs <=
          512 * wto_check_work g roots)%N).
      { eapply N.le_trans; [apply N.le_add_l|]. eapply N.le_trans; [exact Hedges0|].
        clear - Hbase. nia. }
      clear - g roots w ranks intervals vs Hpositive Henvelope Hlisted Hrootscan
        Hfuel Hwidth Hindex_time Hready Hsearch Hentered Hcover Hreverse Hedges.
      time_cbn.
      destruct (Nat.leb (length vs)
        (length (entered (prepared_search_trace (scc_graph g) roots))));
      destruct (forallb (fun v => match trie_get v ranks with Some _ => true | None => false end)
        (entered (prepared_search_trace (scc_graph g) roots)));
        time_cbn; nia.
    + clear - Hpositive Henvelope Hlisted Hrootscan Hfuel Hwidth Hindex_time.
      time_cbn. nia.
  - clear - Hpositive Henvelope Hlisted Hrootscan. time_cbn. nia.
Qed.

Local Transparent loopN scc_graph scc_graph_counted prepared_search_trace wto_check_work.


(** Every enclosed vertex occurs in the structural order of its containing tree. *)
Lemma wto_enclosed_vertex_member h v w :
  wto_encloses h v w -> In v (wto_order w).
Proof.
  intro Henclosed. induction Henclosed; cbn [wto_order].
  - destruct H as [Heq|Hin].
    + subst v. now left.
    + right. apply in_or_app. now left.
  - now right.
  - right. apply in_or_app. now left.
  - right. apply in_or_app. now right.
Qed.

(** A unique concatenation has disjoint left and right inventories. *)
Local Lemma wto_interval_disjoint {A} (first rest : list A) v :
  NoDup (first ++ rest) -> In v first -> ~ In v rest.
Proof.
  induction first as [|x first IH]; [contradiction|].
  cbn [app]. intro Hunique. inversion Hunique as [|? ? Hfresh Htail]; subst.
  intros [Heq|Hin] Hrest.
  - subst x. apply Hfresh. apply in_or_app. now right.
  - exact (IH Htail Hin Hrest).
Qed.

(** Every structural subtree inherits the candidate's unique vertex inventory. *)
Local Lemma wto_interval_subtree_unique whole tree :
  wto_subtree whole tree -> NoDup (wto_order whole) -> NoDup (wto_order tree).
Proof.
  intro Htree. induction Htree; intro Hunique; [exact Hunique| | |].
  - specialize (IHHtree Hunique). inversion IHHtree. assumption.
  - specialize (IHHtree Hunique). inversion IHHtree as [|? ? Hfresh Htail].
    now apply NoDup_app_remove_r in Htail.
  - specialize (IHHtree Hunique). inversion IHHtree as [|? ? Hfresh Htail].
    now apply NoDup_app_remove_l in Htail.
Qed.

Local Lemma wto_interval_vertex_head v tail h :
  NoDup (wto_order (WVertex v tail)) -> ~ wto_encloses h v (WVertex v tail).
Proof.
  intros Hunique Henclosed. cbn [wto_order] in Hunique.
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  inversion Henclosed as [inside rest Hmember|head rest Hinside|
    head inside rest Hinside|head inside rest Hinside]; subst.
  apply Hfresh. exact (wto_enclosed_vertex_member _ _ _ Hinside).
Qed.

Local Lemma wto_interval_loop_head h body tail k :
  NoDup (wto_order (WLoop h body tail)) -> wto_encloses k h (WLoop h body tail) -> k = h.
Proof.
  intros Hunique Henclosed. cbn [wto_order] in Hunique.
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  inversion Henclosed as [inside rest Hmember|head rest Hinside|
    head inside rest Hinside|head inside rest Hinside]; subst; [reflexivity| |].
  - exfalso. apply Hfresh. apply in_or_app. left.
    exact (wto_enclosed_vertex_member _ _ _ Hinside).
  - exfalso. apply Hfresh. apply in_or_app. right.
    exact (wto_enclosed_vertex_member _ _ _ Hinside).
Qed.

Local Lemma wto_interval_loop_body h body tail k u :
  NoDup (wto_order (WLoop h body tail)) -> In u (wto_order body) ->
  wto_encloses k u (WLoop h body tail) -> k = h \/ wto_encloses k u body.
Proof.
  intros Hunique Hu Henclosed. cbn [wto_order] in Hunique.
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  inversion Henclosed as [inside rest Hmember|head rest Hinside|
    head inside rest Hinside|head inside rest Hinside]; subst; [now left|now right|].
  exfalso. apply (wto_interval_disjoint (wto_order body) (wto_order tail) u Htail Hu).
  exact (wto_enclosed_vertex_member _ _ _ Hinside).
Qed.

Local Lemma wto_interval_loop_rest h body tail k u :
  NoDup (wto_order (WLoop h body tail)) -> In u (wto_order tail) ->
  wto_encloses k u (WLoop h body tail) -> wto_encloses k u tail.
Proof.
  intros Hunique Hu Henclosed. cbn [wto_order] in Hunique.
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  inversion Henclosed as [inside rest Hmember|head rest Hinside|
    head inside rest Hinside|head inside rest Hinside]; subst; [| |exact Hinside].
  - destruct Hmember as [Heq|Hin].
    + subst u. exfalso. apply Hfresh. apply in_or_app. now right.
    + exfalso. exact (wto_interval_disjoint _ _ _ Htail Hin Hu).
  - exfalso. apply (wto_interval_disjoint (wto_order body) (wto_order tail) u Htail).
    + exact (wto_enclosed_vertex_member _ _ _ Hinside).
    + exact Hu.
Qed.

(** Enclosure of a future vertex is internal to its visit or awaits a later close. *)
Fixpoint wto_interval_cover (whole : wto) (tasks : list wto_check_task) : Prop :=
  match tasks with
  | [] => True
  | WtoCheckVisit tree :: rest =>
      (forall h u, In u (wto_order tree) -> wto_encloses h u whole ->
        wto_encloses h u tree \/ In (WtoCheckClose h) rest) /\
      wto_interval_cover whole rest
  | WtoCheckClose _ :: rest => wto_interval_cover whole rest
  end.

Local Lemma wto_interval_cover_vertex whole v tail tasks :
  wto_interval_cover whole (WtoCheckVisit (WVertex v tail) :: tasks) ->
  wto_interval_cover whole (WtoCheckVisit tail :: tasks).
Proof.
  intros [Hcover Hrest]. split; [|exact Hrest].
  intros h u Hu Henclosed. destruct (Hcover h u (or_intror Hu) Henclosed) as [Hinside|Hclose].
  - left. inversion Hinside; assumption.
  - now right.
Qed.

Local Lemma wto_interval_cover_loop whole h body tail tasks :
  NoDup (wto_order (WLoop h body tail)) ->
  wto_interval_cover whole (WtoCheckVisit (WLoop h body tail) :: tasks) ->
  wto_interval_cover whole
    (WtoCheckVisit body :: WtoCheckClose h :: WtoCheckVisit tail :: tasks).
Proof.
  intros Hunique [Hcover Hrest]. split.
  - intros k u Hu Henclosed.
    assert (Hu_parent : In u (wto_order (WLoop h body tail))).
    { right. apply in_or_app. now left. }
    destruct (Hcover k u Hu_parent Henclosed) as [Hinside|Hclose].
    + destruct (wto_interval_loop_body h body tail k u Hunique Hu Hinside) as [Heq|Hbody].
      * subst k. right. now left.
      * now left.
    + right. now right; right.
  - split; [|exact Hrest]. intros k u Hu Henclosed.
    assert (Hu_parent : In u (wto_order (WLoop h body tail))).
    { right. apply in_or_app. now right. }
    destruct (Hcover k u Hu_parent Henclosed) as [Hinside|Hclose].
    + left. exact (wto_interval_loop_rest h body tail k u Hunique Hu Hinside).
    + now right.
Qed.

(** Every emitted enclosed vertex is covered by an active close or a stored interval. *)
Definition wto_interval_seen (whole : wto) (s : wto_check_state) : Prop :=
  forall h u ru, trie_get u (wto_check_ranks s) = Some ru -> wto_encloses h u whole ->
  exists lo, trie_get h (wto_check_ranks s) = Some lo /\ (lo <= ru)%N /\
    (In (WtoCheckClose h) (wto_check_tasks s) \/
      exists hi, trie_get h (wto_check_intervals s) = Some (lo, hi) /\ (ru < hi)%N).

Local Lemma wto_interval_rank_bound whole listed s u ru :
  wto_index_invariant whole listed s -> trie_get u (wto_check_ranks s) = Some ru ->
  (ru < wto_check_next s)%N.
Proof.
  intros Hinv Hget. destruct Hinv as [_ Hnext _ Hranks _ _ _ _].
  destruct (Hranks u ru Hget) as [i [Hi [Hr Hbound]]].
  rewrite Hr, Hnext. lia.
Qed.

(** Emitting a vertex preserves existing ranges and records all of its enclosing heads. *)
Local Lemma wto_interval_seen_emit whole listed tasks next ranks intervals vs v tasks' :
  wto_index_invariant whole listed (WtoCheckState tasks next ranks intervals vs) ->
  wto_interval_seen whole (WtoCheckState tasks next ranks intervals vs) ->
  trie_get v ranks = None ->
  (forall h, In (WtoCheckClose h) tasks -> In (WtoCheckClose h) tasks') ->
  (forall h, wto_encloses h v whole ->
    (h = v /\ In (WtoCheckClose h) tasks') \/ In (WtoCheckClose h) tasks) ->
  wto_interval_seen whole
    (WtoCheckState tasks' (N.succ next) (PTrieCode.set v next ranks) intervals (v :: vs)).
Proof.
  intros Hinv Hseen Hfresh Hcloses Hnew.
  unfold wto_interval_seen in Hseen |- *.
  cbn [wto_check_ranks wto_check_tasks wto_check_intervals] in Hseen |- *.
  intros h u ru Hget Henclosed.
  destruct (wto_get_set_cases N ranks v next u ru Hget) as [[Heq Hr]|[Hdifferent Hold]].
  - subst u ru. destruct (Hnew h Henclosed) as [[Heq Hclose]|Hclose].
    + subst h. exists next. split; [apply PTrie.get_set_same|].
      split; [reflexivity|now left].
    + destruct (@index_active whole listed _ Hinv h Hclose) as [lo [Hlo Hinside]].
      cbn [wto_check_ranks] in Hlo.
      assert (Hne : h <> v) by (intro Heq; subst h; congruence).
      pose proof (wto_interval_rank_bound whole listed _ h lo Hinv Hlo) as Hbound.
      cbn [wto_check_next] in Hbound. exists lo. split.
      * now rewrite PTrie.get_set_other by exact Hne.
      * split; [now apply N.lt_le_incl|]. left. now apply Hcloses.
  - destruct (Hseen h u ru Hold Henclosed) as [lo [Hlo [Hrange Hcover]]].
    assert (Hne : h <> v) by (intro Heq; subst h; congruence).
    exists lo. split; [now rewrite PTrie.get_set_other by exact Hne|].
    split; [exact Hrange|]. destruct Hcover as [Hclose|Hclosed]; [left; now apply Hcloses|now right].
Qed.

(** Closing a loop replaces its active coverage by the interval ending at the next rank. *)
Local Lemma wto_interval_seen_close whole listed tasks next ranks intervals vs h start :
  wto_index_invariant whole listed
    (WtoCheckState (WtoCheckClose h :: tasks) next ranks intervals vs) ->
  wto_interval_seen whole
    (WtoCheckState (WtoCheckClose h :: tasks) next ranks intervals vs) ->
  trie_get h ranks = Some start ->
  wto_interval_seen whole
    (WtoCheckState tasks next ranks (PTrieCode.set h (start, next) intervals) vs).
Proof.
  intros Hinv Hseen Hstart. unfold wto_interval_seen in Hseen |- *.
  cbn [wto_check_ranks wto_check_tasks wto_check_intervals] in Hseen |- *.
  intros head u ru Hget Henclosed.
  destruct (Hseen head u ru Hget Henclosed) as [lo [Hlo [Hrange Hcover]]].
  destruct (Pos.eq_dec head h) as [Heq|Hne].
  - subst head. assert (lo = start) by congruence. subst lo.
    exists start. split; [exact Hstart|]. split; [exact Hrange|]. right.
    exists next. split; [apply PTrie.get_set_same|].
    exact (wto_interval_rank_bound whole listed _ u ru Hinv Hget).
  - exists lo. split; [exact Hlo|]. split; [exact Hrange|].
    destruct Hcover as [[Heq|Hclose]|[hi [Hinterval Hbound]]].
    + injection Heq as Heq. congruence.
    + now left.
    + right. exists hi. split; [now rewrite PTrie.get_set_other by exact Hne|exact Hbound].
Qed.

Definition wto_interval_invariant whole listed s : Prop :=
  wto_index_invariant whole listed s /\ wto_interval_cover whole (wto_check_tasks s) /\
    wto_interval_seen whole s.

Definition wto_interval_result whole listed
    (result : option (ptrie N * ptrie (N * N) * list positive)) : Prop :=
  match result with
  | None => True
  | Some (ranks, intervals, vs) => exists s,
      wto_interval_invariant whole listed s /\ wto_check_tasks s = [] /\
      wto_check_ranks s = ranks /\ wto_check_intervals s = intervals /\
      rev (wto_check_vertices s) = vs
  end.

Local Lemma wto_interval_seen_tasks whole tasks tasks' next ranks intervals vs :
  (forall h, In (WtoCheckClose h) tasks -> In (WtoCheckClose h) tasks') ->
  wto_interval_seen whole (WtoCheckState tasks next ranks intervals vs) ->
  wto_interval_seen whole (WtoCheckState tasks' next ranks intervals vs).
Proof.
  intros Htasks Hseen. unfold wto_interval_seen in Hseen |- *.
  cbn [wto_check_ranks wto_check_tasks wto_check_intervals] in Hseen |- *.
  intros h u ru Hget Henclosed. destruct (Hseen h u ru Hget Henclosed) as [lo [Hlo [Hrange Hcover]]].
  exists lo. split; [exact Hlo|]. split; [exact Hrange|].
  destruct Hcover; [left; now apply Htasks|now right].
Qed.

(** Successful index transitions retain complete enclosure coverage. *)
Lemma wto_interval_step whole width listed s :
  NoDup (wto_order whole) -> wto_interval_invariant whole listed s ->
  match wto_check_step width listed s with
  | inl next => wto_interval_invariant whole listed next
  | inr result => wto_interval_result whole listed result
  end.
Proof.
  intros Hunique [Hinv [Hcover Hseen]].
  pose proof (wto_index_step whole width listed s Hinv) as Hchecked.
  destruct s as [tasks next ranks intervals vs].
  cbn [wto_check_tasks] in Hcover.
  destruct tasks as [|task tasks].
  - cbn [wto_check_step wto_interval_result].
    exists (WtoCheckState [] next ranks intervals vs). split.
    + split; [exact Hinv|]. now split.
    + repeat split; try reflexivity. now rewrite rev_append_rev, app_nil_r.
  - destruct task as [tree|h].
    + destruct tree as [|v tail|h body tail].
      * cbn [wto_check_step] in Hchecked |- *. split; [exact Hchecked|].
        split; [exact (proj2 Hcover)|].
        eapply wto_interval_seen_tasks; [|exact Hseen].
        intros head [Heq|Hin]; [discriminate|exact Hin].
      * cbn [wto_check_step] in Hchecked |- *.
        destruct (wto_key_fits width v); [|exact I].
        destruct (trie_get v listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get v ranks) as [r|] eqn:Hfresh; [exact I|].
        split; [exact Hchecked|]. split.
        -- now apply wto_interval_cover_vertex in Hcover.
        -- eapply wto_interval_seen_emit; [exact Hinv|exact Hseen|exact Hfresh| |].
           ++ intros head [Heq|Hin]; [discriminate|]. now right.
           ++ intros head Henclosed.
              destruct (proj1 Hcover head v (or_introl eq_refl) Henclosed) as [Hinside|Hclose].
              ** exfalso. apply (wto_interval_vertex_head v tail head); [|exact Hinside].
                 apply (wto_interval_subtree_unique whole _); [|exact Hunique].
                 apply (@index_origins whole listed _ Hinv). now left.
              ** right. now right.
      * cbn [wto_check_step] in Hchecked |- *.
        destruct (wto_key_fits width h); [|exact I].
        destruct (trie_get h listed) as [b|] eqn:Hlisted; [|exact I].
        destruct (trie_get h ranks) as [r|] eqn:Hfresh; [exact I|].
        assert (Hcurrent : NoDup (wto_order (WLoop h body tail))).
        { apply (wto_interval_subtree_unique whole _); [|exact Hunique].
          apply (@index_origins whole listed _ Hinv). now left. }
        split; [exact Hchecked|]. split.
        -- now apply wto_interval_cover_loop.
        -- eapply wto_interval_seen_emit; [exact Hinv|exact Hseen|exact Hfresh| |].
           ++ intros head [Heq|Hin]; [discriminate|]. now right; right; right.
           ++ intros head Henclosed.
              destruct (proj1 Hcover head h (or_introl eq_refl) Henclosed) as [Hinside|Hclose].
              ** left. split; [exact (wto_interval_loop_head h body tail head Hcurrent Hinside)|].
                 assert (head = h) by exact (wto_interval_loop_head h body tail head Hcurrent Hinside).
                 subst head. now right; left.
              ** right. now right.
    + cbn [wto_check_step] in Hchecked |- *.
      destruct (trie_get h ranks) as [lo|] eqn:Hlo; [|exact I].
      split; [exact Hchecked|]. split; [exact Hcover|].
      eapply wto_interval_seen_close; eassumption.
Qed.

(** The empty index has no emitted enclosure obligation. *)
Lemma wto_interval_initial whole listed :
  wto_interval_invariant whole listed
    (WtoCheckState [WtoCheckVisit whole] 0 Empty Empty []).
Proof.
  split; [apply wto_index_initial|]. split.
  - split; [intros h u Hu Henclosed; now left|exact I].
  - intros h u ru Hget Henclosed. cbn [wto_check_ranks] in Hget.
    rewrite PTrie.get_empty in Hget. discriminate.
Qed.

Local Lemma wto_interval_loop whole width listed fuel :
  forall s, NoDup (wto_order whole) -> wto_interval_invariant whole listed s ->
  match loop_fuel (wto_check_step width listed) fuel s with
  | inl _ => True
  | inr result => wto_interval_result whole listed result
  end.
Proof.
  induction fuel as [|fuel IH]; intros s Hunique Hinv; [exact I|].
  cbn [loop_fuel]. pose proof (wto_interval_step whole width listed s Hunique Hinv) as Hstep.
  destruct (wto_check_step width listed s) as [next|result].
  - apply IH; assumption.
  - exact Hstep.
Qed.

Local Opaque loopN.

Lemma wto_interval_run whole fuel width listed s :
  NoDup (wto_order whole) -> wto_interval_invariant whole listed s ->
  match loopN (wto_check_step width listed) fuel s with
  | inl _ => True
  | inr result => wto_interval_result whole listed result
  end.
Proof.
  rewrite search_loopN_fuel. apply wto_interval_loop.
Qed.

(** Every structural enclosure is represented by the successful numeric interval index. *)
Lemma wto_check_index_complete_intervals fuel width listed w ranks intervals vs :
  wto_check_index fuel width listed [WtoCheckVisit w] 0 Empty Empty [] =
    Some (ranks, intervals, vs) ->
  forall h u, wto_encloses h u w ->
    exists lo hi ru, trie_get h intervals = Some (lo, hi) /\
      trie_get u ranks = Some ru /\ (lo <= ru < hi)%N.
Proof.
  intro Hindex.
  destruct (wto_check_index_spec fuel width listed w ranks intervals vs Hindex)
    as [Hunique [Horder [Hdomain Hedge]]].
  pose proof (wto_interval_run w fuel width listed
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty []) Hunique
    (wto_interval_initial w listed)) as Hresult.
  unfold wto_check_index in Hindex.
  destruct (loopN (wto_check_step width listed) fuel
    (WtoCheckState [WtoCheckVisit w] 0 Empty Empty [])) as [s|result]; [discriminate|].
  destruct result as [[[ranks' intervals'] vs']|]; [|discriminate].
  inversion Hindex; subst.
  destruct Hresult as [[tasks next ranks' intervals' seen]
    [[Hinv [Hcover Hseen]] [Htasks [Hranks [Hintervals Hvs]]]]].
  cbn [wto_check_tasks wto_check_ranks wto_check_intervals wto_check_vertices] in *.
  subst tasks ranks' intervals'.
  intros h u Henclosed.
  destruct (proj2 (Hdomain u) (wto_enclosed_vertex_member h u w Henclosed)) as [ru Hru].
  destruct (Hseen h u ru Hru Henclosed) as [lo [Hlo [Hlower [Hactive|[hi [Hinterval Hupper]]]]]].
  - contradiction.
  - exists lo, hi, ru. auto.
Qed.

Local Transparent loopN.

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

  Local Opaque loopN.

  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Lemma check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  Proof.
    intros g roots w Hcheck. apply (wto_check_sound_from_reach g roots w); [|exact Hcheck].
    apply prepared_search_reach_closed.
    - apply scc_graph_counts.
    - intros u v Hu Hedge. rewrite scc_graph_nodes. now apply (scc_graph_closed g u).
    - intros r Hin. rewrite scc_graph_nodes. exact (wto_check_roots g roots w Hcheck r Hin).
  Qed.

  Local Transparent loopN.

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
  Definition c_wto : N :=
    let b := (128 * (SccT.c_scc + DigraphT.c_prepare + SccT.k_callback +
      search_trace_coefficient + 16384 + 8 * (PTrieT.c_trie + 1)))%N in
    (4096 * b * b + 262144 * (c_loopN + 1) * (PTrieT.c_trie + 1) +
      PTrieT.c_trie + 8)%N.

  (** The common coefficient retains both structural projection bounds. *)
  Lemma c_wto_projection : (PTrieT.c_trie + 8 <= c_wto)%N.
  Proof.
    unfold c_wto. lia.
  Qed.

  Lemma c_wto_check_coefficient : (wto_check_coefficient <= c_wto)%N.
  Proof.
    unfold c_wto, wto_check_coefficient. lia.
  Qed.

  Local Opaque loopN.

  Lemma T_check_le : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    intros g roots w. pose proof (wto_check_linear_time g roots w) as Hcheck.
    time_unfold @T_check.
    eapply N.le_trans; [exact Hcheck|].
    unfold wto_check_work. rewrite <- N.mul_assoc.
    apply N.mul_le_mono_r. exact c_wto_check_coefficient.
  Qed.

  Lemma T_heads_le : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof.
    intro w. pose proof (wto_heads_into_clock w []) as Hheads.
    pose proof c_wto_projection as Hcoefficient. time_step.
  Qed.

  Lemma T_ranks_le : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof.
    intro w. pose proof (wto_order_into_clock w []) as Horder.
    pose proof (wto_rank_rows_one_clock (wto_order w)) as Hrows.
    pose proof c_wto_projection as Hcoefficient. time_unfold @T_ranks.
    rewrite (proj2 (wto_into_spec w [])), app_nil_r. time_cbn.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma heads_bigO : bigO (fun _ : wto => True)
    (fun w => N.of_nat (length (wto_order w))) T_heads.
  Proof.
    exists c_wto. intros w _.
    eapply N.le_trans; [apply T_heads_le|].
    rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma ranks_bigO : bigO (fun _ : wto => True)
    (fun w => N.of_nat ((length (wto_order w) + 1) *
      (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1)))
    T_ranks.
  Proof.
    exists c_wto. intros w _.
    eapply N.le_trans; [apply T_ranks_le|].
    rewrite Nat2N.inj_mul. nia.
  Qed.

  Lemma check_bigO : bigO (fun _ : prepared * list positive * wto => True)
    (fun '(g, roots, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots, w) => T_check g roots w).
  Proof.
    exists c_wto. intros [[g roots] w] _.
    eapply N.le_trans; [apply T_check_le|].
    rewrite Nat2N.inj_mul. nia.
  Qed.

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

  Definition k_member : N := 4%N.
  Definition k_index : N := (4096 * (PTrieT.c_trie + 1))%N.
  Definition k_check : N := 512%N.
  Definition k_build : N :=
    (128 * (SccT.c_scc + DigraphT.c_prepare + SccT.k_callback +
      search_trace_coefficient + 16384 + 8 * (PTrieT.c_trie + 1)))%N.
  Definition k_scope : N := (2 * k_build)%N.
  Definition k_expand : N := 32%N.
  Definition k_heads : N := 1%N.
  Definition k_ranks : N := (PTrieT.c_trie + 4)%N.

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
  Proof.
    intros w Hunique. split; [apply wto_annotation_order|].
    now apply wto_annotation_spec.
  Qed.

  Lemma F3_index : forall w, NoDup (wto_order w) -> index_correct w.
  Proof.
    intros w Hunique u. unfold checked_index.
    destruct (wto_positions_spec (wto_annotate [] w)
      ltac:(rewrite wto_annotation_order; exact Hunique) u) as [Habsent Hpresent].
    rewrite wto_annotation_order in Habsent. split; [exact Habsent|].
    intros after stack Hget. destruct (Hpresent after stack Hget) as [Hin Hafter].
    split.
    - rewrite <- (wto_annotation_order w []). exact (in_map fst _ _ Hin).
    - split.
      + now rewrite wto_annotation_order in Hafter.
      + now apply wto_annotation_spec.
  Qed.

  (** Acceptance also establishes every clause of the plan's annotation-based predicate. *)
  Lemma wto_checked_from_acceptance g roots w :
    check g roots w = true -> checked g roots w.
  Proof.
    intro Hcheck. pose proof (Wto.check_sound g roots w Hcheck) as Hsound.
    destruct Hsound as [Hunique [Hcover Hedges]].
    pose proof Hcheck as Hindex. change (wto_check_linear g roots w = true) in Hindex.
    rewrite wto_check_linear_agrees in Hindex. unfold wto_check_linear_spec in Hindex.
    destruct (forallb (fun v => match trie_get v (listed_of g) with
      Some _ => true | None => false end) roots); [|discriminate].
    destruct (Galois.Graph.Wto.wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty []) as [[[ranks intervals] vs]|] eqn:Hindexed;
      [|discriminate].
    destruct (wto_check_index_spec _ _ _ _ _ _ _ Hindexed) as [_ [Hvs _]].
    destruct (wto_check_index_seen _ _ _ _ _ _ _ Hindexed) as [_ Hlisted].
    unfold checked. split; [now apply wto_check_roots with (w := w)|].
    split.
    - intros v Hin. apply (proj1 (scc_listed_lookup (nodes g) v)). apply Hlisted.
      now rewrite Hvs.
    - split; [exact Hunique|]. split.
      + intro v. unfold live, search_trace. rewrite search_trace_reach_raw.
        apply Hcover.
      + intros u v Hu Hedge. apply (proj2 (wto_positions_edge_spec w u v Hunique Hu)).
        apply Hedges; [exact Hedge|now apply Hcover].
  Qed.

  (** Completeness reduces to storing every structural enclosure in the numeric index. *)
  Lemma wto_checked_acceptance_from_intervals g roots w :
    (forall ranks intervals vs,
      wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
        [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
      forall h u, wto_encloses h u w ->
        exists lo hi ru, trie_get h intervals = Some (lo, hi) /\
          trie_get u ranks = Some ru /\ (lo <= ru < hi)%N) ->
    checked g roots w -> check g roots w = true.
  Proof.
    intros Hcomplete [Hroots [Hlisted [Hunique [Hlive Hedges]]]].
    destruct (wto_check_index_listed_complete g w Hunique Hlisted)
      as [ranks [intervals [vs Hindex]]].
    apply (wto_check_from_coverage g roots w ranks intervals vs);
      [exact Hroots|exact Hlisted| |exact Hindex|].
    - intro v. specialize (Hlive v). unfold live, search_trace in Hlive.
      now rewrite search_trace_reach_raw in Hlive.
    - intros u v Hu Hedge.
      pose proof (proj1 (wto_positions_edge_spec w u v Hunique Hu)
        (Hedges u v Hu Hedge)) as Hlegal.
      destruct Hlegal as [Hforward|Hencloses].
      + now apply (wto_check_index_forward _ _ _ _ _ _ _ _ _ Hindex).
      + destruct (Hcomplete ranks intervals vs Hindex v u Hencloses)
          as [lo [hi [ru [Hinterval [Huget Hbounds]]]]].
        destruct (wto_check_index_spec _ _ _ _ _ _ _ Hindex) as [_ [_ [Hdomain Hsound]]].
        destruct (proj2 (Hdomain v) (proj2 (wto_encloses_member w v u Hencloses)))
          as [rv Hvget].
        unfold Galois.Graph.Wto.wto_interval_edge. rewrite Huget, Hvget, Hinterval.
        apply orb_true_iff. right. apply andb_true_iff. split.
        * apply N.leb_le. exact (proj1 Hbounds).
        * apply N.ltb_lt. exact (proj2 Hbounds).
  Qed.

  Lemma F4_check : forall g roots w, check g roots w = true <-> checked g roots w.
  Proof.
    intros g roots w. split.
    - exact (wto_checked_from_acceptance g roots w).
    - intro Hchecked. apply (wto_checked_acceptance_from_intervals g roots w).
      + intros ranks intervals vs Hindex h u Hencloses.
        eapply wto_check_index_complete_intervals; eassumption.
      + exact Hchecked.
  Qed.


  Lemma F5_live : forall g roots v, In v (live g roots) <-> reach (base g) roots v.
  Proof.
    intros g roots v. unfold live, search_trace. apply search_trace_reach_raw.
  Qed.

  Lemma F6_sound : forall g roots w, check g roots w = true -> is_wto g roots w.
  Proof.
    apply check_sound.
  Qed.

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



  (** Reversing component order preserves the multiset of all component vertices. *)
  Lemma components_reverse : forall (cs : list (list positive)),
    Permutation (concat cs) (concat (rev cs)).
  Proof.
    intro cs. change (Permutation (flat_map (fun c : list positive => c) cs)
      (flat_map (fun c : list positive => c) (rev cs))).
    apply Permutation_flat_map. apply Permutation_rev.
  Qed.

  (** Expansion tasks retain their component lists without creating close tasks. *)
  Lemma expand_inventory : forall within entries owners cs,
    concat (map task_members (wto_expand_tasks within entries owners cs)) = concat cs /\
    fold_right (fun task hs =>
      match task with WtoClose h => h :: hs | _ => hs end) []
      (wto_expand_tasks within entries owners cs) = [] /\
    filter (fun task => match task with WtoClose _ => true | _ => false end)
      (wto_expand_tasks within entries owners cs) = [].
  Proof.
    intros within entries owners cs.
    change (wto_expand_tasks within entries owners cs) with
      (map (fun c => WtoExpand within entries owners c) cs).
    induction cs as [|c rest IH].
    - repeat split; reflexivity.
    - destruct IH as [Hmembers [Hheads Hcloses]].
      cbn [map task_members concat fold_right filter] in *.
      now rewrite Hmembers, Hheads, Hcloses.
  Qed.

  (** Initial expansion tasks account for every vertex and suspend no parent. *)
  Lemma expanded_initial_inventory : forall within entries owners cs,
    inventory (concat cs)
      (WtoState (wto_expand_tasks within entries owners (rev cs)) WNil []).
  Proof.
    intros within entries owners cs.
    destruct (expand_inventory within entries owners (rev cs))
      as [Hmembers [Hheads Hcloses]].
    unfold inventory. cbn [wto_tasks wto_partial wto_parents wto_order].
    rewrite Hmembers, Hheads, Hcloses. cbn [map concat app length]. rewrite app_nil_r.
    split; [apply components_reverse|reflexivity].
  Qed.

  (** Pending expansion credit is three units per component vertex. *)
  Lemma expand_potential : forall g within entries owners cs partial parents,
    potential g (WtoState (wto_expand_tasks within entries owners cs) partial parents) =
      3 * length (concat cs).
  Proof.
    intros g within entries owners cs partial parents.
    unfold potential. cbn [wto_tasks].
    change (wto_expand_tasks within entries owners cs) with
      (map (fun c => WtoExpand within entries owners c) cs).
    induction cs as [|c rest IH].
    - reflexivity.
    - cbn [map fold_right task_mass concat] in *.
      rewrite IH, length_app. lia.
  Qed.

  Lemma F14_initial : forall g roots,
    invariant g roots (initial g roots) /\
    potential g (initial g roots) = 3 * length (concat (comps (wto_components g roots))).
  Proof.
    intros g roots. split.
    - split.
      + exists 0. reflexivity.
      + unfold initial. apply expanded_initial_inventory.
    - unfold initial. rewrite expand_potential.
      rewrite <- (Permutation_length (components_reverse (comps (wto_components g roots)))).
      reflexivity.
  Qed.



  Local Opaque loopN.

  Lemma F16_done : forall g roots,
    exists w, loopN (wto_step g)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots) = inr w.
  Proof.
    intros g roots. rewrite search_loopN_fuel, Nat2N.id.
    apply wto_fuel_complete.
    - unfold initial. cbn [wto_tasks]. apply wto_expand_nonempty.
      apply Forall_rev. apply wto_components_nonempty.
    - change (potential g (initial g roots) <
        3 * length (concat (comps (wto_components g roots))) + 1).
      rewrite (proj2 (F14_initial g roots)). lia.
  Qed.

  Local Transparent loopN.

  (** Every recorded history starts at its supplied state. *)
  Lemma history_from_head : forall g fuel st,
    exists rest, history_from g fuel st = st :: rest.
  Proof.
    intros g [|fuel] st; cbn [history_from]; destruct (wto_step g st); eexists; reflexivity.
  Qed.

  (** A finished fuel run gives a terminal history with each adjacent transition recorded. *)
  Lemma history_from_complete : forall g fuel st w,
    loop_fuel (wto_step g) fuel st = inr w ->
    exists terminal prefix, history_from g fuel st = prefix ++ [terminal] /\
      Forall2 (fun before after => wto_step g before = inl after)
        prefix (tl (history_from g fuel st)) /\
      wto_step g terminal = inr w.
  Proof.
    intros g fuel. induction fuel as [|fuel IH]; intros st w Hrun; [discriminate|].
    cbn [loop_fuel] in Hrun.
    destruct (wto_step g st) as [next|result] eqn:Hstep.
    - destruct (IH next w Hrun) as [terminal [prefix [Hhistory [Hsteps Hterminal]]]].
      destruct (history_from_head g fuel next) as [tail Hhead].
      exists terminal, (st :: prefix). split.
      + cbn [history_from]. rewrite Hstep. cbn [app]. now rewrite Hhistory.
      + split.
        * cbn [history_from]. rewrite Hstep. cbn [tl]. rewrite Hhead.
          constructor; [exact Hstep|]. rewrite Hhead in Hsteps. exact Hsteps.
        * exact Hterminal.
    - injection Hrun as Heq. subst result. exists st, [].
      cbn [history_from]. rewrite Hstep. cbn [app tl].
      split; [reflexivity|]. split; [constructor|reflexivity].
  Qed.

  Local Opaque loopN.

  Lemma F17_history : forall g roots,
    exists terminal prefix, history g roots = prefix ++ [terminal] /\
      (match prefix with [] => terminal | first :: _ => first end) = initial g roots /\
      Forall2 (fun before after => wto_step g before = inl after)
        prefix (tl (history g roots)) /\
      wto_step g terminal = inr (build g roots).
  Proof.
    intros g roots. destruct (F16_done g roots) as [w Hrun].
    assert (Hbuild : build g roots = w).
    { unfold build. rewrite rev_append_rev, app_nil_r.
      change ((match loopN (wto_step g)
        (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
        (initial g roots) with
        | inl st => wto_reverse_into (wto_partial st) WNil
        | inr result => result
        end) = w).
      now rewrite Hrun. }
    rewrite search_loopN_fuel, Nat2N.id in Hrun.
    destruct (history_from_complete g _ (initial g roots) w Hrun)
      as [terminal [prefix [Hhistory [Hsteps Hterminal]]]].
    exists terminal, prefix. split; [exact Hhistory|]. split.
    - destruct (history_from_head g
        (3 * length (concat (comps (wto_components g roots))) + 1) (initial g roots))
        as [tail Hhead].
      rewrite Hhistory in Hhead. destruct prefix; cbn [app] in Hhead;
        inversion Hhead; reflexivity.
    - split; [exact Hsteps|]. now rewrite Hbuild.
  Qed.

  Local Transparent loopN.

  Local Opaque loopN.

  (** Source mass adds across concatenated vertex lists. *)
  Lemma source_mass_app : forall g first rest,
    source_mass g (first ++ rest) = source_mass g first + source_mass g rest.
  Proof.
    intros g first rest. unfold source_mass.
    induction first as [|v first IH]; cbn [app fold_right]; [reflexivity|].
    rewrite IH. lia.
  Qed.

  (** Reordering vertices preserves their total source mass. *)
  Lemma source_mass_permutation : forall g first rest,
    Permutation first rest -> source_mass g first = source_mass g rest.
  Proof.
    intros g first rest Hpermutation. unfold source_mass.
    induction Hpermutation; cbn [fold_right]; lia.
  Qed.

  (** Summing component source masses counts their concatenated vertex list. *)
  Lemma components_source_mass : forall g cs,
    fold_right (fun c n => source_mass g c + n) 0 cs = source_mass g (concat cs).
  Proof.
    intros g cs. induction cs as [|c rest IH]; cbn [fold_right concat].
    - reflexivity.
    - rewrite source_mass_app, IH. reflexivity.
  Qed.

  Local Opaque loopN prepared_search_trace Galois.Graph.Wto.wto_scoped.

  (** Visiting a root for every listed source returns that source inventory exactly. *)
  Lemma partition_components_total g roots :
    NoDup (nodes g) -> (forall v, In v (nodes g) -> In v roots) ->
    Permutation (concat (comps (wto_components g roots))) (nodes g).
  Proof.
    intros Hunique Hcover. rewrite wto_components_agrees.
    set (ready := scc_graph g).
    set (chosen := filter (fun v => match trie_get v (succ (base ready)) with
      Some _ => true | None => false end) roots).
    assert (Hchosen : forall v, In v chosen -> In v (nodes ready)).
    { intros v Hin. unfold chosen in Hin. apply filter_In in Hin.
      destruct Hin as [_ Hlisted]. unfold ready in *.
      rewrite wto_scc_root_test in Hlisted. rewrite scc_graph_nodes.
      now apply wto_member_spec. }
    assert (Hclosed : forall u v,
      In u (nodes ready) -> edge (base ready) u v -> In v (nodes ready)).
    { intros u v Hu Hedge. unfold ready. rewrite scc_graph_nodes.
      now apply (scc_graph_closed g u). }
    assert (Hnested : trace_stack [] (prepared_search_trace ready chosen) []).
    { apply prepared_search_nested_closed; [apply scc_graph_counts|exact Hclosed|exact Hchosen]. }
    pose proof (tarjan_complete_components (prepared_search_trace ready chosen)
      (prepared_search_unique_raw ready chosen) Hnested) as Hcomponents.
    change (Permutation (concat (rev_append
      (tarjan_emitted (TarjanSearch.dfs ready chosen tarjan_initial)) [])) (nodes g)).
    rewrite rev_append_rev, app_nil_r. eapply Permutation_trans; [exact Hcomponents|].
    apply NoDup_Permutation; [apply prepared_search_unique_raw|exact Hunique|].
    intro v. split.
    - intro Hin. exact (wto_component_trace_listed g roots v Hin).
    - intro Hin. apply (proj2 (prepared_search_reach_closed ready chosen
        (scc_graph_counts g) Hclosed Hchosen v)).
      exists v, [v]. split; [|constructor].
      unfold chosen. apply filter_In. split; [now apply Hcover|].
      unfold ready. rewrite wto_scc_root_test. now apply wto_member_spec.
  Qed.

  Lemma F13_partition : forall g body,
    NoDup body ->
    let r := wto_components (wto_scoped g (Some body)) (rev body) in
    Permutation (concat (comps r)) body /\
    fold_right (fun c n => source_mass g c + n) 0 (comps r) = source_mass g body.
  Proof.
    intros g body.
    intro Hunique. cbn zeta.
    pose proof (proj1 (F12_scope g body)) as Hnodes.
    assert (Hready : NoDup (nodes (wto_scoped g (Some body)))) by (now rewrite Hnodes).
    assert (Hroots : forall v, In v (nodes (wto_scoped g (Some body))) -> In v (rev body)).
    { intros v Hin. rewrite Hnodes in Hin. now apply (proj1 (in_rev body v)). }
    pose proof (partition_components_total (wto_scoped g (Some body)) (rev body)
      Hready Hroots) as Hpartition.
    rewrite Hnodes in Hpartition.
    split; [exact Hpartition|].
    rewrite components_source_mass. now apply source_mass_permutation.
  Qed.

  Local Transparent prepared_search_trace Galois.Graph.Wto.wto_scoped.

  (** A duplicate-free subdomain cannot have more source mass than its containing list. *)
  Lemma source_mass_subdomain : forall g first rest,
    NoDup first -> incl first rest -> source_mass g first <= source_mass g rest.
  Proof.
    intros g first. induction first as [|v first IH]; intros rest Hunique Hincl.
    - cbn [source_mass fold_right]. lia.
    - inversion Hunique as [|? ? Habsent Htail]; subst.
      destruct (in_split v rest (Hincl v (or_introl eq_refl))) as [before [after Heq]].
      subst rest.
      assert (Hin : incl first (before ++ after)).
      { intros u Hu. specialize (Hincl u (or_intror Hu)).
        apply in_app_iff in Hincl. apply in_app_iff. destruct Hincl as [Hin|[Heq|Hin]].
        - now left.
        - subst u. contradiction.
        - now right. }
      specialize (IH (before ++ after) Htail Hin).
      rewrite (source_mass_app g before after) in IH.
      rewrite (source_mass_app g before (v :: after)).
      change (1 + length (succs (base g) v) + source_mass g first <=
        source_mass g before + (1 + length (succs (base g) v) + source_mass g after)).
      lia.
  Qed.

  (** Scoped component output is a duplicate-free subdomain of the requested body. *)
  Lemma scoped_components_source_mass : forall g body roots,
    source_mass g (concat (comps (wto_components (wto_scoped g (Some body)) roots))) <=
      source_mass g body.
  Proof.
    intros g body roots. apply source_mass_subdomain.
    - apply wto_components_unique.
    - intros v Hin. exact (wto_components_listed (wto_scoped g (Some body)) roots v Hin).
  Qed.

  (** Pending expansions below one level reserve the source mass that can reach that level. *)
  Fixpoint level_credit (g : prepared) (level depth : nat) (tasks : list wto_task) : nat :=
    match tasks with
    | [] => 0
    | WtoExpand _ _ _ c :: tasks =>
      (if Nat.leb depth level then source_mass g c else 0) +
        level_credit g level depth tasks
    | WtoClose _ :: tasks => level_credit g level (Nat.pred depth) tasks
    end.

  (** A block of expansions contributes its combined source mass at the current depth. *)
  Lemma level_credit_expands : forall g level depth within entries owners cs tasks,
    level_credit g level depth (wto_expand_tasks within entries owners cs ++ tasks) =
      (if Nat.leb depth level then source_mass g (concat cs) else 0) +
        level_credit g level depth tasks.
  Proof.
    intros g level depth within entries owners cs tasks.
    change (wto_expand_tasks within entries owners cs) with
      (map (fun c => WtoExpand within entries owners c) cs).
    induction cs as [|c rest IH].
    - cbn [map app concat source_mass fold_right].
      destruct (Nat.leb depth level); reflexivity.
    - cbn [map app concat level_credit]. rewrite IH, source_mass_app.
      destruct (Nat.leb depth level); lia.
  Qed.

  (** One expansion is the only source-mass charge made by a state at its own depth. *)
  Definition level_entry g level st :=
    if Nat.eqb (length (wto_parents st)) level then
      match wto_tasks st with WtoExpand _ _ _ c :: _ => source_mass g c | _ => 0 end
    else 0.

  Lemma level_mass_cons : forall g level st states,
    level_mass g level (st :: states) = level_entry g level st + level_mass g level states.
  Proof.
    intros g level st states. unfold level_mass, level_entry. cbn [fold_right].
    destruct (Nat.eqb (length (wto_parents st)) level); [|reflexivity].
    destruct (wto_tasks st) as [|task tasks]; [reflexivity|].
    destruct task; reflexivity.
  Qed.

  (** A possible charge at the current head is already present in the pending credit. *)
  Lemma level_entry_credit : forall g level st,
    level_entry g level st <=
      level_credit g level (length (wto_parents st)) (wto_tasks st).
  Proof.
    intros g level [tasks partial parents]. unfold level_entry.
    cbn [wto_tasks wto_parents].
    destruct (Nat.eqb (length parents) level) eqn:Hlevel; [|lia].
    apply Nat.eqb_eq in Hlevel. subst level.
    destruct tasks as [|task tasks]; [reflexivity|].
    destruct task; cbn [level_credit]; rewrite ?Nat.leb_refl; lia.
  Qed.

  (** A step spends its level charge and preserves enough credit for every child expansion. *)
  Local Opaque Galois.Graph.Wto.wto_components.

  Lemma level_credit_step : forall g level st next,
    wto_step g st = inl next ->
    level_entry g level st +
      level_credit g level (length (wto_parents next)) (wto_tasks next) <=
      level_credit g level (length (wto_parents st)) (wto_tasks st).
  Proof.
    intros g level [tasks partial parents] next Hstep.
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    destruct task as [within entries owners c|h].
    - unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select
        (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + pose proof (source_mass_permutation g _ _ (wto_select_spec _ _ _ _ Hselect))
          as Hmass.
        change (source_mass g c =
          1 + length (succs (base g) h) + source_mass g body) in Hmass.
        destruct body as [|v body].
        * inversion Hstep; subst next.
          clear Hstep Hselect Hmass.
          change ((if Nat.eqb (length parents) level then source_mass g c else 0) +
            level_credit g level (length parents) tasks <=
            (if Nat.leb (length parents) level then source_mass g c else 0) +
            level_credit g level (length parents) tasks).
          destruct (Nat.eqb_spec (length parents) level) as [Heq|Hdifferent].
          -- subst level. rewrite Nat.leb_refl. reflexivity.
          -- destruct (Nat.leb (length parents) level); lia.
        * inversion Hstep; subst next.
          pose proof (scoped_components_source_mass g (v :: body)
            (rev (v :: body))) as Hchild.
          rewrite !rev_append_rev, !app_nil_r.
          set (cs := comps (Galois.Graph.Wto.wto_components
            (Galois.Graph.Wto.wto_scoped g (Some (v :: body)))
            (rev (v :: body)))) in *.
          change (source_mass g (concat cs) <= source_mass g (v :: body)) in Hchild.
          clear Hstep Hselect.
          cbn [wto_tasks wto_parents length]. rewrite level_credit_expands.
          cbn [level_credit Nat.pred].
          change ((if Nat.eqb (length parents) level then source_mass g c else 0) +
            ((if Nat.leb (S (length parents)) level then source_mass g (concat (rev cs)) else 0) +
              level_credit g level (length parents) tasks) <=
            (if Nat.leb (length parents) level then source_mass g c else 0) +
              level_credit g level (length parents) tasks).
          rewrite <- (source_mass_permutation g _ _ (wto_components_reverse cs)).
          assert (Hsub : source_mass g (concat cs) <= source_mass g c) by lia.
          clear Hmass Hchild.
          destruct (Nat.eqb_spec (length parents) level);
            destruct (Nat.leb_spec0 (length parents) level);
            destruct (Nat.leb_spec0 (S (length parents)) level); lia.
      + apply wto_select_empty in Hselect. subst c. inversion Hstep; subst next.
        unfold level_entry. cbn [wto_tasks wto_parents level_credit source_mass fold_right].
        destruct (Nat.eqb (length parents) level), (Nat.leb (length parents) level); lia.
    - destruct parents as [|parent parents]; inversion Hstep; subst next;
        unfold level_entry; cbn [wto_tasks wto_parents length level_credit Nat.pred].
      + destruct (Nat.eqb 0 level); lia.
      + destruct (Nat.eqb (S (length parents)) level); lia.
  Qed.

  Local Transparent Galois.Graph.Wto.wto_components.

  (** Summing a finite history cannot spend more source mass than its pending credit. *)
  Lemma history_level_credit : forall g level fuel st,
    level_mass g level (history_from g fuel st) <=
      level_credit g level (length (wto_parents st)) (wto_tasks st).
  Proof.
    intros g level fuel. induction fuel as [|fuel IH]; intro st.
    - cbn [history_from]. destruct (wto_step g st); rewrite level_mass_cons;
        cbn [level_mass fold_right]; pose proof (level_entry_credit g level st); lia.
    - cbn [history_from]. destruct (wto_step g st) as [next|result] eqn:Hstep.
      + rewrite level_mass_cons. specialize (IH next).
        pose proof (level_credit_step g level st next Hstep). lia.
      + rewrite level_mass_cons. cbn [level_mass fold_right].
        pose proof (level_entry_credit g level st). lia.
  Qed.

  Lemma F18_level_mass : forall g roots level,
    level_mass g level (history g roots) <=
      source_mass g (concat (comps (wto_components g roots))).
  Proof.
    intros g roots level. unfold history.
    eapply Nat.le_trans; [apply history_level_credit|].
    unfold initial. cbn [wto_parents wto_tasks length].
    pose proof (level_credit_expands g level 0 None
      (wto_entries g roots (wto_components g roots)) (comp (wto_components g roots))
      (rev (comps (wto_components g roots))) []) as Hcredit.
    rewrite app_nil_r in Hcredit. rewrite Hcredit.
    cbn [Nat.leb level_credit].
    rewrite <- (source_mass_permutation g _ _ (wto_components_reverse _)). lia.
  Qed.

  Local Transparent loopN.


  (** Reversing a sibling sequence preserves its maximal nesting depth. *)
  Lemma reverse_into_depth : forall w tail,
    wto_depth (wto_reverse_into w tail) = Nat.max (wto_depth w) (wto_depth tail).
  Proof.
    intro w. unfold wto_reverse_into. induction w as
      [|v rest IH|h body IHbody rest IHrest]; intro tail.
    - cbn [Galois.Graph.Wto.wto_reverse_into wto_depth]. lia.
    - cbn [Galois.Graph.Wto.wto_reverse_into wto_depth]. rewrite IH. reflexivity.
    - cbn [Galois.Graph.Wto.wto_reverse_into wto_depth]. rewrite IHrest.
      cbn [wto_depth].
      change (Nat.max (wto_depth rest) (Nat.max (S (wto_depth body)) (wto_depth tail)) =
        Nat.max (Nat.max (S (wto_depth body)) (wto_depth rest)) (wto_depth tail)).
      lia.
  Qed.

  (** Closing the suspended parents computes the depth already promised by a state. *)
  Definition state_depth st :=
    fold_left (fun depth parent => Nat.max (S depth) (wto_depth parent))
      (wto_parents st) (wto_depth (wto_partial st)).

  Lemma parents_depth_monotone : forall parents first second,
    first <= second ->
    fold_left (fun depth parent => Nat.max (S depth) (wto_depth parent)) parents first <=
    fold_left (fun depth parent => Nat.max (S depth) (wto_depth parent)) parents second.
  Proof.
    intro parents. induction parents as [|parent parents IH]; intros first second Hle.
    - exact Hle.
    - cbn [fold_left]. apply IH. lia.
  Qed.

  Lemma parents_depth_lower : forall parents depth,
    length parents + depth <=
      fold_left (fun current parent => Nat.max (S current) (wto_depth parent)) parents depth.
  Proof.
    intro parents. induction parents as [|parent parents IH]; intro depth.
    - cbn [length fold_left]. lia.
    - cbn [length fold_left]. specialize (IH (Nat.max (S depth) (wto_depth parent))).
      pose proof (Nat.le_max_l (S depth) (wto_depth parent)). lia.
  Qed.

  Lemma state_depth_lower : forall st, length (wto_parents st) <= state_depth st.
  Proof.
    intro st. unfold state_depth.
    pose proof (parents_depth_lower (wto_parents st) (wto_depth (wto_partial st))). lia.
  Qed.

  Local Opaque Galois.Graph.Wto.wto_components.

  (** Every task transition preserves or increases the depth promised by suspended loops. *)
  Lemma state_depth_step : forall g st next,
    wto_step g st = inl next -> state_depth st <= state_depth next.
  Proof.
    intros g [tasks partial parents] next Hstep.
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    destruct task as [within entries owners c|h].
    - unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + destruct body as [|v body]; inversion Hstep; subst next;
          unfold state_depth; cbn [wto_partial wto_parents fold_left wto_depth].
        * apply parents_depth_monotone.
          destruct (Galois.Graph.Wto.wto_member h (succs (base g) h)); cbn [wto_depth].
          -- change (wto_depth partial <= Nat.max 1 (wto_depth partial)).
             apply Nat.le_max_r.
          -- lia.
        * apply parents_depth_monotone. apply Nat.le_max_r.
      + inversion Hstep; subst next. reflexivity.
    - destruct parents as [|parent parents]; inversion Hstep; subst next;
        unfold state_depth; cbn [wto_partial wto_parents fold_left wto_depth].
      + reflexivity.
      + rewrite reverse_into_depth. cbn [wto_depth].
        rewrite Nat.max_0_r. reflexivity.
  Qed.

  (** Each suspended parent has exactly one future close task. *)
  Definition frames_balanced st :=
    length (wto_parents st) =
      length (filter (fun task => match task with WtoClose _ => true | _ => false end)
        (wto_tasks st)).

  Lemma frames_balanced_step : forall g st next,
    frames_balanced st -> wto_step g st = inl next -> frames_balanced next.
  Proof.
    intros g [tasks partial parents] next Hbalance Hstep.
    unfold frames_balanced in *. cbn [wto_tasks wto_parents] in Hbalance.
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    destruct task as [within entries owners c|h].
    - cbn [filter] in Hbalance.
      unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + destruct body as [|v body]; inversion Hstep; subst next;
          cbn [wto_tasks wto_parents length].
        * exact Hbalance.
        * rewrite filter_app, (proj2 (proj2 (expand_inventory _ _ _ _))).
          cbn [filter app length]. lia.
      + inversion Hstep; subst next. exact Hbalance.
    - cbn [filter length] in Hbalance.
      destruct parents as [|parent parents]; inversion Hstep; subst next;
        cbn [wto_tasks wto_parents length] in *; lia.
  Qed.

  Lemma frames_balanced_initial : forall g roots, frames_balanced (initial g roots).
  Proof.
    intros g roots. unfold initial, frames_balanced. cbn [wto_tasks wto_parents length].
    rewrite (proj2 (proj2 (expand_inventory _ _ _ _))). reflexivity.
  Qed.

  (** A terminal task state returns the reversal of its accumulated partial output. *)
  Lemma step_terminal_shape : forall g st w,
    wto_step g st = inr w -> wto_tasks st = [] /\
      w = wto_reverse_into (wto_partial st) WNil.
  Proof.
    intros g [tasks partial parents] w Hstep. destruct tasks as [|task tasks].
    - unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      inversion Hstep; subst w. split; reflexivity.
    - destruct task as [within entries owners c|h].
      + unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
        cbn [wto_step_spec] in Hstep.
        destruct (Galois.Graph.Wto.wto_select (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|];
          [destruct body|]; discriminate.
      + destruct parents; discriminate Hstep.
  Qed.

  (** A balanced completed run realizes all depth already promised by its starting state. *)
  Lemma completed_state_depth : forall g fuel st w,
    frames_balanced st -> loop_fuel (wto_step g) fuel st = inr w ->
      state_depth st <= wto_depth w.
  Proof.
    intros g fuel. induction fuel as [|fuel IH]; intros st w Hbalance Hrun;
      [discriminate|].
    cbn [loop_fuel] in Hrun. destruct (wto_step g st) as [next|result] eqn:Hstep.
    - eapply Nat.le_trans; [apply (state_depth_step g st next Hstep)|].
      apply (IH next w); [eapply frames_balanced_step; eassumption|exact Hrun].
    - injection Hrun as Heq. subst result.
      destruct (step_terminal_shape g st w Hstep) as [Htasks Hresult].
      unfold frames_balanced in Hbalance. rewrite Htasks in Hbalance.
      cbn [filter length] in Hbalance. apply length_zero_iff_nil in Hbalance.
      unfold state_depth. rewrite Hbalance. cbn [fold_left]. rewrite Hresult.
      rewrite reverse_into_depth. cbn [wto_depth]. lia.
  Qed.

  (** Every state in a balanced completed history fits inside the eventual result depth. *)
  Lemma history_state_depth : forall g fuel st w,
    frames_balanced st -> loop_fuel (wto_step g) fuel st = inr w ->
    Forall (fun current => state_depth current <= wto_depth w) (history_from g fuel st).
  Proof.
    intros g fuel. induction fuel as [|fuel IH]; intros st w Hbalance Hrun;
      [discriminate|].
    pose proof (completed_state_depth g (S fuel) st w Hbalance Hrun) as Hdepth.
    cbn [history_from]. destruct (wto_step g st) as [next|result] eqn:Hstep.
    - constructor; [exact Hdepth|]. apply (IH next w).
      + eapply frames_balanced_step; eassumption.
      + cbn [loop_fuel] in Hrun. now rewrite Hstep in Hrun.
    - constructor; [exact Hdepth|constructor].
  Qed.

  Local Opaque loopN.

  (** Every recorded state has at most the nesting depth of the completed output. *)
  Lemma history_depth_bound : forall g roots st,
    In st (history g roots) ->
    length (wto_parents st) <= wto_depth (build g roots).
  Proof.
    intros g roots st Hin.
    destruct (F16_done g roots) as [w Hrun].
    assert (Hbuild : build g roots = w).
    { unfold build. rewrite rev_append_rev, app_nil_r.
      change ((match loopN (wto_step g)
        (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
        (initial g roots) with
        | inl current => wto_reverse_into (wto_partial current) WNil
        | inr result => result
        end) = w).
      now rewrite Hrun. }
    rewrite Hbuild. rewrite search_loopN_fuel, Nat2N.id in Hrun.
    pose proof (history_state_depth g _ _ w (frames_balanced_initial g roots) Hrun) as Hdepth.
    apply Forall_forall with (x := st) in Hdepth; [|exact Hin].
    eapply Nat.le_trans; [apply state_depth_lower|exact Hdepth].
  Qed.

  Lemma F19_depth : forall g roots st within entries owners c tasks,
    In st (history g roots) ->
    wto_tasks st = WtoExpand within entries owners c :: tasks ->
    length (wto_parents st) <= wto_depth (build g roots).
  Proof.
    intros g roots st within entries owners c tasks Hin Htasks.
    now apply history_depth_bound.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components.


  Lemma T1_member : forall v vs,
    (T_wto_member v vs <= k_member * N.of_nat (length vs + 1) *
      N.of_nat (graph_max (Pos.size_nat v) (vertex_width vs) + 1))%N.
  Proof.
    intros v vs. pose proof (wto_member_clock v vs) as Hmember.
    assert (Hwidth : Pos.size_nat v <= graph_max (Pos.size_nat v) (vertex_width vs)).
    { rewrite wto_graph_max_nat. apply Nat.le_max_l. }
    unfold k_member. time_step.
  Qed.

  (** A left fold charges a separate occurrence budget for every visited element. *)
  Local Lemma scope_fold_left_budget {A X} (f : A -> X -> A) (clock : A -> X -> N)
      (weight : X -> nat) xs initial coefficient width :
    (forall state x, In x xs ->
      (clock state x + 1 <= coefficient * N.of_nat (weight x) * N.of_nat (width + 1))%N) ->
    (List.T_fold_left f clock xs initial <= coefficient *
      N.of_nat (fold_right (fun x n => (weight x + n)%nat) 0%nat xs) *
      N.of_nat (width + 1) + 1)%N.
  Proof.
    revert initial. induction xs as [|x xs IH]; intros initial Hcost.
    - time_unfold @List.T_fold_left. cbn [fold_right]. nia.
    - pose proof (Hcost initial x (or_introl eq_refl)) as Hhead.
      pose proof (IH (f initial x) (fun state y Hin => Hcost state y (or_intror Hin))) as Htail.
      time_unfold @List.T_fold_left. cbn [fold_right]. rewrite Nat2N.inj_add.
      clear - Hhead Htail. nia.
  Qed.

  Local Lemma scope_unit_mass {A} (xs : list A) :
    fold_right (fun _ n => 1 + n) 0 xs = length xs.
  Proof.
    induction xs; cbn [fold_right length]; lia.
  Qed.

  (** Filtering pays only predicate calls at members of the supplied row. *)
  Local Lemma scope_filter_members_time {A} (predicate : A -> bool) clock xs coefficient :
    (forall x, In x xs -> (clock x <= coefficient)%N) ->
    (List.T_filter predicate clock xs <= (coefficient + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hcost.
    - time_unfold @List.T_filter. cbn [length]. nia.
    - pose proof (Hcost x (or_introl eq_refl)) as Hhead.
      specialize (IH (fun y Hin => Hcost y (or_intror Hin))).
      time_unfold @List.T_filter. cbn [length]. rewrite Nat2N.inj_succ.
      destruct (predicate x); nia.
  Qed.

  (** Listed source rows contribute every target key to the original graph width. *)
  Local Lemma scope_row_key_width g u v : In u (nodes g) -> In v (succs (base g) u) ->
    Pos.size_nat v <= graph_width (base g).
  Proof.
    destruct g as [[vertices adjacency] predecessors n e].
    cbn [nodes base graph_width]. intros Hu Hv.
    pose proof (search_row_width_member (Digraph vertices adjacency) vertices u v Hu Hv) as Hrow.
    rewrite wto_graph_max_nat. eapply Nat.le_trans; [exact Hrow|apply Nat.le_max_r].
  Qed.

  Local Lemma scope_listed_key_widths g vs :
    (forall v, In v vs -> In v (nodes g)) ->
    Forall (fun u =>
      Pos.size_nat u <= graph_max (graph_width (base g)) (vertex_width vs) /\
      Forall (fun v => Pos.size_nat v <= graph_max (graph_width (base g)) (vertex_width vs))
        (succs (base g) u)) vs.
  Proof.
    intros Hlisted. apply Forall_forall. intros u Hu. split.
    - eapply Nat.le_trans; [exact (scc_node_width g u (Hlisted u Hu))|].
      rewrite wto_graph_max_nat. apply Nat.le_max_l.
    - apply Forall_forall. intros v Hv.
      eapply Nat.le_trans; [exact (scope_row_key_width g u v (Hlisted u Hu) Hv)|].
      rewrite wto_graph_max_nat. apply Nat.le_max_l.
  Qed.

  (** Building the membership trie pays one bounded insertion per selected occurrence. *)
  Local Lemma scope_index_time vs width :
    Forall (fun v => Pos.size_nat v <= width) vs ->
    (List.T_fold_left (fun acc v => PTrieCode.set v true acc)
      (fun acc v => 1 + PTrieCode.T_set v true acc)%N vs Empty <=
      8 * (PTrieT.c_trie + 1) * N.of_nat (length vs + 1) * N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth.
    assert (Hcost : forall acc v, In v vs ->
      (1 + PTrieCode.T_set v true acc + 1 <=
        (4 * (PTrieT.c_trie + 1)) * N.of_nat 1 * N.of_nat (width + 1))%N).
    { intros acc v Hin. rewrite Forall_forall in Hwidth. specialize (Hwidth v Hin).
      pose proof (PTrieT.T_set_le bool v true acc) as Hset.
      rewrite !Nat2N.inj_add in *. nia. }
    pose proof (scope_fold_left_budget (fun acc v => PTrieCode.set v true acc)
      (fun acc v => (1 + PTrieCode.T_set v true acc)%N) (fun _ => 1)
      vs Empty (4 * (PTrieT.c_trie + 1))%N width Hcost) as Hfold.
    rewrite scope_unit_mass in Hfold. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Testing row targets in the membership trie pays only their key widths. *)
  Local Lemma scope_filter_time (listed : ptrie bool) row width :
    Forall (fun v => Pos.size_nat v <= width) row ->
    (List.T_filter (fun v => match trie_get v listed with Some _ => true | None => false end)
      (fun v => 1 + T_trie_get v listed)%N row <=
      8 * N.of_nat (length row + 1) * N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth.
    assert (Hcost : forall v, In v row ->
      (1 + T_trie_get v listed <= 4 * N.of_nat (width + 1))%N).
    { intros v Hin. rewrite Forall_forall in Hwidth. specialize (Hwidth v Hin).
      PTrieT.trie_get_le. rewrite Nat2N.inj_add. nia. }
    pose proof (scope_filter_members_time
      (fun v => match trie_get v listed with Some _ => true | None => false end)
      (fun v => (1 + T_trie_get v listed)%N) row (4 * N.of_nat (width + 1))%N Hcost) as Hfilter.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Materializing rows charges each selected source and its outgoing occurrences once. *)
  Local Lemma scope_rows_time g (listed : ptrie bool) vs width :
    Forall (fun u => Pos.size_nat u <= width /\
      Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) vs ->
    (List.T_fold_left
      (fun acc v => PTrieCode.set v (filter (fun u =>
        match trie_get u listed with Some _ => true | None => false end) (succs (base g) v)) acc)
      (fun acc v => 1 + (((T_base g + T_succs (base g) v) +
        List.T_filter (fun u => match trie_get u listed with Some _ => true | None => false end)
          (fun u => 1 + T_trie_get u listed)%N (succs (base g) v)) +
        PTrieCode.T_set v (filter (fun u =>
          match trie_get u listed with Some _ => true | None => false end)
          (succs (base g) v)) acc))%N
      vs Empty <= 64 * (PTrieT.c_trie + 1) * N.of_nat (source_mass g vs + 1) *
        N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth.
    assert (Hcost : forall acc v, In v vs ->
      (1 + (((T_base g + T_succs (base g) v) +
        List.T_filter (fun u => match trie_get u listed with Some _ => true | None => false end)
          (fun u => 1 + T_trie_get u listed)%N (succs (base g) v)) +
        PTrieCode.T_set v (filter (fun u =>
          match trie_get u listed with Some _ => true | None => false end)
          (succs (base g) v)) acc) + 1 <=
        (32 * (PTrieT.c_trie + 1)) * N.of_nat (1 + length (succs (base g) v)) *
          N.of_nat (width + 1))%N).
    { intros acc v Hin. rewrite Forall_forall in Hwidth.
      destruct (Hwidth v Hin) as [Hv Hrow].
      pose proof (search_succs_clock (base g) v) as Hread.
      pose proof (scope_filter_time listed (succs (base g) v) width Hrow) as Hfilter.
      pose proof (PTrieT.T_set_le (list positive) v
        (filter (fun u => match trie_get u listed with Some _ => true | None => false end)
          (succs (base g) v)) acc) as Hset.
      unfold T_base. rewrite !Nat2N.inj_add in *.
      clear - Hv Hread Hfilter Hset. nia. }
    pose proof (scope_fold_left_budget
      (fun acc v => PTrieCode.set v (filter (fun u =>
        match trie_get u listed with Some _ => true | None => false end) (succs (base g) v)) acc)
      (fun acc v => (1 + (((T_base g + T_succs (base g) v) +
        List.T_filter (fun u => match trie_get u listed with Some _ => true | None => false end)
          (fun u => (1 + T_trie_get u listed)%N) (succs (base g) v)) +
        PTrieCode.T_set v (filter (fun u =>
          match trie_get u listed with Some _ => true | None => false end)
          (succs (base g) v)) acc))%N)
      (fun v => 1 + length (succs (base g) v)) vs Empty
      (32 * (PTrieT.c_trie + 1))%N width Hcost) as Hfold.
    match goal with
    | |- (?clock <= _)%N =>
      change (clock <= 32 * (PTrieT.c_trie + 1) * N.of_nat (source_mass g vs) *
        N.of_nat (width + 1) + 1)%N in Hfold
    end.
    rewrite !Nat2N.inj_add in *. clear - Hfold. nia.
  Qed.

  Local Lemma scope_mass_length g vs : length vs <= source_mass g vs.
  Proof.
    unfold source_mass. induction vs; cbn [length fold_right]; lia.
  Qed.

  (** The materialization clock is linear in selected source mass at the supplied key width. *)
  Lemma scope_materialization_time g vs width :
    Forall (fun u => Pos.size_nat u <= width /\
      Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) vs ->
    (T_wto_scoped g (Some vs) <= 128 * (PTrieT.c_trie + 1) *
      N.of_nat (source_mass g vs + 1) * N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth.
    assert (Hkeys : Forall (fun v => Pos.size_nat v <= width) vs).
    { eapply Forall_impl; [|exact Hwidth]. intros v Hv. exact (proj1 Hv). }
    pose proof (scope_index_time vs width Hkeys) as Hindex.
    set (listed := fold_left (fun acc v => PTrieCode.set v true acc) vs Empty).
    pose proof (scope_rows_time g listed vs width Hwidth) as Hrows.
    pose proof (scope_mass_length g vs) as Hlength.
    time_unfold @T_wto_scoped. time_unfold @Galois.Graph.Wto.T_wto_scoped.
    fold listed. unfold T_nv, T_ne. time_cbn.
    rewrite !Nat2N.inj_add in *. clear - Hindex Hrows Hlength. nia.
  Qed.

  (** Pointwise weight bounds extend to occurrence sums without distinctness premises. *)
  Local Lemma scope_weight_mono {A} (first second : A -> nat) xs :
    (forall x, In x xs -> first x <= second x) ->
    fold_right (fun x n => first x + n) 0 xs <=
      fold_right (fun x n => second x + n) 0 xs.
  Proof.
    induction xs as [|x xs IH]; intro Hweight; cbn [fold_right]; [lia|].
    pose proof (Hweight x (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y Hin => Hweight y (or_intror Hin))). lia.
  Qed.

  (** The materialized graph contains only filtered occurrences of the selected rows. *)
  Local Lemma scope_graph_edges g vs :
    graph_e (base (wto_scoped g (Some vs))) <=
      fold_right (fun v n => length (succs (base g) v) + n) 0 vs.
  Proof.
    change (fold_right (fun v n => length (succs (base (wto_scoped g (Some vs))) v) + n)
      0 vs <= fold_right (fun v n => length (succs (base g) v) + n) 0 vs).
    apply scope_weight_mono. intros v Hin.
    change (length (succs (base (Galois.Graph.Wto.wto_scoped g (Some vs))) v) <=
      length (succs (base g) v)).
    rewrite (proj2 (wto_scoped_spec g vs) v Hin). apply filter_length_le.
  Qed.

  Local Lemma scope_mass_decompose g vs : source_mass g vs =
    length vs + fold_right (fun v n => length (succs (base g) v) + n) 0 vs.
  Proof.
    unfold source_mass. induction vs; cbn [length fold_right]; lia.
  Qed.

  (** A scoped phase counts the selected vertices once as graph nodes and once as roots. *)
  Local Lemma scope_graph_size g vs :
    graph_n (base (wto_scoped g (Some vs))) +
      graph_e (base (wto_scoped g (Some vs))) + length (rev vs) + 1 <=
      2 * (source_mass g vs + 1).
  Proof.
    pose proof (scope_graph_edges g vs) as Hedges.
    rewrite length_rev, scope_mass_decompose.
    change (length vs + graph_e (base (wto_scoped g (Some vs))) + length vs + 1 <=
      2 * (length vs + fold_right (fun v n => length (succs (base g) v) + n) 0 vs + 1)).
    lia.
  Qed.

  (** A finite list's maximum width respects a common bound on all its keys. *)
  Local Lemma scope_vertex_width_bound vs width :
    Forall (fun v => Pos.size_nat v <= width) vs -> vertex_width vs <= width.
  Proof.
    intro Hwidth. unfold vertex_width. induction Hwidth; cbn [fold_right]; [lia|].
    rewrite wto_graph_max_nat. apply Nat.max_lub; assumption.
  Qed.

  Local Lemma scope_max_bound {A} (weight : A -> nat) xs width :
    (forall x, In x xs -> weight x <= width) ->
    fold_right (fun x n => graph_max (weight x) n) 0 xs <= width.
  Proof.
    induction xs as [|x xs IH]; intro Hbound; cbn [fold_right]; [lia|].
    rewrite wto_graph_max_nat. apply Nat.max_lub.
    - apply Hbound. now left.
    - apply IH. intros y Hin. apply Hbound. now right.
  Qed.

  (** Every materialized row targets keys in the selected domain. *)
  Local Lemma scope_graph_width g vs :
    graph_width (base (wto_scoped g (Some vs))) <= vertex_width vs.
  Proof.
    assert (Hrows : forall v, In v vs ->
      vertex_width (succs (base (wto_scoped g (Some vs))) v) <= vertex_width vs).
    { intros v Hin. apply scope_vertex_width_bound. apply Forall_forall. intros u Hu.
      change (In u (succs (base (Galois.Graph.Wto.wto_scoped g (Some vs))) v)) in Hu.
      rewrite (proj2 (wto_scoped_spec g vs) v Hin) in Hu.
      apply filter_In in Hu. destruct Hu as [_ Hmember]. apply wto_member_spec in Hmember.
      now apply search_vertex_width_member. }
    change (graph_max (vertex_width vs)
      (fold_right (fun v n => graph_max
        (vertex_width (succs (base (wto_scoped g (Some vs))) v)) n) 0 vs) <= vertex_width vs).
    rewrite wto_graph_max_nat. apply Nat.max_lub; [lia|].
    now apply scope_max_bound.
  Qed.

  (** Reversed scoped roots and scoped rows obey the same original phase width. *)
  Local Lemma scope_phase_width g vs :
    graph_max (graph_width (base (wto_scoped g (Some vs)))) (vertex_width (rev vs)) <=
      graph_max (graph_width (base g)) (vertex_width vs).
  Proof.
    pose proof (scope_graph_width g vs) as Hgraph.
    assert (Hroots : vertex_width (rev vs) <= vertex_width vs).
    { apply scope_vertex_width_bound. apply Forall_forall. intros v Hin.
      apply search_vertex_width_member. now apply (proj2 (in_rev vs v)). }
    rewrite !wto_graph_max_nat. apply Nat.max_lub.
    - eapply Nat.le_trans; [exact Hgraph|apply Nat.le_max_r].
    - eapply Nat.le_trans; [exact Hroots|apply Nat.le_max_r].
  Qed.

  (** Listed scopes pay their selected source rows at the original graph width. *)
  Lemma T3_scope_listed : forall g vs,
    (forall v, In v vs -> In v (nodes g)) ->
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.
  Proof.
    intros g vs Hlisted.
    pose proof (scope_materialization_time g vs
      (graph_max (graph_width (base g)) (vertex_width vs))
      (scope_listed_key_widths g vs Hlisted)) as Htime.
    unfold scope_work. rewrite Nat2N.inj_mul, N.mul_assoc.
    eapply N.le_trans; [exact Htime|].
    apply N.mul_le_mono_r. apply N.mul_le_mono_r. unfold k_scope, k_build. lia.
  Qed.

  Lemma T3_scope : forall g vs,
    (forall v, In v vs -> In v (nodes g)) ->
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.
  Proof.
    exact T3_scope_listed.
  Qed.

  (** The index loop checks each key's width and listing before it reads a trie. *)
  Lemma T4a_index : forall g w,
    (T_wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] <=
    k_index * N.of_nat (graph_n (base g) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g w. pose proof (wto_check_index_clock g w) as Hindex.
    unfold k_index. time_unfold @T_wto_check_index. exact Hindex.
  Qed.

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
    exact wto_edges_ok_agrees.
  Qed.

  (** The edge scan reads the rows of distinct listed vertices once each. *)
  Local Opaque loopN.

  Lemma T4b_edges : forall g w ranks intervals vs,
    wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit w] 0 Empty Empty [] = Some (ranks, intervals, vs) ->
    (T_wto_edges_ok (base g) ranks intervals vs <=
     k_check * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
       N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g w ranks intervals vs Hindex.
    unfold wto_check_index in Hindex.
    pose proof (wto_checked_edges_clock g w ranks intervals vs Hindex) as Htime.
    unfold k_check. time_unfold @T_wto_edges_ok. exact Htime.
  Qed.

  Local Transparent loopN.

  Lemma T5_check_public : forall g roots w,
    (T_check g roots w <= c_wto *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    exact T_check_le.
  Qed.

  Lemma T6_expand : forall g within entries owners c tasks partial parents h body,
    wto_select (wto_preferred owners entries c) c = Some (h, body) -> body <> [] ->
    (T_wto_step g (WtoState (WtoExpand within entries owners c :: tasks) partial parents) <=
      k_expand * (T_wto_preferred owners entries c +
        T_wto_select (wto_preferred owners entries c) c + T_wto_scoped g (Some body) +
        T_wto_components (wto_scoped g (Some body)) (rev body) +
        T_wto_entries (wto_scoped g (Some body)) (rev body)
          (wto_components (wto_scoped g (Some body)) (rev body)) +
        N.of_nat (length body) + N.of_nat (length c) + 1))%N.
  Proof.
    intros g within entries owners c tasks partial parents h body Hselect Hbody.
    pose proof (wto_expand_step_clock g within entries owners c tasks partial parents h body
      Hselect Hbody) as Hstep.
    unfold k_expand. time_unfold @T_wto_step. time_unfold @T_wto_preferred.
    time_unfold @T_wto_select. time_unfold @T_wto_scoped. time_unfold @T_wto_components.
    time_unfold @T_wto_entries. unfold wto_preferred, wto_scoped, wto_components.
    time_simpl. nia.
  Qed.

  Lemma T8_heads_source : forall w,
    (T_heads w <= k_heads * (T_wto_heads_into w [] + 1))%N.
  Proof.
    intro w. unfold k_heads. time_step.
    time_unfold @T_wto_heads_into. time_cbn. lia.
  Qed.

  Lemma T9_heads_public : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  Proof.
    apply T_heads_le.
  Qed.

  Lemma T10_ranks_source : forall w,
    (T_ranks w <= k_ranks *
      (T_wto_order_into w [] + T_wto_rank_rows 1%positive (wto_order w) + 1))%N.
  Proof.
    intro w. unfold k_ranks. time_unfold @T_ranks.
    rewrite (proj2 (wto_into_spec w [])), app_nil_r.
    time_unfold @T_wto_order_into. time_unfold @T_wto_rank_rows. time_cbn. nia.
  Qed.

  Lemma T11_ranks_public : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof.
    apply T_ranks_le.
  Qed.

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
  Proof.
    intros w acc. pose proof (wto_heads_into_clock w acc) as Hheads.
    unfold k_heads. time_step.
  Qed.

  (** Flattening by accumulation visits each constructor once. *)
  Lemma T10b_order_into : forall w acc,
      (T_wto_order_into w acc <= k_ranks * N.of_nat (2 * length (wto_order w) + 2))%N.
  Proof.
    intros w acc. pose proof (wto_order_into_clock w acc) as Horder.
    unfold k_ranks. time_step.
  Qed.

  (** Rank insertion pays each key and an amortised binary successor. *)
  Lemma T10c_rank_rows : forall vs,
      (T_wto_rank_rows 1%positive vs <= k_ranks * N.of_nat (length vs + 1) *
        N.of_nat (vertex_width vs + Nat.log2 (length vs) + 1))%N.
  Proof.
    intro vs. pose proof (wto_rank_rows_one_clock vs) as Hrows.
    unfold k_ranks. time_step.
  Qed.

  (** Offering an entry reads and, at most once, writes its bounded component key. *)
  Local Lemma scope_offer_time i v entries width : Pos.size_nat i <= width + 1 ->
    (T_wto_offer i v entries <= 8 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth. pose proof (PTrieT.T_set_le positive i v entries) as Hset.
    time_unfold @T_wto_offer. PTrieT.trie_get_le.
    destruct (trie_get i entries); rewrite !Nat2N.inj_add in *; nia.
  Qed.

  (** Root seeding reads the supplied root key and its bounded owner, if present. *)
  Local Lemma scope_root_entry_time owners entries v width :
    Pos.size_nat v <= width ->
    (forall u i, trie_get u owners = Some i -> Pos.size_nat i <= width + 1) ->
    (T_wto_root_entry owners entries v + 1 <=
      16 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
  Proof.
    intros Hv Howners. time_unfold @T_wto_root_entry.
    PTrieT.trie_get_le.
    destruct (trie_get v owners) as [i|] eqn:Hlookup.
    - pose proof (scope_offer_time i v entries width (Howners v i Hlookup)) as Hoffer.
      rewrite !Nat2N.inj_add in *. nia.
    - rewrite !Nat2N.inj_add. nia.
  Qed.

  (** An edge entry compares bounded owner identifiers and offers its target at most once. *)
  Local Lemma scope_edge_entry_time owners u entries v width :
    Pos.size_nat v <= width ->
    (forall x i, trie_get x owners = Some i -> Pos.size_nat i <= width + 1) ->
    (T_wto_edge_entry owners (trie_get u owners) entries v + 1 <=
      16 * (PTrieT.c_trie + 1) * N.of_nat (width + 1))%N.
  Proof.
    intros Hv Howners. time_unfold @T_wto_edge_entry.
    destruct (trie_get u owners) as [i|] eqn:Hsource.
    - PTrieT.trie_get_le.
      destruct (trie_get v owners) as [j|] eqn:Htarget.
      + pose proof (Howners u i Hsource) as Hi.
        pose proof (scope_offer_time j v entries width (Howners v j Htarget)) as Hoffer.
        pose proof (Pos.T_eqb_le i j) as Heq.
        destruct (Pos.eqb i j); rewrite !Nat2N.inj_add in *; nia.
      + rewrite !Nat2N.inj_add. nia.
    - rewrite Nat2N.inj_add. nia.
  Qed.

  (** A row scan charges one bounded owner operation per target occurrence. *)
  Local Lemma scope_edge_fold_time owners u row entries width :
    Forall (fun v => Pos.size_nat v <= width) row ->
    (forall x i, trie_get x owners = Some i -> Pos.size_nat i <= width + 1) ->
    (List.T_fold_left (wto_edge_entry owners (trie_get u owners))
      (fun acc v => T_wto_edge_entry owners (trie_get u owners) acc v) row entries <=
      16 * (PTrieT.c_trie + 1) * N.of_nat (length row) * N.of_nat (width + 1) + 1)%N.
  Proof.
    intros Hwidth Howners.
    pose proof (scope_fold_left_budget (wto_edge_entry owners (trie_get u owners))
      (fun acc v => T_wto_edge_entry owners (trie_get u owners) acc v)
      (fun _ => 1) row entries (16 * (PTrieT.c_trie + 1))%N width) as Hfold.
    rewrite scope_unit_mass in Hfold. apply Hfold. intros acc v Hin.
    cbn [N.of_nat]. rewrite N.mul_1_r. apply scope_edge_entry_time; [|exact Howners].
    rewrite Forall_forall in Hwidth. now apply Hwidth.
  Qed.

  (** Component rows consume their original source and edge occurrence mass. *)
  Local Lemma scope_entry_rows_time g owners vs entries width :
    Forall (fun u => Pos.size_nat u <= width /\
      Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) vs ->
    (forall x i, trie_get x owners = Some i -> Pos.size_nat i <= width + 1) ->
    (List.T_fold_left
      (fun acc u => fold_left (wto_edge_entry owners (trie_get u owners))
        (succs (base g) u) acc)
      (fun acc u => 1 + ((T_trie_get u owners + (T_base g + T_succs (base g) u)) +
        List.T_fold_left (wto_edge_entry owners (trie_get u owners))
          (fun state v => T_wto_edge_entry owners (trie_get u owners) state v)
          (succs (base g) u) acc))%N vs entries <=
      64 * (PTrieT.c_trie + 1) * N.of_nat (source_mass g vs) * N.of_nat (width + 1) + 1)%N.
  Proof.
    intros Hwidth Howners. unfold source_mass.
    apply scope_fold_left_budget. intros acc u Hin.
    rewrite Forall_forall in Hwidth. destruct (Hwidth u Hin) as [Hu Hrow].
    pose proof (scope_edge_fold_time owners u (succs (base g) u) acc width Hrow Howners) as Hfold.
    pose proof (search_succs_clock (base g) u) as Hread.
    unfold T_base.
    rewrite !Nat2N.inj_add in *. clear - Hu Hfold Hread. PTrieT.trie_get_le. nia.
  Qed.

  Local Lemma scope_mass_app g first last :
    source_mass g (first ++ last) = source_mass g first + source_mass g last.
  Proof.
    unfold source_mass. induction first; cbn [app fold_right]; lia.
  Qed.

  Local Lemma scope_component_mass g cs :
    fold_right (fun c n => source_mass g c + 1 + n) 0 cs =
      source_mass g (concat cs) + length cs.
  Proof.
    induction cs; cbn [fold_right concat length]; [reflexivity|].
    rewrite scope_mass_app. lia.
  Qed.

  (** Entry construction charges roots, component headers and original row occurrences. *)
  Lemma scope_entries_time g roots r width :
    Forall (fun v => Pos.size_nat v <= width) roots ->
    Forall (fun u => Pos.size_nat u <= width /\
      Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) (concat (comps r)) ->
    (forall u i, trie_get u (comp r) = Some i -> Pos.size_nat i <= width + 1) ->
    (T_wto_entries g roots r <=
      256 * (PTrieT.c_trie + 1) *
        N.of_nat (length roots + length (comps r) + source_mass g (concat (comps r)) + 1) *
        N.of_nat (width + 1))%N.
  Proof.
    intros Hroots Hrows Howners. set (owners := comp r).
    assert (Hrootcost : forall acc v, In v roots ->
      (T_wto_root_entry owners acc v + 1 <=
        16 * (PTrieT.c_trie + 1) * N.of_nat 1 * N.of_nat (width + 1))%N).
    { intros acc v Hin. cbn [N.of_nat]. rewrite N.mul_1_r.
      apply scope_root_entry_time; [|exact Howners].
      rewrite Forall_forall in Hroots. now apply Hroots. }
    pose proof (scope_fold_left_budget (wto_root_entry owners)
      (fun acc v => T_wto_root_entry owners acc v) (fun _ => 1) roots Empty
      (16 * (PTrieT.c_trie + 1))%N width Hrootcost) as Hseed.
    rewrite scope_unit_mass in Hseed.
    set (seeded := fold_left (wto_root_entry owners) roots Empty).
    assert (Hcomponent : forall acc c, In c (comps r) ->
      (1 + List.T_fold_left
        (fun state u => fold_left (wto_edge_entry owners (trie_get u owners))
          (succs (base g) u) state)
        (fun state u => 1 + ((T_trie_get u owners + (T_base g + T_succs (base g) u)) +
          List.T_fold_left (wto_edge_entry owners (trie_get u owners))
            (fun entries v => T_wto_edge_entry owners (trie_get u owners) entries v)
            (succs (base g) u) state))%N c acc + 1 <=
        128 * (PTrieT.c_trie + 1) * N.of_nat (source_mass g c + 1) *
          N.of_nat (width + 1))%N).
    { intros acc c Hin.
      assert (Hc : Forall (fun u => Pos.size_nat u <= width /\
        Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) c).
      { apply Forall_forall. intros u Hu. rewrite Forall_forall in Hrows.
        apply Hrows. apply in_concat. exists c. auto. }
      pose proof (scope_entry_rows_time g owners c acc width Hc Howners) as Hcost.
      rewrite !Nat2N.inj_add in *. clear - Hcost. nia. }
    pose proof (scope_fold_left_budget
      (fun acc c => fold_left (fun state u => fold_left
        (wto_edge_entry owners (trie_get u owners)) (succs (base g) u) state) c acc)
      (fun acc c => (1 + List.T_fold_left
        (fun state u => fold_left (wto_edge_entry owners (trie_get u owners))
          (succs (base g) u) state)
        (fun state u => (1 + ((T_trie_get u owners + (T_base g + T_succs (base g) u)) +
          List.T_fold_left (wto_edge_entry owners (trie_get u owners))
            (fun entries v => T_wto_edge_entry owners (trie_get u owners) entries v)
            (succs (base g) u) state))%N) c acc)%N)
      (fun c => source_mass g c + 1) (comps r) seeded
      (128 * (PTrieT.c_trie + 1))%N width Hcomponent) as Hcomponents.
    cbn beta in Hcomponents. rewrite scope_component_mass in Hcomponents.
    time_unfold @T_wto_entries. time_unfold @Galois.Graph.Wto.T_wto_entries.
    fold owners. fold seeded. unfold T_comp, T_comps.
    rewrite !Nat2N.inj_add in *. clear - Hseed Hcomponents. nia.
  Qed.

  Local Opaque loopN prepared_search_trace.

  Local Lemma scope_phase_product coefficient first last width bound :
    first <= last -> width <= bound ->
    (coefficient * N.of_nat first * N.of_nat width <=
      coefficient * N.of_nat last * N.of_nat bound)%N.
  Proof.
    intros Hcount Hwidth. apply N.mul_le_mono.
    - apply N.mul_le_mono_l. now apply time_of_nat_le.
    - now apply time_of_nat_le.
  Qed.

  Local Lemma scope_double_coefficient (coefficient : N) (count width : nat) :
    ((2 * coefficient) * N.of_nat count * N.of_nat width =
      coefficient * N.of_nat (2 * count) * N.of_nat width)%N.
  Proof. rewrite Nat2N.inj_mul. nia. Qed.

  Local Lemma scope_entry_coefficient (coefficient : N) (count : nat) :
    (512 * (coefficient + 1) * N.of_nat count =
      256 * (coefficient + 1) * N.of_nat (2 * count))%N.
  Proof. rewrite Nat2N.inj_mul. nia. Qed.

  Local Lemma scope_sum_product (first last count width : N) :
    (first * count * width + last * count * width =
      (first + last) * count * width)%N.
  Proof. nia. Qed.

  (** Filtering arbitrary supplied roots pays their own key widths. *)
  Local Lemma scope_root_filter_time g roots width :
    Forall (fun v => Pos.size_nat v <= width) roots ->
    (List.T_filter (fun v =>
      match trie_get v (succ (base (scc_graph g))) with Some _ => true | None => false end)
      (fun v => 1 + ((T_base (scc_graph g) + T_succ (base (scc_graph g))) +
        T_trie_get v (succ (base (scc_graph g)))))%N roots <=
      16 * N.of_nat (length roots + 1) * N.of_nat (width + 1))%N.
  Proof.
    intro Hwidth.
    assert (Hpredicate : forall v, In v roots ->
      (1 + ((T_base (scc_graph g) + T_succ (base (scc_graph g))) +
        T_trie_get v (succ (base (scc_graph g)))) <= 8 * N.of_nat (width + 1))%N).
    { intros v Hin. rewrite Forall_forall in Hwidth. specialize (Hwidth v Hin).
      PTrieT.trie_get_le. unfold T_base, T_succ.
      rewrite Nat2N.inj_add. nia. }
    pose proof (scope_filter_members_time
      (fun v => match trie_get v (succ (base (scc_graph g))) with
        Some _ => true | None => false end)
      (fun v => (1 + ((T_base (scc_graph g) + T_succ (base (scc_graph g))) +
        T_trie_get v (succ (base (scc_graph g)))))%N)
      roots (8 * N.of_nat (width + 1))%N Hpredicate) as Hfilter.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Rebuilding, searching and folding a component phase each fit the input occurrence budget. *)
  Lemma scope_components_time g roots :
    (T_wto_components g roots <=
      8 * (16384 + SccT.k_callback + search_trace_coefficient + 1) *
        N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
        N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    set (ready := scc_graph g).
    set (chosen := filter (fun v => match trie_get v (succ (base ready)) with
      Some _ => true | None => false end) roots).
    set (events := prepared_search_trace ready chosen).
    set (state := TarjanSearch.dfs ready chosen tarjan_initial).
    assert (Hchosen : forall v, In v chosen -> In v (nodes g)).
    { intros v Hin. unfold chosen in Hin. apply filter_In in Hin.
      destruct Hin as [_ Hlisted]. unfold ready in Hlisted.
      rewrite wto_scc_root_test in Hlisted. now apply wto_member_spec in Hlisted. }
    assert (Hchosen_length : length chosen <= length roots).
    { unfold chosen. apply filter_length_le. }
    assert (Hgraph_width : graph_width (base g) <=
      graph_max (graph_width (base g)) (vertex_width roots)).
    { rewrite wto_graph_max_nat. apply Nat.le_max_l. }
    assert (Hroot_width : Forall (fun v => Pos.size_nat v <=
      graph_max (graph_width (base g)) (vertex_width roots)) roots).
    { apply Forall_forall. intros v Hin. eapply Nat.le_trans.
      - exact (search_vertex_width_member roots v Hin).
      - rewrite wto_graph_max_nat. apply Nat.le_max_r. }
    pose proof (scope_root_filter_time g roots _ Hroot_width) as Hfilter.
    fold ready in Hfilter.
    pose proof (scc_graph_counted_time g) as Hprepare.
    pose proof (scc_search_time g chosen Hchosen) as Hsearch. fold ready in Hsearch.
    destruct (scc_search_sizes g chosen Hchosen) as [Hvertices Hrows].
    fold ready in Hvertices, Hrows. fold events in Hvertices, Hrows.
    pose proof (prepared_search_event_bound ready chosen) as Hlength.
    fold events in Hlength. rewrite search_event_supply_entered in Hlength.
    assert (Hwidth : Forall (SccT.event_domain (graph_width (base g))) events).
    { unfold events, ready. now apply scc_search_event_width. }
    assert (Hunique : NoDup (entered events)).
    { unfold events. apply prepared_search_unique_raw. }
    pose proof (SccT.visitor_fold_time (graph_width (base g)) events Hunique Hwidth) as Hfold.
    change (T_fold_events TarjanVisitor.enter (fun v s => TarjanVisitor.T_enter v s)
      TarjanVisitor.leave (fun v s => TarjanVisitor.T_leave v s)
      TarjanVisitor.edge (fun kind u v s => TarjanVisitor.T_edge kind u v s)
      events tarjan_initial <= SccT.k_callback * N.of_nat (length events + 1) *
        N.of_nat (graph_width (base g) + 1))%N in Hfold.
    pose proof (tarjan_emitted_count events) as Hemitted.
    change (length (tarjan_emitted state) <= length (entered events)) in Hemitted.
    set (count := graph_n (base g) + graph_e (base g) + length roots + 1) in *.
    set (width := graph_max (graph_width (base g)) (vertex_width roots)) in *.
    assert (Hprepare_budget : (T_scc_graph_counted g <=
      16384 * N.of_nat count * N.of_nat (width + 1))%N).
    { eapply N.le_trans; [exact Hprepare|]. apply scope_phase_product.
      - unfold count. lia.
      - lia. }
    assert (Hfilter_scale : (16 * N.of_nat (length roots + 1) * N.of_nat (width + 1) <=
      16 * N.of_nat count * N.of_nat (width + 1))%N).
    { apply scope_phase_product; [unfold count; lia|reflexivity]. }
    pose proof (N.le_trans _ _ _ Hfilter Hfilter_scale) as Hfilter_budget.
    assert (Hsearch_budget : (1 + T_prepared_search_trace ready chosen <=
      (2 * search_trace_coefficient) * N.of_nat count * N.of_nat (width + 1))%N).
    { eapply N.le_trans; [exact Hsearch|]. apply scope_phase_product.
      - unfold count. lia.
      - lia. }
    assert (Hfold_scale : (SccT.k_callback * N.of_nat (length events + 1) *
        N.of_nat (graph_width (base g) + 1) <=
      (2 * SccT.k_callback) * N.of_nat count * N.of_nat (width + 1))%N).
    { replace ((2 * SccT.k_callback) * N.of_nat count * N.of_nat (width + 1))%N with
        (SccT.k_callback * N.of_nat (2 * count) * N.of_nat (width + 1))%N
        by first [apply scope_double_coefficient | symmetry; apply scope_double_coefficient].
      apply scope_phase_product; [unfold count; lia|lia]. }
    pose proof (N.le_trans _ _ _ Hfold Hfold_scale) as Hfold_budget.
    assert (Hreturned : length (tarjan_emitted state) + 1 <= count).
    { unfold count. lia. }
    pose proof (time_of_nat_le _ _ Hreturned) as Hreturned_budget.
    assert (Hcount_positive : (1 <= N.of_nat count)%N).
    { apply (time_of_nat_le 1 count). unfold count. lia. }
    assert (Hwidth_positive : (1 <= N.of_nat (width + 1))%N).
    { apply (time_of_nat_le 1 (width + 1)). lia. }
    clearbody count width.
    time_unfold @T_wto_components. time_unfold @Galois.Graph.Wto.T_wto_components.
    rewrite scc_graph_counted_agrees.
    fold ready. fold chosen. fold state.
    time_unfold @TarjanSearch.T_dfs. fold events.
    unfold T_tarjan_owners, T_tarjan_emitted. rewrite wto_rev_append_clock.
    rewrite !Nat2N.inj_add in *.
    clear - Hfilter_budget Hprepare_budget Hsearch_budget Hfold_budget Hreturned_budget
      Hcount_positive Hwidth_positive. nia.
  Qed.

  Local Lemma scope_nonempty_count (cs : list (list positive)) :
    Forall (fun c => c <> []) cs -> length cs <= length (concat cs).
  Proof.
    intro Hnonempty. induction Hnonempty as [|c cs Hc Hcs IH]; [reflexivity|].
    destruct c; [contradiction|]. cbn [concat length]. rewrite length_app. cbn [length]. lia.
  Qed.

  Local Lemma scope_whole_mass g :
    source_mass g (nodes g) = graph_n (base g) + graph_e (base g).
  Proof.
    rewrite scope_mass_decompose.
    destruct g as [[vertices adjacency] predecessors n e]. reflexivity.
  Qed.

  Local Opaque Galois.Graph.Wto.wto_components.

  (** Distinct listed components consume only original source and edge occurrences. *)
  Lemma scope_actual_entries_time g roots :
    (T_wto_entries g roots (wto_components g roots) <=
      512 * (PTrieT.c_trie + 1) *
        N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
        N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    set (r := wto_components g roots).
    set (width := graph_max (graph_width (base g)) (vertex_width roots)).
    assert (Hgraph_width : graph_width (base g) <= width).
    { unfold width. rewrite wto_graph_max_nat. apply Nat.le_max_l. }
    assert (Hroot_width : Forall (fun v => Pos.size_nat v <= width) roots).
    { apply Forall_forall. intros v Hin. eapply Nat.le_trans.
      - exact (search_vertex_width_member roots v Hin).
      - unfold width. rewrite wto_graph_max_nat. apply Nat.le_max_r. }
    assert (Hlisted : forall v, In v (concat (comps r)) -> In v (nodes g)).
    { intros v Hin. unfold r in Hin. now apply (wto_components_listed g roots v). }
    assert (Hrows : Forall (fun u => Pos.size_nat u <= width /\
      Forall (fun v => Pos.size_nat v <= width) (succs (base g) u)) (concat (comps r))).
    { apply Forall_forall. intros u Hin. split.
      - eapply Nat.le_trans; [exact (scc_node_width g u (Hlisted u Hin))|exact Hgraph_width].
      - apply Forall_forall. intros v Hv. eapply Nat.le_trans; [|exact Hgraph_width].
        exact (scope_row_key_width g u v (Hlisted u Hin) Hv). }
    assert (Howners : forall u i, trie_get u (comp r) = Some i -> Pos.size_nat i <= width + 1).
    { intros u i Hlookup. unfold r in Hlookup.
      pose proof (wto_components_owner_width g roots u i Hlookup) as Howner.
      eapply Nat.le_trans; [exact Howner|]. now apply Nat.add_le_mono_r. }
    pose proof (scope_entries_time g roots r width Hroot_width Hrows Howners) as Htime.
    pose proof (wto_components_unique g roots) as Hunique. fold r in Hunique.
    pose proof (scc_weight_incl (fun v => 1 + length (succs (base g) v))
      (concat (comps r)) (nodes g) Hunique Hlisted) as Hmass.
    change (source_mass g (concat (comps r)) <= source_mass g (nodes g)) in Hmass.
    rewrite scope_whole_mass in Hmass.
    pose proof (scope_nonempty_count (comps r) (wto_components_nonempty g roots)) as Hcount.
    pose proof (wto_components_size g roots) as Hsize.
    change (length (concat (comps r)) <= length (nodes g)) in Hsize.
    assert (Hnodes : length (nodes g) = graph_n (base g)).
    { destruct g as [[vertices adjacency] predecessors n e]. reflexivity. }
    rewrite Hnodes in Hsize. eapply N.le_trans; [exact Htime|].
    clear Htime Hroot_width Hrows Howners Hunique Hlisted. clearbody r.
    apply N.mul_le_mono_r.
    replace (512 * (PTrieT.c_trie + 1) *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1))%N with
      (256 * (PTrieT.c_trie + 1) *
        N.of_nat (2 * (graph_n (base g) + graph_e (base g) + length roots + 1)))%N
      by first [apply scope_entry_coefficient | symmetry; apply scope_entry_coefficient].
    apply N.mul_le_mono_l. apply time_of_nat_le. clear - Hmass Hcount Hsize. lia.
  Qed.

  Local Transparent Galois.Graph.Wto.wto_components.

  Local Lemma scope_initial_coefficient :
    (8 * (16384 + SccT.k_callback + search_trace_coefficient + 1) +
      512 * (PTrieT.c_trie + 1) <= k_build)%N.
  Proof. unfold k_build. lia. Qed.


  (** Initial components and entries pay the listed graph and the supplied roots. *)
  Local Opaque loopN prepared_search_trace.

  Lemma T13_initial : forall g roots,
      (T_wto_components g roots + T_wto_entries g roots (wto_components g roots) <=
        k_build * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
        N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    intros g roots.
    pose proof (scope_components_time g roots) as Hcomponents.
    pose proof (scope_actual_entries_time g roots) as Hentries.
    eapply N.le_trans.
    - apply N.add_le_mono; [exact Hcomponents|exact Hentries].
    - clear Hcomponents Hentries.
      set (count := N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1)).
      set (width := N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1)).
      replace (8 * (16384 + SccT.k_callback + search_trace_coefficient + 1) * count * width +
        512 * (PTrieT.c_trie + 1) * count * width)%N with
        ((8 * (16384 + SccT.k_callback + search_trace_coefficient + 1) +
          512 * (PTrieT.c_trie + 1)) * count * width)%N
        by first [apply scope_sum_product | symmetry; apply scope_sum_product].
      apply N.mul_le_mono_r. apply N.mul_le_mono_r. exact scope_initial_coefficient.
  Qed.

  Local Lemma scope_scale_algebra (b x y : N) :
    ((2 * b) * (x * y) = b * (2 * x) * y)%N.
  Proof. nia. Qed.

  Local Lemma scope_count_width_bound (coefficient : N) (size mass width bound : nat) :
    size <= 2 * mass -> width <= bound ->
    (coefficient * N.of_nat size * N.of_nat (width + 1) <=
      (2 * coefficient) * N.of_nat (mass * (bound + 1)))%N.
  Proof.
    intros Hsize Hwidth. rewrite Nat2N.inj_mul.
    rewrite (scope_scale_algebra coefficient (N.of_nat mass) (N.of_nat (bound + 1))).
    apply N.mul_le_mono.
    - apply N.mul_le_mono_l.
      pose proof (time_of_nat_le size (2 * mass) Hsize) as Hcount.
      rewrite Nat2N.inj_mul in Hcount. exact Hcount.
    - apply time_of_nat_le. now apply Nat.add_le_mono_r.
  Qed.

  (** Scoped components and entries read the materialized rows once. *)
  Lemma T12_scoped : forall g vs, NoDup vs -> (forall v, In v vs -> In v (nodes g)) ->
      (T_wto_components (wto_scoped g (Some vs)) (rev vs) +
        T_wto_entries (wto_scoped g (Some vs)) (rev vs)
          (wto_components (wto_scoped g (Some vs)) (rev vs)) <=
      k_scope * N.of_nat (scope_work g vs))%N.
  Proof.
    intros g vs Hunique Hlisted.
    exact (N.le_trans _ _ _
      (T13_initial (wto_scoped g (Some vs)) (rev vs))
      (scope_count_width_bound k_build
        (graph_n (base (wto_scoped g (Some vs))) +
          graph_e (base (wto_scoped g (Some vs))) + length (rev vs) + 1)
        (source_mass g vs + 1)
        (graph_max (graph_width (base (wto_scoped g (Some vs)))) (vertex_width (rev vs)))
        (graph_max (graph_width (base g)) (vertex_width vs))
        (scope_graph_size g vs) (scope_phase_width g vs))).
  Qed.

  Local Transparent loopN prepared_search_trace.

  Local Opaque loopN Galois.Graph.Wto.wto_components.

  (** A globally unique component inventory makes every individual block unique. *)
  Lemma component_lists_unique : forall cs,
    NoDup (concat cs) -> Forall (@NoDup positive) cs.
  Proof.
    intro cs. induction cs as [|c rest IH]; intro Hunique; [constructor|].
    cbn [concat] in Hunique. constructor.
    - now apply NoDup_app_remove_r in Hunique.
    - apply IH. now apply NoDup_app_remove_l in Hunique.
  Qed.

  (** Actual expansion tasks retain listed distinct vertices and bounded component identifiers. *)
  Definition task_domain g task :=
    match task with
    | WtoExpand _ _ owners c => c <> [] /\ NoDup c /\
        (forall v, In v c -> In v (nodes g)) /\
        (forall v i, trie_get v owners = Some i ->
          Pos.size_nat i <= graph_width (base g) + 1)
    | WtoClose _ => True
    end.

  Lemma components_task_domain : forall g graph roots within entries,
    (forall v, In v (nodes graph) -> In v (nodes g)) ->
    Forall (task_domain g)
      (wto_expand_tasks within entries (comp (wto_components graph roots))
        (rev (comps (wto_components graph roots)))).
  Proof.
    intros g graph roots within entries Hsub.
    pose proof (component_lists_unique _ (wto_components_unique graph roots)) as Hunique.
    pose proof (wto_components_nonempty graph roots) as Hnonempty.
    rewrite Forall_forall in Hunique, Hnonempty.
    assert (Howners : forall v i, trie_get v (comp (wto_components graph roots)) = Some i ->
      Pos.size_nat i <= graph_width (base g) + 1).
    { intros v i Howner. eapply (wto_components_owner_bound graph roots).
      - apply Forall_forall. intros u Hu. apply wto_listed_width, Hsub, Hu.
      - exact Howner. }
    change (wto_expand_tasks within entries (comp (wto_components graph roots))
      (rev (comps (wto_components graph roots)))) with
      (map (fun c => WtoExpand within entries (comp (wto_components graph roots)) c)
        (rev (comps (wto_components graph roots)))).
    rewrite Forall_map. apply Forall_rev. apply Forall_forall. intros c Hc.
    cbn [task_domain]. split; [now apply Hnonempty|]. split; [now apply Hunique|].
    split; [|exact Howners]. intros v Hv. apply Hsub.
    apply (wto_components_listed graph roots v). apply in_concat. exists c. auto.
  Qed.

  Lemma initial_task_domain : forall g roots,
    Forall (task_domain g) (wto_tasks (initial g roots)).
  Proof.
    intros g roots. unfold initial. cbn [wto_tasks]. apply components_task_domain.
    intros v Hin. exact Hin.
  Qed.

  Lemma task_domain_step : forall g st next,
    Forall (task_domain g) (wto_tasks st) -> wto_step g st = inl next ->
    Forall (task_domain g) (wto_tasks next).
  Proof.
    intros g [tasks partial parents] next Hdomain Hstep.
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    inversion Hdomain as [|? ? Hhead Htail]; subst.
    destruct task as [within entries owners c|h].
    - cbn [task_domain] in Hhead. destruct Hhead as [Hnonempty [Hunique [Hlisted Howners]]].
      unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select
        (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + destruct body as [|v body]; inversion Hstep; subst next.
        * exact Htail.
        * cbn [wto_tasks]. rewrite !rev_append_rev, !app_nil_r.
          apply Forall_app. split.
          -- apply components_task_domain. intros u Hu.
             change (In u (v :: body)) in Hu. apply Hlisted.
             eapply Permutation_in.
             ++ apply Permutation_sym. exact (wto_select_spec _ _ _ _ Hselect).
             ++ right. exact Hu.
          -- constructor; [exact I|exact Htail].
      + inversion Hstep; subst next. exact Htail.
    - destruct parents; inversion Hstep; subst next; exact Htail.
  Qed.

  Local Opaque prepared_search_trace.

  Local Lemma inventory_rotate {A} (head : A) first rest :
    Permutation (head :: first ++ rest) (first ++ head :: rest).
  Proof.
    induction first as [|x first IH]; cbn [app]; [reflexivity|].
    eapply Permutation_trans; [apply perm_swap|]. now apply perm_skip.
  Qed.

  (** Reversing the outer constructors changes only the order of their vertex inventory. *)
  Local Lemma inventory_reverse w tail :
    Permutation (wto_order (Galois.Graph.Wto.wto_reverse_into w tail))
      (wto_order w ++ wto_order tail).
  Proof.
    revert tail. induction w as [|v rest IH|h body IHbody rest IHrest]; intro tail.
    - reflexivity.
    - cbn [Galois.Graph.Wto.wto_reverse_into].
      eapply Permutation_trans; [apply IH|]. cbn [wto_order].
      apply Permutation_sym. apply inventory_rotate.
    - cbn [Galois.Graph.Wto.wto_reverse_into].
      eapply Permutation_trans; [apply IHrest|]. cbn [wto_order].
      eapply Permutation_trans.
      + exact (Permutation_sym (inventory_rotate h (wto_order rest)
          (wto_order body ++ wto_order tail))).
      + apply perm_skip. rewrite !app_assoc.
        apply Permutation_app_tail. apply Permutation_app_comm.
  Qed.

  Local Lemma inventory_single_order c (h : positive) pending partial parents heads :
    Permutation c [h] ->
    Permutation (c ++ pending ++ partial ++ parents ++ heads)
      (pending ++ h :: (partial ++ parents ++ heads)).
  Proof.
    intro Hselect. eapply Permutation_trans.
    - apply Permutation_app_tail. exact Hselect.
    - cbn [app]. apply inventory_rotate.
  Qed.

  Local Lemma inventory_expand_order c (h : positive) body children pending partial parents heads :
    Permutation c (h :: body) -> Permutation children body ->
    Permutation (c ++ pending ++ partial ++ parents ++ heads)
      (children ++ pending ++ partial ++ parents ++ h :: heads).
  Proof.
    intros Hselect Hchildren. eapply Permutation_trans.
    - apply Permutation_app_tail. exact Hselect.
    - cbn [app]. eapply Permutation_trans.
      + rewrite !app_assoc. apply inventory_rotate.
      + rewrite <- !app_assoc. apply Permutation_app_tail.
        now apply Permutation_sym.
  Qed.

  Local Lemma inventory_close_order (h : positive) pending partial reversed parent parents heads :
    Permutation reversed partial ->
    Permutation (pending ++ partial ++ parent ++ parents ++ h :: heads)
      (pending ++ h :: (reversed ++ parent ++ parents ++ heads)).
  Proof.
    intro Hreverse. apply Permutation_app_head. eapply Permutation_trans.
    - rewrite !app_assoc. apply Permutation_sym. apply inventory_rotate.
    - apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_tail.
      now apply Permutation_sym.
  Qed.


  Local Lemma inventory_heads_app first rest :
    fold_right (fun task hs => match task with WtoClose h => h :: hs | _ => hs end) []
      (first ++ rest) =
    fold_right (fun task hs => match task with WtoClose h => h :: hs | _ => hs end) [] first ++
    fold_right (fun task hs => match task with WtoClose h => h :: hs | _ => hs end) [] rest.
  Proof.
    induction first as [|task first IH]; [reflexivity|].
    destruct task; cbn [app fold_right]; now rewrite IH.
  Qed.

  (** Every reachable pending component remains distinct and nonempty. *)
  Lemma inventory_iter_domain g roots n :
    Forall (task_domain g) (wto_tasks (Nat.iter n (advance g) (initial g roots))).
  Proof.
    induction n as [|n IH]; [apply initial_task_domain|].
    rewrite Nat.iter_succ. unfold advance at 1.
    destruct (wto_step g (Nat.iter n (advance g) (initial g roots))) as [next|result] eqn:Hstep.
    - eapply task_domain_step; eassumption.
    - exact IH.
  Qed.

  (** Each transition moves, selects or closes vertices without changing their inventory. *)
  Lemma inventory_step g vertices st next :
    Forall (task_domain g) (wto_tasks st) ->
    inventory vertices st -> wto_step g st = inl next -> inventory vertices next.
  Proof.
    intros Hdomain [Horder Hbalance] Hstep. split.
    2: { change (frames_balanced next). eapply frames_balanced_step; eassumption. }
    destruct st as [tasks partial parents].
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    inversion Hdomain as [|? ? Hhead Htail]; subst.
    destruct task as [within entries owners c|h].
    - cbn [task_domain] in Hhead. destruct Hhead as [Hnonempty [Hunique [Hlisted Howners]]].
      unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select
        (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + pose proof (wto_select_spec _ _ _ _ Hselect) as Hselect_perm.
        destruct body as [|v body]; inversion Hstep; subst next.
        * cbn [wto_tasks wto_partial wto_parents map concat task_members fold_right] in Horder.
          destruct (Galois.Graph.Wto.wto_member h (succs (base g) h));
            cbn [wto_tasks wto_partial wto_parents wto_order app];
            repeat rewrite <- app_assoc in Horder;
            repeat rewrite <- app_assoc;
            (eapply Permutation_trans; [exact Horder|now apply inventory_single_order]).
        * assert (Hbody : NoDup (v :: body)).
          { pose proof (Permutation_NoDup Hselect_perm Hunique) as Hselected.
            inversion Hselected. assumption. }
          pose proof (proj1 (F13_partition g (v :: body) Hbody)) as Hpartition.
          rewrite !rev_append_rev, !app_nil_r.
          cbn [wto_tasks wto_partial wto_parents wto_order].
          rewrite map_app, concat_app, inventory_heads_app.
          rewrite (proj1 (expand_inventory _ _ _ _)),
            (proj1 (proj2 (expand_inventory _ _ _ _))).
          cbn [map concat task_members fold_right wto_order app].
          cbn [wto_tasks wto_partial wto_parents map concat task_members fold_right] in Horder.
          repeat rewrite <- app_assoc in Horder. repeat rewrite <- app_assoc.
          eapply Permutation_trans; [exact Horder|].
          eapply inventory_expand_order; [exact Hselect_perm|].
          eapply Permutation_trans; [apply Permutation_sym, components_reverse|exact Hpartition].
      + apply wto_select_empty in Hselect. contradiction.
    - cbn [wto_tasks wto_parents filter length] in Hbalance.
      destruct parents as [|parent parents].
      + cbn [length] in Hbalance. discriminate.
      + inversion Hstep; subst next.
        cbn [wto_tasks wto_partial wto_parents map concat task_members fold_right wto_order app] in Horder |- *.
        repeat rewrite <- app_assoc in Horder. repeat rewrite <- app_assoc.
        eapply Permutation_trans; [exact Horder|].
        apply inventory_close_order.
        pose proof (inventory_reverse partial WNil) as Hreverse.
        cbn [wto_order] in Hreverse. now rewrite app_nil_r in Hreverse.
  Qed.

  Lemma F15_step : forall g roots st next,
    invariant g roots st -> wto_step g st = inl next ->
    invariant g roots next /\ potential g next < potential g st.
  Proof.
    intros g roots st next.
    intros [[n Hreachable] Hinventory] Hstep.
    pose proof (inventory_iter_domain g roots n) as Hdomain. rewrite Hreachable in Hdomain.
    split.
    - split.
      + exists (S n). rewrite Nat.iter_succ, Hreachable. unfold advance. now rewrite Hstep.
      + eapply inventory_step; eassumption.
    - change (wto_pending_credit (wto_tasks next) < wto_pending_credit (wto_tasks st)).
      apply (wto_step_credit g st next); [|exact Hstep].
      unfold wto_expansions_nonempty. eapply Forall_impl; [|exact Hdomain].
      intros task Htask. destruct task; [exact (proj1 Htask)|exact I].
  Qed.

  Local Transparent prepared_search_trace.

  Lemma history_from_domain : forall g fuel st,
    Forall (task_domain g) (wto_tasks st) ->
    Forall (fun current => Forall (task_domain g) (wto_tasks current))
      (history_from g fuel st).
  Proof.
    intros g fuel. induction fuel as [|fuel IH]; intros st Hdomain.
    - cbn [history_from]. destruct (wto_step g st); constructor; auto.
    - cbn [history_from]. destruct (wto_step g st) as [next|result] eqn:Hstep.
      + constructor; [exact Hdomain|]. apply IH. eapply task_domain_step; eassumption.
      + constructor; [exact Hdomain|constructor].
  Qed.

  Lemma history_task_domain : forall g roots st,
    In st (history g roots) -> Forall (task_domain g) (wto_tasks st).
  Proof.
    intros g roots st Hin.
    pose proof (history_from_domain g
      (3 * length (concat (comps (wto_components g roots))) + 1)
      (initial g roots) (initial_task_domain g roots)) as Hall.
    apply Forall_forall with (x := st) in Hall; [exact Hall|exact Hin].
  Qed.

  Lemma history_component_domain : forall g roots st within entries owners c tasks,
    In st (history g roots) -> wto_tasks st = WtoExpand within entries owners c :: tasks ->
    c <> [] /\ NoDup c /\ (forall v, In v c -> In v (nodes g)) /\
    (forall v i, trie_get v owners = Some i -> Pos.size_nat i <= graph_width (base g) + 1).
  Proof.
    intros g roots st within entries owners c tasks Hin Htasks.
    pose proof (history_task_domain g roots st Hin) as Hall. rewrite Htasks in Hall.
    inversion Hall as [|? ? Hhead Htail]. exact Hhead.
  Qed.

  Lemma history_body_domain : forall g roots st within entries owners c tasks h body,
    In st (history g roots) -> wto_tasks st = WtoExpand within entries owners c :: tasks ->
    wto_select (wto_preferred owners entries c) c = Some (h, body) ->
    NoDup body /\ (forall v, In v body -> In v (nodes g)).
  Proof.
    intros g roots st within entries owners c tasks h body Hin Htasks Hselect.
    destruct (history_component_domain g roots st within entries owners c tasks Hin Htasks)
      as [Hnonempty [Hunique [Hlisted Howners]]].
    pose proof (wto_select_spec _ _ _ _ Hselect) as Hselection. split.
    - apply (Permutation_NoDup Hselection) in Hunique. now inversion Hunique.
    - intros v Hv. apply Hlisted. eapply Permutation_in.
      + exact (Permutation_sym Hselection).
      + right. exact Hv.
  Qed.

  (** Every vertex contributes at least one unit of source mass. *)
  Lemma source_mass_length : forall g vs, length vs <= source_mass g vs.
  Proof.
    intros g vs. unfold source_mass. induction vs as [|v rest IH]; cbn [length fold_right]; lia.
  Qed.

  (** Preference and selection scan an actual component once. *)
  Lemma T14_select : forall g roots st within entries owners c tasks,
      In st (history g roots) -> wto_tasks st = WtoExpand within entries owners c :: tasks ->
      (T_wto_preferred owners entries c + T_wto_select (wto_preferred owners entries c) c <=
        k_expand * N.of_nat (scope_work g c))%N.
  Proof.
    intros g roots st within entries owners c tasks Hin Htasks.
    destruct (history_component_domain g roots st within entries owners c tasks Hin Htasks)
      as [Hnonempty [Hunique [Hlisted Howners]]].
    assert (Hwidth : Forall (fun v => Pos.size_nat v <= graph_width (base g)) c).
    { apply Forall_forall. intros v Hv. apply wto_listed_width, Hlisted, Hv. }
    pose proof (wto_selection_clock owners entries c (graph_width (base g)) Hwidth Howners)
      as Hclock.
    pose proof (source_mass_length g c) as Hmass.
    assert (Hmax : graph_width (base g) <=
      graph_max (graph_width (base g)) (vertex_width c)).
    { rewrite wto_graph_max_nat. apply Nat.le_max_l. }
    clear - Hclock Hmass Hmax.
    unfold T_wto_preferred, T_wto_select, wto_preferred, k_expand, scope_work.
    time_simpl. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components.

  Local Opaque loopN.

  (** A short step pays its component row or the partial output that it reverses. *)
  Definition short_mass (g : prepared) (st : wto_state) : nat :=
    match wto_tasks st with
    | WtoExpand _ _ _ c :: _ => source_mass g c
    | _ => length (wto_order (wto_partial st))
    end.

  Lemma short_step_clock : forall g roots st,
    In st (history g roots) ->
    (forall within entries owners c tasks h body,
      wto_tasks st = WtoExpand within entries owners c :: tasks ->
      wto_select (wto_preferred owners entries c) c = Some (h, body) -> body = []) ->
    (T_wto_step g st <= k_expand * N.of_nat (short_mass g st + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g roots [tasks partial parents] Hin Hshort.
    destruct tasks as [|task tasks].
    - pose proof (wto_reverse_clock partial WNil) as Hreverse.
      unfold k_expand, short_mass. cbn [wto_tasks wto_partial].
      time_unfold @T_wto_step. time_unfold @Galois.Graph.Wto.T_wto_step.
      time_simpl. rewrite !Nat2N.inj_add in *. nia.
    - destruct task as [within entries owners c|h].
      + destruct (history_component_domain g roots
          (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
          within entries owners c tasks Hin eq_refl)
          as [Hnonempty [Hunique [Hlisted Howners]]].
        assert (Hwidth : Forall (fun v => Pos.size_nat v <= graph_width (base g)) c).
        { apply Forall_forall. intros v Hv. apply wto_listed_width, Hlisted, Hv. }
        pose proof (wto_selection_clock owners entries c (graph_width (base g))
          Hwidth Howners) as Hselection_clock.
        destruct (Galois.Graph.Wto.wto_select
          (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
        * pose proof (Hshort within entries owners c tasks h body eq_refl Hselect) as Hbody.
          subst body.
          pose proof (wto_select_spec _ _ _ _ Hselect) as Hpermutation.
          pose proof (Permutation_length Hpermutation) as Hlength.
          cbn [length] in Hlength. rewrite Hlength in Hselection_clock.
          pose proof (source_mass_permutation g _ _ Hpermutation) as Hmass.
          change (source_mass g c = 1 + length (succs (base g) h) + 0) in Hmass.
          rewrite Nat.add_0_r in Hmass.
          assert (Hhead : Pos.size_nat h <= graph_width (base g)).
          { apply wto_listed_width, Hlisted. eapply Permutation_in.
            - exact (Permutation_sym Hpermutation).
            - now left. }
          pose proof (search_succs_clock (base g) h) as Hrow.
          pose proof (wto_member_clock h (succs (base g) h)) as Hmember.
          clear Hin Hshort Hnonempty Hunique Hlisted Howners Hwidth Hpermutation Hlength.
          unfold k_expand, short_mass. cbn [wto_tasks wto_partial]. rewrite Hmass.
          time_unfold @T_wto_step. time_unfold @Galois.Graph.Wto.T_wto_step.
          rewrite Hselect. cbn beta iota zeta.
          destruct (Galois.Graph.Wto.wto_member h (succs (base g) h));
            time_simpl; rewrite !Nat2N.inj_add in *; nia.
        * apply wto_select_empty in Hselect. contradiction.
      + pose proof (wto_reverse_clock partial WNil) as Hreverse.
        unfold k_expand, short_mass. cbn [wto_tasks wto_partial].
        destruct parents;
          time_unfold @T_wto_step; time_unfold @Galois.Graph.Wto.T_wto_step;
          time_simpl; rewrite !Nat2N.inj_add in *; nia.
  Qed.

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
  Proof.
    intros g roots st Hin Hshort.
    pose proof (short_step_clock g roots st Hin Hshort) as Hclock.
    assert (Hmass : short_mass g st <= length (wto_order (wto_partial st)) +
      source_mass g (concat (map task_members (firstn 1 (wto_tasks st))))).
    { destruct st as [tasks partial parents]. destruct tasks as [|task tasks];
        [cbn [short_mass wto_tasks wto_partial firstn map concat source_mass]; lia|].
      destruct task; cbn [short_mass wto_tasks wto_partial firstn map concat task_members].
      - rewrite app_nil_r. lia.
      - cbn [source_mass]. lia. }
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Local Transparent loopN.

  (** Concatenation visits each component cell and each of its vertices once. *)
  Lemma components_concat_clock : forall (cs : list (list positive)),
    (TimeHelpers.List.T_concat cs <=
      N.of_nat (length (concat cs) + 2 * length cs + 1))%N.
  Proof.
    intro cs. induction cs as [|c cs IH].
    - time_step.
    - pose proof (Datatypes.T_app_le c (concat cs)) as Happ.
      time_unfold @TimeHelpers.List.T_concat. time_cbn.
      rewrite length_app, !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** Every driver callback on a completed path appears in the recorded history. *)
  Lemma history_path_cost : forall g st states last,
    search_machine_path (wto_step g) st states last -> forall fuel w,
    loop_fuel (wto_step g) fuel st = inr w ->
    (fold_right N.add 0%N (map (T_wto_step g) states) +
      match wto_step g last with inl _ => 0 | inr _ => T_wto_step g last end <=
      execution_cost g (history_from g fuel st))%N.
  Proof.
    intros g st states last Hpath. induction Hpath as
      [st|st next states last Hstep Hpath IH]; intros fuel w Hrun.
    - cbn [map fold_right]. destruct (wto_step g st) as [next|result] eqn:Hstep.
      + apply N.le_0_l.
      + destruct fuel; cbn [history_from]; rewrite Hstep; unfold execution_cost;
          cbn [fold_right]; lia.
    - destruct fuel as [|fuel]; [discriminate|]. cbn [loop_fuel] in Hrun.
      rewrite Hstep in Hrun. specialize (IH fuel w Hrun).
      cbn [history_from]. rewrite Hstep. unfold execution_cost in *.
      cbn [map fold_right]. lia.
  Qed.

  Local Opaque loopN.

  (** The loop's administrative cost is linear in the initial component inventory. *)
  Lemma build_loop_clock : forall g roots,
    (T_loopN (wto_step g) (fun st => T_wto_step g st)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots) <= execution_cost g (history g roots) +
      18 * N.of_nat (length (concat (comps (wto_components g roots)))) + 9)%N.
  Proof.
    intros g roots. destruct (F16_done g roots) as [w Hrun].
    rewrite search_loopN_fuel, Nat2N.id in Hrun.
    destruct (search_loop_trace_clock (wto_step g) (fun st => T_wto_step g st)
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots)) as [states [last [Hpath [Hlength Hclock]]]].
    pose proof (history_path_cost g _ _ _ Hpath _ w Hrun) as Hhistory.
    change (fold_right N.add 0%N (map (fun st => T_wto_step g st) states) +
      match wto_step g last with inl _ => 0 | inr _ => T_wto_step g last end <=
      execution_cost g (history_from g
        (3 * length (concat (comps (wto_components g roots))) + 1) (initial g roots)))%N
      in Hhistory.
    pose proof (search_N_size_value
      (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))) as Hbits.
    rewrite Nat2N.id in Hlength, Hbits. unfold history.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *.
    nia.
  Qed.

  (** Building pays the initial phases, the task list and each recorded step once. *)
  Local Opaque loopN prepared_search_trace Galois.Graph.Wto.wto_components.

  Local Lemma build_constant_clock : forall g roots,
    (T_build g roots <= 128 * (T_wto_components g roots +
      T_wto_entries g roots (wto_components g roots) +
      N.of_nat (length (concat (comps (wto_components g roots)))) +
      execution_cost g (history g roots) + 1))%N.
  Proof.
    intros g roots.
    pose proof (build_loop_clock g roots) as Hloop.
    pose proof (components_concat_clock (comps (wto_components g roots))) as Hconcat.
    pose proof (wto_components_output_clock g roots) as Hcomponents.
    pose proof (Datatypes.T_length_le (concat (comps (wto_components g roots)))) as Hlength.
    pose proof (List.T_rev_append_le (comps (wto_components g roots)) []) as Hrev.
    pose proof (wto_expand_tasks_clock None
      (wto_entries g roots (wto_components g roots)) (comp (wto_components g roots))
      (rev_append (comps (wto_components g roots)) [])) as Htasks.
    pose proof (Nat.T_mul_le 3 (length (concat (comps (wto_components g roots))))) as Hmultiply.
    pose proof (Nat.T_add_le (3 * length (concat (comps (wto_components g roots)))) 1) as Hadd.
    pose proof (graph_of_nat_time
      (3 * length (concat (comps (wto_components g roots))) + 1)) as Hfuel.
    assert (Hcallback : forall st,
      (Galois.Graph.Wto.T_wto_step g st <= T_wto_step g st)%N).
    { intro st. time_unfold @T_wto_step. lia. }
    pose proof (search_binary_clock_mono (wto_step g)
      (fun st => Galois.Graph.Wto.T_wto_step g st) (fun st => T_wto_step g st)
      Hcallback (N.of_nat (3 * length (concat (comps (wto_components g roots))) + 1))
      (initial g roots)) as Hmono.
    destruct (F16_done g roots) as [w Hrun].
    unfold initial in Hloop, Hmono, Hrun.
    unfold wto_components, wto_entries, wto_expand_tasks, wto_step in *.
    rewrite rev_append_rev, app_nil_r, length_rev in Htasks.
    time_unfold @T_build.
    rewrite rev_append_rev, app_nil_r, Hrun.
    unfold T_wto_components, T_wto_entries. time_simpl.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. lia.
  Qed.

  Lemma T16_build : forall g roots,
    (T_build g roots <= k_build * (T_wto_components g roots +
      T_wto_entries g roots (wto_components g roots) +
      N.of_nat (length (concat (comps (wto_components g roots)))) +
      execution_cost g (history g roots) + 1))%N.
  Proof.
    assert (Hcoefficient : (128 <= k_build)%N) by (unfold k_build; lia).
    intros g roots. eapply N.le_trans; [exact (build_constant_clock g roots)|].
    now apply N.mul_le_mono_r.
  Qed.

  Local Transparent prepared_search_trace Galois.Graph.Wto.wto_components.

  Local Transparent loopN.

  (** Sibling reversal preserves every emitted vertex occurrence. *)
  Lemma reverse_into_length : forall w tail,
    length (wto_order (wto_reverse_into w tail)) =
      length (wto_order w) + length (wto_order tail).
  Proof.
    intro w. unfold wto_reverse_into. induction w as
      [|v rest IH|h body IHbody rest IHrest]; intro tail.
    - reflexivity.
    - cbn [Galois.Graph.Wto.wto_reverse_into]. rewrite IH.
      cbn [wto_order length]. lia.
    - cbn [Galois.Graph.Wto.wto_reverse_into]. rewrite IHrest.
      cbn [wto_order length]. rewrite !length_app. lia.
  Qed.

  (** Suspended output can be charged only at its current depth or an outer one. *)
  Fixpoint suspended_credit level depth parents :=
    match parents with
    | [] => 0
    | parent :: rest =>
      (if Nat.leb level depth then length (wto_order parent) else 0) +
        suspended_credit level (Nat.pred depth) rest
    end.

  Definition partial_stack_credit level depth partial parents :=
    (if Nat.leb level depth then length (wto_order partial) else 0) +
      suspended_credit level (Nat.pred depth) parents.

  (** Pending component vertices may still reach any level; a close head only moves outward. *)
  Fixpoint partial_tasks_credit level depth tasks :=
    match tasks with
    | [] => 0
    | WtoExpand _ _ _ c :: tasks => length c + partial_tasks_credit level depth tasks
    | WtoClose _ :: tasks =>
      (if Nat.leb level (Nat.pred depth) then 1 else 0) +
        partial_tasks_credit level (Nat.pred depth) tasks
    end.

  Definition partial_credit level st :=
    partial_tasks_credit level (length (wto_parents st)) (wto_tasks st) +
      partial_stack_credit level (length (wto_parents st))
        (wto_partial st) (wto_parents st).

  Definition partial_entry level st :=
    if Nat.eqb (length (wto_parents st)) level then
      match wto_tasks st with
      | [] | WtoClose _ :: _ => length (wto_order (wto_partial st))
      | _ => 0
      end
    else 0.

  Definition partial_mass level states :=
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then
        match wto_tasks st with
        | [] | WtoClose _ :: _ => length (wto_order (wto_partial st)) + n
        | _ => n
        end
      else n) 0 states.

  Lemma partial_mass_cons : forall level st states,
    partial_mass level (st :: states) = partial_entry level st + partial_mass level states.
  Proof.
    intros level st states. unfold partial_mass, partial_entry. cbn [fold_right].
    destruct (Nat.eqb (length (wto_parents st)) level); [|reflexivity].
    destruct (wto_tasks st) as [|task tasks]; [reflexivity|]. destruct task; reflexivity.
  Qed.

  Lemma partial_entry_credit : forall level st, partial_entry level st <= partial_credit level st.
  Proof.
    intros level st. unfold partial_entry, partial_credit, partial_stack_credit.
    destruct (Nat.eqb (length (wto_parents st)) level) eqn:Hlevel; [|lia].
    apply Nat.eqb_eq in Hlevel. subst level. rewrite Nat.leb_refl.
    destruct (wto_tasks st) as [|task tasks]; [lia|]. destruct task; lia.
  Qed.

  Lemma partial_tasks_expands : forall level depth within entries owners cs tasks,
    partial_tasks_credit level depth (wto_expand_tasks within entries owners cs ++ tasks) =
      length (concat cs) + partial_tasks_credit level depth tasks.
  Proof.
    intros level depth within entries owners cs tasks.
    change (wto_expand_tasks within entries owners cs) with
      (map (fun c => WtoExpand within entries owners c) cs).
    induction cs as [|c rest IH]; cbn [map app concat partial_tasks_credit]; [reflexivity|].
    rewrite IH, length_app. lia.
  Qed.

  Local Opaque loopN Galois.Graph.Wto.wto_components.

  (** A close at the chosen depth spends exactly the partial output it moves outward. *)
  Lemma partial_credit_step : forall g level st next,
    frames_balanced st -> wto_step g st = inl next ->
      partial_entry level st + partial_credit level next <= partial_credit level st.
  Proof.
    intros g level [tasks partial parents] next Hbalance Hstep.
    destruct tasks as [|task tasks]; [discriminate Hstep|].
    destruct task as [within entries owners c|h].
    - unfold wto_step in Hstep. rewrite wto_step_agrees in Hstep.
      cbn [wto_step_spec] in Hstep.
      destruct (Galois.Graph.Wto.wto_select
        (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
      + pose proof (Permutation_length (wto_select_spec _ _ _ _ Hselect)) as Hlength.
        destruct body as [|v body].
        * inversion Hstep; subst next. cbn [length] in Hlength.
          unfold partial_entry, partial_credit, partial_stack_credit.
          cbn [wto_tasks wto_parents wto_partial partial_tasks_credit].
          destruct (Galois.Graph.Wto.wto_member h (succs (base g) h));
            cbn [wto_order length app];
            destruct (Nat.eqb (length parents) level), (Nat.leb level (length parents)); lia.
        * inversion Hstep; subst next.
          pose proof (wto_components_size (Galois.Graph.Wto.wto_scoped g (Some (v :: body)))
            (rev (v :: body))) as Hchild.
          rewrite !rev_append_rev, !app_nil_r.
          set (cs := comps (Galois.Graph.Wto.wto_components
            (Galois.Graph.Wto.wto_scoped g (Some (v :: body)))
            (rev (v :: body)))) in *.
          change (length (concat cs) <= length (v :: body)) in Hchild.
          clear Hstep Hselect.
          unfold partial_entry, partial_credit, partial_stack_credit.
          cbn [wto_tasks wto_parents wto_partial length].
          rewrite partial_tasks_expands. cbn [partial_tasks_credit suspended_credit Nat.pred].
          change ((if Nat.eqb (length parents) level then 0 else 0) +
            (length (concat (rev cs)) +
              ((if Nat.leb level (length parents) then 1 else 0) +
                partial_tasks_credit level (length parents) tasks) +
              ((if Nat.leb level (S (length parents)) then 0 else 0) +
                ((if Nat.leb level (length parents) then length (wto_order partial) else 0) +
                  suspended_credit level (Nat.pred (length parents)) parents))) <=
            length c + partial_tasks_credit level (length parents) tasks +
              ((if Nat.leb level (length parents) then length (wto_order partial) else 0) +
                suspended_credit level (Nat.pred (length parents)) parents)).
          clearbody cs.
          rewrite <- (Permutation_length (wto_components_reverse cs)).
          cbn [wto_order length] in Hlength, Hchild |- *.
          destruct (Nat.eqb (length parents) level), (Nat.leb level (length parents)),
            (Nat.leb level (S (length parents))); lia.
      + apply wto_select_empty in Hselect. subst c. inversion Hstep; subst next.
        unfold partial_entry, partial_credit, partial_stack_credit.
        cbn [wto_tasks wto_parents wto_partial partial_tasks_credit length].
        destruct (Nat.eqb (length parents) level); lia.
    - unfold frames_balanced in Hbalance.
      cbn [wto_tasks wto_parents filter length] in Hbalance.
      destruct parents as [|parent parents]; [cbn [length] in Hbalance; lia|].
      inversion Hstep; subst next.
      unfold partial_entry, partial_credit, partial_stack_credit.
      cbn [wto_tasks wto_parents wto_partial length partial_tasks_credit suspended_credit Nat.pred].
      cbn [wto_order length]. rewrite length_app, reverse_into_length.
      cbn [wto_order length].
      destruct (Nat.eqb_spec (S (length parents)) level);
        destruct (Nat.leb_spec0 level (S (length parents)));
        destruct (Nat.leb_spec0 level (length parents)); lia.
  Qed.

  Lemma history_partial_credit : forall g level fuel st,
    frames_balanced st -> partial_mass level (history_from g fuel st) <= partial_credit level st.
  Proof.
    intros g level fuel. induction fuel as [|fuel IH]; intros st Hbalance.
    - cbn [history_from]. destruct (wto_step g st); rewrite partial_mass_cons;
        cbn [partial_mass fold_right]; pose proof (partial_entry_credit level st); lia.
    - cbn [history_from]. destruct (wto_step g st) as [next|result] eqn:Hstep.
      + rewrite partial_mass_cons.
        specialize (IH next (frames_balanced_step g st next Hbalance Hstep)).
        pose proof (partial_credit_step g level st next Hbalance Hstep). lia.
      + rewrite partial_mass_cons. cbn [partial_mass fold_right].
        pose proof (partial_entry_credit level st). lia.
  Qed.

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
  Proof.
    intros g roots level. change (partial_mass level (history g roots) <=
      length (concat (comps (wto_components g roots)))).
    unfold history. eapply Nat.le_trans.
    - apply history_partial_credit, frames_balanced_initial.
    - unfold initial, partial_credit, partial_stack_credit.
      cbn [wto_parents wto_tasks wto_partial length wto_order suspended_credit].
      pose proof (partial_tasks_expands level 0 None
        (wto_entries g roots (wto_components g roots)) (comp (wto_components g roots))
        (rev (comps (wto_components g roots))) []) as Hcredit.
      rewrite app_nil_r in Hcredit. rewrite Hcredit. cbn [partial_tasks_credit].
      rewrite <- (Permutation_length (wto_components_reverse _)).
      destruct (Nat.leb level 0); lia.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components.


  Local Opaque loopN.

  (** A finite sum over nesting levels, including level zero. *)
  Fixpoint sum_levels (top : nat) (charge : nat -> nat) : nat :=
    match top with
    | 0 => charge 0
    | S rest => charge (S rest) + sum_levels rest charge
    end.

  Lemma sum_levels_ext : forall top first second,
    (forall level, level <= top -> first level = second level) ->
    sum_levels top first = sum_levels top second.
  Proof.
    intro top. induction top as [|top IH]; intros first second Heq.
    - cbn [sum_levels]. apply Heq. reflexivity.
    - cbn [sum_levels]. rewrite (Heq (S top) (Nat.le_refl _)).
      f_equal. apply IH. intros level Hlevel. apply Heq. lia.
  Qed.

  Lemma sum_levels_add : forall top first second,
    sum_levels top (fun level => first level + second level) =
      sum_levels top first + sum_levels top second.
  Proof.
    intro top. induction top as [|top IH]; intros first second;
      cbn [sum_levels]; [reflexivity|]. rewrite IH. lia.
  Qed.

  Lemma sum_levels_zero : forall top,
    sum_levels top (fun _ => 0) = 0.
  Proof.
    intro top. induction top as [|top IH]; cbn [sum_levels]; [reflexivity|exact IH].
  Qed.

  Lemma sum_levels_above : forall top depth weight,
    top < depth ->
    sum_levels top (fun level => if Nat.eqb depth level then weight else 0) = 0.
  Proof.
    intro top. induction top as [|top IH]; intros depth weight Habove.
    - cbn [sum_levels]. destruct (Nat.eqb_spec depth 0); lia.
    - cbn [sum_levels]. destruct (Nat.eqb_spec depth (S top)); [lia|].
      apply IH. lia.
  Qed.

  Lemma sum_levels_single : forall top depth weight,
    depth <= top ->
    sum_levels top (fun level => if Nat.eqb depth level then weight else 0) = weight.
  Proof.
    intro top. induction top as [|top IH]; intros depth weight Hdepth.
    - assert (depth = 0) by lia. subst depth. reflexivity.
    - cbn [sum_levels]. destruct (Nat.eqb_spec depth (S top)) as [Heq|Hneq].
      + rewrite (sum_levels_above top depth weight) by lia. lia.
      + apply IH. lia.
  Qed.

  Lemma sum_levels_bound : forall top charge budget,
    (forall level, level <= top -> charge level <= budget) ->
    sum_levels top charge <= (top + 1) * budget.
  Proof.
    intro top. induction top as [|top IH]; intros charge budget Hbound.
    - cbn [sum_levels]. pose proof (Hbound 0 (Nat.le_refl 0)). lia.
    - cbn [sum_levels]. pose proof (Hbound (S top) (Nat.le_refl _)) as Hlast.
      assert (Hrest : sum_levels top charge <= (top + 1) * budget).
      { apply IH. intros level Hlevel. apply Hbound. lia. }
      nia.
  Qed.

  (** Summing each depth separately counts every state charge exactly once. *)
  Lemma state_level_partition : forall (A : Type) (depth weight : A -> nat) states top,
    Forall (fun st => depth st <= top) states ->
    fold_right (fun st n => (weight st + n)%nat) 0%nat states =
      sum_levels top (fun level =>
        fold_right (fun st n => if Nat.eqb (depth st) level then weight st + n else n)
          0 states).
  Proof.
    intros A depth weight states. induction states as [|st states IH]; intros top Hdepth.
    - cbn [fold_right]. symmetry. apply sum_levels_zero.
    - inversion Hdepth as [|? ? Hhead Htail]; subst.
      cbn [fold_right]. rewrite (IH top Htail).
      transitivity (sum_levels top (fun level =>
        (if Nat.eqb (depth st) level then weight st else 0) +
        fold_right (fun current n =>
          if Nat.eqb (depth current) level then weight current + n else n) 0 states)).
      + rewrite sum_levels_add, (sum_levels_single top (depth st) (weight st) Hhead).
        reflexivity.
      + apply sum_levels_ext. intros level Hlevel.
        destruct (Nat.eqb (depth st) level); reflexivity.
  Qed.

  Lemma state_level_bound : forall (A : Type) (depth weight : A -> nat) states top budget,
    Forall (fun st => depth st <= top) states ->
    (forall level,
      fold_right (fun st n => if Nat.eqb (depth st) level then weight st + n else n)
        0 states <= budget) ->
    fold_right (fun st n => (weight st + n)%nat) 0%nat states <= (top + 1) * budget.
  Proof.
    intros A depth weight states top budget Hdepth Hlevels.
    rewrite (state_level_partition A depth weight states top Hdepth).
    apply sum_levels_bound. intros level Hlevel. apply Hlevels.
  Qed.

  (** The recorded trace has at most one more state than its supplied fuel. *)
  Lemma history_from_length : forall g fuel st,
    length (history_from g fuel st) <= fuel + 1.
  Proof.
    intros g fuel. induction fuel as [|fuel IH]; intro st;
      cbn [history_from]; destruct (wto_step g st) as [next|result]; cbn [length];
      try lia. pose proof (IH next). lia.
  Qed.

  Definition state_expansion_mass (g : prepared) (st : wto_state) : nat :=
    match wto_tasks st with WtoExpand _ _ _ c :: _ => source_mass g c | _ => 0 end.

  Definition state_partial_mass (st : wto_state) : nat :=
    match wto_tasks st with
    | [] | WtoClose _ :: _ => length (wto_order (wto_partial st))
    | _ => 0
    end.

  Lemma expansion_level_mass : forall g level states,
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then state_expansion_mass g st + n else n)
      0 states = level_mass g level states.
  Proof.
    intros g level states. induction states as [|st states IH]; [reflexivity|].
    unfold level_mass in *. cbn [fold_right]. rewrite <- IH.
    destruct (Nat.eqb (length (wto_parents st)) level); [|reflexivity].
    unfold state_expansion_mass. destruct (wto_tasks st) as [|task tasks]; [reflexivity|].
    destruct task; reflexivity.
  Qed.

  Lemma listed_graph_size : forall g,
    length (nodes g) = graph_n (base g).
  Proof. intros [[vs rows] predecessors n e]. reflexivity. Qed.

  Lemma source_mass_nodes : forall g,
    source_mass g (nodes g) = graph_n (base g) + graph_e (base g).
  Proof.
    assert (Hsum : forall (vs : list positive) (weight : positive -> nat),
      fold_right (fun v n => 1 + weight v + n) 0 vs =
        length vs + fold_right (fun v n => weight v + n) 0 vs).
    { intro vs. induction vs as [|v vs IH]; intro weight;
        cbn [fold_right length]; [reflexivity|]. rewrite IH. lia. }
    intros [[vs rows] predecessors n e].
    exact (Hsum vs (fun v => length (succs (Digraph vs rows) v))).
  Qed.

  Local Transparent loopN.

  Local Opaque loopN Galois.Graph.Wto.wto_components.

  Lemma partial_level_mass : forall level states,
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then state_partial_mass st + n else n) 0 states =
    fold_right (fun st n =>
      if Nat.eqb (length (wto_parents st)) level then
        match wto_tasks st with
        | [] | WtoClose _ :: _ => length (wto_order (wto_partial st)) + n
        | _ => n
        end
      else n) 0 states.
  Proof.

    intros level states. induction states as [|st states IH]; [reflexivity|].
    cbn [fold_right]. rewrite IH.
    destruct (Nat.eqb (length (wto_parents st)) level); [|reflexivity].
    unfold state_partial_mass. destruct (wto_tasks st) as [|task tasks]; [reflexivity|].
    destruct task; reflexivity.
  Qed.

  Lemma state_mass_sum : forall g states,
    fold_right (fun st n => state_expansion_mass g st + state_partial_mass st + 1 + n) 0 states =
      fold_right (fun st n => state_expansion_mass g st + n) 0 states +
      fold_right (fun st n => state_partial_mass st + n) 0 states + length states.
  Proof.

    intros g states. induction states; cbn [fold_right length]; [reflexivity|]. rewrite IHstates. lia.
  Qed.

  Lemma initial_source_mass : forall g roots,
    source_mass g (concat (comps (wto_components g roots))) <=
      graph_n (base g) + graph_e (base g).
  Proof.

    intros g roots. rewrite <- source_mass_nodes. apply source_mass_subdomain.
    - apply wto_components_unique.
    - intros v Hin. now apply (wto_components_listed g roots).
  Qed.

  Lemma history_mass_arithmetic : forall n e roots depth mass size expansions partial count,
    mass <= n + e -> size <= n ->
    expansions <= (depth + 1) * mass -> partial <= (depth + 1) * size ->
    count <= 3 * size + 1 + 1 ->
    expansions + partial + count <= 5 * (n + e + roots + 1) * (depth + 1).
  Proof. intros. nia. Qed.

  (** Per-depth component and partial-output charges sum to graph size times output depth. *)
  Lemma history_mass_bound_from_levels : forall g roots,
    (forall level,
      fold_right (fun st n =>
        if Nat.eqb (length (wto_parents st)) level then state_partial_mass st + n else n)
        0 (history g roots) <= length (concat (comps (wto_components g roots)))) ->
    fold_right (fun st n => state_expansion_mass g st + state_partial_mass st + 1 + n) 0
      (history g roots) <=
    5 * (graph_n (base g) + graph_e (base g) + length roots + 1) *
      (wto_depth (build g roots) + 1).
  Proof.

    intros g roots Hpartial_levels.
    assert (Hdepth : Forall (fun st => length (wto_parents st) <= wto_depth (build g roots))
      (history g roots)).
    { apply Forall_forall. intros st Hin. now apply (history_depth_bound g roots). }
    assert (Hexpansions :
      fold_right (fun st n => state_expansion_mass g st + n) 0 (history g roots) <=
      (wto_depth (build g roots) + 1) * source_mass g (concat (comps (wto_components g roots)))).
    { apply (state_level_bound wto_state (fun st => length (wto_parents st))
        (state_expansion_mass g)); [exact Hdepth|].
      intro level. rewrite expansion_level_mass. apply F18_level_mass. }
    assert (Hpartials : fold_right (fun st n => state_partial_mass st + n) 0 (history g roots) <=
      (wto_depth (build g roots) + 1) * length (concat (comps (wto_components g roots)))).
    { apply (state_level_bound wto_state (fun st => length (wto_parents st))
        state_partial_mass); [exact Hdepth|].
      intro level. apply Hpartial_levels. }
    pose proof (initial_source_mass g roots) as Hmass.
    pose proof (wto_components_size g roots) as Hsize.
    rewrite listed_graph_size in Hsize.
    pose proof (history_from_length g
      (3 * length (concat (comps (wto_components g roots))) + 1) (initial g roots)) as Hlength.
    change (length (history g roots) <= 3 * length (concat (comps (wto_components g roots))) + 1 + 1)
      in Hlength.
    rewrite state_mass_sum.
    eapply (history_mass_arithmetic (graph_n (base g)) (graph_e (base g)) (length roots)
      (wto_depth (build g roots)) (source_mass g (concat (comps (wto_components g roots))))
      (length (concat (comps (wto_components g roots))))).
    - exact Hmass.
    - exact Hsize.
    - exact Hexpansions.
    - exact Hpartials.
    - exact Hlength.
  Qed.

  Lemma sum_clock_weight : forall (A : Type) (weight : A -> nat) (clock : A -> N) states rate,
    (forall st, In st states -> (clock st <= rate * N.of_nat (weight st))%N) ->
    (fold_right (fun st n => clock st + n)%N 0%N states <=
      rate * N.of_nat (fold_right (fun st n => (weight st + n)%nat) 0%nat states))%N.
  Proof.

    intros A weight clock states. induction states as [|st states IH]; intros rate Hclock.
    - cbn [fold_right]. lia.
    - pose proof (Hclock st (or_introl eq_refl)) as Hhead.
      assert (Htail : (fold_right (fun current n => clock current + n)%N 0%N states <=
        rate * N.of_nat (fold_right (fun current n => (weight current + n)%nat) 0%nat states))%N).
      { apply IH. intros current Hin. apply Hclock. now right. }
      cbn [fold_right]. rewrite Nat2N.inj_add. nia.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components.

  Local Opaque loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

  (** Listed scope keys fit the original graph's width envelope. *)
  Lemma listed_vertex_width : forall g vs,
    (forall v, In v vs -> In v (nodes g)) -> vertex_width vs <= graph_width (base g).
  Proof.
    intros g vs. unfold vertex_width.
    induction vs as [|v vs IH]; intro Hlisted; cbn [fold_right]; [lia|].
    rewrite wto_graph_max_nat. apply Nat.max_lub.
    - apply wto_listed_width, Hlisted. now left.
    - apply IH. intros u Hu. apply Hlisted. now right.
  Qed.

  Lemma scope_work_listed : forall g vs,
    (forall v, In v vs -> In v (nodes g)) ->
    scope_work g vs = (source_mass g vs + 1) * (graph_width (base g) + 1).
  Proof.
    intros g vs Hlisted. unfold scope_work. rewrite wto_graph_max_nat.
    rewrite Nat.max_l; [reflexivity|]. now apply listed_vertex_width.
  Qed.

  Lemma builder_coefficient_positive : (128 <= k_build)%N.
  Proof. unfold k_build. nia. Qed.

  (** Every recorded step pays only its selected component or its reversed partial output. *)
  Lemma builder_state_clock_from_scope : forall g roots st coefficient,
    (128 <= coefficient)%N ->
    (forall vs, NoDup vs -> (forall v, In v vs -> In v (nodes g)) ->
      (T_wto_scoped g (Some vs) +
        T_wto_components (wto_scoped g (Some vs)) (rev vs) +
        T_wto_entries (wto_scoped g (Some vs)) (rev vs)
          (wto_components (wto_scoped g (Some vs)) (rev vs)) <=
        4 * coefficient * N.of_nat (scope_work g vs))%N) ->
    In st (history g roots) ->
    (T_wto_step g st <= 512 * coefficient *
      N.of_nat (state_expansion_mass g st + state_partial_mass st + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g roots [tasks partial parents] coefficient Hcoefficient Hscope_bound Hin.
    destruct tasks as [|task tasks].
    - assert (Hshort : forall within entries owners c tasks h body,
        wto_tasks (WtoState [] partial parents) = WtoExpand within entries owners c :: tasks ->
        wto_select (wto_preferred owners entries c) c = Some (h, body) -> body = []).
      { intros within entries owners c tasks h body Htasks. discriminate Htasks. }
      pose proof (short_step_clock g roots (WtoState [] partial parents) Hin Hshort) as Hclock.
      cbn [short_mass state_expansion_mass state_partial_mass wto_tasks wto_partial] in Hclock |- *.
      unfold k_expand in Hclock. nia.
    - destruct task as [within entries owners c|h].
      + destruct (Galois.Graph.Wto.wto_select
          (Galois.Graph.Wto.wto_preferred owners entries c) c) as [[h body]|] eqn:Hselect.
        * destruct body as [|v body].
          -- assert (Hshort : forall within' entries' owners' c' tasks' h' body',
              wto_tasks (WtoState (WtoExpand within entries owners c :: tasks) partial parents) =
                WtoExpand within' entries' owners' c' :: tasks' ->
              wto_select (wto_preferred owners' entries' c') c' = Some (h', body') -> body' = []).
             { intros within' entries' owners' c' tasks' h' body' Htasks Hselected.
               inversion Htasks; subst. unfold wto_select, wto_preferred in Hselected.
               rewrite Hselect in Hselected. now inversion Hselected. }
             pose proof (short_step_clock g roots
               (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
               Hin Hshort) as Hclock.
             cbn [short_mass state_expansion_mass state_partial_mass wto_tasks wto_partial] in Hclock |- *.
             unfold k_expand in Hclock. nia.
          -- destruct (history_component_domain g roots
               (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
               within entries owners c tasks Hin eq_refl)
               as [Hnonempty [Hunique [Hlisted Howners]]].
             destruct (history_body_domain g roots
               (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
               within entries owners c tasks h (v :: body) Hin eq_refl Hselect)
               as [Hbody_unique Hbody_listed].
             pose proof (T14_select g roots
               (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
               within entries owners c tasks Hin eq_refl) as Hselect_clock.
             pose proof (Hscope_bound (v :: body) Hbody_unique Hbody_listed) as Hscope_clock.
             pose proof (T6_expand g within entries owners c tasks partial parents h (v :: body)
               Hselect ltac:(discriminate)) as Hstep.
             pose proof (source_mass_permutation g _ _ (wto_select_spec _ _ _ _ Hselect))
               as Hmass.
             change (source_mass g c =
               1 + length (succs (base g) h) + source_mass g (v :: body)) in Hmass.
             pose proof (source_mass_length g c) as Hlength_c.
             pose proof (source_mass_length g (v :: body)) as Hlength_body.
             rewrite (scope_work_listed g c Hlisted) in Hselect_clock.
             rewrite (scope_work_listed g (v :: body) Hbody_listed) in Hscope_clock.
             clear Hin Hnonempty Hunique Hlisted Howners Hbody_unique Hbody_listed Hselect Hscope_bound.
             cbn [state_expansion_mass state_partial_mass wto_tasks].
             unfold k_expand in Hselect_clock, Hstep.
             rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
        * assert (Hshort : forall within' entries' owners' c' tasks' h' body',
            wto_tasks (WtoState (WtoExpand within entries owners c :: tasks) partial parents) =
              WtoExpand within' entries' owners' c' :: tasks' ->
            wto_select (wto_preferred owners' entries' c') c' = Some (h', body') -> body' = []).
          { intros within' entries' owners' c' tasks' h' body' Htasks Hselected.
            inversion Htasks; subst. unfold wto_select, wto_preferred in Hselected.
            rewrite Hselect in Hselected. discriminate. }
          pose proof (short_step_clock g roots
            (WtoState (WtoExpand within entries owners c :: tasks) partial parents)
            Hin Hshort) as Hclock.
          cbn [short_mass state_expansion_mass state_partial_mass wto_tasks wto_partial] in Hclock |- *.
          unfold k_expand in Hclock. nia.
      + assert (Hshort : forall within entries owners c tasks' h' body,
          wto_tasks (WtoState (WtoClose h :: tasks) partial parents) =
            WtoExpand within entries owners c :: tasks' ->
          wto_select (wto_preferred owners entries c) c = Some (h', body) -> body = []).
        { intros within entries owners c tasks' h' body Htasks. discriminate Htasks. }
        pose proof (short_step_clock g roots
          (WtoState (WtoClose h :: tasks) partial parents) Hin Hshort) as Hclock.
        cbn [short_mass state_expansion_mass state_partial_mass wto_tasks wto_partial] in Hclock |- *.
        unfold k_expand in Hclock. nia.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

  Local Opaque loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

  Definition builder_scope_bound g : Prop :=
    forall vs, NoDup vs -> (forall v, In v vs -> In v (nodes g)) ->
      (T_wto_scoped g (Some vs) +
        T_wto_components (wto_scoped g (Some vs)) (rev vs) +
        T_wto_entries (wto_scoped g (Some vs)) (rev vs)
          (wto_components (wto_scoped g (Some vs)) (rev vs)) <=
        4 * k_build * N.of_nat (scope_work g vs))%N.

  Definition builder_partial_bound g roots : Prop :=
    forall level,
      fold_right (fun st n =>
        if Nat.eqb (length (wto_parents st)) level then state_partial_mass st + n else n)
        0 (history g roots) <= length (concat (comps (wto_components g roots))).

  Definition builder_initial_bound g roots : Prop :=
    (T_wto_components g roots + T_wto_entries g roots (wto_components g roots) <=
      k_build * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.

  Lemma execution_budget_arithmetic : forall coefficient work width size depth cost,
    (work <= 5 * size * depth)%N ->
    (cost <= 512 * coefficient * width * work)%N ->
    (cost <= 2560 * coefficient * size * depth * width)%N.
  Proof.
    intros coefficient work width size depth cost Hwork Hcost.
    eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans with (512 * coefficient * width * (5 * size * depth))%N.
    - now apply N.mul_le_mono_l.
    - nia.
  Qed.

  Lemma execution_cost_from_bounds : forall g roots,
    builder_scope_bound g -> builder_partial_bound g roots ->
    (execution_cost g (history g roots) <= 2560 * k_build *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g roots Hscope Hpartial.
    pose proof (sum_clock_weight wto_state
      (fun st => state_expansion_mass g st + state_partial_mass st + 1) (T_wto_step g)
      (history g roots) (512 * k_build * N.of_nat (graph_width (base g) + 1))%N)
      as Hsum.
    assert (Hper : forall st, In st (history g roots) ->
      (T_wto_step g st <= 512 * k_build * N.of_nat (graph_width (base g) + 1) *
        N.of_nat (state_expansion_mass g st + state_partial_mass st + 1))%N).
    { intros st Hin.
      pose proof (builder_state_clock_from_scope g roots st k_build
        builder_coefficient_positive Hscope Hin) as Hclock.
      nia. }
    specialize (Hsum Hper).
    pose proof (history_mass_bound_from_levels g roots Hpartial) as Hmass.
    apply time_of_nat_le in Hmass. rewrite !Nat2N.inj_mul in Hmass.
    change (execution_cost g (history g roots) <=
      512 * k_build * N.of_nat (graph_width (base g) + 1) *
      N.of_nat (fold_right (fun st n =>
        (state_expansion_mass g st + state_partial_mass st + 1 + n)%nat) 0%nat
        (history g roots)))%N in Hsum.
    eapply execution_budget_arithmetic; [exact Hmass|exact Hsum].
  Qed.

  Lemma build_budget_arithmetic : forall coefficient size depth width initial count execution cost,
    (128 <= coefficient)%N -> (1 <= size)%N -> (1 <= depth)%N -> (1 <= width)%N ->
    (initial <= coefficient * size * width)%N -> (count + 1 <= size)%N ->
    (execution <= 2560 * coefficient * size * depth * width)%N ->
    (cost <= coefficient * (initial + count + execution + 1))%N ->
    (cost <= 4096 * coefficient * coefficient * size * depth * width)%N.
  Proof.
    intros coefficient size depth width initial count execution cost
      Hcoefficient Hsize Hdepth Hwidth Hinitial Hcount Hexecution Hcost.
    set (budget := (size * depth * width)%N).
    assert (Hsize_budget : (size <= budget)%N).
    { unfold budget. eapply N.le_trans with (size * depth)%N.
      - replace size with (size * 1)%N at 1 by nia. now apply N.mul_le_mono_l.
      - replace (size * depth)%N with (size * depth * 1)%N at 1 by nia.
        now apply N.mul_le_mono_l. }
    assert (Hinitial_budget : (initial <= coefficient * budget)%N).
    { eapply N.le_trans; [exact Hinitial|]. unfold budget.
      replace (coefficient * (size * depth * width))%N with
        (coefficient * size * depth * width)%N by nia.
      apply N.mul_le_mono_r. replace (coefficient * size)%N with
        (coefficient * size * 1)%N at 1 by nia. now apply N.mul_le_mono_l. }
    assert (Hexecution_budget : (execution <= 2560 * coefficient * budget)%N).
    { unfold budget. replace (2560 * coefficient * (size * depth * width))%N with
        (2560 * coefficient * size * depth * width)%N by nia. exact Hexecution. }
    assert (Hinside : (initial + count + execution + 1 <= (2561 * coefficient + 1) * budget)%N)
      by nia.
    eapply N.le_trans; [exact Hcost|].
    eapply N.le_trans with (coefficient * ((2561 * coefficient + 1) * budget))%N.
    - now apply N.mul_le_mono_l.
    - replace (coefficient * ((2561 * coefficient + 1) * budget))%N with
        ((2561 * coefficient * coefficient + coefficient) * budget)%N by nia.
      replace (4096 * coefficient * coefficient * size * depth * width)%N with
        ((4096 * coefficient * coefficient) * budget)%N by (unfold budget; nia).
      apply N.mul_le_mono_r. nia.
  Qed.

  Lemma positive_nat_successor : forall value, (1 <= N.of_nat (value + 1))%N.
  Proof. intro value. rewrite Nat2N.inj_add. nia. Qed.

  Lemma initial_count_margin : forall count n e roots,
    count <= n -> count + 1 <= n + e + roots + 1.
  Proof. intros. lia. Qed.

  Lemma build_clock_from_bounds : forall g roots,
    builder_initial_bound g roots -> builder_scope_bound g -> builder_partial_bound g roots ->
    (T_build g roots <= 4096 * k_build * k_build *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    intros g roots Hinitial Hscope Hpartial.
    pose proof (T16_build g roots) as Hbuild.
    pose proof (execution_cost_from_bounds g roots Hscope Hpartial) as Hexecution.
    pose proof (wto_components_size g roots) as Hsize. rewrite listed_graph_size in Hsize.
    pose proof (initial_count_margin _ _ (graph_e (base g)) (length roots) Hsize) as Hmargin.
    apply time_of_nat_le in Hmargin. rewrite Nat2N.inj_add in Hmargin.
    assert (Hwidth : (N.of_nat (graph_width (base g) + 1) <=
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N).
    { apply time_of_nat_le. apply Nat.add_le_mono_r.
      rewrite wto_graph_max_nat. apply Nat.le_max_l. }
    assert (Hexecution_full : (execution_cost g (history g roots) <= 2560 * k_build *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N).
    { eapply N.le_trans; [exact Hexecution|]. now apply N.mul_le_mono_l. }
    eapply (build_budget_arithmetic k_build
      (N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1))
      (N.of_nat (wto_depth (build g roots) + 1))
      (N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))
      (T_wto_components g roots + T_wto_entries g roots (wto_components g roots))%N
      (N.of_nat (length (concat (comps (wto_components g roots)))))
      (execution_cost g (history g roots))).
    - exact builder_coefficient_positive.
    - apply positive_nat_successor.
    - apply positive_nat_successor.
    - apply positive_nat_successor.
    - exact Hinitial.
    - exact Hmargin.
    - exact Hexecution_full.
    - exact Hbuild.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

  Local Opaque loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

  Lemma builder_scope_phase : forall g, builder_scope_bound g.
  Proof.
    intros g vs Hunique Hlisted.
    pose proof (T3_scope_listed g vs Hlisted) as Hscoped.
    pose proof (T12_scoped g vs Hunique Hlisted) as Hcomponents.
    unfold k_scope in Hscoped, Hcomponents. nia.
  Qed.

  Lemma build_clock_envelope : forall g roots,
    (T_build g roots <= 4096 * k_build * k_build *
      N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    intros g roots. apply build_clock_from_bounds.
    - exact (T13_initial g roots).
    - apply builder_scope_phase.
    - intro level. rewrite partial_level_mass. apply F21_partial_mass.
  Qed.

  Lemma c_wto_builder : (4096 * k_build * k_build <= c_wto)%N.
  Proof. unfold c_wto. fold k_build. lia. Qed.

  Lemma T_build_le : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof.
    intros g roots. eapply N.le_trans; [exact (build_clock_envelope g roots)|].
    apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_r.
    exact c_wto_builder.
  Qed.

  Lemma T7_build_public : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. apply T_build_le. Qed.

  Lemma build_bigO : bigO (fun _ : prepared * list positive => True)
    (fun '(g, roots) => N.of_nat ((graph_n (base g) + graph_e (base g) + length roots + 1) *
      (wto_depth (build g roots) + 1) *
      (graph_max (graph_width (base g)) (vertex_width roots) + 1)))
    (fun '(g, roots) => T_build g roots).
  Proof.
    exists c_wto. intros [g roots] _.
    pose proof (T_build_le g roots) as Hbuild.
    rewrite !Nat2N.inj_mul. nia.
  Qed.

  Local Transparent loopN Galois.Graph.Wto.wto_components Galois.Graph.Wto.wto_scoped.

End WtoT.
