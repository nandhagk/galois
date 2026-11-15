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

Definition wto_components g roots :=
  let ready := scc_graph g in
  let listed_roots := filter (fun v =>
    match trie_get v (succ (base ready)) with Some _ => true | None => false end) roots in
  let s := TarjanSearch.dfs ready listed_roots tarjan_initial in
  Scc (tarjan_owners s) (rev_append (tarjan_emitted s) []).
TimeFun wto_components.

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
  intros g roots v Hin. set (ready := scc_graph g).
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
    eapply Permutation_in; [apply Permutation_sym, wto_components_reverse|exact Hin].
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
  intros g roots width Hwidth v i Howner. unfold wto_components in Howner. cbn [comp] in Howner.
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
  intros g roots. set (ready := scc_graph g).
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
    pose proof (PTrieT.trie_get_clock positive v owners) as Hget.
    time_unfold @T_wto_preferred. cbn beta iota zeta.
    destruct (trie_get v owners) as [i|] eqn:Howner.
    + pose proof (Howners v i Howner) as Hidentifier.
      pose proof (PTrieT.trie_get_clock positive i entries) as Hentry.
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
  rewrite !rev_append_rev, !app_nil_r. fold members scoped r entries'.
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
  - cbn [wto_step] in Hstep.
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
  - cbn [wto_step] in Hstep.
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
  intros g roots w Htrace Hcheck. unfold wto_check_linear in Hcheck.
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
  unfold wto_edges_ok in Hedges. rewrite forallb_forall in Hedges.
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

Lemma wto_key_fits_width width v : wto_key_fits width v = true -> Pos.size_nat v <= width.
Proof.
  revert v. induction width as [|width IH]; intro v; destruct v;
    cbn [wto_key_fits Pos.size_nat]; try discriminate; intros Hfit; try lia;
    specialize (IH _ Hfit); lia.
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
        pose proof (PTrieT.trie_get_clock bool v (listed_of g)) as Hlisted.
        pose proof (PTrieT.trie_get_clock N v ranks) as Hranks.
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
        pose proof (PTrieT.trie_get_clock bool h (listed_of g)) as Hlisted.
        pose proof (PTrieT.trie_get_clock N h ranks) as Hranks.
        pose proof (PTrieT.T_set_le N h next ranks) as Hset.
        pose proof (N.T_succ_le next) as Hsucc.
        time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        destruct (trie_get h (listed_of g)); destruct (trie_get h ranks);
          time_cbn; rewrite ?Hlisted, ?Hranks; rewrite !Nat2N.inj_add in *; nia.
      * time_unfold @T_wto_check_step. rewrite Hfits. time_cbn.
        rewrite !Nat2N.inj_add in *. nia.
  - pose proof (wto_index_close_width g whole _ h Hinv (or_introl eq_refl)) as Hh.
    pose proof (PTrieT.trie_get_clock N h ranks) as Hget.
    destruct (trie_get h ranks) as [lo|] eqn:Hlo.
    + pose proof (PTrieT.T_set_le (N * N) h (lo, next) intervals) as Hset.
      time_unfold @T_wto_check_step. rewrite Hlo. time_cbn. rewrite Hget.
      rewrite !Nat2N.inj_add in *. nia.
    + time_unfold @T_wto_check_step. rewrite Hlo. time_cbn. rewrite Hget.
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
Lemma wto_check_index_clock g whole :
  (1 + T_wto_check_index (check_fuel g) (graph_width (base g)) (listed_of g)
      [WtoCheckVisit whole] 0 Empty Empty [] <=
    4096 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  destruct (search_loop_trace_clock
    (wto_check_step (graph_width (base g)) (listed_of g))
    (fun st => T_wto_check_step (graph_width (base g)) (listed_of g) st)
    (check_fuel g) (WtoCheckState [WtoCheckVisit whole] 0 Empty Empty []))
    as [states [last [Hpath [Hlength Hclock]]]].
  destruct (wto_index_path g whole _ _ _ Hpath (wto_index_initial whole (listed_of g)))
    as [Hstates Hlast].
  assert (Hcost : forall st, In st states ->
      (T_wto_check_step (graph_width (base g)) (listed_of g) st <=
        128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N).
  { intros st Hin. rewrite Forall_forall in Hstates.
    destruct (Hstates st Hin) as [Hinv [next Hstep]].
    now apply (wto_check_continuing_clock g whole st next). }
  assert (Hcostall : Forall (fun st =>
    (T_wto_check_step (graph_width (base g)) (listed_of g) st <=
      128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N) states).
  { apply Forall_forall. exact Hcost. }
  pose proof (search_sum_clock_bound
    (fun st => T_wto_check_step (graph_width (base g)) (listed_of g) st) states
    (128 * (PTrieT.c_trie + 1) * N.of_nat (graph_width (base g) + 1))%N Hcostall) as Hsum.
  pose proof (wto_check_terminal_clock g whole last Hlast) as Hterminal.
  pose proof (search_N_size_value (check_fuel g)) as Hbits.
  assert (Hfuel : N.to_nat (check_fuel g) = 4 * graph_n (base g) + 2).
  { unfold check_fuel. rewrite !N.double_spec. lia. }
  rewrite Hfuel in Hlength, Hbits.
  assert (HlengthN : (N.of_nat (length states) <= 4 * N.of_nat (graph_n (base g) + 1))%N)
    by lia.
  assert (Hsum_scaled :
    (fold_right N.add 0%N (map
      (fun st => T_wto_check_step (graph_width (base g)) (listed_of g) st) states) <=
      512 * (PTrieT.c_trie + 1) * N.of_nat (graph_n (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N).
  { eapply N.le_trans; [exact Hsum|]. clear - HlengthN. nia. }
  clear Hpath Hstates Hlast Hcost Hcostall Hsum Hfuel.
  time_unfold @T_wto_check_index. time_cbn.
  destruct (wto_check_step (graph_width (base g)) (listed_of g) last);
    rewrite !Nat2N.inj_add in *; nia.
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
  pose proof (PTrieT.trie_get_clock N u ranks) as Hgetu.
  pose proof (PTrieT.trie_get_clock N v ranks) as Hgetv.
  pose proof (PTrieT.trie_get_clock (N * N) v intervals) as Hgetinterval.
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
  pose proof (wto_edge_rows_clock g ranks intervals vs Hlistedall Hrank) as Hscan.
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
    rewrite (PTrieT.trie_get_clock A v table), Nat2N.inj_add. nia. }
  pose proof (wto_forallb_clock
    (fun v => match trie_get v table with Some _ => true | None => false end)
    (fun v => 1 + T_trie_get v table)%N vs (4 * N.of_nat (width + 1))%N Hcallback) as Hscan.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

Lemma wto_entered_time es : (T_entered es <= 4 * N.of_nat (length es + 1))%N.
Proof.
  induction es as [|e es IH]; [time_step|]. destruct e; time_step.
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

  Local Opaque loopN.

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

  Definition k_member : N := 4%N.
  Definition k_index : N := (4096 * (PTrieT.c_trie + 1))%N.
  Definition k_check : N := 512%N.
  Definition k_scope : N := 1%N. (* STUB *)
  Definition k_expand : N := 32%N.
  Definition k_build : N :=
    (128 * (SccT.c_scc + DigraphT.c_prepare + PTrieT.c_trie + 1))%N.
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

  Lemma F4_check : forall g roots w, check g roots w = true <-> checked g roots w.
  Proof. Admitted. (* STUB *)

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

  Lemma F13_partition : forall g body,
    NoDup body ->
    let r := wto_components (wto_scoped g (Some body)) (rev body) in
    Permutation (concat (comps r)) body /\
    fold_right (fun c n => source_mass g c + n) 0 (comps r) = source_mass g body.
  Proof. Admitted. (* STUB *)

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

  Lemma F15_step : forall g roots st next,
    invariant g roots st -> wto_step g st = inl next ->
    invariant g roots next /\ potential g next < potential g st.
  Proof. Admitted. (* STUB *)

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
    - cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
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
    - cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
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
    - cbn [filter] in Hbalance. cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
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
    - cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
      inversion Hstep; subst w. split; reflexivity.
    - destruct task as [within entries owners c|h].
      + cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
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

  Lemma T3_scope : forall g vs,
    (T_wto_scoped g (Some vs) <= k_scope * N.of_nat (scope_work g vs))%N.
  Proof. Admitted. (* PLAN-DEFECT: unlisted scope rows can contain unbounded-width successors. *)

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
    reflexivity.
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
  Proof.
    intros g within entries owners c tasks partial parents h body Hselect Hbody.
    pose proof (wto_expand_step_clock g within entries owners c tasks partial parents h body
      Hselect Hbody) as Hstep.
    unfold k_expand. time_unfold @T_wto_step. time_unfold @T_wto_preferred.
    time_unfold @T_wto_select. time_unfold @T_wto_scoped. time_unfold @T_wto_components.
    time_unfold @T_wto_entries. unfold wto_preferred, wto_scoped, wto_components.
    time_simpl. nia.
  Qed.

  Lemma T7_build_public : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + length roots + 1) *
      N.of_nat (wto_depth (build g roots) + 1) *
      N.of_nat (graph_max (graph_width (base g)) (vertex_width roots) + 1))%N.
  Proof. Admitted. (* STUB *)

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
      cbn [wto_step Galois.Graph.Wto.wto_step] in Hstep.
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
  Lemma T16_build : forall g roots,
    (T_build g roots <= k_build * (T_wto_components g roots +
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
    unfold T_wto_components, T_wto_entries, k_build. time_simpl.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  Local Transparent loopN.

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

End WtoT.
