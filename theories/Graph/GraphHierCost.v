(** * Hierarchy numeric and family costs

    A depth factor multiplies disjoint source work at each recursive SCC level.
    For example, a rejected outgoing target stays charged through its admitted source row.
    Builds on: GraphHierLocalCost, GraphHierCostData and GraphHierCostRec. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia Permutation Wf_nat.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchCost GraphSearchScopedCost GraphSccSpec GraphHierSpec GraphHier GraphHierEntries
  GraphHierProducer GraphHierWork GraphHierLocalCost GraphHierCostData GraphHierCostRec
  GraphTarjan GraphTarjanExact GraphTarjanCost GraphTarjanPartition.
Import List.ListNotations.
Local Open Scope N_scope.

Module HierCost.

(** The expansion coefficient composes local hierarchy work with the public SCC coefficient. *)
Definition expand_k := 1024 + 2 * TarjanCost.scc_k.

(** The full hierarchy coefficient retains the public SCC coefficient symbolically. *)
Definition hier_k := 2048 + 4 * TarjanCost.scc_k.

Local Lemma outer_arithmetic s K L d B m q k x y z :
  1 <= d -> m <= B -> q <= B -> k <= m ->
  x <= s * B -> y <= 128 * (q + m) -> z <= k + K * d * m ->
  s + 258 + K <= L ->
  x + (y + (k + z)) <= L * (d * B).
Proof.
  intros Hd Hm Hq Hk Hx Hy Hz Hcoefficient.
  assert (Hrecursive : K * d * m <= K * d * B) by
    (apply N.mul_le_mono_l, Hm).
  assert (Hbase : x + y + 2 * k <= (s + 258) * B) by nia.
  assert (Hlift : (s + 258) * B <= (s + 258) * d * B).
  { replace ((s + 258) * B) with ((s + 258) * 1 * B) by ring.
    apply N.mul_le_mono_r, N.mul_le_mono_l, Hd. }
  eapply N.le_trans with ((s + 258) * d * B + K * d * B); [lia|].
  replace ((s + 258) * d * B + K * d * B) with
    ((s + 258 + K) * (d * B)) by ring.
  apply N.mul_le_mono_r, Hcoefficient.
Qed.

Local Lemma valid_width {V E} (p : Prepared.t V E) w :
  SearchCost.width_bound p [] w -> forall v, Prepared.valid_id p v ->
    key_bits positive_encoding v <= w.
Proof.
  intros Hwidth v Hv. apply Hwidth. now left.
Qed.

Local Lemma selected_width {V E} (p : Prepared.t V E) scope roots c preferred h body w :
  Prepared.ready p -> SearchCost.width_bound p [] w ->
  In c (Scc.components (Tarjan.compute p scope roots)) ->
  HierRun.select preferred c = Some (h, body) ->
  key_bits positive_encoding h <= w /\
    (forall v, In v body -> key_bits positive_encoding v <= w).
Proof.
  intros Hready Hwidth Hc Hselected.
  destruct (HierCostData.component_domain p scope roots c Hready Hc) as [_ Hvalid].
  pose proof (HierRun.select_permutation preferred c h body Hselected) as Hperm.
  split.
  - apply Hwidth. left. apply Hvalid.
    exact (Permutation_in h (Permutation_sym Hperm) (or_introl eq_refl)).
  - intros v Hv. apply Hwidth. left. apply Hvalid.
    exact (Permutation_in v (Permutation_sym Hperm) (or_intror Hv)).
Qed.

Local Lemma selected_mass {V E} (p : Prepared.t V E) w c preferred h body :
  HierRun.select preferred c = Some (h, body) ->
    HierWork.mass p w c = HierWork.weight p w h + HierWork.mass p w body.
Proof.
  intro Hselected. pose proof (HierWork.sum_permutation (HierWork.weight p w) _ _
    (HierRun.select_permutation preferred c h body Hselected)) as Hperm.
  exact Hperm.
Qed.

Local Lemma expansion_singleton_cost {V E} (p : Prepared.t V E) scope roots c index h w :
  Prepared.ready p -> SearchCost.width_bound p [] w -> HierLocalCost.counter_width p w ->
  In c (Scc.components (Tarjan.compute p scope roots)) ->
  HierRun.select (HierRun.preferred (Scc.comp_of (Tarjan.compute p scope roots)) index c) c =
    Some (h, []) ->
  Cost.ticks (HierRun.expand_c p
    (scope, index, Scc.comp_of (Tarjan.compute p scope roots), c)) <=
      expand_k * HierWork.mass p w c.
Proof.
  intros Hready Hwidth Hcounter Hc Hselected.
  destruct (HierCostData.component_domain p scope roots c Hready Hc) as [Hnodup Hvalid].
  assert (Hwidths : forall v, In v c -> key_bits positive_encoding v <= w).
  { intros v Hv. apply Hwidth. left. now apply Hvalid. }
  pose proof (HierLocalCost.preferred_cost w (Tarjan.compute p scope roots) index c Hwidths
    (HierCostData.owners_width p scope roots w Hready Hcounter)) as Hpreferred.
  pose proof (HierLocalCost.select_cost w
    (HierRun.preferred (Scc.comp_of (Tarjan.compute p scope roots)) index c) c Hwidths)
    as Hselect.
  destruct (selected_width p scope roots c _ h [] w Hready Hwidth Hc Hselected) as [Hh _].
  pose proof (HierLocalCost.self_loop_cost p w h Hh) as Hself.
  rewrite SearchCost.id_cost_equation in Hself.
  pose proof (HierRun.select_length _ c h [] Hselected) as Hlength.
  pose proof (selected_mass p w c _ h [] Hselected) as Hmass.
  rewrite HierRun.expand_cost_equation, Hselected.
  change (HierWork.mass p w c = HierWork.weight p w h + 0) in Hmass.
  rewrite N.add_0_r in Hmass.
  rewrite Hmass. unfold HierWork.weight, expand_k, HierLocalCost.id_cost in *.
  cbn [length] in Hlength. rewrite <- Hlength in Hselect. cbn [length] in Hselect.
  nia.
Qed.

Local Lemma selected_decrease {V E} (p : Prepared.t V E) scope roots c preferred h body d :
  Prepared.ready p -> In c (Scc.components (Tarjan.compute p scope roots)) ->
  HierRun.select preferred c = Some (h, body) ->
  In d (Scc.components (Tarjan.compute p (HierRun.child_scope scope h body) (rev body))) ->
    (length d < length c)%nat.
Proof.
  intros Hready Hc Hselected Hin.
  destruct (HierRun.child_support p scope h body (rev body) d Hin) as [Hnodup Hsub].
  pose proof (NoDup_incl_length Hnodup Hsub).
  pose proof (HierRun.select_length preferred c h body Hselected). lia.
Qed.

Local Lemma component_local_cost {V E} (p : Prepared.t V E) scope roots c index h body w :
  Prepared.ready p -> SearchCost.width_bound p [] w -> HierLocalCost.counter_width p w ->
  In c (Scc.components (Tarjan.compute p scope roots)) ->
  HierRun.preferred (Scc.comp_of (Tarjan.compute p scope roots)) index c = Some h ->
  HierRun.select (Some h) c = Some (h, body) ->
  let child := HierRun.child_scope scope h body in
  let childroots := rev body in
  let next := Tarjan.compute p child childroots in
  1 + Cost.ticks (HierRun.preferred_c
    (Scc.comp_of (Tarjan.compute p scope roots)) index c) +
    Cost.ticks (HierRun.select_c (Some h) c) +
    Cost.ticks (HierRun.child_scope_c scope h body) +
    N.of_nat (length body) + Cost.ticks (Tarjan.compute_c p child childroots) +
    Cost.ticks (HierRun.entries_c p childroots next) +
    2 * N.of_nat (length (Scc.components next)) <= expand_k * HierWork.mass p w c.
Proof.
  intros Hready Hwidth Hcounter Hc Hpreferred Hselected child childroots next.
  destruct (HierCostData.child_domain p scope roots c (Some h) h body Hready Hc Hselected)
    as [Hnodup Hdomain].
  destruct (selected_width p scope roots c (Some h) h body w
    Hready Hwidth Hc Hselected) as [Hheader Hbody_width].
  pose proof (HierLocalCost.child_scope_cost w scope h body Hheader Hbody_width) as Hscope.
  pose proof (HierCostData.child_scc_cost p scope h body w Hready Hwidth Hnodup Hdomain) as Hscc.
  pose proof (HierCostData.child_entries_cost p scope h body w Hready Hwidth Hcounter
    Hnodup Hdomain) as Hentries.
  pose proof (proj2 (HierCostData.child_partition_work p scope h body w Hready Hnodup Hdomain))
    as Hcount.
  fold child childroots next in Hscc, Hentries, Hcount.
  assert (Hcount' : N.of_nat (length (Scc.components next)) <= N.of_nat (length body)) by lia.
  destruct (HierCostData.component_domain p scope roots c Hready Hc) as [_ Hvalid].
  assert (Hwidths : forall x, In x c -> key_bits positive_encoding x <= w).
  { intros x Hx. apply Hwidth. left. now apply Hvalid. }
  pose proof (HierLocalCost.preferred_cost w (Tarjan.compute p scope roots) index c
    Hwidths (HierCostData.owners_width p scope roots w Hready Hcounter)) as Hpref.
  pose proof (HierLocalCost.select_cost w (Some h) c Hwidths) as Hselect.
  pose proof (HierRun.select_length (Some h) c h body Hselected) as Hlength.
  pose proof (selected_mass p w c (Some h) h body Hselected) as Hmass.
  assert (Hbodymass : N.of_nat (length body) * (1 + w) <= HierWork.mass p w body).
  { rewrite HierWork.mass_equation. nia. }
  clear - Hpref Hselect Hscope Hscc Hentries Hmass Hbodymass Hcount' Hlength.
  unfold expand_k, HierLocalCost.id_cost in *.
  unfold HierWork.weight in Hmass. nia.
Qed.

(** Expansion work is bounded by its output depth and its original component's source work. *)
Theorem expand_cost {V E} (p : Prepared.t V E) w :
  Prepared.ready p -> SearchCost.width_bound p [] w -> HierLocalCost.counter_width p w ->
  forall c scope roots t,
  In c (Scc.components (Tarjan.compute p scope roots)) ->
  Cost.value (HierRun.expand_c p
    (scope, HierRun.entries p roots (Tarjan.compute p scope roots),
      Scc.comp_of (Tarjan.compute p scope roots), c)) = Some t ->
  Cost.ticks (HierRun.expand_c p
    (scope, HierRun.entries p roots (Tarjan.compute p scope roots),
      Scc.comp_of (Tarjan.compute p scope roots), c)) <=
    expand_k * N.of_nat (S (HierWork.depth_tree t)) * HierWork.mass p w c.
Proof.
  intros Hready Hwidth Hcounter c.
  induction c as [c IH] using
    (well_founded_induction (well_founded_ltof _ (@length positive))).
  intros scope roots t Hc Hvalue.
  set (r := Tarjan.compute p scope roots) in *.
  pose proof (TarjanExact.compute_exact p scope roots Hready) as Hexact.
  fold r in Hexact.
  pose proof (TarjanExact.block_exact p scope roots c Hready Hc) as Hblock.
  destruct c as [|v rest]; [exfalso; exact (proj1 Hblock eq_refl)|].
  destruct (HierEntries.selection_entry p scope roots r (v :: rest) v Hready Hexact Hc
    (or_introl eq_refl)) as [i [h [body [Howner [Hrow [Hselected Hentry]]]]]].
  assert (Hpreferred : HierRun.preferred (Scc.comp_of r) (HierRun.entries p roots r) (v :: rest) =
    Some h).
  { rewrite HierRun.preferred_equation, Howner, Hrow. reflexivity. }
  destruct body as [|b body].
  - pose proof (expansion_singleton_cost p scope roots (v :: rest)
      (HierRun.entries p roots r) h w Hready Hwidth Hcounter Hc
      ltac:(fold r; rewrite Hpreferred; exact Hselected)) as Hcost.
    fold r in Hcost. eapply N.le_trans; [exact Hcost|].
    assert (Hdepth : 1 <= N.of_nat (S (HierWork.depth_tree t))) by
      (rewrite Nat2N.inj_succ; lia).
    nia.
  - set (child := HierRun.child_scope scope h (b :: body)).
    set (childroots := rev (b :: body)).
    set (next := Tarjan.compute p child childroots).
    destruct (HierCostData.child_domain p scope roots (v :: rest) (Some h) h (b :: body)
      Hready Hc Hselected) as [Hnodup Hdomain].
    assert (Hwidth_roots : SearchCost.width_bound p childroots w).
    { intros x [Hx|Hx]; apply Hwidth; left; [exact Hx|].
      exact (proj1 (Hdomain x (proj2 (in_rev (b :: body) x) Hx))). }
    assert (Hcallbacks : forall d (Hin : In d (rev (Scc.components next))), exists tree,
      Cost.value ((fun d _ => HierRun.expand_c p
        (child, HierRun.entries p childroots next, Scc.comp_of next, d)) d Hin) = Some tree /\
      Permutation d (Hier.members_tree tree) /\
      Cost.ticks ((fun d _ => HierRun.expand_c p
        (child, HierRun.entries p childroots next, Scc.comp_of next, d)) d Hin) <=
        expand_k * N.of_nat (S (HierWork.depth_tree tree)) * HierWork.mass p w d).
    { intros d Hin. assert (Hd : In d (Scc.components next)) by
        (exact (proj2 (in_rev _ _) Hin)).
      destruct (HierProducer.expand_exact p Hready d child childroots next
        (TarjanExact.compute_exact p child childroots Hready) Hd)
        as [tree [Htree [Hmembers Hblocks]]].
      exists tree. split; [exact Htree|]. split; [exact Hmembers|].
      apply (IH d (selected_decrease p scope roots (v :: rest) (Some h) h (b :: body) d
        Hready Hc Hselected Hd) child childroots tree Hd Htree). }
    pose proof (HierCostRec.assemble_bound p w expand_k (rev (Scc.components next)) _
      Hcallbacks) as Hassembly.
    set (f := Cost.value (HierRun.assemble_c (rev (Scc.components next))
      (fun d _ => HierRun.expand_c p
        (child, HierRun.entries p childroots next, Scc.comp_of next, d)))) in *.
    assert (Ht : t = Hier.Component h f).
    { rewrite HierRun.expand_value_equation, Howner, Hrow in Hvalue.
      cbn beta iota zeta in Hvalue. rewrite Hselected in Hvalue.
      inversion Hvalue. reflexivity. }
    subst t.
    pose proof (proj1 (HierCostData.child_partition_work p scope h (b :: body) w
      Hready Hnodup Hdomain)) as Hpartition_mass.
    fold child childroots next in Hpartition_mass.
    rewrite length_rev, Hpartition_mass in Hassembly.
    pose proof (selected_mass p w (v :: rest) (Some h) h (b :: body) Hselected) as Hmass.
    pose proof (component_local_cost p scope roots (v :: rest) (HierRun.entries p roots r)
      h (b :: body) w Hready Hwidth Hcounter Hc Hpreferred Hselected) as Hlocal.
    cbn beta iota zeta in Hlocal.
    fold r child childroots next in Hlocal.
    assert (Hmass_le : HierWork.mass p w (b :: body) <= HierWork.mass p w (v :: rest)).
    { rewrite Hmass. lia. }
    assert (Hscale :
      expand_k * N.of_nat (S (HierWork.depth f)) * HierWork.mass p w (b :: body) <=
      expand_k * N.of_nat (S (HierWork.depth f)) * HierWork.mass p w (v :: rest)).
    { apply N.mul_le_mono_l, Hmass_le. }
    change (Cost.ticks (HierRun.assemble_c (rev (Scc.components next))
      (fun d _ => HierRun.expand_c p
        (child, HierRun.entries p childroots next, Scc.comp_of next, d))) <=
      N.of_nat (length (Scc.components next)) +
      expand_k * N.of_nat (S (HierWork.depth f)) * HierWork.mass p w (b :: body)) in Hassembly.
    rewrite HierRun.expand_cost_equation, Hpreferred, Hselected, !ticks_rev_c.
    fold child childroots next.
    cbn [HierWork.depth_tree].
    fold next. rewrite ticks_rev_c.
    clear - Hlocal Hassembly Hscale.
    rewrite !Nat2N.inj_succ in *.
    nia.
Qed.

(** The root-aware size retains each supplied occurrence and the original global fuel width. *)
Definition size {V E} (p : Prepared.t V E) scope roots w :=
  N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))) *
    ((N.of_nat (length (Graph.nodes (Prepared.graph p))) +
      N.of_nat (GraphModel.edge_count (Prepared.graph p)) +
      N.of_nat (length roots)) * (1 + w) +
      (N.of_nat (length (Graph.nodes (Prepared.graph p))) +
        N.of_nat (length roots)) * HierWork.fuel_width p).

Local Lemma hierarchy_budget {V E} (p : Prepared.t V E) scope roots w B :
  Prepared.ready p -> SearchCost.width_bound p roots w -> HierLocalCost.counter_width p w ->
  Cost.ticks (Tarjan.compute_c p scope roots) <= TarjanCost.scc_k * B ->
  HierWork.mass p w (concat (Scc.components (Tarjan.compute p scope roots))) <= B ->
  N.of_nat (length roots) * (1 + w) <= B ->
  Cost.ticks (HierRun.compute_c p scope roots) <=
    hier_k * (N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))) * B).
Proof.
  intros Hready Hwidth Hcounter Hscc_total HmassB HrootB.
  assert (Hvalid_width : SearchCost.width_bound p [] w).
  { intros v [Hv|Hfalse]; [apply Hwidth; now left|contradiction]. }
  set (r := Tarjan.compute p scope roots).
  assert (Hcallbacks : forall c (Hin : In c (rev (Scc.components r))), exists t,
    Cost.value ((fun c _ => HierRun.expand_c p
      (scope, HierRun.entries p roots r, Scc.comp_of r, c)) c Hin) = Some t /\
    Permutation c (Hier.members_tree t) /\
    Cost.ticks ((fun c _ => HierRun.expand_c p
      (scope, HierRun.entries p roots r, Scc.comp_of r, c)) c Hin) <=
      expand_k * N.of_nat (S (HierWork.depth_tree t)) * HierWork.mass p w c).
  { intros c Hin. assert (Hc : In c (Scc.components r)) by
      (exact (proj2 (in_rev _ _) Hin)).
    destruct (HierProducer.expand_exact p Hready c scope roots r
      (TarjanExact.compute_exact p scope roots Hready) Hc)
      as [t [Hvalue [Hmembers Hblocks]]].
    exists t. split; [exact Hvalue|]. split; [exact Hmembers|].
    exact (expand_cost p w Hready Hvalid_width Hcounter c scope roots t Hc Hvalue). }
  pose proof (HierCostRec.assemble_bound p w expand_k (rev (Scc.components r)) _ Hcallbacks)
    as Hassembly.
  pose proof (HierCostData.entries_actual_cost p scope roots w Hready Hwidth Hcounter)
    as Hentries.
  fold r in Hentries, HmassB.
  rewrite length_rev in Hassembly.
  pose proof (HierWork.sum_permutation (HierWork.weight p w) _ _
    (TarjanPartition.concat_rev_permutation (Scc.components r))) as Hreverse.
  fold (HierWork.mass p w (concat (Scc.components r)))
    (HierWork.mass p w (concat (rev (Scc.components r)))) in Hreverse.
  rewrite <- Hreverse in Hassembly.
  destruct (TarjanExact.component_count_bounds p scope roots Hready) as [Hcount _].
  fold r in Hcount.
  assert (Hcount' : N.of_nat (length (Scc.components r)) <=
    HierWork.mass p w (concat (Scc.components r))).
  { rewrite HierWork.mass_equation. assert (HcountN :
      N.of_nat (length (Scc.components r)) <= N.of_nat (length (concat (Scc.components r)))) by lia.
    nia. }
  assert (Hforest :
    Cost.value (HierRun.assemble_c (rev (Scc.components r))
      (fun c _ => HierRun.expand_c p
        (scope, HierRun.entries p roots r, Scc.comp_of r, c))) = HierRun.compute p scope roots).
  { rewrite HierRun.compute_equation. reflexivity. }
  rewrite Hforest in Hassembly.
  unfold HierRun.compute_c. rewrite !Cost.ticks_bind, value_rev_c, ticks_rev_c.
  fold (Tarjan.compute p scope roots). fold r. fold (HierRun.entries p roots r).
  set (d := N.of_nat (S (HierWork.depth (HierRun.compute p scope roots)))) in *.
  assert (Hd : 1 <= d) by (unfold d; rewrite Nat2N.inj_succ; lia).
  fold (Tarjan.compute p scope roots). fold r. fold (HierRun.entries p roots r).
  apply (outer_arithmetic TarjanCost.scc_k expand_k hier_k d B
    (HierWork.mass p w (concat (Scc.components r)))
    (N.of_nat (length roots) * (1 + w)) (N.of_nat (length (Scc.components r)))).
  - exact Hd.
  - exact HmassB.
  - exact HrootB.
  - exact Hcount'.
  - exact Hscc_total.
  - exact Hentries.
  - exact Hassembly.
  - unfold hier_k, expand_k. nia.
Qed.

(** Actual hierarchy ticks have a depth-sensitive numeric bound retaining all root occurrences. *)
Theorem hier_cost {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
    Cost.ticks (HierRun.compute_c p scope roots) <= hier_k * size p scope roots w.
Proof.
  intros Hready Hwidth. unfold size.
  apply (hierarchy_budget p scope roots w _);
    [exact Hready|exact Hwidth|exact (HierCostData.counter_width p roots w Hready Hwidth)| | |].
  - pose proof (TarjanCost.scc_cost p scope roots w Hready Hwidth) as Hcost.
    eapply N.le_trans; [exact Hcost|]. apply N.mul_le_mono_l.
    unfold TarjanCost.scc_size, HierWork.fuel_width. nia.
  - pose proof (HierCostData.global_mass p scope roots w Hready). nia.
  - nia.
Qed.

(** Scoped size counts all outgoing occurrences at admitted valid sources and all supplied roots. *)
Definition scoped_size {V E} (p : Prepared.t V E) scope roots w :=
  N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))) *
    ((N.of_nat (ScopedSearchCost.node_count p scope) +
      N.of_nat (ScopedSearchCost.edge_count p scope) +
      N.of_nat (length roots)) * (1 + w) +
      (N.of_nat (ScopedSearchCost.node_count p scope) +
        N.of_nat (length roots)) * HierWork.fuel_width p).

(** The scoped bound retains component-sensitive work and global key and fuel widths. *)
Theorem hier_scoped_cost {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
    Cost.ticks (HierRun.compute_c p scope roots) <= hier_k * scoped_size p scope roots w.
Proof.
  intros Hready Hwidth. unfold scoped_size.
  apply (hierarchy_budget p scope roots w _);
    [exact Hready|exact Hwidth|exact (HierCostData.counter_width p roots w Hready Hwidth)| | |].
  - pose proof (TarjanCost.scc_scoped_cost p scope roots w Hready Hwidth) as Hcost.
    eapply N.le_trans; [exact Hcost|]. apply N.mul_le_mono_l.
    unfold TarjanCost.scc_scoped_size, HierWork.fuel_width. nia.
  - pose proof (HierCostData.scoped_mass p scope roots w Hready). nia.
  - nia.
Qed.

(** Root restriction removes root size when its occurrence count is bounded by node count. *)
Definition root_restricted_size {V E} (p : Prepared.t V E) scope roots w :=
  N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))) *
    ((N.of_nat (length (Graph.nodes (Prepared.graph p))) +
      N.of_nat (GraphModel.edge_count (Prepared.graph p))) * (1 + w) +
      N.of_nat (length (Graph.nodes (Prepared.graph p))) * HierWork.fuel_width p).

(** The node/edge-only corollary states its necessary supplied-root count duty. *)
Theorem hier_cost_root_restricted {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  (length roots <= length (Graph.nodes (Prepared.graph p)))%nat ->
  Cost.ticks (HierRun.compute_c p scope roots) <=
    2 * hier_k * root_restricted_size p scope roots w.
Proof.
  intros Hready Hwidth Hroots.
  pose proof (hier_cost p scope roots w Hready Hwidth) as Hcost.
  assert (Hsize : size p scope roots w <= 2 * root_restricted_size p scope roots w).
  { unfold size, root_restricted_size.
    assert (Hr : N.of_nat (length roots) <=
      N.of_nat (length (Graph.nodes (Prepared.graph p)))) by lia.
    rewrite N.mul_assoc.
    rewrite (N.mul_comm 2 (N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))))).
    rewrite <- N.mul_assoc. apply N.mul_le_mono_l.
    nia. }
  pose proof (N.mul_le_mono_l _ _ hier_k Hsize). nia.
Qed.

(** Distinct valid roots discharge the global root-count duty through the public SCC rule. *)
Theorem hier_cost_distinct_valid_roots {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  NoDup roots -> (forall v, In v roots -> Prepared.valid_id p v) ->
  Cost.ticks (HierRun.compute_c p scope roots) <=
    2 * hier_k * root_restricted_size p scope roots w.
Proof.
  intros Hready Hwidth Hnodup Hvalid.
  apply hier_cost_root_restricted; [exact Hready|exact Hwidth|].
  exact (TarjanCost.valid_root_count p roots Hnodup Hvalid).
Qed.

(** The scoped restricted measure keeps all outgoing occurrences and original fuel width. *)
Definition scoped_root_restricted_size {V E} (p : Prepared.t V E) scope roots w :=
  N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))) *
    ((N.of_nat (ScopedSearchCost.node_count p scope) +
      N.of_nat (ScopedSearchCost.edge_count p scope)) * (1 + w) +
      N.of_nat (ScopedSearchCost.node_count p scope) * HierWork.fuel_width p).

(** The scoped node/edge-only bound requires the actual supplied-root occurrence restriction. *)
Theorem hier_scoped_cost_root_restricted {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  (length roots <= ScopedSearchCost.node_count p scope)%nat ->
  Cost.ticks (HierRun.compute_c p scope roots) <=
    2 * hier_k * scoped_root_restricted_size p scope roots w.
Proof.
  intros Hready Hwidth Hroots.
  pose proof (hier_scoped_cost p scope roots w Hready Hwidth) as Hcost.
  assert (Hsize :
    scoped_size p scope roots w <= 2 * scoped_root_restricted_size p scope roots w).
  { unfold scoped_size, scoped_root_restricted_size.
    assert (Hr : N.of_nat (length roots) <= N.of_nat (ScopedSearchCost.node_count p scope)) by lia.
    rewrite N.mul_assoc.
    rewrite (N.mul_comm 2 (N.of_nat (S (HierWork.depth (HierRun.compute p scope roots))))).
    rewrite <- N.mul_assoc. apply N.mul_le_mono_l. nia. }
  pose proof (N.mul_le_mono_l _ _ hier_k Hsize). nia.
Qed.

(** Distinct admitted valid roots discharge the scoped supplied-root restriction. *)
Theorem hier_scoped_cost_distinct_roots {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> SearchCost.width_bound p roots w ->
  NoDup roots ->
  (forall v, In v roots -> Prepared.valid_id p v /\ Scope.admits scope v = true) ->
  Cost.ticks (HierRun.compute_c p scope roots) <=
    2 * hier_k * scoped_root_restricted_size p scope roots w.
Proof.
  intros Hready Hwidth Hnodup Hvalid.
  apply hier_scoped_cost_root_restricted; [exact Hready|exact Hwidth|].
  exact (TarjanCost.scoped_root_count p scope roots Hnodup Hvalid).
Qed.

(** The numeric hierarchy theorem lifts uniformly to families satisfying its primitive duties. *)
Theorem hier_bigO {X V E} (p : X -> Prepared.t V E) scope roots w :
  (forall x, Prepared.ready (p x)) ->
  (forall x, SearchCost.width_bound (p x) (roots x) (w x)) ->
  bigO (fun x => size (p x) (scope x) (roots x) (w x))
    (fun x => Cost.ticks (HierRun.compute_c (p x) (scope x) (roots x))).
Proof.
  intros Hready Hwidth. exists hier_k. intro x.
  pose proof (hier_cost (p x) (scope x) (roots x) (w x)
    (Hready x) (Hwidth x)).
  nia.
Qed.

(** The component-sensitive numeric theorem lifts to varying graph, scope and root families. *)
Theorem hier_scoped_bigO {X V E} (p : X -> Prepared.t V E) scope roots w :
  (forall x, Prepared.ready (p x)) ->
  (forall x, SearchCost.width_bound (p x) (roots x) (w x)) ->
  bigO (fun x => scoped_size (p x) (scope x) (roots x) (w x))
    (fun x => Cost.ticks (HierRun.compute_c (p x) (scope x) (roots x))).
Proof.
  intros Hready Hwidth. exists hier_k. intro x.
  pose proof (hier_scoped_cost (p x) (scope x) (roots x) (w x)
    (Hready x) (Hwidth x)).
  nia.
Qed.

End HierCost.
