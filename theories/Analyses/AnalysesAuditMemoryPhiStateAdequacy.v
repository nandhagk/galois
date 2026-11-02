(** * Phi dependency order and persistent resolution

    Relational steps agree with the plain computation, and the actual SCC order preserves
    fixed representatives and equal operands throughout resolution.
    For example, a later phi reads the fixed image written for an earlier dependency.
    Builds on: AnalysesAuditMemoryPhiState, graph SCC order and resolution adequacy. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphScc GraphLoops.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryFrontier
  AnalysesMemoryWalk
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiPlain AnalysesAuditMemoryPhiResolveAdequacy.
Import List.ListNotations.

Lemma phi_compute_step_indexed N E (EN : encoding N) (EE : encoding E) index before n :
  audit_phi_compute_step EN EE index before n =
    if FinSet.mem EN n (phi_index_cycles index) then before else
      match index_edges EN (phi_index_inputs index) n with
      | [] =>
        before
      | (_, input) :: rest =>
        let candidate := phi_rep_from_map EN EE before input in
        if andb (negb (Pos.eqb (encode (memory_version_encoding EN EE) candidate)
             (encode (memory_version_encoding EN EE) (MemoryPhi n))))
             (forallb (phi_same_rep EN EE before candidate) rest) then
          Map.set (memory_version_encoding EN EE) (MemoryPhi n) candidate before
        else before
      end.
Proof.
  unfold audit_phi_compute_step, index_edges.
  destruct (FinSet.mem EN n (phi_index_cycles index)); [reflexivity|].
  destruct (Map.get EN n (phi_index_inputs index)) as [[|[key input] rest]|]; reflexivity.
Qed.

(** * Captured input rows and dependency edges *)

Lemma phi_operand_rows_member N E (mg : memory_graph N E) n keys key v :
  In (key, v) (flat_map (fun k =>
    match memory_operand mg n k with
    | Some input =>
      [(k, input)]
    | None =>
      []
    end) keys) <-> In key keys /\ memory_operand mg n key = Some v.
Proof.
  rewrite in_flat_map.
  split.
  - intros [k [Hin Hpair]].
    destruct (memory_operand mg n k) as [input|] eqn:Hoperand; cbn in Hpair.
    + destruct Hpair as [Hequal|Hfalse]; [|contradiction].
      inversion Hequal; subst k input; auto.
    + contradiction.
  - intros [Hin Hoperand].
    exists key; split; [exact Hin|].
    rewrite Hoperand; left; reflexivity.
Qed.

Lemma phi_operand_rows_keys_nodup N E (mg : memory_graph N E) n keys :
  NoDup keys ->
  NoDup (map fst (flat_map (fun k =>
    match memory_operand mg n k with
    | Some input =>
      [(k, input)]
    | None =>
      []
    end) keys)).
Proof.
  intro Hkeys; induction Hkeys as [|key rest Hnot Hkeys IH].
  - constructor.
  - cbn [flat_map].
    destruct (memory_operand mg n key) as [v|]; cbn [app map fst]; [|exact IH].
    constructor; [|exact IH].
    intro Hin; apply in_map_iff in Hin.
    destruct Hin as [[other input] [Hequal Hmember]]; cbn in Hequal; subst other.
    apply phi_operand_rows_member in Hmember.
    exact (Hnot (proj1 Hmember)).
Qed.

Lemma phi_dependency_entries_member N E (n : N)
    (row : list (option E * memory_version N E)) edge :
  In edge (flat_map (fun kv =>
    match snd kv with
    | MemoryPhi target =>
      [PhiDependencyEdgeData n (fst kv) target]
    | _ =>
      []
    end) row) <->
  exists key target, edge = PhiDependencyEdgeData n key target /\
    In (key, MemoryPhi target) row.
Proof.
  rewrite in_flat_map; split.
  - intros [[key v] [Hin Hedge]].
    destruct v as [|target|e i]; cbn in Hedge; try contradiction.
    destruct Hedge as [Hequal|Hfalse]; [|contradiction].
    exists key, target; split; [symmetry; exact Hequal|exact Hin].
  - intros [key [target [-> Hin]]].
    exists (key, MemoryPhi target); split; [exact Hin|left; reflexivity].
Qed.

Lemma phi_dependency_entries_nodup N E (n : N)
    (row : list (option E * memory_version N E)) :
  NoDup (map fst row) ->
  NoDup (flat_map (fun kv =>
    match snd kv with
    | MemoryPhi target =>
      [PhiDependencyEdgeData n (fst kv) target]
    | _ =>
      []
    end) row).
Proof.
  induction row as [|[key v] rest IH]; intro Hkeys.
  - constructor.
  - cbn [map fst] in Hkeys.
    inversion Hkeys as [|head tail Hnot Hrest]; subst head tail.
    cbn [flat_map fst snd].
    destruct v as [|target|e i]; cbn [app]; try (apply IH; exact Hrest).
    constructor; [|apply IH; exact Hrest].
    intro Hin; apply phi_dependency_entries_member in Hin.
    destruct Hin as [other [next [Hequal Hmember]]].
    inversion Hequal; subst other next.
    apply Hnot; apply in_map_iff.
    exists (key, MemoryPhi target); split; [reflexivity|exact Hmember].
Qed.

Lemma phi_input_rows_at N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg n :
  In n (memory_phis mg) ->
  index_edges EN (phi_input_rows EN EE g effects mg) n =
    flat_map (fun key =>
      match memory_operand mg n key with
      | Some input =>
        [(key, input)]
      | None =>
        []
      end) (memory_distinct (option_encoding EE) (None :: map Some (pred_edges (prepare EN g) n))).
Proof.
  intro Hin.
  unfold phi_input_rows, index_edges.
  rewrite memory_result_index_at by exact Hin.
  reflexivity.
Qed.

Lemma phi_dependency_out_at N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg n :
  In n (memory_phis mg) ->
  Graph.out (phi_dependency_graph EN EE g effects mg) n =
    flat_map (fun kv =>
      match snd kv with
      | MemoryPhi target =>
        [PhiDependencyEdgeData n (fst kv) target]
      | _ =>
        []
      end) (index_edges EN (phi_input_rows EN EE g effects mg) n).
Proof.
  intro Hin.
  unfold phi_dependency_graph, phi_dependency_graph_from_inputs,
    phi_dependency_rows_from_inputs, index_edges at 1.
  cbn [Graph.out].
  unfold index_edges at 1.
  rewrite memory_result_index_at by exact Hin.
  reflexivity.
Qed.

Lemma phi_dependency_out_unlisted N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg n :
  ~ In n (memory_phis mg) -> Graph.out (phi_dependency_graph EN EE g effects mg) n = [].
Proof.
  intro Hnot.
  unfold phi_dependency_graph, phi_dependency_graph_from_inputs, phi_dependency_rows_from_inputs.
  cbn [Graph.out].
  unfold index_edges at 1.
  destruct (Map.get EN n (memory_result_index EN _ (memory_phis mg))) as [row|] eqn:Hget.
  - exfalso; apply Hnot.
    eapply (proj1 (memory_result_index_domain EN _ (memory_phis mg) n)).
    eexists; exact Hget.
  - reflexivity.
Qed.

Lemma phi_dependency_out_member N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n edge :
  In edge (Graph.out (phi_dependency_graph EN EE g effects mg) n) <->
    In n (memory_phis mg) /\ exists key target,
      edge = PhiDependencyEdgeData n key target /\
        memory_operand mg n key = Some (MemoryPhi target).
Proof.
  destruct (in_dec (GraphDfs.dfs_eq_dec EN) n (memory_phis mg)) as [Hin|Hnot].
  - rewrite phi_dependency_out_at by exact Hin.
    rewrite phi_dependency_entries_member, phi_input_rows_at by exact Hin.
    split.
    + intros [key [target [Hedge Hrow]]].
      apply phi_operand_rows_member in Hrow.
      split; [exact Hin|].
      exists key, target; split; [exact Hedge|exact (proj2 Hrow)].
    + intros [_ [key [target [Hedge Hoperand]]]].
      exists key, target; split; [exact Hedge|].
      apply phi_operand_rows_member; split; [|exact Hoperand].
      apply memory_distinct_in.
      eapply memory_walk_operand_key; eassumption.
  - rewrite phi_dependency_out_unlisted by exact Hnot.
    cbn; tauto.
Qed.

(** A well-formed memory graph gives a ready dependency graph with unique outgoing edges. *)
Theorem phi_dependency_ready : phi_dependency_ready_statement.
Proof.
  intros N E T EN EE g effects mg Hwf.
  apply prepare_ready.
  - constructor.
    + exact (memory_phis_nodup Hwf).
    + intros n Hin; exact Hin.
    + intros n edge Hedge.
      apply (phi_dependency_out_member N E T EN EE g effects mg Hwf) in Hedge.
      destruct Hedge as [_ [key [target [-> Hoperand]]]]; reflexivity.
    + intros n edge _ Hedge.
      apply (phi_dependency_out_member N E T EN EE g effects mg Hwf) in Hedge.
      destruct Hedge as [_ [key [target [-> Hoperand]]]].
      exact (proj2 (memory_walk_operand_valid g effects mg Hwf n key (MemoryPhi target) Hoperand)).
  - intro n.
    destruct (in_dec (GraphDfs.dfs_eq_dec EN) n (memory_phis mg)) as [Hin|Hnot].
    + rewrite phi_dependency_out_at, phi_input_rows_at by exact Hin.
      apply phi_dependency_entries_nodup, phi_operand_rows_keys_nodup, memory_distinct_nodup.
    + rewrite phi_dependency_out_unlisted by exact Hnot; constructor.
Qed.

Lemma phi_dependency_path_graph N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n m :
  phi_dependency_path mg n m ->
  exists edges, edges <> [] /\ path (phi_dependency_graph EN EE g effects mg) n edges m.
Proof.
  intro Hpath.
  induction Hpath as [n key next Hoperand|n key middle last Hoperand Hpath IH].
  - exists [PhiDependencyEdgeData n key next]; split; [discriminate|].
    apply (@path_cons N (phi_dependency_edge N E) (phi_dependency_graph EN EE g effects mg)
      (PhiDependencyEdgeData n key next) [] next); [|constructor].
    apply (phi_dependency_out_member N E T EN EE g effects mg Hwf).
    split.
    + exact (proj1 (proj1 (memory_operand_domain Hwf n key) (ex_intro _ _ Hoperand))).
    + exists key, next; split; [reflexivity|exact Hoperand].
  - destruct IH as [edges [_ Hedges]].
    exists (PhiDependencyEdgeData n key middle :: edges); split; [discriminate|].
    apply (@path_cons N (phi_dependency_edge N E) (phi_dependency_graph EN EE g effects mg)
      (PhiDependencyEdgeData n key middle) edges last); [|exact Hedges].
    apply (phi_dependency_out_member N E T EN EE g effects mg Hwf).
    split.
    + exact (proj1 (proj1 (memory_operand_domain Hwf n key) (ex_intro _ _ Hoperand))).
    + exists key, middle; split; [reflexivity|exact Hoperand].
Qed.

Lemma phi_dependency_graph_path N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n edges m :
  path (phi_dependency_graph EN EE g effects mg) n edges m ->
  edges <> [] -> phi_dependency_path mg n m.
Proof.
  intro Hpath.
  induction Hpath as [n|edge rest last Hedge Hpath IH]; intro Hnonempty.
  - contradiction.
  - apply (phi_dependency_out_member N E T EN EE g effects mg Hwf) in Hedge.
    destruct Hedge as [_ [key [next [Hedge Hoperand]]]].
    assert (Hsource : Graph.source (phi_dependency_graph EN EE g effects mg) edge =
      dependency_source edge) by reflexivity.
    assert (Htarget : Graph.target (phi_dependency_graph EN EE g effects mg) edge =
      dependency_target edge) by reflexivity.
    rewrite Hsource in Hedge, Hoperand |- *.
    destruct edge as [source edge_key target]; cbn in Hedge, Hoperand, Htarget |- *.
    inversion Hedge; subst edge_key next.
    destruct rest as [|following tail].
    + inversion Hpath; subst last.
      apply PhiDependencyEdge with (key := key); exact Hoperand.
    + eapply PhiDependencyExtend with (key := key) (middle := target).
      * exact Hoperand.
      * apply IH; discriminate.
Qed.

(** Nonempty dependency-graph paths and semantic operand paths have the same endpoints. *)
Theorem phi_dependency_paths : phi_dependency_paths_statement.
Proof.
  intros N E T EN EE g effects mg Hwf n m Hin.
  split.
  - apply phi_dependency_path_graph; exact Hwf.
  - intros [edges [Hnonempty Hpath]].
    eapply phi_dependency_graph_path; eassumption.
Qed.

(** * Cycle flags and strongly connected components *)

Lemma phi_cycle_flags_from_member N E (EN : encoding N)
    (dep : Graph.t N (phi_dependency_edge N E)) (p : prepared EN dep) components n :
  forall marked,
  FinSet.mem EN n (fold_left (fun flags component =>
    if phi_component_cyclic EN dep p component then
      fold_left (fun flags node => FinSet.add EN node flags) component flags
    else flags) components marked) = true <->
  FinSet.mem EN n marked = true \/
    exists component, In component components /\
      phi_component_cyclic EN dep p component = true /\ In n component.
Proof.
  induction components as [|component rest IH]; intro marked.
  - cbn [fold_left]; split; [auto|].
    intros [Hmarked|[c [Hfalse _]]]; [exact Hmarked|contradiction].
  - cbn [fold_left].
    rewrite IH.
    destruct (phi_component_cyclic EN dep p component) eqn:Hcyclic.
    + rewrite FinSet.mem_fold_add.
      split.
      * intros [[Hmember|Hmarked]|[c [Hrest Hfacts]]].
        -- right; exists component; split; [left; reflexivity|auto].
        -- left; exact Hmarked.
        -- right; exists c; split; [right; exact Hrest|exact Hfacts].
      * intros [Hmarked|[c [[Hequal|Hrest] Hfacts]]].
        -- left; right; exact Hmarked.
        -- subst c; left; left; exact (proj2 Hfacts).
        -- right; exists c; auto.
    + split.
      * intros [Hmarked|[c [Hrest Hfacts]]].
        -- left; exact Hmarked.
        -- right; exists c; split; [right; exact Hrest|exact Hfacts].
      * intros [Hmarked|[c [[Hequal|Hrest] Hfacts]]].
        -- left; exact Hmarked.
        -- subst c; destruct Hfacts as [Htrue _]; congruence.
        -- right; exists c; auto.
Qed.

Lemma phi_cycle_flags_member N E (EN : encoding N)
    (dep : Graph.t N (phi_dependency_edge N E)) (p : prepared EN dep) result n :
  FinSet.mem EN n (phi_cycle_flags EN dep p result) = true <->
    exists component, In component (components result) /\
      phi_component_cyclic EN dep p component = true /\ In n component.
Proof.
  unfold phi_cycle_flags.
  rewrite phi_cycle_flags_from_member, FinSet.mem_empty.
  intuition discriminate.
Qed.

Lemma phi_cycle_flags_graph_cycle N E (EN : encoding N)
    (dep : Graph.t N (phi_dependency_edge N E)) (p : prepared EN dep) n :
  ready EN dep p -> In n (Graph.nodes dep) ->
  (FinSet.mem EN n (phi_cycle_flags EN dep p (scc p)) = true <->
    exists edges, edges <> [] /\ path dep n edges n).
Proof.
  intros Hready Hin.
  rewrite phi_cycle_flags_member.
  split.
  - intros [component [Hcomponent [Hcyclic Hmember]]].
    destruct (loop_component_spec EN dep p (Graph.nodes dep) component Hready
      (fun _ H => H) Hcomponent) as [Hnodup [Hsub Hstrong]].
    change (loop_cyclic p component = true) in Hcyclic.
    destruct (loop_component_cycle EN dep p (Graph.nodes dep) component n Hready
      (fun _ H => H) Hnodup Hsub Hmember Hstrong Hcyclic) as [edges [Hnonempty Hpath]].
    exists edges; split; [exact Hnonempty|].
    eapply tarjan_induced_path; exact Hpath.
  - intros [edges [Hnonempty Hpath]].
    pose proof (tarjan_induced_full_path EN dep n edges n (proj1 Hready) Hpath Hin) as Hinduced.
    destruct (loop_cycle_scc EN dep p (Graph.nodes dep) n edges Hready
      (fun _ H => H) Hin Hnonempty Hinduced)
      as [component [Hcomponent [_ [_ [Hmember [Hcyclic _]]]]]].
    exists component; split; [exact Hcomponent|].
    split; [exact Hcyclic|exact Hmember].
Qed.

(** The prepared cycle flags identify exactly the original phis on semantic operand cycles. *)
Theorem phi_cycle_flags : phi_cycle_flags_statement.
Proof.
  intros N E T EN EE g effects mg Hwf n Hin.
  change (FinSet.mem EN n
    (AnalysesAuditMemoryPhiState.phi_cycle_flags EN (phi_dependency_graph EN EE g effects mg)
      (prepare EN (phi_dependency_graph EN EE g effects mg))
      (scc (prepare EN (phi_dependency_graph EN EE g effects mg)))) = true <->
    phi_dependency_path mg n n).
  pose proof (phi_dependency_ready N E T EN EE g effects mg Hwf) as Hready.
  rewrite (phi_cycle_flags_graph_cycle N E EN _ _ n Hready Hin).
  symmetry; apply phi_dependency_paths; assumption.
Qed.

Lemma phi_resolve_step_computes N E (EN : encoding N) (EE : encoding E) index before n after :
  phi_resolve_step EN EE index before n after ->
  audit_phi_compute_step EN EE index before n = after.
Proof.
  intro Hstep.
  rewrite phi_compute_step_indexed.
  destruct Hstep as
    [before n Hcycle
    |before n Hcycle Hempty
    |before n key input rest candidate Hcycle Hrow Hcandidate Hself Hsame
    |before n key input rest candidate Hcycle Hrow Hcandidate Hkeep].
  - now rewrite Hcycle.
  - now rewrite Hcycle, Hempty.
  - rewrite Hcycle, Hrow; cbn beta iota zeta.
    rewrite <- Hcandidate, Hself, Hsame; reflexivity.
  - rewrite Hcycle, Hrow; cbn beta iota zeta.
    rewrite <- Hcandidate.
    destruct Hkeep as [Hself|Hsame].
    + rewrite Hself; reflexivity.
    + rewrite Hsame; now destruct (Pos.eqb
        (encode (memory_version_encoding EN EE) candidate)
        (encode (memory_version_encoding EN EE) (MemoryPhi n))).
Qed.

(** Every input map and node has a relational resolution successor. *)
Theorem phi_resolve_step_total : phi_resolve_step_total_statement.
Proof.
  intros N E EN EE index before n.
  exists (audit_phi_compute_step EN EE index before n).
  apply audit_phi_compute_step_refines.
Qed.

(** Two relational resolution steps from the same input have identical output maps. *)
Theorem phi_resolve_step_deterministic : phi_resolve_step_deterministic_statement.
Proof.
  intros N E EN EE index before n a b Hfirst Hsecond.
  rewrite <- (phi_resolve_step_computes N E EN EE index before n a Hfirst).
  exact (phi_resolve_step_computes N E EN EE index before n b Hsecond).
Qed.

(** * Operand order in the actual SCC schedule *)

Lemma phi_input_row_member N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n key input :
  In n (memory_phis mg) ->
  (In (key, input) (index_edges EN (phi_input_rows EN EE g effects mg) n) <->
    memory_operand mg n key = Some input).
Proof.
  intro Hn; rewrite phi_input_rows_at by exact Hn.
  rewrite phi_operand_rows_member; split; [tauto|].
  intro Hop; split; [|exact Hop].
  apply memory_distinct_in; eapply memory_walk_operand_key; eassumption.
Qed.

Lemma phi_combine_position A B (xs : list A) (ys : list B) x y :
  In (x, y) (combine xs ys) ->
  exists k, nth_error xs k = Some x /\ nth_error ys k = Some y.
Proof.
  revert ys; induction xs as [|a xs IH]; intros [|b ys] Hin; cbn in Hin;
    try contradiction.
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst a b; exists 0; split; reflexivity.
  - destruct (IH ys Hin) as [k [Hx Hy]].
    exists (S k); split; assumption.
Qed.

Lemma phi_concat_position A (rows : list (list A)) i j a b left right :
  i < j -> nth_error rows i = Some left -> nth_error rows j = Some right ->
  In a left -> In b right -> before (concat rows) a b.
Proof.
  revert rows i; induction j as [|j IH]; intros [|row rows] i Hlt Hleft Hright Ha Hb;
    try discriminate; try lia.
  destruct i as [|i].
  - cbn in Hleft; inversion Hleft; subst row.
    cbn [nth_error] in Hright.
    apply tarjan_before_cross; [exact Ha|].
    apply in_concat; exists right; split; [eapply nth_error_In; exact Hright|exact Hb].
  - cbn [nth_error] in Hleft, Hright.
    cbn [concat].
    apply tarjan_before_prefix; apply (IH rows i); try assumption; lia.
Qed.

Lemma phi_component_before N (result : scc_result N) i j ci cj n m :
  NoDup (component_ids result) -> before (component_ids result) j i ->
  In (i, ci) (combine (component_ids result) (components result)) ->
  In (j, cj) (combine (component_ids result) (components result)) ->
  In n ci -> In m cj -> before (concat (components result)) m n.
Proof.
  intros Hids Hbefore Hi Hj Hn Hm.
  destruct (phi_combine_position _ _ _ _ _ _ Hi) as [ki [Hki Hci]].
  destruct (phi_combine_position _ _ _ _ _ _ Hj) as [kj [Hkj Hcj]].
  apply GraphDfs.dfs_before_indices in Hbefore.
  destruct Hbefore as [a [b [Hab [Ha Hb]]]].
  assert (Ha' : a = kj).
  { apply (proj1 (NoDup_nth_error _) Hids); [apply nth_error_Some; congruence|congruence]. }
  assert (Hb' : b = ki).
  { apply (proj1 (NoDup_nth_error _) Hids); [apply nth_error_Some; congruence|congruence]. }
  eapply phi_concat_position; [|exact Hcj|exact Hci|exact Hm|exact Hn].
  now subst a b.
Qed.

Lemma phi_dependency_same_component_cycle N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n key m i :
  In n (memory_phis mg) -> memory_operand mg n key = Some (MemoryPhi m) ->
  let dep := phi_dependency_graph EN EE g effects mg in
  let result := scc (prepare EN dep) in
  Map.get EN n (comp_of result) = Some i ->
  Map.get EN m (comp_of result) = Some i -> phi_dependency_path mg n n.
Proof.
  intros Hn Hop dep result Hnowner Hmowner.
  pose proof (phi_dependency_ready N E T EN EE g effects mg Hwf) as Hready.
  assert (Hm : In m (memory_phis mg)).
  { exact (proj2 (memory_walk_operand_valid g effects mg Hwf n key (MemoryPhi m) Hop)). }
  destruct (scc_exact EN dep (prepare EN dep) n m Hready) as [_ [_ Hmutual]].
  destruct (proj1 (Hmutual Hn Hm) (ex_intro _ i (conj Hnowner Hmowner)))
    as [_ [back Hback]].
  apply (proj2 (phi_dependency_paths N E T EN EE g effects mg Hwf n n Hn)).
  exists (PhiDependencyEdgeData n key m :: back); split; [discriminate|].
  apply (@path_cons N (phi_dependency_edge N E) dep
    (PhiDependencyEdgeData n key m) back n); [|exact Hback].
  apply (phi_dependency_out_member N E T EN EE g effects mg Hwf).
  split; [exact Hn|exists key, m; auto].
Qed.

Lemma phi_operand_before N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg
    (Hwf : memory_graph_wf g effects mg) n key m :
  In n (memory_phis mg) ->
  FinSet.mem EN n (phi_index_cycles (phi_prepare_dependencies EN EE g effects mg)) = false ->
  memory_operand mg n key = Some (MemoryPhi m) ->
  before (concat (components (scc (prepare EN (phi_dependency_graph EN EE g effects mg))))) m n.
Proof.
  intros Hn Hnotcycle Hop.
  set (dep := phi_dependency_graph EN EE g effects mg).
  set (prep := prepare EN dep).
  set (result := scc prep).
  pose proof (phi_dependency_ready N E T EN EE g effects mg Hwf) as Hready.
  assert (Hm : In m (memory_phis mg)).
  { exact (proj2 (memory_walk_operand_valid g effects mg Hwf n key (MemoryPhi m) Hop)). }
  assert (Hedge : In (PhiDependencyEdgeData n key m) (Graph.out dep n)).
  { apply (phi_dependency_out_member N E T EN EE g effects mg Hwf).
    split; [exact Hn|exists key, m; auto]. }
  destruct (scc_reverse_topological EN dep prep (PhiDependencyEdgeData n key m)
    (Graph.nodes dep) Hready (fun _ H => H) Hedge Hn Hm)
    as [i [j [Hi [Hj Hle]]]].
  assert (Hne : i <> j).
  { intro Heq; subst j.
    pose proof (phi_dependency_same_component_cycle N E T EN EE g effects mg Hwf
      n key m i Hn Hop Hi Hj) as Hcycle.
    apply (proj2 (phi_cycle_flags N E T EN EE g effects mg Hwf n Hn)) in Hcycle.
    congruence. }
  destruct (scc_within_indexes EN dep prep (Graph.nodes dep))
    as [_ [_ [_ [Hat [Hids [Howner Horder]]]]]].
  destruct (proj1 (Howner n i) Hi) as [ci [Hci Hni]].
  destruct (proj1 (Howner m j) Hj) as [cj [Hcj Hmj]].
  apply Hat in Hci, Hcj.
  assert (Hii : In i (component_ids result)).
  { apply in_combine_l in Hci; exact Hci. }
  assert (Hjj : In j (component_ids result)).
  { apply in_combine_l in Hcj; exact Hcj. }
  assert (Hbefore : before (component_ids result) j i).
  { apply (proj2 (GraphDfs.dfs_before_reverse (component_ids result) j i)).
    apply Horder; try assumption.
    lia. }
  eapply phi_component_before; eassumption.
Qed.

(** * Persistent resolution invariants *)

(** Stored representatives are fixed valid values, and every removed row agrees with its image. *)
Record phi_resolution_invariant {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T))
    (old : memory_graph N E) (index : phi_dependency_index (E := E) EN)
    (processed : list N) (reps : Map.t (memory_version N E) (memory_version N E)) : Prop := {
  phi_resolution_map_wf : Map.wf (memory_version_encoding EN EE) reps;
  phi_resolution_domain : forall v w,
    Map.get (memory_version_encoding EN EE) v reps = Some w ->
    exists n, v = MemoryPhi n /\ In n processed /\
      FinSet.mem EN n (phi_index_cycles index) = false /\
      exists key first, memory_operand old n key = Some first /\
        w = phi_rep_from_map EN EE reps first /\
        forall key input, memory_operand old n key = Some input ->
          phi_rep_from_map EN EE reps input = w;
  phi_resolution_range : forall v w,
    Map.get (memory_version_encoding EN EE) v reps = Some w ->
    memory_valid_version g effects old w /\
    Map.get (memory_version_encoding EN EE) w reps = None /\
    forall m, w = MemoryPhi m ->
      In m processed \/ FinSet.mem EN m (phi_index_cycles index) = true;
  phi_resolution_decision : forall n, In n processed ->
    FinSet.mem EN n (phi_index_cycles index) = false ->
    (exists key first, memory_operand old n key = Some first /\
      forall key input, memory_operand old n key = Some input ->
        phi_rep_from_map EN EE reps input = phi_rep_from_map EN EE reps first) ->
    Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps <> None
}.

Lemma phi_resolution_empty N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old index :
  phi_resolution_invariant EN EE g effects old index [] Map.empty.
Proof.
  constructor.
  - apply Map.wf_empty.
  - intros v w Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v w Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros n Hfalse; contradiction.
Qed.

Lemma phi_resolution_unprocessed N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T))
    old index processed reps n :
  phi_resolution_invariant EN EE g effects old index processed reps ->
  ~ In n processed -> Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps = None.
Proof.
  intros Hinv Hnot.
  destruct (Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps) as [w|] eqn:Hget;
    [|reflexivity].
  destruct (phi_resolution_domain EN EE g effects old index processed reps Hinv _ _ Hget)
    as [m [Heq [Hm _]]].
  inversion Heq; subst m; contradiction.
Qed.

Lemma phi_resolution_rep_valid N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T))
    old index processed reps v :
  phi_resolution_invariant EN EE g effects old index processed reps ->
  memory_valid_version g effects old v ->
  memory_valid_version g effects old (phi_rep_from_map EN EE reps v).
Proof.
  intros Hinv Hv; unfold phi_rep_from_map.
  destruct (Map.get (memory_version_encoding EN EE) v reps) as [w|] eqn:Hget; [|exact Hv].
  exact (proj1 (phi_resolution_range EN EE g effects old index processed reps Hinv _ _ Hget)).
Qed.

Lemma phi_resolution_rep_fixed N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T))
    old index processed reps v :
  phi_resolution_invariant EN EE g effects old index processed reps ->
  phi_rep_from_map EN EE reps (phi_rep_from_map EN EE reps v) = phi_rep_from_map EN EE reps v.
Proof.
  intro Hinv; unfold phi_rep_from_map at 2 3.
  destruct (Map.get (memory_version_encoding EN EE) v reps) as [w|] eqn:Hget.
  - unfold phi_rep_from_map.
    rewrite (proj1 (proj2 (phi_resolution_range EN EE g effects old index processed reps
      Hinv _ _ Hget))); reflexivity.
  - unfold phi_rep_from_map; now rewrite Hget.
Qed.

Lemma phi_rep_set_other N E (EN : encoding N) (EE : encoding E) reps n w v :
  v <> MemoryPhi n ->
  phi_rep_from_map EN EE (Map.set (memory_version_encoding EN EE) (MemoryPhi n) w reps) v =
    phi_rep_from_map EN EE reps v.
Proof.
  intro Hne; unfold phi_rep_from_map.
  now rewrite Map.get_set_other.
Qed.

Lemma phi_resolution_input_safe N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T))
    old index processed reps input :
  phi_resolution_invariant EN EE g effects old index processed reps ->
  memory_valid_version g effects old input ->
  (forall m, input = MemoryPhi m -> In m processed) ->
  let image := phi_rep_from_map EN EE reps input in
  memory_valid_version g effects old image /\
  Map.get (memory_version_encoding EN EE) image reps = None /\
  forall m, image = MemoryPhi m ->
    In m processed \/ FinSet.mem EN m (phi_index_cycles index) = true.
Proof.
  intros Hinv Hvalid Hinput; unfold phi_rep_from_map.
  destruct (Map.get (memory_version_encoding EN EE) input reps) as [w|] eqn:Hget.
  - exact (phi_resolution_range EN EE g effects old index processed reps Hinv _ _ Hget).
  - split; [exact Hvalid|split; [exact Hget|]].
    intros m Heq; left; apply Hinput; exact Heq.
Qed.

Lemma phi_resolution_safe_fresh N E (EN : encoding N)
    (index : phi_dependency_index (E := E) EN) processed n (v : memory_version N E) :
  ~ In n processed -> FinSet.mem EN n (phi_index_cycles index) = false ->
  (forall m, v = MemoryPhi m ->
    In m processed \/ FinSet.mem EN m (phi_index_cycles index) = true) ->
  v <> MemoryPhi n.
Proof.
  intros Hfresh Hcycle Hsafe Heq.
  destruct (Hsafe n Heq); congruence.
Qed.

Section ResolutionWrite.
Context {N E T : Type} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
  (effects : E -> list (ViewsMemoryEffects.memory_effect T)) (old : memory_graph N E)
  (index : phi_dependency_index (E := E) EN) (processed : list N)
  (reps : Map.t (memory_version N E) (memory_version N E)) (n : N) (key : option E)
  (first : memory_version N E) (Hwf : memory_graph_wf g effects old)
  (Hinv : phi_resolution_invariant EN EE g effects old index processed reps)
  (Hfresh : ~ In n processed) (Hcycle : FinSet.mem EN n (phi_index_cycles index) = false)
  (Hfirst : memory_operand old n key = Some first)
  (Hclosed : forall source k m, In source processed ->
    FinSet.mem EN source (phi_index_cycles index) = false ->
    memory_operand old source k = Some (MemoryPhi m) -> In m processed)
  (Hdeps : forall k m, memory_operand old n k = Some (MemoryPhi m) -> In m processed)
  (Hsame : forall k input, memory_operand old n k = Some input ->
    phi_rep_from_map EN EE reps input = phi_rep_from_map EN EE reps first).
Let candidate := phi_rep_from_map EN EE reps first.
Let next := Map.set (memory_version_encoding EN EE) (MemoryPhi n) candidate reps.

Lemma phi_write_candidate :
  memory_valid_version g effects old candidate /\
  Map.get (memory_version_encoding EN EE) candidate reps = None /\
  forall m, candidate = MemoryPhi m ->
    In m processed \/ FinSet.mem EN m (phi_index_cycles index) = true.
Proof.
  exact (phi_resolution_input_safe N E T EN EE g effects old index processed reps first
    Hinv (memory_walk_operand_valid g effects old Hwf n key first Hfirst)
    (fun m Heq => Hdeps key m (eq_trans Hfirst (f_equal Some Heq)))).
Qed.

Lemma phi_write_input k input :
  memory_operand old n k = Some input -> input <> MemoryPhi n.
Proof.
  intros Hop Heq; subst input; exact (Hfresh (Hdeps k n Hop)).
Qed.

Lemma phi_write_old_input source k input :
  In source processed -> FinSet.mem EN source (phi_index_cycles index) = false ->
  memory_operand old source k = Some input -> input <> MemoryPhi n.
Proof.
  intros Hsource Hcyclic Hop Heq; subst input.
  exact (Hfresh (Hclosed source k n Hsource Hcyclic Hop)).
Qed.

Lemma phi_write_domain v w :
  Map.get (memory_version_encoding EN EE) v next = Some w ->
  exists source, v = MemoryPhi source /\ In source (n :: processed) /\
    FinSet.mem EN source (phi_index_cycles index) = false /\
    exists k input, memory_operand old source k = Some input /\
      w = phi_rep_from_map EN EE next input /\
      forall k' input', memory_operand old source k' = Some input' ->
        phi_rep_from_map EN EE next input' = w.
Proof.
  unfold next; intro Hget.
  destruct (GraphDfs.dfs_eq_dec (memory_version_encoding EN EE) v (MemoryPhi n))
    as [Heq|Hne].
  - subst v; rewrite Map.get_set_same in Hget; inversion Hget; subst w.
    exists n; split; [reflexivity|split; [left; reflexivity|split; [exact Hcycle|]]].
    exists key, first; split; [exact Hfirst|split].
    + rewrite phi_rep_set_other by (eapply phi_write_input; exact Hfirst); reflexivity.
    + intros k input Hop; rewrite phi_rep_set_other by (eapply phi_write_input; exact Hop).
      exact (Hsame k input Hop).
  - rewrite Map.get_set_other in Hget by exact Hne.
    destruct (phi_resolution_domain EN EE g effects old index processed reps Hinv _ _ Hget)
      as [source [Hv [Hsource [Hcyclic [k [input [Hop [Hw Hall]]]]]]]].
    exists source; split; [exact Hv|split; [right; exact Hsource|split; [exact Hcyclic|]]].
    exists k, input; split; [exact Hop|split].
    + rewrite phi_rep_set_other by (eapply phi_write_old_input; eassumption); exact Hw.
    + intros k' input' Hop'.
      rewrite phi_rep_set_other by (eapply phi_write_old_input; eassumption).
      exact (Hall k' input' Hop').
Qed.

Lemma phi_write_range v w :
  Map.get (memory_version_encoding EN EE) v next = Some w ->
  memory_valid_version g effects old w /\
  Map.get (memory_version_encoding EN EE) w next = None /\
  forall m, w = MemoryPhi m ->
    In m (n :: processed) \/ FinSet.mem EN m (phi_index_cycles index) = true.
Proof.
  unfold next; intro Hget.
  destruct phi_write_candidate as [Hvalid [Hfixed Hsafe]].
  assert (Hcandidate : candidate <> MemoryPhi n).
  { apply (phi_resolution_safe_fresh N E EN index processed n candidate); assumption. }
  destruct (GraphDfs.dfs_eq_dec (memory_version_encoding EN EE) v (MemoryPhi n))
    as [Heq|Hne].
  - subst v; rewrite Map.get_set_same in Hget; inversion Hget; subst w.
    split; [exact Hvalid|split].
    + rewrite Map.get_set_other by exact Hcandidate; exact Hfixed.
    + intros m Hm; destruct (Hsafe m Hm); [left; right|right]; assumption.
  - rewrite Map.get_set_other in Hget by exact Hne.
    destruct (phi_resolution_range EN EE g effects old index processed reps Hinv _ _ Hget)
      as [Hwvalid [Hwfixed Hwsafe]].
    split; [exact Hwvalid|split].
    + rewrite Map.get_set_other; [exact Hwfixed|].
      apply (phi_resolution_safe_fresh N E EN index processed n w); assumption.
    + intros m Hm; destruct (Hwsafe m Hm); [left; right|right]; assumption.
Qed.

Lemma phi_write_decision source :
  In source (n :: processed) -> FinSet.mem EN source (phi_index_cycles index) = false ->
  (exists k input, memory_operand old source k = Some input /\
    forall k' input', memory_operand old source k' = Some input' ->
      phi_rep_from_map EN EE next input' = phi_rep_from_map EN EE next input) ->
  Map.get (memory_version_encoding EN EE) (MemoryPhi source) next <> None.
Proof.
  unfold next; intros [Heq|Hsource] Hcyclic Hresolved.
  - subst source; rewrite Map.get_set_same; discriminate.
  - rewrite Map.get_set_other by (intro Heq; inversion Heq; subst source; contradiction).
    apply (phi_resolution_decision EN EE g effects old index processed reps Hinv source
      Hsource Hcyclic).
    destruct Hresolved as [k [input [Hop Hall]]]; exists k, input; split; [exact Hop|].
    intros k' input' Hop'.
    specialize (Hall k' input' Hop').
    rewrite !phi_rep_set_other in Hall by (eapply phi_write_old_input; eassumption).
    exact Hall.
Qed.

Lemma phi_resolution_write :
  phi_resolution_invariant EN EE g effects old index (n :: processed) next.
Proof.
  constructor.
  - apply Map.wf_set; exact (phi_resolution_map_wf EN EE g effects old index processed reps Hinv).
  - exact phi_write_domain.
  - exact phi_write_range.
  - exact phi_write_decision.
Qed.

End ResolutionWrite.

Lemma phi_resolution_keep N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (index : phi_dependency_index (E := E) EN) processed reps n :
  phi_resolution_invariant EN EE g effects old index processed reps ->
  (FinSet.mem EN n (phi_index_cycles index) = false ->
    (exists key first, memory_operand old n key = Some first /\
      forall key input, memory_operand old n key = Some input ->
        phi_rep_from_map EN EE reps input = phi_rep_from_map EN EE reps first) -> False) ->
  phi_resolution_invariant EN EE g effects old index (n :: processed) reps.
Proof.
  intros Hinv Hreject; constructor.
  - exact (phi_resolution_map_wf EN EE g effects old index processed reps Hinv).
  - intros v w Hget.
    destruct (phi_resolution_domain EN EE g effects old index processed reps Hinv _ _ Hget)
      as [source [Hv [Hsource Hrest]]].
    exists source; split; [exact Hv|split; [right; exact Hsource|exact Hrest]].
  - intros v w Hget.
    destruct (phi_resolution_range EN EE g effects old index processed reps Hinv _ _ Hget)
      as [Hvalid [Hfixed Hsafe]].
    split; [exact Hvalid|split; [exact Hfixed|]].
    intros m Hm; destruct (Hsafe m Hm); [left; right|right]; assumption.
  - intros source [Heq|Hsource] Hcycle Hresolved.
    + subst source; exfalso; exact (Hreject Hcycle Hresolved).
    + exact (phi_resolution_decision EN EE g effects old index processed reps Hinv
        source Hsource Hcycle Hresolved).
Qed.

Lemma phi_same_row N E (EN : encoding N) (EE : encoding E) reps candidate row :
  forallb (phi_same_rep EN EE reps candidate) row = true <->
  forall key input, In (key, input) row -> phi_rep_from_map EN EE reps input = candidate.
Proof.
  rewrite forallb_forall; split.
  - intros Hall key input Hin.
    specialize (Hall (key, input) Hin).
    unfold phi_same_rep in Hall; cbn [snd] in Hall.
    apply Pos.eqb_eq in Hall; symmetry; eapply encode_injective; exact Hall.
  - intros Hall [key input] Hin.
    unfold phi_same_rep; cbn [snd].
    rewrite (Hall key input Hin); apply Pos.eqb_refl.
Qed.

Lemma phi_resolution_step_invariant N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (Hwf : memory_graph_wf g effects old) processed reps n :
  let index := phi_prepare_dependencies EN EE g effects old in
  phi_resolution_invariant EN EE g effects old index processed reps ->
  In n (memory_phis old) -> ~ In n processed ->
  (forall source key m, In source processed ->
    FinSet.mem EN source (phi_index_cycles index) = false ->
    memory_operand old source key = Some (MemoryPhi m) -> In m processed) ->
  (FinSet.mem EN n (phi_index_cycles index) = false ->
    forall key m, memory_operand old n key = Some (MemoryPhi m) -> In m processed) ->
  phi_resolution_invariant EN EE g effects old index (n :: processed)
    (audit_phi_compute_step EN EE index reps n).
Proof.
  intros index Hinv Hn Hfresh Hclosed Hdeps.
  rewrite phi_compute_step_indexed.
  destruct (FinSet.mem EN n (phi_index_cycles index)) eqn:Hcycle.
  - apply phi_resolution_keep; [exact Hinv|intros Hfalse; congruence].
  - specialize (Hdeps eq_refl).
    assert (Hrow : forall key input,
      In (key, input) (index_edges EN (phi_index_inputs index) n) <->
      memory_operand old n key = Some input).
    { intros key input; apply phi_input_row_member; assumption. }
    destruct (index_edges EN (phi_index_inputs index) n) as [|[key first] rest] eqn:Hinputs.
    + apply phi_resolution_keep; [exact Hinv|].
      intros _ [k [input [Hop _]]].
      apply (proj2 (Hrow k input)) in Hop; contradiction.
    + assert (Hfirst : memory_operand old n key = Some first).
      { apply (proj1 (Hrow key first)); left; reflexivity. }
      set (candidate := phi_rep_from_map EN EE reps first).
      destruct (phi_resolution_input_safe N E T EN EE g effects old index processed reps first
        Hinv (memory_walk_operand_valid g effects old Hwf n key first Hfirst)
        (fun m Heq => Hdeps key m (eq_trans Hfirst (f_equal Some Heq))))
        as [_ [_ Hsafe]].
      assert (Hne : candidate <> MemoryPhi n).
      { eapply phi_resolution_safe_fresh; eassumption. }
      assert (Hself : Pos.eqb (encode (memory_version_encoding EN EE) candidate)
        (encode (memory_version_encoding EN EE) (MemoryPhi n)) = false).
      { apply Pos.eqb_neq; intro Heq; apply Hne; eapply encode_injective; exact Heq. }
      cbn beta iota zeta; fold candidate.
      rewrite Hself; cbn [negb andb].
      destruct (forallb (phi_same_rep EN EE reps candidate) rest) eqn:Hsame.
      * apply phi_resolution_write with (key := key); try assumption.
        intros k input Hop; apply (proj2 (Hrow k input)) in Hop.
        destruct Hop as [Heq|Hin].
        -- inversion Heq; subst k input; reflexivity.
        -- apply (proj1 (phi_same_row N E EN EE reps candidate rest) Hsame k input Hin).
      * apply phi_resolution_keep; [exact Hinv|].
        intros _ [k [input [Hop Hall]]].
        assert (Hcandidate : phi_rep_from_map EN EE reps input = candidate).
        { symmetry; apply (Hall key first Hfirst). }
        assert (Htrue : forallb (phi_same_rep EN EE reps candidate) rest = true).
        { apply phi_same_row; intros k' input' Hin.
          rewrite <- Hcandidate; apply (Hall k' input').
          apply (proj1 (Hrow k' input')); right; exact Hin. }
        congruence.
Qed.

Lemma phi_resolution_fold_invariant N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (Hwf : memory_graph_wf g effects old) remaining :
  let index := phi_prepare_dependencies EN EE g effects old in
  forall processed reps,
  phi_resolution_invariant EN EE g effects old index processed reps ->
  incl remaining (memory_phis old) -> NoDup remaining ->
  (forall n, In n remaining -> ~ In n processed) ->
  (forall source key m, In source processed ->
    FinSet.mem EN source (phi_index_cycles index) = false ->
    memory_operand old source key = Some (MemoryPhi m) -> In m processed) ->
  (forall source key m, In source remaining ->
    FinSet.mem EN source (phi_index_cycles index) = false ->
    memory_operand old source key = Some (MemoryPhi m) ->
    In m processed \/ before remaining m source) ->
  phi_resolution_invariant EN EE g effects old index (rev remaining ++ processed)
    (fold_left (audit_phi_compute_step EN EE index) remaining reps).
Proof.
  intros index; induction remaining as [|n rest IH];
    intros processed reps Hinv Hlisted Hnodup Hdisjoint Hclosed Horder.
  - exact Hinv.
  - inversion Hnodup as [|head tail Hnot Hrest]; subst head tail.
    assert (Hdeps : FinSet.mem EN n (phi_index_cycles index) = false ->
      forall key m, memory_operand old n key = Some (MemoryPhi m) -> In m processed).
    { intros Hcycle key m Hop.
      destruct (Horder n key m (or_introl eq_refl) Hcycle Hop) as [Hin|Hbefore];
        [exact Hin|].
      exfalso; exact (GraphDfs.dfs_before_head_false n rest m Hnodup Hbefore). }
    assert (Hnext : phi_resolution_invariant EN EE g effects old index (n :: processed)
      (audit_phi_compute_step EN EE index reps n)).
    { apply phi_resolution_step_invariant; try assumption.
      - apply Hlisted; left; reflexivity.
      - apply Hdisjoint; left; reflexivity. }
    cbn [fold_left rev].
    rewrite <- app_assoc; cbn [app].
    apply IH; try assumption.
    + intros m Hm; apply Hlisted; right; exact Hm.
    + intros m Hm [Heq|Hin]; [subst m; contradiction|].
      exact (Hdisjoint m (or_intror Hm) Hin).
    + intros source key m [Heq|Hsource] Hcycle Hop.
      * subst source; right; exact (Hdeps Hcycle key m Hop).
      * right; exact (Hclosed source key m Hsource Hcycle Hop).
    + intros source key m Hsource Hcycle Hop.
      destruct (Horder source key m (or_intror Hsource) Hcycle Hop) as [Hin|Hbefore].
      * left; right; exact Hin.
      * apply GraphDfs.dfs_before_cons in Hbefore.
        destruct Hbefore as [[Heq _]|Hbefore].
        -- left; left; symmetry; exact Heq.
        -- right; exact Hbefore.
Qed.

Lemma phi_compute_resolution_invariant N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (Hwf : memory_graph_wf g effects old) :
  let index := phi_prepare_dependencies EN EE g effects old in
  let order := concat (components (phi_index_scc index)) in
  phi_resolution_invariant EN EE g effects old index (rev order)
    (fold_left (audit_phi_compute_step EN EE index) order Map.empty).
Proof.
  intros index order.
  pose proof (phi_dependency_ready N E T EN EE g effects old Hwf) as Hready.
  destruct (scc_within_indexes EN (phi_dependency_graph EN EE g effects old)
    (prepare EN (phi_dependency_graph EN EE g effects old)) (memory_phis old)) as [Hnodup _].
  pose proof (scc_within_members EN (phi_dependency_graph EN EE g effects old)
    (prepare EN (phi_dependency_graph EN EE g effects old)) (memory_phis old)
    Hready (fun _ H => H)) as Hmembers.
  rewrite <- (app_nil_r (rev order)).
  apply phi_resolution_fold_invariant; try assumption.
  - apply phi_resolution_empty.
  - intros n Hin; apply Hmembers; exact Hin.
  - intros n Hin Hfalse; contradiction.
  - intros source key m Hfalse; contradiction.
  - intros source key m Hin Hcycle Hop; right.
    apply (phi_operand_before N E T EN EE g effects old Hwf source key m).
    + apply Hmembers; exact Hin.
    + exact Hcycle.
    + exact Hop.
Qed.
