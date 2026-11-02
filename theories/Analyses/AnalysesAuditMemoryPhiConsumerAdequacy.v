(** * Phi closure costs and produced graph semantics

    Returned closures preserve callback values and costs, while resolution invariants establish
    graph well-formedness and preserve the original path histories.
    For example, a removed phi has no output operand and a retained operand maps its source value.
    Builds on: AnalysesAuditMemoryPhiConsumer, persistent resolution and encoded map adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy.
From Galois.Graph Require Import GraphCore.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiPlain AnalysesAuditMemoryPhiProducer
  AnalysesAuditMemoryPhiStateAdequacy
  AnalysesAuditMemoryPhiProducerAdequacy AnalysesAuditMemoryPhiResolveAdequacy
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryEncodingAdequacy
  AnalysesAuditMemoryPhiInputBudget AnalysesAuditMemoryPhiConsumer.
Import List.ListNotations.

(** The actual optional callback body and representative read fit their input budgets. *)
Theorem audit_phi_closure_whole_input_bound : audit_phi_closure_whole_input_bound_statement.
Proof.
  intros I N E CV CE version_enc base version_work base_work version_budget base_budget
    reps input Hversion Hbase.
  specialize (Hbase input).
  unfold audit_phi_output_optional_call, audit_phi_closure_input_budget.
  destruct (base input) as [[v|] body]; cbn [fst snd] in Hbase |- *.
  - pose proof (audit_map_get_source_work_bound _ _ CV version_enc version_work v reps) as Hget.
    pose proof (Hversion v) as Hencode.
    destruct (audit_map_get version_enc v reps) as [found calls] eqn:Hread.
    cbn [snd audit_phi_closure_source_work] in Hget |- *.
    unfold audit_phi_get_input_budget.
    lia.
  - cbn [audit_phi_closure_source_work]; lia.
Qed.

(** Optional erasure preserves None and the exact stored-or-original fallback for Some. *)
Theorem audit_phi_output_optional_erases : audit_phi_output_optional_erases_statement.
Proof.
  intros I N E CV CE EN EE version_enc base original reps input Henc Hbase.
  unfold audit_phi_output_optional_call.
  destruct (base input) as [[v|] body]; cbn [fst] in Hbase.
  - pose proof (audit_map_get_erases _ _ CV version_enc (memory_version_encoding EN EE)
      v reps (Henc v)) as Hget.
    destruct (audit_map_get version_enc v reps) as [found calls].
    cbn [fst] in Hget |- *.
    rewrite <- Hbase; cbn [option_map].
    unfold audit_phi_producer_rep.
    now rewrite <- Hget.
  - rewrite <- Hbase; reflexivity.
Qed.

Lemma audit_phi_output_total_erases I N E CV CE (EN : encoding N) (EE : encoding E)
    (version_enc : memory_version N E -> positive * list CV)
    (base : I -> memory_version N E * list CE) original reps input :
  (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
  fst (base input) = original input ->
  fst (audit_phi_output_total_call version_enc base reps input) =
    Some (audit_phi_producer_rep EN EE reps (original input)).
Proof.
  intros Henc Hbase.
  unfold audit_phi_output_total_call.
  apply (audit_phi_output_optional_erases I N E CV CE EN EE version_enc
    (fun arg => let '(v, body) := base arg in (Some v, body))
    (fun arg => Some (original arg)) reps input Henc).
  destruct (base input) as [v body]; cbn [fst] in Hbase |- *.
  now rewrite Hbase.
Qed.

(** The four existing output fields instantiate closure erasure at their actual input types. *)
Theorem audit_phi_output_fields_erases : audit_phi_output_fields_erases_statement.
Proof.
  intros N E CN CE BE OE CV EN EE version_enc in_body out_body before_body operand_body
    old reps Henc Hin Hout Hbefore Hoperand.
  split.
  - intro n.
    apply (audit_phi_output_total_erases N N E CV CN EN EE version_enc in_body
      (memory_in old) reps n Henc (Hin n)).
  - split.
    + intro e.
      apply (audit_phi_output_total_erases E N E CV CE EN EE version_enc out_body
        (memory_out old) reps e Henc (Hout e)).
    + split.
      * intros e i.
        apply (audit_phi_output_optional_erases (E * nat)%type N E CV BE EN EE version_enc
          before_body (fun args => memory_before old (fst args) (snd args)) reps (e, i)
          Henc (Hbefore e i)).
      * intros n key.
        cbn [audit_phi_producer_output memory_phis memory_operand].
        rewrite audit_phi_kept_set_stable.
        destruct (FinSet.mem EN n (FinSet.of_list EN
          (filter (fun node => Pos.eqb
            (encode (memory_version_encoding EN EE) (MemoryPhi node))
            (encode (memory_version_encoding EN EE)
              (audit_phi_producer_rep EN EE reps (MemoryPhi node)))) (memory_phis old))));
          [|reflexivity].
        apply (audit_phi_output_optional_erases (N * option E)%type N E CV OE EN EE version_enc
          operand_body (fun args => memory_operand old (fst args) (snd args)) reps (n, key)
          Henc (Hoperand n key)).
Qed.

(** The complete counted producer returns the exact plain graph and representative table. *)
Theorem audit_memory_phi_producer_erases : audit_memory_phi_producer_erases_statement.
Proof.
  intros N E T CN CE PE OE EN EE node_enc edge_enc pred operand g effects mg
    Hnode Hedge Hpred Hoperand.
  set (version_enc := audit_memory_version_encode node_enc edge_enc).
  assert (Hversion : forall v, fst (version_enc v) =
    encode (memory_version_encoding EN EE) v).
  { intro v; apply audit_memory_version_encode_erases; assumption. }
  pose proof (audit_phi_producer_index_erases N E T CN CE PE OE _ EN EE node_enc edge_enc pred
    operand version_enc g effects mg Hnode Hedge Hpred Hoperand) as Hindex.
  pose proof (audit_phi_producer_value_shape N E T CN CE PE OE _ EN EE node_enc edge_enc pred
    operand version_enc g effects mg) as [Horder [Hreps Houtput]].
  rewrite Horder, Hindex in Hreps.
  rewrite (audit_phi_resolve_all_erases N E CN _ EN EE node_enc version_enc
    (phi_prepare_dependencies EN EE g effects mg)
    (List.concat (GraphScc.components
      (phi_index_scc (phi_prepare_dependencies EN EE g effects mg))))
    Hnode Hversion) in Hreps.
  rewrite (audit_phi_output_counted_erases N E CN _ EN EE node_enc version_enc mg _
    Hnode Hversion) in Houtput.
  cbn zeta.
  split.
  - rewrite Houtput, Hreps; reflexivity.
  - exact Hreps.
Qed.

(** * Semantic invariants of the actual produced graph *)

Section ComputedSemantics.
Context {N E T : Type} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
  (effects : E -> list (ViewsMemoryEffects.memory_effect T)) (old : memory_graph N E)
  (Hwf : memory_graph_wf g effects old).
Let index := phi_prepare_dependencies EN EE g effects old.
Let order := List.concat (GraphScc.components (phi_index_scc index)).
Let reps := fold_left (audit_phi_compute_step EN EE index) order Map.empty.
Let rep := phi_rep_from_map EN EE reps.
Let output := audit_phi_compute_output EN EE old reps.

Lemma phi_compute_invariant :
  phi_resolution_invariant EN EE g effects old index (rev order) reps.
Proof.
  apply phi_compute_resolution_invariant; exact Hwf.
Qed.

Lemma phi_compute_order_member n : In n (rev order) <-> In n (memory_phis old).
Proof.
  rewrite <- in_rev.
  apply GraphScc.scc_within_members.
  - apply phi_dependency_ready; exact Hwf.
  - intros node Hin; exact Hin.
Qed.

Lemma phi_compute_fixed v : rep (rep v) = rep v.
Proof.
  apply (phi_resolution_rep_fixed N E T EN EE g effects old index (rev order) reps v).
  exact phi_compute_invariant.
Qed.

Lemma phi_compute_rep_identity v :
  rep v = v <-> Map.get (memory_version_encoding EN EE) v reps = None.
Proof.
  unfold rep, phi_rep_from_map at 1.
  destruct (Map.get (memory_version_encoding EN EE) v reps) as [w|] eqn:Hget.
  - split; [|discriminate].
    intro Heq; subst w.
    destruct (phi_resolution_range EN EE g effects old index (rev order) reps
      phi_compute_invariant _ _ Hget) as [_ [Hnone _]].
    congruence.
  - tauto.
Qed.

Lemma phi_compute_terminal v :
  (v = MemoryLive \/ exists e i, v = MemoryDef e i) -> rep v = v.
Proof.
  intro Hterminal; apply phi_compute_rep_identity.
  destruct (Map.get (memory_version_encoding EN EE) v reps) as [w|] eqn:Hget;
    [|reflexivity].
  destruct (phi_resolution_domain EN EE g effects old index (rev order) reps
    phi_compute_invariant _ _ Hget) as [n [Heq _]].
  destruct Hterminal as [Hlive|[e [i Hdef]]]; congruence.
Qed.

Lemma phi_compute_kept n :
  In n (memory_phis output) <-> In n (memory_phis old) /\ rep (MemoryPhi n) = MemoryPhi n.
Proof.
  unfold output, audit_phi_compute_output; cbn [memory_phis].
  rewrite filter_In, FinSet.of_list_spec, filter_In.
  split.
  - intros [_ [Hn Heq]]; split; [exact Hn|].
    apply Pos.eqb_eq in Heq; symmetry; eapply encode_injective; exact Heq.
  - intros [Hn Heq]; split; [exact Hn|split; [exact Hn|]].
    change (Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n))
      (encode (memory_version_encoding EN EE) (rep (MemoryPhi n))) = true).
    rewrite Heq; apply Pos.eqb_refl.
Qed.

Lemma phi_compute_valid v :
  memory_valid_version g effects old v -> memory_valid_version g effects output (rep v).
Proof.
  intro Hv.
  pose proof (phi_resolution_rep_valid N E T EN EE g effects old index (rev order) reps v
    phi_compute_invariant Hv) as Himage.
  pose proof (phi_compute_fixed v) as Hfixed.
  change (memory_valid_version g effects old (rep v)) in Himage.
  destruct (rep v) as [|n|e i] eqn:Hrep; try exact Himage.
  destruct Himage as [Hreachable Hn].
  split; [exact Hreachable|apply phi_compute_kept; split; assumption].
Qed.

Lemma phi_compute_removed n :
  In n (memory_phis old) -> ~ In n (memory_phis output) ->
  exists w, Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps = Some w /\
    rep (MemoryPhi n) = w /\
    exists key first, memory_operand old n key = Some first /\
      forall key input, memory_operand old n key = Some input -> rep input = w.
Proof.
  intros Hn Hremoved.
  destruct (Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps) as [w|] eqn:Hget.
  - exists w; split; [reflexivity|split; [unfold rep, phi_rep_from_map; now rewrite Hget|]].
    destruct (phi_resolution_domain EN EE g effects old index (rev order) reps
      phi_compute_invariant _ _ Hget) as [m [Heq [_ [_ [key [first [Hop [_ Hall]]]]]]]].
    inversion Heq; subst m; exists key, first; auto.
  - exfalso; apply Hremoved; apply phi_compute_kept; split; [exact Hn|].
    apply phi_compute_rep_identity; exact Hget.
Qed.

Lemma phi_compute_operand n key :
  memory_operand output n key =
    if FinSet.mem EN n (FinSet.of_list EN (memory_phis output))
    then option_map rep (memory_operand old n key) else None.
Proof.
  unfold output, audit_phi_compute_output; cbn [memory_operand memory_phis].
  rewrite audit_phi_kept_set_stable; reflexivity.
Qed.

Lemma phi_compute_operand_kept n key :
  In n (memory_phis output) ->
  memory_operand output n key = option_map rep (memory_operand old n key).
Proof.
  intro Hn; rewrite phi_compute_operand.
  rewrite (proj2 (FinSet.of_list_spec EN _ _) Hn); reflexivity.
Qed.

Lemma phi_compute_arrival n key v :
  memory_arrival old n key v -> memory_arrival output n key (rep v).
Proof.
  intros [[Hphi [Hop Hin]]|[Hnot Hin]].
  - destruct (in_dec (GraphDfs.dfs_eq_dec EN) n (memory_phis output)) as [Hkept|Hremoved].
    + left; split; [exact Hkept|split].
      * rewrite phi_compute_operand_kept by exact Hkept; now rewrite Hop.
      * change (rep (memory_in old n) = MemoryPhi n).
        rewrite Hin; exact (proj2 (proj1 (phi_compute_kept n) Hkept)).
    + right; split; [exact Hremoved|].
      change (rep (memory_in old n) = rep v); rewrite Hin.
      destruct (phi_compute_removed n Hphi Hremoved) as [w [_ [Hrep [k [first [_ Hall]]]]]].
      rewrite Hrep, (Hall key v Hop); reflexivity.
  - right; split.
    + intro Hnew; apply Hnot; exact (proj1 (proj1 (phi_compute_kept n) Hnew)).
    + change (rep (memory_in old n) = rep v); now rewrite Hin.
Qed.

Lemma phi_compute_after e i (a : ViewsMemoryEffects.memory_effect T) v :
  rep (memory_after e i a v) = memory_after e i a (rep v).
Proof.
  unfold memory_after; destruct (ViewsMemoryEffects.effect_is_def a); [|reflexivity].
  apply phi_compute_terminal; right; exists e, i; reflexivity.
Qed.

Lemma phi_compute_edge_flow e start (actions : list (ViewsMemoryEffects.memory_effect T))
    input last :
  memory_edge_flow old e start actions input last ->
  memory_edge_flow output e start actions (rep input) (rep last).
Proof.
  intro Hflow; induction Hflow as [i v|i a rest v w Hbefore Hflow IH].
  - constructor.
  - constructor.
    + change (option_map rep (memory_before old e i) = Some (rep v)).
      now rewrite Hbefore.
    + rewrite <- phi_compute_after; exact IH.
Qed.

Lemma phi_compute_versions_exact v :
  In v (memory_versions output) <-> memory_valid_version g effects output v.
Proof.
  unfold output, audit_phi_compute_output; cbn [memory_versions].
  rewrite filter_In, (memory_versions_exact Hwf).
  destruct v as [|n|e i]; cbn [memory_valid_version].
  - tauto.
  - fold output; rewrite <- audit_phi_kept_set_stable.
    change ((reachable g n /\ memory_phi_at old n) /\
      FinSet.mem EN n (FinSet.of_list EN (memory_phis output)) = true <->
      reachable g n /\ memory_phi_at output n).
    rewrite FinSet.of_list_spec; unfold memory_phi_at.
    split; [tauto|].
    intros [Hreach Hn]; split; [split; [exact Hreach|]|exact Hn].
    exact (proj1 (proj1 (phi_compute_kept n) Hn)).
  - tauto.
Qed.

Lemma phi_compute_operand_domain n key :
  (exists v, memory_operand output n key = Some v) <->
  memory_phi_at output n /\
  match key with
  | None => In n (Graph.entries g)
  | Some e => In e (Graph.out g (Graph.source g e)) /\
      reachable g (Graph.source g e) /\ Graph.target g e = n
  end.
Proof.
  rewrite phi_compute_operand.
  destruct (FinSet.mem EN n (FinSet.of_list EN (memory_phis output))) eqn:Hkept.
  - apply FinSet.of_list_spec in Hkept.
    split.
    + intros [v Hv].
      destruct (memory_operand old n key) as [input|] eqn:Hop; cbn in Hv; [|discriminate].
      split; [exact Hkept|].
      exact (proj2 (proj1 (memory_operand_domain Hwf n key) (ex_intro _ input Hop))).
    + intros [_ Hkey].
      destruct (proj2 (memory_operand_domain Hwf n key)
        (conj (proj1 (proj1 (phi_compute_kept n) Hkept)) Hkey)) as [v Hv].
      rewrite Hv; exists (rep v); reflexivity.
  - split; [intros [v Hfalse]; discriminate|].
    intros [Hn _]; unfold memory_phi_at in Hn.
    apply (proj2 (FinSet.of_list_spec EN n (memory_phis output))) in Hn; congruence.
Qed.

Lemma phi_compute_wf : memory_graph_wf g effects output.
Proof.
  constructor.
  - exact (memory_cfg_wf Hwf).
  - apply NoDup_filter; exact (memory_phis_nodup Hwf).
  - intros n Hn; apply (memory_phi_reachable Hwf).
    exact (proj1 (proj1 (phi_compute_kept n) Hn)).
  - apply NoDup_filter; exact (memory_versions_nodup Hwf).
  - apply phi_compute_versions_exact.
  - intros n Hentry.
    pose proof (phi_compute_arrival n None MemoryLive (memory_entries_arrive Hwf n Hentry))
      as Harrival.
    rewrite (phi_compute_terminal MemoryLive (or_introl eq_refl)) in Harrival.
    exact Harrival.
  - intros e Hedge Hreach.
    apply phi_compute_edge_flow; apply (memory_edges_flow Hwf); assumption.
  - intros e Hedge Hreach.
    apply phi_compute_arrival; apply (memory_edges_arrive Hwf); assumption.
  - intros n Hreach; apply phi_compute_valid; apply (memory_in_valid Hwf); exact Hreach.
  - intros e Hedge Hreach; apply phi_compute_valid; apply (memory_out_valid Hwf); assumption.
  - intros e i.
    change ((exists v, option_map rep (memory_before old e i) = Some v) <->
      exists a, memory_occurrence g effects e i a).
    rewrite <- (memory_before_domain Hwf e i).
    destruct (memory_before old e i) as [v|]; cbn; split;
      intros [w Heq]; try discriminate; eexists; reflexivity.
  - apply phi_compute_operand_domain.
Qed.

Lemma phi_compute_edge_provenance e start (actions : list (ViewsMemoryEffects.memory_effect T))
    input origin last final :
  memory_edge_provenance old e start actions input origin last final ->
  rep origin = origin ->
  memory_edge_provenance output e start actions (rep input) origin (rep last) final /\
    rep final = final.
Proof.
  intro Hhistory.
  induction Hhistory as [i input origin|i a rest input origin last final Hbefore Hhistory IH];
    intro Horigin.
  - split; [constructor|exact Horigin].
  - assert (Hafter : rep (memory_after e i a origin) = memory_after e i a origin).
    { rewrite phi_compute_after, Horigin; reflexivity. }
    destruct (IH Hafter) as [Htail Hfinal].
    split; [|exact Hfinal].
    constructor.
    + change (option_map rep (memory_before old e i) = Some (rep input)).
      now rewrite Hbefore.
    + rewrite <- phi_compute_after; exact Htail.
Qed.

Lemma phi_compute_provenance root es n v origin :
  memory_provenance g effects old root es n v origin ->
  memory_provenance g effects output root es n (rep v) origin /\ rep origin = origin.
Proof.
  intro Hhistory.
  induction Hhistory as [Hentry Harrival|es e origin last Hhistory IH Hedge Hflow Harrival].
  - split.
    + apply memory_provenance_entry; [exact Hentry|].
      pose proof (phi_compute_arrival root None MemoryLive Harrival) as Hnew.
      rewrite (phi_compute_terminal MemoryLive (or_introl eq_refl)) in Hnew; exact Hnew.
    + apply phi_compute_terminal; left; reflexivity.
  - destruct IH as [Hprefix Horigin].
    destruct (phi_compute_edge_provenance e 0 (effects e) _ _ _ _ Hflow Horigin)
      as [Hedgehistory Hlast].
    split; [|exact Hlast].
    apply (@memory_provenance_edge N E T g effects output root es e origin last);
      [exact Hprefix|exact Hedge|exact Hedgehistory|].
    apply phi_compute_arrival; exact Harrival.
Qed.

Lemma phi_compute_last_defs e start (actions : list (ViewsMemoryEffects.memory_effect T)) origin :
  rep origin = origin ->
  rep (memory_last_defs e start actions origin) = memory_last_defs e start actions origin.
Proof.
  revert start origin; induction actions as [|a rest IH]; intros start origin Horigin.
  - exact Horigin.
  - cbn [memory_last_defs]; apply IH.
    rewrite phi_compute_after, Horigin; reflexivity.
Qed.

Lemma phi_compute_last_path es :
  rep (memory_last_path effects es) = memory_last_path effects es.
Proof.
  unfold memory_last_path.
  assert (Hfold : forall edges origin, rep origin = origin ->
    rep (fold_left (fun value e => memory_last_defs e 0 (effects e) value) edges origin) =
      fold_left (fun value e => memory_last_defs e 0 (effects e) value) edges origin).
  { induction edges as [|e rest IH]; intros origin Horigin; [exact Horigin|].
    cbn [fold_left]; apply IH, phi_compute_last_defs; exact Horigin. }
  apply Hfold, phi_compute_terminal; left; reflexivity.
Qed.

Lemma phi_compute_occurrence_history es e i input origin :
  memory_occurrence_history g effects old es e i input origin ->
  memory_occurrence_history g effects output es e i (rep input) origin.
Proof.
  intros [Hbefore [Hprefix Horigin]].
  split.
  - change (option_map rep (memory_before old e i) = Some (rep input)); now rewrite Hbefore.
  - split; [|exact Horigin].
    exact (proj1 (phi_compute_edge_provenance e 0 (firstn i (effects e)) _ _ _ _
      Hprefix (phi_compute_last_path es))).
Qed.

Lemma phi_compute_history_projection :
  phi_history_projection EN EE g effects old
    (@PhiResult N E output reps).
Proof.
  unfold phi_history_projection; cbn [phi_graph phi_representatives].
  change (memory_graph_wf g effects output /\
    Map.wf (memory_version_encoding EN EE) reps /\
    (forall n, In n (memory_phis output) -> In n (memory_phis old)) /\
    (forall v, memory_valid_version g effects old v ->
      memory_valid_version g effects output (rep v)) /\
    rep MemoryLive = MemoryLive /\
    (forall e i, rep (MemoryDef e i) = MemoryDef e i) /\
    (forall n, In n (memory_phis output) -> rep (MemoryPhi n) = MemoryPhi n) /\
    (forall v, rep (rep v) = rep v) /\
    (forall n, memory_in output n = rep (memory_in old n)) /\
    (forall e, memory_out output e = rep (memory_out old e)) /\
    (forall e i, memory_before output e i = option_map rep (memory_before old e i)) /\
    (forall n key, In n (memory_phis output) ->
      memory_operand output n key = option_map rep (memory_operand old n key)) /\
    (forall n, In n (memory_phis old) -> ~ In n (memory_phis output) ->
      rep (MemoryPhi n) <> MemoryPhi n /\
      forall key input, memory_operand old n key = Some input -> rep input = rep (MemoryPhi n)) /\
    (forall root es n v origin, memory_provenance g effects old root es n v origin ->
      memory_provenance g effects output root es n (rep v) origin) /\
    forall es e i input origin, memory_occurrence_history g effects old es e i input origin ->
      memory_occurrence_history g effects output es e i (rep input) origin).
  split; [exact phi_compute_wf|].
  split; [exact (phi_resolution_map_wf EN EE g effects old index (rev order) reps
    phi_compute_invariant)|].
  split; [intros n Hn; exact (proj1 (proj1 (phi_compute_kept n) Hn))|].
  split; [exact phi_compute_valid|].
  split; [apply phi_compute_terminal; left; reflexivity|].
  split; [intros e i; apply phi_compute_terminal; right; eauto|].
  split; [intros n Hn; exact (proj2 (proj1 (phi_compute_kept n) Hn))|].
  split; [exact phi_compute_fixed|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact phi_compute_operand_kept|].
  split.
  - intros n Hn Hremoved; split.
    + intro Heq; apply Hremoved; apply phi_compute_kept; auto.
    + destruct (phi_compute_removed n Hn Hremoved) as [w [_ [Hrep [_ [_ [_ Hall]]]]]].
      intros key input Hop; rewrite Hrep; exact (Hall key input Hop).
  - split.
    + intros root es n v origin Hhistory.
      exact (proj1 (phi_compute_provenance root es n v origin Hhistory)).
    + exact phi_compute_occurrence_history.
Qed.

Lemma phi_compute_cycle_kept n :
  In n (memory_phis old) -> phi_dependency_path old n n -> In n (memory_phis output).
Proof.
  intros Hn Hpath; apply phi_compute_kept; split; [exact Hn|].
  apply phi_compute_rep_identity.
  pose proof (proj2 (phi_cycle_flags N E T EN EE g effects old Hwf n Hn) Hpath) as Hcycle.
  change (FinSet.mem EN n (phi_index_cycles index) = true) in Hcycle.
  destruct (Map.get (memory_version_encoding EN EE) (MemoryPhi n) reps) as [w|] eqn:Hget;
    [|reflexivity].
  destruct (phi_resolution_domain EN EE g effects old index (rev order) reps
    phi_compute_invariant _ _ Hget) as [m [Heq [_ [Hfalse _]]]].
  inversion Heq; subst m; congruence.
Qed.

Lemma phi_compute_resolved_removed n :
  In n (memory_phis old) -> ~ phi_dependency_path old n n ->
  (exists key first, memory_operand old n key = Some first /\
    forall key input, memory_operand old n key = Some input -> rep input = rep first) ->
  ~ In n (memory_phis output).
Proof.
  intros Hn Hacyclic Hresolved Hkept.
  assert (Hcycle : FinSet.mem EN n (phi_index_cycles index) = false).
  { destruct (FinSet.mem EN n (phi_index_cycles index)) eqn:Hflag; [|reflexivity].
    exfalso; apply Hacyclic; apply (proj1 (phi_cycle_flags N E T EN EE g effects old Hwf n Hn));
      exact Hflag. }
  pose proof (phi_resolution_decision EN EE g effects old index (rev order) reps
    phi_compute_invariant n (proj2 (phi_compute_order_member n) Hn) Hcycle Hresolved) as Hbound.
  apply Hbound; apply phi_compute_rep_identity.
  exact (proj2 (proj1 (phi_compute_kept n) Hkept)).
Qed.

Lemma phi_dependency_first n m :
  phi_dependency_path old n m ->
  exists key next, memory_operand old n key = Some (MemoryPhi next).
Proof.
  intros Hpath; destruct Hpath as [n key next Hop|n key middle last Hop Htail]; eauto.
Qed.

Lemma phi_compute_terminal_removed n v :
  In n (memory_phis old) ->
  (v = MemoryLive \/ exists e i, v = MemoryDef e i) ->
  (exists key, memory_operand old n key = Some v) ->
  (forall key input, memory_operand old n key = Some input -> input = v) ->
  ~ In n (memory_phis output).
Proof.
  intros Hn Hterminal [key Hfirst] Hall.
  apply phi_compute_resolved_removed; [exact Hn| |].
  - intro Hpath.
    destruct (phi_dependency_first n n Hpath) as [k [next Hop]].
    specialize (Hall k (MemoryPhi next) Hop).
    destruct Hterminal as [Heq|[e [i Heq]]]; congruence.
  - exists key, v; split; [exact Hfirst|].
    intros k input Hop; now rewrite (Hall k input Hop).
Qed.

End ComputedSemantics.

(** The plain producer preserves history, terminal removal, cycles and checked legacy bytes. *)
Theorem audit_memory_phi_prune_semantics : audit_memory_phi_prune_semantics_statement.
Proof.
  split.
  - intros N E T EN EE g effects old Hwf.
    apply phi_compute_history_projection; exact Hwf.
  - split.
    + intros N E T EN EE g effects old Hwf n v Hn Hterminal Hfirst Hall.
      apply (phi_compute_terminal_removed EN EE g effects old Hwf n v); assumption.
    + split.
      * intros N E T EN EE g effects old Hwf n Hn [key Hself] Hall.
        apply (phi_compute_cycle_kept EN EE g effects old Hwf n Hn).
        apply PhiDependencyEdge with (key := key); exact Hself.
      * split.
        -- intros N E T EN EE g effects old Hwf n Hn Hcycle.
           apply (phi_compute_cycle_kept EN EE g effects old Hwf n); assumption.
        -- split.
           ++ intros F N E T EN EE EF ET f g effects writes reads old loads fuel Hwf.
              split; apply AnalysesMemoryLegacy.project_memory_legacy_correct.
              ** exact Hwf.
              ** apply phi_compute_wf; exact Hwf.
           ++ intros S O N E T F L m bv EN EE EF ET f effects reads old loads fuel Hbytes Hwf.
              pose proof (AnalysesMemoryLegacy.project_memory_legacy_correct EN EE EF ET f
                (ViewsGraph.cfg (AnalysesMemoryBase.bgv bv)) effects
                (AnalysesMemoryBase.writes_at bv) reads old loads fuel Hwf) as Hold.
              pose proof (phi_compute_wf EN EE _ effects old Hwf) as Hnewwf.
              pose proof (AnalysesMemoryLegacy.project_memory_legacy_correct EN EE EF ET f
                (ViewsGraph.cfg (AnalysesMemoryBase.bgv bv)) effects
                (AnalysesMemoryBase.writes_at bv) reads _ loads fuel Hnewwf) as Hnew.
              destruct (AnalysesMemoryLegacy.no_clobber_unchanged m bv EN EF ET f _ reads
                Hbytes Hold) as [Holddef Holdlive].
              destruct (AnalysesMemoryLegacy.no_clobber_unchanged m bv EN EF ET f _ reads
                Hbytes Hnew) as [Hnewdef Hnewlive].
              split.
              ** intros before first after e es n l site offset Hreach Hfirst Hrun Hpoint
                   Hcovered Hsite.
                 split; intro Hdef.
                 --- exact (Holddef before first after e es n Hreach Hfirst Hrun Hpoint Hdef
                       l site offset Hcovered Hsite).
                 --- exact (Hnewdef before first after e es n Hreach Hfirst Hrun Hpoint Hdef
                       l site offset Hcovered Hsite).
              ** intros before es after n l site offset Hreach Hentry Hrun Hpoint Hcovered Hsite.
                 split; intro Hlive.
                 --- exact (Holdlive before es after n Hreach Hentry Hrun Hpoint Hlive
                       l site offset Hcovered Hsite).
                 --- exact (Hnewlive before es after n Hreach Hentry Hrun Hpoint Hlive
                       l site offset Hcovered Hsite).
Qed.
