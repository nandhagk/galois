(** * Adequacy of complete legacy occurrence proposals

    Every occurrence branch preserves the original proposal and pays its actual captured bodies.
    For example, a missing effect skips the before callback and the complete clobber query.
    Builds on: legacy guard, effect lookup and whole clobber adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryLegacyProposalSource AnalysesAuditMemoryMemoLegacyPlain
  AnalysesAuditMemoryLegacyGuard
  AnalysesAuditMemoryLegacyGuardAdequacy AnalysesAuditMemoryDistinctAdequacy
  AnalysesAuditMemoryEffects AnalysesAuditMemoryEffectsAdequacy AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryInputBudgetAdequacy AnalysesAuditMemoryClobbersSource
  AnalysesAuditMemoryClobbersSourceAdequacy.
Import List.ListNotations.

(** Matching source observations preserve the singleton-root proposal exactly. *)
Lemma audit_legacy_finish_proposal_erases F N E T CN CE XE BE LE RE CP
    (source : E -> N * list XE) (g : Graph.t N E) function result :
  (forall e, fst (source e) = Graph.source g e) ->
  fst (@audit_legacy_finish_proposal F N E T CN CE XE BE LE RE CP source function result) =
    legacy_clobber_proposal function g result.
Proof.
  intro Hsource; unfold audit_legacy_finish_proposal, legacy_clobber_proposal.
  destruct (clobber_roots result) as [|root rest]; [reflexivity|].
  destruct rest; [|destruct root; reflexivity].
  destruct root as [|phi|edge index]; try reflexivity.
  specialize (Hsource edge); destruct (source edge); exact (f_equal (fun n => Some (MDef
    function n))
    Hsource).
Qed.

(** The generic occurrence mirror preserves the plain request and singleton finish. *)
Lemma audit_legacy_occurrence_with_erases F N E T CN CE XE BE LE RE CP
    (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) (g : Graph.t N E) (mg : memory_graph N E)
    listed reached table (before : E -> nat -> option (memory_version N E) * list BE)
    (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
    (clobbers : memory_scope T -> memory_version N E -> positive -> memory_clobber_result N E * CP)
    (function : F) fuel node :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall e, fst (edge_enc e) = encode EE e) ->
  (forall e, fst (source e) = Graph.source g e) ->
  (forall e i, fst (before e i) = memory_before mg e i) ->
  fst (audit_legacy_occurrence_source_with node_enc edge_enc source listed reached table before
    load reads clobbers function fuel node) =
  match audit_memo_legacy_request EN EE g mg reached listed table
      (fun n => fst (reads n)) (fun n => fst (load n)) node with
  | None => None
  | Some (scope, start) => legacy_clobber_proposal function g (fst (clobbers scope start fuel))
  end.
Proof.
  intros Hnode Hedge Hsource Hbefore.
  unfold audit_legacy_occurrence_source_with, audit_memo_legacy_request.
  destruct (load node) as [occurrence load_body]; cbn [fst].
  destruct occurrence as [[edge index]|]; [|reflexivity].
  pose proof (audit_legacy_guard_erases N E CN CE XE EN EE g node_enc edge_enc source reached
    listed edge node Hnode Hedge Hsource) as Hguard.
  destruct (audit_legacy_guard node_enc edge_enc source reached listed edge node)
    as [guard guard_body]; cbn [fst] in Hguard.
  rewrite <- Hguard; destruct guard; [|reflexivity].
  pose proof (audit_memory_effect_get_erases E T CE edge_enc EE table edge index (Hedge edge))
    as Heffect.
  destruct (audit_memory_effect_get edge_enc table edge index) as [effect effect_body];
    cbn [fst] in Heffect; rewrite <- Heffect.
  destruct effect as [actual|]; [|destruct (memory_before mg edge index); reflexivity].
  pose proof (Hbefore edge index) as Hinput.
  destruct (before edge index) as [input before_body]; cbn [fst] in Hinput.
  rewrite <- Hinput; destruct input as [start|]; [|reflexivity].
  destruct (memory_effect_has_read actual); [|reflexivity].
  destruct (reads node) as [footprints read_body]; cbn [fst].
  pose proof (audit_legacy_finish_proposal_erases F N E T CN CE XE BE LE RE CP source g function
    (fst (clobbers (MemoryRegions footprints) start fuel)) Hsource) as Hfinish.
  destruct (clobbers (MemoryRegions footprints) start fuel) as [result receipt].
  cbn [fst] in Hfinish.
  destruct (@audit_legacy_finish_proposal F N E T CN CE XE BE LE RE CP source function result)
    as [answer finish_body]; exact Hfinish.
Qed.

(** The strict guard pays two source calls, three node encodings and both membership probes. *)
Lemma audit_legacy_guard_work_input N E CN CE XE
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) node_work edge_work source_work
    node_budget edge_budget source_budget reached listed edge node :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  (forall e, source_work (snd (source e)) <= source_budget e) ->
  audit_legacy_guard_source_work node_work edge_work source_work
    (snd (audit_legacy_guard node_enc edge_enc source reached listed edge node)) <=
  audit_legacy_guard_input_budget node_enc edge_enc source node_budget edge_budget source_budget
    edge node.
Proof.
  intros Hnode Hedge Hsource.
  pose proof (Hsource edge) as Hsrc.
  pose proof (Hnode (fst (source edge))) as Horigin.
  pose proof (Hnode node) as Hload.
  pose proof (audit_memory_distinct_mem_bound N CN node_enc node_work (fst (source edge)) reached)
    as Hreached.
  pose proof (audit_memory_distinct_mem_bound E CE edge_enc edge_work edge listed) as Hlisted.
  pose proof (Hedge edge) as Hedgework.
  pose proof (audit_positive_eqb_source_bound (fst (node_enc (fst (source edge))))
    (fst (node_enc node))) as Hequal.
  unfold audit_legacy_guard, audit_legacy_guard_input_budget.
  destruct (source edge) as [origin source_body].
  cbn [fst snd] in *.
  destruct (node_enc origin) as [origin_code origin_body].
  destruct (node_enc node) as [node_code node_body].
  cbn [fst snd] in Horigin, Hload, Hsrc, Hequal, Hreached.
  destruct (audit_positive_eqb origin_code node_code) as [equal equal_body].
  destruct (audit_finset_mem node_enc origin reached) as [seen seen_body].
  destruct (audit_finset_mem edge_enc edge listed) as [present present_body].
  cbn [fst snd] in Hreached, Hlisted, Hequal.
  unfold audit_legacy_guard_source_work.
  cbn [snd length audit_legacy_guard_primitive_work].
  cbn [fst].
  lia.
Qed.

(** Work distributes over a concatenation without expanding any captured child body. *)
Lemma audit_legacy_occurrence_work_app F N E T CN CE XE BE LE RE CP
    node_work edge_work source_work before_work load_work read_work clobber_work
    (left right : list (audit_legacy_source_proposal_event F N E T CN CE XE BE LE RE CP)) :
  audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
    read_work clobber_work (left ++ right) =
  audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
    read_work clobber_work left +
  audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
    read_work clobber_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - cbn [app audit_legacy_occurrence_source_work]; rewrite IH; lia.
Qed.

(** A singleton definition finish pays the actual source callback; other finishes are constant. *)
Lemma audit_legacy_finish_work_input F N E T CN CE XE BE LE RE CP
    (source : E -> N * list XE) node_work edge_work source_work before_work load_work read_work
    clobber_work source_budget (function : F) result :
  (forall e, source_work (snd (source e)) <= source_budget e) ->
  audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
    read_work clobber_work
    (snd (@audit_legacy_finish_proposal F N E T CN CE XE BE LE RE CP source function result)) <=
  5 + match clobber_roots result with
  | [MemoryDef edge _] => source_budget edge
  | _ => 0
  end.
Proof.
  intro Hsource; unfold audit_legacy_finish_proposal.
  destruct (clobber_roots result) as [|root rest]; [cbn; lia|].
  destruct rest; [|destruct root; cbn; lia].
  destruct root as [|phi|edge index]; try (cbn; lia).
  specialize (Hsource edge); destruct (source edge); cbn in *; lia.
Qed.

(** Per-call callback and clobber bounds lift through all malformed and successful branches. *)
Lemma audit_legacy_occurrence_with_input_bound F N E T CN CE XE BE LE RE CP
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) listed reached table
    (before : E -> nat -> option (memory_version N E) * list BE)
    (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
    (clobbers : memory_scope T -> memory_version N E -> positive -> memory_clobber_result N E * CP)
    node_work edge_work source_work before_work load_work read_work clobber_work
    node_budget load_budget read_budget edge_budget source_budget before_budget clobber_budget
    (function : F) fuel node :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  (forall e, source_work (snd (source e)) <= source_budget e) ->
  (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
  (forall n, load_work (snd (load n)) <= load_budget n) ->
  (forall n, read_work (snd (reads n)) <= read_budget n) ->
  (forall scope start fuel, clobber_work (snd (clobbers scope start fuel)) <=
    clobber_budget scope start fuel) ->
  audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
    read_work clobber_work (snd (audit_legacy_occurrence_source_with node_enc edge_enc source
      listed reached table before load reads clobbers function fuel node)) <=
  audit_legacy_occurrence_with_input_budget node_enc edge_enc source listed reached table before
    load reads clobbers node_budget load_budget read_budget edge_budget source_budget before_budget
    clobber_budget function fuel node.
Proof.
  intros Hnode Hedge Hsource Hbefore Hload Hread Hclobber.
  pose proof (Hload node) as Hloadwork.
  unfold audit_legacy_occurrence_source_with, audit_legacy_occurrence_with_input_budget.
  destruct (load node) as [occurrence load_body]; cbn [fst snd] in Hloadwork |- *.
  destruct occurrence as [[edge index]|]; [|cbn; lia].
  pose proof (audit_legacy_guard_work_input N E CN CE XE node_enc edge_enc source node_work
    edge_work source_work node_budget edge_budget source_budget reached listed edge node
    Hnode Hedge Hsource) as Hguard.
  destruct (audit_legacy_guard node_enc edge_enc source reached listed edge node)
    as [guard guard_body]; cbn [fst snd] in Hguard |- *.
  destruct guard; [|cbn [snd app audit_legacy_occurrence_source_work]; lia].
  pose proof (audit_memory_effect_get_work_input E T CE edge_enc edge_work edge_budget table
    edge index Hedge) as Heffect.
  destruct (audit_memory_effect_get edge_enc table edge index) as [effect effect_body];
    cbn [fst snd] in Heffect |- *.
  destruct effect as [actual|]; [|cbn [snd app audit_legacy_occurrence_source_work]; lia].
  pose proof (Hbefore edge index) as Hinput.
  destruct (before edge index) as [input before_body]; cbn [fst snd] in Hinput |- *.
  destruct input as [start|]; [|cbn [snd app audit_legacy_occurrence_source_work]; lia].
  destruct (memory_effect_has_read actual);
    [|cbn [snd app audit_legacy_occurrence_source_work]; lia].
  pose proof (Hread node) as Hreadwork.
  destruct (reads node) as [footprints read_body]; cbn [fst snd] in Hreadwork |- *.
  pose proof (Hclobber (MemoryRegions footprints) start fuel) as Hquery.
  destruct (clobbers (MemoryRegions footprints) start fuel) as [result receipt];
    cbn [fst snd] in Hquery |- *.
  pose proof (audit_legacy_finish_work_input F N E T CN CE XE BE LE RE CP source node_work
    edge_work source_work before_work load_work read_work clobber_work source_budget function result
    Hsource) as Hfinish.
  destruct (@audit_legacy_finish_proposal F N E T CN CE XE BE LE RE CP source function result)
    as [answer finish_body]; cbn [snd] in Hfinish |- *.
  cbn [app audit_legacy_occurrence_source_work]; lia.
Qed.

(** The complete clobber body erases to the original occurrence producer at every input. *)
Theorem audit_legacy_occurrence_source_erases : audit_legacy_occurrence_source_erases_statement.
Proof.
  intros F N E T CN CE SE XE OE TE FE PE BE LE RE EN EE ET node_enc edge_enc site_enc source out
    target effects operand before load reads listed reached table g mg function fuel node
    Hnode Hedge Hsite Hsource Hout Htarget Hoperand Hbefore.
  unfold audit_legacy_occurrence_source.
  rewrite (audit_legacy_occurrence_with_erases F N E T CN CE XE BE LE RE _ EN EE node_enc edge_enc
    source g mg listed reached table before load reads _ function fuel node Hnode Hedge Hsource
    Hbefore).
  unfold audit_memo_legacy_request, legacy_occurrence_proposal.
  destruct (fst (load node)) as [[edge index]|]; [|reflexivity].
  destruct (Pos.eqb (encode EN (Graph.source g edge)) (encode EN node) &&
    FinSet.mem EN (Graph.source g edge) reached && FinSet.mem EE edge listed)%bool;
    [|reflexivity].
  destruct (memory_walk_effect_get EE table edge index) as [actual|];
    destruct (memory_before mg edge index) as [start|]; try reflexivity.
  destruct (memory_effect_has_read actual); [|reflexivity].
  unfold audit_legacy_full_clobbers; cbn [fst].
  rewrite (audit_memory_clobbers_source_erases N E T CN CE SE OE TE FE PE BE EN EE ET node_enc
    edge_enc site_enc out target effects operand before g (fun e => fst (effects e)) mg
    (MemoryRegions (fst (reads node))) start fuel Hnode Hedge Hsite Hout Htarget (fun _ => eq_refl)
    Hoperand Hbefore).
  reflexivity.
Qed.

(** Whole occurrence work derives its internal costs and composes the complete search bound. *)
Theorem audit_legacy_occurrence_whole_input_bound :
  audit_legacy_occurrence_whole_input_bound_statement.
Proof.
  intros F N E T CN CE SE XE OE TE FE PE BE LE RE EN node_enc edge_enc site_enc source out target
    effects operand before load reads node_work edge_work site_work source_work out_work target_work
    effect_work operand_work before_work load_work read_work node_budget edge_budget site_budget
    source_budget out_budget target_budget effect_budget operand_budget before_budget load_budget
    read_budget listed reached table g mg function fuel node Hnode Hout Htarget Hnw Hew Hsw Hxw
    How Htw Hfw Hpw Hbw Hlw Hrw.
  apply audit_legacy_occurrence_with_input_bound; try assumption.
  intros scope start query_fuel; unfold audit_legacy_full_clobbers; cbn [snd].
  apply audit_memory_clobbers_whole_input_bound; assumption.
Qed.
