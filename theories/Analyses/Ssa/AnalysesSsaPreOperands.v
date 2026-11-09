(** * Materialized factored redundancy graphs and explicit construction outcomes

    The raw builder preserves discovery exhaustion, rename exhaustion and missing block names.
    For example, a completed diamond retains separate operands for its two incoming join edges.
    Builds on: AnalysesSsaPreFrg, AnalysesSsaPreRename and the shared costed list operations. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom GraphCheckDomCost.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep
  AnalysesSsaPreFrameEnd AnalysesSsaPreFrameCache AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameVisit
  AnalysesSsaPreFrameOrigins AnalysesSsaPreFrameMeaning AnalysesSsaPreFrameDominance AnalysesSsaPreFrameTables
  AnalysesSsaPreFrameWalk AnalysesSsaPreFrameOccurrence.
Import List.ListNotations Cost.Notations.

Module PreOperands.

Section Build.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Version materialization reads cached fresh definitions rather than rescanning program edges. *)
Definition version_list_c family keys (acc : PreRename.accumulator B BE E U) :=
  let* unavailable := map_c (fun u => Cost.ret (PreFrg.Unavailable u)) family in
  let* initial_family := filter_c (fun u => Cost.step ;; Pre.initial_c (Pre.input c) u) family in
  let* initials := map_c (fun u => Cost.ret (PreFrg.Initial u)) initial_family in
  let* phis := map_c (fun key => Cost.ret (PreFrg.Phi (fst key) (snd key))) keys in
  let* definitions := app_c phis (PreRename.created acc) in
  let* available := app_c initials definitions in
  let* versions := app_c unavailable available in
  PreFamily.canonical_c (PreFrg.version_encoding c) versions.
Definition version_list family keys acc := Cost.value (version_list_c family keys acc).

Definition assemble_c family keys (acc : PreRename.accumulator B BE E U) status :=
  let* versions := version_list_c family keys acc in
  let* phis := FinSet.of_list_c (PreFrg.phi_encoding c) keys in
  Cost.ret (PreFrg.Frg versions (PreRename.occurrence_index acc) (PreRename.fresh_index acc)
    phis (PreRename.link_index acc) (PreRename.unsafe_index acc) status).
Definition assemble family keys acc status := Cost.value (assemble_c family keys acc status).

(** Raw unsupported inputs return their actual partial output
    and an explicit construction status. *)
Definition build_frg_c : Cost.t (PreFrg.frg B BE E U) :=
  let* placement := PreFrg.phi_sites_c c in
  match placement with
  | inl partial =>
    let* family := filter_c (fun u => Cost.step ;; Pre.pure_c (Pre.input c) u) partial in
    assemble_c family [] PreRename.empty_accumulator PreFrg.DiscoveryExhausted
  | inr data =>
    let* index := PreRename.prepare_c c data in
    let* result := PreRename.run_c c index in
    assemble_c (PreRename.eligible_family index) (PreRename.phi_keys index)
      (PreRename.stop_output result) (PreRename.stop_status result)
  end.
Definition build_frg := Cost.value build_frg_c.

(** The version list contains exactly the constructor-tagged materialization sources. *)
Theorem version_list_equation family keys {acc} :
  version_list family keys acc =
    PreFamily.canonical (PreFrg.version_encoding c)
      (map PreFrg.Unavailable family ++ map PreFrg.Initial (filter (Pre.initial c) family) ++
        map (fun key => PreFrg.Phi (fst key) (snd key)) keys ++ PreRename.created acc).
Proof.
  unfold version_list, version_list_c; rewrite !Cost.value_bind.
  rewrite !value_map_c, value_filter_c, !value_app_c; reflexivity.
Qed.

(** Assembly retains every accumulated index
    and canonicalizes the materialized node inventory. *)
Theorem assemble_equation family keys {acc status} :
  assemble family keys acc status =
    PreFrg.Frg (version_list family keys acc) (PreRename.occurrence_index acc)
      (PreRename.fresh_index acc) (FinSet.of_list (PreFrg.phi_encoding c) keys)
      (PreRename.link_index acc) (PreRename.unsafe_index acc) status.
Proof.
  unfold assemble, assemble_c; rewrite !Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** Successful placement delegates once to the prepared scoped renamer and retains its outcome. *)
Theorem build_frg_equation :
  build_frg =
    match PreFrg.phi_sites c with
    | inl partial =>
      assemble (filter (Pre.pure c) partial) [] PreRename.empty_accumulator
        PreFrg.DiscoveryExhausted
    | inr data =>
      let index := PreRename.prepare c data in
      let result := PreRename.run c index in
      assemble (PreRename.eligible_family index) (PreRename.phi_keys index)
        (PreRename.stop_output result) (PreRename.stop_status result)
    end.
Proof.
  unfold build_frg, build_frg_c; rewrite Cost.value_bind; fold (PreFrg.phi_sites c).
  destruct (PreFrg.phi_sites c); rewrite !Cost.value_bind, ?value_filter_c; reflexivity.
Qed.

(** Raw assembly always produces a duplicate-free version list. *)
Theorem assemble_versions_nodup {family keys acc status} :
  NoDup (PreFrg.versions (assemble family keys acc status)).
Proof.
  rewrite assemble_equation; cbn [PreFrg.versions]; rewrite version_list_equation.
  apply PreFamily.canonical_nodup.
Qed.

Local Lemma assemble_indexes_wf family keys {acc status} :
  PreFrameEnd.accumulator_wf c acc ->
  Map.wf (Pre.ee (Pre.keys c)) (PreFrg.occurrences (assemble family keys acc status)) /\
  FinSet.wf (Pre.ee (Pre.keys c)) (PreFrg.fresh (assemble family keys acc status)) /\
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.phis (assemble family keys acc status)) /\
  Map.wf (PreFrg.link_encoding c) (PreFrg.operands (assemble family keys acc status)) /\
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.unsafe (assemble family keys acc status)).
Proof.
  intros [Hocc [Hfresh [Hlinks Hunsafe]]]; rewrite assemble_equation.
  repeat split; try assumption; apply FinSet.wf_of_list.
Qed.

(** Every raw producer outcome retains canonical occurrence, fresh, phi,
    operand and unsafe indexes. *)
Theorem build_frg_indexes_wf :
  Map.wf (Pre.ee (Pre.keys c)) (PreFrg.occurrences build_frg) /\
  FinSet.wf (Pre.ee (Pre.keys c)) (PreFrg.fresh build_frg) /\
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.phis build_frg) /\
  Map.wf (PreFrg.link_encoding c) (PreFrg.operands build_frg) /\
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.unsafe build_frg).
Proof.
  rewrite build_frg_equation; destruct (PreFrg.phi_sites c).
  - apply assemble_indexes_wf; exact (PreFrameEnd.empty_accumulator_wf c).
  - apply assemble_indexes_wf; apply PreFrameEnd.run_wf.
Qed.

(** Every raw producer outcome enumerates each materialized graph version once. *)
Theorem build_frg_versions_nodup : NoDup (PreFrg.versions build_frg).
Proof.
  rewrite build_frg_equation; destruct (PreFrg.phi_sites c); apply assemble_versions_nodup.
Qed.

(** A lawful context makes the actual discovery and scoped-driver construction complete. *)
Theorem build_frg_completed :
  Pre.laws c -> PreFrg.status build_frg = PreFrg.Completed.
Proof.
  intro Hlaw; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Hdata Hrest]].
  rewrite build_frg_equation, Hdata, assemble_equation; cbn [PreFrg.status].
  apply PreRename.run_completed; apply PreRename.prepare_walk_domain; exact Hlaw.
Qed.

(** Every materialized version has a pure family expression and its actual static source domain. *)
Theorem build_frg_source_versions :
  Pre.laws c ->
  forall d, In d (PreFrg.versions build_frg) -> PreFrameInvariant.source_version c d.
Proof.
  intros Hlaw d Hd; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hd.
  cbn [PreFrg.versions] in Hd; rewrite version_list_equation in Hd.
  rewrite (PreFamily.canonical_member _ (PreFrg.version_encoding_laws c Hlaw)) in Hd.
  rewrite !in_app_iff in Hd.
  destruct Hd as [Hmissing|[Hinitial|[Hphi|Hcreated]]].
  - apply in_map_iff in Hmissing; destruct Hmissing as [u [<- Hu]].
    rewrite (PreFrameCache.cached_eligible c data _ (PreFrameCache.prepare_laws c data)) in Hu.
    apply (PreFrameCache.eligible_exact c data Hdata) in Hu.
    unfold PreFrameInvariant.source_version; cbn [PreFrg.version_expr PreFrg.definition_domain].
    tauto.
  - apply in_map_iff in Hinitial; destruct Hinitial as [u [<- Hu]].
    apply filter_In in Hu; destruct Hu as [Hu Hinitial].
    rewrite (PreFrameCache.cached_eligible c data _ (PreFrameCache.prepare_laws c data)) in Hu.
    apply (PreFrameCache.eligible_exact c data Hdata) in Hu.
    unfold PreFrameInvariant.source_version; cbn [PreFrg.version_expr PreFrg.definition_domain].
    tauto.
  - apply in_map_iff in Hphi; destruct Hphi as [[b u] [<- Hkey]].
    rewrite (PreFrameCache.cached_phi_keys c data _ (PreFrameCache.prepare_laws c data)) in Hkey.
    apply (PreFrameCache.keys_exact c data Hlaw Hdata) in Hkey.
    unfold PreFrameInvariant.source_version; cbn [PreFrg.version_expr PreFrg.definition_domain].
    split; [exact (PreFrg.phi_needed_family c (proj1 Hkey))|exact (conj (proj2 Hkey) (proj1 Hkey))].
  - exact (proj1 (PreFrameInvariant.source_created c _
      (PreFrameInvariant.run_output_source c data Hlaw Hdata) d Hcreated)).
Qed.

(** Every selected occurrence is backed by a pure source computation and a nonsentinel definition. *)
Theorem build_frg_occurrence_sources :
  Pre.laws c ->
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some d ->
    PreFrameInvariant.occurrence_source_at c e d.
Proof.
  intros Hlaw e d Hget; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hget.
  exact (PreFrameInvariant.source_occurrences c _
    (PreFrameInvariant.run_output_source c data Hlaw Hdata) e d Hget).
Qed.

(** Every listed pure recomputation receives an actual finite occurrence in the completed graph. *)
Theorem build_frg_occurrence_total :
  Pre.laws c ->
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      exists d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some d.
Proof.
  intros Hlaw e u He Hcomputed Hpure.
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation.
  exact (PreFrameVisit.run_occurrence_total c data Hlaw Hdata e u He Hcomputed Hpure).
Qed.

Local Lemma created_fresh_exact :
  Pre.laws c ->
  forall data, PreFrameCache.placement_laws c data ->
  forall e u,
    let acc := PreRename.stop_output (PreRename.run c (PreRename.prepare c data)) in
    In (PreFrg.Fresh e u) (PreRename.created acc) <->
      In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u /\
        FinSet.mem (Pre.ee (Pre.keys c)) e (PreRename.fresh_index acc) = true.
Proof.
  intros Hlaw data Hdata e u acc.
  pose proof (PreFrameInvariant.run_output_source c data Hlaw Hdata) as Hsource.
  pose proof (proj2 (PreFrameEnd.run_fresh_ledger c Hlaw (PreRename.prepare c data)) e) as Hledger.
  split.
  - intro Hin; destruct (PreFrameInvariant.source_created c _ Hsource _ Hin) as [Hd Horigin].
    destruct Hd as [Hfamily [Hpure [He Hcomputed]]].
    split; [exact He|]; split; [exact Hcomputed|].
    apply Hledger; now exists u.
  - intros [He [Hcomputed Hflag]]; apply Hledger in Hflag; destruct Hflag as [v Hin].
    destruct (PreFrameInvariant.source_created c _ Hsource _ Hin) as [Hd Horigin].
    destruct Hd as [Hfamily [Hpure [He' Hcomputed']]].
    assert (v = u) by congruence; subst v; exact Hin.
Qed.

(** Assembly membership separates constructor origins without identifying distinct source expressions. *)
Local Lemma assembled_member :
  Pre.laws c ->
  forall family keys acc,
    (forall d, In d (PreRename.created acc) -> exists e u, d = PreFrg.Fresh e u) ->
  forall d, In d (version_list family keys acc) <->
    match d with
    | PreFrg.Unavailable u => In u family
    | PreFrg.Initial u => In u family /\ Pre.initial c u = true
    | PreFrg.Fresh e u => In (PreFrg.Fresh e u) (PreRename.created acc)
    | PreFrg.Phi b u => In (b, u) keys
    end.
Proof.
  intros Hlaw family keys acc Hcreated d; rewrite version_list_equation,
    (PreFamily.canonical_member _ (PreFrg.version_encoding_laws c Hlaw)), !in_app_iff.
  split.
  - intros [Hmissing|[Hinitial|[Hphi|Hfresh]]].
    + apply in_map_iff in Hmissing; destruct Hmissing as [u [<- Hin]]; exact Hin.
    + apply in_map_iff in Hinitial; destruct Hinitial as [u [<- Hin]].
      apply filter_In in Hin; exact Hin.
    + apply in_map_iff in Hphi; destruct Hphi as [[b u] [<- Hin]]; exact Hin.
    + destruct (Hcreated d Hfresh) as [e [u ->]]; exact Hfresh.
  - destruct d as [u|u|e u|b u]; intro Hin.
    + left; apply in_map; exact Hin.
    + right; left; apply in_map; apply filter_In; exact Hin.
    + right; right; right; exact Hin.
    + right; right; left; apply in_map_iff; exists (b, u); auto.
Qed.

(** Materialized versions are exactly eligible sentinels, actual initials, source fresh flags and phis. *)
Theorem build_frg_versions_exact :
  Pre.laws c ->
  forall d, In d (PreFrg.versions build_frg) <->
    match d with
    | PreFrg.Unavailable u => PreFamily.in_family c u /\ Pre.pure c u = true
    | PreFrg.Initial u =>
        PreFamily.in_family c u /\ Pre.pure c u = true /\ Pre.initial c u = true
    | PreFrg.Fresh e u =>
        In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u /\
        FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true
    | PreFrg.Phi b u => FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = true
    end.
Proof.
  intros Hlaw d; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  pose proof (PreFrameInvariant.run_output_source c data Hlaw Hdata) as Hsource.
  rewrite build_frg_equation, Houtput, assemble_equation.
  cbn [PreFrg.versions PreFrg.fresh PreFrg.phis].
  rewrite (assembled_member Hlaw) by
    (intros version Hversion; exact (proj2
      (PreFrameInvariant.source_created c _ Hsource version Hversion))).
  destruct d as [u|u|e u|b u].
  - rewrite (PreFrameCache.cached_eligible c data _ (PreFrameCache.prepare_laws c data)).
    apply PreFrameCache.eligible_exact; exact Hdata.
  - rewrite (PreFrameCache.cached_eligible c data _ (PreFrameCache.prepare_laws c data)),
      (PreFrameCache.eligible_exact c data Hdata); tauto.
  - exact (created_fresh_exact Hlaw data Hdata e u).
  - symmetry; apply PreFamily.set_member; apply PreFrg.phi_encoding_laws; exact Hlaw.
Qed.

(** The final phi index contains exactly the pure sites of all four placement constructors. *)
Theorem build_frg_phi_exact :
  Pre.laws c ->
  forall b u, FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = true <->
    PreFamily.in_family c u /\ Pre.pure c u = true /\ PreFrg.phi_needed c u b.
Proof.
  intros Hlaw b u; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation; cbn [PreFrg.phis].
  rewrite (PreFamily.set_member _ (PreFrg.phi_encoding_laws c Hlaw)),
    (PreFrameCache.cached_phi_keys c data _ (PreFrameCache.prepare_laws c data)),
    (PreFrameCache.keys_exact c data Hlaw Hdata).
  split; [intros [Hphi Hpure]; repeat split; try assumption;
    exact (PreFrg.phi_needed_family c Hphi)|tauto].
Qed.

Local Lemma source_materialized :
  Pre.laws c ->
  forall data acc, PreFrameCache.placement_laws c data ->
  forall d, PreFrameInvariant.source_version c d ->
    PreFrameOrigins.origin (PreRename.created acc) d ->
    In d (version_list (PreRename.eligible_family (PreRename.prepare c data))
      (PreRename.phi_keys (PreRename.prepare c data)) acc).
Proof.
  intros Hlaw data acc Hdata d [Hfamily [Hpure Hdomain]] Horigin.
  rewrite version_list_equation,
    (PreFamily.canonical_member _ (PreFrg.version_encoding_laws c Hlaw)), !in_app_iff.
  rewrite (PreFrameCache.cached_eligible c data _ (PreFrameCache.prepare_laws c data)),
    (PreFrameCache.cached_phi_keys c data _ (PreFrameCache.prepare_laws c data)).
  destruct d as [u|u|e u|b u].
  - left; apply in_map; apply (PreFrameCache.eligible_exact c data Hdata); auto.
  - right; left; apply in_map; apply filter_In; split; [|exact (proj2 Hdomain)].
    apply (PreFrameCache.eligible_exact c data Hdata); auto.
  - right; right; right; exact Horigin.
  - right; right; left; apply in_map_iff; exists (b, u); split; [reflexivity|].
    apply (PreFrameCache.keys_exact c data Hlaw Hdata); auto.
Qed.

(** Every selected occurrence version belongs to the actual final materialized version list. *)
Theorem build_frg_occurrence_member :
  Pre.laws c ->
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some d ->
    In d (PreFrg.versions build_frg).
Proof.
  intros Hlaw e d Hget.
  destruct (build_frg_occurrence_sources Hlaw e d Hget) as [He [u [Hcomputed
    [Hpure [Hexpr [Hsource Hnonempty]]]]]].
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hget |- *.
  apply (source_materialized Hlaw data _ Hdata d Hsource).
  exact (PreFrameOrigins.origins_occurrences c _
    (PreFrameOrigins.run_prepared_origins c data) e d Hget).
Qed.

(** Every final incoming link retains its actual phi, incoming edge and translated source version. *)
Theorem build_frg_operand_sources :
  Pre.laws c ->
  forall key op, Map.get (PreFrg.link_encoding c) key (PreFrg.operands build_frg) = Some op ->
    PreFrameInvariant.link_source_at c key op.
Proof.
  intros Hlaw key op Hget.
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hget.
  exact (PreFrameInvariant.source_links c _
    (PreFrameInvariant.run_links_source c data Hlaw Hdata) key op Hget).
Qed.

(** Every selected incoming operand version belongs to the same graph's final node inventory. *)
Theorem build_frg_operand_member :
  Pre.laws c ->
  forall key op, Map.get (PreFrg.link_encoding c) key (PreFrg.operands build_frg) = Some op ->
    In (PreFrg.operand_version op) (PreFrg.versions build_frg).
Proof.
  intros Hlaw key op Hget.
  destruct (build_frg_operand_sources Hlaw key op Hget) as
    [Hphi [Hpure [Hbe [Htarget [Htranslate Hsource]]]]].
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hget |- *.
  apply (source_materialized Hlaw data _ Hdata _ Hsource).
  exact (PreFrameOrigins.origins_links c _
    (PreFrameOrigins.run_prepared_origins c data) key op Hget).
Qed.

(** Every incoming operand key names a real phi site and a listed incoming edge to that site. *)
Theorem build_frg_operand_domain :
  Pre.laws c ->
  forall b u be op,
    Map.get (PreFrg.link_encoding c) ((b, u), be) (PreFrg.operands build_frg) = Some op ->
    FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = true /\
    In be (Cfg.edges (Pre.block_cfg c)) /\ Graph.target (Pre.bg c) be = b.
Proof.
  intros Hlaw b u be op Hget.
  destruct (build_frg_operand_sources Hlaw _ _ Hget) as
    [Hphi [Hpure [Hbe [Htarget [Htranslate Hsource]]]]].
  split; [|exact (conj Hbe Htarget)].
  apply (proj2 (build_frg_phi_exact Hlaw b u)).
  exact (conj (PreFrg.phi_needed_family c Hphi) (conj Hpure Hphi)).
Qed.

(** The actual builder's prepared entry scope has full frame meaning for its final graph. *)
Theorem build_frg_entry_scope_laws :
  Pre.laws c ->
  forall data, PreFrg.phi_sites c = inr data ->
  forall b first, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block (Pre.points (Pre.input c)) b) 0 = Some first ->
    Graph.entries (Pre.pg c) = [first] ->
    PreCoverage.scope_laws c build_frg first (PreRename.entry_scope (PreRename.prepare c data)).
Proof.
  intros Hlaw data Houtput b first Hb Hfirst Hentry.
  eapply (PreFrameMeaning.entry_scope_laws c build_frg Hlaw).
  - intros d Hd; exact (proj2 (proj2 (build_frg_source_versions Hlaw d Hd))).
  - intros e d Hget.
    destruct (build_frg_occurrence_sources Hlaw e d Hget) as [He [u [Hcomputed Hrest]]].
    split; [exact He|now exists u].
  - exact (PreFrameCache.placement_from_output c Hlaw data Houtput).
  - exact Hb.
  - exact Hfirst.
  - exact Hentry.
  - intros u Hfamily Hpure; rewrite (build_frg_versions_exact Hlaw (PreFrg.Initial u)); tauto.
Qed.

(** Actual selected definitions dominate occurrence targets and every nonfresh selection's source. *)
Theorem build_frg_occurrence_dominance :
  Pre.laws c ->
  forall e d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some d ->
    PreFrameDominance.occurrence_dominance c e d.
Proof.
  intros Hlaw e d Hget.
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hget.
  exact (PreFrameDominance.dominance_occurrences c _
    (PreFrameDominance.run_dominance c data Hlaw Hdata) e d Hget).
Qed.

(** A built phi has no real use at its own completed parameter-definition point. *)
Theorem build_frg_phi_no_real_use :
  Pre.laws c ->
  forall b u, In b (Graph.nodes (Pre.bg c)) ->
    ~ PreCoverage.real_use_at c build_frg
      (Graph.target (Pre.pg c) (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
      (PreFrg.Phi b u).
Proof.
  intros Hlaw b u Hb; eapply (PreFrameMeaning.phi_no_real_use c build_frg Hlaw).
  - intros e d Hget; destruct (build_frg_occurrence_sources Hlaw e d Hget)
      as [He [v [Hcomputed Hrest]]]; split; [exact He|now exists v].
  - intros e d Hget q Hq.
    destruct (build_frg_occurrence_dominance Hlaw e d Hget) as [point [Hpoint [Hdom Hreuse]]].
    assert (point = q) by congruence; subst point; exact Hdom.
  - exact Hb.
Qed.

(** Every materialized phi establishes a nearest available unused frame at its actual definition. *)
Theorem build_frg_phi_frame :
  Pre.laws c ->
  forall b u, FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = true ->
    PreCoverage.frame_laws c build_frg u
      (Graph.target (Pre.pg c) (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
      (PreRename.Frame (PreFrg.Operand (PreFrg.Phi b u) false) true).
Proof.
  intros Hlaw b u Hphi.
  pose proof (PreFrg.phi_needed_nodes c Hlaw (proj2 (proj2
    (proj1 (build_frg_phi_exact Hlaw b u) Hphi)))) as Hb.
  apply (PreFrameStep.definition_frame c build_frg Hlaw u _ (PreFrg.Phi b u) false).
  - destruct (PreFrg.parameter_edge_listed c Hlaw Hb) as [He Hi].
    destruct (PreCoverage.listed_edge_out c Hlaw He) as [Hsource Hout].
    apply (Pre.reachable_points c (Pre.graphs c Hlaw)).
    exact (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      _ _ Hsource Hout).
  - exact (proj2 (build_frg_versions_exact Hlaw (PreFrg.Phi b u)) Hphi).
  - reflexivity.
  - rewrite PreFrg.version_point_equation; reflexivity.
  - split; [discriminate|intro Hreal].
    exfalso; exact (build_frg_phi_no_real_use Hlaw b u Hb Hreal).
Qed.

(** A completed instruction has no other matching definition when its fresh and phi cases are absent. *)
Theorem build_frg_no_definition_target :
  Pre.laws c ->
  forall b e u, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    ~ In (PreFrg.Fresh e u) (PreFrg.versions build_frg) ->
    (e = SsaPoints.parameter_edge (Pre.points (Pre.input c)) b ->
      FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = false) ->
  forall d, In d (PreFrg.versions build_frg) -> PreFrg.version_expr d = u ->
    PreFrg.version_point c d <> Some (Graph.target (Pre.pg c) e).
Proof.
  intros Hlaw b e u Hb Hin Hfresh Hphi d Hd Hu Hpoint.
  pose proof (PreCoverage.instruction_edge_listed c Hlaw Hb Hin) as He.
  pose proof (instruction_edges_internal (Pre.point_laws c (Pre.graphs c Hlaw)) b e Hb Hin) as Hi.
  pose proof (proj2 (proj2 (build_frg_source_versions Hlaw d Hd))) as Hdomain.
  destruct d as [v|v|other v|owner v]; cbn [PreFrg.version_expr] in Hu; subst v;
    rewrite PreFrg.version_point_equation in Hpoint.
  - discriminate.
  - exact (PreFrg.internal_target_not_entry c Hlaw He Hi
      (nth_error_In _ _ Hpoint) eq_refl).
  - destruct Hdomain as [Hother Hcomputed].
    assert (Htarget : Graph.target (Pre.pg c) other = Graph.target (Pre.pg c) e) by congruence.
    pose proof (PreCoverage.internal_incoming_unique c Hlaw He Hi Hother Htarget) as Heq.
    subst other; exact (Hfresh Hd).
  - pose proof (PreFrg.phi_needed_nodes c Hlaw Hdomain) as Howner.
    destruct (PreFrg.parameter_edge_listed c Hlaw Howner) as [Hparameter Hiparameter].
    assert (Htarget : Graph.target (Pre.pg c)
      (SsaPoints.parameter_edge (Pre.points (Pre.input c)) owner) = Graph.target (Pre.pg c) e)
      by congruence.
    pose proof (PreCoverage.internal_incoming_unique c Hlaw He Hi Hparameter Htarget) as Hedge.
    assert (Hblock : owner = b).
    { pose proof (PreFrameTables.instruction_owner c Hlaw Hb Hin) as Howner_e.
      pose proof (PreFrameTables.instruction_owner c Hlaw Howner
        (nth_error_In _ _ (parameter_edge_first (Pre.point_laws c (Pre.graphs c Hlaw))
          owner Howner))) as Howner_parameter.
      rewrite Hedge in Howner_parameter; congruence. }
    subst owner; pose proof (Hphi (eq_sym Hedge)) as Habsent.
    pose proof (proj1 (build_frg_versions_exact Hlaw (PreFrg.Phi b u)) Hd) as Hpresent; congruence.
Qed.

Local Lemma built_fresh_absent {e u} :
  Pre.laws c ->
  (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = false \/
    Pre.recomputed c e <> Some u) ->
    ~ In (PreFrg.Fresh e u) (PreFrg.versions build_frg).
Proof.
  intros Hlaw Habsent Hin.
  apply (proj1 (build_frg_versions_exact Hlaw (PreFrg.Fresh e u))) in Hin.
  destruct Hin as [He [Hcomputed Hflag]]; destruct Habsent; congruence.
Qed.

Local Lemma built_frame_unchanged :
  Pre.laws c ->
  forall b e u frame, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    ~ In (PreFrg.Fresh e u) (PreFrg.versions build_frg) ->
    (e = SsaPoints.parameter_edge (Pre.points (Pre.input c)) b ->
      FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = false) ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) <>
      Some (PreFrg.operand_version (PreRename.selected frame)) ->
    PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) frame ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (if Pre.killed c e u then PreRename.Frame (PreRename.selected frame) false else frame).
Proof.
  intros Hlaw b e u [[d real] available] Hb Hin Hfresh Hphi Hnot Hframe.
  pose proof (PreFrameStep.frame_instruction c build_frg Hlaw
    (fun edge version Hget => proj1 (build_frg_occurrence_sources Hlaw edge version Hget))
    u e d real available false (PreCoverage.instruction_edge_listed c Hlaw Hb Hin)
    (instruction_edges_internal (Pre.point_laws c (Pre.graphs c Hlaw)) b e Hb Hin)
    (build_frg_no_definition_target Hlaw b e u Hb Hin Hfresh Hphi)
    ltac:(split; [discriminate|intro Hget; exfalso; exact (Hnot Hget)]) Hframe) as Htarget.
  rewrite orb_false_r in Htarget.
  destruct (Pre.killed c e u), available; exact Htarget.
Qed.

Local Lemma built_frame_reused :
  Pre.laws c ->
  forall b e u frame, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = false ->
    e <> SsaPoints.parameter_edge (Pre.points (Pre.input c)) b ->
    PreRename.available frame = true ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) =
      Some (PreFrg.operand_version (PreRename.selected frame)) ->
    PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) frame ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (PreRename.Frame (PreFrg.Operand
        (PreFrg.operand_version (PreRename.selected frame)) true) (negb (Pre.killed c e u))).
Proof.
  intros Hlaw b e u [[d real] available] Hb Hin Hflag Hparameter Hav Hget Hframe.
  cbn [PreRename.available] in Hav; subst available.
  pose proof (PreFrameStep.frame_instruction c build_frg Hlaw
    (fun edge version Hread => proj1 (build_frg_occurrence_sources Hlaw edge version Hread))
    u e d real true true (PreCoverage.instruction_edge_listed c Hlaw Hb Hin)
    (instruction_edges_internal (Pre.point_laws c (Pre.graphs c Hlaw)) b e Hb Hin)
    (build_frg_no_definition_target Hlaw b e u Hb Hin
      (built_fresh_absent Hlaw (or_introl Hflag)) ltac:(intro Heq; contradiction))
    ltac:(split; [intros _; exact Hget|intros _; reflexivity]) Hframe) as Htarget.
  rewrite orb_true_r in Htarget; exact Htarget.
Qed.

Local Lemma built_fresh_frame :
  Pre.laws c ->
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u ->
    FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some (PreFrg.Fresh e u) ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (PreRename.Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true).
Proof.
  intros Hlaw e u He Hcomputed Hfresh Hget.
  apply (PreFrameStep.definition_frame c build_frg Hlaw u _ (PreFrg.Fresh e u) true).
  - destruct (PreCoverage.listed_edge_out c Hlaw He) as [Hsource Hout].
    apply (Pre.reachable_points c (Pre.graphs c Hlaw)).
    exact (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      _ e Hsource Hout).
  - apply (proj2 (build_frg_versions_exact Hlaw (PreFrg.Fresh e u))); auto.
  - reflexivity.
  - rewrite PreFrg.version_point_equation; reflexivity.
  - split; [intros _; exists e; split; [exact Hget|apply dominates_refl]|intros _; reflexivity].
Qed.

Local Lemma built_different_selection :
  Pre.laws c ->
  forall e v u frame, Pre.recomputed c e = Some v -> u <> v ->
    PreFrg.version_expr (PreFrg.operand_version (PreRename.selected frame)) = u ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) <>
      Some (PreFrg.operand_version (PreRename.selected frame)).
Proof.
  intros Hlaw e v u frame Hcomputed Hne Hexpr Hget.
  destruct (build_frg_occurrence_sources Hlaw e _ Hget) as [He [value [Hvalue
    [Hpure [Hidentity Hrest]]]]].
  apply Hne; congruence.
Qed.

Local Definition built_stamp e :=
  (Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg),
    FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg)).

Local Lemma built_phi_absent :
  Pre.laws c ->
  forall data, PreFrameCache.placement_laws c data ->
  forall b e u id, Intern.find (Pre.eu (Pre.keys c)) u (PreFrameCache.names c data) = Some id ->
    eqb (Pre.ee (Pre.keys c)) e (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) &&
      existsb (fun pair => eqb (Pre.eu (Pre.keys c)) u (snd (snd pair)))
        (Index.find (Pre.eb (Pre.keys c)) b
          (PreRename.phi_definitions (PreRename.prepare c data))) = false ->
    e = SsaPoints.parameter_edge (Pre.points (Pre.input c)) b ->
      FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg) = false.
Proof.
  intros Hlaw data Hdata b e u id Hid Hnone Heq; subst e.
  rewrite eqb_refl in Hnone; cbn [andb] in Hnone.
  destruct (FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis build_frg)) eqn:Hphi;
    [|reflexivity].
  pose proof (proj2 (proj2 (proj1 (build_frg_phi_exact Hlaw b u) Hphi))) as Hneeded.
  pose proof (proj2 (PreFrameInvariant.phi_bucket_test c data Hlaw Hdata b u id Hid) Hneeded);
    congruence.
Qed.

Local Lemma built_skipped_frame :
  Pre.laws c ->
  forall data, PreFrameCache.placement_laws c data ->
  forall frames acc b e, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    PreFrameInvariant.scope_source c data frames ->
    PreRename.evaluation (PreFrameCache.event_description c (PreFrameCache.names c data) e) = None ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = None ->
    FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = false ->
    PreCoverage.scope_laws c build_frg (Graph.source (Pre.pg c) e) frames ->
  forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (PreRename.top c (fst (PreRename.instruction c (PreRename.prepare c data) b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) (frames, acc) e)) u).
Proof.
  intros Hlaw data Hdata frames acc b e Hb Hin Hsource Hskip Hget Hflag Hscope u Hu Hpure.
  pose proof (PreCoverage.instruction_edge_listed c Hlaw Hb Hin) as He.
  destruct (proj2 (PreFrameCache.names_domain c data Hlaw Hdata u) (conj Hu Hpure)) as [id Hid].
  rewrite (PreFrameInvariant.instruction_top c data Hlaw Hdata frames acc b e Hsource He u id Hid).
  cbn zeta; rewrite Hskip, PreRename.occurrence_equation; cbn [fst snd].
  destruct (eqb (Pre.ee (Pre.keys c)) e (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) &&
    existsb (fun pair => eqb (Pre.eu (Pre.keys c)) u (snd (snd pair)))
      (Index.find (Pre.eb (Pre.keys c)) b
        (PreRename.phi_definitions (PreRename.prepare c data)))) eqn:Hphi.
  - apply andb_true_iff in Hphi; destruct Hphi as [Hparameter Hneeded].
    apply (eqb_true_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hparameter; subst e.
    apply build_frg_phi_frame; [exact Hlaw|].
    apply (proj2 (build_frg_phi_exact Hlaw b u)); split; [exact Hu|]; split; [exact Hpure|].
    exact (proj1 (PreFrameInvariant.phi_bucket_test c data Hlaw Hdata b u id Hid) Hneeded).
  - apply (built_frame_unchanged Hlaw b e u _ Hb Hin).
    + exact (built_fresh_absent Hlaw (or_introl Hflag)).
    + exact (built_phi_absent Hlaw data Hdata b e u id Hid Hphi).
    + rewrite Hget; discriminate.
    + exact (Hscope u Hu Hpure).
Qed.

Local Lemma built_other_frame :
  Pre.laws c ->
  forall b e v u frame, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    Pre.recomputed c e = Some v -> u <> v ->
    PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) frame ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (if Pre.killed c e u then PreRename.Frame (PreRename.selected frame) false else frame).
Proof.
  intros Hlaw b e v u frame Hb Hin Hcomputed Hne Hframe.
  apply (built_frame_unchanged Hlaw b e u frame Hb Hin).
  - apply built_fresh_absent; [exact Hlaw|right; intro Heq; apply Hne; congruence].
  - intro Heq; exfalso; exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e v Hcomputed) b Heq).
  - exact (built_different_selection Hlaw e v u frame Hcomputed Hne (proj1 Hframe)).
  - exact Hframe.
Qed.

Local Lemma built_named_reuse :
  Pre.laws c ->
  forall data frames b e id u, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    PreFrameInvariant.scope_source c data frames ->
    Intern.find (Pre.eu (Pre.keys c)) u (PreFrameCache.names c data) = Some id ->
    PreRename.frame_reuse c (PreRename.top_id frames id u) u = true ->
    e <> SsaPoints.parameter_edge (Pre.points (Pre.input c)) b ->
    FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = false ->
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) =
      Some (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u))) ->
    PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) (PreRename.top c frames u) ->
    let used := PreRename.Frame (PreFrg.Operand
      (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u))) true) true in
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (if Pre.killed c e u then PreRename.Frame (PreRename.selected used) false else used).
Proof.
  intros Hlaw data frames b e id u Hb Hin Hsource Hfind Hreuse Hparameter Hflag Hget Hscope.
  assert (Htop : PreRename.top_id frames id u = PreRename.top c frames u).
  { symmetry; apply PreFrameCache.top_id_agrees.
    rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hfind. }
  rewrite Htop in Hreuse, Hget |- *.
  assert (Havailable : PreRename.available (PreRename.top c frames u) = true).
  { unfold PreRename.frame_reuse in Hreuse.
    destruct (PreRename.available (PreRename.top c frames u)); [reflexivity|discriminate]. }
  pose proof (built_frame_reused Hlaw b e u _ Hb Hin Hflag Hparameter Havailable Hget Hscope)
    as Hframe.
  destruct (Pre.killed c e u); exact Hframe.
Qed.

Local Lemma built_real_frame :
  Pre.laws c ->
  forall data, PreFrameCache.placement_laws c data ->
  forall frames acc b e id v, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    PreFrameInvariant.scope_source c data frames ->
    PreRename.evaluation (PreFrameCache.event_description c (PreFrameCache.names c data) e) =
      Some (id, v) ->
    built_stamp e = (
      let frame := PreRename.top_id frames id v in
      let reuse := PreRename.frame_reuse c frame v in
      (Some (if reuse then PreFrg.operand_version (PreRename.selected frame)
        else PreFrg.Fresh e v), negb reuse)) ->
    PreCoverage.scope_laws c build_frg (Graph.source (Pre.pg c) e) frames ->
  forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
    PreCoverage.frame_laws c build_frg u (Graph.target (Pre.pg c) e)
      (PreRename.top c (fst (PreRename.instruction c (PreRename.prepare c data) b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) (frames, acc) e)) u).
Proof.
  intros Hlaw data Hdata frames acc b e id v Hb Hin Hsource Hinstance Hstamp Hscope u Hu Hpure.
  pose proof (PreCoverage.instruction_edge_listed c Hlaw Hb Hin) as He.
  destruct (proj1 (PreFrameCache.evaluation_exact c (PreFrameCache.names c data) e) Hinstance)
    as [Hcomputed [Hvpure Hfind]].
  assert (Hparameter : eqb (Pre.ee (Pre.keys c)) e
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) = false).
  { apply (eqb_false_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))).
    exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e v Hcomputed) b). }
  destruct (proj2 (PreFrameCache.names_domain c data Hlaw Hdata u) (conj Hu Hpure))
    as [query Hquery].
  rewrite (PreFrameInvariant.instruction_top c data Hlaw Hdata
    frames acc b e Hsource He u query Hquery).
  cbn zeta; rewrite Hinstance, PreRename.occurrence_equation, Hparameter; cbn [andb].
  cbn zeta in Hstamp |- *.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id v) v) eqn:Hreuse;
    cbn [fst snd].
  - rewrite (PreFrameCache.top_store c Hlaw frames v id _
      (PreFrameInvariant.scope_representation c data frames Hsource)).
    2: { rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hfind. }
    destruct (eqb (Pre.eu (Pre.keys c)) u v) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hsame; subst v.
      apply (built_named_reuse Hlaw data frames b e id u Hb Hin Hsource Hfind Hreuse).
      * exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed) b).
      * exact (f_equal snd Hstamp).
      * exact (f_equal fst Hstamp).
      * exact (Hscope u Hu Hpure).
    + apply built_other_frame with (b := b) (v := v); try assumption.
      * apply (eqb_false_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))); exact Hsame.
      * exact (Hscope u Hu Hpure).
  - destruct (eqb (Pre.eu (Pre.keys c)) u v) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hsame; subst v.
      apply (built_fresh_frame Hlaw e u He Hcomputed).
      * exact (f_equal snd Hstamp).
      * exact (f_equal fst Hstamp).
    + apply built_other_frame with (b := b) (v := v); try assumption.
      * apply (eqb_false_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))); exact Hsame.
      * exact (Hscope u Hu Hpure).
Qed.

Local Lemma built_instruction_scope :
  Pre.laws c ->
  forall data, PreFrameCache.placement_laws c data ->
  forall frames acc b e, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreFrameTables.stamp c e acc = (None, false) ->
    built_stamp e = PreFrameTables.stamp c e
      (snd (PreRename.instruction c (PreRename.prepare c data) b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) (frames, acc) e)) ->
    PreCoverage.scope_laws c build_frg (Graph.source (Pre.pg c) e) frames ->
    PreCoverage.scope_laws c build_frg (Graph.target (Pre.pg c) e)
      (fst (PreRename.instruction c (PreRename.prepare c data) b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b) (frames, acc) e)).
Proof.
  intros Hlaw data Hdata frames acc b e Hb Hin Hsource Hwf Hbefore Hpacket Hscope.
  pose proof (PreCoverage.instruction_edge_listed c Hlaw Hb Hin) as He.
  pose proof (PreFrameCache.event_lookup c data Hlaw e He) as Hlookup.
  destruct (PreRename.evaluation
    (PreFrameCache.event_description c (PreFrameCache.names c data) e))
    as [[id v]|] eqn:Hinstance.
  - rewrite (PreFrameTables.real_packet_stamp c (work := (frames, acc))
      Hwf Hlookup Hinstance Hbefore) in Hpacket.
    exact (built_real_frame Hlaw data Hdata frames acc b e id v
      Hb Hin Hsource Hinstance Hpacket Hscope).
  - rewrite (PreFrameTables.skipped_packet_stamp c (work := (frames, acc))
      Hlookup Hinstance) in Hpacket.
    cbn [snd] in Hpacket; rewrite Hbefore in Hpacket.
    exact (built_skipped_frame Hlaw data Hdata frames acc b e Hb Hin Hsource Hinstance
      (f_equal fst Hpacket) (f_equal snd Hpacket) Hscope).
Qed.

(** The actual producer's entire indexed execution maintains full nearest, availability and real-use frames. *)
Theorem build_frg_frame_history :
  Pre.laws c ->
  exists data labels, PreFrg.phi_sites c = inr data /\
    let index := PreRename.prepare c data in
    PreFrameStep.history (PreFrameWalk.checked_step c data (g := build_frg))
      (inl (PreRename.initial index)) labels
      (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
        (PreRename.initial index))).
Proof.
  intro Hlaw; destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  set (index := PreRename.prepare c data).
  set (final := PreRename.stop_output (PreRename.run c index)).
  assert (Hstamp : forall e, built_stamp e = PreFrameTables.stamp c e final).
  { intro e; unfold built_stamp, PreFrameTables.stamp.
    rewrite build_frg_equation, Houtput, assemble_equation; reflexivity. }
  assert (Hfinal : final = PreFrameTables.output_of
    (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
      (PreRename.initial index)))).
  { unfold final; rewrite PreRename.run_equation.
    destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
      (PreRename.initial index))); reflexivity. }
  assert (Hhistory : exists labels,
    PreFrameStep.history (PreFrameWalk.checked_step c data (g := build_frg))
      (inl (PreRename.initial index)) labels
      (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
        (PreRename.initial index)))).
  { apply (PreFrameWalk.run_scope_history c data final Hlaw Hdata).
    - intros d Hd; exact (proj2 (proj2 (build_frg_source_versions Hlaw d Hd))).
    - intros e d Hget; destruct (build_frg_occurrence_sources Hlaw e d Hget)
        as [He [u [Hcomputed Hother]]]; split; [exact He|now exists u].
    - intros u Hu Hpure; rewrite (build_frg_versions_exact Hlaw (PreFrg.Initial u)); tauto.
    - intros frames acc b e Hb Hin Hsource Hwf Hbefore Hpacket Hscope.
      apply (built_instruction_scope Hlaw data Hdata frames acc b e
        Hb Hin Hsource Hwf Hbefore); [rewrite Hstamp; exact Hpacket|exact Hscope].
    - exact Hfinal. }
  destruct Hhistory as [labels Hhistory]; exists data, labels; auto.
Qed.

Local Lemma build_output_equation {data} :
  PreFrg.phi_sites c = inr data ->
  forall e, built_stamp e = PreFrameTables.stamp c e
    (PreFrameTables.output_of (Cost.value (iterate (PreRename.step_c c (PreRename.prepare c data))
      (PreRename.walk_budget (PreRename.prepare c data))
      (PreRename.initial (PreRename.prepare c data))))).
Proof.
  intros Houtput e; unfold built_stamp, PreFrameTables.stamp.
  rewrite build_frg_equation, Houtput, assemble_equation, PreRename.run_equation.
  destruct (Cost.value (iterate (PreRename.step_c c (PreRename.prepare c data))
    (PreRename.walk_budget (PreRename.prepare c data))
    (PreRename.initial (PreRename.prepare c data)))); reflexivity.
Qed.

Local Lemma built_block_history :
  Pre.laws c ->
  forall data final, PreFrameCache.placement_laws c data ->
    (forall e, built_stamp e = PreFrameTables.stamp c e final) ->
  forall b first frames acc, In b (Graph.nodes (Pre.bg c)) ->
    nth_error (SsaPoints.points_in_block (Pre.points (Pre.input c)) b) 0 = Some first ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreCoverage.scope_laws c build_frg first frames ->
    PreFrameTables.unwritten c
      (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) acc ->
    (forall e, In e (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) ->
      PreFrameTables.stamp c e final =
        PreFrameTables.stamp c e (snd (PreRename.block c (PreRename.prepare c data) b frames acc))) ->
    let entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c (PreRename.prepare c data) point (frames, acc)
    end in
    PreFrameStep.history (PreFrameWalk.instruction_step c data (g := build_frg) final b)
      entered (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b)
      (fold_left (PreRename.instruction c (PreRename.prepare c data) b
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
        (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered).
Proof.
  intros Hlaw data final Hdata Hstamp.
  apply (PreFrameWalk.block_history c data final Hlaw Hdata).
  intros frames acc b e Hb Hin Hsource Hwf Hbefore Hpacket Hscope.
  apply (built_instruction_scope Hlaw data Hdata frames acc b e
    Hb Hin Hsource Hwf Hbefore); [rewrite Hstamp; exact Hpacket|exact Hscope].
Qed.

(** Every final occurrence is selected from a full source frame in its actual instruction history. *)
Theorem build_frg_occurrence_selection :
  Pre.laws c ->
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    exists frame, PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) frame /\
      (Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg),
        FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg)) =
      (Some (if PreRename.available frame
        then PreFrg.operand_version (PreRename.selected frame) else PreFrg.Fresh e u),
        negb (PreRename.available frame)).
Proof.
  intros Hlaw e u He Hcomputed Hpure.
  destruct (build_frg_frame_history Hlaw) as [data [labels [Houtput Hhistory]]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  pose proof (build_output_equation Houtput) as Hstamp.
  set (final := PreFrameTables.output_of (Cost.value (iterate
    (PreRename.step_c c (PreRename.prepare c data)) (PreRename.walk_budget (PreRename.prepare c data))
    (PreRename.initial (PreRename.prepare c data))))) in *.
  assert (Hwritten : PreFrameTables.stamp c e final <> (None, false)).
  { rewrite <- Hstamp; destruct (build_frg_occurrence_total Hlaw e u He Hcomputed Hpure) as [d Hget].
    unfold built_stamp; rewrite Hget; discriminate. }
  destruct (PreFrameOccurrence.writing_block c data Hlaw Hhistory Hwritten)
    as [b [first [frames [acc [Hb [Hfirst [Hin [Hsource [Hwf [Hscope [Hunwritten Htable]]]]]]]]]]].
  pose proof (built_block_history Hlaw data final Hdata Hstamp b first frames acc
    Hb Hfirst Hsource Hwf Hscope Hunwritten Htable) as Hbody.
  destruct (PreFrameOccurrence.instruction_input c data Hbody Hin)
    as [input [before [Hinput [Hbefore [Hmeaning Hpacket]]]]].
  exists (PreRename.top c input u).
  pose proof (PreFrameOccurrence.packet_selection c Hlaw Hdata He Hcomputed Hpure
    Hinput Hbefore Hmeaning Hpacket) as [Hframe Hselection].
  split; [exact Hframe|]; fold (built_stamp e).
  rewrite Hstamp; exact Hselection.
Qed.

Local Lemma built_observed_availability :
  Pre.laws c ->
  forall u n frame, PreFamily.in_family c u -> Pre.pure c u = true ->
    PreCoverage.observed c n -> PreCoverage.frame_laws c build_frg u n frame ->
    (PreRename.available frame = true <-> exists d, PreRename.reusable c build_frg u n d) /\
    (PreRename.available frame = true ->
      PreRename.reusable c build_frg u n (PreFrg.operand_version (PreRename.selected frame))).
Proof.
  intros Hlaw u n frame Hfamily Hpure Hobserved Hframe.
  apply (PreCoverage.frame_availability c Hlaw build_frg u n frame Hfamily Hobserved).
  - intros b Hphi; apply (proj2 (build_frg_versions_exact Hlaw (PreFrg.Phi b u))).
    apply (proj2 (build_frg_phi_exact Hlaw b u)); auto.
  - exact Hframe.
Qed.

Local Lemma built_occurrence_availability {e u frame} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  Pre.recomputed c e = Some u -> Pre.pure c u = true ->
  PreCoverage.frame_laws c build_frg u (Graph.source (Pre.pg c) e) frame ->
    (PreRename.available frame = true <->
      exists d, PreRename.reusable c build_frg u (Graph.source (Pre.pg c) e) d) /\
    (PreRename.available frame = true ->
      PreRename.reusable c build_frg u (Graph.source (Pre.pg c) e)
        (PreFrg.operand_version (PreRename.selected frame))).
Proof.
  intros Hlaw He Hcomputed Hpure Hframe; apply (built_observed_availability Hlaw).
  - apply Pre.family_seed; exact (Pre.occurrences_seeded c (Pre.shapes c Hlaw) e u Hcomputed).
  - exact Hpure.
  - left; exists e, u; auto.
  - exact Hframe.
Qed.

(** Each eligible occurrence selects its own fresh definition or a reusable nearest definition. *)
Theorem build_frg_occurrence_exact :
  Pre.laws c ->
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    exists d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some d /\
      In d (PreFrg.versions build_frg) /\ PreFrg.version_expr d = u /\
      (d = PreFrg.Fresh e u \/
        PreRename.reusable c build_frg u (Graph.source (Pre.pg c) e) d).
Proof.
  intros Hlaw e u He Hcomputed Hpure.
  destruct (build_frg_occurrence_selection Hlaw e u He Hcomputed Hpure)
    as [frame [Hframe Hstamp]].
  pose proof (f_equal fst Hstamp) as Hget; cbn [fst] in Hget.
  pose proof (built_occurrence_availability Hlaw He Hcomputed Hpure Hframe) as [Havailable Hreuse].
  destruct (PreRename.available frame) eqn:Hflag.
  - exists (PreFrg.operand_version (PreRename.selected frame)).
    split; [exact Hget|]; split; [exact (build_frg_occurrence_member Hlaw _ _ Hget)|].
    split; [exact (proj1 Hframe)|right; exact (Hreuse eq_refl)].
  - exists (PreFrg.Fresh e u); split; [exact Hget|].
    split; [exact (build_frg_occurrence_member Hlaw _ _ Hget)|]; split; [reflexivity|now left].
Qed.

(** Fresh flags mark precisely the eligible occurrences with no reusable incoming definition. *)
Theorem build_frg_fresh_required :
  Pre.laws c ->
  forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true <->
      ~ exists d, PreRename.reusable c build_frg u (Graph.source (Pre.pg c) e) d).
Proof.
  intros Hlaw e u He Hcomputed Hpure.
  destruct (build_frg_occurrence_selection Hlaw e u He Hcomputed Hpure)
    as [frame [Hframe Hstamp]].
  pose proof (f_equal snd Hstamp) as Hflag; cbn [snd] in Hflag.
  pose proof (proj1 (built_occurrence_availability Hlaw He Hcomputed Hpure Hframe)) as Havail.
  rewrite Hflag; destruct (PreRename.available frame); cbn [negb] in *; split.
  - discriminate.
  - intro Hnone; exfalso; apply Hnone; apply Havail; reflexivity.
  - intros _ Hexists; apply Havail in Hexists; discriminate.
  - intros _; reflexivity.
Qed.

Local Lemma built_fresh_source {e} :
  Pre.laws c -> FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true ->
    In e (Cfg.edges (Pre.point_cfg c)) /\
      exists u, Pre.recomputed c e = Some u /\ Pre.pure c u = true.
Proof.
  intros Hlaw Hfresh.
  destruct (PreFrg.phi_sites_exact c Hlaw) as [data [Houtput Hrest]].
  pose proof (PreFrameCache.placement_from_output c Hlaw data Houtput) as Hdata.
  rewrite build_frg_equation, Houtput, assemble_equation in Hfresh.
  apply (proj2 (PreFrameEnd.run_fresh_ledger c Hlaw (PreRename.prepare c data)) e) in Hfresh.
  destruct Hfresh as [u Hcreated].
  destruct (PreFrameInvariant.source_created c _
    (PreFrameInvariant.run_output_source c data Hlaw Hdata) _ Hcreated)
    as [[Hfamily [Hpure [He Hcomputed]]] Horigin].
  split; [exact He|]; exists u; auto.
Qed.

(** Every fresh flag belongs to an original finite point-edge occurrence. *)
Theorem build_frg_fresh_domain :
  Pre.laws c ->
  forall e, FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true ->
    In e (Cfg.edges (Pre.point_cfg c)).
Proof.
  intros Hlaw e Hfresh; exact (proj1 (built_fresh_source Hlaw Hfresh)).
Qed.

Local Lemma built_fresh_selection {e u} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true <->
      Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some (PreFrg.Fresh e u)).
Proof.
  intros Hlaw He Hcomputed Hpure.
  destruct (build_frg_occurrence_selection Hlaw e u He Hcomputed Hpure)
    as [frame [Hframe Hstamp]].
  pose proof (f_equal fst Hstamp) as Hget; cbn [fst] in Hget.
  pose proof (f_equal snd Hstamp) as Hflag; cbn [snd] in Hflag.
  pose proof (proj2 (built_occurrence_availability Hlaw He Hcomputed Hpure Hframe)) as Hreuse.
  rewrite Hflag, Hget; destruct (PreRename.available frame); cbn [negb]; split.
  - discriminate.
  - intro Heq; inversion Heq as [Hsame].
    exfalso; apply (PreFrameOccurrence.current_not_reusable c (g := build_frg) Hlaw He Hcomputed).
    rewrite <- Hsame; exact (Hreuse eq_refl).
  - intros _; reflexivity.
  - intros _; reflexivity.
Qed.

(** For every recomputation, its fresh flag agrees with selection of its own fresh version. *)
Theorem build_frg_fresh_exact :
  Pre.laws c ->
  forall e u, Pre.recomputed c e = Some u ->
    (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh build_frg) = true <->
      Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences build_frg) = Some (PreFrg.Fresh e u)).
Proof.
  intros Hlaw e u Hcomputed; split.
  - intro Hflag; destruct (built_fresh_source Hlaw Hflag) as [He [v [Hv Hpure]]].
    assert (Hsame : v = u) by congruence; subst v.
    exact (proj1 (built_fresh_selection Hlaw He Hcomputed Hpure) Hflag).
  - intro Hget.
    destruct (build_frg_occurrence_sources Hlaw e _ Hget) as [He [v [Hv [Hpure [Hexpr Hrest]]]]].
    cbn [PreFrg.version_expr] in Hexpr; subst v.
    exact (proj2 (built_fresh_selection Hlaw He Hcomputed Hpure) Hget).
Qed.

(** The caller gate checks the supplied block-parent map and rejects every partial raw outcome.
    It does not certify arbitrary supplied numbering, expression laws or concrete semantics. *)
Definition build_frg_checked_c :=
  let* accepted := DomCheckCost.check_c (Pre.blocks c) (Dom.idom (Pre.dom c)) in
  if accepted then
    let* graph := build_frg_c in
    Cost.ret (match PreFrg.status graph with
      | PreFrg.Completed => Some graph
      | _ => None
      end)
  else Cost.ret None.
Definition build_frg_checked := Cost.value build_frg_checked_c.

(** Checked observations use the owning checker contract
    and delegate once to the same raw builder. *)
Theorem build_frg_checked_equation :
  build_frg_checked =
    if DomCheck.check (Pre.blocks c) (Dom.idom (Pre.dom c)) then
      match PreFrg.status build_frg with
      | PreFrg.Completed => Some build_frg
      | _ => None
      end
    else None.
Proof.
  unfold build_frg_checked, build_frg_checked_c.
  rewrite Cost.value_bind, DomCheckCost.check_c_value.
  destruct (DomCheck.check (Pre.blocks c) (Dom.idom (Pre.dom c)));
    rewrite ?Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

(** The checked gate retains all actual checker work
    and charges raw construction exactly when reached. *)
Theorem build_frg_checked_cost :
  Cost.ticks build_frg_checked_c =
    (Cost.ticks (DomCheckCost.check_c (Pre.blocks c) (Dom.idom (Pre.dom c))) +
      if DomCheck.check (Pre.blocks c) (Dom.idom (Pre.dom c))
      then Cost.ticks build_frg_c else 0)%N.
Proof.
  unfold build_frg_checked_c; rewrite Cost.ticks_bind, DomCheckCost.check_c_value.
  destruct (DomCheck.check (Pre.blocks c) (Dom.idom (Pre.dom c)));
    rewrite ?Cost.ticks_bind, !Cost.ticks_ret; lia.
Qed.

(** Lawful contexts pass the real checker and return exactly the completed raw graph. *)
Theorem build_frg_checked_agrees :
  Pre.laws c -> build_frg_checked = Some build_frg.
Proof.
  intro Hlaw; rewrite build_frg_checked_equation.
  assert (Hcheck : DomCheck.check (Pre.blocks c) (Dom.idom (Pre.dom c)) = true).
  { apply DomCheck.check_complete; [exact (Pre.blocks_ready c (Pre.graphs c Hlaw))|].
    exists (Pre.dom c); split; [exact (Pre.tree_exact c (Pre.graphs c Hlaw))|reflexivity]. }
  rewrite Hcheck, (build_frg_completed Hlaw); reflexivity.
Qed.

(** Canonical output indexes enumerate distinct keys even for malformed or exhausted raw inputs. *)
Theorem build_frg_index_keys_nodup :
  NoDup (map fst (Map.elements (PreFrg.occurrences build_frg))) /\
  NoDup (FinSet.elements (PreFrg.fresh build_frg)) /\
  NoDup (FinSet.elements (PreFrg.phis build_frg)) /\
  NoDup (map fst (Map.elements (PreFrg.operands build_frg))) /\
  NoDup (FinSet.elements (PreFrg.unsafe build_frg)).
Proof.
  destruct build_frg_indexes_wf as [Hocc [Hfresh [Hphi [Hlinks Hunsafe]]]].
  repeat split.
  - exact (Map.elements_nodup _ _ Hocc).
  - exact (FinSet.elements_nodup _ _ Hfresh).
  - exact (FinSet.elements_nodup _ _ Hphi).
  - exact (Map.elements_nodup _ _ Hlinks).
  - exact (FinSet.elements_nodup _ _ Hunsafe).
Qed.

End Build.

End PreOperands.
