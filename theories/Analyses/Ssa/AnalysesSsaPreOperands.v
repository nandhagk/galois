(** * Materialized factored redundancy graphs and explicit construction outcomes

    The raw builder preserves discovery exhaustion, rename exhaustion and missing block names.
    For example, a completed diamond retains separate operands for its two incoming join edges.
    Builds on: AnalysesSsaPreFrg, AnalysesSsaPreRename and the shared costed list operations. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom GraphCheckDomCost.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep
  AnalysesSsaPreFrameEnd AnalysesSsaPreFrameCache AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameVisit
  AnalysesSsaPreFrameOrigins AnalysesSsaPreFrameMeaning AnalysesSsaPreFrameDominance AnalysesSsaPreFrameTables.
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
