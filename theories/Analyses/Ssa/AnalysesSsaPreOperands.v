(** * Materialized factored redundancy graphs and explicit construction outcomes

    The raw builder preserves discovery exhaustion, rename exhaustion and missing block names.
    For example, a completed diamond retains separate operands for its two incoming join edges.
    Builds on: AnalysesSsaPreFrg, AnalysesSsaPreRename and the shared costed list operations. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphDomSpec GraphCheckDom GraphCheckDomCost.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep
  AnalysesSsaPreFrameEnd.
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
