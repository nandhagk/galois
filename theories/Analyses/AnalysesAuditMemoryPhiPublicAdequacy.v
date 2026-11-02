(** * Public phi pruning guarantees

    The fixed produced graph satisfies every public semantic and well-formedness contract.
    For example, graph-only packaging projects the same proved representative-bearing result.
    Builds on: AnalysesAuditMemoryPhiPublic and the producer's semantic invariants. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphScc.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiPlain AnalysesAuditMemoryPhiPublic
  AnalysesAuditMemoryPhiProducerAdequacy AnalysesAuditMemoryPhiResolveAdequacy
  AnalysesAuditMemoryPhiStateAdequacy AnalysesAuditMemoryPhiConsumerAdequacy.
Import List.ListNotations.

(** Given the helper's correctness argument, packaging preserves both exact data projections. *)
Theorem audit_memory_phi_public_projection : audit_memory_phi_public_projection_statement.
Proof.
  intros correct N E T EN EE g effects mg wf.
  split; reflexivity.
Qed.

(** The fixed pruning result satisfies every memory graph law under the original input premise. *)
Theorem audit_memory_phi_prune_wf : audit_memory_phi_prune_wf_statement.
Proof.
  intros N E T EN EE g effects old Hwf.
  apply phi_compute_wf; exact Hwf.
Qed.

Lemma phi_compute_unlisted N E T (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (Hwf : memory_graph_wf g effects old) n :
  ~ In n (memory_phis old) ->
  phi_rep EN EE (AnalysesAuditMemoryPhiConsumer.audit_memory_phi_prune N E T EN EE g effects old)
    (MemoryPhi n) = MemoryPhi n.
Proof.
  intro Hnot.
  apply (proj2 (phi_compute_rep_identity EN EE g effects old Hwf (MemoryPhi n))).
  apply (phi_resolution_unprocessed N E T EN EE g effects old
    (phi_prepare_dependencies EN EE g effects old)
    (rev (concat (components (phi_index_scc (phi_prepare_dependencies EN EE g effects old)))))
    _ n); [apply phi_compute_resolution_invariant; exact Hwf|].
  intro Hin; apply Hnot.
  apply (proj1 (phi_compute_order_member EN EE g effects old Hwf n)); exact Hin.
Qed.

Lemma phi_compute_inventory N E (EN : encoding N) (EE : encoding E) old reps :
  let output := audit_phi_compute_output EN EE old reps in
  let kept := FinSet.of_list EN (memory_phis output) in
  memory_phis output = filter (fun n => FinSet.mem EN n kept) (memory_phis old) /\
  memory_versions output = filter (fun v =>
    match v with
    | MemoryPhi n => FinSet.mem EN n kept
    | _ => true
    end) (memory_versions old).
Proof.
  unfold audit_phi_compute_output; cbn [memory_phis memory_versions].
  split; apply filter_ext.
  - intro n; symmetry; apply audit_phi_kept_set_stable.
  - intros [|n|e i]; try reflexivity.
    symmetry; apply audit_phi_kept_set_stable.
Qed.

Lemma phi_compute_public_map_domain N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (ViewsMemoryEffects.memory_effect T)) old
    (Hwf : memory_graph_wf g effects old) v w :
  let result := AnalysesAuditMemoryPhiConsumer.audit_memory_phi_prune N E T EN EE g effects old in
  Map.get (memory_version_encoding EN EE) v (phi_representatives result) = Some w <->
  exists n, v = MemoryPhi n /\ In n (memory_phis old) /\
    ~ In n (memory_phis (phi_graph result)) /\ w = phi_rep EN EE result v.
Proof.
  intro result; split.
  - intro Hget.
    destruct (phi_resolution_domain EN EE g effects old _ _ _
      (phi_compute_resolution_invariant N E T EN EE g effects old Hwf) v w Hget)
      as [n [Hv [Hn Hrest]]].
    exists n; split; [exact Hv|split].
    + apply (proj1 (phi_compute_order_member EN EE g effects old Hwf n)); exact Hn.
    + split.
      * intro Hkept.
        pose proof (proj2 (proj1 (phi_compute_kept EN EE g effects old n) Hkept)) as Heq.
        apply (proj1 (phi_compute_rep_identity EN EE g effects old Hwf (MemoryPhi n))) in Heq.
        change (Map.get (memory_version_encoding EN EE) (MemoryPhi n)
          (phi_representatives result) = None) in Heq.
        rewrite Hv in Hget; congruence.
      * unfold phi_rep; now rewrite Hget.
  - intros [n [Hv [Hn [Hremoved Hw]]]]; subst v.
    destruct (phi_compute_removed EN EE g effects old Hwf n Hn Hremoved)
      as [image [Hget [Hrep Hrow]]].
    change (w = phi_rep_from_map EN EE (phi_representatives result) (MemoryPhi n)) in Hw.
    change (phi_rep_from_map EN EE (phi_representatives result) (MemoryPhi n) = image) in Hrep.
    rewrite Hrep in Hw; subst w; exact Hget.
Qed.

Lemma phi_compute_resolution_trace N E (EN : encoding N) (EE : encoding E) index nodes reps :
  phi_resolve_trace EN EE index nodes reps
    (fold_left (audit_phi_compute_step EN EE index) nodes reps).
Proof.
  revert reps; induction nodes as [|n rest IH]; intro reps.
  - constructor.
  - cbn [fold_left]; eapply PhiResolveTraceCons.
    + apply audit_phi_compute_step_refines.
    + apply IH.
Qed.

(** Packaging exposes all original semantic, map, shape and resolution contracts together. *)
Theorem audit_memory_phi_public_semantics : audit_memory_phi_public_semantics_statement.
Proof.
  split; [exact audit_memory_phi_prune_wf|].
  intro correct.
  destruct audit_memory_phi_prune_semantics as
    [Hprojection [Hterminal [Hself [Hcycles [Hlegacy Hbytes]]]]].
  split; [exact Hprojection|].
  split; [exact Hterminal|].
  split; [exact Hcycles|].
  split.
  - intros N E T EN EE g effects wf; split; apply Hprojection; apply proj2_sig.
  - split.
    { intros F N E T EN EE EF ET f g effects writes reads old wf loads fuel.
      exact (Hlegacy F N E T EN EE EF ET f g effects writes reads old loads fuel wf). }
    split; [intros S O N E T F L m bv EN EE EF ET f effects reads old wf loads fuel Hlaws;
      exact (Hbytes S O N E T F L m bv EN EE EF ET f effects reads old loads fuel Hlaws wf)|].
    split.
    + intros N E T EN EE g effects old wf n; cbn zeta; intros Hn Hremoved.
      destruct (phi_compute_removed EN EE g effects old wf n Hn Hremoved)
        as [w [_ [Hrep [key [first [Hop Hall]]]]]].
      exists key, first; split; [exact Hop|].
      set (reps := phi_representatives
        (AnalysesAuditMemoryPhiConsumer.audit_memory_phi_prune N E T EN EE g effects old)).
      change (phi_rep_from_map EN EE reps first = phi_rep_from_map EN EE reps (MemoryPhi n)).
      change (phi_rep_from_map EN EE reps (MemoryPhi n) = w) in Hrep.
      rewrite Hrep; exact (Hall key first Hop).
    + split.
      * intros N E T EN EE g effects old wf n; cbn zeta.
        intros Hn Hacyclic [key [first [Hop [Hne Hall]]]].
        apply (phi_compute_resolved_removed EN EE g effects old wf n Hn Hacyclic).
        exists key, first; auto.
      * split.
        -- intros N E T EN EE g effects old wf.
           split.
           { intros n Hnot; apply (phi_compute_unlisted N E T EN EE g effects old wf n Hnot). }
           apply phi_compute_inventory.
        -- split.
           ++ intros N E T EN EE g effects old wf v w.
              apply (phi_compute_public_map_domain N E T EN EE g effects old wf v w).
           ++ split.
              ** intros N E T EN EE g effects old wf; apply phi_compute_resolution_trace.
              ** split.
                 --- intros N E T EN EE g effects old wf; apply proj2_sig.
                 --- intros N E T EN EE g effects old wf; reflexivity.
Qed.
