(** * Phi resolution adequacy

    Counted resolution follows the fixed relational steps and threads every persistent map.
    For example, a conflicting operand retains the map after evaluating all later operands.
    Builds on: AnalysesAuditMemoryPhiResolve, its plain computation, and collection adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiPlain AnalysesAuditMemoryPhiResolve.
Import List.ListNotations.

(** * Erasure of individual operations *)

Lemma audit_phi_rep_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (enc : memory_version N E -> positive * list CV) reps v :
  (forall x, fst (enc x) = encode (memory_version_encoding EN EE) x) ->
  fst (@audit_phi_rep N E CN CV enc reps v) = phi_rep_from_map EN EE reps v.
Proof.
  intro Henc.
  unfold audit_phi_rep, phi_rep_from_map.
  pose proof (audit_map_get_erases _ _ CV enc (memory_version_encoding EN EE) v reps (Henc v))
    as Hget.
  destruct (audit_map_get enc v reps) as [found calls]; cbn in Hget |- *.
  now rewrite Hget.
Qed.

Lemma audit_phi_compare_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (enc : memory_version N E -> positive * list CV) left right :
  (forall x, fst (enc x) = encode (memory_version_encoding EN EE) x) ->
  fst (@audit_phi_compare N E CN CV enc left right) =
    Pos.eqb (encode (memory_version_encoding EN EE) left)
      (encode (memory_version_encoding EN EE) right).
Proof.
  intro Henc.
  unfold audit_phi_compare.
  specialize (Henc left) as Hleft; specialize (Henc right) as Hright.
  destruct (enc left) as [lc le]; destruct (enc right) as [rc re].
  pose proof (audit_positive_eqb_erases lc rc) as Heq.
  destruct (audit_positive_eqb lc rc) as [same calls]; cbn in *.
  now rewrite Heq, Hleft, Hright.
Qed.

Lemma audit_phi_all_same_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (enc : memory_version N E -> positive * list CV) reps candidate row :
  (forall x, fst (enc x) = encode (memory_version_encoding EN EE) x) ->
  fst (@audit_phi_all_same N E CN CV enc reps candidate row) =
    forallb (phi_same_rep EN EE reps candidate) row.
Proof.
  intro Henc.
  induction row as [|[key v] rest IH].
  - reflexivity.
  - cbn [audit_phi_all_same forallb].
    pose proof (audit_phi_rep_erases N E CN CV EN EE enc reps v Henc) as Hrep.
    destruct (@audit_phi_rep N E CN CV enc reps v) as [representative re].
    pose proof (audit_phi_compare_erases N E CN CV EN EE enc candidate representative Henc)
      as Hcompare.
    destruct (@audit_phi_compare N E CN CV enc candidate representative) as [same ce].
    destruct (@audit_phi_all_same N E CN CV enc reps candidate rest) as [later te].
    cbn in Hrep, Hcompare, IH |- *.
    unfold phi_same_rep; cbn [snd].
    now rewrite Hcompare, Hrep, IH.
Qed.

Lemma audit_phi_resolve_step_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) index reps n :
  (forall x, fst (node_enc x) = encode EN x) ->
  (forall x, fst (version_enc x) = encode (memory_version_encoding EN EE) x) ->
  fst (audit_phi_resolve_step EN node_enc version_enc index reps n) =
    audit_phi_compute_step EN EE index reps n.
Proof.
  intros Hnode Hversion.
  unfold audit_phi_resolve_step, audit_phi_compute_step.
  pose proof (audit_finset_mem_erases N CN node_enc EN n (phi_index_cycles index) (Hnode n))
    as Hcycle.
  destruct (audit_finset_mem node_enc n (phi_index_cycles index)) as [cyclic ce].
  cbn in Hcycle; rewrite <- Hcycle.
  destruct cyclic; [reflexivity|].
  pose proof (audit_map_get_erases N _ CN node_enc EN n (phi_index_inputs index) (Hnode n))
    as Hrow.
  destruct (audit_map_get node_enc n (phi_index_inputs index)) as [row ie].
  cbn in Hrow; rewrite <- Hrow.
  destruct row as [[|[key v] rest]|]; try reflexivity.
  pose proof (audit_phi_rep_erases N E CN CV EN EE version_enc reps v Hversion) as Hrep.
  destruct (@audit_phi_rep N E CN CV version_enc reps v) as [candidate re].
  pose proof (audit_phi_compare_erases N E CN CV EN EE version_enc candidate (MemoryPhi n)
    Hversion) as Hself.
  destruct (@audit_phi_compare N E CN CV version_enc candidate (MemoryPhi n)) as [self se].
  pose proof (audit_phi_all_same_erases N E CN CV EN EE version_enc reps candidate rest Hversion)
    as Hsame.
  destruct (@audit_phi_all_same N E CN CV version_enc reps candidate rest) as [same ae].
  cbn [fst snd] in Hrep, Hself, Hsame |- *.
  change (candidate = audit_phi_compute_rep EN EE reps v) in Hrep.
  change (same = forallb (fun kv =>
    Pos.eqb (encode (memory_version_encoding EN EE) candidate)
      (encode (memory_version_encoding EN EE) (audit_phi_compute_rep EN EE reps (snd kv))))
    rest) in Hsame.
  rewrite <- Hrep, <- Hself, <- Hsame.
  destruct (andb (negb self) same); [|reflexivity].
  pose proof (audit_map_set_erases _ _ CV version_enc (memory_version_encoding EN EE)
    (MemoryPhi n) candidate reps (Hversion (MemoryPhi n))) as Hset.
  destruct (audit_map_set version_enc (MemoryPhi n) candidate reps); exact Hset.
Qed.

(** * The relational step and its concrete successor *)

Lemma audit_phi_compute_step_refines N E (EN : encoding N) (EE : encoding E)
    index reps n :
  phi_resolve_step EN EE index reps n (audit_phi_compute_step EN EE index reps n).
Proof.
  unfold audit_phi_compute_step.
  destruct (FinSet.mem EN n (phi_index_cycles index)) eqn:Hcycle.
  - apply PhiResolveCyclic; exact Hcycle.
  - destruct (Map.get EN n (phi_index_inputs index)) as [row|] eqn:Hget.
    + destruct row as [|[key v] rest].
      * apply PhiResolveEmpty; [exact Hcycle|].
        unfold index_edges; now rewrite Hget.
      * set (candidate := audit_phi_compute_rep EN EE reps v).
        destruct (Pos.eqb (encode (memory_version_encoding EN EE) candidate)
          (encode (memory_version_encoding EN EE) (MemoryPhi n))) eqn:Hself.
        -- cbn [negb andb].
           eapply PhiResolveKeep with (key := key) (input := v) (rest := rest).
           ++ exact Hcycle.
           ++ unfold index_edges; now rewrite Hget.
           ++ reflexivity.
           ++ left; exact Hself.
        -- destruct (forallb (fun kv => Pos.eqb (encode (memory_version_encoding EN EE)
             candidate) (encode (memory_version_encoding EN EE)
               (audit_phi_compute_rep EN EE reps (snd kv)))) rest) eqn:Hsame.
           ++ cbn [negb andb].
              eapply PhiResolveEqual with (key := key) (input := v) (rest := rest).
              ** exact Hcycle.
              ** unfold index_edges; now rewrite Hget.
              ** reflexivity.
              ** exact Hself.
              ** exact Hsame.
           ++ cbn [negb andb].
              eapply PhiResolveKeep with (key := key) (input := v) (rest := rest).
              ** exact Hcycle.
              ** unfold index_edges; now rewrite Hget.
              ** reflexivity.
              ** right; exact Hsame.
    + apply PhiResolveEmpty; [exact Hcycle|].
      unfold index_edges; now rewrite Hget.
Qed.

(** Matching encoders make the actual counted successor a valid relational step. *)
Theorem audit_phi_resolve_step_refines : audit_phi_resolve_step_refines_statement.
Proof.
  intros N E CN CV EN EE index node_enc version_enc reps n Hnode Hversion.
  rewrite (audit_phi_resolve_step_erases N E CN CV EN EE node_enc version_enc index reps n
    Hnode Hversion).
  apply audit_phi_compute_step_refines.
Qed.

(** * Trace lengths and source frames *)

Lemma audit_phi_resolve_all_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) index nodes :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
  forall reps, fst (audit_phi_resolve_all EN node_enc version_enc index nodes reps) =
    fold_left (audit_phi_compute_step EN EE index) nodes reps.
Proof.
  intros Hnode Hversion.
  induction nodes as [|n rest IH]; intro reps.
  - reflexivity.
  - cbn [audit_phi_resolve_all fold_left].
    pose proof (audit_phi_resolve_step_erases N E CN CV EN EE node_enc version_enc index reps n
      Hnode Hversion) as Hstep.
    destruct (audit_phi_resolve_step EN node_enc version_enc index reps n) as [next events].
    specialize (IH next).
    destruct (audit_phi_resolve_all EN node_enc version_enc index rest next).
    cbn [fst] in IH, Hstep |- *.
    now rewrite IH, Hstep.
Qed.

Lemma audit_phi_rep_count N E CN CV (enc : memory_version N E -> positive * list CV) reps v :
  length (snd (@audit_phi_rep N E CN CV enc reps v)) = 1.
Proof.
  unfold audit_phi_rep.
  destruct (audit_map_get enc v reps); reflexivity.
Qed.

Lemma audit_phi_compare_count N E CN CV (enc : memory_version N E -> positive * list CV) a b :
  length (snd (@audit_phi_compare N E CN CV enc a b)) = 3.
Proof.
  unfold audit_phi_compare.
  destruct (enc a) as [left_code left_body], (enc b) as [right_code right_body].
  destruct (audit_positive_eqb left_code right_code); reflexivity.
Qed.

Lemma audit_phi_all_same_count N E CN CV (enc : memory_version N E -> positive * list CV)
    reps candidate row :
  length (snd (@audit_phi_all_same N E CN CV enc reps candidate row)) = 1 + 5 * length row.
Proof.
  induction row as [|[key v] rest IH].
  - reflexivity.
  - cbn [audit_phi_all_same].
    pose proof (audit_phi_rep_count N E CN CV enc reps v) as Hrep.
    destruct (@audit_phi_rep N E CN CV enc reps v) as [representative re].
    pose proof (audit_phi_compare_count N E CN CV enc candidate representative) as Hcompare.
    destruct (@audit_phi_compare N E CN CV enc candidate representative) as [same ce].
    destruct (@audit_phi_all_same N E CN CV enc reps candidate rest) as [later te].
    cbn in Hrep, Hcompare, IH |- *.
    rewrite !length_app; lia.
Qed.

Lemma audit_phi_resolve_step_count N E CN CV (EN : encoding N)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) index reps n :
  length (snd (audit_phi_resolve_step EN node_enc version_enc index reps n)) <=
    8 + 5 * length (
      match fst (audit_map_get node_enc n (phi_index_inputs index)) with
      | None =>
        []
      | Some row =>
        row
      end).
Proof.
  unfold audit_phi_resolve_step.
  destruct (audit_finset_mem node_enc n (phi_index_cycles index)) as [cyclic ce].
  destruct cyclic; [cbn; lia|].
  destruct (audit_map_get node_enc n (phi_index_inputs index)) as [row ie].
  destruct row as [[|[key v] rest]|]; try (cbn; lia).
  pose proof (audit_phi_rep_count N E CN CV version_enc reps v) as Hrep.
  destruct (@audit_phi_rep N E CN CV version_enc reps v) as [candidate re].
  pose proof (audit_phi_compare_count N E CN CV version_enc candidate (MemoryPhi n)) as Hcompare.
  destruct (@audit_phi_compare N E CN CV version_enc candidate (MemoryPhi n)) as [self se].
  pose proof (audit_phi_all_same_count N E CN CV version_enc reps candidate rest) as Hsame.
  destruct (@audit_phi_all_same N E CN CV version_enc reps candidate rest) as [same ae].
  cbn in Hrep, Hcompare, Hsame |- *.
  destruct (andb (negb self) same).
  - destruct (audit_map_set version_enc (MemoryPhi n) candidate reps).
    cbn; rewrite !length_app; cbn; lia.
  - cbn; rewrite !length_app; cbn; lia.
Qed.

(** One step's outer work is bounded by the actual stored row, retaining primitive work. *)
Theorem audit_phi_resolve_source_bound : audit_phi_resolve_source_bound_statement.
Proof.
  intros N E CN CV EN node_enc version_enc index reps n node_work version_work.
  pose proof (audit_phi_resolve_step_count N E CN CV EN node_enc version_enc index reps n)
    as Hcount.
  unfold audit_phi_resolve_source_work.
  lia.
Qed.

Lemma audit_phi_resolve_primitive_work_app N E CN CV node_work version_work
    (left right : list (audit_phi_resolve_event N E CN CV)) :
  audit_phi_resolve_primitive_work node_work version_work (left ++ right) =
    audit_phi_resolve_primitive_work node_work version_work left +
      audit_phi_resolve_primitive_work node_work version_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn [app audit_phi_resolve_primitive_work]; rewrite IH; lia.
Qed.

Lemma audit_phi_resolve_source_work_app N E CN CV node_work version_work
    (left right : list (audit_phi_resolve_event N E CN CV)) :
  audit_phi_resolve_source_work node_work version_work (left ++ right) =
    audit_phi_resolve_source_work node_work version_work left +
      audit_phi_resolve_source_work node_work version_work right.
Proof.
  unfold audit_phi_resolve_source_work.
  rewrite length_app, audit_phi_resolve_primitive_work_app.
  lia.
Qed.

(** The complete counted pass threads the same actual maps as the relational trace. *)
Theorem audit_phi_resolve_all_refines : audit_phi_resolve_all_refines_statement.
Proof.
  intros N E CN CV EN EE index node_enc version_enc nodes reps Hnode Hversion.
  revert reps.
  induction nodes as [|n rest IH]; intro reps.
  - constructor.
  - cbn [audit_phi_resolve_all].
    pose proof (audit_phi_resolve_step_refines N E CN CV EN EE index node_enc version_enc reps n
      Hnode Hversion) as Hstep.
    destruct (audit_phi_resolve_step EN node_enc version_enc index reps n) as [next first].
    specialize (IH next).
    destruct (audit_phi_resolve_all EN node_enc version_enc index rest next) as [final tail].
    cbn in Hstep, IH |- *.
    econstructor; eassumption.
Qed.

(** Source work adds across the actual intermediate states of the complete pass. *)
Theorem audit_phi_resolve_all_source_bound : audit_phi_resolve_all_source_bound_statement.
Proof.
  intros N E CN CV EN node_enc version_enc index nodes reps node_work version_work.
  revert reps.
  induction nodes as [|n rest IH]; intro reps.
  - reflexivity.
  - cbn [audit_phi_resolve_all audit_phi_resolve_all_budget].
    pose proof (audit_phi_resolve_source_bound N E CN CV EN node_enc version_enc index reps n
      node_work version_work) as Hstep.
    destruct (audit_phi_resolve_step EN node_enc version_enc index reps n) as [next first].
    specialize (IH next).
    destruct (audit_phi_resolve_all EN node_enc version_enc index rest next) as [final tail].
    cbn [fst snd] in Hstep, IH |- *.
    rewrite audit_phi_resolve_source_work_app.
    lia.
Qed.
