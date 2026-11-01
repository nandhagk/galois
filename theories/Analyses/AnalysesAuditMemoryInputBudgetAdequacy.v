(** * Adequacy of memory input budgets

    These bounds account for concrete encoder and raw-successor operations at their actual inputs.
    For example, a definition successor charges the indexed lookup and its before callback.
    Builds on: AnalysesAuditMemoryInputBudget and concrete collection adequacy proofs. *)

From Stdlib Require Import List PArith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditEncoding
  CollectionsAuditEncoderBudget CollectionsAuditEncoderBudgetAdequacy CollectionsMap
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryEffects AnalysesAuditMemoryDisjoint
  AnalysesAuditMemoryDisjointAdequacy AnalysesAuditMemoryRawNext.
Import List.ListNotations.

(** A version charges only its selected node or edge encoding. *)
Lemma audit_memory_version_input_bound N E CN CE (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) node_work edge_work node_budget edge_budget v :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  audit_memory_version_work node_work edge_work
    (snd (audit_memory_version_encode node_enc edge_enc v)) <=
    audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget v.
Proof.
  intros Hnode Hedge.
  destruct audit_base_encoder_input_bound as [_ [_ [_ [_ [Hnat _]]]]].
  destruct v as [|node|edge index].
  - reflexivity.
  - cbn [audit_memory_version_encode audit_memory_version_input_budget].
    specialize (Hnode node); destruct (node_enc node); simpl in *; lia.
  - cbn [audit_memory_version_encode audit_memory_version_input_budget].
    pose proof (audit_pair_input_bound E nat CE _ edge_enc audit_nat_encode edge_work
      audit_nat_events_work edge_budget audit_nat_input_budget (edge, index) Hedge Hnat) as Hpair.
    destruct (audit_pair_encode edge_enc audit_nat_encode (edge, index)); simpl in *; lia.
Qed.

(** A footprint budget composes the site and two signed endpoint encoders. *)
Lemma audit_memory_footprint_input_bound T CE (site_enc : T -> positive * list CE)
    site_work site_budget fp :
  (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
  audit_memory_footprint_work site_work (snd (audit_memory_footprint_encode site_enc fp)) <=
    audit_memory_footprint_input_budget site_enc site_budget fp.
Proof.
  intro Hsite.
  destruct audit_base_encoder_input_bound as [_ [_ [_ [Hz _]]]].
  unfold audit_memory_footprint_work, audit_memory_footprint_encode,
    audit_memory_footprint_input_budget.
  apply audit_pair_input_bound; [exact Hsite|].
  intro endpoints; apply audit_pair_input_bound; exact Hz.
Qed.

(** A scope pays for the selected sum branch and all actual footprint occurrences. *)
Lemma audit_memory_scope_input_bound T CE (site_enc : T -> positive * list CE)
    site_work site_budget q :
  (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
  audit_memory_scope_work site_work (snd (audit_memory_scope_encode site_enc q)) <=
    audit_memory_scope_input_budget site_enc site_budget q.
Proof.
  intro Hsite.
  destruct audit_base_encoder_input_bound as [_ [_ [Hunit _]]].
  destruct audit_sum_option_input_bound as [_ Hsum].
  pose proof (Hsum unit (list (footprint T)) _ _ audit_unit_encode
    (audit_list_encode (audit_memory_footprint_encode site_enc)) audit_basic_encoding_work
    (audit_list_events_work (audit_memory_footprint_work site_work)) (fun _ => 1)
    (audit_list_input_budget (audit_memory_footprint_encode site_enc)
      (audit_memory_footprint_input_budget site_enc site_budget))) as Hbound.
  assert (Hlist : forall fs,
    audit_list_events_work (audit_memory_footprint_work site_work)
      (snd (audit_list_encode (audit_memory_footprint_encode site_enc) fs)) <=
    audit_list_input_budget (audit_memory_footprint_encode site_enc)
      (audit_memory_footprint_input_budget site_enc site_budget) fs).
  { intro fs; apply audit_list_input_bound; intro fp.
    apply audit_memory_footprint_input_bound; exact Hsite. }
  destruct q as [fs|].
  - specialize (Hbound (inr fs) Hunit Hlist).
    exact Hbound.
  - specialize (Hbound (inl tt) Hunit Hlist).
    exact Hbound.
Qed.

(** The four encoders are bounded by component callbacks at their original inputs. *)
Theorem audit_memory_encoders_input_bound : audit_memory_encoders_input_bound_statement.
Proof.
  intros N E T CN CE SE node_enc edge_enc site_enc node_work edge_work site_work
    node_budget edge_budget site_budget Hnode Hedge Hsite.
  repeat split.
  - intro v; apply audit_memory_version_input_bound; assumption.
  - intro fp; apply audit_memory_footprint_input_bound; assumption.
  - intro q; apply audit_memory_scope_input_bound; assumption.
  - intro key.
    destruct audit_base_encoder_input_bound as [Hpositive _].
    unfold audit_memory_memo_key_work, audit_memory_memo_key_encode,
      audit_memory_memo_key_input_budget.
    apply audit_pair_input_bound; [exact Hpositive|].
    intro v; apply audit_memory_version_input_bound; assumption.
Qed.

(** Each compared pair uses both site callbacks and the actual equality trace. *)
Lemma audit_disjoint_pair_budget_input T CE (enc : T -> positive * list CE) work budget
    (left right : footprint T) :
  (forall t, work (snd (enc t)) <= budget t) ->
  audit_disjoint_pair_work work left right (snd (enc (fp_site left))) (snd (enc (fp_site right)))
    (snd (audit_positive_eqb (fst (enc (fp_site left))) (fst (enc (fp_site right))))) <=
    audit_disjoint_pair_input_budget enc budget left right.
Proof.
  intro Hsite.
  pose proof (Hsite (fp_site left)) as Hleft.
  pose proof (Hsite (fp_site right)) as Hright.
  pose proof (audit_positive_eqb_source_bound (fst (enc (fp_site left)))
    (fst (enc (fp_site right)))) as Heq.
  unfold audit_disjoint_pair_work, audit_disjoint_pair_input_budget; lia.
Qed.

(** The inner disjointness budget lifts pair bounds to all right occurrences. *)
Lemma audit_disjoint_inner_budget_input T CE (enc : T -> positive * list CE) work budget
    (left : footprint T) (right : list (footprint T)) :
  (forall t, work (snd (enc t)) <= budget t) ->
  audit_disjoint_inner_budget enc work left right <=
    audit_disjoint_inner_input_budget enc budget left right.
Proof.
  intro Hsite; induction right as [|item rest IH].
  - reflexivity.
  - cbn [audit_disjoint_inner_budget audit_disjoint_inner_input_budget].
    pose proof (audit_disjoint_pair_budget_input T CE enc work budget left item Hsite); lia.
Qed.

(** Scope work is bounded by all input pairs or zero for an all-memory branch. *)
Lemma audit_scopes_disjoint_work_input T CE (enc : T -> positive * list CE) work budget
    (left right : memory_scope T) :
  (forall t, work (snd (enc t)) <= budget t) ->
  AnalysesAuditMemoryDisjoint.audit_disjoint_source_work work
    (snd (audit_memory_scopes_disjoint enc left right)) <=
    audit_scopes_disjoint_input_budget enc budget left right.
Proof.
  intro Hsite; destruct left as [ls|], right as [rs|];
    cbn [audit_memory_scopes_disjoint audit_scopes_disjoint_input_budget]; try reflexivity.
  rewrite audit_disjoint_source_work.
  induction ls as [|item rest IH].
  - reflexivity.
  - cbn [audit_disjoint_budget audit_disjoint_input_budget].
    pose proof (audit_disjoint_inner_budget_input T CE enc work budget item rs Hsite); lia.
Qed.

(** An effect lookup charges its actual edge lookup and, when present, its numeric lookup. *)
Lemma audit_memory_effect_get_work_input E T CE (enc : E -> positive * list CE)
    work budget (table : Map.t E (Map.t nat (memory_effect T))) edge index :
  (forall e, work (snd (enc e)) <= budget e) ->
  audit_memory_effect_get_work work (snd (audit_memory_effect_get enc table edge index)) <=
    audit_memory_effect_get_input_budget enc budget table edge index.
Proof.
  intro Hedge.
  pose proof (audit_map_get_source_work_bound E _ CE enc work edge table) as Hfirst.
  pose proof (Hedge edge) as Henc.
  destruct audit_base_encoder_input_bound as [_ [_ [_ [_ [Hnat _]]]]].
  unfold audit_memory_effect_get, audit_memory_effect_get_input_budget.
  destruct (audit_map_get enc edge table) as [row first] eqn:Hget.
  cbn in Hfirst |- *.
  destruct row as [actual|].
  - pose proof (audit_map_get_source_work_bound nat _ _ audit_nat_encode audit_nat_events_work
      index actual) as Hsecond.
    specialize (Hnat index).
    destruct (audit_map_get audit_nat_encode index actual) as [result second] eqn:Hindex.
    simpl in Hsecond |- *; unfold audit_nat_input_budget in Hnat; simpl in Hnat.
    lia.
  - cbn; lia.
Qed.

(** Operand calls preserve every key occurrence, including missing results. *)
Lemma audit_memory_operands_work_input N E T CE SE IE OE BE
    (operand : N -> option E -> option (memory_version N E) * list OE)
    edge_work site_work incoming_work operand_work before_work budget node keys :
  (forall n key, operand_work (snd (operand n key)) <= budget n key) ->
  audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work
    (snd (@audit_memory_operands N E T CE SE IE OE BE operand node keys)) <=
    audit_operand_calls_input_budget budget node keys.
Proof.
  intro Hoperand; induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_memory_operands audit_operand_calls_input_budget].
    pose proof (Hoperand node key) as Hcall.
    destruct (operand node key) as [entry events].
    destruct (@audit_memory_operands N E T CE SE IE OE BE operand node rest) as [tail calls].
    destruct entry; simpl in *; unfold audit_raw_next_source_work in *; simpl in *; lia.
Qed.

(** The raw successor budget covers each actual lookup and callback on every branch. *)
Theorem audit_raw_next_whole_input_bound : audit_raw_next_whole_input_bound_statement.
Proof.
  intros N E T CE SE IE OE BE edge_enc site_enc table incoming operand before
    edge_work site_work incoming_work operand_work before_work edge_budget site_budget
    incoming_budget operand_budget before_budget q v Hedge Hsite Hincoming Hoperand Hbefore.
  destruct v as [|node|edge index].
  - reflexivity.
  - cbn [audit_memory_raw_next audit_raw_next_input_budget].
    pose proof (Hincoming node) as Hin.
    destruct (incoming node) as [edges events].
    cbn in Hin |- *.
    pose proof (Hoperand node None) as Hfirst.
    pose proof (audit_memory_operands_work_input N E T CE SE IE OE BE operand edge_work
      site_work incoming_work operand_work before_work operand_budget node (map Some edges)
      Hoperand) as Hcalls.
    destruct (@audit_memory_operands N E T CE SE IE OE BE operand node (map Some edges))
      as [out calls].
    destruct (operand node None) as [entry first]; destruct entry;
    unfold audit_raw_next_source_work in *; simpl in *; lia.
  - cbn [audit_memory_raw_next audit_raw_next_input_budget].
    pose proof (audit_memory_effect_get_work_input E T CE edge_enc edge_work edge_budget table
      edge index Hedge) as Hget.
    destruct (audit_memory_effect_get edge_enc table edge index) as [effect events].
    cbn in Hget |- *.
    destruct effect as [effect|].
    + pose proof (Hbefore edge index) as Hprev.
      destruct (before edge index) as [previous calls].
      cbn in Hprev |- *.
      destruct previous as [previous|].
      * pose proof (audit_scopes_disjoint_work_input T SE site_enc site_work site_budget
          (effect_writes effect) q Hsite) as Hdisjoint.
        destruct (audit_memory_scopes_disjoint site_enc (effect_writes effect) q)
          as [disjoint de].
        cbn in Hdisjoint |- *.
        unfold audit_raw_next_source_work; simpl; lia.
      * unfold audit_raw_next_source_work; simpl; lia.
    + unfold audit_raw_next_source_work; simpl; lia.
Qed.
