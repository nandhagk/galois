(** * Search input budget adequacy

    Each search transition pays for its actual key and successor calls.
    For example, a repeated key adds a root without fetching successors.
    Builds on: AnalysesAuditMemorySearchInputBudget and collection work bounds. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditMapAdequacy CollectionsAuditDenseAdequacy.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemorySearch
  AnalysesAuditMemorySearchInputBudget AnalysesAuditMemorySearchAdequacy.
Import List.ListNotations.

(** * Input-derived search bounds *)

(** The step recurrence covers its actual reads, writes, root insertion and successor body. *)
Lemma audit_search_step_input_bound {V CE NE} (enc : V -> positive * list CE)
    (next : V -> list V * list NE) work next_work key_budget next_budget st :
  (forall v, work (snd (enc v)) <= key_budget v) ->
  (forall v, next_work (snd (next v)) <= next_budget v) ->
  audit_memory_search_source_work work next_work (snd (audit_memory_search_step enc next st)) <=
    audit_search_step_input_budget enc next key_budget next_budget st.
Proof.
  intros Hkey Hnext.
  unfold audit_memory_search_step, audit_search_step_input_budget.
  destruct (memory_search_todo st) as [|v rest]; cbn; [lia|].
  pose proof (audit_map_get_source_work_bound V nat CE enc work v (memory_search_seen st)) as Hr.
  pose proof (dense_finset_add_bound V CE enc work v (memory_search_roots st)) as Ha.
  pose proof (audit_map_set_source_work_bound V nat CE enc work v (memory_search_clock st)
    (memory_search_seen st)) as Hw.
  specialize (Hkey v); specialize (Hnext v).
  destruct (audit_map_get enc v (memory_search_seen st)) as [found reads]; cbn in Hr.
  destruct found as [rank|].
  - destruct (audit_finset_add enc v (memory_search_roots st)) as [roots calls]; cbn in Ha.
    cbn [snd audit_memory_search_source_work audit_search_read_input_budget
      audit_search_write_input_budget fst]; lia.
  - destruct (audit_map_set enc v (memory_search_clock st) (memory_search_seen st))
      as [updated writes]; cbn in Hw.
    destruct (next v) as [successors calls]; cbn in Hnext.
    destruct successors as [|w ws].
    + destruct (audit_finset_add enc v (memory_search_roots st)) as [roots root_calls]; cbn in Ha.
      cbn [snd fst audit_memory_search_source_work audit_search_read_input_budget
        audit_search_write_input_budget]; lia.
    + cbn [snd fst audit_memory_search_source_work audit_search_read_input_budget
        audit_search_write_input_budget]; lia.
Qed.

(** The recurrence follows both actual intermediate states for binary fuel. *)
Theorem audit_search_whole_input_bound : audit_search_whole_input_bound_statement.
Proof.
  intros V CE NE enc next work next_work key_budget next_budget fuel.
  induction fuel as [half IH|half IH|]; intros st Hkey Hnext;
    cbn [audit_memory_search_run audit_search_run_input_budget];
    destruct (memory_search_todo st) as [|v rest] eqn:Htodo; cbn.
  - lia.
  - pose proof (IH st Hkey Hnext) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle Hkey Hnext) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [after second] eqn:Hsecond.
    cbn in Htwo.
    pose proof (audit_search_step_input_bound enc next work next_work key_budget next_budget after
      Hkey Hnext) as Hlast.
    destruct (audit_memory_search_step enc next after) as [out final]; cbn in Hlast.
    cbn [snd fst audit_memory_search_source_work].
    destruct (audit_memory_search_work_app work next_work first (second ++ final)) as [Hs _].
    destruct (audit_memory_search_work_app work next_work second final) as [Hs' _].
    rewrite Hs, Hs', Hsecond; cbn; lia.
  - lia.
  - pose proof (IH st Hkey Hnext) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle Hkey Hnext) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [out second] eqn:Hsecond.
    cbn in Htwo.
    cbn [snd fst audit_memory_search_source_work].
    destruct (audit_memory_search_work_app work next_work first second) as [Hs _].
    rewrite Hs; lia.
  - lia.
  - pose proof (audit_search_step_input_bound enc next work next_work key_budget next_budget st
      Hkey Hnext) as Hstep.
    destruct (audit_memory_search_step enc next st) as [out events]; cbn in Hstep.
    cbn [snd fst audit_memory_search_source_work]; lia.
Qed.
