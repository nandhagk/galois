(** * Adequacy of counted memory search

    The counted search follows the actual worklist transitions and binary fuel.
    For example, an empty worklist stops before performing a search step.
    Builds on: AnalysesAuditMemorySearch and collection operation adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditMap
  CollectionsAuditFinSet CollectionsAuditMapAdequacy CollectionsAuditFinSetAdequacy.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemorySearch.
Import List.ListNotations.

(** * Search transitions and fuel *)

(** A counted transition returns the same state as the original search step. *)
Lemma audit_memory_search_step_erases {V E NE} (original : encoding V)
    (enc : V -> positive * list E) (next : V -> list V * list NE) st :
  (forall v, fst (enc v) = encode original v) ->
  fst (audit_memory_search_step enc next st) =
    memory_search_step original (fun v => fst (next v)) st.
Proof.
  intro Henc.
  unfold audit_memory_search_step, memory_search_step.
  destruct (memory_search_todo st) as [|v rest]; [reflexivity|].
  pose proof (audit_map_get_erases V nat E enc original v (memory_search_seen st) (Henc v))
    as Hread.
  destruct (audit_map_get enc v (memory_search_seen st)) as [found reads]; cbn in Hread.
  rewrite <- Hread.
  destruct found as [rank|].
  - pose proof (audit_finset_add_erases V E enc original v (memory_search_roots st) (Henc v))
      as Hroot.
    destruct (audit_finset_add enc v (memory_search_roots st)) as [roots calls]; cbn in Hroot.
    now rewrite <- Hroot.
  - pose proof (audit_map_set_erases V nat E enc original v (memory_search_clock st)
      (memory_search_seen st) (Henc v)) as Hwrite.
    destruct (audit_map_set enc v (memory_search_clock st) (memory_search_seen st))
      as [updated writes]; cbn in Hwrite.
    rewrite <- Hwrite.
    destruct (next v) as [successors calls].
    destruct successors as [|w ws]; cbn.
    + pose proof (audit_finset_add_erases V E enc original v (memory_search_roots st) (Henc v))
        as Hroot.
      destruct (audit_finset_add enc v (memory_search_roots st)) as [roots events]; cbn in Hroot.
      now rewrite <- Hroot.
    + reflexivity.
Qed.

(** Binary recursion erases to the plain search at each actual intermediate state. *)
Theorem audit_memory_search_run_erases : audit_memory_search_run_erases_statement.
Proof.
  intros V E NE original enc next fuel.
  induction fuel as [half IH|half IH|]; intros st Henc;
    cbn [audit_memory_search_run memory_search_run];
    destruct (memory_search_todo st) as [|v rest] eqn:Htodo; cbn; try reflexivity.
  - destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    pose proof (IH st Henc) as Hone; rewrite Hfirst in Hone; cbn in Hone.
    destruct (audit_memory_search_run enc next half middle) as [after second] eqn:Hsecond.
    pose proof (IH middle Henc) as Hmiddle.
    rewrite Hsecond in Hmiddle; cbn in Hmiddle.
    rewrite <- Hone, <- Hmiddle.
    pose proof (audit_memory_search_step_erases original enc next after Henc) as Hstep.
    destruct (audit_memory_search_step enc next after) as [out final]; cbn in *.
    exact Hstep.
  - destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    pose proof (IH st Henc) as Hone; rewrite Hfirst in Hone; cbn in Hone.
    pose proof (IH middle Henc) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [after second] eqn:Hsecond.
    cbn in Htwo.
    now rewrite <- Hone, <- Htwo.
  - pose proof (audit_memory_search_step_erases original enc next st Henc) as Hstep.
    destruct (audit_memory_search_step enc next st) as [out events]; cbn in *.
    exact Hstep.
Qed.

(** Appending traces adds their counted transitions. *)
Lemma audit_memory_search_steps_app {V E NE} (xs ys : list (audit_memory_search_event V E NE)) :
  audit_memory_search_steps (xs ++ ys) =
    audit_memory_search_steps xs + audit_memory_search_steps ys.
Proof.
  induction xs as [|event rest IH]; cbn; [reflexivity|].
  destruct event; cbn; rewrite IH; reflexivity.
Qed.

(** A single worklist transition records exactly one step. *)
Lemma audit_memory_search_step_count {V E NE} (enc : V -> positive * list E)
    (next : V -> list V * list NE) st :
  audit_memory_search_steps (snd (audit_memory_search_step enc next st)) = 1.
Proof.
  unfold audit_memory_search_step.
  destruct (memory_search_todo st) as [|v rest]; cbn; [reflexivity|].
  destruct (audit_map_get enc v (memory_search_seen st)) as [found reads].
  destruct found as [rank|].
  - destruct (audit_finset_add enc v (memory_search_roots st)); reflexivity.
  - destruct (audit_map_set enc v (memory_search_clock st) (memory_search_seen st)).
    destruct (next v) as [successors events].
    destruct successors; [destruct (audit_finset_add enc v (memory_search_roots st))|];
      reflexivity.
Qed.

(** A search can perform at most one transition for each unit of fuel. *)
Theorem audit_memory_search_step_bound : audit_memory_search_step_bound_statement.
Proof.
  intros V E NE enc next fuel.
  induction fuel as [half IH|half IH|]; intro st;
    cbn [audit_memory_search_run];
    destruct (memory_search_todo st) as [|v rest] eqn:Htodo; cbn.
  - lia.
  - pose proof (IH st) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [after second] eqn:Hsecond.
    cbn in Htwo.
    pose proof (audit_memory_search_step_count enc next after) as Hlast.
    destruct (audit_memory_search_step enc next after) as [out final]; cbn in Hlast.
    cbn [snd audit_memory_search_steps].
    rewrite !audit_memory_search_steps_app, Hlast.
    rewrite Pos2Nat.inj_xI; lia.
  - lia.
  - pose proof (IH st) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [out second] eqn:Hsecond.
    cbn in Htwo.
    cbn [snd audit_memory_search_steps].
    rewrite audit_memory_search_steps_app, Pos2Nat.inj_xO; lia.
  - lia.
  - pose proof (audit_memory_search_step_count enc next st) as Hstep.
    destruct (audit_memory_search_step enc next st) as [out events]; cbn in Hstep.
    cbn [snd audit_memory_search_steps]; lia.
Qed.

(** Source and primitive charges both distribute over concatenated event traces. *)
Lemma audit_memory_search_work_app {V E NE} (work : list E -> nat)
    (next_work : list NE -> nat) (xs ys : list (audit_memory_search_event V E NE)) :
  audit_memory_search_source_work work next_work (xs ++ ys) =
    audit_memory_search_source_work work next_work xs +
    audit_memory_search_source_work work next_work ys /\
  audit_memory_search_primitive_work work next_work (xs ++ ys) =
    audit_memory_search_primitive_work work next_work xs +
    audit_memory_search_primitive_work work next_work ys.
Proof.
  induction xs as [|event rest IH]; cbn; [split; reflexivity|].
  destruct IH as [Hsource Hprimitive].
  destruct event; cbn; rewrite Hsource, Hprimitive; lia.
Qed.

(** One step adds at most four control units beyond its captured primitive calls. *)
Lemma audit_memory_search_step_work {V E NE} (enc : V -> positive * list E)
    (next : V -> list V * list NE) work next_work st :
  audit_memory_search_source_work work next_work (snd (audit_memory_search_step enc next st)) <=
    4 + audit_memory_search_primitive_work work next_work
      (snd (audit_memory_search_step enc next st)).
Proof.
  unfold audit_memory_search_step.
  destruct (memory_search_todo st) as [|v rest]; cbn; [lia|].
  destruct (audit_map_get enc v (memory_search_seen st)) as [found reads].
  destruct found as [rank|].
  - destruct (audit_finset_add enc v (memory_search_roots st)); cbn; lia.
  - destruct (audit_map_set enc v (memory_search_clock st) (memory_search_seen st)).
    destruct (next v) as [successors events].
    destruct successors; [destruct (audit_finset_add enc v (memory_search_roots st))|]; cbn; lia.
Qed.

(** The extra two-unit margin pays for the parent frame of a binary call. *)
Lemma audit_memory_search_source_bound_margin {V E NE} (enc : V -> positive * list E)
    (next : V -> list V * list NE) work next_work fuel st :
  2 + audit_memory_search_source_work work next_work
    (snd (audit_memory_search_run enc next fuel st)) <=
  8 * Pos.to_nat fuel + audit_memory_search_primitive_work work next_work
    (snd (audit_memory_search_run enc next fuel st)).
Proof.
  revert st.
  induction fuel as [half IH|half IH|]; intro st;
    cbn [audit_memory_search_run];
    destruct (memory_search_todo st) as [|v rest] eqn:Htodo; cbn.
  - pose proof (Pos2Nat.is_pos (xI half)); lia.
  - pose proof (IH st) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [after second] eqn:Hsecond.
    cbn in Htwo.
    pose proof (audit_memory_search_step_work enc next work next_work after) as Hlast.
    destruct (audit_memory_search_step enc next after) as [out final]; cbn in Hlast.
    cbn [snd audit_memory_search_source_work audit_memory_search_primitive_work].
    destruct (audit_memory_search_work_app work next_work first (second ++ final)) as [Hs Hp].
    destruct (audit_memory_search_work_app work next_work second final) as [Hs' Hp'].
    rewrite Hs, Hp, Hs', Hp', Pos2Nat.inj_xI; lia.
  - pose proof (Pos2Nat.is_pos (xO half)); lia.
  - pose proof (IH st) as Hone.
    destruct (audit_memory_search_run enc next half st) as [middle first] eqn:Hfirst.
    cbn in Hone.
    pose proof (IH middle) as Htwo.
    destruct (audit_memory_search_run enc next half middle) as [out second] eqn:Hsecond.
    cbn in Htwo.
    cbn [snd audit_memory_search_source_work audit_memory_search_primitive_work].
    destruct (audit_memory_search_work_app work next_work first second) as [Hs Hp].
    rewrite Hs, Hp, Pos2Nat.inj_xO.
    pose proof (Pos2Nat.is_pos half); lia.
  - cbn; lia.
  - pose proof (audit_memory_search_step_work enc next work next_work st) as Hstep.
    destruct (audit_memory_search_step enc next st) as [out events]; cbn in Hstep.
    cbn [snd audit_memory_search_source_work audit_memory_search_primitive_work]; lia.
Qed.

(** Binary recursion charges its control separately from the actual nested calls. *)
Theorem audit_memory_search_source_bound : audit_memory_search_source_bound_statement.
Proof.
  intros V E NE enc next work next_work fuel st.
  cbn zeta.
  pose proof (audit_memory_search_source_bound_margin enc next work next_work fuel st).
  lia.
Qed.

(** Pointwise equal successor callbacks give the same transition. *)
Lemma memory_search_step_next_agrees {V} (enc : encoding V) (left right : V -> list V) st :
  (forall v, left v = right v) ->
  memory_search_step enc left st = memory_search_step enc right st.
Proof.
  intro Hnext; unfold memory_search_step.
  destruct (memory_search_todo st) as [|v rest]; [reflexivity|].
  destruct (CollectionsMap.Map.get enc v (memory_search_seen st)); [reflexivity|].
  now rewrite Hnext.
Qed.

(** Pointwise successor agreement propagates through the actual intermediate states. *)
Lemma memory_search_run_next_agrees {V} (enc : encoding V) (left right : V -> list V) fuel st :
  (forall v, left v = right v) ->
  memory_search_run enc left fuel st = memory_search_run enc right fuel st.
Proof.
  revert st.
  induction fuel as [half IH|half IH|]; intros st Hnext;
    cbn [memory_search_run]; destruct (memory_search_todo st); [reflexivity| |reflexivity| |
      reflexivity|].
  - rewrite (IH st Hnext), (IH (memory_search_run enc right half st) Hnext).
    apply memory_search_step_next_agrees; exact Hnext.
  - rewrite (IH st Hnext), (IH (memory_search_run enc right half st) Hnext); reflexivity.
  - apply memory_search_step_next_agrees; exact Hnext.
Qed.
