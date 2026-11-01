(** * Binary-credit memo execution adequacy

    The concrete producer follows the memo tree rules with its exact returned persistent cache.
    For example, a completed hit preserves all eight supplied credits.
    Builds on: memo execution, binary predecessor and well-founded recursion. *)

From Stdlib Require Import List NArith PArith Wf_nat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditMapAdequacy
  CollectionsAuditFinSetAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryFrontier
  AnalysesMemoryWalk AnalysesAuditMemoryState AnalysesAuditMemoryStateAdequacy
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoPlain
  AnalysesAuditMemoryMemoPlainAdequacy AnalysesAuditMemoryMemoExecute.
Import List.ListNotations.

(** * Binary predecessor *)

(** Binary borrow visits at most one frame per input bit and returns the standard predecessor. *)
Lemma audit_memo_pred_double_correct input :
  fst (audit_memo_pred_double input) = Pos.pred_double input /\
  length (snd (audit_memo_pred_double input)) <= Pos.size_nat input.
Proof.
  induction input as [input IH|input IH|]; cbn [audit_memo_pred_double Pos.pred_double];
    try (split; [reflexivity|cbn; lia]).
  destruct (audit_memo_pred_double input) as [result events]; cbn in IH |- *.
  destruct IH as [Hresult Hlength]; rewrite Hresult; split; [reflexivity|cbn; lia].
Qed.

(** The predecessor mirror returns N.pred and charges every binary borrow frame. *)
Theorem audit_memo_pred_correct : audit_memo_pred_correct_statement.
Proof.
  intros [|[input|input|]]; cbn [audit_memo_pred N.pred];
    try (split; [reflexivity|cbn; lia]).
  pose proof (audit_memo_pred_double_correct input) as Hdouble.
  destruct (audit_memo_pred_double input) as [result events]; cbn in Hdouble |- *.
  destruct Hdouble as [Hresult Hlength]; rewrite Hresult; split; [reflexivity|cbn; lia].
Qed.

(** * Concrete execution trees *)

Section ExecutionTree.
  Context {N E CV CK NE : Type}.
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable scope : positive.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.

  (** Child recursion composes the oracle's trees and threads each returned memo and credit. *)
  Lemma audit_memo_execute_children_tree bound recur active versions :
    (forall credit Hcredit memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      audit_memo_tree version_enc key_enc scope next active memo v credit
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run)) ->
    forall memo credit Hcredit,
      let run := proj1_sig (audit_memo_execute_children version_enc bound recur active memo
        versions credit Hcredit) in
      audit_memo_children version_enc key_enc scope next active memo versions credit
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run).
  Proof.
    intro Hrecur; induction versions as [|v rest IH]; intros memo credit Hcredit.
    - cbn [audit_memo_execute_children]; constructor.
    - pose proof (Hrecur credit Hcredit memo v) as Hone.
      cbn [audit_memo_execute_children].
      destruct (recur credit Hcredit active memo v) as [one Hbound].
      cbn [proj1_sig] in Hone |- *.
      match goal with
      | |- context [audit_memo_execute_children _ _ _ _ _ _ _ ?proof] =>
        specialize (IH (audit_memo_cache one) (audit_memo_credit one) proof);
        destruct (audit_memo_execute_children version_enc bound recur active
          (audit_memo_cache one) rest (audit_memo_credit one) proof) as [tail Htail]
      end.
      cbn [proj1_sig] in IH |- *.
      destruct (audit_memo_union version_enc (clobber_roots (audit_memo_value one))
        (clobber_roots (audit_memo_value tail))) as [roots [build enumeration]] eqn:Hunion.
      cbn [proj1_sig audit_memo_value audit_memo_cache audit_memo_credit audit_memo_body_events].
      econstructor; eassumption.
  Qed.

  (** Every body branch constructs its tree from the exact primitive calls and child trees. *)
  Lemma audit_memo_execute_body_tree fuel recur :
    (forall credit Hcredit active memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      audit_memo_tree version_enc key_enc scope next active memo v credit
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run)) ->
    forall active memo v,
      let run := proj1_sig (audit_memo_execute_body version_enc key_enc scope next
        fuel recur active memo v) in
      audit_memo_tree version_enc key_enc scope next active memo v fuel
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run).
  Proof.
    intros Hrecur active memo v.
    unfold audit_memo_execute_body.
    destruct (audit_finset_mem version_enc v active) as [is_active ae] eqn:Hactive.
    destruct is_active.
    - cbn; econstructor; exact Hactive.
    - destruct (audit_map_get key_enc (scope, v) memo) as [entry le] eqn:Hlookup.
      destruct entry as [[|roots]|].
      + cbn; eapply AuditMemoTreeBusy; eassumption.
      + cbn; eapply AuditMemoTreeDone; eassumption.
      + destruct fuel as [|positive_fuel].
        * cbn; eapply AuditMemoTreeFuel; eassumption.
        * destruct (next v) as [successors ne] eqn:Hnext.
          destruct successors as [|first rest].
          -- destruct (audit_map_set key_enc (scope, v) (MemoDone [v]) memo)
               as [final se] eqn:Hstore.
             cbn [proj1_sig audit_memo_value audit_memo_cache audit_memo_credit
               audit_memo_body_events].
             replace (Npos positive_fuel) with (N.succ (N.pred (Npos positive_fuel))) at 1
               by (rewrite N.succ_pred; [reflexivity|discriminate]).
             eapply AuditMemoTreeTerminal; eassumption.
          -- destruct (audit_finset_add version_enc v active) as [active' adds] eqn:Hadd.
             match goal with
             | |- context [audit_memo_execute_children _ _ _ _ _ _ _ ?proof] =>
               pose proof (audit_memo_execute_children_tree (Npos positive_fuel) recur active'
                 (first :: rest) (fun credit Hcredit memo' v' =>
                   Hrecur credit Hcredit active' memo' v') memo (N.pred (Npos positive_fuel))
                 proof) as Hchildren;
               destruct (audit_memo_execute_children version_enc (Npos positive_fuel) recur
                 active' memo (first :: rest) (N.pred (Npos positive_fuel)) proof)
                 as [children Hbound]
             end.
             cbn [proj1_sig] in Hchildren |- *.
             destruct (clobber_complete (audit_memo_value children)) eqn:Hcomplete.
             ++ destruct (audit_map_set key_enc (scope, v)
                  (MemoDone (clobber_roots (audit_memo_value children)))
                  (audit_memo_cache children)) as [final se] eqn:Hstore.
                cbn [proj1_sig audit_memo_value audit_memo_cache audit_memo_credit
                  audit_memo_body_events].
                replace (Npos positive_fuel) with (N.succ (N.pred (Npos positive_fuel))) at 1
                  by (rewrite N.succ_pred; [reflexivity|discriminate]).
                eapply AuditMemoTreeBranchComplete; eassumption.
             ++ cbn [proj1_sig audit_memo_value audit_memo_cache audit_memo_credit
                  audit_memo_body_events].
                replace (Npos positive_fuel) with (N.succ (N.pred (Npos positive_fuel))) at 1
                  by (rewrite N.succ_pred; [reflexivity|discriminate]).
                eapply AuditMemoTreeBranchIncomplete; eassumption.
  Qed.

  (** Accessibility induction validates the actual well-founded producer without extensionality. *)
  Lemma audit_memo_fix_tree fuel (access : Acc (ltof BinNums.N N.to_nat) fuel) :
    forall active memo v,
      let run := proj1_sig (Fix_F
        (fun credit => forall active memo v,
          {run : audit_memo_execution N E CV CK NE | audit_memo_credit_bounded credit run})
        (audit_memo_execute_body version_enc key_enc scope next) access active memo v) in
      audit_memo_tree version_enc key_enc scope next active memo v fuel
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run)
        (audit_memo_body_events run).
  Proof.
    revert fuel access; fix IH 2; intros fuel [smaller] active memo v.
    cbn [Fix_F].
    apply audit_memo_execute_body_tree.
    intros credit Hcredit active' memo' v'; apply IH.
  Qed.
End ExecutionTree.

(** The fixed producer returns a tree at its precise result, cache, remaining credit and events. *)
Theorem audit_memo_execute_tree : audit_memo_execute_tree_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next fuel active memo v.
  unfold audit_memo_execute, Fix.
  apply audit_memo_fix_tree.
Qed.

(** * Trace prefixes and cycles *)

Section TraceFacts.
  Context {N E T : Type}.
  Variable ET : encoding T.
  Variable effects : E -> list (memory_effect T).
  Variable mg : memory_graph N E.
  Variable q : memory_scope T.

  (** Every backward trace includes its starting version and is nonempty. *)
  Lemma audit_memo_trace_head start trace :
    memory_walk_trace ET effects mg q start trace -> In start trace /\ trace <> [].
  Proof.
    intro Htrace; inversion Htrace; subst; split; cbn; intuition discriminate.
  Qed.

  (** Prefixing a nonempty trace preserves its last version. *)
  Lemma audit_memo_trace_last_cons start trace prefix :
    memory_walk_trace ET effects mg q start trace ->
    memory_trace_last (prefix :: trace) = memory_trace_last trace.
  Proof.
    intro Htrace; inversion Htrace; reflexivity.
  Qed.

  (** A trace can stop at any of its vertices while retaining only original occurrences. *)
  Lemma audit_memo_trace_prefix start trace target :
    memory_walk_trace ET effects mg q start trace -> In target trace ->
    exists prefix, memory_walk_trace ET effects mg q start prefix /\
      memory_trace_last prefix = Some target /\ incl prefix trace.
  Proof.
    intros Htrace; induction Htrace as [v|v w rest Hstep Htrace IH]; intro Hin.
    - destruct Hin as [<-|Hfalse]; [|contradiction].
      exists [v]; split; [constructor|split; [reflexivity|apply incl_refl]].
    - destruct Hin as [<-|Hin].
      + exists [v]; split; [constructor|split; [reflexivity|]].
        intros item [<-|Hfalse]; [left; reflexivity|contradiction].
      + destruct (IH Hin) as [prefix [Hprefix [Hlast Hincl]]].
        exists (v :: prefix); split; [econstructor; eassumption|].
        split; [rewrite (audit_memo_trace_last_cons w prefix v Hprefix); exact Hlast|].
        intros item [<-|Hmember]; [left; reflexivity|right; apply Hincl; exact Hmember].
  Qed.

  (** Appending one successor extends the same trace at its actual final version. *)
  Lemma audit_memo_trace_extend start trace last target :
    memory_walk_trace ET effects mg q start trace -> memory_trace_last trace = Some last ->
    memory_walk_next ET effects mg q last target ->
    memory_walk_trace ET effects mg q start (trace ++ [target]).
  Proof.
    intros Htrace; induction Htrace as [v|v w rest Hstep Htrace IH]; intros Hlast Hnext.
    - cbn in Hlast; inversion Hlast; subst; cbn; econstructor; [exact Hnext|constructor].
    - rewrite (audit_memo_trace_last_cons w rest v Htrace) in Hlast.
      cbn; econstructor; [exact Hstep|apply IH; assumption].
  Qed.

  (** A path from a child back to its parent produces a repeated-child trace. *)
  Lemma audit_memo_trace_cycle parent child trace :
    memory_walk_next ET effects mg q parent child ->
    memory_walk_trace ET effects mg q child trace -> In parent trace ->
    exists cycle, memory_walk_trace ET effects mg q child cycle /\
      ~ NoDup cycle /\ incl cycle (parent :: trace).
  Proof.
    intros Hstep Htrace Hparent.
    destruct (audit_memo_trace_prefix child trace parent Htrace Hparent)
      as [prefix [Hprefix [Hlast Hincl]]].
    exists (prefix ++ [child]); split.
    - eapply audit_memo_trace_extend; eassumption.
    - split.
      + intro Hnodup.
        pose proof (@NoDup_remove_2 _ prefix [] child Hnodup) as Hnot.
        rewrite app_nil_r in Hnot.
        apply Hnot; exact (proj1 (audit_memo_trace_head child prefix Hprefix)).
      + intros item Hin; apply in_app_iff in Hin; destruct Hin as [Hin|[<-|Hfalse]].
        * right; apply Hincl; exact Hin.
        * right; exact (proj1 (audit_memo_trace_head child trace Htrace)).
        * contradiction.
  Qed.

  (** Acyclic child traces cannot revisit the parent of their first edge. *)
  Lemma audit_memo_acyclic_parent parent child :
    memory_walk_next ET effects mg q parent child ->
    (forall trace, memory_walk_trace ET effects mg q child trace -> NoDup trace) ->
    forall trace, memory_walk_trace ET effects mg q child trace -> ~ In parent trace.
  Proof.
    intros Hstep Hacyclic trace Htrace Hin.
    destruct (audit_memo_trace_cycle parent child trace Hstep Htrace Hin)
      as [cycle [Hcycle [Hrepeat Hincl]]].
    apply Hrepeat; apply Hacyclic; exact Hcycle.
  Qed.

  (** A cyclic parent trace either already has a cyclic tail or has a rotated child cycle. *)
  Lemma audit_memo_cycle_tail (VE : encoding (memory_version N E)) parent child trace :
    memory_walk_next ET effects mg q parent child ->
    memory_walk_trace ET effects mg q child trace -> ~ NoDup (parent :: trace) ->
    ~ NoDup trace \/ exists cycle, memory_walk_trace ET effects mg q child cycle /\
      ~ NoDup cycle /\ incl cycle (parent :: trace).
  Proof.
    intros Hstep Htrace Hrepeat.
    assert (Heq_dec : forall x y : memory_version N E, {x = y} + {x <> y}).
    { intros x y; destruct (Pos.eq_dec (encode VE x) (encode VE y)) as [Hequal|Hdifferent].
      - left; apply (encode_injective VE); exact Hequal.
      - right; intro Hequal; apply Hdifferent; now rewrite Hequal. }
    destruct (in_dec Heq_dec parent trace) as [Hin|Hnot].
    - right; apply audit_memo_trace_cycle; assumption.
    - left; intro Hnodup; apply Hrepeat; constructor; assumption.
  Qed.
End TraceFacts.

(** * Result semantics *)

Section ResultSemantics.
  Context {N E T : Type}.
  Variable ET : encoding T.
  Variable effects : E -> list (memory_effect T).
  Variable mg : memory_graph N E.
  Variable q : memory_scope T.

  (** A result has unique roots, exact acyclic completion, and intersects terminal or cyclic
      traces. *)
  Definition audit_memo_result_correct start (result : memory_clobber_result N E) : Prop :=
    NoDup (clobber_roots result) /\
    (clobber_complete result = true ->
      (forall trace, memory_walk_trace ET effects mg q start trace -> NoDup trace) /\
      forall v, In v (clobber_roots result) <-> memory_walk_terminal ET effects mg q v /\
        exists trace, memory_walk_trace ET effects mg q start trace /\
          memory_trace_last trace = Some v) /\
    forall trace last, memory_walk_trace ET effects mg q start trace ->
      memory_trace_last trace = Some last ->
      (memory_walk_terminal ET effects mg q last \/ ~ NoDup trace) ->
      exists hit, In hit trace /\ In hit (clobber_roots result).

  (** Child results describe the union of their starts while preserving each start's trace facts. *)
  Definition audit_memo_children_correct versions (result : memory_clobber_result N E) : Prop :=
    NoDup (clobber_roots result) /\
    (clobber_complete result = true ->
      (forall start, In start versions -> forall trace,
        memory_walk_trace ET effects mg q start trace -> NoDup trace) /\
      forall v, In v (clobber_roots result) <-> memory_walk_terminal ET effects mg q v /\
        exists start trace, In start versions /\ memory_walk_trace ET effects mg q start trace /\
          memory_trace_last trace = Some v) /\
    forall start, In start versions -> forall trace last,
      memory_walk_trace ET effects mg q start trace -> memory_trace_last trace = Some last ->
      (memory_walk_terminal ET effects mg q last \/ ~ NoDup trace) ->
      exists hit, In hit trace /\ In hit (clobber_roots result).

  (** Every finite backward trace has an actual final version. *)
  Lemma audit_memo_trace_last_exists start trace :
    memory_walk_trace ET effects mg q start trace -> exists last, memory_trace_last trace = Some
      last.
  Proof.
    intro Htrace; induction Htrace as [v|v w rest Hstep Htrace IH].
    - exists v; reflexivity.
    - rewrite (audit_memo_trace_last_cons ET effects mg q w rest v Htrace); exact IH.
  Qed.

  (** A terminal start permits only its singleton trace. *)
  Lemma audit_memo_terminal_trace start trace :
    memory_walk_terminal ET effects mg q start ->
    memory_walk_trace ET effects mg q start trace -> trace = [start].
  Proof.
    intros Hterminal Htrace; inversion Htrace; subst; [reflexivity|].
    exfalso; eapply Hterminal; eassumption.
  Qed.

  (** A cutoff retains its starting version, which intersects every trace. *)
  Lemma audit_memo_cut_correct start :
    audit_memo_result_correct start (MemoryClobberResult [start] false).
  Proof.
    split; [constructor; [cbn; tauto|constructor]|].
    split; [discriminate|].
    intros trace last Htrace Hlast Hend; exists start; split.
    - exact (proj1 (audit_memo_trace_head ET effects mg q start trace Htrace)).
    - left; reflexivity.
  Qed.

  (** A terminal result has one exact root and only singleton traces. *)
  Lemma audit_memo_terminal_correct start :
    memory_walk_terminal ET effects mg q start ->
    audit_memo_result_correct start (MemoryClobberResult [start] true).
  Proof.
    intro Hterminal; split; [constructor; [cbn; tauto|constructor]|].
    split.
    - intro Hcomplete; split.
      + intros trace Htrace; rewrite (audit_memo_terminal_trace start trace Hterminal Htrace).
        constructor; [cbn; tauto|constructor].
      + intro v; split.
        * intros [<-|Hfalse]; [|contradiction].
          split; [exact Hterminal|exists [start]; split; [constructor|reflexivity]].
        * intros [Hend [trace [Htrace Hlast]]].
          rewrite (audit_memo_terminal_trace start trace Hterminal Htrace) in Hlast.
          cbn in Hlast; inversion Hlast; left; reflexivity.
    - intros trace last Htrace Hlast Hend; exists start; split.
      + exact (proj1 (audit_memo_trace_head ET effects mg q start trace Htrace)).
      + left; reflexivity.
  Qed.

  (** A completed entry's exact acyclic terminal semantics supplies the query result contract. *)
  Lemma audit_memo_done_correct start roots :
    NoDup roots ->
    (forall trace, memory_walk_trace ET effects mg q start trace -> NoDup trace) ->
    (forall v, In v roots <-> memory_walk_terminal ET effects mg q v /\
      exists trace, memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace = Some
        v) ->
    audit_memo_result_correct start (MemoryClobberResult roots true).
  Proof.
    intros Hroots Hacyclic Hexact; split; [exact Hroots|].
    split; [intro Hcomplete; split; assumption|].
    intros trace last Htrace Hlast [Hterminal|Hrepeat].
    - exists last; split; [eapply memory_trace_last_in; exact Hlast|].
      apply Hexact; split; [exact Hterminal|exists trace; auto].
    - exfalso; apply Hrepeat; apply Hacyclic; exact Htrace.
  Qed.

  (** The empty child list has no roots and no trace obligations for a start. *)
  Lemma audit_memo_children_nil_correct :
    audit_memo_children_correct [] (MemoryClobberResult [] true).
  Proof.
    split; [constructor|]; split.
    - intro Hcomplete; split; [intros start Hfalse; contradiction|].
      intro v; split; [contradiction|intros [_ [start [trace [Hfalse _]]]]; contradiction].
    - intros start Hfalse; contradiction.
  Qed.

  (** Canonical union preserves child coverage and combines exact completed terminal roots. *)
  Lemma audit_memo_children_cons_correct start rest one tail roots :
    audit_memo_result_correct start one -> audit_memo_children_correct rest tail ->
    NoDup roots ->
    (forall v, In v roots <-> In v (clobber_roots one) \/ In v (clobber_roots tail)) ->
    audit_memo_children_correct (start :: rest)
      (MemoryClobberResult roots (andb (clobber_complete one) (clobber_complete tail))).
  Proof.
    intros [Hone [Honecomplete Honecover]] [Htail [Htailcomplete Htailcover]] Hroots Hunion.
    split; [exact Hroots|]; split.
    - intro Hcomplete; apply Bool.andb_true_iff in Hcomplete as [Hfirst Hrest].
      destruct (Honecomplete Hfirst) as [Hfirstacyclic Hfirstexact].
      destruct (Htailcomplete Hrest) as [Hrestacyclic Hrestexact]; split.
      + intros v [<-|Hin] trace Htrace.
        * apply Hfirstacyclic; exact Htrace.
        * eapply Hrestacyclic; eassumption.
      + intro v; cbn [clobber_roots]; rewrite Hunion, Hfirstexact, Hrestexact; split.
        * intros [[Hterminal [trace [Htrace Hlast]]]|[Hterminal [child [trace [Hin [Htrace
          Hlast]]]]]].
          -- split; [exact Hterminal|exists start, trace; split; [left; reflexivity|split;
            assumption]].
          -- split; [exact Hterminal|exists child, trace; split; [right; exact Hin|split;
            assumption]].
        * intros [Hterminal [child [trace [[<-|Hin] [Htrace Hlast]]]]].
          -- left; split; [exact Hterminal|exists trace; auto].
          -- right; split; [exact Hterminal|exists child, trace; split; [exact Hin|split;
            assumption]].
    - intros child [<-|Hin] trace last Htrace Hlast Hend.
      + destruct (Honecover trace last Htrace Hlast Hend) as [hit [Hhit Hroot]].
        exists hit; split; [exact Hhit|apply Hunion; left; exact Hroot].
      + destruct (Htailcover child Hin trace last Htrace Hlast Hend) as [hit [Hhit Hroot]].
        exists hit; split; [exact Hhit|apply Hunion; right; exact Hroot].
  Qed.

  (** Nonempty branch semantics follow from all actual children, including cycles through the
      parent. *)
  Lemma audit_memo_branch_correct (VE : encoding (memory_version N E))
      start first rest result :
    (forall child, In child (first :: rest) <-> memory_walk_next ET effects mg q start child) ->
    audit_memo_children_correct (first :: rest) result -> audit_memo_result_correct start result.
  Proof.
    intros Hnext [Hroots [Hcomplete Hcover]]; split; [exact Hroots|]; split.
    - intro Hdone; destruct (Hcomplete Hdone) as [Hacyclic Hexact]; split.
      + intros trace Htrace; inversion Htrace as [|parent child suffix Hstep Hsuffix]; subst.
        * constructor; [cbn; tauto|constructor].
        * constructor.
          -- eapply audit_memo_acyclic_parent; [exact Hstep| |exact Hsuffix].
             apply Hacyclic; apply Hnext; exact Hstep.
          -- eapply Hacyclic; [apply Hnext; exact Hstep|exact Hsuffix].
      + intro v; rewrite Hexact; split.
        * intros [Hterminal [child [trace [Hin [Htrace Hlast]]]]].
          split; [exact Hterminal|exists (start :: trace); split].
          -- econstructor; [apply Hnext; exact Hin|exact Htrace].
          -- rewrite (audit_memo_trace_last_cons ET effects mg q child trace start Htrace); exact
            Hlast.
        * intros [Hterminal [trace [Htrace Hlast]]].
          inversion Htrace as [|parent child suffix Hstep Hsuffix]; subst.
          -- cbn in Hlast; inversion Hlast; subst v.
             exfalso; apply (Hterminal first); apply Hnext; left; reflexivity.
          -- split; [exact Hterminal|exists child, suffix; split; [apply Hnext; exact Hstep|]].
             split; [exact Hsuffix|].
             rewrite (audit_memo_trace_last_cons ET effects mg q child suffix start Hsuffix) in
               Hlast.
             exact Hlast.
    - intros trace last Htrace Hlast Hend.
      inversion Htrace as [|parent child suffix Hstep Hsuffix]; subst.
      + cbn in Hlast; inversion Hlast; subst last; destruct Hend as [Hterminal|Hrepeat].
        * exfalso; apply (Hterminal first); apply Hnext; left; reflexivity.
        * exfalso; apply Hrepeat; constructor; [cbn; tauto|constructor].
      + rewrite (audit_memo_trace_last_cons ET effects mg q child suffix start Hsuffix) in Hlast.
        destruct Hend as [Hterminal|Hrepeat].
        * destruct (Hcover child (proj2 (Hnext child) Hstep) suffix last Hsuffix Hlast
            (or_introl Hterminal)) as [hit [Hhit Hroot]].
          exists hit; split; [right; exact Hhit|exact Hroot].
        * destruct (audit_memo_cycle_tail ET effects mg q VE start child suffix Hstep Hsuffix
          Hrepeat)
            as [Htailrepeat|[cycle [Hcycle [Hcyclerepeat Hincl]]]].
          -- destruct (Hcover child (proj2 (Hnext child) Hstep) suffix last Hsuffix Hlast
               (or_intror Htailrepeat)) as [hit [Hhit Hroot]].
             exists hit; split; [right; exact Hhit|exact Hroot].
          -- destruct (audit_memo_trace_last_exists child cycle Hcycle) as [cycle_last Hcyclelast].
             destruct (Hcover child (proj2 (Hnext child) Hstep) cycle cycle_last Hcycle Hcyclelast
               (or_intror Hcyclerepeat)) as [hit [Hhit Hroot]].
             exists hit; split; [apply Hincl; exact Hhit|exact Hroot].
  Qed.
End ResultSemantics.

(** A faithful root union is duplicate-free and denotes membership in either actual input list. *)
Lemma audit_memo_union_members N E CV (VE : encoding (memory_version N E))
    (version_enc : memory_version N E -> positive * list CV) left right roots build enumeration :
  (forall v, fst (version_enc v) = encode VE v) ->
  audit_memo_union version_enc left right = (roots, (build, enumeration)) ->
  NoDup roots /\ forall v, In v roots <-> In v left \/ In v right.
Proof.
  intros Henc Hcall.
  pose proof (audit_memo_union_erases N E CV VE version_enc left right Henc) as Herase.
  rewrite Hcall in Herase; cbn [fst] in Herase; rewrite Herase.
  assert (Hwf : FinSet.wf VE (FinSet.of_list VE (left ++ right))).
  { unfold FinSet.of_list; apply FinSet.wf_fold_add; apply Map.wf_empty. }
  split; [apply (FinSet.elements_nodup VE); exact Hwf|].
  intro v; rewrite (FinSet.elements_spec VE v _ Hwf), FinSet.of_list_spec, in_app_iff; tauto.
Qed.

(** * Persistent cache validity *)

Section CacheSemantics.
  Context {N E T : Type}.
  Variable EN : encoding N.
  Variable EE : encoding E.
  Variable ET : encoding T.
  Variable g : Graph.t N E.
  Variable effects : E -> list (memory_effect T).
  Variable mg : memory_graph N E.

  (** Entry validity retains all scopes' completed-root semantics, not just the current query. *)
  Definition audit_memo_entries_valid
      (memo : Map.t (positive * memory_version N E) (memo_entry N E)) : Prop :=
    Map.wf (memo_key EN EE) memo /\
    (forall key, Map.get (memo_key EN EE) key memo <> Some MemoBusy) /\
    forall q start roots,
      Map.get (memo_key EN EE) (scope_code ET q, start) memo = Some (MemoDone roots) ->
      NoDup roots /\ memory_valid_version g effects mg start /\
      (forall trace, memory_walk_trace ET effects mg q start trace -> NoDup trace) /\
      forall v, In v roots <-> memory_walk_terminal ET effects mg q v /\
        exists trace, memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace =
          Some v.

  (** Storing a complete valid result preserves every other scope's persistent entry. *)
  Lemma audit_memo_store_preserved memo q start result :
    audit_memo_entries_valid memo -> memory_valid_version g effects mg start ->
    audit_memo_result_correct ET effects mg q start result -> clobber_complete result = true ->
    audit_memo_entries_valid
      (Map.set (memo_key EN EE) (scope_code ET q, start) (MemoDone (clobber_roots result)) memo).
  Proof.
    intros [Hwf [Hbusy Hentries]] Hstart [Hroots [Hresult Hcover]] Hcomplete.
    destruct (Hresult Hcomplete) as [Hacyclic Hexact].
    split; [apply Map.wf_set; exact Hwf|]; split.
    - intro key.
      destruct (Pos.eq_dec (encode (memo_key EN EE) key)
        (encode (memo_key EN EE) (scope_code ET q, start))) as [Hequal|Hdifferent].
      + apply (encode_injective (memo_key EN EE)) in Hequal; subst key.
        rewrite Map.get_set_same; discriminate.
      + rewrite Map.get_set_other; [apply Hbusy|].
        intro Hequal; apply Hdifferent; now rewrite Hequal.
    - intros q' start' roots Hget.
      destruct (Pos.eq_dec (encode (memo_key EN EE) (scope_code ET q', start'))
        (encode (memo_key EN EE) (scope_code ET q, start))) as [Hequal|Hdifferent].
      + apply (encode_injective (memo_key EN EE)) in Hequal.
        injection Hequal as Hscope Hstart'; subst start'.
        apply (scope_code_injective T ET) in Hscope; subst q'.
        rewrite Map.get_set_same in Hget; inversion Hget; subst roots.
        exact (conj Hroots (conj Hstart (conj Hacyclic Hexact))).
      + rewrite Map.get_set_other in Hget; [apply Hentries; exact Hget|].
        intro Hequal; apply Hdifferent; now rewrite Hequal.
  Qed.
End CacheSemantics.

(** * Memo tree semantics *)

Scheme audit_memo_semantic_tree_mutual := Induction for audit_memo_tree Sort Prop
with audit_memo_semantic_children_mutual := Induction for audit_memo_children Sort Prop.

Combined Scheme audit_memo_semantic_mutual from audit_memo_semantic_tree_mutual,
  audit_memo_semantic_children_mutual.

Section TreeSemantics.
  Context {N E T CV CK NE : Type}.
  Variable EN : encoding N.
  Variable EE : encoding E.
  Variable ET : encoding T.
  Variable g : Graph.t N E.
  Variable effects : E -> list (memory_effect T).
  Variable mg : memory_graph N E.
  Variable q : memory_scope T.
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.
  Hypothesis Hwf : memory_graph_wf g effects mg.
  Hypothesis Hversion : forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v.
  Hypothesis Hkey : forall key, fst (key_enc key) = encode (memo_key EN EE) key.
  Hypothesis Hnext : forall v, memory_valid_version g effects mg v -> forall child,
    In child (fst (next v)) <-> memory_walk_next ET effects mg q v child.

  (** Every actual successor of a valid version remains in the well-formed memory graph. *)
  Lemma audit_memo_successors_valid v versions events :
    memory_valid_version g effects mg v -> next v = (versions, events) ->
    forall child, In child versions -> memory_valid_version g effects mg child.
  Proof.
    intros Hvalid Hcall child Hin.
    apply (memory_walk_next_valid ET g effects mg q v child Hwf Hvalid).
    apply (Hnext v Hvalid); rewrite Hcall; exact Hin.
  Qed.

  (** A completed lookup recovers the stored roots' full trace semantics. *)
  Lemma audit_memo_cached_correct memo v roots calls :
    audit_map_get key_enc (scope_code ET q, v) memo = (Some (MemoDone roots), calls) ->
    audit_memo_entries_valid EN EE ET g effects mg memo ->
    audit_memo_result_correct ET effects mg q v (MemoryClobberResult roots true).
  Proof.
    intros Hlookup [Hmap [Hbusy Hentries]].
    pose proof (audit_map_get_erases _ _ _ key_enc (memo_key EN EE) (scope_code ET q, v)
      memo (Hkey (scope_code ET q, v))) as Herase.
    rewrite Hlookup in Herase; cbn [fst] in Herase.
    destruct (Hentries q v roots (eq_sym Herase)) as [Hroots [Hstart [Hacyclic Hexact]]].
    apply audit_memo_done_correct; assumption.
  Qed.

  (** A valid cache cannot supply a busy entry to the concrete lookup. *)
  Lemma audit_memo_busy_impossible memo v calls :
    audit_map_get key_enc (scope_code ET q, v) memo = (Some MemoBusy, calls) ->
    audit_memo_entries_valid EN EE ET g effects mg memo -> False.
  Proof.
    intros Hlookup [Hmap [Hbusy Hentries]]; apply (Hbusy (scope_code ET q, v)).
    pose proof (audit_map_get_erases _ _ _ key_enc (memo_key EN EE) (scope_code ET q, v)
      memo (Hkey (scope_code ET q, v))) as Herase.
    rewrite Hlookup in Herase; exact (eq_sym Herase).
  Qed.

  (** An actual counted store retains the all-scope invariant for a complete valid result. *)
  Lemma audit_memo_stored_correct memo v result final calls :
    audit_map_set key_enc (scope_code ET q, v) (MemoDone (clobber_roots result)) memo =
      (final, calls) ->
    audit_memo_entries_valid EN EE ET g effects mg memo -> memory_valid_version g effects mg v ->
    audit_memo_result_correct ET effects mg q v result -> clobber_complete result = true ->
    audit_memo_entries_valid EN EE ET g effects mg final.
  Proof.
    intros Hstore Hmemo Hvalid Hresult Hcomplete.
    pose proof (audit_map_set_erases _ _ _ key_enc (memo_key EN EE) (scope_code ET q, v)
      (MemoDone (clobber_roots result)) memo (Hkey (scope_code ET q, v))) as Herase.
    rewrite Hstore in Herase; cbn [fst] in Herase; rewrite Herase.
    apply audit_memo_store_preserved; assumption.
  Qed.

  (** An empty actual successor list yields a terminal result and a valid completed store. *)
  Lemma audit_memo_terminal_semantics memo v events final calls :
    next v = ([], events) ->
    audit_map_set key_enc (scope_code ET q, v) (MemoDone [v]) memo = (final, calls) ->
    audit_memo_entries_valid EN EE ET g effects mg memo -> memory_valid_version g effects mg v ->
    audit_memo_entries_valid EN EE ET g effects mg final /\
    audit_memo_result_correct ET effects mg q v (MemoryClobberResult [v] true).
  Proof.
    intros Hsuccessors Hstore Hmemo Hvalid.
    assert (Hterminal : memory_walk_terminal ET effects mg q v).
    { intros child Hstep; apply (Hnext v Hvalid) in Hstep; rewrite Hsuccessors in Hstep; exact
      Hstep. }
    pose proof (audit_memo_terminal_correct ET effects mg q v Hterminal) as Hresult.
    split; [|exact Hresult].
    apply (audit_memo_stored_correct memo v (MemoryClobberResult [v] true) final calls);
      assumption || reflexivity.
  Qed.

  (** Nonempty actual successors lift their child summary to the parent's trace contract. *)
  Lemma audit_memo_expanded_correct v first rest events result :
    memory_valid_version g effects mg v -> next v = (first :: rest, events) ->
    audit_memo_children_correct ET effects mg q (first :: rest) result ->
    audit_memo_result_correct ET effects mg q v result.
  Proof.
    intros Hvalid Hsuccessors Hchildren.
    apply (audit_memo_branch_correct ET effects mg q (memory_version_encoding EN EE)
      v first rest result); [|exact Hchildren].
    intro child; specialize (Hnext v Hvalid child); rewrite Hsuccessors in Hnext; exact Hnext.
  Qed.

  (** Actual memo trees preserve all completed entries and establish result semantics. *)
  Lemma audit_memo_tree_semantics :
    (forall active memo v fuel result final remaining events,
      audit_memo_tree version_enc key_enc (scope_code ET q) next active memo v fuel
        result final remaining events ->
      audit_memo_entries_valid EN EE ET g effects mg memo -> memory_valid_version g effects mg v ->
      audit_memo_entries_valid EN EE ET g effects mg final /\
      audit_memo_result_correct ET effects mg q v result) /\
    (forall active memo versions fuel result final remaining events,
      audit_memo_children version_enc key_enc (scope_code ET q) next active memo versions fuel
        result final remaining events ->
      audit_memo_entries_valid EN EE ET g effects mg memo ->
      (forall v, In v versions -> memory_valid_version g effects mg v) ->
      audit_memo_entries_valid EN EE ET g effects mg final /\
      audit_memo_children_correct ET effects mg q versions result).
  Proof.
    apply audit_memo_semantic_mutual.
    - intros active memo v fuel ae Hactive Hmemo Hvalid.
      split; [exact Hmemo|apply audit_memo_cut_correct].
    - intros active memo v fuel ae le roots Hactive Hlookup Hmemo Hvalid.
      split; [exact Hmemo|eapply audit_memo_cached_correct; eassumption].
    - intros active memo v fuel ae le Hactive Hlookup Hmemo Hvalid.
      exfalso; eapply audit_memo_busy_impossible; eassumption.
    - intros active memo v ae le Hactive Hlookup Hmemo Hvalid.
      split; [exact Hmemo|apply audit_memo_cut_correct].
    - intros active memo v fuel ae le ne final se Hactive Hlookup Hsuccessors Hstore Hmemo Hvalid.
      eapply audit_memo_terminal_semantics; eassumption.
    - intros active memo v fuel ae le ne first rest active' adds result middle remaining events
        final se Hactive Hlookup Hsuccessors Hadd Hchildren IH Hcomplete Hstore Hmemo Hvalid.
      destruct (IH Hmemo (audit_memo_successors_valid v (first :: rest) ne Hvalid Hsuccessors))
        as [Hmiddle Hchildrenresult].
      assert (Hresult : audit_memo_result_correct ET effects mg q v result).
      { eapply audit_memo_expanded_correct; eassumption. }
      split; [eapply audit_memo_stored_correct; eassumption|exact Hresult].
    - intros active memo v fuel ae le ne first rest active' adds result final remaining events
        Hactive Hlookup Hsuccessors Hadd Hchildren IH Hcomplete Hmemo Hvalid.
      destruct (IH Hmemo (audit_memo_successors_valid v (first :: rest) ne Hvalid Hsuccessors))
        as [Hfinal Hchildrenresult].
      split; [exact Hfinal|].
      eapply audit_memo_expanded_correct; eassumption.
    - intros active memo fuel Hmemo Hversions.
      split; [exact Hmemo|apply audit_memo_children_nil_correct].
    - intros active memo v vs fuel one middle credit first tail final remaining events roots
        build enumeration Htree IHfirst Hchildren IHtail Hunion Hmemo Hversions.
      destruct (IHfirst Hmemo (Hversions v (or_introl eq_refl))) as [Hmiddle Hone].
      destruct (IHtail Hmiddle (fun child Hin => Hversions child (or_intror Hin))) as [Hfinal
        Htail].
      split; [exact Hfinal|].
      destruct (audit_memo_union_members N E CV (memory_version_encoding EN EE) version_enc
        (clobber_roots one) (clobber_roots tail) roots build enumeration Hversion Hunion)
        as [Hroots Hmembers].
      apply audit_memo_children_cons_correct; assumption.
  Qed.
End TreeSemantics.

(** * Plain public query semantics *)

(** The prepared raw successor list agrees with the memory transition relation at valid versions. *)
Lemma audit_memo_raw_successors_correct N E T (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) effects (mg : memory_graph N E) q v child :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (In child (memory_walk_raw_next EE ET (memory_walk_effect_table EE g effects)
      (pred_edges (prepare EN g)) mg q v) <-> memory_walk_next ET effects mg q v child).
Proof.
  intros Hwf Hvalid.
  pose proof (memory_walk_successors_correct EN EE ET g effects mg q v child Hwf Hvalid) as Hnext.
  unfold memory_walk_successors, memory_walk_index, index_edges in Hnext.
  rewrite memory_result_index_at in Hnext by (apply (memory_versions_exact Hwf); exact Hvalid).
  exact Hnext.
Qed.

(** A plain public query preserves the full memo invariant and establishes its trace semantics. *)
Lemma audit_memory_memo_query_correct N E T (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) effects (mg : memory_graph N E) state q start fuel :
  memo_valid EN EE ET g effects mg state -> memory_graph_wf g effects mg ->
  memory_valid_version g effects mg start ->
  memo_valid EN EE ET g effects mg
    (snd (audit_memory_memo_query EN EE ET g effects mg state q start fuel)) /\
  audit_memo_result_correct ET effects mg q start
    (fst (audit_memory_memo_query EN EE ET g effects mg state q start fuel)).
Proof.
  intros [Hadj [Htable Hentries]] Hwf Hstart.
  set (version_enc := fun v => (encode (memory_version_encoding EN EE) v, @nil unit)).
  set (key_enc := fun key => (encode (memo_key EN EE) key, @nil unit)).
  set (next := fun v => (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
    (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v, @nil unit)).
  destruct (audit_plain_compute_tree (memory_version_encoding EN EE) (memo_key EN EE)
    version_enc key_enc (scope_code ET q) next (fun _ => eq_refl) (fun _ => eq_refl)
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start) as [events Htree].
  assert (Hnext : forall v, memory_valid_version g effects mg v -> forall child,
    In child (fst (next v)) <-> memory_walk_next ET effects mg q v child).
  { intros v Hvalid child; unfold next; cbn [fst]; rewrite Hadj, Htable.
    apply (audit_memo_raw_successors_correct N E T EN EE ET g effects mg q v child Hwf Hvalid). }
  destruct (proj1 (audit_memo_tree_semantics EN EE ET g effects mg q version_enc key_enc next
    Hwf (fun _ => eq_refl) (fun _ => eq_refl) Hnext) FinSet.empty
    (@memo_entries N E T EN g effects mg state) start (Npos fuel) _ _ _ _ Htree Hentries Hstart)
    as [Hfinal Hresult].
  unfold audit_memory_memo_query; cbn [fst snd memo_adjacency memo_effect_index memo_entries].
  split; [exact (conj Hadj (conj Htable Hfinal))|exact Hresult].
Qed.

(** A complete tree leaves its own completed root binding in the exact returned memo. *)
Lemma audit_memo_complete_stored N E CV CK NE version_enc key_enc scope next
    (KE : encoding (positive * memory_version N E)) active memo v fuel result final remaining
      events :
  (forall key, fst (key_enc key) = encode KE key) ->
  @audit_memo_tree N E CV CK NE version_enc key_enc scope next active memo v fuel
    result final remaining events -> clobber_complete result = true ->
  Map.get KE (scope, v) final = Some (MemoDone (clobber_roots result)).
Proof.
  intros Hkey Htree Hcomplete; inversion Htree; subst; cbn in Hcomplete; try discriminate;
    try congruence.
  - match goal with
    | Hcall : audit_map_get key_enc ?key ?input = _ |- _ =>
      pose proof (audit_map_get_erases _ _ _ key_enc KE key input (Hkey key)) as Herase;
      rewrite Hcall in Herase; exact (eq_sym Herase)
    end.
  - match goal with
    | Hcall : audit_map_set key_enc ?key ?value ?input = _ |- _ =>
      pose proof (audit_map_set_erases _ _ _ key_enc KE key value input (Hkey key)) as Herase;
      rewrite Hcall in Herase; cbn [fst] in Herase; rewrite Herase; apply Map.get_set_same
    end.
  - match goal with
    | Hcall : audit_map_set key_enc ?key ?value ?input = _ |- _ =>
      pose proof (audit_map_set_erases _ _ _ key_enc KE key value input (Hkey key)) as Herase;
      rewrite Hcall in Herase; cbn [fst] in Herase; rewrite Herase; apply Map.get_set_same
    end.
Qed.

(** A completed root hit determines the tree result and returns the original persistent memo. *)
Lemma audit_memo_hit_tree N E CV CK NE version_enc key_enc scope next
    (VE : encoding (memory_version N E)) (KE : encoding (positive * memory_version N E))
    memo v fuel result final remaining events roots :
  (forall version, fst (version_enc version) = encode VE version) ->
  (forall key, fst (key_enc key) = encode KE key) ->
  @audit_memo_tree N E CV CK NE version_enc key_enc scope next FinSet.empty memo v fuel
    result final remaining events -> Map.get KE (scope, v) memo = Some (MemoDone roots) ->
  result = MemoryClobberResult roots true /\ final = memo.
Proof.
  intros Hversion Hkey Htree Hget.
  pose proof (audit_finset_mem_erases _ _ version_enc VE v FinSet.empty (Hversion v)) as Hactive.
  rewrite FinSet.mem_empty in Hactive.
  pose proof (audit_map_get_erases _ _ _ key_enc KE (scope, v) memo (Hkey (scope, v))) as Hlookup.
  rewrite Hget in Hlookup.
  inversion Htree; subst;
    repeat match goal with
    | Hcall : audit_finset_mem _ _ _ = _ |- _ => rewrite Hcall in Hactive; clear Hcall
    | Hcall : audit_map_get _ _ _ = _ |- _ => rewrite Hcall in Hlookup; clear Hcall
    end; cbn [fst] in Hactive, Hlookup; try discriminate.
  injection Hlookup as Hroots; subst; split; reflexivity.
Qed.

(** Saved completed entries are exact public hits, including equality of the full returned state. *)
Lemma audit_memory_memo_query_hit : memo_hit_statement (@audit_memory_memo_query).
Proof.
  intros N E T EN EE ET g effects mg state q start fuel roots Hvalid Hget.
  set (version_enc := fun v => (encode (memory_version_encoding EN EE) v, @nil unit)).
  set (key_enc := fun key => (encode (memo_key EN EE) key, @nil unit)).
  set (next := fun v => (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
    (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v, @nil unit)).
  destruct (audit_plain_compute_tree (memory_version_encoding EN EE) (memo_key EN EE)
    version_enc key_enc (scope_code ET q) next (fun _ => eq_refl) (fun _ => eq_refl)
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start) as [events Htree].
  destruct (audit_memo_hit_tree N E unit unit unit version_enc key_enc (scope_code ET q) next
    (memory_version_encoding EN EE) (memo_key EN EE) _ _ _ _ _ _ _ roots
    (fun _ => eq_refl) (fun _ => eq_refl) Htree Hget) as [Hresult Hmemo].
  unfold audit_memory_memo_query; cbn zeta.
  set (run := audit_memo_compute (memory_version_encoding EN EE) (memo_key EN EE)
    (scope_code ET q) (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
      (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q)
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start).
  assert (Hvalue : audit_plain_memo_value run = MemoryClobberResult roots true) by exact Hresult.
  assert (Hcache : audit_plain_memo_cache run = @memo_entries N E T EN g effects mg state)
    by exact Hmemo.
  rewrite Hvalue, Hcache; destruct state; reflexivity.
Qed.

(** Every complete public query installs its result in the exact returned cache. *)
Lemma audit_memory_memo_query_stored : memo_store_complete_statement (@audit_memory_memo_query).
Proof.
  intros N E T EN EE ET g effects mg state q start fuel Hvalid Hwf Hstart.
  set (version_enc := fun v => (encode (memory_version_encoding EN EE) v, @nil unit)).
  set (key_enc := fun key => (encode (memo_key EN EE) key, @nil unit)).
  set (next := fun v => (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
    (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v, @nil unit)).
  destruct (audit_plain_compute_tree (memory_version_encoding EN EE) (memo_key EN EE)
    version_enc key_enc (scope_code ET q) next (fun _ => eq_refl) (fun _ => eq_refl)
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start) as [events Htree].
  unfold audit_memory_memo_query; cbn zeta; intro Hcomplete.
  apply (audit_memo_complete_stored N E unit unit unit version_enc key_enc (scope_code ET q) next
    (memo_key EN EE) _ _ _ _ _ _ _ _ (fun _ => eq_refl) Htree Hcomplete).
Qed.

(** A second query reuses the first complete result and leaves its returned cache unchanged. *)
Lemma audit_memory_memo_query_second : memo_second_query_statement (@audit_memory_memo_query).
Proof.
  intros N E T EN EE ET g effects mg state q start first_fuel second_fuel Hvalid Hwf Hstart.
  pose proof (proj1 (audit_memory_memo_query_correct N E T EN EE ET g effects mg state
    q start first_fuel Hvalid Hwf Hstart)) as Hnextvalid.
  pose proof (audit_memory_memo_query_stored N E T EN EE ET g effects mg state q start first_fuel
    Hvalid Hwf Hstart) as Hstored.
  destruct (audit_memory_memo_query EN EE ET g effects mg state q start first_fuel)
    as [[roots complete] final]; cbn in Hnextvalid, Hstored |- *; intros ->.
  apply audit_memory_memo_query_hit; [exact Hnextvalid|apply Hstored; reflexivity].
Qed.

(** Every dynamic occurrence history meets the query roots along its actual backward trace. *)
Lemma audit_memory_memo_query_execution : memo_execution_statement (@audit_memory_memo_query).
Proof.
  intros N E T EN EE ET g effects mg state q fuel Hvalid Hwf root es e i a Hentry Hpath Hocc.
  destruct (memory_definition_before_occurrence g effects mg Hwf root es e i a Hentry Hpath Hocc)
    as [input [origin [Hprovenance Hhistory]]].
  destruct (memory_walk_provenance_history ET g effects mg q root es _ _ _ Hprovenance)
    as [prefix [Hprefix [Hprefixlast Hprefixterminal]]].
  destruct Hhistory as [Hbefore [Hflow Horigin]].
  destruct (memory_walk_edge_history ET effects mg q e 0 (firstn i (effects e)) _ _ _ _ Hflow
    ltac:(intros j observed Hnth; eapply memory_walk_prefix_position; exact Hnth)
    prefix _ Hprefix Hprefixlast Hprefixterminal) as [trace [Htrace [Hlast Hterminal]]].
  destruct (memory_occurrence_input_valid g effects mg Hwf e i a Hocc)
    as [incoming [Hincoming [Hinputvalid Hrest]]].
  rewrite Hbefore in Hincoming; inversion Hincoming; subst incoming.
  destruct (audit_memory_memo_query_correct N E T EN EE ET g effects mg state q input fuel
    Hvalid Hwf Hinputvalid) as [Hfinal [_ [_ Hcoverage]]].
  destruct (Hcoverage trace _ Htrace Hlast (or_introl Hterminal)) as [hit [Hhit Hroot]].
  exists input, origin, trace, hit; split; [exact Hprovenance|].
  split; [exact (conj Hbefore (conj Hflow Horigin))|].
  split; [exact Htrace|split; [exact Hlast|split; assumption]].
Qed.

(** The fixed plain query preserves memo validity, exact completion, coverage and reusable hits. *)
Theorem audit_memory_memo_query_semantics : audit_memory_memo_query_semantics_statement.
Proof.
  split.
  - intros N E T EN EE ET g effects mg state q start fuel Hvalid Hwf Hstart.
    exact (proj1 (audit_memory_memo_query_correct N E T EN EE ET g effects mg state
      q start fuel Hvalid Hwf Hstart)).
  - split.
    + intros N E T EN EE ET g effects mg state q start fuel Hvalid Hwf Hstart.
      destruct (audit_memory_memo_query_correct N E T EN EE ET g effects mg state
        q start fuel Hvalid Hwf Hstart) as [Hfinal [Hroots [Hresult Hcoverage]]].
      exact Hcoverage.
    + split.
      * intros N E T EN EE ET g effects mg state q start fuel Hvalid Hwf Hstart Hcomplete.
        destruct (audit_memory_memo_query_correct N E T EN EE ET g effects mg state
          q start fuel Hvalid Hwf Hstart) as [Hfinal [Hroots [Hresult Hcoverage]]].
        exact (proj2 (Hresult Hcomplete)).
      * split; [exact audit_memory_memo_query_execution|].
        split; [exact audit_memory_memo_query_hit|].
        split; [exact audit_memory_memo_query_stored|exact audit_memory_memo_query_second].
Qed.
