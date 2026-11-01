(** * Memo execution projection and source bounds

    Erasing callback bodies preserves results, persistent memo states and binary credit.
    For example, changing only encoder traces leaves a completed hit's credit unchanged.
    Builds on: concrete execution trees, plain computation trees and input-budget adequacy. *)

From Stdlib Require Import List NArith PArith Wf_nat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditTrie CollectionsAuditElements.
From Galois.Graph Require Import GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryEncodingAdequacy
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryRawNextAdequacy AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryInputBudgetAdequacy AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoAdequacy
  AnalysesAuditMemoryMemoPlain AnalysesAuditMemoryMemoPlainAdequacy
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteAdequacy
  AnalysesAuditMemoryMemoWhole AnalysesAuditMemoryMemoWholeAdequacy
  AnalysesAuditMemoryMemoExecuteBound.
Import List.ListNotations.

(** * Primitive observer projections *)

(** Finite-set membership depends on encoder codes and retains arbitrary source traces. *)
Lemma audit_memo_mem_projection V A B (enc : V -> positive * list A)
    (enc' : V -> positive * list B) active v :
  fst (enc v) = fst (enc' v) ->
  fst (audit_finset_mem enc v active) = fst (audit_finset_mem enc' v active).
Proof.
  unfold audit_finset_mem; destruct (enc v) as [code calls], (enc' v) as [code' calls']; cbn [fst].
  intros ->; destruct (audit_map_code_get code' active); reflexivity.
Qed.

(** Binary credit width cannot increase when the numeric credit decreases. *)
Lemma audit_memo_width_monotone first second :
  N.to_nat first <= N.to_nat second ->
  audit_memo_credit_width first <= audit_memo_credit_width second.
Proof.
  intros Hle; destruct first as [|first], second as [|second];
    cbn [audit_memo_credit_width N.to_nat] in *; try lia.
  destruct (Pos.eq_dec first second) as [->|Hdifferent]; [lia|].
  apply Pos.size_nat_monotone; apply Pos2Nat.inj_lt.
  assert (Hne : Pos.to_nat first <> Pos.to_nat second).
  { intro Hequal; apply Hdifferent; apply Pos2Nat.inj; exact Hequal. }
  lia.
Qed.

(** Equal first projections retain a possibly different observer body at the same output. *)
Lemma audit_memo_return_same {A B C} (left : A * B) (right : A * C) result body :
  left = (result, body) -> fst left = fst right -> exists body', right = (result, body').
Proof.
  intros Hleft Hresult; destruct right as [result' body']; exists body'.
  rewrite Hleft in Hresult; cbn in Hresult; subst result'; reflexivity.
Qed.

(** Persistent set insertion depends on codes, including for encoders without injectivity laws. *)
Lemma audit_memo_add_projection V A B (enc : V -> positive * list A)
    (enc' : V -> positive * list B) active v :
  fst (enc v) = fst (enc' v) ->
  fst (audit_finset_add enc v active) = fst (audit_finset_add enc' v active).
Proof.
  unfold audit_finset_add; destruct (enc v) as [code calls], (enc' v) as [code' calls']; cbn [fst].
  intros ->; destruct (audit_trie_set code' (v, tt) active); reflexivity.
Qed.

(** Memo lookup depends on its actual composite-key code. *)
Lemma audit_memo_get_projection K V A B (enc : K -> positive * list A)
    (enc' : K -> positive * list B) (memo : Map.t K V) key :
  fst (enc key) = fst (enc' key) ->
  fst (audit_map_get enc key memo) = fst (audit_map_get enc' key memo).
Proof.
  unfold audit_map_get; destruct (enc key) as [code calls], (enc' key) as [code' calls']; cbn [fst].
  intros ->; destruct (audit_map_code_get code' memo); reflexivity.
Qed.

(** Memo insertion retains the same supplied key and value at equal codes. *)
Lemma audit_memo_set_projection K V A B (enc : K -> positive * list A)
    (enc' : K -> positive * list B) (memo : Map.t K V) key value :
  fst (enc key) = fst (enc' key) ->
  fst (audit_map_set enc key value memo) = fst (audit_map_set enc' key value memo).
Proof.
  unfold audit_map_set; destruct (enc key) as [code calls], (enc' key) as [code' calls']; cbn [fst].
  intros ->; destruct (audit_trie_set code' (key, value) memo); reflexivity.
Qed.

(** Set construction threads equal persistent accumulators when all actual codes agree. *)
Lemma audit_memo_fold_projection V A B (enc : V -> positive * list A)
    (enc' : V -> positive * list B) versions :
  (forall v, fst (enc v) = fst (enc' v)) -> forall active,
  fst (audit_finset_fold enc versions active) = fst (audit_finset_fold enc' versions active).
Proof.
  intro Henc; induction versions as [|v rest IH]; intro active; cbn [audit_finset_fold];
    [reflexivity|].
  pose proof (audit_memo_add_projection V A B enc enc' active v (Henc v)) as Hadd.
  destruct (audit_finset_add enc v active) as [middle calls].
  destruct (audit_finset_add enc' v active) as [middle' calls']; cbn [fst] in Hadd; subst middle'.
  specialize (IH middle).
  destruct (audit_finset_fold enc rest middle), (audit_finset_fold enc' rest middle); exact IH.
Qed.

(** Canonical root union depends on actual codes and not on its observer bodies. *)
Lemma audit_memo_union_projection N E A B
    (enc : memory_version N E -> positive * list A)
    (enc' : memory_version N E -> positive * list B) left right :
  (forall v, fst (enc v) = fst (enc' v)) ->
  fst (audit_memo_union enc left right) = fst (audit_memo_union enc' left right).
Proof.
  intro Henc; unfold audit_memo_union, audit_finset_of_list.
  pose proof (audit_memo_fold_projection _ A B enc enc' (left ++ right) Henc FinSet.empty) as Hset.
  destruct (audit_finset_fold enc (left ++ right) FinSet.empty) as [set calls].
  destruct (audit_finset_fold enc' (left ++ right) FinSet.empty) as [set' calls']; cbn [fst] in
    Hset.
  subst set'; destruct (audit_finset_elements set); reflexivity.
Qed.

(** The separate plain producer and counted producer have identical result, cache and credit. *)
Theorem audit_memo_execute_plain_erases : audit_memo_execute_plain_erases_statement.
Proof.
  intros N E CV CK NE version_encoding key_encoding version_enc key_enc next scope fuel active
    memo start Hversion Hkey.
  pose proof (audit_memo_execute_tree N E CV CK NE version_enc key_enc scope next
    fuel active memo start) as Hcounted.
  destruct (audit_plain_compute_tree version_encoding key_encoding version_enc key_enc scope next
    Hversion Hkey fuel active memo start) as [events Hplain].
  pose proof (audit_memo_tree_deterministic N E CV CK NE version_enc key_enc scope next
    active memo start fuel _ _ _ _ _ _ _ _ Hcounted Hplain) as [Hvalue [Hcache [Hcredit _]]].
  exact (conj Hvalue (conj Hcache Hcredit)).
Qed.

(** * Tree projection *)

Section TreeProjection.
  Context {N E CV CK NE CV' CK' NE' : Type}.
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.
  Variable version_enc' : memory_version N E -> positive * list CV'.
  Variable key_enc' : positive * memory_version N E -> positive * list CK'.
  Variable next' : memory_version N E -> list (memory_version N E) * list NE'.
  Variable scope : positive.
  Hypothesis Hversion : forall v, fst (version_enc v) = fst (version_enc' v).
  Hypothesis Hkey : forall key, fst (key_enc key) = fst (key_enc' key).
  Hypothesis Hnext : forall v, fst (next v) = fst (next' v).

  (** The active and memo probes retain both results while changing only their observer bodies. *)
  Lemma audit_memo_probes_projection active
      (memo : Map.t (positive * memory_version N E) (memo_entry N E)) v flag entry ae le :
    audit_finset_mem version_enc v active = (flag, ae) ->
    audit_map_get key_enc (scope, v) memo = (entry, le) ->
    exists ae' le', audit_finset_mem version_enc' v active = (flag, ae') /\
      audit_map_get key_enc' (scope, v) memo = (entry, le').
  Proof.
    intros Hactive Hlookup.
    destruct (audit_memo_return_same _ _ _ _ Hactive
      (audit_memo_mem_projection _ _ _ version_enc version_enc' active v (Hversion v)))
      as [ae' Hactive'].
    destruct (audit_memo_return_same _ _ _ _ Hlookup
      (audit_memo_get_projection _ _ _ _ key_enc key_enc' memo (scope, v) (Hkey (scope, v))))
      as [le' Hlookup'].
    exists ae', le'; split; assumption.
  Qed.

  (** A terminal expansion transports its exact persistent completed store. *)
  Lemma audit_memo_terminal_projection active memo v fuel ae le ne final se :
    audit_finset_mem version_enc v active = (false, ae) ->
    audit_map_get key_enc (scope, v) memo = (None, le) -> next v = ([], ne) ->
    audit_map_set key_enc (scope, v) (MemoDone [v]) memo = (final, se) ->
    exists events', audit_memo_tree version_enc' key_enc' scope next' active memo v (N.succ fuel)
      (MemoryClobberResult [v] true) final fuel events'.
  Proof.
    intros Hactive Hlookup Hsuccessors Hstore.
    destruct (audit_memo_probes_projection active memo v false None ae le Hactive Hlookup)
      as [ae' [le' [Hactive' Hlookup']]].
    destruct (audit_memo_return_same _ _ _ _ Hsuccessors (Hnext v)) as [ne' Hsuccessors'].
    destruct (audit_memo_return_same _ _ _ _ Hstore
      (audit_memo_set_projection _ _ _ _ key_enc key_enc' memo (scope, v) (MemoDone [v])
        (Hkey (scope, v)))) as [se' Hstore'].
    eexists; eapply AuditMemoTreeTerminal; eassumption.
  Qed.

  (** A projected child tree determines the branch's unchanged result, credit and conditional
      store. *)
  Lemma audit_memo_branch_projection active memo v fuel ae le ne first rest active' adds
      result middle remaining children_events :
    audit_finset_mem version_enc v active = (false, ae) ->
    audit_map_get key_enc (scope, v) memo = (None, le) -> next v = (first :: rest, ne) ->
    audit_finset_add version_enc v active = (active', adds) ->
    audit_memo_children version_enc' key_enc' scope next' active' memo (first :: rest) fuel
      result middle remaining children_events ->
    exists events', audit_memo_tree version_enc' key_enc' scope next' active memo v (N.succ fuel)
      result (if clobber_complete result then
        fst (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) middle) else middle)
      remaining events'.
  Proof.
    intros Hactive Hlookup Hsuccessors Hadd Hchildren'.
    destruct (audit_memo_probes_projection active memo v false None ae le Hactive Hlookup)
      as [ae' [le' [Hactive' Hlookup']]].
    destruct (audit_memo_return_same _ _ _ _ Hsuccessors (Hnext v)) as [ne' Hsuccessors'].
    destruct (audit_memo_return_same _ _ _ _ Hadd
      (audit_memo_add_projection _ _ _ version_enc version_enc' active v (Hversion v)))
      as [adds' Hadd'].
    destruct (clobber_complete result) eqn:Hcomplete.
    - destruct (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) middle)
        as [final se] eqn:Hstore.
      destruct (audit_memo_return_same _ _ _ _ Hstore
        (audit_memo_set_projection _ _ _ _ key_enc key_enc' middle (scope, v)
          (MemoDone (clobber_roots result)) (Hkey (scope, v)))) as [se' Hstore'].
      cbn [fst]; eexists; eapply AuditMemoTreeBranchComplete; eassumption.
    - eexists; eapply AuditMemoTreeBranchIncomplete; eassumption.
  Qed.

  (** Encoder-body changes transport every tree while retaining all semantic and state endpoints. *)
  Lemma audit_memo_tree_projection :
    (forall active memo v fuel result final remaining events,
      audit_memo_tree version_enc key_enc scope next active memo v fuel result final remaining
        events ->
      exists events', audit_memo_tree version_enc' key_enc' scope next' active memo v fuel
        result final remaining events') /\
    (forall active memo vs fuel result final remaining events,
      audit_memo_children version_enc key_enc scope next active memo vs fuel result final remaining
        events ->
      exists events', audit_memo_children version_enc' key_enc' scope next' active memo vs fuel
        result final remaining events').
  Proof.
    apply audit_memo_mutual.
    - intros active memo v fuel ae Hactive.
      destruct (audit_memo_return_same _ _ _ _ Hactive
        (audit_memo_mem_projection _ _ _ version_enc version_enc' active v (Hversion v)))
        as [ae' Hactive'].
      eexists; constructor; exact Hactive'.
    - intros active memo v fuel ae le roots Hactive Hlookup.
      destruct (audit_memo_probes_projection active memo v false (Some (MemoDone roots)) ae le
        Hactive Hlookup) as [ae' [le' [Hactive' Hlookup']]].
      eexists; eapply AuditMemoTreeDone; eassumption.
    - intros active memo v fuel ae le Hactive Hlookup.
      destruct (audit_memo_probes_projection active memo v false (Some MemoBusy) ae le Hactive
        Hlookup)
        as [ae' [le' [Hactive' Hlookup']]].
      eexists; eapply AuditMemoTreeBusy; eassumption.
    - intros active memo v ae le Hactive Hlookup.
      destruct (audit_memo_probes_projection active memo v false None ae le Hactive Hlookup)
        as [ae' [le' [Hactive' Hlookup']]].
      eexists; eapply AuditMemoTreeFuel; eassumption.
    - intros active memo v fuel ae le ne final se Hactive Hlookup Hsuccessors Hstore.
      eapply audit_memo_terminal_projection; eassumption.
    - intros active memo v fuel ae le ne first rest active' adds result middle remaining events
        final se Hactive Hlookup Hsuccessors Hadd Hchildren [events' Hchildren'] Hcomplete Hstore.
      pose proof (audit_memo_branch_projection active memo v fuel ae le ne first rest active' adds
        result middle remaining events' Hactive Hlookup Hsuccessors Hadd Hchildren') as Hbranch.
      rewrite Hcomplete, Hstore in Hbranch; exact Hbranch.
    - intros active memo v fuel ae le ne first rest active' adds result final remaining events
        Hactive Hlookup Hsuccessors Hadd Hchildren [events' Hchildren'] Hcomplete.
      pose proof (audit_memo_branch_projection active memo v fuel ae le ne first rest active' adds
        result final remaining events' Hactive Hlookup Hsuccessors Hadd Hchildren') as Hbranch.
      rewrite Hcomplete in Hbranch; exact Hbranch.
    - intros active memo fuel; eexists; constructor.
    - intros active memo v vs fuel one middle credit first tail final remaining events roots
        build enumeration Htree [first' Htree'] Hchildren [events' Hchildren'] Hunion.
      pose proof (audit_memo_union_projection N E CV CV' version_enc version_enc'
        (clobber_roots one) (clobber_roots tail) Hversion) as Hroots.
      destruct (audit_memo_union version_enc' (clobber_roots one) (clobber_roots tail))
        as [roots' [build' enumeration']] eqn:Hunion'.
      rewrite Hunion in Hroots; cbn [fst] in Hroots; subst roots'.
      eexists; econstructor; eassumption.
  Qed.
End TreeProjection.

(** Any two observer bodies with equal codes and successors have identical execution endpoints. *)
Theorem audit_memo_execute_projection : audit_memo_execute_projection_statement.
Proof.
  intros N E CV CK NE CV' CK' NE' version_enc key_enc next version_enc' key_enc' next'
    scope fuel active memo start Hversion Hkey Hnext.
  pose proof (audit_memo_execute_tree N E CV CK NE version_enc key_enc scope next
    fuel active memo start) as Hfirst.
  destruct (proj1 (audit_memo_tree_projection version_enc key_enc next version_enc' key_enc' next'
    scope Hversion Hkey Hnext) active memo start fuel _ _ _ _ Hfirst) as [events Hprojection].
  pose proof (audit_memo_execute_tree N E CV' CK' NE' version_enc' key_enc' scope next'
    fuel active memo start) as Hsecond.
  destruct (audit_memo_tree_deterministic N E CV' CK' NE' version_enc' key_enc' scope next'
    active memo start fuel _ _ _ _ _ _ _ _ Hprojection Hsecond)
    as [Hvalue [Hcache [Hcredit _]]].
  exact (conj Hvalue (conj Hcache Hcredit)).
Qed.

(** * Binary control costs *)

Section ControlBound.
  Context {N E CV CK NE : Type}.
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable scope : positive.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.

  (** Each child-list frame is paid by its union event, with one final empty-list frame. *)
  Lemma audit_memo_children_control_bound bound
      (recur : forall credit, N.to_nat credit < N.to_nat bound ->
        FinSet.t (memory_version N E) -> Map.t (positive * memory_version N E) (memo_entry N E) ->
        memory_version N E ->
        {run : audit_memo_execution N E CV CK NE | audit_memo_credit_bounded credit run})
      active versions width :
    (forall credit Hcredit memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      length (audit_memo_control_events run) <=
        (4 + width) * length (audit_memo_body_events run)) ->
    forall memo credit Hcredit,
      let run := proj1_sig (audit_memo_execute_children version_enc bound recur active memo versions
        credit Hcredit) in
      length (audit_memo_control_events run) <=
        (4 + width) * length (audit_memo_body_events run) + 1.
  Proof.
    intro Hrecur; induction versions as [|v rest IH]; intros memo credit Hcredit.
    - cbn [audit_memo_execute_children proj1_sig audit_memo_control_events
        audit_memo_body_events length]; lia.
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
      destruct (audit_memo_union version_enc (clobber_roots (audit_memo_value one))
        (clobber_roots (audit_memo_value tail))) as [roots [build enumeration]].
      cbn [proj1_sig audit_memo_control_events audit_memo_body_events] in IH |- *.
      repeat rewrite length_app; cbn [length]; repeat rewrite length_app; nia.
  Qed.

  (** The body charges its binary predecessor and all actual recursive child control frames. *)
  Lemma audit_memo_body_control_bound fuel recur width :
    audit_memo_credit_width fuel <= width ->
    (forall credit Hcredit active memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      length (audit_memo_control_events run) <=
        (4 + width) * length (audit_memo_body_events run)) ->
    forall active memo v,
      let run := proj1_sig (audit_memo_execute_body version_enc key_enc scope next
        fuel recur active memo v) in
      length (audit_memo_control_events run) <=
        (4 + width) * length (audit_memo_body_events run).
  Proof.
    intros Hwidth Hrecur active memo v.
    pose proof (proj2 (audit_memo_pred_correct fuel)) as Hpred.
    unfold audit_memo_execute_body.
    destruct (audit_finset_mem version_enc v active) as [flag ae]; destruct flag.
    - cbn; nia.
    - destruct (audit_map_get key_enc (scope, v) memo) as [[[|roots]|] le].
      + cbn; nia.
      + cbn; nia.
      + destruct fuel as [|positive_fuel].
        * cbn; nia.
        * cbn [audit_memo_credit_width] in Hwidth.
          destruct (next v) as [[|first rest] ne].
          -- destruct (audit_map_set key_enc (scope, v) (MemoDone [v]) memo) as [final se].
             cbn [proj1_sig audit_memo_control_events audit_memo_body_events length].
             nia.
          -- destruct (audit_finset_add version_enc v active) as [active' adds].
             match goal with
             | |- context [audit_memo_execute_children _ _ _ _ _ _ _ ?proof] =>
               pose proof (audit_memo_children_control_bound (Npos positive_fuel) recur active'
                 (first :: rest) width (fun credit Hcredit memo' v' =>
                   Hrecur credit Hcredit active' memo' v') memo (N.pred (Npos positive_fuel))
                 proof) as Hchildren;
               destruct (audit_memo_execute_children version_enc (Npos positive_fuel) recur
                 active' memo (first :: rest) (N.pred (Npos positive_fuel)) proof)
                 as [children Hbound]
             end.
             cbn [proj1_sig] in Hchildren |- *.
             destruct (clobber_complete (audit_memo_value children)).
             ++ destruct (audit_map_set key_enc (scope, v)
                  (MemoDone (clobber_roots (audit_memo_value children)))
                  (audit_memo_cache children)) as [final se].
                cbn [proj1_sig audit_memo_control_events audit_memo_body_events].
                repeat rewrite length_app; cbn [length]; repeat rewrite length_app; nia.
             ++ cbn [proj1_sig audit_memo_control_events audit_memo_body_events].
                repeat rewrite length_app; cbn [length]; repeat rewrite length_app; nia.
  Qed.

  (** Accessibility induction bounds every actual control event by the original credit width. *)
  Lemma audit_memo_fix_control_bound fuel (access : Acc (ltof BinNums.N N.to_nat) fuel) :
    forall limit, N.to_nat fuel <= N.to_nat limit -> forall active memo v,
      let run := proj1_sig (Fix_F
        (fun credit => forall active memo v,
          {run : audit_memo_execution N E CV CK NE | audit_memo_credit_bounded credit run})
        (audit_memo_execute_body version_enc key_enc scope next) access active memo v) in
      length (audit_memo_control_events run) <=
        (4 + audit_memo_credit_width limit) * length (audit_memo_body_events run).
  Proof.
    revert fuel access; fix IH 2; intros fuel [smaller] limit Hle active memo v.
    cbn [Fix_F]; apply audit_memo_body_control_bound.
    - apply audit_memo_width_monotone; exact Hle.
    - intros credit Hcredit active' memo' v'; apply IH.
      unfold ltof in Hcredit; lia.
  Qed.

  (** The concrete executor's control trace is bounded at its original binary fuel width. *)
  Lemma audit_memo_execute_control_bound fuel active memo v :
    let run := audit_memo_execute version_enc key_enc scope next fuel active memo v in
    length (audit_memo_control_events run) <=
      (4 + audit_memo_credit_width fuel) * length (audit_memo_body_events run).
  Proof.
    unfold audit_memo_execute, Fix; apply audit_memo_fix_control_bound; lia.
  Qed.
End ControlBound.

(** Whole executor work includes the concrete binary control and the independent memo recurrence. *)
Theorem audit_memo_execute_whole_input_bound : audit_memo_execute_whole_input_bound_statement.
Proof.
  intros N E CV CK NE version_enc key_enc next scope version_work key_work next_work
    version_budget key_budget next_budget fuel active memo start Hversion Hkey Hnext.
  pose proof (audit_memo_execute_tree N E CV CK NE version_enc key_enc scope next
    fuel active memo start) as Htree.
  destruct (audit_memo_whole_input_bound N E CV CK NE version_enc key_enc scope next
    version_budget key_budget next_budget version_work key_work next_work Hversion Hkey Hnext
    active memo start fuel _ _ _ _ Htree) as [budget [Hbudget Hwork]].
  exists budget; split; [exact Hbudget|].
  pose proof (audit_memo_execute_control_bound version_enc key_enc scope next fuel active memo
    start)
    as Hcontrol.
  unfold audit_memo_execution_source_work, audit_memo_source_work in *; nia.
Qed.

(** * Public query erasure and source bounds *)

(** The counted query preserves the public result and every returned memo entry. *)
Theorem audit_memory_memo_query_counted_erases : audit_memory_memo_query_counted_erases_statement.
Proof.
  intros N E T CN CE SE IE OE BE EN EE ET node_enc edge_enc site_enc g effects mg state
    incoming operand before q start fuel Hnode Hedge Hsite Hincoming Hoperand Hbefore.
  set (version_enc := audit_memory_version_encode node_enc edge_enc).
  set (key_enc := audit_memory_memo_key_encode node_enc edge_enc).
  set (next := audit_memory_raw_next edge_enc site_enc
    (@memo_effect_index N E T EN g effects mg state) incoming operand before q).
  set (original_next := fun v =>
    (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
      (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v, @nil unit)).
  assert (Hversion : forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v).
  { intro v; apply audit_memory_version_encode_erases; assumption. }
  assert (Hkey : forall key, fst (key_enc key) = encode (memo_key EN EE) key).
  { intro key; apply audit_memory_memo_key_encode_erases; assumption. }
  assert (Hnext : forall v, fst (next v) = fst (original_next v)).
  { intro v; unfold next, original_next; cbn [fst].
    rewrite (audit_memory_raw_next_erases N E T CE SE IE OE BE EE ET edge_enc site_enc
      _ incoming operand before mg q v Hedge Hsite Hoperand Hbefore).
    destruct v; cbn [memory_walk_raw_next]; try reflexivity.
    rewrite Hincoming; reflexivity. }
  pose proof (audit_memo_execute_projection N E _ _ _ _ _ _ version_enc key_enc next
    version_enc key_enc original_next (scope_code ET q) (Npos fuel) FinSet.empty
    (@memo_entries N E T EN g effects mg state) start
    (fun _ => eq_refl) (fun _ => eq_refl) Hnext) as Hprojection.
  pose proof (audit_memo_execute_plain_erases N E _ _ _ (memory_version_encoding EN EE)
    (memo_key EN EE) version_enc key_enc original_next (scope_code ET q) (Npos fuel)
    FinSet.empty (@memo_entries N E T EN g effects mg state) start Hversion Hkey) as Hplain.
  pose proof (audit_memory_scope_encode_erases T SE ET site_enc q Hsite) as Hscope.
  unfold audit_memory_memo_query_counted, audit_memory_memo_query.
  destruct (audit_memory_scope_encode site_enc q) as [code calls]; cbn [fst] in Hscope.
  subst code; cbn [snd fst memo_entries].
  destruct Hprojection as [Hvalue [Hcache Hcredit]].
  destruct Hplain as [Hplainvalue [Hplaincache Hplaincredit]].
  change (audit_memo_value (audit_memo_execute version_enc key_enc (scope_code ET q) next
      (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start) =
    audit_plain_memo_value (audit_memo_compute (memory_version_encoding EN EE) (memo_key EN EE)
      (scope_code ET q) (fun v => fst (original_next v)) (Npos fuel) FinSet.empty
      (@memo_entries N E T EN g effects mg state) start) /\
    audit_memo_cache (audit_memo_execute version_enc key_enc (scope_code ET q) next
      (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start) =
    audit_plain_memo_cache (audit_memo_compute (memory_version_encoding EN EE) (memo_key EN EE)
      (scope_code ET q) (fun v => fst (original_next v)) (Npos fuel) FinSet.empty
      (@memo_entries N E T EN g effects mg state) start)).
  split; congruence.
Qed.

(** Whole query work discharges concrete encoder, raw-successor and binary-control costs. *)
Theorem audit_memory_memo_query_whole_input_bound :
  audit_memory_memo_query_whole_input_bound_statement.
Proof.
  intros N E T CN CE SE IE OE BE EN node_enc edge_enc site_enc g effects mg state incoming
    operand before node_work edge_work site_work incoming_work operand_work before_work
    node_budget edge_budget site_budget incoming_budget operand_budget before_budget q start fuel
    Hnode Hedge Hsite Hincoming Hoperand Hbefore.
  pose proof (audit_memory_encoders_input_bound N E T CN CE SE node_enc edge_enc site_enc
    node_work edge_work site_work node_budget edge_budget site_budget Hnode Hedge Hsite)
    as [Hversion [_ [Hscope Hkey]]].
  pose proof (audit_memo_execute_whole_input_bound N E _ _ _
    (audit_memory_version_encode node_enc edge_enc) (audit_memory_memo_key_encode node_enc edge_enc)
    (audit_memory_raw_next edge_enc site_enc (@memo_effect_index N E T EN g effects mg state)
      incoming operand before q) (fst (audit_memory_scope_encode site_enc q))
    (audit_memory_version_work node_work edge_work) (audit_memory_memo_key_work node_work edge_work)
    (audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work)
    (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
    (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
    (@audit_raw_next_input_budget N E T CE SE IE OE BE edge_enc site_enc
      (@memo_effect_index N E T EN g effects mg state) incoming before edge_budget site_budget
      incoming_budget operand_budget before_budget q)
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start Hversion Hkey
    (fun v => audit_raw_next_whole_input_bound N E T CE SE IE OE BE edge_enc site_enc
      _ incoming operand before edge_work site_work incoming_work operand_work before_work
      edge_budget site_budget incoming_budget operand_budget before_budget q v
      Hedge Hsite Hincoming Hoperand Hbefore)) as Hbound.
  specialize (Hscope q).
  unfold audit_memory_memo_query_counted.
  destruct (audit_memory_scope_encode site_enc q) as [code calls].
  cbn [fst] in Hbound; destruct Hbound as [budget [Hbudget Hwork]].
  exists budget; split; [exact Hbudget|].
  unfold audit_memo_credit_width in Hwork; cbn [fst snd] in Hscope, Hwork |- *; lia.
Qed.

(** The public plain query realizes arbitrary faithful observer trees at its exact saved indexes. *)
Theorem audit_memory_memo_query_execution_contract :
  audit_memory_memo_query_execution_contract_statement.
Proof.
  intros N E T CV CK NE EN EE ET g effects mg state q start fuel version_enc key_enc next
    Hversion Hkey Hnext.
  set (plain_next := fun v =>
    (memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
      (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v, @nil unit)).
  destruct (audit_plain_compute_tree (memory_version_encoding EN EE) (memo_key EN EE)
    version_enc key_enc (scope_code ET q) plain_next Hversion Hkey (Npos fuel) FinSet.empty
    (@memo_entries N E T EN g effects mg state) start) as [events Htree].
  destruct (proj1 (audit_memo_tree_projection version_enc key_enc plain_next
    version_enc key_enc next (scope_code ET q) (fun _ => eq_refl) (fun _ => eq_refl)
    (fun v => eq_sym (Hnext v))) FinSet.empty
    (@memo_entries N E T EN g effects mg state) start (Npos fuel) _ _ _ _ Htree)
    as [events' Htree'].
  unfold audit_memory_memo_query.
  cbn zeta.
  eexists; exists events'; split; [exact Htree'|split; reflexivity].
Qed.
