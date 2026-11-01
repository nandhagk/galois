(** * Whole memo input-budget adequacy

    Independent input recurrences pay the actual probes, expansions, unions and persistent stores.
    For example, a completed hit pays two probes and no successor expansion.
    Builds on: memo trees and concrete map, finite-set and enumeration adequacy. *)

From Stdlib Require Import List NArith Lia.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet CollectionsAuditMap
  CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditMapAdequacy
  CollectionsAuditFinSetAdequacy CollectionsAuditElementsAdequacy CollectionsAuditDenseAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoAdequacy
  AnalysesAuditMemoryMemoWhole AnalysesAuditMemoryEncoding AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryInputBudgetAdequacy.
Import List.ListNotations.

(** * Trace work and independent recurrence determinacy *)

(** Primitive work is additive across the exact concatenated event segments. *)
Lemma audit_memo_primitive_work_app N E CV CK NE version_work key_work next_work
    (left right : list (audit_memo_event N E CV CK NE)) :
  audit_memo_primitive_work version_work key_work next_work (left ++ right) =
    audit_memo_primitive_work version_work key_work next_work left +
    audit_memo_primitive_work version_work key_work next_work right.
Proof.
  induction left as [|event rest IH]; cbn; [reflexivity|].
  destruct event; cbn; rewrite IH; lia.
Qed.

Scheme audit_memo_budget_tree_mutual := Induction for audit_memo_input_budget_run Sort Prop
with audit_memo_budget_children_mutual :=
  Induction for audit_memo_children_input_budget_run Sort Prop.

Combined Scheme audit_memo_budget_mutual from audit_memo_budget_tree_mutual,
  audit_memo_budget_children_mutual.

(** Equal branch discriminants identify their constructor payloads and binary fuel. *)
Local Ltac audit_memo_budget_inputs :=
  repeat match goal with
  | Hfuel : N.succ ?first = N.succ ?second |- _ =>
    apply N.succ_inj in Hfuel; subst
  | Hleft : ?call = ?left, Hright : ?call = ?right |- _ =>
    let Hequal := fresh "Hequal" in
    assert (Hequal : left = right) by congruence;
    clear Hright; inversion Hequal; subst; clear Hequal
  end.

(** The independent recurrence determines its output state and cost from its original inputs. *)
Lemma audit_memo_budget_unique N E CV CK NE version_enc key_enc scope next
    version_budget key_budget next_budget :
  (forall active memo v fuel result final remaining cost,
    @audit_memo_input_budget_run N E CV CK NE version_enc key_enc scope next
      version_budget key_budget next_budget active memo v fuel result final remaining cost ->
    forall result' final' remaining' cost',
      audit_memo_input_budget_run version_enc key_enc scope next
        version_budget key_budget next_budget active memo v fuel result' final' remaining' cost' ->
      result = result' /\ final = final' /\ remaining = remaining' /\ cost = cost') /\
  (forall active memo vs fuel result final remaining cost,
    @audit_memo_children_input_budget_run N E CV CK NE version_enc key_enc scope next
      version_budget key_budget next_budget active memo vs fuel result final remaining cost ->
    forall result' final' remaining' cost',
      audit_memo_children_input_budget_run version_enc key_enc scope next
        version_budget key_budget next_budget active memo vs fuel result' final' remaining' cost' ->
      result = result' /\ final = final' /\ remaining = remaining' /\ cost = cost').
Proof.
  apply audit_memo_budget_mutual; intros;
    match goal with
    | |- _ = ?result /\ _ = ?final /\ _ = ?credit /\ _ = ?cost =>
      match goal with
      | Hrun : audit_memo_input_budget_run _ _ _ _ _ _ _ _ _ _ _ result final credit cost |- _ =>
        inversion Hrun; subst
      | Hrun : audit_memo_children_input_budget_run _ _ _ _ _ _ _ _ _ _ _
          result final credit cost |- _ => inversion Hrun; subst
      end
    end;
    try congruence; audit_memo_budget_inputs; try congruence; try lia.
  all: repeat match goal with
  | IH : forall result final credit cost,
      audit_memo_input_budget_run _ _ _ _ _ _ _ ?active ?memo ?v ?fuel
        result final credit cost -> _,
    Hrun : audit_memo_input_budget_run _ _ _ _ _ _ _ ?active ?memo ?v ?fuel _ _ _ _ |- _ =>
    let Hequal := fresh "Hequal" in
    pose proof (IH _ _ _ _ Hrun) as Hequal; clear IH;
    destruct Hequal as [? [? [? ?]]]; subst
  | IH : forall result final credit cost,
      audit_memo_children_input_budget_run _ _ _ _ _ _ _ ?active ?memo ?vs ?fuel
        result final credit cost -> _,
    Hrun : audit_memo_children_input_budget_run _ _ _ _ _ _ _ ?active ?memo ?vs ?fuel _ _ _ _ |- _
      =>
    let Hequal := fresh "Hequal" in
    pose proof (IH _ _ _ _ Hrun) as Hequal; clear IH;
    destruct Hequal as [? [? [? ?]]]; subst
  end; audit_memo_budget_inputs; try congruence; repeat split; reflexivity.
Qed.

(** * Concrete source budgets *)

(** Concatenating traces adds their source work without changing any captured operand. *)
Lemma audit_memo_source_work_app N E CV CK NE version_work key_work next_work
    (left right : list (audit_memo_event N E CV CK NE)) :
  audit_memo_source_work version_work key_work next_work (left ++ right) =
    audit_memo_source_work version_work key_work next_work left +
    audit_memo_source_work version_work key_work next_work right.
Proof.
  unfold audit_memo_source_work; rewrite length_app, audit_memo_primitive_work_app; lia.
Qed.

(** Per-key encoder bounds lift to the actual finite-set construction recurrence. *)
Lemma audit_memo_build_bound N E CV (enc : memory_version N E -> positive * list CV) work budget :
  (forall v, work (snd (enc v)) <= budget v) -> forall roots,
  audit_finset_of_list_budget enc work roots <= audit_memo_build_input_budget enc budget roots.
Proof.
  intros Hwork roots; induction roots as [|root rest IH]; cbn; [lia|].
  specialize (Hwork root); lia.
Qed.

(** Union work includes input concatenation, duplicate-preserving construction and enumeration. *)
Lemma audit_memo_union_bound N E CV (enc : memory_version N E -> positive * list CV) work budget
    left right roots build enumeration :
  (forall v, work (snd (enc v)) <= budget v) ->
  audit_memo_union enc left right = (roots, (build, enumeration)) ->
  2 + length left + audit_finset_source_work work build + audit_set_elements_work enumeration <=
    audit_memo_union_input_budget enc budget left right.
Proof.
  intros Hwork Hunion.
  unfold audit_memo_union, audit_memo_union_input_budget in *.
  pose proof (audit_finset_of_list_source_bound _ _ enc work (left ++ right)) as Hbuild.
  pose proof (audit_memo_build_bound N E CV enc work budget Hwork (left ++ right)) as Hbudget.
  destruct (audit_finset_of_list enc (left ++ right)) as [set calls].
  pose proof (audit_finset_elements_work_bound _ set) as Henumeration.
  destruct (audit_finset_elements set) as [output events].
  inversion Hunion; subst; cbn [fst snd] in *; lia.
Qed.

Section PrimitiveBudgets.
  Context {N E CV CK NE : Type}.
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable scope : positive.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.
  Variable version_work : list CV -> nat.
  Variable key_work : list CK -> nat.
  Variable next_work : list NE -> nat.
  Variable version_budget : memory_version N E -> nat.
  Variable key_budget : positive * memory_version N E -> nat.
  Variable next_budget : memory_version N E -> nat.
  Hypothesis Hversion : forall v, version_work (snd (version_enc v)) <= version_budget v.
  Hypothesis Hkey : forall key, key_work (snd (key_enc key)) <= key_budget key.
  Hypothesis Hnext : forall v, next_work (snd (next v)) <= next_budget v.

  (** Active membership pays its exact encoder and map path. *)
  Lemma audit_memo_active_bound active v flag calls :
    audit_finset_mem version_enc v active = (flag, calls) ->
    2 + audit_finset_source_work version_work calls <=
      audit_memo_active_input_budget version_enc version_budget v.
  Proof.
    intro Hcall.
    pose proof (dense_finset_mem_bound _ _ version_enc version_work v active) as Hbound.
    rewrite Hcall in Hbound; cbn [snd] in Hbound.
    unfold audit_memo_active_input_budget; specialize (Hversion v); lia.
  Qed.

  (** The memo probe pays its actual composite-key encoding and trie read. *)
  Lemma audit_memo_lookup_bound
      (memo : Map.t (positive * memory_version N E) (memo_entry N E))
      v entry calls :
    audit_map_get key_enc (scope, v) memo = (entry, calls) ->
    2 + audit_map_source_work key_work calls <=
      audit_memo_lookup_input_budget key_enc scope key_budget v.
  Proof.
    intro Hcall.
    pose proof (audit_map_get_source_work_bound _ _ _ key_enc key_work (scope, v) memo) as Hbound.
    rewrite Hcall in Hbound; cbn [snd] in Hbound.
    unfold audit_memo_lookup_input_budget; specialize (Hkey (scope, v)); lia.
  Qed.

  (** Storing completed roots pays the concrete persistent insertion into the returned child memo.
      *)
  Lemma audit_memo_store_bound
      (memo : Map.t (positive * memory_version N E) (memo_entry N E))
      v roots final calls :
    audit_map_set key_enc (scope, v) (MemoDone roots) memo = (final, calls) ->
    2 + audit_map_source_work key_work calls <=
      audit_memo_store_input_budget key_enc scope key_budget v.
  Proof.
    intro Hcall.
    pose proof (audit_map_set_source_work_bound _ _ _ key_enc key_work (scope, v)
      (MemoDone roots) memo) as Hbound.
    rewrite Hcall in Hbound; cbn [snd] in Hbound.
    unfold audit_memo_store_input_budget; specialize (Hkey (scope, v)); lia.
  Qed.

  (** Adding the current version pays its concrete persistent active-set insertion. *)
  Lemma audit_memo_add_bound active v final calls :
    audit_finset_add version_enc v active = (final, calls) ->
    2 + audit_finset_source_work version_work calls <=
      audit_memo_add_active_input_budget version_enc version_budget v.
  Proof.
    intro Hcall.
    pose proof (dense_finset_add_bound _ _ version_enc version_work v active) as Hbound.
    rewrite Hcall in Hbound; cbn [snd] in Hbound.
    unfold audit_memo_add_active_input_budget; specialize (Hversion v); lia.
  Qed.

  (** A terminal expansion pays both probes, its successor call and its actual completed store. *)
  Lemma audit_memo_terminal_whole_bound active memo v fuel ae le ne final se :
    audit_finset_mem version_enc v active = (false, ae) ->
    audit_map_get key_enc (scope, v) memo = (None, le) -> next v = ([], ne) ->
    audit_map_set key_enc (scope, v) (MemoDone [v]) memo = (final, se) ->
    exists budget, audit_memo_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active memo v (N.succ fuel)
      (MemoryClobberResult [v] true) final fuel budget /\
      audit_memo_source_work version_work key_work next_work
        [AuditMemoActive v false ae; AuditMemoLookup v None le; AuditMemoExpand v [] ne;
          AuditMemoStore v [v] se] <= budget.
  Proof.
    intros Hactive Hlookup Hsuccessors Hstore; eexists; split.
    - replace final with (fst (audit_map_set key_enc (scope, v) (MemoDone [v]) memo))
        by (rewrite Hstore; reflexivity).
      eapply AuditMemoBudgetTerminal; rewrite ?Hactive, ?Hlookup, ?Hsuccessors; reflexivity.
    - pose proof (audit_memo_active_bound active v false ae Hactive).
      pose proof (audit_memo_lookup_bound memo v None le Hlookup).
      pose proof (audit_memo_store_bound memo v [v] final se Hstore).
      specialize (Hnext v); rewrite Hsuccessors in Hnext; cbn [snd] in Hnext.
      unfold audit_memo_probe_input_budget, audit_memo_source_work.
      cbn [audit_memo_primitive_work length]; lia.
  Qed.

  (** A nonempty branch combines its child's independent budget and its exact conditional store. *)
  Lemma audit_memo_branch_whole_bound active memo v fuel ae le ne first rest active' adds
      result middle remaining events :
    audit_finset_mem version_enc v active = (false, ae) ->
    audit_map_get key_enc (scope, v) memo = (None, le) -> next v = (first :: rest, ne) ->
    audit_finset_add version_enc v active = (active', adds) ->
    (exists cost, audit_memo_children_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active' memo (first :: rest)
      fuel result middle remaining cost /\
      audit_memo_source_work version_work key_work next_work events <= cost) ->
    let prefix := [AuditMemoActive v false ae; AuditMemoLookup v None le;
      AuditMemoExpand v (first :: rest) ne; AuditMemoAddActive v adds] in
    let '(final, body) := if clobber_complete result then
      let '(final, calls) := audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result))
        middle in
      (final, prefix ++ events ++ [AuditMemoStore v (clobber_roots result) calls])
      else (middle, prefix ++ events) in
    exists budget, audit_memo_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active memo v (N.succ fuel) result final remaining
        budget /\
      audit_memo_source_work version_work key_work next_work body <= budget.
  Proof.
    intros Hactive Hlookup Hsuccessors Hadd [cost [Hbudget Hwork]].
    pose proof (audit_memo_active_bound active v false ae Hactive).
    pose proof (audit_memo_lookup_bound memo v None le Hlookup).
    pose proof (audit_memo_add_bound active v active' adds Hadd).
    specialize (Hnext v); rewrite Hsuccessors in Hnext; cbn [snd] in Hnext.
    destruct (clobber_complete result) eqn:Hcomplete.
    - destruct (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) middle)
        as [final calls] eqn:Hstore.
      eexists; split.
      + replace final with (if clobber_complete result then
          fst (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) middle)
          else middle) at 1 by (rewrite Hcomplete, Hstore; reflexivity).
        eapply AuditMemoBudgetBranch; rewrite ?Hactive, ?Hlookup, ?Hsuccessors; try reflexivity.
        rewrite Hadd; exact Hbudget.
      + pose proof (audit_memo_store_bound middle v (clobber_roots result) final calls Hstore).
        repeat rewrite audit_memo_source_work_app.
        unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length].
        unfold audit_memo_probe_input_budget; rewrite Hcomplete; lia.
    - eexists; split.
      + replace middle with (if clobber_complete result then
          fst (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) middle)
          else middle) at 1 by (rewrite Hcomplete; reflexivity).
        eapply AuditMemoBudgetBranch; rewrite ?Hactive, ?Hlookup, ?Hsuccessors; try reflexivity.
        rewrite Hadd; exact Hbudget.
      + repeat rewrite audit_memo_source_work_app.
        unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length].
        unfold audit_memo_probe_input_budget; rewrite Hcomplete; lia.
  Qed.

  (** Child composition pays canonical union on the same two returned root lists. *)
  Lemma audit_memo_children_whole_bound active memo v vs fuel one middle credit first
      tail final remaining events roots build enumeration :
    (exists cost, audit_memo_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active memo v fuel one middle credit cost /\
      audit_memo_source_work version_work key_work next_work first <= cost) ->
    (exists cost, audit_memo_children_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active middle vs credit tail final remaining cost /\
      audit_memo_source_work version_work key_work next_work events <= cost) ->
    audit_memo_union version_enc (clobber_roots one) (clobber_roots tail) =
      (roots, (build, enumeration)) ->
    exists budget, audit_memo_children_input_budget_run version_enc key_enc scope next
      version_budget key_budget next_budget active memo (v :: vs) fuel
      (MemoryClobberResult roots (andb (clobber_complete one) (clobber_complete tail)))
      final remaining budget /\ audit_memo_source_work version_work key_work next_work
        (first ++ events ++ [AuditMemoUnion (clobber_roots one) (clobber_roots tail)
          roots build enumeration]) <= budget.
  Proof.
    intros [first_cost [Hfirst Hfirstwork]] [tail_cost [Htail Htailwork]] Hunion.
    eexists; split.
    - replace roots with (fst (audit_memo_union version_enc (clobber_roots one)
        (clobber_roots tail))) by (rewrite Hunion; reflexivity).
      econstructor; eassumption.
    - pose proof (audit_memo_union_bound N E CV version_enc version_work version_budget
        (clobber_roots one) (clobber_roots tail) roots build enumeration Hversion Hunion).
      repeat rewrite audit_memo_source_work_app.
      unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length]; lia.
  Qed.

  (** Tree induction constructs a budget witness with identical results, memo and credit. *)
  Lemma audit_memo_tree_whole_bound :
    (forall active memo v fuel result final remaining events,
      audit_memo_tree version_enc key_enc scope next active memo v fuel result final remaining
        events ->
      exists budget,
        audit_memo_input_budget_run version_enc key_enc scope next
          version_budget key_budget next_budget active memo v fuel result final remaining budget /\
        audit_memo_source_work version_work key_work next_work events <= budget) /\
    (forall active memo versions fuel result final remaining events,
      audit_memo_children version_enc key_enc scope next active memo versions fuel result final
        remaining events ->
      exists budget,
        audit_memo_children_input_budget_run version_enc key_enc scope next
          version_budget key_budget next_budget active memo versions fuel result final remaining
          budget /\
        audit_memo_source_work version_work key_work next_work events <= budget).
  Proof.
    apply audit_memo_mutual.
    - intros active memo v fuel ae Hactive.
      exists (audit_memo_active_input_budget version_enc version_budget v); split.
      + constructor; rewrite Hactive; reflexivity.
      + unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length].
        pose proof (audit_memo_active_bound active v true ae Hactive); lia.
    - intros active memo v fuel ae le roots Hactive Hlookup.
      exists (audit_memo_probe_input_budget version_enc key_enc scope version_budget key_budget v).
      split; [econstructor; rewrite ?Hactive, ?Hlookup; reflexivity|].
      pose proof (audit_memo_active_bound active v false ae Hactive).
      pose proof (audit_memo_lookup_bound memo v (Some (MemoDone roots)) le Hlookup).
      unfold audit_memo_probe_input_budget.
      unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length]; lia.
    - intros active memo v fuel ae le Hactive Hlookup.
      exists (audit_memo_probe_input_budget version_enc key_enc scope version_budget key_budget v).
      split; [econstructor; rewrite ?Hactive, ?Hlookup; reflexivity|].
      pose proof (audit_memo_active_bound active v false ae Hactive).
      pose proof (audit_memo_lookup_bound memo v (Some MemoBusy) le Hlookup).
      unfold audit_memo_probe_input_budget.
      unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length]; lia.
    - intros active memo v ae le Hactive Hlookup.
      exists (audit_memo_probe_input_budget version_enc key_enc scope version_budget key_budget v).
      split; [econstructor; rewrite ?Hactive, ?Hlookup; reflexivity|].
      pose proof (audit_memo_active_bound active v false ae Hactive).
      pose proof (audit_memo_lookup_bound memo v None le Hlookup).
      unfold audit_memo_probe_input_budget.
      unfold audit_memo_source_work in *; cbn [audit_memo_primitive_work length]; lia.
    - intros active memo v fuel ae le ne final se Hactive Hlookup Hsuccessors Hstore.
      eapply audit_memo_terminal_whole_bound; eassumption.
    - intros active memo v fuel ae le ne first rest active' adds result middle remaining events
        final se Hactive Hlookup Hsuccessors Hadd Hchildren IH Hcomplete Hstore.
      pose proof (audit_memo_branch_whole_bound active memo v fuel ae le ne first rest active' adds
        result middle remaining events Hactive Hlookup Hsuccessors Hadd IH) as Hbound.
      rewrite Hcomplete, Hstore in Hbound; exact Hbound.
    - intros active memo v fuel ae le ne first rest active' adds result final remaining events
        Hactive Hlookup Hsuccessors Hadd Hchildren IH Hcomplete.
      pose proof (audit_memo_branch_whole_bound active memo v fuel ae le ne first rest active' adds
        result final remaining events Hactive Hlookup Hsuccessors Hadd IH) as Hbound.
      rewrite Hcomplete in Hbound; exact Hbound.
    - intros active memo fuel; exists 0; split; [constructor|reflexivity].
    - intros active memo v vs fuel one middle credit first tail final remaining events roots
        build enumeration Htree IHfirst Hchildren IHtail Hunion.
      eapply audit_memo_children_whole_bound; eassumption.
  Qed.
End PrimitiveBudgets.

(** Every tree has the independent input recurrence at the same observable endpoints. *)
Theorem audit_memo_whole_input_bound : audit_memo_whole_input_bound_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next version_budget key_budget next_budget
    version_work key_work next_work Hversion Hkey Hnext active memo v fuel result final remaining
    events Htree.
  exact (proj1 (audit_memo_tree_whole_bound version_enc key_enc scope next version_work key_work
    next_work version_budget key_budget next_budget Hversion Hkey Hnext)
    active memo v fuel result final remaining events Htree).
Qed.

(** Two recurrence witnesses at the same input cannot choose different budgets. *)
Theorem audit_memo_input_budget_deterministic : audit_memo_input_budget_deterministic_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next version_budget key_budget next_budget
    active memo v fuel result final remaining first second Hfirst Hsecond.
  pose proof (proj1 (audit_memo_budget_unique N E CV CK NE version_enc key_enc scope next
    version_budget key_budget next_budget) active memo v fuel result final remaining first Hfirst
    result final remaining second Hsecond) as [_ [_ [_ Hcost]]].
  exact Hcost.
Qed.

(** Concrete encoder and successor bounds discharge all internal bodies of the memory recurrence. *)
Theorem audit_memory_memo_whole_input_bound : audit_memory_memo_whole_input_bound_statement.
Proof.
  intros N E T CN CE SE IE OE BE node_enc edge_enc site_enc table incoming operand before
    node_work edge_work site_work incoming_work operand_work before_work
    node_budget edge_budget site_budget incoming_budget operand_budget before_budget
    q active memo v fuel result final remaining events Hnode Hedge Hsite Hincoming Hoperand Hbefore.
  pose proof (audit_memory_encoders_input_bound N E T CN CE SE node_enc edge_enc site_enc
    node_work edge_work site_work node_budget edge_budget site_budget Hnode Hedge Hsite)
    as [Hversion [_ [Hscope Hkey]]].
  pose proof (audit_memo_whole_input_bound N E _ _ _
    (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_memo_key_encode node_enc edge_enc)
    (fst (audit_memory_scope_encode site_enc q))
    (audit_memory_raw_next edge_enc site_enc table incoming
      operand before q)
    (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
    (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
    (@audit_raw_next_input_budget N E T CE SE IE OE BE edge_enc site_enc table incoming before
      edge_budget site_budget incoming_budget operand_budget before_budget q)
    (audit_memory_version_work node_work edge_work)
    (audit_memory_memo_key_work node_work edge_work)
    (audit_raw_next_source_work edge_work site_work incoming_work
      operand_work before_work) Hversion Hkey
    (fun version => audit_raw_next_whole_input_bound N E T CE SE IE OE BE edge_enc site_enc
      table incoming operand before edge_work site_work incoming_work operand_work before_work
      edge_budget site_budget incoming_budget operand_budget before_budget q version
      Hedge Hsite Hincoming Hoperand Hbefore)
    active memo v fuel result final remaining events) as Hbound.
  cbn zeta; intro Htree.
  destruct (Hbound Htree) as [budget [Hbudget Hwork]].
  exists budget; split; [exact Hbudget|specialize (Hscope q); lia].
Qed.
