(** * Plain memo computation trees

    The untraced producer has the same source-tree endpoints as its counted mirror.
    For example, a cache hit returns its saved roots and unchanged binary credit.
    Builds on: plain memo computation, memo rules and collection erasure proofs. *)

From Stdlib Require Import List NArith Wf_nat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditMapAdequacy
  CollectionsAuditFinSetAdequacy CollectionsAuditElementsAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoPlain.
Import List.ListNotations.

(** * Collection erasure *)

(** Counted union erases to the exact canonical set enumeration used by the plain producer. *)
Lemma audit_memo_union_erases N E CV (original : encoding (memory_version N E))
    (enc : memory_version N E -> positive * list CV) left right :
  (forall v, fst (enc v) = encode original v) ->
  fst (audit_memo_union enc left right) =
    FinSet.elements (FinSet.of_list original (left ++ right)).
Proof.
  intro Henc; unfold audit_memo_union.
  pose proof (audit_finset_of_list_erases _ _ enc original (left ++ right)
    (fun v _ => Henc v)) as Hbuild.
  destruct (audit_finset_of_list enc (left ++ right)) as [set calls].
  pose proof (audit_finset_elements_erases _ set) as Henumerate.
  destruct (audit_finset_elements set) as [roots events].
  cbn [fst] in *; rewrite Henumerate, Hbuild; reflexivity.
Qed.

(** * Plain execution trees *)

Section PlainTrees.
  Context {N E CV CK NE : Type}.
  Variable version_encoding : encoding (memory_version N E).
  Variable key_encoding : encoding (positive * memory_version N E).
  Variable version_enc : memory_version N E -> positive * list CV.
  Variable key_enc : positive * memory_version N E -> positive * list CK.
  Variable scope : positive.
  Variable next : memory_version N E -> list (memory_version N E) * list NE.
  Hypothesis Hversion : forall v, fst (version_enc v) = encode version_encoding v.
  Hypothesis Hkey : forall key, fst (key_enc key) = encode key_encoding key.

  (** Plain child recursion has trees for the exact sequential memo and credit endpoints. *)
  Lemma audit_plain_children_tree bound recur active versions :
    (forall credit Hcredit memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      exists events, audit_memo_tree version_enc key_enc scope next active memo v credit
        (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events) ->
    forall memo credit Hcredit,
      let run := proj1_sig (audit_plain_memo_children version_encoding bound recur active memo
        versions credit Hcredit) in
      exists events, audit_memo_children version_enc key_enc scope next active memo versions credit
        (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events.
  Proof.
    intro Hrecur; induction versions as [|v rest IH]; intros memo credit Hcredit.
    - cbn [audit_plain_memo_children]; eexists; constructor.
    - pose proof (Hrecur credit Hcredit memo v) as Hone.
      cbn [audit_plain_memo_children].
      destruct (recur credit Hcredit active memo v) as [one Hbound].
      cbn [proj1_sig] in Hone |- *.
      destruct Hone as [first Hfirst].
      match goal with
      | |- context [audit_plain_memo_children _ _ _ _ _ _ _ ?proof] =>
        specialize (IH (audit_plain_memo_cache one) (audit_plain_memo_credit one) proof);
        destruct (audit_plain_memo_children version_encoding bound recur active
          (audit_plain_memo_cache one) rest (audit_plain_memo_credit one) proof) as [tail Htail]
      end.
      cbn [proj1_sig] in IH |- *; destruct IH as [events Hchildren].
      pose proof (audit_memo_union_erases N E CV version_encoding version_enc
        (clobber_roots (audit_plain_memo_value one))
        (clobber_roots (audit_plain_memo_value tail)) Hversion) as Hunion.
      destruct (audit_memo_union version_enc (clobber_roots (audit_plain_memo_value one))
        (clobber_roots (audit_plain_memo_value tail))) as [roots [build enumeration]] eqn:Hcall.
      cbn [fst] in Hunion; rewrite <- Hunion.
      eexists; econstructor; eassumption.
  Qed.

  (** A plain nonempty branch keeps its child endpoints and stores exactly complete results. *)
  Lemma audit_plain_branch_tree active memo v fuel first rest ne ae le active' adds
      result final remaining events :
    audit_finset_mem version_enc v active = (false, ae) ->
    audit_map_get key_enc (scope, v) memo = (None, le) ->
    next v = (first :: rest, ne) -> audit_finset_add version_enc v active = (active', adds) ->
    audit_memo_children version_enc key_enc scope next active' memo (first :: rest) fuel
      result final remaining events ->
    exists events', audit_memo_tree version_enc key_enc scope next active memo v (N.succ fuel)
      result (if clobber_complete result then
        Map.set key_encoding (scope, v) (MemoDone (clobber_roots result)) final else final)
      remaining events'.
  Proof.
    intros Hactive Hlookup Hnext Hadd Hchildren.
    destruct (clobber_complete result) eqn:Hcomplete.
    - pose proof (audit_map_set_erases _ _ _ key_enc key_encoding (scope, v)
        (MemoDone (clobber_roots result)) final (Hkey (scope, v))) as Hstore.
      destruct (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) final)
        as [stored calls] eqn:Hstorecall.
      cbn [fst] in Hstore; rewrite <- Hstore.
      eexists; eapply AuditMemoTreeBranchComplete; eassumption.
    - eexists; eapply AuditMemoTreeBranchIncomplete; eassumption.
  Qed.

  (** Every plain body branch retains the exact observable primitive and child-tree results. *)
  Lemma audit_plain_body_tree fuel recur :
    (forall credit Hcredit active memo v,
      let run := proj1_sig (recur credit Hcredit active memo v) in
      exists events, audit_memo_tree version_enc key_enc scope next active memo v credit
        (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events) ->
    forall active memo v,
      let run := proj1_sig (audit_plain_memo_body version_encoding key_encoding scope
        (fun v => fst (next v)) fuel recur active memo v) in
      exists events, audit_memo_tree version_enc key_enc scope next active memo v fuel
        (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events.
  Proof.
    intros Hrecur active memo v.
    pose proof (audit_finset_mem_erases _ _ version_enc version_encoding v active (Hversion v))
      as Hactive.
    unfold audit_plain_memo_body.
    destruct (audit_finset_mem version_enc v active) as [flag ae] eqn:Hactivecall.
    cbn [fst] in Hactive; rewrite <- Hactive; destruct flag.
    - cbn; eexists; constructor; exact Hactivecall.
    - pose proof (audit_map_get_erases _ _ _ key_enc key_encoding (scope, v) memo
        (Hkey (scope, v))) as Hlookup.
      destruct (audit_map_get key_enc (scope, v) memo) as [entry le] eqn:Hlookupcall.
      cbn [fst] in Hlookup; rewrite <- Hlookup; destruct entry as [[|roots]|].
      + cbn; eexists; eapply AuditMemoTreeBusy; eassumption.
      + cbn; eexists; eapply AuditMemoTreeDone; eassumption.
      + destruct fuel as [|positive_fuel].
        * cbn; eexists; eapply AuditMemoTreeFuel; eassumption.
        * destruct (next v) as [successors ne] eqn:Hnext.
          cbn [fst]; destruct successors as [|first rest].
          -- pose proof (audit_map_set_erases _ _ _ key_enc key_encoding (scope, v)
               (MemoDone [v]) memo (Hkey (scope, v))) as Hstore.
             destruct (audit_map_set key_enc (scope, v) (MemoDone [v]) memo)
               as [final se] eqn:Hstorecall.
             cbn [fst] in Hstore.
             cbn [proj1_sig audit_plain_memo_value audit_plain_memo_cache audit_plain_memo_credit].
             rewrite <- Hstore.
             eexists.
             replace (Npos positive_fuel) with (N.succ (N.pred (Npos positive_fuel))) at 1
               by (rewrite N.succ_pred; [reflexivity|discriminate]).
             eapply AuditMemoTreeTerminal; eassumption.
          -- pose proof (audit_finset_add_erases _ _ version_enc version_encoding v active
               (Hversion v)) as Hadd.
             destruct (audit_finset_add version_enc v active) as [active' adds] eqn:Haddcall.
             cbn [fst] in Hadd; rewrite <- Hadd.
             match goal with
             | |- context [audit_plain_memo_children _ _ _ _ _ _ _ ?proof] =>
               pose proof (audit_plain_children_tree (Npos positive_fuel) recur active'
                 (first :: rest) (fun credit Hcredit memo' v' =>
                   Hrecur credit Hcredit active' memo' v') memo (N.pred (Npos positive_fuel))
                 proof) as Hchildren;
               destruct (audit_plain_memo_children version_encoding (Npos positive_fuel) recur
                 active' memo (first :: rest) (N.pred (Npos positive_fuel)) proof)
                 as [children Hbound]
             end.
             cbn [proj1_sig] in Hchildren |- *; destruct Hchildren as [events Hchildren].
             change (exists events', audit_memo_tree version_enc key_enc scope next active memo v
               (Npos positive_fuel) (audit_plain_memo_value children)
               (if clobber_complete (audit_plain_memo_value children) then
                 Map.set key_encoding (scope, v) (MemoDone (clobber_roots
                   (audit_plain_memo_value children))) (audit_plain_memo_cache children)
                else audit_plain_memo_cache children) (audit_plain_memo_credit children) events').
             pose proof (audit_plain_branch_tree active memo v (N.pred (Npos positive_fuel))
               first rest ne ae le active' adds _ _ _ events Hactivecall Hlookupcall Hnext Haddcall
               Hchildren) as Hbranch.
             rewrite N.succ_pred in Hbranch by discriminate; exact Hbranch.
  Qed.

  (** Accessibility recursion connects the actual plain fixed point to a source tree. *)
  Lemma audit_plain_fix_tree fuel (access : Acc (ltof BinNums.N N.to_nat) fuel) :
    forall active memo v,
      let run := proj1_sig (Fix_F
        (fun credit => forall active memo v,
          {run : audit_plain_memo_result N E | audit_plain_memo_bounded credit run})
        (audit_plain_memo_body version_encoding key_encoding scope (fun v => fst (next v)))
        access active memo v) in
      exists events, audit_memo_tree version_enc key_enc scope next active memo v fuel
        (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events.
  Proof.
    revert fuel access; fix IH 2; intros fuel [smaller] active memo v.
    cbn [Fix_F]; apply audit_plain_body_tree.
    intros credit Hcredit active' memo' v'; apply IH.
  Qed.

  (** The plain producer inhabits a counted tree at exactly its result, cache and remaining credit.
      *)
  Lemma audit_plain_compute_tree fuel active memo v :
    let run := audit_memo_compute version_encoding key_encoding scope (fun v => fst (next v))
      fuel active memo v in
    exists events, audit_memo_tree version_enc key_enc scope next active memo v fuel
      (audit_plain_memo_value run) (audit_plain_memo_cache run) (audit_plain_memo_credit run)
        events.
  Proof.
    unfold audit_memo_compute, Fix; apply audit_plain_fix_tree.
  Qed.
End PlainTrees.
