(** * Adequacy of expiration-map comparisons

    The counted traversal follows the first trie's selective branches.
    For example, failure in a left child skips the parent value and right child.
    Builds on: FixpointAuditObserveExpireCheck and FixpointAuditObserveCompareAdequacy. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklistCallbacks
  FixpointAuditObserveCompare FixpointAuditObserveCompareAdequacy FixpointAuditObserveExpireCheck.
Import List.ListNotations.

(** * Selective traversal *)

Definition fx_expire_codes {X} (EX : encoding X) (event : fx_expire_check_event X) : Prop :=
  match event with
  | FxExpireCheckCase => True
  | FxExpireCheckCompare events => Forall (fx_compare_codes EX) events
  end.

Lemma fx_expire_work_app X (first last : list (fx_expire_check_event X)) :
  fx_expire_check_work (first ++ last) =
    fx_expire_check_work first + fx_expire_check_work last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - destruct event as [|body].
    + change (fx_expire_check_work (rest ++ last) + 1 =
        (fx_expire_check_work rest + 1) + fx_expire_check_work last).
      rewrite IH; lia.
    + change (fx_expire_check_work (rest ++ last) + fx_observe_compare_work body =
        (fx_expire_check_work rest + fx_observe_compare_work body) +
          fx_expire_check_work last).
      rewrite IH; lia.
Qed.

Lemma fx_expire_value_adequate X (EX : encoding X) (entry : X * list X) opposite :
  let '(out, events) := fx_expire_check_value EX entry opposite in
  out = observation_seteq EX (snd entry)
    (match opposite with
    | Some (_, ys) => ys
    | None => []
    end) /\
  fx_expire_check_work events <= fx_observe_seteq_budget EX (snd entry)
    (match opposite with
    | Some (_, ys) => ys
    | None => []
    end) /\
  Forall (fx_expire_codes EX) events.
Proof.
  unfold fx_expire_check_value.
  destruct opposite as [[key ys]|].
  - pose proof (fx_observe_seteq_correct X EX (snd entry) ys) as Hcorrect.
    pose proof (fx_seteq_codes X EX (snd entry) ys) as Hcodes.
    destruct (fx_observe_seteq EX (snd entry) ys) as [out events].
    cbn in Hcorrect, Hcodes |- *; destruct Hcorrect as [Hout Hwork].
    repeat split; try assumption; constructor; [exact Hcodes | constructor].
  - pose proof (fx_observe_seteq_correct X EX (snd entry) []) as Hcorrect.
    pose proof (fx_seteq_codes X EX (snd entry) []) as Hcodes.
    destruct (fx_observe_seteq EX (snd entry) []) as [out events].
    cbn in Hcorrect, Hcodes |- *; destruct Hcorrect as [Hout Hwork].
    repeat split; try assumption; constructor; [exact Hcodes | constructor].
Qed.

(** The relation used by the original directed map traversal. *)
Definition fx_expire_relation {X} (EX : encoding X) (entry : X * list X)
    (other : option (X * list X)) : bool :=
  observation_seteq EX (snd entry)
    (match other with
    | Some (_, ys) => ys
    | None => []
    end).

Lemma fx_expire_ne_adequate X (EX : encoding X) (first : Trie.ne (X * list X)) :
  forall second,
    let '(out, events) := fx_expire_check_ne EX first second in
    out = Trie.forall2_ne (fx_expire_relation EX) first second /\
    fx_expire_check_work events <= fx_expire_check_ne_budget EX first second /\
    Forall (fx_expire_codes EX) events.
Proof.
  induction first as [r IHr | v | v r IHr | l IHl | l IHl r IHr |
    l IHl v | l IHl v r IHr]; intro second;
    cbn [fx_expire_check_ne Trie.forall2_ne fx_expire_check_ne_budget].
  - specialize (IHr (Trie.right second)).
    destruct (fx_expire_check_ne EX r (Trie.right second)) as [out events].
    cbn in IHr |- *; destruct IHr as [Hout [Hwork Hcodes]].
    split; [exact Hout |]; split.
    + unfold fx_expire_check_work in *; cbn in *; lia.
    + constructor; [exact I | exact Hcodes].
  - pose proof (fx_expire_value_adequate X EX v (Trie.value second)) as Hvalue.
    destruct (fx_expire_check_value EX v (Trie.value second)) as [out events].
    cbn in Hvalue |- *; destruct Hvalue as [Hout [Hwork Hcodes]].
    split; [exact Hout |]; split.
    + unfold fx_expire_check_work in *; cbn in *; lia.
    + constructor; [exact I | exact Hcodes].
  - pose proof (fx_expire_value_adequate X EX v (Trie.value second)) as Hvalue.
    destruct (fx_expire_check_value EX v (Trie.value second)) as [test events].
    cbn in Hvalue; destruct Hvalue as [Htest [Hwork Hcodes]].
    destruct test.
    + specialize (IHr (Trie.right second)).
      destruct (fx_expire_check_ne EX r (Trie.right second)) as [out later].
      cbn in IHr |- *; destruct IHr as [Hout [Hlater Hlatercodes]].
      unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [exact Hout |]; split.
      * change (fx_expire_check_work (events ++ later) + 1 <=
          fx_expire_check_ne_budget EX (Trie.N011 v r) second).
        rewrite fx_expire_work_app; cbn [fx_expire_check_ne_budget].
        unfold fx_observe_seteq_budget in *; lia.
      * constructor; [exact I | apply Forall_app; split; assumption].
    + cbn; unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [reflexivity |]; split.
      * unfold fx_expire_check_work, fx_observe_seteq_budget in *; cbn in *; lia.
      * constructor; [exact I | exact Hcodes].
  - specialize (IHl (Trie.left second)).
    destruct (fx_expire_check_ne EX l (Trie.left second)) as [out events].
    cbn in IHl |- *; destruct IHl as [Hout [Hwork Hcodes]].
    split; [exact Hout |]; split.
    + unfold fx_expire_check_work in *; cbn in *; lia.
    + constructor; [exact I | exact Hcodes].
  - specialize (IHl (Trie.left second)).
    destruct (fx_expire_check_ne EX l (Trie.left second)) as [test events].
    cbn in IHl; destruct IHl as [Htest [Hwork Hcodes]].
    destruct test.
    + specialize (IHr (Trie.right second)).
      destruct (fx_expire_check_ne EX r (Trie.right second)) as [out later].
      cbn in IHr |- *; destruct IHr as [Hout [Hlater Hlatercodes]].
      unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [exact Hout |]; split.
      * change (fx_expire_check_work (events ++ later) + 1 <=
          fx_expire_check_ne_budget EX (Trie.N101 l r) second).
        rewrite fx_expire_work_app; cbn [fx_expire_check_ne_budget].
        unfold fx_observe_seteq_budget in *; lia.
      * constructor; [exact I | apply Forall_app; split; assumption].
    + cbn; unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [reflexivity |]; split.
      * unfold fx_expire_check_work, fx_observe_seteq_budget in *; cbn in *; lia.
      * constructor; [exact I | exact Hcodes].
  - specialize (IHl (Trie.left second)).
    destruct (fx_expire_check_ne EX l (Trie.left second)) as [test events].
    cbn in IHl; destruct IHl as [Htest [Hwork Hcodes]].
    destruct test.
    + pose proof (fx_expire_value_adequate X EX v (Trie.value second)) as Hvalue.
      destruct (fx_expire_check_value EX v (Trie.value second)) as [out later].
      cbn in Hvalue |- *; destruct Hvalue as [Hout [Hlater Hlatercodes]].
      unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [exact Hout |]; split.
      * change (fx_expire_check_work (events ++ later) + 1 <=
          fx_expire_check_ne_budget EX (Trie.N110 l v) second).
        rewrite fx_expire_work_app; cbn [fx_expire_check_ne_budget].
        unfold fx_observe_seteq_budget in *; lia.
      * constructor; [exact I | apply Forall_app; split; assumption].
    + cbn; unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [reflexivity |]; split.
      * unfold fx_expire_check_work, fx_observe_seteq_budget in *; cbn in *; lia.
      * constructor; [exact I | exact Hcodes].
  - specialize (IHl (Trie.left second)).
    destruct (fx_expire_check_ne EX l (Trie.left second)) as [test events].
    cbn in IHl; destruct IHl as [Htest [Hwork Hcodes]].
    destruct test.
    + pose proof (fx_expire_value_adequate X EX v (Trie.value second)) as Hvalue.
      destruct (fx_expire_check_value EX v (Trie.value second)) as [middle mid].
      cbn in Hvalue; destruct Hvalue as [Hmid [Hmidwork Hmidcodes]].
      destruct middle.
      * specialize (IHr (Trie.right second)).
        destruct (fx_expire_check_ne EX r (Trie.right second)) as [out later].
        cbn in IHr |- *; destruct IHr as [Hout [Hlater Hlatercodes]].
        unfold fx_expire_relation in *; rewrite <- Htest, <- Hmid; cbn.
        split; [exact Hout |]; split.
        -- change (fx_expire_check_work (events ++ mid ++ later) + 1 <=
             fx_expire_check_ne_budget EX (Trie.N111 l v r) second).
           repeat rewrite fx_expire_work_app; cbn [fx_expire_check_ne_budget].
           unfold fx_observe_seteq_budget in *; lia.
        -- constructor; [exact I | repeat rewrite Forall_app; tauto].
      * cbn; unfold fx_expire_relation in *; rewrite <- Htest, <- Hmid; cbn.
        split; [reflexivity |]; split.
        -- change (fx_expire_check_work (events ++ mid) + 1 <=
             fx_expire_check_ne_budget EX (Trie.N111 l v r) second).
           rewrite fx_expire_work_app; cbn [fx_expire_check_ne_budget].
           unfold fx_observe_seteq_budget in *; lia.
        -- constructor; [exact I | apply Forall_app; split; assumption].
    + cbn; unfold fx_expire_relation in *; rewrite <- Htest; cbn; split; [reflexivity |]; split.
      * unfold fx_expire_check_work, fx_observe_seteq_budget in *; cbn in *; lia.
      * constructor; [exact I | exact Hcodes].
Qed.

Lemma fx_expire_directed_adequate X (EX : encoding X) first second :
  let '(out, events) := fx_expire_check_directed EX first second in
  out = Trie.forall2 (fx_expire_relation EX) first second /\
  fx_expire_check_work events <= fx_expire_check_directed_budget EX first second /\
  Forall (fx_expire_codes EX) events.
Proof.
  destruct first as [|first].
  - cbn [fx_expire_check_directed Trie.forall2 fx_expire_check_directed_budget
      fx_expire_check_work fold_right].
    repeat split; try lia; constructor; [exact I | constructor].
  - pose proof (fx_expire_ne_adequate X EX first second) as Hne.
    unfold fx_expire_check_directed, Trie.forall2, fx_expire_check_directed_budget.
    destruct (fx_expire_check_ne EX first second) as [out events].
    cbn in Hne |- *; destruct Hne as [Hout [Hwork Hcodes]].
    split; [exact Hout |]; split.
    + unfold fx_expire_check_work in *; cbn in *; lia.
    + constructor; [exact I | exact Hcodes].
Qed.

Definition fx_expire_relation_map {X} (EX : encoding X) (entry : X * list X)
    (other : option (X * list X)) : bool :=
  observation_seteq EX (snd entry)
    (match option_map snd other with
    | Some ys => ys
    | None => []
    end).

Lemma fx_expire_relation_agrees X (EX : encoding X) entry other :
  fx_expire_relation EX entry other = fx_expire_relation_map EX entry other.
Proof.
  destruct other as [[key ys]|]; reflexivity.
Qed.

Lemma fx_expire_trie_agrees X (EX : encoding X) (first : Trie.ne (X * list X)) :
  forall second, Trie.forall2_ne (fx_expire_relation EX) first second =
    Trie.forall2_ne (fx_expire_relation_map EX) first second.
Proof.
  induction first; intro second; cbn [Trie.forall2_ne];
    repeat rewrite fx_expire_relation_agrees;
    repeat match goal with
    | IH : forall second, _ = _ |- _ => rewrite IH
    end; reflexivity.
Qed.

Lemma fx_expire_map_agrees X (EX : encoding X) first second :
  Trie.forall2 (fx_expire_relation EX) first second =
    Trie.forall2 (fx_expire_relation_map EX) first second.
Proof.
  destruct first; [reflexivity | apply fx_expire_trie_agrees].
Qed.

(** The two directed traversals preserve the map check and its input-derived bound. *)
Theorem fx_expire_check_correct : fx_expire_check_statement.
Proof.
  intros X EX left_map right_map.
  pose proof (fx_expire_directed_adequate X EX left_map right_map) as Hleft.
  pose proof (fx_expire_directed_adequate X EX right_map left_map) as Hright.
  unfold fx_expire_check, fx_expire_check_budget, observation_expire_check, Map.forall2.
  destruct (fx_expire_check_directed EX left_map right_map) as [a first].
  destruct (fx_expire_check_directed EX right_map left_map) as [b second].
  cbn in Hleft, Hright; destruct Hleft as [Ha [Hfirst _]];
    destruct Hright as [Hb [Hsecond _]].
  change (a && b = (Trie.forall2 (fx_expire_relation_map EX) left_map right_map &&
    Trie.forall2 (fx_expire_relation_map EX) right_map left_map) /\
    fx_expire_check_work (first ++ second) + 1 <=
      1 + fx_expire_check_directed_budget EX left_map right_map +
        fx_expire_check_directed_budget EX right_map left_map).
  rewrite <- !fx_expire_map_agrees, Ha, Hb, fx_expire_work_app; split; [reflexivity | lia].
Qed.

Lemma fx_expire_check_codes X (EX : encoding X) left_map right_map :
  Forall (fx_expire_codes EX) (snd (fx_expire_check EX left_map right_map)).
Proof.
  pose proof (fx_expire_directed_adequate X EX left_map right_map) as Hleft.
  pose proof (fx_expire_directed_adequate X EX right_map left_map) as Hright.
  unfold fx_expire_check.
  destruct (fx_expire_check_directed EX left_map right_map) as [a first].
  destruct (fx_expire_check_directed EX right_map left_map) as [b second].
  cbn in Hleft, Hright |- *; destruct Hleft as [_ [_ Hleft]];
    destruct Hright as [_ [_ Hright]].
  constructor; [exact I | apply Forall_app; split; assumption].
Qed.

(** * Encoder receipts on selected comparisons *)

Lemma fx_body_work_concat B (weight : B -> nat) groups :
  fx_one_body_work (fun body => fx_one_body_work weight body) (concat groups) =
    fx_declared_body_work weight groups.
Proof.
  induction groups as [|group rest IH].
  - reflexivity.
  - unfold fx_one_body_work, fx_declared_body_work in *; cbn [concat fold_right].
    rewrite fold_right_app; cbn; rewrite <- IH.
    clear IH; induction group as [|body tail IH].
    + reflexivity.
    + cbn; rewrite IH; lia.
Qed.

Lemma fx_expire_sources X C A B (EX : encoding X)
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_observe_compare_source_laws EX source budget ->
  Forall (fx_expire_codes EX) events ->
  exists bodies, Forall2 (fx_expire_check_event_source source) events bodies /\
    fx_declared_body_work (fx_body_weight budget) bodies <=
      fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 events.
Proof.
  intros Hlaws Hcodes; induction Hcodes as [|event rest Hcode Hrest IH].
  - exists []; split; [constructor | reflexivity].
  - destruct IH as [tail [Htail Hwork]].
    destruct event as [|comparisons].
    + exists ([] :: tail); split.
      * constructor; [reflexivity | exact Htail].
      * unfold fx_declared_body_work in *; cbn in *; lia.
    + cbn [fx_expire_codes] in Hcode.
      destruct (fx_compare_sources X C A B EX source budget comparisons Hlaws Hcode)
        as [groups [Hgroups Hbudget]].
      exists (concat groups :: tail); split.
      * constructor; [exists groups; split; [exact Hgroups | reflexivity] | exact Htail].
      * change (fx_one_body_work (fun body => fx_one_body_work (fx_body_weight budget) body)
          (concat groups) + fx_declared_body_work (fx_body_weight budget) tail <=
          fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 comparisons +
          fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 rest).
        rewrite fx_body_work_concat; lia.
Qed.

(** Expiration-check receipts cover exactly the selected comparisons in both directions. *)
Theorem fx_expire_check_source : fx_expire_check_source_statement.
Proof.
  intros X C A B EX source budget left_map right_map Hlaws.
  pose proof (fx_expire_check_correct X EX left_map right_map) as Hcorrect.
  pose proof (fx_expire_check_codes X EX left_map right_map) as Hcodes.
  destruct (fx_expire_check EX left_map right_map) as [out events].
  cbn in Hcorrect, Hcodes |- *; destruct Hcorrect as [Hout Hframe].
  destruct (fx_expire_sources X C A B EX source budget events Hlaws Hcodes)
    as [bodies [Hsource Hwork]].
  exists bodies; repeat split; try assumption; lia.
Qed.
