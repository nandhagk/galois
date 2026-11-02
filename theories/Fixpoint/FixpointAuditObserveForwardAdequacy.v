(** * Adequacy of forward observation boundaries

    Forward checks retain the actual target, dependency and encoder calls at each boundary.
    For example, an absent target skips dependencies but still checks later constraints.
    Builds on: FixpointAuditObserveForward and CollectionsAuditFinSetAdequacy. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditFinSet CollectionsAuditTrieAdequacy
  CollectionsAuditFinSetAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditIndex
  FixpointAuditIndexAdequacy FixpointAuditObserveForward.
Import List.ListNotations.

(** * Finite-set calls *)

Lemma fx_forward_set_fold_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) input :
  (forall x, let '(out, body) := fxi_encode cb x in fxi_encode_source source x out body) ->
  forall set, fxi_set_external_adequacy source (snd (audit_finset_fold (fxi_encode cb) input set)).
Proof.
  intro Hsource; induction input as [|x rest IH]; intro set.
  - constructor; [exact I | constructor].
  - cbn [audit_finset_fold]; unfold audit_finset_add.
    pose proof (Hsource x) as Henc.
    destruct (fxi_encode cb x) as [code body].
    destruct (audit_trie_set code (x, tt) set) as [next trace].
    specialize (IH next); destruct (audit_finset_fold (fxi_encode cb) rest next) as [out events].
    cbn in IH, Henc |- *; constructor; [exact I |].
    constructor; [exact Henc | exact IH].
Qed.

Lemma fx_forward_mem_adequate X C B (EX : encoding X) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) (source : fx_index_external_source X C B) x set :
  fst (fxi_encode cb x) = encode EX x ->
  fxi_body_work ib (snd (fxi_encode cb x)) <= fxi_encode_bound ib x ->
  (let '(code, body) := fxi_encode cb x in fxi_encode_source source x code body) ->
  let '(out, events) := audit_finset_mem (fxi_encode cb) x set in
  out = FinSet.mem EX x set /\ fxi_set_external_adequacy source events /\
  audit_finset_source_work (fxi_body_work ib) events <=
    6 + fxi_encode_bound ib x + 5 * Pos.size_nat (encode EX x).
Proof.
  intros Hencode Hbound Hsource.
  pose proof (audit_finset_mem_erases X B (fxi_encode cb) EX x set Hencode) as Herase.
  destruct (fxi_encode cb x) as [code body] eqn:Henc; cbn in Hencode, Hbound, Hsource.
  subst code.
  pose proof (audit_trie_get_source_work_bound (X * unit)%type (encode EX x) set) as Htrie.
  pose proof (audit_trie_get_trace_adequate (X * unit)%type (encode EX x) set) as Htrace.
  unfold audit_finset_mem in Herase |- *; rewrite Henc in Herase |- *.
  unfold audit_map_code_get in Herase |- *.
  destruct (audit_trie_get (encode EX x) set) as [found trace].
  cbn in Htrace, Htrie, Herase |- *; split; [exact Herase |]; split.
  - constructor; [exact Hsource | constructor].
  - destruct found; cbn [audit_finset_source_work option_map]; rewrite Htrace;
      unfold fxi_body_work in *; lia.
Qed.

(** * Strict dependency and constraint scans *)

Lemma fx_forward_work_app X C B (ib : fx_index_external_budget X C B) first last :
  fx_observe_forward_work ib (first ++ last) =
    fx_observe_forward_work ib first + fx_observe_forward_work ib last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - change (fx_observe_forward_event_work ib event +
      fx_observe_forward_work ib (rest ++ last) =
      (fx_observe_forward_event_work ib event + fx_observe_forward_work ib rest) +
      fx_observe_forward_work ib last).
    rewrite IH; lia.
Qed.

Section Forward.

Context {X C A B : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).

Context (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B).

Context (source : fx_index_external_source X C B).

Context (Herase : fx_index_external_erases EX S SS cb).

Context (Hbounded : fx_index_external_bounded cb ib).

Context (Hencsource : forall x, let '(out, body) := fxi_encode cb x in
  fxi_encode_source source x out body).

Context (Htargetsource : forall c, let '(out, body) := fxi_target cb c in
  fxi_target_source source c out body).

Context (Hdepssource : forall c, let '(out, body) := fxi_deps cb c in
  fxi_deps_source source c out body).

Lemma fx_forward_deps_adequate later deps :
  let '(out, events) := fx_forward_deps cb later deps in
  out = forallb (fun x => negb (FinSet.mem EX x later)) deps /\
  Forall (fx_observe_forward_event_source source) events /\
  fx_observe_forward_work ib events <= fx_forward_deps_budget EX ib deps.
Proof.
  destruct Herase as [Hencode _].
  destruct Hbounded as [_ [Hencbound _]].
  induction deps as [|x rest IH].
  - cbn [fx_forward_deps fx_forward_deps_budget forallb fx_observe_forward_work fold_right
      fx_observe_forward_event_work]; repeat split; try lia; constructor; [exact I | constructor].
  - cbn [fx_forward_deps fx_forward_deps_budget forallb].
    pose proof (fx_forward_mem_adequate X C B EX cb ib source x later
      (Hencode x) (Hencbound x) (Hencsource x)) as Hmem.
    destruct (audit_finset_mem (fxi_encode cb) x later) as [present mem].
    destruct (fx_forward_deps cb later rest) as [out events].
    cbn in Hmem, IH; destruct Hmem as [Hpresent [Hmemsource Hmemwork]].
    destruct IH as [Hout [Hsource Hwork]].
    split; [cbn; now rewrite Hpresent, Hout |]; split.
    + constructor; [exact I | constructor; [exact Hmemsource | exact Hsource]].
    + change (1 + audit_finset_source_work (fxi_body_work ib) mem +
        fx_observe_forward_work ib events <=
        8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
        fx_forward_deps_budget EX ib rest).
      lia.
Qed.

Lemma fx_forward_constraints_adequate members later cs :
  let '(out, events) := fx_forward_constraints cb members later cs in
  out = forallb (fun c => if FinSet.mem EX (System.target S c) members then
    forallb (fun x => negb (FinSet.mem EX x later)) (System.deps SS c) else true) cs /\
  Forall (fx_observe_forward_event_source source) events /\
  fx_observe_forward_work ib events <= fx_forward_constraints_budget EX S SS ib members cs.
Proof.
  destruct Herase as [Hencode [Htarget [_ Hdeps]]].
  destruct Hbounded as [_ [Hencbound [Htbound [_ Hdbound]]]].
  induction cs as [|c rest IH].
  - cbn [fx_forward_constraints fx_forward_constraints_budget forallb fx_observe_forward_work
      fold_right fx_observe_forward_event_work]; repeat split; try lia;
      constructor; [exact I | constructor].
  - cbn [fx_forward_constraints fx_forward_constraints_budget forallb].
    pose proof (Htarget c) as Ht; pose proof (Htbound c) as Htb.
    pose proof (Htargetsource c) as Hts.
    destruct (fxi_target cb c) as [target target_body] eqn:Htc.
    cbn in Ht, Htb, Hts; subst target.
    pose proof (fx_forward_mem_adequate X C B EX cb ib source (System.target S c) members
      (Hencode _) (Hencbound _) (Hencsource _)) as Hmem.
    destruct (audit_finset_mem (fxi_encode cb) (System.target S c) members) as [present mem].
    cbn in Hmem; destruct Hmem as [Hpresent [Hmemsource Hmemwork]].
    destruct (fx_forward_constraints cb members later rest) as [out tail].
    cbn in IH; destruct IH as [Hout [Htailsource Htailwork]].
    destruct present.
    + pose proof (Hdeps c) as Hd; pose proof (Hdbound c) as Hdb.
      pose proof (Hdepssource c) as Hds.
      destruct (fxi_deps cb c) as [deps deps_body] eqn:Hdc.
      cbn in Hd, Hdb, Hds; subst deps.
      pose proof (fx_forward_deps_adequate later (System.deps SS c)) as Hscan.
      destruct (fx_forward_deps cb later (System.deps SS c)) as [current events].
      cbn in Hscan; destruct Hscan as [Hcurrent [Hscansource Hscanwork]].
      rewrite <- Hpresent; cbn; split; [now rewrite Hcurrent, Hout |]; split.
      * constructor; [exact I | constructor; [constructor; [exact Hts | constructor] |]].
        constructor; [exact Hmemsource | constructor; [constructor; [exact Hds | constructor] |]].
        apply Forall_app; split; assumption.
      * change (1 + ((3 + fxi_body_work ib target_body + 0) +
          (audit_finset_source_work (fxi_body_work ib) mem +
          ((3 + fxi_body_work ib deps_body + 0) + fx_observe_forward_work ib (events ++ tail)))) <=
          12 + fxi_target_bound ib c + fxi_encode_bound ib (System.target S c) +
          5 * Pos.size_nat (encode EX (System.target S c)) +
          (3 + fxi_deps_bound ib c + fx_forward_deps_budget EX ib (System.deps SS c)) +
          fx_forward_constraints_budget EX S SS ib members rest).
        rewrite fx_forward_work_app;
        unfold fxi_body_work in *; lia.
    + rewrite <- Hpresent; cbn; split; [exact Hout |]; split.
      * constructor; [exact I | constructor; [constructor; [exact Hts | constructor] |]].
        constructor; [exact Hmemsource | exact Htailsource].
      * change (1 + ((3 + fxi_body_work ib target_body + 0) +
          (audit_finset_source_work (fxi_body_work ib) mem + fx_observe_forward_work ib tail)) <=
          12 + fxi_target_bound ib c + fxi_encode_bound ib (System.target S c) +
          5 * Pos.size_nat (encode EX (System.target S c)) + 0 +
          fx_forward_constraints_budget EX S SS ib members rest).
        unfold fxi_body_work in *; lia.
Qed.

Lemma fx_forward_set_adequate input :
  let '(out, events) := audit_finset_of_list (fxi_encode cb) input in
  out = FinSet.of_list EX input /\ fxi_set_external_adequacy source events /\
  audit_finset_source_work (fxi_body_work ib) events <= fxi_set_input_budget EX ib input.
Proof.
  destruct Herase as [Hencode _].
  destruct Hbounded as [_ [Hencbound _]].
  pose proof (audit_finset_of_list_erases X B (fxi_encode cb) EX input
    (fun x _ => Hencode x)) as Hout.
  pose proof (audit_finset_of_list_source_bound X B (fxi_encode cb) (fxi_body_work ib) input)
    as Hwork.
  pose proof (fxi_set_budget_bound X C B EX cb ib input Hencode Hencbound) as Hbudget.
  pose proof (fx_forward_set_fold_source X C B cb source input Hencsource FinSet.empty) as Hsource.
  unfold audit_finset_of_list in Hout, Hwork |- *.
  destruct (audit_finset_fold (fxi_encode cb) input FinSet.empty) as [out events].
  cbn in *; repeat split; try assumption; lia.
Qed.

Lemma fx_forward_boundary_adequate component suffix :
  let '(out, events) := fx_forward_boundary cb (System.constraints S) component suffix in
  out = observation_boundary_check EX S SS component suffix /\
  Forall (fx_observe_forward_event_source source) events /\
  fx_observe_forward_work ib events <= fx_forward_boundary_budget EX S SS ib component suffix.
Proof.
  pose proof (fx_forward_set_adequate component) as Hmembers.
  pose proof (fx_forward_set_adequate (concat suffix)) as Hlater.
  unfold fx_forward_boundary, observation_boundary_check, fx_forward_boundary_budget.
  destruct (audit_finset_of_list (fxi_encode cb) component) as [members member_events].
  destruct (audit_finset_of_list (fxi_encode cb) (concat suffix)) as [later later_events].
  cbn in Hmembers, Hlater; destruct Hmembers as [Hmembers [Hmemberssource Hmemberswork]];
    destruct Hlater as [Hlater [Hlatersource Hlaterwork]].
  subst members later.
  pose proof (fx_forward_constraints_adequate (FinSet.of_list EX component)
    (FinSet.of_list EX (concat suffix)) (System.constraints S)) as Hconstraints.
  destruct (fx_forward_constraints cb (FinSet.of_list EX component)
    (FinSet.of_list EX (concat suffix)) (System.constraints S)) as [out events].
  cbn in Hconstraints; destruct Hconstraints as [Hout [Hsource Hwork]].
  split; [exact Hout |]; split.
  - constructor; [exact Hmemberssource | constructor; [exact I |]].
    constructor; [exact Hlatersource | exact Hsource].
  - change (audit_finset_source_work (fxi_body_work ib) member_events +
      ((2 + length suffix + length (concat suffix)) +
      (audit_finset_source_work (fxi_body_work ib) later_events +
        fx_observe_forward_work ib events)) <=
      2 + length suffix + length (concat suffix) + fxi_set_input_budget EX ib component +
      fxi_set_input_budget EX ib (concat suffix) +
      fx_forward_constraints_budget EX S SS ib (FinSet.of_list EX component)
        (System.constraints S)).
    lia.
Qed.

Lemma fx_forward_order_adequate order :
  let '(out, events) := fx_observe_forward cb (System.constraints S) order in
  out = forallb (fun boundary => observation_boundary_check EX S SS (fst boundary) (snd boundary))
    (observation_boundaries order) /\
  Forall (fx_observe_forward_event_source source) events /\
  fx_observe_forward_work ib events <= fx_observe_forward_budget EX S SS ib order.
Proof.
  induction order as [|component rest IH].
  - cbn [fx_observe_forward observation_boundaries forallb fx_observe_forward_budget
      fx_observe_forward_work fold_right fx_observe_forward_event_work].
    repeat split; try lia; constructor; [exact I | constructor].
  - cbn [fx_observe_forward observation_boundaries forallb fx_observe_forward_budget].
    pose proof (fx_forward_boundary_adequate component rest) as Hboundary.
    destruct (fx_forward_boundary cb (System.constraints S) component rest) as [here events].
    destruct (fx_observe_forward cb (System.constraints S) rest) as [later tail].
    cbn in Hboundary, IH; destruct Hboundary as [Hhere [Hsource Hwork]];
      destruct IH as [Hlater [Htailsource Htailwork]].
    split; [cbn; now rewrite Hhere, Hlater |]; split.
    + constructor; [exact I | apply Forall_app; split; assumption].
    + change (1 + fx_observe_forward_work ib (events ++ tail) <=
        1 + fx_forward_boundary_budget EX S SS ib component rest +
          fx_observe_forward_budget EX S SS ib rest).
      change (fx_observe_forward_work ib events <=
        fx_forward_boundary_budget EX S SS ib component rest) in Hwork.
      change (fx_observe_forward_work ib tail <=
        fx_observe_forward_budget EX S SS ib rest) in Htailwork.
      rewrite fx_forward_work_app; lia.
Qed.

End Forward.

(** Forward checking preserves its source result, captured callback bodies and input bound. *)
Theorem fx_observe_forward_source : fx_observe_forward_source_statement.
Proof.
  intros X C A B EX S SS cb ib source order Herase Hbounded Henc Htarget Hdeps.
  pose proof (fx_forward_order_adequate EX S SS cb ib source Herase Hbounded Henc Htarget Hdeps
    order) as Horder.
  unfold fx_observe_forward_run, observation_forward_check.
  destruct (fx_observe_forward cb (System.constraints S) order) as [out events].
  cbn in Horder; destruct Horder as [Hout [Hsource Hwork]].
  split; [constructor; [exact I | exact Hsource] |]; split; [exact Hout |].
  change ((2 + 2 * length order) + fx_observe_forward_work ib events <=
    2 + 2 * length order + fx_observe_forward_budget EX S SS ib order).
  lia.
Qed.
