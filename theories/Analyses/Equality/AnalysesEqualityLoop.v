(** * Indexed loop invariance with total-query fallbacks

    Closed listed queries use a countdown worklist.
    Other inside queries use the costed reference.
    For example, an unlisted pure nullary definition keeps its original finite-round classification.
    Builds on: AnalysesEqualityLoopCorrect, AnalysesEqualityLoopReference and BaseMap. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSemantics ProgramLink ProgramStrict.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityLoopReference AnalysesEqualityLoopWorklist AnalysesEqualityLoopCorrect.
Import List.ListNotations Cost.Notations Numbering.

Local Open Scope nat_scope.

Module NumberingLoop.

Section Invariance.
Context {N E V K G : Type} (np : problem N E V K G) (lp : loop_info N).
Let syntax := ssa np.
Let EV := Ssa.val_enc syntax.
Let values := Ssa.values syntax.

Definition inside x := body lp (Ssa.home syntax x).

(** A finite rule retains exactly the pure operation's inside-body dependency occurrences. *)
Definition rule x : option (list V) :=
  if inside x then
    match Ssa.def syntax x with
    | Op op args => if pure np op then Some (filter inside args) else None
    | _ => None
    end
  else None.

Definition rule_c x : Cost.t (option (list V)) :=
  let* in_body := NumberingLoopReference.inside_c np lp x in
  if in_body then
    Cost.step ;;
    let* def := Ssa.def_c syntax x in
    match def with
    | Op op args =>
      Cost.step ;;
      let* pure := pure_c np op in
      if pure then Cost.map (@Some (list V))
        (filter_c (fun y => Cost.step ;; NumberingLoopReference.inside_c np lp y) args)
      else Cost.ret None
    | _ => Cost.ret None
    end
  else Cost.ret None.

(** Classification charges the supplied dictionaries and returns the exact finite rule. *)
Theorem rule_value x : Cost.value (rule_c x) = rule x.
Proof.
  unfold rule_c, rule, inside; rewrite Cost.value_bind, NumberingLoopReference.inside_value.
  unfold syntax; destruct (body lp (Ssa.home (ssa np) x)); [|reflexivity].
  autorewrite with galois_cost; fold (Ssa.def (ssa np) x).
  destruct (Ssa.def (ssa np) x) as [op args|b i|]; [|reflexivity|reflexivity].
  autorewrite with galois_cost; unfold pure.
  destruct (Cost.value (pure_c np op)); [|reflexivity].
  autorewrite with galois_cost; rewrite ?value_filter_c; reflexivity.
Qed.

(** Computational finite preparation contains no representation or semantic proof fields. *)
Record finite : Type := Finite {
  universe : FinSet.t V;
  definitions : Map.t V (list V);
  countdown : NumberingLoopWorklist.prepared (V := V)
}.

Inductive preparation : Type :=
  | Accepted (data : finite)
  | Rejected.

Definition closed_entries_c nodes (entries : list (V * list V)) :=
  forallb_c (fun entry => Cost.step ;;
    forallb_c (fun y => Cost.step ;; FinSet.mem_c EV y nodes) (snd entry)) entries.

(** Closure validation observes every stored inside-body dependency through costed membership. *)
Theorem closed_entries_value nodes entries :
  Cost.value (closed_entries_c nodes entries) =
    forallb (fun entry => forallb (fun y => FinSet.mem EV y nodes) (snd entry)) entries.
Proof.
  unfold closed_entries_c; rewrite value_forallb_c.
  induction entries as [|entry rest IH]; [reflexivity|].
  cbn [forallb]; rewrite Cost.value_bind, value_forallb_c, IH; reflexivity.
Qed.

Definition prepare_finite_c nodes : Cost.t preparation :=
  let* order := FinSet.elements_c nodes in
  let* classified := NumberingSignature.tabulate_c EV rule_c order in
  let* rules := Map.filter_map_c (fun result => Cost.ret result) classified in
  let* entries := Map.elements_c rules in
  let* closed := closed_entries_c nodes entries in
  if closed then
    let* prepared := NumberingLoopWorklist.prepare_c EV nodes rules in
    Cost.ret (Accepted (Finite nodes rules prepared))
  else Cost.ret Rejected.

Definition prepare_finite nodes := Cost.value (prepare_finite_c nodes).

(** The checked preparation validates finite closure and exposes rejection separately. *)
Definition prepare_checked_c : Cost.t preparation :=
  let* nodes := FinSet.of_list_c EV values in prepare_finite_c nodes.

(** Finite construction reuses native map filtering and the single countdown preparation engine. *)
Theorem prepare_finite_equation nodes :
  prepare_finite nodes =
  let classified := NumberingSignature.tabulate EV rule_c (FinSet.elements nodes) in
  let rules := Map.filter_map (fun result => result) classified in
  let closed := forallb (fun entry =>
    forallb (fun y => FinSet.mem EV y nodes) (snd entry)) (Map.elements rules) in
  if closed then
    Accepted (Finite nodes rules (NumberingLoopWorklist.prepare EV nodes rules))
  else Rejected.
Proof.
  unfold prepare_finite, prepare_finite_c; rewrite !Cost.value_bind.
  rewrite Map.filter_map_c_value, closed_entries_value.
  set (rules := Map.filter_map (fun result => result)
    (NumberingSignature.tabulate EV rule_c (FinSet.elements nodes))).
  change (Cost.value
    (if forallb (fun entry => forallb (fun y => FinSet.mem EV y nodes) (snd entry))
      (Map.elements rules)
     then
       let* prepared := NumberingLoopWorklist.prepare_c EV nodes rules in
       Cost.ret (Accepted (Finite nodes rules prepared))
     else Cost.ret Rejected) =
    if forallb (fun entry => forallb (fun y => FinSet.mem EV y nodes) (snd entry))
      (Map.elements rules)
    then Accepted (Finite nodes rules (NumberingLoopWorklist.prepare EV nodes rules))
    else Rejected).
  destruct (forallb (fun entry => forallb (fun y => FinSet.mem EV y nodes) (snd entry))
    (Map.elements rules)); reflexivity.
Qed.

Inductive path : Type :=
  | Outside
  | Indexed
  | Unlisted_fallback
  | Malformed_fallback
  | Exhausted_fallback.

(** A query reports its computational branch without changing its Boolean contract. *)
Record answer : Type := Answer {
  classification : bool;
  route : path
}.

Definition fallback_c branch x : Cost.t answer :=
  Cost.map (fun result => Answer result branch) (NumberingLoopReference.reference_c np lp x).

Definition query_c x : Cost.t answer :=
  let* in_body := NumberingLoopReference.inside_c np lp x in
  if in_body then
    let* nodes := FinSet.of_list_c EV values in
    let* listed := FinSet.mem_c EV x nodes in
    if listed then
      let* prepared := prepare_finite_c nodes in
      match prepared with
      | Rejected => fallback_c Malformed_fallback x
      | Accepted data =>
        let* solved := NumberingLoopWorklist.solve_prepared_c EV (countdown data) in
        match solved with
        | inl _ => fallback_c Exhausted_fallback x
        | inr final =>
          let* result := FinSet.mem_c EV x (NumberingLoopWorklist.marked final) in
          Cost.ret (Answer result Indexed)
        end
      end
    else fallback_c Unlisted_fallback x
  else Cost.ret (Answer true Outside).

(** The public computational entry needs data and callbacks, without any law proof argument. *)
Definition invariant_in_c x := Cost.map classification (query_c x).

Definition invariant_in x := Cost.value (invariant_in_c x).

(** The public reference retains the original total-query finite-round specification. *)
Definition invariant_in_ref x := NumberingLoopReference.invariant_in_ref np lp x.

(** Every fallback is charged and preserves the total reference Boolean result. *)
Theorem fallback_value branch x :
  classification (Cost.value (fallback_c branch x)) = invariant_in_ref x.
Proof.
  unfold fallback_c; rewrite Cost.value_map.
  exact (NumberingLoopReference.reference_agrees np lp x).
Qed.

Definition rules_of nodes :=
  Map.filter_map (fun result => result)
    (NumberingSignature.tabulate EV rule_c (FinSet.elements nodes)).

(** Native filtering preserves the representation validity established by tabulation. *)
Theorem rules_wf nodes : Map.wf EV (rules_of nodes).
Proof.
  apply Map.wf_filter_map, NumberingSignature.tabulate_wf.
Qed.

Section Laws.
Context (HV : encoding_laws EV).

(** A listed rule lookup agrees with the actual body, definition and purity dictionaries. *)
Theorem rules_get nodes x :
  FinSet.wf EV nodes -> FinSet.mem EV x nodes = true ->
  Map.get EV x (rules_of nodes) = rule x.
Proof.
  intros Hwf Hmember; unfold rules_of; rewrite Map.get_filter_map.
  rewrite (NumberingSignature.tabulate_get EV HV)
    by (apply (proj2 (FinSet.elements_spec EV HV x nodes Hwf)); exact Hmember).
  apply rule_value.
Qed.

Local Lemma rules_absent nodes x :
  ~ In x (FinSet.elements nodes) -> Map.get EV x (rules_of nodes) = None.
Proof.
  intro Hnot; unfold rules_of; rewrite Map.get_filter_map.
  rewrite (NumberingSignature.tabulate_absent EV HV) by exact Hnot; reflexivity.
Qed.

(** Every rule key comes from the actual finite node universe. *)
Theorem rules_supported nodes :
  FinSet.wf EV nodes ->
  NumberingLoopCorrect.rules_supported EV nodes (rules_of nodes).
Proof.
  intros Hwf x deps Hget.
  destruct (in_dec (eqb_dec EV HV) x (FinSet.elements nodes)) as [Hin|Hnot].
  - exact (proj1 (FinSet.elements_spec EV HV x nodes Hwf) Hin).
  - rewrite (rules_absent nodes x Hnot) in Hget; discriminate.
Qed.

(** Preparation laws describe stored syntax and validated closure, never a desired analysis result. *)
Record finite_laws nodes data : Prop := {
  universe_same : universe data = nodes;
  definitions_same : definitions data = rules_of nodes;
  dependencies_closed : forall x deps, Map.get EV x (definitions data) = Some deps ->
    forallb (fun y => FinSet.mem EV y nodes) deps = true;
  countdown_same : countdown data =
    NumberingLoopWorklist.prepare EV nodes (definitions data)
}.

(** Accepted finite data derives all static laws from the actual constructor and closure check. *)
Theorem prepare_finite_laws nodes data :
  prepare_finite nodes = Accepted data -> finite_laws nodes data.
Proof.
  rewrite prepare_finite_equation; cbn zeta; fold (rules_of nodes).
  destruct (forallb (fun entry => forallb (fun y => FinSet.mem EV y nodes) (snd entry))
    (Map.elements (rules_of nodes))) eqn:Hclosed; [|discriminate].
  intro Haccepted; injection Haccepted as <-; constructor.
  - reflexivity.
  - reflexivity.
  - intros x deps Hget.
    exact (proj1 (forallb_forall _ _) Hclosed (x, deps)
      (proj2 (Map.elements_spec EV HV x deps (rules_of nodes) (rules_wf nodes)) Hget)).
  - reflexivity.
Qed.

(** The finite deduplicated universe never exceeds the raw inventory length. *)
Theorem universe_bound : FinSet.size (FinSet.of_list EV values) <= length values.
Proof.
  rewrite FinSet.size_elements; apply NoDup_incl_length.
  - exact (FinSet.elements_nodup EV _ (FinSet.wf_of_list EV values)).
  - intros x Hin.
    apply (proj1 (NumberingSignature.listed_spec EV HV values x)).
    exact (proj1 (FinSet.elements_spec EV HV x _ (FinSet.wf_of_list EV values)) Hin).
Qed.

Local Lemma forallb_inside (f g : V -> bool) args :
  (forall y, In y args -> inside y = false -> f y = true) ->
  (forall y, In y args -> inside y = true -> f y = g y) ->
  forallb f args = forallb g (filter inside args).
Proof.
  revert f g; induction args as [|y rest IH]; intros f g Houtside Hinside; [reflexivity|].
  cbn [forallb filter]; destruct (inside y) eqn:Hbody.
  - rewrite (Hinside y (or_introl eq_refl) Hbody); cbn [forallb].
    rewrite (IH f g); [reflexivity| |].
    + intros z Hz; apply Houtside; now right.
    + intros z Hz; apply Hinside; now right.
  - rewrite (Houtside y (or_introl eq_refl) Hbody); cbn [andb].
    apply (IH f g).
    + intros z Hz; apply Houtside; now right.
    + intros z Hz; apply Hinside; now right.
Qed.

(** Accepted finite rules reproduce every original round on listed inside-body queries. *)
Theorem finite_reference nodes data count x :
  FinSet.wf EV nodes -> finite_laws nodes data ->
  FinSet.mem EV x nodes = true -> inside x = true ->
  NumberingLoopReference.after np lp count (NumberingLoopReference.initial np lp) x =
    NumberingLoopWorklist.reference EV (definitions data) count x.
Proof.
  intros Hwf Hdata; revert x; induction count as [|count IH]; intros x Hmember Hinside.
  - unfold NumberingLoopReference.initial; change (negb (inside x) = false).
    now rewrite Hinside.
  - rewrite NumberingLoopReference.after_round.
    unfold NumberingLoopReference.round; fold syntax; fold (inside x); rewrite Hinside.
    cbn [NumberingLoopWorklist.reference].
    assert (Hlookup : Map.get EV x (definitions data) = rule x).
    { rewrite (definitions_same _ _ Hdata); now apply rules_get. }
    rewrite Hlookup; unfold rule; rewrite Hinside.
    destruct (Ssa.def syntax x) as [op args|b i|] eqn:Hdef; [|reflexivity|reflexivity].
    destruct (pure np op) eqn:Hp; [|reflexivity].
    cbn [andb]; apply forallb_inside.
    + intros y Hy Houtside.
      apply NumberingLoopReference.reference_outside; exact Houtside.
    + intros y Hy Hin.
      apply IH; [|exact Hin].
      assert (Hrule : Map.get EV x (definitions data) = Some (filter inside args)).
      { rewrite Hlookup; unfold rule; rewrite Hinside, Hdef, Hp; reflexivity. }
      exact (proj1 (forallb_forall _ _) (dependencies_closed _ _ Hdata x _ Hrule) y
        (proj2 (filter_In inside y args) (conj Hy Hin))).
Qed.

(** Accepted actual finite preparation supplies the kernel's own representation and support duties. *)
Theorem finite_result_agrees data x :
  finite_laws (FinSet.of_list EV values) data ->
  FinSet.mem EV x (FinSet.of_list EV values) = true -> inside x = true ->
  FinSet.mem EV x (NumberingLoopWorklist.marked
    (NumberingLoopWorklist.last_state
      (Cost.value (NumberingLoopWorklist.solve_prepared_c EV (countdown data))))) =
      invariant_in_ref x.
Proof.
  intros Hdata Hmember Hinside.
  set (nodes := FinSet.of_list EV values).
  assert (Hnodes : FinSet.wf EV nodes) by apply FinSet.wf_of_list.
  assert (Hdefinitions : Map.wf EV (definitions data)).
  { rewrite (definitions_same _ _ Hdata); apply rules_wf. }
  assert (Hsupported : NumberingLoopCorrect.rules_supported EV nodes (definitions data)).
  { rewrite (definitions_same _ _ Hdata); now apply rules_supported. }
  rewrite (countdown_same _ _ Hdata).
  change (FinSet.mem EV x (NumberingLoopWorklist.marked
    (NumberingLoopWorklist.last_state
      (Cost.value (NumberingLoopWorklist.solve_c EV nodes (definitions data))))) =
    invariant_in_ref x).
  rewrite (NumberingLoopCorrect.solve_agrees EV HV nodes (definitions data) (length values)
    Hnodes Hdefinitions Hsupported universe_bound x).
  symmetry; unfold invariant_in_ref, NumberingLoopReference.invariant_in_ref.
  exact (finite_reference nodes data (length values) x Hnodes Hdata Hmember Hinside).
Qed.

(** Accepted actual preparation cannot exhaust its finite worklist budget. *)
Theorem finite_finishes data :
  finite_laws (FinSet.of_list EV values) data ->
  exists final,
    Cost.value (NumberingLoopWorklist.solve_prepared_c EV (countdown data)) = inr final.
Proof.
  intro Hdata.
  assert (Hdefinitions : Map.wf EV (definitions data)).
  { rewrite (definitions_same _ _ Hdata); apply rules_wf. }
  destruct (NumberingLoopWorklist.solve_finishes EV HV (FinSet.of_list EV values)
    (definitions data) (FinSet.wf_of_list EV values) Hdefinitions)
    as [final [Hresult _]].
  exists final; rewrite (countdown_same _ _ Hdata).
  exact Hresult.
Qed.

(** Agreement is universal over raw syntax, inventories and queries under the stated value-key law.
    No closure or listed-query premise is needed because all rejected branches use the costed reference. *)
Theorem invariant_in_agrees x : invariant_in x = invariant_in_ref x.
Proof.
  unfold invariant_in, invariant_in_c; rewrite Cost.value_map.
  unfold query_c; rewrite Cost.value_bind, NumberingLoopReference.inside_value.
  fold syntax; fold (inside x); destruct (inside x) eqn:Hinside.
  - rewrite Cost.value_bind; fold (FinSet.of_list EV values).
    rewrite Cost.value_bind; fold (FinSet.mem EV x (FinSet.of_list EV values)).
    destruct (FinSet.mem EV x (FinSet.of_list EV values)) eqn:Hmember.
    + rewrite Cost.value_bind; fold (prepare_finite (FinSet.of_list EV values)).
      destruct (prepare_finite (FinSet.of_list EV values)) as [data|] eqn:Hprepared.
      * rewrite Cost.value_bind.
        destruct (Cost.value (NumberingLoopWorklist.solve_prepared_c EV (countdown data)))
          as [partial|final] eqn:Hsolve.
        -- apply fallback_value.
        -- rewrite Cost.value_bind.
           change (FinSet.mem EV x (NumberingLoopWorklist.marked final) = invariant_in_ref x).
           pose proof (finite_result_agrees data x
             (prepare_finite_laws _ _ Hprepared) Hmember Hinside) as Hagrees.
           rewrite Hsolve in Hagrees; exact Hagrees.
      * apply fallback_value.
    + apply fallback_value.
  - change (true = invariant_in_ref x); symmetry.
    unfold invariant_in_ref, NumberingLoopReference.invariant_in_ref.
    apply NumberingLoopReference.reference_outside; exact Hinside.
Qed.

End Laws.

End Invariance.

(** Once a recognized invariant changes, stable direct operands prevent a second change.
    The three-run and option-valued statement is the unchanged legacy semantic contract. *)
Theorem loop_invariant_sound {S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (eval : K -> list C -> option C) (holds : G -> list C -> Prop)
    (lp : loop_info N) (x : V) (HV : encoding_laws (Ssa.val_enc (ssa np))) :
  ssa_laws m (ssa np) sl eval holds -> strict_ssa_laws m (ssa np) sl ->
  loop_laws m np sl eval -> loop_info_wf (Cfg.graph (Ssa.cfg (ssa np))) lp ->
  invariant_in np lp x = true -> loop_operands_stable m np sl lp x ->
  forall s events1 u1 events2 u2 events3 u3, reachable_state m s ->
    exec_in m (fun u => body lp (Link.point (SsaLink.link sl) u) = true) s events1 u1 ->
    exec_in m (fun u => body lp (Link.point (SsaLink.link sl) u) = true) u1 events2 u2 ->
    exec_in m (fun u => body lp (Link.point (SsaLink.link sl) u) = true) u2 events3 u3 ->
    SsaLink.val sl u1 x <> SsaLink.val sl u2 x ->
    SsaLink.val sl u2 x = SsaLink.val sl u3 x.
Proof.
  intros Hssa Hstrict Hloop Hwf Hinvariant Hstable.
  apply (NumberingLoopReference.invariant_in_ref_sound m np sl eval holds lp x
    Hssa Hstrict Hloop Hwf).
  - change (invariant_in_ref np lp x = true).
    rewrite <- (invariant_in_agrees np lp HV x); exact Hinvariant.
  - exact Hstable.
Qed.

End NumberingLoop.
