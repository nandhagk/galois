(** * Indexed loop invariance with total-query fallbacks

    Closed listed queries use a countdown worklist.
    Other inside queries use the costed reference.
    For example, an unlisted pure nullary definition keeps its original finite-round classification.
    Builds on: AnalysesEqualityLoopCorrect, AnalysesEqualityLoopReference and BaseMap. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseMapCost BaseSet BaseTrieCost.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSemantics ProgramLink ProgramStrict.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityLoopReference AnalysesEqualityLoopWorklist AnalysesEqualityLoopCorrect
  AnalysesEqualityLoopCost.
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

(** Primitive budgets concern finite listed values and their actual operand callbacks. *)
Record primitive_prices nodes (e w c : BinNums.N) (arity : nat) : Prop := LoopPrices {
  listed_prices : forall x, In x (FinSet.elements nodes) ->
    (Cost.ticks (encode_c EV x) <= e)%N /\ (key_bits EV x <= w)%N /\
    (Cost.ticks (Ssa.home_c syntax x) <= c)%N /\
    (Cost.ticks (body_c lp (Ssa.home syntax x)) <= c)%N /\
    (Cost.ticks (Ssa.def_c syntax x) <= c)%N;
  operand_prices : forall x op args, In x (FinSet.elements nodes) ->
    Ssa.def syntax x = Op op args ->
    (Cost.ticks (pure_c np op) <= c)%N /\ length args <= arity /\
    forall y, In y args ->
      (Cost.ticks (encode_c EV y) <= e)%N /\ (key_bits EV y <= w)%N /\
      (Cost.ticks (Ssa.home_c syntax y) <= c)%N /\
      (Cost.ticks (body_c lp (Ssa.home syntax y)) <= c)%N
}.

(** A body observation includes the home and body dictionary invocations and their callee costs. *)
Theorem inside_cost x c :
  (Cost.ticks (Ssa.home_c syntax x) <= c)%N ->
  (Cost.ticks (body_c lp (Ssa.home syntax x)) <= c)%N ->
  (Cost.ticks (NumberingLoopReference.inside_c np lp x) <= 2 + 2 * c)%N.
Proof.
  intros Hhome Hbody; unfold NumberingLoopReference.inside_c.
  autorewrite with galois_cost; fold syntax; fold (Ssa.home syntax x); lia.
Qed.

(** Rule classification accounts for the static definition, purity and every operand observation. *)
Definition rule_price (c : BinNums.N) (arity : nat) : BinNums.N :=
  4 + 4 * c + N.of_nat arity * (4 + 2 * c).

(** Finite primitive budgets derive the price of the owned rule computation. *)
Theorem rule_cost nodes e w c arity x :
  primitive_prices nodes e w c arity -> In x (FinSet.elements nodes) ->
  (Cost.ticks (rule_c x) <= rule_price c arity)%N.
Proof.
  intros Hprices Hx.
  destruct (listed_prices _ _ _ _ _ Hprices x Hx) as [_ [_ [Hhome [Hbody Hdef]]]].
  pose proof (inside_cost x c Hhome Hbody) as Hinside.
  unfold rule_c; rewrite Cost.ticks_bind, NumberingLoopReference.inside_value.
  fold syntax; fold (inside x); destruct (inside x);
    [|rewrite Cost.ticks_ret; unfold rule_price; lia].
  autorewrite with galois_cost; fold (Ssa.def syntax x).
  destruct (Ssa.def syntax x) as [op args|block index|] eqn:Hdefinition;
    try (rewrite Cost.ticks_ret; unfold rule_price; lia).
  destruct (operand_prices _ _ _ _ _ Hprices x op args Hx Hdefinition)
    as [Hpure [Harity Hargs]].
  autorewrite with galois_cost.
  destruct (Cost.value (pure_c np op));
    [rewrite Cost.ticks_map|rewrite Cost.ticks_ret; unfold rule_price; lia].
  pose proof (NumberingLoopCost.filter_visited_cost
    (fun y => Cost.step ;; NumberingLoopReference.inside_c np lp y) args (3 + 2 * c)%N)
    as Hfilter.
  assert (Hcallbacks : forall y, In y args ->
    (Cost.ticks (Cost.step ;; NumberingLoopReference.inside_c np lp y) <= 3 + 2 * c)%N).
  { intros y Hy; destruct (Hargs y Hy) as [_ [_ [Hyhome Hybody]]].
    pose proof (inside_cost y c Hyhome Hybody) as Hyinside; autorewrite with galois_cost; lia. }
  specialize (Hfilter Hcallbacks); unfold rule_price; nia.
Qed.

Local Lemma present_rule nodes x deps :
  FinSet.wf EV nodes -> Map.get EV x (rules_of nodes) = Some deps ->
  exists op args, In x (FinSet.elements nodes) /\ Ssa.def syntax x = Op op args /\
    deps = filter inside args.
Proof.
  intros Hwf Hget.
  pose proof (rules_supported nodes Hwf x deps Hget) as Hmember.
  assert (Hx : In x (FinSet.elements nodes)).
  { exact (proj2 (FinSet.elements_spec EV HV x nodes Hwf) Hmember). }
  rewrite (rules_get nodes x Hwf Hmember) in Hget.
  unfold rule in Hget; destruct (inside x); [|discriminate].
  destruct (Ssa.def syntax x) as [op args|block index|] eqn:Hdef; try discriminate.
  destruct (pure np op); [|discriminate].
  injection Hget as <-; exists op, args; now repeat split.
Qed.

Local Lemma rule_arity nodes e w c arity x deps :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  Map.get EV x (rules_of nodes) = Some deps -> length deps <= arity.
Proof.
  intros Hwf Hprices Hget.
  destruct (present_rule nodes x deps Hwf Hget) as [op [args [Hx [Hdef ->]]]].
  destruct (operand_prices _ _ _ _ _ Hprices x op args Hx Hdef) as [_ [Harity _]].
  pose proof (filter_length inside args); lia.
Qed.

(** Primitive prices for the countdown engine follow from the actual finite SSA rule map. *)
Theorem kernel_prices nodes e w c arity :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  NumberingLoopCost.primitive_prices EV nodes (rules_of nodes) e w.
Proof.
  intros Hwf Hprices x [Hx|Hx].
  - destruct (listed_prices _ _ _ _ _ Hprices x Hx) as [He [Hw _]]; now split.
  - apply in_map_iff in Hx as [[dependency user] [Heq Hrow]]; cbn [fst] in Heq; subst dependency.
    unfold NumberingLoopCost.rows in Hrow; apply in_flat_map in Hrow
      as [[owner deps] [Hentry Hrow]].
    apply in_map_iff in Hrow as [dependency [Heq Hin]]; injection Heq as <- <-.
    apply (Map.elements_spec EV HV owner deps _ (rules_wf nodes)) in Hentry.
    destruct (present_rule nodes owner deps Hwf Hentry) as [op [args [Howner [Hdef Hdeps]]]].
    rewrite Hdeps in Hin; apply filter_In in Hin as [Hin _].
    destruct (operand_prices _ _ _ _ _ Hprices owner op args Howner Hdef)
      as [_ [_ Hargs]].
    destruct (Hargs dependency Hin) as [He [Hw _]]; now split.
Qed.

(** The actual finite rule map has at most one arity budget per distinct listed value. *)
Theorem rule_mass nodes e w c arity :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  (N.of_nat (length (NumberingLoopCost.rows (rules_of nodes))) <=
    N.of_nat (FinSet.size nodes) * N.of_nat arity)%N.
Proof.
  intros Hwf Hprices.
  pose proof (NumberingLoopCost.definitions_size EV HV nodes (rules_of nodes)
    Hwf (rules_wf nodes) (rules_supported nodes Hwf)) as Hsize.
  assert (Hmass : (NumberingLoopCost.dependency_mass (Map.elements (rules_of nodes)) <=
    N.of_nat (length (Map.elements (rules_of nodes))) * N.of_nat arity)%N).
  { assert (Hentries : forall x deps, In (x, deps) (Map.elements (rules_of nodes)) ->
      length deps <= arity).
    { intros x deps Hin; apply (rule_arity nodes e w c arity x deps Hwf Hprices).
      exact (proj1 (Map.elements_spec EV HV x deps _ (rules_wf nodes)) Hin). }
    clear Hsize; generalize dependent (Map.elements (rules_of nodes)); intros entries Hentries.
    induction entries as [|[x deps] rest IH]; [reflexivity|].
    cbn [NumberingLoopCost.dependency_mass fold_right snd length]; rewrite Nat2N.inj_succ.
    fold (NumberingLoopCost.dependency_mass rest).
    pose proof (Hentries x deps (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y args Hin => Hentries y args (or_intror Hin))); nia. }
  rewrite <- Map.size_elements in Hmass.
  rewrite NumberingLoopCost.rows_length; nia.
Qed.

Local Lemma rule_dependency_prices nodes e w c arity x deps y :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  Map.get EV x (rules_of nodes) = Some deps -> In y deps ->
  (Cost.ticks (encode_c EV y) <= e)%N /\ (key_bits EV y <= w)%N.
Proof.
  intros Hwf Hprices Hget Hy.
  destruct (present_rule nodes x deps Hwf Hget) as [op [args [Hx [Hdef ->]]]].
  apply filter_In in Hy as [Hy _].
  destruct (operand_prices _ _ _ _ _ Hprices x op args Hx Hdef) as [_ [_ Hargs]].
  destruct (Hargs y Hy) as [He [Hw _]]; now split.
Qed.

Local Lemma forallb_visited_cost {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> (Cost.ticks (f x) <= k)%N) ->
  (Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (k + 1))%N.
Proof.
  induction xs as [|x rest IH]; intro Hprices; [reflexivity|].
  rewrite ticks_forallb_c_cons; cbn [length]; rewrite Nat2N.inj_succ.
  pose proof (Hprices x (or_introl eq_refl)) as Hhead.
  specialize (IH (fun y Hy => Hprices y (or_intror Hy))).
  destruct (Cost.value (f x)); nia.
Qed.

Local Lemma closed_entries_cost nodes e w c arity :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  (Cost.ticks (closed_entries_c nodes (Map.elements (rules_of nodes))) <=
    N.of_nat (FinSet.size nodes) *
      (2 + N.of_nat arity * (2 + NumberingLoopCost.key_price e w)))%N.
Proof.
  intros Hwf Hprices.
  pose proof (NumberingLoopCost.definitions_size EV HV nodes (rules_of nodes)
    Hwf (rules_wf nodes) (rules_supported nodes Hwf)) as Hsize.
  unfold closed_entries_c.
  eapply N.le_trans; [apply (forallb_visited_cost _
    _ (1 + N.of_nat arity * (2 + NumberingLoopCost.key_price e w))%N)|].
  - intros [x deps] Hin; autorewrite with galois_cost; cbn [snd].
    pose proof (proj1 (Map.elements_spec EV HV x deps _ (rules_wf nodes)) Hin) as Hget.
    pose proof (rule_arity nodes e w c arity x deps Hwf Hprices Hget) as Harity.
    pose proof (forallb_visited_cost (fun y => Cost.step ;; FinSet.mem_c EV y nodes)
      deps (1 + NumberingLoopCost.key_price e w)%N) as Hdeps.
    assert (Hdep_prices : forall y, In y deps ->
      (Cost.ticks (Cost.step ;; FinSet.mem_c EV y nodes) <=
        1 + NumberingLoopCost.key_price e w)%N).
    { intros y Hy; destruct (rule_dependency_prices nodes e w c arity x deps y
        Hwf Hprices Hget Hy) as [He Hw].
      autorewrite with galois_cost; unfold FinSet.mem_c; rewrite Map.mem_cost.
      fold (key_bits EV y); unfold NumberingLoopCost.key_price; lia. }
    specialize (Hdeps Hdep_prices); nia.
  - rewrite <- Map.size_elements.
    replace (1 + N.of_nat arity * (2 + NumberingLoopCost.key_price e w) + 1)%N with
      (2 + N.of_nat arity * (2 + NumberingLoopCost.key_price e w))%N by lia.
    apply N.mul_le_mono_r; lia.
Qed.

Local Lemma classified_member nodes x result :
  Map.get EV x (NumberingSignature.tabulate EV rule_c (FinSet.elements nodes)) = Some result ->
  In x (FinSet.elements nodes).
Proof.
  intro Hget; destruct (in_dec (eqb_dec EV HV) x (FinSet.elements nodes)) as [Hin|Hnot];
    [exact Hin|].
  rewrite (NumberingSignature.tabulate_absent EV HV rule_c _ x Hnot) in Hget; discriminate.
Qed.

Local Lemma zero_sum {A B} (entries : list (A * option B)) :
  fold_right (fun entry total => Cost.ticks (Cost.ret (snd entry)) + total)%N 0%N entries = 0%N.
Proof.
  induction entries as [|entry rest IH]; cbn [fold_right]; rewrite ?Cost.ticks_ret, ?IH;
    reflexivity.
Qed.

Local Lemma of_nat_le n m : n <= m -> (N.of_nat n <= N.of_nat m)%N.
Proof.
  intro Hle; induction Hle; [reflexivity|rewrite Nat2N.inj_succ; lia].
Qed.

(** The preparation constant includes SSA callbacks, native filtering and countdown preparation. *)
Definition preparation_k : BinNums.N :=
  128 + 16 * TrieCost.trie_k + 4 * NumberingLoopCost.prepare_k.

Local Lemma preparation_sum n a e w c :
  (TrieCost.trie_k * (1 + n * w) + n +
    (n * (4 + e + w + (4 + 4 * c + a * (4 + 2 * c))) +
    (2 * n * w + (TrieCost.trie_k * (1 + n * w) +
    (n * (2 + a * (2 + NumberingLoopCost.key_price e w)) +
      NumberingLoopCost.prepare_k * (1 + n + n * a) * (1 + e + w))))) <=
    preparation_k * (1 + n) * (1 + a) * (1 + e + w + c))%N.
Proof.
  unfold preparation_k, NumberingLoopCost.key_price; nia.
Qed.

(** Complete finite preparation is priced from finite SSA primitives, even when closure rejects. *)
Theorem preparation_cost nodes e w c arity :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  (Cost.ticks (prepare_finite_c nodes) <= preparation_k *
    (1 + N.of_nat (FinSet.size nodes)) * (1 + N.of_nat arity) * (1 + e + w + c))%N.
Proof.
  intros Hwf Hprices.
  set (classified := NumberingSignature.tabulate EV rule_c (FinSet.elements nodes)).
  assert (Hclassified : Map.wf EV classified) by apply NumberingSignature.tabulate_wf.
  assert (Hsize : Map.size classified <= FinSet.size nodes).
  { rewrite FinSet.size_elements.
    apply (Map.size_support_bound EV HV (FinSet.elements nodes) classified Hclassified).
    intros x result Hget; exact (classified_member nodes x result Hget). }
  assert (Hwidth : forall x result, Map.get EV x classified = Some result ->
    (key_bits EV x <= w)%N).
  { intros x result Hget.
    exact (proj1 (proj2 (listed_prices _ _ _ _ _ Hprices x
      (classified_member nodes x result Hget)))). }
  pose proof (MapCost.elements_numeric_cost EV nodes w Hwf) as Hnodes.
  assert (Hnode_width : forall x (u : unit), Map.get EV x nodes = Some u ->
    (key_bits EV x <= w)%N).
  { intros x [] Hget.
    pose proof (proj2 (FinSet.mem_spec EV x nodes) Hget) as Hmem.
    exact (proj1 (proj2 (listed_prices _ _ _ _ _ Hprices x
      (proj2 (FinSet.elements_spec EV HV x nodes Hwf) Hmem)))). }
  specialize (Hnodes Hnode_width); rewrite <- FinSet.size_backend in Hnodes.
  pose proof (NumberingSignature.tabulate_cost EV rule_c (FinSet.elements nodes)
    e w (rule_price c arity)) as Htabulate.
  specialize (Htabulate (fun x Hx => conj
    (proj1 (listed_prices _ _ _ _ _ Hprices x Hx))
    (conj (proj1 (proj2 (listed_prices _ _ _ _ _ Hprices x Hx)))
      (rule_cost nodes e w c arity x Hprices Hx)))).
  rewrite <- FinSet.size_elements in Htabulate.
  pose proof (MapCost.filter_map_numeric_cost EV (fun result => Cost.ret result)
    classified w Hclassified Hwidth) as Hfilter.
  rewrite zero_sum in Hfilter.
  assert (Hfiltered : Cost.value (Map.filter_map_c (fun result => Cost.ret result) classified) =
    rules_of nodes).
  { rewrite Map.filter_map_c_value; reflexivity. }
  pose proof (NumberingLoopCost.definitions_size EV HV nodes (rules_of nodes)
    Hwf (rules_wf nodes) (rules_supported nodes Hwf)) as Hrule_size.
  pose proof (of_nat_le _ _ Hrule_size) as Hrule_size_N.
  pose proof (MapCost.elements_numeric_cost EV (rules_of nodes) w (rules_wf nodes))
    as Hentries.
  specialize (Hentries (fun x deps Hget => Hnode_width x tt
    (proj1 (FinSet.mem_spec EV x nodes) (rules_supported nodes Hwf x deps Hget)))).
  pose proof (closed_entries_cost nodes e w c arity Hwf Hprices) as Hclosed.
  assert (Hfilter_bound : (Cost.ticks (Map.filter_map_c (fun result => Cost.ret result)
    classified) <= 2 * N.of_nat (FinSet.size nodes) * w)%N).
  { rewrite N.add_0_r in Hfilter; eapply N.le_trans; [exact Hfilter|].
    apply N.mul_le_mono_r, N.mul_le_mono_l.
    exact (of_nat_le _ _ Hsize). }
  assert (Hentries_bound : (Cost.ticks (Map.elements_c (rules_of nodes)) <=
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size nodes) * w))%N).
  { eapply N.le_trans; [exact Hentries|].
    apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r; exact Hrule_size_N. }
  pose proof (NumberingLoopCost.prepare_cost EV HV nodes (rules_of nodes) e w
    Hwf (rules_wf nodes) (rules_supported nodes Hwf) (kernel_prices nodes e w c arity Hwf Hprices))
    as Hcountdown.
  pose proof (rule_mass nodes e w c arity Hwf Hprices) as Hmass.
  assert (Hcountdown_bound :
    (Cost.ticks (NumberingLoopWorklist.prepare_c EV nodes (rules_of nodes)) <=
      NumberingLoopCost.prepare_k * (1 + N.of_nat (FinSet.size nodes) +
        N.of_nat (FinSet.size nodes) * N.of_nat arity) * (1 + e + w))%N) by nia.
  unfold prepare_finite_c; rewrite !Cost.ticks_bind.
  fold (FinSet.elements nodes).
  fold (NumberingSignature.tabulate EV rule_c (FinSet.elements nodes)).
  fold classified; rewrite Hfiltered; fold (Map.elements (rules_of nodes)).
  assert (Hrest :
    (Cost.ticks
      (if Cost.value (closed_entries_c nodes (Map.elements (rules_of nodes))) then
         let* prepared := NumberingLoopWorklist.prepare_c EV nodes (rules_of nodes) in
         Cost.ret (Accepted (Finite nodes (rules_of nodes) prepared))
       else Cost.ret Rejected) <=
      NumberingLoopCost.prepare_k * (1 + N.of_nat (FinSet.size nodes) +
        N.of_nat (FinSet.size nodes) * N.of_nat arity) * (1 + e + w))%N).
  { destruct (Cost.value (closed_entries_c nodes (Map.elements (rules_of nodes))));
      autorewrite with galois_cost; lia. }
  eapply N.le_trans.
  - apply N.add_le_mono.
    + rewrite FinSet.elements_cost_equation; apply N.add_le_mono_r; exact Hnodes.
    + apply N.add_le_mono; [exact Htabulate|].
      apply N.add_le_mono.
      * exact Hfilter_bound.
      * apply N.add_le_mono.
        -- exact Hentries_bound.
        -- apply N.add_le_mono; [exact Hclosed|exact Hrest].
  - unfold rule_price; apply preparation_sum.
Qed.

(** The fast domain requires closure only for the finite stored inside-body dependencies. *)
Definition closed_inventory nodes : Prop :=
  forall x deps, Map.get EV x (rules_of nodes) = Some deps ->
    forallb (fun y => FinSet.mem EV y nodes) deps = true.

(** The actual closure validator accepts every inventory in the explicit finite fast domain. *)
Theorem closed_preparation nodes :
  closed_inventory nodes -> exists data, prepare_finite nodes = Accepted data.
Proof.
  intro Hclosed; rewrite prepare_finite_equation; cbn zeta; fold (rules_of nodes).
  assert (Htest : forallb (fun entry =>
    forallb (fun y => FinSet.mem EV y nodes) (snd entry))
    (Map.elements (rules_of nodes)) = true).
  { apply forallb_forall; intros [x deps] Hin; apply (Hclosed x deps).
    exact (proj1 (Map.elements_spec EV HV x deps _ (rules_wf nodes)) Hin). }
  rewrite Htest; eexists; reflexivity.
Qed.

(** Accepted finite data runs the same occurrence-bounded kernel without assuming an outcome. *)
Theorem prepared_result_cost nodes data e w c arity :
  FinSet.wf EV nodes -> primitive_prices nodes e w c arity ->
  prepare_finite nodes = Accepted data ->
  (Cost.ticks (NumberingLoopWorklist.solve_prepared_c EV (countdown data)) <=
    NumberingLoopCost.kernel_k * (1 + N.of_nat (FinSet.size nodes)) *
      (1 + N.of_nat arity) * (1 + e + w))%N.
Proof.
  intros Hwf Hprices Haccepted.
  pose proof (prepare_finite_laws nodes data Haccepted) as Hdata.
  rewrite (countdown_same _ _ Hdata), (definitions_same _ _ Hdata).
  pose proof (NumberingLoopCost.solve_prepared_cost EV HV nodes (rules_of nodes) e w
    Hwf (rules_wf nodes) (rules_supported nodes Hwf) (kernel_prices nodes e w c arity Hwf Hprices))
    as Hkernel.
  pose proof (rule_mass nodes e w c arity Hwf Hprices) as Hmass; nia.
Qed.

(** The public fast-entry constant includes inventory construction, validation and final lookup. *)
Definition invariant_k : BinNums.N :=
  32 + preparation_k + NumberingLoopCost.kernel_k.

Local Lemma query_sum n a e w c :
  (2 + 2 * c + (n * (3 + e + w) + (NumberingLoopCost.key_price e w +
    (preparation_k * (1 + n) * (1 + a) * (1 + e + w + c) +
    (NumberingLoopCost.kernel_k * (1 + n) * (1 + a) * (1 + e + w) +
      NumberingLoopCost.key_price e w)))) <=
    invariant_k * (1 + n) * (1 + a) * (1 + e + w + c))%N.
Proof.
  unfold invariant_k, NumberingLoopCost.key_price; nia.
Qed.

(** The public indexed query has a full linear arity/width/callback bound on closed listed inputs.
    Arbitrary unlisted or malformed queries retain their separately charged reference fallback. *)
Theorem invariant_in_cost x e w c arity :
  primitive_prices (FinSet.of_list EV values) e w c arity ->
  closed_inventory (FinSet.of_list EV values) ->
  FinSet.mem EV x (FinSet.of_list EV values) = true ->
  (Cost.ticks (invariant_in_c x) <= invariant_k *
    (1 + N.of_nat (length values)) * (1 + N.of_nat arity) * (1 + e + w + c))%N.
Proof.
  intros Hprices Hclosed Hmember; set (nodes := FinSet.of_list EV values).
  fold nodes in Hmember.
  assert (Hwf : FinSet.wf EV nodes) by apply FinSet.wf_of_list.
  assert (Hx : In x (FinSet.elements nodes)).
  { exact (proj2 (FinSet.elements_spec EV HV x nodes Hwf) Hmember). }
  destruct (listed_prices _ _ _ _ _ Hprices x Hx) as [Hex [Hwx [Hhx [Hbx _]]]].
  pose proof (inside_cost x c Hhx Hbx) as Hinside.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold EV values e w) as Hinventory.
  assert (Hvalue_prices : forall y, In y values ->
    (Cost.ticks (encode_c EV y) <= e)%N /\ (key_bits EV y <= w)%N).
  { intros y Hy.
    pose proof (proj2 (NumberingSignature.listed_spec EV HV values y) Hy) as Hmem.
    destruct (listed_prices _ _ _ _ _ Hprices y
      (proj2 (FinSet.elements_spec EV HV y nodes Hwf) Hmem)) as [He [Hw _]]; now split. }
  specialize (Hinventory Hvalue_prices).
  destruct (closed_preparation nodes Hclosed) as [data Haccepted].
  pose proof (prepare_finite_laws nodes data Haccepted) as Hdata.
  destruct (finite_finishes data Hdata) as [final Hsolve].
  pose proof (preparation_cost nodes e w c arity Hwf Hprices) as Hprepare.
  pose proof (prepared_result_cost nodes data e w c arity Hwf Hprices Haccepted) as Hkernel.
  pose proof (of_nat_le _ _ universe_bound) as Hsize.
  fold nodes in Hsize.
  assert (Hprepare_bound : (Cost.ticks (prepare_finite_c nodes) <=
    preparation_k * (1 + N.of_nat (length values)) * (1 + N.of_nat arity) *
      (1 + e + w + c))%N) by nia.
  assert (Hkernel_bound :
    (Cost.ticks (NumberingLoopWorklist.solve_prepared_c EV (countdown data)) <=
    NumberingLoopCost.kernel_k * (1 + N.of_nat (length values)) * (1 + N.of_nat arity) *
      (1 + e + w))%N) by nia.
  assert (Hlookup : forall set, (Cost.ticks (FinSet.mem_c EV x set) <=
    NumberingLoopCost.key_price e w)%N).
  { intro set; unfold FinSet.mem_c; rewrite Map.mem_cost; fold (key_bits EV x).
    unfold NumberingLoopCost.key_price; lia. }
  unfold invariant_in_c; rewrite Cost.ticks_map.
  unfold query_c; rewrite Cost.ticks_bind, NumberingLoopReference.inside_value.
  fold syntax; fold (inside x); destruct (inside x).
  - rewrite Cost.ticks_bind; fold (FinSet.of_list EV values); fold nodes.
    rewrite Cost.ticks_bind; fold (FinSet.mem EV x nodes); rewrite Hmember.
    rewrite Cost.ticks_bind; fold (prepare_finite nodes); rewrite Haccepted.
    rewrite Cost.ticks_bind, Hsolve, Cost.ticks_bind, Cost.ticks_ret.
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hinside|].
      apply N.add_le_mono; [exact Hinventory|].
      apply N.add_le_mono; [apply Hlookup|].
      apply N.add_le_mono; [exact Hprepare_bound|].
      apply N.add_le_mono; [exact Hkernel_bound|].
      rewrite N.add_0_r; apply Hlookup.
    + apply query_sum.
  - rewrite Cost.ticks_ret.
    eapply N.le_trans; [|apply (query_sum (N.of_nat (length values)) (N.of_nat arity))].
    eapply N.le_trans; [|apply N.le_add_r]; lia.
Qed.

End Laws.

End Invariance.

(** Families of closed listed queries retain varying programs, inventories and primitive budgets. *)
Theorem invariant_in_bigO {X N E V K G}
    (problems : X -> problem N E V K G) (loops : X -> loop_info N) (queries : X -> V)
    (encoder width callback : X -> BinNums.N) (arity : X -> nat) :
  (forall x, encoding_laws (Ssa.val_enc (ssa (problems x)))) ->
  (forall x, primitive_prices (problems x) (loops x)
    (FinSet.of_list (Ssa.val_enc (ssa (problems x))) (Ssa.values (ssa (problems x))))
    (encoder x) (width x) (callback x) (arity x)) ->
  (forall x, closed_inventory (problems x) (loops x)
    (FinSet.of_list (Ssa.val_enc (ssa (problems x))) (Ssa.values (ssa (problems x))))) ->
  (forall x, FinSet.mem (Ssa.val_enc (ssa (problems x))) (queries x)
    (FinSet.of_list (Ssa.val_enc (ssa (problems x))) (Ssa.values (ssa (problems x)))) = true) ->
  bigO (fun x => ((1 + N.of_nat (length (Ssa.values (ssa (problems x))))) *
    (1 + N.of_nat (arity x)) * (1 + encoder x + width x + callback x))%N)
    (fun x => Cost.ticks (invariant_in_c (problems x) (loops x) (queries x))).
Proof.
  intros Hencoding Hprices Hclosed Hlisted; exists invariant_k; intro x.
  pose proof (invariant_in_cost (problems x) (loops x) (Hencoding x) (queries x)
    (encoder x) (width x) (callback x) (arity x) (Hprices x) (Hclosed x) (Hlisted x)) as Hcost.
  nia.
Qed.

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
