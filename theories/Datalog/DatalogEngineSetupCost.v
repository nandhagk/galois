(** * Primitive preparation and storage prices for the fast wrapper

    The wrapper pays the actual stratifier's source scans, map accesses and bounded passes.
    For example, rejected stratification still charges all passes that the checker performs.
    Builds on: DatalogPipelineCost and public Map and list cost contracts. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogCompile
  DatalogCompileProof DatalogSolve DatalogSolveProof DatalogCost DatalogJoinFireCost
  DatalogPipelineCost DatalogSemiNaiveCost DatalogSemiNaiveInitialCost DatalogSemiNaiveTrace.
Import List.ListNotations Cost.Notations SemiNaiveCost SemiNaiveInitialCost SemiNaiveTrace.
Local Open Scope N_scope.

Module EngineSetupCost.

(** Predicate support retains all source rule and fact occurrences. *)
Definition predicate_inventory {P} (prog : program P) (facts : list (ground_atom P)) :=
  rule_nodes prog ++ map fst facts.

(** Only predicates in the finite source inventory need uniform primitive key budgets. *)
Definition predicate_keys {P} (prog : program P) facts ep wp : Prop :=
  forall p, In p (predicate_inventory prog facts) -> key_budget (penc prog) ep wp p.

Lemma head_support {P} (prog : program P) facts r :
  In r (rules prog) -> In (pred (head r)) (predicate_inventory prog facts).
Proof.
  intro Hr; apply in_app_iff; left; apply rule_nodes_spec; exists r; split; [exact Hr |].
  rewrite rule_predicates_equation; now left.
Qed.

Lemma literal_support {P} (prog : program P) facts r lit :
  In r (rules prog) -> In lit (body r) ->
  In (pred (lit_atom lit)) (predicate_inventory prog facts).
Proof.
  intros Hr Hlit; apply in_app_iff; left; apply rule_nodes_spec; exists r; split; [exact Hr |].
  rewrite rule_predicates_equation; right; apply in_map_iff; exists lit; auto.
Qed.

Lemma fact_support {P} (prog : program P) facts f :
  In f facts -> In (fst f) (predicate_inventory prog facts).
Proof.
  intro Hf; apply in_app_iff; right; apply in_map, Hf.
Qed.

Lemma target_support {P} (prog : program P) facts st k p :
  In p (stratum_targets prog facts st k) -> In p (predicate_inventory prog facts).
Proof.
  rewrite stratum_targets_equation, in_map_iff.
  intros [[i h | q] [Heq Hconstraint]]; cbn [Constraint.target] in Heq; subst p.
  - destruct (rule_constraint_view prog facts st k i h Hconstraint) as [r [Hr [-> _]]].
    apply head_support, Hr.
  - rewrite stratum_constraints_equation, in_app_iff in Hconstraint.
    destruct Hconstraint as [Hbad | Hfact].
    + apply rule_constraints_spec in Hbad as [i [r [_ [_ Hbad]]]]; discriminate.
    + apply in_map_iff in Hfact as [f [Heq Hf]]; injection Heq as <-.
      apply filter_In in Hf as [Hf _]; apply fact_support, Hf.
Qed.

(** Node preparation retains each source predicate occurrence and both literal traversals. *)
Definition node_charge {P} (prog : program P) :=
  sum (fun r => 2 + 2 * N.of_nat (length (body r))) (rules prog).

(** Edge preparation retains each rule visit and both literal traversals. *)
Definition edge_charge {P} (prog : program P) :=
  sum (fun r => 1 + 2 * N.of_nat (length (body r))) (rules prog).

Lemma edges_cost {P} (prog : program P) :
  Cost.ticks (program_edges_c prog) <= edge_charge prog.
Proof.
  unfold program_edges_c; eapply N.le_trans;
    [apply (fold_price _ _ _ (fun r => 2 * N.of_nat (length (body r)))) |].
  - intros r acc Hr; rewrite Cost.ticks_bind, ticks_app_c.
    assert (Hrule : Cost.ticks (rule_edges_c r) = N.of_nat (length (body r))).
    { unfold rule_edges_c; apply ret_map_cost. }
    rewrite Hrule.
    fold (@rule_edges P r); rewrite rule_edges_equation, length_map; lia.
  - apply N.le_refl.
Qed.

Lemma nodes_cost {P} (prog : program P) :
  Cost.ticks (rule_nodes_c prog) <= node_charge prog.
Proof.
  unfold rule_nodes_c; eapply N.le_trans;
    [apply (fold_price _ _ _ (fun r => 1 + 2 * N.of_nat (length (body r)))) |].
  - intros r acc Hr; rewrite Cost.ticks_bind, ticks_app_c.
    assert (Hrule : Cost.ticks (rule_predicates_c r) = N.of_nat (length (body r))).
    { unfold rule_predicates_c; rewrite Cost.ticks_map; apply ret_map_cost. }
    rewrite Hrule.
    fold (@rule_predicates P r); rewrite rule_predicates_equation; cbn [length].
    rewrite length_map, Nat2N.inj_succ; lia.
  - unfold node_charge, sum; induction (rules prog) as [|r rs IH]; cbn [fold_right]; lia.
Qed.

Lemma level_at_cost {P} (E : encoding P) m p ep wp :
  key_budget E ep wp p -> Cost.ticks (level_at_c E m p) <= 1 + ep + wp.
Proof.
  intros [Hencode Hwidth]; unfold level_at_c; rewrite Map.find_or_cost, Map.get_cost.
  fold (key_bits E p); lia.
Qed.

Lemma edge_test_cost {P} (E : encoding P) m e ep wp :
  key_budget E ep wp (fst e) -> key_budget E ep wp (fst (snd e)) ->
  Cost.ticks (edge_ok_c E m e) <= 3 + 2 * (ep + wp).
Proof.
  intros Hhead Hbody.
  pose proof (level_at_cost E m _ ep wp Hhead).
  pose proof (level_at_cost E m _ ep wp Hbody).
  unfold edge_ok_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step, Cost.ticks_ret; lia.
Qed.

Lemma edge_raise_cost {P} (E : encoding P) m e ep wp :
  key_budget E ep wp (fst e) -> key_budget E ep wp (fst (snd e)) ->
  Cost.ticks (raise_edge_c E m e) <= 4 + 3 * (ep + wp).
Proof.
  intros Hhead Hbody.
  pose proof (level_at_cost E m _ ep wp Hhead).
  pose proof (level_at_cost E m _ ep wp Hbody).
  destruct Hhead as [Henc Hwidth].
  unfold raise_edge_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step, Map.set_cost.
  fold (key_bits E (fst e)); lia.
Qed.

Lemma left_bound {A B} (f : B -> A -> Cost.t B) xs init c :
  (forall x acc, In x xs -> Cost.ticks (f acc x) <= c) ->
  Cost.ticks (fold_left_c f xs init) <= N.of_nat (length xs) * (c + 1).
Proof.
  revert init; induction xs as [|x xs IH]; intros init Hcost; [change (0 <= 0); lia |].
  rewrite ticks_fold_left_c_cons.
  specialize (IH (Cost.value (f init x)) (fun y acc Hy => Hcost y acc (or_intror Hy))).
  pose proof (Hcost x init (or_introl eq_refl)).
  cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Source key duties cover the two endpoints of every listed stratifier edge. *)
Definition stratifier_keys {P} (prog : program P) ep wp : Prop :=
  forall p, In p (rule_nodes prog) -> key_budget (penc prog) ep wp p.

Lemma endpoints {P} (prog : program P) ep wp e :
  stratifier_keys prog ep wp -> In e (program_edges prog) ->
  key_budget (penc prog) ep wp (fst e) /\
  key_budget (penc prog) ep wp (fst (snd e)).
Proof.
  intros Hkeys He; destruct e as [h [b w]].
  destruct (edge_nodes prog h b w He) as [Hhead Hbody]; split; apply Hkeys; assumption.
Qed.

Lemma levels_cost {P} (prog : program P) m ep wp :
  stratifier_keys prog ep wp ->
  Cost.ticks (levels_ok_c prog m) <= edge_charge prog +
    N.of_nat (length (program_edges prog)) * (4 + 2 * (ep + wp)).
Proof.
  intro Hkeys; pose proof (edges_cost prog) as Hedges.
  unfold levels_ok_c; rewrite Cost.ticks_bind; fold (@program_edges P prog).
  assert (Htest : Cost.ticks (forallb_c (edge_ok_c (penc prog) m) (program_edges prog)) <=
    N.of_nat (length (program_edges prog)) * (4 + 2 * (ep + wp))).
  { replace (4 + 2 * (ep + wp)) with ((3 + 2 * (ep + wp)) + 1) by lia.
    apply JoinFireCost.forallb_bound_on; intros e He.
    destruct (endpoints prog ep wp e Hkeys He); apply edge_test_cost; assumption. }
  lia.
Qed.

Lemma raises_cost {P} (prog : program P) m ep wp :
  stratifier_keys prog ep wp ->
  Cost.ticks (raise_pass_c (penc prog) (program_edges prog) m) <=
    N.of_nat (length (program_edges prog)) * (5 + 3 * (ep + wp)).
Proof.
  intro Hkeys; unfold raise_pass_c.
  replace (5 + 3 * (ep + wp)) with ((4 + 3 * (ep + wp)) + 1) by lia.
  apply left_bound; intros e acc He.
  destruct (endpoints prog ep wp e Hkeys He); apply edge_raise_cost; assumption.
Qed.

(** A full pass includes the checker, repeated edge preparation and all level updates. *)
Definition pass_charge {P} (prog : program P) ep wp :=
  1 + edge_charge prog +
    N.of_nat (length (program_edges prog)) * (4 + 2 * (ep + wp)) +
  edge_charge prog +
    N.of_nat (length (program_edges prog)) * (5 + 3 * (ep + wp)).

Lemma stratifier_loop_cost {P} (prog : program P) n m ep wp :
  stratifier_keys prog ep wp ->
  Cost.ticks (stratify_loop_c prog n m) <= N.of_nat n * pass_charge prog ep wp.
Proof.
  intro Hkeys; revert m; induction n as [|n IH]; intro m; [change (0 <= 0); lia |].
  rewrite stratify_loop_cost.
  pose proof (levels_cost prog m ep wp Hkeys) as Hlevels.
  pose proof (edges_cost prog) as Hedges.
  pose proof (raises_cost prog m ep wp Hkeys) as Hraises.
  specialize (IH (raise_pass (penc prog) (program_edges prog) m)).
  assert (Hpass : 1 + Cost.ticks (levels_ok_c prog m) +
    Cost.ticks (program_edges_c prog) +
    Cost.ticks (raise_pass_c (penc prog) (program_edges prog) m) <=
      pass_charge prog ep wp).
  { unfold pass_charge; lia. }
  rewrite Nat2N.inj_succ, N.mul_succ_l; destruct (levels_ok prog m); lia.
Qed.

Lemma maximum_cost {P} (prog : program P) m ep wp :
  stratifier_keys prog ep wp ->
  Cost.ticks (maximum_c prog m) <= node_charge prog +
    N.of_nat (length (rule_nodes prog)) * (2 + ep + wp).
Proof.
  intro Hkeys; pose proof (nodes_cost prog) as Hnodes.
  unfold maximum_c; rewrite Cost.ticks_bind; fold (@rule_nodes P prog).
  assert (Hfold : Cost.ticks (fold_left_c (fun n p =>
    let* v := level_at_c (penc prog) m p in Cost.ret (Nat.max n v)) (rule_nodes prog) 0%nat) <=
      N.of_nat (length (rule_nodes prog)) * (2 + ep + wp)).
  { replace (2 + ep + wp) with ((1 + ep + wp) + 1) by lia.
    apply left_bound; intros p acc Hp; rewrite Cost.ticks_bind, Cost.ticks_ret.
    pose proof (level_at_cost (penc prog) m p ep wp (Hkeys p Hp)); lia. }
  lia.
Qed.

(** The stratifier price contains full source preparation and its actual finite pass budget. *)
Definition stratifier_charge {P} (prog : program P) ep wp :=
  node_charge prog + N.of_nat (length (rule_nodes prog)) + 1 +
  N.of_nat (length (rule_nodes prog) * length (rule_nodes prog) + 1)%nat *
    pass_charge prog ep wp +
  node_charge prog + N.of_nat (length (rule_nodes prog)) * (2 + ep + wp).

(** Stratification has a complete primitive bound on both acceptance and rejection paths. *)
Theorem stratifier_cost {P} (prog : program P) ep wp :
  stratifier_keys prog ep wp ->
  Cost.ticks (stratify_c prog) <= stratifier_charge prog ep wp.
Proof.
  intro Hkeys; rewrite stratify_cost.
  pose proof (nodes_cost prog) as Hnodes.
  pose proof (stratifier_loop_cost prog
    (length (rule_nodes prog) * length (rule_nodes prog) + 1)%nat Map.empty ep wp Hkeys) as Hloop.
  unfold stratifier_charge; destruct (stratify_loop prog _ Map.empty) as [m []].
  - pose proof (maximum_cost prog m ep wp Hkeys); lia.
  - nia.
Qed.

(** Successful stratification installs a level callback priced by primitive predicate lookup. *)
Theorem stratified_callback_cost {P} (prog : program P) st ep wp p :
  stratify prog = Some st -> key_budget (penc prog) ep wp p ->
  Cost.ticks (level_c st p) <= 1 + ep + wp.
Proof.
  rewrite stratify_equation.
  destruct (stratify_loop prog _ Map.empty) as [m []]; [|discriminate].
  intro Heq; injection Heq as <-; apply level_at_cost.
Qed.

Lemma rule_targets_cost {P} (st : stratification P) k start rs l :
  (forall r, In r rs -> Cost.ticks (level_c st (pred (head r))) <= l) ->
  Cost.ticks (rule_constraints_c st k start rs) <= N.of_nat (length rs) * (2 + l).
Proof.
  revert start; induction rs as [|r rs IH]; intros start Hlevel;
    [change (0 <= 0); lia |].
  cbn [rule_constraints_c]; repeat rewrite Cost.ticks_bind.
  rewrite !Cost.ticks_step, Cost.ticks_ret.
  pose proof (Hlevel r (or_introl eq_refl)).
  specialize (IH (S start) (fun r Hr => Hlevel r (or_intror Hr))).
  cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

Lemma constraints_cost {P} (prog : program P) facts st k l :
  (forall p, In p (predicate_inventory prog facts) -> Cost.ticks (level_c st p) <= l) ->
  Cost.ticks (stratum_constraints_c prog facts st k) <=
    (N.of_nat (length (rules prog)) + N.of_nat (length facts)) * (3 + l).
Proof.
  intro Hlevel.
  pose proof (rule_targets_cost st k 0 (rules prog) l
    (fun r Hr => Hlevel _ (head_support prog facts r Hr))) as Hrules.
  pose proof (nat_N_le _ _ (rule_constraints_length st k 0 (rules prog))) as Hrulelength.
  assert (Hfacts : Cost.ticks (filter_c (fun f =>
    Cost.step ;; Cost.map (fun n => Nat.eqb n k) (level_c st (fst f))) facts) <=
      N.of_nat (length facts) * (2 + l)).
  { rewrite ticks_filter_c; replace (2 + l) with ((1 + l) + 1) by lia.
    apply traversal_bound_on; intros f Hf.
    rewrite Cost.ticks_bind, Cost.ticks_step, Cost.ticks_map.
    pose proof (Hlevel (fst f) (fact_support prog facts f Hf)); lia. }
  pose proof (nat_N_le _ _ (filter_length_bound
    (fun f => Nat.eqb (level st (fst f)) k) facts)) as Hfactlength.
  unfold stratum_constraints_c; repeat rewrite Cost.ticks_bind.
  rewrite ret_map_cost, ticks_app_c, value_filter_c.
  fold (@rule_constraints P st k 0 (rules prog)).
  change (Cost.ticks (rule_constraints_c st k 0 (rules prog)) +
    (Cost.ticks (filter_c (fun f =>
      Cost.step ;; Cost.map (fun n => Nat.eqb n k) (level_c st (fst f))) facts) +
    (N.of_nat (length (filter (fun f => Nat.eqb (level st (fst f)) k) facts)) +
      N.of_nat (length (rule_constraints st k 0 (rules prog))))) <=
    (N.of_nat (length (rules prog)) + N.of_nat (length facts)) * (3 + l)).
  eapply N.le_trans with (m :=
    N.of_nat (length (rules prog)) * (2 + l) +
    (N.of_nat (length facts) * (2 + l) +
      (N.of_nat (length facts) + N.of_nat (length (rules prog))))).
  - apply N.add_le_mono; [exact Hrules |].
    apply N.add_le_mono; [exact Hfacts |].
    apply N.add_le_mono; [exact Hfactlength | exact Hrulelength].
  - replace (3 + l) with ((2 + l) + 1) by lia.
    rewrite N.mul_add_distr_r, !N.mul_add_distr_l, !N.mul_1_r.
    lia.
Qed.

(** Target preparation charges rule and fact scans, filtering, append and both mapping passes. *)
Theorem targets_cost {P} (prog : program P) facts st k l :
  (forall p, In p (predicate_inventory prog facts) -> Cost.ticks (level_c st p) <= l) ->
  Cost.ticks (stratum_targets_c prog facts st k) <=
    (N.of_nat (length (rules prog)) + N.of_nat (length facts)) * (4 + l).
Proof.
  intro Hlevel; pose proof (constraints_cost prog facts st k l Hlevel) as Hconstraints.
  pose proof (nat_N_le _ _ (constraints_length prog facts st k)) as Hlength.
  unfold stratum_targets_c; rewrite Cost.ticks_bind, ret_map_cost.
  fold (@stratum_constraints P prog facts st k); nia.
Qed.

(** Storing local results pays both the local lookup and destination insertion for every target. *)
Theorem store_cost {P} (prog : program P) ps local db ep wp :
  (forall p, In p ps -> key_budget (penc prog) ep wp p) ->
  Cost.ticks (store_relations_c prog ps (rel_of_c prog local) db) <=
    N.of_nat (length ps) * (4 + 2 * (ep + wp)).
Proof.
  intro Hkeys; unfold store_relations_c.
  eapply N.le_trans; [apply (fold_right_bound_on _ (3 + 2 * (ep + wp))) |].
  - intros p acc Hp; pose proof (rel_of_cost prog local p ep wp (Hkeys p Hp)) as Hlookup.
    destruct (Hkeys p Hp) as [Henc Hwidth].
    repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step, Map.set_cost.
    fold (key_bits (penc prog) p); lia.
  - nia.
Qed.

End EngineSetupCost.
Import EngineSetupCost.
