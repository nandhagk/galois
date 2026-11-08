(** * General selected-head widening adequacy

    Unsatisfied-row debt pays for non-head joins while selected changes spend rank or delay credit.
    For example, a selected outer head can stabilize a cycle through an unselected inner vertex.
    Builds on: FixpointNestedCredit and the public finite-path-weight WorklistWiden contracts. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointNested FixpointNestedProof FixpointNestedCost
  FixpointNestedWiden FixpointNestedCredit FixpointNestedPrimitive
  FixpointWorklistCost FixpointWorklistWiden.
Import List.ListNotations.

Local Open Scope nat_scope.

Module NestedDebt.

Local Lemma sum_app {B} (f : B -> nat) xs ys :
  WorklistCost.sum f (xs ++ ys) = WorklistCost.sum f xs + WorklistCost.sum f ys.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (f x + WorklistCost.sum f (xs ++ ys) =
    (f x + WorklistCost.sum f xs) + WorklistCost.sum f ys).
  rewrite IH; lia.
Qed.

Local Lemma sum_filter {B} (f : B -> nat) pred xs :
  WorklistCost.sum f (filter pred xs) =
    WorklistCost.sum (fun x => if pred x then f x else 0) xs.
Proof.
  unfold WorklistCost.sum; induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter fold_right]; destruct (pred x); cbn [fold_right]; now rewrite IH.
Qed.

Local Lemma sum_incl {B} (f : B -> nat) xs ys :
  NoDup xs -> incl xs ys -> WorklistCost.sum f xs <= WorklistCost.sum f ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys Hnodup Hincl; [cbn; lia|].
  inversion Hnodup as [|head tail Hfresh Htail]; subst head tail.
  destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [before [after ->]].
  rewrite sum_app.
  change (f x + WorklistCost.sum f xs <=
    WorklistCost.sum f before + (f x + WorklistCost.sum f after)).
  assert (Hrest : incl xs (before ++ after)).
  { intros y Hy; specialize (Hincl y (or_intror Hy)).
    apply in_app_iff in Hincl; apply in_or_app.
    destruct Hincl as [Hin|[Hsame|Hin]]; [now left|subst y; contradiction|now right]. }
  specialize (IH (before ++ after) Htail Hrest); rewrite sum_app in IH; lia.
Qed.

Section Debt.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (W : widening_rank (Analysis.lat a))
  (HC : NestedWiden.selected_cuts a p).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let hs := FinSet.of_list EX (Nested.heads p).
Let delay := N.of_nat (Policy.delay (Analysis.policy a)).
Let adapted := NestedCredit.masked a hs.
Let ix := index_system EX S (Analysis.static a).
Let HI := index_system_laws EX (Analysis.key_laws Hl) S (Analysis.static a).
Let cut := NestedCredit.masked_cuts a p HC.

(** Public path weights are instantiated with the actual selected-head intersection. *)
Definition weight := WorklistWiden.constraint_weight adapted ix HI cut.
Definition rows := distinct EC (System.constraints S).
Definition debt_cap := WorklistCost.sum weight rows.
Definition later c := flat_map (readers_of EX ix) (WorklistWiden.noncut_outputs adapted c).

(** Bad rows are exactly rows whose frozen outputs escape the current assignment. *)
Definition bad (m : assignment X A) c :=
  negb (forallb (fun out => leb L (snd out) (lookup EX L m (fst out)))
    (fst (Eval.outputs S c (lookup EX L m)))).

Definition bounded m c :=
  forall x v, In (x, v) (fst (Eval.outputs S c (lookup EX L m))) ->
    leb L v (lookup EX L m x) = true.

Definition debt m := WorklistCost.sum weight (filter (bad m) rows).
Definition credits := NestedCredit.credit a p W.
Definition rho m counts := credits m counts * (1 + debt_cap) + debt m.

Local Lemma bad_spec m c : bad m c = false <-> bounded m c.
Proof.
  unfold bad, bounded; rewrite negb_false_iff, forallb_forall.
  split.
  - intros H x v Hin; exact (H (x, v) Hin).
  - intros H [x v] Hin; exact (H x v Hin).
Qed.

Local Lemma outputs_agree c before after :
  (forall x, In x (Query.reads (System.rhs S c) (lookup EX L before)) ->
    lookup EX L before x = lookup EX L after x) ->
  fst (Eval.outputs S c (lookup EX L before)) =
    fst (Eval.outputs S c (lookup EX L after)).
Proof.
  intro Hreads.
  destruct (Query.query_determined (System.rhs S c)
    (lookup EX L before) (lookup EX L after) Hreads) as [Hv [Hr Hs]].
  rewrite !Eval.outputs_spec; cbn [fst]; now rewrite Hv, Hs.
Qed.

Local Lemma bounded_transport c before after :
  fun_leb L (lookup EX L before) (lookup EX L after) ->
  (forall x, In x (Query.reads (System.rhs S c) (lookup EX L before)) ->
    lookup EX L before x = lookup EX L after x) ->
  bounded before c -> bounded after c.
Proof.
  intros Hup Hreads Hbounded x v Hin.
  rewrite <- (outputs_agree c before after Hreads) in Hin.
  eapply (leb_trans (Analysis.lattice_law Hl)); [exact (Hbounded x v Hin)|apply Hup].
Qed.

Local Lemma rows_spec c : In c rows <-> In c (System.constraints S).
Proof.
  apply distinct_spec, (Analysis.row_laws Hl).
Qed.

Local Lemma output_metadata c m x v :
  In c (System.constraints S) ->
  In (x, v) (fst (Eval.outputs S c (lookup EX L m))) ->
  In x (System.target S c :: side_targets (Analysis.static a) c).
Proof.
  intros Hc Hout; rewrite Eval.outputs_spec in Hout; cbn [fst] in Hout.
  destruct Hout as [Hsame|Hside]; [injection Hsame as <- <-; now left|].
  right; apply (System.sides_within (Analysis.static_law Hl) c (lookup EX L m)).
  apply in_map_iff; exists (x, v); auto.
Qed.

Local Lemma output_universe c m x v :
  In c (System.constraints S) ->
  In (x, v) (fst (Eval.outputs S c (lookup EX L m))) -> In x (NestedCost.universe a).
Proof.
  intros Hc Hout; unfold NestedCost.universe; apply in_flat_map.
  exists c; split; [exact Hc|exact (output_metadata c m x v Hc Hout)].
Qed.

Local Lemma unselected_output c m x v :
  In c (System.constraints S) ->
  In (x, v) (fst (Eval.outputs S c (lookup EX L m))) ->
  NestedWiden.selected a p x = false -> In x (WorklistWiden.noncut_outputs adapted c).
Proof.
  intros Hc Hout Hno.
  change (In x (filter (fun y => negb (Policy.widen_at (Analysis.policy adapted) y))
    (System.target S c :: side_targets (Analysis.static a) c))).
  apply filter_In; split; [exact (output_metadata c m x v Hc Hout)|].
  apply negb_true_iff; unfold adapted, hs, EX.
  rewrite NestedCredit.masked_selection; exact Hno.
Qed.

Local Lemma bad_support c before after :
  In c (System.constraints S) ->
  fun_leb L (lookup EX L before) (lookup EX L after) ->
  (forall x v, In (x, v) (fst (Eval.outputs S c (lookup EX L before))) ->
    leb L v (lookup EX L after x) = true) ->
  (forall d, In d (System.constraints S) -> ~ In d (later c) ->
    forall x, In x (Query.reads (System.rhs S d) (lookup EX L before)) ->
    lookup EX L before x = lookup EX L after x) ->
  incl (filter (bad after) rows)
    (filter (fun d => bad before d && negb (eqb EC d c)) rows ++ later c).
Proof.
  intros Hc Hup Hbounds Hreads d Hin; apply filter_In in Hin; destruct Hin as [Hd Hbad].
  destruct (in_dec (eqb_dec EC (Analysis.row_laws Hl)) d (later c)) as [Hlater|Hnot].
  - apply in_or_app; now right.
  - assert (Hlisted : In d (System.constraints S)) by now apply rows_spec.
    assert (Hdifferent : d <> c).
    { intros ->.
      assert (Hgood : bounded after c).
      { intros x v Hv; rewrite <- (outputs_agree c before after (Hreads c Hc Hnot)) in Hv.
        exact (Hbounds x v Hv). }
      apply (proj2 (bad_spec after c)) in Hgood; congruence. }
    assert (Hold : bad before d = true).
    { destruct (bad before d) eqn:Hold; [reflexivity|].
      pose proof (bounded_transport d before after Hup (Hreads d Hlisted Hnot)
        (proj1 (bad_spec before d) Hold)) as Hgood.
      apply (proj2 (bad_spec after d)) in Hgood; congruence. }
    apply in_or_app; left; apply filter_In; split; [exact Hd|].
    apply andb_true_iff; split; [exact Hold|].
    apply negb_true_iff; apply (eqb_false_iff EC (Analysis.row_laws Hl)); exact Hdifferent.
Qed.

Local Lemma remove_bad c m :
  In c rows -> bad m c = true ->
  weight c + WorklistCost.sum weight
    (filter (fun d => bad m d && negb (eqb EC d c)) rows) <= debt m.
Proof.
  unfold debt; generalize rows as cs; intro cs.
  induction cs as [|d cs IH]; intros Hin Hbad; [contradiction|].
  cbn [filter]; destruct Hin as [Hsame|Hin].
  - subst d; rewrite Hbad, eqb_refl; cbn [andb negb].
    change (weight c + WorklistCost.sum weight
      (filter (fun d => bad m d && negb (eqb EC d c)) cs) <=
      weight c + WorklistCost.sum weight (filter (bad m) cs)).
    rewrite !sum_filter; apply Nat.add_le_mono_l, WorklistCost.sum_le.
    intros x Hx; destruct (bad m x), (eqb EC x c); cbn; lia.
  - specialize (IH Hin Hbad).
    unfold WorklistCost.sum in *.
    destruct (bad m d), (eqb EC d c); cbn [andb negb fold_right] in *; lia.
Qed.

(** Unsatisfied-row debt is bounded independently of the current assignment. *)
Theorem debt_bound m : debt m <= debt_cap.
Proof.
  unfold debt, debt_cap; rewrite sum_filter.
  apply WorklistCost.sum_le; intros c Hc; destruct (bad m c); lia.
Qed.

Local Lemma constant_credit_debt c before counts r :
  NestedCredit.good a before counts -> In c (System.constraints S) ->
  r = Nested.updates a hs delay
    (fst (Eval.outputs S c (lookup EX L before))) before counts ->
  credits (fst (fst r)) (snd (fst r)) = credits before counts ->
  bad before c = true -> debt (fst (fst r)) < debt before.
Proof.
  intros Hg Hc Hr Heq Hbad; subst r.
  set (outs := fst (Eval.outputs S c (lookup EX L before))).
  set (r := Nested.updates a hs delay outs before counts) in *.
  destruct (NestedCredit.updates_properties a p Hl W outs before counts Hg
    (fun x v Hin => output_universe c before x v Hc Hin))
    as [Hgood [Hcredit [Hup [Hbounds Hagree]]]].
  fold r in Hgood, Hcredit, Hup, Hbounds, Hagree.
  assert (Hreads : forall d, In d (System.constraints S) -> ~ In d (later c) ->
    forall x, In x (Query.reads (System.rhs S d) (lookup EX L before)) ->
    lookup EX L before x = lookup EX L (fst (fst r)) x).
  { intros d Hd Hnot x Hread; symmetry; apply Hagree; [|exact Heq].
    intros v Hout; destruct (NestedWiden.selected a p x) eqn:Hselected; [reflexivity|].
    exfalso; apply Hnot; unfold later; apply in_flat_map; exists x; split.
    - exact (unselected_output c before x v Hc Hout Hselected).
    - apply (readers_agree HI); split; [exact Hd|].
      exact (System.reads_within (Analysis.static_law Hl) d (lookup EX L before) x Hread). }
  pose proof (bad_support c before (fst (fst r)) Hc Hup Hbounds Hreads) as Hincl.
  pose proof (sum_incl weight _ _ (NoDup_filter _ (distinct_nodup EC _)) Hincl) as Hsum.
  fold rows in Hsum; rewrite sum_app in Hsum.
  pose proof (remove_bad c before (proj2 (rows_spec c) Hc) Hbad) as Hremove.
  pose proof (WorklistWiden.constraint_weight_dominates adapted ix HI cut c) as Hdominates.
  change (WorklistCost.sum weight (later c) < weight c) in Hdominates.
  unfold debt in Hremove |- *; lia.
Qed.

(** The legacy-strength local rank/debt duties follow from the selected cut and public weights. *)
Theorem evaluation_laws :
  NestedCost.evaluation_laws a p (NestedCredit.good a) rho.
Proof.
  constructor.
  - split; apply Map.wf_empty.
  - intros m counts c Hg Hc; cbn zeta.
    set (outs := fst (Eval.outputs (Analysis.system a) c (lookup EX L m))).
    set (r := Nested.updates a hs delay outs m counts).
    destruct (NestedCredit.updates_properties a p Hl W outs m counts Hg
      (fun x v Hin => output_universe c m x v Hc Hin))
      as [Hgood [Hcredit [Hup [Hbounds Hagree]]]].
    fold r in Hgood, Hcredit, Hup, Hbounds, Hagree; split; [exact Hgood|].
    change (credits (fst (fst r)) (snd (fst r)) <= credits m counts) in Hcredit.
    change (rho (fst (fst r)) (snd (fst r)) <= rho m counts /\
      (snd r = true -> rho (fst (fst r)) (snd (fst r)) < rho m counts)).
    destruct (snd r) eqn:Hflag.
    + assert (Hbad : bad m c = true).
      { destruct (bad m c) eqn:Hbad; [reflexivity|].
        pose proof (NestedCredit.updates_below a p outs m counts
          (proj1 (bad_spec m c) Hbad)) as Hidle.
        change (r = (m, counts, false)) in Hidle; rewrite Hidle in Hflag; discriminate. }
      assert (Hstrict : rho (fst (fst r)) (snd (fst r)) < rho m counts).
      { destruct (Nat.lt_ge_cases (credits (fst (fst r)) (snd (fst r))) (credits m counts))
          as [Hdrop|Hequal].
        - pose proof (debt_bound (fst (fst r))); unfold rho; fold credits in Hcredit; nia.
        - assert (Heq : credits (fst (fst r)) (snd (fst r)) = credits m counts) by lia.
          pose proof (constant_credit_debt c m counts r Hg Hc eq_refl Heq Hbad).
          unfold rho; rewrite Heq; lia. }
      split; [lia|intros; exact Hstrict].
    + pose proof (NestedProof.updates_stationary a hs delay outs m counts Hflag) as [_ Hbelow].
      pose proof (NestedCredit.updates_below a p outs m counts Hbelow) as Hidle.
      change (r = (m, counts, false)) in Hidle; rewrite Hidle; cbn; split; [lia|discriminate].
Qed.

(** This rank/path budget is not polynomial in general because path weights can be exponential. *)
Definition initial_budget :=
  (1 + length (NestedCost.universe a) * (Policy.delay (Analysis.policy a) + wbound W)) *
    (1 + debt_cap).

(** The derived initial budget does not assume any run or local-progress result. *)
Theorem initial_bound : rho Map.empty Map.empty < initial_budget.
Proof.
  pose proof (NestedCredit.initial_credit a p W) as Hcredit.
  pose proof (debt_bound (@Map.empty X A)) as Hdebt.
  unfold rho, credits, initial_budget; nia.
Qed.

(** Selected-head cycle cuts and widening ranks suffice for the actual nested runner. *)
Theorem fuel_enough fuel :
  Nested.code_ok a p ->
  (NestedCost.work EX ix p + 1) *
    (1 + (Nested.depth p + 1) * initial_budget) < Pos.to_nat fuel ->
  exists m, Nested.run a p fuel = Outcome.Solved m.
Proof.
  intros Hcode Hfuel.
  apply (NestedCost.ranked_fuel_enough a p (Analysis.key_laws Hl)
    (NestedCredit.good a) rho evaluation_laws fuel Hcode).
  eapply Nat.le_lt_trans; [|exact Hfuel].
  apply Nat.mul_le_mono_l, Nat.add_le_mono_l, Nat.mul_le_mono_l.
  pose proof initial_bound; lia.
Qed.

(** A full rank and the selected cut imply eventual completion without a finite-height premise. *)
Theorem adequate :
  Nested.code_ok a p ->
  exists fuel m, Nested.run a p fuel = Outcome.Solved m.
Proof.
  intro Hcode.
  exists (Pos.of_succ_nat ((NestedCost.work EX ix p + 1) *
    (1 + (Nested.depth p + 1) * initial_budget))).
  apply fuel_enough; [exact Hcode|rewrite SuccNat2Pos.id_succ; lia].
Qed.

(** Primitive numeric callback prices compose with the derived general widening potential. *)
Theorem primitive_cost (b : NestedPrimitive.budget) (HB : NestedPrimitive.model a p b) fuel :
  Nested.code_ok a p ->
  (Cost.ticks (Nested.run_c a p fuel) <= NestedPrimitive.preparation_k a p b +
    (NestedPrimitive.step_k b + 2) *
      (N.of_nat ((NestedCost.work EX ix p + 1) *
        (1 + (Nested.depth p + 1) * initial_budget)) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  intro Hcode.
  pose proof (NestedCost.nested_widen_cost a p (Analysis.key_laws Hl)
    (NestedCredit.good a) rho evaluation_laws fuel (NestedPrimitive.step_k b)
    ltac:(intros s [Hcontrol [Hgood Hlisted]] Hprefix;
      exact (NestedPrimitive.step_cost a p Hl b HB s Hprefix Hlisted))) as Hloop.
  pose proof (NestedPrimitive.run_cost a p Hl b HB fuel Hcode) as Hrun.
  assert (Hnat :
    (NestedCost.work EX ix p + 1) *
      (1 + (Nested.depth p + 1) * rho Map.empty Map.empty) <=
    (NestedCost.work EX ix p + 1) *
      (1 + (Nested.depth p + 1) * initial_budget)).
  { apply Nat.mul_le_mono_l, Nat.add_le_mono_l, Nat.mul_le_mono_l.
    pose proof initial_bound; lia. }
  assert (HN :
    (N.of_nat ((NestedCost.work EX ix p + 1) *
      (1 + (Nested.depth p + 1) * rho Map.empty Map.empty)) <=
    N.of_nat ((NestedCost.work EX ix p + 1) *
      (1 + (Nested.depth p + 1) * initial_budget)))%N) by lia.
  assert (Hmult :
    ((NestedPrimitive.step_k b + 2) *
      (N.of_nat ((NestedCost.work EX ix p + 1) *
        (1 + (Nested.depth p + 1) * rho Map.empty Map.empty)) + 1) <=
    (NestedPrimitive.step_k b + 2) *
      (N.of_nat ((NestedCost.work EX ix p + 1) *
        (1 + (Nested.depth p + 1) * initial_budget)) + 1))%N).
  { apply N.mul_le_mono; [reflexivity|lia]. }
  fold EX S in Hloop, Hrun; fold ix hs delay in Hloop, Hrun; nia.
Qed.

End Debt.

End NestedDebt.
Import NestedDebt.
