(** * Selected-head widening credits and output preservation

    Actual selected updates consume widening-rank or delay credit and preserve frozen outputs.
    For example, a join at an unselected body vertex changes values without spending cut credit.
    Builds on: FixpointNestedWiden and the state-independent WorklistWiden rank contracts. *)

From Stdlib Require Import List Bool Arith NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeKit.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCycles FixpointEval
  FixpointIndex FixpointAnalysis FixpointNested FixpointNestedProof FixpointNestedCost
  FixpointNestedWiden FixpointWorklistCost FixpointWorklistWiden.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module NestedCredit.

(** The proof adapter changes only policy selection and retains both callback charges. *)
Definition masked {X C A} (a : Analysis.t X C A) (hs : FinSet.t X) : Analysis.t X C A :=
  Analysis.Make (Analysis.key_enc a) (Analysis.row_enc a) (Analysis.lat a)
    (Analysis.system a) (Analysis.static a)
    (Policy.Make (Policy.order_c (Analysis.policy a))
      (fun x =>
        let* head := FinSet.mem_c (Analysis.key_enc a) x hs in
        Cost.step ;;
        let* flag := Policy.widen_at_c (Analysis.policy a) x in
        Cost.ret (head && flag))
      (Policy.delay (Analysis.policy a)) (Policy.narrowing (Analysis.policy a))).

(** The adapter selects exactly the runtime intersection on the prepared head set. *)
Theorem masked_selection {X C A} (a : Analysis.t X C A) p x :
  Policy.widen_at (Analysis.policy (masked a
    (FinSet.of_list (Analysis.key_enc a) (Nested.heads p)))) x =
    NestedWiden.selected a p x.
Proof.
  change (Cost.value
    (let* head := FinSet.mem_c (Analysis.key_enc a) x
        (FinSet.of_list (Analysis.key_enc a) (Nested.heads p)) in
      Cost.step ;;
      let* flag := Policy.widen_at_c (Analysis.policy a) x in Cost.ret (head && flag)) =
    NestedWiden.selected a p x).
  autorewrite with galois_cost.
  fold (FinSet.mem (Analysis.key_enc a) x
    (FinSet.of_list (Analysis.key_enc a) (Nested.heads p))).
  rewrite FinSet.mem_of_list; reflexivity.
Qed.

(** The separate selected-head cut duty transports to the proof adapter's unchanged metadata. *)
Theorem masked_cuts {X C A} (a : Analysis.t X C A) p :
  NestedWiden.selected_cuts a p ->
  cuts_every_cycle (Analysis.static (masked a
    (FinSet.of_list (Analysis.key_enc a) (Nested.heads p))))
    (Policy.widen_at (Analysis.policy (masked a
      (FinSet.of_list (Analysis.key_enc a) (Nested.heads p))))).
Proof.
  intros Hcut x Hcycle; apply (Hcut x).
  assert (Htransport : forall u v,
    clos_trans X (fun y z => flows (Analysis.static (masked a
      (FinSet.of_list (Analysis.key_enc a) (Nested.heads p)))) y z /\
      Policy.widen_at (Analysis.policy (masked a
        (FinSet.of_list (Analysis.key_enc a) (Nested.heads p)))) z = false) u v ->
    clos_trans X (fun y z => flows (Analysis.static a) y z /\
      NestedWiden.selected a p z = false) u v).
  { intros u v Hpath; induction Hpath as [u v [Hflow Hno]|u v w Huv IHuv Hvw IHvw].
    - apply t_step; split; [exact Hflow|].
      rewrite <- masked_selection; exact Hno.
    - eapply t_trans; eassumption. }
  exact (Htransport x x Hcycle).
Qed.

Section Updates.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (W : widening_rank (Analysis.lat a)).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let U := NestedCost.universe a.
Let hs := FinSet.of_list EX (Nested.heads p).
Let delay := Policy.delay (Analysis.policy a).
Let selected := NestedWiden.selected a p.

Definition count_at (counts : Map.t X N) x := Map.find_or EX 0%N x counts.
Definition remaining (counts : Map.t X N) x := delay - N.to_nat (count_at counts x).
Definition site m counts x :=
  if selected x then WorklistWiden.local_credit W (remaining counts x) (lookup EX L m x)
  else 0.
Definition credit m counts := WorklistCost.sum (site m counts) U.

(** Only map well-formedness is needed when the widening dictionary has a full-carrier rank. *)
Definition good (m : assignment X A) (counts : Map.t X N) : Prop :=
  Map.wf EX m /\ Map.wf EX counts.

Local Lemma lookup_set m x v y :
  Map.wf EX m ->
  lookup EX L (Map.set EX x v m) y = if eqb EX y x then v else lookup EX L m y.
Proof.
  intro Hwf; rewrite !lookup_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

Local Lemma count_set counts x n y :
  Map.wf EX counts ->
  count_at (Map.set EX x n counts) y = if eqb EX y x then n else count_at counts y.
Proof.
  intro Hwf; unfold count_at; rewrite !Map.find_or_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

(** Runtime operator choice uses the actual head-policy intersection. *)
Theorem operation_value x count old value :
  Cost.value (Nested.op_c a hs (N.of_nat delay) x count old value) =
    if selected x && N.leb (N.of_nat delay) count then widen L old value else join L old value.
Proof.
  unfold Nested.op_c; autorewrite with galois_cost.
  fold EX; fold (FinSet.mem EX x hs).
  unfold hs; rewrite FinSet.mem_of_list.
  fold (Policy.widen_at (Analysis.policy a) x).
  change (Cost.value
    (if selected x && N.leb (N.of_nat delay) count
     then Cost.step ;; widen_c L old value else Cost.step ;; join_c L old value) =
    if selected x && N.leb (N.of_nat delay) count then widen L old value else join L old value).
  destruct (selected x && N.leb (N.of_nat delay) count); reflexivity.
Qed.

Local Lemma selected_operation counts x old value :
  selected x = true ->
  Cost.value (Nested.op_c a hs (N.of_nat delay) x (count_at counts x) old value) =
    match remaining counts x with
    | O => widen L old value
    | S _ => join L old value
    end.
Proof.
  intro Hselected; rewrite operation_value, Hselected; cbn [andb].
  unfold remaining.
  destruct (N.leb (N.of_nat delay) (count_at counts x)) eqn:Hdelay.
  - apply N.leb_le in Hdelay.
    replace (delay - N.to_nat (count_at counts x)) with 0 by lia; reflexivity.
  - apply N.leb_gt in Hdelay.
    destruct (delay - N.to_nat (count_at counts x)) eqn:Hremaining; [lia|reflexivity].
Qed.

Local Lemma operation_bounds x count old value :
  leb L old (Cost.value (Nested.op_c a hs (N.of_nat delay) x count old value)) = true /\
  leb L value (Cost.value (Nested.op_c a hs (N.of_nat delay) x count old value)) = true.
Proof.
  rewrite operation_value; destruct (selected x && N.leb (N.of_nat delay) count).
  - split; [apply (widen_upper_l (Analysis.lattice_law Hl))|
      apply (widen_upper_r (Analysis.lattice_law Hl))].
  - split; [apply (join_upper_l (Analysis.lattice_law Hl))|
      apply (join_upper_r (Analysis.lattice_law Hl))].
Qed.

Local Lemma changed_credit m counts x value :
  good m counts -> In x U -> leb L value (lookup EX L m x) = false ->
  let v := Cost.value (Nested.op_c a hs (N.of_nat delay) x (count_at counts x)
    (lookup EX L m x) value) in
  let counts' := Map.set EX x (N.succ (count_at counts x)) counts in
  credit (Map.set EX x v m) counts' <= credit m counts /\
  (credit (Map.set EX x v m) counts' = credit m counts -> selected x = false).
Proof.
  intros [Hwf Hcounts] Hx Hbelow; cbn zeta.
  set (v := Cost.value (Nested.op_c a hs (N.of_nat delay) x (count_at counts x)
    (lookup EX L m x) value)).
  set (next_counts := Map.set EX x (N.succ (count_at counts x)) counts).
  assert (Hother : forall y, y <> x ->
    site (Map.set EX x v m) next_counts y = site m counts y).
  { intros y Hne; unfold site, remaining, next_counts.
    rewrite lookup_set, count_set by assumption.
    rewrite (proj2 (eqb_false_iff EX (Analysis.key_laws Hl) y x) Hne); reflexivity. }
  assert (Hself : selected x = true ->
    site (Map.set EX x v m) next_counts x < site m counts x).
  { intro Hsel; unfold site, remaining, next_counts; rewrite Hsel.
    rewrite lookup_set, count_set by assumption; rewrite eqb_refl, N2Nat.inj_succ.
    replace (delay - S (N.to_nat (count_at counts x))) with
      (Nat.pred (delay - N.to_nat (count_at counts x))) by lia.
    unfold v; rewrite selected_operation by exact Hsel.
    apply WorklistWiden.delayed_rank_credit_progress, Hbelow. }
  assert (Hpoint : forall y, In y U ->
    site (Map.set EX x v m) next_counts y <= site m counts y).
  { intros y Hy; destruct (eqb EX y x) eqn:Hsame.
    - apply (eqb_true_iff EX (Analysis.key_laws Hl)) in Hsame; subst y.
      destruct (selected x) eqn:Hsel.
      + pose proof (Hself eq_refl); lia.
      + unfold site; rewrite Hsel; lia.
    - apply (eqb_false_iff EX (Analysis.key_laws Hl)) in Hsame.
      rewrite Hother by exact Hsame; lia. }
  split; [apply WorklistCost.sum_le, Hpoint|].
  intro Heq; destruct (selected x) eqn:Hsel; [|reflexivity].
  pose proof (WorklistCost.sum_drop (site m counts)
    (site (Map.set EX x v m) next_counts) U x 1 Hx Hpoint
    ltac:(pose proof (Hself eq_refl); lia)) as Hdrop.
  unfold credit in Heq; lia.
Qed.

Local Lemma rule_properties m counts x value :
  good m counts -> In x U ->
  let first := Update.rule EX L
    (Nested.op_c a hs (N.of_nat delay) x (count_at counts x)) m x value in
  let counts' := if snd first then Map.set EX x (N.succ (count_at counts x)) counts else counts in
  good (fst first) counts' /\
  credit (fst first) counts' <= credit m counts /\
  fun_leb L (lookup EX L m) (lookup EX L (fst first)) /\
  leb L value (lookup EX L (fst first) x) = true /\
  (forall y, (y = x -> selected y = true) ->
    credit (fst first) counts' = credit m counts -> lookup EX L (fst first) y = lookup EX L m y).
Proof.
  intros [Hwf Hcounts] Hx; cbn zeta; rewrite Update.rule_equation.
  destruct (leb L value (lookup EX L m x)) eqn:Hbelow; cbn [fst snd].
  - split; [now split|]; split; [lia|]; split.
    + intro y; apply (leb_refl (Analysis.lattice_law Hl)).
    + split; [exact Hbelow|intros; reflexivity].
  - set (v := Cost.value (Nested.op_c a hs (N.of_nat delay) x (count_at counts x)
      (lookup EX L m x) value)).
    set (next_counts := Map.set EX x (N.succ (count_at counts x)) counts).
    destruct (changed_credit m counts x value (conj Hwf Hcounts) Hx Hbelow)
      as [Hcredit Hselected].
    split; [split; apply Map.wf_set; assumption|].
    split; [exact Hcredit|]; split.
    + intro y; rewrite lookup_set by exact Hwf.
      destruct (eqb EX y x) eqn:Hsame.
      * apply (eqb_true_iff EX (Analysis.key_laws Hl)) in Hsame; subst y.
        apply (proj1 (operation_bounds x (count_at counts x) (lookup EX L m x) value)).
      * apply (leb_refl (Analysis.lattice_law Hl)).
    + split.
      * rewrite lookup_set by exact Hwf; rewrite eqb_refl.
        apply (proj2 (operation_bounds x (count_at counts x) (lookup EX L m x) value)).
      * intros y Hy Heq; rewrite lookup_set by exact Hwf.
        destruct (eqb EX y x) eqn:Hsame; [|reflexivity].
        apply (eqb_true_iff EX (Analysis.key_laws Hl)) in Hsame; subst y.
        pose proof (Hy eq_refl); pose proof (Hselected Heq); congruence.
Qed.

(** Actual output folds preserve values, credit and agreement outside changed unselected outputs. *)
Theorem updates_properties outs m counts :
  good m counts -> (forall x v, In (x, v) outs -> In x U) ->
  let r := Nested.updates a hs (N.of_nat delay) outs m counts in
  good (fst (fst r)) (snd (fst r)) /\
  credit (fst (fst r)) (snd (fst r)) <= credit m counts /\
  fun_leb L (lookup EX L m) (lookup EX L (fst (fst r))) /\
  (forall x v, In (x, v) outs -> leb L v (lookup EX L (fst (fst r)) x) = true) /\
  (forall y, (forall v, In (y, v) outs -> selected y = true) ->
    credit (fst (fst r)) (snd (fst r)) = credit m counts ->
    lookup EX L (fst (fst r)) y = lookup EX L m y).
Proof.
  revert m counts; induction outs as [|[x v] rest IH]; intros m counts Hg Hkeys;
    cbn zeta; rewrite NestedProof.updates_equation.
  - cbn; split; [exact Hg|]; split; [lia|]; split.
    + intro y; apply (leb_refl (Analysis.lattice_law Hl)).
    + split; [intros y value Hin; contradiction|intros; reflexivity].
  - cbn zeta; cbn [fst snd]; fold EX L.
    pose proof (rule_properties m counts x v Hg (Hkeys x v (or_introl eq_refl))) as Hfirst.
    cbn zeta in Hfirst.
    set (first := Update.rule EX L
      (Nested.op_c a hs (N.of_nat delay) x (count_at counts x)) m x v) in *.
    set (next_counts := if snd first then
      Map.set EX x (N.succ (count_at counts x)) counts else counts) in *.
    destruct Hfirst as [Hgfirst [Hlefirst [Hupfirst [Hvfirst Hagreefirst]]]].
    assert (Htail : forall y value, In (y, value) rest -> In y U).
    { intros y value Hin; exact (Hkeys y value (or_intror Hin)). }
    destruct (IH (fst first) next_counts Hgfirst Htail)
      as [Hgfinal [Hlefinal [Hupfinal [Hbounds Hagreefinal]]]].
    split; [exact Hgfinal|]; split; [exact (Nat.le_trans _ _ _ Hlefinal Hlefirst)|].
    split.
    + intro y; eapply (leb_trans (Analysis.lattice_law Hl)); [apply Hupfirst|apply Hupfinal].
    + split.
      * intros y value [Hsame|Hin].
        -- injection Hsame as <- <-; eapply (leb_trans (Analysis.lattice_law Hl));
             [exact Hvfirst|apply Hupfinal].
        -- exact (Hbounds y value Hin).
      * intros y Hy Heq.
        change (credit
          (fst (fst (Nested.updates a hs (N.of_nat delay) rest (fst first) next_counts)))
          (snd (fst (Nested.updates a hs (N.of_nat delay) rest (fst first) next_counts))) =
          credit m counts) in Heq.
        assert (Hmid : credit (fst first) next_counts = credit m counts) by lia.
        assert (Hend : credit
          (fst (fst (Nested.updates a hs (N.of_nat delay) rest (fst first) next_counts)))
          (snd (fst (Nested.updates a hs (N.of_nat delay) rest (fst first) next_counts))) =
          credit (fst first) next_counts) by lia.
        eapply eq_trans.
        -- exact (Hagreefinal y (fun value Hin => Hy value (or_intror Hin)) Hend).
        -- apply Hagreefirst; [|exact Hmid].
           intros ->; apply (Hy v); now left.
Qed.

(** Already bounded frozen outputs skip every actual update and retain both maps. *)
Theorem updates_below outs m counts :
  (forall x v, In (x, v) outs -> leb L v (lookup EX L m x) = true) ->
  Nested.updates a hs (N.of_nat delay) outs m counts = (m, counts, false).
Proof.
  revert m counts; induction outs as [|[x v] rest IH]; intros m counts Hbelow;
    rewrite NestedProof.updates_equation; [reflexivity|].
  cbn zeta; fold EX L; rewrite Update.rule_equation; fold EX L.
  rewrite (Hbelow x v (or_introl eq_refl)); cbn [fst snd].
  rewrite IH by (intros y value Hin; exact (Hbelow y value (or_intror Hin))); reflexivity.
Qed.

(** Initial cut credit follows only from the full widening rank and the actual policy delay. *)
Theorem initial_credit :
  credit Map.empty Map.empty <= length U * (delay + wbound W).
Proof.
  unfold credit.
  assert (Hconstant : forall xs, WorklistCost.sum (fun _ : X => delay + wbound W) xs =
    length xs * (delay + wbound W)).
  { intro xs; exact (msum_constant xs (delay + wbound W)). }
  rewrite <- Hconstant; apply WorklistCost.sum_le; intros x Hx.
  unfold site, remaining, count_at; rewrite lookup_empty, Map.find_or_equation, Map.get_empty.
  destruct (selected x); [|lia].
  cbn [N.to_nat]; rewrite Nat.sub_0_r.
  destruct delay as [|n]; cbn [WorklistWiden.local_credit].
  - exact (wrank_bounded W (bot L) I).
  - lia.
Qed.

End Updates.

End NestedCredit.
Import NestedCredit.
