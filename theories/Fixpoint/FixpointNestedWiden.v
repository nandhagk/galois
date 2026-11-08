(** * Derived widening credit at selected output points

    Remaining delay credits pay for joins before a bounded widening rank takes over.
    For example, an unbounded ascending natural-number loop finishes by widening after its delay.
    Builds on: FixpointNestedCost, LatticeHeight and the public map and update contracts. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeKit.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCycles FixpointEval
  FixpointIndex FixpointAnalysis FixpointSolver FixpointNested FixpointNestedProof
  FixpointNestedCost.
Import List.ListNotations.

Local Open Scope nat_scope.

Module NestedWiden.

(** The cut predicate records the intersection actually used by the runtime operator. *)
Definition selected {X C A} (a : Analysis.t X C A) (p : Nested.code X) x :=
  existsb (eqb (Analysis.key_enc a) x) (Nested.heads p) &&
    Policy.widen_at (Analysis.policy a) x.

(** A widening cut must cut cycles at component heads that the policy also selects. *)
Definition selected_cuts {X C A} (a : Analysis.t X C A) p :=
  cuts_every_cycle (Analysis.static a) (selected a p).

(** This specialization widens every declared output point and permits arbitrary feedback cycles. *)
Definition all_selected {X C A} (a : Analysis.t X C A) p :=
  forall x, In x (NestedCost.universe a) -> selected a p x = true.

(** Value closure is independent of the computational analysis and widening-rank dictionary. *)
Record invariant_laws {X C A} (a : Analysis.t X C A) (inv : A -> Prop) : Prop := InvariantLaws {
  bottom_invariant : inv (bot (Analysis.lat a));
  join_invariant : forall x y, inv x -> inv y -> inv (join (Analysis.lat a) x y);
  widen_invariant : forall x y, inv x -> inv y -> inv (widen (Analysis.lat a) x y);
  outputs_invariant : forall s, (forall x, inv (s x)) ->
    forall c, In c (System.constraints (Analysis.system a)) ->
    forall x v, In (x, v) (fst (Eval.outputs (Analysis.system a) c s)) -> inv v
}.

Section Credit.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (Hselected : all_selected a p)
  {inv : A -> Prop} (WR : widening_rank_on (Analysis.lat a) inv)
  (HI : invariant_laws a inv).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let U := NestedCost.universe a.
Let hs := FinSet.of_list EX (Nested.heads p).
Let d := Policy.delay (Analysis.policy a).

Definition count_at (counts : Map.t X N) x := Map.find_or EX 0%N x counts.

(** One remaining delayed join can spend the full rank bound and still consume one credit. *)
Definition credit (v : A) (count : N) :=
  (d - N.to_nat count) * (wbound WR + 1) + wrank WR v.

Definition rho (m : assignment X A) (counts : Map.t X N) :=
  msum U (fun x => credit (lookup EX L m x) (count_at counts x)).

(** The invariant includes both maps so counter updates have their public lookup semantics. *)
Definition good (m : assignment X A) (counts : Map.t X N) : Prop :=
  Map.wf EX m /\ Map.wf EX counts /\ forall x, inv (lookup EX L m x).

Local Lemma count_empty x : count_at Map.empty x = 0%N.
Proof.
  unfold count_at; rewrite Map.find_or_equation, Map.get_empty; reflexivity.
Qed.

Local Lemma count_set counts x n y :
  Map.wf EX counts ->
  count_at (Map.set EX x n counts) y =
    if eqb EX y x then n else count_at counts y.
Proof.
  intro Hwf; unfold count_at; rewrite !Map.find_or_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

Local Lemma lookup_set m x v y :
  Map.wf EX m ->
  lookup EX L (Map.set EX x v m) y = if eqb EX y x then v else lookup EX L m y.
Proof.
  intro Hwf; rewrite !lookup_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

Local Lemma operator_value x count old value :
  In x U ->
  Cost.value (Nested.op_c a hs (N.of_nat d) x count old value) =
    if N.leb (N.of_nat d) count then widen L old value else join L old value.
Proof.
  intro Hx; pose proof (Hselected x Hx) as Hsel.
  unfold selected in Hsel; apply andb_true_iff in Hsel as [Hhead Hpolicy].
  unfold Nested.op_c; autorewrite with galois_cost.
  fold EX; fold (FinSet.mem EX x hs) (Policy.widen_at (Analysis.policy a) x).
  fold EX in Hhead; unfold hs; rewrite FinSet.mem_of_list, Hhead, Hpolicy.
  destruct (N.leb (N.of_nat d) count); reflexivity.
Qed.

Local Lemma operator_invariant x count old value :
  In x U -> inv old -> inv value ->
  inv (Cost.value (Nested.op_c a hs (N.of_nat d) x count old value)).
Proof.
  intros Hx Hold Hvalue; rewrite operator_value by exact Hx.
  destruct (N.leb (N.of_nat d) count).
  - apply (widen_invariant _ _ HI); assumption.
  - apply (join_invariant _ _ HI); assumption.
Qed.

Local Lemma credit_progress x old value count :
  In x U -> inv old -> inv value -> leb L value old = false ->
  credit (Cost.value (Nested.op_c a hs (N.of_nat d) x count old value)) (N.succ count) <
    credit old count.
Proof.
  intros Hx Hold Hvalue Hbelow; rewrite operator_value by exact Hx.
  unfold credit; rewrite N2Nat.inj_succ.
  destruct (N.leb (N.of_nat d) count) eqn:Hdelay.
  - apply N.leb_le in Hdelay.
    pose proof (widen_rank_progress WR old value Hold Hvalue Hbelow) as Hrank.
    assert (Hnat : d <= N.to_nat count) by lia.
    replace (d - N.to_nat count) with 0 by lia.
    replace (d - S (N.to_nat count)) with 0 by lia.
    cbn; exact Hrank.
  - apply N.leb_gt in Hdelay.
    pose proof (wrank_bounded WR (join L old value)
      (join_invariant _ _ HI old value Hold Hvalue)); nia.
Qed.

Local Lemma rule_progress m counts x value :
  good m counts -> In x U -> inv value ->
  let count := count_at counts x in
  let first := Update.rule EX L (Nested.op_c a hs (N.of_nat d) x count) m x value in
  let counts' := if snd first then Map.set EX x (N.succ count) counts else counts in
  good (fst first) counts' /\
  rho (fst first) counts' <= rho m counts /\
  (snd first = true -> rho (fst first) counts' < rho m counts).
Proof.
  intros [Hwf [Hcounts Hinv]] Hx Hvalue; cbn zeta.
  rewrite Update.rule_equation.
  destruct (leb L value (lookup EX L m x)) eqn:Hbelow; cbn [fst snd].
  - split; [repeat split; assumption|]; split; [lia|discriminate].
  - set (v := Cost.value (Nested.op_c a hs (N.of_nat d) x (count_at counts x)
      (lookup EX L m x) value)).
    assert (Hv : inv v) by
      (apply operator_invariant; [exact Hx|apply Hinv|exact Hvalue]).
    assert (Hpoint : forall y,
      credit (lookup EX L (Map.set EX x v m) y)
        (count_at (Map.set EX x (N.succ (count_at counts x)) counts) y) <=
      credit (lookup EX L m y) (count_at counts y)).
    { intro y; rewrite lookup_set, count_set by assumption.
      destruct (eqb EX y x) eqn:Hsame; [|lia].
      apply (eqb_true_iff EX (Analysis.key_laws Hl)) in Hsame; subst y.
      pose proof (credit_progress x (lookup EX L m x) value (count_at counts x)
        Hx (Hinv x) Hvalue Hbelow); unfold v; lia. }
    split.
    + split; [apply Map.wf_set, Hwf|]; split; [apply Map.wf_set, Hcounts|].
      intro y; rewrite lookup_set by exact Hwf.
      destruct (eqb EX y x); [exact Hv|apply Hinv].
    + split.
      * apply msum_bounded; intros y Hy; apply Hpoint.
      * intros _; unfold rho; apply msum_grows.
        -- intros y Hy; apply Hpoint.
        -- exists x; split; [exact Hx|].
           rewrite lookup_set, count_set by assumption; rewrite eqb_refl.
           apply credit_progress; [exact Hx|apply Hinv|exact Hvalue|exact Hbelow].
Qed.

Local Lemma updates_progress outs m counts :
  good m counts ->
  (forall x v, In (x, v) outs -> In x U /\ inv v) ->
  let r := Nested.updates a hs (N.of_nat d) outs m counts in
  good (fst (fst r)) (snd (fst r)) /\
  rho (fst (fst r)) (snd (fst r)) <= rho m counts /\
  (snd r = true -> rho (fst (fst r)) (snd (fst r)) < rho m counts).
Proof.
  revert m counts; induction outs as [|[x v] rest IH]; intros m counts Hg Houts;
    cbn zeta; rewrite NestedProof.updates_equation.
  - cbn; split; [exact Hg|]; split; [lia|discriminate].
  - cbn zeta; cbn [fst snd]; fold EX L.
    destruct (Houts x v (or_introl eq_refl)) as [Hx Hv].
    pose proof (rule_progress m counts x v Hg Hx Hv) as Hfirst.
    cbn zeta in Hfirst.
    set (first := Update.rule EX L
      (Nested.op_c a hs (N.of_nat d) x (count_at counts x)) m x v) in *.
    set (counts' := if snd first then
      Map.set EX x (N.succ (count_at counts x)) counts else counts) in *.
    destruct Hfirst as [Hgfirst [Hlefirst Hstrictfirst]].
    assert (Hrest : forall y w, In (y, w) rest -> In y U /\ inv w).
    { intros y w Hin; apply Houts; now right. }
    destruct (IH (fst first) counts' Hgfirst Hrest) as [Hgfinal [Hlefinal Hstrictfinal]].
    split; [exact Hgfinal|]; split; [exact (Nat.le_trans _ _ _ Hlefinal Hlefirst)|].
    rewrite orb_true_iff; intros [Hchange|Hchange].
    + exact (Nat.le_lt_trans _ _ _ Hlefinal (Hstrictfirst Hchange)).
    + exact (Nat.lt_le_trans _ _ _ (Hstrictfinal Hchange) Hlefirst).
Qed.

Local Lemma output_keys c m x v :
  In c (System.constraints (Analysis.system a)) ->
  In (x, v) (fst (Eval.outputs (Analysis.system a) c (lookup EX L m))) -> In x U.
Proof.
  intros Hc Hout; unfold U, NestedCost.universe; apply in_flat_map.
  exists c; split; [exact Hc|].
  rewrite Eval.outputs_spec in Hout; cbn [fst] in Hout.
  destruct Hout as [Hsame|Hside]; [injection Hsame as <- <-; now left|].
  right; apply (System.sides_within (Analysis.static_law Hl) c (lookup EX L m)).
  apply in_map_iff; exists (x, v); auto.
Qed.

(** Widening ranks and finite delay counters establish the actual local evaluation-credit laws. *)
Theorem evaluation_laws :
  NestedCost.evaluation_laws a p good rho.
Proof.
  constructor.
  - split; [apply Map.wf_empty|]; split; [apply Map.wf_empty|].
    intro x; rewrite lookup_empty; apply (bottom_invariant _ _ HI).
  - intros m counts c Hg Hc; apply updates_progress; [exact Hg|].
    intros x v Hout; split.
    + exact (output_keys c m x v Hc Hout).
    + apply (outputs_invariant _ _ HI (lookup EX L m) (proj2 (proj2 Hg)) c Hc x v Hout).
Qed.

(** The initial rank-and-delay credit is bounded using only the output inventory and rank data. *)
Theorem initial_credit :
  rho Map.empty Map.empty <= length U * (d * (wbound WR + 1) + wrank WR (bot L)).
Proof.
  unfold rho; rewrite <- msum_constant; apply msum_bounded.
  intros x Hx; rewrite lookup_empty, count_empty; unfold credit; cbn; lia.
Qed.

(** Selecting every declared output implies the separate cut duty for the runtime intersection. *)
Theorem selected_cuts_all : selected_cuts a p.
Proof.
  assert (Hedge : forall x y, flows (Analysis.static a) x y -> selected a p y = true).
  { intros x y [c [Hc [Hread Hout]]]; apply Hselected.
    unfold NestedCost.universe; apply in_flat_map; exists c; split; [exact Hc|].
    destruct Hout as [->|Hin]; [now left|now right]. }
  intros x Hcycle.
  induction Hcycle as [x y [Hflow Hno]|x y z Hxy IHxy Hyz IHyz].
  - pose proof (Hedge x y Hflow); congruence.
  - exact IHxy.
Qed.

(** Every-output widening has an actual fuel threshold without a finite-height premise. *)
Theorem fuel_enough fuel :
  Nested.code_ok a p ->
  (NestedCost.work EX
    (index_system EX (Analysis.system a) (Analysis.static a)) p + 1) *
    (1 + (Nested.depth p + 1) *
      (length U * (d * (wbound WR + 1) + wrank WR (bot L)))) < Pos.to_nat fuel ->
  exists m, Nested.run a p fuel = Outcome.Solved m.
Proof.
  intros Hcode Hfuel.
  apply (NestedCost.ranked_fuel_enough a p (Analysis.key_laws Hl)
    good rho evaluation_laws fuel Hcode).
  pose proof initial_credit as Hinitial; fold EX L d U in Hinitial |- *.
  eapply Nat.le_lt_trans; [|exact Hfuel].
  apply Nat.mul_le_mono_l, Nat.add_le_mono_l, Nat.mul_le_mono_l, Hinitial.
Qed.

End Credit.

End NestedWiden.
Import NestedWiden.
