(** * Constraint evaluation and updates

    Every engine shares the same evaluator and conditional update rule.
    For example, a repeated side target is updated in trace order.
    Builds on: FixpointSystem, CostMonad, BaseMap and BaseEq. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem.
Import List.ListNotations Cost.Notations.

Module Eval.

(** Outputs place the primary target before the ordered side trace. *)
Definition outputs_c {X C A} (S : System.t X C A) (look : X -> Cost.t A) c
    : Cost.t (list (X * A) * list X) :=
  Cost.step ;;
  let* x := System.target_c S c in
  Cost.step ;;
  let* q := System.rhs_c S c in
  let* r := Query.run_c look q in
  Cost.ret ((x, Query.result r) :: Query.side_log r, Query.read_log r).

Definition outputs {X C A} (S : System.t X C A) c (s : X -> A) :=
  Cost.value (outputs_c S (fun x => Cost.ret (s x)) c).

(** Evaluation returns exactly the target, side and read observations of one query run. *)
Theorem outputs_spec {X C A} (S : System.t X C A) c s :
  outputs S c s =
    ((System.target S c, Query.eval (System.rhs S c) s) ::
      Query.sides (System.rhs S c) s, Query.reads (System.rhs S c) s).
Proof.
  reflexivity.
Qed.

(** Arbitrary lookup charges are retained without changing the outputs. *)
Theorem outputs_c_spec {X C A} (S : System.t X C A) c look s :
  (forall x, Cost.value (look x) = s x) ->
  Cost.value (outputs_c S look c) = outputs S c s.
Proof.
  intro Hlook; unfold outputs_c; autorewrite with galois_cost.
  rewrite (Query.run_c_spec _ look s Hlook); reflexivity.
Qed.

(** Evaluation retains both system callback charges and the complete charged query run. *)
Theorem outputs_cost {X C A} (S : System.t X C A) c look :
  Cost.ticks (outputs_c S look c) =
    (2 + Cost.ticks (System.target_c S c) + Cost.ticks (System.rhs_c S c) +
      Cost.ticks (Query.run_c look (System.rhs S c)))%N.
Proof.
  unfold outputs_c; autorewrite with galois_cost.
  fold (System.rhs S c).
  lia.
Qed.

Arguments outputs_c {X C A} S look c : simpl never.
Arguments outputs {X C A} S c s : simpl never.

End Eval.
Import Eval.

Module Update.

(** The one update rule skips bounded contributions and otherwise invokes its costed operator. *)
Definition rule_c {X A} (EX : encoding X) (L : lattice A)
    (op : A -> A -> Cost.t A) (m : assignment X A) x a
    : Cost.t (assignment X A * bool) :=
  let* old := lookup_c EX L m x in
  Cost.step ;;
  let* below := leb_c L a old in
  if below then Cost.ret (m, false)
  else
    Cost.step ;;
    let* value := op old a in
    let* next := Map.set_c EX x value m in
    Cost.ret (next, true).

Definition rule {X A} (EX : encoding X) (L : lattice A) op m x a :=
  Cost.value (rule_c EX L op m x a).

(** The rule equation exposes the skip decision and the single map write. *)
Theorem rule_equation {X A} (EX : encoding X) (L : lattice A) op m x a :
  rule EX L op m x a =
    if leb L a (lookup EX L m x) then (m, false)
    else (Map.set EX x (Cost.value (op (lookup EX L m x) a)) m, true).
Proof.
  unfold rule, rule_c; autorewrite with galois_cost.
  change (Cost.value
    (if leb L a (lookup EX L m x) then Cost.ret (m, false)
     else Cost.step ;;
       let* value := op (lookup EX L m x) a in
       let* next := Map.set_c EX x value m in Cost.ret (next, true)) =
    if leb L a (lookup EX L m x) then (m, false)
    else (Map.set EX x (Cost.value (op (lookup EX L m x) a)) m, true)).
  destruct (leb L a (lookup EX L m x)); autorewrite with galois_cost; reflexivity.
Qed.

(** A well-formed input yields a well-formed output for every operator. *)
Theorem rule_wf {X A} (EX : encoding X) (L : lattice A) op m x a :
  Map.wf EX m -> Map.wf EX (fst (rule EX L op m x a)).
Proof.
  intro Hwf; rewrite rule_equation; destruct (leb L a (lookup EX L m x));
    cbn [fst]; [exact Hwf|now apply Map.wf_set].
Qed.

(** Lookup changes only at the updated key, and the flag records exactly the skip decision. *)
Theorem rule_spec {X A} (EX : encoding X) (L : lattice A) op m x a :
  Map.wf EX m ->
  snd (rule EX L op m x a) = negb (leb L a (lookup EX L m x)) /\
  forall y, lookup EX L (fst (rule EX L op m x a)) y =
    if leb L a (lookup EX L m x) then lookup EX L m y
    else if eqb EX y x then Cost.value (op (lookup EX L m x) a) else lookup EX L m y.
Proof.
  intro Hwf; rewrite rule_equation; destruct (leb L a (lookup EX L m x));
    cbn [fst snd negb]; split; try reflexivity.
  intro y; rewrite !lookup_equation, Map.get_set by exact Hwf.
  destruct (eqb EX y x); reflexivity.
Qed.

(** No change retains the original map exactly. *)
Theorem rule_unchanged {X A} (EX : encoding X) (L : lattice A) op m x a :
  snd (rule EX L op m x a) = false -> fst (rule EX L op m x a) = m.
Proof.
  rewrite rule_equation; destruct (leb L a (lookup EX L m x)); cbn; congruence.
Qed.

(** Updating retains lookup, comparison, operator and map-write charges on the taken branch. *)
Theorem rule_cost {X A} (EX : encoding X) (L : lattice A) op m x a :
  Cost.ticks (rule_c EX L op m x a) =
    (Cost.ticks (lookup_c EX L m x) + 1 +
      Cost.ticks (leb_c L a (lookup EX L m x)) +
      if leb L a (lookup EX L m x) then 0
      else 1 + Cost.ticks (op (lookup EX L m x) a) +
        Cost.ticks (Map.set_c EX x (Cost.value (op (lookup EX L m x) a)) m))%N.
Proof.
  unfold rule_c; autorewrite with galois_cost.
  fold (lookup EX L m x); fold (leb L a (lookup EX L m x)).
  destruct (leb L a (lookup EX L m x)); autorewrite with galois_cost;
    lia.
Qed.

(** Applying outputs invokes the single rule in trace order and combines its change flags. *)
Fixpoint apply_c {X A} (EX : encoding X) (L : lattice A) op
    (outs : list (X * A)) (m : assignment X A) : Cost.t (assignment X A * bool) :=
  match outs with
  | [] => Cost.ret (m, false)
  | (x, a) :: rest =>
    Cost.step ;;
    let* first := rule_c EX L op m x a in
    let* next := apply_c EX L op rest (fst first) in
    Cost.ret (fst next, snd first || snd next)
  end.

Definition apply {X A} (EX : encoding X) (L : lattice A) op outs m :=
  Cost.value (apply_c EX L op outs m).

(** The output-fold equation uses the public rule as its sole update operation. *)
Theorem apply_equation {X A} (EX : encoding X) (L : lattice A) op outs m :
  apply EX L op outs m =
  match outs with
  | [] => (m, false)
  | (x, a) :: rest =>
    let first := rule EX L op m x a in
    let next := apply EX L op rest (fst first) in
    (fst next, snd first || snd next)
  end.
Proof.
  destruct outs as [|[x a] rest]; reflexivity.
Qed.

(** Applying outputs maintains map well-formedness. *)
Theorem apply_wf {X A} (EX : encoding X) (L : lattice A) op outs m :
  Map.wf EX m -> Map.wf EX (fst (apply EX L op outs m)).
Proof.
  revert m; induction outs as [|[x a] rest IH]; intros m Hwf; rewrite apply_equation.
  - exact Hwf.
  - cbn [fst]; apply IH, rule_wf, Hwf.
Qed.

(** An unchanged output fold leaves its input map unchanged. *)
Theorem apply_unchanged {X A} (EX : encoding X) (L : lattice A) op outs m :
  snd (apply EX L op outs m) = false -> fst (apply EX L op outs m) = m.
Proof.
  revert m; induction outs as [|[x a] rest IH]; intro m; rewrite apply_equation.
  - reflexivity.
  - cbn [fst snd]; rewrite orb_false_iff; intros [Hfirst Hnext].
    rewrite (IH _ Hnext); now apply rule_unchanged.
Qed.

(** A stationary output fold bounds every contribution in the unchanged input assignment. *)
Theorem apply_stationary {X A} (EX : encoding X) (L : lattice A) op outs m :
  snd (apply EX L op outs m) = false ->
  forall x a, In (x, a) outs -> leb L a (lookup EX L m x) = true.
Proof.
  revert m; induction outs as [|[x a] rest IH]; intros m Hstable y b Hin.
  - contradiction.
  - rewrite apply_equation in Hstable; cbn [snd] in Hstable.
    apply orb_false_iff in Hstable as [Hfirst Hnext].
    rewrite (rule_unchanged EX L op m x a Hfirst) in Hnext.
    destruct Hin as [Heq|Hin].
    + injection Heq as <- <-.
      rewrite rule_equation in Hfirst.
      destruct (leb L a (lookup EX L m x)); cbn in Hfirst; congruence.
    + exact (IH m Hnext y b Hin).
Qed.

(** An output fold leaves every key outside its output list unchanged. *)
Theorem apply_preserves {X A} (EX : encoding X) (HE : encoding_laws EX)
    (L : lattice A) op outs m p :
  Map.wf EX m -> (forall x a, In (x, a) outs -> p <> x) ->
  lookup EX L (fst (apply EX L op outs m)) p = lookup EX L m p.
Proof.
  revert m; induction outs as [|[x a] outs IH]; intros m Hwf Houtside;
    rewrite apply_equation; [reflexivity|].
  cbn [fst]; rewrite IH.
  - rewrite (proj2 (rule_spec EX L op m x a Hwf)).
    destruct (leb L a (lookup EX L m x)); [reflexivity|].
    rewrite (proj2 (eqb_false_iff EX HE p x) (Houtside x a (or_introl eq_refl))).
    reflexivity.
  - apply rule_wf, Hwf.
  - intros y b Hb; exact (Houtside y b (or_intror Hb)).
Qed.

Arguments rule_c {X A} EX L op m x a : simpl never.
Arguments rule {X A} EX L op m x a : simpl never.
Arguments apply_c {X A} EX L op outs m : simpl never.
Arguments apply {X A} EX L op outs m : simpl never.

End Update.
Import Update.
