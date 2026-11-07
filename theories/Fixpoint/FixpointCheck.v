(** * Full solution checking

    The checker evaluates each constraint once and checks every output.
    For example, a side value above its destination rejects the candidate.
    Builds on: FixpointEval and CostList. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval.
Import List.ListNotations Cost.Notations.

Local Lemma forallb_ext {B} (f g : B -> bool) xs :
  (forall x, f x = g x) -> forallb f xs = forallb g xs.
Proof.
  intro Hfg; induction xs as [|x xs IH]; cbn [forallb]; [reflexivity|].
  now rewrite Hfg, IH.
Qed.

(** Universal testing costs at most all callback charges and one tick per list occurrence. *)
Theorem forallb_cost {B} (f : B -> Cost.t bool) xs :
  (Cost.ticks (forallb_c f xs) <=
    fold_right (fun x total => 1 + Cost.ticks (f x) + total) 0 xs)%N.
Proof.
  induction xs as [|x xs IH].
  - rewrite ticks_forallb_c_nil; reflexivity.
  - rewrite ticks_forallb_c_cons; cbn [fold_right].
    destruct (Cost.value (f x)); nia.
Qed.

(** Every output comparison retains lookup and lattice charges and both call overheads. *)
Definition check_outputs_c {X A} (L : lattice A) (look : X -> Cost.t A)
    (outs : list (X * A)) : Cost.t bool :=
  forallb_c (fun xa =>
    Cost.step ;;
    let* old := look (fst xa) in
    Cost.step ;;
    leb_c L (snd xa) old) outs.

Definition check_constraint_c {X C A} (L : lattice A) (S : System.t X C A) look c :=
  let* r := Eval.outputs_c S look c in
  check_outputs_c L look (fst r).

(** Full checking needs neither static summaries nor lattice laws. *)
Definition check_post_c {X C A} (L : lattice A) (S : System.t X C A) look :=
  forallb_c (check_constraint_c L S look) (System.constraints S).

Definition check_post {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) :=
  Cost.value (check_post_c L S (fun x => Cost.ret (s x))).

(** Checking outputs is pointwise comparison of all contributions. *)
Theorem check_outputs_spec {X A} (L : lattice A) look (s : X -> A) outs :
  (forall x, Cost.value (look x) = s x) ->
  Cost.value (check_outputs_c L look outs) =
    forallb (fun xa => leb L (snd xa) (s (fst xa))) outs.
Proof.
  intro Hlook; unfold check_outputs_c; rewrite value_forallb_c.
  apply forallb_ext; intros [x a]; autorewrite with galois_cost.
  rewrite Hlook; reflexivity.
Qed.

(** Full checking reflects the declarative post-solution property. *)
Theorem check_post_iff {X C A} (L : lattice A) (S : System.t X C A) s :
  check_post L S s = true <-> post_solution L S s.
Proof.
  unfold check_post, check_post_c; rewrite value_forallb_c.
  assert (Hconstraint : forall c,
    Cost.value (check_constraint_c L S (fun x => Cost.ret (s x)) c) =
      forallb (fun xa => leb L (snd xa) (s (fst xa))) (fst (Eval.outputs S c s))).
  { intro c; unfold check_constraint_c; rewrite Cost.value_bind.
    rewrite (Eval.outputs_c_spec S c _ s) by reflexivity.
    apply check_outputs_spec; reflexivity. }
  rewrite (forallb_ext _ _ _ Hconstraint), forallb_forall.
  unfold post_solution; split; intros H c Hc;
    specialize (H c Hc); rewrite Eval.outputs_spec in *; cbn [fst snd forallb] in *.
  - apply andb_true_iff in H as [Hvalue Hsides]; split; [exact Hvalue|].
    intros x a Hin; exact (proj1 (forallb_forall _ _) Hsides (x, a) Hin).
  - destruct H as [Hvalue Hsides]; apply andb_true_iff; split; [exact Hvalue|].
    apply forallb_forall; intros [x a] Hin; exact (Hsides x a Hin).
Qed.

(** Callback-value agreement allows full certification of an arbitrary costed lookup. *)
Theorem check_post_c_spec {X C A} (L : lattice A) (S : System.t X C A) look s :
  (forall x, Cost.value (look x) = s x) ->
  Cost.value (check_post_c L S look) = check_post L S s.
Proof.
  intro Hlook; unfold check_post, check_post_c; rewrite !value_forallb_c.
  apply forallb_ext; intro c; unfold check_constraint_c; rewrite !Cost.value_bind.
  rewrite (Eval.outputs_c_spec S c look s Hlook).
  rewrite (Eval.outputs_c_spec S c (fun x => Cost.ret (s x)) s) by reflexivity.
  rewrite !check_outputs_spec with (s := s) by assumption || reflexivity.
  reflexivity.
Qed.

(** Acceptance certifies every primary and side output. *)
Theorem check_post_sound {X C A} (L : lattice A) (S : System.t X C A) s :
  check_post L S s = true -> post_solution L S s.
Proof.
  apply check_post_iff.
Qed.

(** A checker budget bounds the sum of evaluation and per-output callback work. *)
Definition check_budget {X C A} (L : lattice A) (S : System.t X C A) look budget : Prop :=
  (fold_right (fun c total =>
    (1 + Cost.ticks (Eval.outputs_c S look c) +
      fold_right (fun xa subtotal =>
        3 + Cost.ticks (look (fst xa)) +
          Cost.ticks (leb_c L (snd xa) (Cost.value (look (fst xa)))) + subtotal)
        0 (fst (Cost.value (Eval.outputs_c S look c))) + total)%N)
    0 (System.constraints S) <= budget)%N.

Local Lemma check_outputs_cost {X A} (L : lattice A) look (outs : list (X * A)) :
  (Cost.ticks (check_outputs_c L look outs) <=
    fold_right (fun xa subtotal =>
      3 + Cost.ticks (look (fst xa)) +
        Cost.ticks (leb_c L (snd xa) (Cost.value (look (fst xa)))) + subtotal)
      0 outs)%N.
Proof.
  unfold check_outputs_c; induction outs as [|[x a] outs IH].
  - rewrite ticks_forallb_c_nil; reflexivity.
  - rewrite ticks_forallb_c_cons; autorewrite with galois_cost.
    cbn [fold_right fst snd].
    destruct (Cost.value (leb_c L a (Cost.value (look x)))); nia.
Qed.

(** Full checking costs at most the sum of query, system, lookup and lattice callback work. *)
Theorem check_post_cost {X C A} (L : lattice A) (S : System.t X C A) look budget :
  check_budget L S look budget -> (Cost.ticks (check_post_c L S look) <= budget)%N.
Proof.
  unfold check_budget; intro Hbudget; eapply N.le_trans; [|exact Hbudget].
  clear Hbudget.
  unfold check_post_c.
  induction (System.constraints S) as [|c cs IH].
  - rewrite ticks_forallb_c_nil; reflexivity.
  - rewrite ticks_forallb_c_cons; cbn [fold_right].
    assert (Hcost : (Cost.ticks (check_constraint_c L S look c) <=
      Cost.ticks (Eval.outputs_c S look c) +
      fold_right (fun xa subtotal =>
        3 + Cost.ticks (look (fst xa)) +
          Cost.ticks (leb_c L (snd xa) (Cost.value (look (fst xa)))) + subtotal)
        0 (fst (Cost.value (Eval.outputs_c S look c))))%N).
    { unfold check_constraint_c; rewrite Cost.ticks_bind.
      apply N.add_le_mono_l, check_outputs_cost. }
    destruct (Cost.value (check_constraint_c L S look c)); nia.
Qed.

Arguments check_post_c {X C A} L S look : simpl never.
Arguments check_post {X C A} L S s : simpl never.
