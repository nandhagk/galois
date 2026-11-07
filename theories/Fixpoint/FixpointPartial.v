(** * Closed partial solutions

    Partial checking visits each indexed contributor once and checks its explored outputs.
    For example, an explored target whose query reads outside the explored set is rejected.
    Builds on: FixpointIndex, FixpointEval and CostList. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseSet BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointCheck.
Import List.ListNotations Cost.Notations.

(** A touched constraint contributes to an explored primary or declared side target. *)
Definition touches {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (E : FinSet.t X) c :=
  exists x, FinSet.mem EX x E = true /\
    (System.target S c = x \/ In x (side_targets SS c)).

(** Closed partial solutions cover dynamic reads and bound every explored output. *)
Definition closed_partial {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) E (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) -> touches EX S SS E c ->
    (forall y, In y (snd (Eval.outputs S c s)) -> FinSet.mem EX y E = true) /\
    forall y a, In (y, a) (fst (Eval.outputs S c s)) ->
      FinSet.mem EX y E = true -> leb L a (s y) = true.

Fixpoint gather_rows_c {X C} (EX : encoding X) (ix : sys_index X C) xs
    : Cost.t (list C) :=
  match xs with
  | [] => Cost.ret []
  | x :: rest =>
    Cost.step ;;
    let* here := contributors_of_c EX ix x in
    let* tail := gather_rows_c EX ix rest in app_c here tail
  end.

(** Prepared contributor visits are deduplicated by the row encoding. *)
Definition partial_rows_c {X C} (EX : encoding X) (EC : encoding C) ix E :=
  let* xs := FinSet.elements_c E in
  let* cs := gather_rows_c EX ix xs in distinct_c EC cs.

Definition partial_rows {X C} (EX : encoding X) (EC : encoding C) ix E :=
  Cost.value (partial_rows_c EX EC ix E).

Definition partial_constraint_c {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) E look c : Cost.t bool :=
  let* r := Eval.outputs_c S look c in
  let* closed := forallb_c (fun y => FinSet.mem_c EX y E) (snd r) in
  let* bounded := forallb_c (fun xa =>
      let* explored := FinSet.mem_c EX (fst xa) E in
      if explored then
        Cost.step ;;
        let* old := look (fst xa) in
        Cost.step ;; leb_c L (snd xa) old
      else Cost.ret true) (fst r) in
  Cost.ret (closed && bounded).

(** Partial checking evaluates each touched constraint at most once. *)
Definition check_partial_c {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (S : System.t X C A) (SS : System.static S) ix E m :=
  let* cs := partial_rows_c EX EC ix E in
  forallb_c (partial_constraint_c EX L S E (lookup_c EX L m)) cs.

Definition check_partial {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (S : System.t X C A) SS ix E m :=
  Cost.value (check_partial_c EX EC L S SS ix E m).

Local Lemma gather_rows_spec {X C} (EX : encoding X) (ix : sys_index X C) xs :
  Cost.value (gather_rows_c EX ix xs) = flat_map (contributors_of EX ix) xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [gather_rows_c flat_map]; autorewrite with galois_cost.
  rewrite ?value_app_c, IH; reflexivity.
Qed.

(** Partial visits contain each touched row at most once even when indexes repeat rows. *)
Theorem partial_rows_nodup {X C} (EX : encoding X) (EC : encoding C) ix E :
  NoDup (partial_rows EX EC ix E).
Proof.
  unfold partial_rows, partial_rows_c; autorewrite with galois_cost.
  apply distinct_nodup.
Qed.

(** A partial visit is exactly a listed constraint touching the explored set. *)
Theorem partial_rows_spec {X C A} (EX : encoding X) (EC : encoding C)
    (HE : encoding_laws EX) (HC : encoding_laws EC) (S : System.t X C A)
    (SS : System.static S) ix E c :
  sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  (In c (partial_rows EX EC ix E) <->
    In c (System.constraints S) /\ touches EX S SS E c).
Proof.
  intros Hix Hwf; unfold partial_rows, partial_rows_c; autorewrite with galois_cost.
  fold (FinSet.elements E).
  fold (distinct EC (Cost.value (gather_rows_c EX ix (FinSet.elements E)))).
  rewrite distinct_spec by exact HC.
  rewrite gather_rows_spec, in_flat_map; split.
  - intros [x [Hx Hc]]; apply (contributors_agree Hix) in Hc as [Hc Hout].
    split; [exact Hc|exists x; split; [|exact Hout]].
    apply (FinSet.elements_spec EX HE x E Hwf), Hx.
  - intros [Hc [x [Hx Hout]]]; exists x; split.
    + apply (FinSet.elements_spec EX HE x E Hwf), Hx.
    + apply (contributors_agree Hix); now split.
Qed.

Local Lemma guard_true (p q : bool) :
  (if p then q else true) = true <-> (p = true -> q = true).
Proof.
  destruct p, q; cbn; intuition discriminate.
Qed.

Local Lemma partial_constraint_spec {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) E look s c :
  (forall x, Cost.value (look x) = s x) ->
  (Cost.value (partial_constraint_c EX L S E look c) = true <->
    (forall y, In y (snd (Eval.outputs S c s)) -> FinSet.mem EX y E = true) /\
    forall y a, In (y, a) (fst (Eval.outputs S c s)) ->
      FinSet.mem EX y E = true -> leb L a (s y) = true).
Proof.
  intro Hlook; unfold partial_constraint_c; rewrite Cost.value_bind.
  rewrite (Eval.outputs_c_spec S c look s Hlook), Cost.value_bind.
  rewrite Cost.value_bind, Cost.value_ret, !value_forallb_c, andb_true_iff.
  rewrite forallb_forall.
  split.
  - intros [Hr Ho]; split; [exact Hr|].
    intros y a Hin Hy; specialize (proj1 (forallb_forall _ _) Ho (y, a) Hin) as H.
    cbn [fst snd] in H; autorewrite with galois_cost in H.
    change (Cost.value (if FinSet.mem EX y E then
      Cost.step ;; let* old := look y in Cost.step ;; leb_c L a old
      else Cost.ret true) = true) in H.
    rewrite Hy in H; autorewrite with galois_cost in H; rewrite Hlook in H; exact H.
  - intros [Hr Ho]; split; [exact Hr|].
    apply forallb_forall; intros [y a] Hin; cbn [fst snd]; autorewrite with galois_cost.
    change (Cost.value (if FinSet.mem EX y E then
      Cost.step ;; let* old := look y in Cost.step ;; leb_c L a old
      else Cost.ret true) = true).
    destruct (FinSet.mem EX y E) eqn:Hy; autorewrite with galois_cost; [|reflexivity].
    rewrite Hlook; exact (Ho y a Hin Hy).
Qed.

(** Indexed partial checking reflects closed partial solutions under explicit index and set laws. *)
Theorem check_partial_correct {X C A} (EX : encoding X) (EC : encoding C)
    (HE : encoding_laws EX) (HC : encoding_laws EC) (L : lattice A)
    (S : System.t X C A) SS ix E m :
  sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  (check_partial EX EC L S SS ix E m = true <->
    closed_partial EX L S SS E (lookup EX L m)).
Proof.
  intros Hix Hwf; unfold check_partial, check_partial_c; rewrite Cost.value_bind.
  rewrite value_forallb_c, forallb_forall; unfold closed_partial.
  fold (partial_rows EX EC ix E).
  split.
  - intros H c Hc Htouch.
    apply (partial_constraint_spec EX L S E (lookup_c EX L m) (lookup EX L m) c).
    + reflexivity.
    + apply H; apply (partial_rows_spec EX EC HE HC S SS ix E c Hix Hwf); now split.
  - intros H c Hc.
    apply (partial_constraint_spec EX L S E (lookup_c EX L m) (lookup EX L m) c).
    + reflexivity.
    + apply (partial_rows_spec EX EC HE HC S SS ix E c Hix Hwf) in Hc as [Hc Htouch].
      exact (H c Hc Htouch).
Qed.

(** Acceptance certifies a closed partial solution under explicit index and explored-set laws. *)
Theorem check_partial_sound {X C A} (EX : encoding X) (EC : encoding C)
    (HE : encoding_laws EX) (HC : encoding_laws EC) (L : lattice A)
    (S : System.t X C A) SS ix E m :
  sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  check_partial EX EC L S SS ix E m = true ->
  closed_partial EX L S SS E (lookup EX L m).
Proof.
  intros Hix Hwf; apply (check_partial_correct EX EC HE HC L S SS ix E m Hix Hwf).
Qed.

(** Partial checking charges preparation and at most one check per distinct touched row. *)
Theorem check_partial_cost {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (S : System.t X C A) SS ix E m :
  (Cost.ticks (check_partial_c EX EC L S SS ix E m) <=
    Cost.ticks (partial_rows_c EX EC ix E) +
    fold_right (fun c total =>
      1 + Cost.ticks (partial_constraint_c EX L S E (lookup_c EX L m) c) + total)
      0 (partial_rows EX EC ix E))%N.
Proof.
  unfold check_partial_c; rewrite Cost.ticks_bind.
  apply N.add_le_mono_l, forallb_cost.
Qed.

Arguments check_partial_c {X C A} EX EC L S SS ix E m : simpl never.
Arguments check_partial {X C A} EX EC L S SS ix E m : simpl never.
