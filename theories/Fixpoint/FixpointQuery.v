(** * Observable costed queries

    A query records reads and side contributions in traversal order.
    For example, asking twice retains both reads even when their keys agree.
    Builds on: CostMonad and Stdlib lists. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
Import List.ListNotations Cost.Notations.

Module Query.

(** Continuations charge for constructing their selected child. *)
Inductive t (X A : Type) : Type :=
  | Ret (a : A)
  | Ask (x : X) (k : A -> Cost.t (t X A))
  | Side (x : X) (a : A) (q : t X A).

Arguments Ret {X A}.
Arguments Ask {X A}.
Arguments Side {X A}.

(** A trace retains the result and both ordered, duplicate-preserving traces. *)
Record trace (X A : Type) := Trace {
  result : A;
  read_log : list X;
  side_log : list (X * A)
}.

Arguments Trace {X A}.
Arguments result {X A}.
Arguments read_log {X A}.
Arguments side_log {X A}.

(** Each node and callback invocation charges overhead in addition to callback work. *)
Fixpoint run_c {X A} (look : X -> Cost.t A) (q : t X A) {struct q}
    : Cost.t (trace X A) :=
  Cost.step ;;
  match q with
  | Ret a => Cost.ret (Trace a [] [])
  | Ask x k =>
    Cost.step ;;
    let* a := look x in
    Cost.step ;;
    let next := k a in
    let child := run_c look (Cost.value next) in
    Cost.bind next (fun _ =>
      Cost.map (fun r => Trace (result r) (x :: read_log r) (side_log r)) child)
  | Side x a child =>
    Cost.map (fun r => Trace (result r) (read_log r) ((x, a) :: side_log r))
      (run_c look child)
  end.

(** Pure observations run the same evaluator with zero-cost assignment reads. *)
Definition run {X A} (q : t X A) (s : X -> A) :=
  Cost.value (run_c (fun x => Cost.ret (s x)) q).

Definition eval {X A} (q : t X A) s := result (run q s).
Definition reads {X A} (q : t X A) s := read_log (run q s).
Definition sides {X A} (q : t X A) s := side_log (run q s).

(** The public equation exposes one query node without exposing the cost implementation. *)
Theorem run_equation {X A} (q : t X A) s :
  run q s =
  match q with
  | Ret a => Trace a [] []
  | Ask x k =>
    let r := run (Cost.value (k (s x))) s in
    Trace (result r) (x :: read_log r) (side_log r)
  | Side x a child =>
    let r := run child s in
    Trace (result r) (read_log r) ((x, a) :: side_log r)
  end.
Proof.
  destruct q; reflexivity.
Qed.

(** Changing lookup charges leaves all observations unchanged when lookup values agree. *)
Theorem run_c_spec {X A} (q : t X A) look s :
  (forall x, Cost.value (look x) = s x) -> Cost.value (run_c look q) = run q s.
Proof.
  intro Hlook; induction q as [a|x k IH|x a child IH].
  - reflexivity.
  - cbn [run_c]; autorewrite with galois_cost.
    rewrite Hlook, run_equation.
    rewrite (IH (s x)); reflexivity.
  - cbn [run_c]; autorewrite with galois_cost.
    rewrite IH, (run_equation (Side x a child) s); reflexivity.
Qed.

(** Running once supplies the result and both public trace projections. *)
Theorem run_spec {X A} (q : t X A) s :
  run q s = Trace (eval q s) (reads q s) (sides q s).
Proof.
  unfold eval, reads, sides; destruct (run q s); reflexivity.
Qed.

(** Agreement on actual reads determines the complete observable trace. *)
Theorem query_determined {X A} (q : t X A) s u :
  (forall x, In x (reads q s) -> s x = u x) ->
  eval q s = eval q u /\ reads q s = reads q u /\ sides q s = sides q u.
Proof.
  induction q as [a|x k IH|x a child IH]; intro Hagree.
  - repeat split; reflexivity.
  - assert (Hx : s x = u x).
    { apply Hagree; unfold reads; rewrite run_equation; now left. }
    assert (Htail : forall y, In y (reads (Cost.value (k (s x))) s) -> s y = u y).
    { intros y Hy; apply Hagree; unfold reads in *; rewrite run_equation; now right. }
    destruct (IH (s x) Htail) as [Hv [Hr Hs]].
    unfold eval, reads, sides in *.
    rewrite (run_equation (Ask x k) s), (run_equation (Ask x k) u), <- Hx.
    cbn -[run]; rewrite Hv, Hr, Hs; auto.
  - assert (Htail : forall y, In y (reads child s) -> s y = u y).
    { intros y Hy; apply Hagree; unfold reads; rewrite run_equation; exact Hy. }
    destruct (IH Htail) as [Hv [Hr Hs]].
    unfold eval, reads, sides in *.
    rewrite (run_equation (Side x a child) s), (run_equation (Side x a child) u).
    cbn -[run].
    rewrite Hv, Hr, Hs; auto.
Qed.

(** A path budget bounds its node count and every selected continuation charge. *)
Inductive within {X A} (tau : N) (s : X -> A) : nat -> t X A -> Prop :=
  | within_ret a : within tau s 1 (Ret a)
  | within_ask n x k :
      (Cost.ticks (k (s x)) <= tau)%N ->
      within tau s n (Cost.value (k (s x))) ->
      within tau s (S n) (Ask x k)
  | within_side n x a q :
      within tau s n q -> within tau s (S n) (Side x a q)
  | within_bound n m q :
      within tau s n q -> (n <= m)%nat -> within tau s m q.

(** Path budgets include query nodes, lookup work and continuation work with call overhead. *)
Theorem run_c_cost {X A} (q : t X A) look s nu tau w :
  within tau s nu q ->
  (forall x, Cost.value (look x) = s x) ->
  (forall x, (Cost.ticks (look x) <= w)%N) ->
  (Cost.ticks (run_c look q) <= N.of_nat nu * (3 + w + tau))%N.
Proof.
  intros Hwithin Hlook Hcost; induction Hwithin as
    [a|n x k Hk Hwithin IH|n x a child Hwithin IH|n m child Hwithin IH Hle];
    cbn [run_c]; autorewrite with galois_cost.
  - nia.
  - rewrite Hlook, Nat2N.inj_succ; specialize (Hcost x); nia.
  - rewrite Nat2N.inj_succ; nia.
  - assert (Hnm : (N.of_nat n <= N.of_nat m)%N).
    { apply (proj1 (N.compare_le_iff _ _)).
      rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle. }
    eapply N.le_trans; [exact IH|apply N.mul_le_mono_r, Hnm].
Qed.

(** Lookup bounds are needed only for keys on the actual selected read trace. *)
Theorem run_c_cost_on {X A} (q : t X A) look s nu tau w :
  within tau s nu q ->
  (forall x, Cost.value (look x) = s x) ->
  (forall x, In x (reads q s) -> (Cost.ticks (look x) <= w)%N) ->
  (Cost.ticks (run_c look q) <= N.of_nat nu * (3 + w + tau))%N.
Proof.
  intros Hwithin Hlook; induction Hwithin as
    [a|n x k Hk Hwithin IH|n x a child Hwithin IH|n m child Hwithin IH Hle];
    intro Hcost.
  - cbn [run_c]; autorewrite with galois_cost; nia.
  - assert (Hx : (Cost.ticks (look x) <= w)%N).
    { apply Hcost; change (In x (x :: reads (Cost.value (k (s x))) s)); now left. }
    assert (Htail : (Cost.ticks (run_c look (Cost.value (k (s x)))) <=
      N.of_nat n * (3 + w + tau))%N).
    { apply IH; intros y Hy; apply Hcost.
      change (In y (x :: reads (Cost.value (k (s x))) s)); now right. }
    cbn [run_c]; autorewrite with galois_cost.
    rewrite Hlook, Nat2N.inj_succ; nia.
  - change (forall x, In x (reads child s) -> (Cost.ticks (look x) <= w)%N) in Hcost.
    specialize (IH Hcost); cbn [run_c]; autorewrite with galois_cost.
    rewrite Nat2N.inj_succ; nia.
  - specialize (IH Hcost).
    assert (Hnm : (N.of_nat n <= N.of_nat m)%N).
    { apply (proj1 (N.compare_le_iff _ _)).
      rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle. }
    eapply N.le_trans; [exact IH|apply N.mul_le_mono_r, Hnm].
Qed.

End Query.
Import Query.

(** Sequenced reads charge the costed continuation only at the end. *)
Fixpoint ask_all_c {X A} (xs : list X) (k : list A -> Cost.t (Query.t X A))
    : Cost.t (Query.t X A) :=
  match xs with
  | [] => Cost.step ;; k []
  | x :: rest =>
    Cost.step ;;
    Cost.ret (Query.Ask x (fun a => ask_all_c rest (fun vs => k (a :: vs))))
  end.

Definition ask_all {X A} xs (k : list A -> Cost.t (Query.t X A)) :=
  Cost.value (ask_all_c xs k).

(** Sequenced contributions keep their original order. *)
Fixpoint side_all_c {X A} (xs : list (X * A)) (q : Query.t X A) : Cost.t (Query.t X A) :=
  match xs with
  | [] => Cost.ret q
  | (x, a) :: rest =>
    Cost.step ;; Cost.map (Query.Side x a) (side_all_c rest q)
  end.

Definition side_all {X A} xs (q : Query.t X A) := Cost.value (side_all_c xs q).

(** Sequenced asks prefix the selected continuation's read trace. *)
Theorem ask_all_spec {X A} (s : X -> A) xs k :
  Query.reads (ask_all xs k) s =
    xs ++ Query.reads (Cost.value (k (map s xs))) s /\
  Query.eval (ask_all xs k) s = Query.eval (Cost.value (k (map s xs))) s /\
  Query.sides (ask_all xs k) s = Query.sides (Cost.value (k (map s xs))) s.
Proof.
  revert k; induction xs as [|x xs IH]; intro k.
  - repeat split; reflexivity.
  - change (x :: Query.reads (ask_all xs (fun vs => k (s x :: vs))) s =
        x :: (xs ++ Query.reads (Cost.value (k (s x :: map s xs))) s) /\
      Query.eval (ask_all xs (fun vs => k (s x :: vs))) s =
        Query.eval (Cost.value (k (s x :: map s xs))) s /\
      Query.sides (ask_all xs (fun vs => k (s x :: vs))) s =
        Query.sides (Cost.value (k (s x :: map s xs))) s).
    destruct (IH (fun vs => k (s x :: vs))) as [Hr [Hv Hs]].
    rewrite Hr, Hv, Hs; auto.
Qed.

(** Sequenced sides prefix the contribution trace and leave reads and result unchanged. *)
Theorem side_all_spec {X A} (q : Query.t X A) s xs :
  Query.eval (side_all xs q) s = Query.eval q s /\
  Query.reads (side_all xs q) s = Query.reads q s /\
  Query.sides (side_all xs q) s = xs ++ Query.sides q s.
Proof.
  induction xs as [|[x a] xs IH].
  - repeat split; reflexivity.
  - change (Query.eval (side_all xs q) s = Query.eval q s /\
      Query.reads (side_all xs q) s = Query.reads q s /\
      (x, a) :: Query.sides (side_all xs q) s =
        (x, a) :: (xs ++ Query.sides q s)).
    destruct IH as [Hv [Hr Hs]].
    rewrite Hv, Hr, Hs; auto.
Qed.
