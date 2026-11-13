(** * Queries with explicit frames

    Queries return a value, read a key through a frame, or emit a side contribution.
    For example, [Side x a (Ret b)] returns [b] and the contribution [(x, a)].
    Builds on: Argent.Loop, Base.Trie and Base.MapSig. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import MapSig Trie.

Inductive query (K A F : Type) : Type :=
  | Ret (a : A)
  | Ask (x : K) (f : F)
  | Side (x : K) (a : A) (q : query K A F).

Arguments Ret {K A F} a.
Arguments Ask {K A F} x f.
Arguments Side {K A F} x a q.

Fixpoint peel {K A F} (q : query K A F) (acc : list (K * A))
    : (A + K * F) * list (K * A) :=
  match q with
  | Ret a => (inl a, acc)
  | Ask x f => (inr (x, f), acc)
  | Side x a rest => peel rest ((x, a) :: acc)
  end.
TimeFun peel.

Definition eval_step {K A F} (resume : F -> A -> query K A F) (look : K -> A)
    (s : query K A F * list (K * A))
    : query K A F * list (K * A) + A * list (K * A) :=
  match peel (fst s) (snd s) with
  | (inl a, acc) => inr (a, rev_append acc nil)
  | (inr (x, f), acc) => inl (resume f (look x), acc)
  end.
TimeFun eval_step.

Definition eval_query {K A F} (resume : F -> A -> query K A F) (look : K -> A)
    (fuel : nat) (q : query K A F) : option (A * list (K * A)) :=
  match loop_fuel (eval_step resume look) fuel (q, nil) with
  | inr out => Some out
  | inl _ => None
  end.
TimeFun eval_query.

(** A row is accepted when its primary value and every side contribution fit the lookup. *)
Definition row_ok {K A} (leb : A -> A -> bool) (look : K -> A) (x : K)
    (out : option (A * list (K * A))) : bool :=
  match out with
  | None => false
  | Some (a, ss) =>
    leb a (look x) && forallb (fun xa => leb (snd xa) (look (fst xa))) ss
  end.
TimeFun row_ok.

Definition look_or {K A} (code : K -> positive) (d : A) (m : kmap K A) (x : K) : A :=
  match trie_get (code x) m with
  | Some (_, a) => a
  | None => d
  end.
TimeFun look_or.

(** Output comparison retains the keys and occurrence order of side contributions. *)
Definition out_leb {K A} (leb : A -> A -> bool)
    (left right : option (A * list (K * A))) : Prop :=
  match left, right with
  | Some (a, ss), Some (b, ts) =>
    leb a b = true /\
    Forall2 (fun xa yb => fst xa = fst yb /\ leb (snd xa) (snd yb) = true) ss ts
  | _, _ => False
  end.

(** A continuing prefix can be extended by its next continuing callback. *)
Lemma loop_fuel_succ_inl {St R : Type} (step : St -> St + R) :
  forall n s s1 s2, loop_fuel step n s = inl s1 -> step s1 = inl s2 ->
    loop_fuel step (S n) s = inl s2.
Proof.
  induction n as [|n IH]; intros s s1 s2 Hprefix Hstep.
  - cbn [loop_fuel] in Hprefix; injection Hprefix as <-.
    cbn [loop_fuel]; now rewrite Hstep.
  - cbn [loop_fuel] in Hprefix |- *.
    destruct (step s) as [next|result] eqn:Hnext; [|discriminate].
    now apply (IH next s1 s2).
Qed.

(** Peeling pays once for each side contribution appended to the reverse accumulator. *)
Lemma T_peel_acc {K A F : Type} (q : query K A F) : forall acc,
  (T_peel q acc + N.of_nat (length acc) <=
    N.of_nat (length (snd (peel q acc)) + 1))%N.
Proof.
  induction q as [a|x f|x a q IH]; intros acc.
  - time_step.
  - time_step.
  - specialize (IH ((x, a) :: acc)); time_step.
Qed.

(** A successful query loop charges each reached read and each accumulated side occurrence. *)
Lemma T_eval_loop_le {K A F : Type}
    (resume : F -> A -> query K A F) (T_resume : F -> A -> N)
    (look : K -> A) (T_look : K -> N) (w : N)
    (initial : query K A F * list (K * A)) :
  (forall n q acc x f,
    loop_fuel (eval_step resume look) n initial = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_look x + T_resume f (look x) <= w)%N) ->
  forall fuel used q acc a ss,
    loop_fuel (eval_step resume look) used initial = inl (q, acc) ->
    loop_fuel (eval_step resume look) fuel (q, acc) = inr (a, ss) ->
    (T_loop_fuel (eval_step resume look) (T_eval_step resume T_resume look T_look)
        fuel (q, acc) + N.of_nat (length acc) <=
      6 * N.of_nat fuel * (w + 1) + 2 * N.of_nat (length ss) + 1)%N.
Proof.
  intros Hread fuel; induction fuel as [|fuel IH]; intros used q acc a ss Hprefix Hdone.
  - discriminate.
  - pose proof (T_peel_acc q acc) as Hpeel_cost.
    destruct (peel q acc) as [[value|[x f]] acc1] eqn:Hpeel.
    + assert (Hstep : eval_step resume look (q, acc) =
        inr (value, rev_append acc1 nil)).
      { unfold eval_step; cbn [fst snd]; now rewrite Hpeel. }
      cbn [loop_fuel] in Hdone; rewrite Hstep in Hdone.
      injection Hdone as <- <-.
      pose proof (List.T_rev_append_le acc1 nil) as Hreverse.
      time_unfold @T_loop_fuel.
      cbn beta iota zeta; rewrite Hstep.
      time_unfold @T_eval_step.
      time_simpl; time_cbn; rewrite Hpeel.
      rewrite rev_append_rev, app_nil_r, length_rev.
      time_cbn_all; nia.
    + assert (Hstep : eval_step resume look (q, acc) =
        inl (resume f (look x), acc1)).
      { unfold eval_step; cbn [fst snd]; now rewrite Hpeel. }
      assert (Hread_cost : (T_look x + T_resume f (look x) <= w)%N).
      { apply (Hread used q acc x f Hprefix); now rewrite Hpeel. }
      assert (Hnext : loop_fuel (eval_step resume look) (S used) initial =
        inl (resume f (look x), acc1)).
      { eapply loop_fuel_succ_inl; [exact Hprefix|exact Hstep]. }
      cbn [loop_fuel] in Hdone; rewrite Hstep in Hdone.
      specialize (IH (S used) (resume f (look x)) acc1 a ss Hnext Hdone).
      assert (Hstep_cost :
        (T_eval_step resume T_resume look T_look (q, acc) + N.of_nat (length acc) <=
          w + N.of_nat (length acc1) + 4)%N).
      { time_unfold @T_eval_step.
        time_simpl; time_cbn; rewrite Hpeel.
        time_cbn_all; nia. }
      time_unfold @T_loop_fuel.
      cbn beta iota zeta; rewrite Hstep.
      time_simpl; time_cbn_all; nia.
Qed.

(** Successful evaluation needs only the read costs along its actual selected path. *)
Lemma T_eval_query_le {K A F : Type}
    (resume : F -> A -> query K A F) (T_resume : F -> A -> N)
    (look : K -> A) (T_look : K -> N) fuel q a ss w :
  eval_query resume look fuel q = Some (a, ss) ->
  (forall n q1 acc x f,
    loop_fuel (eval_step resume look) n (q, nil) = inl (q1, acc) ->
    fst (peel q1 acc) = inr (x, f) ->
    (T_look x + T_resume f (look x) <= w)%N) ->
  (T_eval_query resume T_resume look T_look fuel q <=
    10 * N.of_nat (fuel + length ss + 1) * (w + 1))%N.
Proof.
  intros Hdone Hread.
  unfold eval_query in Hdone.
  destruct (loop_fuel (eval_step resume look) fuel (q, nil))
    as [[q1 acc]|[value sides]] eqn:Hloop; [discriminate|].
  injection Hdone as <- <-.
  pose proof (T_eval_loop_le resume T_resume look T_look w (q, nil) Hread
    fuel 0 q nil value sides eq_refl Hloop) as Hcost.
  time_unfold @T_eval_query.
  change (1 + T_loop_fuel (eval_step resume look)
    (T_eval_step resume T_resume look T_look) fuel (q, nil) <=
    10 * N.of_nat (fuel + length sides + 1) * (w + 1))%N.
  time_cbn_all; nia.
Qed.
