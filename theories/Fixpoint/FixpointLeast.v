(** * Reached and least solutions

    Reachability records finite sequences of the shared constraint update.
    For example, the empty sequence reaches the bottom assignment.
    Builds on: FixpointEval and LatticeCore. *)

From Stdlib Require Import List Bool Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval.
Import Cost.Notations.

(** A constraint step freezes its query inputs before applying the resulting output list. *)
Definition raise_c {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) c m :=
  let* r := Eval.outputs_c S (lookup_c EX L m) c in
  Update.apply_c EX L (join_c L) (fst r) m.

Definition raise_result {X C A} (EX : encoding X) (L : lattice A) S c m :=
  Cost.value (@raise_c X C A EX L S c m).

(** A raise is a shared update of one listed constraint on a well-formed map. *)
Definition raise {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (m n : assignment X A) : Prop :=
  Map.wf EX m /\ exists c, In c (System.constraints S) /\ n = fst (raise_result EX L S c m).

(** Reached functions are observations of maps reached from the empty map. *)
Definition reached {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (s : X -> A) : Prop :=
  exists m, clos_refl_trans (assignment X A) (raise EX L S) Map.empty m /\
    forall x, s x = lookup EX L m x.

(** A least solution bounds every other post-solution pointwise. *)
Definition least_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) :=
  post_solution L S s /\ forall u, post_solution L S u -> fun_leb L s u.

(** A constraint step is characterized by the evaluator and the one update fold. *)
Theorem raise_equation {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) c m :
  raise_result EX L S c m =
    Update.apply EX L (join_c L) (fst (Eval.outputs S c (lookup EX L m))) m.
Proof.
  unfold raise_result, raise_c; rewrite Cost.value_bind.
  rewrite (Eval.outputs_c_spec S c _ (lookup EX L m)) by reflexivity.
  reflexivity.
Qed.

Section Least.
Context {X C A : Type} (EX : encoding X) (HE : encoding_laws EX)
  (L : lattice A) (S : System.t X C A).

Local Lemma rule_below (HJ : lub_laws L) m s x a :
  Map.wf EX m -> fun_leb L (lookup EX L m) s -> leb L a (s x) = true ->
  fun_leb L (lookup EX L (fst (Update.rule EX L (join_c L) m x a))) s.
Proof.
  intros Hwf Hbelow Ha y.
  rewrite (proj2 (Update.rule_spec EX L (join_c L) m x a Hwf)).
  destruct (leb L a (lookup EX L m x)); [apply Hbelow|].
  destruct (eqb EX y x) eqn:Hy; [|apply Hbelow].
  apply (eqb_true_iff EX HE) in Hy; subst y.
  rewrite <- join_equation; apply (join_least HJ); [apply Hbelow|exact Ha].
Qed.

Local Lemma apply_below (HJ : lub_laws L) outs m s :
  Map.wf EX m -> fun_leb L (lookup EX L m) s ->
  (forall x a, In (x, a) outs -> leb L a (s x) = true) ->
  fun_leb L (lookup EX L (fst (Update.apply EX L (join_c L) outs m))) s.
Proof.
  revert m; induction outs as [|[x a] outs IH]; intros m Hwf Hbelow Houts;
    rewrite Update.apply_equation.
  - exact Hbelow.
  - cbn [fst]; apply IH.
    + apply Update.rule_wf, Hwf.
    + apply rule_below; [exact HJ|exact Hwf|exact Hbelow|apply Houts; now left].
    + intros y b Hb; apply Houts; now right.
Qed.

(** Monotone query outputs on a smaller assignment lie below any post-solution. *)
Theorem outputs_below (HL : lattice_laws L) s u c :
  monotone_query L (System.rhs S c) -> In c (System.constraints S) ->
  post_solution L S u -> fun_leb L s u ->
  forall x a, In (x, a) (fst (Eval.outputs S c s)) -> leb L a (u x) = true.
Proof.
  intros [Hvalue Hside] Hc Hpost Hbelow x a Hin.
  rewrite Eval.outputs_spec in Hin; cbn [fst] in Hin.
  destruct (Hpost c Hc) as [Hprimary Hsides].
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; eapply (leb_trans HL); [apply Hvalue, Hbelow|exact Hprimary].
  - destruct (Hside s u Hbelow x a Hin) as [b [Hb Hab]].
    eapply (leb_trans HL); [exact Hab|exact (Hsides x b Hb)].
Qed.

Local Lemma raise_below (HL : lattice_laws L) (HJ : lub_laws L)
    (HM : monotone_system L S) m n s :
  post_solution L S s -> fun_leb L (lookup EX L m) s -> raise EX L S m n ->
  fun_leb L (lookup EX L n) s.
Proof.
  intros Hpost Hbelow [Hwf [c [Hc ->]]]; rewrite raise_equation.
  apply apply_below; [exact HJ|exact Hwf|exact Hbelow|].
  apply outputs_below; [exact HL|apply HM, Hc|exact Hc|exact Hpost|exact Hbelow].
Qed.

(** Every reached assignment lies below every post-solution of a monotone system. *)
Theorem reached_below s u :
  lattice_laws L -> lub_laws L -> monotone_system L S ->
  reached EX L S s -> post_solution L S u -> fun_leb L s u.
Proof.
  intros HL HJ HM [m [Hpath Hagree]] Hpost.
  assert (Hpreserve : forall m n,
    clos_refl_trans (assignment X A) (raise EX L S) m n ->
    fun_leb L (lookup EX L m) u -> fun_leb L (lookup EX L n) u).
  { intros p q Hsteps; induction Hsteps as [p q Hstep|p|p q r Hpq IHpq Hqr IHqr];
      intro Hbelow.
    - eapply raise_below; eassumption.
    - exact Hbelow.
    - apply IHqr, IHpq, Hbelow. }
  intro x; rewrite Hagree; apply (Hpreserve _ _ Hpath).
  intro y; rewrite lookup_empty; apply (bot_least HL).
Qed.

(** A reached post-solution is least under the separate least-upper-bound laws. *)
Theorem reached_least s :
  lattice_laws L -> lub_laws L -> monotone_system L S ->
  reached EX L S s -> post_solution L S s -> least_solution L S s.
Proof.
  intros HL HJ HM Hreached Hpost; split; [exact Hpost|].
  intros u Hu; exact (reached_below s u HL HJ HM Hreached Hu).
Qed.

End Least.

(** Least solutions agree up to the lattice preorder equivalence. *)
Theorem least_solution_unique {X C A} (L : lattice A) (S : System.t X C A) s u :
  least_solution L S s -> least_solution L S u -> fun_leb L s u /\ fun_leb L u s.
Proof.
  intros [Hs Hleast] [Hu Hleast']; split; [apply Hleast, Hu|apply Hleast', Hs].
Qed.
