(** * Reference solver comparison with legacy Rules

    The fixtures compare whole finite relations after converting legacy tuple enumeration.
    For example, the recursive seed produces the same relation at both predicates.
    Builds on: DatalogSolveTest and legacy RulesDelta. *)

From Stdlib Require Import List PeanoNat PArith.
From Galois.Base Require Import BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSolver.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogSolve.
From Galois.Tests.Datalog Require Import DatalogSolveTest.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsFinSet.
From GaloisLegacy.Rules Require RulesSyntax RulesStratify RulesSolve RulesJoin RulesDelta.
Import List.ListNotations.

Definition old_term (t : term) :=
  match t with
  | TVar v => RulesSyntax.TVar v
  | TConst c => RulesSyntax.TConst c
  end.
Definition old_atom (a : atom nat) := RulesSyntax.Atom (pred a) (map old_term (args a)).
Definition old_literal (l : literal nat) :=
  match l with
  | LPos a => RulesSyntax.LPos (old_atom a)
  | LNeg a => RulesSyntax.LNeg (old_atom a)
  end.
Definition old_rule (r : rule nat) :=
  RulesSyntax.Rule (old_atom (head r)) (map old_literal (body r)).
Definition old_program (prog : program nat) :=
  RulesSyntax.Program CollectionsEncoding.nat_encoding (arity prog) (map old_rule (rules prog)).

Definition compare_relations prog facts ps :=
  match solve_program prog facts 8%positive,
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested (old_program prog) facts 8%positive
  with
  | Outcome.Solved db, Some old_db =>
    forallb (fun p => FinSet.equal (set_raw (rel_of prog db p))
      (set_raw (set_of_list tuple_encoding
        (CollectionsFinSet.FinSet.elements (RulesSolve.rel_of (old_program prog) old_db p))))) ps
  | Outcome.Rejected _, None => true
  | _, _ => false
  end.

(** A computed bounded legacy result agrees pointwise with an actual total-reference result. *)
Theorem bounded_legacy_is_reference (prog : RulesSyntax.program nat) facts delta :
  RulesSyntax.program_wf prog facts ->
  (exists st, RulesStratify.stratified prog st) ->
  RulesDelta.delta_bounded_program RulesJoin.IndexedNested prog facts 8%positive = Some delta ->
  exists db, RulesSolve.solve_program prog facts = Some db /\
    forall p ts, RulesSolve.db_holds prog db p ts = RulesSolve.db_holds prog delta p ts.
Proof.
  intros Hwf Hstrat Hbounded.
  destruct (RulesSolve.solve_program_exact prog facts Hwf Hstrat) as [db [Hdb _]].
  exists db; split; [exact Hdb |].
  apply (RulesDelta.solve_program_delta_agrees RulesJoin.IndexedNested prog facts db delta Hwf
    Hdb (RulesDelta.delta_bounded_program_agrees _ _ _ _ _ Hbounded)).
Qed.

Example legacy_empty : compare_relations empty_program [] [0; 42] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_recursive :
  compare_relations recursive_program recursive_facts [0; 1; 2] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_negation :
  compare_relations negation_program negation_facts [1; 2; 3; 4] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_failure : compare_relations self_negation [] [0] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_failure_total_reference :
  RulesSolve.solve_program (old_program self_negation) [] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_nonlinear_chain : compare_relations nonlinear chain [0; 1] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_linear_chain : compare_relations linear chain [0; 1] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_repeated_constant :
  compare_relations repeated_program repeated_facts [0; 1; 2] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma old_copy_safe h b :
  RulesSyntax.safe_rule (old_rule (copy h b)).
Proof.
  intros v [Hv | [a [Ha _]]].
  - exists (RulesSyntax.Atom b [RulesSyntax.TVar 0]); split; [now left | exact Hv].
  - cbn in Ha; destruct Ha as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

Lemma old_recursive_wf :
  RulesSyntax.program_wf (old_program recursive_program) recursive_facts.
Proof.
  split.
  - intros r [Heq | [Heq | Hbad]]; [subst r | subst r | contradiction];
      split; [apply old_copy_safe | | apply old_copy_safe |];
      split; [reflexivity | intros l [Heq | Hbad]; [subst l; reflexivity | contradiction]
        | reflexivity | intros l [Heq | Hbad]; [subst l; reflexivity | contradiction]].
  - intros f [Heq | Hbad]; [subst f; reflexivity | contradiction].
Qed.

(** The recursive differential fixture is connected to the actual legacy total solve result. *)
Example legacy_recursive_total_reference :
  exists db delta,
    RulesSolve.solve_program (old_program recursive_program) recursive_facts = Some db /\
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program recursive_program) recursive_facts 8%positive = Some delta /\
    forall p ts, RulesSolve.db_holds (old_program recursive_program) db p ts =
      RulesSolve.db_holds (old_program recursive_program) delta p ts.
Proof.
  assert (Hbounded : exists delta,
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program recursive_program) recursive_facts 8%positive = Some delta).
  { vm_compute; eexists; reflexivity. }
  destruct Hbounded as [delta Hdelta].
  assert (Hstrat : exists st, RulesStratify.stratified (old_program recursive_program) st).
  { eexists; apply RulesStratify.stratify_sound; vm_compute; reflexivity. }
  destruct (bounded_legacy_is_reference _ _ delta old_recursive_wf Hstrat Hdelta)
    as [db [Hdb Hagree]].
  exists db, delta; auto.
Qed.

Lemma old_negation_wf :
  RulesSyntax.program_wf (old_program negation_program) negation_facts.
Proof.
  split.
  - intros r [Heq | Hbad]; [subst r | contradiction]; split.
    + intros v [Hv | [a [Ha Hv]]].
      * exists (RulesSyntax.Atom 1 [RulesSyntax.TVar 0]); split; [now left | exact Hv].
      * destruct Ha as [Hbad | [Heq | Hbad]]; [discriminate | | contradiction].
        injection Heq as Heq; subst a.
        exists (RulesSyntax.Atom 1 [RulesSyntax.TVar 0]); split; [now left | exact Hv].
    + split; [reflexivity |].
      intros l [Heq | [Heq | Hbad]]; [subst l | subst l | contradiction]; reflexivity.
  - intros f [Heq | [Heq | [Heq | Hbad]]]; [subst f | subst f | subst f | contradiction];
      reflexivity.
Qed.

(** The completed-negation fixture also agrees with the actual total legacy reference. *)
Example legacy_negation_total_reference :
  exists db delta,
    RulesSolve.solve_program (old_program negation_program) negation_facts = Some db /\
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program negation_program) negation_facts 8%positive = Some delta /\
    forall p ts, RulesSolve.db_holds (old_program negation_program) db p ts =
      RulesSolve.db_holds (old_program negation_program) delta p ts.
Proof.
  assert (Hbounded : exists delta,
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program negation_program) negation_facts 8%positive = Some delta).
  { vm_compute; eexists; reflexivity. }
  destruct Hbounded as [delta Hdelta].
  assert (Hstrat : exists st, RulesStratify.stratified (old_program negation_program) st).
  { eexists; apply RulesStratify.stratify_sound; vm_compute; reflexivity. }
  destruct (bounded_legacy_is_reference _ _ delta old_negation_wf Hstrat Hdelta)
    as [db [Hdb Hagree]].
  exists db, delta; auto.
Qed.

Example legacy_empty_total_reference :
  exists db delta,
    RulesSolve.solve_program (old_program empty_program) [] = Some db /\
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program empty_program) [] 8%positive = Some delta /\
    forall p ts, RulesSolve.db_holds (old_program empty_program) db p ts =
      RulesSolve.db_holds (old_program empty_program) delta p ts.
Proof.
  assert (Hwf : RulesSyntax.program_wf (old_program empty_program) []).
  { split; intros x Hbad; contradiction. }
  assert (Hstrat : exists st, RulesStratify.stratified (old_program empty_program) st).
  { eexists; apply RulesStratify.stratify_sound; vm_compute; reflexivity. }
  assert (Hbounded : exists delta,
    RulesDelta.delta_bounded_program RulesJoin.IndexedNested
      (old_program empty_program) [] 8%positive = Some delta).
  { vm_compute; eexists; reflexivity. }
  destruct Hbounded as [delta Hdelta].
  destruct (bounded_legacy_is_reference _ _ delta Hwf Hstrat Hdelta)
    as [db [Hdb Hagree]].
  exists db, delta; auto.
Qed.
