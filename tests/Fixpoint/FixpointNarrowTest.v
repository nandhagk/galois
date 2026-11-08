(** * Simultaneous narrowing clients

    Actual narrowing passes distinguish frozen reads, accepted decrease and rejected candidates.
    For example, lowering a negated read invalidates a previously safe output.
    Builds on: FixpointNarrow, boolean controls and a test-local interval lattice. *)

From Stdlib Require Import List Bool Arith NArith ZArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointCheck
  FixpointAnalysis FixpointSolver FixpointNarrow FixpointIndexCost FixpointTotalCost
  FixpointNarrowCost.
Import List.ListNotations Cost.Notations.
Local Close Scope N_scope.

Module NarrowTest.

Definition lat : lattice bool :=
  of_pure implb false orb orb (fun _ b => b).

Definition accepted : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then
      Query.Side 2 false (Query.Ret false) else Query.Ask 0 (fun b => Cost.ret (Query.Ret b)))).

Definition rejected : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then
      Query.Ask 1 (fun b => Cost.ret (Query.Ret (negb b))) else Query.Ret false)).

Definition declarations (S : System.t nat nat bool) : System.static S :=
  System.Static (fun _ => Cost.ret [0; 1]) (fun _ => Cost.ret [2]).

Definition analysis S : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding lat S (declarations S) (Policy.flat nat).

Definition old : assignment nat bool :=
  Map.of_list nat_encoding [(0, true); (1, true); (2, true); (99, true)].

Definition observe m := map (lookup nat_encoding lat m) [0; 1; 2; 99; 100].

Example simultaneous_old_reads :
  observe (Narrow.pass (analysis accepted) old) = [false; true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example two_checked_passes :
  observe (Narrow.checked (analysis accepted) 2 old) = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example broken_candidate_is_discarded :
  check_post lat rejected (lookup nat_encoding lat old) = true /\
  check_post lat rejected (lookup nat_encoding lat (Narrow.pass (analysis rejected) old)) =
    false /\
  Narrow.checked (analysis rejected) 1 old = old.
Proof.
  vm_compute; auto.
Qed.

Example zero_rounds : Narrow.checked (analysis accepted) 0 old = old.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty : System.t nat nat bool :=
  System.Make [] (fun c => Cost.ret c) (fun _ => Cost.ret (Query.Ret false)).

Example empty_keeps_unrelated : Narrow.pass (analysis empty) old = old.
Proof.
  vm_compute; reflexivity.
Qed.

(** This candidate producer checks its output, so its soundness holds for arbitrary analyses. *)
Definition produce_c (a : Analysis.t nat nat bool) (_ : positive) :
    Cost.t (Outcome.t nat bool (assignment nat bool)) :=
  let* safe := check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) old) in
  Cost.ret (if safe then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).

Definition producer : Solver.t nat nat bool := Solver.Make produce_c.

Theorem producer_sound a fuel m :
  Analysis.laws a -> Solver.run producer a fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros _ Hrun.
  assert (Heq : Solver.run producer a fuel =
    if check_post (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) old)
    then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).
  { assert (Hobserve : Solver.run producer a fuel = Cost.value (produce_c a fuel))
      by reflexivity.
    rewrite Hobserve.
    unfold produce_c; rewrite Cost.value_bind.
    rewrite (check_post_c_spec _ _ _ _) by reflexivity; reflexivity. }
  rewrite Heq in Hrun; destruct (check_post _ _ _) eqn:Hcheck; [|discriminate].
  injection Hrun as <-; apply check_post_sound, Hcheck.
Qed.

(** Exhaustion propagates without narrowing an unchecked assignment. *)
Example wrapper_exhaustion :
  Solver.run (Narrow.wrap (Solver.Make (fun _ _ => Cost.ret (Outcome.OutOfFuel old))))
    (analysis accepted) 1%positive = Outcome.OutOfFuel old.
Proof.
  vm_compute; reflexivity.
Qed.

(** Underlying rejection retains its original reason. *)
Example wrapper_rejection :
  Solver.run (Narrow.wrap (Solver.Make
    (fun _ _ => Cost.ret (Outcome.Rejected Reason.Bad_plan))))
    (analysis accepted) 1%positive = Outcome.Rejected Reason.Bad_plan.
Proof.
  vm_compute; reflexivity.
Qed.

(** Importing the wrapper's soundness theorem discharges its substantive producer premise. *)
Theorem wrapper_client a fuel m :
  Analysis.laws a -> Solver.run (Narrow.wrap producer) a fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  apply Narrow.narrow_wrap_sound, producer_sound.
Qed.

Definition policy : Policy.t nat :=
  Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret false) 0 2.

Definition wrapping S : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding lat S (declarations S) policy.

Example wrapper_lowers :
  match Solver.run (Narrow.wrap producer) (wrapping accepted) 1%positive with
  | Outcome.Solved m => observe m
  | _ => []
  end = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition wrapping_one S : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding lat S (declarations S)
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret false) 0 1).

Example wrapper_discards_breaking_candidate :
  Solver.run (Narrow.wrap producer) (wrapping_one rejected) 1%positive = Outcome.Solved old.
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_lat : lattice bool :=
  {| leb_c := fun a b => Cost.step ;; leb_c lat a b;
     join_c := fun a b => Cost.step ;; join_c lat a b;
     widen_c := widen_c lat;
     narrow_c := fun a b => Cost.step ;; narrow_c lat a b;
     bot := false |}.

Definition charged : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding charged_lat accepted (declarations accepted) policy.

Example callbacks_retain_values :
  Narrow.pass charged old = Narrow.pass (wrapping accepted) old.
Proof.
  vm_compute; reflexivity.
Qed.

Example callbacks_add_ticks :
  (Cost.ticks (Narrow.pass_c (wrapping accepted) old) <
    Cost.ticks (Narrow.pass_c charged old))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition metadata_budget : SystemIndexCost.Budget.t :=
  SystemIndexCost.Budget.Make 10 10 0 0 0 2 2.

Definition budget : TotalCost.Budget.t :=
  TotalCost.Budget.Make metadata_budget 10 10 1 0 2 0 2.

(** The custom second-argument narrowing satisfies the weak lattice laws. *)
Theorem lattice_laws_client : lattice_laws lat.
Proof.
  constructor; intros; repeat match goal with
  | x : bool |- _ => destruct x
  end; vm_compute in *; congruence.
Qed.

(** The accepted example's conservative metadata covers all actual reads and sides. *)
Theorem laws_client : Analysis.laws (wrapping accepted).
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact lattice_laws_client.
  - constructor; intros c s x Hin; destruct c; vm_compute in *; intuition congruence.
Qed.

(** The actual wrapped result instantiates soundness with every law and run premise discharged. *)
Theorem sound_client :
  post_solution lat accepted
    (lookup nat_encoding lat (Narrow.checked (wrapping accepted) 2 old)).
Proof.
  apply (wrapper_client (wrapping accepted) 1%positive
    (Narrow.checked (wrapping accepted) 2 old) laws_client).
  vm_compute; reflexivity.
Qed.

(** The fixture's query syntax is public without reducing the shared evaluator. *)
Local Lemma rhs_equation c :
  System.rhs (Analysis.system (wrapping accepted)) c =
    if Nat.eqb c 0 then Query.Side 2 false (Query.Ret false)
    else Query.Ask 0 (fun b => Cost.ret (Query.Ret b)).
Proof.
  reflexivity.
Qed.

Local Lemma sides_equation c s :
  Query.sides (System.rhs (Analysis.system (wrapping accepted)) c) s =
    if Nat.eqb c 0 then [(2, false)] else [].
Proof.
  assert (Hrun : Query.run (System.rhs (Analysis.system (wrapping accepted)) c) s =
    if Nat.eqb c 0 then Query.Trace false [] [(2, false)]
    else Query.Trace (s 0) [0] []).
  { rewrite rhs_equation; destruct (Nat.eqb c 0);
      rewrite !Query.run_equation, ?Cost.value_ret, ?Query.run_equation; reflexivity. }
  rewrite Query.run_spec in Hrun.
  apply (f_equal (@Query.side_log nat bool)) in Hrun.
  destruct (Nat.eqb c 0); cbn [Query.side_log] in Hrun; exact Hrun.
Qed.

(** The importing pass-cost model discharges all primitive and selected-query duties. *)
Theorem cost_model : TotalCost.model (wrapping accepted) budget.
Proof.
  constructor.
  - constructor.
    + intros c Hc x Hx; vm_compute in Hc.
      destruct Hc as [<-|[<-|Hbad]]; try contradiction;
        vm_compute in Hx; intuition subst; vm_compute; congruence.
    + intros c Hc; vm_compute; repeat split; congruence.
    + intros c Hc; vm_compute in Hc.
      destruct Hc as [<-|[<-|Hbad]]; try contradiction; vm_compute; split; lia.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction; vm_compute; split; congruence.
  - intros [] []; vm_compute; split; congruence.
  - intros c Hc; vm_compute; congruence.
  - intros c s Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|Hbad]]; try contradiction.
    + exists 2%nat; split; [vm_compute; lia|].
      rewrite rhs_equation; apply Query.within_side, Query.within_ret.
    + exists 2%nat; split; [vm_compute; lia|].
      rewrite rhs_equation; apply Query.within_ask.
      * rewrite Cost.ticks_ret; vm_compute; congruence.
      * rewrite Cost.value_ret; apply Query.within_ret.
  - intros c s _; rewrite Eval.outputs_spec, sides_equation.
    destruct (Nat.eqb c 0); cbn [fst length budget TotalCost.Budget.outputs]; lia.
Qed.

(** Narrowing callback charges are discharged independently of any complete pass cost. *)
Theorem narrowing_budget x y : (Cost.ticks (narrow_c lat x y) <= 1)%N.
Proof.
  vm_compute; congruence.
Qed.

(** The numeric client composes actual passes, unary conversion and the independent full checker. *)
Theorem numeric_checked_client :
  (Cost.ticks (Narrow.checked_c (wrapping accepted) 2 old) <=
    2 + (NarrowCost.pass_budget budget 1 2 4 + 2) * 3 +
    2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c 2))) +
    2 * (1 + TotalCost.Budget.evaluation budget +
      2 * (3 + TotalCost.Budget.key budget + TotalCost.Budget.lattice_ticks budget)))%N.
Proof.
  exact (NarrowCost.narrow_checked_cost (wrapping accepted) laws_client budget cost_model
    1%N narrowing_budget 2%nat old).
Qed.

(** Arbitrarily many requested passes instantiate the checked-narrowing numeric family theorem. *)
Theorem bigO_client :
  bigO (fun n : nat =>
    (N.of_nat n + (NarrowCost.pass_budget budget 1 2 4 + 2) * (N.of_nat n + 1) +
      2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c n))) +
      2 * (1 + TotalCost.Budget.evaluation budget +
        2 * (3 + TotalCost.Budget.key budget + TotalCost.Budget.lattice_ticks budget)))%N)
    (fun n => Cost.ticks (Narrow.checked_c (wrapping accepted) n old)).
Proof.
  exact (NarrowCost.narrow_bigO (fun _ : nat => wrapping accepted)
    (fun _ => laws_client) (fun _ => budget) (fun _ => cost_model) (fun _ => 1%N)
    (fun _ => narrowing_budget) (fun n => n) (fun _ => old)).
Qed.

(** The public wrapper retains its solver cost and adds the proved narrowing budget. *)
Theorem numeric_wrap_client :
  (Cost.ticks (Solver.run_c (Narrow.wrap producer) (wrapping accepted) 1%positive) <=
    1 + Cost.ticks (Solver.run_c producer (wrapping accepted) 1%positive) +
    2 + (NarrowCost.pass_budget budget 1 2 4 + 2) * 3 +
    2 * N.pos (Pos.size (Cost.value (Narrow.fuel_c 2))) +
    2 * (1 + TotalCost.Budget.evaluation budget +
      2 * (3 + TotalCost.Budget.key budget + TotalCost.Budget.lattice_ticks budget)))%N.
Proof.
  pose proof (NarrowCost.narrow_wrap_cost (wrapping accepted) laws_client budget cost_model
    1%N narrowing_budget producer 1%positive) as Hcost.
  cbn zeta in Hcost; exact Hcost.
Qed.

End NarrowTest.
Import NarrowTest.

Module NarrowIntervalTest.

(** None is bottom and endpoint pairs describe closed integer intervals. *)
Definition interval := option (Z * Z).

Definition span (lower upper : Z) : interval := Some (lower, upper).

Definition below (a b : interval) :=
  match a, b with
  | None, _ => true
  | Some _, None => false
  | Some (lo, hi), Some (lo', hi') => Z.leb lo' lo && Z.leb hi hi'
  end.

Definition hull (a b : interval) : interval :=
  match a, b with
  | None, other => other
  | other, None => other
  | Some (lo, hi), Some (lo', hi') => span (Z.min lo lo') (Z.max hi hi')
  end.

Definition shift (a : interval) : interval :=
  match a with
  | None => None
  | Some (lo, hi) => span (Z.add lo 1%Z) (Z.add hi 1%Z)
  end.

Definition contains (a : interval) (z : Z) :=
  match a with
  | None => false
  | Some (lo, hi) => Z.leb lo z && Z.leb z hi
  end.

Definition lat : lattice interval := of_pure below None hull hull (fun _ next => next).

(** The second row shifts the old interval read from the first row. *)
Definition system : System.t nat nat interval :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then Query.Ret (span 0%Z 4%Z)
      else Query.Ask 0 (fun value => Cost.ret (Query.Ret (shift value))))).

Definition static : System.static system :=
  System.Static (fun c => Cost.ret (if Nat.eqb c 0 then [] else [0]))
    (fun _ => Cost.ret []).

Definition analysis : Analysis.t nat nat interval :=
  Analysis.Make nat_encoding nat_encoding lat system static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret false) 0 2).

Definition old : assignment nat interval :=
  Map.of_list nat_encoding
    [(0, span (-10)%Z 10%Z); (1, span (-20)%Z 20%Z); (99, span (-7)%Z 9%Z)].

Definition observe m := map (lookup nat_encoding lat m) [0; 1; 99].

(** A checked coarse candidate supplies input; the actual wrapper performs all narrowing work. *)
Definition coarse_c (a : Analysis.t nat nat interval) (_ : positive) :
    Cost.t (Outcome.t nat interval (assignment nat interval)) :=
  let* safe := check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) old) in
  Cost.ret (if safe then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).

Definition coarse_source : Solver.t nat nat interval := Solver.Make coarse_c.

Definition wrapped := Solver.run (Narrow.wrap coarse_source) analysis 1%positive.

Example coarse_input_is_post :
  check_post lat system (lookup nat_encoding lat old) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example first_pass_reads_old_endpoints :
  observe (Narrow.pass analysis old) =
    [span 0%Z 4%Z; span (-9)%Z 11%Z; span (-7)%Z 9%Z].
Proof.
  vm_compute; reflexivity.
Qed.

Example first_pass_independent_full_check :
  check_post lat system (lookup nat_encoding lat (Narrow.pass analysis old)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_endpoint_decrease :
  match wrapped with
  | Outcome.Solved m => Some (observe m)
  | _ => None
  end = Some [span 0%Z 4%Z; span 1%Z 5%Z; span (-7)%Z 9%Z].
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_strict_decrease_and_values :
  match wrapped with
  | Outcome.Solved m =>
    let value := lookup nat_encoding lat m 1 in
    [below value (lookup nat_encoding lat old 1);
     below (lookup nat_encoding lat old 1) value;
     contains value 0%Z; contains value 1%Z; contains value 5%Z; contains value 6%Z]
  | _ => []
  end = [true; false; false; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_independent_full_check :
  match wrapped with
  | Outcome.Solved m => check_post lat system (lookup nat_encoding lat m)
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

End NarrowIntervalTest.
Import NarrowIntervalTest.
