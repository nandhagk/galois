(** * Partial semantics and guards

    Evaluation stops at an undefined child, and guards read the supplied facts.
    For example, a guard can reject a fact even when a rule has no missing holes.
    Builds on: EgraphRules. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Egraph Require Import EgraphSyntax EgraphRules.
Import List.ListNotations.
Import Cost.Notations.

Definition sample_sem : EggSem.t nat bool nat :=
  EggSem.Make nat bool nat (fun v => if v then Some 4 else None)
    (fun _ args => Some (length args)).

Definition sample_rule : EggRule.t nat bool bool bool bool :=
  EggRule.Make nat bool bool bool bool bool_encoding [true]
    (fun h => Cost.lift (fun _ => 1%N) (fun h : bool => if h then Some true else None) h)
    (EggPattern.Hole true true) (EggPattern.Hole true true)
    (fun facts => Cost.step ;; facts true).

Example denote_defined :
  EggSem.denote sample_sem (EggTerm.App true 0 [EggTerm.Var true true]) = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example denote_undefined :
  EggSem.denote sample_sem (EggTerm.App true 0 [EggTerm.Var true false]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example guard_rejects :
  EggRule.guard sample_rule (fun _ => false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example guard_accepts :
  EggRule.guard sample_rule (fun _ => true) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The single-read fixture satisfies value agreement for every costed fact lookup. *)
Theorem sample_guard_laws : EggRule.guard_laws sample_rule.
Proof.
  constructor; intro phi; reflexivity.
Qed.

Definition repeated_rule : EggRule.t nat bool bool bool bool :=
  EggRule.Make nat bool bool bool bool bool_encoding [true]
    (fun h => Cost.ret (if h then Some true else None))
    (EggPattern.Hole true true) (EggPattern.Hole true true)
    (fun facts =>
      Cost.step ;;
      let* first := facts true in
      Cost.step ;;
      let* second := facts true in
      Cost.ret (andb first second)).

(** Reading the same hole repeatedly still agrees with the pure guard on returned values. *)
Theorem repeated_guard_laws : EggRule.guard_laws repeated_rule.
Proof.
  constructor; intro phi; reflexivity.
Qed.

Definition expensive_facts (b : bool) (_ : bool) : Cost.t bool :=
  Cost.tick 7 ;; Cost.ret b.

Example expensive_guard_read_retains_lookup_charge :
  (Cost.value (EggRule.guard_c sample_rule (expensive_facts true)),
    Cost.ticks (EggRule.guard_c sample_rule (expensive_facts true))) = (true, 8%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_guard_reads_retain_both_lookup_charges :
  (Cost.value (EggRule.guard_c repeated_rule (expensive_facts true)),
    Cost.ticks (EggRule.guard_c repeated_rule (expensive_facts true))) = (true, 16%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_rejecting_guard_still_charges_both_reads :
  (Cost.value (EggRule.guard_c repeated_rule (expensive_facts false)),
    Cost.ticks (EggRule.guard_c repeated_rule (expensive_facts false))) = (false, 16%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** The repeated guard retains each callee's cost and one invocation tick for each read. *)
Theorem repeated_guard_cost (phi : bool -> Cost.t bool) :
  Cost.ticks (EggRule.guard_c repeated_rule phi) =
    (1 + Cost.ticks (phi true) + 1 + Cost.ticks (phi true))%N.
Proof.
  unfold repeated_rule; cbn [EggRule.guard_c].
  rewrite !Cost.ticks_bind, !Cost.ticks_step, Cost.ticks_ret.
  rewrite N.add_0_r, !N.add_assoc; reflexivity.
Qed.

Definition fact_table := Map.set bool_encoding true true Map.empty.

Definition mapped_facts h :=
  Cost.map (fun result => match result with Some b => b | None => false end)
    (Map.get_c bool_encoding h fact_table).

Example map_lookup_charge_flows_through_guard :
  (Cost.ticks (mapped_facts true), Cost.ticks (EggRule.guard_c sample_rule mapped_facts),
    Cost.ticks (EggRule.guard_c repeated_rule mapped_facts)) = (4%N, 5%N, 10%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** A runtime client uses the separate guard law to obtain the semantic pure-guard premise. *)
Theorem runtime_guard_client (phi : bool -> Cost.t bool) :
  Cost.value (EggRule.guard_c sample_rule phi) = true ->
  EggRule.guard sample_rule (fun h => Cost.value (phi h)) = true.
Proof.
  intro Haccepted; rewrite <- (EggRule.guard_agrees sample_rule sample_guard_laws phi).
  exact Haccepted.
Qed.
