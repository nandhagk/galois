(** * Independent primitive budgets for engine composition

    Engine callback prices are derived from level, lower-environment and predicate-key budgets.
    For example, a tagged frontier read pays a predicate lookup without scanning stored rows.
    Builds on: DatalogSemiNaiveCost and the complete Join preparation and firing contracts. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogCost DatalogJoin DatalogJoinProof DatalogJoinCost
  DatalogJoinPrepareCost DatalogJoinFireCost DatalogSemiNaive DatalogSemiNaiveCost.
Import List.ListNotations SemiNaive SemiNaiveCost.
Local Open Scope N_scope.

Module SemiNaiveBudget.

(** Budgets describe primitive data, callbacks and key costs independently of engine outcomes. *)
Record budget : Type := Budget {
  args_bound : nat;
  variables_bound : nat;
  binding_bound : nat;
  rows_bound : N;
  component_bound : N;
  level_bound : N;
  lower_bound : N;
  predicate_encode : N;
  predicate_width : N;
  tuple_encode : N;
  tuple_width : N;
  ground_encode : N;
  ground_width : N
}.

(** Primitive input duties contain no engine-helper cost or semantic result. *)
Definition input {P} (prog : program P) (st : stratification P)
    (lower : P -> Cost.t relation) b p :=
  Cost.ticks (level_c st p) <= level_bound b /\
  Cost.ticks (lower p) <= lower_bound b /\
  key_budget (penc prog) (predicate_encode b) (predicate_width b) p.

(** This coefficient covers both branches of a current or tagged environment read. *)
Definition environment_charge b :=
  3 + level_bound b + lower_bound b + predicate_encode b + predicate_width b.

Lemma current_cost {P} (prog : program P) st lower b k db p :
  input prog st lower b p ->
  Cost.ticks (current_c prog st k lower db p) <= environment_charge b.
Proof.
  intros [Hlevel [Hlower Hkey]].
  pose proof (rel_of_cost prog db p _ _ Hkey) as Hlookup.
  unfold current_c; repeat rewrite Cost.ticks_bind; rewrite !Cost.ticks_step.
  fold (level st p); destruct (Nat.eqb (level st p) k);
    unfold environment_charge; lia.
Qed.

(** Tagged callback prices follow from primitive inputs at the underlying source predicate. *)
Theorem tagged_cost {P} (prog : program P) st lower b k acc front q :
  input prog st lower b (fst q) ->
  Cost.ticks (tagged_c prog st k lower acc front q) <= environment_charge b.
Proof.
  intro Hinput; unfold tagged_c; destruct (snd q).
  - pose proof (rel_of_cost prog front (fst q) _ _ (proj2 (proj2 Hinput))).
    unfold environment_charge; lia.
  - apply current_cost, Hinput.
Qed.

(** Erased callback charges isolate preparation's row, mask, length and key duties. *)
Definition preparation_data {P} bound ps (env : P -> Cost.t relation) b :=
  JoinPrepareCost.prepare_primitives bound ps (fun p => Cost.ret (Cost.value (env p)))
    (args_bound b) (variables_bound b) (rows_bound b) 0
    (tuple_width b) (tuple_encode b) (tuple_width b).

Lemma preparation_lift {P} bound ps (env : P -> Cost.t relation) b c :
  preparation_data bound ps env b ->
  (forall atom, In atom ps -> Cost.ticks (env (pred atom)) <= c) ->
  JoinPrepareCost.prepare_primitives bound ps env
    (args_bound b) (variables_bound b) (rows_bound b) c
    (tuple_width b) (tuple_encode b) (tuple_width b).
Proof.
  revert bound; induction ps as [|atom rest IH]; intros bound Hdata Henv; [exact I |].
  destruct Hdata as [Ha [Hb [_ [Hr [Hw [Hkey Htail]]]]]].
  split; [exact Ha | split; [exact Hb | split]].
  - apply Henv; now left.
  - split; [exact Hr | split; [exact Hw | split; [exact Hkey |]]].
    apply IH; [exact Htail | intros x Hx; apply Henv; now right].
Qed.

(** Erased callback charges isolate firing's reached binding, probe and head-key duties. *)
Definition firing_data {P} (r : rule P) (env : P -> Cost.t relation) plan b :=
  JoinFireCost.fire_primitives r (fun p => Cost.ret (Cost.value (env p))) plan
    (args_bound b) (binding_bound b) (component_bound b) 0 (tuple_encode b) (tuple_width b).

Lemma firing_lift {P} (r : rule P) env plan b c :
  firing_data r env plan b ->
  (forall atom, In (LNeg atom) (body r) -> Cost.ticks (env (pred atom)) <= c) ->
  JoinFireCost.fire_primitives r env plan
    (args_bound b) (binding_bound b) (component_bound b) c (tuple_encode b) (tuple_width b).
Proof.
  intros [Hrun [Hhead Hbindings]] Henv; split; [exact Hrun | split; [exact Hhead |]].
  intros binding Hbinding.
  destruct (Hbindings binding Hbinding) as [Hlength [Hnegative Hkey]].
  split; [exact Hlength | split; [|exact Hkey]].
  intros atom Hatom; destruct (Hnegative atom Hatom) as [Ha [_ Hkeys]].
  split; [exact Ha | split; [apply Henv, Hatom | exact Hkeys]].
Qed.

(** Firing head keys inherit their primitive duties from the actual emitted binding. *)
Theorem firing_keys {P} (r : rule P) env plan b row :
  firing_data r env plan b -> member row (Join.fire r env plan) = true ->
  key_budget tuple_encoding (tuple_encode b) (tuple_width b) row.
Proof.
  intros [_ [_ Hbindings]] Hrow.
  apply JoinProof.fire_members in Hrow as [binding [Hin [_ ->]]].
  exact (proj2 (proj2 (Hbindings binding Hin))).
Qed.

(** Output cardinality counts distinct emitted heads and is bounded by actual Join work. *)
Theorem firing_size {P} (r : rule P) env plan :
  N.of_nat (FinSet.size (set_raw (Join.fire r env plan))) <= Join.work plan + 1.
Proof.
  assert (Hlength : (FinSet.size (set_raw (Join.fire r env plan)) <=
    length (Join.run plan))%nat).
  { rewrite FinSet.size_elements.
    rewrite <- (length_map (fun binding =>
      map (inst (binding_value binding)) (args (head r))) (Join.run plan)).
    apply NoDup_incl_length.
    - apply (FinSet.elements_nodup tuple_encoding), (proj2_sig (Join.fire r env plan)).
    - intros row Hrow.
      apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
        (proj2_sig (Join.fire r env plan))) in Hrow.
      apply JoinProof.fire_members in Hrow as [binding [Hin [_ ->]]].
      apply in_map_iff; exists binding; split; [reflexivity | exact Hin]. }
  pose proof (JoinFireCost.join_run_length plan); apply nat_N_le in Hlength; lia.
Qed.

End SemiNaiveBudget.
Import SemiNaiveBudget.
