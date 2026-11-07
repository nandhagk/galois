(** * Weight extension and rooted path contracts

    These fixtures separate lawful ties, reconstructible routes and reachable cycles.
    For example, an unreachable self-loop permits an optimal result for an isolated entry.
    Builds on: GraphPathsSpec and GraphModelTest. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPathsSpec.
From Galois.Tests.Graph Require Import GraphModelTest.
Import List.ListNotations Cost.Notations.
Close Scope positive_scope.

Definition max_nat : Weight.t nat :=
  Weight.of_pure 0 Nat.add (fun a b => Nat.ltb b a).

Example max_nat_laws : Weight.laws max_nat.
Proof.
  constructor.
  - change (forall a b c : nat, a + b + c = a + (b + c)). intros. lia.
  - change (forall a : nat, 0 + a = a). reflexivity.
  - change (forall a : nat, a + 0 = a). intros. lia.
  - change (forall a : nat, (a <? a) = false). apply Nat.ltb_irrefl.
  - change (forall a b c : nat, (b <? a) = true -> (c <? b) = true -> (c <? a) = true).
    intros a b c Hab Hbc. apply Nat.ltb_lt in Hab, Hbc. apply Nat.ltb_lt. lia.
  - change (forall a b c : nat, (b <? a) = false -> (a <? b) = false ->
      (c <? b) = false -> (b <? c) = false ->
      (c <? a) = false /\ (a <? c) = false).
    intros a b c Hab Hba Hbc Hcb.
    apply Nat.ltb_ge in Hab, Hba, Hbc, Hcb.
    split; apply Nat.ltb_ge; lia.
  - change (forall a b c : nat, (b <? a) = true -> (c + b <? c + a) = true).
    intros a b c Hab. apply Nat.ltb_lt in Hab. apply Nat.ltb_lt. lia.
  - change (forall a b c : nat, (b <? a) = true -> (b + c <? a + c) = true).
    intros a b c Hab. apply Nat.ltb_lt in Hab. apply Nat.ltb_lt. lia.
  - change (forall a b c : nat, (b <? a) = false /\ (a <? b) = false ->
      (c + b <? c + a) = false /\ (c + a <? c + b) = false).
    intros a b c [Hab Hba]. apply Nat.ltb_ge in Hab, Hba.
    split; apply Nat.ltb_ge; lia.
  - change (forall a b c : nat, (b <? a) = false /\ (a <? b) = false ->
      (b + c <? a + c) = false /\ (a + c <? b + c) = false).
    intros a b c [Hab Hba]. apply Nat.ltb_ge in Hab, Hba.
    split; apply Nat.ltb_ge; lia.
Qed.

Example numeric_tie_extension :
  Weight.tied max_nat
    (Weight.plus max_nat (Weight.plus max_nat 1 1) 3)
    (Weight.plus max_nat (Weight.plus max_nat 2 0) 3).
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Counterfixture callbacks charge their list traversals rather than claiming primitive cost. *)
Fixpoint append_bits_c (xs ys : list bool) : Cost.t (list bool) :=
  match xs with
  | [] => Cost.ret ys
  | x :: rest =>
    Cost.step ;; let* zs := append_bits_c rest ys in Cost.ret (x :: zs)
  end.

Fixpoint bit_length_c (xs : list bool) : Cost.t nat :=
  match xs with
  | [] => Cost.ret 0
  | _ :: rest => Cost.step ;; let* n := bit_length_c rest in Cost.ret (S n)
  end.

Fixpoint lex_bits_c (xs ys : list bool) : Cost.t bool :=
  Cost.step ;;
  match xs, ys with
  | [], _ => Cost.ret false
  | _ :: _, [] => Cost.ret true
  | x :: rest, y :: other =>
    if Bool.eqb x y then lex_bits_c rest other else Cost.ret x
  end.

Definition split_better_c (xs ys : list bool) :=
  let* nx := bit_length_c xs in
  let* ny := bit_length_c ys in
  if Nat.eqb nx ny then
    match xs, ys with
    | [_], [_] => Cost.ret false
    | _, _ => lex_bits_c xs ys
    end
  else Cost.ret (Nat.ltb ny nx).

Definition split_weights : Weight.t (list bool) :=
  Weight.Make [] append_bits_c split_better_c.

Example distinct_singletons_tie : Weight.tied split_weights [false] [true].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example right_extension_splits_tie :
  Weight.better split_weights
    (Weight.plus split_weights [true] [false])
    (Weight.plus split_weights [false] [false]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example left_extension_splits_tie :
  Weight.better split_weights
    (Weight.plus split_weights [false] [true])
    (Weight.plus split_weights [false] [false]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example split_weight_laws_rejected : ~ Weight.laws split_weights.
Proof.
  intro Hlaws.
  pose proof (Weight.tie_preserved_right split_weights Hlaws [false] [true] [false]
    distinct_singletons_tie) as Htie.
  destruct Htie as [_ Hfalse]. vm_compute in Hfalse. discriminate.
Qed.

Definition unit_weight (_ : edge) := Cost.lift (fun _ => 1%N) (fun _ => 1%nat) tt.

Definition two_roots := fixture [1%positive; 2%positive]
  [1%positive; 2%positive] [(1%positive, 2%positive)].
Definition two_roots_p := Prepared.prepare positive_encoding two_roots.
Definition improved_best := Map.of_list positive_encoding [(1%positive, 0); (2%positive, 1)].

Example entry_improved_by_incoming_path :
  In 2%positive (Graph.entries two_roots) /\
  path two_roots 1%positive [(1%positive, 2%positive)] 2%positive /\
  Weight.path_weight max_nat unit_weight [(1%positive, 2%positive)] = 1 /\
  Weight.zero max_nat = 0.
Proof.
  split; [vm_compute; auto|]. split.
  - apply (@path_cons positive edge two_roots (1%positive, 2%positive)).
    + vm_compute. auto.
    + constructor.
  - vm_compute. split; reflexivity.
Qed.

Example improved_entry_without_via_rejected :
  ~ Dag.optimal two_roots_p max_nat unit_weight improved_best Map.empty.
Proof.
  intro Hoptimal.
  assert (Hbest : Map.get positive_encoding 2%positive improved_best = Some 1).
  { vm_compute. reflexivity. }
  pose proof (Dag.via_base two_roots_p max_nat unit_weight improved_best Map.empty
    Hoptimal 2%positive 1 Hbest (Map.get_empty positive_encoding 2%positive)) as Hbase.
  destruct Hbase as [Hfalse _]. vm_compute in Hfalse. discriminate.
Qed.

Definition isolated_cycle :=
  fixture [1%positive] [1%positive; 2%positive] [(2%positive, 2%positive)].
Definition isolated_p := Prepared.prepare positive_encoding isolated_cycle.
Definition isolated_best := Map.set positive_encoding 1%positive 0 Map.empty.

Example isolated_wf : graph_wf isolated_cycle.
Proof.
  constructor.
  - change (NoDup [1%positive; 2%positive]).
    repeat (apply NoDup_cons; [cbn; intuition discriminate|]). apply NoDup_nil.
  - vm_compute. intuition congruence.
  - intros v [s t] Hin. apply filter_In in Hin.
    destruct Hin as [_ Heq]. cbn in Heq. now apply Pos.eqb_eq in Heq.
  - intros v [s t] Hv Hin. apply filter_In in Hin.
    destruct Hin as [Hin _]. vm_compute in Hin |- *. intuition congruence.
Qed.

Example isolated_ready : Prepared.ready isolated_p.
Proof.
  apply Prepared.prepare_ready; [exact positive_encoding_laws|exact isolated_wf|].
  intro v. apply NoDup_filter.
  change (NoDup [(2%positive, 2%positive)]).
  apply NoDup_cons; [cbn; tauto|apply NoDup_nil].
Qed.

Local Lemma isolated_reachable v : reachable isolated_cycle v <-> v = 1%positive.
Proof.
  split.
  - intro Hreach. induction Hreach as [v Hin|[s t] Hreach IH Hedge].
    + vm_compute in Hin. intuition congruence.
    + change (s = 1%positive) in IH. subst s.
      vm_compute in Hedge. contradiction.
  - intros ->. apply reachable_entry. vm_compute. auto.
Qed.

Local Lemma isolated_path s es n :
  path isolated_cycle s es n -> s = 1%positive -> es = [] /\ n = 1%positive.
Proof.
  intro Hpath. induction Hpath as [v|e es z Hedge Hpath IH]; intro Hstart.
  - auto.
  - rewrite Hstart in Hedge. change (In e []) in Hedge. contradiction.
Qed.

Local Lemma isolated_id_one n : Prepared.id_of isolated_p n = Some 1%positive ->
  n = 1%positive.
Proof.
  intro Hid.
  pose proof (Prepared.name_of_id_of isolated_p n 1%positive
    (proj2 (proj2 isolated_ready)) Hid) as Hname.
  assert (Hone : Prepared.name_of isolated_p 1%positive = Some 1%positive).
  { vm_compute. reflexivity. }
  congruence.
Qed.

Local Lemma isolated_best_lookup i value :
  Map.get positive_encoding i isolated_best = Some value <->
    i = 1%positive /\ value = 0.
Proof.
  unfold isolated_best. rewrite Map.get_set by apply Map.wf_empty.
  rewrite Map.get_empty.
  destruct (eqb_spec positive_encoding positive_encoding_laws i 1%positive) as [->|Hne].
  - split; [intro Hvalue; injection Hvalue as <-; auto|intros [_ ->]; reflexivity].
  - split; [discriminate|intros [Heq _]; contradiction].
Qed.

Example isolated_optimal : Dag.optimal isolated_p max_nat unit_weight isolated_best Map.empty.
Proof.
  constructor.
  - apply Map.wf_set, Map.wf_empty.
  - apply Map.wf_empty.
  - intros n i Hid.
    change (reachable isolated_cycle n <->
      exists value, Map.get positive_encoding i isolated_best = Some value).
    rewrite isolated_reachable. split.
    + intros ->.
      assert (Hi : i = 1%positive) by (vm_compute in Hid; congruence).
      subst i. exists 0. vm_compute. reflexivity.
    + intros [value Hget]. apply isolated_best_lookup in Hget.
      destruct Hget as [-> _]. now apply isolated_id_one.
  - intros i value Hget. apply isolated_best_lookup in Hget.
    destruct Hget as [-> _]. exists 1%positive. split.
    + vm_compute. reflexivity.
    + apply isolated_reachable. reflexivity.
  - intros n i value Hid Hget. apply isolated_best_lookup in Hget.
    destruct Hget as [-> ->]. apply isolated_id_one in Hid. subst n.
    exists 1%positive, []. split; [vm_compute; auto|].
    split; [constructor|vm_compute; reflexivity].
  - intros n i value s es Hid Hget Hentry Hpath.
    apply isolated_best_lookup in Hget. destruct Hget as [_ ->].
    change (In s [1%positive]) in Hentry. destruct Hentry as [<-|Hfalse]; [|contradiction].
    apply isolated_path in Hpath; [|reflexivity]. destruct Hpath as [-> _].
    vm_compute. reflexivity.
  - intros i e Hget. rewrite Map.get_empty in Hget. discriminate.
  - intros n i Hid Hreach Hnonentry.
    apply isolated_reachable in Hreach. subst n.
    exfalso. apply Hnonentry. vm_compute. auto.
  - intros i value Hget Hmissing. apply isolated_best_lookup in Hget.
    destruct Hget as [-> ->]. split; [reflexivity|].
    exists 1%positive. split; vm_compute; auto.
Qed.

Example isolated_allows_optimal :
  Dag.spec isolated_p max_nat unit_weight (Dag.Optimal isolated_best Map.empty).
Proof.
  split; [|exact isolated_optimal].
  intros v es Hreach Hpath. apply isolated_reachable in Hreach.
  apply (isolated_path v es v Hpath) in Hreach. tauto.
Qed.

Example isolated_cycle_not_rooted_witness :
  ~ Dag.cyclic_witness isolated_p (2%positive, 2%positive).
Proof.
  intros [Hreach _]. apply isolated_reachable in Hreach. discriminate.
Qed.

Example isolated_forbids_cyclic :
  ~ Dag.spec isolated_p max_nat unit_weight (@Dag.Cyclic nat edge (2%positive, 2%positive)).
Proof.
  exact isolated_cycle_not_rooted_witness.
Qed.

Example reachable_loop_allows_cyclic :
  Dag.spec (Prepared.prepare positive_encoding self_loop) max_nat unit_weight
    (@Dag.Cyclic nat edge (1%positive, 1%positive)).
Proof.
  split; [apply reachable_entry; vm_compute; auto|].
  split; [vm_compute; auto|].
  split; [vm_compute; auto|].
  exists []. constructor.
Qed.

Example isolated_has_global_cycle : ~ acyclic isolated_cycle.
Proof.
  intro Hacyclic.
  assert (Hpath : path isolated_cycle 2%positive [(2%positive, 2%positive)] 2%positive).
  { apply (@path_cons positive edge isolated_cycle (2%positive, 2%positive)).
    - vm_compute. auto.
    - constructor. }
  specialize (Hacyclic 2%positive [(2%positive, 2%positive)]
    (or_intror (or_introl eq_refl)) Hpath). discriminate.
Qed.
