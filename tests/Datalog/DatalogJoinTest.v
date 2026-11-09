(** * Prepared nested join computations and importing clients

    The examples run the indexed plan, incremental insertion and its public numerical contract.
    For example, a triangle requires a shared value in all three relation occurrences.
    Builds on: DatalogJoin, DatalogJoinProof and DatalogJoinCost. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire
  DatalogJoin DatalogJoinProof DatalogJoinCost DatalogJoinUpdateCost.
Import List.ListNotations Join JoinProof JoinCost JoinUpdateCost.

Definition join_program : program nat := Program nat_encoding (fun _ => Cost.ret 2) [].

Definition join_facts : list (ground_atom nat) :=
  [(0%nat, [2; 3]); (0%nat, [2; 4]); (0%nat, [3; 3]); (1%nat, [3; 5]);
   (1%nat, [4; 6]); (2%nat, [2; 5]); (2%nat, [7; 6])]%positive.

Definition join_env p := Cost.lift (fun _ => 7%N)
  (fun _ => set_of_list tuple_encoding
    (map snd (filter (fun f => Nat.eqb p (fst f)) join_facts))) tt.

Definition shared_atoms : list (atom nat) :=
  [Atom 0 [TVar 0; TVar 1]; Atom 1 [TVar 1; TVar 2]].
Definition triangle_atoms := shared_atoms ++ [Atom 2 [TVar 0; TVar 2]].

Definition observe_join ps vars :=
  map (fun b => map (binding_value b) vars) (run (prepare join_program ps join_env)).

Example shared_two_atoms :
  observe_join shared_atoms [0; 1; 2] = [[2; 4; 6]; [2; 3; 5]; [3; 3; 5]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example triangle_three_atoms :
  observe_join triangle_atoms [0; 1; 2] = [[2; 3; 5]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example constant_selection :
  observe_join [Atom 0 [TVar 0; TConst 4%positive]] [0] = [[2]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_variable_rejects :
  observe_join [Atom 0 [TVar 0; TVar 0]] [0] = [[3]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_relation :
  observe_join [Atom 8 [TVar 0; TVar 1]] [0; 1] = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_body : run (prepare join_program [] join_env) = [[]].
Proof.
  vm_compute; reflexivity.
Qed.

Example nullary_join :
  run (prepare join_program [Atom 9 []]
    (fun _ => Cost.ret (set_of_list tuple_encoding [[]]))) = [[]].
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_rows_reject :
  run (prepare join_program [Atom 0 [TVar 0; TVar 1]]
    (fun _ => Cost.ret (set_of_list tuple_encoding
      [[2%positive]; [2%positive; 3%positive; 4%positive]]))) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Definition negative_rule : rule nat :=
  Rule (Atom 3 [TVar 0])
    [LPos (Atom 0 [TVar 0; TVar 1]); LNeg (Atom 2 [TVar 0; TConst 5%positive])].

Example negative_filter :
  let plan := prepare join_program (positive_atoms (body negative_rule)) join_env in
  FinSet.elements (set_raw (fire negative_rule join_env plan)) = [[3]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

(** Firing uses the landed exactness theorem after the indexed plan establishes its duties. *)
Example semantic_fire_contract ts :
  member ts
    (fire negative_rule join_env
      (prepare join_program (positive_atoms (body negative_rule)) join_env)) =
    member ts (fire_rule join_program negative_rule join_env).
Proof.
  apply join_fire_agrees, prepare_ready.
Qed.

Example incremental_insert :
  let plan := prepare join_program [Atom 0 [TVar 0; TVar 1]] join_env in
  let updated := insert_rows (fun _ => Cost.ret false)
    (fun _ => Cost.ret [[8%positive; 9%positive]]) plan in
  map (fun b => map (binding_value b) [0; 1]) (run updated) =
    [[8; 9]; [2; 4]; [2; 3]; [3; 3]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example frontier_reset :
  let plan := prepare join_program [Atom 0 [TVar 0; TVar 1]] join_env in
  let updated := insert_rows (fun _ => Cost.ret true)
    (fun _ => Cost.ret [[8%positive; 9%positive]]) plan in
  map (fun b => map (binding_value b) [0; 1]) (run updated) = [[8; 9]]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_insert_retains_occurrences :
  let plan := prepare join_program [Atom 0 [TVar 0; TVar 1]]
    (fun _ => Cost.ret (set_of_list tuple_encoding [])) in
  let updated := insert_rows (fun _ => Cost.ret false)
    (fun _ => Cost.ret [[2%positive; 3%positive]; [2%positive; 3%positive]]) plan in
  length (run updated) = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example work_small_inputs :
  (work (prepare join_program [] join_env),
    work (prepare join_program shared_atoms join_env),
    work (prepare join_program triangle_atoms join_env)) = (0, 12, 17)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example nonunit_environment_preparation :
  Cost.ticks (prepare_c join_program shared_atoms join_env) =
    (14 + Cost.ticks (prepare_c join_program shared_atoms
      (fun p => Cost.ret (Cost.value (join_env p)))))%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** A nonempty importing client discharges all lengths, encoding and component-width duties. *)
Example numeric_join_contract :
  let plan := prepare join_program [Atom 0 [TConst 2%positive; TConst 4%positive]] join_env in
  (Cost.ticks (run_c plan) <=
    (work plan + 1) * join_unit_cost 2 0 3 200 200)%N.
Proof.
  cbn zeta; apply (join_run_cost _ 2 0 3 200 200).
  split.
  - split; [vm_compute; lia | split; [vm_compute; lia |]].
    intros b [Heq | Hbad]; [subst b | contradiction].
    split; [reflexivity |].
    split; [vm_compute; discriminate | split; [vm_compute; discriminate |]].
    intros row c Hrow Hc; vm_compute in Hrow.
    destruct Hrow as [Heq | Hbad]; [subst row | contradiction].
    cbn in Hc; destruct Hc as [<- | [<- | Hbad]];
      [vm_compute; discriminate | vm_compute; discriminate | contradiction].
  - exact I.
Qed.

(** The insertion client pays a nonunit reset and row callback and a nonempty encoded batch. *)
Example numeric_insert_contract :
  let plan := prepare join_program [Atom 0 [TConst 2%positive; TConst 4%positive]] join_env in
  (Cost.ticks (insert_rows_c
    (fun _ => Cost.lift (fun _ => 19%N) (fun _ => false) tt)
    (fun _ => Cost.lift (fun _ => 11%N)
      (fun _ => [[2%positive; 4%positive]]) tt) plan) <=
    N.of_nat (length plan) * insert_unit_cost 2 1 19 11 200 200)%N.
Proof.
  cbn zeta; apply (join_insert_cost _ _ _ 2 1 19 11 200 200).
  intros n Hn; vm_compute in Hn.
  destruct Hn as [Heq | Hbad]; [subst n | contradiction].
  split; [vm_compute; lia |].
  split; [vm_compute; discriminate | split; [vm_compute; discriminate |]].
  split; [vm_compute; discriminate |].
  intros row key [Heq | Hbad] Hkey; [subst row | contradiction].
  vm_compute in Hkey; injection Hkey as <-.
  split; vm_compute; discriminate.
Qed.

(** Preparation supplies the semantic duties of the public binding agreement theorem. *)
Example semantic_join_contract :
  list_equiv (run (prepare join_program triangle_atoms join_env))
    (join_positive_ref triangle_atoms join_env [[]]).
Proof.
  apply join_run_agrees, prepare_ready.
Qed.

(** Incremental updates inherit their semantic duties from preparation and maintenance proofs. *)
Example semantic_insert_contract :
  list_equiv
    (run (insert_rows (fun _ => Cost.ret false)
      (fun _ => Cost.ret [[8%positive; 9%positive]])
      (prepare join_program triangle_atoms join_env)))
    (run (prepare join_program triangle_atoms
      (fun p => Cost.ret (updated_env (fun _ => Cost.ret false)
        (fun _ => Cost.ret [[8%positive; 9%positive]]) join_env p)))).
Proof.
  apply join_insert_agrees, prepare_ready.
Qed.
