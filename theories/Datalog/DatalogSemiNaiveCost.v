(** * Primitive costs of semi-naive batch maintenance

    Batch storage and cached-plan maintenance charge new rows and the complete plan inventory.
    For example, a frontier reset never enumerates the previous frontier or accumulated relations.
    Builds on: DatalogJoinUpdateCost and the public one-sided FinSet traversal bounds. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost BaseSet BaseSetCost BaseTrieCost.
From Galois.Lattice Require Import LatticeSet.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogCost DatalogSolve
  DatalogJoin DatalogJoinCost DatalogJoinUpdateCost DatalogJoinPrepareCost DatalogSemiNaive
  DatalogSemiNaiveIndex.
Import List.ListNotations Cost.Notations SemiNaive SemiNaiveIndex.
Local Open Scope N_scope.

Module SemiNaiveCost.

(** A primitive key budget keeps encoding computation and trie width separate. *)
Definition key_budget {A} (E : encoding A) e w x : Prop :=
  Cost.ticks (encode_c E x) <= e /\ key_bits E x <= w.

(** New-batch construction adds a candidate-side difference charge to candidate generation. *)
Theorem new_difference_cost {P} (prog : program P) st lower k s w :
  (forall f, FinSet.mem (ground_encoding prog) f (candidates prog st lower k s) = true ->
    key_bits (ground_encoding prog) f <= w) ->
  Cost.ticks (new_c prog st lower k s) <=
    Cost.ticks (candidates_c prog st lower k s) +
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size (candidates prog st lower k s)) * w).
Proof.
  intro Hwidth; unfold new_c; rewrite Cost.ticks_bind.
  fold (@candidates P prog st lower k s).
  apply N.add_le_mono; [reflexivity |].
  apply (FinSetCost.diff_numeric_cost (ground_encoding prog));
    [apply candidates_wf | exact Hwidth].
Qed.

(** Predicate-index lookup charges the supplied encoder and its actual trie path. *)
Theorem rel_of_cost {P} (prog : program P) db p ep wp :
  key_budget (penc prog) ep wp p ->
  Cost.ticks (rel_of_c prog db p) <= 1 + ep + wp.
Proof.
  intros [Henc Hwidth].
  change (Cost.ticks (lookup_c (penc prog) relation_lattice db p) <= 1 + ep + wp).
  rewrite lookup_cost, Map.get_cost; fold (key_bits (penc prog) p); lia.
Qed.

(** Batch enumeration retains stored ground-key width and one key-extraction tick per member. *)
Theorem batch_elements_cost {P} (prog : program P) batch w :
  FinSet.wf (ground_encoding prog) batch ->
  (forall f, FinSet.mem (ground_encoding prog) f batch = true ->
    key_bits (ground_encoding prog) f <= w) ->
  Cost.ticks (FinSet.elements_c batch) <=
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size batch) * w) +
      N.of_nat (FinSet.size batch).
Proof.
  intros Hwf Hwidth; rewrite FinSet.elements_cost_equation.
  apply N.add_le_mono; [|reflexivity].
  rewrite FinSet.size_backend; apply (MapCost.elements_numeric_cost (ground_encoding prog)).
  - exact Hwf.
  - intros f [] Hget; apply Hwidth, FinSet.mem_spec, Hget.
Qed.

(** The row-storage coefficient includes both predicate encodings and the tuple insertion. *)
Definition add_atoms_unit_cost ep wp et wt := 5 + 2 * (ep + wp) + et + wt.

(** Storing a batch charges supplied row occurrences and never enumerates the existing database. *)
Theorem add_atoms_cost {P} (prog : program P) rows db ep wp et wt :
  (forall f, In f rows ->
    key_budget (penc prog) ep wp (fst f) /\
    key_budget tuple_encoding et wt (snd f)) ->
  Cost.ticks (add_atoms_c prog rows db) <=
    N.of_nat (length rows) * add_atoms_unit_cost ep wp et wt.
Proof.
  intro Hkeys; unfold add_atoms_c.
  eapply N.le_trans; [apply (fold_right_bound_on _
    (add_atoms_unit_cost ep wp et wt - 1)) |].
  - intros f acc Hf; destruct (Hkeys f Hf) as [Hp [Het Hwt]].
    pose proof (rel_of_cost prog acc (fst f) ep wp Hp) as Hlookup.
    destruct Hp as [Hep Hwp].
    repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step, Map.set_cost.
    fold (key_bits (penc prog) (fst f)).
    fold (@rel_of P prog acc (fst f)).
    assert (Hadd : Cost.ticks (set_add_c tuple_encoding (snd f)
      (rel_of prog acc (fst f))) <= 1 + et + wt).
    { change (Cost.ticks (FinSet.add_c tuple_encoding (snd f)
        (set_raw (rel_of prog acc (fst f)))) <= 1 + et + wt).
      rewrite FinSet.add_cost; fold (key_bits tuple_encoding (snd f)); lia. }
    unfold add_atoms_unit_cost; lia.
  - unfold add_atoms_unit_cost; nia.
Qed.

(** Batch-row callbacks pay for predicate lookup and enumeration of the supplied new relation. *)
Definition batch_rows_charge rows ep wp wt :=
  1 + ep + wp + TrieCost.trie_k * (1 + rows * wt) + rows.

Lemma batch_rows_cost {P} (prog : program P) batch q rows ep wp wt :
  key_budget (penc prog) ep wp (fst q) ->
  N.of_nat (FinSet.size (set_raw (rel_of prog batch (fst q)))) <= rows ->
  (forall row, member row (rel_of prog batch (fst q)) = true ->
    key_bits tuple_encoding row <= wt) ->
  Cost.ticks (batch_rows_c prog batch q) <= batch_rows_charge rows ep wp wt.
Proof.
  intros Hkey Hcount Hwidth.
  pose proof (rel_of_cost prog batch (fst q) ep wp Hkey) as Hlookup.
  pose proof (JoinPrepareCost.relation_elements_cost
    (rel_of prog batch (fst q)) wt Hwidth) as Henumeration.
  unfold batch_rows_c; rewrite Cost.ticks_bind.
  change (Cost.ticks (rel_of_c prog batch (fst q)) +
    Cost.ticks (FinSet.elements_c (set_raw (rel_of prog batch (fst q)))) <=
    batch_rows_charge rows ep wp wt).
  assert (Hscaled :
    TrieCost.trie_k * (1 +
      N.of_nat (FinSet.size (set_raw (rel_of prog batch (fst q)))) * wt) +
      N.of_nat (FinSet.size (set_raw (rel_of prog batch (fst q)))) <=
    TrieCost.trie_k * (1 + rows * wt) + rows).
  { apply N.add_le_mono; [|exact Hcount].
    apply N.mul_le_mono; [reflexivity |].
    apply N.add_le_mono; [reflexivity |].
    apply N.mul_le_mono; [exact Hcount | reflexivity]. }
  unfold batch_rows_charge; lia.
Qed.

(** Maintenance duties concern stored row data and primitive keys without a helper-price premise. *)
Definition maintenance_data {P} (prog : program P) batch (plan : Join.plan_state (P * bool))
    a rows ep wp et wt : Prop :=
  forall node, In node plan ->
    (length (Join.mask node) <= a)%nat /\
    key_budget (penc prog) ep wp (fst (pred (Join.source node))) /\
    N.of_nat (FinSet.size (set_raw
      (rel_of prog batch (fst (pred (Join.source node)))))) <= rows /\
    (forall row, member row (rel_of prog batch (fst (pred (Join.source node)))) = true ->
      key_bits tuple_encoding row <= wt) /\
    forall row key,
      member row (rel_of prog batch (fst (pred (Join.source node)))) = true ->
      Join.select (Join.mask node) row = Some key ->
      key_budget tuple_encoding et wt key.

Lemma maintenance_primitives {P} (prog : program P) batch plan a rows ep wp et wt :
  maintenance_data prog batch plan a rows ep wp et wt ->
  JoinUpdateCost.insert_primitives plan (fun q => Cost.ret (snd q)) (batch_rows_c prog batch)
    a rows 0 (batch_rows_charge rows ep wp wt) et wt.
Proof.
  intros Hdata node Hnode.
  destruct (Hdata node Hnode) as [Hmask [Hkey [Hcount [Hwidth Hselected]]]].
  split; [exact Hmask | split; [apply N.le_refl | split]].
  - apply batch_rows_cost; assumption.
  - rewrite batch_rows_equation, <- FinSet.size_elements; split; [exact Hcount |].
    intros row key Hrow Hselect; apply (Hselected row key); [|exact Hselect].
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws); [|exact Hrow].
    exact (proj2_sig (rel_of prog batch (fst (pred (Join.source node))))).
Qed.

(** Cached job maintenance derives callback prices from batch data and public primitive bounds. *)
Theorem update_job_cost {P} (prog : program P) batch j a rows ep wp et wt :
  maintenance_data prog batch (plan j) a rows ep wp et wt ->
  Cost.ticks (update_job_c prog batch j) <=
    N.of_nat (length (plan j)) *
      JoinUpdateCost.insert_unit_cost a rows 0 (batch_rows_charge rows ep wp wt) et wt.
Proof.
  intro Hdata; unfold update_job_c; rewrite Cost.ticks_bind, Cost.ticks_ret, N.add_0_r.
  apply JoinUpdateCost.join_insert_cost, maintenance_primitives, Hdata.
Qed.

(** The maintenance inventory includes every cached atom occurrence even for an empty batch. *)
Definition plan_inventory {P} (js : list (job P)) :=
  fold_right (fun j n => N.of_nat (length (plan j)) + n) 0 js.

Lemma update_jobs_cost {P} (prog : program P) batch js a rows ep wp et wt :
  (forall j, In j js -> maintenance_data prog batch (plan j) a rows ep wp et wt) ->
  Cost.ticks (map_c (update_job_c prog batch) js) <= N.of_nat (length js) +
    plan_inventory js *
      JoinUpdateCost.insert_unit_cost a rows 0 (batch_rows_charge rows ep wp wt) et wt.
Proof.
  intro Hdata; rewrite ticks_map_c.
  induction js as [|j js IH]; [change (0 <= 0); lia |].
  cbn [fold_right length plan_inventory]; rewrite Nat2N.inj_succ.
  fold (@plan_inventory P js).
  pose proof (update_job_cost prog batch j a rows ep wp et wt
    (Hdata j (or_introl eq_refl))) as Hjob.
  specialize (IH (fun x Hx => Hdata x (or_intror Hx))); nia.
Qed.

(** The advancement domain keeps new-batch enumeration, two index stores and every cached plan. *)
Definition advance_charge {P} (s : state P) (batch : FinSet.t (ground_atom P))
    a rows ep wp et wt wg :=
  let count := N.of_nat (FinSet.size batch) in
  TrieCost.trie_k * (1 + count * wg) + count +
  (TrieCost.trie_k + 1) * (1 + count * wg) +
  count * add_atoms_unit_cost ep wp et wt +
  count * add_atoms_unit_cost ep wp et wt +
  N.of_nat (length (jobs s)) +
  plan_inventory (jobs s) *
    JoinUpdateCost.insert_unit_cost a rows 0 (batch_rows_charge rows ep wp wt) et wt.

(** Actual advancement has no old-accumulated-size term and assumes no owned-helper price. *)
Theorem advance_cost {P} (prog : program P) s batch a rows ep wp et wt wg :
  encoding_laws (penc prog) ->
  FinSet.wf (ground_encoding prog) batch ->
  (forall f, FinSet.mem (ground_encoding prog) f batch = true ->
    key_bits (ground_encoding prog) f <= wg /\
    key_budget (penc prog) ep wp (fst f) /\
    key_budget tuple_encoding et wt (snd f)) ->
  (forall j, In j (jobs s) ->
    maintenance_data prog (add_atoms prog (FinSet.elements batch) Map.empty)
      (plan j) a rows ep wp et wt) ->
  Cost.ticks (advance_c prog s batch) <= advance_charge s batch a rows ep wp et wt wg.
Proof.
  intros HE Hwf Hkeys Hmaintenance.
  pose proof (batch_elements_cost prog batch wg Hwf (fun f Hf => proj1 (Hkeys f Hf)))
    as Henumeration.
  pose proof (FinSetCost.union_numeric_cost_right (ground_encoding prog)
    (accumulated s) batch wg Hwf (fun f Hf => proj1 (Hkeys f Hf))) as Hunion.
  assert (Hstorekeys : forall f, In f (FinSet.elements batch) ->
    key_budget (penc prog) ep wp (fst f) /\ key_budget tuple_encoding et wt (snd f)).
  { intros f Hf.
    apply (FinSet.elements_spec (ground_encoding prog)
      (ground_encoding_laws prog HE) _ _ Hwf) in Hf.
    exact (proj2 (Hkeys f Hf)). }
  pose proof (add_atoms_cost prog (FinSet.elements batch) (accumulated_index s)
    ep wp et wt Hstorekeys) as Haccumulated.
  pose proof (add_atoms_cost prog (FinSet.elements batch) Map.empty
    ep wp et wt Hstorekeys) as Hfrontier.
  pose proof (update_jobs_cost prog (add_atoms prog (FinSet.elements batch) Map.empty)
    (jobs s) a rows ep wp et wt Hmaintenance) as Hjobs.
  unfold advance_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_ret.
  fold (@FinSet.elements (ground_atom P) batch).
  fold (@add_atoms P prog (FinSet.elements batch) Map.empty).
  rewrite <- FinSet.size_elements in Haccumulated, Hfrontier.
  change (Cost.ticks (FinSet.elements_c batch) +
    (Cost.ticks (FinSet.union_c (accumulated s) batch) +
    (Cost.ticks (add_atoms_c prog (FinSet.elements batch) (accumulated_index s)) +
    (Cost.ticks (add_atoms_c prog (FinSet.elements batch) Map.empty) +
    (Cost.ticks (map_c (update_job_c prog
      (add_atoms prog (FinSet.elements batch) Map.empty)) (jobs s)) + 0)))) <=
      advance_charge s batch a rows ep wp et wt wg).
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Henumeration |].
    apply N.add_le_mono; [exact Hunion |].
    apply N.add_le_mono; [exact Haccumulated |].
    apply N.add_le_mono; [exact Hfrontier |].
    apply N.add_le_mono; [exact Hjobs | exact (N.le_refl 0)].
  - unfold advance_charge; cbn zeta.
    repeat rewrite N.add_assoc; rewrite N.add_0_r; apply N.le_refl.
Qed.

(** The advancement family permits arbitrary accumulated storage and varying fresh batches. *)
Theorem advance_bigO {X P} (prog : X -> program P) (s : X -> state P)
    (batch : X -> FinSet.t (ground_atom P)) (a : X -> nat)
    (rows ep wp et wt wg : X -> N) :
  (forall x, encoding_laws (penc (prog x))) ->
  (forall x, FinSet.wf (ground_encoding (prog x)) (batch x)) ->
  (forall x f, FinSet.mem (ground_encoding (prog x)) f (batch x) = true ->
    key_bits (ground_encoding (prog x)) f <= wg x /\
    key_budget (penc (prog x)) (ep x) (wp x) (fst f) /\
    key_budget tuple_encoding (et x) (wt x) (snd f)) ->
  (forall x j, In j (jobs (s x)) ->
    maintenance_data (prog x)
      (add_atoms (prog x) (FinSet.elements (batch x)) Map.empty)
      (plan j) (a x) (rows x) (ep x) (wp x) (et x) (wt x)) ->
  bigO (fun x => advance_charge (s x) (batch x) (a x) (rows x)
    (ep x) (wp x) (et x) (wt x) (wg x))
    (fun x => Cost.ticks (advance_c (prog x) (s x) (batch x))).
Proof.
  intros HE Hwf Hkeys Hmaintenance; exists 1; intro x.
  pose proof (advance_cost (prog x) (s x) (batch x) (a x) (rows x)
    (ep x) (wp x) (et x) (wt x) (wg x) (HE x) (Hwf x) (Hkeys x) (Hmaintenance x)).
  nia.
Qed.

End SemiNaiveCost.
Import SemiNaiveCost.
