(** * Charged bounded-ancestry indexes

    Each listed child's raw bounded chain is materialized once for repeated ancestry queries.
    For example, a cyclic candidate retains exactly the compatibility checker's cutoff behavior.
    Builds on: GraphCheckDomCost and public canonical map and set operations. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphCheckDom GraphCheckDomCost.
Import Cost.Notations.

Module DomAncestorIndex.
Local Open Scope N_scope.

Definition row_c fuel (parents : Map.t positive positive) v :=
  let* path := DomCheckCost.chain_c fuel parents v in
  FinSet.of_list_c positive_encoding path.

Definition build_with_c size (parents : Map.t positive positive) nodes :=
  fold_right_c (fun v index =>
    let* ancestors := row_c size parents v in
    Map.set_c positive_encoding v ancestors index) Map.empty nodes.

Definition build_c (parents : Map.t positive positive) nodes :=
  let* size := Map.size_c parents in
  build_with_c size parents nodes.

Definition build parents nodes := Cost.value (build_c parents nodes).

(** A caller that already charged the map-size scan reuses that value without another scan. *)
Theorem build_with_value parents nodes :
  Cost.value (build_with_c (Map.size parents) parents nodes) = build parents nodes.
Proof.
  reflexivity.
Qed.

Definition contains_c (index : Map.t positive (FinSet.t positive)) d n :=
  let* ancestors := Map.get_c positive_encoding n index in
  match ancestors with
  | None => Cost.ret false
  | Some ancestors => FinSet.mem_c positive_encoding d ancestors
  end.

(** Every row contains the exact raw chain, including malformed storage and exhausted cutoffs. *)
Theorem row_value fuel parents v :
  Cost.value (row_c fuel parents v) =
    FinSet.of_list positive_encoding (DomCheck.chain fuel parents v).
Proof.
  unfold row_c. rewrite Cost.value_bind, DomCheckCost.chain_c_value. reflexivity.
Qed.

(** Row membership agrees with the compatibility checker's bounded-chain Boolean. *)
Theorem row_mem fuel parents d n :
  FinSet.mem positive_encoding d (Cost.value (row_c fuel parents n)) =
    existsb (Pos.eqb d) (DomCheck.chain fuel parents n).
Proof.
  rewrite row_value, FinSet.mem_of_list.
  apply Bool.eq_true_iff_eq. rewrite !existsb_exists. split.
  - intros [v [Hin Heq]]. apply (eqb_true_iff _ positive_encoding_laws) in Heq.
    exists v. split; [exact Hin|now apply Pos.eqb_eq].
  - intros [v [Hin Heq]]. apply Pos.eqb_eq in Heq.
    exists v. split; [exact Hin|now apply (eqb_true_iff _ positive_encoding_laws)].
Qed.

(** Index construction uses one size traversal and the actual charged right fold. *)
Theorem build_equation parents nodes :
  build parents nodes =
    fold_right (fun v index =>
      Map.set positive_encoding v
        (FinSet.of_list positive_encoding (DomCheck.chain (Map.size parents) parents v)) index)
      Map.empty nodes.
Proof.
  unfold build, build_c, build_with_c. autorewrite with galois_cost. fold (Map.size parents).
  induction nodes as [|v rest IH]; [reflexivity|].
  cbn [fold_right]. autorewrite with galois_cost. rewrite row_value, IH. reflexivity.
Qed.

Local Lemma fold_wf parents fuel nodes :
  Map.wf positive_encoding
    (fold_right (fun v index =>
      Map.set positive_encoding v
        (FinSet.of_list positive_encoding (DomCheck.chain fuel parents v)) index)
      Map.empty nodes).
Proof.
  induction nodes as [|v rest IH]; [apply Map.wf_empty|].
  cbn [fold_right]. now apply Map.wf_set.
Qed.

(** The index has canonical storage even when the supplied parent map does not. *)
Theorem build_wf parents nodes :
  Map.wf positive_encoding (build parents nodes).
Proof.
  rewrite build_equation. apply fold_wf.
Qed.

Local Lemma fold_get parents fuel nodes n :
  In n nodes ->
  Map.get positive_encoding n
    (fold_right (fun v index =>
      Map.set positive_encoding v
        (FinSet.of_list positive_encoding (DomCheck.chain fuel parents v)) index)
      Map.empty nodes) =
    Some (FinSet.of_list positive_encoding (DomCheck.chain fuel parents n)).
Proof.
  induction nodes as [|v rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct (Pos.eq_dec n v) as [->|Hne].
  - apply Map.get_set_same. apply fold_wf.
  - rewrite Map.get_set_other by
      (try exact positive_encoding_laws; try apply fold_wf; exact Hne).
    apply IH. destruct Hin as [Heq|Hin]; [congruence|exact Hin].
Qed.

(** Every listed child receives its exact bounded-chain set without a uniqueness premise on nodes. *)
Theorem build_get parents nodes n :
  In n nodes ->
  Map.get positive_encoding n (build parents nodes) =
    Some (FinSet.of_list positive_encoding (DomCheck.chain (Map.size parents) parents n)).
Proof.
  intro Hin. rewrite build_equation. now apply fold_get.
Qed.

(** Indexed queries agree unconditionally with raw ancestry for every listed child. *)
Theorem contains_value parents nodes d n :
  In n nodes ->
  Cost.value (contains_c (build parents nodes) d n) = DomCheck.ancestor_b parents d n.
Proof.
  intro Hin.
  change (Cost.value
    (match Map.get positive_encoding n (build parents nodes) with
    | None => Cost.ret false
    | Some ancestors => FinSet.mem_c positive_encoding d ancestors
    end) = DomCheck.ancestor_b parents d n).
  rewrite build_get by exact Hin.
  change (FinSet.mem positive_encoding d
    (FinSet.of_list positive_encoding (DomCheck.chain (Map.size parents) parents n)) =
      DomCheck.ancestor_b parents d n).
  rewrite <- (row_value (Map.size parents) parents n), row_mem.
  symmetry. apply DomCheck.ancestor_b_equation.
Qed.

(** Bounded chains have finite length and inherit the actual query and stored-parent widths. *)
Theorem chain_resources fuel parents n w :
  DomCheckCost.parent_width parents w -> key_bits positive_encoding n <= w ->
  (length (DomCheck.chain fuel parents n) <= S fuel)%nat /\
    Forall (fun v => key_bits positive_encoding v <= w) (DomCheck.chain fuel parents n).
Proof.
  intros Hparents. revert n. induction fuel as [|fuel IH]; intros n Hn;
    rewrite DomCheck.chain_equation.
  - split; [reflexivity|constructor; [exact Hn|constructor]].
  - destruct (Map.get positive_encoding n parents) as [parent|] eqn:Hget.
    + destruct (IH parent (Hparents n parent Hget)) as [Hlength Hwidth].
      split; [cbn [length]; lia|now constructor].
    + split; [cbn [length]; lia|constructor; [exact Hn|constructor]].
Qed.

(** Row construction charges the chain traversal and every inserted ancestor occurrence. *)
Theorem row_cost fuel parents n w :
  DomCheckCost.parent_width parents w -> key_bits positive_encoding n <= w ->
  Cost.ticks (row_c fuel parents n) <=
    N.of_nat (S fuel) * (5 + DomCheckCost.id_get_budget w + w).
Proof.
  intros Hparents Hn.
  pose proof (DomCheckCost.chain_cost fuel parents n w Hparents Hn) as Hchain.
  destruct (chain_resources fuel parents n w Hparents Hn) as [Hlength Hwidth].
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding
    (DomCheck.chain fuel parents n) 1 w
    ltac:(intros v Hv; split; [reflexivity|exact (proj1 (Forall_forall _ _) Hwidth v Hv)]))
    as Hset.
  unfold row_c. rewrite Cost.ticks_bind, DomCheckCost.chain_c_value.
  assert (Hscale : N.of_nat (length (DomCheck.chain fuel parents n)) * (4 + w) <=
    N.of_nat (S fuel) * (4 + w)).
  { apply N.mul_le_mono; [lia|reflexivity]. }
  lia.
Qed.

(** Index construction retains one physical size scan and every row and index-key charge. *)
Theorem build_cost parents nodes w :
  DomCheckCost.parent_width parents w ->
  (forall n, In n nodes -> key_bits positive_encoding n <= w) ->
  Cost.ticks (build_c parents nodes) <=
    TrieCost.trie_k * (1 + MapCost.skeleton_nodes parents) +
    N.of_nat (length nodes) *
      (2 + DomCheckCost.id_get_budget w +
        N.of_nat (S (Map.size parents)) * (5 + DomCheckCost.id_get_budget w + w)).
Proof.
  intros Hparents Hwidth.
  pose proof (MapCost.size_cost parents) as Hsize.
  set (step := fun v (index : Map.t positive (FinSet.t positive)) =>
    let* ancestors := row_c (Map.size parents) parents v in
    Map.set_c positive_encoding v ancestors index).
  set (k := 1 + DomCheckCost.id_get_budget w +
    N.of_nat (S (Map.size parents)) * (5 + DomCheckCost.id_get_budget w + w)).
  assert (Hstep : forall n index, In n nodes -> Cost.ticks (step n index) <= k).
  { intros n index Hn.
    pose proof (row_cost (Map.size parents) parents n w Hparents (Hwidth n Hn)) as Hrow.
    pose proof (Hwidth n Hn) as Hbits.
    unfold step. rewrite Cost.ticks_bind, Map.set_cost.
    change (Cost.ticks (row_c (Map.size parents) parents n) +
      (1 + 1 + key_bits positive_encoding n) <= k).
    unfold k, DomCheckCost.id_get_budget in *. nia. }
  pose proof (proj2 (ticks_fold_right_c_potential step (fun _ => True) (fun _ => 0) k
    nodes Map.empty ltac:(intros n index Hn _; split; [exact I|];
      pose proof (Hstep n index Hn); cbn beta; lia) I)) as Hfold.
  unfold build_c, build_with_c. rewrite Cost.ticks_bind. cbn beta. fold (Map.size parents).
  change (Cost.ticks (Map.size_c parents) +
    Cost.ticks (fold_right_c step Map.empty nodes) <=
    TrieCost.trie_k * (1 + MapCost.skeleton_nodes parents) +
    N.of_nat (length nodes) *
      (2 + DomCheckCost.id_get_budget w +
        N.of_nat (S (Map.size parents)) * (5 + DomCheckCost.id_get_budget w + w))).
  cbn beta in Hfold. unfold k in Hfold.
  rewrite (N.add_comm
    (1 + DomCheckCost.id_get_budget w +
      N.of_nat (S (Map.size parents)) * (5 + DomCheckCost.id_get_budget w + w)) 1) in Hfold.
  rewrite !N.add_assoc in Hfold. lia.
Qed.

(** Indexed ancestry uses two width-priced queries regardless of the stored chain's length. *)
Theorem contains_cost index d n w :
  key_bits positive_encoding d <= w -> key_bits positive_encoding n <= w ->
  Cost.ticks (contains_c index d n) <= 2 * (2 + w).
Proof.
  intros Hd Hn. unfold contains_c. rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding n index).
  pose proof (encode_cost_bound positive_encoding_cost_laws n) as Hencode.
  destruct (Map.get positive_encoding n index) as [ancestors|];
    autorewrite with galois_cost; rewrite Map.get_cost.
  - rewrite FinSet.mem_cost.
    change (1 + 1 + key_bits positive_encoding n +
      (1 + 1 + key_bits positive_encoding d) <= 2 * (2 + w)).
    lia.
  - change (1 + 1 + key_bits positive_encoding n + 0 <= 2 * (2 + w)). lia.
Qed.

End DomAncestorIndex.
