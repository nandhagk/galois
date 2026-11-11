(** * Costed independent dominance checking

    The checker retains raw parent-list semantics and uses the public costed reachability bridge.
    For example, cyclic candidate parents consume their finite budget and are rejected.
    Builds on: GraphCheckDom, GraphFrontierSweep and the primitive map cost boundaries. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphDomSpec
  GraphCheckDom GraphReach GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module DomCheckCost.
Local Open Scope nat_scope.

(** Bounded parent-list construction charges every visited cell and selected parent lookup. *)
Fixpoint chain_c fuel (m : Map.t positive positive) v : Cost.t (list positive) :=
  Cost.step ;;
  match fuel with
  | O => Cost.ret [v]
  | S fuel =>
    let* parent := Map.get_c positive_encoding v m in
    match parent with
    | None => Cost.ret [v]
    | Some u => Cost.map (cons v) (chain_c fuel m u)
    end
  end.

(** The charged list has the same raw cutoff, cycle and zero-fuel behavior as the checker. *)
Theorem chain_c_value fuel m v :
  Cost.value (chain_c fuel m v) = DomCheck.chain fuel m v.
Proof.
  revert v. induction fuel as [|fuel IH]; intro v; rewrite DomCheck.chain_equation.
  - reflexivity.
  - cbn [chain_c]. autorewrite with galois_cost.
    fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m); autorewrite with galois_cost;
      [now rewrite IH|reflexivity].
Qed.

(** Termination checking charges each recursive step and each actual parent-map lookup. *)
Fixpoint ends_c fuel (m : Map.t positive positive) v : Cost.t bool :=
  Cost.step ;;
  match fuel with
  | O => Cost.ret false
  | S fuel =>
    let* parent := Map.get_c positive_encoding v m in
    match parent with
    | None => Cost.ret true
    | Some u => ends_c fuel m u
    end
  end.

(** Charged termination testing agrees even for malformed or cyclic parent storage. *)
Theorem ends_c_value fuel m v :
  Cost.value (ends_c fuel m v) = DomCheck.ends fuel m v.
Proof.
  revert v. induction fuel as [|fuel IH]; intro v; rewrite DomCheck.ends_equation.
  - reflexivity.
  - cbn [ends_c]. autorewrite with galois_cost.
    fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m); [apply IH|reflexivity].
Qed.

(** Ancestry retains map-size traversal, bounded parent-list construction and digit comparisons. *)
Definition ancestor_b_c m d n :=
  let* size := Map.size_c m in
  let* path := chain_c size m n in
  existsb_c (positive_eqb_c d) path.

Local Lemma equality_exists d xs :
  existsb (fun x => Cost.value (positive_eqb_c d x)) xs = existsb (Pos.eqb d) xs.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [existsb]. now rewrite positive_eqb_equation, IH.
Qed.

(** Charged ancestry agrees with the exact existing checker observation for every raw map. *)
Theorem ancestor_b_c_value m d n :
  Cost.value (ancestor_b_c m d n) = DomCheck.ancestor_b m d n.
Proof.
  unfold ancestor_b_c. autorewrite with galois_cost.
  fold (Map.size m). rewrite chain_c_value, equality_exists, DomCheck.ancestor_b_equation.
  reflexivity.
Qed.

(** Blocked reachability charges singleton construction before invoking the shared closure. *)
Definition avoiding_c {V E} (p : Prepared.t V E) d :=
  let* blocked := FinSet.add_c positive_encoding d FinSet.empty in
  FrontierSweep.reach_c p (Scope.Make blocked None) (Prepared.entry_ids p).

(** The shared closure gives unconditional agreement, including malformed prepared inputs. *)
Theorem avoiding_c_value {V E} (p : Prepared.t V E) d :
  Cost.value (avoiding_c p d) =
    Reach.set p (Reach.blocked d) (Prepared.entry_ids p).
Proof.
  unfold avoiding_c. rewrite Cost.value_bind.
  fold (FinSet.add positive_encoding d FinSet.empty).
  rewrite FrontierSweep.reach_value, Reach.blocked_equation. reflexivity.
Qed.

Definition binding_ok_c seen (vu : positive * positive) :=
  let* child := FinSet.mem_c positive_encoding (fst vu) seen in
  let* parent := FinSet.mem_c positive_encoding (snd vu) seen in
  Cost.ret (child && parent).

Definition pair_ok_c m avoiding d n :=
  let* ancestor := ancestor_b_c m d n in
  let* reachable := FinSet.mem_c positive_encoding n avoiding in
  Cost.ret (Bool.eqb ancestor (negb reachable)).

(** The checker charges stored-support scans, chain tests and every blocked-closure computation. *)
Definition check_c {V E} (p : Prepared.t V E) m :=
  let* seen := FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p) in
  let* vs := FinSet.elements_c seen in
  let* bindings := Map.elements_c m in
  let* domains := forallb_c (binding_ok_c seen) bindings in
  let* size := Map.size_c m in
  let* forests := forallb_c (ends_c (S size) m) vs in
  let* pairs := forallb_c (fun d =>
    let* avoiding := avoiding_c p d in
    forallb_c (pair_ok_c m avoiding d) vs) vs in
  Cost.ret (domains && forests && pairs).

(** The checker equation exposes every charged scan and selected closure call. *)
Theorem check_c_equation {V E} (p : Prepared.t V E) m :
  check_c p m =
    (let* seen := FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p) in
     let* vs := FinSet.elements_c seen in
     let* bindings := Map.elements_c m in
     let* domains := forallb_c (binding_ok_c seen) bindings in
     let* size := Map.size_c m in
     let* forests := forallb_c (ends_c (S size) m) vs in
     let* pairs := forallb_c (fun d =>
       let* avoiding := avoiding_c p d in
       forallb_c (pair_ok_c m avoiding d) vs) vs in
     Cost.ret (domains && forests && pairs)).
Proof.
  reflexivity.
Qed.

(** Candidate-domain testing retains both membership queries. *)
Theorem binding_ok_cost seen vu :
  Cost.ticks (binding_ok_c seen vu) =
    (Cost.ticks (FinSet.mem_c positive_encoding (fst vu) seen) +
      Cost.ticks (FinSet.mem_c positive_encoding (snd vu) seen))%N.
Proof.
  unfold binding_ok_c. autorewrite with galois_cost. lia.
Qed.

(** Pair testing retains ancestry construction, scanning and avoiding-set membership. *)
Theorem pair_ok_cost m avoiding d n :
  Cost.ticks (pair_ok_c m avoiding d n) =
    (Cost.ticks (ancestor_b_c m d n) +
      Cost.ticks (FinSet.mem_c positive_encoding n avoiding))%N.
Proof.
  unfold pair_ok_c. autorewrite with galois_cost. lia.
Qed.

(** Avoiding reachability includes singleton construction before the shared closure. *)
Theorem avoiding_cost {V E} (p : Prepared.t V E) d :
  Cost.ticks (avoiding_c p d) =
    (Cost.ticks (FinSet.add_c positive_encoding d FinSet.empty) +
      Cost.ticks (FrontierSweep.reach_c p (Reach.blocked d) (Prepared.entry_ids p)))%N.
Proof.
  unfold avoiding_c. rewrite Cost.ticks_bind, Reach.blocked_equation. reflexivity.
Qed.

Local Lemma binding_ok_value seen vu :
  Cost.value (binding_ok_c seen vu) =
    (FinSet.mem positive_encoding (fst vu) seen &&
      FinSet.mem positive_encoding (snd vu) seen).
Proof.
  reflexivity.
Qed.

Local Lemma pair_ok_value m avoiding d n :
  Cost.value (pair_ok_c m avoiding d n) =
    Bool.eqb (DomCheck.ancestor_b m d n)
      (negb (FinSet.mem positive_encoding n avoiding)).
Proof.
  unfold pair_ok_c. autorewrite with galois_cost.
  now rewrite ancestor_b_c_value.
Qed.

Local Lemma forallb_ext {A} (f g : A -> bool) xs :
  (forall x, f x = g x) -> forallb f xs = forallb g xs.
Proof.
  intro Hagree. induction xs as [|x rest IH]; [reflexivity|].
  cbn [forallb]. now rewrite Hagree, IH.
Qed.

(** The costed checker equals DomCheck.check on all computational inputs without law premises. *)
Theorem check_c_value {V E} (p : Prepared.t V E) m :
  Cost.value (check_c p m) = DomCheck.check p m.
Proof.
  unfold check_c. autorewrite with galois_cost.
  rewrite FrontierSweep.reach_value.
  fold (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))).
  fold (Map.elements m). fold (Map.size m). rewrite DomCheck.check_equation.
  cbn zeta.
  set (seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
  set (vs := FinSet.elements seen).
  assert (Hbindings :
    forallb (fun vu => Cost.value (binding_ok_c seen vu)) (Map.elements m) =
      forallb (fun vu => FinSet.mem positive_encoding (fst vu) seen &&
        FinSet.mem positive_encoding (snd vu) seen) (Map.elements m)).
  { apply forallb_ext. intro vu. apply binding_ok_value. }
  assert (Hends :
    forallb (fun v => Cost.value (ends_c (S (Map.size m)) m v)) vs =
      forallb (DomCheck.ends (S (Map.size m)) m) vs).
  { apply forallb_ext. intro v. apply ends_c_value. }
  rewrite Hbindings, Hends. f_equal.
  apply forallb_ext. intro d. rewrite Cost.value_bind, avoiding_c_value, value_forallb_c.
  apply forallb_ext. intro n. apply pair_ok_value.
Qed.

Definition id_get_budget w := (1 + 2 * w)%N.

Local Lemma id_get_cost {A} (m : Map.t positive A) v w :
  (key_bits positive_encoding v <= w)%N ->
  (Cost.ticks (Map.get_c positive_encoding v m) <= id_get_budget w)%N.
Proof.
  intro Hwidth. rewrite Map.get_cost, positive_encoding_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v) as Hencoding.
  rewrite positive_encoding_cost in Hencoding.
  fold (key_bits positive_encoding v). unfold id_get_budget. nia.
Qed.

(** Candidate-chain widths include every stored parent value, independently of its stored key. *)
Definition parent_width (m : Map.t positive positive) w : Prop :=
  forall v u, Map.get positive_encoding v m = Some u ->
    (key_bits positive_encoding u <= w)%N.

(** A bounded parent-list costs its actual budget times the finite query and parent width. *)
Theorem chain_cost fuel m v w :
  parent_width m w -> (key_bits positive_encoding v <= w)%N ->
  (Cost.ticks (chain_c fuel m v) <=
    N.of_nat (S fuel) * (1 + id_get_budget w))%N.
Proof.
  intros Hparents. revert v. induction fuel as [|fuel IH]; intros v Hv.
  - cbn [chain_c]. autorewrite with galois_cost. unfold id_get_budget. lia.
  - pose proof (id_get_cost m v w Hv) as Hget.
    cbn [chain_c]. autorewrite with galois_cost.
    fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m) as [u|] eqn:Hparent;
      autorewrite with galois_cost.
    + specialize (IH u (Hparents v u Hparent)).
      rewrite Nat2N.inj_succ. nia.
    + rewrite Nat2N.inj_succ. nia.
Qed.

(** Termination testing has the same finite width domain and retains the zero-fuel step. *)
Theorem ends_cost fuel m v w :
  parent_width m w -> (key_bits positive_encoding v <= w)%N ->
  (Cost.ticks (ends_c fuel m v) <=
    N.of_nat (S fuel) * (1 + id_get_budget w))%N.
Proof.
  intros Hparents. revert v. induction fuel as [|fuel IH]; intros v Hv.
  - cbn [ends_c]. autorewrite with galois_cost. unfold id_get_budget. lia.
  - pose proof (id_get_cost m v w Hv) as Hget.
    cbn [ends_c]. autorewrite with galois_cost.
    fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m) as [u|] eqn:Hparent;
      autorewrite with galois_cost.
    + specialize (IH u (Hparents v u Hparent)).
      rewrite Nat2N.inj_succ. nia.
    + rewrite Nat2N.inj_succ. nia.
Qed.

Local Lemma chain_length fuel m v :
  (length (Cost.value (chain_c fuel m v)) <= S fuel)%nat.
Proof.
  revert v. induction fuel as [|fuel IH]; intro v.
  - reflexivity.
  - cbn [chain_c]. autorewrite with galois_cost.
    fold (Map.get positive_encoding v m).
    destruct (Map.get positive_encoding v m) as [u|];
      autorewrite with galois_cost; cbn [length]; [pose proof (IH u)|]; lia.
Qed.

(** Ancestry's numeric budget includes unrelated candidate support and physical trie depth. *)
Definition ancestor_budget (m : Map.t positive positive) w :=
  (TrieCost.trie_k * (1 + MapCost.skeleton_nodes m) +
    N.of_nat (S (Map.size m)) * (2 + id_get_budget w + w))%N.

(** Raw ancestry has a primitive numeric bound with explicit candidate-storage measures. *)
Theorem ancestor_cost m d n w :
  parent_width m w ->
  (key_bits positive_encoding d <= w)%N ->
  (key_bits positive_encoding n <= w)%N ->
  (Cost.ticks (ancestor_b_c m d n) <= ancestor_budget m w)%N.
Proof.
  intros Hparents Hd Hn.
  pose proof (MapCost.size_cost m) as Hsize.
  pose proof (chain_cost (Map.size m) m n w Hparents Hn) as Hchain.
  pose proof (chain_length (Map.size m) m n) as Hlength.
  pose proof (ticks_existsb_c_le (positive_eqb_c d) w
    (Cost.value (chain_c (Map.size m) m n))) as Hscan.
  specialize (Hscan ltac:(intros x;
    eapply N.le_trans; [exact (proj1 (positive_eqb_cost d x))|exact Hd])).
  unfold ancestor_b_c. rewrite !Cost.ticks_bind.
  fold (Map.size m). unfold ancestor_budget.
  assert (Hscaled :
    (N.of_nat (length (Cost.value (chain_c (Map.size m) m n))) * (w + 1) <=
      N.of_nat (S (Map.size m)) * (w + 1))%N).
  { apply N.mul_le_mono; [lia|reflexivity]. }
  nia.
Qed.

(** The ancestry budget keeps both candidate cardinality and physical skeleton size. *)
Definition ancestor_bound b w s :=
  (TrieCost.trie_k * (1 + s) + (N.of_nat b + 1) * (2 + id_get_budget w + w))%N.

(** Finite candidate storage measures bound ancestry without map-validity premises. *)
Theorem ancestor_numeric_cost m d n w b s :
  parent_width m w ->
  (key_bits positive_encoding d <= w)%N ->
  (key_bits positive_encoding n <= w)%N ->
  (Map.size m <= b)%nat -> (MapCost.skeleton_nodes m <= s)%N ->
  (Cost.ticks (ancestor_b_c m d n) <= ancestor_bound b w s)%N.
Proof.
  intros Hparents Hd Hn Hsize Hskeleton.
  pose proof (ancestor_cost m d n w Hparents Hd Hn) as Hcost.
  unfold ancestor_budget, ancestor_bound in *. rewrite Nat2N.inj_succ in Hcost.
  assert (Hcard : (N.of_nat (Map.size m) <= N.of_nat b)%N) by lia.
  assert (Hscan : (TrieCost.trie_k * (1 + MapCost.skeleton_nodes m) <=
    TrieCost.trie_k * (1 + s))%N) by (apply N.mul_le_mono; lia).
  assert (Hwalk : ((N.of_nat (Map.size m) + 1) * (2 + id_get_budget w + w) <=
    (N.of_nat b + 1) * (2 + id_get_budget w + w))%N)
    by (apply N.mul_le_mono; lia).
  lia.
Qed.

(** A checked parent representation remains a separate premise after cost instrumentation. *)
Theorem checked_exact {V E} (p : Prepared.t V E) m :
  Prepared.ready p -> Map.wf positive_encoding m ->
  Cost.value (check_c p m) = true -> Dom.exact p (DomCheck.of_parents p m).
Proof.
  intros Hready Hmap Hcheck. apply (DomCheck.check_sound p m Hready Hmap).
  now rewrite <- check_c_value.
Qed.

End DomCheckCost.
