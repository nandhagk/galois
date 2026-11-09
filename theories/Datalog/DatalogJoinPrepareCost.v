(** * Preparation costs for indexed joins

    Preparation charges source occurrences, bound-variable scans and every supplied relation row.
    For example, two occurrences of the same atom each prepare their own position index.
    Builds on: DatalogJoinUpdateCost and the public Map and FinSet traversal contracts. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost BaseSet BaseTrieCost.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogCost
  DatalogJoin DatalogJoinProof DatalogJoinCost DatalogJoinUpdateCost.
Import List.ListNotations Cost.Notations Join JoinProof JoinUpdateCost.
Local Open Scope N_scope.

Module JoinPrepareCost.

(** Enumeration charges physical trie paths and one extraction tick per stored tuple. *)
Theorem relation_elements_cost (rel : relation) w :
  (forall row, member row rel = true -> key_bits tuple_encoding row <= w) ->
  Cost.ticks (FinSet.elements_c (set_raw rel)) <=
    TrieCost.trie_k * (1 + N.of_nat (FinSet.size (set_raw rel)) * w) +
      N.of_nat (FinSet.size (set_raw rel)).
Proof.
  intro Hwidth; rewrite FinSet.elements_cost_equation.
  apply N.add_le_mono; [|reflexivity].
  rewrite FinSet.size_backend.
  apply (MapCost.elements_numeric_cost tuple_encoding).
  - exact (proj2_sig rel).
  - intros row [] Hget; apply Hwidth.
    unfold member; rewrite FinSet.mem_equation, Hget; reflexivity.
Qed.

(** Bound-position classification scans at most the supplied variable-occurrence inventory. *)
Theorem bound_term_cost bound t :
  Cost.ticks (bound_term_c bound t) <= N.of_nat (length bound).
Proof.
  unfold bound_term_c; destruct t as [v | c]; [|rewrite Cost.ticks_ret; lia].
  pose proof (ticks_existsb_c_le
    (fun w => Cost.ret (Nat.eqb v w)) 0 bound (fun _ => N.le_refl 0)).
  nia.
Qed.

Lemma positions_cost bound ts :
  Cost.ticks (map_c (bound_term_c bound) ts) <=
    N.of_nat (length ts) * (N.of_nat (length bound) + 1).
Proof.
  rewrite ticks_map_c; apply traversal_bound_on.
  intros t _; apply bound_term_cost.
Qed.

Lemma key_terms_cost bound ts :
  Cost.ticks (filter_c (bound_term_c bound) ts) <=
    N.of_nat (length ts) * (N.of_nat (length bound) + 1).
Proof.
  rewrite ticks_filter_c; apply traversal_bound_on.
  intros t _; apply bound_term_cost.
Qed.

(** Variable collection retains one traversal tick per source term occurrence. *)
Theorem variables_cost ts : Cost.ticks (variables_c ts) = N.of_nat (length ts).
Proof.
  unfold variables_c; rewrite ticks_filter_map_c.
  induction ts as [|t ts IH]; cbn [fold_right length].
  - reflexivity.
  - rewrite Cost.ticks_ret, Nat2N.inj_succ; lia.
Qed.

Lemma variables_length ts : (length (variables ts) <= length ts)%nat.
Proof.
  rewrite variables_equation; apply filter_map_length.
Qed.

(** Duties follow the source recursion and refer only to primitive callbacks and selected keys. *)
Fixpoint prepare_primitives {P} bound (ps : list (atom P))
    (env : P -> Cost.t relation) (a b : nat) (r c s e w : N) : Prop :=
  match ps with
  | [] => True
  | atom :: rest =>
    (length (args atom) <= a)%nat /\
    (length bound <= b)%nat /\
    Cost.ticks (env (pred atom)) <= c /\
    N.of_nat (FinSet.size (set_raw (Cost.value (env (pred atom))))) <= r /\
    (forall row, member row (Cost.value (env (pred atom))) = true ->
      key_bits tuple_encoding row <= s) /\
    (forall row key, member row (Cost.value (env (pred atom))) = true ->
      select (map (bound_term bound) (args atom)) row = Some key ->
      Cost.ticks (encode_c tuple_encoding key) <= e /\ key_bits tuple_encoding key <= w) /\
    prepare_primitives (variables (args atom) ++ bound) rest env a b r c s e w
  end.

(** The preparation coefficient retains both classification passes and full relation enumeration. *)
Definition prepare_unit_cost (a b : nat) r c s e w :=
  2 + 2 * N.of_nat a * (N.of_nat b + 1) + c +
    TrieCost.trie_k * (1 + r * s) + r +
    r * (4 + N.of_nat a + 2 * (e + w)) + 2 * N.of_nat a.

Lemma prepare_node_cost {P} bound (atom : atom P) env a b r c s e w :
  (length (args atom) <= a)%nat ->
  (length bound <= b)%nat ->
  Cost.ticks (env (pred atom)) <= c ->
  N.of_nat (FinSet.size (set_raw (Cost.value (env (pred atom))))) <= r ->
  (forall row, member row (Cost.value (env (pred atom))) = true ->
    key_bits tuple_encoding row <= s) ->
  (forall row key, member row (Cost.value (env (pred atom))) = true ->
    select (map (bound_term bound) (args atom)) row = Some key ->
    Cost.ticks (encode_c tuple_encoding key) <= e /\ key_bits tuple_encoding key <= w) ->
  Cost.ticks (map_c (bound_term_c bound) (args atom)) +
    Cost.ticks (filter_c (bound_term_c bound) (args atom)) +
    Cost.ticks (env (pred atom)) +
    Cost.ticks (FinSet.elements_c (set_raw (Cost.value (env (pred atom))))) +
    Cost.ticks (extend_index_c (map (bound_term bound) (args atom))
      (FinSet.elements (set_raw (Cost.value (env (pred atom))))) Map.empty) +
    Cost.ticks (variables_c (args atom)) +
    Cost.ticks (app_c (variables (args atom)) bound) + 2 <=
      prepare_unit_cost a b r c s e w.
Proof.
  intros Hargs Hbound Henv Hrows Hstored Hkeys.
  pose proof (positions_cost bound (args atom)) as Hpositions.
  pose proof (key_terms_cost bound (args atom)) as Hterms.
  pose proof (relation_elements_cost _ s Hstored) as Helements.
  assert (Hextend : Cost.ticks (extend_index_c (map (bound_term bound) (args atom))
    (FinSet.elements (set_raw (Cost.value (env (pred atom))))) Map.empty) <=
      r * (4 + N.of_nat a + 2 * (e + w))).
  { eapply N.le_trans; [apply (extend_index_cost _ _ _ e w) |].
    - intros row key Hrow Hkey; apply (Hkeys row key); [|exact Hkey].
      unfold member; apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws).
      + exact (proj2_sig (Cost.value (env (pred atom)))).
      + exact Hrow.
    - rewrite length_map, <- FinSet.size_elements.
      apply N.mul_le_mono; [exact Hrows |].
      pose proof (nat_N_le _ _ Hargs); lia. }
  rewrite variables_cost, ticks_app_c.
  pose proof (nat_N_le _ _ Hargs) as HargsN.
  pose proof (nat_N_le _ _ Hbound) as HboundN.
  pose proof (nat_N_le _ _ (variables_length (args atom))) as Hvariables.
  assert (Hclassify : N.of_nat (length (args atom)) *
    (N.of_nat (length bound) + 1) <= N.of_nat a * (N.of_nat b + 1)).
  { apply N.mul_le_mono; [exact HargsN | lia]. }
  assert (Henumerate : Cost.ticks (FinSet.elements_c
    (set_raw (Cost.value (env (pred atom))))) <=
    TrieCost.trie_k * (1 + r * s) + r).
  { eapply N.le_trans; [exact Helements |].
    apply N.add_le_mono; [|exact Hrows].
    apply N.mul_le_mono; [reflexivity |].
    apply N.add_le_mono; [reflexivity |].
    apply N.mul_le_mono; [exact Hrows | reflexivity]. }
  unfold prepare_unit_cost; lia.
Qed.

Lemma prepare_from_cost {P} bound (ps : list (atom P)) env a b r c s e w :
  prepare_primitives bound ps env a b r c s e w ->
  Cost.ticks (prepare_from_c bound ps env) <=
    N.of_nat (length ps) * prepare_unit_cost a b r c s e w.
Proof.
  revert bound; induction ps as [|atom ps IH]; intros bound Hprimitives.
  - change (0 <= 0); lia.
  - destruct Hprimitives as [Ha [Hb [Hc [Hr [Hs [Hkeys Htail]]]]]].
    pose proof (prepare_node_cost bound atom env a b r c s e w Ha Hb Hc Hr Hs Hkeys)
      as Hnode.
    specialize (IH (variables (args atom) ++ bound) Htail).
    cbn [prepare_from_c]; repeat rewrite Cost.ticks_bind.
    rewrite !Cost.ticks_step, Cost.ticks_ret.
    rewrite value_map_c, value_app_c.
    fold (variables (args atom)).
    change (1 + (Cost.ticks (map_c (bound_term_c bound) (args atom)) +
      (Cost.ticks (filter_c (bound_term_c bound) (args atom)) +
      (1 + (Cost.ticks (env (pred atom)) +
      (Cost.ticks (FinSet.elements_c (set_raw (Cost.value (env (pred atom))))) +
      (Cost.ticks (extend_index_c (map (bound_term bound) (args atom))
        (FinSet.elements (set_raw (Cost.value (env (pred atom))))) Map.empty) +
      (Cost.ticks (variables_c (args atom)) +
      (Cost.ticks (app_c (variables (args atom)) bound) +
      (Cost.ticks (prepare_from_c (variables (args atom) ++ bound) ps env) + 0))))))))) <=
        N.of_nat (length (atom :: ps)) * prepare_unit_cost a b r c s e w).
    cbn [length]; rewrite Nat2N.inj_succ, N.mul_succ_l.
    lia.
Qed.

(** Preparing a plan is linear in the listed atom inventory at its explicit primitive coefficient. *)
Theorem join_prepare_cost {P} (prog : program P) ps env a b r c s e w :
  prepare_primitives [] ps env a b r c s e w ->
  Cost.ticks (prepare_c prog ps env) <=
    N.of_nat (length ps) * prepare_unit_cost a b r c s e w.
Proof.
  apply prepare_from_cost.
Qed.

(** Varying inventories and primitive budgets give the same preparation family bound. *)
Theorem join_prepare_bigO {X P} (prog : X -> program P)
    (ps : X -> list (atom P)) (env : X -> P -> Cost.t relation)
    (a b : X -> nat) (r c s e w : X -> N) :
  (forall x, prepare_primitives [] (ps x) (env x)
    (a x) (b x) (r x) (c x) (s x) (e x) (w x)) ->
  bigO (fun x => N.of_nat (length (ps x)) *
    prepare_unit_cost (a x) (b x) (r x) (c x) (s x) (e x) (w x))
    (fun x => Cost.ticks (prepare_c (prog x) (ps x) (env x))).
Proof.
  intro Hprimitives; exists 1; intro x.
  pose proof (join_prepare_cost (prog x) (ps x) (env x)
    (a x) (b x) (r x) (c x) (s x) (e x) (w x) (Hprimitives x)); nia.
Qed.

End JoinPrepareCost.
Import JoinPrepareCost.
