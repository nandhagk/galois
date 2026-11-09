(** * Primitive numeric costs for PRE family discovery

    Setup prices follow from input counts, maximum arity, binary widths and primitive callbacks.
    For example, enumeration charges both outgoing graph readers and the copied edge occurrences.
    Builds on: AnalysesSsaPreFamily, BaseMapCost and the owning framework traversal contracts. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseMapCost BaseTrieCost BaseInternCost.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Framework Require Import FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily.
Import List.ListNotations Cost.Notations.
Open Scope N_scope.

Module PreFamilyCost.

Definition power_limit n arity := N.pow (1 + n) (N.of_nat arity).

Local Lemma power_zero n : power_limit n 0 = 1.
Proof.
  reflexivity.
Qed.

Local Lemma power_succ n a : power_limit n (S a) = (1 + n) * power_limit n a.
Proof.
  unfold power_limit; rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity.
Qed.

Local Lemma power_positive n a : 1 <= power_limit n a.
Proof.
  induction a; [reflexivity|rewrite power_succ; nia].
Qed.

Local Lemma power_monotone n a b : (a <= b)%nat -> power_limit n a <= power_limit n b.
Proof.
  revert a; induction b as [|b IH]; intros [|a] Hle.
  - reflexivity.
  - lia.
  - apply power_positive.
  - rewrite !power_succ; specialize (IH a ltac:(lia)); nia.
Qed.

Local Lemma width_monotone a b :
  a <= b -> PreFamily.binary_width a <= PreFamily.binary_width b.
Proof.
  destruct a as [|a], b as [|b]; cbn [PreFamily.binary_width]; intro Hle; try lia.
  apply InternCost.bits_monotone; exact Hle.
Qed.

Local Lemma multiply_bound cap a b :
  a <= cap -> b <= cap ->
  Cost.ticks (PreFamily.multiply_c a b) <=
    1 + PreFamily.binary_width cap * PreFamily.binary_width cap.
Proof.
  intros Ha Hb; rewrite PreFamily.multiply_cost.
  pose proof (width_monotone a cap Ha); pose proof (width_monotone b cap Hb).
  destruct b; cbn [PreFamily.binary_width] in *; nia.
Qed.

Local Lemma power_fold_bound {X} n cap (xs : list X) :
  n <= cap ->
  forall p, p * power_limit n (length xs) <= cap ->
    Cost.ticks (fold_left_c (fun total (_ : X) => PreFamily.multiply_c total n) xs p) <=
      N.of_nat (length xs) * (2 + PreFamily.binary_width cap * PreFamily.binary_width cap).
Proof.
  intro Hn; induction xs as [|x rest IH]; intros p Hp.
  - rewrite ticks_fold_left_c_nil; reflexivity.
  - rewrite ticks_fold_left_c_cons, PreFamily.multiply_value.
    cbn [length] in Hp |- *; rewrite power_succ in Hp.
    pose proof (power_positive n (length rest)) as Hpositive.
    assert (Hpcap : p <= cap) by nia.
    assert (Hnext : p * n * power_limit n (length rest) <= cap) by nia.
    pose proof (multiply_bound cap p n Hpcap Hn) as Hmultiply.
    specialize (IH (p * n) Hnext); rewrite Nat2N.inj_succ; nia.
Qed.

(** Exponent construction charges each operand-list cell and bounded-width multiplication. *)
Theorem power_cost {X} n cap arity (xs : list X) :
  n <= cap -> (length xs <= arity)%nat -> power_limit n arity <= cap ->
    Cost.ticks (PreFamily.power_c n xs) <=
      N.of_nat arity * (2 + PreFamily.binary_width cap * PreFamily.binary_width cap).
Proof.
  intros Hn Harity Hcap.
  pose proof (power_monotone n (length xs) arity Harity) as Hpower.
  pose proof (power_fold_bound n cap xs Hn 1 ltac:(nia)) as Hcost.
  unfold PreFamily.power_c; nia.
Qed.

Section Family.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition seeds := N.of_nat (length (Pre.seeds (Pre.input c))).
Definition values := N.of_nat (length (Pre.values (Pre.input c))).
Definition edges := N.of_nat (length (Cfg.edges (Pre.block_cfg c))).
Definition nodes := N.of_nat (length (Graph.nodes (Pre.bg c))).

(** This input-derived magnitude covers every bound-construction arithmetic operand. *)
Definition arithmetic_limit arity :=
  1 + seeds + values + edges + (1 + seeds) * power_limit values arity * (1 + edges).
Definition width arity := PreFamily.binary_width (arithmetic_limit arity).

(** The setup bound depends only on input counts, maximum arity and primitive callback budgets. *)
Definition setup_bound arity operand_price outgoing_price :=
  nodes * (2 + outgoing_price) + 2 * edges + seeds + values +
  seeds * (2 + operand_price + N.of_nat arity * (2 + width arity * width arity) +
    2 * width arity) + 1 + width arity * width arity + 5 * width arity.

Local Definition bound_step seed total :=
  Cost.step ;;
  let* operands := Pre.operands_c (Pre.input c) seed in
  let* choices := PreFamily.power_c values operands in PreFamily.add_c choices total.

Local Lemma power_numeric n a :
  N.pow n (N.of_nat a) <= power_limit n a.
Proof.
  induction a; [reflexivity|].
  unfold power_limit in *; rewrite Nat2N.inj_succ, !N.pow_succ_r'; nia.
Qed.

Local Lemma bound_fold_value arity :
  forall inputs,
    (forall u, In u inputs -> (length (Pre.operands c u) <= arity)%nat) ->
    Cost.value (fold_right_c bound_step 0 inputs) <=
      N.of_nat (length inputs) * power_limit values arity.
Proof.
  intro inputs; induction inputs as [|seed rest IH]; intro Hlength; [reflexivity|].
  rewrite value_fold_right_c; cbn [fold_right]; unfold bound_step at 1.
  rewrite !Cost.value_bind, PreFamily.add_value, PreFamily.power_value.
  fold (Pre.operands c seed).
  pose proof (power_numeric values (length (Pre.operands c seed))) as Hnumeric.
  pose proof (power_monotone values (length (Pre.operands c seed)) arity
    (Hlength seed (or_introl eq_refl))) as Hpower.
  specialize (IH (fun u Hu => Hlength u (or_intror Hu))).
  rewrite value_fold_right_c in IH; cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

Local Lemma bound_step_cost arity operand_price seed total :
  (length (Pre.operands c seed) <= arity)%nat ->
  Cost.ticks (Pre.operands_c (Pre.input c) seed) <= operand_price ->
  total <= seeds * power_limit values arity ->
  Cost.ticks (bound_step seed total) <=
    1 + operand_price + N.of_nat arity * (2 + width arity * width arity) + 2 * width arity.
Proof.
  intros Harity Hoperand Htotal.
  pose proof (power_positive values arity) as Hpositive.
  assert (Hlimit : power_limit values arity <= arithmetic_limit arity) by
    (unfold arithmetic_limit; nia).
  assert (Hvalues : values <= arithmetic_limit arity) by (unfold arithmetic_limit; nia).
  pose proof (power_cost values (arithmetic_limit arity) arity (Pre.operands c seed)
    Hvalues Harity Hlimit) as Hpower.
  pose proof (power_numeric values (length (Pre.operands c seed))) as Hnumeric.
  pose proof (power_monotone values (length (Pre.operands c seed)) arity Harity) as Hmono.
  pose proof (width_monotone total (arithmetic_limit arity)
    ltac:(unfold arithmetic_limit; nia)) as Htotal_width.
  pose proof (width_monotone (N.pow values (N.of_nat (length (Pre.operands c seed))))
    (arithmetic_limit arity) ltac:(nia)) as Hchoice_width.
  unfold bound_step; autorewrite with galois_cost.
  rewrite PreFamily.power_value, PreFamily.add_cost; fold (Pre.operands c seed).
  unfold width in *; nia.
Qed.

Local Lemma bound_fold_cost arity operand_price :
  forall inputs, incl inputs (Pre.seeds (Pre.input c)) ->
    (length inputs <= length (Pre.seeds (Pre.input c)))%nat ->
    (forall u, In u (Pre.seeds (Pre.input c)) ->
      (length (Pre.operands c u) <= arity)%nat /\
      Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price) ->
    Cost.ticks (fold_right_c bound_step 0 inputs) <=
      N.of_nat (length inputs) *
        (2 + operand_price + N.of_nat arity * (2 + width arity * width arity) + 2 * width arity).
Proof.
  intro inputs; induction inputs as [|seed rest IH]; intros Hsub Hlength Hduties.
  - rewrite ticks_fold_right_c_nil; reflexivity.
  - rewrite ticks_fold_right_c_cons.
    pose proof (Hduties seed (Hsub seed (or_introl eq_refl))) as [Harity Hoperand].
    assert (Hrest : incl rest (Pre.seeds (Pre.input c))) by
      (intros u Hu; apply Hsub; now right).
    specialize (IH Hrest ltac:(cbn [length] in Hlength; lia) Hduties).
    assert (Hcount : N.of_nat (length rest) <= seeds).
    { unfold seeds; cbn [length] in Hlength; lia. }
    assert (Hrest_value := bound_fold_value arity rest
      (fun u Hu => proj1 (Hduties u (Hrest u Hu)))).
    pose proof (bound_step_cost arity operand_price seed
      (Cost.value (fold_right_c bound_step 0 rest)) Harity Hoperand ltac:(nia)) as Hstep.
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** The capacity bound itself is derived from supplied seeds and their maximum operand arity. *)
Theorem capacity_bound arity :
  (forall u, In u (Pre.seeds (Pre.input c)) -> (length (Pre.operands c u) <= arity)%nat) ->
  PreFamily.family_bound c <= seeds * power_limit values arity.
Proof.
  intro Hduties; unfold PreFamily.family_bound, PreFamily.family_bound_c.
  rewrite Cost.value_bind; fold (PreFamily.count (Pre.values (Pre.input c))).
  rewrite PreFamily.count_value; fold values.
  exact (bound_fold_value arity _ Hduties).
Qed.

(** Computing the capacity charges the values scan and every seed's operand and arithmetic work. *)
Theorem capacity_cost arity operand_price :
  (forall u, In u (Pre.seeds (Pre.input c)) ->
    (length (Pre.operands c u) <= arity)%nat /\
    Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price) ->
  Cost.ticks (PreFamily.family_bound_c c) <= values +
    seeds * (2 + operand_price + N.of_nat arity * (2 + width arity * width arity) + 2 * width arity).
Proof.
  intro Hduties; unfold PreFamily.family_bound_c.
  rewrite Cost.ticks_bind, PreFamily.count_cost.
  fold (PreFamily.count (Pre.values (Pre.input c))); rewrite PreFamily.count_value; fold values.
  pose proof (bound_fold_cost arity operand_price (Pre.seeds (Pre.input c))
    (incl_refl _) (le_n _) Hduties) as Hcost.
  unfold bound_step in Hcost; unfold seeds; nia.
Qed.

Local Lemma setup_cost_relative arity operand_price outgoing_price :
  (forall u, In u (Pre.seeds (Pre.input c)) ->
    (length (Pre.operands c u) <= arity)%nat /\
    Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price) ->
  Cost.ticks (fw_edges_c (Pre.block_cfg c)) <= nodes * (2 + outgoing_price) + edges ->
  Cost.ticks (PreFamily.setup_c c) <= setup_bound arity operand_price outgoing_price.
Proof.
  intros Hduties Hedges.
  pose proof (capacity_bound arity (fun u Hu => proj1 (Hduties u Hu))) as Hcapacity.
  pose proof (capacity_cost arity operand_price Hduties) as Hcost.
  pose proof (power_positive values arity) as Hpositive.
  assert (Hcapacity_limit : PreFamily.family_bound c <= arithmetic_limit arity) by
    (unfold arithmetic_limit; nia).
  assert (Hdegree_limit : 1 + edges <= arithmetic_limit arity) by
    (unfold arithmetic_limit; nia).
  assert (Hroot_limit : seeds <= arithmetic_limit arity) by (unfold arithmetic_limit; nia).
  assert (Hcredit_limit : PreFamily.family_bound c * (1 + edges) <= arithmetic_limit arity) by
    (unfold arithmetic_limit; nia).
  assert (Hfuel_limit : seeds + PreFamily.family_bound c * (1 + edges) <= arithmetic_limit arity) by
    (unfold arithmetic_limit; nia).
  pose proof (multiply_bound (arithmetic_limit arity)
    (PreFamily.family_bound c) (1 + edges) Hcapacity_limit Hdegree_limit) as Hmultiply.
  pose proof (width_monotone 1 (arithmetic_limit arity) ltac:(unfold arithmetic_limit; nia)) as Hone.
  pose proof (width_monotone edges (arithmetic_limit arity) ltac:(nia)) as Hdegree.
  pose proof (width_monotone seeds (arithmetic_limit arity) Hroot_limit) as Hroots.
  pose proof (width_monotone _ _ Hcredit_limit) as Hcredit.
  pose proof (width_monotone _ _ Hfuel_limit) as Hfuel.
  unfold PreFamily.setup_c; rewrite !Cost.ticks_bind, fw_edges_value.
  fold (PreFamily.count (Pre.seeds (Pre.input c))).
  fold (PreFamily.count (Cfg.edges (Pre.block_cfg c))).
  fold (PreFamily.family_bound c).
  rewrite !PreFamily.count_value; fold seeds edges.
  rewrite !PreFamily.count_cost, !PreFamily.add_value, PreFamily.multiply_value,
    !PreFamily.add_cost, PreFamily.bits_cost, Cost.ticks_ret.
  fold seeds edges; unfold setup_bound, width in *; nia.
Qed.

(** Canonical family enumeration is bounded by family cardinality and primitive stored-key width. *)
Theorem materialization_cost (key_price : BinNums.N) :
  Pre.laws c ->
  (forall u, PreFamily.in_family c u -> key_bits (Pre.eu (Pre.keys c)) u <= key_price) ->
  Cost.ticks (FinSet.elements_c (snd (PreFamily.result_state
    (Cost.value (PreFamily.discover_state_c c))))) <=
    TrieCost.trie_k * (1 + PreFamily.discovered_count c * key_price) + PreFamily.discovered_count c.
Proof.
  intros Hlaw Hkeys.
  pose proof (PreFamily.discovered_valid c Hlaw) as [Hwf [Hfamily Hpending]].
  set (final := snd (PreFamily.result_state (Cost.value (PreFamily.discover_state_c c)))) in *.
  assert (Hsize : N.of_nat (Map.size final) = PreFamily.discovered_count c).
  { rewrite <- FinSet.size_backend, FinSet.size_elements.
    unfold PreFamily.discovered_count; rewrite PreFamily.universe_state; reflexivity. }
  pose proof (MapCost.elements_numeric_cost (Pre.eu (Pre.keys c)) final key_price Hwf) as Hmap.
  assert (Hstored : forall u v, Map.get (Pre.eu (Pre.keys c)) u final = Some v ->
    key_bits (Pre.eu (Pre.keys c)) u <= key_price).
  { intros u [] Hget; apply Hkeys.
    apply (proj1 (Forall_forall _ _) Hfamily u).
    apply (FinSet.elements_spec _ (Pre.eu_laws c (Pre.graphs c Hlaw))); [exact Hwf|].
    apply FinSet.mem_spec; exact Hget. }
  specialize (Hmap Hstored); rewrite Hsize in Hmap.
  rewrite FinSet.elements_cost_equation, FinSet.size_backend, Hsize; lia.
Qed.

(** Setup is bounded by primitive outgoing and operand callbacks, including both input scans. *)
Theorem setup_cost arity operand_price outgoing_price :
  (forall u, In u (Pre.seeds (Pre.input c)) ->
    (length (Pre.operands c u) <= arity)%nat /\
    Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price) ->
  (forall n, In n (Graph.nodes (Pre.bg c)) ->
    Cost.ticks (Graph.out_c (Pre.bg c) n) <= outgoing_price) ->
  Cost.ticks (PreFamily.setup_c c) <= setup_bound arity operand_price outgoing_price.
Proof.
  intros Hoperands Hout; apply (setup_cost_relative arity operand_price outgoing_price Hoperands).
  exact (fw_edges_cost (Pre.block_cfg c) outgoing_price Hout).
Qed.

Local Lemma fuel_width_bound arity :
  (forall u, In u (Pre.seeds (Pre.input c)) -> (length (Pre.operands c u) <= arity)%nat) ->
  PreFamily.fuel_width c <= width arity.
Proof.
  intro Harity; pose proof (capacity_bound arity Harity) as Hcapacity.
  pose proof (power_positive values arity) as Hpositive.
  unfold PreFamily.fuel_width; rewrite PreFamily.setup_equation; cbn [snd].
  fold seeds edges.
  change (PreFamily.binary_width (N.pos (N.succ_pos
    (seeds + PreFamily.family_bound c * (1 + edges)))) <= width arity).
  rewrite N.succ_pos_spec; apply width_monotone; unfold arithmetic_limit; nia.
Qed.

(** Primitive prices and maximum arity are input duties, independent of setup or result prices. *)
Record prices := Prices {
  max_arity : nat;
  key_price : BinNums.N;
  translation_price : BinNums.N;
  operand_price : BinNums.N;
  outgoing_price : BinNums.N
}.

(** The complete numeric bound prices setup, memoized discovery and canonical output enumeration. *)
Definition discovery_bound (b : prices) family_size :=
  setup_bound (max_arity b) (operand_price b) (outgoing_price b) +
  TrieCost.trie_k * (1 + family_size * key_price b) + family_size +
  family_size * (key_price b + edges * (2 + translation_price b) + 1 +
    edges * (key_price b + 3)) + seeds * (key_price b + 2) + 2 * width (max_arity b).

Local Lemma discovery_bound_monotone b small large :
  small <= large -> discovery_bound b small <= discovery_bound b large.
Proof.
  intro Hle.
  assert (Hkeys : small * key_price b <= large * key_price b) by nia.
  assert (Hmap : TrieCost.trie_k * (1 + small * key_price b) <=
    TrieCost.trie_k * (1 + large * key_price b)) by nia.
  set (per_member := key_price b + edges * (2 + translation_price b) + 1 +
    edges * (key_price b + 3)).
  assert (Hloop : small * per_member <= large * per_member) by nia.
  unfold discovery_bound; fold per_member; lia.
Qed.

(** Actual discovered-family work has a primitive numeric bound with no owned-operation prices. *)
Theorem discover_cost (b : prices) :
  Pre.laws c ->
  (forall u, PreFamily.in_family c u ->
    1 + Cost.ticks (encode_c (Pre.eu (Pre.keys c)) u) +
      key_bits (Pre.eu (Pre.keys c)) u <= key_price b) ->
  (forall be u, In be (Cfg.edges (Pre.block_cfg c)) -> PreFamily.in_family c u ->
    Cost.ticks (Pre.translate_c (Pre.input c) be u) <= translation_price b) ->
  (forall u, In u (Pre.seeds (Pre.input c)) ->
    (length (Pre.operands c u) <= max_arity b)%nat /\
    Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price b) ->
  (forall n, In n (Graph.nodes (Pre.bg c)) ->
    Cost.ticks (Graph.out_c (Pre.bg c) n) <= outgoing_price b) ->
  Cost.ticks (PreFamily.discover_c c) <= discovery_bound b (PreFamily.discovered_count c).
Proof.
  intros Hlaw Hkeys Htranslate Hoperands Hout.
  pose proof (PreFamily.discover_relative_cost c
    (PreFamily.Budgets (key_price b) (translation_price b)) Hlaw Hkeys Htranslate) as Hloop.
  pose proof (setup_cost (max_arity b) (operand_price b) (outgoing_price b) Hoperands Hout) as Hsetup.
  pose proof (materialization_cost (key_price b) Hlaw
    (fun u Hu => ltac:(pose proof (Hkeys u Hu); lia))) as Hmaterialize.
  pose proof (fuel_width_bound (max_arity b) (fun u Hu => proj1 (Hoperands u Hu))) as Hwidth.
  unfold PreFamily.key_budget, PreFamily.callback_budget in Hloop.
  unfold PreFamily.seed_count, PreFamily.edge_count in Hloop; fold seeds edges in Hloop.
  unfold discovery_bound; nia.
Qed.

(** Input signature capacity gives a second bound independent of the produced family enumeration. *)
Theorem discover_input_cost (b : prices) :
  Pre.laws c ->
  (forall u, PreFamily.in_family c u ->
    1 + Cost.ticks (encode_c (Pre.eu (Pre.keys c)) u) +
      key_bits (Pre.eu (Pre.keys c)) u <= key_price b) ->
  (forall be u, In be (Cfg.edges (Pre.block_cfg c)) -> PreFamily.in_family c u ->
    Cost.ticks (Pre.translate_c (Pre.input c) be u) <= translation_price b) ->
  (forall u, In u (Pre.seeds (Pre.input c)) ->
    (length (Pre.operands c u) <= max_arity b)%nat /\
    Cost.ticks (Pre.operands_c (Pre.input c) u) <= operand_price b) ->
  (forall n, In n (Graph.nodes (Pre.bg c)) ->
    Cost.ticks (Graph.out_c (Pre.bg c) n) <= outgoing_price b) ->
  Cost.ticks (PreFamily.discover_c c) <=
    discovery_bound b (seeds * power_limit values (max_arity b)).
Proof.
  intros Hlaw Hkeys Htranslate Hoperands Hout.
  pose proof (discover_cost b Hlaw Hkeys Htranslate Hoperands Hout) as Hcost.
  pose proof (capacity_bound (max_arity b) (fun u Hu => proj1 (Hoperands u Hu))) as Hcapacity.
  destruct (PreFamily.universe_exact c Hlaw) as [Hnodup Hexact].
  assert (Hfamily : Forall (PreFamily.in_family c) (PreFamily.universe c)).
  { apply Forall_forall; intros u Hu; apply Hexact; exact Hu. }
  pose proof (PreFamily.family_cardinal c Hlaw _ Hnodup Hfamily) as Hcardinal.
  eapply N.le_trans; [exact Hcost|]; apply discovery_bound_monotone.
  unfold PreFamily.discovered_count; lia.
Qed.

End Family.

Section Uniform.
Context {X B BE N E V K G C U : Type}.
Variable contexts : X -> Pre.ctx B BE N E V K G C U.
Variable budgets : X -> prices.

Hypothesis Hlaws : forall x, Pre.laws (contexts x).
Hypothesis Hkeys : forall x u, PreFamily.in_family (contexts x) u ->
  1 + Cost.ticks (encode_c (Pre.eu (Pre.keys (contexts x))) u) +
    key_bits (Pre.eu (Pre.keys (contexts x))) u <= key_price (budgets x).
Hypothesis Htranslate : forall x be u,
  In be (Cfg.edges (Pre.block_cfg (contexts x))) -> PreFamily.in_family (contexts x) u ->
  Cost.ticks (Pre.translate_c (Pre.input (contexts x)) be u) <= translation_price (budgets x).
Hypothesis Hoperands : forall x u, In u (Pre.seeds (Pre.input (contexts x))) ->
  (length (Pre.operands (contexts x) u) <= max_arity (budgets x))%nat /\
  Cost.ticks (Pre.operands_c (Pre.input (contexts x)) u) <= operand_price (budgets x).
Hypothesis Hout : forall x n, In n (Graph.nodes (Pre.bg (contexts x))) ->
  Cost.ticks (Graph.out_c (Pre.bg (contexts x)) n) <= outgoing_price (budgets x).

(** One constant bounds complete discovery uniformly over varying contexts and primitive prices. *)
Theorem discover_bigO :
  bigO
    (fun x => discovery_bound (contexts x) (budgets x) (PreFamily.discovered_count (contexts x)))
    (fun x => Cost.ticks (PreFamily.discover_c (contexts x))).
Proof.
  exists 1; intro x.
  pose proof (discover_cost (contexts x) (budgets x)
    (Hlaws x) (Hkeys x) (Htranslate x) (Hoperands x) (Hout x)) as Hbound.
  nia.
Qed.

(** The input-capacity bound also holds uniformly when presentations and all primitive prices vary. *)
Theorem discover_input_bigO :
  bigO
    (fun x => discovery_bound (contexts x) (budgets x)
      (seeds (contexts x) * power_limit (values (contexts x)) (max_arity (budgets x))))
    (fun x => Cost.ticks (PreFamily.discover_c (contexts x))).
Proof.
  exists 1; intro x.
  pose proof (discover_input_cost (contexts x) (budgets x)
    (Hlaws x) (Hkeys x) (Htranslate x) (Hoperands x) (Hout x)) as Hbound.
  nia.
Qed.

End Uniform.

End PreFamilyCost.
