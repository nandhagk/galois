(** * Reference firing cost composition

    Bounds retain relation enumeration, nested binding probes and output construction.
    For example, each positive atom can multiply the number of candidate bindings by its row count.
    Builds on: DatalogFire and CostList. *)

From Stdlib Require Import List PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

(** Binding lookup charges at most one tick per stored variable assignment. *)
Theorem binding_get_cost b v :
  Cost.ticks (binding_get_c b v) <= N.of_nat (length b).
Proof.
  induction b as [|[w c] rest IH]; [reflexivity |].
  cbn [binding_get_c length]; rewrite Cost.ticks_bind, Cost.ticks_step, Nat2N.inj_succ.
  destruct (Nat.eqb v w); rewrite ?Cost.ticks_ret; lia.
Qed.

Lemma nat_N_le a b : (a <= b)%nat -> N.of_nat a <= N.of_nat b.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)), Hle.
Qed.

Lemma traversal_bound_on {A} (f : A -> N) k xs :
  (forall x, In x xs -> f x <= k) ->
  fold_right (fun x n => 1 + f x + n) 0 xs <= N.of_nat (length xs) * (k + 1).
Proof.
  induction xs as [|x xs IH]; intro H; cbn [fold_right length]; [nia |].
  rewrite Nat2N.inj_succ.
  assert (Hx := H x (or_introl eq_refl)).
  assert (Htail : fold_right (fun x n => 1 + f x + n) 0 xs <=
    N.of_nat (length xs) * (k + 1)).
  { apply IH; intros y Hy; apply H; now right. }
  nia.
Qed.

Lemma filter_map_length {A B} (f : A -> option B) xs :
  (length (filter_map f xs) <= length xs)%nat.
Proof.
  unfold filter_map; induction xs as [|x xs IH]; cbn [fold_right length]; [lia |].
  destruct (f x); cbn [length]; lia.
Qed.

Lemma fold_right_bound_on {A B} (f : A -> B -> Cost.t B) k xs init :
  (forall x b, In x xs -> Cost.ticks (f x b) <= k) ->
  Cost.ticks (fold_right_c f init xs) <= N.of_nat (length xs) * (k + 1).
Proof.
  induction xs as [|x xs IH]; intro H; [change (0 <= 0); lia |].
  rewrite ticks_fold_right_c_cons.
  specialize (IH (fun y b Hy => H y b (or_intror Hy))).
  pose proof (H x (Cost.value (fold_right_c f init xs)) (or_introl eq_refl)).
  cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

Lemma filter_length_bound {A} (f : A -> bool) xs :
  (length (filter f xs) <= length xs)%nat.
Proof.
  induction xs as [|x xs IH]; cbn [filter length]; [lia |].
  destruct (f x); cbn [length]; lia.
Qed.

Lemma bind_term_length b t c b' :
  bind_term b t c = Some b' -> (length b' <= S (length b))%nat.
Proof.
  rewrite bind_term_equation; destruct t as [v | d].
  - destruct (binding_get b v) as [d |]; [destruct (Pos.eqb c d) |];
      intro Hsome; try discriminate; injection Hsome as <-; cbn [length]; lia.
  - destruct (Pos.eqb c d); intro Hsome; [injection Hsome as <-; lia | discriminate].
Qed.

(** Matching a term charges the binding lookup and the actual positive component width. *)
Theorem bind_term_cost b t c v :
  N.pos (Pos.size c) <= v ->
  Cost.ticks (bind_term_c b t c) <= 1 + N.of_nat (length b) + v.
Proof.
  intro Hbits; unfold bind_term_c; rewrite Cost.ticks_bind, Cost.ticks_step.
  destruct t as [x | d].
  - rewrite Cost.ticks_bind; fold (binding_get b x).
    pose proof (binding_get_cost b x) as Hget.
    destruct (binding_get b x) as [d |].
    + rewrite Cost.ticks_bind; pose proof (proj1 (positive_eqb_cost c d)).
      destruct (Cost.value (positive_eqb_c c d)); rewrite Cost.ticks_ret; lia.
    + rewrite Cost.ticks_ret; lia.
  - rewrite Cost.ticks_bind; pose proof (proj1 (positive_eqb_cost c d)).
    destruct (Cost.value (positive_eqb_c c d)); rewrite Cost.ticks_ret; lia.
Qed.

(** Row matching retains term count, maximum reached binding length and row-component widths. *)
Theorem bind_terms_cost ts row b h v :
  (length b + length ts <= h)%nat ->
  (forall c, In c row -> N.pos (Pos.size c) <= v) ->
  Cost.ticks (bind_terms_c ts row b) <=
    (N.of_nat (length ts) + 1) * (2 + N.of_nat h + v).
Proof.
  revert row b; induction ts as [|t ts IH]; intros [|c row] b Hlength Hbits.
  - cbn [bind_terms_c length]; autorewrite with galois_cost; nia.
  - cbn [bind_terms_c length]; autorewrite with galois_cost; nia.
  - cbn [bind_terms_c length]; autorewrite with galois_cost; nia.
  - cbn [bind_terms_c]; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
    pose proof (bind_term_cost b t c v (Hbits c (or_introl eq_refl))) as Hterm.
    pose proof (nat_N_le (length b) h ltac:(cbn [length] in Hlength; lia)) as Hlen.
    fold (bind_term b t c); destruct (bind_term b t c) as [b' |] eqn:Hbind.
    + pose proof (bind_term_length _ _ _ _ Hbind) as Hnext.
      specialize (IH row b' ltac:(cbn [length] in Hlength; lia)
        (fun d Hd => Hbits d (or_intror Hd))).
      cbn [length]; rewrite Nat2N.inj_succ; nia.
    + rewrite Cost.ticks_ret; cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Instantiation charges the term traversal and every partial-valuation lookup. *)
Theorem instantiate_cost b ts :
  Cost.ticks (instantiate_c b ts) <=
    N.of_nat (length ts) * (1 + N.of_nat (length b)).
Proof.
  replace (1 + N.of_nat (length b)) with (N.of_nat (length b) + 1) by lia.
  unfold instantiate_c; rewrite ticks_map_c.
  apply traversal_bound_on; intros [v | c] _.
  - unfold binding_value_c; rewrite Cost.ticks_map; apply binding_get_cost.
  - rewrite Cost.ticks_ret; lia.
Qed.

Lemma forallb_bound_on {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> Cost.ticks (f x) <= k) ->
  Cost.ticks (forallb_c f xs) <= N.of_nat (length xs) * (k + 1).
Proof.
  induction xs as [|x xs IH]; intro Hbounds.
  - rewrite ticks_forallb_c_nil; reflexivity.
  - rewrite ticks_forallb_c_cons.
    specialize (IH (fun y Hy => Hbounds y (or_intror Hy))).
    pose proof (Hbounds x (or_introl eq_refl)).
    cbn [length]; rewrite Nat2N.inj_succ.
    destruct (Cost.value (f x)); nia.
Qed.

(** Negative testing retains body inventory, binding scans, callbacks and actual key budgets. *)
Theorem negative_cost {P} (r : rule P) env b a h c e w :
  (length b <= h)%nat ->
  (forall atom, In (LNeg atom) (body r) ->
    (length (args atom) <= a)%nat /\
    Cost.ticks (env (pred atom)) <= c /\
    Cost.ticks (encode_c tuple_encoding
      (map (inst (binding_value b)) (args atom))) <= e /\
    key_bits tuple_encoding (map (inst (binding_value b)) (args atom)) <= w) ->
  Cost.ticks (negative_ok_c r env b) <=
    N.of_nat (length (body r)) * (3 + N.of_nat a * (1 + N.of_nat h) + c + e + w).
Proof.
  intros Hbinding Hnegative; unfold negative_ok_c.
  replace (3 + N.of_nat a * (1 + N.of_nat h) + c + e + w) with
    ((2 + N.of_nat a * (1 + N.of_nat h) + c + e + w) + 1) by lia.
  apply forallb_bound_on; intros [atom | atom] Hatom.
  - rewrite Cost.ticks_ret; lia.
  - destruct (Hnegative atom Hatom) as [Hargs [Henv [Henc Hwidth]]].
    repeat rewrite Cost.ticks_bind.
    rewrite Cost.ticks_step, Cost.ticks_map, FinSet.mem_cost, instantiate_equation.
    fold (key_bits tuple_encoding (map (inst (binding_value b)) (args atom))).
    pose proof (instantiate_cost b (args atom)) as Hinstantiate.
    pose proof (nat_N_le _ _ Hbinding) as HbindingN.
    pose proof (nat_N_le _ _ Hargs) as HargsN.
    assert (Hscaled : N.of_nat (length (args atom)) * (1 + N.of_nat (length b)) <=
      N.of_nat a * (1 + N.of_nat h)).
    { apply N.mul_le_mono; [exact HargsN | lia]. }
    lia.
Qed.

Lemma join_atom_list {P} (a : atom P) env bs :
  join_atom a env bs = flat_map (fun b =>
    filter_map (fun cs => bind_terms (args a) cs b)
      (FinSet.elements (set_raw (Cost.value (env (pred a)))))) bs.
Proof.
  unfold join_atom, join_atom_c; repeat rewrite Cost.value_bind.
  rewrite value_fold_right_c.
  induction bs as [|b bs IH]; cbn [fold_right flat_map]; [reflexivity |].
  rewrite Cost.value_bind, value_app_c, value_filter_map_c, IH; reflexivity.
Qed.

(** An atom's output count is bounded by the product of input bindings and enumerated rows. *)
Theorem join_atom_length {P} (a : atom P) env bs :
  (length (join_atom a env bs) <=
    length bs * length (FinSet.elements (set_raw (Cost.value (env (pred a))))))%nat.
Proof.
  rewrite join_atom_list.
  assert (Hflat : forall A B (f : A -> list B) xs n,
    (forall x, In x xs -> (length (f x) <= n)%nat) ->
    (length (flat_map f xs) <= length xs * n)%nat).
  { intros A B f xs n; induction xs as [|x xs IH]; intro H; [cbn; lia |].
    cbn [flat_map]; rewrite length_app.
    specialize (IH (fun y Hy => H y (or_intror Hy))).
    pose proof (H x (or_introl eq_refl)).
    change (length (f x) + length (flat_map f xs) <= n + length xs * n)%nat.
    lia. }
  apply Hflat; intros b _; apply filter_map_length.
Qed.

(** A nested probe retains full lookup and enumeration costs and charges every binding-row match. *)
Theorem join_atom_cost {P} (a : atom P) env bs q :
  (forall b cs, In b bs ->
    In cs (FinSet.elements (set_raw (Cost.value (env (pred a))))) ->
    Cost.ticks (bind_terms_c (args a) cs b) <= q) ->
  Cost.ticks (join_atom_c a env bs) <=
    1 + Cost.ticks (env (pred a)) +
    Cost.ticks (FinSet.elements_c (set_raw (Cost.value (env (pred a))))) +
    N.of_nat (length bs) *
      (N.of_nat (length (FinSet.elements (set_raw (Cost.value (env (pred a)))))) *
        (q + 2) + 1).
Proof.
  intro Hmatch; unfold join_atom_c; repeat rewrite Cost.ticks_bind.
  rewrite Cost.ticks_step.
  rewrite <- !N.add_assoc.
  apply N.add_le_mono; [reflexivity |].
  apply N.add_le_mono; [reflexivity |].
  apply N.add_le_mono; [reflexivity |].
  apply fold_right_bound_on; intros b acc Hb.
  rewrite Cost.ticks_bind, ticks_app_c, value_filter_map_c.
  pose proof (traversal_bound_on
    (fun cs => Cost.ticks (bind_terms_c (args a) cs b)) q
    (FinSet.elements (set_raw (Cost.value (env (pred a))))))
    as Hcost.
  specialize (Hcost (fun cs Hcs => Hmatch b cs Hb Hcs)).
  rewrite ticks_filter_map_c.
  pose proof (filter_map_length (fun cs => bind_terms (args a) cs b)
    (FinSet.elements (set_raw (Cost.value (env (pred a)))))) as Hlength.
  apply nat_N_le in Hlength.
  change (fold_right (fun cs n => 1 + Cost.ticks (bind_terms_c (args a) cs b) + n) 0
      (FinSet.elements (set_raw (Cost.value (env (pred a))))) +
    N.of_nat (length (filter_map (fun cs => bind_terms (args a) cs b)
      (FinSet.elements (set_raw (Cost.value (env (pred a))))))) <=
    N.of_nat (length (FinSet.elements (set_raw (Cost.value (env (pred a)))))) * (q + 2)).
  nia.
Qed.

(** Local budgets concern the finite nested-loop path and its actual binding-row callbacks. *)
Fixpoint join_bounded {P} (env : P -> Cost.t relation) (q e m : N)
    (ps : list (atom P)) (bs : list binding) : Prop :=
  match ps with
  | [] => True
  | a :: rest =>
    Cost.ticks (env (pred a)) +
      Cost.ticks (FinSet.elements_c (set_raw (Cost.value (env (pred a))))) <= e /\
    N.of_nat (length (FinSet.elements (set_raw (Cost.value (env (pred a)))))) <= m /\
    (forall b cs, In b bs ->
      In cs (FinSet.elements (set_raw (Cost.value (env (pred a))))) ->
      Cost.ticks (bind_terms_c (args a) cs b) <= q) /\
    join_bounded env q e m rest (join_atom a env bs)
  end.

(** The reference work bound multiplies candidates at successive positive atoms. *)
Fixpoint join_work (n : nat) (b q e m : N) : N :=
  match n with
  | O => 0
  | S n' => 2 + e + b * (m * (q + 2) + 1) + join_work n' (b * m) q e m
  end.

Lemma join_work_mono n b b' q e m : b <= b' ->
  join_work n b q e m <= join_work n b' q e m.
Proof.
  revert b b'; induction n as [|n IH]; intros b b' Hle; cbn [join_work]; [lia |].
  assert (Hmul : b * m <= b' * m) by nia.
  pose proof (IH (b * m) (b' * m) Hmul); nia.
Qed.

(** Successive atom budgets bound the complete nested-loop traversal. *)
Theorem join_positive_cost {P} (ps : list (atom P)) env bs q e m :
  join_bounded env q e m ps bs ->
  Cost.ticks (join_positive_c ps env bs) <=
    join_work (length ps) (N.of_nat (length bs)) q e m.
Proof.
  revert bs; induction ps as [|a ps IH]; intros bs Hbudget.
  - reflexivity.
  - destruct Hbudget as [Henv [Hrows [Hmatch Htail]]].
    specialize (IH (join_atom a env bs) Htail).
    cbn [join_positive_c length join_work]; repeat rewrite Cost.ticks_bind.
    rewrite Cost.ticks_step.
    change (Cost.ticks (join_positive_c ps env (join_atom a env bs)) <=
      join_work (length ps) (N.of_nat (length (join_atom a env bs))) q e m) in IH.
    pose proof (join_atom_cost a env bs q Hmatch) as Hatom.
    assert (Hatom' : Cost.ticks (join_atom_c a env bs) <=
      1 + e + N.of_nat (length bs) * (m * (q + 2) + 1)).
    { eapply N.le_trans; [exact Hatom |].
      assert (Hrowwork :
        N.of_nat (length (FinSet.elements (set_raw (Cost.value (env (pred a)))))) *
          (q + 2) <= m * (q + 2)) by nia.
      assert (Hprefix : 1 + Cost.ticks (env (pred a)) +
        Cost.ticks (FinSet.elements_c (set_raw (Cost.value (env (pred a))))) <= 1 + e)
        by lia.
      assert (Hproduct : N.of_nat (length bs) *
        (N.of_nat (length (FinSet.elements (set_raw (Cost.value (env (pred a)))))) *
          (q + 2) + 1) <= N.of_nat (length bs) * (m * (q + 2) + 1)).
      { apply N.mul_le_mono; [reflexivity | lia]. }
      exact (N.add_le_mono _ _ _ _ Hprefix Hproduct). }
    pose proof (join_atom_length a env bs) as Hlength.
    apply nat_N_le in Hlength; rewrite Nat2N.inj_mul in Hlength.
    pose proof (join_work_mono (length ps)
      (N.of_nat (length (join_atom a env bs))) (N.of_nat (length bs) * m)
      q e m ltac:(nia)) as Hwork.
    rewrite !N.add_assoc.
    change (1 + Cost.ticks (join_atom_c a env bs) +
      Cost.ticks (join_positive_c ps env (join_atom a env bs)) <=
      2 + e + N.of_nat (length bs) * (m * (q + 2) + 1) +
        join_work (length ps) (N.of_nat (length bs) * m) q e m).
    lia.
Qed.

(** Firing composes nested joins, literal tests, head instantiation and full set construction. *)
Theorem fire_rule_cost {P} (prog : program P) r env q e m n i :
  let ps := positive_atoms (body r) in
  let bs := join_positive_ref ps env [[]] in
  let selected := filter (negative_ok r env) bs in
  let heads := map (fun b => map (inst (binding_value b)) (args (head r))) selected in
  join_bounded env q e m ps [[]] ->
  (forall b, In b bs -> Cost.ticks (negative_ok_c r env b) <= n) ->
  (forall b, In b selected -> Cost.ticks (instantiate_c b (args (head r))) <= i) ->
  Cost.ticks (fire_rule_c prog r env) <=
    N.of_nat (length (body r)) + join_work (length ps) 1 q e m +
    N.of_nat (length bs) * (n + i + 2) +
    Cost.ticks (set_of_list_c tuple_encoding heads).
Proof.
  intros ps bs selected heads Hjoin Hnegative Hhead.
  unfold fire_rule_c; repeat rewrite Cost.ticks_bind.
  assert (Hpositive : Cost.ticks (positive_atoms_c (body r)) <= N.of_nat (length (body r))).
  { unfold positive_atoms_c.
    pose proof (ticks_filter_map_c_le
      (fun l : literal P => Cost.ret
        (match l with LPos a => Some a | LNeg _ => None end)) 0 (body r)
      (fun _ => N.le_refl 0)).
    nia. }
  pose proof (join_positive_cost ps env [[]] q e m Hjoin) as Hjoins.
  assert (Hneg : Cost.ticks (filter_c (negative_ok_c r env) bs) <=
    N.of_nat (length bs) * (n + 1)).
  { rewrite ticks_filter_c; apply traversal_bound_on, Hnegative. }
  assert (Hheads : Cost.ticks (map_c (fun b => instantiate_c b (args (head r))) selected) <=
    N.of_nat (length selected) * (i + 1)).
  { rewrite ticks_map_c; apply traversal_bound_on, Hhead. }
  assert (Hlength : N.of_nat (length selected) <= N.of_nat (length bs)).
  { apply nat_N_le, filter_length_bound. }
  repeat rewrite value_filter_c.
  repeat rewrite value_map_c.
  change (Cost.ticks (positive_atoms_c (body r)) +
    (Cost.ticks (join_positive_c ps env [[]]) +
    (Cost.ticks (filter_c (negative_ok_c r env) bs) +
    (Cost.ticks (map_c (fun b => instantiate_c b (args (head r))) selected) +
    Cost.ticks (set_of_list_c tuple_encoding
      (map (fun b => Cost.value (instantiate_c b (args (head r)))) selected))))) <=
    N.of_nat (length (body r)) + join_work (length ps) 1 q e m +
    N.of_nat (length bs) * (n + i + 2) +
    Cost.ticks (set_of_list_c tuple_encoding heads)).
  assert (Htuples : map (fun b => Cost.value (instantiate_c b (args (head r)))) selected =
    heads).
  { unfold heads; apply map_ext; intro b; apply instantiate_equation. }
  rewrite Htuples.
  assert (Hscale : N.of_nat (length selected) * (i + 1) <=
    N.of_nat (length bs) * (i + 1)).
  { apply N.mul_le_mono; [exact Hlength | reflexivity]. }
  change (Cost.ticks (join_positive_c ps env [[]]) <= join_work (length ps) 1 q e m)
    in Hjoins.
  nia.
Qed.

(** The nested-loop work measure bounds every family satisfying its local callback budgets. *)
Theorem join_positive_bigO {X P} (ps : X -> list (atom P))
    (env : X -> P -> Cost.t relation) (bs : X -> list binding) q e m :
  (forall x, join_bounded (env x) q e m (ps x) (bs x)) ->
  bigO (fun x => join_work (length (ps x)) (N.of_nat (length (bs x))) q e m)
    (fun x => Cost.ticks (join_positive_c (ps x) (env x) (bs x))).
Proof.
  intro Hbudget; exists 1; intro x.
  pose proof (join_positive_cost (ps x) (env x) (bs x) q e m (Hbudget x)); nia.
Qed.
