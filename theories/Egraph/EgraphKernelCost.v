(** * Finite-support e-graph query bounds

    Logarithmic query bounds require rank-size evidence independently of semantic WF.
    For example, an unknown query pays for its own encoded width even in an empty graph.
    Builds on: EgraphGraph, BaseUnionFindRank and BaseUnionFindCost. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import
  BaseEncoding BaseCode BaseEq BaseMap BaseUnionFind BaseUnionFindRank BaseUnionFindCost.
From Galois.Egraph Require Import
  EgraphSyntax EgraphCoreIndex EgraphGraph EgraphRebuild EgraphCoreTransition
  EgraphCoreBatch EgraphCoreProgress EgraphCoreStructural EgraphCoreWork.
Import List.ListNotations Cost.Notations.

Module EggCost.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

Local Open Scope N_scope.

(** The certificate includes distinct finite class witnesses and an attained rank maximum. *)
Definition rank_inv (g : Egraph.t K Sort V) : Prop :=
  UnionFindRank.rank_size_inv Egraph.id_encoding (Egraph.uf g).

(** Stored-support budgets range over the finite UF support, independently of external keys. *)
Definition support_budget w (g : Egraph.t K Sort V) : Prop :=
  UnionFindCost.support_budget Egraph.id_encoding w (Egraph.uf g).

(** Each query budget includes its encoder charge and its encoded width. *)
Definition query_budget w c : Prop :=
  UnionFindCost.key_bound Egraph.id_encoding w c.

(** The logarithmic factor counts known forest keys and has a nonzero empty-state case. *)
Definition find_bound (g : Egraph.t K Sort V) w : N :=
  UnionFindCost.uf_k *
    N.of_nat (S (Nat.log2 (length (UnionFind.keys Egraph.id_encoding (Egraph.uf g))))) *
    (1 + w).

Local Lemma id_laws : encoding_laws Egraph.id_encoding.
Proof.
  exact positive_encoding_laws.
Qed.

(** Empty construction establishes the separate cost certificate without client key laws. *)
Theorem empty_rank_inv : rank_inv (@Egraph.empty K Sort V).
Proof.
  apply UnionFindRank.rank_size_inv_make.
Qed.

(** The actual compression result retains the certificate when clients keep its returned forest. *)
Theorem compression_rank_inv g c :
  rank_inv g ->
  UnionFindRank.rank_size_inv Egraph.id_encoding
    (snd (UnionFind.find Egraph.id_encoding c (Egraph.uf g))).
Proof.
  apply UnionFindRank.find_rank_size_inv; exact id_laws.
Qed.

(** Find's cost is logarithmic under rank-size, stored-support and actual-query budgets. *)
Theorem find_cost g c w :
  rank_inv g -> support_budget w g -> query_budget w c ->
  Cost.ticks (Egraph.find_c a g c) <= find_bound g w.
Proof.
  intros Hrank Hsupport Hquery.
  unfold Egraph.find_c; rewrite Cost.ticks_map.
  exact (UnionFindCost.find_cost Egraph.id_encoding id_laws Map.cost_laws_hold
    c (Egraph.uf g) w Hrank Hsupport Hquery).
Qed.

(** Canonicalization pays for the queried children alone and has no stored-node traversal. *)
Theorem canonical_cost g n w :
  rank_inv g -> support_budget w g ->
  (forall c, In c
    (match n with Egraph.NVar _ _ => [] | Egraph.NApp _ _ cs => cs end) ->
    query_budget w c) ->
  Cost.ticks (Egraph.canonical_c a g n) <=
    N.of_nat
      (length (match n with Egraph.NVar _ _ => [] | Egraph.NApp _ _ cs => cs end)) *
      (1 + find_bound g w).
Proof.
  intros Hrank Hsupport Hqueries.
  destruct n as [s v|s op cs]; [reflexivity|].
  unfold Egraph.canonical_c; rewrite Cost.ticks_map, ticks_map_c.
  induction cs as [|c cs IH]; cbn [fold_right length].
  - lia.
  - rewrite Nat2N.inj_succ.
    pose proof (find_cost g c w Hrank Hsupport (Hqueries c (or_introl eq_refl))) as Hhead.
    specialize (IH (fun d Hd => Hqueries d (or_intror Hd))).
    nia.
Qed.

(** Allocation preserves the certificate through its actual singleton-registration union. *)
Theorem allocate_rank_inv g n key :
  rank_inv g -> rank_inv (snd (Egraph.allocate a g n key)).
Proof.
  intro Hrank.
  change (UnionFindRank.rank_size_inv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g))).
  apply UnionFindRank.union_rank_size_inv; [exact id_laws|exact Hrank].
Qed.

(** Node-key budgets retain the actual symbol callbacks, serialization callback and memo key. *)
Record node_budget (n : Egraph.enode K Sort V) w : Prop := Node_budget {
  sort_callback : Cost.ticks
    (encode_c (EggAlg.sort_enc K Sort V a) (Egraph.node_sort n)) <= w;
  payload_callback :
    match n with
    | Egraph.NVar _ v => Cost.ticks (encode_c (EggAlg.var_enc K Sort V a) v) <= w
    | Egraph.NApp _ op _ => Cost.ticks (encode_c (EggAlg.op_enc K Sort V a) op) <= w
    end;
  serialization_callback :
    UnionFindCost.key_bound (codec_enc (list_codec positive_codec)) w (Egraph.signature a n);
  memo_query : query_budget w (Egraph.node_code a n)
}.

(** Shape budgets cover the selected dictionary callbacks and Base equality query. *)
Definition validation_budget (g : Egraph.t K Sort V) (n : Egraph.enode K Sort V) w : Prop :=
  match n with
  | Egraph.NVar s v =>
    Cost.ticks (EggAlg.var_sort_c a v) <= w /\
    forall declared, EggAlg.var_sort a v = Some declared ->
      Cost.ticks (eqb_c (EggAlg.sort_enc K Sort V a) s declared) <= w
  | Egraph.NApp s op cs =>
    forall sorts, Egraph.child_sorts a g cs = Some sorts ->
      Cost.ticks (EggAlg.op_shape_c a op sorts s) <= w
  end.

Local Lemma map_get_bound {A} (table : Map.t Egraph.id A) key w :
  query_budget w key -> Cost.ticks (Map.get_c Egraph.id_encoding key table) <= 1 + w.
Proof.
  intro Hkey; rewrite Map.get_cost.
  unfold query_budget, UnionFindCost.key_bound in Hkey; lia.
Qed.

(** Every child-sort lookup pays its queried key and its traversal callback. *)
Theorem child_sorts_cost g cs w :
  (forall c, In c cs -> query_budget w c) ->
  Cost.ticks (Egraph.child_sorts_c a g cs) <= N.of_nat (length cs) * (2 + w).
Proof.
  intro Hqueries; unfold Egraph.child_sorts_c.
  rewrite (ticks_fold_right_c_sum _ (fun c => Cost.ticks (Egraph.sort_of_c a g c))).
  - induction cs as [|c cs IH]; cbn [fold_right length]; [reflexivity|].
    rewrite Nat2N.inj_succ.
    assert (Hhead : Cost.ticks (Egraph.sort_of_c a g c) <= 1 + w).
    { unfold Egraph.sort_of_c; rewrite Cost.ticks_map.
      exact (map_get_bound _ c w (Hqueries c (or_introl eq_refl))). }
    specialize (IH (fun d Hd => Hqueries d (or_intror Hd))); nia.
  - intros c rest; rewrite Cost.ticks_bind, Cost.ticks_ret; lia.
Qed.

(** Validation is arity-linear and retains arbitrary runtime shape and declaration charges. *)
Theorem node_valid_cost g n w :
  validation_budget g n w ->
  (forall c, In c (Egraph.node_children n) -> query_budget w c) ->
  Cost.ticks (Egraph.node_valid_c a g n) <=
    (N.of_nat (length (Egraph.node_children n)) + 1) * (2 + 2 * w).
Proof.
  intros Hcallbacks Hqueries; destruct n as [s v|s op cs].
  - destruct Hcallbacks as [Hdeclared Hcompare].
    unfold Egraph.node_valid_c; rewrite !Cost.ticks_bind.
    fold (EggAlg.var_sort a v).
    destruct (EggAlg.var_sort a v) as [declared|] eqn:Hdeclared_value;
      autorewrite with galois_cost; cbn [Egraph.node_children length].
    + pose proof (Hcompare declared eq_refl); nia.
    + nia.
  - unfold validation_budget in Hcallbacks.
    pose proof (child_sorts_cost g cs w Hqueries) as Hchildren.
    unfold Egraph.node_valid_c; rewrite Cost.ticks_bind.
    fold (Egraph.child_sorts a g cs).
    destruct (Egraph.child_sorts a g cs) as [sorts|] eqn:Hsorts;
      autorewrite with galois_cost; cbn [Egraph.node_children].
    + pose proof (Hcallbacks sorts eq_refl); nia.
    + nia.
Qed.

(** Signature construction pays both symbol encoders and their invocation ticks. *)
Theorem signature_cost n w :
  node_budget n w -> Cost.ticks (Egraph.signature_c a n) <= 2 + 2 * w.
Proof.
  intro Hbudget.
  pose proof (sort_callback n w Hbudget) as Hsort.
  pose proof (payload_callback n w Hbudget) as Hpayload.
  destruct n; unfold Egraph.signature_c; autorewrite with galois_cost;
    cbn [Egraph.node_sort] in Hsort, Hpayload |- *; nia.
Qed.

(** Node coding charges both signature construction and the actual serialization callback. *)
Theorem node_code_cost n w :
  node_budget n w -> Cost.ticks (Egraph.node_code_c a n) <= 3 * (1 + w).
Proof.
  intro Hbudget.
  pose proof (signature_cost n w Hbudget) as Hsignature.
  pose proof (serialization_callback n w Hbudget) as Hserialization.
  unfold UnionFindCost.key_bound in Hserialization.
  unfold Egraph.node_code_c; rewrite !Cost.ticks_bind.
  fold (Egraph.signature a n); autorewrite with galois_cost; nia.
Qed.

Local Lemma register_bound index children i w :
  (forall c, In c children -> query_budget w c) ->
  Cost.ticks (EggParent.register_c index children i) <=
    N.of_nat (length children) * (3 + 2 * w).
Proof.
  intro Hqueries; rewrite EggParent.register_cost.
  change (fold_right (fun c total =>
    1 + 2 * (1 + Cost.ticks (encode_c Egraph.id_encoding c) +
      N.pos (Pos.size (encode Egraph.id_encoding c))) + total) 0 children <=
    N.of_nat (length children) * (3 + 2 * w)).
  induction children as [|c children IH]; cbn [fold_right length]; [reflexivity|].
  rewrite Nat2N.inj_succ.
  pose proof (Hqueries c (or_introl eq_refl)) as Hhead.
  unfold query_budget, UnionFindCost.key_bound in Hhead.
  specialize (IH (fun d Hd => Hqueries d (or_intror Hd))); nia.
Qed.

(** Allocation composes UF registration, three trie insertions and every child-root occurrence. *)
Theorem allocate_cost g n key w :
  rank_inv g -> support_budget w g -> query_budget w (Egraph.next g) -> query_budget w key ->
  (forall c, In c (Egraph.node_children n) -> query_budget w c) ->
  Cost.ticks (Egraph.allocate_c a g n key) <=
    find_bound g w + 3 * (1 + w) + N.of_nat (length (Egraph.node_children n)) * (3 + 2 * w).
Proof.
  intros Hrank Hsupport Hfresh Hkey Hchildren.
  pose proof (UnionFindCost.union_cost Egraph.id_encoding id_laws Map.cost_laws_hold
    (Egraph.next g) (Egraph.next g) (Egraph.uf g) w Hrank Hsupport Hfresh Hfresh) as Huf.
  pose proof (register_bound (Egraph.parents g) (Egraph.node_children n)
    (Egraph.next g) w Hchildren) as Hparents.
  unfold Egraph.allocate_c, Egraph.allocation_kernel_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  rewrite !Map.set_cost.
  autorewrite with galois_cost.
  unfold query_budget, UnionFindCost.key_bound in Hfresh, Hkey.
  unfold find_bound; nia.
Qed.

Local Lemma canonical_arity g n :
  length (Egraph.node_children (Egraph.canonical a g n)) = length (Egraph.node_children n).
Proof.
  destruct n; rewrite Egraph.canonical_equation; cbn [Egraph.node_children];
    rewrite ?length_map; reflexivity.
Qed.

(** The insertion constant covers validation, canonicalization, hashcons and parent registration. *)
Definition insert_k : N := 16.

(** Insertion depends on its arity and finite queried keys without a stored-graph scan. *)
Theorem add_node_cost g n w :
  rank_inv g -> support_budget w g ->
  validation_budget g n w ->
  (forall c, In c (Egraph.node_children n) -> query_budget w c) ->
  (forall c, In c (Egraph.node_children (Egraph.canonical a g n)) -> query_budget w c) ->
  node_budget (Egraph.canonical a g n) w ->
  query_budget w (Egraph.next g) ->
  (forall c, Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g) = Some c -> query_budget w c) ->
  Cost.ticks (Egraph.add_node_c a g n) <=
    insert_k * (N.of_nat (length (Egraph.node_children n)) + 1) * (1 + find_bound g w + w).
Proof.
  intros Hrank Hsupport Hvalidation Hchildren Hroots Hnode Hfresh Hhits.
  pose proof (node_valid_cost g n w Hvalidation Hchildren) as Hcheck.
  pose proof (canonical_cost g n w Hrank Hsupport Hchildren) as Hcanonical.
  change (Cost.ticks (Egraph.canonical_c a g n) <=
    N.of_nat (length (Egraph.node_children n)) * (1 + find_bound g w)) in Hcanonical.
  pose proof (node_code_cost _ w Hnode) as Hcode.
  pose proof (memo_query _ w Hnode) as Hkey.
  pose proof (map_get_bound (Egraph.memo g) _ w Hkey) as Hlookup.
  pose proof (allocate_cost g (Egraph.canonical a g n) _ w
    Hrank Hsupport Hfresh Hkey Hroots) as Hallocate.
  rewrite canonical_arity in Hallocate.
  unfold Egraph.add_node_c; rewrite Cost.ticks_bind.
  fold (Egraph.node_valid a g n); destruct (Egraph.node_valid a g n);
    [|unfold insert_k; autorewrite with galois_cost; nia].
  rewrite !Cost.ticks_bind.
  fold (Egraph.canonical a g n) (Egraph.node_code a (Egraph.canonical a g n)).
  fold (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)).
  destruct (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g)) as [other|] eqn:Hhit; autorewrite with galois_cost.
  - pose proof (find_cost g other w Hrank Hsupport (Hhits other eq_refl)).
    unfold insert_k; nia.
  - unfold insert_k; nia.
Qed.

Local Lemma add_node_equation g n :
  Egraph.add_node a g n =
    if Egraph.node_valid a g n then
      match Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
        (Egraph.memo g) with
      | Some c => Some (Egraph.find a g c, g)
      | None => Some (Egraph.allocate a g (Egraph.canonical a g n)
        (Egraph.node_code a (Egraph.canonical a g n)))
      end
    else None.
Proof.
  unfold Egraph.add_node, Egraph.add_node_c; rewrite Cost.value_bind.
  fold (Egraph.node_valid a g n); destruct (Egraph.node_valid a g n); [|reflexivity].
  rewrite !Cost.value_bind.
  fold (Egraph.canonical a g n) (Egraph.node_code a (Egraph.canonical a g n)).
  fold (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g)).
  destruct (Map.get _ _ _); reflexivity.
Qed.

(** Successful node insertion preserves cost evidence on both memo hits and allocation misses. *)
Theorem add_node_rank_inv g n c h :
  rank_inv g -> Egraph.add_node a g n = Some (c, h) -> rank_inv h.
Proof.
  intro Hrank; rewrite add_node_equation.
  destruct (Egraph.node_valid a g n); [|discriminate].
  destruct (Map.get _ _ _) as [d|].
  - intro Hresult; injection Hresult as <- <-; exact Hrank.
  - intro Hresult.
    pose proof (allocate_rank_inv g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n)) Hrank) as Hnew.
    destruct (Egraph.allocate a g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n))) as [d j].
    injection Hresult as <- <-; exact Hnew.
Qed.

Local Lemma terms_rank_inv es :
  Forall (fun e => forall g c h, rank_inv g ->
    Egraph.add_term a g e = Some (c, h) -> rank_inv h) es ->
  forall g cs h, rank_inv g -> Egraph.add_terms a g es = Some (cs, h) -> rank_inv h.
Proof.
  intro Hchildren; induction Hchildren as [|e es He Hrest IH]; intros g cs h Hrank;
    rewrite EggStructural.add_terms_equation.
  - intro Heq; injection Heq as <- <-; exact Hrank.
  - destruct (Egraph.add_term a g e) as [[c j]|] eqn:Hchild; [|discriminate].
    destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Htail; [|discriminate].
    intro Heq; injection Heq as <- <-; exact (IH j ds k (He g c j Hrank Hchild) Htail).
Qed.

(** Nested term insertion carries rank evidence through every actual allocated child. *)
Theorem add_term_rank_inv :
  forall e g c h, rank_inv g -> Egraph.add_term a g e = Some (c, h) -> rank_inv h.
Proof.
  apply (EggStructural.term_ind_all (fun e => forall g c h,
    rank_inv g -> Egraph.add_term a g e = Some (c, h) -> rank_inv h)).
  - intros s v g c h Hrank; rewrite EggStructural.add_term_equation.
    exact (add_node_rank_inv g (Egraph.NVar s v) c h Hrank).
  - intros s op es IH g c h Hrank; rewrite EggStructural.add_term_equation.
    destruct (Egraph.add_terms a g es) as [[cs j]|] eqn:Hchildren; [|discriminate].
    exact (add_node_rank_inv j (Egraph.NApp s op cs) c h
      (terms_rank_inv es IH g cs j Hrank Hchildren)).
Qed.

(** List insertion retains the certificate without adding any semantic premise. *)
Theorem add_terms_rank_inv es g cs h :
  rank_inv g -> Egraph.add_terms a g es = Some (cs, h) -> rank_inv h.
Proof.
  apply terms_rank_inv.
  apply Forall_forall; intros e Hin; exact (add_term_rank_inv e).
Qed.

(** Justified union transports the certificate through the Base union of its returned UF. *)
Theorem union_j_rank_inv g c d reason h :
  rank_inv g -> Egraph.union_j a g c d reason = Some h -> rank_inv h.
Proof.
  intro Hrank; rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g c) as [sc|], (Egraph.sort_of a g d) as [sd|];
    [|discriminate..].
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)); [|discriminate..].
  intro Hresult; injection Hresult as <-.
  change (UnionFindRank.rank_size_inv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))).
  apply UnionFindRank.union_rank_size_inv; [exact id_laws|exact Hrank].
Qed.

(** Ordinary union is the given-justification instance of certificate-preserving union. *)
Theorem union_rank_inv g c d h :
  rank_inv g -> Egraph.union a g c d = Some h -> rank_inv h.
Proof.
  exact (union_j_rank_inv g c d Egraph.JGiven h).
Qed.

(** Installing a historical signature never changes the certified forest. *)
Theorem install_rank_inv g i current oldkey key :
  rank_inv g -> rank_inv (Egraph.install g i current oldkey key).
Proof.
  intro Hrank; exact Hrank.
Qed.

(** Parent repair retains rank-size evidence through its actual justified collision union. *)
Theorem repair_node_rank_inv g i :
  rank_inv g -> rank_inv (Egraph.repair_node a g i).
Proof.
  intro Hrank; rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|],
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try exact Hrank.
  cbv zeta.
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|].
  - destruct (Egraph.union_j a g i other (Egraph.JCongruence i other))
      as [merged|] eqn:Hunion.
    + apply install_rank_inv; exact (union_j_rank_inv g i other _ merged Hrank Hunion).
    + apply install_rank_inv; exact Hrank.
  - apply install_rank_inv; exact Hrank.
Qed.

(** The counted parent fold carries its actual resulting forest's certificate. *)
Theorem repair_rank_inv g loser :
  rank_inv g -> rank_inv (fst (Egraph.repair a g loser)).
Proof.
  intro Hrank.
  change (rank_inv (fst (EggRebuild.repair a g loser))).
  rewrite EggRebuild.repair_equation.
  assert (Hfold : forall parents (state : Egraph.t K Sort V * N),
    rank_inv (fst state) ->
    rank_inv (fst (fold_left (fun result i =>
      (Egraph.repair_node a (fst result) i, N.succ (snd result))) parents state))).
  { intro parents; induction parents as [|i parents IH]; intros [h visits] Hinv.
    - exact Hinv.
    - cbn [fold_left fst snd]; apply IH; apply repair_node_rank_inv; exact Hinv. }
  exact (Hfold _ (g, 0) Hrank).
Qed.

(** A dirty-class callback preserves the certificate of whichever state it actually returns. *)
Theorem dirty_step_rank_inv g visits :
  rank_inv g ->
  match Cost.value (Egraph.dirty_step_c a (g, visits)) with
  | inl state | inr state => rank_inv (fst state)
  end.
Proof.
  intro Hrank; rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g))) as [[loser queue]|].
  - cbn [fst]; apply repair_rank_inv; exact Hrank.
  - exact Hrank.
Qed.

Local Lemma run_rank_inv fuel state result :
  runs (Egraph.dirty_step_c a) fuel state result -> rank_inv (fst state) ->
  match result with inl final | inr final => rank_inv (fst final) end.
Proof.
  intro Hrun; induction Hrun as
    [state|n state final Hstop|n state next result Hnext Hrun IH]; intro Hrank.
  - exact Hrank.
  - destruct state as [g visits].
    pose proof (dirty_step_rank_inv g visits Hrank) as Hstep.
    rewrite Hstop in Hstep; exact Hstep.
  - apply IH; destruct state as [g visits].
    pose proof (dirty_step_rank_inv g visits Hrank) as Hstep.
    rewrite Hnext in Hstep; exact Hstep.
Qed.

(** The actual binary dirty loop retains rank-size evidence for stopped and exhausted results. *)
Theorem iterate_rank_inv fuel g visits :
  rank_inv g ->
  match Cost.value (iterate (Egraph.dirty_step_c a) fuel (g, visits)) with
  | inl state | inr state => rank_inv (fst state)
  end.
Proof.
  intro Hrank.
  exact (run_rank_inv _ _ _ (iterate_value (Egraph.dirty_step_c a) fuel (g, visits)) Hrank).
Qed.

(** The public rebuild projection retains the independent rank-size certificate. *)
Theorem rebuild_rank_inv g :
  rank_inv g -> rank_inv (Egraph.rebuild a g).
Proof.
  intro Hrank.
  pose proof (iterate_rank_inv (Egraph.rebuild_fuel g) g 0 Hrank) as Hrun.
  unfold Egraph.rebuild, Egraph.rebuild_c, Egraph.rebuild_run_c.
  rewrite Cost.value_map, Cost.value_bind.
  fold (Egraph.rebuild_fuel g).
  rewrite Cost.value_bind.
  destruct (Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)));
    exact Hrun.
Qed.

(** Union budgets cover its finite input roots, resulting forest and actual sort callbacks. *)
Record union_budget (g : Egraph.t K Sort V) c d f w p : Prop := Union_budget {
  union_rank : rank_inv g;
  union_support : support_budget w g;
  union_left : query_budget w c;
  union_right : query_budget w d;
  union_old_log : find_bound g w <= f;
  union_new_support : UnionFindCost.support_budget Egraph.id_encoding w
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g));
  union_new_log :
    UnionFindCost.uf_k *
      N.of_nat (S (Nat.log2 (length (UnionFind.keys Egraph.id_encoding
        (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))))) * (1 + w) <= f;
  union_roots : forall root,
    root = Egraph.find a g c \/ root = Egraph.find a g d \/
    root = fst (UnionFind.find Egraph.id_encoding c
      (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))) -> query_budget w root;
  union_buckets : forall root,
    root = Egraph.find a g c \/ root = Egraph.find a g d ->
    N.of_nat (length (EggParent.get (Egraph.parents g) root)) <= p;
  union_sorts : forall key sort, (key = c \/ key = d) ->
    Egraph.sort_of a g key = Some sort ->
    UnionFindCost.key_bound (EggAlg.sort_enc K Sort V a) w sort
}.

Local Lemma positive_compare_bound c d w :
  query_budget w c -> Cost.ticks (positive_eqb_c c d) <= w.
Proof.
  intro Hc; pose proof (proj1 (positive_eqb_cost c d)) as Hcost.
  unfold query_budget, UnionFindCost.key_bound in Hc.
  change (Cost.ticks (encode_c Egraph.id_encoding c) + N.pos (Pos.size c) <= w) in Hc.
  lia.
Qed.

Local Lemma linked_cost (g : Egraph.t K Sort V) loser winner reason w p :
  query_budget w loser -> query_budget w winner ->
  N.of_nat (length (EggParent.get (Egraph.parents g) loser)) <= p ->
  Cost.ticks (Egraph.linked_kernel_c g loser winner reason) <= 6 * (1 + w) + p.
Proof.
  intros Hloser Hwinner Hparents.
  pose proof (EggPending.push_cost loser (Egraph.pending (Egraph.private g))) as Hpush.
  change (Cost.ticks (EggPending.push_c loser (Egraph.pending (Egraph.private g))) <=
    2 * (1 + Cost.ticks (encode_c Egraph.id_encoding loser) +
      N.pos (Pos.size (encode Egraph.id_encoding loser)))) in Hpush.
  unfold query_budget, UnionFindCost.key_bound in Hloser, Hwinner.
  change (Cost.ticks (encode_c Egraph.id_encoding loser) +
    N.pos (Pos.size (encode Egraph.id_encoding loser)) <= w) in Hloser.
  change (Cost.ticks (encode_c Egraph.id_encoding winner) +
    N.pos (Pos.size (encode Egraph.id_encoding winner)) <= w) in Hwinner.
  assert (Hpush_bound :
    Cost.ticks (EggPending.push_c loser (Egraph.pending (Egraph.private g))) <= 2 * (1 + w)).
  { lia. }
  assert (Hmerge : Cost.ticks (EggParent.merge_c (Egraph.parents g) loser winner) <=
    3 * (1 + w) + p).
  { rewrite EggParent.merge_cost.
    change EggParent.encoding with Egraph.id_encoding.
    clear Hpush Hpush_bound.
    apply N.add_le_mono; [|exact Hparents].
    replace (3 * (1 + w)) with ((1 + w) + 2 * (1 + w)) by ring.
    apply N.add_le_mono.
    - rewrite <- N.add_assoc; apply N.add_le_mono; [reflexivity|exact Hloser].
    - apply N.mul_le_mono_l.
      rewrite <- N.add_assoc; apply N.add_le_mono; [reflexivity|exact Hwinner]. }
  assert (Hget : Cost.ticks (EggParent.get_c (Egraph.parents g) loser) <= 1 + w).
  { rewrite EggParent.get_cost.
    change EggParent.encoding with Egraph.id_encoding.
    rewrite <- N.add_assoc; apply N.add_le_mono; [reflexivity|exact Hloser]. }
  unfold Egraph.linked_kernel_c; rewrite !Cost.ticks_bind.
  fold (EggParent.get (Egraph.parents g) loser).
  destruct (EggParent.get (Egraph.parents g) loser);
    autorewrite with galois_cost; lia.
Qed.

(** Unchecked merge pays for Base union, root discovery, deduplication and the copied bucket. *)
Theorem merge_cost g c d reason f w p :
  union_budget g c d f w p ->
  Cost.ticks (Egraph.merge_c a g c d reason) <= 4 * f + 8 * (1 + w) + p.
Proof.
  intro Hbudget; destruct Hbudget as
    [Hrank Hsupport Hc Hd Hlog Hnew_support Hnew_log Hroots Hbuckets Hsorts].
  pose proof (UnionFindCost.union_cost Egraph.id_encoding id_laws Map.cost_laws_hold
    c d (Egraph.uf g) w Hrank Hsupport Hc Hd) as Hunion.
  change (Cost.ticks (UnionFind.union_c Egraph.id_encoding c d (Egraph.uf g)) <=
    find_bound g w) in Hunion.
  pose proof (find_cost g c w Hrank Hsupport Hc) as Hleft.
  pose proof (find_cost g d w Hrank Hsupport Hd) as Hright.
  assert (Hnew_rank : UnionFindRank.rank_size_inv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))).
  { apply UnionFindRank.union_rank_size_inv; [exact id_laws|exact Hrank]. }
  pose proof (UnionFindCost.find_cost Egraph.id_encoding id_laws Map.cost_laws_hold c
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)) w Hnew_rank Hnew_support Hc)
    as Hnew_find.
  pose proof (Hroots _ (or_introl eq_refl)) as Hrc.
  pose proof (positive_compare_bound _ (Egraph.find a g d) w Hrc) as Hcompare.
  unfold Egraph.merge_c, Egraph.union_kernel_c.
  rewrite !Cost.ticks_bind.
  fold (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)).
  fold (Egraph.find a g c) (Egraph.find a g d).
  rewrite positive_eqb_equation.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d)).
  - autorewrite with galois_cost; nia.
  - rewrite !Cost.ticks_bind.
    fold (UnionFind.find Egraph.id_encoding c
      (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))).
    set (root := fst (UnionFind.find Egraph.id_encoding c
      (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))).
    pose proof (Hroots root (or_intror (or_intror eq_refl))) as Hroot.
    pose proof (positive_compare_bound root (Egraph.find a g c) w Hroot) as Hselect.
    rewrite positive_eqb_equation.
    destruct (Pos.eqb root (Egraph.find a g c)).
    + pose proof (linked_cost g (Egraph.find a g d) root reason w p
        (Hroots _ (or_intror (or_introl eq_refl))) Hroot
        (Hbuckets _ (or_intror eq_refl))) as Hlinked.
      autorewrite with galois_cost; nia.
    + pose proof (linked_cost g (Egraph.find a g c) root reason w p Hrc Hroot
        (Hbuckets _ (or_introl eq_refl))) as Hlinked.
      autorewrite with galois_cost; nia.
Qed.

(** Checked union additionally charges both sort lookups, encoders and encoded comparison. *)
Theorem union_j_cost g c d reason f w p :
  union_budget g c d f w p ->
  Cost.ticks (Egraph.union_j_c a g c d reason) <= 4 * f + 15 * (1 + w) + p.
Proof.
  intro Hbudget.
  pose proof (merge_cost g c d reason f w p Hbudget) as Hmerge.
  pose proof (map_get_bound (Egraph.nodes g) c w (union_left _ _ _ _ _ _ Hbudget)) as Hc.
  pose proof (map_get_bound (Egraph.nodes g) d w (union_right _ _ _ _ _ _ Hbudget)) as Hd.
  change (Cost.ticks (Egraph.sort_of_c a g c) <= 1 + w) in Hc.
  change (Cost.ticks (Egraph.sort_of_c a g d) <= 1 + w) in Hd.
  unfold Egraph.union_j_c; rewrite !Cost.ticks_bind.
  fold (Egraph.sort_of a g c) (Egraph.sort_of a g d).
  destruct (Egraph.sort_of a g c) as [sc|] eqn:Hsc,
    (Egraph.sort_of a g d) as [sd|] eqn:Hsd; autorewrite with galois_cost; try nia.
  pose proof (union_sorts _ _ _ _ _ _ Hbudget c sc (or_introl eq_refl) Hsc) as Hsortc.
  pose proof (union_sorts _ _ _ _ _ _ Hbudget d sd (or_intror eq_refl) Hsd) as Hsortd.
  pose proof (Map.code_compare_cost (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)) as Hcompare.
  unfold UnionFindCost.key_bound in Hsortc, Hsortd.
  change (Cost.ticks (encode_c (EggAlg.sort_enc K Sort V a) sc) +
    N.pos (Pos.size (encode (EggAlg.sort_enc K Sort V a) sc)) <= w) in Hsortc.
  fold (encode (EggAlg.sort_enc K Sort V a) sc) (encode (EggAlg.sort_enc K Sort V a) sd).
  fold (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)).
  destruct (Map.code_compare _ _); autorewrite with galois_cost; nia.
Qed.

(** Ordinary union has the same finite-query and parent-copy bound as annotated union. *)
Theorem union_cost g c d f w p :
  union_budget g c d f w p ->
  Cost.ticks (Egraph.union_c a g c d) <= 4 * f + 15 * (1 + w) + p.
Proof.
  exact (union_j_cost g c d Egraph.JGiven f w p).
Qed.

(** A parent budget lists only the node, snapshot, children and collision actually inspected. *)
Record parent_budget (g : Egraph.t K Sort V) i f w p arity : Prop := Parent_budget {
  parent_query : query_budget w i;
  parent_rank : rank_inv g;
  parent_support : support_budget w g;
  parent_log : find_bound g w <= f;
  parent_values : forall n old,
    Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
    Map.get Egraph.id_encoding i (Egraph.cached g) = Some old ->
    N.of_nat (length (Egraph.node_children n)) <= arity /\
    (forall c, In c (Egraph.node_children n) -> query_budget w c) /\
    node_budget (Egraph.canonical a g n) w /\ node_budget old w /\
    (forall other, Map.get Egraph.id_encoding
      (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g) = Some other ->
      union_budget g i other f w p)
}.

Local Lemma install_cost (g : Egraph.t K Sort V) i current oldkey key w :
  query_budget w i -> query_budget w oldkey -> query_budget w key ->
  Cost.ticks (Egraph.install_c g i current oldkey key) <= 3 * (1 + w).
Proof.
  intros Hi Hold Hkey.
  change (Cost.ticks (encode_c Egraph.id_encoding i) +
    N.pos (Pos.size (encode Egraph.id_encoding i)) <= w) in Hi.
  change (Cost.ticks (encode_c Egraph.id_encoding oldkey) +
    N.pos (Pos.size (encode Egraph.id_encoding oldkey)) <= w) in Hold.
  change (Cost.ticks (encode_c Egraph.id_encoding key) +
    N.pos (Pos.size (encode Egraph.id_encoding key)) <= w) in Hkey.
  unfold Egraph.install_c; autorewrite with galois_cost.
  rewrite Map.remove_cost, !Map.set_cost; nia.
Qed.

Local Lemma repair_base_cost g i key f w p :
  query_budget w key ->
  (forall other, Map.get Egraph.id_encoding key (Egraph.memo g) = Some other ->
    union_budget g i other f w p) ->
  Cost.ticks (Egraph.repair_base_c a g i key) <= 4 * f + 16 * (1 + w) + p.
Proof.
  intros Hkey Hcollide.
  pose proof (map_get_bound (Egraph.memo g) key w Hkey) as Hlookup.
  unfold Egraph.repair_base_c; rewrite Cost.ticks_bind.
  fold (Map.get Egraph.id_encoding key (Egraph.memo g)).
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|] eqn:Hhit.
  - pose proof (union_j_cost g i other (Egraph.JCongruence i other) f w p
      (Hcollide other eq_refl)) as Hunion.
    autorewrite with galois_cost.
    destruct (Cost.value (Egraph.union_j_c a g i other (Egraph.JCongruence i other)));
      autorewrite with galois_cost; clear - Hlookup Hunion; nia.
  - rewrite Cost.ticks_ret; clear - Hlookup; nia.
Qed.

(** Parent repair charges snapshot codes, memo removal, insertion and collision list copying. *)
Theorem repair_node_cost g i f w p arity :
  parent_budget g i f w p arity ->
  Cost.ticks (Egraph.repair_node_c a g i) <=
    (arity + 5) * (1 + f) + 30 * (1 + w) + p.
Proof.
  intros [Hi Hrank Hsupport Hlog Hvalues].
  pose proof (map_get_bound (Egraph.nodes g) i w Hi) as Hnode.
  pose proof (map_get_bound (Egraph.cached g) i w Hi) as Hsnapshot.
  unfold Egraph.repair_node_c; rewrite !Cost.ticks_bind.
  fold (Map.get Egraph.id_encoding i (Egraph.nodes g))
    (Map.get Egraph.id_encoding i (Egraph.cached g)).
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hn,
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [old|] eqn:Ho;
    autorewrite with galois_cost.
  2,3,4: clear - Hnode Hsnapshot; nia.
  destruct (Hvalues n old eq_refl eq_refl) as [Harity [Hchildren [Hcurrent [Hold Hcollide]]]].
  pose proof (canonical_cost g n w Hrank Hsupport Hchildren) as Hcanonical.
  change (Cost.ticks (Egraph.canonical_c a g n) <=
    N.of_nat (length (Egraph.node_children n)) * (1 + find_bound g w)) in Hcanonical.
  pose proof (node_code_cost _ w Hcurrent) as Hcode.
  pose proof (node_code_cost old w Hold) as Hhistory.
  pose proof (memo_query _ w Hcurrent) as Hkey.
  pose proof (memo_query old w Hold) as Holdkey.
  pose proof (repair_base_cost g i _ f w p Hkey Hcollide) as Hbase.
  pose proof (install_cost
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n)))
    i (Egraph.canonical a g n) (Egraph.node_code a old)
    (Egraph.node_code a (Egraph.canonical a g n)) w Hi Holdkey Hkey) as Hinstall.
  fold (Egraph.canonical a g n) (Egraph.node_code a old)
    (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.repair_base a g i (Egraph.node_code a (Egraph.canonical a g n))).
  clear - Hnode Hsnapshot Hcanonical Hlog Harity Hcode Hhistory Hbase Hinstall.
  nia.
Qed.

(** A batch certificate follows the actual parent fold's changing graph and fixed parent list. *)
Fixpoint batch_budget (parents : list Egraph.id) (g : Egraph.t K Sort V)
    f w p arity : Prop :=
  match parents with
  | [] => True
  | i :: rest => parent_budget g i f w p arity /\
    batch_budget rest (Egraph.repair_node a g i) f w p arity
  end.

Local Lemma repair_fold_cost parents g visits f w p arity :
  batch_budget parents g f w p arity ->
  Cost.ticks (fold_left_c (fun result i =>
    let* h := Egraph.repair_node_c a (fst result) i in
    Cost.ret (h, N.succ (snd result))) parents (g, visits)) <=
    N.of_nat (length parents) * ((arity + 5) * (1 + f) + 30 * (1 + w) + p + 1).
Proof.
  revert g visits; induction parents as [|i parents IH]; intros g visits Hbudget.
  - reflexivity.
  - destruct Hbudget as [Hhead Htail].
    rewrite ticks_fold_left_c_cons.
    autorewrite with galois_cost.
    cbn [fst snd]; rewrite N.add_0_r.
    fold (Egraph.repair_node a g i).
    pose proof (repair_node_cost g i f w p arity Hhead).
    pose proof (IH _ (N.succ visits) Htail).
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** A loser's batch pays its parent lookup and every actual callback and fold tick. *)
Theorem repair_cost g loser f w p arity :
  query_budget w loser ->
  batch_budget (EggParent.get (Egraph.parents g) loser) g f w p arity ->
  Cost.ticks (Egraph.repair_c a g loser) <=
    1 + w + N.of_nat (length (EggParent.get (Egraph.parents g) loser)) *
      ((arity + 5) * (1 + f) + 30 * (1 + w) + p + 1).
Proof.
  intros Hloser Hbatch.
  pose proof (repair_fold_cost _ g 0 f w p arity Hbatch) as Hfold.
  unfold Egraph.repair_c; rewrite Cost.ticks_bind.
  fold (EggParent.get (Egraph.parents g) loser).
  rewrite EggParent.get_cost.
  change EggParent.encoding with Egraph.id_encoding.
  change (Cost.ticks (encode_c Egraph.id_encoding loser) +
    N.pos (Pos.size (encode Egraph.id_encoding loser)) <= w) in Hloser.
  apply N.add_le_mono.
  - rewrite <- N.add_assoc; apply N.add_le_mono; [reflexivity|exact Hloser].
  - exact Hfold.
Qed.

(** Finite trace budgets concern the actual dequeues and their reached parent-fold inputs. *)
Definition loop_budget (g : Egraph.t K Sort V) f w p arity : Prop :=
  forall used h count,
    runs (Egraph.dirty_step_c a) used (g, 0) (inl (h, count)) ->
    (used < Pos.to_nat (Egraph.rebuild_fuel g))%nat ->
    forall loser queue,
      EggPending.pop (Egraph.pending (Egraph.private h)) = Some (loser, queue) ->
      query_budget w loser /\
      N.of_nat (length (EggParent.get (Egraph.parents h) loser)) <= p /\
      batch_budget (EggParent.get (Egraph.parents h) loser)
        (Egraph.with_queue h queue) f w p arity.

Local Lemma stop_cost g count final :
  Cost.value (Egraph.dirty_step_c a (g, count)) = inr final ->
  Cost.ticks (Egraph.dirty_step_c a (g, count)) = 0.
Proof.
  rewrite EggRebuild.dirty_step_equation.
  destruct (EggPending.pop (Egraph.pending (Egraph.private g)))
    as [[loser queue]|] eqn:Hpop; [discriminate|].
  intros _.
  rewrite EggPending.pop_equation in Hpop.
  destruct (EggPending.entries (Egraph.pending (Egraph.private g))) eqn:Hentries;
    [|discriminate].
  unfold Egraph.dirty_step_c, EggPending.pop_c.
  rewrite Hentries; reflexivity.
Qed.

Local Lemma step_nonempty g count h total :
  Egraph.kernel_inv a g ->
  Cost.value (Egraph.dirty_step_c a (g, count)) = inl (h, total) ->
  count < total.
Proof.
  intros Hinv Hstep.
  destruct (EggRebuild.dirty_step_count a g count h total Hstep)
    as [loser [queue [Hpop Hcount]]].
  pose proof (EggPending.pop_entries _ _ _ Hpop) as Hentries.
  assert (Hin : In loser (Egraph.dirty g)).
  { unfold Egraph.dirty; rewrite Hentries; left; reflexivity. }
  pose proof (Egraph.pending_nonempty a g Hinv loser Hin) as Hnonempty.
  destruct (EggParent.get (Egraph.parents g) loser); [contradiction|].
  cbn [length] in Hcount; rewrite Nat2N.inj_succ in Hcount; lia.
Qed.

(** Each continuing callback costs at most a per-parent budget times its actual visit increment. *)
Local Lemma step_cost g count h total f w p arity :
  Egraph.kernel_inv a g ->
  (forall loser queue,
    EggPending.pop (Egraph.pending (Egraph.private g)) = Some (loser, queue) ->
    query_budget w loser /\
    batch_budget (EggParent.get (Egraph.parents g) loser)
      (Egraph.with_queue g queue) f w p arity) ->
  Cost.value (Egraph.dirty_step_c a (g, count)) = inl (h, total) ->
  Cost.ticks (Egraph.dirty_step_c a (g, count)) <=
    (total - count) * ((arity + 5) * (1 + f) + 32 * (1 + w) + p + 1).
Proof.
  intros Hinv Hbudget Hstep.
  pose proof (step_nonempty g count h total Hinv Hstep) as Hpositive.
  destruct (EggRebuild.dirty_step_count a g count h total Hstep)
    as [loser [queue [Hpop Hcount]]].
  destruct (Hbudget loser queue Hpop) as [Hquery Hbatch].
  pose proof (repair_cost (Egraph.with_queue g queue) loser f w p arity Hquery Hbatch)
    as Hrepair.
  pose proof (EggPending.pop_cost _ _ _ Hpop) as Hqueue.
  change (Cost.ticks (EggPending.pop_c (Egraph.pending (Egraph.private g))) =
    1 + Cost.ticks (encode_c Egraph.id_encoding loser) +
      N.pos (Pos.size (encode Egraph.id_encoding loser))) in Hqueue.
  change (Cost.ticks (encode_c Egraph.id_encoding loser) +
    N.pos (Pos.size (encode Egraph.id_encoding loser)) <= w) in Hquery.
  unfold Egraph.dirty_step_c; rewrite Cost.ticks_bind.
  fold (EggPending.pop (Egraph.pending (Egraph.private g))).
  rewrite Hpop; autorewrite with galois_cost.
  change (Egraph.parents (Egraph.with_queue g queue)) with (Egraph.parents g) in Hrepair.
  rewrite Hqueue; nia.
Qed.

(** A continuing prefix of a stopping run leaves a genuine stopping suffix and unused fuel. *)
Local Lemma prefix_suffix budget state final :
  runs (Egraph.dirty_step_c a) budget state (inr final) ->
  forall used middle,
    runs (Egraph.dirty_step_c a) used state (inl middle) ->
    (used < budget)%nat /\
    runs (Egraph.dirty_step_c a) (budget - used) middle (inr final).
Proof.
  intros Hfull used middle Hprefix.
  remember (inl middle) as outcome eqn:Houtcome.
  revert budget Hfull middle Houtcome.
  induction Hprefix as
    [state|n state result Hstop|n state next result Hnext Hprefix IH];
    intros budget Hfull middle Houtcome.
  - injection Houtcome as <-; destruct budget as [|budget].
    + inversion Hfull.
    + split; [lia|exact Hfull].
  - discriminate.
  - destruct budget as [|budget]; [inversion Hfull|].
    inversion Hfull as [|b s r Hstop|b s following r Hfollowing Hrest]; subst.
    + rewrite Hnext in Hstop; discriminate.
    + rewrite Hnext in Hfollowing; injection Hfollowing as <-.
      destruct (IH budget Hrest middle eq_refl) as [Hbound Hsuffix].
      split; [lia|exact Hsuffix].
Qed.

Local Lemma prefix_extend initial used state next :
  runs (Egraph.dirty_step_c a) used initial (inl state) ->
  Cost.value (Egraph.dirty_step_c a state) = inl next ->
  runs (Egraph.dirty_step_c a) (S used) initial (inl next).
Proof.
  intros Hprefix Hstep.
  replace (S used) with (used + 1)%nat by lia.
  apply (runs_append _ used 1 initial (inl state) Hprefix).
  eapply runs_next; [exact Hstep|apply runs_zero].
Qed.

(** The size cap ranges over the finite parent snapshots dequeued by this particular run. *)
Definition bucket_budget (g : Egraph.t K Sort V) p : Prop :=
  forall used h count,
    runs (Egraph.dirty_step_c a) used (g, 0) (inl (h, count)) ->
    (used < Pos.to_nat (Egraph.rebuild_fuel g))%nat ->
    forall loser queue,
      EggPending.pop (Egraph.pending (Egraph.private h)) = Some (loser, queue) ->
      N.of_nat (length (EggParent.get (Egraph.parents h) loser)) <= p.

Local Definition head_bucket (state : Egraph.t K Sort V * N) :=
  match EggPending.pop (Egraph.pending (Egraph.private (fst state))) with
  | None => 0
  | Some (loser, _) =>
    N.of_nat (length (EggParent.get (Egraph.parents (fst state)) loser))
  end.

Local Lemma head_bucket_bound state loser queue :
  EggPending.pop (Egraph.pending (Egraph.private (fst state))) = Some (loser, queue) ->
  N.of_nat (length (EggParent.get (Egraph.parents (fst state)) loser)) <= head_bucket state.
Proof.
  intro Hpop; unfold head_bucket; rewrite Hpop; reflexivity.
Qed.

Local Lemma run_bucket_cap remaining state result :
  runs (Egraph.dirty_step_c a) remaining state result ->
  exists p, forall used h count,
    runs (Egraph.dirty_step_c a) used state (inl (h, count)) ->
    (used < remaining)%nat ->
    forall loser queue,
      EggPending.pop (Egraph.pending (Egraph.private h)) = Some (loser, queue) ->
      N.of_nat (length (EggParent.get (Egraph.parents h) loser)) <= p.
Proof.
  intro Hrun; induction Hrun as
    [state|n state final Hstop|n state next result Hstep Hrun [p IH]].
  - exists 0; intros used h count Hprefix Hused; lia.
  - exists (head_bucket state).
    intros used h count Hprefix Hused loser queue Hpop.
    inversion Hprefix as [s|b s r Hstopped|b s following r Hfollowing Hrest]; subst.
    + exact (head_bucket_bound (h, count) loser queue Hpop).
    + rewrite Hstop in Hfollowing; discriminate.
  - exists (N.max (head_bucket state) p).
    intros used h count Hprefix Hused loser queue Hpop.
    inversion Hprefix as [s|b s r Hstopped|b s following r Hfollowing Hrest]; subst.
    + eapply N.le_trans; [exact (head_bucket_bound (h, count) loser queue Hpop)|].
      apply N.le_max_l.
    + rewrite Hstep in Hfollowing; injection Hfollowing as <-.
      eapply N.le_trans; [exact (IH b h count Hrest ltac:(lia) loser queue Hpop)|].
      apply N.le_max_r.
Qed.

(** Each bounded dirty run has a finite bucket cap independently of the external key carrier. *)
Theorem bucket_budget_exists g : exists p, bucket_budget g p.
Proof.
  destruct (run_bucket_cap _ _ _
    (iterate_value (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0))) as [p Hp].
  exists p; exact Hp.
Qed.

(** Primitive trace budgets in particular bound the snapshots actually repaired. *)
Theorem loop_bucket_budget g f w p arity :
  loop_budget g f w p arity -> bucket_budget g p.
Proof.
  intros Hbudget used h count Hprefix Hused loser queue Hpop.
  exact (proj1 (proj2 (Hbudget used h count Hprefix Hused loser queue Hpop))).
Qed.

Section Loop.
Context (Hcodes : forall first second,
  Egraph.node_code a first = Egraph.node_code a second -> first = second).
Context (g : Egraph.t K Sort V)
  (Hinv : Egraph.kernel_inv a g) (Hlayout : EggTransition.layout a g).

Local Definition prefix (state : Egraph.t K Sort V * N) :=
  exists used, runs (Egraph.dirty_step_c a) used (g, 0) (inl state).

Local Lemma prefix_inv state :
  prefix state -> EggRepairBatch.execution_inv a g state.
Proof.
  intros [used Hprefix].
  apply (EggRepairBatch.run_preserved a Hcodes g used (g, 0) (inl state) Hprefix).
  unfold EggRepairBatch.execution_inv; cbn [fst].
  split; [exact Hinv|]; split; [exact Hlayout|]; split; reflexivity.
Qed.

Local Definition result_credit p (result :
    (Egraph.t K Sort V * N) + (Egraph.t K Sort V * N)) :=
  match result with
  | inl (h, count) | inr (h, count) =>
    count + p * N.of_nat (EggProgress.potential a (Egraph.next g) h)
  end.

Local Lemma run_repair_credit p remaining state result :
  bucket_budget g p ->
  runs (Egraph.dirty_step_c a) remaining state result ->
  forall used,
    runs (Egraph.dirty_step_c a) used (g, 0) (inl state) ->
    (used + remaining <= Pos.to_nat (Egraph.rebuild_fuel g))%nat ->
    result_credit p result <=
      snd state + p * N.of_nat (EggProgress.potential a (Egraph.next g) (fst state)).
Proof.
  intros Hbudget Hrun.
  induction Hrun as
    [state|n state final Hstop|n state next result Hstep Hrun IH];
    intros used Hprefix Hfuel.
  - destruct state; reflexivity.
  - destruct state as [h count], final as [j total].
    destruct (EggRebuild.dirty_step_stops a h count j total Hstop)
      as [-> [-> Hempty]]; reflexivity.
  - destruct state as [h count], next as [j total].
    assert (Hnewprefix : runs (Egraph.dirty_step_c a) (S used) (g, 0) (inl (j, total))).
    { exact (prefix_extend _ _ _ _ Hprefix Hstep). }
    assert (Hremaining : (S used + n <= Pos.to_nat (Egraph.rebuild_fuel g))%nat).
    { clear - Hfuel; lia. }
    specialize (IH (S used) Hnewprefix Hremaining).
    pose proof (prefix_inv (h, count) (ex_intro _ used Hprefix))
      as [Hh [Hl [Hnodes Hnext]]].
    pose proof (EggProgress.dirty_step_progress a Hcodes (Egraph.next g)
      h count Hh Hl Hnext) as Hprogress.
    rewrite Hstep in Hprogress.
    assert (Hdecrease :
      N.of_nat (EggProgress.potential a (Egraph.next g) j) <
      N.of_nat (EggProgress.potential a (Egraph.next g) h)).
    { clear - Hprogress; lia. }
    destruct (EggRebuild.dirty_step_count a h count j total Hstep)
      as [loser [queue [Hpop Hcount]]].
    assert (Hused : (used < Pos.to_nat (Egraph.rebuild_fuel g))%nat).
    { clear - Hfuel; lia. }
    pose proof (Hbudget used h count Hprefix Hused loser queue Hpop) as Hsize.
    cbn [fst snd] in IH |- *.
    eapply N.le_trans; [exact IH|].
    cbn [fst snd].
    clear - Hdecrease Hcount Hsize.
    nia.
Qed.

(** Dequeued bucket size times the decreasing partition potential bounds actual repair visits. *)
Theorem rebuild_repairs_potential p :
  bucket_budget g p ->
  Egraph.rebuild_repairs a g <=
    p * N.of_nat (EggProgress.potential a (Egraph.next g) g).
Proof.
  intro Hbudget.
  pose proof (iterate_value (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)) as Hrun.
  pose proof (run_repair_credit p _ _ _ Hbudget Hrun O (runs_zero _ (g, 0)) ltac:(lia))
    as Hcredit.
  unfold Egraph.rebuild_repairs; rewrite Egraph.rebuild_run_equation.
  unfold result_credit in Hcredit.
  destruct (Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)))
    as [[h count]|[h count]]; cbn [fst snd] in Hcredit |- *; nia.
Qed.

Local Lemma run_edge_credit p remaining state result :
  bucket_budget g p ->
  runs (Egraph.dirty_step_c a) remaining state result ->
  forall used,
    runs (Egraph.dirty_step_c a) used (g, 0) (inl state) ->
    (used + remaining <= Pos.to_nat (Egraph.rebuild_fuel g))%nat ->
    match result with
    | inl (h, count) | inr (h, count) =>
      count + p * N.of_nat (length (Egraph.dirty h)) +
        p * N.of_nat (length (Egraph.edges (fst state))) <=
      snd state + p * N.of_nat (length (Egraph.dirty (fst state))) +
        p * N.of_nat (length (Egraph.edges h))
    end.
Proof.
  intros Hbudget Hrun.
  induction Hrun as
    [state|n state final Hstop|n state next result Hstep Hrun IH];
    intros used Hprefix Hfuel.
  - destruct state; reflexivity.
  - destruct state as [h count], final as [j total].
    destruct (EggRebuild.dirty_step_stops a h count j total Hstop)
      as [-> [-> Hempty]]; reflexivity.
  - destruct state as [h count], next as [j total].
    assert (Hnewprefix : runs (Egraph.dirty_step_c a) (S used) (g, 0) (inl (j, total))).
    { exact (prefix_extend _ _ _ _ Hprefix Hstep). }
    assert (Hremaining : (S used + n <= Pos.to_nat (Egraph.rebuild_fuel g))%nat).
    { clear - Hfuel; lia. }
    specialize (IH (S used) Hnewprefix Hremaining).
    pose proof (EggWork.dirty_step_queue_credit a h count j total Hstep) as Hwork.
    assert (Hcredit : N.of_nat (length (Egraph.dirty j)) +
      N.of_nat (length (Egraph.edges h)) + 1 <=
      N.of_nat (length (Egraph.dirty h)) + N.of_nat (length (Egraph.edges j))).
    { clear - Hwork; lia. }
    destruct (EggRebuild.dirty_step_count a h count j total Hstep)
      as [loser [queue [Hpop Hcount]]].
    assert (Hused : (used < Pos.to_nat (Egraph.rebuild_fuel g))%nat).
    { clear - Hfuel; lia. }
    pose proof (Hbudget used h count Hprefix Hused loser queue Hpop) as Hsize.
    destruct result as [[final visits]|[final visits]]; cbn [fst snd] in IH |- *;
      clear - IH Hcredit Hcount Hsize; nia.
Qed.

(** Total visits are bounded by bucket size times initial dirty work plus new merges. *)
Theorem rebuild_repairs_total p :
  bucket_budget g p ->
  Egraph.rebuild_repairs a g + p * N.of_nat (length (Egraph.edges g)) <=
    p * (N.of_nat (length (Egraph.dirty g)) +
      N.of_nat (length (Egraph.edges (Egraph.rebuild a g)))).
Proof.
  intro Hbudget.
  pose proof (iterate_value (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)) as Hrun.
  pose proof (run_edge_credit p _ _ _ Hbudget Hrun O (runs_zero _ (g, 0)) ltac:(lia))
    as Hcredit.
  unfold Egraph.rebuild_repairs; rewrite Egraph.rebuild_equation, Egraph.rebuild_run_equation.
  destruct (Cost.value (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)))
    as [[h count]|[h count]]; cbn [fst snd] in Hcredit |- *; nia.
Qed.

(** Terminal credit is spent by the same count that the public rebuild returns. *)
Theorem rebuild_cost f w p arity :
  loop_budget g f w p arity ->
  Cost.ticks (Egraph.rebuild_c a g) <=
    3 + (((arity + 5) * (1 + f) + 32 * (1 + w) + p + 1) + 2) *
      Egraph.rebuild_repairs a g + N.pos (Pos.size (Egraph.rebuild_fuel g)).
Proof.
  intro Hbudget.
  destruct (EggProgress.iterate_stops a g Hcodes Hinv Hlayout)
    as [final [cap [Hstop Hfinal]]].
  pose proof (iterate_value (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0))
    as Hrun.
  rewrite Hstop in Hrun.
  set (k := (arity + 5) * (1 + f) + 32 * (1 + w) + p + 1).
  set (credit := fun state : Egraph.t K Sort V * N => (k + 2) * (cap - snd state)).
  assert (Hcap : forall state, prefix state -> snd state <= cap).
  { intros state [used Hprefix].
    destruct (prefix_suffix _ _ _ Hrun used state Hprefix) as [Hused Hsuffix].
    exact (EggRebuild.run_count_monotone a _ _ _ Hsuffix). }
  assert (Hstep : forall state, prefix state ->
    match Cost.value (Egraph.dirty_step_c a state) with
    | inl next =>
      prefix next /\ Cost.ticks (Egraph.dirty_step_c a state) + credit next + 2 <= credit state
    | inr _ => Cost.ticks (Egraph.dirty_step_c a state) <= credit state
    end).
  { intros [h count] Hprefix.
    pose proof (prefix_inv _ Hprefix) as [Hh [Hhl Hrest]].
    destruct Hprefix as [used Hprefix].
    destruct (prefix_suffix _ _ _ Hrun used (h, count) Hprefix) as [Hused Hsuffix].
    destruct (Cost.value (Egraph.dirty_step_c a (h, count)))
      as [[j total]|[j total]] eqn:Hstep.
    - assert (Hnext : prefix (j, total)).
      { exists (S used); exact (prefix_extend _ _ _ _ Hprefix Hstep). }
      assert (Hlocal : forall loser queue,
        EggPending.pop (Egraph.pending (Egraph.private h)) = Some (loser, queue) ->
        query_budget w loser /\
        batch_budget (EggParent.get (Egraph.parents h) loser)
          (Egraph.with_queue h queue) f w p arity).
      { intros loser queue Hpop.
        destruct (Hbudget used h count Hprefix Hused loser queue Hpop) as [Hq [Hp Hb]].
        split; assumption. }
      pose proof (step_cost h count j total f w p arity Hh Hlocal Hstep) as Hcost.
      pose proof (step_nonempty h count j total Hh Hstep) as Hpositive.
      pose proof (Hcap (j, total) Hnext) as Htotal.
      split; [exact Hnext|]; unfold credit, k; cbn [snd] in Htotal |- *; nia.
    - rewrite (stop_cost h count (j, total) Hstep); apply N.le_0_l. }
  assert (Hinitial : prefix (g, 0)).
  { exists O; apply runs_zero. }
  pose proof (iterate_terminal_credit (Egraph.dirty_step_c a) prefix credit
    (fun _ => 0) 0) as Hcredit.
  assert (Hlocal : forall state, prefix state ->
    match Cost.value (Egraph.dirty_step_c a state) with
    | inl next =>
      prefix next /\ Cost.ticks (Egraph.dirty_step_c a state) + credit next + 2 <= credit state
    | inr result => Cost.ticks (Egraph.dirty_step_c a state) + 0 <= 0 + credit state
    end).
  { intros state Hp; specialize (Hstep state Hp).
    destruct (Cost.value (Egraph.dirty_step_c a state)); [exact Hstep|lia]. }
  specialize (Hcredit Hlocal (Egraph.rebuild_fuel g) (g, 0) Hinitial).
  rewrite Hstop in Hcredit.
  unfold Egraph.rebuild_repairs; rewrite Egraph.rebuild_run_equation, Hstop; cbn [snd].
  unfold Egraph.rebuild_c, Egraph.rebuild_run_c.
  rewrite Cost.ticks_map, !Cost.ticks_bind.
  fold (Egraph.rebuild_fuel g).
  rewrite Hstop, Cost.ticks_ret.
  change (3 + (Cost.ticks
    (iterate (Egraph.dirty_step_c a) (Egraph.rebuild_fuel g) (g, 0)) + 0) <=
    3 + (k + 2) * cap + N.pos (Pos.size (Egraph.rebuild_fuel g))).
  unfold credit in Hcredit; cbn [snd] in Hcredit; nia.
Qed.

End Loop.

End Graph.

End EggCost.
