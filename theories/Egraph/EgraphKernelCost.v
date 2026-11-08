(** * Finite-support e-graph query bounds

    Logarithmic query bounds require rank-size evidence independently of semantic WF.
    For example, an unknown query pays for its own encoded width even in an empty graph.
    Builds on: EgraphGraph, BaseUnionFindRank and BaseUnionFindCost. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import
  BaseEncoding BaseEq BaseMap BaseUnionFind BaseUnionFindRank BaseUnionFindCost.
From Galois.Egraph Require Import EgraphSyntax EgraphCoreIndex EgraphGraph EgraphRebuild.
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

(** Parent registration sums the actual child-root encoder and trie charges. *)
Definition registration_work (n : Egraph.enode K Sort V) : N :=
  fold_right (fun c total =>
    1 + 2 * (1 + 2 * key_bits Egraph.id_encoding c) + total) 0 (Egraph.node_children n).

(** Private allocation charges parent registration and its historical-signature insertion. *)
Theorem allocation_kernel_cost g n w :
  query_budget w (Egraph.next g) ->
  Cost.ticks (Egraph.allocation_kernel_c g n) <= registration_work n + 1 + w.
Proof.
  intro Hfresh.
  assert (Hregister : Cost.ticks
    (EggParent.register_c (Egraph.parents g) (Egraph.node_children n) (Egraph.next g)) <=
    registration_work n).
  { rewrite EggParent.register_cost.
    change (fold_right (fun c total =>
      1 + 2 * (1 + Cost.ticks (encode_c Egraph.id_encoding c) +
        N.pos (Pos.size (encode Egraph.id_encoding c))) + total)
      0 (Egraph.node_children n) <= registration_work n).
    unfold registration_work.
    induction (Egraph.node_children n) as [|c cs IH]; cbn [fold_right].
    - reflexivity.
    - pose proof (encode_cost_bound positive_encoding_cost_laws c) as Hencode.
      change (Cost.ticks (encode_c Egraph.id_encoding c) <=
        1 * key_bits Egraph.id_encoding c) in Hencode.
      unfold key_bits in *; nia. }
  unfold Egraph.allocation_kernel_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  rewrite Map.set_cost.
  unfold query_budget, UnionFindCost.key_bound in Hfresh.
  nia.
Qed.

(** Allocation composes UF registration, all trie insertions and actual parent-list work. *)
Theorem allocate_cost g n key w :
  rank_inv g -> support_budget w g ->
  query_budget w (Egraph.next g) -> query_budget w key ->
  Cost.ticks (Egraph.allocate_c a g n key) <=
    find_bound g w + 3 * (1 + w) + registration_work n.
Proof.
  intros Hrank Hsupport Hfresh Hkey.
  pose proof (UnionFindCost.union_cost Egraph.id_encoding id_laws Map.cost_laws_hold
    (Egraph.next g) (Egraph.next g) (Egraph.uf g) w Hrank Hsupport Hfresh Hfresh) as Huf.
  pose proof (allocation_kernel_cost g n w Hfresh) as Hkernel.
  unfold Egraph.allocate_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  rewrite !Map.set_cost.
  unfold query_budget, UnionFindCost.key_bound in Hfresh, Hkey.
  unfold find_bound; nia.
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

End Graph.

End EggCost.
