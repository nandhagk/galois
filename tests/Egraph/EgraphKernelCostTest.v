(** * Parent-index and repair-queue cost boundaries

    Parent concatenation retains its losing snapshot and charges the copied list.
    For example, merging two singleton buckets retains both occurrences in the winning bucket.
    Builds on: EgraphCoreIndex and EgraphKernelCost. *)

From Stdlib Require Import List PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import
  BaseEncoding BaseMap BaseUnionFind BaseUnionFindRank BaseUnionFindCost.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphSpec EgraphCoreIndex EgraphCoreInvariant
  EgraphCoreRepresentation EgraphCoreMaintained EgraphRebuild EgraphKernelCost.
Import List.ListNotations.
Local Open Scope nat_scope.

Module EggKernelPrimitiveTest.

Definition index :=
  EggParent.register Map.empty [1%positive; 2%positive] 3%positive.

Example parent_merge_retains_loser_snapshot :
  let merged := EggParent.merge index 1%positive 2%positive in
  (EggParent.get merged 1%positive, EggParent.get merged 2%positive) =
    ([3%positive], [3%positive; 3%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Example parent_merge_cost_includes_copy :
  Cost.ticks (EggParent.merge_c index 1%positive 2%positive) = 12%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_parent_bucket :
  EggParent.get index 4%positive = [].
Proof.
  vm_compute. reflexivity.
Qed.

Definition queue := EggPending.push 1%positive EggPending.empty.

Example pending_push_is_deduplicated :
  EggPending.entries (EggPending.push 1%positive queue) = [1%positive].
Proof.
  vm_compute. reflexivity.
Qed.

Example pending_pop_clears_membership :
  option_map (fun result =>
    (fst result, EggPending.entries (snd result),
      Map.get positive_encoding 1%positive (EggPending.flags (snd result))))
    (EggPending.pop queue) = Some (1%positive, [], None).
Proof.
  vm_compute. reflexivity.
Qed.

Example pending_empty_pop :
  EggPending.pop EggPending.empty = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example pending_push_hit_and_pop_ticks :
  (Cost.ticks (EggPending.push_c 1%positive EggPending.empty),
    Cost.ticks (EggPending.push_c 1%positive queue),
    Cost.ticks (EggPending.pop_c queue)) = (6%N, 3%N, 3%N).
Proof.
  vm_compute. reflexivity.
Qed.

Definition alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun _ => Some true) (fun _ _ _ => true).

(** The queue fixture inhabits its exact membership and duplicate-free invariant. *)
Theorem queue_wf : EggPending.wf queue.
Proof.
  apply EggPending.push_wf, EggPending.empty_wf.
Qed.

(** Initial graph construction establishes the certificate used by logarithmic cost laws. *)
Theorem graph_empty_rank_inv :
  EggCost.rank_inv (@Egraph.empty nat bool nat).
Proof.
  apply EggCost.empty_rank_inv.
Qed.

(** Successful insertion carries rank-size evidence independently of semantic WF evidence. *)
Theorem inserted_leaf_rank_inv c h :
  Egraph.add_node alg Egraph.empty (Egraph.NVar true 1) = Some (c, h) ->
  EggCost.rank_inv h.
Proof.
  apply EggCost.add_node_rank_inv; exact graph_empty_rank_inv.
Qed.

(** Empty construction also supplies concrete maintained-index evidence independently of costs. *)
Theorem graph_empty_kernel_inv : Egraph.kernel_inv alg Egraph.empty.
Proof.
  apply EggKernelInv.empty_kernel_inv.
Qed.

(** Leaf insertion establishes maintained coverage through the public computational entry. *)
Theorem inserted_leaf_kernel_inv c h :
  Egraph.add_node alg Egraph.empty (Egraph.NVar true 1) = Some (c, h) ->
  Egraph.kernel_inv alg h.
Proof.
  intro Hadded.
  apply (EggKernelInv.add_node_kernel_inv alg Egraph.empty (Egraph.NVar true 1) c h).
  - exact graph_empty_kernel_inv.
  - apply UnionFind.wf_make.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply Map.get_empty.
  - exact Hadded.
Qed.

Example inserted_leaf_stores_its_signature_snapshot :
  option_map (fun result =>
    (Map.get Egraph.id_encoding (fst result) (Egraph.cached (snd result)),
      Egraph.dirty (snd result), Egraph.edges (snd result)))
    (Egraph.add_node alg Egraph.empty (Egraph.NVar true 1)) =
    Some (Some (Egraph.NVar true 1), [], []).
Proof.
  vm_compute. reflexivity.
Qed.

(** The fixture's operator, sort and variable dictionaries satisfy the public encoding laws. *)
Theorem alg_encoding_laws : EggSpec.encoding_laws alg.
Proof.
  constructor; [exact nat_encoding_laws|exact bool_encoding_laws|exact nat_encoding_laws].
Qed.

(** Structural validity supplies every map, forest and freshness premise of maintained insertion. *)
Theorem structural_insertion_kernel_inv g n c h :
  EggSpec.structural_wf alg g -> Egraph.kernel_inv alg g ->
  Egraph.add_node alg g n = Some (c, h) -> Egraph.kernel_inv alg h.
Proof.
  intros Hstruct Hkernel Hadded.
  apply (EggKernelInv.add_node_kernel_inv alg g n c h).
  - exact Hkernel.
  - exact (EggRepresentation.forest_wf alg g Hstruct).
  - exact (EggRepresentation.nodes_wf alg g Hstruct).
  - exact (EggRepresentation.memo_wf alg g Hstruct).
  - destruct (Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g))
      as [old|] eqn:Hlookup; [|reflexivity].
    assert (Hbound : (Egraph.next g < Egraph.next g)%positive).
    { apply (proj1 (EggRepresentation.allocation alg g Hstruct (Egraph.next g))).
      exists old; exact Hlookup. }
    exact (False_rect _ (Pos.lt_irrefl _ Hbound)).
  - exact Hadded.
Qed.

(** A second public insertion maintains coverage from a genuinely nonempty leaf graph. *)
Theorem insert_parent_from_leaf c g d h :
  Egraph.add_node alg Egraph.empty (Egraph.NVar true 1) = Some (c, g) ->
  Egraph.add_node alg g (Egraph.NApp true 4 [c]) = Some (d, h) ->
  Egraph.kernel_inv alg h.
Proof.
  intros Hleaf Hparent.
  apply (structural_insertion_kernel_inv g (Egraph.NApp true 4 [c]) d h).
  - exact (EggSpec.wf_structural alg g
      (EggSpec.add_node_wf alg Egraph.empty (Egraph.NVar true 1) c g
        alg_encoding_laws (EggSpec.empty_wf alg) Hleaf)).
  - exact (inserted_leaf_kernel_inv c g Hleaf).
  - exact Hparent.
Qed.

Example nonempty_insertion_registers_its_parent :
  match Egraph.add_node alg Egraph.empty (Egraph.NVar true 1) with
  | None => None
  | Some (c, g) =>
    option_map (fun result =>
      (fst result, EggParent.get (Egraph.parents (snd result)) c,
        Map.get Egraph.id_encoding (fst result) (Egraph.cached (snd result))))
      (Egraph.add_node alg g (Egraph.NApp true 4 [c]))
  end = Some (2%positive, [2%positive], Some (Egraph.NApp true 4 [1%positive])).
Proof.
  vm_compute. reflexivity.
Qed.

Definition many_same_op m :=
  Egraph.add_terms alg Egraph.empty
    (map (fun i => EggTerm.App true 4 [EggTerm.Var true (S i)]) (seq 0 m)).

Definition dirty_fixture m :=
  match many_same_op m with
  | None => None
  | Some (_, g) => Egraph.union alg g 1%positive 3%positive
  end.

Definition dirty_loop_observation m :=
  match dirty_fixture m with
  | None => None
  | Some g =>
    let run := iterate (Egraph.dirty_step_c alg) 64%positive (g, 0%N) in
    match Cost.value run with
    | inl _ => None
    | inr (h, visits) =>
      Some (visits, Egraph.dirty h,
        Pos.eqb (Egraph.find alg h 2%positive) (Egraph.find alg h 4%positive),
        Pos.eqb (Egraph.find alg h 1%positive) (Egraph.find alg h 5%positive))
    end
  end.

Example dirty_loop_visits_only_the_losing_leaves_parent :
  (dirty_loop_observation 4, dirty_loop_observation 8, dirty_loop_observation 16) =
    (Some (1%N, [], true, false), Some (1%N, [], true, false), Some (1%N, [], true, false)).
Proof.
  vm_compute. reflexivity.
Qed.

Definition dirty_callback_loop_ticks m :=
  match dirty_fixture m with
  | None => None
  | Some g => Some (Cost.ticks (iterate (Egraph.dirty_step_c alg) 64%positive (g, 0%N)))
  end.

Example dirty_callback_loop_exact_costs :
  (dirty_callback_loop_ticks 4, dirty_callback_loop_ticks 8, dirty_callback_loop_ticks 16) =
    (Some 442%N, Some 442%N, Some 442%N).
Proof.
  vm_compute. reflexivity.
Qed.

Definition insertion_fixture m :=
  Egraph.add_terms alg Egraph.empty
    (map (fun i => EggTerm.Var true (S i)) (seq 0 m)).

Definition insertion_ticks m :=
  match insertion_fixture m with
  | None => None
  | Some (_, g) => Some (Cost.ticks (Egraph.add_node_c alg g (Egraph.NVar true 42)))
  end.

(** Each insertion fixture contains exactly its advertised number of stored nodes. *)
Example insertion_fixture_sizes :
  let size m := option_map (fun result => length (Map.elements (Egraph.nodes (snd result))))
    (insertion_fixture m) in
  (size 4, size 8, size 16) = (Some 4, Some 8, Some 16).
Proof.
  vm_compute. reflexivity.
Qed.

Example insertion_exact_ticks :
  (insertion_ticks 4, insertion_ticks 8, insertion_ticks 16) =
    (Some 196%N, Some 203%N, Some 210%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Observed insertion growth consists of seven charged fresh-key paths per additional key bit. *)
Example insertion_fixed_work_beyond_fresh_key_paths :
  Forall (fun m => match insertion_fixture m, insertion_ticks m with
    | Some (_, g), Some ticks => ticks =
      (175 + 7 * N.pos (Pos.size (Egraph.next g)))%N
    | _, _ => False
    end) [4; 8; 16].
Proof.
  constructor; [vm_compute; reflexivity|].
  constructor; [vm_compute; reflexivity|].
  constructor; [vm_compute; reflexivity|constructor].
Qed.

Definition rebuild_observation m :=
  match dirty_fixture m with
  | None => None
  | Some g => Some (Cost.ticks (Egraph.rebuild_c alg g), Egraph.rebuild_repairs alg g,
      Egraph.dirty (Egraph.rebuild alg g))
  end.

(** Public fuel construction and the actual iterator cost 441 ticks and visit one parent. *)
Example rebuild_exact_ticks_and_repairs :
  (rebuild_observation 4, rebuild_observation 8, rebuild_observation 16) =
    (Some (441%N, 1%N, []), Some (441%N, 1%N, []), Some (441%N, 1%N, [])).
Proof.
  vm_compute. reflexivity.
Qed.

(** The exact observations above give insertion ticks 196, 203 and 210 and rebuild ticks 441.
    EgraphRebuildLegacyTest.legacy_quadratic_pair_preparation records 20, 72 and 272 legacy pairs.
    Legacy has no Cost tick interface, so those pair counts are separate work observations.
    No native timing comparison is claimed. *)

(** These numerical bounds accompany the exact unchanged-input GraphTest observations. *)
Example rebuild_observed_bounds :
  Forall (fun m => match rebuild_observation m with
    | Some (ticks, repairs, _) => (ticks <= 441 /\ repairs <= 1)%N
    | None => False
    end) [4; 8; 16].
Proof.
  constructor; [vm_compute; split; discriminate|].
  constructor; [vm_compute; split; discriminate|].
  constructor; [vm_compute; split; discriminate|constructor].
Qed.

(** Symbolic consumers supply primitive trace budgets separately from maintained WF. *)
Theorem actual_loop_cost_client g f w p arity :
  EggSpec.wf alg g -> EggCost.loop_budget alg g f w p arity ->
  (Cost.ticks (Egraph.rebuild_c alg g) <=
    3 + (((arity + 5) * (1 + f) + 32 * (1 + w) + p + 1) + 2) *
      Egraph.rebuild_repairs alg g + N.pos (Pos.size (Egraph.rebuild_fuel g)))%N.
Proof.
  intros Hwf Hbudget.
  apply (EggCost.rebuild_cost alg (EggSpec.node_code_injective alg alg_encoding_laws) g).
  - exact (EggSpec.wf_kernel alg g Hwf).
  - exact (EggMaintained.layout alg g (EggSpec.wf_structural alg g Hwf)).
  - exact Hbudget.
Qed.

(** Total visits charge initial dirty work and the edges added by actual collision unions. *)
Theorem actual_loop_repair_total_client g p :
  EggCost.bucket_budget alg g p ->
  (Egraph.rebuild_repairs alg g + p * N.of_nat (length (Egraph.edges g)) <=
    p * (N.of_nat (length (Egraph.dirty g)) +
      N.of_nat (length (Egraph.edges (Egraph.rebuild alg g)))))%N.
Proof.
  exact (EggCost.rebuild_repairs_total alg g p).
Qed.

(** Public term insertion supplies maintained WF and independent rank evidence for rebuilding. *)
Theorem constructed_rebuild_client e c g :
  Egraph.add_term alg Egraph.empty e = Some (c, g) ->
  EggSpec.wf alg g /\ EggSpec.clean alg (Egraph.rebuild alg g) /\
    EggCost.rank_inv (Egraph.rebuild alg g).
Proof.
  intro Hadded.
  destruct (proj1 (EggSpec.add_term_represents alg Egraph.empty e
    alg_encoding_laws (EggSpec.empty_wf alg)) c g Hadded) as [Hrep [Hwf Hext]].
  split; [exact Hwf|]; split.
  - exact (EggSpec.rebuild_clean alg g alg_encoding_laws Hwf).
  - apply EggCost.rebuild_rank_inv.
    exact (EggCost.add_term_rank_inv alg e Egraph.empty c g graph_empty_rank_inv Hadded).
Qed.

End EggKernelPrimitiveTest.

Import EggKernelPrimitiveTest.

Module EggKernelConcreteClient.

Definition first_term : EggTerm.t nat bool nat :=
  EggTerm.App true 4 [EggTerm.Var true 1].

Definition second_term : EggTerm.t nat bool nat :=
  EggTerm.App true 4 [EggTerm.Var true 2].

Definition first :=
  match Egraph.add_term alg Egraph.empty first_term with
  | Some (_, g) => g
  | None => Egraph.empty
  end.

Definition before :=
  match Egraph.add_term alg first second_term with
  | Some (_, g) => g
  | None => Egraph.empty
  end.

Definition dirty :=
  match Egraph.union alg before 1%positive 3%positive with
  | Some g => g
  | None => before
  end.

Definition popped := Egraph.with_queue dirty EggPending.empty.
Definition after := Egraph.repair_node alg popped 4%positive.
Definition fresh_node : Egraph.enode nat bool nat := Egraph.NApp true 5 [1%positive].
Definition support_ids := [4; 2; 1; 3]%positive.

(** The shared fixture comes from two successful public nonempty term insertions. *)
Example insertion_results :
  Egraph.add_term alg Egraph.empty first_term = Some (2%positive, first) /\
  Egraph.add_term alg first second_term = Some (4%positive, before).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The external union genuinely merges the two leaves and leaves one parent batch pending. *)
Example union_result :
  Egraph.union alg before 1%positive 3%positive = Some dirty.
Proof.
  vm_compute; reflexivity.
Qed.

(** Public preservation supplies maintained WF independently of all numerical budgets. *)
Theorem before_wf : EggSpec.wf alg before.
Proof.
  destruct insertion_results as [Hfirst Hsecond].
  destruct (proj1 (EggSpec.add_term_represents alg Egraph.empty first_term
    alg_encoding_laws (EggSpec.empty_wf alg)) 2%positive first Hfirst)
    as [Hrep [Hwf Hext]].
  exact (proj1 (proj2 (proj1 (EggSpec.add_term_represents alg first second_term
    alg_encoding_laws Hwf) 4%positive before Hsecond))).
Qed.

(** The dirty numerical client uses maintained WF proved by the actual successful union. *)
Theorem dirty_wf : EggSpec.wf alg dirty.
Proof.
  exact (EggSpec.union_wf alg before 1%positive 3%positive dirty
    alg_encoding_laws before_wf union_result).
Qed.

(** Rank evidence is carried through construction and is not inferred from semantic WF. *)
Theorem before_rank : EggCost.rank_inv before.
Proof.
  destruct insertion_results as [Hfirst Hsecond].
  exact (EggCost.add_term_rank_inv alg second_term first 4%positive before
    (EggCost.add_term_rank_inv alg first_term Egraph.empty 2%positive first
      graph_empty_rank_inv Hfirst) Hsecond).
Qed.

(** Actual union and queue replacement retain the independent certificate used by repair costs. *)
Theorem dirty_rank : EggCost.rank_inv dirty.
Proof.
  exact (EggCost.union_rank_inv alg before 1%positive 3%positive dirty before_rank union_result).
Qed.

Local Lemma popped_rank : EggCost.rank_inv popped.
Proof.
  exact dirty_rank.
Qed.

(** Every queried dense identifier has an explicitly computed encoder-and-width budget. *)
Example dense_queries :
  Forall (EggCost.query_budget 256%N) [1; 2; 3; 4; 5]%positive.
Proof.
  constructor; [vm_compute; discriminate|].
  constructor; [vm_compute; discriminate|].
  constructor; [vm_compute; discriminate|].
  constructor; [vm_compute; discriminate|].
  constructor; [vm_compute; discriminate|constructor].
Qed.

Local Lemma dense_query key :
  In key [1; 2; 3; 4; 5]%positive -> EggCost.query_budget 256%N key.
Proof.
  exact (proj1 (Forall_forall _ _) dense_queries key).
Qed.

(** Closed observations identify finite support for the external union and repair collision. *)
Example forest_supports :
  UnionFind.keys Egraph.id_encoding (Egraph.uf before) = support_ids /\
  UnionFind.keys Egraph.id_encoding (Egraph.uf dirty) = support_ids /\
  UnionFind.keys Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding 4%positive 2%positive (Egraph.uf popped)) = support_ids.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

Local Lemma support_from_keys forest :
  UnionFind.wf Egraph.id_encoding forest ->
  UnionFind.keys Egraph.id_encoding forest = support_ids ->
  UnionFindCost.support_budget Egraph.id_encoding 256%N forest.
Proof.
  intros Hwf Hkeys key Hsupport.
  apply dense_query.
  apply (proj2 (UnionFind.keys_spec Egraph.id_encoding positive_encoding_laws
    forest key Hwf)) in Hsupport.
  rewrite Hkeys in Hsupport.
  unfold support_ids in Hsupport; cbn [In] in Hsupport |- *; intuition.
Qed.

Local Lemma before_support : EggCost.support_budget 256%N before.
Proof.
  apply support_from_keys.
  - exact (UnionFindRank.forest_wf _ _ before_rank).
  - exact (proj1 forest_supports).
Qed.

Local Lemma dirty_support : EggCost.support_budget 256%N dirty.
Proof.
  apply support_from_keys.
  - exact (UnionFindRank.forest_wf _ _ dirty_rank).
  - exact (proj1 (proj2 forest_supports)).
Qed.

Local Lemma popped_support : EggCost.support_budget 256%N popped.
Proof.
  exact dirty_support.
Qed.

(** The logarithmic factors are obtained from these finite supports and their chosen key budget. *)
Example logarithmic_factors :
  EggCost.find_bound before 256%N = 98688%N /\
  EggCost.find_bound dirty 256%N = 98688%N.
Proof.
  unfold EggCost.find_bound.
  rewrite (proj1 forest_supports), (proj1 (proj2 forest_supports)).
  vm_compute; split; reflexivity.
Qed.

(** Fixture opacity keeps numerical contracts separate from direct operation-price reduction. *)
Local Opaque dirty.

(** A nontrivial supported find consumes the public numerical theorem with discharged duties. *)
Theorem concrete_find_cost :
  (Cost.ticks (Egraph.find_c alg dirty 3%positive) <= 98688)%N.
Proof.
  eapply N.le_trans.
  - exact (EggCost.find_cost alg dirty 3%positive 256%N dirty_rank dirty_support
      (dense_query 3%positive ltac:(cbn [In]; intuition))).
  - rewrite (proj2 logarithmic_factors); reflexivity.
Qed.

Local Transparent dirty.

(** Symbol encoding, actual list serialization and memo-key encoding all fit concrete budgets. *)
Example signature_budgets :
  EggCost.node_budget alg fresh_node 256%N /\
  EggCost.node_budget alg (Egraph.NApp true 4 [1%positive]) 256%N /\
  EggCost.node_budget alg (Egraph.NApp true 4 [3%positive]) 256%N.
Proof.
  split; [constructor; vm_compute; discriminate|].
  split; constructor; vm_compute; discriminate.
Qed.

(** Concrete shape validation reads the allocated child and actually accepts the new operator. *)
Example fresh_node_observations :
  Egraph.child_sorts alg before [1%positive] = Some [true] /\
  Egraph.canonical alg before fresh_node = fresh_node /\
  Egraph.next before = 5%positive /\
  Map.get Egraph.id_encoding (Egraph.node_code alg fresh_node) (Egraph.memo before) = None /\
  option_map fst (Egraph.add_node alg before fresh_node) = Some 5%positive.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Local Lemma fresh_validation : EggCost.validation_budget alg before fresh_node 256%N.
Proof.
  change (forall sorts, Egraph.child_sorts alg before [1%positive] = Some sorts ->
    (Cost.ticks (EggAlg.op_shape_c alg 5%nat sorts true) <= 256)%N).
  rewrite (proj1 fresh_node_observations).
  intros sorts Hsorts; injection Hsorts as <-.
  vm_compute; discriminate.
Qed.

Local Opaque first before.

(** Nonempty insertion applies the public arity-linear contract after discharging every duty. *)
Theorem concrete_add_node_cost :
  (Cost.ticks (Egraph.add_node_c alg before fresh_node) <= 3166240)%N.
Proof.
  pose proof (proj1 (proj2 fresh_node_observations)) as Hcanonical.
  assert (Hchildren : forall c, In c (Egraph.node_children fresh_node) ->
    EggCost.query_budget 256%N c).
  { intros c Hin; apply dense_query; cbn [fresh_node Egraph.node_children In] in *; intuition. }
  pose proof (EggCost.add_node_cost alg before fresh_node 256%N before_rank before_support
    fresh_validation Hchildren) as Hcost.
  rewrite Hcanonical in Hcost.
  specialize (Hcost Hchildren (proj1 signature_budgets)).
  specialize (Hcost ltac:(rewrite (proj1 (proj2 (proj2 fresh_node_observations)));
    apply dense_query; cbn [In]; intuition)).
  assert (Hhit : forall c,
    Map.get Egraph.id_encoding (Egraph.node_code alg fresh_node) (Egraph.memo before) = Some c ->
    EggCost.query_budget 256%N c).
  { intros c Hget.
    rewrite (proj1 (proj2 (proj2 (proj2 fresh_node_observations)))) in Hget; discriminate. }
  specialize (Hcost Hhit).
  eapply N.le_trans; [exact Hcost|].
  rewrite (proj1 logarithmic_factors); reflexivity.
Qed.

Local Transparent first before.

(** These observations identify rank-selected roots and the two nonempty parent buckets. *)
Example before_union_observations :
  Egraph.uf dirty =
    UnionFind.union Egraph.id_encoding 1%positive 3%positive (Egraph.uf before) /\
  Egraph.find alg before 1%positive = 1%positive /\
  Egraph.find alg before 3%positive = 3%positive /\
  fst (UnionFind.find Egraph.id_encoding 1%positive
    (UnionFind.union Egraph.id_encoding 1%positive 3%positive (Egraph.uf before))) =
      1%positive /\
  EggParent.get (Egraph.parents before) 1%positive = [2%positive] /\
  EggParent.get (Egraph.parents before) 3%positive = [4%positive] /\
  Egraph.sort_of alg before 1%positive = Some true /\
  Egraph.sort_of alg before 3%positive = Some true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The union certificate discharges both forest supports and the observed root and sort duties. *)
Theorem before_union_budget :
  EggCost.union_budget alg before 1%positive 3%positive 100000%N 256%N 1%N.
Proof.
  destruct before_union_observations as
    [Huf [Hleft [Hright [Hnew [Hparents_left [Hparents_right [Hsort_left Hsort_right]]]]]]].
  constructor.
  - exact before_rank.
  - exact before_support.
  - apply dense_query; cbn [In]; intuition.
  - apply dense_query; cbn [In]; intuition.
  - rewrite (proj1 logarithmic_factors); vm_compute; discriminate.
  - rewrite <- Huf; exact dirty_support.
  - rewrite <- Huf.
    change (EggCost.find_bound dirty 256%N <= 100000)%N.
    rewrite (proj2 logarithmic_factors); vm_compute; discriminate.
  - intros root [-> | [-> | ->]]; rewrite ?Hleft, ?Hright, ?Hnew;
      apply dense_query; cbn [In]; intuition.
  - intros root [-> | ->]; rewrite ?Hleft, ?Hright, ?Hparents_left, ?Hparents_right;
      reflexivity.
  - intros key sort [-> | ->] Hsort; rewrite ?Hsort_left, ?Hsort_right in Hsort;
      injection Hsort as <-; vm_compute; discriminate.
Qed.

Local Opaque first before.

(** Nonempty ordinary union consumes its fully discharged public numerical contract. *)
Theorem concrete_union_cost :
  (Cost.ticks (Egraph.union_c alg before 1%positive 3%positive) <= 403856)%N.
Proof.
  exact (EggCost.union_cost alg before 1%positive 3%positive
    100000%N 256%N 1%N before_union_budget).
Qed.

(** Annotation does not change the discharged budgets for the actual nonempty external union. *)
Theorem concrete_union_j_cost :
  (Cost.ticks (Egraph.union_j_c alg before 1%positive 3%positive Egraph.JGiven) <= 403856)%N.
Proof.
  exact (EggCost.union_j_cost alg before 1%positive 3%positive Egraph.JGiven
    100000%N 256%N 1%N before_union_budget).
Qed.

Local Transparent first before.

(** Repair's collision queries the allocated application roots and their actual parent buckets. *)
Example collision_union_observations :
  Egraph.find alg popped 4%positive = 4%positive /\
  Egraph.find alg popped 2%positive = 2%positive /\
  fst (UnionFind.find Egraph.id_encoding 4%positive
    (UnionFind.union Egraph.id_encoding 4%positive 2%positive (Egraph.uf popped))) =
      4%positive /\
  EggParent.get (Egraph.parents popped) 4%positive = [] /\
  EggParent.get (Egraph.parents popped) 2%positive = [] /\
  Egraph.sort_of alg popped 4%positive = Some true /\
  Egraph.sort_of alg popped 2%positive = Some true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The collision's old and resulting forests have finite certified numerical budgets. *)
Theorem collision_union_budget :
  EggCost.union_budget alg popped 4%positive 2%positive 100000%N 256%N 1%N.
Proof.
  destruct collision_union_observations as
    [Hleft [Hright [Hnew [Hparents_left [Hparents_right [Hsort_left Hsort_right]]]]]].
  constructor.
  - exact popped_rank.
  - exact popped_support.
  - apply dense_query; cbn [In]; intuition.
  - apply dense_query; cbn [In]; intuition.
  - change (EggCost.find_bound dirty 256%N <= 100000)%N.
    rewrite (proj2 logarithmic_factors); vm_compute; discriminate.
  - apply support_from_keys.
    + apply UnionFind.wf_union.
      * exact positive_encoding_laws.
      * exact (UnionFindRank.forest_wf _ _ popped_rank).
    + exact (proj2 (proj2 forest_supports)).
  - rewrite (proj2 (proj2 forest_supports)); vm_compute; discriminate.
  - intros root [-> | [-> | ->]]; rewrite ?Hleft, ?Hright, ?Hnew;
      apply dense_query; cbn [In]; intuition.
  - intros root [-> | ->]; rewrite ?Hleft, ?Hright, ?Hparents_left, ?Hparents_right;
      vm_compute; discriminate.
  - intros key sort [-> | ->] Hsort; rewrite ?Hsort_left, ?Hsort_right in Hsort;
      injection Hsort as <-; vm_compute; discriminate.
Qed.

Local Opaque popped.

(** The actual congruence collision also instantiates the annotated numerical contract directly. *)
Theorem concrete_collision_cost :
  (Cost.ticks (Egraph.union_j_c alg popped 4%positive 2%positive
    (Egraph.JCongruence 4%positive 2%positive)) <= 403856)%N.
Proof.
  exact (EggCost.union_j_cost alg popped 4%positive 2%positive
    (Egraph.JCongruence 4%positive 2%positive) 100000%N 256%N 1%N collision_union_budget).
Qed.

Local Transparent popped.

(** The selected parent has an old child, a current child and a memo collision with node two. *)
Example parent_observations :
  Map.get Egraph.id_encoding 4%positive (Egraph.nodes popped) =
    Some (Egraph.NApp true 4 [3%positive]) /\
  Map.get Egraph.id_encoding 4%positive (Egraph.cached popped) =
    Some (Egraph.NApp true 4 [3%positive]) /\
  Egraph.canonical alg popped (Egraph.NApp true 4 [3%positive]) =
    Egraph.NApp true 4 [1%positive] /\
  Map.get Egraph.id_encoding (Egraph.node_code alg (Egraph.NApp true 4 [1%positive]))
    (Egraph.memo popped) = Some 2%positive /\
  EggParent.get (Egraph.parents popped) 3%positive = [4%positive].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The repair parent discharges arity, children, signatures and its collision certificate. *)
Theorem concrete_parent_budget :
  EggCost.parent_budget alg popped 4%positive 100000%N 256%N 1%N 1%N.
Proof.
  destruct parent_observations as [Hnode [Hsnapshot [Hcanonical [Hcollision Hparents]]]].
  constructor.
  - apply dense_query; cbn [In]; intuition.
  - exact popped_rank.
  - exact popped_support.
  - change (EggCost.find_bound dirty 256%N <= 100000)%N.
    rewrite (proj2 logarithmic_factors); vm_compute; discriminate.
  - intros n old Hn Ho; rewrite Hnode in Hn; rewrite Hsnapshot in Ho.
    injection Hn as <-; injection Ho as <-.
    split; [reflexivity|]; split.
    + intros c Hin; apply dense_query; cbn [Egraph.node_children In] in *; intuition.
    + split; [rewrite Hcanonical; exact (proj1 (proj2 signature_budgets))|].
      split; [exact (proj2 (proj2 signature_budgets))|].
      intros other Hhit; rewrite Hcanonical, Hcollision in Hhit; injection Hhit as <-.
      exact collision_union_budget.
Qed.

Local Lemma concrete_batch_budget :
  EggCost.batch_budget alg (EggParent.get (Egraph.parents popped) 3%positive)
    popped 100000%N 256%N 1%N 1%N.
Proof.
  rewrite (proj2 (proj2 (proj2 (proj2 parent_observations)))).
  split; [exact concrete_parent_budget|exact I].
Qed.

Local Opaque popped.

(** The nonempty parent batch applies repair_cost with its concrete callback and bucket duties. *)
Theorem concrete_repair_cost :
  (Cost.ticks (Egraph.repair_c alg popped 3%positive) <= 607975)%N.
Proof.
  eapply N.le_trans.
  - exact (EggCost.repair_cost alg popped 3%positive 100000%N 256%N 1%N 1%N
      (dense_query 3%positive ltac:(cbn [In]; intuition)) concrete_batch_budget).
  - rewrite (proj2 (proj2 (proj2 (proj2 parent_observations)))).
    reflexivity.
Qed.

Local Transparent popped.

(** The actual dirty queue selects one parent and the repaired graph has no remaining work. *)
Example queue_observations :
  EggPending.pop (Egraph.pending (Egraph.private dirty)) =
    Some (3%positive, EggPending.empty) /\
  EggPending.pop (Egraph.pending (Egraph.private after)) = None /\
  Egraph.dirty dirty = [3%positive] /\
  length (Egraph.edges dirty) = 1 /\
  length (Egraph.edges after) = 2 /\
  N.pos (Pos.size (Egraph.rebuild_fuel dirty)) = 5%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Local Lemma actual_batch_result : Egraph.repair alg popped 3%positive = (after, 1%N).
Proof.
  change (EggRebuild.repair alg popped 3%positive = (after, 1%N)).
  rewrite EggRebuild.repair_equation.
  rewrite (proj2 (proj2 (proj2 (proj2 parent_observations)))).
  reflexivity.
Qed.

Local Lemma dirty_step_value count :
  Cost.value (Egraph.dirty_step_c alg (dirty, count)) = inl (after, (count + 1)%N).
Proof.
  rewrite EggRebuild.dirty_step_equation, (proj1 queue_observations).
  cbv zeta; fold popped.
  change (inl (fst (Egraph.repair alg popped 3%positive),
    N.add count (snd (Egraph.repair alg popped 3%positive))) =
    (@inl (Egraph.t nat bool nat * N) (Egraph.t nat bool nat * N)
      (after, (count + 1)%N))).
  rewrite actual_batch_result; reflexivity.
Qed.

Local Lemma after_step_value count :
  Cost.value (Egraph.dirty_step_c alg (after, count)) = inr (after, count).
Proof.
  rewrite EggRebuild.dirty_step_equation, (proj1 (proj2 queue_observations)); reflexivity.
Qed.

Local Lemma stopped_prefix used state final :
  Cost.value (Egraph.dirty_step_c alg state) = inr state ->
  runs (Egraph.dirty_step_c alg) used state (inl final) ->
  used = 0 /\ final = state.
Proof.
  intros Hstop Hprefix.
  inversion Hprefix as
    [s|n s result Hstopped|n s next result Hnext Hrest]; subst.
  - split; reflexivity.
  - rewrite Hstop in Hnext; discriminate.
Qed.

(** Every continuing prefix of this same actual run is its input or its one repaired state. *)
Theorem actual_prefix_states used state :
  runs (Egraph.dirty_step_c alg) used (dirty, 0%N) (inl state) ->
  (used = 0 /\ state = (dirty, 0%N)) \/
    (used = 1 /\ state = (after, 1%N)).
Proof.
  intro Hprefix.
  inversion Hprefix as
    [s|n s result Hstopped|n s next result Hnext Hrest]; subst.
  - left; split; reflexivity.
  - rewrite (dirty_step_value 0%N) in Hnext; injection Hnext as <-.
    destruct (stopped_prefix _ _ _ (after_step_value 1%N) Hrest) as [Hused Hstate].
    right; split; [clear - Hused; lia|exact Hstate].
Qed.

(** All actual-prefix primitive duties are proved from the identified nonempty parent batch. *)
Theorem concrete_loop_budget : EggCost.loop_budget alg dirty 100000%N 256%N 1%N 1%N.
Proof.
  intros used h count Hprefix Hfuel loser queue Hpop.
  destruct (actual_prefix_states used (h, count) Hprefix)
    as [[Hused Hstate]|[Hused Hstate]].
  - injection Hstate as -> ->.
    rewrite (proj1 queue_observations) in Hpop; injection Hpop as <- <-.
    split; [apply dense_query; cbn [In]; intuition|].
    split.
    + change (N.of_nat (length (EggParent.get (Egraph.parents popped) 3%positive)) <= 1)%N.
      rewrite (proj2 (proj2 (proj2 (proj2 parent_observations)))); reflexivity.
    + exact concrete_batch_budget.
  - injection Hstate as -> ->.
    rewrite (proj1 (proj2 queue_observations)) in Hpop; discriminate.
Qed.

(** The proved concrete primitive trace certificate discharges the actual finite bucket cap. *)
Theorem concrete_bucket_budget : EggCost.bucket_budget alg dirty 1%N.
Proof.
  exact (EggCost.loop_bucket_budget alg dirty 100000%N 256%N 1%N 1%N concrete_loop_budget).
Qed.

(** The public binary driver stops at the same state identified by the actual prefix theorem. *)
Example actual_iterator_value :
  Cost.value (iterate (Egraph.dirty_step_c alg) (Egraph.rebuild_fuel dirty) (dirty, 0%N)) =
    inr (after, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** Public run and numerical clients consume observations without reducing the graph bodies. *)
Local Opaque dirty after.

(** The observed value is certified by the public driver's actual run relation. *)
Theorem actual_run_stops :
  runs (Egraph.dirty_step_c alg) (Pos.to_nat (Egraph.rebuild_fuel dirty))
    (dirty, 0%N) (inr (after, 1%N)).
Proof.
  rewrite <- actual_iterator_value; apply iterate_value.
Qed.

Local Lemma actual_counted_result :
  Cost.value (Egraph.rebuild_run_c alg dirty) = (after, 1%N).
Proof.
  rewrite Egraph.rebuild_run_equation, actual_iterator_value; reflexivity.
Qed.

(** Public projection equations identify both observations of the same counted rebuild. *)
Theorem actual_rebuild_result :
  Egraph.rebuild alg dirty = after /\ Egraph.rebuild_repairs alg dirty = 1%N.
Proof.
  split.
  - rewrite Egraph.rebuild_equation, actual_counted_result; reflexivity.
  - unfold Egraph.rebuild_repairs; rewrite actual_counted_result; reflexivity.
Qed.

(** The headline rebuild contract now yields a numerical price with no budget premises left. *)
Theorem concrete_rebuild_cost :
  (Cost.ticks (Egraph.rebuild_c alg dirty) <= 608242)%N.
Proof.
  eapply N.le_trans.
  - exact (EggCost.rebuild_cost alg (EggSpec.node_code_injective alg alg_encoding_laws)
      dirty (EggSpec.wf_kernel alg dirty dirty_wf)
      (EggMaintained.layout alg dirty (EggSpec.wf_structural alg dirty dirty_wf))
      100000%N 256%N 1%N 1%N concrete_loop_budget).
  - rewrite (proj2 actual_rebuild_result),
      (proj2 (proj2 (proj2 (proj2 (proj2 queue_observations))))).
    reflexivity.
Qed.

(** The total-repair contract bounds visits using concrete queue and new-edge counts. *)
Theorem concrete_rebuild_repairs_total :
  (Egraph.rebuild_repairs alg dirty <= 2)%N.
Proof.
  pose proof (EggCost.rebuild_repairs_total alg dirty 1%N concrete_bucket_budget) as Htotal.
  destruct queue_observations as [Hpop [Hstop [Hdirty [Hedges [Hafter Hfuel]]]]].
  rewrite (proj1 actual_rebuild_result), Hedges, Hdirty, Hafter in Htotal.
  cbn [length] in Htotal.
  assert (Hlinear : forall n : N, (n + 1 <= 3 -> n <= 2)%N).
  { intros n Hbound; lia. }
  apply Hlinear; exact Htotal.
Qed.

(** The same actual numerical rebuild run visits its queued parent. *)
Theorem concrete_rebuild_positive_repairs :
  (0 < Egraph.rebuild_repairs alg dirty)%N.
Proof.
  rewrite (proj2 actual_rebuild_result); reflexivity.
Qed.

End EggKernelConcreteClient.
