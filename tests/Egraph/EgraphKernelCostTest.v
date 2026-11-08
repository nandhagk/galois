(** * Parent-index and repair-queue cost boundaries

    Parent concatenation retains its losing snapshot and charges the copied list.
    For example, merging two singleton buckets retains both occurrences in the winning bucket.
    Builds on: EgraphCoreIndex and EgraphKernelCost. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind BaseUnionFindRank.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphSpec EgraphCoreIndex EgraphCoreInvariant
  EgraphRebuild EgraphKernelCost.
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

(** Successful leaf insertion establishes maintained coverage through the public computational entry. *)
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
  - exact (EggSpec.forest_wf alg g Hstruct).
  - exact (EggSpec.nodes_wf alg g Hstruct).
  - exact (EggSpec.memo_wf alg g Hstruct).
  - destruct (Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g))
      as [old|] eqn:Hlookup; [|reflexivity].
    assert (Hbound : (Egraph.next g < Egraph.next g)%positive).
    { apply (proj1 (EggSpec.allocation alg g Hstruct (Egraph.next g))); exists old; exact Hlookup. }
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
  - exact (EggSpec.add_node_wf alg Egraph.empty (Egraph.NVar true 1) c g
      alg_encoding_laws (EggSpec.empty_wf alg) Hleaf).
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

End EggKernelPrimitiveTest.
