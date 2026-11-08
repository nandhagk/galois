(** * Local transport through actual kernel transitions

    Union preserves old parent obligations and identifies its actual input classes.
    For example, a pending parent remains pending when another loser is scheduled.
    Builds on: EgraphGraph, EgraphCoreInvariant and public Base forest contracts. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph EgraphCoreIndex EgraphCoreInvariant.
Import List.ListNotations.

Module EggTransition.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** Repair uses forest and Map laws and allocated-query bounds independently of semantics. *)
Record layout (g : Egraph.t K Sort V) : Prop := Layout {
  forest_wf : UnionFind.wf Egraph.id_encoding (Egraph.uf g);
  nodes_wf : Map.wf Egraph.id_encoding (Egraph.nodes g);
  memo_wf : Map.wf Egraph.id_encoding (Egraph.memo g);
  allocated_roots : forall c n, Map.get Egraph.id_encoding c (Egraph.nodes g) = Some n ->
    (Egraph.find a g c < Egraph.next g)%positive
}.

(** Updating only the scheduling queue preserves all repair layout duties. *)
Theorem queue_layout g queue :
  layout g -> layout (Egraph.with_queue g queue).
Proof.
  intro Hlayout; constructor.
  - exact (forest_wf g Hlayout).
  - exact (nodes_wf g Hlayout).
  - exact (memo_wf g Hlayout).
  - exact (allocated_roots g Hlayout).
Qed.

(** Signature installation preserves the forest and nodes and maintains the updated memo Map. *)
Theorem install_layout g i current oldkey key :
  layout g -> layout (Egraph.install g i current oldkey key).
Proof.
  intro Hlayout; constructor.
  - exact (forest_wf g Hlayout).
  - exact (nodes_wf g Hlayout).
  - apply Map.wf_set, Map.wf_remove; exact (memo_wf g Hlayout).
  - exact (allocated_roots g Hlayout).
Qed.

(** Dirty buckets are part of the protected work for every active batch. *)
Theorem pending_in_work (g : Egraph.t K Sort V) work i :
  Egraph.pending_node g i -> Egraph.pending_work g work i.
Proof.
  intro Hin; destruct work; cbn [Egraph.pending_work]; auto.
Qed.

(** A batch-tail occurrence remains protected independently of queued dirty classes. *)
Theorem tail_in_work (g : Egraph.t K Sort V) work i :
  In i work -> Egraph.pending_work g work i.
Proof.
  intro Hin; destruct work; cbn [Egraph.pending_work In] in *; tauto.
Qed.

(** Canonical child IDs already have the stored node in their original parent buckets. *)
Theorem canonical_parent_in {work} g i n child :
  Egraph.kernel_inv_on a g work ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  In child (Egraph.node_children (Egraph.canonical a g n)) ->
  In i (EggParent.get (Egraph.parents g) child).
Proof.
  intros Hinv Hnode Hin; destruct n as [s v|s op cs];
    rewrite Egraph.canonical_equation in Hin; cbn [Egraph.node_children] in Hin;
    [contradiction|].
  apply in_map_iff in Hin as [raw [<- Hin]].
  exact (Egraph.current_parents a g Hinv i _ raw Hnode Hin).
Qed.

(** Union never removes an occurrence from an old parent bucket. *)
Theorem merge_parent_mono {work} g c d reason root i :
  Egraph.kernel_inv_on a g work ->
  In i (EggParent.get (Egraph.parents g) root) ->
  In i (EggParent.get (Egraph.parents (Egraph.merge a g c d reason)) root).
Proof.
  intros Hinv Hin; unfold Egraph.parents at 1.
  rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d)); [exact Hin|].
  rewrite Egraph.linked_kernel_equation; cbn [Egraph.parent_index].
  apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv)));
    left; exact Hin.
Qed.

(** Union retains every old dirty-class membership while possibly adding its selected loser. *)
Theorem merge_dirty_mono {work} g c d reason root :
  Egraph.kernel_inv_on a g work ->
  In root (Egraph.dirty g) -> In root (Egraph.dirty (Egraph.merge a g c d reason)).
Proof.
  intros Hinv Hin; unfold Egraph.dirty at 1.
  rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d)); [exact Hin|].
  rewrite Egraph.linked_kernel_equation; cbn [Egraph.pending].
  destruct (EggParent.get (Egraph.parents g)
    (if Pos.eqb
      (fst (UnionFind.find Egraph.id_encoding c
        (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)))) (Egraph.find a g c)
     then Egraph.find a g d else Egraph.find a g c)); [exact Hin|].
  apply (proj2 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv)));
    right; exact Hin.
Qed.

(** An already pending node remains covered through the actual union metadata update. *)
Theorem merge_pending_mono {work} g c d reason i :
  Egraph.kernel_inv_on a g work ->
  Egraph.pending_node g i -> Egraph.pending_node (Egraph.merge a g c d reason) i.
Proof.
  intros Hinv [root [Hdirty Hparent]]; exists root; split.
  - exact (merge_dirty_mono g c d reason root Hinv Hdirty).
  - exact (merge_parent_mono g c d reason root i Hinv Hparent).
Qed.

(** Work-list coverage is monotone through union without enumerating any graph support. *)
Theorem merge_work_mono {oldwork} g c d reason work i :
  Egraph.kernel_inv_on a g oldwork ->
  Egraph.pending_work g work i ->
  Egraph.pending_work (Egraph.merge a g c d reason) work i.
Proof.
  intros Hinv Hin; destruct work; cbn [Egraph.pending_work] in *.
  - exact (merge_pending_mono g c d reason i Hinv Hin).
  - destruct Hin as [Hin|Hin]; [left; exact (merge_pending_mono g c d reason i Hinv Hin)|auto].
Qed.

(** Union leaves historical signature snapshots unchanged. *)
Theorem merge_cached g c d reason :
  Egraph.cached (Egraph.merge a g c d reason) = Egraph.cached g.
Proof.
  unfold Egraph.cached at 1; rewrite Egraph.merge_equation; cbn [Egraph.private].
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct (Pos.eqb (Egraph.find a g c) (Egraph.find a g d)); [reflexivity|].
  rewrite Egraph.linked_kernel_equation; reflexivity.
Qed.

(** Old class equalities survive the actual Base union in the merged graph. *)
Theorem merge_class_mono g c d reason x y :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.find a g x = Egraph.find a g y ->
  Egraph.find a (Egraph.merge a g c d reason) x =
    Egraph.find a (Egraph.merge a g c d reason) y.
Proof.
  intros Hforest Hsame.
  change (UnionFind.equiv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)) x y).
  apply (proj2 (UnionFind.union_equiv Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) c d x y Hforest)); left; exact Hsame.
Qed.

(** The actual merged forest identifies its two inputs without support restrictions. *)
Theorem merge_same g c d reason :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.find a (Egraph.merge a g c d reason) c =
    Egraph.find a (Egraph.merge a g c d reason) d.
Proof.
  intro Hforest.
  change (UnionFind.equiv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g)) c d).
  apply (proj2 (UnionFind.union_equiv Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) c d c d Hforest)); right; left; split; reflexivity.
Qed.

(** Merging already equal classes preserves every exact representative, including unknown keys. *)
Theorem merge_same_representatives g c d reason query :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.find a g c = Egraph.find a g d ->
  Egraph.find a (Egraph.merge a g c d reason) query = Egraph.find a g query.
Proof.
  intros Hforest Hsame.
  change (fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) =
    fst (UnionFind.find Egraph.id_encoding d (Egraph.uf g))) in Hsame.
  pose proof (UnionFind.find_rep_stable Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) d c Hforest) as Hstable.
  destruct (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) as [rc first] eqn:Hfirst.
  destruct (UnionFind.find Egraph.id_encoding d first) as [rd second] eqn:Hsecond.
  cbn [fst snd] in Hsame, Hstable; rewrite ?Hsecond in Hstable; cbn [fst] in Hstable.
  assert (Hequal : rc = rd) by congruence.
  assert (Hcondition : eqb Egraph.id_encoding rc rd = true).
  { rewrite Hequal; apply eqb_refl. }
  change (fst (UnionFind.find Egraph.id_encoding query
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))) =
    fst (UnionFind.find Egraph.id_encoding query (Egraph.uf g))).
  rewrite (UnionFind.union_rep_equation Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) c d query Hforest), Hfirst, Hsecond.
  cbv beta iota zeta; rewrite Hcondition; reflexivity.
Qed.

(** Equality of canonical nodes is preserved by the actual class merge. *)
Theorem merge_canonical_mono g c d reason n m :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.canonical a (Egraph.merge a g c d reason) n =
    Egraph.canonical a (Egraph.merge a g c d reason) m.
Proof.
  intros Hforest Hsame.
  apply (EggKernelInv.canonical_mono a g (Egraph.merge a g c d reason) n m).
  - intros x y; exact (merge_class_mono g c d reason x y Hforest).
  - exact Hsame.
Qed.

(** A merged representative is bounded by the three bounded input representatives it can select. *)
Theorem merge_find_bound g c d reason query :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  (Egraph.find a g query < Egraph.next g)%positive ->
  (Egraph.find a (Egraph.merge a g c d reason) query < Egraph.next g)%positive.
Proof.
  intros Hforest Hc Hd Hquery.
  pose proof (UnionFind.find_rep_stable Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) d c Hforest) as Hstable.
  destruct (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) as [rc first] eqn:Hfirst.
  destruct (UnionFind.find Egraph.id_encoding d first) as [rd second] eqn:Hsecond.
  assert (Hrc : (rc < Egraph.next g)%positive).
  { change (fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) < Egraph.next g)%positive
      in Hc; rewrite Hfirst in Hc; exact Hc. }
  assert (Hrd : (rd < Egraph.next g)%positive).
  { cbn [fst snd] in Hstable; rewrite ?Hsecond in Hstable.
    cbn [fst] in Hstable.
    rewrite Hstable; exact Hd. }
  change (fst (UnionFind.find Egraph.id_encoding query
    (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))) < Egraph.next g)%positive.
  rewrite (UnionFind.union_rep_equation Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) c d query Hforest), Hfirst, Hsecond.
  cbv beta iota zeta.
  fold (Egraph.find a g query).
  destruct (eqb Egraph.id_encoding rc rd); [exact Hquery|].
  destruct (Nat.compare (UnionFind.rank_of Egraph.id_encoding second rc)
    (UnionFind.rank_of Egraph.id_encoding second rd));
    destruct (eqb Egraph.id_encoding
      (fst (UnionFind.find Egraph.id_encoding query (Egraph.uf g))) rc),
      (eqb Egraph.id_encoding
        (fst (UnionFind.find Egraph.id_encoding query (Egraph.uf g))) rd); try assumption.
  all: exact Hquery.
Qed.

End Graph.

End EggTransition.
