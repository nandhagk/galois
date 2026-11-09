(** * Coverage while a dirty parent batch is in progress

    Dequeueing transfers one bucket's obligations to the unvisited repair list.
    For example, a parent stays protected after its losing class leaves the queue.
    Builds on: EgraphGraph, EgraphCoreIndex and EgraphCoreInvariant. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph EgraphCoreIndex EgraphCoreInvariant.
Import List.ListNotations.

Module EggRepairInv.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** Queue replacement maintains the invariant when every old obligation remains covered. *)
Theorem requeue_kernel_inv {oldwork newwork} g queue :
  Egraph.kernel_inv_on a g oldwork ->
  EggPending.wf queue ->
  (forall root, In root (EggPending.entries queue) -> In root (Egraph.dirty g)) ->
  (forall i, Egraph.pending_work g oldwork i ->
    Egraph.pending_work (Egraph.with_queue g queue) newwork i) ->
  Egraph.kernel_inv_on a (Egraph.with_queue g queue) newwork.
Proof.
  intros Hinv Hqueue Hsubset Hcoverage; constructor.
  - exact (Egraph.parent_map_wf a g Hinv).
  - exact (Egraph.snapshot_map_wf a g Hinv).
  - exact Hqueue.
  - exact (Egraph.snapshot_complete a g Hinv).
  - exact (Egraph.snapshot_correct a g Hinv).
  - exact (Egraph.current_parents a g Hinv).
  - exact (Egraph.snapshot_parents a g Hinv).
  - exact (Egraph.indexed_nodes a g Hinv).
  - intros root Hin; apply (Egraph.pending_nonempty a g Hinv root), Hsubset, Hin.
  - intros root Hin; apply (Egraph.pending_allocated a g Hinv root), Hsubset, Hin.
  - intros i n old Hnode Hget Hnot.
    exact (Egraph.stable_snapshot a g Hinv i n old Hnode Hget
      (fun Hin => Hnot (Hcoverage i Hin))).
  - exact (Egraph.memo_owner a g Hinv).
  - intros i n Hnode Hnot.
    exact (Egraph.stable_memo a g Hinv i n Hnode (fun Hin => Hnot (Hcoverage i Hin))).
  - exact (Egraph.reasons_forest a g Hinv).
  - exact (Egraph.reasons_correct a g Hinv).
Qed.

(** An actual dequeue transfers all selected parent obligations into the active batch. *)
Theorem pop_kernel_inv g loser queue :
  Egraph.kernel_inv a g ->
  EggPending.pop (Egraph.pending (Egraph.private g)) = Some (loser, queue) ->
  Egraph.kernel_inv_on a (Egraph.with_queue g queue)
    (EggParent.get (Egraph.parents g) loser).
Proof.
  intros Hinv Hpop.
  pose proof (EggPending.pop_entries _ _ _ Hpop) as Hentries.
  apply (requeue_kernel_inv (oldwork := []) g queue Hinv).
  - exact (EggPending.pop_wf _ _ _ (Egraph.pending_wf a g Hinv) Hpop).
  - intros root Hin; unfold Egraph.dirty; rewrite Hentries; right; exact Hin.
  - intros i [root [Hdirty Hparent]].
    unfold Egraph.dirty in Hdirty; rewrite Hentries in Hdirty.
    destruct Hdirty as [<-|Hdirty].
    + unfold Egraph.pending_work.
      destruct (EggParent.get (Egraph.parents g) loser); [contradiction|right; exact Hparent].
    + assert (Hpending : Egraph.pending_node (Egraph.with_queue g queue) i).
      { exists root; split; [exact Hdirty|exact Hparent]. }
      destruct (EggParent.get (Egraph.parents g) loser); cbn [Egraph.pending_work]; auto.
Qed.

(** Removing a nonexistent node from the batch preserves coverage of stored productions. *)
Theorem absent_parent_kernel_inv g i work :
  Egraph.kernel_inv_on a g (i :: work) ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = None ->
  Egraph.kernel_inv_on a g work.
Proof.
  intros Hinv Habsent.
  assert (Hstable : forall j n, Map.get Egraph.id_encoding j (Egraph.nodes g) = Some n ->
    ~ Egraph.pending_work g work j -> ~ Egraph.pending_work g (i :: work) j).
  { intros j n Hnode Hnot [Hpending|Hin].
    - apply Hnot; destruct work; cbn [Egraph.pending_work]; auto.
    - destruct Hin as [<-|Hin]; [congruence|].
      apply Hnot; destruct work; cbn [Egraph.pending_work In] in *; tauto. }
  constructor.
  - exact (Egraph.parent_map_wf a g Hinv).
  - exact (Egraph.snapshot_map_wf a g Hinv).
  - exact (Egraph.pending_wf a g Hinv).
  - exact (Egraph.snapshot_complete a g Hinv).
  - exact (Egraph.snapshot_correct a g Hinv).
  - exact (Egraph.current_parents a g Hinv).
  - exact (Egraph.snapshot_parents a g Hinv).
  - exact (Egraph.indexed_nodes a g Hinv).
  - exact (Egraph.pending_nonempty a g Hinv).
  - exact (Egraph.pending_allocated a g Hinv).
  - intros j n old Hnode Hget Hnot.
    exact (Egraph.stable_snapshot a g Hinv j n old Hnode Hget (Hstable j n Hnode Hnot)).
  - exact (Egraph.memo_owner a g Hinv).
  - intros j n Hnode Hnot.
    exact (Egraph.stable_memo a g Hinv j n Hnode (Hstable j n Hnode Hnot)).
  - exact (Egraph.reasons_forest a g Hinv).
  - exact (Egraph.reasons_correct a g Hinv).
Qed.

(** A memo collision yields an actual stored-node witness with the same current canonical node. *)
Theorem collision_witness {work} g n other :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (forall first second, Egraph.node_code a first = Egraph.node_code a second -> first = second) ->
  Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g) = Some other ->
  exists m, Map.get Egraph.id_encoding other (Egraph.nodes g) = Some m /\
    Egraph.canonical a g n = Egraph.canonical a g m.
Proof.
  intros Hinv Hforest Hcodes Hmemo.
  destruct (Egraph.memo_owner a g Hinv _ other Hmemo) as [old [Hsnapshot Hcode]].
  apply Hcodes in Hcode; subst old.
  destruct (Egraph.snapshot_correct a g Hinv other _ Hsnapshot) as [m [Hnode Hcanonical]].
  exists m; split; [exact Hnode|].
  rewrite (EggKernelInv.canonical_idem a g n Hforest) in Hcanonical; exact Hcanonical.
Qed.

Local Lemma canonical_sort g n :
  Egraph.node_sort (Egraph.canonical a g n) = Egraph.node_sort n.
Proof.
  destruct n; rewrite Egraph.canonical_equation; reflexivity.
Qed.

(** Stored nodes with equal canonical syntax pass union's actual allocation and sort checks. *)
Theorem congruent_union_equation g i j n m reason :
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.union_j a g i j reason = Some (Egraph.merge a g i j reason).
Proof.
  intros Hi Hj Hcanonical.
  assert (Hsort : Egraph.node_sort n = Egraph.node_sort m).
  { apply (f_equal Egraph.node_sort) in Hcanonical.
    rewrite !canonical_sort in Hcanonical; exact Hcanonical. }
  assert (Hsi : Egraph.sort_of a g i = Some (Egraph.node_sort n)).
  { change (option_map Egraph.node_sort (Map.get Egraph.id_encoding i (Egraph.nodes g)) =
      Some (Egraph.node_sort n)).
    rewrite Hi; reflexivity. }
  assert (Hsj : Egraph.sort_of a g j = Some (Egraph.node_sort m)).
  { change (option_map Egraph.node_sort (Map.get Egraph.id_encoding j (Egraph.nodes g)) =
      Some (Egraph.node_sort m)).
    rewrite Hj; reflexivity. }
  rewrite <- Hsort in Hsj.
  rewrite Egraph.union_j_equation, Hsi, Hsj.
  rewrite (proj2 (Map.code_compare_eq _ _) eq_refl); reflexivity.
Qed.

Local Lemma set_lookup {A} (m : Map.t Egraph.id A) key value query :
  Map.wf Egraph.id_encoding m ->
  Map.get Egraph.id_encoding query (Map.set Egraph.id_encoding key value m) =
    if Pos.eq_dec query key then Some value else Map.get Egraph.id_encoding query m.
Proof.
  intro Hwf; destruct (Pos.eq_dec query key) as [->|Hne].
  - apply Map.get_set_same; exact Hwf.
  - apply Map.get_set_other; [exact positive_encoding_laws|exact Hwf|exact Hne].
Qed.

Local Lemma active_tail_stable (g : Egraph.t K Sort V) i work j :
  j <> i -> ~ Egraph.pending_work g work j -> ~ Egraph.pending_work g (i :: work) j.
Proof.
  intros Hne Hnot [Hpending|Hin].
  - apply Hnot; destruct work; cbn [Egraph.pending_work]; auto.
  - destruct Hin as [Heq|Hin]; [congruence|].
    apply Hnot; destruct work; cbn [Egraph.pending_work In] in *; tauto.
Qed.

(** Signature installation discharges its parent under justified collision-class duties. *)
Theorem install_kernel_inv g i work n historical current :
  Egraph.kernel_inv_on a g (i :: work) ->
  Map.wf Egraph.id_encoding (Egraph.memo g) ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  Map.get Egraph.id_encoding i (Egraph.cached g) = Some historical ->
  Egraph.canonical a g current = Egraph.canonical a g n ->
  (forall child, In child (Egraph.node_children current) ->
    In i (EggParent.get (Egraph.parents g) child)) ->
  (~ Egraph.pending_work g work i -> current = Egraph.canonical a g n) ->
  (forall j m, Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m ->
    ~ Egraph.pending_work g work j ->
    Egraph.node_code a (Egraph.canonical a g m) = Egraph.node_code a current ->
    Egraph.find a g j = Egraph.find a g i) ->
  (forall j m, Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m ->
    ~ Egraph.pending_work g work j ->
    Egraph.node_code a (Egraph.canonical a g m) = Egraph.node_code a historical ->
    Egraph.node_code a historical = Egraph.node_code a current) ->
  Egraph.kernel_inv_on a
    (Egraph.install g i current (Egraph.node_code a historical) (Egraph.node_code a current))
    work.
Proof.
  intros Hinv Hmemo Hnode Hhistorical Hcompatible Hparents Hcurrent Hcollision Hremove.
  set (oldkey := Egraph.node_code a historical).
  set (key := Egraph.node_code a current).
  set (h := Egraph.install g i current oldkey key).
  assert (Hcache : forall j, Map.get Egraph.id_encoding j (Egraph.cached h) =
    if Pos.eq_dec j i then Some current else Map.get Egraph.id_encoding j (Egraph.cached g)).
  { intro j; change (Map.get Egraph.id_encoding j
      (Map.set Egraph.id_encoding i current (Egraph.cached g)) =
      if Pos.eq_dec j i then Some current else Map.get Egraph.id_encoding j (Egraph.cached g)).
    apply set_lookup; exact (Egraph.snapshot_map_wf a g Hinv). }
  assert (Htable : forall code, Map.get Egraph.id_encoding code (Egraph.memo h) =
    if Pos.eq_dec code key then Some i
    else if Pos.eq_dec code oldkey then None else Map.get Egraph.id_encoding code (Egraph.memo g)).
  { intro code; change (Map.get Egraph.id_encoding code
      (Map.set Egraph.id_encoding key i
        (Map.remove Egraph.id_encoding oldkey (Egraph.memo g))) =
      if Pos.eq_dec code key then Some i
      else if Pos.eq_dec code oldkey then None
      else Map.get Egraph.id_encoding code (Egraph.memo g)).
    rewrite set_lookup by (apply Map.wf_remove; exact Hmemo).
    destruct (Pos.eq_dec code key); [reflexivity|].
    destruct (Pos.eq_dec code oldkey) as [->|Hne].
    - apply Map.get_remove_same.
    - apply Map.get_remove_other; [exact positive_encoding_laws|exact Hne]. }
  constructor.
  - exact (Egraph.parent_map_wf a g Hinv).
  - change (Map.wf Egraph.id_encoding
      (Map.set Egraph.id_encoding i current (Egraph.cached g))).
    apply Map.wf_set; exact (Egraph.snapshot_map_wf a g Hinv).
  - exact (Egraph.pending_wf a g Hinv).
  - intros j m Hget; rewrite Hcache; destruct (Pos.eq_dec j i) as [->|Hne].
    + exists current; reflexivity.
    + exact (Egraph.snapshot_complete a g Hinv j m Hget).
  - intros j old Hget; rewrite Hcache in Hget.
    destruct (Pos.eq_dec j i) as [->|Hne].
    + injection Hget as <-; exists n; split; [exact Hnode|exact Hcompatible].
    + exact (Egraph.snapshot_correct a g Hinv j old Hget).
  - exact (Egraph.current_parents a g Hinv).
  - intros j old child Hget Hin; rewrite Hcache in Hget.
    destruct (Pos.eq_dec j i) as [->|Hne].
    + injection Hget as <-; exact (Hparents child Hin).
    + exact (Egraph.snapshot_parents a g Hinv j old child Hget Hin).
  - exact (Egraph.indexed_nodes a g Hinv).
  - exact (Egraph.pending_nonempty a g Hinv).
  - exact (Egraph.pending_allocated a g Hinv).
  - intros j m old Hget Hsnapshot Hnot.
    change (Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m) in Hget.
    rewrite Hcache in Hsnapshot.
    destruct (Pos.eq_dec j i) as [->|Hne].
    + injection Hsnapshot as <-; assert (m = n) by congruence; subst m.
      exact (Hcurrent Hnot).
    + exact (Egraph.stable_snapshot a g Hinv j m old Hget Hsnapshot
        (active_tail_stable g i work j Hne Hnot)).
  - intros code j Hget; rewrite Htable in Hget.
    destruct (Pos.eq_dec code key) as [->|Hnew].
    + injection Hget as <-; exists current; split; [rewrite Hcache|reflexivity].
      destruct (Pos.eq_dec i i); congruence.
    + destruct (Pos.eq_dec code oldkey) as [->|Hold]; [discriminate|].
      destruct (Egraph.memo_owner a g Hinv code j Hget) as [old [Hsnapshot Hcode]].
      exists old; split; [|exact Hcode].
      rewrite Hcache; destruct (Pos.eq_dec j i) as [->|Hne]; [|exact Hsnapshot].
      assert (old = historical) by congruence; subst old.
      exfalso; apply Hold; symmetry; exact Hcode.
  - intros j m Hget Hnot.
    change (Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m) in Hget.
    change (exists other,
      Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g m))
        (Egraph.memo h) = Some other /\
      Egraph.find a g j = Egraph.find a g other).
    rewrite Htable.
    destruct (Pos.eq_dec (Egraph.node_code a (Egraph.canonical a g m)) key) as [Hnew|Hnew].
    + exists i; split; [reflexivity|apply (Hcollision j m Hget Hnot); exact Hnew].
    + destruct (Pos.eq_dec (Egraph.node_code a (Egraph.canonical a g m)) oldkey)
        as [Hold|Hold].
      * pose proof (Hremove j m Hget Hnot Hold) as Heq.
        change (oldkey = key) in Heq.
        exfalso; apply Hnew; exact (eq_trans Hold Heq).
      * destruct (Pos.eq_dec j i) as [->|Hne].
        -- assert (m = n) by congruence; subst m.
           exfalso; apply Hnew; unfold key; f_equal; symmetry; exact (Hcurrent Hnot).
        -- exact (Egraph.stable_memo a g Hinv j m Hget
             (active_tail_stable g i work j Hne Hnot)).
  - exact (Egraph.reasons_forest a g Hinv).
  - exact (Egraph.reasons_correct a g Hinv).
Qed.

End Graph.

End EggRepairInv.
