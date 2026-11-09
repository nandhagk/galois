(** * Preservation by the actual one-parent repair

    Installation duties follow from the observed memo collision and the actual justified union.
    For example, a stable node sharing the repaired key is related through that memo collision.
    Builds on: EgraphCoreObservation, EgraphCoreRepair and EgraphCoreTransition. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphCoreIndex EgraphCoreInvariant EgraphCoreTransition
  EgraphCoreRepair EgraphCoreObservation.
Import List.ListNotations.

Module EggRepairStep.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

Section Stored.
Context (g : Egraph.t K Sort V) (i : Egraph.id) (work : list Egraph.id)
  (n historical : Egraph.enode K Sort V).
Context (Hinv : Egraph.kernel_inv_on a g (i :: work)) (Hlayout : EggTransition.layout a g).
Context (Hcodes : forall first second,
  Egraph.node_code a first = Egraph.node_code a second -> first = second).
Context (Hnode : Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n)
  (Hhistorical : Map.get Egraph.id_encoding i (Egraph.cached g) = Some historical).

Let current := Egraph.canonical a g n.
Let base := Egraph.repair_base a g i (Egraph.node_code a current).

Local Lemma not_queued j :
  ~ Egraph.pending_work base work j -> ~ Egraph.pending_node base j.
Proof.
  intros Hnot Hin; apply Hnot; exact (EggTransition.pending_in_work base work j Hin).
Qed.

Local Lemma old_stable j :
  j <> i -> ~ Egraph.pending_work base work j ->
  ~ Egraph.pending_work g (i :: work) j.
Proof.
  intros Hne Hnot [Hpending|Hin].
  - apply Hnot.
    apply (EggObservation.base_work a g i n Hinv Hlayout Hcodes Hnode work j).
    exact (EggTransition.pending_in_work g work j Hpending).
  - destruct Hin as [Heq|Hin]; [congruence|].
    apply Hnot.
    apply (EggObservation.base_work a g i n Hinv Hlayout Hcodes Hnode work j).
    exact (EggTransition.tail_in_work g work j Hin).
Qed.

Local Lemma historical_agrees :
  Egraph.canonical a g historical = Egraph.canonical a g n.
Proof.
  destruct (Egraph.snapshot_correct a g Hinv i historical Hhistorical)
    as [other [Hother Hsame]].
  assert (other = n) by congruence; subst other; exact Hsame.
Qed.

Local Lemma observed_compatible :
  Egraph.canonical a base current = Egraph.canonical a base n.
Proof.
  apply (EggKernelInv.canonical_mono a g base current n).
  - intros x y; exact (EggObservation.base_classes a g i n Hinv Hlayout Hcodes Hnode x y).
  - exact (EggKernelInv.canonical_idem a g n (EggTransition.forest_wf a g Hlayout)).
Qed.

Local Lemma observed_parents child :
  In child (Egraph.node_children current) ->
  In i (EggParent.get (Egraph.parents base) child).
Proof.
  intro Hin.
  apply (EggObservation.base_parent a g i n Hinv Hlayout Hcodes Hnode child i).
  exact (EggTransition.canonical_parent_in a g i n child Hinv Hnode Hin).
Qed.

Local Lemma observed_current :
  ~ Egraph.pending_work base work i -> current = Egraph.canonical a base n.
Proof.
  intro Hnot; symmetry.
  exact (EggObservation.base_signature a g i n Hinv Hlayout Hcodes Hnode
    i n Hnode (not_queued i Hnot)).
Qed.

Local Lemma observed_collision j m :
  Map.get Egraph.id_encoding j (Egraph.nodes base) = Some m ->
  ~ Egraph.pending_work base work j ->
  Egraph.node_code a (Egraph.canonical a base m) = Egraph.node_code a current ->
  Egraph.find a base j = Egraph.find a base i.
Proof.
  intros Hstored Hnot Hkey.
  unfold base, current in Hstored, Hnot, Hkey.
  rewrite (EggObservation.base_nodes a g i n Hinv Hlayout Hcodes Hnode) in Hstored.
  destruct (Pos.eq_dec j i) as [->|Hne]; [reflexivity|].
  destruct (Egraph.stable_memo a g Hinv j m Hstored (old_stable j Hne Hnot))
    as [other [Hmemo Hclass]].
  pose proof (EggObservation.base_signature a g i n Hinv Hlayout Hcodes Hnode
    j m Hstored (not_queued j Hnot)) as Hsignature.
  rewrite <- Hsignature, Hkey in Hmemo.
  pose proof (EggObservation.base_resolves a g i n Hinv Hlayout Hcodes Hnode other Hmemo)
    as Hresolved.
  pose proof (EggObservation.base_classes a g i n Hinv Hlayout Hcodes Hnode j other Hclass)
    as Hpreserved.
  exact (eq_trans Hpreserved (eq_sym Hresolved)).
Qed.

Local Lemma observed_remove j m :
  Map.get Egraph.id_encoding j (Egraph.nodes base) = Some m ->
  ~ Egraph.pending_work base work j ->
  Egraph.node_code a (Egraph.canonical a base m) = Egraph.node_code a historical ->
  Egraph.node_code a historical = Egraph.node_code a current.
Proof.
  intros Hstored Hnot Hkey; apply Hcodes in Hkey.
  unfold base, current in Hstored, Hnot, Hkey.
  rewrite (EggObservation.base_nodes a g i n Hinv Hlayout Hcodes Hnode) in Hstored.
  pose proof (EggObservation.base_signature a g i n Hinv Hlayout Hcodes Hnode
    j m Hstored (not_queued j Hnot)) as Hsignature.
  assert (Hliteral : historical = Egraph.canonical a g m) by congruence.
  assert (Hfixed : Egraph.canonical a g historical = historical).
  { rewrite Hliteral.
    exact (EggKernelInv.canonical_idem a g m (EggTransition.forest_wf a g Hlayout)). }
  pose proof historical_agrees as Hagrees; rewrite Hfixed in Hagrees.
  f_equal; exact Hagrees.
Qed.

(** Every installation obligation is derived from the actual original memo and collision union. *)
Theorem observed_install_kernel_inv :
  Egraph.kernel_inv_on a
    (Egraph.install base i current (Egraph.node_code a historical) (Egraph.node_code a current))
    work.
Proof.
  apply (EggRepairInv.install_kernel_inv a base i work n historical current).
  - exact (EggObservation.base_kernel_inv a g i n Hinv Hlayout Hcodes Hnode).
  - exact (EggTransition.memo_wf a base
      (EggObservation.base_layout a g i n Hinv Hlayout Hcodes Hnode)).
  - unfold base, current.
    rewrite (EggObservation.base_nodes a g i n Hinv Hlayout Hcodes Hnode); exact Hnode.
  - unfold base, current.
    rewrite (EggObservation.base_cached a g i n Hinv Hlayout Hcodes Hnode); exact Hhistorical.
  - exact observed_compatible.
  - exact observed_parents.
  - exact observed_current.
  - exact observed_collision.
  - exact observed_remove.
Qed.

End Stored.

(** The actual one-parent callback discharges its batch head and retains the repair layout. *)
Theorem repair_node_correct g i work :
  Egraph.kernel_inv_on a g (i :: work) ->
  EggTransition.layout a g ->
  (forall first second, Egraph.node_code a first = Egraph.node_code a second -> first = second) ->
  Egraph.kernel_inv_on a (Egraph.repair_node a g i) work /\
    EggTransition.layout a (Egraph.repair_node a g i).
Proof.
  intros Hinv Hlayout Hcodes; rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|] eqn:Hnode.
  - destruct (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|] eqn:Hhistorical.
    + cbv zeta; rewrite <- Egraph.repair_base_equation.
      split.
      * exact (observed_install_kernel_inv g i work n historical Hinv Hlayout Hcodes
          Hnode Hhistorical).
      * apply EggTransition.install_layout.
        exact (EggObservation.base_layout a g i n Hinv Hlayout Hcodes Hnode).
    + destruct (Egraph.snapshot_complete a g Hinv i n Hnode) as [old Hsnapshot].
      congruence.
  - split.
    + exact (EggRepairInv.absent_parent_kernel_inv a g i work Hinv Hnode).
    + exact Hlayout.
Qed.

(** Repair leaves stored productions unchanged on both valid and missing-node branches. *)
Theorem repair_node_nodes g i :
  Egraph.nodes (Egraph.repair_node a g i) = Egraph.nodes g.
Proof.
  rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|],
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try reflexivity.
  cbv zeta.
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|];
    [|reflexivity].
  rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g i) as [si|], (Egraph.sort_of a g other) as [so|];
    try reflexivity.
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) si)
    (encode (EggAlg.sort_enc K Sort V a) so)); reflexivity.
Qed.

(** Repair never allocates an identifier. *)
Theorem repair_node_next g i : Egraph.next (Egraph.repair_node a g i) = Egraph.next g.
Proof.
  rewrite Egraph.repair_node_equation.
  destruct (Map.get Egraph.id_encoding i (Egraph.nodes g)) as [n|],
    (Map.get Egraph.id_encoding i (Egraph.cached g)) as [historical|]; try reflexivity.
  cbv zeta.
  destruct (Map.get Egraph.id_encoding
    (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g)) as [other|];
    [|reflexivity].
  rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g i) as [si|], (Egraph.sort_of a g other) as [so|];
    try reflexivity.
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) si)
    (encode (EggAlg.sort_enc K Sort V a) so)); reflexivity.
Qed.

End Graph.

End EggRepairStep.
