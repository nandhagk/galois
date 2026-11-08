(** * Evidence for the collision base used by actual repair

    Memo collisions are validated from stored-node snapshots before the signature is replaced.
    For example, a collision union preserves old parent obligations and resolves the observed class.
    Builds on: EgraphCoreRepair, EgraphCoreTransition and public Base union laws. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphCoreIndex EgraphCoreInvariant EgraphCoreTransition
  EgraphCoreRepair.
Import List.ListNotations.

Module EggObservation.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).
Context {work : list Egraph.id} (g : Egraph.t K Sort V) (i : Egraph.id)
  (n : Egraph.enode K Sort V).
Context (Hinv : Egraph.kernel_inv_on a g work) (Hlayout : EggTransition.layout a g).
Context (Hcodes : forall first second,
  Egraph.node_code a first = Egraph.node_code a second -> first = second).
Context (Hnode : Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n).

Let key := Egraph.node_code a (Egraph.canonical a g n).
Let base := Egraph.repair_base a g i key.

(** The actual collision base is a merge after its sort checks are proved successful. *)
Theorem base_equation :
  base = match Map.get Egraph.id_encoding key (Egraph.memo g) with
    | None => g
    | Some other => Egraph.merge a g i other (Egraph.JCongruence i other)
    end.
Proof.
  unfold base; rewrite Egraph.repair_base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|] eqn:Hhit;
    [|reflexivity].
  destruct (EggRepairInv.collision_witness a g n other Hinv
    (EggTransition.forest_wf a g Hlayout) Hcodes Hhit) as [m [Hother Hcanonical]].
  rewrite (EggRepairInv.congruent_union_equation a g i other n m _ Hnode Hother Hcanonical).
  reflexivity.
Qed.

(** Each observed collision queries allocated class roots in the original graph. *)
Theorem collision_roots other :
  Map.get Egraph.id_encoding key (Egraph.memo g) = Some other ->
  (Egraph.find a g i < Egraph.next g)%positive /\
  (Egraph.find a g other < Egraph.next g)%positive.
Proof.
  intro Hhit; split.
  - exact (EggTransition.allocated_roots a g Hlayout i n Hnode).
  - destruct (EggRepairInv.collision_witness a g n other Hinv
      (EggTransition.forest_wf a g Hlayout) Hcodes Hhit) as [m [Hother Hcanonical]].
    exact (EggTransition.allocated_roots a g Hlayout other m Hother).
Qed.

(** The collision base retains every stored production. *)
Theorem base_nodes : Egraph.nodes base = Egraph.nodes g.
Proof.
  rewrite base_equation; destruct (Map.get Egraph.id_encoding key (Egraph.memo g)); reflexivity.
Qed.

(** Collision union does not rewrite the memo table. *)
Theorem base_memo : Egraph.memo base = Egraph.memo g.
Proof.
  rewrite base_equation; destruct (Map.get Egraph.id_encoding key (Egraph.memo g)); reflexivity.
Qed.

(** Collision union does not allocate an identifier. *)
Theorem base_next : Egraph.next base = Egraph.next g.
Proof.
  rewrite base_equation; destruct (Map.get Egraph.id_encoding key (Egraph.memo g)); reflexivity.
Qed.

(** Collision union retains each historical signature snapshot. *)
Theorem base_cached : Egraph.cached base = Egraph.cached g.
Proof.
  rewrite base_equation; destruct (Map.get Egraph.id_encoding key (Egraph.memo g));
    [apply EggTransition.merge_cached|reflexivity].
Qed.

(** Every original parent occurrence remains indexed in the collision base. *)
Theorem base_parent root parent :
  In parent (EggParent.get (Egraph.parents g) root) ->
  In parent (EggParent.get (Egraph.parents base) root).
Proof.
  intro Hin; rewrite base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|]; [|exact Hin].
  exact (EggTransition.merge_parent_mono a g i other _ root parent Hinv Hin).
Qed.

(** Old queue and active-batch obligations remain protected by the collision base. *)
Theorem base_work protected parent :
  Egraph.pending_work g protected parent -> Egraph.pending_work base protected parent.
Proof.
  intro Hin; rewrite base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|]; [|exact Hin].
  exact (EggTransition.merge_work_mono a g i other _ protected parent Hinv Hin).
Qed.

(** The collision base preserves every old class equality through its actual UF call. *)
Theorem base_classes x y :
  Egraph.find a g x = Egraph.find a g y -> Egraph.find a base x = Egraph.find a base y.
Proof.
  intro Hsame; rewrite base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|]; [|exact Hsame].
  exact (EggTransition.merge_class_mono a g i other _ x y
    (EggTransition.forest_wf a g Hlayout) Hsame).
Qed.

(** The actual collision base identifies the queried class and its observed memo class. *)
Theorem base_resolves other :
  Map.get Egraph.id_encoding key (Egraph.memo g) = Some other ->
  Egraph.find a base i = Egraph.find a base other.
Proof.
  intro Hhit; rewrite base_equation, Hhit.
  apply EggTransition.merge_same; exact (EggTransition.forest_wf a g Hlayout).
Qed.

(** The actual collision base maintains local coverage for the still-unvisited batch. *)
Theorem base_kernel_inv : Egraph.kernel_inv_on a base work.
Proof.
  rewrite base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|] eqn:Hhit;
    [|exact Hinv].
  destruct (collision_roots other Hhit) as [Hi Hother].
  exact (EggKernelInv.merge_kernel_inv a g i other _ Hinv
    (EggTransition.forest_wf a g Hlayout) Hi Hother).
Qed.

(** Nodes absent from all new dirty buckets retain their original canonical signatures. *)
Theorem base_signature parent node :
  Map.get Egraph.id_encoding parent (Egraph.nodes g) = Some node ->
  ~ Egraph.pending_node base parent ->
  Egraph.canonical a base node = Egraph.canonical a g node.
Proof.
  intros Hparent Hnot; rewrite base_equation in Hnot |- *.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|] eqn:Hhit;
    [|reflexivity].
  destruct (collision_roots other Hhit) as [Hi Hother].
  exact (EggKernelInv.merge_signature_stable a g i other _ Hinv
    (EggTransition.forest_wf a g Hlayout) Hi Hother parent node Hparent Hnot).
Qed.

(** The collision base retains the precise forest, Map and root-domain duties used by repair. *)
Theorem base_layout : EggTransition.layout a base.
Proof.
  rewrite base_equation.
  destruct (Map.get Egraph.id_encoding key (Egraph.memo g)) as [other|] eqn:Hhit;
    [|exact Hlayout].
  destruct (collision_roots other Hhit) as [Hi Hother].
  constructor.
  - apply UnionFind.wf_union.
    + exact positive_encoding_laws.
    + exact (EggTransition.forest_wf a g Hlayout).
  - exact (EggTransition.nodes_wf a g Hlayout).
  - exact (EggTransition.memo_wf a g Hlayout).
  - intros query node Hquery.
    change (Map.get Egraph.id_encoding query (Egraph.nodes g) = Some node) in Hquery.
    exact (EggTransition.merge_find_bound a g i other _ query
      (EggTransition.forest_wf a g Hlayout) Hi Hother
      (EggTransition.allocated_roots a g Hlayout query node Hquery)).
Qed.

End Graph.

End EggObservation.
