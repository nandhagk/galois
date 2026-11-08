(** * Local consequences of maintained kernel coverage

    Empty scheduling exposes current memo coverage and congruence closure.
    For example, two stable nodes with one canonical signature use the same memo binding.
    Builds on: EgraphGraph and the public Base Map contracts. *)

From Stdlib Require Import List PArith Lia.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphCoreIndex EgraphCoreForest EgraphGraph.
Import List.ListNotations.

Module EggKernelInv.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** Singleton allocation preserves the exact representative function through its actual UF union. *)
Theorem allocation_representatives g n key query :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.find a (snd (Egraph.allocate a g n key)) query = Egraph.find a g query.
Proof.
  intro Hwf.
  change (fst (UnionFind.find Egraph.id_encoding query
    (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g))) =
    fst (UnionFind.find Egraph.id_encoding query (Egraph.uf g))).
  apply EggForest.self_union_representatives; [exact positive_encoding_laws|exact Hwf].
Qed.

Local Lemma allocation_canonical g n key other :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.canonical a (snd (Egraph.allocate a g n key)) other = Egraph.canonical a g other.
Proof.
  intro Hwf; destruct other; rewrite !Egraph.canonical_equation; [reflexivity|].
  f_equal; apply map_ext; intro c; apply allocation_representatives; exact Hwf.
Qed.

Local Lemma set_lookup {A} (m : Map.t Egraph.id A) c value query :
  Map.wf Egraph.id_encoding m ->
  Map.get Egraph.id_encoding query (Map.set Egraph.id_encoding c value m) =
    if Pos.eq_dec query c then Some value else Map.get Egraph.id_encoding query m.
Proof.
  intro Hwf; destruct (Pos.eq_dec query c) as [->|Hne].
  - apply Map.get_set_same; exact Hwf.
  - apply Map.get_set_other; [exact positive_encoding_laws|exact Hwf|exact Hne].
Qed.

Local Lemma allocation_parent_equation g n key :
  Egraph.parents (snd (Egraph.allocate a g n key)) =
    EggParent.register (Egraph.parents g) (Egraph.node_children n) (Egraph.next g).
Proof.
  rewrite Egraph.allocate_equation; cbn [snd Egraph.parents Egraph.private].
  rewrite Egraph.allocation_kernel_equation; reflexivity.
Qed.

Local Lemma allocation_cache_equation g n key :
  Egraph.cached (snd (Egraph.allocate a g n key)) =
    Map.set Egraph.id_encoding (Egraph.next g) n (Egraph.cached g).
Proof.
  rewrite Egraph.allocate_equation; cbn [snd Egraph.cached Egraph.private].
  rewrite Egraph.allocation_kernel_equation; reflexivity.
Qed.

Local Lemma allocation_queue_equation g n key :
  Egraph.pending (Egraph.private (snd (Egraph.allocate a g n key))) =
    Egraph.pending (Egraph.private g).
Proof.
  rewrite Egraph.allocate_equation; cbn [snd Egraph.private].
  rewrite Egraph.allocation_kernel_equation; reflexivity.
Qed.

Local Lemma allocation_edges_equation g n key :
  Egraph.edges (snd (Egraph.allocate a g n key)) = Egraph.edges g.
Proof.
  rewrite Egraph.allocate_equation; cbn [snd Egraph.edges Egraph.private].
  rewrite Egraph.allocation_kernel_equation; reflexivity.
Qed.

Local Lemma allocation_pending_mono {work} g n key i :
  Egraph.kernel_inv_on a g work -> Egraph.pending_node g i ->
  Egraph.pending_node (snd (Egraph.allocate a g n key)) i.
Proof.
  intros Hinv [loser [Hdirty Hin]]; exists loser; split.
  - unfold Egraph.dirty; rewrite allocation_queue_equation; exact Hdirty.
  - rewrite allocation_parent_equation.
    apply (proj2 (EggParent.register_in _ _ _ _ _
      (Egraph.parent_map_wf a g Hinv))); right; exact Hin.
Qed.

Local Lemma pending_work_node (g : Egraph.t K Sort V) work i :
  Egraph.pending_node g i -> Egraph.pending_work g work i.
Proof.
  intro Hin; destruct work; cbn [Egraph.pending_work]; auto.
Qed.

Local Lemma pending_work_mono (g h : Egraph.t K Sort V) work :
  (forall i, Egraph.pending_node g i -> Egraph.pending_node h i) ->
  forall i, Egraph.pending_work g work i -> Egraph.pending_work h work i.
Proof.
  intros Hpending i Hin; destruct work; cbn [Egraph.pending_work] in *; intuition.
Qed.

Local Lemma canonical_children_fixed g n :
  Egraph.canonical a g n = n ->
  forall child, In child (Egraph.node_children n) -> Egraph.find a g child = child.
Proof.
  destruct n as [s v|s op cs]; rewrite Egraph.canonical_equation; intro Hcanonical.
  - intros child Hin; contradiction.
  - injection Hcanonical as Hchildren; cbn [Egraph.node_children].
    induction cs as [|c cs IH]; intros child Hin; [contradiction|].
    cbn [map] in Hchildren; injection Hchildren as Hhead Htail.
    destruct Hin as [<-|Hin]; [exact Hhead|exact (IH Htail child Hin)].
Qed.

(** Empty construction establishes all concrete parent, snapshot, queue, memo and edge duties. *)
Theorem empty_kernel_inv : Egraph.kernel_inv a (@Egraph.empty K Sort V).
Proof.
  constructor.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply EggPending.empty_wf.
  - intros i n Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some n) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros i old Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some old) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros i n child Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some n) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros i old child Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some old) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros root i Hin.
    change (In i (EggParent.get Map.empty root)) in Hin.
    rewrite EggParent.get_equation, Map.get_empty in Hin; contradiction.
  - intros loser Hin.
    change (In loser []) in Hin; contradiction.
  - intros loser Hin.
    change (In loser []) in Hin; contradiction.
  - intros i n old Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some n) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros key i Hget.
    change (Map.get Egraph.id_encoding key Map.empty = Some i) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros i n Hget.
    change (Map.get Egraph.id_encoding i Map.empty = Some n) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - apply Egraph.forest_empty.
  - intros e Hin; change (In e []) in Hin; contradiction.
Qed.

(** A canonical memo miss maintains local coverage while allocating a fresh singleton. *)
Theorem allocate_kernel_inv {work} g n :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Map.wf Egraph.id_encoding (Egraph.nodes g) ->
  Map.wf Egraph.id_encoding (Egraph.memo g) ->
  Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g) = None ->
  Egraph.canonical a g n = n ->
  Map.get Egraph.id_encoding (Egraph.node_code a n) (Egraph.memo g) = None ->
  Egraph.kernel_inv_on a (snd (Egraph.allocate a g n (Egraph.node_code a n))) work.
Proof.
  intros Hinv Hforest Hnodes Hmemo Hfresh Hcanonical Hmiss.
  set (key := Egraph.node_code a n).
  set (h := snd (Egraph.allocate a g n key)).
  assert (Hns : Egraph.nodes h =
    Map.set Egraph.id_encoding (Egraph.next g) n (Egraph.nodes g)) by reflexivity.
  assert (Htable : Egraph.memo h =
    Map.set Egraph.id_encoding key (Egraph.next g) (Egraph.memo g)) by reflexivity.
  assert (Hcache : Egraph.cached h =
    Map.set Egraph.id_encoding (Egraph.next g) n (Egraph.cached g)).
  { apply allocation_cache_equation. }
  assert (Hindex : Egraph.parents h =
    EggParent.register (Egraph.parents g) (Egraph.node_children n) (Egraph.next g)).
  { apply allocation_parent_equation. }
  assert (Hqueue : Egraph.pending (Egraph.private h) = Egraph.pending (Egraph.private g)).
  { apply allocation_queue_equation. }
  assert (Hdirty : Egraph.dirty h = Egraph.dirty g).
  { unfold Egraph.dirty; rewrite Hqueue; reflexivity. }
  assert (Hedges : Egraph.edges h = Egraph.edges g).
  { apply allocation_edges_equation. }
  assert (Hfind : forall c, Egraph.find a h c = Egraph.find a g c).
  { intro c; apply allocation_representatives; exact Hforest. }
  assert (Hcanon : forall m, Egraph.canonical a h m = Egraph.canonical a g m).
  { intro m; apply allocation_canonical; exact Hforest. }
  assert (Hcachefresh : Map.get Egraph.id_encoding (Egraph.next g) (Egraph.cached g) = None).
  { destruct (Map.get Egraph.id_encoding (Egraph.next g) (Egraph.cached g))
      as [old|] eqn:Hget; [|reflexivity].
    destruct (Egraph.snapshot_correct a g Hinv _ old Hget) as [m [Hnode Hsame]].
    congruence. }
  assert (Hretain : forall i m, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some m ->
    Map.get Egraph.id_encoding i (Egraph.nodes h) = Some m).
  { intros i m Hnode; rewrite Hns, set_lookup by exact Hnodes.
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne]; congruence. }
  assert (Hretaincache : forall i old,
    Map.get Egraph.id_encoding i (Egraph.cached g) = Some old ->
    Map.get Egraph.id_encoding i (Egraph.cached h) = Some old).
  { intros i old Hget; rewrite Hcache, set_lookup by exact (Egraph.snapshot_map_wf a g Hinv).
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne]; congruence. }
  assert (Hnewnode : Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes h) = Some n).
  { rewrite Hns; apply Map.get_set_same; exact Hnodes. }
  assert (Hnewcache : Map.get Egraph.id_encoding (Egraph.next g) (Egraph.cached h) = Some n).
  { rewrite Hcache; apply Map.get_set_same; exact (Egraph.snapshot_map_wf a g Hinv). }
  assert (Hstable : forall i, ~ Egraph.pending_work h work i -> ~ Egraph.pending_work g work i).
  { intros i Hnot Hin; apply Hnot.
    apply (pending_work_mono g h work); [|exact Hin].
    intros j Hj; exact (allocation_pending_mono g n key j Hinv Hj). }
  constructor.
  - rewrite Hindex; apply EggParent.register_wf; exact (Egraph.parent_map_wf a g Hinv).
  - rewrite Hcache; apply Map.wf_set; exact (Egraph.snapshot_map_wf a g Hinv).
  - rewrite Hqueue; exact (Egraph.pending_wf a g Hinv).
  - intros i m Hnode; rewrite Hns, set_lookup in Hnode by exact Hnodes.
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + exists n; exact Hnewcache.
    + destruct (Egraph.snapshot_complete a g Hinv i m Hnode) as [old Hget].
      exists old; apply Hretaincache; exact Hget.
  - intros i old Hget; rewrite Hcache, set_lookup in Hget
      by exact (Egraph.snapshot_map_wf a g Hinv).
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + injection Hget as <-; exists n; split; [exact Hnewnode|reflexivity].
    + destruct (Egraph.snapshot_correct a g Hinv i old Hget) as [m [Hnode Heq]].
      exists m; split; [apply Hretain; exact Hnode|rewrite !Hcanon; exact Heq].
  - intros i m child Hnode Hin; rewrite Hns, set_lookup in Hnode by exact Hnodes.
    rewrite Hfind, Hindex.
    apply (proj2 (EggParent.register_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + injection Hnode as <-; left; split; [reflexivity|].
      rewrite (canonical_children_fixed g n Hcanonical child Hin); exact Hin.
    + right; exact (Egraph.current_parents a g Hinv i m child Hnode Hin).
  - intros i old child Hget Hin; rewrite Hcache, set_lookup in Hget
      by exact (Egraph.snapshot_map_wf a g Hinv).
    rewrite Hindex.
    apply (proj2 (EggParent.register_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + injection Hget as <-; left; split; [reflexivity|exact Hin].
    + right; exact (Egraph.snapshot_parents a g Hinv i old child Hget Hin).
  - intros root i Hin; rewrite Hindex in Hin.
    apply (proj1 (EggParent.register_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))) in Hin.
    destruct Hin as [[-> Hchild]|Hin].
    + exists n; exact Hnewnode.
    + destruct (Egraph.indexed_nodes a g Hinv root i Hin) as [m Hnode].
      exists m; apply Hretain; exact Hnode.
  - intros loser Hin Hempty.
    rewrite Hdirty in Hin.
    pose proof (Egraph.pending_nonempty a g Hinv loser Hin) as Hnonempty.
    destruct (EggParent.get (Egraph.parents g) loser) as [|parent rest] eqn:Hparents;
      [contradiction|].
    assert (Hinnew : In parent (EggParent.get (Egraph.parents h) loser)).
    { rewrite Hindex.
      apply (proj2 (EggParent.register_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
      right; rewrite Hparents; left; reflexivity. }
    rewrite Hempty in Hinnew; contradiction.
  - intros loser Hin; rewrite Hdirty in Hin.
    pose proof (Egraph.pending_allocated a g Hinv loser Hin) as Hbound.
    change (loser < Pos.succ (Egraph.next g))%positive; lia.
  - intros i m old Hnode Hget Hnot.
    rewrite Hns, set_lookup in Hnode by exact Hnodes.
    rewrite Hcache, set_lookup in Hget by exact (Egraph.snapshot_map_wf a g Hinv).
    rewrite Hcanon.
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + injection Hnode as <-; injection Hget as <-; symmetry; exact Hcanonical.
    + exact (Egraph.stable_snapshot a g Hinv i m old Hnode Hget (Hstable i Hnot)).
  - intros code i Hget; rewrite Htable, set_lookup in Hget by exact Hmemo.
    destruct (Pos.eq_dec code key) as [->|Hne].
    + injection Hget as <-; exists n; split; [exact Hnewcache|reflexivity].
    + destruct (Egraph.memo_owner a g Hinv code i Hget) as [old [Hgetold Hcode]].
      exists old; split; [apply Hretaincache; exact Hgetold|exact Hcode].
  - intros i m Hnode Hnot; rewrite Hns, set_lookup in Hnode by exact Hnodes.
    rewrite Hcanon.
    destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
    + injection Hnode as <-; rewrite Hcanonical.
      exists (Egraph.next g); split; [rewrite Htable; apply Map.get_set_same; exact Hmemo|reflexivity].
    + destruct (Egraph.stable_memo a g Hinv i m Hnode (Hstable i Hnot))
        as [other [Hget Hsame]].
      exists other; split; [|rewrite !Hfind; exact Hsame].
      rewrite Htable, set_lookup by exact Hmemo.
      destruct (Pos.eq_dec (Egraph.node_code a (Egraph.canonical a g m)) key) as [Heq|Hneq].
      * unfold key in Heq; rewrite Heq, Hmiss in Hget; discriminate.
      * exact Hget.
  - rewrite Hedges; exact (Egraph.reasons_forest a g Hinv).
  - intros e Hin; rewrite Hedges in Hin; rewrite !Hfind.
    exact (Egraph.reasons_correct a g Hinv e Hin).
Qed.

(** Canonicalization is idempotent under the public Base forest invariant alone. *)
Theorem canonical_idem g n :
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Egraph.canonical a g (Egraph.canonical a g n) = Egraph.canonical a g n.
Proof.
  intro Hforest; destruct n; rewrite !Egraph.canonical_equation; [reflexivity|].
  f_equal; rewrite map_map; apply map_ext; intro c.
  change (fst (UnionFind.find Egraph.id_encoding
    (fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g))) (Egraph.uf g)) =
    fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g))).
  apply UnionFind.find_rep_canonical; [exact positive_encoding_laws|exact Hforest].
Qed.

(** Successful node insertion maintains local kernel coverage under the actual map and forest duties. *)
Theorem add_node_kernel_inv {work} g n c h :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  Map.wf Egraph.id_encoding (Egraph.nodes g) ->
  Map.wf Egraph.id_encoding (Egraph.memo g) ->
  Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g) = None ->
  Egraph.add_node a g n = Some (c, h) ->
  Egraph.kernel_inv_on a h work.
Proof.
  intros Hinv Hforest Hnodes Hmemo Hfresh; rewrite Egraph.add_node_equation.
  destruct (Egraph.node_valid a g n); [|discriminate].
  destruct (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g)) as [other|] eqn:Hhit.
  - intro Hresult; injection Hresult as <- <-; exact Hinv.
  - pose proof (allocate_kernel_inv g (Egraph.canonical a g n) Hinv Hforest Hnodes Hmemo
      Hfresh (canonical_idem g n Hforest) Hhit) as Hnew.
    destruct (Egraph.allocate a g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n))) as [fresh allocated].
    intro Hresult; injection Hresult as <- <-; exact Hnew.
Qed.

Local Lemma canonical_mono g h n m :
  (forall c d, Egraph.find a g c = Egraph.find a g d ->
    Egraph.find a h c = Egraph.find a h d) ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.canonical a h n = Egraph.canonical a h m.
Proof.
  intros Hclasses Hcanonical.
  destruct n as [s v|s op cs], m as [s' v'|s' op' ds];
    rewrite !Egraph.canonical_equation in *; try discriminate.
  - exact Hcanonical.
  - injection Hcanonical as Hsort Hop Hchildren; subst s' op'; f_equal.
    revert ds Hchildren; induction cs as [|c cs IH]; intros [|d ds] Heq;
      cbn [map] in *; try discriminate; [reflexivity|].
    injection Heq as Hhead Htail; f_equal; [apply Hclasses; exact Hhead|apply IH; exact Htail].
Qed.

(** Exact root collapse maintains parent, memo and explanation coverage without changing stored nodes. *)
Theorem linked_kernel_inv {work} g forest loser winner reason :
  Egraph.kernel_inv_on a g work ->
  loser <> winner ->
  Egraph.find a g loser = loser ->
  Egraph.find a g winner = winner ->
  (loser < Egraph.next g)%positive ->
  (forall query, fst (UnionFind.find Egraph.id_encoding query forest) =
    if Pos.eqb (Egraph.find a g query) loser then winner else Egraph.find a g query) ->
  Egraph.kernel_inv_on a
    (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
      (Egraph.linked_kernel g loser winner reason)) work.
Proof.
  intros Hinv Hdistinct Hloser Hwinner Hallocated Hcollapse.
  set (h := Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
    (Egraph.linked_kernel g loser winner reason)).
  assert (Hindex : Egraph.parents h = EggParent.merge (Egraph.parents g) loser winner).
  { unfold h, Egraph.parents; cbn [Egraph.private].
    rewrite Egraph.linked_kernel_equation; reflexivity. }
  assert (Hcache : Egraph.cached h = Egraph.cached g).
  { unfold h, Egraph.cached; cbn [Egraph.private].
    rewrite Egraph.linked_kernel_equation; reflexivity. }
  assert (Hqueue : Egraph.pending (Egraph.private h) =
    match EggParent.get (Egraph.parents g) loser with
    | [] => Egraph.pending (Egraph.private g)
    | _ :: _ => EggPending.push loser (Egraph.pending (Egraph.private g))
    end).
  { unfold h; cbn [Egraph.private]; rewrite Egraph.linked_kernel_equation; reflexivity. }
  assert (Hedges : Egraph.edges h = Egraph.Edge loser winner reason :: Egraph.edges g).
  { unfold h, Egraph.edges; cbn [Egraph.private].
    rewrite Egraph.linked_kernel_equation; reflexivity. }
  assert (Hqueuewf : EggPending.wf (Egraph.pending (Egraph.private h))).
  { rewrite Hqueue; destruct (EggParent.get (Egraph.parents g) loser).
    - exact (Egraph.pending_wf a g Hinv).
    - apply EggPending.push_wf; exact (Egraph.pending_wf a g Hinv). }
  assert (Hqmono : forall root, In root (Egraph.dirty g) -> In root (Egraph.dirty h)).
  { intros root Hin; unfold Egraph.dirty; rewrite Hqueue.
    destruct (EggParent.get (Egraph.parents g) loser); [exact Hin|].
    apply (proj2 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv))); right; exact Hin. }
  assert (Hqmember : forall root, In root (Egraph.dirty h) ->
    root = loser \/ In root (Egraph.dirty g)).
  { intros root Hin; unfold Egraph.dirty in Hin; rewrite Hqueue in Hin.
    destruct (EggParent.get (Egraph.parents g) loser); [right; exact Hin|].
    exact (proj1 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv)) Hin). }
  assert (Hqwork : forall root, In root (Egraph.dirty h) ->
    EggParent.get (Egraph.parents g) root <> []).
  { intros root Hin; unfold Egraph.dirty in Hin; rewrite Hqueue in Hin.
    destruct (EggParent.get (Egraph.parents g) loser) as [|parent rest] eqn:Hparents.
    - exact (Egraph.pending_nonempty a g Hinv root Hin).
    - apply (proj1 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv))) in Hin.
      destruct Hin as [->|Hin].
      + rewrite Hparents; discriminate.
      + exact (Egraph.pending_nonempty a g Hinv root Hin). }
  assert (Hnewdirty : forall i, In i (EggParent.get (Egraph.parents g) loser) ->
    Egraph.pending_node h i).
  { intros i Hin; exists loser; split.
    - unfold Egraph.dirty; rewrite Hqueue.
      destruct (EggParent.get (Egraph.parents g) loser) as [|parent rest] eqn:Hparents;
        [contradiction|].
      apply (proj2 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv)));
        left; reflexivity.
    - rewrite Hindex.
      apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv)));
        left; exact Hin. }
  assert (Hpending : forall i, Egraph.pending_node g i -> Egraph.pending_node h i).
  { intros i [root [Hdirty Hparent]]; exists root; split; [apply Hqmono; exact Hdirty|].
    rewrite Hindex.
    apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv)));
      left; exact Hparent. }
  assert (Hfind : forall query, Egraph.find a h query =
    if Pos.eqb (Egraph.find a g query) loser then winner else Egraph.find a g query).
  { exact Hcollapse. }
  assert (Hclasses : forall c d, Egraph.find a g c = Egraph.find a g d ->
    Egraph.find a h c = Egraph.find a h d).
  { intros c d Heq; rewrite !Hfind, Heq; reflexivity. }
  assert (Hstable : forall i n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
    ~ Egraph.pending_work h work i -> Egraph.canonical a h n = Egraph.canonical a g n).
  { intros i n Hnode Hnot.
    destruct n as [s v|s op cs]; rewrite !Egraph.canonical_equation; [reflexivity|].
    f_equal; apply map_ext_in; intros child Hin.
    rewrite Hfind; destruct (Pos.eqb (Egraph.find a g child) loser) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; exfalso; apply Hnot, pending_work_node, Hnewdirty.
    rewrite <- Heq; exact (Egraph.current_parents a g Hinv i _ child Hnode Hin). }
  constructor.
  - rewrite Hindex; apply EggParent.merge_wf; exact (Egraph.parent_map_wf a g Hinv).
  - rewrite Hcache; exact (Egraph.snapshot_map_wf a g Hinv).
  - exact Hqueuewf.
  - intros i n Hnode; change (Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n) in Hnode.
    rewrite Hcache; exact (Egraph.snapshot_complete a g Hinv i n Hnode).
  - intros i old Hget; rewrite Hcache in Hget.
    destruct (Egraph.snapshot_correct a g Hinv i old Hget) as [n [Hnode Hsame]].
    exists n; split; [exact Hnode|apply (canonical_mono g h old n Hclasses); exact Hsame].
  - intros i n child Hnode Hin; rewrite Hindex, Hfind.
    apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
    destruct (Pos.eqb (Egraph.find a g child) loser) eqn:Heq.
    + apply Pos.eqb_eq in Heq; right; split; [reflexivity|].
      rewrite <- Heq; exact (Egraph.current_parents a g Hinv i n child Hnode Hin).
    + left; exact (Egraph.current_parents a g Hinv i n child Hnode Hin).
  - intros i old child Hget Hin; rewrite Hcache in Hget; rewrite Hindex.
    apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
    left; exact (Egraph.snapshot_parents a g Hinv i old child Hget Hin).
  - intros root i Hin; rewrite Hindex in Hin.
    apply (proj1 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))) in Hin.
    destruct Hin as [Hin|[Heq Hin]].
    + exact (Egraph.indexed_nodes a g Hinv root i Hin).
    + exact (Egraph.indexed_nodes a g Hinv loser i Hin).
  - intros root Hin Hempty.
    pose proof (Hqwork root Hin) as Hnonempty.
    destruct (EggParent.get (Egraph.parents g) root) as [|parent rest] eqn:Hparents;
      [contradiction|].
    assert (Hinnew : In parent (EggParent.get (Egraph.parents h) root)).
    { rewrite Hindex.
      apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv))).
      left; rewrite Hparents; left; reflexivity. }
    rewrite Hempty in Hinnew; contradiction.
  - intros root Hin; apply Hqmember in Hin as [->|Hin].
    + exact Hallocated.
    + exact (Egraph.pending_allocated a g Hinv root Hin).
  - intros i n old Hnode Hget Hnot; rewrite Hcache in Hget.
    rewrite (Hstable i n Hnode Hnot).
    apply (Egraph.stable_snapshot a g Hinv i n old Hnode Hget).
    intro Hin; apply Hnot.
    exact (pending_work_mono g h work Hpending i Hin).
  - intros code i Hget; rewrite Hcache.
    exact (Egraph.memo_owner a g Hinv code i Hget).
  - intros i n Hnode Hnot; rewrite (Hstable i n Hnode Hnot).
    destruct (Egraph.stable_memo a g Hinv i n Hnode
      (fun Hin => Hnot (pending_work_mono g h work Hpending i Hin))) as [other [Hget Hsame]].
    exists other; split; [exact Hget|apply Hclasses; exact Hsame].
  - rewrite Hedges; apply Egraph.forest_edge; [exact (Egraph.reasons_forest a g Hinv)|].
    intro Hpath.
    assert (Hsame : Egraph.find a g loser = Egraph.find a g winner).
    { assert (Hpaths : forall c d, Egraph.edge_path (Egraph.edges g) c d ->
        Egraph.find a g c = Egraph.find a g d).
      { intros c d Hwalk; induction Hwalk as [c|c d e Hin Hends target Hrest IH].
        - reflexivity.
        - pose proof (Egraph.reasons_correct a g Hinv e Hin) as Hedge.
          destruct Hends as [[Hleft Hright]|[Hright Hleft]];
            rewrite Hleft, Hright in Hedge; congruence. }
      exact (Hpaths loser winner Hpath). }
    rewrite Hloser, Hwinner in Hsame; contradiction.
  - intros e Hin; rewrite Hedges in Hin; destruct Hin as [<-|Hin].
    + cbn [Egraph.left Egraph.right]; rewrite !Hfind, Hloser, Hwinner, Pos.eqb_refl.
      destruct (Pos.eqb winner loser) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq; congruence.
    + apply Hclasses; exact (Egraph.reasons_correct a g Hinv e Hin).
Qed.

(** Compression-only forest changes retain kernel obligations when every representative is unchanged. *)
Theorem kernel_inv_same_roots {work} g forest :
  Egraph.kernel_inv_on a g work ->
  (forall query, fst (UnionFind.find Egraph.id_encoding query forest) = Egraph.find a g query) ->
  Egraph.kernel_inv_on a
    (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
      (Egraph.private g)) work.
Proof.
  intros Hinv Hroots.
  set (h := Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
    (Egraph.private g)).
  assert (Hfind : forall c, Egraph.find a h c = Egraph.find a g c) by exact Hroots.
  assert (Hcanon : forall n, Egraph.canonical a h n = Egraph.canonical a g n).
  { intros [s v|s op cs]; rewrite !Egraph.canonical_equation; [reflexivity|].
    f_equal; apply map_ext; exact Hfind. }
  constructor.
  - exact (Egraph.parent_map_wf a g Hinv).
  - exact (Egraph.snapshot_map_wf a g Hinv).
  - exact (Egraph.pending_wf a g Hinv).
  - exact (Egraph.snapshot_complete a g Hinv).
  - intros i old Hget.
    destruct (Egraph.snapshot_correct a g Hinv i old Hget) as [n [Hnode Hsame]].
    exists n; split; [exact Hnode|rewrite !Hcanon; exact Hsame].
  - intros i n child Hnode Hin; rewrite Hfind.
    exact (Egraph.current_parents a g Hinv i n child Hnode Hin).
  - exact (Egraph.snapshot_parents a g Hinv).
  - exact (Egraph.indexed_nodes a g Hinv).
  - exact (Egraph.pending_nonempty a g Hinv).
  - exact (Egraph.pending_allocated a g Hinv).
  - intros i n old Hnode Hget Hnot; rewrite Hcanon.
    exact (Egraph.stable_snapshot a g Hinv i n old Hnode Hget Hnot).
  - exact (Egraph.memo_owner a g Hinv).
  - intros i n Hnode Hnot; rewrite Hcanon.
    destruct (Egraph.stable_memo a g Hinv i n Hnode Hnot) as [other [Hget Hsame]].
    exists other; split; [exact Hget|rewrite !Hfind; exact Hsame].
  - exact (Egraph.reasons_forest a g Hinv).
  - intros e Hin; rewrite !Hfind; exact (Egraph.reasons_correct a g Hinv e Hin).
Qed.

Local Lemma id_eqb c d : eqb Egraph.id_encoding c d = Pos.eqb c d.
Proof.
  destruct (eqb Egraph.id_encoding c d) eqn:Hencoded, (Pos.eqb c d) eqn:Hpositive;
    try reflexivity.
  - apply (eqb_true_iff _ positive_encoding_laws) in Hencoded.
    subst d; rewrite Pos.eqb_refl in Hpositive; discriminate.
  - apply Pos.eqb_eq in Hpositive; subst d; rewrite eqb_refl in Hencoded; discriminate.
Qed.

(** A root link changes a node's canonical bytes only when its parent snapshot is scheduled. *)
Theorem linked_signature_stable {work} g forest loser winner reason :
  Egraph.kernel_inv_on a g work ->
  (forall query, fst (UnionFind.find Egraph.id_encoding query forest) =
    if Pos.eqb (Egraph.find a g query) loser then winner else Egraph.find a g query) ->
  forall i n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  ~ Egraph.pending_node
    (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
      (Egraph.linked_kernel g loser winner reason)) i ->
  Egraph.canonical a
    (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
      (Egraph.linked_kernel g loser winner reason)) n = Egraph.canonical a g n.
Proof.
  intros Hinv Hcollapse i n Hnode Hnot.
  set (h := Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
    (Egraph.linked_kernel g loser winner reason)) in *.
  assert (Hfind : forall query, Egraph.find a h query =
    if Pos.eqb (Egraph.find a g query) loser then winner else Egraph.find a g query)
    by exact Hcollapse.
  destruct n as [s v|s op cs]; rewrite !Egraph.canonical_equation; [reflexivity|].
  f_equal; apply map_ext_in; intros child Hin; rewrite Hfind.
  destruct (Pos.eqb (Egraph.find a g child) loser) eqn:Heq; [|reflexivity].
  apply Pos.eqb_eq in Heq.
  assert (Hparent : In i (EggParent.get (Egraph.parents g) loser)).
  { rewrite <- Heq; exact (Egraph.current_parents a g Hinv i _ child Hnode Hin). }
  exfalso; apply Hnot; exists loser; split.
  - unfold Egraph.dirty, h; cbn [Egraph.private].
    rewrite Egraph.linked_kernel_equation; cbn [Egraph.pending].
    destruct (EggParent.get (Egraph.parents g) loser); [contradiction|].
    apply (proj2 (EggPending.push_in _ _ _ (Egraph.pending_wf a g Hinv))); left; reflexivity.
  - unfold Egraph.parents, h; cbn [Egraph.private].
    rewrite Egraph.linked_kernel_equation; cbn [Egraph.parent_index].
    apply (proj2 (EggParent.merge_in _ _ _ _ _ (Egraph.parent_map_wf a g Hinv)));
      left; exact Hparent.
Qed.

Local Lemma selected_union_kernel_correct {work} g forest c d loser winner reason :
  Egraph.kernel_inv_on a g work -> loser <> winner ->
  Egraph.find a g loser = loser -> Egraph.find a g winner = winner ->
  (loser < Egraph.next g)%positive ->
  ((Egraph.find a g c = winner /\ Egraph.find a g d = loser) \/
    (Egraph.find a g c = loser /\ Egraph.find a g d = winner)) ->
  (forall query, fst (UnionFind.find Egraph.id_encoding query forest) =
    if Pos.eqb (Egraph.find a g query) loser then winner else Egraph.find a g query) ->
  Egraph.kernel_inv_on a
    (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
      (Egraph.union_kernel a g c d forest reason)) work /\
  (forall i n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
    ~ Egraph.pending_node
      (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
        (Egraph.union_kernel a g c d forest reason)) i ->
    Egraph.canonical a
      (Egraph.Make K Sort V forest (Egraph.nodes g) (Egraph.memo g) (Egraph.next g)
        (Egraph.union_kernel a g c d forest reason)) n = Egraph.canonical a g n).
Proof.
  intros Hinv Hdistinct Hloser Hwinner Hallocated Hparts Hcollapse.
  assert (Hforward : Pos.eqb loser winner = false) by (apply Pos.eqb_neq; exact Hdistinct).
  assert (Hreverse : Pos.eqb winner loser = false) by (apply Pos.eqb_neq; congruence).
  rewrite Egraph.union_kernel_equation; cbv zeta.
  destruct Hparts as [[Hc Hd]|[Hc Hd]]; rewrite Hc, Hd, ?Hforward, ?Hreverse.
  - rewrite (Hcollapse c), Hc, ?Hreverse, ?Pos.eqb_refl.
    split; [apply linked_kernel_inv|apply (linked_signature_stable (work := work))]; assumption.
  - rewrite (Hcollapse c), Hc, ?Pos.eqb_refl, ?Hreverse.
    split; [apply linked_kernel_inv|apply (linked_signature_stable (work := work))]; assumption.
Qed.

Local Lemma merge_kernel_correct {work} g c d reason :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  Egraph.kernel_inv_on a (Egraph.merge a g c d reason) work /\
  (forall i n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
    ~ Egraph.pending_node (Egraph.merge a g c d reason) i ->
    Egraph.canonical a (Egraph.merge a g c d reason) n = Egraph.canonical a g n).
Proof.
  intros Hinv Hforest Hc_bound Hd_bound.
  pose proof (UnionFind.find_rep_stable Egraph.id_encoding positive_encoding_laws
    (Egraph.uf g) d c Hforest) as Hstable.
  destruct (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) as [rc first] eqn:Hfirst.
  destruct (UnionFind.find Egraph.id_encoding d first) as [rd second] eqn:Hsecond.
  assert (Hc : Egraph.find a g c = rc).
  { change (fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g)) = rc).
    rewrite Hfirst; reflexivity. }
  assert (Hd : Egraph.find a g d = rd).
  { cbn [fst snd] in Hstable; rewrite ?Hsecond in Hstable.
    symmetry; exact Hstable. }
  assert (Hidem : forall query, Egraph.find a g (Egraph.find a g query) =
    Egraph.find a g query).
  { intro query; apply UnionFind.find_rep_canonical; [exact positive_encoding_laws|exact Hforest]. }
  assert (Hrc : Egraph.find a g rc = rc) by (rewrite <- Hc; apply Hidem).
  assert (Hrd : Egraph.find a g rd = rd) by (rewrite <- Hd; apply Hidem).
  rewrite Hc in Hc_bound; rewrite Hd in Hd_bound.
  assert (Hactual : forall query,
    fst (UnionFind.find Egraph.id_encoding query
      (UnionFind.union Egraph.id_encoding c d (Egraph.uf g))) =
    if Pos.eqb rc rd then Egraph.find a g query
    else match Nat.compare (UnionFind.rank_of Egraph.id_encoding second rc)
      (UnionFind.rank_of Egraph.id_encoding second rd) with
    | Eq => if Pos.eqb (Egraph.find a g query) rd then rc else Egraph.find a g query
    | Lt => if Pos.eqb (Egraph.find a g query) rc then rd else Egraph.find a g query
    | Gt => if Pos.eqb (Egraph.find a g query) rd then rc else Egraph.find a g query
    end).
  { intro query.
    rewrite (UnionFind.union_rep_equation Egraph.id_encoding positive_encoding_laws
      (Egraph.uf g) c d query Hforest), Hfirst, Hsecond, !id_eqb.
    reflexivity. }
  rewrite Egraph.merge_equation.
  destruct (Pos.eqb rc rd) eqn:Hsame.
  - rewrite Egraph.union_kernel_equation; cbv zeta; rewrite Hc, Hd, Hsame.
    split; [apply kernel_inv_same_roots; [exact Hinv|exact Hactual]|].
    intros i [s v|s op cs] Hnode Hnot; rewrite !Egraph.canonical_equation; [reflexivity|].
    f_equal; apply map_ext; exact Hactual.
  - apply Pos.eqb_neq in Hsame.
    destruct (Nat.compare (UnionFind.rank_of Egraph.id_encoding second rc)
      (UnionFind.rank_of Egraph.id_encoding second rd)) eqn:Hcompare.
    + apply (selected_union_kernel_correct g _ c d rd rc reason Hinv);
        try assumption; try congruence.
      left; auto.
    + apply (selected_union_kernel_correct g _ c d rc rd reason Hinv);
        try assumption; try congruence.
      right; auto.
    + apply (selected_union_kernel_correct g _ c d rd rc reason Hinv);
        try assumption; try congruence.
      left; auto.
Qed.

(** Actual rank-selected UF union maintains kernel metadata using the public representative equation. *)
Theorem merge_kernel_inv {work} g c d reason :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  Egraph.kernel_inv_on a (Egraph.merge a g c d reason) work.
Proof.
  intros Hinv Hforest Hc Hd; exact (proj1 (merge_kernel_correct g c d reason Hinv Hforest Hc Hd)).
Qed.

(** A node absent from all newly pending parent buckets keeps its canonical bytes through union. *)
Theorem merge_signature_stable {work} g c d reason :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  forall i n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  ~ Egraph.pending_node (Egraph.merge a g c d reason) i ->
  Egraph.canonical a (Egraph.merge a g c d reason) n = Egraph.canonical a g n.
Proof.
  intros Hinv Hforest Hc Hd; exact (proj2 (merge_kernel_correct g c d reason Hinv Hforest Hc Hd)).
Qed.

(** Successful justified union preserves maintained coverage through its actual rank-selected merge. *)
Theorem union_j_kernel_inv {work} g c d reason h :
  Egraph.kernel_inv_on a g work ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  Egraph.union_j a g c d reason = Some h ->
  Egraph.kernel_inv_on a h work.
Proof.
  intros Hinv Hforest Hc Hd; rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g c) as [sc|], (Egraph.sort_of a g d) as [sd|];
    [|discriminate..].
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)); [|discriminate..].
  intro Hresult; injection Hresult as <-.
  exact (merge_kernel_inv g c d reason Hinv Hforest Hc Hd).
Qed.

(** Every successful justified union preserves the explanation forest from maintained input duties. *)
Theorem edges_forest g c d reason h :
  Egraph.kernel_inv a g ->
  UnionFind.wf Egraph.id_encoding (Egraph.uf g) ->
  (Egraph.find a g c < Egraph.next g)%positive ->
  (Egraph.find a g d < Egraph.next g)%positive ->
  Egraph.union_j a g c d reason = Some h ->
  Egraph.explanation_forest (Egraph.edges h).
Proof.
  intros Hinv Hforest Hc Hd Hunion.
  exact (Egraph.reasons_forest a h
    (union_j_kernel_inv g c d reason h Hinv Hforest Hc Hd Hunion)).
Qed.

(** No node is covered by a dirty-class bucket when the scheduling queue is empty. *)
Theorem pending_empty (g : Egraph.t K Sort V) i :
  Egraph.dirty g = [] -> ~ Egraph.pending_node g i.
Proof.
  intros Hempty [loser [Hin Hparent]]; rewrite Hempty in Hin; contradiction.
Qed.

(** Quiescent snapshots are the canonical signatures of their stored nodes. *)
Theorem quiescent_snapshot g i n old :
  Egraph.kernel_inv a g -> Egraph.dirty g = [] ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  Map.get Egraph.id_encoding i (Egraph.cached g) = Some old ->
  old = Egraph.canonical a g n.
Proof.
  intros Hinv Hempty Hnode Hsnapshot.
  exact (Egraph.stable_snapshot a g Hinv i n old Hnode Hsnapshot
    (pending_empty g i Hempty)).
Qed.

(** Every quiescent memo key is the current canonical code of its owning stored node. *)
Theorem quiescent_memo_current g key i :
  Egraph.kernel_inv a g -> Egraph.dirty g = [] ->
  Map.get Egraph.id_encoding key (Egraph.memo g) = Some i ->
  exists n, Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n /\
    Egraph.node_code a (Egraph.canonical a g n) = key.
Proof.
  intros Hinv Hempty Hmemo.
  destruct (Egraph.memo_owner a g Hinv key i Hmemo) as [old [Hsnapshot Hcode]].
  destruct (Egraph.snapshot_correct a g Hinv i old Hsnapshot) as [n [Hnode Hcanonical]].
  exists n; split; [exact Hnode|].
  rewrite <- (quiescent_snapshot g i n old Hinv Hempty Hnode Hsnapshot); exact Hcode.
Qed.

(** Every quiescent stored node has a canonical memo binding in its own current class. *)
Theorem quiescent_memo_complete g i n :
  Egraph.kernel_inv a g -> Egraph.dirty g = [] ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  exists other,
    Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
      (Egraph.memo g) = Some other /\
    Egraph.find a g i = Egraph.find a g other.
Proof.
  intros Hinv Hempty Hnode.
  exact (Egraph.stable_memo a g Hinv i n Hnode (pending_empty g i Hempty)).
Qed.

(** Equal canonical nodes in a quiescent maintained graph belong to the same class. *)
Theorem quiescent_congruence g i j n m :
  Egraph.kernel_inv a g -> Egraph.dirty g = [] ->
  Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n ->
  Map.get Egraph.id_encoding j (Egraph.nodes g) = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.find a g i = Egraph.find a g j.
Proof.
  intros Hinv Hempty Hi Hj Hcanonical.
  destruct (quiescent_memo_complete g i n Hinv Hempty Hi) as [x [Hx Hix]].
  destruct (quiescent_memo_complete g j m Hinv Hempty Hj) as [y [Hy Hjy]].
  rewrite Hcanonical in Hx; assert (x = y) by congruence; subst y; congruence.
Qed.

(** Each explanation path stays inside one current class when its individual edges do. *)
Theorem edge_path_correct g c d :
  (forall e, In e (Egraph.edges g) ->
    Egraph.find a g (Egraph.left e) = Egraph.find a g (Egraph.right e)) ->
  Egraph.edge_path (Egraph.edges g) c d ->
  Egraph.find a g c = Egraph.find a g d.
Proof.
  intros Hedges Hpath; induction Hpath as [c|c d e Hin Hends target Hrest IH].
  - reflexivity.
  - pose proof (Hedges e Hin) as Hsame.
    destruct Hends as [[Hleft Hright]|[Hright Hleft]];
      rewrite Hleft, Hright in Hsame; congruence.
Qed.

(** Distinct current roots are disconnected in every compatible explanation forest. *)
Theorem distinct_classes_disconnected g c d :
  Egraph.kernel_inv a g -> Egraph.find a g c <> Egraph.find a g d ->
  ~ Egraph.edge_path (Egraph.edges g) c d.
Proof.
  intros Hinv Hdistinct Hpath; apply Hdistinct.
  apply edge_path_correct; [exact (Egraph.reasons_correct a g Hinv)|exact Hpath].
Qed.

End Graph.

End EggKernelInv.
