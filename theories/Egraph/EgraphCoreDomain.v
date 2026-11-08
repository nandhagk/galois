(** * Raw-state boundary for deferred rebuilding

    Reference well-formedness permits duplicate leaf productions without a memo entry.
    For example, two singleton classes can both store the same variable.
    Builds on: EgraphGraph, EgraphSpec and public Base equations. *)

From Stdlib Require Import List PArith Lia.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphSpec.
Import List.ListNotations.

Module EggCoreDomain.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V) (s : Sort) (v : V).

Definition leaf : Egraph.enode K Sort V := Egraph.NVar s v.

Definition duplicate_leaves : Egraph.t K Sort V :=
  Egraph.Make K Sort V UnionFind.make
    (Map.set Egraph.id_encoding 2%positive leaf
      (Map.set Egraph.id_encoding 1%positive leaf Map.empty))
    Map.empty 3%positive Egraph.empty_kernel.

Local Lemma id_laws : encoding_laws Egraph.id_encoding.
Proof.
  exact positive_encoding_laws.
Qed.

Local Lemma node_map_wf :
  Map.wf Egraph.id_encoding (Egraph.nodes duplicate_leaves).
Proof.
  apply Map.wf_set, Map.wf_set, Map.wf_empty.
Qed.

Local Lemma lookup c :
  EggSpec.nodes_get duplicate_leaves c =
    if Pos.eq_dec c 2%positive then Some leaf
    else if Pos.eq_dec c 1%positive then Some leaf else None.
Proof.
  change (Map.get Egraph.id_encoding c
    (Map.set Egraph.id_encoding 2%positive leaf
      (Map.set Egraph.id_encoding 1%positive leaf Map.empty)) =
    if Pos.eq_dec c 2%positive then Some leaf
    else if Pos.eq_dec c 1%positive then Some leaf else None).
  destruct (Pos.eq_dec c 2%positive) as [->|Htwo].
  - apply Map.get_set_same, Map.wf_set, Map.wf_empty.
  - rewrite Map.get_set_other by
      (try exact id_laws; try exact Htwo; apply Map.wf_set, Map.wf_empty).
    destruct (Pos.eq_dec c 1%positive) as [->|Hone].
    + apply Map.get_set_same, Map.wf_empty.
    + rewrite Map.get_set_other by
        (try exact id_laws; try exact Hone; apply Map.wf_empty).
      apply Map.get_empty.
Qed.

Local Lemma find c : Egraph.find a duplicate_leaves c = c.
Proof.
  change (fst (UnionFind.find Egraph.id_encoding c UnionFind.make) = c).
  rewrite UnionFind.find_equation, UnionFind.make_equation.
  cbn [UnionFind.max_rank].
  rewrite UnionFind.find_fuel_equation.
  cbn [UnionFind.parents].
  rewrite Map.get_empty; reflexivity.
Qed.

Local Lemma stored_leaf c n :
  EggSpec.nodes_get duplicate_leaves c = Some n -> n = leaf.
Proof.
  rewrite lookup.
  destruct (Pos.eq_dec c 2%positive), (Pos.eq_dec c 1%positive);
    intros Hnode; congruence.
Qed.

(** Structural WF accepts duplicate leaves without any prior union or memo entry. *)
Theorem duplicate_leaves_structural_wf :
  EggAlg.var_sort a v = Some s -> EggSpec.structural_wf a duplicate_leaves.
Proof.
  intro Hdeclared; constructor.
  - apply UnionFind.wf_make.
  - exact node_map_wf.
  - apply Map.wf_empty.
  - intro c; rewrite lookup.
    change ((exists n, (if Pos.eq_dec c 2%positive then Some leaf
      else if Pos.eq_dec c 1%positive then Some leaf else None) = Some n) <->
      (c < 3)%positive).
    destruct (Pos.eq_dec c 2%positive) as [->|Htwo].
    + split; [intros _; lia|intros _; eauto].
    + destruct (Pos.eq_dec c 1%positive) as [->|Hone].
      * split; [intros _; lia|intros _; eauto].
      * split; [intros [n Hnode]; discriminate|intro Hlt; exfalso; lia].
  - intros c Hin.
    change (In c (UnionFind.keys Egraph.id_encoding UnionFind.make)) in Hin.
    rewrite UnionFind.keys_make in Hin; contradiction.
  - intros c d sc sd Hsame Hc Hd.
    change (Egraph.find a duplicate_leaves c = Egraph.find a duplicate_leaves d) in Hsame.
    rewrite !find in Hsame; subst d; congruence.
  - intros c n Hnode; apply stored_leaf in Hnode; subst n.
    exact Hdeclared.
  - intros c n Hnode.
    apply stored_leaf in Hnode as Hleaf; subst n.
    exists (EggTerm.Var s v).
    apply (EggSpec.rep_var a duplicate_leaves c c s v); [reflexivity|exact Hnode].
  - intros key c Hget.
    change (Map.get Egraph.id_encoding key Map.empty = Some c) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Raw duplicate leaves lack the snapshots required by maintained coverage. *)
Theorem duplicate_leaves_not_kernel_inv : ~ Egraph.kernel_inv a duplicate_leaves.
Proof.
  intro Hinv.
  assert (Hnode : Map.get Egraph.id_encoding 1%positive (Egraph.nodes duplicate_leaves) =
    Some leaf).
  { change (EggSpec.nodes_get duplicate_leaves 1%positive = Some leaf).
    rewrite lookup; destruct (Pos.eq_dec 1%positive 2%positive);
      destruct (Pos.eq_dec 1%positive 1%positive); congruence. }
  destruct (Egraph.snapshot_complete a duplicate_leaves Hinv 1%positive leaf Hnode)
    as [old Hsnapshot].
  change (Map.get Egraph.id_encoding 1%positive Map.empty = Some old) in Hsnapshot.
  rewrite Map.get_empty in Hsnapshot; discriminate.
Qed.

(** Both stored variables have equal canonical signatures and remain in distinct classes. *)
Theorem duplicate_leaves_not_clean : ~ EggSpec.clean a duplicate_leaves.
Proof.
  intro Hclean.
  assert (Hone : EggSpec.nodes_get duplicate_leaves 1%positive = Some leaf).
  { rewrite lookup; destruct (Pos.eq_dec 1%positive 2%positive);
      destruct (Pos.eq_dec 1%positive 1%positive); congruence. }
  assert (Htwo : EggSpec.nodes_get duplicate_leaves 2%positive = Some leaf).
  { rewrite lookup; destruct (Pos.eq_dec 2%positive 2%positive); congruence. }
  pose proof (EggSpec.congruence_closed a duplicate_leaves Hclean
    1%positive 2%positive leaf leaf Hone Htwo eq_refl) as Hsame.
  change (Egraph.find a duplicate_leaves 1%positive =
    Egraph.find a duplicate_leaves 2%positive) in Hsame.
  rewrite !find in Hsame; discriminate.
Qed.

(** Every finite term represented by this raw graph is its one variable production. *)
Theorem duplicate_leaves_representation c e :
  EggSpec.represents a duplicate_leaves c e -> e = EggTerm.Var s v.
Proof.
  intros Hrep; destruct Hrep as
    [c i s' v' Hsame Hnode|c i s' op cs args Hsame Hnode Hargs].
  - apply stored_leaf in Hnode; unfold leaf in Hnode.
    injection Hnode as <- <-; reflexivity.
  - apply stored_leaf in Hnode; discriminate.
Qed.

(** Duplicate singleton productions are sound for any generated equality and semantic model. *)
Theorem duplicate_leaves_sound {H F C} adm (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) :
  EggSpec.sound a adm facts rules duplicate_leaves.
Proof.
  intros c t u Ht Hu.
  apply duplicate_leaves_representation in Ht.
  apply duplicate_leaves_representation in Hu.
  subst t u; apply EggEqual.refl.
Qed.

(** Updating memo data alone cannot make the duplicate singleton graph congruence closed. *)
Theorem duplicate_leaves_require_merge h :
  Egraph.nodes h = Egraph.nodes duplicate_leaves ->
  EggSpec.same_class_equal a duplicate_leaves h -> ~ EggSpec.clean a h.
Proof.
  intros Hnodes Hclasses Hclean.
  assert (Hlookup : forall i, EggSpec.nodes_get h i = EggSpec.nodes_get duplicate_leaves i).
  { intro i.
    change (Map.get Egraph.id_encoding i (Egraph.nodes h) =
      Map.get Egraph.id_encoding i (Egraph.nodes duplicate_leaves)).
    now rewrite Hnodes. }
  assert (Hone : EggSpec.nodes_get h 1%positive = Some leaf).
  { rewrite Hlookup, lookup.
    destruct (Pos.eq_dec 1%positive 2%positive);
      destruct (Pos.eq_dec 1%positive 1%positive); congruence. }
  assert (Htwo : EggSpec.nodes_get h 2%positive = Some leaf).
  { rewrite Hlookup, lookup.
    destruct (Pos.eq_dec 2%positive 2%positive); congruence. }
  pose proof (EggSpec.congruence_closed a h Hclean
    1%positive 2%positive leaf leaf Hone Htwo eq_refl) as Hsame.
  apply (proj2 (Hclasses 1%positive 2%positive)) in Hsame.
  change (Egraph.find a duplicate_leaves 1%positive =
    Egraph.find a duplicate_leaves 2%positive) in Hsame.
  rewrite !find in Hsame; discriminate.
Qed.

End Graph.

End EggCoreDomain.
