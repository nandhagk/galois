(** * SCC block assembly

    Aligned component trees keep SCC order while allowing recursive member permutations.
    For example, moving a component's entry header to its front does not change its SCC membership.
    Builds on: GraphHier, GraphSccSpec and GraphTarjanLow. *)

From Stdlib Require Import List PArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearchInvariant GraphSccSpec GraphHierSpec GraphHier GraphTarjanLow
  GraphTarjanPartition.
Import List.ListNotations.

Module HierStructure.

(** Each ordered component corresponds to one top-level tree with the same members. *)
Inductive aligned : list (list positive) -> Hier.forest -> Prop :=
  | aligned_nil : aligned [] Hier.Nil
  | aligned_cons : forall c cs t rest,
      Permutation c (Hier.members_tree t) -> aligned cs rest ->
      aligned (c :: cs) (Hier.Cons t rest).

(** Aligned assembly only permutes members inside each component. *)
Theorem aligned_members cs f :
  aligned cs f -> Permutation (concat cs) (Hier.members f).
Proof.
  intro Haligned. induction Haligned; [constructor|].
  cbn [concat Hier.members]. now apply Permutation_app.
Qed.

(** Every aligned component has its corresponding top-level tree. *)
Theorem aligned_top cs f c :
  aligned cs f -> In c cs ->
  exists t, Hier.top_tree f t /\ Permutation c (Hier.members_tree t).
Proof.
  intro Haligned. induction Haligned as [|head tail t rest Hmembers Haligned IH]; intro Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists t. split; [constructor|exact Hmembers].
    + destruct (IH Hin) as [tree [Htop Hperm]]. exists tree.
      split; [now apply Hier.top_there|exact Hperm].
Qed.

(** Aligned cross-component precedence gives forward precedence between their actual members. *)
Theorem aligned_before cs f first last u v :
  aligned cs f -> before cs first last -> In u first -> In v last ->
    before (Hier.members f) u v.
Proof.
  intro Haligned. induction Haligned as [|c cs t rest Hmembers Haligned IH];
    intros Hbefore Hu Hv.
  - destruct Hbefore as [[|c prefix] [middle [suffix Hbad]]]; discriminate.
  - apply TarjanLow.before_cons in Hbefore.
    destruct Hbefore as [[-> Hlast]|Hbefore]; cbn [Hier.members].
    + apply TarjanLow.before_cross.
      * exact (Permutation_in u Hmembers Hu).
      * apply (Permutation_in v (aligned_members cs rest Haligned)).
        apply in_concat. exists last. auto.
    + apply TarjanLow.before_prefix. exact (IH Hbefore Hu Hv).
Qed.

Local Lemma indexed_member {V E} (p : Prepared.t V E) scope roots r v :
  Scc.exact p scope roots r -> In v (concat (Scc.components r)) ->
  exists n c, nth_error (Scc.components r) n = Some c /\ In v c /\
    Map.get positive_encoding v (Scc.comp_of r) = Some (Pos.of_succ_nat n).
Proof.
  intros Hexact Hin. apply in_concat in Hin. destruct Hin as [c [Hc Hv]].
  apply In_nth_error in Hc. destruct Hc as [n Hnth].
  exists n, c. split; [exact Hnth|]. split; [exact Hv|].
  apply (Scc.owners_exact _ _ _ _ Hexact).
  exists c. rewrite SuccNat2Pos.id_succ. exact (conj Hnth Hv).
Qed.

(** SCC reverse owner order gives the fixed hierarchy's forward-or-same-top-block condition. *)
Theorem aligned_edges {V E} (p : Prepared.t V E) scope roots r f :
  Scc.exact p scope roots r -> aligned (rev (Scc.components r)) f ->
  forall u e v, Prepared.arc p u e v -> In u (Hier.members f) -> In v (Hier.members f) ->
  before (Hier.members f) u v \/
    exists t, Hier.top_tree f t /\ In u (Hier.members_tree t) /\ In v (Hier.members_tree t).
Proof.
  intros Hexact Haligned u e v Harc Hu Hv.
  pose proof (aligned_members _ _ Haligned) as Hmembers.
  assert (Huin : In u (concat (Scc.components r))).
  { apply (proj1 (TarjanPartition.concat_rev_members (Scc.components r) u)).
    exact (Permutation_in u (Permutation_sym Hmembers) Hu). }
  assert (Hvin : In v (concat (Scc.components r))).
  { apply (proj1 (TarjanPartition.concat_rev_members (Scc.components r) v)).
    exact (Permutation_in v (Permutation_sym Hmembers) Hv). }
  destruct (indexed_member p scope roots r u Hexact Huin) as [n [first [Hfirst [Huf Hownu]]]].
  destruct (indexed_member p scope roots r v Hexact Hvin) as [m [last [Hlast [Hvl Hownv]]]].
  destruct (Nat.eq_dec n m) as [->|Hne].
  - rewrite Hfirst in Hlast. inversion Hlast; subst last.
    destruct (aligned_top _ _ first Haligned
      ltac:(apply (proj1 (in_rev _ _)); now apply nth_error_In in Hfirst))
      as [tree [Htop Hperm]].
    right. exists tree. split; [exact Htop|]. split; eapply Permutation_in; eauto.
  - assert (Hids : Pos.of_succ_nat n <> Pos.of_succ_nat m).
    { intro Heq. apply (f_equal Pos.to_nat) in Heq.
      rewrite !SuccNat2Pos.id_succ in Heq. lia. }
    pose proof (Scc.reverse_topological _ _ _ _ Hexact u e v _ _ Harc Hownu Hownv Hids)
      as Hlt.
    apply Pos2Nat.inj_lt in Hlt. rewrite !SuccNat2Pos.id_succ in Hlt.
    left. apply (aligned_before _ _ first last u v Haligned); [|exact Huf|exact Hvl].
    apply (proj1 (TarjanLow.before_reverse _ last first)).
    apply (proj2 (SearchInvariant.before_indices _ last first)).
    exists m, n. repeat split; auto; lia.
Qed.

(** Aligned exact block trees assemble into an exact forest of the same SCC partition. *)
Theorem forest_exact {V E} (p : Prepared.t V E) scope roots r f :
  Scc.exact p scope roots r ->
  aligned (rev (Scc.components r)) f ->
  Hier.blocks_exact p scope roots f -> Hier.exact p scope roots f.
Proof.
  intros Hexact Haligned Hblocks.
  assert (Hmembers : Permutation (concat (Scc.components r)) (Hier.members f)).
  { eapply Permutation_trans; [apply TarjanPartition.concat_rev_permutation|].
    now apply aligned_members. }
  constructor.
  - exact (Permutation_NoDup Hmembers (Scc.partition_unique _ _ _ _ Hexact)).
  - intro v. rewrite <- (Scc.partition_complete _ _ _ _ Hexact v).
    split; intro Hin.
    + exact (Permutation_in v (Permutation_sym Hmembers) Hin).
    + exact (Permutation_in v Hmembers Hin).
  - exact Hblocks.
  - exact (aligned_edges p scope roots r f Hexact Haligned).
Qed.

Local Lemma attach_blocks {V E} (p : Prepared.t V E) scope roots t rest :
  Hier.blocks_exact p scope roots (Hier.Cons t Hier.Nil) ->
  Hier.blocks_exact p scope roots rest ->
    Hier.blocks_exact p scope roots (Hier.Cons t rest).
Proof.
  intros Htree Hrest. inversion Htree; subst; constructor; assumption.
Qed.

(** Successful callbacks assemble their actual trees with aligned members and exact blocks. *)
Theorem assemble_exact {V E} (p : Prepared.t V E) scope roots cs expand :
  (forall c Hin, exists t, Cost.value (expand c Hin) = Some t /\
    Permutation c (Hier.members_tree t) /\
    Hier.blocks_exact p scope roots (Hier.Cons t Hier.Nil)) ->
  aligned cs (Cost.value (HierRun.assemble_c cs expand)) /\
    Hier.blocks_exact p scope roots (Cost.value (HierRun.assemble_c cs expand)).
Proof.
  revert expand. induction cs as [|c rest IH]; intros expand Hexpand.
  - rewrite HierRun.assemble_value_equation. split; constructor.
  - destruct (Hexpand c (or_introl eq_refl)) as [t [Htree [Hperm Hblocks]]].
    rewrite HierRun.assemble_value_equation, Htree.
    assert (Htail : forall d Hin, exists tree,
      Cost.value (expand d (or_intror Hin)) = Some tree /\
      Permutation d (Hier.members_tree tree) /\
      Hier.blocks_exact p scope roots (Hier.Cons tree Hier.Nil)).
    { intros d Hin. apply Hexpand. }
    destruct (IH _ Htail) as [Haligned Hrest]. split.
    + now constructor.
    + exact (attach_blocks p scope roots t _ Hblocks Hrest).
Qed.

End HierStructure.
