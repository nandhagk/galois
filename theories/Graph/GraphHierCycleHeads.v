(** * A cycle's common enclosing header

    Recursive SCC exactness places each nonempty cycle under a header on that same cycle.
    For example, a cycle avoiding an outer header is handled by the exact header-deleted body.
    Builds on: GraphHierCycles, GraphLoopStructure and GraphHierFacts. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphHierFacts GraphHierCycles GraphLoopStructure GraphTarjanState.
Import List.ListNotations.

Module HierCycleHeads.

Local Lemma points_tail {V E} (p : Prepared.t V E) u e v es x :
  Prepared.arc p u e v ->
  In x (HierCycles.points p v es) -> In x (HierCycles.points p u (e :: es)).
Proof.
  intros Harc [<-|Hin]; right; apply Prepared.present_spec.
  - exists e. split; [now left|exact (HierCycles.arc_target p u e v Harc)].
  - apply Prepared.present_spec in Hin. destruct Hin as [edge [Hin Htarget]].
    exists edge. split; [now right|exact Htarget].
Qed.

Local Lemma path_scope_points {V E} (p : Prepared.t V E) source target u es v :
  Search.scoped_path p source u es v ->
  (forall x, In x (HierCycles.points p u es) -> Scope.admits target x = true) ->
    Search.scoped_path p target u es v.
Proof.
  intro Hpath.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH]; intro Hallowed.
  - apply Search.scoped_nil; [exact Hv|apply Hallowed; now left].
  - eapply Search.scoped_cons; [exact Hu|apply Hallowed; now left|exact Harc|].
    apply IH. intros x Hx. apply Hallowed. exact (points_tail p u e v es x Harc Hx).
Qed.

Local Lemma removed_allowed {V E} (p : Prepared.t V E) scope h body v es :
  Search.scoped_path p scope v es v ->
  (forall x, In x (HierCycles.points p v es) -> In x (h :: Hier.members body)) ->
  ~ In h (HierCycles.points p v es) ->
  forall x, In x (HierCycles.points p v es) ->
    Scope.admits (Hier.remove_header scope h (h :: Hier.members body)) x = true.
Proof.
  intros Hcycle Hmembers Hheader x Hx.
  destruct (HierCycles.point_paths p scope v es x Hcycle Hx)
    as [first [last [_ [Hfirst Hlast]]]].
  pose proof (proj2 (HierFacts.path_target p scope v first x Hfirst)) as Ha.
  rewrite Scope.admits_equation in Ha. apply andb_true_iff in Ha.
  destruct Ha as [Hblocked Hwithin]. apply negb_true_iff in Hblocked.
  rewrite Scope.admits_equation. unfold Hier.remove_header.
  cbn [Scope.blocked Scope.within]. rewrite FinSet.mem_add_raw, Hblocked.
  assert (Hne : eqb positive_encoding x h = false).
  { apply Bool.not_true_is_false. intro Heq.
    apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq.
    subst x. contradiction. }
  rewrite Hne. cbn [orb negb andb]. rewrite FinSet.mem_of_list.
  apply (proj2 (TarjanStateFacts.member_test x _)), Hmembers, Hx.
Qed.

Local Lemma removed_cycle {V E} (p : Prepared.t V E) scope h body v es :
  Search.scoped_path p scope v es v ->
  (forall x, In x (HierCycles.points p v es) -> In x (h :: Hier.members body)) ->
  ~ In h (HierCycles.points p v es) ->
  Search.scoped_reachable p (Hier.remove_header scope h (h :: Hier.members body))
    (Hier.members body) v /\
  Search.scoped_path p (Hier.remove_header scope h (h :: Hier.members body)) v es v.
Proof.
  intros Hcycle Hmembers Hheader.
  pose proof (removed_allowed p scope h body v es Hcycle Hmembers Hheader) as Hallowed.
  split.
  - exists v, []. split.
    + destruct (Hmembers v (or_introl eq_refl)) as [Heq|Hin].
      * subst v. exfalso. apply Hheader. now left.
      * exact Hin.
    + apply Search.scoped_nil.
      * exact (proj1 (HierFacts.path_target p scope v es v Hcycle)).
      * apply Hallowed. now left.
  - exact (path_scope_points p _ _ v es v Hcycle Hallowed).
Qed.

Definition forest_heads {V E} (p : Prepared.t V E) scope roots f :=
  forall v es, Search.scoped_reachable p scope roots v ->
  Search.scoped_path p scope v es v -> es <> [] ->
  exists h, In h (HierCycles.points p v es) /\
    forall x, In x (HierCycles.points p v es) -> LoopStructure.in_loop f h x.

Definition tree_heads {V E} (p : Prepared.t V E) scope roots t :=
  forall v es, Search.scoped_reachable p scope roots v ->
  Search.scoped_path p scope v es v -> es <> [] -> In v (Hier.members_tree t) ->
  exists h, In h (HierCycles.points p v es) /\
    forall x, In x (HierCycles.points p v es) ->
      LoopStructure.in_loop (Hier.Cons t Hier.Nil) h x.

Scheme exact_mut := Induction for Hier.exact Sort Prop
with blocks_mut := Induction for Hier.blocks_exact Sort Prop.
Combined Scheme exact_blocks_mut from exact_mut, blocks_mut.

(** Exact hierarchies give each nonempty scoped cycle a common enclosing header on that cycle. *)
Theorem exact_heads {V E} (p : Prepared.t V E) :
  (forall scope roots f, Hier.exact p scope roots f -> forest_heads p scope roots f) /\
  (forall scope roots f, Hier.blocks_exact p scope roots f ->
    forall t, Hier.top_tree f t -> tree_heads p scope roots t).
Proof.
  apply exact_blocks_mut.
  - intros scope roots f Hnodup Hcoverage Hblocks IHblocks Horder v es Hreach Hcycle Hnonempty.
    destruct (LoopStructure.top_member f v (proj2 (Hcoverage v) Hreach)) as [t [Htop Hv]].
    destruct (IHblocks t Htop v es Hreach Hcycle Hnonempty Hv) as [h [Hpoint Hmembers]].
    exists h. split; [exact Hpoint|]. intros x Hx.
    exact (LoopStructure.member_top f t h x Htop (Hmembers x Hx)).
  - intros scope roots t Htop. inversion Htop.
  - intros scope roots v rest Hblock Hself Hrest IH t Htop.
    inversion Htop; subst.
    + intros u es Hreach Hcycle Hnonempty Hu.
      destruct Hu as [<-|Hfalse]; [|contradiction].
      pose proof (HierCycles.points_in_block p scope roots [v] v es Hblock
        (or_introl eq_refl) Hcycle) as Hpoints.
      destruct (HierCycles.singleton_cycle p scope v es Hcycle Hnonempty
        ltac:(intros x Hx; destruct (Hpoints x Hx) as [Heq|Hfalse];
          [symmetry; exact Heq|contradiction])) as [e Harc].
      exfalso. exact (Hself e Harc).
    + now apply IH.
  - intros scope roots h body rest Hblock Hcyclic Hentry Hbody IHbody Hrest IHrest t Htop.
    inversion Htop; subst.
    + intros v es Hreach Hcycle Hnonempty Hv.
      pose proof (HierCycles.points_in_block p scope roots (h :: Hier.members body) v es
        Hblock Hv Hcycle) as Hpoints.
      destruct (in_dec Pos.eq_dec h (HierCycles.points p v es)) as [Hon|Hoff].
      * exists h. split; [exact Hon|]. intros x Hx. exists body.
        split; [constructor|exact (Hpoints x Hx)].
      * destruct (removed_cycle p scope h body v es Hcycle Hpoints Hoff) as [Hroot Hremoved].
        destruct (IHbody v es Hroot Hremoved Hnonempty) as [head [Hhead Hmembers]].
        exists head. split; [exact Hhead|]. intros x Hx.
        destruct (Hmembers x Hx) as [inside [Hcomponent Hmember]].
        exists inside. split; [now apply LoopStructure.component_body|exact Hmember].
    + now apply IHrest.
Qed.

End HierCycleHeads.
