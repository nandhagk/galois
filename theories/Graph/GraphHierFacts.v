(** * Hierarchy projection guarantees

    Exact hierarchy edges become forward edges or returns to enclosing weak-order headers.
    For example, an edge from an inner body to its outer header is justified by that header stack.
    Builds on: GraphHierSpec, GraphWeakOrderFacts and GraphTarjanLow. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphHierSpec GraphWeakOrderFacts GraphTarjanLow.
Import List.ListNotations.

Module HierFacts.

Definition forest_edges {V E} (p : Prepared.t V E) f :=
  forall u e v, Prepared.arc p u e v ->
  In u (Hier.members f) -> In v (Hier.members f) ->
  before (Hier.members f) u v \/
  exists stack, In (u, stack) (Wto.annotate [] (Wto.of_forest f)) /\ In v stack.

Definition tree_edges {V E} (p : Prepared.t V E) t :=
  forall u e v, Prepared.arc p u e v ->
  In u (Hier.members_tree t) -> In v (Hier.members_tree t) ->
  before (Hier.members_tree t) u v \/
  exists stack, In (u, stack)
    (Wto.annotate [] (Cost.value (Wto.emit_tree_c t []))) /\ In v stack.

Local Lemma before_suffix {A} (xs ys : list A) u v :
  before xs u v -> before (xs ++ ys) u v.
Proof.
  intros [first [middle [last ->]]]. exists first, middle, (last ++ ys).
  rewrite <- !app_assoc. cbn [app]. now rewrite <- app_assoc.
Qed.

Local Lemma top_before f t u v :
  Hier.top_tree f t -> before (Hier.members_tree t) u v -> before (Hier.members f) u v.
Proof.
  intro Htop. induction Htop; intro Hbefore; cbn [Hier.members].
  - now apply before_suffix.
  - apply TarjanLow.before_prefix, IHHtop, Hbefore.
Qed.

Local Lemma component_target_head h body u :
  In u (h :: Hier.members body) ->
  exists stack, In (u, stack)
    (Wto.annotate [] (Cost.value (Wto.emit_tree_c (Hier.Component h body) []))) /\
    In h stack.
Proof.
  intro Hu. rewrite WeakOrderFacts.component_tree_annotation.
  destruct Hu as [<-|Hu].
  - exists [h]. split; now left.
  - destruct (WeakOrderFacts.member_annotation body u Hu) as [stack Hstack].
    exists (stack ++ [h]). split.
    + right. apply in_map_iff. exists (u, stack). split; [reflexivity|exact Hstack].
    + apply in_or_app. right. now left.
Qed.

Local Lemma component_edges {V E} (p : Prepared.t V E) h body :
  forest_edges p body -> tree_edges p (Hier.Component h body).
Proof.
  intros Hbody u e v Harc Hu Hv. cbn [Hier.members_tree] in Hu, Hv |- *.
  destruct Hv as [<-|Hv].
  - right. now apply component_target_head.
  - destruct Hu as [<-|Hu].
    + left. apply TarjanLow.before_cons. now left.
    + destruct (Hbody u e v Harc Hu Hv) as [Hforward|[stack [Hrow Hhead]]].
      * left. apply TarjanLow.before_cons. now right.
      * right. exists (stack ++ [h]). split.
        -- rewrite WeakOrderFacts.component_tree_annotation. right.
           apply in_map_iff. exists (u, stack). split; [reflexivity|exact Hrow].
        -- apply in_or_app. now left.
Qed.

Scheme exact_mut := Induction for Hier.exact Sort Prop
with blocks_mut := Induction for Hier.blocks_exact Sort Prop.
Combined Scheme exact_blocks_mut from exact_mut, blocks_mut.

(** Every exact hierarchy orders all internal arcs by its member order and enclosing heads. *)
Theorem internal_edges {V E} (p : Prepared.t V E) :
  (forall scope roots f, Hier.exact p scope roots f -> forest_edges p f) /\
  (forall scope roots f, Hier.blocks_exact p scope roots f ->
    forall t, Hier.top_tree f t -> tree_edges p t).
Proof.
  apply exact_blocks_mut.
  - intros scope roots f Hnodup Hcoverage Hblocks IHblocks Horder u e v Harc Hu Hv.
    destruct (Horder u e v Harc Hu Hv) as [Hforward|[t [Htop [Hut Hvt]]]].
    + now left.
    + destruct (IHblocks t Htop u e v Harc Hut Hvt) as [Hforward|[stack [Hrow Hhead]]].
      * left. exact (top_before f t u v Htop Hforward).
      * right. exists stack. split; [|exact Hhead].
        exact (WeakOrderFacts.top_annotation f t u stack Htop Hrow).
  - intros scope roots t Htop. inversion Htop.
  - intros scope roots v rest Hblock Hself Hrest IH t Htop.
    inversion Htop as [here tail|here tail x Hthere]; subst.
    + intros u e w Harc [<-|Hfalseu] [<-|Hfalsev]; try contradiction.
      exfalso. exact (Hself e Harc).
    + exact (IH t Hthere).
  - intros scope roots h body rest Hblock Hcyclic Hentry Hbody IHbody Hrest IHrest t Htop.
    inversion Htop as [here tail|here tail x Hthere]; subst.
    + now apply component_edges.
    + exact (IHrest t Hthere).
Qed.

(** Every scoped path ends at a valid admitted ID. *)
Theorem path_target {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intro Hpath. induction Hpath; tauto.
Qed.

(** A well-formed client graph gives every interpreted arc a valid target ID. *)
Theorem arc_target_valid {V E} (p : Prepared.t V E) u e v :
  graph_wf (Prepared.graph p) -> Prepared.arc p u e v -> Prepared.valid_id p v.
Proof.
  intros Hwf [a [b [Ha [Hid [Htarget [Hsource [Hendpoint Hedge]]]]]]].
  exists b. split; [|exact Htarget].
  rewrite <- Hendpoint. exact (out_target_in Hwf a e Ha Hedge).
Qed.

(** Arcs to allowed targets preserve rooted scoped reachability over closed graph endpoints. *)
Theorem reachable_step {V E} (p : Prepared.t V E) scope roots u e v :
  graph_wf (Prepared.graph p) -> Search.scoped_reachable p scope roots u ->
  Prepared.arc p u e v -> Scope.admits scope v = true ->
    Search.scoped_reachable p scope roots v.
Proof.
  intros Hwf [r [es [Hr Hpath]]] Harc Htarget_allowed.
  destruct (path_target p scope r es u Hpath) as [Hvalid Hallowed].
  exists r, (es ++ [e]). split; [exact Hr|].
  eapply TarjanLow.path_append; [exact Hpath|].
  eapply Search.scoped_cons; [exact Hvalid|exact Hallowed|exact Harc|].
  apply Search.scoped_nil; [exact (arc_target_valid p u e v Hwf Harc)|exact Htarget_allowed].
Qed.

(** Exact forests over closed graph endpoints flatten to valid scoped weak orders. *)
Theorem exact_wto_valid {V E} (p : Prepared.t V E) scope roots f :
  graph_wf (Prepared.graph p) -> Hier.exact p scope roots f ->
    Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  intros Hwf Hexact.
  pose proof (proj1 (internal_edges p) scope roots f Hexact) as Hedges.
  destruct Hexact as [scope roots f Hnodup Hcoverage Hblocks Horder].
  constructor.
  - apply Wto.of_forest_balanced.
  - rewrite (proj2 WeakOrderFacts.order_members). exact Hnodup.
  - intro v. rewrite (proj2 WeakOrderFacts.order_members). apply Hcoverage.
  - intros u e v Harc Hu Hallowed.
    rewrite (proj2 WeakOrderFacts.order_members) in Hu |- *.
    apply (Hedges u e v Harc Hu).
    apply Hcoverage. exact (reachable_step p scope roots u e v Hwf
      (proj1 (Hcoverage u) Hu) Harc Hallowed).
Qed.

(** Ready preparation discharges the endpoint-closure duty of hierarchy flattening. *)
Theorem exact_wto_valid_ready {V E} (p : Prepared.t V E) scope roots f :
  Prepared.ready p -> Hier.exact p scope roots f ->
    Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  intros Hready Hexact. exact (exact_wto_valid p scope roots f (proj1 Hready) Hexact).
Qed.

(** Empty roots have an exact empty hierarchy for every scope and prepared record. *)
Theorem empty_roots_exact {V E} (p : Prepared.t V E) scope :
  Hier.exact p scope [] Hier.Nil.
Proof.
  constructor.
  - constructor.
  - intro v. split.
    + intro Hfalse. contradiction.
    + intros [r [es [Hfalse _]]]. contradiction.
  - constructor.
  - intros u e v Harc Hfalse. contradiction.
Qed.

End HierFacts.
