(** * Structural loop occurrences

    A loop is the subtree rooted at a component header and includes all its descendant members.
    For example, an inner component's members also belong to its enclosing outer component.
    Builds on: GraphHierSpec, GraphHierCycles and GraphWeakOrderFacts. *)

From Stdlib Require Import List PArith Arith Lia Wf_nat.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphHierCycles GraphWeakOrderFacts GraphTarjanBookkeeping.
Import List.ListNotations.

Module LoopStructure.

(** A component occurrence is either top-level, inside a component body or among later siblings. *)
Inductive component : Hier.forest -> positive -> Hier.forest -> Prop :=
  | component_here : forall h body rest, component (Hier.Cons (Hier.Component h body) rest) h body
  | component_body : forall outer body rest h inside,
      component body h inside -> component (Hier.Cons (Hier.Component outer body) rest) h inside
  | component_rest : forall t rest h body,
      component rest h body -> component (Hier.Cons t rest) h body.

(** Membership reads the members under a component header directly from the forest. *)
Definition in_loop f h v := exists body, component f h body /\ In v (h :: Hier.members body).

(** Component members occur among the members of their containing forest. *)
Theorem component_members f h body :
  component f h body -> incl (h :: Hier.members body) (Hier.members f).
Proof.
  intro Hcomponent. induction Hcomponent; intros v Hv; cbn [Hier.members Hier.members_tree].
  - apply in_or_app. now left.
  - apply in_or_app. left. right. now apply IHHcomponent.
  - apply in_or_app. right. now apply IHHcomponent.
Qed.

(** Every component occurrence contributes its actual opening token to the forest projection. *)
Theorem component_open f h body :
  component f h body -> In (Wto.WOpen h) (Wto.of_forest f).
Proof.
  intro Hcomponent. induction Hcomponent.
  - rewrite WeakOrderFacts.component_equation. now left.
  - rewrite WeakOrderFacts.component_equation. right. apply in_or_app. now left.
  - destruct t as [v|outer inside].
    + rewrite WeakOrderFacts.vertex_equation. now right.
    + rewrite WeakOrderFacts.component_equation. right.
      apply in_or_app. right. now right.
Qed.

Local Lemma rest_row t rest v stack :
  In (v, stack) (Wto.annotate [] (Wto.of_forest rest)) ->
    In (v, stack) (Wto.annotate [] (Wto.of_forest (Hier.Cons t rest))).
Proof.
  intro Hin. rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
    (proj1 WeakOrderFacts.annotate_emit), <- Wto.of_forest_equation.
  apply in_or_app. now right.
Qed.

(** Structural membership agrees with the weak-order projection's enclosing headers. *)
Theorem member_annotation f h v :
  in_loop f h v ->
  exists stack, In (v, stack) (Wto.annotate [] (Wto.of_forest f)) /\ In h stack.
Proof.
  intros [body [Hcomponent Hv]]. revert v Hv.
  induction Hcomponent as [h body rest|outer body rest h inside Hcomponent IH|
    t rest h body Hcomponent IH]; intros v Hv.
  - rewrite WeakOrderFacts.component_annotation.
    destruct Hv as [<-|Hv].
    + exists [h]. split; now left.
    + destruct (WeakOrderFacts.member_annotation body v Hv) as [stack Hrow].
      exists (stack ++ [h]). split.
      * right. apply in_or_app. left. apply in_map_iff.
        exists (v, stack). split; [reflexivity|exact Hrow].
      * apply in_or_app. right. now left.
  - destruct (IH v Hv) as [stack [Hrow Hhead]].
    exists (stack ++ [outer]). split.
    + rewrite WeakOrderFacts.component_annotation. right. apply in_or_app. left.
      apply in_map_iff. exists (v, stack). split; [reflexivity|exact Hrow].
    + apply in_or_app. now left.
  - destruct (IH v Hv) as [stack [Hrow Hhead]].
    exists stack. split; [now apply rest_row|exact Hhead].
Qed.

(** Every forest member belongs to one of its actual top-level trees. *)
Theorem top_member f v :
  In v (Hier.members f) ->
    exists t, Hier.top_tree f t /\ In v (Hier.members_tree t).
Proof.
  induction f as [|t rest IH]; intro Hin; [contradiction|].
  cbn [Hier.members] in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - exists t. split; [constructor|exact Hin].
  - destruct (IH Hin) as [tree [Htop Hmember]]. exists tree.
    split; [now apply Hier.top_there|exact Hmember].
Qed.

(** A component of a singleton top-level tree keeps its identity when siblings are attached. *)
Theorem component_attach t rest h body :
  component (Hier.Cons t Hier.Nil) h body -> component (Hier.Cons t rest) h body.
Proof.
  intro Hcomponent. inversion Hcomponent; subst; [constructor|now apply component_body|].
  match goal with H : component Hier.Nil _ _ |- _ => inversion H end.
Qed.

(** Components of a top-level tree occur in its containing forest with unchanged bodies. *)
Theorem component_top f t h body :
  Hier.top_tree f t -> component (Hier.Cons t Hier.Nil) h body -> component f h body.
Proof.
  intro Htop. induction Htop; intro Hcomponent.
  - now apply component_attach.
  - apply component_rest. now apply IHHtop.
Qed.

(** Loop membership inside a top-level tree lifts unchanged to its containing forest. *)
Theorem member_top f t h v :
  Hier.top_tree f t -> in_loop (Hier.Cons t Hier.Nil) h v -> in_loop f h v.
Proof.
  intros Htop [body [Hcomponent Hmember]]. exists body.
  split; [exact (component_top f t h body Htop Hcomponent)|exact Hmember].
Qed.

Local Lemma top_component f h body :
  Hier.top_tree f (Hier.Component h body) -> component f h body.
Proof.
  intro Htop. remember (Hier.Component h body) as tree eqn:Htree.
  induction Htop as [t rest|t rest x Htop IH].
  - subst t. constructor.
  - apply component_rest, IH, Htree.
Qed.

Local Lemma top_spec {V E} (p : Prepared.t V E) scope roots f t :
  Hier.blocks_exact p scope roots f -> Hier.top_tree f t ->
  Scc.block p scope roots (Hier.members_tree t) /\
  match t with
  | Hier.Vertex v => forall e, ~ Prepared.arc p v e v
  | Hier.Component _ _ => True
  end.
Proof.
  intro Hblocks.
  induction Hblocks as [scope roots|scope roots v rest Hblock Hself Hrest IH|
    scope roots h body rest Hblock Hcyclic Hentry Hbody Hrest IH]; intro Htop.
  - inversion Htop.
  - inversion Htop; subst; [exact (conj Hblock Hself)|now apply IH].
  - inversion Htop; subst; [exact (conj Hblock I)|now apply IH].
Qed.

(** Every rooted node on a nonempty scoped cycle belongs to an actual component subtree. *)
Theorem covers {V E} (p : Prepared.t V E) scope roots f v es :
  Hier.exact p scope roots f ->
  Search.scoped_reachable p scope roots v -> Search.scoped_path p scope v es v ->
  es <> [] -> exists h, in_loop f h v.
Proof.
  intros Hexact Hreach Hcycle Hnonempty.
  destruct Hexact as [scope roots f Hunique Hcoverage Hblocks Horder].
  destruct (top_member f v (proj2 (Hcoverage v) Hreach)) as [tree [Htop Hv]].
  destruct (top_spec p scope roots f tree Hblocks Htop) as [Hblock Hself].
  pose proof (HierCycles.points_in_block p scope roots (Hier.members_tree tree) v es
    Hblock Hv Hcycle) as Hpoints.
  destruct tree as [u|h body].
  - destruct Hv as [<-|Hfalse]; [|contradiction].
    destruct (HierCycles.singleton_cycle p scope u es Hcycle Hnonempty
      ltac:(intros x Hx; specialize (Hpoints x Hx); destruct Hpoints as [Heq|Hfalse];
        [symmetry; exact Heq|contradiction])) as [e Harc].
    exfalso. exact (Hself e Harc).
  - exists h, body. split; [now apply top_component|exact Hv].
Qed.

Local Lemma rest_smaller t rest :
  length (Hier.members rest) < length (Hier.members (Hier.Cons t rest)).
Proof.
  cbn [Hier.members]. rewrite length_app.
  destruct t; cbn [Hier.members_tree length]; lia.
Qed.

Local Lemma body_smaller h body rest :
  length (Hier.members body) <
    length (Hier.members (Hier.Cons (Hier.Component h body) rest)).
Proof.
  cbn [Hier.members Hier.members_tree]. rewrite length_app. cbn [length]. lia.
Qed.

Local Lemma disjoint_subsets (xs ys first last : list positive) :
  NoDup (xs ++ ys) -> incl first xs -> incl last ys ->
    forall v, In v first -> ~ In v last.
Proof.
  intros Hnodup Hfirst Hlast v Hv Hlastv.
  exact (TarjanBook.nodup_disjoint xs ys Hnodup v (Hfirst v Hv) (Hlast v Hlastv)).
Qed.

(** Any two component occurrences of a duplicate-free forest are nested or disjoint. *)
Theorem nested_occurrences f :
  NoDup (Hier.members f) -> forall h body k inside,
  component f h body -> component f k inside ->
  incl (h :: Hier.members body) (k :: Hier.members inside) \/
  incl (k :: Hier.members inside) (h :: Hier.members body) \/
  (forall v, In v (h :: Hier.members body) -> ~ In v (k :: Hier.members inside)).
Proof.
  induction f as [f IH] using
    (well_founded_induction (well_founded_ltof _ (fun f => length (Hier.members f)))).
  intros Hnodup h body k inside Hfirst Hlast.
  destruct f as [|tree rest]; [inversion Hfirst|].
  destruct tree as [v|outer middle].
  - inversion Hfirst; subst. inversion Hlast; subst.
    apply (IH rest (rest_smaller (Hier.Vertex v) rest)).
    + exact (proj2 (TarjanBook.nodup_parts _ _ Hnodup)).
    + assumption.
    + assumption.
  - assert (Hparts : NoDup (outer :: Hier.members middle) /\ NoDup (Hier.members rest)).
    { exact (TarjanBook.nodup_parts _ _ Hnodup). }
    assert (Hmiddle : NoDup (Hier.members middle)).
    { pose proof (proj1 Hparts) as Hprefix. inversion Hprefix; assumption. }
    inversion Hfirst as [head content tail|outside content tail head content' Hfirstbody|
      firsttree tail head content Hfirstrest]; subst.
    + inversion Hlast as [head content tail|outside content tail head content' Hlastbody|
        lasttree tail head content Hlastrest]; subst.
      * left. intros x Hx. exact Hx.
      * right. left. intros x Hx. right. exact (component_members _ _ _ Hlastbody x Hx).
      * right. right. apply (disjoint_subsets _ _ _ _ Hnodup).
        -- intros x Hx. exact Hx.
        -- exact (component_members _ _ _ Hlastrest).
    + inversion Hlast as [head content tail|outside content tail head content' Hlastbody|
        lasttree tail head content Hlastrest]; subst.
      * left. intros x Hx. right. exact (component_members _ _ _ Hfirstbody x Hx).
      * exact (IH middle (body_smaller outer middle rest) Hmiddle
          h body k inside Hfirstbody Hlastbody).
      * right. right. apply (disjoint_subsets _ _ _ _ Hnodup).
        -- intros x Hx. right. exact (component_members _ _ _ Hfirstbody x Hx).
        -- exact (component_members _ _ _ Hlastrest).
    + inversion Hlast as [head content tail|outside content tail head content' Hlastbody|
        lasttree tail head content Hlastrest]; subst.
      * right. right. intros x Hx Hy.
        exact (TarjanBook.nodup_disjoint _ _ Hnodup x Hy
          (component_members _ _ _ Hfirstrest x Hx)).
      * right. right. intros x Hx Hy.
        exact (TarjanBook.nodup_disjoint _ _ Hnodup x
          (or_intror (component_members _ _ _ Hlastbody x Hy))
          (component_members _ _ _ Hfirstrest x Hx)).
      * exact (IH rest (rest_smaller (Hier.Component outer middle) rest) (proj2 Hparts)
          h body k inside Hfirstrest Hlastrest).
Qed.

End LoopStructure.
