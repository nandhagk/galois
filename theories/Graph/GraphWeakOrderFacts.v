(** * Structural observations of hierarchy tokens

    Token emission keeps the forest's member order and restores the incoming header stack.
    For example, a closed inner component leaves its outer header active for its next sibling.
    Builds on: GraphHierSpec. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphHierSpec.
Import List.ListNotations.

Module WeakOrderFacts.

Local Lemma emit_tail :
  (forall t tail, Cost.value (Wto.emit_tree_c t tail) =
    Cost.value (Wto.emit_tree_c t []) ++ tail) /\
  (forall f tail, Cost.value (Wto.emit_forest_c f tail) =
    Wto.of_forest f ++ tail).
Proof.
  apply Hier.forest_tree_ind.
  - intros v tail. rewrite !Wto.emit_tree_equation. reflexivity.
  - intros h body IH tail. rewrite !Wto.emit_tree_equation, !IH.
    cbn [app]. now rewrite <- app_assoc.
  - intro tail. rewrite Wto.emit_forest_equation, Wto.of_forest_equation,
      Wto.emit_forest_equation. reflexivity.
  - intros t IHt rest IHr tail.
    rewrite (Wto.of_forest_equation (Hier.Cons t rest)),
      (Wto.emit_forest_equation (Hier.Cons t rest) tail),
      (Wto.emit_forest_equation (Hier.Cons t rest) []).
    rewrite (IHt (Cost.value (Wto.emit_forest_c rest tail))),
      (IHt (Cost.value (Wto.emit_forest_c rest []))), (IHr tail), (IHr []).
    now rewrite app_nil_r, app_assoc.
Qed.

(** A vertex contributes one token before the flattening of its remaining siblings. *)
Theorem vertex_equation v rest :
  Wto.of_forest (Hier.Cons (Hier.Vertex v) rest) =
    Wto.WVertex v :: Wto.of_forest rest.
Proof.
  rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
    Wto.emit_tree_equation. now rewrite <- Wto.of_forest_equation.
Qed.

(** A component encloses its body's tokens before the flattening of its siblings. *)
Theorem component_equation h body rest :
  Wto.of_forest (Hier.Cons (Hier.Component h body) rest) =
    Wto.WOpen h :: Wto.of_forest body ++ Wto.WClose :: Wto.of_forest rest.
Proof.
  rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
    Wto.emit_tree_equation, (proj2 emit_tail).
  now rewrite <- Wto.of_forest_equation.
Qed.

(** An empty forest emits no tokens. *)
Theorem nil_equation : Wto.of_forest Hier.Nil = [].
Proof.
  rewrite Wto.of_forest_equation, Wto.emit_forest_equation. reflexivity.
Qed.

(** Appending token lists appends their vertex orders. *)
Theorem order_app first last :
  Wto.order (first ++ last) = Wto.order first ++ Wto.order last.
Proof.
  induction first as [|[v|h|] rest IH].
  - cbn [app]. rewrite (Wto.order_equation []). reflexivity.
  - cbn [app]. rewrite (Wto.order_equation (Wto.WVertex v :: _)),
      (Wto.order_equation (Wto.WVertex v :: _)). now rewrite IH.
  - cbn [app]. rewrite (Wto.order_equation (Wto.WOpen h :: _)),
      (Wto.order_equation (Wto.WOpen h :: _)). now rewrite IH.
  - cbn [app]. rewrite (Wto.order_equation (Wto.WClose :: _)),
      (Wto.order_equation (Wto.WClose :: _)). exact IH.
Qed.

(** Closing a well-formed forest segment restores its original enclosing stack. *)
Theorem annotate_emit :
  (forall t stack tail,
    Wto.annotate stack (Cost.value (Wto.emit_tree_c t tail)) =
      Wto.annotate stack (Cost.value (Wto.emit_tree_c t [])) ++
      Wto.annotate stack tail) /\
  (forall f stack tail,
    Wto.annotate stack (Cost.value (Wto.emit_forest_c f tail)) =
      Wto.annotate stack (Wto.of_forest f) ++ Wto.annotate stack tail).
Proof.
  apply Hier.forest_tree_ind.
  - intros v stack tail.
    rewrite (Wto.emit_tree_equation (Hier.Vertex v) tail),
      (Wto.emit_tree_equation (Hier.Vertex v) []),
      (Wto.annotate_equation stack (Wto.WVertex v :: tail)),
      (Wto.annotate_equation stack [Wto.WVertex v]),
      (Wto.annotate_equation stack []).
    reflexivity.
  - intros h body IH stack tail.
    rewrite !Wto.emit_tree_equation,
      (Wto.annotate_equation stack (Wto.WOpen h :: _)),
      (Wto.annotate_equation stack (Wto.WOpen h :: _)), !IH.
    rewrite (Wto.annotate_equation (h :: stack) (Wto.WClose :: tail)),
      (Wto.annotate_equation (h :: stack) [Wto.WClose]).
    cbn [tl app]. now rewrite app_nil_r.
  - intros stack tail. rewrite Wto.emit_forest_equation, nil_equation,
      (Wto.annotate_equation stack []). reflexivity.
  - intros t IHt rest IHr stack tail.
    rewrite (Wto.of_forest_equation (Hier.Cons t rest)),
      (Wto.emit_forest_equation (Hier.Cons t rest) tail),
      (Wto.emit_forest_equation (Hier.Cons t rest) []).
    rewrite (IHt stack (Cost.value (Wto.emit_forest_c rest tail))),
      (IHt stack (Cost.value (Wto.emit_forest_c rest []))),
      (IHr stack tail), (IHr stack []).
    rewrite (Wto.annotate_equation stack []), app_nil_r, app_assoc.
    reflexivity.
Qed.

(** Flattening a forest lists each member at its structural position. *)
Theorem order_members :
  (forall t, Wto.order (Cost.value (Wto.emit_tree_c t [])) = Hier.members_tree t) /\
  (forall f, Wto.order (Wto.of_forest f) = Hier.members f).
Proof.
  apply Hier.forest_tree_ind.
  - intro v. rewrite Wto.emit_tree_equation,
      (Wto.order_equation [Wto.WVertex v]), (Wto.order_equation []). reflexivity.
  - intros h body IH. rewrite Wto.emit_tree_equation, (proj2 emit_tail),
      (Wto.order_equation (Wto.WOpen h :: _)), order_app,
      (Wto.order_equation [Wto.WClose]), (Wto.order_equation []).
    cbn [Hier.members_tree]. now rewrite IH, app_nil_r.
  - rewrite nil_equation, Wto.order_equation. reflexivity.
  - intros t IHt rest IHr.
    rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
      (proj1 emit_tail), order_app, <- Wto.of_forest_equation, IHt, IHr.
    reflexivity.
Qed.

(** The first projection of every annotation is the corresponding vertex order. *)
Theorem annotation_order w stack : map fst (Wto.annotate stack w) = Wto.order w.
Proof.
  revert stack. induction w as [|[v|h|] rest IH]; intro stack;
    rewrite Wto.annotate_equation, Wto.order_equation; cbn [map fst];
    now rewrite ?IH.
Qed.

Definition extend stack (row : positive * list positive) :=
  (fst row, snd row ++ stack).

Local Lemma extend_nil rows : map (extend []) rows = rows.
Proof.
  rewrite <- (map_id rows) at 2. apply map_ext. intros [v stack].
  unfold extend. cbn [fst snd]. now rewrite app_nil_r.
Qed.

Local Lemma extend_compose inside outside row :
  extend outside (extend inside row) = extend (inside ++ outside) row.
Proof.
  destruct row as [v stack]. unfold extend. cbn [fst snd]. now rewrite app_assoc.
Qed.

(** Entering a forest under an outer stack appends that stack to every emitted annotation. *)
Theorem annotate_context :
  (forall t stack tail,
    Wto.annotate stack (Cost.value (Wto.emit_tree_c t tail)) =
      map (extend stack) (Wto.annotate [] (Cost.value (Wto.emit_tree_c t []))) ++
        Wto.annotate stack tail) /\
  (forall f stack tail,
    Wto.annotate stack (Cost.value (Wto.emit_forest_c f tail)) =
      map (extend stack) (Wto.annotate [] (Wto.of_forest f)) ++ Wto.annotate stack tail).
Proof.
  apply Hier.forest_tree_ind.
  - intros v stack tail. rewrite !Wto.emit_tree_equation,
      (Wto.annotate_equation stack (Wto.WVertex v :: tail)),
      (Wto.annotate_equation [] [Wto.WVertex v]), (Wto.annotate_equation [] []).
    reflexivity.
  - intros h body IH stack tail. rewrite !Wto.emit_tree_equation,
      (Wto.annotate_equation stack (Wto.WOpen h :: _)),
      (Wto.annotate_equation [] (Wto.WOpen h :: _)),
      (IH (h :: stack) (Wto.WClose :: tail)), (IH [h] [Wto.WClose]),
      (Wto.annotate_equation (h :: stack) (Wto.WClose :: tail)),
      (Wto.annotate_equation [h] [Wto.WClose]).
    cbn [tl]. rewrite (Wto.annotate_equation [] []).
    cbn [map app extend fst snd]. rewrite app_nil_r, map_map.
    f_equal. f_equal. apply map_ext. intro row.
    rewrite extend_compose. reflexivity.
  - intros stack tail. rewrite Wto.emit_forest_equation, nil_equation,
      (Wto.annotate_equation [] []). reflexivity.
  - intros t IHt rest IHr stack tail.
    rewrite (Wto.of_forest_equation (Hier.Cons t rest)),
      (Wto.emit_forest_equation (Hier.Cons t rest) tail),
      (Wto.emit_forest_equation (Hier.Cons t rest) []).
    rewrite (IHt stack (Cost.value (Wto.emit_forest_c rest tail))),
      (proj1 annotate_emit t [] (Cost.value (Wto.emit_forest_c rest []))),
      (IHr stack tail), <- Wto.of_forest_equation,
      map_app, app_assoc.
    reflexivity.
Qed.

(** A component annotation records its head and places that head outside every body stack. *)
Theorem component_annotation h body rest :
  Wto.annotate [] (Wto.of_forest (Hier.Cons (Hier.Component h body) rest)) =
    (h, [h]) :: map (extend [h]) (Wto.annotate [] (Wto.of_forest body)) ++
      Wto.annotate [] (Wto.of_forest rest).
Proof.
  rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
    Wto.emit_tree_equation, Wto.annotate_equation, (proj2 annotate_context),
    Wto.annotate_equation, <- Wto.of_forest_equation.
  reflexivity.
Qed.

(** A top-level tree's annotations occur unchanged in its containing forest. *)
Theorem top_annotation f t v stack :
  Hier.top_tree f t ->
  In (v, stack) (Wto.annotate [] (Cost.value (Wto.emit_tree_c t []))) ->
  In (v, stack) (Wto.annotate [] (Wto.of_forest f)).
Proof.
  intros Htop. induction Htop as [t rest|t rest x Htop IH]; intro Hin;
    rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
      (proj1 annotate_emit), <- Wto.of_forest_equation.
  - apply in_or_app. now left.
  - apply in_or_app. right. now apply IH.
Qed.

(** Every forest member has an annotation at its structural position. *)
Theorem member_annotation f v :
  In v (Hier.members f) ->
    exists stack, In (v, stack) (Wto.annotate [] (Wto.of_forest f)).
Proof.
  intro Hin. rewrite <- (proj2 order_members f), <- (annotation_order _ []) in Hin.
  apply in_map_iff in Hin. destruct Hin as [[x stack] [Heq Hin]].
  cbn [fst] in Heq. subst x. now exists stack.
Qed.

(** A singleton forest and its one tree have the same emitted tokens. *)
Theorem singleton_equation t :
  Wto.of_forest (Hier.Cons t Hier.Nil) = Cost.value (Wto.emit_tree_c t []).
Proof.
  rewrite Wto.of_forest_equation, Wto.emit_forest_equation,
    Wto.emit_forest_equation. reflexivity.
Qed.

(** A lone component appends its head to every body annotation's enclosing stack. *)
Theorem component_tree_annotation h body :
  Wto.annotate [] (Cost.value (Wto.emit_tree_c (Hier.Component h body) [])) =
    (h, [h]) :: map (extend [h]) (Wto.annotate [] (Wto.of_forest body)).
Proof.
  rewrite <- singleton_equation, component_annotation, nil_equation,
    Wto.annotate_equation, app_nil_r. reflexivity.
Qed.

End WeakOrderFacts.
