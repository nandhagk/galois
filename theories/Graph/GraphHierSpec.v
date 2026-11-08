(** * Hierarchies, weak orders and loop forests

    Nested components share one representation whose flattening gives a weak order.
    For example, a component with an empty body represents a self-loop header.
    Builds on: GraphSccSpec and GraphDomSpec. *)

From Stdlib Require Import List Bool PArith Arith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSccSpec GraphDomSpec.
Import List.ListNotations Cost.Notations.

Module Hier.

Inductive tree :=
  | Vertex (v : positive)
  | Component (h : positive) (body : forest)
with forest :=
  | Nil
  | Cons (t : tree) (rest : forest).

Scheme tree_ind_mut := Induction for tree Sort Prop
with forest_ind_mut := Induction for forest Sort Prop.
Combined Scheme forest_tree_ind from tree_ind_mut, forest_ind_mut.

Fixpoint members_tree (t : tree) : list positive :=
  match t with
  | Vertex v => [v]
  | Component h body => h :: members body
  end
with members (f : forest) : list positive :=
  match f with
  | Nil => []
  | Cons t rest => members_tree t ++ members rest
  end.

(** A component entry is a root or the target of an edge from another block. *)
Definition entry {V E} (p : Prepared.t V E) scope roots c h :=
  In h c /\ (In h roots \/ exists u e, Search.scoped_reachable p scope roots u /\
    ~ In u c /\ Prepared.arc p u e h).

Definition remove_header scope h c :=
  Scope.Make (FinSet.add positive_encoding h (Scope.blocked scope))
    (Some (FinSet.of_list positive_encoding c)).

(** Top-level trees identify distinct blocks before recursive header deletion. *)
Inductive top_tree : forest -> tree -> Prop :=
  | top_here : forall t rest, top_tree (Cons t rest) t
  | top_there : forall t rest x, top_tree rest x -> top_tree (Cons t rest) x.

(** Exact forests order maximal SCCs and recursively decompose each cyclic block. *)
Inductive exact {V E} (p : Prepared.t V E) :
    Scope.t -> list positive -> forest -> Prop :=
  | exact_forest : forall scope roots f,
      NoDup (members f) ->
      (forall v, In v (members f) <-> Search.scoped_reachable p scope roots v) ->
      blocks_exact p scope roots f ->
      (forall u e v, Prepared.arc p u e v -> In u (members f) -> In v (members f) ->
        before (members f) u v \/
        exists t, top_tree f t /\ In u (members_tree t) /\ In v (members_tree t)) ->
      exact p scope roots f
with blocks_exact {V E} (p : Prepared.t V E) :
    Scope.t -> list positive -> forest -> Prop :=
  | blocks_nil : forall scope roots, blocks_exact p scope roots Nil
  | blocks_vertex : forall scope roots v rest,
      Scc.block p scope roots [v] ->
      (forall e, ~ Prepared.arc p v e v) ->
      blocks_exact p scope roots rest ->
      blocks_exact p scope roots (Cons (Vertex v) rest)
  | blocks_component : forall scope roots h body rest,
      Scc.block p scope roots (h :: members body) ->
      (members body <> [] \/ exists e, Prepared.arc p h e h) ->
      ((exists x, entry p scope roots (h :: members body) x) ->
        entry p scope roots (h :: members body) h) ->
      exact p (remove_header scope h (h :: members body)) (members body) body ->
      blocks_exact p scope roots rest ->
      blocks_exact p scope roots (Cons (Component h body) rest).

End Hier.

Module Wto.

Inductive token :=
  | WVertex (v : positive)
  | WOpen (h : positive)
  | WClose.

Fixpoint emit_tree_c (t : Hier.tree) (tail : list token) : Cost.t (list token) :=
  Cost.step ;;
  match t with
  | Hier.Vertex v => Cost.ret (WVertex v :: tail)
  | Hier.Component h body =>
    let* inside := emit_forest_c body (WClose :: tail) in Cost.ret (WOpen h :: inside)
  end
with emit_forest_c (f : Hier.forest) (tail : list token) : Cost.t (list token) :=
  match f with
  | Hier.Nil => Cost.ret tail
  | Hier.Cons t rest =>
    Cost.step ;;
    let* outside := emit_forest_c rest tail in emit_tree_c t outside
  end.

Definition of_forest_c f := emit_forest_c f [].
Definition of_forest f := Cost.value (of_forest_c f).

(** Emitting a tree places its tokens before the supplied continuation. *)
Theorem emit_tree_equation t tail :
  Cost.value (emit_tree_c t tail) =
  match t with
  | Hier.Vertex v => WVertex v :: tail
  | Hier.Component h body =>
    WOpen h :: Cost.value (emit_forest_c body (WClose :: tail))
  end.
Proof.
  destruct t; reflexivity.
Qed.

(** Emitting a forest processes its sibling continuation before its first tree. *)
Theorem emit_forest_equation f tail :
  Cost.value (emit_forest_c f tail) =
  match f with
  | Hier.Nil => tail
  | Hier.Cons t rest =>
    Cost.value (emit_tree_c t (Cost.value (emit_forest_c rest tail)))
  end.
Proof.
  destruct f; reflexivity.
Qed.

(** Flattening starts the emitter with an empty continuation. *)
Theorem of_forest_equation f :
  of_forest f = Cost.value (emit_forest_c f []).
Proof.
  reflexivity.
Qed.

Fixpoint annotate_c (stack : list positive) (w : list token) :
    Cost.t (list (positive * list positive)) :=
  match w with
  | [] => Cost.ret []
  | WVertex v :: rest =>
    Cost.step ;;
    let* rows := annotate_c stack rest in Cost.ret ((v, stack) :: rows)
  | WOpen h :: rest =>
    Cost.step ;;
    let* rows := annotate_c (h :: stack) rest in Cost.ret ((h, h :: stack) :: rows)
  | WClose :: rest => Cost.step ;; annotate_c (tl stack) rest
  end.

Definition annotate stack w := Cost.value (annotate_c stack w).

Fixpoint order_c (w : list token) : Cost.t (list positive) :=
  match w with
  | [] => Cost.ret []
  | WVertex v :: rest =>
    Cost.step ;; let* vs := order_c rest in Cost.ret (v :: vs)
  | WOpen h :: rest =>
    Cost.step ;; let* vs := order_c rest in Cost.ret (h :: vs)
  | WClose :: rest => Cost.step ;; order_c rest
  end.

Definition order w := Cost.value (order_c w).

(** Annotation records the current enclosing headers and updates them at delimiters. *)
Theorem annotate_equation stack w :
  annotate stack w =
  match w with
  | [] => []
  | WVertex v :: rest => (v, stack) :: annotate stack rest
  | WOpen h :: rest => (h, h :: stack) :: annotate (h :: stack) rest
  | WClose :: rest => annotate (tl stack) rest
  end.
Proof.
  destruct w as [|[v|h|] rest]; reflexivity.
Qed.

(** Token order counts every vertex and opening header and skips closing tokens. *)
Theorem order_equation w :
  order w =
  match w with
  | [] => []
  | WVertex v :: rest => v :: order rest
  | WOpen h :: rest => h :: order rest
  | WClose :: rest => order rest
  end.
Proof.
  destruct w as [|[v|h|] rest]; reflexivity.
Qed.

Fixpoint balanced_from d w :=
  match w with
  | [] => Nat.eqb d 0
  | WVertex _ :: rest => balanced_from d rest
  | WOpen _ :: rest => balanced_from (S d) rest
  | WClose :: rest =>
    match d with
    | O => false
    | S n => balanced_from n rest
    end
  end.

(** A scoped weak order covers its rooted domain and orders every admitted edge. *)
Record valid_within {V E} (p : Prepared.t V E) scope roots w : Prop := {
  balanced : balanced_from 0 w = true;
  unique : NoDup (order w);
  covers : forall v, In v (order w) <->
    Search.scoped_reachable p scope roots v;
  edges : forall a e b, Prepared.arc p a e b -> In a (order w) ->
    Scope.admits scope b = true ->
    before (order w) a b \/
    exists stack, In (a, stack) (annotate [] w) /\ In b stack
}.

(** The ordinary weak-order contract uses the unrestricted graph scope. *)
Definition valid {V E} (p : Prepared.t V E) roots w :=
  valid_within p (Scope.Make FinSet.empty None) roots w.

Local Lemma emit_balanced :
  (forall t d tail, balanced_from d (Cost.value (emit_tree_c t tail)) =
    balanced_from d tail) /\
  (forall f d tail, balanced_from d (Cost.value (emit_forest_c f tail)) =
    balanced_from d tail).
Proof.
  apply Hier.forest_tree_ind.
  - intros v d tail. reflexivity.
  - intros h body IH d tail.
    cbn [emit_tree_c]. autorewrite with galois_cost.
    cbn [balanced_from]. rewrite IH. reflexivity.
  - intros d tail. reflexivity.
  - intros t IHt rest IHr d tail.
    cbn [emit_forest_c]. autorewrite with galois_cost.
    rewrite IHt, IHr. reflexivity.
Qed.

(** Every hierarchy flattening is balanced, including an empty-body self-loop. *)
Theorem of_forest_balanced f : balanced_from 0 (of_forest f) = true.
Proof.
  unfold of_forest, of_forest_c. rewrite (proj2 emit_balanced). reflexivity.
Qed.

Arguments of_forest_c f : simpl never.
Arguments of_forest f : simpl never.
Arguments annotate_c stack w : simpl never.
Arguments annotate stack w : simpl never.
Arguments order_c w : simpl never.
Arguments order w : simpl never.

End Wto.

Module Loops.

Record t := Make {
  loop_parent : Map.t positive positive;
  innermost : Map.t positive positive;
  headers : list positive
}.

(** Loop maps reproduce the headers and innermost-first nesting of an exact hierarchy. *)
Record exact {V E} (p : Prepared.t V E) scope roots f (loops : t) : Prop := {
  hierarchy_exact : Hier.exact p scope roots f;
  headers_exact : forall h, In h (headers loops) <->
    exists rest, In (Wto.WOpen h) (Wto.of_forest f) /\
      In (h, h :: rest) (Wto.annotate [] (Wto.of_forest f));
  headers_unique : NoDup (headers loops);
  maps_wf : Map.wf positive_encoding (loop_parent loops) /\
    Map.wf positive_encoding (innermost loops);
  parent_exact : forall h outer, Map.get positive_encoding h (loop_parent loops) = Some outer <->
    exists rest, In h (headers loops) /\
      In (h, h :: outer :: rest) (Wto.annotate [] (Wto.of_forest f));
  innermost_exact : forall v h, Map.get positive_encoding v (innermost loops) = Some h <->
    exists rest, In (v, h :: rest) (Wto.annotate [] (Wto.of_forest f))
}.

End Loops.

(** Every nonempty listed cycle contains an edge back to a dominator of its source. *)
Definition reducible {V E} (g : Graph.t V E) :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es <> [] ->
    exists e, In e es /\ back_edge g e.
