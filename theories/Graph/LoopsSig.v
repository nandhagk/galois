(** * Natural loop forest signatures

    Natural loops group back-edge sources under dominating headers.
    For example, a two-vertex cycle has its DFS entry as its natural loop header.
    Builds on: DFS trace derivations, graph dominance and preparation measures. *)

From Stdlib Require Import PArith NArith List Bool.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig DomSig.
Import List.ListNotations.

(** Back edges target a reachable dominator of their source. *)
Definition natural_header (g : digraph) (r h : positive) : Prop :=
  exists latch, reach g [r] latch /\ edge g latch h /\ dominates g r h latch.

(** A natural loop contains its header and paths to latches that avoid the header. *)
Definition natural_loop (g : digraph) (r h v : positive) : Prop :=
  natural_header g r h /\
  (v = h \/ exists latch vs, reach g [r] latch /\ edge g latch h /\
    dominates g r h latch /\ path g v vs latch /\ forall x, In x vs -> x <> h).

(** Strict containment compares the complete semantic loop bodies. *)
Definition loop_inside (g : digraph) (r inner outer : positive) : Prop :=
  inner <> outer /\ natural_header g r inner /\ natural_header g r outer /\
  (forall v, natural_loop g r inner v -> natural_loop g r outer v).

(** An immediate outer loop has no intervening strict containing loop. *)
Definition immediate_outer (g : digraph) (r inner outer : positive) : Prop :=
  loop_inside g r inner outer /\
  ~ exists middle, loop_inside g r inner middle /\ loop_inside g r middle outer.

(** The innermost header contains the vertex without a smaller containing loop. *)
Definition innermost_header (g : digraph) (r v h : positive) : Prop :=
  natural_loop g r h v /\
  ~ exists inner, natural_loop g r inner v /\ loop_inside g r inner h.

(** Retreating edges are back-edge events in a depth-first traversal from the root. *)
Definition retreating_edge (g : digraph) (r u v : positive) : Prop :=
  exists es final, dfs_roots g [] [r] es final /\ In (Edge Back u v) es.

(** Reducibility requires every retreating edge to target a dominator. *)
Definition reducible (g : digraph) (r : positive) : Prop :=
  forall u v, retreating_edge g r u v -> dominates g r v u.

Definition loop_body (l : loops) (h : positive) : list positive :=
  match l with
  | Loops _ _ rows =>
    match trie_get h rows with
    | Some vs => vs
    | None => []
    end
  end.
TimeFun loop_body.

Fixpoint loop_parent_depth (fuel : nat) (parents : ptrie positive) (h : positive) : nat :=
  match fuel with
  | 0 => 0
  | S remaining =>
    match trie_get h parents with
    | None => 0
    | Some outer => S (loop_parent_depth remaining parents outer)
    end
  end.
TimeFun loop_parent_depth.

Definition loop_depth (g : prepared) (l : loops) : nat :=
  match l with
  | Loops _ parents rows =>
    fold_right (fun h depth =>
      match trie_get h rows with
      | None => depth
      | Some _ => graph_max (S (loop_parent_depth (length (nodes g)) parents h)) depth
      end) 0 (nodes g)
  end.
TimeFun loop_depth.

Module Type LOOPS_OPS.
  Parameter forest : prepared -> domtree -> loops.
  Parameter reducible_b : prepared -> domtree -> bool.
End LOOPS_OPS.

Module Type LOOPS_LAWS (Import L : LOOPS_OPS).
  (** Body bindings exist precisely at targets of dominance back edges. *)
  Parameter headers_spec : forall g t r h,
    (exists vs, trie_get h (body (forest g t)) = Some vs) <-> natural_header (base g) r h.
  (** Each header row is the semantic natural loop of that header. *)
  Parameter body_spec : forall g t r h v,
    In v (loop_body (forest g t) h) <-> natural_loop (base g) r h v.
  (** Loop bodies contain no repeated vertex. *)
  Parameter body_unique : forall g t h, NoDup (loop_body (forest g t) h).
  (** Header lookup chooses the innermost loop containing a vertex. *)
  Parameter header_spec : forall g t r v h,
    trie_get v (header (forest g t)) = Some h <-> innermost_header (base g) r v h.
  (** Parent lookup gives immediate strict containment of natural loops. *)
  Parameter parent_spec : forall g t r inner outer,
    trie_get inner (parent (forest g t)) = Some outer <->
    immediate_outer (base g) r inner outer.
  (** The Boolean test reflects the requested retreating-edge condition. *)
  Parameter reducible_b_spec : forall g t r,
    reflect (reducible (base g) r) (reducible_b g t).
End LOOPS_LAWS.

Module Type LOOPS := LOOPS_OPS <+ LOOPS_LAWS.

Module Type LOOPS_TIME (Import L : LOOPS).
  Parameter T_forest : prepared -> domtree -> N.
  Parameter T_reducible_b : prepared -> domtree -> N.
  Parameter c_loops : N.
  (** Forest construction charges graph occurrences at every loop nesting depth. *)
  Parameter T_forest_le : forall g t,
    (T_forest g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Reducibility checking has the published nesting-sensitive graph bound. *)
  Parameter T_reducible_b_le : forall g t,
    (T_reducible_b g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Forest construction has the published nesting-sensitive bit-cost bound. *)
  Parameter forest_bigO : bigO (fun _ : prepared * domtree => True)
    (fun '(g, t) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t) => T_forest g t).
  (** Reducibility checking has the published nesting-sensitive bit-cost bound. *)
  Parameter reducible_b_bigO : bigO (fun _ : prepared * domtree => True)
    (fun '(g, t) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t) => T_reducible_b g t).
End LOOPS_TIME.

Module Type LOOPS_T := LOOPS <+ LOOPS_TIME.
