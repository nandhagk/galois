(** * Weak topological order signatures

    A checked order covers the reachable vertices and sends backward edges to enclosing heads.
    For example, a self-loop requires its vertex to be a loop head.
    Builds on: graph semantics, preparation measures and Argent time interfaces. *)

From Stdlib Require Import PArith NArith List Arith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig.
Import List.ListNotations.

Fixpoint wto_order (w : wto) : list positive :=
  match w with
  | WNil => []
  | WVertex v rest => v :: wto_order rest
  | WLoop h inside rest => h :: (wto_order inside ++ wto_order rest)
  end.
TimeFun wto_order.

Fixpoint wto_heads (w : wto) : list positive :=
  match w with
  | WNil => []
  | WVertex _ rest => wto_heads rest
  | WLoop h inside rest => h :: (wto_heads inside ++ wto_heads rest)
  end.
TimeFun wto_heads.

Fixpoint wto_depth (w : wto) : nat :=
  match w with
  | WNil => 0
  | WVertex _ rest => wto_depth rest
  | WLoop _ inside rest => graph_max (S (wto_depth inside)) (wto_depth rest)
  end.
TimeFun wto_depth.

(** A vertex lies in the loop headed by [h], including the head itself. *)
Inductive wto_encloses (h v : positive) : wto -> Prop :=
  | encloses_here : forall inside rest,
      (v = h \/ In v (wto_order inside)) -> wto_encloses h v (WLoop h inside rest)
  | encloses_vertex : forall u rest,
      wto_encloses h v rest -> wto_encloses h v (WVertex u rest)
  | encloses_body : forall u inside rest,
      wto_encloses h v inside -> wto_encloses h v (WLoop u inside rest)
  | encloses_rest : forall u inside rest,
      wto_encloses h v rest -> wto_encloses h v (WLoop u inside rest).

(** List order compares positions rather than vertex identifiers. *)
Definition graph_before (vs : list positive) (u v : positive) : Prop :=
  exists prefix middle suffix, vs = prefix ++ u :: middle ++ v :: suffix.

(** Valid orders have unique exact coverage and forward or enclosing-head edges. *)
Definition is_wto (g : prepared) (roots : list positive) (w : wto) : Prop :=
  NoDup (wto_order w) /\
  (forall v, In v (wto_order w) <-> reach (base g) roots v) /\
  forall u v, edge (base g) u v -> reach (base g) roots u ->
    graph_before (wto_order w) u v \/ wto_encloses v u w.

Module Type WTO_OPS.
  Parameter build : prepared -> list positive -> wto.
  Parameter check : prepared -> list positive -> wto -> bool.
  Parameter heads : wto -> list positive.
  Parameter ranks : wto -> ptrie positive.
End WTO_OPS.

Module Type WTO_LAWS (Import W : WTO_OPS).
  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Parameter check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  (** Heads are the structural loop heads in traversal order. *)
  Parameter heads_spec : forall w, heads w = wto_heads w.
  (** Ranks number the unique linear order starting at one. *)
  Parameter ranks_spec : forall w, NoDup (wto_order w) -> forall v i,
    nth_error (wto_order w) i = Some v ->
    trie_get v (ranks w) = Some (Pos.of_succ_nat i).
  (** Vertices outside the linear order have no rank. *)
  Parameter ranks_absent : forall w v,
    ~ In v (wto_order w) -> trie_get v (ranks w) = None.
  (** Every reachable cycle contains a structural loop head. *)
  Parameter check_cuts : forall g roots w,
    check g roots w = true -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (heads w).
  (** Edges increase rank unless their target is a backward loop head. *)
  Parameter ranks_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
End WTO_LAWS.

Module Type WTO := WTO_OPS <+ WTO_LAWS.

Module Type WTO_TIME (Import W : WTO).
  Parameter T_build : prepared -> list positive -> N.
  Parameter T_check : prepared -> list positive -> wto -> N.
  Parameter T_heads : wto -> N.
  Parameter T_ranks : wto -> N.
  Parameter c_wto : N.
  (** Checking has the published linear graph bit-cost bound, including rejection. *)
  Parameter T_check_le : forall g roots w,
    (T_check g roots w <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Building charges each graph occurrence once per nesting level. *)
  Parameter T_build_le : forall g roots,
    (T_build g roots <= c_wto * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (wto_depth (build g roots) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Head projection charges the supplied order. *)
  Parameter T_heads_le : forall w,
    (T_heads w <= c_wto * N.of_nat (length (wto_order w) + 1))%N.
  (** Ranking charges emitted keys and binary positions. *)
  Parameter T_ranks_le : forall w,
    (T_ranks w <= c_wto * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  (** Checking is linear in graph size and identifier width. *)
  Parameter check_bigO : bigO (fun _ : prepared * list positive * wto => True)
    (fun '(g, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, roots, w) => T_check g roots w).
  (** Building has the published nesting-sensitive bound. *)
  Parameter build_bigO : bigO (fun _ : prepared * list positive => True)
    (fun '(g, roots) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (wto_depth (build g roots) + 1) * (graph_width (base g) + 1)))
    (fun '(g, roots) => T_build g roots).
End WTO_TIME.

Module Type WTO_T := WTO <+ WTO_TIME.
