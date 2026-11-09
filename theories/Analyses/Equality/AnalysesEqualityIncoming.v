(** * Prepared incoming argument rows

    Incoming edges are grouped once and their argument positions are indexed once.
    For example, two parameters read the same ordered incoming-edge buckets.
    Builds on: BaseIndex, BaseMap, ProgramCfg and ProgramSsa. *)

From Stdlib Require Import List Bool Arith Lia NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module NumberingIncoming.

(** Argument indices contain every position of a row without repeated list indexing. *)
Fixpoint arguments_from_c {V} (i : nat) (xs : list V) : Cost.t (Map.t nat V) :=
  match xs with
  | [] => Map.empty_c
  | x :: rest =>
    Cost.step ;;
    let* tail := arguments_from_c (S i) rest in
    Map.set_c nat_encoding i x tail
  end.

Definition arguments_from {V} i (xs : list V) := Cost.value (arguments_from_c i xs).

(** The indexed row equation exposes the map operations used by the preparation. *)
Theorem arguments_from_equation {V} i (xs : list V) :
  arguments_from i xs =
  match xs with
  | [] => Map.empty
  | x :: rest => Map.set nat_encoding i x (arguments_from (S i) rest)
  end.
Proof.
  destruct xs; reflexivity.
Qed.

(** Row preparation preserves the map representation invariant. *)
Theorem arguments_from_wf {V} i (xs : list V) :
  Map.wf nat_encoding (arguments_from i xs).
Proof.
  revert i; induction xs as [|x rest IH]; intro i; rewrite arguments_from_equation.
  - apply Map.wf_empty.
  - apply Map.wf_set, IH.
Qed.

(** Indexed argument lookup agrees with the original position in the row. *)
Theorem arguments_from_get {V} (xs : list V) i j :
  Map.get nat_encoding (i + j) (arguments_from i xs) = nth_error xs j.
Proof.
  revert i j; induction xs as [|x rest IH]; intros i [|j];
    rewrite arguments_from_equation; cbn [nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same, arguments_from_wf.
  - rewrite (Map.get_set_other nat_encoding nat_encoding_laws)
      by (try apply arguments_from_wf; lia).
    replace (i + S j) with (S i + j) by lia; apply IH.
Qed.

(** Row indices start at zero. *)
Definition argument_index {V} (xs : list V) := arguments_from 0 xs.

(** A zero-based row index has the original nth_error observation. *)
Theorem argument_index_get {V} (xs : list V) i :
  Map.get nat_encoding i (argument_index xs) = nth_error xs i.
Proof.
  exact (arguments_from_get xs 0 i).
Qed.

(** A row retains its target block and its prepared positional map. *)
Definition row N V := (N * Map.t nat V)%type.

(** CFG edge enumeration charges every outgoing callback and copied edge occurrence. *)
Definition edges_c {N E} (c : Cfg.t N E) : Cost.t (list E) :=
  fold_right_c (fun n tail =>
    Cost.step ;;
    let* outgoing := Graph.out_c (Cfg.graph c) n in
    app_c outgoing tail) [] (Graph.nodes (Cfg.graph c)).

(** Costed enumeration keeps the exact public CFG edge order and multiplicities. *)
Theorem edges_value {N E} (c : Cfg.t N E) : Cost.value (edges_c c) = Cfg.edges c.
Proof.
  unfold edges_c; rewrite value_fold_right_c.
  change (fold_right (fun n tail =>
    Cost.value (Cost.step ;;
      (let* outgoing := Graph.out_c (Cfg.graph c) n in app_c outgoing tail))) []
    (Graph.nodes (Cfg.graph c)) = Cfg.edges c).
  change (fold_right (fun n tail =>
    Cost.value (Cost.step ;;
      (let* outgoing := Graph.out_c (Cfg.graph c) n in app_c outgoing tail))) []
    (Graph.nodes (Cfg.graph c)) =
    flat_map (Graph.out (Cfg.graph c)) (Graph.nodes (Cfg.graph c))).
  induction (Graph.nodes (Cfg.graph c)) as [|n rest IH]; [reflexivity|].
  cbn [fold_right flat_map]; autorewrite with galois_cost.
  fold (Graph.out (Cfg.graph c) n); now rewrite IH.
Qed.

(** Each edge row calls the target and argument dictionaries once. *)
Definition edge_row_c {N E V K G} (p : Ssa.t N E V K G) e : Cost.t (row N V) :=
  Cost.step ;;
  let* target := Graph.target_c (Cfg.graph (Ssa.cfg p)) e in
  Cost.step ;;
  let* args := Ssa.args_c p e in
  Cost.map (fun indexed => (target, indexed)) (arguments_from_c 0 args).

(** Prepared rows retain the edge's target and all original argument positions. *)
Theorem edge_row_value {N E V K G} (p : Ssa.t N E V K G) e :
  Cost.value (edge_row_c p e) =
    (Graph.target (Cfg.graph (Ssa.cfg p)) e, argument_index (Ssa.args p e)).
Proof.
  reflexivity.
Qed.

(** The incoming index groups all prepared rows in edge occurrence order. *)
Definition prepare_c {N E V K G} (p : Ssa.t N E V K G) :
    Cost.t (Index.t N (row N V)) :=
  let* es := edges_c (Ssa.cfg p) in
  let* rows := map_c (fun e => Cost.step ;; edge_row_c p e) es in
  Index.group_by_c (Cfg.node_enc (Ssa.cfg p)) (fun r => Cost.ret (fst r)) rows.

Definition prepare {N E V K G} (p : Ssa.t N E V K G) := Cost.value (prepare_c p).

(** Preparation agrees with stable grouping of each source edge's indexed arguments. *)
Theorem prepare_equation {N E V K G} (p : Ssa.t N E V K G) :
  prepare p = Index.group_by (Cfg.node_enc (Ssa.cfg p)) fst
    (map (fun e => (Graph.target (Cfg.graph (Ssa.cfg p)) e,
      argument_index (Ssa.args p e))) (Cfg.edges (Ssa.cfg p))).
Proof.
  unfold prepare, prepare_c; rewrite Cost.value_bind, edges_value.
  rewrite Cost.value_bind, value_map_c, Index.group_by_c_value.
  reflexivity.
Qed.

(** Every listed incoming edge occurs in its target bucket, including duplicate occurrences. *)
Theorem incoming_member {N E V K G} (p : Ssa.t N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg p))) e :
  In e (Cfg.edges (Ssa.cfg p)) ->
  In (Graph.target (Cfg.graph (Ssa.cfg p)) e, argument_index (Ssa.args p e))
    (Index.find (Cfg.node_enc (Ssa.cfg p)) (Graph.target (Cfg.graph (Ssa.cfg p)) e)
      (prepare p)).
Proof.
  intro He; rewrite prepare_equation, Index.find_group_by, filter_In.
  split.
  - apply in_map_iff; exists e; split; [reflexivity|exact He].
  - apply eqb_refl.
Qed.

(** Reading one parameter traverses its incoming bucket and performs indexed row lookups. *)
Fixpoint read_rows_c {N V} (rs : list (row N V)) (i : nat) : Cost.t (option (list V)) :=
  match rs with
  | [] => Cost.ret (Some [])
  | (_, r) :: rest =>
    Cost.step ;;
    let* head := Map.get_c nat_encoding i r in
    let* tail := read_rows_c rest i in
    Cost.ret (match head, tail with
              | Some x, Some xs => Some (x :: xs)
              | _, _ => None
              end)
  end.

Definition read_rows {N V} (rs : list (row N V)) i := Cost.value (read_rows_c rs i).

(** Missing argument positions reject a parameter signature without inventing a sentinel. *)
Theorem read_rows_equation {N V} (rs : list (row N V)) i :
  read_rows rs i =
  match rs with
  | [] => Some []
  | (_, r) :: rest =>
    match Map.get nat_encoding i r, read_rows rest i with
    | Some x, Some xs => Some (x :: xs)
    | _, _ => None
    end
  end.
Proof.
  destruct rs as [|[b r] rest]; reflexivity.
Qed.

(** Equal mapped columns give related arguments on the same incoming edge occurrence. *)
Theorem read_rows_pair {N V W} (f : V -> W) (rs : list (row N V)) i j xs ys b r :
  read_rows rs i = Some xs -> read_rows rs j = Some ys ->
  map f xs = map f ys -> In (b, r) rs ->
  exists x y, Map.get nat_encoding i r = Some x /\
    Map.get nat_encoding j r = Some y /\ In x xs /\ In y ys /\ f x = f y.
Proof.
  revert xs ys; induction rs as [|[a head] rest IH];
    intros xs ys Hx Hy Heq Hr; [contradiction|].
  rewrite read_rows_equation in Hx, Hy.
  destruct (Map.get nat_encoding i head) as [x|] eqn:Hxi; [|discriminate].
  destruct (Map.get nat_encoding j head) as [y|] eqn:Hyj; [|discriminate].
  destruct (read_rows rest i) as [xs'|] eqn:Hxs; [|discriminate].
  destruct (read_rows rest j) as [ys'|] eqn:Hys; [|discriminate].
  injection Hx as <-; injection Hy as <-; cbn [map] in Heq.
  injection Heq as Hhead Htail.
  destruct Hr as [Hrow|Hr].
  - injection Hrow as <- <-; exists x, y; repeat split; try assumption; now left.
  - destruct (IH _ _ eq_refl eq_refl Htail Hr) as [u [v [Hu [Hv [Hin [Hjn Huv]]]]]].
    exists u, v; repeat split; try assumption; now right.
Qed.

End NumberingIncoming.
