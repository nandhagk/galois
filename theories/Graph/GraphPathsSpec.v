(** * Weighted paths and forwarding outcomes

    Path outcomes separate optimal routes, cycles and forwarding landings.
    For example, a forwarding self-loop returns cycle data whose validity is a separate property.
    Builds on: GraphPrepared and GraphSearchSpec. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec.
Import List.ListNotations Cost.Notations.

Module Weight.

Record t (W : Type) := Make {
  zero : W;
  plus_c : W -> W -> Cost.t W;
  better_c : W -> W -> Cost.t bool
}.
Arguments Make {W}.
Arguments zero {W}.
Arguments plus_c {W}.
Arguments better_c {W}.

Definition plus {W} (w : t W) a b := Cost.value (plus_c w a b).
Definition better {W} (w : t W) a b := Cost.value (better_c w a b).

(** Pure weight primitives charge one tick per binary operation. *)
Definition of_pure {W} zero (plus : W -> W -> W) (better : W -> W -> bool) :=
  Make zero (fun a => Cost.lift (fun _ => 1%N) (plus a))
    (fun a => Cost.lift (fun _ => 1%N) (better a)).

(** Weights form a monoid ordered by a monotone strict weak preference. *)
Record laws {W} (w : t W) : Prop := {
  associative : forall a b c, plus w (plus w a b) c = plus w a (plus w b c);
  identity_left : forall a, plus w (zero w) a = a;
  identity_right : forall a, plus w a (zero w) = a;
  irreflexive : forall a, better w a a = false;
  transitive : forall a b c, better w a b = true -> better w b c = true ->
    better w a c = true;
  incomparable_transitive : forall a b c,
    better w a b = false -> better w b a = false ->
    better w b c = false -> better w c b = false ->
    better w a c = false /\ better w c a = false;
  monotone_left : forall a b c, better w a b = true ->
    better w (plus w c a) (plus w c b) = true;
  monotone_right : forall a b c, better w a b = true ->
    better w (plus w a c) (plus w b c) = true
}.

Fixpoint path_weight_c {W E} (w : t W) (edge_weight_c : E -> Cost.t W) es : Cost.t W :=
  match es with
  | [] => Cost.ret (zero w)
  | e :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* a := edge_weight_c e in
    let* b := path_weight_c w edge_weight_c rest in
    Cost.step ;; plus_c w a b
  end.

Definition path_weight {W E} (w : t W) (f : E -> Cost.t W) es :=
  Cost.value (path_weight_c w f es).

(** Path weighting folds edge values in traversal order and retains the declared zero. *)
Theorem path_weight_equation {W E} (w : t W) (f : E -> Cost.t W) es :
  path_weight w f es =
    match es with
    | [] => zero w
    | e :: rest => plus w (Cost.value (f e)) (path_weight w f rest)
    end.
Proof.
  destruct es; reflexivity.
Qed.

End Weight.

Module Dag.

Inductive outcome (W E : Type) :=
  | Optimal (best : Map.t positive W) (via : Map.t positive E)
  | Cyclic (edge : E).
Arguments Optimal {W E}.
Arguments Cyclic {W E}.

(** A cycle witness returns from the reported edge's target to its source. *)
Definition cyclic_witness {V E} (p : Prepared.t V E) e :=
  In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)) /\
  In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
  exists es, path (Prepared.graph p) (Graph.target (Prepared.graph p) e) es
    (Graph.source (Prepared.graph p) e).

(** Optimal values have attaining entry paths and are no worse than every competing path. *)
Record optimal {V E W} (p : Prepared.t V E) (w : Weight.t W)
    (weight_c : E -> Cost.t W) best via : Prop := {
  best_wf : Map.wf positive_encoding best;
  via_wf : Map.wf positive_encoding via;
  best_domain : forall n i, Prepared.id_of p n = Some i ->
    (reachable (Prepared.graph p) n <->
      exists value, Map.get positive_encoding i best = Some value);
  best_no_extra : forall i value, Map.get positive_encoding i best = Some value ->
    exists n, Prepared.id_of p n = Some i /\ reachable (Prepared.graph p) n;
  best_attained : forall n i value, Prepared.id_of p n = Some i ->
    Map.get positive_encoding i best = Some value ->
    exists s es, In s (Graph.entries (Prepared.graph p)) /\
      path (Prepared.graph p) s es n /\ Weight.path_weight w weight_c es = value;
  best_preferred : forall n i value s es, Prepared.id_of p n = Some i ->
    Map.get positive_encoding i best = Some value ->
    In s (Graph.entries (Prepared.graph p)) -> path (Prepared.graph p) s es n ->
    Weight.better w (Weight.path_weight w weight_c es) value = false;
  via_valid : forall i e, Map.get positive_encoding i via = Some e ->
    exists n j, Prepared.id_of p n = Some i /\
      Graph.target (Prepared.graph p) e = n /\
      Prepared.id_of p (Graph.source (Prepared.graph p) e) = Some j /\
      In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
      exists a b, Map.get positive_encoding j best = Some a /\
        Map.get positive_encoding i best = Some b /\
        Weight.plus w a (Cost.value (weight_c e)) = b;
  via_complete : forall n i, Prepared.id_of p n = Some i ->
    reachable (Prepared.graph p) n -> ~ In n (Graph.entries (Prepared.graph p)) ->
    exists e, Map.get positive_encoding i via = Some e
}.

(** Outcome semantics keep cyclic evidence separate from computational outcome data. *)
Definition spec {V E W} (p : Prepared.t V E) (w : Weight.t W) f (r : outcome W E) :=
  match r with
  | Optimal best via => acyclic (Prepared.graph p) /\ optimal p w f best via
  | Cyclic e => cyclic_witness p e
  end.

End Dag.

Module Chain.

Inductive outcome (E : Type) :=
  | Landing (id : positive)
  | ForwardingCycle (prefix cycle : list E).
Arguments Landing {E}.
Arguments ForwardingCycle {E}.

(** Forwarding follows a unique outgoing edge only at a marked node. *)
Definition forward_step {V E} (g : Graph.t V E) (fwd : V -> bool) v :=
  if fwd v then
    match Graph.out g v with
    | [e] => Some e
    | _ => None
    end
  else None.

Inductive walk {V E} (g : Graph.t V E) fwd : V -> list E -> V -> Prop :=
  | walk_nil : forall v, walk g fwd v [] v
  | walk_cons : forall v e es z, forward_step g fwd v = Some e ->
      walk g fwd (Graph.target g e) es z -> walk g fwd v (e :: es) z.

(** A landing terminates forwarding and a cycle outcome supplies a reachable nonempty cycle. *)
Definition spec {V E} (p : Prepared.t V E) fwd start (r : outcome E) :=
  match r with
  | Landing i =>
    exists v es, Prepared.id_of p v = Some i /\
      walk (Prepared.graph p) fwd start es v /\
      forward_step (Prepared.graph p) fwd v = None
  | ForwardingCycle prefix cycle =>
    exists v, walk (Prepared.graph p) fwd start prefix v /\
      cycle <> [] /\ walk (Prepared.graph p) fwd v cycle v
  end.

End Chain.
