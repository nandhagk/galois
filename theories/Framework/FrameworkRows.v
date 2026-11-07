(** * Prepared fixed-read rows

    A prepared row separates its static reads from its charged value callback.
    For example, a constant row has an empty read list.
    Builds on: FixpointQuery and FixpointAnalysis. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem.
Import List.ListNotations Cost.Notations.

Module Rows.

(** A row reads its prepared keys in order and then calls its evaluator once. *)
Record t (X A : Type) := Make {
  target : X;
  reads : list X;
  eval_c : list A -> Cost.t A
}.
Arguments Make {X A}.
Arguments target {X A}.
Arguments reads {X A}.
Arguments eval_c {X A}.

Definition query_c {X A} (r : t X A) :=
  ask_all_c (reads r) (fun fs =>
    Cost.step ;; Cost.map (@Query.Ret X A) (eval_c r fs)).

Definition query {X A} (r : t X A) := Cost.value (query_c r).

(** Prepared rows read exactly their static list and never emit side contributions. *)
Theorem query_spec {X A} (r : t X A) s :
  Query.reads (query r) s = reads r /\
  Query.eval (query r) s = Cost.value (eval_c r (map s (reads r))) /\
  Query.sides (query r) s = [].
Proof.
  unfold query, query_c; fold (ask_all (reads r)
    (fun fs => Cost.step ;; Cost.map (@Query.Ret X A) (eval_c r fs))).
  destruct (ask_all_spec s (reads r)
    (fun fs => Cost.step ;; Cost.map (@Query.Ret X A) (eval_c r fs)))
    as [Hr [Hv Hs]].
  autorewrite with galois_cost in Hr, Hv, Hs.
  change (Query.reads (query r) s = reads r ++ []) in Hr.
  rewrite app_nil_r in Hr; repeat split; assumption.
Qed.

(** A computational row reader constructs a system without law evidence. *)
Definition system {X C A} cs (get_c : C -> Cost.t (t X A)) :=
  System.Make cs
    (fun c => Cost.step ;; Cost.map target (get_c c))
    (fun c => Cost.step ;; let* r := get_c c in query_c r).

Definition static {X C A} cs (get_c : C -> Cost.t (t X A)) :
    System.static (system cs get_c) :=
  System.Static (fun c => Cost.step ;; Cost.map reads (get_c c))
    (fun _ => Cost.ret []).

(** The fixed-read summary covers all assignments even when its evaluator is unlawful. *)
Theorem static_laws {X C A} cs (get_c : C -> Cost.t (t X A)) :
  System.static_laws (static cs get_c).
Proof.
  constructor; intros c s.
  - change (incl (Query.reads (query (Cost.value (get_c c))) s)
      (reads (Cost.value (get_c c)))).
    rewrite (proj1 (query_spec _ _)); apply incl_refl.
  - change (incl (map fst (Query.sides (query (Cost.value (get_c c))) s)) []).
    rewrite (proj2 (proj2 (query_spec _ _))); apply incl_refl.
Qed.

End Rows.
