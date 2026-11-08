(** * Reducibility checks on actual search events

    One search visitor checks dominance for every actual Back occurrence.
    For example, the two-entry cycle fails because neither cycle entry dominates the other.
    Builds on: GraphSearch, GraphDomSpec and GraphCheckDom. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphDomSpec GraphCheckDom.
Import List.ListNotations Cost.Notations.

Module Reducibility.

(** Dominance queries retain all four optional interval lookups and return false on missing ranks. *)
Definition dominates_c (t : Dom.tree) d n :=
  let* a := Map.get_c positive_encoding d (Dom.tin t) in
  let* b := Map.get_c positive_encoding n (Dom.tin t) in
  let* c := Map.get_c positive_encoding n (Dom.tout t) in
  let* e := Map.get_c positive_encoding d (Dom.tout t) in
  Cost.ret
    (match a, b, c, e with
    | Some a, Some b, Some c, Some e => (Pos.leb a b && Pos.leb c e)%bool
    | _, _, _, _ => false
    end).

Definition dominates t d n := Cost.value (dominates_c t d n).

(** The interval query exposes missing observations without substituting a rank. *)
Theorem dominates_equation t d n :
  dominates t d n =
  match Map.get positive_encoding d (Dom.tin t),
      Map.get positive_encoding n (Dom.tin t),
      Map.get positive_encoding n (Dom.tout t),
      Map.get positive_encoding d (Dom.tout t) with
  | Some a, Some b, Some c, Some e => (Pos.leb a b && Pos.leb c e)%bool
  | _, _, _, _ => false
  end.
Proof.
  unfold dominates, dominates_c. rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** Exact dominator numbering makes the charged interval query reflect semantic dominance. *)
Theorem dominates_correct {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> Dom.exact p t ->
  reachable (Prepared.graph p) n -> reachable (Prepared.graph p) d ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (dominates t u v = true <-> GraphDomSpec.dominates (Prepared.graph p) d n).
Proof.
  intros Hready Htree Hn Hd Hv Hu.
  destruct (Dom.numbering p t Htree n d v u Hn Hd Hv Hu)
    as [a [b [c [e [Ha [Hb [Hc [He Hnumber]]]]]]]].
  rewrite dominates_equation, Ha, Hb, Hc, He, andb_true_iff, !Pos.leb_le, Hnumber.
  exact (DomCheck.ancestry_spec p t n d v u Hready Htree Hn Hv Hu).
Qed.

Definition edge_c t u v k state :=
  match k with
  | Search.Back =>
    let* back := dominates_c t v u in Cost.ret (state && back)%bool
  | _ => Cost.ret state
  end.

Definition visitor {E} t : Visitor.t E bool :=
  Visitor.Make (fun _ _ state => Cost.ret state)
    (fun _ => edge_c t) (fun _ _ state => Cost.ret state).

(** Event dispatch tests only Back occurrences and leaves all other notifications unchanged. *)
Theorem visitor_equation {E} t (ev : Search.event E) state :
  Visitor.apply (visitor t) ev state =
  match ev with
  | Search.Edge _ u v Search.Back => (state && dominates t v u)%bool
  | _ => state
  end.
Proof.
  destruct ev as [v via|e u v [| | |]|v parent]; reflexivity.
Qed.

(** Reducibility computation runs the shared engine once with its Boolean checking visitor. *)
Definition test_c {V E} (p : Prepared.t V E) t :=
  let* answer := SearchRun.run_c p (visitor t) (Scope.Make FinSet.empty None)
    (Prepared.entry_ids p) true in
  Cost.ret (snd answer).

Definition test {V E} (p : Prepared.t V E) t := Cost.value (test_c p t).

Definition passes {E} t (ev : Search.event E) :=
  match ev with
  | Search.Edge _ u v Search.Back => dominates t v u
  | _ => true
  end.

Local Lemma visitor_passes {E} t (ev : Search.event E) state :
  Visitor.apply (visitor t) ev state = (state && passes t ev)%bool.
Proof.
  rewrite visitor_equation.
  destruct ev as [v via|e u v [| | |]|v parent]; cbn [passes];
    now rewrite ?andb_true_r.
Qed.

Local Lemma events_pass {E} t (evs : list (Search.event E)) state :
  SearchRun.apply_events (visitor t) evs state = true <->
    state = true /\ Forall (fun ev => passes t ev = true) evs.
Proof.
  revert state. induction evs as [|ev rest IH]; intro state.
  - rewrite SearchRun.apply_events_nil. split; [intro Hstate; split|intros [Hstate _]];
      auto using Forall_nil.
  - rewrite SearchRun.apply_events_cons, IH, visitor_passes, andb_true_iff, Forall_cons_iff.
    tauto.
Qed.

(** Acceptance is exactly successful dominance testing of every actual Back event in the one run. *)
Theorem test_events {V E} (p : Prepared.t V E) t :
  test p t = true <->
  forall e u v,
    In (Search.Edge e u v Search.Back)
      (SearchRun.events p (Scope.Make FinSet.empty None) (Prepared.entry_ids p)) ->
    dominates t v u = true.
Proof.
  unfold test, test_c. rewrite Cost.value_bind, SearchRun.run_events.
  rewrite Cost.value_ret. cbn [snd].
  rewrite events_pass, Forall_forall. split.
  - intros [_ Hall] e u v Hin. exact (Hall (Search.Edge e u v Search.Back) Hin).
  - intro Hback. split; [reflexivity|].
    intros ev Hin. destruct ev as [v via|e u v [| | |]|v parent];
      try reflexivity.
    exact (Hback e u v Hin).
Qed.

End Reducibility.
