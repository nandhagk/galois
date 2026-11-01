(** * Observation expiration-map validation

    Structural comparison follows the first trie and stops at the first failed subcomparison.
    For example, a failed left child suppresses its parent value and right child.
    Builds on: FixpointAuditObserveCompare and CollectionsTrie. *)

From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditWorklistCallbacks
  FixpointAuditObserveCompare.
Import List.ListNotations.

Inductive fx_expire_check_event (X : Type) : Type :=
  | FxExpireCheckCase
  | FxExpireCheckCompare (events : list (fx_observe_compare_event X)).

Arguments FxExpireCheckCase {X}.

Arguments FxExpireCheckCompare {X} _.

(** The relation compares actual stored lists, using [] for an absent opposite binding. *)

Definition fx_expire_check_value {X} (EX : encoding X) (entry : X * list X)
    (opposite : option (X * list X)) : bool * list (fx_expire_check_event X) :=
  let ys :=
    match opposite with
    | Some (_, found) => found
    | None => []
    end in
  let '(out, events) := fx_observe_seteq EX (snd entry) ys in
  (out, [FxExpireCheckCompare events]).

(** Each trie branch follows the source's selective nested matches. *)

Fixpoint fx_expire_check_ne {X} (EX : encoding X) (first : Trie.ne (X * list X))
    (second : Trie.t (X * list X)) : bool * list (fx_expire_check_event X) :=
  match first with
  | Trie.N001 r =>
      let '(out, events) := fx_expire_check_ne EX r (Trie.right second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N010 v =>
      let '(out, events) := fx_expire_check_value EX v (Trie.value second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N011 v r =>
      let '(test, events) := fx_expire_check_value EX v (Trie.value second) in
      if test then
        let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N100 l =>
      let '(out, events) := fx_expire_check_ne EX l (Trie.left second) in
      (out, FxExpireCheckCase :: events)
  | Trie.N101 l r =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N110 l v =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(out, later) := fx_expire_check_value EX v (Trie.value second) in
        (out, FxExpireCheckCase :: events ++ later)
      else (false, FxExpireCheckCase :: events)
  | Trie.N111 l v r =>
      let '(test, events) := fx_expire_check_ne EX l (Trie.left second) in
      if test then
        let '(middle, mid_events) := fx_expire_check_value EX v (Trie.value second) in
        if middle then
          let '(out, later) := fx_expire_check_ne EX r (Trie.right second) in
          (out, FxExpireCheckCase :: events ++ mid_events ++ later)
        else (false, FxExpireCheckCase :: events ++ mid_events)
      else (false, FxExpireCheckCase :: events)
  end.

(** A directed map comparison processes its first trie's actual shape. *)

Definition fx_expire_check_directed {X} (EX : encoding X) (first second : Map.t X (list X)) :
    bool * list (fx_expire_check_event X) :=
  match first with
  | Trie.Empty => (true, [FxExpireCheckCase])
  | Trie.Nodes n =>
      let '(out, events) := fx_expire_check_ne EX n second in
      (out, FxExpireCheckCase :: events)
  end.

(** Both directed map comparisons execute because their enclosing andb is strict. *)

Definition fx_expire_check {X} (EX : encoding X) (left_map right_map : Map.t X (list X)) :
    bool * list (fx_expire_check_event X) :=
  let '(a, first) := fx_expire_check_directed EX left_map right_map in
  let '(b, second) := fx_expire_check_directed EX right_map left_map in
  (a && b, FxExpireCheckCase :: first ++ second).

(** The selected trace counts trie frames and every captured set comparison. *)

Definition fx_expire_check_work {X} (events : list (fx_expire_check_event X)) : nat :=
  fold_right (fun e n => n +
    match e with
    | FxExpireCheckCase => 1
    | FxExpireCheckCompare body => fx_observe_compare_work body
    end) 0 events.

(** This upper bound covers both children and values, including branches skipped on failure. *)

Fixpoint fx_expire_check_ne_budget {X} (EX : encoding X) (first : Trie.ne (X * list X))
    (second : Trie.t (X * list X)) : nat :=
  let vbudget := fun v => fx_observe_seteq_budget EX (snd v)
    (
      match Trie.value second with
      | Some (_, ys) => ys
      | None => []
      end) in
  match first with
  | Trie.N001 r => 1 + fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N010 v => 1 + vbudget v
  | Trie.N011 v r => 1 + vbudget v + fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N100 l => 1 + fx_expire_check_ne_budget EX l (Trie.left second)
  | Trie.N101 l r => 1 + fx_expire_check_ne_budget EX l (Trie.left second) +
      fx_expire_check_ne_budget EX r (Trie.right second)
  | Trie.N110 l v => 1 + fx_expire_check_ne_budget EX l (Trie.left second) + vbudget v
  | Trie.N111 l v r => 1 + fx_expire_check_ne_budget EX l (Trie.left second) + vbudget v +
      fx_expire_check_ne_budget EX r (Trie.right second)
  end.

(** The directed bound includes the outer trie match. *)

Definition fx_expire_check_directed_budget {X} (EX : encoding X)
    (first second : Map.t X (list X)) : nat :=
  match first with
  | Trie.Empty => 1
  | Trie.Nodes n => 1 + fx_expire_check_ne_budget EX n second
  end.

(** Both directions contribute independent input-derived upper bounds. *)

Definition fx_expire_check_budget {X} (EX : encoding X) (left_map right_map : Map.t X (list X))
    : nat :=
  1 + fx_expire_check_directed_budget EX left_map right_map +
    fx_expire_check_directed_budget EX right_map left_map.

(** The exact map-check result and source-frame budget follow one captured traversal. *)

(** Counted expiry checking returns the original comparison result within the two-map budget. *)
Definition fx_expire_check_statement : Prop :=
  forall (X : Type) (EX : encoding X) (left_map right_map : Map.t X (list X)),
    let '(out, events) := fx_expire_check EX left_map right_map in
    out = observation_expire_check EX left_map right_map /\
      fx_expire_check_work events <= fx_expire_check_budget EX left_map right_map.

(** Comparison events relate their groups to encoder sources; case events require no bodies. *)

Definition fx_expire_check_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_expire_check_event X) (bodies : list (list B)) : Prop :=
  match event with
  | FxExpireCheckCase => bodies = []
  | FxExpireCheckCompare events => exists groups,
      Forall2 (fx_observe_compare_source source) events groups /\ bodies = concat groups
  end.

(** Only selected comparisons contribute external encoder-call budgets. *)

Definition fx_expire_check_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (event : fx_expire_check_event X) : nat :=
  match event with
  | FxExpireCheckCase => 0
  | FxExpireCheckCompare events =>
      fold_right (fun e n => fx_observe_compare_external_budget budget e + n) 0 events
  end.

(** The same selective traversal provides exact output, bodies and an input-derived bound. *)

(** Under encoder source laws, expiry checking preserves its result and has source receipts and a
    work bound. *)
Definition fx_expire_check_source_statement : Prop :=
  forall (X C A B : Type) (EX : encoding X) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (left_map right_map : Map.t X (list X)),
    fx_observe_compare_source_laws EX source budget ->
    let '(out, events) := fx_expire_check EX left_map right_map in
    exists bodies, Forall2 (fx_expire_check_event_source source) events bodies /\
      out = observation_expire_check EX left_map right_map /\
      fx_expire_check_work events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_expire_check_budget EX left_map right_map +
        fold_right (fun e n => fx_expire_check_external_budget budget e + n) 0 events.
