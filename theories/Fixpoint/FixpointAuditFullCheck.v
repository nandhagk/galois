(** * Full checker with explicit external callback bodies

    Every callback is invoked once at the real source call, and its body observations are
    retained inside that same event. Only externally supplied functions use these adapters;
    concrete internally constructed callbacks must instantiate their literal models.
    For example, a target callback carries its returned value and body trace.
    Builds on: FixpointCheck and the frozen shared trie model. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

Record fx_check_external_model (X C A B : Type) : Type := FxCheckExternalModel {
  fx_check_encode_model : X -> positive * list B;
  fx_check_rhs_model : C -> Query.t X A * list B;
  fx_check_target_model : C -> X * list B;
  fx_check_continue_model : (A -> Query.t X A) -> A -> Query.t X A * list B;
  fx_check_leb_model : A -> A -> bool * list B
}.

Arguments fx_check_encode_model {X C A B} _ _.

Arguments fx_check_rhs_model {X C A B} _ _.

Arguments fx_check_target_model {X C A B} _ _.

Arguments fx_check_continue_model {X C A B} _ _ _.

Arguments fx_check_leb_model {X C A B} _ _ _.

(** The modeled encoder, target, right-hand side, continuation and comparison return their
    original values. *)
Definition fx_check_external_erases {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (cb : fx_check_external_model X C A B) : Prop :=
  (forall x, fst (fx_check_encode_model cb x) = encode EX x) /\
  (forall c, fst (fx_check_rhs_model cb c) = System.rhs S c) /\
  (forall c, fst (fx_check_target_model cb c) = System.target S c) /\
  (forall k a, fst (fx_check_continue_model cb k a) = k a) /\
  (forall a b, fst (fx_check_leb_model cb a b) = leb L a b).

Inductive fx_check_nested_event (X C A B : Type) : Type :=
  | FcnGet (x : X) (code : positive) (input : assignment X A) (raw : option A)
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * A)))
  | FcnRhs (c : C) (out : Query.t X A) (body : list B)
  | FcnTarget (c : C) (out : X) (body : list B)
  | FcnContinue (k : A -> Query.t X A) (value : A) (out : Query.t X A) (body : list B)
  | FcnLeb (lhs rhs : A) (out : bool) (body : list B)
  | FcnCase (site : nat).

Arguments FcnGet {X C A B} _ _ _ _ _ _.

Arguments FcnRhs {X C A B} _ _ _.

Arguments FcnTarget {X C A B} _ _ _.

Arguments FcnContinue {X C A B} _ _ _ _.

Arguments FcnLeb {X C A B} _ _ _ _.

Arguments FcnCase {X C A B} _.

Section NestedCheck.
Context {X C A B : Type} (L : lattice A) (S : System.t X C A) (m : assignment X A)
  (cb : fx_check_external_model X C A B).

Definition fcn_lookup (x : X) : A * list (fx_check_nested_event X C A B) :=
  let '(code, enc_body) := fx_check_encode_model cb x in
  let '(raw, trie_body) := audit_map_code_get code m in
  (
    match raw with
    | Some value => value
    | None => bot L
    end,
   [FcnGet x code m raw enc_body trie_body; FcnCase 0]).

(** A query derivation records each actual lookup and continuation body in execution order. *)
Inductive fcn_query_run : Query.t X A -> (A * list X * list (X * A)) ->
    list (fx_check_nested_event X C A B) -> Prop :=
  | FcnQueryRet : forall a, fcn_query_run (Query.Ret a) (a, [], []) [FcnCase 1]
  | FcnQueryAsk : forall x k value read_events next cont_body out reads sides later,
      fcn_lookup x = (value, read_events) ->
      fx_check_continue_model cb k value = (next, cont_body) ->
      fcn_query_run next (out, reads, sides) later ->
      fcn_query_run (Query.Ask x k) (out, x :: reads, sides)
        (FcnCase 1 :: read_events ++ FcnContinue k value next cont_body :: later ++ [FcnCase 2])
  | FcnQuerySide : forall x a next out reads sides later,
      fcn_query_run next (out, reads, sides) later ->
      fcn_query_run (Query.Side x a next) (out, reads, (x, a) :: sides)
        (FcnCase 1 :: later ++ [FcnCase 3]).

Fixpoint fcn_sides (sides : list (X * A)) : bool * list (fx_check_nested_event X C A B) :=
  match sides with
  | [] => (true, [FcnCase 4])
  | (x, value) :: rest =>
      let '(old, lookup_events) := fcn_lookup x in
      let '(head, leb_body) := fx_check_leb_model cb value old in
      let '(tail, later) := fcn_sides rest in
      (andb head tail, FcnCase 4 :: lookup_events ++ FcnLeb value old head leb_body ::
        later ++ [FcnCase 5])
  end.

(** A constraints derivation checks each query, target and side contribution and joins events. *)
Inductive fcn_constraints_run : list C -> bool -> list (fx_check_nested_event X C A B) -> Prop :=
  | FcnConstraintsNil : fcn_constraints_run [] true [FcnCase 6]
  | FcnConstraintsCons : forall c rest rhs rhs_body value reads sides query_events
      target target_body old lookup_events direct leb_body side_ok side_events tail later,
      fx_check_rhs_model cb c = (rhs, rhs_body) ->
      fcn_query_run rhs (value, reads, sides) query_events ->
      fx_check_target_model cb c = (target, target_body) ->
      fcn_lookup target = (old, lookup_events) ->
      fx_check_leb_model cb value old = (direct, leb_body) ->
      fcn_sides sides = (side_ok, side_events) ->
      fcn_constraints_run rest tail later ->
      fcn_constraints_run (c :: rest) (andb (andb direct side_ok) tail)
        (FcnCase 6 :: FcnRhs c rhs rhs_body :: query_events ++
          FcnTarget c target target_body :: lookup_events ++ FcnLeb value old direct leb_body ::
          side_events ++ FcnCase 7 :: later ++ [FcnCase 8]).

(** A full-check derivation runs the constraint relation over the system's declared constraints. *)
Definition fx_fullcheck_nested_run := fcn_constraints_run (System.constraints S).

End NestedCheck.

(** If callbacks return the original values, every counted checker run yields the uncounted
    result. *)
Definition fx_fullcheck_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> forall out events,
    fx_fullcheck_nested_run L S m cb out events -> out = check_post L S (lookup EX L m).

(** For callbacks that erase correctly, the nested checker relation has a run for every input. *)
Definition fx_fullcheck_nested_total_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B),
    fx_check_external_erases EX L S cb -> exists out events, fx_fullcheck_nested_run L S m cb
  out events.

(** These interfaces describe individual genuinely external callbacks, never a whole-check
    budget premise. Each client must prove its concrete callback-body source adequacy. *)

Record fx_check_external_budget (X C A B : Type) : Type := FxCheckExternalBudget {
  fx_check_body_weight : B -> nat;
  fx_check_encode_bound : X -> nat;
  fx_check_rhs_bound : C -> nat;
  fx_check_target_bound : C -> nat;
  fx_check_continue_bound : (A -> Query.t X A) -> A -> nat;
  fx_check_leb_bound : A -> A -> nat
}.

Arguments fx_check_body_weight {X C A B} _ _.

Arguments fx_check_encode_bound {X C A B} _ _.

Arguments fx_check_rhs_bound {X C A B} _ _.

Arguments fx_check_target_bound {X C A B} _ _.

Arguments fx_check_continue_bound {X C A B} _ _ _.

Arguments fx_check_leb_bound {X C A B} _ _ _.

Definition fx_check_body_work {X C A B} (budget : fx_check_external_budget X C A B)
    (body : list B) : nat := fold_right (fun e n => fx_check_body_weight budget e + n) 0 body.

(** Every modeled callback body fits its input bound and every body event has positive weight. *)
Definition fx_check_external_bounded {X C A B} (cb : fx_check_external_model X C A B)
    (budget : fx_check_external_budget X C A B) : Prop :=
  (forall b, 1 <= fx_check_body_weight budget b) /\
  (forall x, fx_check_body_work budget (snd (fx_check_encode_model cb x)) <=
  fx_check_encode_bound budget x) /\
  (forall c, fx_check_body_work budget (snd (fx_check_rhs_model cb c)) <= fx_check_rhs_bound
  budget c) /\
  (forall c, fx_check_body_work budget (snd (fx_check_target_model cb c)) <=
  fx_check_target_bound budget c) /\
  (forall k a, fx_check_body_work budget (snd (fx_check_continue_model cb k a)) <=
    fx_check_continue_bound budget k a) /\
  (forall a b, fx_check_body_work budget (snd (fx_check_leb_model cb a b)) <= fx_check_leb_bound
  budget a b).

Definition fx_check_nested_event_work {X C A B} (budget : fx_check_external_budget X C A B)
    (event : fx_check_nested_event X C A B) : nat :=
  match event with
  | FcnGet _ _ _ _ enc_body trie_body =>
      8 + fx_check_body_work budget enc_body + audit_trie_get_trace_source_work trie_body
  | FcnRhs _ _ body
  | FcnTarget _ _ body
  | FcnContinue _ _ _ body
  | FcnLeb _ _ _ body =>
      3 + fx_check_body_work budget body
  | FcnCase _ => 3
  end.

Definition fx_check_nested_work {X C A B} (budget : fx_check_external_budget X C A B)
    (events : list (fx_check_nested_event X C A B)) : nat :=
  fold_right (fun e n => fx_check_nested_event_work budget e + n) 0 events.

Definition fx_check_nested_lookup_budget {X C A B} (EX : encoding X)
    (budget : fx_check_external_budget X C A B) (x : X) : nat :=
  11 + fx_check_encode_bound budget x + 5 * Pos.size_nat (encode EX x).

Fixpoint fx_check_nested_query_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (q : Query.t X A) : nat :=
  match q with
  | Query.Ret _ => 3
  | Query.Ask x k =>
      let value := lookup EX L m x in
      9 + fx_check_nested_lookup_budget EX budget x + fx_check_continue_bound budget k value +
        fx_check_nested_query_budget EX L budget m (k value)
  | Query.Side _ _ next => 6 + fx_check_nested_query_budget EX L budget m next
  end.

Fixpoint fx_check_nested_sides_budget {X C A B} (EX : encoding X) (L : lattice A)
    (budget : fx_check_external_budget X C A B) (m : assignment X A) (sides : list (X * A)) : nat :=
  match sides with
  | [] => 3
  | (x, value) :: rest =>
      9 + fx_check_nested_lookup_budget EX budget x +
      fx_check_leb_bound budget value (lookup EX L m x) +
      fx_check_nested_sides_budget EX L budget m rest
  end.

Fixpoint fx_check_nested_constraints_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B)
    (m : assignment X A) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest =>
      let rhs := System.rhs S c in
      let '(value, _, sides) := Query.run rhs (lookup EX L m) in
      let target := System.target S c in
      18 + fx_check_rhs_bound budget c + fx_check_nested_query_budget EX L budget m rhs +
      fx_check_target_bound budget c + fx_check_nested_lookup_budget EX budget target +
      fx_check_leb_bound budget value (lookup EX L m target) +
      fx_check_nested_sides_budget EX L budget m sides +
      fx_check_nested_constraints_budget EX L S budget m rest
  end.

Definition fx_fullcheck_nested_input_budget {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (budget : fx_check_external_budget X C A B) (m : assignment X A) : nat :=
  fx_check_nested_constraints_budget EX L S budget m (System.constraints S).

(** Under erasure and callback bounds, a checker run agrees with the original and fits its input
    budget. *)
Definition fx_fullcheck_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B) (budget : fx_check_external_budget X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_fullcheck_nested_run L S m cb out events ->
    out = check_post L S (lookup EX L m) /\
    fx_check_nested_work budget events <= fx_fullcheck_nested_input_budget EX L S budget m.

(** A client supplies source relations only for its external callback bodies. They are not
    relations for the checker or its total cost. The client must define and prove the actual
    source rules for these relations before using this adapter as implementation adequacy. *)

Record fx_check_external_source (X C A B : Type) : Type := FxCheckExternalSource {
  fx_check_encode_source : X -> positive -> list B -> Prop;
  fx_check_rhs_source : C -> Query.t X A -> list B -> Prop;
  fx_check_target_source : C -> X -> list B -> Prop;
  fx_check_continue_source : (A -> Query.t X A) -> A -> Query.t X A -> list B -> Prop;
  fx_check_leb_source : A -> A -> bool -> list B -> Prop
}.

Arguments fx_check_encode_source {X C A B} _ _ _ _.

Arguments fx_check_rhs_source {X C A B} _ _ _ _.

Arguments fx_check_target_source {X C A B} _ _ _ _.

Arguments fx_check_continue_source {X C A B} _ _ _ _ _.

Arguments fx_check_leb_source {X C A B} _ _ _ _ _.

(** The modeled callback outputs and bodies satisfy the corresponding supplied source relations. *)
Definition fx_check_external_source_adequacy {X C A B}
    (source : fx_check_external_source X C A B) (cb : fx_check_external_model X C A B) : Prop :=
  (forall x, let '(out, body) := fx_check_encode_model cb x in fx_check_encode_source source x
  out body) /\
  (forall c, let '(out, body) := fx_check_rhs_model cb c in fx_check_rhs_source source c out
  body) /\
  (forall c, let '(out, body) := fx_check_target_model cb c in fx_check_target_source source c
  out body) /\
  (forall k a, let '(out, body) := fx_check_continue_model cb k a in
    fx_check_continue_source source k a out body) /\
  (forall a b, let '(out, body) := fx_check_leb_model cb a b in fx_check_leb_source source a b
  out body).

(** Recorded lookup, RHS, target, continuation and comparison bodies satisfy their source
    relations; checker case events impose no condition. *)

Definition fx_check_external_trace_adequacy {X C A B} (source : fx_check_external_source X C A B)
    (events : list (fx_check_nested_event X C A B)) : Prop :=
  Forall (fun e =>
    match e with
    | FcnGet x code _ _ body _ => fx_check_encode_source source x code body
    | FcnRhs c out body => fx_check_rhs_source source c out body
    | FcnTarget c out body => fx_check_target_source source c out body
    | FcnContinue k value out body => fx_check_continue_source source k value out body
    | FcnLeb lhs rhs out body => fx_check_leb_source source lhs rhs out body
    | FcnCase _ => True
    end) events.

(** With checker callback erasure and bounds, a nested run with adequate source receipts returns
    the original check within its input budget. *)
Definition fx_fullcheck_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (L : lattice A) (S : System.t X C A) m
    (cb : fx_check_external_model X C A B) (budget : fx_check_external_budget X C A B)
    (source : fx_check_external_source X C A B),
    fx_check_external_erases EX L S cb -> fx_check_external_bounded cb budget -> forall out events,
    fx_fullcheck_nested_run L S m cb out events -> fx_check_external_trace_adequacy source events ->
    out = check_post L S (lookup EX L m) /\
    fx_check_nested_work budget events <= fx_fullcheck_nested_input_budget EX L S budget m.
