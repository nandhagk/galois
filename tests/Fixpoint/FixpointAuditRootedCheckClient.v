(** * Rooted checker client with a recursive encoder

    This client supplies actual unary encoder runs and per-call callback laws.
    For example, reading unknown one retains its encoder's successor events.
    Builds on: the rooted checker theorem and unary encoder adequacy. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditCost
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Order Require Import OrderLattice OrderBasic.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNarrowCheck
  FixpointAuditCheckCallbacks FixpointAuditCheckCallbacksAdequacy.
Import List.ListNotations.

(** * A two-constraint system with an actual continuation and side contribution *)

(** The first adapter keeps symbolic empty bodies for non-encoder callbacks. *)

Definition rooted_system : System.t nat nat bool :=
  @System.Make nat nat bool [0; 1] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ret true
      else Query.Ask 1 (fun value => Query.Side 2 value (Query.Ret value))).

Definition rooted_source : fx_declared_callback_source nat nat bool audit_nat_encoding_event :=
  FxDeclaredCallbackSource nat nat bool audit_nat_encoding_event
    (fun x code body => exists work, audit_nat_encode_run x code body work /\
      work = audit_nat_events_work body)
    (fun _ _ _ => False)
    (fun c result body => result = System.target rooted_system c /\ body = [])
    (fun _ _ _ => False) (fun _ _ _ => False)
    (fun c result body => result = System.rhs rooted_system c /\ body = [])
    (fun k value result body => result = k value /\ body = [])
    (fun a b result body => result = leb bool_lattice a b /\ body = [])
    (fun _ _ _ _ => False) (fun _ _ _ _ => False).

Definition rooted_budget : fx_declared_callback_budget nat nat bool audit_nat_encoding_event :=
  FxDeclaredCallbackBudget nat nat bool audit_nat_encoding_event (fun _ => 2)
    (fun x => 2 * S x * S (Pos.size_nat (encode nat_encoding x))) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0).

Lemma rooted_encoder_body_work body :
  fx_one_body_work (fx_body_weight rooted_budget) body = audit_nat_events_work body.
Proof.
  induction body as [|event rest IH]; [reflexivity|].
  change (2 + fx_one_body_work (fx_body_weight rooted_budget) rest = 2 * S (length rest)).
  unfold audit_nat_events_work in IH; lia.
Qed.

Lemma rooted_encoder_run x :
  exists work, audit_nat_encode_run x (fst (audit_nat_encode x)) (snd (audit_nat_encode x)) work /\
    work = audit_nat_events_work (snd (audit_nat_encode x)).
Proof.
  destruct (audit_nat_encode_run_total x) as [code [body [work Hrun]]].
  pose proof (audit_nat_encode_run_correct x code body work Hrun) as [_ [Hpair [Hwork _]]].
  exists work; rewrite <- Hpair; cbn; split; [exact Hrun|].
  unfold audit_nat_events_work; exact Hwork.
Qed.

Lemma rooted_encoder_source_work x code body work :
  audit_nat_encode_run x code body work ->
  work = fx_one_body_work (fx_body_weight rooted_budget) body /\
  work <= fx_budget_encode_x rooted_budget x.
Proof.
  intro Hrun.
  pose proof (audit_nat_encode_run_correct x code body work Hrun) as [_ [_ [Hwork Hbound]]].
  rewrite rooted_encoder_body_work; unfold audit_nat_events_work; split; assumption.
Qed.

Lemma rooted_laws : fx_fullcheck_rooted_laws nat_encoding bool_lattice rooted_system
  rooted_source rooted_budget.
Proof.
  unfold fx_fullcheck_rooted_laws; repeat split.
  - intro x; destruct (audit_nat_encode_run_total x) as [code [body [work Hrun]]].
    pose proof (audit_nat_encode_run_correct x code body work Hrun) as [Hcode [_ [Hwork _]]].
    subst code; exists body, work; split; [exact Hrun|].
    unfold audit_nat_events_work; exact Hwork.
  - intros c Hc; exists []; split; reflexivity.
  - intros c Hc; exists []; split; reflexivity.
  - intros k a Hreachable; exists []; split; reflexivity.
  - intros a b; exists []; split; reflexivity.
  - intros x out body [work [Hrun Hwork]].
    pose proof (audit_nat_encode_run_correct x out body work Hrun) as [_ [_ [_ Hbound]]].
    rewrite rooted_encoder_body_work, <- Hwork; exact Hbound.
  - intros c out body [_ ->]; reflexivity.
  - intros c out body [_ ->]; reflexivity.
  - intros k a out body [_ ->]; reflexivity.
  - intros a b out body [_ ->]; reflexivity.
Qed.

(** The nonempty client supplies genuine encoder runs to the rooted source theorem. *)
Example rooted_source_bound m :
  let '(out, events) := fx_fullcheck_counted nat_encoding bool_lattice rooted_system m in
  exists bodies, fx_fullcheck_rooted_trace_source rooted_source events bodies /\
    out = check_post bool_lattice rooted_system (lookup nat_encoding bool_lattice m) /\
    fx_fullcheck_work nat_encoding events + fx_declared_body_work (fun _ => 2) bodies <=
      fx_fullcheck_input_budget nat_encoding bool_lattice rooted_system m +
      fx_fullcheck_rooted_external_budget rooted_budget events.
Proof.
  apply (fx_fullcheck_rooted_source nat nat bool audit_nat_encoding_event nat_encoding nat_encoding
    bool_lattice rooted_system m rooted_source rooted_budget rooted_laws).
Qed.

(** * Concrete callback source steps *)

(** The encoder frames keep their original charge; the other tags name actual source blocks. *)
Inductive concrete_check_event : Type :=
  | ConcreteEncode (event : audit_nat_encoding_event)
  | ConcreteRhsCase (c : nat)
  | ConcreteRhsZeroCase
  | ConcreteRhsBranch (is_zero : bool)
  | ConcreteRhsRet
  | ConcreteRhsAsk
  | ConcreteTarget (c : nat)
  | ConcreteContinueRet (value : bool)
  | ConcreteContinueSide (value : bool)
  | ConcreteLeb (left right : bool).

Definition concrete_check_weight (event : concrete_check_event) : nat :=
  match event with
  | ConcreteEncode _ => 2
  | _ => 1
  end.

Definition concrete_continuation (value : bool) : Query.t nat bool :=
  Query.Side 2 value (Query.Ret value).

Definition concrete_rhs (c : nat) : Query.t nat bool * list concrete_check_event :=
  if Nat.eqb c 0 then
    (Query.Ret true,
      [ConcreteRhsCase c; ConcreteRhsZeroCase; ConcreteRhsBranch true; ConcreteRhsRet])
  else
    (Query.Ask 1 concrete_continuation,
      [ConcreteRhsCase c; ConcreteRhsZeroCase; ConcreteRhsBranch false; ConcreteRhsAsk]).

Definition concrete_target (c : nat) : nat * list concrete_check_event :=
  (c, [ConcreteTarget c]).

Definition concrete_continue (k : bool -> Query.t nat bool) (value : bool) :
    Query.t nat bool * list concrete_check_event :=
  (k value, [ConcreteContinueRet value; ConcreteContinueSide value]).

Definition concrete_leb (a b : bool) : bool * list concrete_check_event :=
  (leb bool_lattice a b, [ConcreteLeb a b]).

Definition concrete_encode (x : nat) : positive * list concrete_check_event :=
  let '(code, body) := audit_nat_encode x in (code, map ConcreteEncode body).

(** These rules record the exact case inspection and query constructor for each RHS. *)
Inductive concrete_rhs_run : nat -> Query.t nat bool -> list concrete_check_event -> Prop :=
  | ConcreteRhsZero : concrete_rhs_run 0 (Query.Ret true)
      [ConcreteRhsCase 0; ConcreteRhsZeroCase; ConcreteRhsBranch true; ConcreteRhsRet]
  | ConcreteRhsSuccessor : forall c,
      concrete_rhs_run (S c) (Query.Ask 1 concrete_continuation)
        [ConcreteRhsCase (S c); ConcreteRhsZeroCase; ConcreteRhsBranch false; ConcreteRhsAsk].

(** Target is the identity and records the actual returned constraint key. *)
Inductive concrete_target_run : nat -> nat -> list concrete_check_event -> Prop :=
  | ConcreteTargetRun : forall c, concrete_target_run c c [ConcreteTarget c].

(** Only the continuation occurring in the concrete system has this two-constructor derivation. *)
Inductive concrete_continue_run : (bool -> Query.t nat bool) -> bool -> Query.t nat bool ->
    list concrete_check_event -> Prop :=
  | ConcreteContinueRun : forall value,
      concrete_continue_run concrete_continuation value (concrete_continuation value)
        [ConcreteContinueRet value; ConcreteContinueSide value].

(** Boolean implication records the inspected operands and resulting branch. *)
Inductive concrete_leb_run : bool -> bool -> bool -> list concrete_check_event -> Prop :=
  | ConcreteLebFalse : forall b, concrete_leb_run false b true [ConcreteLeb false b]
  | ConcreteLebTrue : forall b, concrete_leb_run true b b [ConcreteLeb true b].

Definition concrete_encoder_source x code body : Prop :=
  exists frames work, audit_nat_encode_run x code frames work /\
    body = map ConcreteEncode frames /\ work = audit_nat_events_work frames.

Definition concrete_source : fx_declared_callback_source nat nat bool concrete_check_event :=
  FxDeclaredCallbackSource nat nat bool concrete_check_event
    concrete_encoder_source (fun _ _ _ => False) concrete_target_run
    (fun _ _ _ => False) (fun _ _ _ => False) concrete_rhs_run concrete_continue_run
    concrete_leb_run (fun _ _ _ _ => False) (fun _ _ _ _ => False).

Definition concrete_budget : fx_declared_callback_budget nat nat bool concrete_check_event :=
  FxDeclaredCallbackBudget nat nat bool concrete_check_event concrete_check_weight
    (fun x => 2 * S x * S (Pos.size_nat (encode nat_encoding x))) (fun _ => 0)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 4)
    (fun _ _ => 2) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0).

Lemma concrete_encode_work frames :
  fx_one_body_work concrete_check_weight (map ConcreteEncode frames) = audit_nat_events_work frames.
Proof.
  induction frames as [|frame rest IH]; [reflexivity|].
  change (2 + fx_one_body_work concrete_check_weight (map ConcreteEncode rest) =
    2 * S (length rest)).
  unfold audit_nat_events_work in IH; lia.
Qed.

Lemma concrete_rhs_source_correct c out body : concrete_rhs_run c out body ->
  concrete_rhs c = (out, body) /\ fx_one_body_work concrete_check_weight body = 4.
Proof.
  intro Hrun; inversion Hrun; split; reflexivity.
Qed.

Lemma concrete_target_source_correct c out body : concrete_target_run c out body ->
  concrete_target c = (out, body) /\ fx_one_body_work concrete_check_weight body = 1.
Proof.
  intro Hrun; inversion Hrun; split; reflexivity.
Qed.

Lemma concrete_continue_source_correct k value out body : concrete_continue_run k value out body ->
  concrete_continue k value = (out, body) /\ fx_one_body_work concrete_check_weight body = 2.
Proof.
  intro Hrun; inversion Hrun; split; reflexivity.
Qed.

Lemma concrete_leb_source_correct a b out body : concrete_leb_run a b out body ->
  concrete_leb a b = (out, body) /\ fx_one_body_work concrete_check_weight body = 1.
Proof.
  intro Hrun; inversion Hrun; split; reflexivity.
Qed.

Lemma concrete_encoder_source_correct x code body : concrete_encoder_source x code body ->
  concrete_encode x = (code, body) /\
  exists work, audit_nat_encode_run x code (snd (audit_nat_encode x)) work /\
    work = fx_one_body_work concrete_check_weight body /\
    work <= 2 * S x * S (Pos.size_nat (encode nat_encoding x)).
Proof.
  intros [frames [work [Hrun [Hbody Hwork]]]]; subst body.
  pose proof (audit_nat_encode_run_correct x code frames work Hrun) as
    [_ [Hpair [_ Hbound]]].
  split.
  - unfold concrete_encode; rewrite <- Hpair; reflexivity.
  - exists work; rewrite <- Hpair; cbn; split; [exact Hrun|].
    rewrite concrete_encode_work; split; assumption.
Qed.

(** Any reached Ask in this system is its single concrete continuation. *)
Lemma concrete_reachable_shape q : fx_declared_query_reachable rooted_system q ->
  q = Query.Ret true \/ q = Query.Ask 1 concrete_continuation \/
  (exists value, q = Query.Side 2 value (Query.Ret value)) \/
  (exists value, q = Query.Ret value).
Proof.
  intro Hreachable; induction Hreachable as [c Hin|x k a Hreach IH|x a next Hreach IH].
  - unfold rooted_system in Hin |- *; cbn in Hin |- *.
    destruct c as [|c]; [now left|].
    right; left; reflexivity.
  - destruct IH as [Hret|[Hask|[[v Hside]|[v Hret]]]]; try discriminate.
    inversion Hask; subst; right; right; left; exists a; reflexivity.
  - destruct IH as [Hret|[Hask|[[v Hside]|[v Hret]]]]; try discriminate.
    inversion Hside; subst; right; right; right; eauto.
Qed.

Lemma concrete_reachable_continuation k :
  (exists x, fx_declared_query_reachable rooted_system (Query.Ask x k)) ->
  k = concrete_continuation.
Proof.
  intros [x Hreach].
  pose proof (concrete_reachable_shape _ Hreach) as Hshape.
  destruct Hshape as [Hret|[Hask|[[value Hside]|[value Hret]]]]; try discriminate.
  now inversion Hask.
Qed.

Lemma concrete_rooted_laws : fx_fullcheck_rooted_laws nat_encoding bool_lattice rooted_system
  concrete_source concrete_budget.
Proof.
  unfold fx_fullcheck_rooted_laws; repeat split.
  - intro x; destruct (rooted_encoder_run x) as [work [Hrun Hwork]].
    exists (map ConcreteEncode (snd (audit_nat_encode x))).
    exists (snd (audit_nat_encode x)), work; repeat split; try assumption; try reflexivity.
    now rewrite audit_nat_encode_erases in Hrun.
  - intros c Hc; exists [ConcreteTarget c]; constructor.
  - intros c Hc; destruct c as [|c];
      [exists [ConcreteRhsCase 0; ConcreteRhsZeroCase; ConcreteRhsBranch true; ConcreteRhsRet]|
       exists [ConcreteRhsCase (S c); ConcreteRhsZeroCase; ConcreteRhsBranch false;
         ConcreteRhsAsk]]; constructor.
  - intros k a Hreach; apply concrete_reachable_continuation in Hreach; subst k.
    exists [ConcreteContinueRet a; ConcreteContinueSide a]; constructor.
  - intros [] b; [exists [ConcreteLeb true b]|exists [ConcreteLeb false b]]; constructor.
  - intros x out body [frames [work [Hrun [-> Hwork]]]].
    rewrite concrete_encode_work, <- Hwork.
    pose proof (audit_nat_encode_run_correct x out frames work Hrun) as [_ [_ [_ Hbound]]].
    exact Hbound.
  - intros c out body Hrun; inversion Hrun; reflexivity.
  - intros c out body Hrun; inversion Hrun; reflexivity.
  - intros k a out body Hrun; inversion Hrun; reflexivity.
  - intros a b out body Hrun; inversion Hrun; reflexivity.
Qed.

(** The real source rules account for the nonempty checker's reached callbacks. *)
Example concrete_rooted_source_bound m :
  let '(out, events) := fx_fullcheck_counted nat_encoding bool_lattice rooted_system m in
  exists bodies, fx_fullcheck_rooted_trace_source concrete_source events bodies /\
    out = check_post bool_lattice rooted_system (lookup nat_encoding bool_lattice m) /\
    fx_fullcheck_work nat_encoding events + fx_declared_body_work concrete_check_weight bodies <=
      fx_fullcheck_input_budget nat_encoding bool_lattice rooted_system m +
      fx_fullcheck_rooted_external_budget concrete_budget events.
Proof.
  apply (fx_fullcheck_rooted_source nat nat bool concrete_check_event nat_encoding nat_encoding
    bool_lattice rooted_system m concrete_source concrete_budget concrete_rooted_laws).
Qed.
