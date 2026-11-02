(** * Nested full checker examples

    The nested model retains the actual unary encoder and individual callback bodies.
    For example, a lookup of one records both unary frames and the successor frame.
    Builds on: nested checker adequacy and the rooted checker client. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Order Require Import OrderLattice OrderBasic.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditWorklistCallbacks FixpointAuditFullCheck FixpointAuditFullCheckAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointAuditRootedCheckClient
  FixpointAuditRootedFullCheckExamples.
Import List.ListNotations.

(** * Individual external callbacks *)

(** This adapter retains symbolic empty bodies; the concrete client below supplies source steps. *)

Definition nested_client : fx_check_external_model nat nat bool audit_nat_encoding_event :=
  FxCheckExternalModel nat nat bool audit_nat_encoding_event audit_nat_encode
    (fun c => (System.rhs rooted_system c, []))
    (fun c => (System.target rooted_system c, []))
    (fun k value => (k value, [])) (fun a b => (leb bool_lattice a b, [])).

Definition nested_budget : fx_check_external_budget nat nat bool audit_nat_encoding_event :=
  FxCheckExternalBudget nat nat bool audit_nat_encoding_event (fun _ => 2)
    (fun x => 2 * S x * S (Pos.size_nat (encode nat_encoding x))) (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0).

Definition nested_source : fx_check_external_source nat nat bool audit_nat_encoding_event :=
  FxCheckExternalSource nat nat bool audit_nat_encoding_event
    (fun x code body => exists work, audit_nat_encode_run x code body work /\
      work = audit_nat_events_work body)
    (fun c result body => result = System.rhs rooted_system c /\ body = [])
    (fun c result body => result = System.target rooted_system c /\ body = [])
    (fun k value result body => result = k value /\ body = [])
    (fun a b result body => result = leb bool_lattice a b /\ body = []).

Lemma nested_client_erases : fx_check_external_erases nat_encoding bool_lattice rooted_system
  nested_client.
Proof.
  unfold fx_check_external_erases, nested_client; cbn; repeat split; intros; try reflexivity.
  apply audit_nat_encode_erases.
Qed.

Lemma nested_client_bounded : fx_check_external_bounded nested_client nested_budget.
Proof.
  unfold fx_check_external_bounded; repeat split; intros; try reflexivity.
  - change (1 <= 2); lia.
  - change (fx_one_body_work (fx_body_weight rooted_budget) (snd (audit_nat_encode x)) <=
      2 * S x * S (Pos.size_nat (encode nat_encoding x))).
    rewrite rooted_encoder_body_work.
    destruct (rooted_encoder_run x) as [work [Hrun Hwork]].
    pose proof (audit_nat_encode_run_correct x _ _ work Hrun) as [_ [_ [_ Hbound]]].
    lia.
Qed.

Lemma nested_client_source : fx_check_external_source_adequacy nested_source nested_client.
Proof.
  unfold fx_check_external_source_adequacy; split.
  - intro x; change (let '(code, body) := audit_nat_encode x in
      exists work, audit_nat_encode_run x code body work /\ work = audit_nat_events_work body).
    pose proof (rooted_encoder_run x) as Hrun.
    destruct (audit_nat_encode x); exact Hrun.
  - repeat split; intros; split; reflexivity.
Qed.

Lemma nested_encoder_source_work x code body work :
  audit_nat_encode_run x code body work ->
  work = fx_check_body_work nested_budget body /\ work <= fx_check_encode_bound nested_budget x.
Proof.
  intro Hrun.
  exact (rooted_encoder_source_work x code body work Hrun).
Qed.

(** Key two's real work exceeds both the former event count and its former allowance. *)
Example nested_key_two_source_charge :
  exists work, audit_nat_encode_run 2 (fst (audit_nat_encode 2)) (snd (audit_nat_encode 2)) work /\
    work = 10 /\ length (snd (audit_nat_encode 2)) = 5 /\
    S 2 * S (Pos.size_nat (encode nat_encoding 2)) = 9 /\
    fx_one_body_work (fx_body_weight rooted_budget) (snd (audit_nat_encode 2)) = work /\
    fx_check_body_work nested_budget (snd (audit_nat_encode 2)) = work /\
    fx_budget_encode_x rooted_budget 2 = 18 /\ fx_check_encode_bound nested_budget 2 = 18 /\
    5 < work /\ 9 < work.
Proof.
  destruct (rooted_encoder_run 2) as [work [Hrun Hwork]].
  exists work; split; [exact Hrun|].
  vm_compute in Hwork; subst work; vm_compute; repeat split; try reflexivity; lia.
Qed.

(** Any nested run of this client retains the checker result and satisfies its input bound. *)
Example nested_client_input_bound m out events :
  fx_fullcheck_nested_run bool_lattice rooted_system m nested_client out events ->
  out = check_post bool_lattice rooted_system (lookup nat_encoding bool_lattice m) /\
  fx_check_nested_work nested_budget events <=
    fx_fullcheck_nested_input_budget nat_encoding bool_lattice rooted_system nested_budget m.
Proof.
  apply (fx_fullcheck_nested_input_bound nat nat bool audit_nat_encoding_event nat_encoding
    bool_lattice rooted_system m nested_client nested_budget nested_client_erases
    nested_client_bounded).
Qed.

(** Both empty and nonempty assignments have an actual nested derivation. *)
Example nested_client_total m :
  exists out events, fx_fullcheck_nested_run bool_lattice rooted_system m nested_client out events.
Proof.
  apply (fx_fullcheck_nested_total nat nat bool audit_nat_encoding_event nat_encoding bool_lattice
    rooted_system m nested_client nested_client_erases).
Qed.

(** The empty assignment is rejected by this nonempty system. *)
Example nested_empty_assignment_rejected events :
  fx_fullcheck_nested_run bool_lattice rooted_system Map.empty nested_client true events -> False.
Proof.
  intro Hrun.
  pose proof (fx_fullcheck_nested_erasure nat nat bool audit_nat_encoding_event nat_encoding
    bool_lattice rooted_system Map.empty nested_client nested_client_erases true events Hrun) as H.
  discriminate H.
Qed.

(** The populated assignment is accepted by every nested derivation. *)
Example nested_nonempty_assignment_accepted out events :
  fx_fullcheck_nested_run bool_lattice rooted_system rooted_all_true nested_client out events ->
  out = true.
Proof.
  intro Hrun.
  pose proof (fx_fullcheck_nested_erasure nat nat bool audit_nat_encoding_event nat_encoding
    bool_lattice rooted_system rooted_all_true nested_client nested_client_erases out events Hrun)
    as H.
  exact H.
Qed.

Definition nested_calls
    (events : list (fx_check_nested_event nat nat bool audit_nat_encoding_event)) :
    list (nat * nat * nat) :=
  flat_map (fun (event : fx_check_nested_event nat nat bool audit_nat_encoding_event) =>
    match event with
    | FcnGet x code _ _ _ _ => [(0, x, Pos.to_nat code)]
    | FcnContinue _ value _ _ => [(1, 1, (if value then 1 else 0))]
    | FcnRhs c _ _ => [(2, c, 0)]
    | FcnTarget c x _ => [(3, c, x)]
    | FcnLeb a b _ _ => [(4, (if a then 1 else 0), (if b then 1 else 0))]
    | FcnCase _ => []
    end) events.

Definition nested_gets
    (events : list (fx_check_nested_event nat nat bool audit_nat_encoding_event)) :=
  flat_map (fun (event : fx_check_nested_event nat nat bool audit_nat_encoding_event) =>
    match event with
    | FcnGet x code input raw body trie => [(x, code, input, raw, body, trie)]
    | _ => []
    end) events.

Definition nested_continuations
    (events : list (fx_check_nested_event nat nat bool audit_nat_encoding_event)) :=
  flat_map (fun (event : fx_check_nested_event nat nat bool audit_nat_encoding_event) =>
    match event with
    | FcnContinue _ value (Query.Side x side (Query.Ret result)) body =>
        [(value, x, side, result, body)]
    | _ => []
    end) events.

Lemma nested_encoder_run x :
  exists work, audit_nat_encode_run x (fst (audit_nat_encode x)) (snd (audit_nat_encode x)) work /\
    work = audit_nat_events_work (snd (audit_nat_encode x)).
Proof.
  apply rooted_encoder_run.
Qed.

(** The nested false-first run records the later read, continuation and side comparison in order. *)
Example nested_false_first_receipts :
  exists events, fx_fullcheck_nested_run bool_lattice rooted_system Map.empty nested_client false
    events /\ nested_calls events =
      [(2, 0, 0); (3, 0, 0); (0, 0, 1); (4, 1, 0);
       (2, 1, 0); (0, 1, 2); (1, 1, 0); (3, 1, 1); (0, 1, 2); (4, 0, 0);
       (0, 2, 3); (4, 0, 0)] /\
    nested_gets events =
      [(0, 1%positive, Map.empty, None, snd (audit_nat_encode 0),
        snd (audit_map_code_get 1%positive Map.empty));
       (1, 2%positive, Map.empty, None, snd (audit_nat_encode 1),
        snd (audit_map_code_get 2%positive Map.empty));
       (1, 2%positive, Map.empty, None, snd (audit_nat_encode 1),
        snd (audit_map_code_get 2%positive Map.empty));
       (2, 3%positive, Map.empty, None, snd (audit_nat_encode 2),
        snd (audit_map_code_get 3%positive Map.empty))] /\
    nested_continuations events = [(false, 2, false, false, [])] /\
    fx_check_external_trace_adequacy nested_source events.
Proof.
  eexists; split.
  - unfold fx_fullcheck_nested_run, rooted_system; cbn [System.constraints].
    eapply FcnConstraintsCons with (direct := false) (side_ok := true) (tail := true).
    + reflexivity.
    + apply FcnQueryRet.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply FcnConstraintsCons with (direct := true) (side_ok := true) (tail := true).
      * reflexivity.
      * eapply FcnQueryAsk.
        -- reflexivity.
        -- reflexivity.
        -- apply FcnQuerySide, FcnQueryRet.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply FcnConstraintsNil.
  - vm_compute; repeat (apply (nested_encoder_run 0) || apply (nested_encoder_run 1) ||
      apply (nested_encoder_run 2) || constructor || split || reflexivity).
Qed.

(** The concrete source receipts discharge the external-source theorem for the rejected run. *)
Example nested_false_first_source_bound :
  exists events, fx_fullcheck_nested_run bool_lattice rooted_system Map.empty nested_client false
    events /\ fx_check_external_trace_adequacy nested_source events /\
    fx_check_nested_work nested_budget events <=
      fx_fullcheck_nested_input_budget nat_encoding bool_lattice rooted_system nested_budget
        Map.empty.
Proof.
  destruct nested_false_first_receipts as [events [Hrun [_ [_ [_ Hsource]]]]].
  exists events; split; [exact Hrun|]; split; [exact Hsource|].
  pose proof (fx_fullcheck_external_source nat nat bool audit_nat_encoding_event nat_encoding
    bool_lattice rooted_system Map.empty nested_client nested_budget nested_source
    nested_client_erases nested_client_bounded false events Hrun Hsource) as [_ Hwork].
  exact Hwork.
Qed.

(** An empty constraint list has a single case event and accepts. *)
Example nested_empty_system :
  fx_fullcheck_nested_run bool_lattice
    (@System.Make nat nat bool [] (fun c => c) (fun _ => Query.Ret true)) Map.empty
    nested_client true [FcnCase 6].
Proof.
  constructor.
Qed.

(** The populated accepting assignment has an actual nested run returning true. *)
Example nested_accepted_run :
  exists events, fx_fullcheck_nested_run bool_lattice rooted_system rooted_all_true nested_client
    true events.
Proof.
  destruct (nested_client_total rooted_all_true) as [out [events Hrun]].
  pose proof (nested_nonempty_assignment_accepted out events Hrun) as Hout.
  subst out; exists events; exact Hrun.
Qed.

(** * Concrete nested callback bodies *)

Definition concrete_nested_client : fx_check_external_model nat nat bool concrete_check_event :=
  FxCheckExternalModel nat nat bool concrete_check_event concrete_encode concrete_rhs
    concrete_target concrete_continue concrete_leb.

Definition concrete_nested_budget : fx_check_external_budget nat nat bool concrete_check_event :=
  FxCheckExternalBudget nat nat bool concrete_check_event concrete_check_weight
    (fun x => 2 * S x * S (Pos.size_nat (encode nat_encoding x))) (fun _ => 4) (fun _ => 1)
    (fun _ _ => 2) (fun _ _ => 1).

Definition concrete_nested_source : fx_check_external_source nat nat bool concrete_check_event :=
  FxCheckExternalSource nat nat bool concrete_check_event concrete_encoder_source concrete_rhs_run
    concrete_target_run concrete_continue_run concrete_leb_run.

Lemma concrete_encoder_run x :
  let '(code, body) := concrete_encode x in concrete_encoder_source x code body.
Proof.
  unfold concrete_encode, concrete_encoder_source.
  destruct (rooted_encoder_run x) as [work [Hrun Hwork]].
  destruct (audit_nat_encode x) as [code frames] eqn:Hencode; cbn in Hrun, Hwork |- *.
  exists frames, work; repeat split; assumption || reflexivity.
Qed.

Lemma concrete_nested_erases : fx_check_external_erases nat_encoding bool_lattice rooted_system
  concrete_nested_client.
Proof.
  unfold fx_check_external_erases, concrete_nested_client; repeat split; intros.
  - change (fst (concrete_encode x) = encode nat_encoding x).
    unfold concrete_encode; destruct (audit_nat_encode x) as [code frames] eqn:Hencode.
    pose proof (audit_nat_encode_erases x) as Hcode; rewrite Hencode in Hcode; exact Hcode.
  - destruct c; reflexivity.
Qed.

Lemma concrete_nested_bounded :
  fx_check_external_bounded concrete_nested_client concrete_nested_budget.
Proof.
  unfold fx_check_external_bounded; repeat split; intros.
  - destruct b; first [change (1 <= 2) | change (1 <= 1)]; lia.
  - change (fx_one_body_work concrete_check_weight (snd (concrete_encode x)) <=
      2 * S x * S (Pos.size_nat (encode nat_encoding x))).
    unfold concrete_encode; destruct (audit_nat_encode x) as [code frames] eqn:Hencode.
    change (fx_one_body_work concrete_check_weight (map ConcreteEncode frames) <=
      2 * S x * S (Pos.size_nat (encode nat_encoding x))).
    rewrite concrete_encode_work.
    destruct (rooted_encoder_run x) as [work [Hrun Hwork]].
    rewrite Hencode in Hrun, Hwork; cbn in Hrun, Hwork.
    pose proof (audit_nat_encode_run_correct x code frames work Hrun) as [_ [_ [_ Hbound]]].
    change (work = audit_nat_events_work frames) in Hwork.
    now rewrite <- Hwork.
  - destruct c; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The concrete tagged encoders charge the actual ten units of work for key two. *)
Example concrete_key_two_source_charge :
  let '(code, body) := concrete_encode 2 in
  concrete_encoder_source 2 code body /\
  fx_one_body_work concrete_check_weight body = 10 /\
  fx_check_body_work concrete_nested_budget body = 10 /\
  fx_budget_encode_x concrete_budget 2 = 18 /\ fx_check_encode_bound concrete_nested_budget 2 = 18.
Proof.
  split.
  - change (let '(code, body) := concrete_encode 2 in concrete_encoder_source 2 code body).
    exact (concrete_encoder_run 2).
  - vm_compute; repeat split; reflexivity.
Qed.

Definition concrete_nested_bodies (events : list
    (fx_check_nested_event nat nat bool concrete_check_event)) : list concrete_check_event :=
  flat_map (fun event => match event with
    | FcnGet _ _ _ _ body _ => body
    | FcnRhs _ _ body => body
    | FcnTarget _ _ body => body
    | FcnContinue _ _ _ body => body
    | FcnLeb _ _ _ body => body
    | FcnCase _ => []
    end) events.

Definition concrete_nested_gets (events : list
    (fx_check_nested_event nat nat bool concrete_check_event)) :=
  flat_map (fun event => match event with
    | FcnGet x code input raw body trie => [(x, code, input, raw, body, trie)]
    | _ => []
    end) events.

Definition concrete_nested_continuations (events : list
    (fx_check_nested_event nat nat bool concrete_check_event)) :=
  flat_map (fun event => match event with
    | FcnContinue _ value (Query.Side x side (Query.Ret result)) body =>
        [(value, x, side, result, body)]
    | _ => []
    end) events.

(** The false-first run retains every concrete callback block and its real source derivation. *)
Example concrete_nested_false_first :
  exists events,
    fx_fullcheck_nested_run bool_lattice rooted_system Map.empty concrete_nested_client false
      events /\
    fx_check_external_trace_adequacy concrete_nested_source events /\
    concrete_nested_bodies events =
      [ConcreteRhsCase 0; ConcreteRhsZeroCase; ConcreteRhsBranch true; ConcreteRhsRet;
       ConcreteTarget 0] ++
      map ConcreteEncode (snd (audit_nat_encode 0)) ++ [ConcreteLeb true false;
      ConcreteRhsCase 1; ConcreteRhsZeroCase; ConcreteRhsBranch false; ConcreteRhsAsk] ++
      map ConcreteEncode (snd (audit_nat_encode 1)) ++
      [ConcreteContinueRet false; ConcreteContinueSide false; ConcreteTarget 1] ++
      map ConcreteEncode (snd (audit_nat_encode 1)) ++ [ConcreteLeb false false] ++
      map ConcreteEncode (snd (audit_nat_encode 2)) ++ [ConcreteLeb false false] /\
    concrete_nested_gets events =
      [(0, 1%positive, Map.empty, None, map ConcreteEncode (snd (audit_nat_encode 0)),
        snd (audit_map_code_get 1%positive Map.empty));
       (1, 2%positive, Map.empty, None, map ConcreteEncode (snd (audit_nat_encode 1)),
        snd (audit_map_code_get 2%positive Map.empty));
       (1, 2%positive, Map.empty, None, map ConcreteEncode (snd (audit_nat_encode 1)),
        snd (audit_map_code_get 2%positive Map.empty));
       (2, 3%positive, Map.empty, None, map ConcreteEncode (snd (audit_nat_encode 2)),
        snd (audit_map_code_get 3%positive Map.empty))] /\
    concrete_nested_continuations events =
      [(false, 2, false, false, [ConcreteContinueRet false; ConcreteContinueSide false])].
Proof.
  eexists; split.
  - unfold fx_fullcheck_nested_run, rooted_system; cbn [System.constraints].
    eapply FcnConstraintsCons with (direct := false) (side_ok := true) (tail := true).
    + reflexivity.
    + apply FcnQueryRet.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply FcnConstraintsCons with (direct := true) (side_ok := true) (tail := true).
      * reflexivity.
      * eapply FcnQueryAsk.
        -- reflexivity.
        -- reflexivity.
        -- apply FcnQuerySide, FcnQueryRet.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply FcnConstraintsNil.
  - vm_compute; repeat (apply (concrete_encoder_run 0) || apply (concrete_encoder_run 1) ||
      apply (concrete_encoder_run 2) || constructor || split || reflexivity).
Qed.

(** The false-first run meets the nested bound with only its actual callback source receipts. *)
Example concrete_nested_false_first_bound :
  exists events,
    fx_fullcheck_nested_run bool_lattice rooted_system Map.empty concrete_nested_client false
      events /\
    fx_check_external_trace_adequacy concrete_nested_source events /\
    fx_check_nested_work concrete_nested_budget events <=
      fx_fullcheck_nested_input_budget nat_encoding bool_lattice rooted_system
        concrete_nested_budget Map.empty.
Proof.
  destruct concrete_nested_false_first as [events [Hrun [Hsource Hobservations]]].
  exists events; split; [exact Hrun|]; split; [exact Hsource|].
  pose proof (fx_fullcheck_external_source nat nat bool concrete_check_event nat_encoding
    bool_lattice rooted_system Map.empty concrete_nested_client concrete_nested_budget
    concrete_nested_source concrete_nested_erases concrete_nested_bounded false events Hrun Hsource)
    as [_ Hwork].
  exact Hwork.
Qed.
