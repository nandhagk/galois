(** * Shared exact source contracts

    This canonical candidate fixes executable definitions and future proposition types.
    For example, each source mirror retains the actual operands and returned result.
    Builds on: collection audit models, interprocedural facts, and SSA PRE graphs. *)

From Stdlib Require Import Bool List NArith PArith ZArith.
From Galois.Analyses Require Import AnalysesInterprocedural AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap CollectionsTrie.
Import List.ListNotations.

(* Definition source: ExternalSource.v *)

(** * Genuine external callback source adapters

    These adapters may describe supplied client functions only.
    Library-created closures and helpers require their fixed library source definitions.
    The adapter law is a per-invocation source/erasure/budget duty, never the caller's bound. *)
Inductive audit_external_frame : Type :=
  | ExternalReturn
  | ExternalCase (site : nat)
  | ExternalConstruct (site : nat)
  | ExternalBinary (first second : Z)
  | ExternalMultiply (first second : Z)
  | ExternalDivide (first second : Z)
  | ExternalEmit (code : positive)
  | ExternalUnary (input : nat).

Definition audit_external_frame_work (frame : audit_external_frame) : nat :=
  64 +
  match frame with
  | ExternalBinary x y => audit_binary_weight x y
  | ExternalMultiply x y => audit_multiply_weight x y
  | ExternalDivide x y => audit_divide_weight x y
  | ExternalEmit code => audit_encoding_weight (Pos.size_nat code)
  | ExternalUnary input => audit_unary_conversion_weight input
  | _ => 0
  end.

Definition audit_external_trace_work (events : list audit_external_frame) : nat :=
  fold_right (fun frame rest => audit_external_frame_work frame + rest) 0 events.

Record audit_external_receipt (O : Type) : Type := AuditExternalReceipt {
  external_value : O;
  external_events : list audit_external_frame
}.
Arguments AuditExternalReceipt {O}.
Arguments external_value {O}.
Arguments external_events {O}.

Record audit_external_adapter (I O : Type) (plain : I -> O) : Type := AuditExternalAdapter {
  external_counted : I -> audit_external_receipt O;
  external_source : I -> O -> list audit_external_frame -> Prop;
  external_input_budget : I -> nat
}.
Arguments AuditExternalAdapter {I O plain}.
Arguments external_counted {I O plain}.
Arguments external_source {I O plain}.
Arguments external_input_budget {I O plain}.

(** This judgment attaches a source body to the retained input and returned output.
    It cannot justify an unrelated trace or a zero valuation. No callback is re-executed by
    this relation. A concrete client supplies literal source rules and proves the adapter. *)
Definition audit_external_body {I O plain} (adapter : audit_external_adapter I O plain)
    (input : I) (actual : O) (events : list audit_external_frame) : Prop :=
  external_source adapter input actual events /\ events <> [].

(** Each callback receipt erases to the plain result and meets its budget. *)
Definition audit_external_adapter_laws {I O plain} (adapter : audit_external_adapter I O plain) :
  Prop :=
  forall input,
  let receipt := external_counted adapter input in
  external_value receipt = plain input /\
  audit_external_body adapter input (external_value receipt) (external_events receipt) /\
  audit_external_trace_work (external_events receipt) <= external_input_budget adapter input.

(** Adapter laws imply erasure of each instrumented callback. *)
Definition audit_external_instrumentation_erases_statement : Prop :=
  forall I O plain (adapter : audit_external_adapter I O plain),
    audit_external_adapter_laws adapter ->
    forall input, external_value (external_counted adapter input) = plain input.

(** Each external source body has positive work. *)
Definition audit_external_body_positive_statement : Prop :=
  forall I O plain (adapter : audit_external_adapter I O plain) input output trace,
    audit_external_body adapter input output trace -> 64 <= audit_external_trace_work trace.

Inductive audit_bool_or_source : bool * bool -> bool -> list audit_external_frame -> Prop :=
  | ExternalOrFalse y : audit_bool_or_source (false,y) y [ExternalCase 0;ExternalReturn]
  | ExternalOrTrue y : audit_bool_or_source (true,y) true [ExternalCase 1;ExternalReturn].

Definition audit_bool_or_adapter : audit_external_adapter (bool * bool) bool
    (fun pair => orb (fst pair) (snd pair)) :=
  AuditExternalAdapter
    (fun pair => AuditExternalReceipt (orb (fst pair) (snd pair))
      [ExternalCase (if fst pair then 1 else 0);ExternalReturn]) audit_bool_or_source (fun _ =>
        128).

(* Definition source: ExactSource.v *)

(** * Typed compositional source counters

    These small combinators compose literal family source equations. They do not interpret
    an arbitrary language or accept an arbitrary execution relation. For example, a counted
    right fold evaluates its recursive tail before its actual callback.
    Builds on: the collection audit cost vocabulary. *)
Record exact_counted (Call A : Type) : Type := ExactCounted {
  exact_value : A;
  exact_units : nat;
  exact_events : audit_trace Call;
  exact_bodies : list (Call * list audit_external_frame)
}.
Arguments ExactCounted {Call A}.
Arguments exact_value {Call A}.
Arguments exact_units {Call A}.
Arguments exact_events {Call A}.
Arguments exact_bodies {Call A}.

Definition exact_lift {Call Other A} (inject : Call -> Other) (run : exact_counted Call A)
    : exact_counted Other A :=
  ExactCounted (exact_value run) (exact_units run)
    (map (fun event =>
      match event with
      | AuditCall call => AuditCall (inject call)
      | AuditCase site args => AuditCase site args
      | AuditConstruct site args => AuditConstruct site args
      | AuditKeyBit bit => AuditKeyBit bit
      | AuditArithmetic site args => AuditArithmetic site args
      end) (exact_events run))
    (map (fun body => (inject (fst body),snd body)) (exact_bodies run)).

(** A source constructor or fixed scalar result contributes one positive frame. *)
Definition exact_return {Call A} (site : nat) (value : A) : exact_counted Call A :=
  ExactCounted value 64 [AuditConstruct site []] [].

(** The source let is inspected after its first operand and before its continuation. *)
Definition exact_bind {Call A B} (site : nat) (first : exact_counted Call A)
    (next : A -> exact_counted Call B) : exact_counted Call B :=
  let later := next (exact_value first) in
  ExactCounted (exact_value later) (exact_units first + 64 + exact_units later)
    (exact_events first ++ AuditCase site [] :: exact_events later)
    (exact_bodies first ++ exact_bodies later).

(** A fixed source call retains its actual typed payload and positive abstract charge. *)
Definition exact_call {Call A} (call : Call) (charge : nat) (value : A) : exact_counted Call A :=
  ExactCounted value (64 + charge) [AuditCall call] [].

(** A genuine external callback executes its counted adapter once. Its actual typed call
    payload and positive source body are retained together; bind/lift preserve their order. *)
Definition exact_external_call {Call I O plain}
    (adapter : audit_external_adapter I O plain) (input : I) (call : O -> Call)
    : exact_counted Call O :=
  let receipt := external_counted adapter input in
  let actual := call (external_value receipt) in
  ExactCounted (external_value receipt)
    (64 + audit_external_trace_work (external_events receipt)) [AuditCall actual]
    [(actual,external_events receipt)].

(** Source cases precede the body selected by that case. *)
Definition exact_case {Call A} (site : nat) (body : exact_counted Call A) : exact_counted Call A :=
  ExactCounted (exact_value body) (64 + exact_units body)
    (AuditCase site [] :: exact_events body) (exact_bodies body).

Fixpoint exact_append {Call A} (site : nat) (first second : list A)
    : exact_counted Call (list A) :=
  match first with
  | [] => exact_case site (exact_return site second)
  | x :: xs => exact_case site
      (exact_bind site (exact_append site xs second) (fun tail => exact_return site (x :: tail)))
  end.

Fixpoint exact_map {Call A B} (site : nat) (f : A -> exact_counted Call B) (xs : list A)
    : exact_counted Call (list B) :=
  match xs with
  | [] => exact_case site (exact_return site [])
  | x :: rest => exact_case site
      (exact_bind site (f x) (fun y =>
       exact_bind site (exact_map site f rest) (fun ys => exact_return site (y :: ys))))
  end.

Fixpoint exact_flat_map {Call A B} (site : nat) (f : A -> exact_counted Call (list B))
    (xs : list A) : exact_counted Call (list B) :=
  match xs with
  | [] => exact_case site (exact_return site [])
  | x :: rest => exact_case site
      (exact_bind site (f x) (fun ys =>
       exact_bind site (exact_flat_map site f rest) (fun later => exact_append site ys later)))
  end.

Fixpoint exact_fold_left {Call A B} (site : nat) (f : B -> A -> exact_counted Call B)
    (xs : list A) (state : B) : exact_counted Call B :=
  match xs with
  | [] => exact_case site (exact_return site state)
  | x :: rest => exact_case site
      (exact_bind site (f state x) (fun next => exact_fold_left site f rest next))
  end.

Fixpoint exact_fold_right {Call A B} (site : nat) (f : A -> B -> exact_counted Call B)
    (state : B) (xs : list A) : exact_counted Call B :=
  match xs with
  | [] => exact_case site (exact_return site state)
  | x :: rest => exact_case site
      (exact_bind site (exact_fold_right site f state rest) (fun next => f x next))
  end.

(** The payload retains raw keys, encoded operands and actual map results. *)
Inductive exact_map_call (K V : Type) : Type :=
  | ExactEncode (key : K) (code : positive)
  | ExactGet (key : K) (code : positive) (before : Map.t K V) (answer : option V)
  | ExactSet (key : K) (code : positive) (value : V) (before after : Map.t K V)
  | ExactRemove (key : K) (code : positive) (before after : Map.t K V)
  | ExactElements (before : Map.t K V) (answer : list (K * V)).
Arguments ExactEncode {K V}.
Arguments ExactGet {K V}.
Arguments ExactSet {K V}.
Arguments ExactRemove {K V}.
Arguments ExactElements {K V}.

(** Encoder body work is a genuine supplied-encoder adapter; derived encoders must instantiate
    it with their fixed internal equation, not a caller law asserting the desired whole bound. *)
Definition exact_encode {Call K V} (inject : exact_map_call K V -> Call)
    (E : encoding K) (body : K -> nat) (key : K) : exact_counted Call positive :=
  let code := encode E key in
  exact_call (inject (ExactEncode key code))
    (audit_encoding_weight (Pos.size_nat code) + body key) code.

Definition exact_get {Call K V} (inject : exact_map_call K V -> Call)
    (E : encoding K) (body : K -> nat) (key : K) (table : Map.t K V)
    : exact_counted Call (option V) :=
  exact_bind 1 (exact_encode inject E body key) (fun code =>
    let answer := Map.code_get code table in
    exact_call (inject (ExactGet key code table answer))
      (audit_get_weight code + 32 * Pos.size_nat code) answer).

Definition exact_set {Call K V} (inject : exact_map_call K V -> Call)
    (E : encoding K) (body : K -> nat) (key : K) (value : V) (table : Map.t K V)
    : exact_counted Call (Map.t K V) :=
  exact_bind 2 (exact_encode inject E body key) (fun code =>
    let after := Trie.set code (key, value) table in
    exact_call (inject (ExactSet key code value table after))
      (audit_set_weight code + 64 * Pos.size_nat code) after).

Definition exact_remove {Call K V} (inject : exact_map_call K V -> Call)
    (E : encoding K) (body : K -> nat) (key : K) (table : Map.t K V)
    : exact_counted Call (Map.t K V) :=
  exact_bind 3 (exact_encode inject E body key) (fun code =>
    let after := Trie.remove code table in
    exact_call (inject (ExactRemove key code table after))
      (audit_remove_weight code + 64 * Pos.size_nat code) after).

Fixpoint exact_ne_nodes {A} (tree : Trie.ne A) : nat :=
  match tree with
  | Trie.N001 r | Trie.N100 r => S (exact_ne_nodes r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r | Trie.N110 r _ => S (exact_ne_nodes r)
  | Trie.N101 l r | Trie.N111 l _ r => S (exact_ne_nodes l + exact_ne_nodes r)
  end.

Definition exact_trie_nodes {A} (tree : Trie.t A) : nat :=
  match tree with
  | Trie.Empty => 1
  | Trie.Nodes root => S (exact_ne_nodes root)
  end.

(** Enumeration charges actual structural size and actual output; AUD-CL supplies its source
    recurrence/implementation bridge. Neither key labels nor output construction are free. *)
Definition exact_elements {Call K V} (inject : exact_map_call K V -> Call) (table : Map.t K V)
    : exact_counted Call (list (K * V)) :=
  let answer := Map.elements table in
  exact_call (inject (ExactElements table answer))
    (1 + 32 * Nat.pow (S (exact_trie_nodes table)) 2 + 8 * length answer) answer.

(** Counted lookup returns the plain map result. *)
Definition exact_get_erases_statement : Prop := forall (Call K V : Type)
    (inject : exact_map_call K V -> Call) E body key table,
  @exact_value Call (option V) (exact_get inject E body key table) = Map.get E key table.

(** Counted update returns the plain map result. *)
Definition exact_set_erases_statement : Prop := forall (Call K V : Type)
    (inject : exact_map_call K V -> Call) E body key value table,
  @exact_value Call (Map.t K V) (exact_set inject E body key value table) = Map.set E key value
    table.

(** Counted append returns ordinary concatenation. *)
Definition exact_append_erases_statement : Prop := forall Call A site xs ys,
  @exact_value Call (list A) (exact_append site xs ys) = xs ++ ys.

(** Counted map returns the mapped callback values. *)
Definition exact_map_erases_statement : Prop := forall (Call A B : Type) site
    (f : A -> exact_counted Call B) xs,
  @exact_value Call (list B) (exact_map site f xs) = map (fun x => exact_value (f x)) xs.

(** Counted right fold returns the fold of callback values. *)
Definition exact_fold_right_erases_statement : Prop := forall (Call A B : Type) site
    (f : A -> B -> exact_counted Call B) state xs,
  @exact_value Call B (exact_fold_right site f state xs) =
    fold_right (fun x acc => exact_value (f x acc)) state xs.

(** Counted left fold returns the fold of callback values. *)
Definition exact_fold_left_erases_statement : Prop := forall (Call A B : Type) site
    (f : B -> A -> exact_counted Call B) xs state,
  @exact_value Call B (exact_fold_left site f xs state) =
    fold_left (fun acc x => exact_value (f acc x)) xs state.

Fixpoint exact_filter {Call A} (site : nat) (test : A -> exact_counted Call bool)
    (xs : list A) : exact_counted Call (list A) :=
  match xs with
  | [] => exact_case site (exact_return site [])
  | x :: rest => exact_case site (exact_bind site (test x) (fun keep =>
      if keep then exact_case site (exact_bind site (exact_filter site test rest)
        (fun tail => exact_return site (x :: tail)))
      else exact_case site (exact_filter site test rest)))
  end.

Fixpoint exact_rev {Call A} (site : nat) (xs : list A) : exact_counted Call (list A) :=
  match xs with
  | [] => exact_case site (exact_return site [])
  | x :: rest => exact_case site (exact_bind site (exact_rev site rest)
      (fun tail => exact_bind site (exact_return site [x]) (fun singleton =>
        exact_append site tail singleton)))
  end.

Definition exact_set_of_list {Call K} (inject : exact_map_call K unit -> Call)
    (E : encoding K) (body : K -> nat) (xs : list K) : exact_counted Call (FinSet.t K) :=
  exact_fold_left 4 (fun state key => exact_set inject E body key tt state) xs FinSet.empty.

Definition exact_set_elements {Call K} (inject : exact_map_call K unit -> Call)
    (set : FinSet.t K) : exact_counted Call (list K) :=
  exact_bind 5 (exact_elements inject set)
    (fun rows => exact_map 5 (fun row => exact_return 5 (fst row)) rows).

Definition exact_set_mem {Call K} (inject : exact_map_call K unit -> Call)
    (E : encoding K) (body : K -> nat) (key : K) (set : FinSet.t K)
    : exact_counted Call bool :=
  exact_bind 6 (exact_get inject E body key set) (fun found =>
    exact_case 6 (exact_return 6 (
      match found with
      | Some _ => true
      | None => false
      end))).

Fixpoint exact_all {Call A} (site : nat) (test : A -> exact_counted Call bool) (xs : list A)
    : exact_counted Call bool :=
  match xs with
  | [] => exact_case site (exact_return site true)
  | x :: rest => exact_case site (exact_bind site (test x) (fun first =>
      exact_bind site (exact_all site test rest) (fun later => exact_return site (first && later))))
  end.

(* Definition source: PrePrimitiveAdequacy.v *)

(** * PRE's fixed collection and encoding source bridge duties

    Card: AUD-SP. These are actual library source recurrences with the represented operands;
    no client's desired whole placement bound is an assumption. *)
Definition pre_map_literal_work {K V} (body : K -> nat) (call : exact_map_call K V) : nat :=
  match call with
  | ExactEncode key _ => 1 + body key
  | ExactGet _ code before _ => 5 + audit_trie_get_source_work code before
  | ExactSet key code value before _ => 2 + audit_trie_update_source_work code (Some (key,value))
    before
  | ExactRemove _ code before _ => 2 + audit_trie_update_source_work code None before
  | ExactElements before _ => audit_elements_work (snd (audit_map_elements before))
  end.

Definition pre_map_fixed_charge {K V} (body : K -> nat) (call : exact_map_call K V) : nat :=
  64 +
  match call with
  | ExactEncode key code => audit_encoding_weight (Pos.size_nat code) + body key
  | ExactGet _ code _ _ => audit_get_weight code + 32 * Pos.size_nat code
  | ExactSet _ code _ _ _ => audit_set_weight code + 64 * Pos.size_nat code
  | ExactRemove _ code _ _ => audit_remove_weight code + 64 * Pos.size_nat code
  | ExactElements before answer =>
      1 + 32 * Nat.pow (S (exact_trie_nodes before)) 2 + 8 * length answer
  end.

(** The fixed map charge bounds literal implementation work. *)
Definition audit_pre_map_implementation_adequacy_statement : Prop :=
  forall K V (body : K -> nat) (call : exact_map_call K V),
    pre_map_literal_work body call <= pre_map_fixed_charge body call.

Definition pre_external_encode {K} (E : encoding K) (key : K) : positive * list (K * positive) :=
  let code := encode E key in (code,[(key,code)]).

Definition pre_external_encode_work {K} (body : K -> nat) (events : list (K * positive)) : nat :=
  fold_right (fun event rest => body (fst event) + rest) 0 events.

Definition pre_pair_encode_body {A B} (EA : encoding A) (EB : encoding B)
    (ab : A -> nat) (bb : B -> nat) (key : A * B) :=
  64 + ab (fst key) + bb (snd key) + 32 * Pos.size_nat (encode (pair_encoding EA EB) key).

(** The pair encoder returns its code within its fixed charge. *)
Definition audit_pre_pair_encoding_adequacy_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (ab : A -> nat) (bb : B -> nat) key,
    let run := audit_pair_encode (pre_external_encode EA) (pre_external_encode EB) key in
    fst run = encode (pair_encoding EA EB) key /\
    audit_pair_events_work (pre_external_encode_work ab) (pre_external_encode_work bb) (snd run) <=
      pre_pair_encode_body EA EB ab bb key.

(* Definition source: PreDerivedEncoding.v *)

(** Card: AUD-SP. Actual internal derived-encoder runs and exact future adequacy targets. *)
Definition pre_triple_source_encoding {A B C} EA EB EC :=
  @audit_pair_encode (A * B) C _ _
    (audit_pair_encode (pre_external_encode EA) (pre_external_encode EB)) (pre_external_encode EC).

Definition pre_triple_source_work {A B C} (ab : A -> nat) (bb : B -> nat) (cb : C -> nat) :=
  audit_pair_events_work (A:=A * B) (B:=C)
    (audit_pair_events_work (A:=A) (B:=B) (pre_external_encode_work ab) (pre_external_encode_work
      bb))
    (pre_external_encode_work cb).

Definition pre_frg_source_encoding {B E U} EB EE EU (d : frg_version B E U) :=
  let u := pre_external_encode EU in
  let eu := audit_pair_encode (pre_external_encode EE) u in
  let bu := audit_pair_encode (pre_external_encode EB) u in
  audit_sum_encode u (audit_sum_encode u (audit_sum_encode eu bu))
    (match d with
    | FrUnavailable u => inl u
    | FrInitial u => inr (inl u)
    | FrFresh e u => inr (inr (inl (e,u)))
    | FrPhi b u => inr (inr (inr (b,u)))
    end).

Definition pre_frg_source_work {B E U} (bb : B -> nat) (eb : E -> nat) (ub : U -> nat) :=
  let u := pre_external_encode_work ub in
  let eu := audit_pair_events_work (A:=E) (B:=U) (pre_external_encode_work eb) u in
  let bu := audit_pair_events_work (A:=B) (B:=U) (pre_external_encode_work bb) u in
  audit_sum_events_work (A:=U) (B:=U + (E * U + B * U)) u
    (audit_sum_events_work (A:=U) (B:=E * U + B * U) u
      (audit_sum_events_work (A:=E * U) (B:=B * U) eu bu)).

(** The derived encoders return their codes within their fixed charges. *)
Definition audit_pre_derived_encoding_adequacy_statement : Prop :=
  (forall A B C (EA : encoding A) (EB : encoding B) (EC : encoding C)
    (ab : A -> nat) (bb : B -> nat) (cb : C -> nat) key,
    let run := pre_triple_source_encoding EA EB EC key in
    fst run = encode (pair_encoding (pair_encoding EA EB) EC) key /\
    pre_triple_source_work ab bb cb (snd run) <=
      128 + ab (fst (fst key)) + bb (snd (fst key)) + cb (snd key) + 16 * Pos.size_nat (fst run)) /\
  (forall B E U (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (bb : B -> nat) (eb : E -> nat) (ub : U -> nat) d,
    let run := pre_frg_source_encoding EB EE EU d in
    fst run = encode (frg_version_encoding EB EE EU) d /\
    pre_frg_source_work bb eb ub (snd run) <=
      128 + 64 * Pos.size_nat (fst run) +
      match d with
      | FrUnavailable u | FrInitial u => ub u
      | FrFresh e u => eb e + ub u
      | FrPhi b u => bb b + ub u
      end).

(* Generic finite-key derived encoder work, used by both IDE branches. *)
Definition ide_option_body {D} (body : D -> nat) (d : option D) : nat :=
  match d with
  | None => 3
  | Some value => 4 + body value
  end.

Definition ide_fact_body {N D} (EN : encoding N) (ED : encoding D)
    (node_body : N -> nat) (fact_body : D -> nat) (key : IpTab.fact N D) : nat :=
  let vertex_cost vertex := 64 + node_body (fst vertex) + ide_option_body fact_body (snd vertex) in
  128 + 64 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) key) +
  match key with
  | inl (first,second) => vertex_cost first + vertex_cost second
  | inr vertex => vertex_cost vertex
  end.

(** * Relational receipts for actual calls

    These propositions attach source traces to the input and output retained at one actual
    invocation. They do not execute an external function again to recover its result.
    For example, a base encoder receipt certifies the code already passed to a trie lookup.
    Builds on: genuine external adapters and concrete collection encoder events. *)

(** A same-call receipt relates the actual result and trace to the adapter. *)
Definition audit_external_same_call {I O plain}
    (adapter : audit_external_adapter I O plain) (input : I) (output : O)
    (trace : list audit_external_frame) : Prop :=
  output = plain input /\ audit_external_body adapter input output trace /\
  audit_external_trace_work trace <= external_input_budget adapter input.

(** Adapter laws provide a source trace for each actual callback result. *)
Definition audit_external_same_call_exists_statement : Prop :=
  forall I O plain (adapter : audit_external_adapter I O plain),
  audit_external_adapter_laws adapter -> forall input output,
  output = plain input -> exists trace, audit_external_same_call adapter input output trace.

Definition audit_source_body_work (traces : list (list audit_external_frame)) : nat :=
  fold_right (fun trace rest => audit_external_trace_work trace + rest) 0 traces.

(** A base encoding receipt retains the actual encoded input and output. *)
Definition audit_base_encoding_receipts {K} (E : encoding K)
    (adapter : audit_external_adapter K positive (encode E)) input output
    (events : list (K * positive)) (trace : list audit_external_frame) : Prop :=
  events = [(input,output)] /\ audit_external_same_call adapter input output trace.

(** Pair receipts relate component events to their actual body traces. *)
Definition audit_pair_encoding_receipts {A B EA EB}
    (first : A -> positive -> list EA -> list audit_external_frame -> Prop)
    (second : B -> positive -> list EB -> list audit_external_frame -> Prop)
    (events : list (audit_pair_event A B EA EB)) (trace : list audit_external_frame) : Prop :=
  exists traces,
    Forall2 (fun event frames =>
      match event with
      | AuditPairFirst input output nested => first input output nested frames
      | AuditPairSecond input output nested => second input output nested frames
      | AuditPairFrame _ => frames = []
      end) events traces /\ trace = concat traces.

(** Option receipts relate component events to their actual body traces. *)
Definition audit_option_encoding_receipts {A E}
    (element : A -> positive -> list E -> list audit_external_frame -> Prop)
    (events : list (audit_option_event A E)) (trace : list audit_external_frame) : Prop :=
  exists traces,
    Forall2 (fun event frames =>
      match event with
      | AuditOptionNone => frames = []
      | AuditOptionSome input output nested => element input output nested frames
      end) events traces /\ trace = concat traces.

(** List receipts relate component events to their actual body traces. *)
Definition audit_list_encoding_receipts {A E}
    (element : A -> positive -> list E -> list audit_external_frame -> Prop)
    (events : list (audit_list_event A E)) (trace : list audit_external_frame) : Prop :=
  exists traces,
    Forall2 (fun event frames =>
      match event with
      | AuditListComponent input output nested => element input output nested frames
      | AuditListCase _ | AuditListFrame _ => frames = []
      end) events traces /\ trace = concat traces.

(** Sum receipts relate component events to their actual body traces. *)
Definition audit_sum_encoding_receipts {A B EA EB}
    (left : A -> positive -> list EA -> list audit_external_frame -> Prop)
    (right : B -> positive -> list EB -> list audit_external_frame -> Prop)
    (events : list (audit_sum_event A B EA EB)) (trace : list audit_external_frame) : Prop :=
  exists traces,
    Forall2 (fun event frames =>
      match event with
      | AuditSumLeft input output nested => left input output nested frames
      | AuditSumRight input output nested => right input output nested frames
      end) events traces /\ trace = concat traces.
