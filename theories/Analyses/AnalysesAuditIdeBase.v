(** * Finite IDE registry and ranked machine

    Defines the registry, rules and machine used by the IDE source models.
    For example, evaluating the true transformer at zero yields one.
    Builds on: AnalysesAuditSource, AnalysesInterprocedural and CollectionsMap. *)

From Stdlib Require Import Arith Bool Lia List NArith PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Fixpoint Require Import FixpointIndex.
From Galois.Order Require Import OrderLattice.
Import List.ListNotations.

(* Definition source: IdeGeneratedBase.v *)
(** Consuming copy of retained IDE semantics and fixed generated models; no semantic weakening. *)

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-core-declarations.md *)
Record audit_ide_registry (A F : Type) : Type := AuditIdeRegistry {
  audit_ide_eval : F -> A -> A;
  audit_ide_id : F;
  audit_ide_compose : F -> F -> F;
  audit_ide_join : F -> F -> F;
  audit_ide_equal : F -> F -> bool;
  audit_ide_rank : F -> nat;
  audit_ide_bound : nat
}.

Arguments audit_ide_eval {A F}.

Arguments audit_ide_id {A F}.

Arguments audit_ide_compose {A F}.

Arguments audit_ide_join {A F}.

Arguments audit_ide_equal {A F}.

Arguments audit_ide_rank {A F}.

Arguments audit_ide_bound {A F}.

(** Registry laws couple lattice behavior, extensional equality, composition, join and rank
    progress. *)
Record audit_ide_registry_laws {A F} (L : lattice A) (r : audit_ide_registry A F) : Prop := {
  audit_ide_lattice_laws : lattice_laws L;
  audit_ide_lub_laws : lub_laws L;
  audit_ide_eq_spec : forall f h, audit_ide_equal r f h = true <->
    forall a, audit_ide_eval r f a = audit_ide_eval r h a;
  audit_ide_identity : forall a, equivalent L (audit_ide_eval r (audit_ide_id r) a) a;
  audit_ide_composition : forall f h a,
    equivalent L (audit_ide_eval r (audit_ide_compose r f h) a)
      (audit_ide_eval r h (audit_ide_eval r f a));
  audit_ide_pointwise_join : forall f h a,
    equivalent L (audit_ide_eval r (audit_ide_join r f h) a)
      (join L (audit_ide_eval r f a) (audit_ide_eval r h a));
  audit_ide_distributes : forall f a b,
    equivalent L (audit_ide_eval r f (join L a b))
      (join L (audit_ide_eval r f a) (audit_ide_eval r f b));
  audit_ide_rank_bounded : forall f, audit_ide_rank r f <= audit_ide_bound r;
  audit_ide_rank_progress : forall f h,
    audit_ide_equal r (audit_ide_join r f h) f = false ->
    audit_ide_rank r f < audit_ide_rank r (audit_ide_join r f h)
}.

(** One successful insertion or strict pointwise join at a finite summary key. *)
Inductive audit_ide_update {K A F} (EK : encoding K) (r : audit_ide_registry A F)
    (keys : list K) : Map.t K F -> K -> Map.t K F -> Prop :=
  | AuditIdeFirst : forall state key incoming,
      In key keys -> Map.get EK key state = None ->
      audit_ide_update EK r keys state key (Map.set EK key incoming state)
  | AuditIdeGrow : forall state key old incoming,
      In key keys -> Map.get EK key state = Some old ->
      audit_ide_equal r (audit_ide_join r old incoming) old = false ->
      audit_ide_update EK r keys state key (Map.set EK key (audit_ide_join r old incoming) state).

(** The key sequence records actual successful updates, with each intermediate map retained. *)
Inductive audit_ide_update_trace {K A F} (EK : encoding K) (r : audit_ide_registry A F)
    (keys : list K) : Map.t K F -> list K -> Map.t K F -> Prop :=
  | AuditIdeTraceNil : forall state, audit_ide_update_trace EK r keys state [] state
  | AuditIdeTraceCons : forall state key next events final,
      audit_ide_update EK r keys state key next ->
      audit_ide_update_trace EK r keys next events final ->
      audit_ide_update_trace EK r keys state (key :: events) final.

(** Successful updates fit within the per-key rank bound. *)
Definition audit_ide_updates_bound_statement : Prop :=
  forall K A F (EK : encoding K) (L : lattice A) (r : audit_ide_registry A F) keys,
    audit_ide_registry_laws L r -> NoDup keys -> forall events final,
      audit_ide_update_trace EK r keys Map.empty events final ->
      length events <= length keys * S (audit_ide_bound r).

Definition audit_ide_summary_keys {N P D} (q : ip_problem N P D) : list (IpTab.fact N D) :=
  let vertices := IpTab.vertices q in
  map (@inl (IpTab.vertex N D * IpTab.vertex N D) (IpTab.vertex N D))
    (flat_map (fun v => map (fun w => (v,w)) vertices) vertices) ++
  map (@inr (IpTab.vertex N D * IpTab.vertex N D) (IpTab.vertex N D)) vertices.

(** Well-formed inputs yield distinct summary keys of the stated size. *)
Definition audit_ide_summary_keys_statement : Prop :=
  forall N P D (q : ip_problem N P D), ip_problem_wf q ->
    NoDup (audit_ide_summary_keys q) /\
    length (audit_ide_summary_keys q) =
      length (IpTab.vertices q) * length (IpTab.vertices q) + length (IpTab.vertices q).

(** A weighted arc stores one edge occurrence's kind, endpoints and transformer. *)
Record audit_ide_arc (N P D F : Type) : Type := AuditIdeArc {
  audit_ide_arc_kind : ip_kind P;
  audit_ide_arc_from : IpTab.vertex N D;
  audit_ide_arc_to : IpTab.vertex N D;
  audit_ide_arc_weight : F
}.

Arguments AuditIdeArc {N P D F}.

Arguments audit_ide_arc_kind {N P D F}.

Arguments audit_ide_arc_from {N P D F}.

Arguments audit_ide_arc_to {N P D F}.

Arguments audit_ide_arc_weight {N P D F}.

Definition audit_ide_arcs {N P D F} (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F) : list (audit_ide_arc N P D F) :=
  flat_map (fun e => map (fun xy => AuditIdeArc (ip_action e)
    (ip_source e, fst xy) (ip_target e, snd xy) (weight e (fst xy) (snd xy))) (ip_pairs e))
    (ip_edges q).

(** A ground rule seeds a key or derives one destination from one or two source keys. *)
Inductive audit_ide_rule (N D F : Type) : Type :=
  | AuditIdeSeed : IpTab.fact N D -> F -> audit_ide_rule N D F
  | AuditIdeUnary : IpTab.fact N D -> IpTab.fact N D -> F -> audit_ide_rule N D F
  | AuditIdeBinary : IpTab.fact N D -> IpTab.fact N D -> IpTab.fact N D -> F -> F -> audit_ide_rule
    N D F.

Arguments AuditIdeSeed {N D F}.

Arguments AuditIdeUnary {N D F}.

Arguments AuditIdeBinary {N D F}.

(** Ground rules describe root, identity, internal, matched-call, prefix and call cases. *)
Inductive audit_ide_generated_rule {N P D A F} (r : audit_ide_registry A F)
    (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F)
    (root : IpTab.vertex N D) : audit_ide_rule N D F -> Prop :=
  | AuditIdeGeneratedRoot : audit_ide_generated_rule r q weight root
      (AuditIdeSeed (inr root) (audit_ide_id r))
  | AuditIdeGeneratedIdentity : forall v, In v (IpTab.vertices q) ->
      audit_ide_generated_rule r q weight root (AuditIdeSeed (inl (v,v)) (audit_ide_id r))
  | AuditIdeGeneratedInternal : forall arc a, In arc (audit_ide_arcs q weight) ->
      audit_ide_arc_kind arc = IpInternal -> In a (IpTab.vertices q) ->
      audit_ide_generated_rule r q weight root (AuditIdeUnary
        (inl (a,audit_ide_arc_from arc)) (inl (a,audit_ide_arc_to arc)) (audit_ide_arc_weight arc))
  | AuditIdeGeneratedMatched : forall call ret site a,
      In call (audit_ide_arcs q weight) -> In ret (audit_ide_arcs q weight) ->
      audit_ide_arc_kind call = IpCall site -> audit_ide_arc_kind ret = IpReturn site ->
      In a (IpTab.vertices q) ->
      audit_ide_generated_rule r q weight root (AuditIdeBinary
        (inl (a,audit_ide_arc_from call)) (inl (audit_ide_arc_to call,audit_ide_arc_from ret))
        (inl (a,audit_ide_arc_to ret)) (audit_ide_arc_weight call) (audit_ide_arc_weight ret))
  | AuditIdeGeneratedPrefix : forall u v, In u (IpTab.vertices q) -> In v (IpTab.vertices q) ->
      audit_ide_generated_rule r q weight root (AuditIdeBinary (inr u) (inl (u,v)) (inr v)
        (audit_ide_id r) (audit_ide_id r))
  | AuditIdeGeneratedCall : forall call site, In call (audit_ide_arcs q weight) ->
      audit_ide_arc_kind call = IpCall site ->
      audit_ide_generated_rule r q weight root (AuditIdeUnary (inr (audit_ide_arc_from call))
        (inr (audit_ide_arc_to call)) (audit_ide_arc_weight call)).

Definition audit_ide_rule_result {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (state : Map.t (IpTab.fact N D) F)
    (rule : audit_ide_rule N D F) : option (IpTab.fact N D * F) :=
  let key := IpTab.fact_encoding EN ED in
  match rule with
  | AuditIdeSeed dst value => Some (dst,value)
  | AuditIdeUnary source dst suffix =>
    option_map (fun value => (dst,audit_ide_compose r value suffix)) (Map.get key source state)
  | AuditIdeBinary first second dst between after =>
    match Map.get key first state, Map.get key second state with
    | Some x, Some y => Some (dst,audit_ide_compose r
        (audit_ide_compose r (audit_ide_compose r x between) y) after)
    | _, _ => None
    end
  end.

(** Every enabled contribution joins into an existing value without changing it. *)
Definition audit_ide_rules_closed {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (rules : audit_ide_rule N D F -> Prop)
    (state : Map.t (IpTab.fact N D) F) : Prop :=
  forall rule dst contribution, rules rule ->
    audit_ide_rule_result EN ED r state rule = Some (dst,contribution) ->
    exists old, Map.get (IpTab.fact_encoding EN ED) dst state = Some old /\
      audit_ide_equal r (audit_ide_join r old contribution) old = true.

Definition audit_ide_rule_keys {N D F} (rule : audit_ide_rule N D F) : list (IpTab.fact N D) :=
  match rule with
  | AuditIdeSeed dst _ => [dst]
  | AuditIdeUnary source dst _ => [source;dst]
  | AuditIdeBinary first second dst _ _ => [first;second;dst]
  end.

(** Generated rules refer only to keys in the finite summary universe. *)
Definition audit_ide_rule_universe_statement : Prop :=
  forall N P D A F (r : audit_ide_registry A F)
    (q : ip_problem N P D) weight start seed,
    ip_problem_wf q -> In start (ip_nodes q) ->
    (match seed with
    | None => True
    | Some d => In d (ip_facts q)
    end) ->
    forall rule key, audit_ide_generated_rule r q weight (start,seed) rule ->
      In key (audit_ide_rule_keys rule) -> In key (audit_ide_summary_keys q).

(** A derived update inserts or strictly grows an allowed rule's destination key. *)
Inductive audit_ide_derived_update {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (allowed : audit_ide_rule N D F -> Prop)
    (keys : list (IpTab.fact N D)) :
    Map.t (IpTab.fact N D) F -> audit_ide_rule N D F -> IpTab.fact N D ->
    Map.t (IpTab.fact N D) F -> Prop :=
  | AuditIdeDerivedFirst : forall state rule key incoming,
      allowed rule -> In key keys -> audit_ide_rule_result EN ED r state rule = Some (key,incoming)
        ->
      Map.get (IpTab.fact_encoding EN ED) key state = None ->
      audit_ide_derived_update EN ED r allowed keys state rule key
        (Map.set (IpTab.fact_encoding EN ED) key incoming state)
  | AuditIdeDerivedGrow : forall state rule key incoming old,
      allowed rule -> In key keys -> audit_ide_rule_result EN ED r state rule = Some (key,incoming)
        ->
      Map.get (IpTab.fact_encoding EN ED) key state = Some old ->
      audit_ide_equal r (audit_ide_join r old incoming) old = false ->
      audit_ide_derived_update EN ED r allowed keys state rule key
        (Map.set (IpTab.fact_encoding EN ED) key (audit_ide_join r old incoming) state).

(** The trace links each derived rule and key to its successive map states. *)
Inductive audit_ide_derived_trace {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (allowed : audit_ide_rule N D F -> Prop)
    (keys : list (IpTab.fact N D)) : Map.t (IpTab.fact N D) F ->
    list (audit_ide_rule N D F * IpTab.fact N D) -> Map.t (IpTab.fact N D) F -> Prop :=
  | AuditIdeDerivedNil : forall state, audit_ide_derived_trace EN ED r allowed keys state [] state
  | AuditIdeDerivedCons : forall state rule key next events final,
      audit_ide_derived_update EN ED r allowed keys state rule key next ->
      audit_ide_derived_trace EN ED r allowed keys next events final ->
      audit_ide_derived_trace EN ED r allowed keys state ((rule,key) :: events) final.

(** Derived updates fit within the per-key rank bound. *)
Definition audit_ide_derived_bound_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (L : lattice A)
    (r : audit_ide_registry A F) allowed keys,
    audit_ide_registry_laws L r -> NoDup keys -> forall events final,
    audit_ide_derived_trace EN ED r allowed keys Map.empty events final ->
    length events <= length keys * S (audit_ide_bound r).

(** A probe records the rule, optional destination and whether its value changed or existed. *)
Record audit_ide_probe (N D F : Type) : Type := AuditIdeProbe {
  audit_ide_probe_rule : audit_ide_rule N D F;
  audit_ide_probe_key : option (IpTab.fact N D);
  audit_ide_probe_changed : bool;
  audit_ide_probe_existing : bool
}.

Arguments AuditIdeProbe {N D F}.

Arguments audit_ide_probe_rule {N D F}.

Arguments audit_ide_probe_key {N D F}.

Arguments audit_ide_probe_changed {N D F}.

Arguments audit_ide_probe_existing {N D F}.

(** A probe records disabled, stable, first-insertion or growing rule evaluation. *)
Inductive audit_ide_probe_step {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (allowed : audit_ide_rule N D F -> Prop)
    (keys : list (IpTab.fact N D)) : Map.t (IpTab.fact N D) F -> audit_ide_probe N D F ->
    Map.t (IpTab.fact N D) F -> Prop :=
  | AuditIdeProbeDisabled : forall state rule,
      allowed rule -> audit_ide_rule_result EN ED r state rule = None ->
      audit_ide_probe_step EN ED r allowed keys state (AuditIdeProbe rule None false false) state
  | AuditIdeProbeStable : forall state rule key incoming old,
      allowed rule -> In key keys -> audit_ide_rule_result EN ED r state rule = Some (key,incoming)
        ->
      Map.get (IpTab.fact_encoding EN ED) key state = Some old ->
      audit_ide_equal r (audit_ide_join r old incoming) old = true ->
      audit_ide_probe_step EN ED r allowed keys state (AuditIdeProbe rule (Some key) false true)
        state
  | AuditIdeProbeFirst : forall state rule key incoming,
      allowed rule -> In key keys -> audit_ide_rule_result EN ED r state rule = Some (key,incoming)
        ->
      Map.get (IpTab.fact_encoding EN ED) key state = None ->
      audit_ide_probe_step EN ED r allowed keys state (AuditIdeProbe rule (Some key) true false)
        (Map.set (IpTab.fact_encoding EN ED) key incoming state)
  | AuditIdeProbeGrow : forall state rule key incoming old,
      allowed rule -> In key keys -> audit_ide_rule_result EN ED r state rule = Some (key,incoming)
        ->
      Map.get (IpTab.fact_encoding EN ED) key state = Some old ->
      audit_ide_equal r (audit_ide_join r old incoming) old = false ->
      audit_ide_probe_step EN ED r allowed keys state (AuditIdeProbe rule (Some key) true true)
        (Map.set (IpTab.fact_encoding EN ED) key (audit_ide_join r old incoming) state).

(** A probe trace retains every intermediate state, including unchanged steps. *)
Inductive audit_ide_probe_trace {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (allowed : audit_ide_rule N D F -> Prop)
    (keys : list (IpTab.fact N D)) : Map.t (IpTab.fact N D) F -> list (audit_ide_probe N D F) ->
    Map.t (IpTab.fact N D) F -> Prop :=
  | AuditIdeProbeNil : forall state, audit_ide_probe_trace EN ED r allowed keys state [] state
  | AuditIdeProbeCons : forall state event next events final,
      audit_ide_probe_step EN ED r allowed keys state event next ->
      audit_ide_probe_trace EN ED r allowed keys next events final ->
      audit_ide_probe_trace EN ED r allowed keys state (event :: events) final.

Definition audit_ide_probe_updates {N D F} (events : list (audit_ide_probe N D F))
    : list (audit_ide_rule N D F * IpTab.fact N D) :=
  flat_map (fun event => match audit_ide_probe_key event, audit_ide_probe_changed event with
    | Some key, true => [(audit_ide_probe_rule event,key)]
    | _, _ => []
    end) events.

Definition audit_ide_probe_join_count {N D F} (events : list (audit_ide_probe N D F)) : nat :=
  fold_right (fun event n => if audit_ide_probe_existing event then S n else n) 0 events.

Definition audit_ide_probe_compose_count {N D F} (events : list (audit_ide_probe N D F)) : nat :=
  fold_right (fun event n => match audit_ide_probe_key event, audit_ide_probe_rule event with
    | None, _ => n
    | Some _, AuditIdeSeed _ _ => n
    | Some _, AuditIdeUnary _ _ _ => S n
    | Some _, AuditIdeBinary _ _ _ _ _ => 3 + n
    end) 0 events.

(** Probes project to updates and bound join and composition counts. *)
Definition audit_ide_probe_projection_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) allowed keys
    state events final,
    audit_ide_probe_trace EN ED r allowed keys state events final ->
    audit_ide_derived_trace EN ED r allowed keys state (audit_ide_probe_updates events) final /\
    length (audit_ide_probe_updates events) <= length events /\
    audit_ide_probe_join_count events <= length events /\
    audit_ide_probe_compose_count events <= 3 * length events.

Definition audit_ide_rule_sources {N D F} (rule : audit_ide_rule N D F) : list (IpTab.fact N D) :=
  match rule with
  | AuditIdeSeed _ _ => []
  | AuditIdeUnary source _ _ => [source]
  | AuditIdeBinary first second _ _ _ => [first;second]
  end.

Definition audit_ide_rule_table {N D F} (rules : list (audit_ide_rule N D F)) : Map.t nat
  (audit_ide_rule N D F) :=
  Map.of_list nat_encoding (combine (seq 0 (length rules)) rules).

Definition audit_ide_rule_incidence {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) : Map.t (IpTab.fact N D) (list nat) :=
  fold_right (fun row index => index_push_many (IpTab.fact_encoding EN ED) (fst row)
    (audit_ide_rule_sources (snd row)) index) Map.empty (combine (seq 0 (length rules)) rules).

Definition audit_ide_enqueue (ids : list nat) (pending : list nat) (queued : FinSet.t nat)
    : list nat * FinSet.t nat :=
  fold_left (fun state id => let '(todo,seen) := state in
    if FinSet.mem nat_encoding id seen then state
    else (id :: todo, FinSet.add nat_encoding id seen)) ids (pending,queued).

(** The scheduler keeps indexed rules, pending IDs, values and its reverse probe history. *)
Record audit_ide_machine (N D F : Type) : Type := AuditIdeMachine {
  audit_ide_machine_rules : list (audit_ide_rule N D F);
  audit_ide_machine_table : Map.t nat (audit_ide_rule N D F);
  audit_ide_machine_incidence : Map.t (IpTab.fact N D) (list nat);
  audit_ide_machine_pending : list nat;
  audit_ide_machine_queued : FinSet.t nat;
  audit_ide_machine_values : Map.t (IpTab.fact N D) F;
  audit_ide_machine_probes_rev : list (audit_ide_probe N D F)
}.

Arguments AuditIdeMachine {N D F}.

Arguments audit_ide_machine_rules {N D F}.

Arguments audit_ide_machine_table {N D F}.

Arguments audit_ide_machine_incidence {N D F}.

Arguments audit_ide_machine_pending {N D F}.

Arguments audit_ide_machine_queued {N D F}.

Arguments audit_ide_machine_values {N D F}.

Arguments audit_ide_machine_probes_rev {N D F}.

Definition audit_ide_machine_initial {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) : audit_ide_machine N D F :=
  let ids := seq 0 (length rules) in
  AuditIdeMachine rules (audit_ide_rule_table rules) (audit_ide_rule_incidence EN ED rules)
    ids (FinSet.of_list nat_encoding ids) Map.empty [].

(** The machine's maps and queue are well formed and agree with its rules and pending IDs. *)
Definition audit_ide_machine_valid {N D F} (EN : encoding N) (ED : encoding D)
    (st : audit_ide_machine N D F) : Prop :=
  Map.wf nat_encoding (audit_ide_machine_table st) /\
  Map.wf (IpTab.fact_encoding EN ED) (audit_ide_machine_incidence st) /\
  Map.wf (IpTab.fact_encoding EN ED) (audit_ide_machine_values st) /\
  FinSet.wf nat_encoding (audit_ide_machine_queued st) /\
  NoDup (audit_ide_machine_pending st) /\
  (forall id, Map.get nat_encoding id (audit_ide_machine_table st) = nth_error
    (audit_ide_machine_rules st) id) /\
  (forall key id, In id (match Map.get (IpTab.fact_encoding EN ED) key (audit_ide_machine_incidence
    st) with
    | Some ids => ids
    | None => []
    end) <->
    exists rule, nth_error (audit_ide_machine_rules st) id = Some rule /\ In key
      (audit_ide_rule_sources rule)) /\
  (forall id, FinSet.mem nat_encoding id (audit_ide_machine_queued st) = true <->
    In id (audit_ide_machine_pending st)) /\
  forall id, In id (audit_ide_machine_pending st) -> id < length (audit_ide_machine_rules st).

(** A probe updates one key and schedules only the indexed dependents of a strict change. *)
Definition audit_ide_machine_step {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (st : audit_ide_machine N D F) : option (audit_ide_machine N D F)
      :=
  match audit_ide_machine_pending st with
  | [] => None
  | id :: rest =>
    let queued := FinSet.remove nat_encoding id (audit_ide_machine_queued st) in
    match Map.get nat_encoding id (audit_ide_machine_table st) with
    | None => Some (AuditIdeMachine (audit_ide_machine_rules st) (audit_ide_machine_table st)
        (audit_ide_machine_incidence st) rest queued (audit_ide_machine_values st)
        (audit_ide_machine_probes_rev st))
    | Some rule =>
      let key := IpTab.fact_encoding EN ED in
      let values := audit_ide_machine_values st in
      let '(next_values,event) := match audit_ide_rule_result EN ED r values rule with
        | None => (values,AuditIdeProbe rule None false false)
        | Some (dst,incoming) => match Map.get key dst values with
          | None => (Map.set key dst incoming values,AuditIdeProbe rule (Some dst) true false)
          | Some old => let joined := audit_ide_join r old incoming in
            if audit_ide_equal r joined old then (values,AuditIdeProbe rule (Some dst) false true)
            else (Map.set key dst joined values,AuditIdeProbe rule (Some dst) true true)
          end
        end in
      let '(todo,seen) := match audit_ide_probe_key event, audit_ide_probe_changed event with
        | Some dst, true => audit_ide_enqueue
            (match Map.get key dst (audit_ide_machine_incidence st) with
            | Some ids => ids
            | None => []
            end)
            rest queued
        | _, _ => (rest,queued)
        end in
      Some (AuditIdeMachine (audit_ide_machine_rules st) (audit_ide_machine_table st)
        (audit_ide_machine_incidence st) todo seen next_values (event ::
          audit_ide_machine_probes_rev st))
    end
  end.

(** Every key referenced by a stored rule belongs to the supplied finite key list. *)
Definition audit_ide_machine_keys_valid {N D F} (keys : list (IpTab.fact N D))
    (st : audit_ide_machine N D F) : Prop :=
  forall rule key, In rule (audit_ide_machine_rules st) -> In key (audit_ide_rule_keys rule) -> In
    key keys.

(** Initialization establishes the machine invariant. *)
Definition audit_ide_machine_initial_statement : Prop :=
  forall N D F (EN : encoding N) (ED : encoding D) (rules : list (audit_ide_rule N D F)),
    audit_ide_machine_valid EN ED (audit_ide_machine_initial EN ED rules).

(** A successful step preserves invariants and records its probe. *)
Definition audit_ide_machine_step_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) keys st next,
    audit_ide_machine_valid EN ED st -> audit_ide_machine_keys_valid keys st ->
    audit_ide_machine_step EN ED r st = Some next ->
    audit_ide_machine_valid EN ED next /\ audit_ide_machine_keys_valid keys next /\
    exists event, audit_ide_machine_probes_rev next = event :: audit_ide_machine_probes_rev st /\
      audit_ide_probe_step EN ED r (fun rule => In rule (audit_ide_machine_rules st)) keys
        (audit_ide_machine_values st) event (audit_ide_machine_values next).

(** Reachability is the reflexive transitive closure of successful machine steps. *)
Inductive audit_ide_machine_reaches {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) : audit_ide_machine N D F -> audit_ide_machine N D F -> Prop :=
  | AuditIdeMachineRefl : forall state, audit_ide_machine_reaches EN ED r state state
  | AuditIdeMachineNext : forall first current next,
      audit_ide_machine_reaches EN ED r first current ->
      audit_ide_machine_step EN ED r current = Some next ->
      audit_ide_machine_reaches EN ED r first next.

(** A reachable machine with no pending work has closed rules. *)
Definition audit_ide_machine_closed_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (L : lattice A) (r : audit_ide_registry A F)
    (rules : list (audit_ide_rule N D F)) final,
    audit_ide_registry_laws L r ->
    audit_ide_machine_reaches EN ED r (audit_ide_machine_initial EN ED rules) final ->
    audit_ide_machine_pending final = [] ->
    audit_ide_rules_closed EN ED r (fun rule => In rule rules) (audit_ide_machine_values final).

Definition audit_ide_machine_fuel {N D A F} (r : audit_ide_registry A F)
    (keys : list (IpTab.fact N D)) (rules : list (audit_ide_rule N D F)) : positive :=
  N.succ_pos (N.of_nat (length rules) *
    (1 + 2 * N.of_nat (length keys) * N.of_nat (S (audit_ide_bound r))))%N.

Fixpoint audit_ide_machine_loop {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (fuel : positive) (st : audit_ide_machine N D F)
    : audit_ide_machine N D F :=
  match audit_ide_machine_pending st with
  | [] => st
  | _ => match fuel with
    | xH => match audit_ide_machine_step EN ED r st with
      | Some next => next
      | None => st
      end
    | xO p => audit_ide_machine_loop EN ED r p (audit_ide_machine_loop EN ED r p st)
    | xI p => let mid := audit_ide_machine_loop EN ED r p (audit_ide_machine_loop EN ED r p st) in
      match audit_ide_machine_step EN ED r mid with
      | Some next => next
      | None => mid
      end
    end
  end.

(** Under registry laws, distinct keys and initial key closure, the calculated fuel empties the
    pending queue. *)
Definition audit_ide_machine_terminates_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (L : lattice A) (r : audit_ide_registry A F)
    (keys : list (IpTab.fact N D)) (rules : list (audit_ide_rule N D F)),
    audit_ide_registry_laws L r -> NoDup keys ->
    audit_ide_machine_keys_valid keys (audit_ide_machine_initial EN ED rules) ->
    audit_ide_machine_pending (audit_ide_machine_loop EN ED r (audit_ide_machine_fuel r keys rules)
      (audit_ide_machine_initial EN ED rules)) = [].

Section Candidate.

  Context {N P D A F : Type} (L : lattice A) (r : audit_ide_registry A F)
    (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F).

  (** A path follows graph steps while applying each edge's registered transformer. *)
  Inductive audit_ide_path : N * option D * list P -> A -> N * option D * list P -> A -> Prop :=
    | audit_ide_path_refl : forall c a, audit_ide_path c a c a
    | audit_ide_path_step : forall n x stack e n' y stack' a c b,
        ip_step q (n, x, stack) e (n', y, stack') ->
        audit_ide_path (n', y, stack') (audit_ide_eval r (weight e x y) a) c b ->
        audit_ide_path (n, x, stack) a c b.

  Variable solve : N -> option D -> A -> N -> option D -> option A.

  (** The proposed query returns exactly reachable path joins. *)
  Definition audit_ide_path_exact_statement : Prop :=
    audit_ide_registry_laws L r -> ip_problem_wf q ->
    forall start seed a, In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      forall n d,
      (solve start seed a n d = None <->
        ~ exists stack b, audit_ide_path (start, seed, nil) a (n, d, stack) b) /\
      (forall result, solve start seed a n d = Some result ->
        (exists stack b, audit_ide_path (start, seed, nil) a (n, d, stack) b) /\
        (forall stack b, audit_ide_path (start, seed, nil) a (n, d, stack) b ->
          OrderLattice.leb L b result = true) /\
        (forall upper, (forall stack b,
          audit_ide_path (start, seed, nil) a (n, d, stack) b -> OrderLattice.leb L b upper = true)
            ->
          OrderLattice.leb L result upper = true)).

  (** A compatible finite backend agrees with the proposed query. *)
  Definition audit_ide_finite_agreement_statement (EA : encoding A)
      (old : ide_problem N P D A) : Prop :=
    ide_laws old -> audit_ide_registry_laws L r ->
    ide_graph old = q -> ide_lattice old = L ->
    (forall e x y a, In e (ip_edges q) -> In (x, y) (ip_pairs e) ->
      equivalent L (audit_ide_eval r (weight e x y) a) (ide_weight old e x y a)) ->
    forall (EN : encoding N) (EP : encoding P) (ED : encoding D) start seed a,
      In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      forall n d,
        equivalent L
          (match solve start seed a n d with
          | Some result => result
          | None => bot L
          end)
          (ide_solve EN EP ED EA old start seed a n d).

End Candidate.

(** A summary stores a result map alongside update, event and probe lists. *)
Record audit_ide_summary (N D F : Type) : Type := AuditIdeSummary {
  audit_ide_summary_map : Map.t (IpTab.fact N D) F;
  audit_ide_summary_updates : list (IpTab.fact N D);
  audit_ide_summary_events : list (audit_ide_rule N D F * IpTab.fact N D);
  audit_ide_summary_probes : list (audit_ide_probe N D F)
}.

Arguments AuditIdeSummary {N D F}.

Arguments audit_ide_summary_map {N D F}.

Arguments audit_ide_summary_updates {N D F}.

Arguments audit_ide_summary_events {N D F}.

Arguments audit_ide_summary_probes {N D F}.

Definition audit_ide_arc_count {N P D} (q : ip_problem N P D) : nat :=
  fold_right (fun e n => length (ip_pairs e) + n) 0 (ip_edges q).

(** A deliberately coarse finite rule and incidence budget; it does not enumerate F or A. *)
Definition audit_ide_rule_budget {N P D} (q : ip_problem N P D) : nat :=
  let v := S (length (IpTab.vertices q)) in
  let a := S (audit_ide_arc_count q) in
  4 * v * v * v * a * a.

Section RuleGenerator.

  Variable generate : forall N P D A F, encoding P -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> IpTab.vertex N D -> list (audit_ide_rule N D F).

  (** The proposed generator lists exactly the ground rules within budget. *)
  Definition audit_ide_rule_generator_statement : Prop :=
    forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
      (q : ip_problem N P D) weight root,
      let rules := generate N P D A F EP r q weight root in
      length rules <= audit_ide_rule_budget q /\
      forall rule, In rule rules <-> audit_ide_generated_rule r q weight root rule.

End RuleGenerator.

Definition audit_ide_summary_query {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (summary : audit_ide_summary N D F)
    (initial : A) (n : N) (d : option D) : option A :=
  option_map (fun f => audit_ide_eval r f initial)
    (Map.get (IpTab.fact_encoding EN ED) (inr (n,d)) (audit_ide_summary_map summary)).

Section ExecutableContract.

  Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (L : lattice A) (r : audit_ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F).

  Variable execute : encoding N -> encoding P -> encoding D -> lattice A ->
    audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) ->
    N -> option D -> audit_ide_summary N D F.

  (** Execution retains a valid trace of generated-rule updates. *)
  Definition audit_ide_execute_trace_statement : Prop :=
    audit_ide_registry_laws L r -> ip_problem_wf q ->
    forall start seed, In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      let result := execute EN EP ED L r q weight start seed in
      Map.wf (IpTab.fact_encoding EN ED) (audit_ide_summary_map result) /\
      audit_ide_probe_trace EN ED r (audit_ide_generated_rule r q weight (start,seed))
        (audit_ide_summary_keys q) Map.empty (audit_ide_summary_probes result)
          (audit_ide_summary_map result) /\
      audit_ide_probe_updates (audit_ide_summary_probes result) = audit_ide_summary_events result /\
      audit_ide_derived_trace EN ED r (audit_ide_generated_rule r q weight (start,seed))
        (audit_ide_summary_keys q) Map.empty (audit_ide_summary_events result)
          (audit_ide_summary_map result) /\
      map snd (audit_ide_summary_events result) = audit_ide_summary_updates result /\
      length (audit_ide_summary_updates result) <=
        length (audit_ide_summary_keys q) * S (audit_ide_bound r).

  (** Execution gives the exact path query under the stated laws. *)
  Definition audit_ide_execute_exact_statement : Prop :=
    @audit_ide_path_exact_statement N P D A F L r q weight
      (fun start seed a n d => audit_ide_summary_query EN ED r (execute EN EP ED L r q weight start
        seed) a n d).

  (** Execution returns a state closed under generated rules. *)
  Definition audit_ide_execute_closed_statement : Prop :=
    audit_ide_registry_laws L r -> ip_problem_wf q ->
    forall start seed, In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      audit_ide_rules_closed EN ED r (audit_ide_generated_rule r q weight (start,seed))
        (audit_ide_summary_map (execute EN EP ED L r q weight start seed)).

  (** Execution agrees with the compatible finite backend. *)
  Definition audit_ide_execute_finite_statement (EA : encoding A)
      (old : ide_problem N P D A) : Prop :=
    @audit_ide_finite_agreement_statement N P D A F L r q weight
      (fun start seed a n d => audit_ide_summary_query EN ED r (execute EN EP ED L r q weight start
        seed) a n d) EA old.

End ExecutableContract.

Definition audit_ide_nat_lattice : lattice nat :=
  {| OrderLattice.leb := Nat.leb;
    bot := 0;
    join := Nat.max;
    widen := Nat.max;
    narrow := fun x _ => x |}.

Definition audit_ide_nat_registry : audit_ide_registry nat bool :=
  {| audit_ide_eval := fun (f : bool) (x : nat) => if f then Nat.max x 1 else x;
    audit_ide_id := false;
    audit_ide_compose := orb;
    audit_ide_join := orb;
    audit_ide_equal := Bool.eqb;
    audit_ide_rank := fun (f : bool) => if f then 1 else 0;
    audit_ide_bound := 1 |}.

(** The natural-number instance satisfies the registry laws. *)
Definition audit_ide_nat_laws_statement : Prop :=
  audit_ide_registry_laws audit_ide_nat_lattice audit_ide_nat_registry.

(** No finite list enumerates the natural-number carrier. *)
Definition audit_ide_nat_nonfinite_statement : Prop :=
  forall xs : list nat, exists n, ~ In n xs.

(** This carrier is not countably enumerable. Its preorder observes only bit zero. *)
Definition audit_ide_stream := nat -> bool.

Definition audit_ide_stream_join (a b : audit_ide_stream) : audit_ide_stream :=
  fun i => orb (a i) (b i).

Definition audit_ide_stream_lattice : lattice audit_ide_stream :=
  {| OrderLattice.leb := fun a b => implb (a 0) (b 0);
    bot := fun _ => false;
    join := audit_ide_stream_join;
    widen := audit_ide_stream_join;
    narrow := fun a _ => a |}.

Definition audit_ide_stream_registry : audit_ide_registry audit_ide_stream bool :=
  {| audit_ide_eval := fun (f : bool) (a : audit_ide_stream) i =>
        if Nat.eqb i 0 then orb (a i) f else a i;
    audit_ide_id := false;
    audit_ide_compose := orb;
    audit_ide_join := orb;
    audit_ide_equal := Bool.eqb;
    audit_ide_rank := fun (f : bool) => if f then 1 else 0;
    audit_ide_bound := 1 |}.

(** The stream instance satisfies the registry laws. *)
Definition audit_ide_stream_laws_statement : Prop :=
  audit_ide_registry_laws audit_ide_stream_lattice audit_ide_stream_registry.

(** A diagonal stream differs from every stream in an enumeration. *)
Definition audit_ide_stream_uncountable_statement : Prop :=
  forall enumerate : nat -> audit_ide_stream,
    exists diagonal : audit_ide_stream, forall n, diagonal <> enumerate n.

(** The stream order distinguishes the two constant observations. *)
Definition audit_ide_stream_two_observations_statement : Prop :=
  OrderLattice.leb audit_ide_stream_lattice (fun _ => false) (fun _ => true) = true /\
  OrderLattice.leb audit_ide_stream_lattice (fun _ => true) (fun _ => false) = false.

Definition audit_ide_stream_graph : ip_problem nat nat unit :=
  IpProblem [0; 1; 2; 3] [0; 1] []
    [IpEdge 0 1 (IpCall 0) [(None, None)];
      IpEdge 1 2 (IpReturn 0) [(None, None)];
      IpEdge 1 3 (IpReturn 1) [(None, None)]].

Definition audit_ide_stream_weight (e : ip_edge nat nat unit)
    (_ _ : option unit) : bool :=
  match ip_action e with
  | IpReturn _ => true
  | _ => false
  end.

(** The stream query distinguishes matching from mismatched returns. *)
Definition audit_ide_stream_consumer_statement
    (execute : encoding nat -> encoding nat -> encoding unit -> lattice audit_ide_stream ->
      audit_ide_registry audit_ide_stream bool -> ip_problem nat nat unit ->
      (ip_edge nat nat unit -> option unit -> option unit -> bool) ->
      nat -> option unit -> audit_ide_summary nat unit bool) : Prop :=
  let result := execute nat_encoding nat_encoding unit_encoding audit_ide_stream_lattice
    audit_ide_stream_registry audit_ide_stream_graph audit_ide_stream_weight 0 None in
  let query := audit_ide_summary_query nat_encoding unit_encoding audit_ide_stream_registry
    result (fun i => Nat.eqb i 2) in
  (exists before, query 1 None = Some before /\ before 0 = false) /\
  (exists after, query 2 None = Some after /\ after 0 = true /\ after 2 = true) /\
  query 3 None = None.

(** Literal bottom is reached, while the mismatched-return target stays absent. *)
Definition audit_ide_stream_bottom_statement
    (execute : encoding nat -> encoding nat -> encoding unit -> lattice audit_ide_stream ->
      audit_ide_registry audit_ide_stream bool -> ip_problem nat nat unit ->
      (ip_edge nat nat unit -> option unit -> option unit -> bool) ->
      nat -> option unit -> audit_ide_summary nat unit bool) : Prop :=
  let result := execute nat_encoding nat_encoding unit_encoding audit_ide_stream_lattice
    audit_ide_stream_registry audit_ide_stream_graph audit_ide_stream_weight 0 None in
  let query := audit_ide_summary_query nat_encoding unit_encoding audit_ide_stream_registry
    result (bot audit_ide_stream_lattice) in
  (exists value, query 1 None = Some value /\ forall i, value i = false) /\
  query 3 None = None.

Section MachineConsumerContract.

  Variable generate : forall N P D A F, encoding P -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> IpTab.vertex N D -> list (audit_ide_rule N D F).

  Variable execute : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> audit_ide_summary N D F.

  (** Exact observation of the same generated-rule machine, including unsuccessful probes. *)
  Definition audit_ide_machine_consumer_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : audit_ide_registry A F) (q : ip_problem N P D) weight start seed,
      audit_ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      let rules := generate N P D A F EP r q weight (start,seed) in
      let keys := audit_ide_summary_keys q in
      let final := audit_ide_machine_loop EN ED r (audit_ide_machine_fuel r keys rules)
        (audit_ide_machine_initial EN ED rules) in
      let result := execute EN EP ED L r q weight start seed in
      audit_ide_summary_map result = audit_ide_machine_values final /\
      audit_ide_summary_probes result = rev (audit_ide_machine_probes_rev final).

End MachineConsumerContract.

(** A query's encoded key may be larger than every key in the input graph. *)
Definition audit_ide_query_key_bits {N D} (EN : encoding N) (ED : encoding D)
    (n : N) (d : option D) : nat :=
  Pos.size_nat (encode (IpTab.fact_encoding EN ED) (inr (n, d))).

(** The value callback is called exactly once on a present summary key. *)
Definition audit_ide_query_eval_calls {N D F} (EN : encoding N) (ED : encoding D)
    (summary : audit_ide_summary N D F) (n : N) (d : option D) : nat :=
  match Map.get (IpTab.fact_encoding EN ED) (inr (n, d))
      (audit_ide_summary_map summary) with
  | Some _ => 1
  | None => 0
  end.

(** At most one evaluation is counted, and zero calls coincide with an absent query result. *)
Definition audit_ide_query_cost_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F)
    (summary : audit_ide_summary N D F) (initial : A) n d,
    audit_ide_query_eval_calls EN ED summary n d <= 1 /\
    (audit_ide_query_eval_calls EN ED summary n d = 0 <->
      audit_ide_summary_query EN ED r summary initial n d = None).

(** A mathematical size specification; implementation uses site buckets, not this scan. *)
Definition audit_ide_internal_occurrences {N P D} (q : ip_problem N P D) : nat :=
  fold_right (fun e n => match ip_action e with
    | IpInternal => length (ip_pairs e) + n
    | _ => n
    end) 0 (ip_edges q).

Definition audit_ide_call_occurrences {N P D} (q : ip_problem N P D) : nat :=
  fold_right (fun e n => match ip_action e with
    | IpCall _ => length (ip_pairs e) + n
    | _ => n
    end) 0 (ip_edges q).

Definition audit_ide_matching_occurrences {N P D} (EP : encoding P)
    (q : ip_problem N P D) : nat :=
  fold_right (fun call n => match ip_action call with
    | IpCall site => length (ip_pairs call) *
        fold_right (fun ret m => match ip_action ret with
          | IpReturn site' => if Pos.eqb (encode EP site) (encode EP site')
              then length (ip_pairs ret) + m else m
          | _ => m
          end) 0 (ip_edges q) + n
    | _ => n
    end) 0 (ip_edges q).

Definition audit_ide_occurrence_rule_count {N P D} (EP : encoding P)
    (q : ip_problem N P D) : nat :=
  let v := length (IpTab.vertices q) in
  1 + v + audit_ide_internal_occurrences q * v + audit_ide_matching_occurrences EP q * v +
    v * v + audit_ide_call_occurrences q.

Section OccurrenceGenerator.

  Variable generate : forall N P D A F, encoding P -> audit_ide_registry A F ->
    ip_problem N P D -> (ip_edge N P D -> option D -> option D -> F) ->
    IpTab.vertex N D -> list (audit_ide_rule N D F).

  (** The generator emits the number of rows in the occurrence-counting specification. *)
  Definition audit_ide_generator_occurrences_statement : Prop :=
    forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
      (q : ip_problem N P D) weight root,
      length (generate N P D A F EP r q weight root) = audit_ide_occurrence_rule_count EP q.

End OccurrenceGenerator.

(** Each changed probe visits the complete indexed incidence bucket, including queued IDs. *)
Definition audit_ide_incidence_visits {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) (events : list (audit_ide_probe N D F)) : nat :=
  let index := audit_ide_rule_incidence EN ED rules in
  fold_right (fun event total =>
    match audit_ide_probe_key event, audit_ide_probe_changed event with
    | Some key, true =>
      length (match Map.get (IpTab.fact_encoding EN ED) key index with
        | Some ids => ids
        | None => []
        end) + total
    | _, _ => total
    end) 0 events.

(** Incidence visits are bounded by two source occurrences per rule per changed probe. *)
Definition audit_ide_incidence_visits_bound_statement : Prop :=
  forall N D F (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) events,
    audit_ide_incidence_visits EN ED rules events <=
      2 * length rules * length (audit_ide_probe_updates events).

(** A trace contains the actual before and after state of each scheduler step. *)
Inductive audit_ide_machine_trace {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) : audit_ide_machine N D F ->
    list (audit_ide_machine N D F * audit_ide_machine N D F) ->
    audit_ide_machine N D F -> Prop :=
  | AuditIdeMachineTraceNil : forall state,
      audit_ide_machine_trace EN ED r state [] state
  | AuditIdeMachineTraceCons : forall state next transitions final,
      audit_ide_machine_step EN ED r state = Some next ->
      audit_ide_machine_trace EN ED r next transitions final ->
      audit_ide_machine_trace EN ED r state ((state, next) :: transitions) final.

(** A transition counts the prior incidence bucket selected by the latest changed probe. *)
Definition audit_ide_transition_incidence_visits {N D F} (EN : encoding N) (ED : encoding D)
    (transition : audit_ide_machine N D F * audit_ide_machine N D F) : nat :=
  let '(before, after) := transition in
  match audit_ide_machine_probes_rev after with
  | event :: _ => match audit_ide_probe_key event, audit_ide_probe_changed event with
    | Some key, true => length (match Map.get (IpTab.fact_encoding EN ED) key
        (audit_ide_machine_incidence before) with
      | Some ids => ids
      | None => []
      end)
    | _, _ => 0
    end
  | [] => 0
  end.

(** Transition visits equal the visits recorded by final probes. *)
Definition audit_ide_machine_incidence_correspondence_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F)
    (rules : list (audit_ide_rule N D F)) transitions final,
    audit_ide_machine_trace EN ED r (audit_ide_machine_initial EN ED rules) transitions final ->
    fold_right (fun transition n => audit_ide_transition_incidence_visits EN ED transition + n)
      0 transitions =
    audit_ide_incidence_visits EN ED rules (rev (audit_ide_machine_probes_rev final)).

(** The binary runner is a finite trace of the scheduler's own transition function. *)
Definition audit_ide_machine_loop_trace_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F)
    (rules : list (audit_ide_rule N D F)) fuel,
    let initial := audit_ide_machine_initial EN ED rules in
    let final := audit_ide_machine_loop EN ED r fuel initial in
    exists transitions, audit_ide_machine_trace EN ED r initial transitions final /\
      length transitions = length (audit_ide_machine_probes_rev final).

Section IncidenceConsumer.

  Variable generate : forall N P D A F, encoding P -> audit_ide_registry A F ->
    ip_problem N P D -> (ip_edge N P D -> option D -> option D -> F) ->
    IpTab.vertex N D -> list (audit_ide_rule N D F).

  Variable execute : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> audit_ide_summary N D F.

  (** Charges the indexed dependency-list visits of the actual returned probe sequence. *)
  Definition audit_ide_public_incidence_bound_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : audit_ide_registry A F) (q : ip_problem N P D) weight start seed,
      audit_ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      let rules := generate N P D A F EP r q weight (start, seed) in
      let result := execute EN EP ED L r q weight start seed in
      audit_ide_incidence_visits EN ED rules (audit_ide_summary_probes result) <=
        2 * audit_ide_rule_budget q * length (audit_ide_summary_keys q) *
          S (audit_ide_bound r).

  (** Bounds the observed probes, joins and compositions produced by the scheduler. *)
  Definition audit_ide_public_probe_counts_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : audit_ide_registry A F) (q : ip_problem N P D) weight start seed,
      audit_ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      let rules := generate N P D A F EP r q weight (start, seed) in
      let result := execute EN EP ED L r q weight start seed in
      let probes := audit_ide_summary_probes result in
      let updates := length (audit_ide_probe_updates probes) in
      length probes <= length rules + 2 * length rules * updates /\
      audit_ide_probe_join_count probes <= length probes /\
      audit_ide_probe_compose_count probes <= 3 * length probes /\
      updates <= length (audit_ide_summary_keys q) * S (audit_ide_bound r).

End IncidenceConsumer.

(** Literally equal edge evaluations preserve the very same matched-path output. *)
Definition audit_ide_finite_path_equal_statement : Prop :=
  forall N P D A F (r : audit_ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F) (old : ide_problem N P D A),
    ide_graph old = q ->
    (forall e x y a, In e (ip_edges q) -> In (x, y) (ip_pairs e) ->
      audit_ide_eval r (weight e x y) a = ide_weight old e x y a) ->
    forall start seed initial n d stack b,
      ide_path old (start, seed, []) initial (n, d, stack) b <->
      @audit_ide_path N P D A F r q weight (start, seed, []) initial (n, d, stack) b.

(** * Congruent transformer contract pilot

    This augments the provisional registry with preservation of lattice equivalence.
    For example, equivalent values remain equivalent after any registered transformer.
    Builds on: the isolated IDE candidate and OrderLattice. *)

(** Every represented transformer respects the chosen preorder equivalence. *)
Record audit_ide_congruence_laws {A F} (L : lattice A) (r : audit_ide_registry A F) : Prop := {
  audit_ide_eval_proper : forall f a b, equivalent L a b ->
    equivalent L (audit_ide_eval r f a) (audit_ide_eval r f b)
}.

Section PublicStrong.

  Variable execute : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> audit_ide_summary N D F.

  (** Exact reachable path joins require both registry laws and transformer congruence. *)
  Definition audit_ide_strong_path_exact_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : audit_ide_registry A F)
      (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F),
      audit_ide_congruence_laws L r ->
      audit_ide_execute_exact_statement EN EP ED L r q weight (@execute N P D A F).

  (** Old and new finite results agree under equivalent represented weights. *)
  Definition audit_ide_strong_finite_agreement_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : audit_ide_registry A F)
      (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F)
      (EA : encoding A) (old : ide_problem N P D A),
      audit_ide_congruence_laws L r ->
      audit_ide_execute_finite_statement EN EP ED L r q weight (@execute N P D A F) EA old.

End PublicStrong.

(** Equal endpoints and stacks have equivalent values under compatible proper weights. *)
Definition audit_ide_strong_path_correspondence_statement : Prop :=
  forall N P D A F (L : lattice A) (r : audit_ide_registry A F)
    (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F)
    (old : ide_problem N P D A),
    audit_ide_congruence_laws L r -> audit_ide_registry_laws L r -> ide_laws old ->
    ide_graph old = q -> ide_lattice old = L ->
    (forall e x y a, In e (ip_edges q) -> In (x, y) (ip_pairs e) ->
      equivalent L (audit_ide_eval r (weight e x y) a) (ide_weight old e x y a)) ->
    forall start seed initial n d stack,
      (forall b, ide_path old (start, seed, nil) initial (n, d, stack) b ->
        exists b', @audit_ide_path N P D A F r q weight
          (start, seed, nil) initial (n, d, stack) b' /\ equivalent L b b') /\
      (forall b', @audit_ide_path N P D A F r q weight
          (start, seed, nil) initial (n, d, stack) b' ->
        exists b, ide_path old (start, seed, nil) initial (n, d, stack) b /\
          equivalent L b b').

(** Congruence is required only on real weights of an existing finite problem. *)
Definition audit_ide_old_weights_proper {N P D A} (old : ide_problem N P D A) : Prop :=
  forall e x y a b, In e (ip_edges (ide_graph old)) -> In (x, y) (ip_pairs e) ->
    equivalent (ide_lattice old) a b ->
    equivalent (ide_lattice old) (ide_weight old e x y a) (ide_weight old e x y b).

(** Finite compatibility has an explicit constructive-adapter target. *)
Definition audit_ide_strong_finite_registry_exists_statement : Prop :=
  forall N P D A (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (EA : encoding A) (old : ide_problem N P D A),
    ide_laws old -> audit_ide_old_weights_proper old ->
    exists (F : Type) (r : audit_ide_registry A F)
      (weight : ip_edge N P D -> option D -> option D -> F),
      audit_ide_registry_laws (ide_lattice old) r /\
      audit_ide_congruence_laws (ide_lattice old) r /\
      forall e x y a, In e (ip_edges (ide_graph old)) -> In (x, y) (ip_pairs e) ->
        equivalent (ide_lattice old) (audit_ide_eval r (weight e x y) a)
          (ide_weight old e x y a).

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-public-semantics.md *)
(** This deliberately simple specification is not the indexed generator implementation. *)
Definition audit_ide_rule_spec {N P D A F} (EP : encoding P) (r : audit_ide_registry A F)
    (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F)
    (root : IpTab.vertex N D) : list (audit_ide_rule N D F) :=
  let vertices := IpTab.vertices q in
  let arcs := audit_ide_arcs q weight in
  AuditIdeSeed (inr root) (audit_ide_id r) ::
  map (fun v => AuditIdeSeed (inl (v, v)) (audit_ide_id r)) vertices ++
  flat_map (fun arc => match audit_ide_arc_kind arc with
    | IpInternal => map (fun a => AuditIdeUnary (inl (a, audit_ide_arc_from arc))
        (inl (a, audit_ide_arc_to arc)) (audit_ide_arc_weight arc)) vertices
    | _ => []
    end) arcs ++
  flat_map (fun call => match audit_ide_arc_kind call with
    | IpCall site => flat_map (fun ret => match audit_ide_arc_kind ret with
        | IpReturn return_site => if Pos.eqb (encode EP site) (encode EP return_site) then
            map (fun a => AuditIdeBinary (inl (a, audit_ide_arc_from call))
              (inl (audit_ide_arc_to call, audit_ide_arc_from ret))
              (inl (a, audit_ide_arc_to ret)) (audit_ide_arc_weight call)
              (audit_ide_arc_weight ret)) vertices
          else []
        | _ => []
        end) arcs
    | _ => []
    end) arcs ++
  flat_map (fun u => map (fun v => AuditIdeBinary (inr u) (inl (u, v)) (inr v)
    (audit_ide_id r) (audit_ide_id r)) vertices) vertices ++
  flat_map (fun call => match audit_ide_arc_kind call with
    | IpCall _ => [AuditIdeUnary (inr (audit_ide_arc_from call))
        (inr (audit_ide_arc_to call)) (audit_ide_arc_weight call)]
    | _ => []
    end) arcs.

(** The reference list has the declared duplicate-preserving rule count. *)
Definition audit_ide_rule_spec_length_statement : Prop :=
  forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
    (q : ip_problem N P D) weight root,
    length (audit_ide_rule_spec EP r q weight root) = audit_ide_occurrence_rule_count EP q.

(** The occurrence list has exactly the declarative weighted ground rules. *)
Definition audit_ide_rule_spec_membership_statement : Prop :=
  forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
    (q : ip_problem N P D) weight root rule,
    In rule (audit_ide_rule_spec EP r q weight root) <->
      audit_ide_generated_rule r q weight root rule.

Section GeneratorContract.

  Variable generate : forall N P D A F, encoding P -> audit_ide_registry A F ->
    ip_problem N P D -> (ip_edge N P D -> option D -> option D -> F) ->
    IpTab.vertex N D -> list (audit_ide_rule N D F).

  (** The indexed generator preserves reference rows, multiplicities and order. *)
  Definition audit_ide_generator_exact_rows_statement : Prop :=
    forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
      (q : ip_problem N P D) weight root,
      generate N P D A F EP r q weight root = audit_ide_rule_spec EP r q weight root.

End GeneratorContract.

Definition audit_ide_finite_compatible_check {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F) : bool :=
  let L := ide_lattice old in
  forallb (fun e => forallb (fun xy => forallb (fun a =>
    let new := audit_ide_eval r (weight e (fst xy) (snd xy)) a in
    let prior := ide_weight old e (fst xy) (snd xy) a in
    OrderLattice.leb L new prior && OrderLattice.leb L prior new) (ide_values old)) (ip_pairs e))
    (ip_edges (ide_graph old)).

(** The selector chooses either the generated machine or the finite legacy backend. *)
Inductive audit_ide_selected_backend : Type :=
  | AuditIdeGenerated
  | AuditIdeFiniteLegacy.

(** A selection pairs its backend mode with an optional-valued query. *)
Record audit_ide_finite_selection (N D A : Type) : Type := AuditIdeFiniteSelection {
  audit_ide_selected_mode : audit_ide_selected_backend;
  audit_ide_selected_query : N -> option D -> option A
}.

Arguments AuditIdeFiniteSelection {N D A}.

Arguments audit_ide_selected_mode {N D A}.

Arguments audit_ide_selected_query {N D A}.

(** The old finite solvers distinguish unreachable keys from reachable bottom. *)
Definition audit_ide_legacy_query {N P D A} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (EA : encoding A) (old : ide_problem N P D A)
    (start : N) (seed : option D) (initial : A) : N -> option D -> option A :=
  let reach := ifds_solve EN EP ED (ide_graph old) start seed in
  let values := ide_solve EN EP ED EA old start seed initial in
  fun n d => if reach n d then Some (values n d) else None.

Section SelectionContract.

  Variable execute : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> audit_ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> audit_ide_summary N D F.

  (** The reference selection preserves the finite backend as an explicit fallback. *)
  Definition audit_ide_finite_select {N P D A F}
      (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
      (old : ide_problem N P D A) (r : audit_ide_registry A F)
      (weight : ip_edge N P D -> option D -> option D -> F)
      (start : N) (seed : option D) (initial : A) : audit_ide_finite_selection N D A :=
    if audit_ide_finite_compatible_check old r weight then
      let summary := execute EN EP ED (ide_lattice old) r (ide_graph old) weight start seed in
      AuditIdeFiniteSelection AuditIdeGenerated (audit_ide_summary_query EN ED r summary initial)
    else AuditIdeFiniteSelection AuditIdeFiniteLegacy
      (audit_ide_legacy_query EN EP ED EA old start seed initial).

  (** Both modes agree with the old result and distinguish absence from reachable bottom. *)
  Definition audit_ide_finite_select_correct_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
      (old : ide_problem N P D A) (r : audit_ide_registry A F) weight start seed initial,
      ide_laws old -> audit_ide_registry_laws (ide_lattice old) r ->
      audit_ide_congruence_laws (ide_lattice old) r -> In start (ip_nodes (ide_graph old)) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts (ide_graph old))
      end) ->
      let result := audit_ide_finite_select EN EP ED EA old r weight start seed initial in
      forall n d,
      (audit_ide_selected_query result n d = None <->
        ~ exists stack b, ide_path old (start, seed, []) initial (n, d, stack) b) /\
      (forall value, audit_ide_selected_query result n d = Some value ->
        equivalent (ide_lattice old) value (ide_solve EN EP ED EA old start seed initial n d)).

End SelectionContract.

(** The public registry names the same transformer dictionary as the audit model. *)
Definition ide_registry := audit_ide_registry.

(** The public registry laws alias the lattice, transformer and rank obligations. *)
Definition ide_registry_laws {A F} := @audit_ide_registry_laws A F.

(** The public congruence laws require transformers to preserve lattice equivalence. *)
Definition ide_registry_congruence_laws {A F} := @audit_ide_congruence_laws A F.

(** The public summary retains the result map and its probe sequence. *)
Record ide_registry_summary (N D F : Type) : Type := IdeRegistrySummary {
  ide_registry_summary_map : Map.t (IpTab.fact N D) F;
  ide_registry_summary_probes : list (audit_ide_probe N D F)
}.

Arguments IdeRegistrySummary {N D F}.

Arguments ide_registry_summary_map {N D F}.

Arguments ide_registry_summary_probes {N D F}.

(** This view derives the update projections from the returned probe trace. *)
Definition audit_ide_public_view {N D F} (summary : ide_registry_summary N D F) :
    audit_ide_summary N D F :=
  let events := audit_ide_probe_updates (ide_registry_summary_probes summary) in
  AuditIdeSummary (ide_registry_summary_map summary) (map snd events) events
    (ide_registry_summary_probes summary).

Definition ide_registry_query {N D A F} (EN : encoding N) (ED : encoding D)
    (r : ide_registry A F) (summary : ide_registry_summary N D F) (initial : A)
    (n : N) (d : option D) : option A :=
  option_map (fun transformer => audit_ide_eval r transformer initial)
    (Map.get (IpTab.fact_encoding EN ED) (inr (n,d)) (ide_registry_summary_map summary)).

(** The public path relation follows the same weighted graph steps as the audit path. *)
Definition ide_registry_path {N P D A F} := @audit_ide_path N P D A F.

(** The public generator relation names the same ground rules as the audit relation. *)
Definition ide_registry_generate {N P D A F} := @audit_ide_generated_rule N P D A F.

Section PublicContract.

  Variable ide_registry_solve : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> ide_registry_summary N D F.

  Definition audit_ide_public_solve_view {N P D A F} (EN : encoding N) (EP : encoding P)
      (ED : encoding D) (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
      (weight : ip_edge N P D -> option D -> option D -> F) start seed :=
    audit_ide_public_view (ide_registry_solve EN EP ED L r q weight start seed).

  (** Results are least upper bounds of values of paths with matched stack actions. *)
  Definition audit_ide_public_paths : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight,
      ide_registry_congruence_laws L r ->
      audit_ide_execute_exact_statement EN EP ED L r q weight (@audit_ide_public_solve_view N P D A
        F).

  (** Absence means no path; a reachable bottom is returned as [Some], not absence. *)
  Definition audit_ide_public_bottom : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight,
      ide_registry_laws L r -> ide_registry_congruence_laws L r -> ip_problem_wf q ->
      forall start seed initial, In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      forall n d,
      let result := ide_registry_query EN ED r (ide_registry_solve EN EP ED L r q weight start seed)
        initial n d in
      (result = None <-> ~ exists stack b,
        ide_registry_path r q weight (start, seed, []) initial (n, d, stack) b) /\
      ((exists stack b, ide_registry_path r q weight (start, seed, []) initial (n, d, stack) b) ->
        exists value, result = Some value).

  (** The public solver exposes the generated update trace. *)
  Definition audit_ide_public_updates : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight,
      audit_ide_execute_trace_statement EN EP ED L r q weight (@audit_ide_public_solve_view N P D A
        F).

  (** The public solver agrees with a compatible finite backend. *)
  Definition audit_ide_public_finite_agreement : Prop :=
    audit_ide_strong_finite_agreement_statement (@audit_ide_public_solve_view).

  (** The selection signature instantiates the reference selector with the public solver view. *)
  Definition audit_ide_select_signature := @audit_ide_finite_select (@audit_ide_public_solve_view).

  (** The public selector preserves the finite backend result. *)
  Definition audit_ide_public_select_correct : Prop :=
    audit_ide_finite_select_correct_statement (@audit_ide_public_solve_view).

  (** The nonenumerable stream witness exercises matched and mismatched returns. *)
  Definition audit_ide_public_stream_consumer : Prop :=
    audit_ide_stream_consumer_statement (@audit_ide_public_solve_view nat nat unit audit_ide_stream
      bool).

  (** The public solver preserves the reachable stream bottom. *)
  Definition audit_ide_public_stream_bottom : Prop :=
    audit_ide_stream_bottom_statement (@audit_ide_public_solve_view nat nat unit audit_ide_stream
      bool).

  Variable generate : forall N P D A F, encoding P -> ide_registry A F ->
    ip_problem N P D -> (ip_edge N P D -> option D -> option D -> F) ->
    IpTab.vertex N D -> list (audit_ide_rule N D F).

  (** The public generator preserves exact reference rows. *)
  Definition audit_ide_public_generate_exact : Prop := audit_ide_generator_exact_rows_statement
    generate.

  (** The public solver follows the generated-rule machine. *)
  Definition audit_ide_public_scheduler : Prop :=
    audit_ide_machine_consumer_statement generate (@audit_ide_public_solve_view).

  (** The public solver bounds its recorded probe operations. *)
  Definition audit_ide_public_probe_counts : Prop :=
    audit_ide_public_probe_counts_statement generate (@audit_ide_public_solve_view).

End PublicContract.

(** The public incidence count has the declared bound. *)
Definition audit_ide_public_incidence_counts : Prop := audit_ide_incidence_visits_bound_statement.

(** Equal edge weights give the same path values. *)
Definition audit_ide_public_equal_weight_paths : Prop := audit_ide_finite_path_equal_statement.

(** Equivalent proper edge weights yield corresponding path values. *)
Definition audit_ide_public_equivalent_weight_paths : Prop :=
  audit_ide_strong_path_correspondence_statement.

Module IdeRegistrySpec.

  (** Paths return the least upper bounds of matched-path values. *)
  Definition paths := audit_ide_public_paths.

  (** Absence is distinguished from a reachable bottom value. *)
  Definition bottom := audit_ide_public_bottom.

  (** Successful updates are projected from the recorded probe trace. *)
  Definition updates := audit_ide_public_updates.

  (** Compatible finite and public results agree under the stated laws. *)
  Definition finite_agreement := audit_ide_public_finite_agreement.

  (** Both selected modes preserve the legacy finite result. *)
  Definition select_correct := audit_ide_public_select_correct.

  (** The stream client distinguishes matching and mismatched returns. *)
  Definition stream_consumer := audit_ide_public_stream_consumer.

  (** A reachable stream bottom remains present in the result. *)
  Definition stream_bottom := audit_ide_public_stream_bottom.

  (** Generated rows retain the reference list's order and multiplicity. *)
  Definition generate_exact := audit_ide_public_generate_exact.

  (** The public result observes the generated-rule machine. *)
  Definition scheduler := audit_ide_public_scheduler.

  (** The recorded probes, joins and compositions satisfy their bounds. *)
  Definition probe_counts := audit_ide_public_probe_counts.

  (** Changed probes bound visits to indexed incidence buckets. *)
  Definition incidence_counts := audit_ide_public_incidence_counts.

  (** Literally equal weights yield the same matched-path values. *)
  Definition equal_weight_paths := audit_ide_public_equal_weight_paths.

  (** Equivalent proper weights yield corresponding matched-path values. *)
  Definition equivalent_weight_paths := audit_ide_public_equivalent_weight_paths.

End IdeRegistrySpec.

(** * Typed genuine IDE callback bodies

    Card: AUD-IDE-BASE. Only original public dictionary/weight/lattice/base-encoding inputs
    receive adapters. Derived encoders, Horn callbacks and internal closures remain library
    source duties. Neither the carrier nor the transformer carrier is enumerated here. *)
Record audit_ide_registry_adapters {A F} (r : ide_registry A F) : Type := IdeRegistryAdapters {
  ide_eval_adapter : audit_external_adapter (F * A) A
    (fun pair => audit_ide_eval r (fst pair) (snd pair));
  ide_compose_adapter : audit_external_adapter (F * F) F
    (fun pair => audit_ide_compose r (fst pair) (snd pair));
  ide_join_adapter : audit_external_adapter (F * F) F
    (fun pair => audit_ide_join r (fst pair) (snd pair));
  ide_equal_adapter : audit_external_adapter (F * F) bool
    (fun pair => audit_ide_equal r (fst pair) (snd pair))
}.

Arguments ide_eval_adapter {A F r}.

Arguments ide_compose_adapter {A F r}.

Arguments ide_join_adapter {A F r}.

Arguments ide_equal_adapter {A F r}.

(** All four dictionary adapters satisfy their separate external body laws. *)
Definition audit_ide_registry_adapter_laws {A F r} (adapters : @audit_ide_registry_adapters A F r)
  :=
  audit_external_adapter_laws (ide_eval_adapter adapters) /\
  audit_external_adapter_laws (ide_compose_adapter adapters) /\
  audit_external_adapter_laws (ide_join_adapter adapters) /\
  audit_external_adapter_laws (ide_equal_adapter adapters).

(** The graph adapters instrument the supplied node, site and fact encoders separately. *)
Record audit_ide_graph_encoding_adapters {N P D}
    (EN : encoding N) (EP : encoding P) (ED : encoding D) : Type := IdeGraphEncodingAdapters {
  ide_node_encoding_adapter : audit_external_adapter N positive (encode EN);
  ide_site_encoding_adapter : audit_external_adapter P positive (encode EP);
  ide_fact_encoding_adapter : audit_external_adapter D positive (encode ED)
}.

Arguments ide_node_encoding_adapter {N P D EN EP ED}.

Arguments ide_site_encoding_adapter {N P D EN EP ED}.

Arguments ide_fact_encoding_adapter {N P D EN EP ED}.

(** The node, site and fact encoding adapters satisfy their external body laws. *)
Definition audit_ide_graph_encoding_laws {N P D EN EP ED}
    (adapters : @audit_ide_graph_encoding_adapters N P D EN EP ED) :=
  audit_external_adapter_laws (ide_node_encoding_adapter adapters) /\
  audit_external_adapter_laws (ide_site_encoding_adapter adapters) /\
  audit_external_adapter_laws (ide_fact_encoding_adapter adapters).

Definition audit_ide_weight_adapter {N P D F}
    (weight : ip_edge N P D -> option D -> option D -> F) :=
  audit_external_adapter (ip_edge N P D * (option D * option D)) F
    (fun input => weight (fst input) (fst (snd input)) (snd (snd input))).

(** Legacy adapters instrument graph and value encoders, weight, lattice join and order. *)
Record audit_ide_legacy_adapters {N P D A}
    (EN : encoding N) (EP : encoding P) (ED : encoding D) (EA : encoding A)
    (old : ide_problem N P D A) : Type := IdeLegacyAdapters {
  ide_legacy_graph_encoding : audit_ide_graph_encoding_adapters EN EP ED;
  ide_value_encoding_adapter : audit_external_adapter A positive (encode EA);
  ide_legacy_weight_adapter : audit_external_adapter
    (ip_edge N P D * (option D * (option D * A))) A
    (fun input => ide_weight old (fst input) (fst (snd input))
      (fst (snd (snd input))) (snd (snd (snd input))));
  ide_lattice_join_adapter : audit_external_adapter (A * A) A
    (fun pair => OrderLattice.join (ide_lattice old) (fst pair) (snd pair));
  ide_lattice_order_adapter : audit_external_adapter (A * A) bool
    (fun pair => OrderLattice.leb (ide_lattice old) (fst pair) (snd pair))
}.

Arguments ide_legacy_graph_encoding {N P D A EN EP ED EA old}.

Arguments ide_value_encoding_adapter {N P D A EN EP ED EA old}.

Arguments ide_legacy_weight_adapter {N P D A EN EP ED EA old}.

Arguments ide_lattice_join_adapter {N P D A EN EP ED EA old}.

Arguments ide_lattice_order_adapter {N P D A EN EP ED EA old}.

(** The legacy graph, value, weight and lattice adapters satisfy their external laws. *)
Definition audit_ide_legacy_adapter_laws {N P D A EN EP ED EA old}
    (adapters : @audit_ide_legacy_adapters N P D A EN EP ED EA old) :=
  audit_ide_graph_encoding_laws (ide_legacy_graph_encoding adapters) /\
  audit_external_adapter_laws (ide_value_encoding_adapter adapters) /\
  audit_external_adapter_laws (ide_legacy_weight_adapter adapters) /\
  audit_external_adapter_laws (ide_lattice_join_adapter adapters) /\
  audit_external_adapter_laws (ide_lattice_order_adapter adapters).

(** Typed actual dictionary invocations carry body traces at the invocation site. *)
Inductive audit_ide_dictionary_body (A F : Type) : Type :=
  | IdeBodyEval (transformer : F) (input output : A) (trace : list audit_external_frame)
  | IdeBodyCompose (first second output : F) (trace : list audit_external_frame)
  | IdeBodyJoin (first second output : F) (trace : list audit_external_frame)
  | IdeBodyEqual (first second : F) (output : bool) (trace : list audit_external_frame).

Arguments IdeBodyEval {A F}.

Arguments IdeBodyCompose {A F}.

Arguments IdeBodyJoin {A F}.

Arguments IdeBodyEqual {A F}.

Definition audit_ide_dictionary_body_work {A F} (event : audit_ide_dictionary_body A F) :=
  match event with
  | IdeBodyEval _ _ _ trace | IdeBodyCompose _ _ _ trace | IdeBodyJoin _ _ _ trace |
    IdeBodyEqual _ _ _ trace => audit_external_trace_work trace
  end.

Definition ide_eval_with_body {A F r} (adapters : @audit_ide_registry_adapters A F r) f a :=
  let receipt := external_counted (ide_eval_adapter adapters) (f,a) in
  (external_value receipt, IdeBodyEval f a (external_value receipt) (external_events receipt)).

Definition ide_compose_with_body {A F r} (adapters : @audit_ide_registry_adapters A F r) f g :=
  let receipt := external_counted (ide_compose_adapter adapters) (f,g) in
  (external_value receipt, IdeBodyCompose (A:=A) f g (external_value receipt) (external_events
    receipt)).

Definition ide_join_with_body {A F r} (adapters : @audit_ide_registry_adapters A F r) f g :=
  let receipt := external_counted (ide_join_adapter adapters) (f,g) in
  (external_value receipt, IdeBodyJoin (A:=A) f g (external_value receipt) (external_events
    receipt)).

Definition ide_equal_with_body {A F r} (adapters : @audit_ide_registry_adapters A F r) f g :=
  let receipt := external_counted (ide_equal_adapter adapters) (f,g) in
  (external_value receipt, IdeBodyEqual (A:=A) f g (external_value receipt) (external_events
    receipt)).

(** A dictionary event's trace satisfies the external body relation for its recorded call. *)
Definition audit_ide_dictionary_body_valid {A F r}
    (adapters : @audit_ide_registry_adapters A F r) (event : audit_ide_dictionary_body A F) :=
  match event with
  | IdeBodyEval f a out trace => audit_external_body (ide_eval_adapter adapters) (f,a) out trace
  | IdeBodyCompose f g out trace => audit_external_body (ide_compose_adapter adapters) (f,g) out
    trace
  | IdeBodyJoin f g out trace => audit_external_body (ide_join_adapter adapters) (f,g) out trace
  | IdeBodyEqual f g out trace => audit_external_body (ide_equal_adapter adapters) (f,g) out trace
  end.

Definition audit_ide_dictionary_body_budget {A F r}
    (adapters : @audit_ide_registry_adapters A F r) (event : audit_ide_dictionary_body A F) :=
  match event with
  | IdeBodyEval f a _ _ => external_input_budget (ide_eval_adapter adapters) (f,a)
  | IdeBodyCompose f g _ _ => external_input_budget (ide_compose_adapter adapters) (f,g)
  | IdeBodyJoin f g _ _ => external_input_budget (ide_join_adapter adapters) (f,g)
  | IdeBodyEqual f g _ _ => external_input_budget (ide_equal_adapter adapters) (f,g)
  end.

(** Each adapter invocation returns the registered result within its allowance. *)
Definition audit_ide_dictionary_invocation_statement : Prop := forall A F r
    (adapters : @audit_ide_registry_adapters A F r), audit_ide_registry_adapter_laws adapters ->
  (forall f a, let '(out,event) := ide_eval_with_body adapters f a in
    out = audit_ide_eval r f a /\ audit_ide_dictionary_body_valid adapters event /\
    audit_ide_dictionary_body_work event <= audit_ide_dictionary_body_budget adapters event) /\
  (forall f g, let '(out,event) := ide_compose_with_body adapters f g in
    out = audit_ide_compose r f g /\ audit_ide_dictionary_body_valid adapters event /\
    audit_ide_dictionary_body_work event <= audit_ide_dictionary_body_budget adapters event) /\
  (forall f g, let '(out,event) := ide_join_with_body adapters f g in
    out = audit_ide_join r f g /\ audit_ide_dictionary_body_valid adapters event /\
    audit_ide_dictionary_body_work event <= audit_ide_dictionary_body_budget adapters event) /\
  (forall f g, let '(out,event) := ide_equal_with_body adapters f g in
    out = audit_ide_equal r f g /\ audit_ide_dictionary_body_valid adapters event /\
    audit_ide_dictionary_body_work event <= audit_ide_dictionary_body_budget adapters event).
