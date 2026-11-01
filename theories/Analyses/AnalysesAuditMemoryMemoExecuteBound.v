(** * Fixed memo producer source bounds and public erasure

    These contracts include binary predecessor work and the fixed query's returned cache.
    For example, zero-credit cutoff pays its probes and credit case but never calls successors.
    Builds on: the fixed memo producer, its input recurrence and concrete memory adapters. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoWhole
  AnalysesAuditMemoryMemoExecute.
Import List.ListNotations.

Definition audit_memo_credit_width (fuel : BinNums.N) : nat :=
  match fuel with
  | N0 => 0
  | Npos p => Pos.size_nat p
  end.

Definition audit_memo_execution_source_work {N E CV CK NE}
    (version_work : list CV -> nat) (key_work : list CK -> nat) (next_work : list NE -> nat)
    (run : audit_memo_execution N E CV CK NE) : nat :=
  audit_memo_source_work version_work key_work next_work (audit_memo_body_events run) +
    2 * length (audit_memo_control_events run).

(** Matching encoder codes and successor results make two executions return equal values, caches
    and remaining credit. *)
Definition audit_memo_execute_projection_statement : Prop :=
  forall N E CV CK NE CV' CK' NE'
      (version_enc : memory_version N E -> positive * list CV)
      (key_enc : positive * memory_version N E -> positive * list CK)
      (next : memory_version N E -> list (memory_version N E) * list NE)
      (version_enc' : memory_version N E -> positive * list CV')
      (key_enc' : positive * memory_version N E -> positive * list CK')
      (next' : memory_version N E -> list (memory_version N E) * list NE')
      scope fuel active memo start,
    (forall v, fst (version_enc v) = fst (version_enc' v)) ->
    (forall key, fst (key_enc key) = fst (key_enc' key)) ->
    (forall v, fst (next v) = fst (next' v)) ->
    let run := audit_memo_execute version_enc key_enc scope next fuel active memo start in
    let run' := audit_memo_execute version_enc' key_enc' scope next' fuel active memo start in
    audit_memo_value run = audit_memo_value run' /\
    audit_memo_cache run = audit_memo_cache run' /\
    audit_memo_credit run = audit_memo_credit run'.

(** Callback budgets yield a recurrence witness at the execution endpoints and bound source work
    including binary control. *)
Definition audit_memo_execute_whole_input_bound_statement : Prop :=
  forall N E CV CK NE (version_enc : memory_version N E -> positive * list CV)
      (key_enc : positive * memory_version N E -> positive * list CK)
      (next : memory_version N E -> list (memory_version N E) * list NE)
      scope version_work key_work next_work version_budget key_budget next_budget
      fuel active memo start,
    (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
    (forall key, key_work (snd (key_enc key)) <= key_budget key) ->
    (forall v, next_work (snd (next v)) <= next_budget v) ->
    let run := audit_memo_execute version_enc key_enc scope next fuel active memo start in
    exists budget,
      audit_memo_input_budget_run version_enc key_enc scope next
        version_budget key_budget next_budget active memo start fuel
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run) budget /\
      audit_memo_execution_source_work version_work key_work next_work run <=
        16 * S (audit_memo_credit_width fuel) * budget.

(** The counted query executes actual memory callbacks from the same saved prepared state. *)
Definition audit_memory_memo_query_counted {N E T CN CE SE IE OE BE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (site_enc : T -> positive * list SE) (EN : encoding N) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (state : memo_state EN g effects mg)
    (incoming : N -> list E * list IE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :=
  let scope := audit_memory_scope_encode site_enc q in
  let next := audit_memory_raw_next edge_enc site_enc
    (@memo_effect_index N E T EN g effects mg state) incoming operand before q in
  (scope, audit_memo_execute (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_memo_key_encode node_enc edge_enc) (fst scope) next
    (Npos fuel) FinSet.empty (@memo_entries N E T EN g effects mg state) start).

(** Matching encoders, predecessor, operand and before callbacks make the counted result and
    memo entries agree with the public query. *)
Definition audit_memory_memo_query_counted_erases_statement : Prop :=
  forall N E T CN CE SE IE OE BE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg) (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE) q start fuel,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (incoming n) = pred_edges (@memo_adjacency N E T EN g effects mg state) n) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    let run := snd (audit_memory_memo_query_counted node_enc edge_enc site_enc EN g effects mg state
      incoming operand before q start fuel) in
    let original := audit_memory_memo_query EN EE ET g effects mg state q start fuel in
    audit_memo_value run = fst original /\
    audit_memo_cache run = @memo_entries N E T EN g effects mg (snd original).

(** Callback budgets yield a same-endpoint recurrence witness and bound counted query source
    work including binary control. *)
Definition audit_memory_memo_query_whole_input_bound_statement : Prop :=
  forall N E T CN CE SE IE OE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (g : Graph.t N E)
      (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg) (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work incoming_work operand_work before_work
      node_budget edge_budget site_budget incoming_budget operand_budget before_budget q start fuel,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, incoming_work (snd (incoming n)) <= incoming_budget n) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
    let '(scope, run) := audit_memory_memo_query_counted node_enc edge_enc site_enc EN
      g effects mg state incoming operand before q start fuel in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next := audit_memory_raw_next edge_enc site_enc
      (@memo_effect_index N E T EN g effects mg state) incoming operand before q in
    exists budget,
      audit_memo_input_budget_run version_enc key_enc (fst scope) next
        (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget)
        (audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget)
        (@audit_raw_next_input_budget N E T CE SE IE OE BE edge_enc site_enc
          (@memo_effect_index N E T EN g effects mg state) incoming before
          edge_budget site_budget incoming_budget operand_budget before_budget q)
        FinSet.empty (@memo_entries N E T EN g effects mg state) start (Npos fuel)
        (audit_memo_value run) (audit_memo_cache run) (audit_memo_credit run) budget /\
      audit_memory_scope_work site_work (snd scope) +
        audit_memo_execution_source_work (audit_memory_version_work node_work edge_work)
          (audit_memory_memo_key_work node_work edge_work)
          (audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work)
          run <= audit_memory_scope_input_budget site_enc site_budget q +
            16 * S (Pos.size_nat fuel) * budget.

(** Matching version and key encoders make counted and plain executions agree on value, cache
    and remaining credit. *)
Definition audit_memo_execute_plain_erases_statement : Prop :=
  forall N E CV CK NE (version_encoding : encoding (memory_version N E))
      (key_encoding : encoding (positive * memory_version N E))
      (version_enc : memory_version N E -> positive * list CV)
      (key_enc : positive * memory_version N E -> positive * list CK)
      (next : memory_version N E -> list (memory_version N E) * list NE)
      scope fuel active memo start,
    (forall v, fst (version_enc v) = encode version_encoding v) ->
    (forall key, fst (key_enc key) = encode key_encoding key) ->
    let counted := audit_memo_execute version_enc key_enc scope next fuel active memo start in
    let plain := AnalysesAuditMemoryMemoPlain.audit_memo_compute version_encoding key_encoding scope
      (fun v => fst (next v)) fuel active memo start in
    audit_memo_value counted = AnalysesAuditMemoryMemoPlain.audit_plain_memo_value plain /\
    audit_memo_cache counted = AnalysesAuditMemoryMemoPlain.audit_plain_memo_cache plain /\
    audit_memo_credit counted = AnalysesAuditMemoryMemoPlain.audit_plain_memo_credit plain.

(** With matching encoders and successor callback, the concrete query has a memo-tree witness
    and preserves its prepared indexes. *)
Definition audit_memory_memo_query_execution_contract_statement : Prop :=
  audit_memo_query_execution_contract (@audit_memory_memo_query).
