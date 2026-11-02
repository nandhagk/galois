(** * Guarded memory-phi operand query contracts

    This candidate fixes the retained-set probe, branch frames and optional query body.
    For example, a removed phi performs one indexed probe and no operand or representative call.
    Builds on: CollectionsAuditFinSet and the existing optional memory-phi closure model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCallback CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget AnalysesAuditMemoryPhiConsumer
  AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiSetup
  AnalysesAuditMemoryPhiInputBudget.
Import List.ListNotations.

(** * Guarded source values and explicit local frames *)

(** The code probe uses the actual returned node code and the already captured set. *)
Definition audit_phi_operand_code_mem {N} (code : positive) (kept : FinSet.t N) : bool :=
  match Map.code_get code kept with
  | Some _ => true
  | None => false
  end.

(** Source frames inspect the guard and construct None only on the removed-node branch. *)
Definition audit_phi_operand_guard_frames (retained : bool) : audit_trace unit :=
  AuditCase 0 [] :: if retained then [] else [AuditConstruct 1 []].

(** These events retain the actual set probe before the selected optional-query body. *)
Inductive audit_phi_operand_query_event (N E CN CV CE : Type) : Type :=
  | AuditPhiOperandProbe (node : N) (retained : bool) (calls : list (audit_set_event N CN))
  | AuditPhiOperandBody (calls : list (audit_phi_closure_event (N * option E) N E CV CE))
  | AuditPhiOperandAbsent.

Arguments AuditPhiOperandProbe {N E CN CV CE} _ _ _.
Arguments AuditPhiOperandBody {N E CN CV CE} _.
Arguments AuditPhiOperandAbsent {N E CN CV CE}.

(** The query reuses its supplied captured set; removed nodes never evaluate base or reps. *)
Definition audit_phi_output_operand_call {N E CN CV CE}
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) (kept : FinSet.t N)
    (base : (N * option E) -> option (memory_version N E) * list CE)
    (reps : Map.t (memory_version N E) (memory_version N E)) (input : N * option E) :
    option (memory_version N E) * list (audit_phi_operand_query_event N E CN CV CE) :=
  let '(retained, probe) := audit_finset_mem node_enc (fst input) kept in
  if retained then
    let '(result, calls) := audit_phi_output_optional_call version_enc base reps input in
    (result, [AuditPhiOperandProbe (fst input) retained probe; AuditPhiOperandBody calls])
  else (None, [AuditPhiOperandProbe (fst input) retained probe; AuditPhiOperandAbsent]).

(** Probe/body source work excludes observer records and counts the literal guard frames. *)
Fixpoint audit_phi_operand_query_source_work {N E CN CV CE}
    (node_work : list CN -> nat) (version_work : list CV -> nat) (base_work : list CE -> nat)
    (events : list (audit_phi_operand_query_event N E CN CV CE)) : nat :=
  match events with
  | [] => 0
  | AuditPhiOperandProbe _ _ calls :: rest =>
      audit_finset_source_work node_work calls + audit_work [@AuditCase unit 0 []] +
      audit_phi_operand_query_source_work node_work version_work base_work rest
  | AuditPhiOperandBody calls :: rest =>
      audit_phi_closure_source_work version_work base_work calls +
      audit_phi_operand_query_source_work node_work version_work base_work rest
  | AuditPhiOperandAbsent :: rest =>
      audit_work [@AuditConstruct unit 1 []] +
      audit_phi_operand_query_source_work node_work version_work base_work rest
  end.

(** Direct source work follows the exact lookup branches without inspecting observer traces. *)
Definition audit_phi_operand_query_direct_work {N E CN CV CE}
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    (base : (N * option E) -> option (memory_version N E) * list CE)
    (node_work : list CN -> nat) (version_work : list CV -> nat) (base_work : list CE -> nat)
    (kept : FinSet.t N) (reps : Map.t (memory_version N E) (memory_version N E))
    (input : N * option E) : nat :=
  let code := fst (node_enc (fst input)) in
  let retained := audit_phi_operand_code_mem code kept in
  2 + node_work (snd (node_enc (fst input))) + audit_trie_get_source_work code kept +
  (if retained then 4 else 2) + audit_work (audit_phi_operand_guard_frames retained) +
  if retained then
    4 + base_work (snd (base input)) +
    match fst (base input) with
    | None => 0
    | Some v =>
        let version_code := fst (version_enc v) in
        4 + 1 + version_work (snd (version_enc v)) +
        audit_trie_get_source_work version_code reps +
        match Map.code_get version_code reps with
        | None => 2
        | Some _ => 4
        end
    end
  else 0.

(** The input budget bounds the exact branch's probe and only its executed optional body. *)
Definition audit_phi_operand_query_input_budget {N E CN CV CE}
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    (base : (N * option E) -> option (memory_version N E) * list CE)
    (node_budget : N -> nat) (version_budget : memory_version N E -> nat)
    (base_budget : (N * option E) -> nat) (kept : FinSet.t N) (input : N * option E) : nat :=
  let code := fst (node_enc (fst input)) in
  let retained := audit_phi_operand_code_mem code kept in
  2 + node_budget (fst input) + 5 * Pos.size_nat code +
  (if retained then 4 else 2) + audit_work (audit_phi_operand_guard_frames retained) +
  if retained then
    audit_phi_closure_input_budget version_enc base version_budget base_budget input
  else 0.

(** * Exact future claims; these definitions are not proofs *)

(** Erasure preserves the guard and only maps operands belonging to retained nodes. *)
Definition audit_phi_output_operand_erases_statement : Prop :=
  forall N E CN CV CE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list CE) original reps kept input,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    fst (base input) = original input ->
    fst (audit_phi_output_operand_call node_enc version_enc kept base reps input) =
      if FinSet.mem EN (fst input) kept
      then option_map (audit_phi_producer_rep EN EE reps) (original input) else None.

(** The trace preserves the precise probe/body order and absence of skipped child calls. *)
Definition audit_phi_operand_query_trace_statement : Prop :=
  forall N E CN CV CE (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list CE) reps kept input,
    let '(retained, probe) := audit_finset_mem node_enc (fst input) kept in
    audit_phi_output_operand_call node_enc version_enc kept base reps input =
      if retained then
        let '(result, body) := audit_phi_output_optional_call version_enc base reps input in
        (result, [AuditPhiOperandProbe (fst input) retained probe; AuditPhiOperandBody body])
      else (None, [AuditPhiOperandProbe (fst input) retained probe; AuditPhiOperandAbsent]).

(** The child trace fold equals independently input-defined source work, including all branches. *)
Definition audit_phi_operand_query_source_adequate_statement : Prop :=
  forall N E CN CV CE (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list CE)
      node_work version_work base_work reps kept input,
    audit_phi_operand_query_source_work node_work version_work base_work
      (snd (audit_phi_output_operand_call node_enc version_enc kept base reps input)) =
    audit_phi_operand_query_direct_work node_enc version_enc base node_work version_work
      base_work kept reps input.

(** Actual encoder/body budgets bound queries even with malformed sets, maps and missing keys. *)
Definition audit_phi_operand_query_whole_input_bound_statement : Prop :=
  forall N E CN CV CE (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list CE)
      node_work version_work base_work node_budget version_budget base_budget reps kept input,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
    (forall arg, base_work (snd (base arg)) <= base_budget arg) ->
    audit_phi_operand_query_source_work node_work version_work base_work
      (snd (audit_phi_output_operand_call node_enc version_enc kept base reps input)) <=
    audit_phi_operand_query_input_budget node_enc version_enc base node_budget version_budget
      base_budget kept input.

(** * Genuine callback observations and adapted bounds *)

(** Only genuine node/edge encoder bodies are foreign inside the concrete version encoder. *)
Definition audit_phi_operand_version_sources {N E CN CE}
    (node_work : list CN -> nat) (edge_work : list CE -> nat)
    (node_source : N -> positive -> list CN -> nat -> Prop)
    (edge_source : E -> positive -> list CE -> nat -> Prop)
    (event : audit_memory_version_event N E CN CE) : Prop :=
  match event with
  | AuditVersionLive => True
  | AuditVersionPhi n code body => node_source n code body (node_work body)
  | AuditVersionDef _ _ _ calls =>
      Forall (fun call =>
        match call with
        | AuditPairFirst e code body => edge_source e code body (edge_work body)
        | AuditPairSecond _ _ _ | AuditPairFrame _ => True
        end) calls
  end.

(** Recorded callbacks are attached to their actual argument, result and returned child body. *)
Definition audit_phi_operand_query_callbacks {N E CN CE B}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (base_work : list B -> nat)
    (node_source : N -> positive -> list CN -> nat -> Prop)
    (edge_source : E -> positive -> list CE -> nat -> Prop)
    (base_source : (N * option E) -> option (memory_version N E) -> list B -> nat -> Prop)
    (events : list (audit_phi_operand_query_event N E CN
      (audit_memory_version_event N E CN CE) B)) : Prop :=
  Forall (fun event =>
    match event with
    | AuditPhiOperandProbe _ _ calls =>
        Forall (fun call =>
          match call with
          | AuditSetMem n code _ _ body _ => node_source n code body (node_work body)
          | _ => False
          end) calls
    | AuditPhiOperandBody calls =>
        Forall (fun call =>
          match call with
          | AuditPhiClosureCall arg result body => base_source arg result body (base_work body)
          | AuditPhiClosureRead _ _ map_calls =>
              Forall (fun map_call =>
                match map_call with
                | AuditMapGet _ _ _ _ body _ =>
                    Forall (audit_phi_operand_version_sources node_work edge_work
                      node_source edge_source) body
                | _ => False
                end) map_calls
          end) calls
    | AuditPhiOperandAbsent => True
    end) events.

(** Genuine adapters witness only executed callbacks and bound the same query's exact work. *)
Definition audit_phi_operand_query_adapted_source_statement : Prop :=
  forall N E CN CE B (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE)
      (base : (N * option E) -> option (memory_version N E) * list B)
      node_work edge_work base_work node_budget edge_budget base_budget
      node_source edge_source base_source reps kept input,
    audit_external_callback_adapter node_enc node_work node_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
    audit_external_callback_adapter base base_work base_source base_budget ->
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let version_work := audit_memory_version_work node_work edge_work in
    let version_budget := audit_memory_version_input_budget node_enc edge_enc
      node_budget edge_budget in
    let run := audit_phi_output_operand_call node_enc version_enc kept base reps input in
    audit_phi_operand_query_callbacks node_work edge_work base_work node_source edge_source
      base_source (snd run) /\
    audit_phi_operand_query_source_work node_work version_work base_work (snd run) =
      audit_phi_operand_query_direct_work node_enc version_enc base node_work version_work
        base_work kept reps input /\
    audit_phi_operand_query_source_work node_work version_work base_work (snd run) <=
      audit_phi_operand_query_input_budget node_enc version_enc base node_budget version_budget
        base_budget kept input.

(** * Captured-set and actual producer bridges *)

(** This specification names the existing output constructor's captured set, not query work. *)
Definition audit_phi_operand_output_index {N E} (EN : encoding N) (EE : encoding E)
    (old : memory_graph N E) (reps : Map.t (memory_version N E) (memory_version N E))
    : FinSet.t N :=
  let rep := audit_phi_producer_rep EN EE reps in
  FinSet.of_list EN (filter (fun n =>
    Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n))
      (encode (memory_version_encoding EN EE) (rep (MemoryPhi n)))) (memory_phis old)).

(** Partial application captures an existing index; there is no set construction in this body. *)
Definition audit_phi_operand_saved_query {N E CN CV B}
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) (captured : FinSet.t N)
    (base : (N * option E) -> option (memory_version N E) * list B)
    (reps : Map.t (memory_version N E) (memory_version N E)) :=
  fun input => audit_phi_output_operand_call node_enc version_enc captured base reps input.

(** The saved index is exactly the output-construction set and retained-inventory membership. *)
Definition audit_phi_operand_saved_index_statement : Prop :=
  forall N E CN CV (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV) old reps,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    let kept := fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps
      (memory_phis old)) in
    let '(captured, calls) := audit_finset_of_list node_enc kept in
    captured = audit_phi_operand_output_index EN EE old reps /\
    In (AuditSetFold [] captured) calls /\
    In (AuditPhiOutputSetBuild calls)
      (snd (audit_phi_producer_output_counted EN EE node_enc version_enc old reps)) /\
    forall n, FinSet.mem EN n captured = true <->
      In n (memory_phis (audit_phi_producer_output EN EE old reps)).

(** The actual output constructor's captured set supports every repeated query without rebuild. *)
Definition audit_phi_operand_output_saved_query_statement : Prop :=
  forall N E CN CV B (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list B) old reps,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    (forall input, fst (base input) = memory_operand old (fst input) (snd input)) ->
    let kept := fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps
      (memory_phis old)) in
    let captured := fst (audit_finset_of_list node_enc kept) in
    let saved := audit_phi_operand_saved_query node_enc version_enc captured base reps in
    forall input, fst (saved input) =
      memory_operand (audit_phi_producer_output EN EE old reps) (fst input) (snd input).

(** The complete producer's saved query observes the same counted and public plain operands. *)
Definition audit_phi_operand_producer_saved_query_statement : Prop :=
  forall N E T CN CE PE B (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (pred : N -> list E * list PE)
      (operand : N -> option E -> option (memory_version N E) * list B)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (pred n) = pred_edges (prepare EN g) n) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let run := audit_phi_produce EN EE node_enc edge_enc pred operand version_enc g effects mg in
    let reps := audit_phi_run_representatives EN run in
    let kept := fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis mg)) in
    let captured := fst (audit_finset_of_list node_enc kept) in
    let saved := audit_phi_operand_saved_query node_enc version_enc captured
      (fun input => operand (fst input) (snd input)) reps in
    forall input,
      fst (saved input) = memory_operand (audit_phi_run_output EN run) (fst input) (snd input) /\
      fst (saved input) = memory_operand
        (phi_graph (audit_memory_phi_prune N E T EN EE g effects mg)) (fst input) (snd input).

(** The public source wrapper plus one query charges preparation once and the captured probe. *)
Definition audit_phi_operand_public_source_bridge_statement : Prop :=
  forall N E T CN CE OE TE B (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (operand : N -> option E -> option (memory_version N E) * list B)
      node_work edge_work out_work target_work operand_work
      node_budget edge_budget out_budget target_budget operand_budget
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      node_source edge_source out_source target_source operand_source input,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    audit_external_callback_adapter node_enc node_work node_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
    audit_external_callback_adapter out out_work out_source out_budget ->
    audit_external_callback_adapter target target_work target_source target_budget ->
    audit_external_callback_adapter
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) ->
    let '(base, preparation, run) := audit_memory_phi_prune_counted EN EE node_enc edge_enc
      out target operand g effects mg in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let version_work := audit_memory_version_work node_work edge_work in
    let version_budget := audit_memory_version_input_budget node_enc edge_enc
      node_budget edge_budget in
    let reps := audit_phi_run_representatives EN run in
    let kept := fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis mg)) in
    let captured := fst (audit_finset_of_list node_enc kept) in
    let saved := audit_phi_operand_saved_query node_enc version_enc captured
      (fun args => operand (fst args) (snd args)) reps in
    let query := saved input in
    fst query = memory_operand
      (phi_graph (audit_memory_phi_prune N E T EN EE g effects mg)) (fst input) (snd input) /\
    audit_phi_operand_query_callbacks node_work edge_work operand_work node_source edge_source
      operand_source (snd query) /\
    audit_prepare_source_work (audit_phi_input_graph_body_work node_work out_work target_work)
      preparation +
    audit_phi_producer_work node_work edge_work (audit_map_source_work node_work) operand_work
      version_work EN run +
    audit_phi_operand_query_source_work node_work version_work operand_work (snd query) <=
    audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_phi_input_graph_envelope out target node_budget out_budget target_budget
        (Graph.nodes g) +
    audit_phi_producer_input_budget EN EE node_enc edge_enc
      (audit_phi_predecessors_counted EN node_enc g base) operand node_budget edge_budget
      (audit_phi_get_input_budget node_enc node_budget) operand_budget g effects mg +
    audit_phi_operand_query_input_budget node_enc version_enc
      (fun args => operand (fst args) (snd args)) node_budget version_budget
      (fun args => operand_budget (fst args) (snd args)) captured input.

(** One captured index supports a finite sequence of queries, with no per-query preparation. *)
Definition audit_phi_operand_saved_queries_bound_statement : Prop :=
  forall N E CN CV CE (node_enc : N -> positive * list CN)
      (version_enc : memory_version N E -> positive * list CV)
      (base : (N * option E) -> option (memory_version N E) * list CE)
      node_work version_work base_work node_budget version_budget base_budget reps captured,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
    (forall arg, base_work (snd (base arg)) <= base_budget arg) ->
    let saved := audit_phi_operand_saved_query node_enc version_enc captured base reps in
    forall inputs : list (N * option E),
      fold_right (fun input work =>
        audit_phi_operand_query_source_work node_work version_work base_work
          (snd (saved input)) + work) 0 inputs <=
      fold_right (fun input budget =>
        audit_phi_operand_query_input_budget node_enc version_enc base node_budget
          version_budget base_budget captured input + budget) 0 inputs.

(** All new query obligations remain required, with the original semantic contracts unchanged. *)
Definition audit_phi_operand_query_contract_statement : Prop :=
  audit_phi_output_operand_erases_statement /\
  audit_phi_operand_query_trace_statement /\
  audit_phi_operand_query_source_adequate_statement /\
  audit_phi_operand_query_whole_input_bound_statement /\
  audit_phi_operand_query_adapted_source_statement /\
  audit_phi_operand_saved_index_statement /\
  audit_phi_operand_output_saved_query_statement /\
  audit_phi_operand_producer_saved_query_statement /\
  audit_phi_operand_public_source_bridge_statement /\
  audit_phi_operand_saved_queries_bound_statement.
