(** * PRE three reset-closure source models

    Counted reset closures compute the three PRE availability phases.
    For example, an empty arc set leaves only its seed nodes reachable.
    Builds on: shared source counters and graph preparation. *)

From Stdlib Require Import Decimal Arith Bool List PArith.
From Galois.Analyses Require Export AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesSsaLiveQuery AnalysesSsaPre AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphCore GraphDfs GraphPrepare.
Import List.ListNotations.

Scheme All for option.

Scheme All for list.

Scheme All for prod.

Scheme All for CollectionsTrie.Trie.ne.

Scheme All for CollectionsTrie.Trie.t.

Scheme All for audit_trie_call.

Scheme All for audit_event.

Scheme All for audit_map_event.

Scheme All for audit_prepare_source_event.

Scheme All for audit_graph_callback_capture.

(* Definition source: PreResetClosure.v *)
(** * PRE reset closures with the actual internal Graph.out source model

    Preparation invokes the counted map/enumerate/pair callback itself, so its work is not
    recovered by replaying a recorded output. Builds on: the GR owner's concrete adapters. *)

Inductive pre_closure_call (K : Type) : Type :=
  | PreClosureRows (call : exact_map_call K (FinSet.t K))
  | PreClosureSet (call : exact_map_call K unit)
  | PreClosureOut (key : K) (output : list (K * K)) (source_units : nat)
      (source_events : audit_trace (pre_closure_call K))
  | PreClosureEncode (key : K) (code : positive)
  | PreClosureTarget (edge : K * K) (target : K)
  | PreClosurePrepare (graph : Graph.t K (K * K))
      (events : list (audit_prepare_source_event K (K * K) (pre_closure_call K)))
  | PreClosureDfs (graph : Graph.t K (K * K))
      (events : list (audit_dfs_nested_event K (K * K) (audit_graph_callback_capture K (K * K)
        (pre_closure_call K)))).

Arguments PreClosureRows {K}.

Arguments PreClosureSet {K}.

Arguments PreClosureOut {K}.

Arguments PreClosureEncode {K}.

Arguments PreClosureTarget {K}.

Arguments PreClosurePrepare {K}.

Arguments PreClosureDfs {K}.

Section Closure.

Context {K : Type} (EK : encoding K) (key_body : K -> nat).

(** Closure traversal records graph and map calls on keys of type K. *)
Let Call := pre_closure_call K.

Definition pre_reset_add_counted (index : Map.t K (FinSet.t K)) (arc : K * K)
    : exact_counted Call (Map.t K (FinSet.t K)) :=
  exact_bind 800 (exact_get PreClosureRows EK key_body (fst arc) index) (fun found =>
  exact_bind 801 (exact_case 801 (exact_return 801 (
    match found with
    | Some set => set
    | None => FinSet.empty end))) (fun row =>
  exact_bind 802 (exact_set PreClosureSet EK key_body (snd arc) tt row) (fun added =>
    exact_set PreClosureRows EK key_body (fst arc) added index))).

Definition pre_reset_index_source (arcs : list (K * K))
    : exact_counted Call (Map.t K (FinSet.t K)) :=
  exact_fold_left 803 pre_reset_add_counted arcs Map.empty.

Definition pre_reset_nodes_source (seeds : list K) (arcs : list (K * K))
    : exact_counted Call (list K) :=
  exact_bind 804 (exact_flat_map 805 (fun arc => exact_return 805 [fst arc;snd arc]) arcs) (fun ends
    =>
  exact_bind 806 (exact_append 806 seeds ends) (fun nodes =>
  exact_bind 807 (exact_set_of_list PreClosureSet EK key_body nodes) (fun set =>
    exact_set_elements PreClosureSet set))).

Definition pre_reset_out_source (index : Map.t K (FinSet.t K)) (key : K)
    : exact_counted Call (list (K * K)) :=
  exact_bind 810 (exact_get PreClosureRows EK key_body key index) (fun found =>
  exact_bind 811 (exact_case 811 (exact_return 811 (
    match found with
    | Some set => set
    | None => FinSet.empty end))) (fun set =>
  exact_bind 812 (exact_set_elements PreClosureSet set) (fun successors =>
    exact_map 813 (fun target => exact_return 813 (key,target)) successors))).

Definition pre_reset_out_adapter (index : Map.t K (FinSet.t K)) (key : K)
    : list (K * K) * list Call :=
  let run := pre_reset_out_source index key in
  (exact_value run,[PreClosureOut key (exact_value run) (exact_units run) (exact_events run)]).

Definition pre_reset_encode_adapter (key : K) : positive * list Call :=
  let code := encode EK key in (code,[PreClosureEncode key code]).

Definition pre_reset_target_adapter (edge : K * K) : K * list Call :=
  (snd edge,[PreClosureTarget edge (snd edge)]).

Definition pre_reset_body_work (call : Call) : nat :=
  match call with
  | PreClosureOut _ _ units _ => units
  | PreClosureEncode key code => 64 + key_body key + audit_encoding_weight (Pos.size_nat code)
  | PreClosureTarget _ _ => 64
  | _ => 0
  end.

Definition pre_reset_closure_source (seeds : list K) (arcs : list (K * K))
    : exact_counted Call (FinSet.t K) :=
  exact_bind 820 (pre_reset_index_source arcs) (fun index =>
  exact_bind 821 (pre_reset_nodes_source seeds arcs) (fun nodes =>
  let graph := Graph.Make seeds nodes
    (fun key => map (fun target => (key,target)) (FinSet.elements (live_index_get EK key index)))
      fst snd in
  let prepare_callbacks := AuditPrepareCallbackModel K (K * K) Call
    (pre_reset_out_adapter index) pre_reset_target_adapter pre_reset_encode_adapter in
  let '(prepared_graph, preparation_events) := audit_prepare_source_counted EK graph
    prepare_callbacks in
  exact_bind 822 (exact_call (PreClosurePrepare graph preparation_events)
    (audit_prepare_source_work pre_reset_body_work preparation_events) prepared_graph) (fun p =>
  let dfs_callbacks := AuditDfsCallbackModel K (K * K) Call pre_reset_target_adapter
    pre_reset_encode_adapter in
  let '(result, dfs_events) := audit_dfs_source_counted p dfs_callbacks FinSet.empty seeds in
  exact_bind 823 (exact_call (PreClosureDfs graph dfs_events)
    (audit_dfs_source_work pre_reset_body_work dfs_events) result)
    (fun search => exact_return 824 (visited search))))).

Definition pre_reset_source_operand (seeds : list K) (arcs : list (K * K)) : nat :=
  fold_right Nat.max 0 (map (fun key => key_body key + Pos.size_nat (encode EK key))
    (seeds ++ flat_map (fun arc => [fst arc;snd arc]) arcs)).

Definition pre_reset_closure_input_budget (seeds : list K) (arcs : list (K * K)) : nat :=
  (Nat.of_num_uint 1048576%uint) * Nat.pow (S (length seeds + 2 * length arcs)) 12 *
    Nat.pow (S (pre_reset_source_operand seeds arcs)) 6.

(** The reset closure returns the original reachable set within the input-only budget. *)
Definition audit_pre_reset_closure_full_source_statement : Prop := forall seeds arcs,
  let run := pre_reset_closure_source seeds arcs in
  exact_value run = AnalysesSsaPre.pre_reset_closure EK seeds arcs /\
  exact_units run <= pre_reset_closure_input_budget seeds arcs.

(** The reset callback emits the indexed successor edges for the requested key. *)
Definition pre_reset_out_adapter_erases_statement : Prop := forall index key,
  fst (pre_reset_out_adapter index key) =
    map (fun target => (key,target)) (FinSet.elements (live_index_get EK key index)).

End Closure.

(* Definition source: PreSolve.v *)
(** * All three PRE reset phases and strict flag/arc callbacks

    The five internal emit callbacks are literal fixed bodies, not external price laws.
    Builds on: PreResetClosure. *)

Inductive pre_solver_call (B BE E U : Type) : Type :=
  | PreSolverClosure (call : pre_closure_call (B * U))
  | PreSolverFlags (call : exact_map_call (B * U) bool)
  | PreSolverKeys (call : exact_map_call (B * U) unit)
  | PreSolverLinks (call : exact_map_call ((B * U) * BE) (frg_operand B E U)).

Arguments PreSolverClosure {B BE E U}.

Arguments PreSolverFlags {B BE E U}.

Arguments PreSolverKeys {B BE E U}.

Arguments PreSolverLinks {B BE E U}.

Section Solve.

Context {B BE E U : Type} (EB : encoding B) (EU : encoding U)
  (block_body : B -> nat) (expr_body : U -> nat).

(** Solver calls use block-expression keys, encoding EK and links that retain each operand. *)
Let Key := (B * U)%type.

Let EK := pair_encoding EB EU.

Let Call := pre_solver_call B BE E U.

Let Link := (((B * U) * BE) * frg_operand B E U)%type.

Definition pre_solver_key_body (key : Key) : nat :=
  64 + block_body (fst key) + expr_body (snd key) + 32 * Pos.size_nat (encode EK key).

Definition pre_solver_get (flags : Map.t Key bool) (key : Key) : exact_counted Call bool :=
  exact_bind 900 (exact_get PreSolverFlags EK pre_solver_key_body key flags)
    (fun found => exact_case 901 (exact_return 901 (
      match found with
      | Some value => value
      | None => false end))).

Definition pre_solver_flags (keys : list Key) (flag : Key -> exact_counted Call bool)
    : exact_counted Call (Map.t Key bool) :=
  exact_fold_right 902 (fun key flags => exact_bind 903 (flag key)
    (fun value => exact_set PreSolverFlags EK pre_solver_key_body key value flags)) Map.empty keys.

Definition pre_solver_down_arcs (links : list Link) : exact_counted Call (list (Key * Key)) :=
  exact_flat_map 904 (fun link => let key := fst (fst link) in let op := snd link in
    if frg_operand_real_use op then exact_case 905 (exact_return 905 [])
    else exact_case 906 (
      match frg_operand_version op with
      | FrPhi b u => exact_case 907 (exact_return 907 [(key,(b,u))])
      | _ => exact_case 908 (exact_return 908 []) end)) links.

Definition pre_solver_cannot_seeds (down : Map.t Key bool) (links : list Link)
    : exact_counted Call (list Key) :=
  exact_flat_map 909 (fun link => let key := fst (fst link) in let op := snd link in
    exact_bind 910 (pre_solver_get down key) (fun flag =>
    if flag then exact_case 911 (exact_return 911 [])
    else exact_case 912 (
      match frg_operand_version op with
      | FrUnavailable _ => exact_case 913 (exact_return 913 [key])
      | _ => exact_case 914 (exact_return 914 []) end))) links.

Definition pre_solver_cannot_arcs (down : Map.t Key bool) (links : list Link)
    : exact_counted Call (list (Key * Key)) :=
  exact_flat_map 915 (fun link => let key := fst (fst link) in let op := snd link in
    exact_bind 916 (pre_solver_get down key) (fun flag =>
    exact_bind 917 (exact_return 917 (flag || frg_operand_real_use op)) (fun blocked =>
    if blocked then exact_case 918 (exact_return 918 [])
    else exact_case 919 (
      match frg_operand_version op with
      | FrPhi b u => exact_case 920 (exact_return 920 [((b,u),key)])
      | _ => exact_case 921 (exact_return 921 []) end)))) links.

Definition pre_solver_later_seeds (can : Map.t Key bool) (links : list Link)
    : exact_counted Call (list Key) :=
  exact_flat_map 922 (fun link => let key := fst (fst link) in let op := snd link in
    exact_bind 923 (pre_solver_get can key) (fun flag =>
    exact_bind 924 (exact_return 924 (flag && frg_operand_real_use op)) (fun present =>
    if present then exact_case 925 (
      match frg_operand_version op with
      | FrUnavailable _ => exact_case 926 (exact_return 926 [])
      | _ => exact_case 927 (exact_return 927 [key]) end)
    else exact_case 928 (exact_return 928 [])))) links.

Definition pre_solver_later_arcs (can : Map.t Key bool) (links : list Link)
    : exact_counted Call (list (Key * Key)) :=
  exact_flat_map 929 (fun link => let key := fst (fst link) in let op := snd link in
    exact_bind 930 (pre_solver_get can key) (fun flag =>
    if flag then exact_case 931 (
      match frg_operand_version op with
      | FrPhi b u => exact_case 932 (exact_return 932 [((b,u),key)])
      | _ => exact_case 933 (exact_return 933 []) end)
    else exact_case 934 (exact_return 934 []))) links.

Definition pre_solver_closure (seeds : list Key) (arcs : list (Key * Key))
    : exact_counted Call (FinSet.t Key) :=
  exact_lift PreSolverClosure (pre_reset_closure_source EK pre_solver_key_body seeds arcs).

Definition pre_solver_member (key : Key) (set : FinSet.t Key) : exact_counted Call bool :=
  exact_set_mem PreSolverKeys EK pre_solver_key_body key set.

Definition pre_solve_source (f : factored_redundancy_graph B BE E U)
    : exact_counted Call (ssapre_facts B U) :=
  exact_bind 940 (exact_set_elements PreSolverKeys (frg_phi_index f)) (fun keys =>
  exact_bind 941 (exact_elements PreSolverLinks (frg_phi_operands f)) (fun links =>
  exact_bind 942 (exact_set_elements PreSolverKeys (frg_unsafe_seeds f)) (fun seeds =>
  exact_bind 943 (pre_solver_down_arcs links) (fun down_arcs =>
  exact_bind 944 (pre_solver_closure seeds down_arcs) (fun unsafe =>
  exact_bind 945 (pre_solver_flags keys (fun key => exact_bind 946 (pre_solver_member key unsafe)
    (fun present => exact_return 946 (negb present)))) (fun down =>
  exact_bind 947 (pre_solver_cannot_seeds down links) (fun cannot_seeds =>
  exact_bind 948 (pre_solver_cannot_arcs down links) (fun cannot_arcs =>
  exact_bind 949 (pre_solver_closure cannot_seeds cannot_arcs) (fun cannot =>
  exact_bind 950 (pre_solver_flags keys (fun key => exact_bind 951 (pre_solver_member key cannot)
    (fun present => exact_return 951 (negb present)))) (fun can =>
  exact_bind 952 (pre_solver_later_seeds can links) (fun later_seeds =>
  exact_bind 953 (pre_solver_later_arcs can links) (fun later_arcs =>
  exact_bind 954 (pre_solver_closure later_seeds later_arcs) (fun reset =>
  exact_bind 955 (pre_solver_flags keys (fun key =>
    exact_bind 956 (pre_solver_get can key) (fun flag =>
    exact_bind 957 (pre_solver_member key reset) (fun present => exact_return 958 (flag && negb
      present)))))
    (fun later => exact_return 959 (SsaPreFacts down can later))))))))))))))).

(** Erasing the three counted reset phases returns the original PRE facts. *)
Definition pre_solve_source_erases_statement : Prop :=
  forall S O N V K C (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) f,
    exact_value (pre_solve_source f) = solve_ssapre EB EBE EN EE EV EU a f.

Definition pre_solver_input_support (f : factored_redundancy_graph B BE E U) : list Key :=
  FinSet.elements (frg_phi_index f) ++ FinSet.elements (frg_unsafe_seeds f) ++
  flat_map (fun link => let key := fst (fst link) in
    match frg_operand_version (snd link) with
    | FrPhi b u => [key;(b,u)]
    | _ => [key] end) (Map.elements (frg_phi_operands f)).

Definition pre_solve_input_budget (f : factored_redundancy_graph B BE E U) : nat :=
  let nodes := exact_trie_nodes (frg_phi_index f) + exact_trie_nodes (frg_unsafe_seeds f) +
    exact_trie_nodes (frg_phi_operands f) + length (pre_solver_input_support f) in
  let operand := fold_right Nat.max 0 (map (fun key =>
    pre_solver_key_body key + Pos.size_nat (encode EK key)) (pre_solver_input_support f)) in
  (Nat.of_num_uint 16777216%uint) * Nat.pow (S nodes) 16 * Nat.pow (S operand) 8.

(** The three reset phases return the original facts within their input-only budget. *)
Definition audit_pre_solve_full_source_statement : Prop :=
  forall S O N V K C (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) f,
    let run := pre_solve_source f in
    exact_value run = solve_ssapre EB EBE EN EE EV EU a f /\
    exact_units run <= pre_solve_input_budget f.

End Solve.
