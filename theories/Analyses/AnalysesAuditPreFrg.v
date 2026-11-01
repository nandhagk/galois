(** * PRE phi graph and renaming source

    Counted phi placement and renaming record the actual graph and expression callbacks.
    For example, a translated phi edge retains its source block and expression.
    Builds on: PRE family, graph audits and expression SSA. *)

From Stdlib Require Import Decimal Arith Bool List PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditPreFamily AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphCore GraphDfs GraphDominators
  GraphFrontier GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSsa ViewsSsaPoints.
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

(* Definition source: PreRename.v *)
(** * Literal FRG rename cells and strict occurrence/argument handling

    Card: AUD-SP. Every metadata callback carries its actual result. Internal maps, flags,
    expression encodings and both strict comparison operands are library-owned equations. *)
Inductive pre_rename_call (B BE N E V U : Type) : Type :=
  | PrnScope (call : exact_map_call U (frg_operand B E U * bool))
  | PrnOccurrence (call : exact_map_call E (frg_version B E U))
  | PrnFresh (call : exact_map_call E unit)
  | PrnLink (call : exact_map_call ((B * U) * BE) (frg_operand B E U))
  | PrnUnsafe (call : exact_map_call (B * U) unit)
  | PrnSeen (call : exact_map_call B unit)
  | PrnGroupBU (call : exact_map_call B (FinSet.t U))
  | PrnGroupEU (call : exact_map_call E (FinSet.t U))
  | PrnGroupVU (call : exact_map_call V (FinSet.t U))
  | PrnSites (call : exact_map_call U (FinSet.t B))
  | PrnPred (call : exact_map_call B (list BE))
  | PrnSetU (call : exact_map_call U unit)
  | PrnExit (call : exact_map_call N (list U))
  | PrnArguments (call : exact_map_call B (FinSet.t (BE * U)))
  | PrnSetArgument (call : exact_map_call (BE * U) unit)
  | PrnChildren (call : exact_map_call B (list B))
  | PrnPhis (call : exact_map_call (B * U) unit)
  | PrnVersions (call : exact_map_call (frg_version B E U) unit)
  | PrnInitial (u : U) (result : bool)
  | PrnPure (u : U) (result : bool)
  | PrnRecomputed (edge : E) (result : option U)
  | PrnTranslate (edge : BE) (u : U) (result : option U)
  | PrnKilled (edge : E) (u : U) (result : bool)
  | PrnTarget (edge : E) (result : N)
  | PrnBlockTarget (edge : BE) (result : B)
  | PrnBlockSource (edge : BE) (result : B)
  | PrnParameter (block : B) (result : E)
  | PrnPoints (block : B) (result : list N)
  | PrnInstructions (block : B) (result : list E)
  | PrnOperands (u : U) (result : list V)
  | PrnDefinitions (edge : E) (result : list V)
  | PrnOut (n : N) (result : list E)
  | PrnExitPoint (n : N) (result : bool)
  | PrnEncodeU (u : U) (result : positive)
  | PrnEncodeE (edge : E) (result : positive)
  | PrnEqual (first second : positive) (result : bool).

Arguments PrnScope {B BE N E V U}.

Arguments PrnOccurrence {B BE N E V U}.

Arguments PrnFresh {B BE N E V U}.

Arguments PrnLink {B BE N E V U}.

Arguments PrnUnsafe {B BE N E V U}.

Arguments PrnSeen {B BE N E V U}.

Arguments PrnGroupBU {B BE N E V U}.

Arguments PrnGroupEU {B BE N E V U}.

Arguments PrnGroupVU {B BE N E V U}.

Arguments PrnSites {B BE N E V U}.

Arguments PrnPred {B BE N E V U}.

Arguments PrnSetU {B BE N E V U}.

Arguments PrnExit {B BE N E V U}.

Arguments PrnArguments {B BE N E V U}.

Arguments PrnSetArgument {B BE N E V U}.

Arguments PrnChildren {B BE N E V U}.

Arguments PrnPhis {B BE N E V U}.

Arguments PrnVersions {B BE N E V U}.

Arguments PrnInitial {B BE N E V U}.

Arguments PrnPure {B BE N E V U}.

Arguments PrnRecomputed {B BE N E V U}.

Arguments PrnTranslate {B BE N E V U}.

Arguments PrnKilled {B BE N E V U}.

Arguments PrnTarget {B BE N E V U}.

Arguments PrnBlockTarget {B BE N E V U}.

Arguments PrnBlockSource {B BE N E V U}.

Arguments PrnParameter {B BE N E V U}.

Arguments PrnPoints {B BE N E V U}.

Arguments PrnInstructions {B BE N E V U}.

Arguments PrnOperands {B BE N E V U}.

Arguments PrnDefinitions {B BE N E V U}.

Arguments PrnOut {B BE N E V U}.

Arguments PrnExitPoint {B BE N E V U}.

Arguments PrnEncodeU {B BE N E V U}.

Arguments PrnEncodeE {B BE N E V U}.

Arguments PrnEqual {B BE N E V U}.

Definition pre_group_lookup_counted {Call X Y} (inject : exact_map_call X (FinSet.t Y) -> Call)
    EX body index x : exact_counted Call (FinSet.t Y) :=
  exact_bind 1400 (exact_get inject EX body x index) (fun found =>
    exact_case 1401 (exact_return 1401 (
      match found with
      | Some xs => xs
      | None => FinSet.empty
        end))).

Definition pre_group_add_counted {Call X Y}
    (inject : exact_map_call X (FinSet.t Y) -> Call) (set_inject : exact_map_call Y unit -> Call)
    EX EY xb yb (index : Map.t X (FinSet.t Y)) (key : X * Y) :=
  exact_bind 1402 (pre_group_lookup_counted inject EX xb index (fst key)) (fun old =>
  exact_bind 1403 (exact_set set_inject EY yb (snd key) tt old)
    (fun next => exact_set inject EX xb (fst key) next index)).

Section Rename.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** Rename traces calls while carrying the current scope and accumulated graph rows. *)
Let Call := pre_rename_call B BE N E V U.

Let Scope := Map.t U (frg_operand B E U * bool).

Let Acc := pre_rename_acc B BE E U.

Let Work := (Scope * Acc)%type.

Definition pre_rename_bu_body (key : B * U) :=
  64 + bb (fst key) + ub (snd key) + 32 * Pos.size_nat (encode (pair_encoding EB EU) key).

Definition pre_rename_bu_be_body (key : (B * U) * BE) :=
  128 + pre_rename_bu_body (fst key) + beb (snd key) +
    32 * Pos.size_nat (encode (pair_encoding (pair_encoding EB EU) EBE) key).

Definition pre_rename_expr_code u : exact_counted Call positive :=
  let code := encode EU u in exact_call (PrnEncodeU u code)
    (ub u + 32 * Pos.size_nat code) code.

Definition pre_rename_edge_code e : exact_counted Call positive :=
  let code := encode EE e in exact_call (PrnEncodeE e code)
    (eb e + 32 * Pos.size_nat code) code.

Definition pre_rename_equal first second : exact_counted Call bool :=
  let result := Pos.eqb first second in
  exact_call (PrnEqual first second result) (8 * audit_binary_weight (Z.pos first) (Z.pos second))
    result.

Definition pre_rename_same_counted (v : option U) u : exact_counted Call bool :=
  match v with
  | None => exact_case 1410 (exact_return 1410 false)
  | Some x =>
    exact_case 1411 (exact_bind 1412 (pre_rename_expr_code x)
      (fun xc => exact_bind 1413 (pre_rename_expr_code u) (pre_rename_equal xc))) end.

Definition pre_rename_top_counted (scope : Scope) u : exact_counted Call (frg_operand B E U * bool)
  :=
  exact_bind 1414 (exact_get PrnScope EU ub u scope) (fun found =>
    exact_case 1415 (exact_return 1415 (
      match found with
      Some frame => frame
      | None => (FrgOperand (FrUnavailable u) false,false) end))).

Definition pre_rename_initial_counted family : exact_counted Call Scope :=
  exact_bind 1416 (exact_map 1416 (fun u => let available := pre_initial_available a u in
    exact_bind 1417 (exact_call (PrnInitial u available) 0 available) (fun available =>
    exact_return 1418 (u,(FrgOperand (if available then FrInitial u else FrUnavailable u)
      false,available))))
      family) (fun rows => exact_fold_left 1419 (fun scope row =>
        exact_set PrnScope EU ub (fst row) (snd row) scope) rows Map.empty).

Definition pre_rename_mark_counted (scope : Scope) (acc : Acc) u : exact_counted Call Acc :=
  exact_bind 1420 (pre_rename_top_counted scope u) (fun top =>
    match top with
    | (FrgOperand (FrPhi b v) false,_) =>
      exact_case 1421
        (exact_bind 1422 (exact_set PrnUnsafe (pair_encoding EB EU) pre_rename_bu_body (b,v) tt
          (pre_rename_unsafe acc)) (fun unsafe => exact_return 1423
            (PreRenameAcc (pre_rename_occurrences acc) (pre_rename_fresh acc) (pre_rename_links acc)
              unsafe)))
    | _ => exact_case 1424 (exact_return 1424 acc) end).

Definition pre_rename_alter_counted e (work : Work) u : exact_counted Call Work :=
  let '(scope,acc) := work in let computed := pre_recomputed (pre_expression a) e in
  exact_bind 1425 (exact_call (PrnRecomputed e computed) 0 computed) (fun computed =>
  exact_bind 1426 (pre_rename_same_counted computed u) (fun same =>
  exact_bind 1427 (if same then exact_case 1427 (exact_return 1427 acc)
    else exact_case 1428 (pre_rename_mark_counted scope acc u)) (fun marked =>
  exact_bind 1429 (pre_rename_top_counted scope u) (fun top =>
  exact_bind 1430 (exact_set PrnScope EU ub u (fst top,false) scope)
    (fun next => exact_return 1431 (next,marked)))))).

Definition pre_rename_occurrence_counted e (work : Work) : exact_counted Call (Work * option U) :=
  let '(scope,acc) := work in let computed := pre_recomputed (pre_expression a) e in
  exact_bind 1432 (exact_call (PrnRecomputed e computed) 0 computed) (fun computed =>
    match computed with
    | None => exact_case 1433 (exact_return 1433 (work,None))
    | Some u =>
      exact_case 1434
        (let pure := pre_total_pure (pre_expression a) u in
        exact_bind 1435 (exact_call (PrnPure u pure) 0 pure) (fun pure =>
        if pure then exact_case 1436
          (exact_bind 1437 (pre_rename_top_counted scope u) (fun top =>
          let '(frame,available) := top in
          exact_bind 1438 (if available then
            match frg_operand_version frame with
            | FrUnavailable _ => exact_case 1438 (exact_return 1438 true)
            | _ =>
              exact_case 1439 (exact_bind 1439
                (pre_rename_same_counted (Some (frg_version_expr (frg_operand_version frame))) u)
                  (fun same => exact_return 1440 (negb same))) end
            else exact_case 1441 (exact_return 1441 true)) (fun fresh =>
          let d := if fresh then FrFresh e u else frg_operand_version frame in
          exact_bind 1442 (exact_set PrnOccurrence EE eb e d (pre_rename_occurrences acc)) (fun
            occurrences =>
          exact_bind 1443 (if fresh then exact_case 1443 (exact_set PrnFresh EE eb e tt
            (pre_rename_fresh acc))
            else exact_case 1444 (exact_return 1444 (pre_rename_fresh acc))) (fun fresh_set =>
          let updated := PreRenameAcc occurrences fresh_set (pre_rename_links acc)
            (pre_rename_unsafe acc) in
          exact_bind 1445 (if fresh then exact_case 1445 (exact_return 1445 scope)
            else exact_case 1446 (exact_set PrnScope EU ub u (FrgOperand d true,true) scope))
            (fun next => exact_return 1447 ((next,updated),if fresh then Some u else None)))))))
        else exact_case 1448 (exact_return 1448 (work,None)))) end).

Definition pre_rename_argument_counted (scope : Scope) (acc : Acc) (argument : BE * U)
    : exact_counted Call Acc :=
  let '(be,u) := argument in let translated := pre_phi_translate a be u in
  exact_bind 1450 (exact_call (PrnTranslate be u translated) 0 translated) (fun translated =>
    match translated with
    | None => exact_case 1451 (exact_return 1451 acc)
    | Some value =>
      exact_case 1452
        (exact_bind 1453 (pre_rename_top_counted scope value) (fun top => let '(frame,available) :=
          top in
        exact_bind 1454 (pre_rename_same_counted
          (Some (frg_version_expr (frg_operand_version frame))) value)
          (fun same => let operand := if available && same then frame
              else FrgOperand (FrUnavailable value) false in
        let target := Graph.target (block_graph (pre_ssa_points a)) be in
        exact_bind 1455 (exact_call (PrnBlockTarget be target) 0 target) (fun target =>
        exact_bind 1456 (exact_set PrnLink (pair_encoding (pair_encoding EB EU) EBE)
          pre_rename_bu_be_body ((target,u),be) operand (pre_rename_links acc)) (fun links =>
        exact_return 1457 (PreRenameAcc (pre_rename_occurrences acc) (pre_rename_fresh acc) links
          (pre_rename_unsafe acc))))))) end).

(** Erasing rename cells recovers the original scope, occurrence and argument operations. *)
Definition pre_rename_cells_erases_statement : Prop :=
  (forall scope u, exact_value (pre_rename_top_counted scope u) =
    AnalysesSsaPreGraph.pre_rename_top EU scope u) /\
  (forall family, exact_value (pre_rename_initial_counted family) =
    AnalysesSsaPreGraph.pre_initial_scope EU a family) /\
  (forall scope acc u, exact_value (pre_rename_mark_counted scope acc u) =
    AnalysesSsaPreGraph.pre_rename_mark EB EU scope acc u) /\
  (forall e work u, exact_value (pre_rename_alter_counted e work u) =
    AnalysesSsaPreGraph.pre_rename_alter EB EU a e work u) /\
  (forall e work, exact_value (pre_rename_occurrence_counted e work) =
    AnalysesSsaPreGraph.pre_rename_occurrence EB EE EU a e work) /\
  (forall scope acc argument, exact_value (pre_rename_argument_counted scope acc argument) =
    AnalysesSsaPreGraph.pre_rename_argument EB EBE EU a scope acc argument).

Definition pre_rename_exit_counted (exits : Map.t N (list U)) n (work : Work)
    : exact_counted Call Work :=
  let '(scope,acc) := work in
  exact_bind 1460 (exact_get PrnExit EN nb n exits) (fun found =>
  exact_bind 1461 (exact_case 1461 (exact_return 1461 (
    match found with
    | Some xs => xs
    | None => [] end))) (fun xs =>
  exact_bind 1462 (exact_fold_left 1462 (pre_rename_mark_counted scope) xs acc)
    (fun marked => exact_return 1463 (scope,marked)))).

Definition pre_rename_definitions_counted (phis : Map.t B (FinSet.t U)) b e fresh (scope : Scope)
    : exact_counted Call Scope :=
  exact_bind 1470 (
    match fresh with
    | None => exact_case 1470 (exact_return 1470 scope)
    | Some u => exact_case 1471 (exact_set PrnScope EU ub u (FrgOperand (FrFresh e u) true,true)
      scope)
    end) (fun scope =>
  exact_bind 1472 (pre_rename_edge_code e) (fun first =>
  let parameter := parameter_edge (pre_ssa_points a) b in
  exact_bind 1473 (exact_call (PrnParameter b parameter) 0 parameter) (fun parameter =>
  exact_bind 1474 (pre_rename_edge_code parameter) (fun second =>
  exact_bind 1475 (pre_rename_equal first second) (fun same =>
  if same then exact_case 1476
    (exact_bind 1477 (pre_group_lookup_counted PrnGroupBU EB bb phis b) (fun set =>
    exact_bind 1478 (exact_set_elements PrnSetU set) (fun keys =>
      exact_fold_left 1479 (fun frames u =>
        exact_set PrnScope EU ub u (FrgOperand (FrPhi b u) false,true) frames) keys scope)))
  else exact_case 1480 (exact_return 1480 scope)))))).

Definition pre_rename_instruction_counted (alterations : Map.t E (FinSet.t U))
    (exits : Map.t N (list U)) (phis : Map.t B (FinSet.t U)) b (work : Work) e
    : exact_counted Call Work :=
  exact_bind 1481 (pre_rename_occurrence_counted e work) (fun observed =>
  let '(observed,fresh) := observed in
  exact_bind 1482 (pre_group_lookup_counted PrnGroupEU EE eb alterations e) (fun set =>
  exact_bind 1483 (exact_set_elements PrnSetU set) (fun keys =>
  exact_bind 1484 (exact_fold_left 1484 (pre_rename_alter_counted e) keys observed) (fun altered =>
  let '(scope,acc) := altered in
  let target := Graph.target (live_graph (point_model (pre_ssa_points a))) e in
  exact_bind 1485 (exact_call (PrnTarget e target) 0 target) (fun target =>
  exact_bind 1486 (pre_rename_definitions_counted phis b e fresh scope)
    (fun next => pre_rename_exit_counted exits target (next,acc))))))).

Definition pre_rename_block_counted (alterations : Map.t E (FinSet.t U))
    (exits : Map.t N (list U)) (phis : Map.t B (FinSet.t U))
    (arguments : Map.t B (FinSet.t (BE * U))) b (scope : Scope) (acc : Acc)
    : exact_counted Call Work :=
  let points := points_in_block (pre_ssa_points a) b in
  exact_bind 1490 (exact_call (PrnPoints b points) 0 points) (fun points =>
  exact_bind 1491 (
    match points with
    | [] => exact_case 1491 (exact_return 1491 (scope,acc))
    | n :: _ => exact_case 1492 (pre_rename_exit_counted exits n (scope,acc)) end) (fun entered =>
  let instructions := instruction_edges (pre_ssa_points a) b in
  exact_bind 1493 (exact_call (PrnInstructions b instructions) 0 instructions) (fun instructions =>
  exact_bind 1494 (exact_fold_left 1494 (pre_rename_instruction_counted alterations exits phis b)
    instructions entered) (fun result => let '(scope,acc) := result in
  exact_bind 1495 (pre_group_lookup_counted PrnArguments EB bb arguments b) (fun set =>
  exact_bind 1496 (exact_set_elements PrnSetArgument set) (fun keys =>
  exact_bind 1497 (exact_fold_left 1497 (pre_rename_argument_counted scope) keys acc)
    (fun next => exact_return 1498 (scope,next)))))))).

(** Rename work holds pending scoped blocks, visited blocks and the accumulator. *)
Let RenameWork := (list (B * Scope) * FinSet.t B * Acc)%type.

Definition pre_rename_step_counted (children : Map.t B (list B))
    (alterations : Map.t E (FinSet.t U)) (exits : Map.t N (list U))
    (phis : Map.t B (FinSet.t U)) (arguments : Map.t B (FinSet.t (BE * U)))
    (work : RenameWork) : exact_counted Call RenameWork :=
  let '(tasks,seen,acc) := work in
  match tasks with
  | [] => exact_case 1500 (exact_return 1500 work)
  | (b,scope) :: rest =>
    exact_case 1501
      (exact_bind 1502 (exact_set_mem PrnSeen EB bb b seen) (fun present =>
      if present then exact_case 1503 (exact_return 1503 (rest,seen,acc))
      else exact_case 1504
        (exact_bind 1505 (pre_rename_block_counted alterations exits phis arguments b scope acc)
          (fun result => let '(scope,acc) := result in
        exact_bind 1506 (exact_get PrnChildren EB bb b children) (fun found =>
        exact_bind 1507 (exact_case 1507 (exact_return 1507 (
          match found with
          | Some xs => xs
          | None => [] end))) (fun children =>
        exact_bind 1508 (exact_map 1508 (fun child => exact_return 1508 (child,scope)) children)
          (fun additions =>
        exact_bind 1509 (exact_append 1509 additions rest) (fun pending =>
        exact_bind 1510 (exact_set PrnSeen EB bb b tt seen)
          (fun seen => exact_return 1511 (pending,seen,acc)))))))))) end.

Fixpoint pre_rename_run_counted (step : RenameWork -> exact_counted Call RenameWork)
    (fuel : positive) (work : RenameWork) : exact_counted Call RenameWork :=
  match fst (fst work) with
  | [] => exact_case 1512 (exact_return 1512 work)
  | _ :: _ =>
    match fuel with
    | xH => exact_case 1513 (step work)
    | xO p =>
      exact_case 1514 (exact_bind 1514 (pre_rename_run_counted step p work)
        (pre_rename_run_counted step p))
    | xI p =>
      exact_case 1515 (exact_bind 1515 (pre_rename_run_counted step p work)
        (fun first => exact_bind 1515 (pre_rename_run_counted step p first) step)) end end.

(** Erasing the counted walk recovers the original rename transitions and fuelled run. *)
Definition pre_rename_walk_erases_statement : Prop :=
  (forall exits n work, exact_value (pre_rename_exit_counted exits n work) =
    AnalysesSsaPreGraph.pre_rename_exit EB EN EU exits n work) /\
  (forall phis b e fresh scope, exact_value (pre_rename_definitions_counted phis b e fresh scope) =
    AnalysesSsaPreGraph.pre_rename_definitions EB EE EU a phis b e fresh scope) /\
  (forall alterations exits phis b work e,
    exact_value (pre_rename_instruction_counted alterations exits phis b work e) =
    AnalysesSsaPreGraph.pre_rename_instruction EB EN EE EU a alterations exits phis b work e) /\
  (forall children alterations exits phis arguments fuel work,
    exact_value (pre_rename_run_counted
      (pre_rename_step_counted children alterations exits phis arguments) fuel work) =
    AnalysesSsaPreGraph.pre_rename_run
      (AnalysesSsaPreGraph.pre_rename_step EB EBE EN EE EU a children alterations exits phis
        arguments)
      fuel work).

Definition pre_rename_beu_body (key : BE * U) :=
  64 + beb (fst key) + ub (snd key) + 32 * Pos.size_nat (encode (pair_encoding EBE EU) key).

Definition pre_rename_version_body (version : frg_version B E U) :=
  128 + 64 * Pos.size_nat (encode (frg_version_encoding EB EE EU) version) +
    match version with
    | FrUnavailable u | FrInitial u => ub u
    | FrFresh e u => eb e + ub u
    | FrPhi b u => bb b + ub u end.

Definition pre_rename_edges_counted : exact_counted Call (list E) :=
  exact_flat_map 1520 (fun n => let edges := Graph.out (live_graph (point_model (pre_ssa_points a)))
    n in
    exact_call (PrnOut n edges) 0 edges) (Graph.nodes (live_graph (point_model (pre_ssa_points
      a)))).

Definition pre_rename_operand_index_counted family : exact_counted Call (Map.t V (FinSet.t U)) :=
  exact_bind 1521 (exact_flat_map 1521 (fun u => let values := pre_operands a u in
    exact_bind 1522 (exact_call (PrnOperands u values) 0 values)
      (fun values => exact_map 1523 (fun x => exact_return 1523 (x,u)) values)) family) (fun pairs
        =>
    exact_fold_left 1524 (pre_group_add_counted PrnGroupVU PrnSetU EV EU vb ub) pairs Map.empty).

Definition pre_rename_alter_candidates_counted (operands : Map.t V (FinSet.t U)) e
    : exact_counted Call (list U) :=
  let defs := edge_def (point_model (pre_ssa_points a)) e in
  exact_bind 1525 (exact_call (PrnDefinitions e defs) 0 defs) (fun defs =>
  exact_bind 1526 (exact_flat_map 1526 (fun x =>
    exact_bind 1527 (pre_group_lookup_counted PrnGroupVU EV vb operands x)
      (exact_set_elements PrnSetU)) defs) (fun values =>
  exact_bind 1528 (exact_set_of_list PrnSetU EU ub values) (exact_set_elements PrnSetU))).

Definition pre_rename_alter_index_counted family : exact_counted Call (Map.t E (FinSet.t U)) :=
  exact_bind 1530 (pre_rename_operand_index_counted family) (fun operands =>
  exact_bind 1531 pre_rename_edges_counted (fun edges =>
  exact_bind 1532 (exact_flat_map 1532 (fun e =>
    exact_bind 1533 (pre_rename_alter_candidates_counted operands e) (fun candidates =>
    exact_bind 1534 (exact_filter 1534 (fun u => let killed := kill (pre_genkill (pre_expression a))
      e u in
      exact_call (PrnKilled e u killed) 0 killed) candidates) (fun killed =>
      exact_map 1535 (fun u => exact_return 1535 (e,u)) killed))) edges) (fun pairs =>
      exact_fold_left 1536 (pre_group_add_counted PrnGroupEU PrnSetU EE EU eb ub) pairs
        Map.empty))).

Definition pre_rename_exit_index_counted family : exact_counted Call (Map.t N (list U)) :=
  exact_bind 1540 (exact_flat_map 1540 (fun n => let exit := pre_exit_point a n in
    exact_bind 1541 (exact_call (PrnExitPoint n exit) 0 exit) (fun exit =>
    if exit then exact_case 1542 (exact_return 1542 [(n,family)])
    else exact_case 1543
      (let edges := Graph.out (live_graph (point_model (pre_ssa_points a))) n in
      exact_bind 1544 (exact_call (PrnOut n edges) 0 edges) (fun edges =>
        match edges with
        | [] => exact_case 1545 (exact_return 1545 [(n,family)])
        | _ :: _ => exact_case 1546 (exact_return 1546 []) end))))
      (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) (fun pairs =>
      exact_fold_left 1547 (fun index pair => exact_set PrnExit EN nb (fst pair) (snd pair) index)
        pairs Map.empty).

Definition pre_rename_phi_index_counted (sites : Map.t U (FinSet.t B)) family
    : exact_counted Call (FinSet.t (B * U)) :=
  exact_bind 1550 (exact_flat_map 1550 (fun u => let pure := pre_total_pure (pre_expression a) u in
    exact_bind 1551 (exact_call (PrnPure u pure) 0 pure) (fun pure =>
    if pure then exact_case 1552
      (exact_bind 1553 (pre_group_lookup_counted PrnSites EU ub sites u) (fun set =>
      exact_bind 1554 (exact_set_elements PrnSeen set)
        (fun blocks => exact_map 1555 (fun b => exact_return 1555 (b,u)) blocks)))
    else exact_case 1556 (exact_return 1556 []))) family) (fun pairs =>
      exact_set_of_list PrnPhis (pair_encoding EB EU) pre_rename_bu_body pairs).

Definition pre_rename_argument_index_counted (p : prepared EB (block_graph (pre_ssa_points a)))
    (phis : FinSet.t (B * U)) : exact_counted Call (Map.t B (FinSet.t (BE * U))) :=
  exact_bind 1560 (exact_set_elements PrnPhis phis) (fun keys =>
  exact_bind 1561 (exact_flat_map 1561 (fun key => let '(b,u) := key in
    exact_bind 1562 (exact_get PrnPred EB bb b (in_index p)) (fun found =>
    exact_bind 1563 (exact_case 1563 (exact_return 1563 (
      match found with
      | Some xs => xs
      | None => [] end))) (fun edges =>
    exact_map 1564 (fun be => let source := Graph.source (block_graph (pre_ssa_points a)) be in
      exact_bind 1565 (exact_call (PrnBlockSource be source) 0 source)
        (fun source => exact_return 1566 (source,(be,u)))) edges))) keys) (fun pairs =>
    exact_fold_left 1567 (pre_group_add_counted PrnArguments PrnSetArgument EB (pair_encoding EBE
      EU)
      bb pre_rename_beu_body) pairs Map.empty)).

Definition pre_rename_fresh_versions_counted (acc : Acc) : exact_counted Call (list (frg_version B E
  U)) :=
  exact_bind 1570 pre_rename_edges_counted (fun edges =>
  exact_flat_map 1571 (fun e =>
    exact_bind 1572 (exact_set_mem PrnFresh EE eb e (pre_rename_fresh acc)) (fun fresh =>
    if fresh then exact_case 1573
      (let computed := pre_recomputed (pre_expression a) e in
      exact_bind 1574 (exact_call (PrnRecomputed e computed) 0 computed) (fun computed =>
        match computed with
        | None => exact_case 1575 (exact_return 1575 [])
        | Some u => exact_case 1576 (exact_return 1576 [FrFresh e u]) end))
    else exact_case 1577 (exact_return 1577 []))) edges).

Definition pre_rename_versions_counted family phis (acc : Acc)
    : exact_counted Call (list (frg_version B E U)) :=
  exact_bind 1580 (exact_map 1580 (fun u => exact_return 1580 (FrUnavailable u)) family) (fun
    unavailable =>
  exact_bind 1581 (exact_filter 1581 (fun u => let available := pre_initial_available a u in
    exact_call (PrnInitial u available) 0 available) family) (fun available =>
  exact_bind 1582 (exact_map 1582 (fun u => exact_return 1582 (FrInitial u)) available) (fun initial
    =>
  exact_bind 1583 (exact_set_elements PrnPhis phis) (fun keys =>
  exact_bind 1584 (exact_map 1584 (fun key => exact_return 1584 (FrPhi (fst key) (snd key))) keys)
    (fun merged =>
  exact_bind 1585 (pre_rename_fresh_versions_counted acc) (fun fresh =>
  exact_bind 1586 (exact_append 1586 merged fresh) (fun tail =>
  exact_bind 1587 (exact_append 1587 initial tail) (fun tail =>
  exact_bind 1588 (exact_append 1588 unavailable tail) (fun values =>
  exact_bind 1589 (exact_set_of_list PrnVersions (frg_version_encoding EB EE EU)
    pre_rename_version_body values)
    (exact_set_elements PrnVersions)))))))))).

(** The counted indexes and version list agree with the original rename setup. *)
Definition pre_rename_setup_erases_statement : Prop :=
  (forall family, exact_value (pre_rename_operand_index_counted family) =
    AnalysesSsaPreGraph.pre_rename_operand_index EV EU a family) /\
  (forall family, exact_value (pre_rename_alter_index_counted family) =
    AnalysesSsaPreGraph.pre_rename_alter_index EE EV EU a family) /\
  (forall family, exact_value (pre_rename_exit_index_counted family) =
    AnalysesSsaPreGraph.pre_rename_exit_index EN a family) /\
  (forall sites family, exact_value (pre_rename_phi_index_counted sites family) =
    AnalysesSsaPreGraph.pre_rename_phi_index EB EU a (AnalysesSsaPreGraph.pre_group_lookup EU sites)
      family) /\
  (forall p phis, exact_value (pre_rename_argument_index_counted p phis) =
    AnalysesSsaPreGraph.pre_rename_argument_index EB EBE EU a p phis) /\
  (forall family phis acc, exact_value (pre_rename_versions_counted family phis acc) =
    AnalysesSsaPreGraph.pre_rename_versions EB EE EU a family phis acc).

End Rename.

(* Definition source: PrePhi.v *)
(** * PRE phi-product graph's literal source callbacks and seed construction

    Card: AUD-SP. The generated graph's out closure is internal; its complete body below is
    used at each actual prepare invocation. Shared union uses its actual persistent trie run. *)
Inductive pre_phi_call (B BE N E V U : Type) : Type :=
  | PhiRename (call : pre_rename_call B BE N E V U)
  | PhiOccurrences (call : exact_map_call U (FinSet.t B))
  | PhiParameters (call : exact_map_call V (FinSet.t B))
  | PhiBlocks (call : exact_map_call B unit)
  | PhiPairs (call : exact_map_call (U * B) unit)
  | PhiFrontier (call : exact_map_call B (FinSet.t B))
  | PhiPred (call : exact_map_call B (list BE))
  | PhiHome (value : V) (result : B)
  | PhiBlockOf (point : N) (result : B)
  | PhiSource (edge : E) (result : N)
  | PhiBlockParams (block : B) (result : list V)
  | PhiUnion (first second result : FinSet.t B) (events : list (audit_union_event B)).

Arguments PhiRename {B BE N E V U}.

Arguments PhiOccurrences {B BE N E V U}.

Arguments PhiParameters {B BE N E V U}.

Arguments PhiBlocks {B BE N E V U}.

Arguments PhiPairs {B BE N E V U}.

Arguments PhiFrontier {B BE N E V U}.

Arguments PhiPred {B BE N E V U}.

Arguments PhiHome {B BE N E V U}.

Arguments PhiBlockOf {B BE N E V U}.

Arguments PhiSource {B BE N E V U}.

Arguments PhiBlockParams {B BE N E V U}.

Arguments PhiUnion {B BE N E V U}.

Section Phi.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** Phi construction records calls on the original views and its indexes. *)
Let Call := pre_phi_call B BE N E V U.

Definition pre_phi_ub_body (key : U * B) :=
  64 + ub (fst key) + bb (snd key) + 32 * Pos.size_nat (encode (pair_encoding EU EB) key).

Definition pre_phi_union_counted first second : exact_counted Call (FinSet.t B) :=
  let '(result,events) := audit_finset_union first second in
  exact_call (PhiUnion first second result events) (audit_finset_union_source_work events) result.

Definition pre_phi_frontier_counted (df : Map.t B (FinSet.t B)) b : exact_counted Call (list B) :=
  exact_bind 1600 (exact_get PhiFrontier EB bb b df) (fun found =>
    match found with
    | None => exact_case 1601 (exact_return 1601 [])
    | Some set => exact_case 1602 (exact_set_elements PhiBlocks set) end).

Definition pre_occurrence_blocks_counted : exact_counted Call (Map.t U (FinSet.t B)) :=
  exact_bind 1610 (exact_lift PhiRename (pre_rename_edges_counted a)) (fun edges =>
  exact_bind 1611 (exact_flat_map 1611 (fun e => let result := pre_recomputed (pre_expression a) e
    in
    exact_bind 1612 (exact_call (PhiRename (PrnRecomputed e result)) 0 result) (fun result =>
      match result with
      | None => exact_case 1613 (exact_return 1613 [])
      | Some u => exact_case 1614
        (let pure := pre_total_pure (pre_expression a) u in
        exact_bind 1615 (exact_call (PhiRename (PrnPure u pure)) 0 pure) (fun pure =>
        if pure then exact_case 1616
          (let point := Graph.source (live_graph (point_model (pre_ssa_points a))) e in
          exact_bind 1617 (exact_call (PhiSource e point) 0 point) (fun point =>
          let block := block_of_point (pre_ssa_points a) point in
          exact_bind 1618 (exact_call (PhiBlockOf point block) 0 block)
            (fun block => exact_return 1619 [(u,block)])))
        else exact_case 1620 (exact_return 1620 []))) end)) edges) (fun pairs =>
      exact_fold_left 1621 (pre_group_add_counted PhiOccurrences PhiBlocks EU EB ub bb) pairs
        Map.empty)).

Definition pre_definitions_query_counted (occurrences : Map.t U (FinSet.t B))
    (entry : FinSet.t B) u : exact_counted Call (list B) :=
  exact_bind 1630 (pre_group_lookup_counted PhiOccurrences EU ub occurrences u) (fun real =>
  let values := pre_operands a u in
  exact_bind 1631 (exact_call (PhiRename (PrnOperands u values)) 0 values) (fun values =>
  exact_bind 1632 (exact_map 1632 (fun value => let block := home (pre_ssa_view a) value in
    exact_call (PhiHome value block) 0 block) values) (fun homes =>
  exact_bind 1633 (exact_set_of_list PhiBlocks EB bb homes) (fun homes =>
  exact_bind 1634 (pre_phi_union_counted entry homes) (fun inner =>
  exact_bind 1635 (pre_phi_union_counted real inner) (exact_set_elements PhiBlocks)))))).

Definition pre_parameter_blocks_counted : exact_counted Call (Map.t V (FinSet.t B)) :=
  exact_bind 1640 (exact_set_of_list PhiBlocks EB bb
    (Graph.entries (block_graph (pre_ssa_points a)))) (fun entries =>
  exact_bind 1641 (exact_flat_map 1641 (fun b =>
    exact_bind 1642 (exact_set_mem PhiBlocks EB bb b entries) (fun is_entry =>
    if is_entry then exact_case 1643 (exact_return 1643 [])
    else exact_case 1644
      (let values := block_params (pre_ssa_points a) b in
      exact_bind 1645 (exact_call (PhiBlockParams b values) 0 values)
        (fun values => exact_map 1646 (fun x => exact_return 1646 (x,b)) values))))
      (Graph.nodes (block_graph (pre_ssa_points a)))) (fun pairs =>
    exact_fold_left 1647 (pre_group_add_counted PhiParameters PhiBlocks EV EB vb bb) pairs
      Map.empty)).

Definition pre_phi_direct_counted family : exact_counted Call (list (U * B)) :=
  exact_bind 1650 pre_parameter_blocks_counted (fun parameters =>
  exact_bind 1651 (exact_flat_map 1651 (fun u => let values := pre_operands a u in
    exact_bind 1652 (exact_call (PhiRename (PrnOperands u values)) 0 values) (fun values =>
    exact_flat_map 1653 (fun value =>
      exact_bind 1654 (pre_group_lookup_counted PhiParameters EV vb parameters value) (fun set =>
      exact_bind 1655 (exact_set_elements PhiBlocks set)
        (fun blocks => exact_map 1656 (fun b => exact_return 1656 (u,b)) blocks))) values)) family)
    (fun pairs => exact_bind 1657 (exact_set_of_list PhiPairs (pair_encoding EU EB) pre_phi_ub_body
      pairs)
      (exact_set_elements PhiPairs))).

Definition pre_phi_starts_counted family (df : Map.t B (FinSet.t B))
    : exact_counted Call (list (U * B)) :=
  exact_bind 1660 pre_occurrence_blocks_counted (fun occurrences =>
  exact_bind 1661 (exact_set_of_list PhiBlocks EB bb
    (Graph.entries (block_graph (pre_ssa_points a)))) (fun entry =>
  exact_bind 1662 (pre_phi_direct_counted family) (fun direct =>
  exact_bind 1663 (exact_flat_map 1663 (fun u =>
    exact_bind 1664 (pre_definitions_query_counted occurrences entry u) (fun definitions =>
    exact_flat_map 1665 (fun d => exact_bind 1666 (pre_phi_frontier_counted df d)
      (fun blocks => exact_map 1667 (fun b => exact_return 1667 (u,b)) blocks)) definitions))
        family)
    (fun frontier => exact_append 1668 direct frontier)))).

Definition pre_phi_next_counted (p : prepared EB (block_graph (pre_ssa_points a)))
    (df : Map.t B (FinSet.t B)) (key : U * B) : exact_counted Call (list (U * B)) :=
  let '(u,b) := key in
  exact_bind 1670 (pre_phi_frontier_counted df b) (fun blocks =>
  exact_bind 1671 (exact_map 1671 (fun c => exact_return 1671 (u,c)) blocks) (fun first =>
  exact_bind 1672 (exact_get PhiPred EB bb b (in_index p)) (fun found =>
  exact_bind 1673 (exact_case 1673 (exact_return 1673 (
    match found with
    | Some xs => xs
    | None => [] end))) (fun edges =>
  exact_bind 1674 (exact_flat_map 1674 (fun be => let value := pre_phi_translate a be u in
    exact_bind 1675 (exact_call (PhiRename (PrnTranslate be u value)) 0 value) (fun value =>
      match value with
      | None => exact_case 1676 (exact_return 1676 [])
      | Some v => exact_case 1677
        (let source := Graph.source (block_graph (pre_ssa_points a)) be in
        exact_bind 1678 (exact_call (PhiRename (PrnBlockSource be source)) 0 source) (fun source =>
        exact_bind 1679 (pre_phi_frontier_counted df source)
          (fun targets => exact_map 1680 (fun c => exact_return 1680 (v,c)) targets))) end)) edges)
    (fun translated => exact_bind 1681 (exact_append 1681 first translated) (fun pairs =>
    exact_bind 1682 (exact_set_of_list PhiPairs (pair_encoding EU EB) pre_phi_ub_body pairs)
      (exact_set_elements PhiPairs))))))).

(** The counted phi seeds and successors agree with their original graph helpers. *)
Definition pre_phi_helpers_erases_statement : Prop :=
  exact_value pre_occurrence_blocks_counted = AnalysesSsaPreGraph.pre_occurrence_blocks EB EU a /\
  exact_value pre_parameter_blocks_counted = AnalysesSsaPreGraph.pre_parameter_blocks EB EV a /\
  (forall family, exact_value (pre_phi_direct_counted family) =
    AnalysesSsaPreGraph.pre_phi_direct EB EV EU a family) /\
  (forall family df, exact_value (pre_phi_starts_counted family df) =
    AnalysesSsaPreGraph.pre_phi_starts EB EV EU a family df) /\
  (forall p df key, exact_value (pre_phi_next_counted p df key) =
    AnalysesSsaPreGraph.pre_phi_next EB EU a p df key).

End Phi.

(* Definition source: PrePhiGraph.v *)
(** * Actual nested execution of PRE's generated phi graph

    Card: AUD-SP. Callback receipts are produced at the real graph invocation and contain
    the whole literal out-body run. No callback is replayed merely to recover its cost. *)
Inductive pre_phi_graph_call (B BE N E V U : Type) : Type :=
  | PhiGraphBody (call : pre_phi_call B BE N E V U)
  | PhiGraphOut (key : U * B) (result : list ((U * B) * (U * B)))
      (units : nat) (events : audit_trace (pre_phi_call B BE N E V U))
  | PhiGraphEncode (key : U * B) (code : positive)
  | PhiGraphTarget (edge : (U * B) * (U * B)) (key : U * B)
  | PhiGraphPrepare (graph : Graph.t (U * B) ((U * B) * (U * B)))
      (events : list (audit_prepare_source_event (U * B) ((U * B) * (U * B))
        (pre_phi_graph_call B BE N E V U)))
  | PhiGraphDfs (graph : Graph.t (U * B) ((U * B) * (U * B)))
      (events : list (audit_dfs_nested_event (U * B) ((U * B) * (U * B))
        (audit_graph_callback_capture (U * B) ((U * B) * (U * B)) (pre_phi_graph_call B BE N E V
          U)))).

Arguments PhiGraphBody {B BE N E V U}.

Arguments PhiGraphOut {B BE N E V U}.

Arguments PhiGraphEncode {B BE N E V U}.

Arguments PhiGraphTarget {B BE N E V U}.

Arguments PhiGraphPrepare {B BE N E V U}.

Arguments PhiGraphDfs {B BE N E V U}.

Section PhiGraph.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** Phi graph calls use expression-block keys, paired-key edges, encoding EK and key-body cost. *)
Let Call := pre_phi_graph_call B BE N E V U.

Let EK := pair_encoding EU EB.

Let Key := (U * B)%type.

Let Edge := (Key * Key)%type.

Let key_body := pre_phi_ub_body EB EU bb ub.

Definition pre_phi_out_counted (p : prepared EB (block_graph (pre_ssa_points a)))
    (df : Map.t B (FinSet.t B)) key : exact_counted (pre_phi_call B BE N E V U) (list Edge) :=
  exact_bind 1700 (pre_phi_next_counted EB EU a bb ub p df key)
    (fun targets => exact_map 1701 (fun target => exact_return 1701 (key,target)) targets).

Definition pre_phi_out_adapter p df key : list Edge * list Call :=
  let run := pre_phi_out_counted p df key in
  (exact_value run,[PhiGraphOut key (exact_value run) (exact_units run) (exact_events run)]).

Definition pre_phi_encode_adapter key : positive * list Call :=
  let code := encode EK key in (code,[PhiGraphEncode key code]).

Definition pre_phi_target_adapter edge : Key * list Call :=
  (snd edge,[PhiGraphTarget edge (snd edge)]).

Definition pre_phi_graph_body_work (call : Call) : nat :=
  match call with
  | PhiGraphOut _ _ units _ => units
  | PhiGraphEncode key code => 64 + key_body key + audit_encoding_weight (Pos.size_nat code)
  | PhiGraphTarget _ _ => 64
  | _ => 0 end.

Definition pre_phi_graph_counted (p : prepared EB (block_graph (pre_ssa_points a)))
    (df : Map.t B (FinSet.t B)) (family : list U)
    : exact_counted Call (Graph.t Key Edge) :=
  exact_bind 1710 (exact_lift PhiGraphBody (pre_phi_starts_counted EB EV EU a bb vb ub family df))
    (fun entries =>
  exact_bind 1711 (exact_flat_map 1711 (fun u => exact_map 1712
    (fun b => exact_return 1712 (u,b)) (Graph.nodes (block_graph (pre_ssa_points a)))) family)
    (fun nodes => exact_return 1713 (Graph.Make entries nodes
      (fun key => map (fun target => (key,target)) (AnalysesSsaPreGraph.pre_phi_next EB EU a p df
        key))
        fst snd))).

Definition pre_phi_sites_counted (p : prepared EB (block_graph (pre_ssa_points a)))
    (df : Map.t B (FinSet.t B)) (family : list U)
    : exact_counted Call (Map.t U (FinSet.t B)) :=
  exact_bind 1720 (pre_phi_graph_counted p df family) (fun graph =>
  let cb := AuditPrepareCallbackModel Key Edge Call
    (pre_phi_out_adapter p df) pre_phi_target_adapter pre_phi_encode_adapter in
  let '(prepared_graph,prepare_events) := audit_prepare_source_counted EK graph cb in
  exact_bind 1721 (exact_call (PhiGraphPrepare graph prepare_events)
    (audit_prepare_source_work pre_phi_graph_body_work prepare_events) prepared_graph) (fun
      prepared_graph =>
  let dfs_cb := AuditDfsCallbackModel Key Edge Call pre_phi_target_adapter pre_phi_encode_adapter in
  let '(search,dfs_events) := audit_dfs_source_counted prepared_graph dfs_cb FinSet.empty
    (Graph.entries graph) in
  exact_bind 1722 (exact_call (PhiGraphDfs graph dfs_events)
    (audit_dfs_source_work pre_phi_graph_body_work dfs_events) search) (fun search =>
    exact_fold_left 1723 (pre_group_add_counted (fun call => PhiGraphBody (PhiOccurrences call))
      (fun call => PhiGraphBody (PhiBlocks call)) EU EB ub bb) (preorder search) Map.empty))).

(** The counted phi graph, callback output and site lookup agree with the original graph. *)
Definition pre_phi_graph_erases_statement : Prop :=
  (forall p df family, exact_value (pre_phi_graph_counted p df family) =
    AnalysesSsaPreGraph.pre_phi_graph_from EB EV EU a p df family) /\
  (forall p df key, fst (pre_phi_out_adapter p df key) =
    map (fun target => (key,target)) (AnalysesSsaPreGraph.pre_phi_next EB EU a p df key)) /\
  (forall p df family u,
    AnalysesSsaPreGraph.pre_group_lookup EU (exact_value (pre_phi_sites_counted p df family)) u =
      AnalysesSsaPreGraph.pre_phi_sites_graph EB EU
        (AnalysesSsaPreGraph.pre_phi_graph_from EB EV EU a p df family) u).

End PhiGraph.

(* Definition source: PreFrgFromGraph.v *)
(** * Full FRG body after the actual graph backend results

    Card: AUD-SP. This exact stage consumes prepared graph, dominator tree and frontier.
    It does not charge their construction as a constant or claim that missing GR source
    contracts are complete. Every subsequent library phase is an actual child run. *)
Inductive pre_frg_call (B BE N E V U : Type) : Type :=
  | FrgFamily (call : pre_family_call B BE V U)
  | FrgPhi (call : pre_phi_graph_call B BE N E V U)
  | FrgRename (call : pre_rename_call B BE N E V U)
  | FrgParents (call : exact_map_call B B)
  | FrgFuel (root_count parent_count : nat) (result : positive).

Arguments FrgFamily {B BE N E V U}.

Arguments FrgPhi {B BE N E V U}.

Arguments FrgRename {B BE N E V U}.

Arguments FrgParents {B BE N E V U}.

Arguments FrgFuel {B BE N E V U}.

Section Frg.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
  (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
  (bb : B -> nat) (beb : BE -> nat) (nb : N -> nat) (eb : E -> nat)
  (vb : V -> nat) (ub : U -> nat).

(** The FRG stage records child calls and maintains an expression-to-operand scope. *)
Let Call := pre_frg_call B BE N E V U.

Let Scope := Map.t U (frg_operand B E U * bool).

Fixpoint pre_frg_children_counted (bindings : list (B * B)) : exact_counted Call (Map.t B (list B))
  :=
  match bindings with
  | [] => exact_case 1800 (exact_return 1800 Map.empty)
  | (v,u) :: rest =>
    exact_case 1801
      (exact_bind 1802 (pre_frg_children_counted rest) (fun children =>
      exact_bind 1803 (exact_get (fun c => FrgRename (PrnChildren c)) EB bb u children) (fun found
        =>
      exact_bind 1804 (exact_case 1804 (exact_return 1804 (
        match found with
        | Some xs => xs
        | None => [] end))) (fun xs =>
        exact_set (fun c => FrgRename (PrnChildren c)) EB bb u (v :: xs) children)))) end.

Fixpoint pre_frg_length_counted {X} (xs : list X) : exact_counted Call nat :=
  match xs with
  | [] => exact_case 1805 (exact_return 1805 0)
  | _ :: rest =>
    exact_case 1806 (exact_bind 1806 (pre_frg_length_counted rest)
      (fun count => exact_return 1806 (Datatypes.S count))) end.

Definition pre_build_frg_from_graph
    (p : prepared EB (block_graph (pre_ssa_points a))) (tree : dom_tree B)
    (df : Map.t B (FinSet.t B)) : factored_redundancy_graph B BE E U :=
  let all_family := pre_expr_universe EBE EV EU a in
  let sites := AnalysesSsaPreGraph.pre_phi_sites_graph EB EU
    (AnalysesSsaPreGraph.pre_phi_graph_from EB EV EU a p df all_family) in
  let family := filter (pre_total_pure (pre_expression a)) all_family in
  let phis := AnalysesSsaPreGraph.pre_rename_phi_index EB EU a sites family in
  let phi_blocks := fold_left (AnalysesSsaPreGraph.pre_group_add EB EU) (FinSet.elements phis)
    Map.empty in
  let alterations := AnalysesSsaPreGraph.pre_rename_alter_index EE EV EU a family in
  let exits := AnalysesSsaPreGraph.pre_rename_exit_index EN a family in
  let arguments := AnalysesSsaPreGraph.pre_rename_argument_index EB EBE EU a p phis in
  let parents := Map.elements (idom tree) in
  let children := dom_children EB parents in
  let scope := AnalysesSsaPreGraph.pre_initial_scope EU a family in
  let roots := Graph.entries (block_graph (pre_ssa_points a)) in
  let initial := (map (fun b => (b,scope)) roots,FinSet.empty,
    PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty) in
  let result := AnalysesSsaPreGraph.pre_rename_run
    (AnalysesSsaPreGraph.pre_rename_step EB EBE EN EE EU a children alterations exits phi_blocks
      arguments)
    (Pos.of_succ_nat (length roots + length parents)) initial in
  let acc := snd result in
  FactoredRedundancyGraph (AnalysesSsaPreGraph.pre_rename_versions EB EE EU a family phis acc)
    (pre_rename_occurrences acc) (pre_rename_fresh acc) phis (pre_rename_links acc)
      (pre_rename_unsafe acc).

Definition pre_build_frg_from_graph_counted
    (p : prepared EB (block_graph (pre_ssa_points a))) (tree : dom_tree B)
    (df : Map.t B (FinSet.t B)) : exact_counted Call (factored_redundancy_graph B BE E U) :=
  exact_bind 1810 (exact_lift FrgFamily (pre_expr_universe_counted EBE EU a beb ub)) (fun all_family
    =>
  exact_bind 1811 (exact_lift FrgPhi (pre_phi_sites_counted EB EV EU a bb vb ub p df all_family))
    (fun sites =>
  exact_bind 1812 (exact_filter 1812 (fun u => let pure := pre_total_pure (pre_expression a) u in
    exact_call (FrgRename (PrnPure u pure)) 0 pure) all_family) (fun family =>
  exact_bind 1813 (exact_lift FrgRename (pre_rename_phi_index_counted EB EU a bb ub sites family))
    (fun phis =>
  exact_bind 1814 (exact_set_elements (fun c => FrgRename (PrnPhis c)) phis) (fun keys =>
  exact_bind 1815 (exact_fold_left 1815 (pre_group_add_counted (fun c => FrgRename (PrnGroupBU c))
    (fun c => FrgRename (PrnSetU c)) EB EU bb ub) keys Map.empty) (fun phi_blocks =>
  exact_bind 1816 (exact_lift FrgRename (pre_rename_alter_index_counted EE EV EU a eb vb ub family))
    (fun alterations =>
  exact_bind 1817 (exact_lift FrgRename (pre_rename_exit_index_counted EN a nb family)) (fun exits
    =>
  exact_bind 1818 (exact_lift FrgRename (pre_rename_argument_index_counted EB EBE EU a bb beb ub p
    phis))
    (fun arguments =>
  exact_bind 1819 (exact_elements FrgParents (idom tree)) (fun parents =>
  exact_bind 1820 (pre_frg_children_counted parents) (fun children =>
  exact_bind 1821 (exact_lift FrgRename (pre_rename_initial_counted EU a ub family)) (fun scope =>
  let roots := Graph.entries (block_graph (pre_ssa_points a)) in
  exact_bind 1822 (exact_map 1822 (fun b => exact_return 1822 (b,scope)) roots) (fun tasks =>
  exact_bind 1823 (pre_frg_length_counted roots) (fun roots_length =>
  exact_bind 1824 (pre_frg_length_counted parents) (fun parents_length =>
  let fuel := Pos.of_succ_nat (roots_length + parents_length) in
  exact_bind 1825 (exact_call (FrgFuel roots_length parents_length fuel)
    (64 * Datatypes.S (roots_length + parents_length) * Datatypes.S (Pos.size_nat fuel)) fuel) (fun
      fuel =>
  exact_bind 1826 (exact_lift FrgRename
    (pre_rename_run_counted (pre_rename_step_counted EB EBE EN EE EU a bb beb nb eb ub
      children alterations exits phi_blocks arguments) fuel
      (tasks,FinSet.empty,PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty))) (fun result
        =>
  let acc := snd result in
  exact_bind 1827 (exact_lift FrgRename (pre_rename_versions_counted EB EE EU a bb eb ub family phis
    acc))
    (fun versions => exact_return 1828 (FactoredRedundancyGraph versions (pre_rename_occurrences
      acc)
      (pre_rename_fresh acc) phis (pre_rename_links acc) (pre_rename_unsafe acc)))))))))))))))))))).

(** The counted FRG stage returns the plain stage and agrees with the public builder
    for its backends. *)
Definition pre_build_frg_from_graph_erases_statement : Prop :=
  (forall p tree df, exact_value (pre_build_frg_from_graph_counted p tree df) =
    pre_build_frg_from_graph p tree df) /\
  (forall p tree df,
    p = prepare EB (block_graph (pre_ssa_points a)) -> tree = dominator_tree p ->
    df = dominance_frontier p tree -> pre_build_frg_from_graph p tree df = build_frg EB EBE EN EE EV
      EU a).

(** Static value observer for the stage input. It contains raw list/trie sizes and actual
    encoder operands, never the counted trace or the returned work projection. *)
Definition pre_frg_from_graph_input_budget (p : prepared EB (block_graph (pre_ssa_points a)))
    (tree : dom_tree B) (df : Map.t B (FinSet.t B)) : nat :=
  let family := pre_expr_universe EBE EV EU a in
  let blocks := Graph.nodes (block_graph (pre_ssa_points a)) in
  let points := Graph.nodes (live_graph (point_model (pre_ssa_points a))) in
  let block_edges := edges_of (block_graph (pre_ssa_points a)) in
  let point_edges := edges_of (live_graph (point_model (pre_ssa_points a))) in
  let instructions := flat_map (instruction_edges (pre_ssa_points a)) blocks in
  let all_edges := point_edges ++ instructions ++ map (parameter_edge (pre_ssa_points a)) blocks in
  let values := pre_value_universe a ++ flat_map (block_params (pre_ssa_points a)) blocks ++
    flat_map (pre_operands a) (pre_seed_expressions a ++ family) ++
    flat_map (edge_def (point_model (pre_ssa_points a))) all_edges in
  let all_blocks := blocks ++ Graph.entries (block_graph (pre_ssa_points a)) ++
    map (home (pre_ssa_view a)) values ++
    flat_map (fun pair => [fst pair;snd pair]) (Map.elements (idom tree)) in
  let block_width := fold_right Nat.max 0 (map (fun b => bb b + Pos.size_nat (encode EB b))
    all_blocks) in
  let point_width := fold_right Nat.max 0 (map (fun n => nb n + Pos.size_nat (encode EN n)) points)
    in
  let edge_width := fold_right Nat.max 0 (map (fun e => eb e + Pos.size_nat (encode EE e))
    all_edges) in
  let be_width := fold_right Nat.max 0 (map (fun e => beb e + Pos.size_nat (encode EBE e))
    block_edges) in
  let value_width := fold_right Nat.max 0 (map (fun v => vb v + Pos.size_nat (encode EV v)) values)
    in
  let expr_width := fold_right Nat.max 0 (map (fun u => ub u + Pos.size_nat (encode EU u))
    (pre_seed_expressions a ++ family)) in
  let geometry := 1 + length blocks + length points + length block_edges + length all_edges +
    length values + length family + exact_trie_nodes (idom tree) + exact_trie_nodes df +
    exact_trie_nodes (in_index p) + exact_trie_nodes (out_index p) +
    fold_right (fun row n => exact_trie_nodes (snd row) + n) 0 (Map.elements df) in
  pre_family_input_budget EBE EU a beb ub EV +
    (Nat.of_num_uint 16777216%uint) * Nat.pow geometry 48 *
      Nat.pow (1 + block_width + point_width + edge_width + be_width + value_width + expr_width) 24.

(** The FRG stage erases and fits its input budget for the actual prepared backends. *)
Definition audit_pre_frg_from_graph_source_statement : Prop :=
  pre_build_frg_from_graph_erases_statement /\
  forall p tree df, pre_expr_ssa_laws EV a ->
    p = prepare EB (block_graph (pre_ssa_points a)) -> tree = dominator_tree p ->
    df = dominance_frontier p tree ->
    exact_units (pre_build_frg_from_graph_counted p tree df) <= pre_frg_from_graph_input_budget p
      tree df.

End Frg.
