(** * Complete SEG builder source contracts

    Record graph preparation, event tests, path splices, materialization and generated callbacks.
    For example, the returned sparse graph retains the final arc map of the same builder run.
    Builds on: graph and collection source models and expression SEG operations. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTrie
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements
  CollectionsAuditPrimitive CollectionsAuditCompare CollectionsAuditMapTraverse.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditDfs.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesSeg.
Import List.ListNotations.

(** * Complete SEG builder source contracts *)

(** Events retain every actual client callback input, result and body. *)
Inductive audit_seg_transfer_source_event (E U B : Type) : Type :=
  | SegTransferCase : nat -> audit_seg_transfer_source_event E U B
  | SegTransferGen : E -> list U -> list B -> audit_seg_transfer_source_event E U B
  | SegTransferKill : E -> U -> bool -> list B -> audit_seg_transfer_source_event E U B
  | SegTransferEncode : U -> positive -> list B -> audit_seg_transfer_source_event E U B
  | SegTransferEqual : positive -> positive -> bool -> list audit_positive_eqb_event ->
    audit_seg_transfer_source_event E U B.

Arguments SegTransferCase {E U B} _.

Arguments SegTransferGen {E U B} _ _ _.

Arguments SegTransferKill {E U B} _ _ _ _.

Arguments SegTransferEncode {E U B} _ _ _.

Arguments SegTransferEqual {E U B} _ _ _ _.

(** The strict mention scan visits every expression occurrence. *)
Fixpoint audit_seg_transfer_source_mentions {E U B} (enc : U -> positive * list B) (u : U)
    (values : list U)
    : bool * list (audit_seg_transfer_source_event E U B) :=
  match values with
  | [] => (false, [SegTransferCase 0])
  | v :: rest =>
    let '(a, ea) := enc u in let '(b, eb) := enc v in
    let '(equal, calls) := audit_positive_eqb a b in
    let '(later, events) := audit_seg_transfer_source_mentions enc u rest in
    (equal || later, SegTransferCase 1 :: SegTransferEncode u a ea :: SegTransferEncode v b eb ::
      SegTransferEqual a b equal calls :: events)
  end.

(** Generation and kill both execute for every event or transfer invocation. *)
Definition audit_seg_transfer_source_operands {E U B} (enc : U -> positive * list B)
    (gen_call : E -> list U * list B) (kill_call : E * U -> bool * list B) (u : U) (e : E)
    : (bool * bool) * list (audit_seg_transfer_source_event E U B) :=
  let '(generated, gen_body) := gen_call e in
  let '(found, mentions) := audit_seg_transfer_source_mentions (E := E) enc u generated in
  let '(killed, kill_body) := kill_call (e, u) in
  ((found, killed), SegTransferGen e generated gen_body :: mentions ++
    [SegTransferKill e u killed kill_body]).

(** Event detection returns the strict disjunction of the captured operands. *)
Definition audit_seg_event_source_counted {E U B} (enc : U -> positive * list B)
    (gen_call : E -> list U * list B) (kill_call : E * U -> bool * list B) (u : U) (e : E)
    : bool * list (audit_seg_transfer_source_event E U B) :=
  let '((found, killed), events) := audit_seg_transfer_source_operands enc gen_call kill_call u e in
  (found || killed, events ++ [SegTransferCase 2]).

(** Transfer uses the same operands and the supplied incoming Boolean. *)
Definition audit_seg_transfer_source_counted {E U B} (enc : U -> positive * list B)
    (gen_call : E -> list U * list B) (kill_call : E * U -> bool * list B) (u : U) (e : E)
    (b : bool)
    : bool * list (audit_seg_transfer_source_event E U B) :=
  let '((found, killed), events) := audit_seg_transfer_source_operands enc gen_call kill_call u e in
  (found || (b && negb killed), events ++ [SegTransferCase 3]).

(** Work includes actual equality source frames and supplied callback bodies. *)
Definition audit_seg_transfer_source_event_work {E U B} (weight : B -> nat)
    (event : audit_seg_transfer_source_event E U B) : nat :=
  64 + match event with
  | SegTransferGen _ _ body | SegTransferKill _ _ _ body | SegTransferEncode _ _ body =>
    fold_right (fun x n => weight x + n) 0 body
  | SegTransferEqual _ _ _ calls => audit_positive_eqb_source_work calls
  | SegTransferCase _ => 0
  end.

(** External work is the sum of actual generated, kill and encoder bodies. *)
Definition audit_seg_transfer_source_event_external {E U B} (weight : B -> nat)
    (event : audit_seg_transfer_source_event E U B) : nat :=
  match event with
  | SegTransferGen _ _ body | SegTransferKill _ _ _ body | SegTransferEncode _ _ body =>
    fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Work charges all source events and occurrence-list construction. *)
Definition audit_seg_transfer_source_work {E U B} (weight : B -> nat)
    (events : list (audit_seg_transfer_source_event E U B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_seg_transfer_source_event_work weight event + n) 0 events.

(** Callback cost is taken from the same recorded run. *)
Definition audit_seg_transfer_source_external {E U B} (weight : B -> nat)
    (events : list (audit_seg_transfer_source_event E U B)) : nat :=
  fold_right (fun event n => audit_seg_transfer_source_event_external weight event + n) 0 events.

(** The input bound uses actual generation output and encoded expression widths. *)
Definition audit_seg_transfer_source_budget {E U} (EU : encoding U) (gen_value : E -> list U)
    (u : U) (e : E) : nat :=
  let values := u :: gen_value e in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EU v)) values) in
  4096 * Nat.pow (S (length values + width)) 4.

(** With matching callbacks, event and transfer match their source results and have work bounds. *)
Definition audit_seg_transfer_source_statement : Prop :=
  forall S O N E U C B (EU : encoding U) (gk : genkill_view S O N E U C) u e b
    (enc : U -> positive * list B) (gen_call : E -> list U * list B)
    (kill_call : E * U -> bool * list B)
    (weight : B -> nat),
    (forall x, fst (enc x) = encode EU x) -> (forall x, fst (gen_call x) = gen gk x) ->
    (forall edge expression, fst (kill_call (edge, expression)) = kill gk edge expression) ->
    let '(event_result, event_calls) := audit_seg_event_source_counted enc gen_call kill_call u e in
    let '(transfer_result, transfer_calls) := audit_seg_transfer_source_counted enc gen_call
      kill_call u e b in
    event_result = seg_event EU gk u e /\ transfer_result = seg_bit_transfer EU gk u e b /\
      audit_seg_transfer_source_work weight event_calls <= audit_seg_transfer_source_budget EU
        (gen gk) u e + audit_seg_transfer_source_external weight event_calls /\
      audit_seg_transfer_source_work weight transfer_calls <= audit_seg_transfer_source_budget EU
        (gen gk) u e + audit_seg_transfer_source_external weight transfer_calls.

(** Each source event charges a genuine callback at its actual input. *)
Definition audit_seg_transfer_source_event_budget {E U B} (encode_budget : U -> nat)
    (gen_budget : E -> nat)
    (kill_budget : E * U -> nat) (event : audit_seg_transfer_source_event E U B) : nat :=
  match event with
  | SegTransferGen e _ _ => gen_budget e
  | SegTransferKill e u _ _ => kill_budget (e, u)
  | SegTransferEncode u _ _ => encode_budget u
  | _ => 0
  end.

(** Under callback laws, event and transfer results agree and both bounds charge actual calls. *)
Definition audit_seg_transfer_source_adapted_statement : Prop :=
  forall S O N E U C B (EU : encoding U) (gk : genkill_view S O N E U C) u e b
    (enc : U -> positive * list B) (gen_call : E -> list U * list B)
    (kill_call : E * U -> bool * list B)
    (weight : B -> nat) encode_source gen_source kill_source encode_budget gen_budget kill_budget,
    (forall x, fst (enc x) = encode EU x) -> (forall x, fst (gen_call x) = gen gk x) ->
    (forall edge expression, fst (kill_call (edge, expression)) = kill gk edge expression) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    audit_graph_external_callback_adapter gen_call weight gen_source gen_budget ->
    audit_graph_external_callback_adapter kill_call weight kill_source kill_budget ->
    let '(event_result, event_calls) := audit_seg_event_source_counted enc gen_call kill_call u e in
    let '(transfer_result, transfer_calls) := audit_seg_transfer_source_counted enc gen_call
      kill_call u e b in
    event_result = seg_event EU gk u e /\ transfer_result = seg_bit_transfer EU gk u e b /\
      audit_seg_transfer_source_work weight event_calls <= audit_seg_transfer_source_budget EU
        (gen gk) u e + fold_right (fun event n =>
          audit_seg_transfer_source_event_budget encode_budget gen_budget kill_budget event + n)
          0 event_calls /\
      audit_seg_transfer_source_work weight transfer_calls <= audit_seg_transfer_source_budget EU
        (gen gk) u e + fold_right (fun event n =>
          audit_seg_transfer_source_event_budget encode_budget gen_budget kill_budget event + n)
          0 transfer_calls.

(** The component contract includes strict event, transfer and equality source obligations. *)
Definition audit_seg_transfer_source_contract_statement : Prop :=
  audit_seg_transfer_source_statement /\ audit_seg_transfer_source_adapted_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement.

(** All supplied graph, encoder and expression callbacks retain actual source bodies. *)
Record audit_seg_build_callbacks (N E U B : Type) : Type := SegBuildCallbacks {
  seg_build_node_encode : N -> positive * list B;
  seg_build_edge_encode : E -> positive * list B;
  seg_build_expr_encode : U -> positive * list B;
  seg_build_out : N -> list E * list B;
  seg_build_target : E -> N * list B;
  seg_build_source : E -> N * list B;
  seg_build_gen : E -> list U * list B;
  seg_build_kill : E * U -> bool * list B
}.

Arguments seg_build_node_encode {N E U B} _ _.

Arguments seg_build_edge_encode {N E U B} _ _.

Arguments seg_build_expr_encode {N E U B} _ _.

Arguments seg_build_out {N E U B} _ _.

Arguments seg_build_target {N E U B} _ _.

Arguments seg_build_source {N E U B} _ _.

Arguments seg_build_gen {N E U B} _ _.

Arguments seg_build_kill {N E U B} _ _.

(** Events retain actual operands, intermediate maps and callback bodies. *)
Inductive audit_seg_build_event (N E U B : Type) : Type :=
  | SegBuildCase : nat -> audit_seg_build_event N E U B
  | SegBuildPrepare : audit_prepare_source_event N E B -> audit_seg_build_event N E U B
  | SegBuildOut : N -> list E -> list B -> audit_seg_build_event N E U B
  | SegBuildTarget : E -> N -> list B -> audit_seg_build_event N E U B
  | SegBuildSource : E -> N -> list B -> audit_seg_build_event N E U B
  | SegBuildTransfer : audit_seg_transfer_source_event E U B -> audit_seg_build_event N E U B
  | SegBuildSet : audit_set_event N B -> audit_seg_build_event N E U B
  | SegBuildAdj : audit_map_event N (list E) B -> audit_seg_build_event N E U B
  | SegBuildNodeMap : audit_map_event N E B -> audit_seg_build_event N E U B
  | SegBuildArcMap : audit_map_event E (seg_arc N E) B -> audit_seg_build_event N E U B
  | SegBuildOutput : nat -> audit_seg_build_event N E U B.

Arguments SegBuildCase {N E U B} _.

Arguments SegBuildPrepare {N E U B} _.

Arguments SegBuildOut {N E U B} _ _ _.

Arguments SegBuildTarget {N E U B} _ _ _.

Arguments SegBuildSource {N E U B} _ _ _.

Arguments SegBuildTransfer {N E U B} _.

Arguments SegBuildSet {N E U B} _.

Arguments SegBuildAdj {N E U B} _.

Arguments SegBuildNodeMap {N E U B} _.

Arguments SegBuildArcMap {N E U B} _.

Arguments SegBuildOutput {N E U B} _.

(** Edge enumeration invokes the original outgoing callback at each listed node. *)
Fixpoint audit_seg_build_edges {N E U B} (cb : audit_seg_build_callbacks N E U B) (nodes : list N)
    : list E * list (audit_seg_build_event N E U B) :=
  match nodes with
  | [] => ([], [SegBuildCase 0])
  | n :: rest => let '(edges, body) := seg_build_out cb n in
    let '(later, events) := audit_seg_build_edges cb rest in
    (edges ++ later, SegBuildCase 1 :: SegBuildOut n edges body :: events ++
      [SegBuildOutput (length edges)])
  end.

(** Event endpoints use the exact transfer-predicate source and conditional endpoint calls. *)
Fixpoint audit_seg_build_points {N E U B} (cb : audit_seg_build_callbacks N E U B) (u : U)
    (edges : list E)
    : FinSet.t N * list (audit_seg_build_event N E U B) :=
  match edges with
  | [] => (FinSet.empty, [SegBuildCase 2])
  | e :: rest =>
    let '(middle, later) := audit_seg_build_points cb u rest in
    let '(event, calls) := audit_seg_event_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e in
    if event then
      let '(src, sb) := seg_build_source cb e in let '(dst, db) := seg_build_target cb e in
      let '(after_dst, dst_calls) := audit_finset_add (seg_build_node_encode cb) dst middle in
      let '(result, src_calls) := audit_finset_add (seg_build_node_encode cb) src after_dst in
      (result, SegBuildCase 3 :: later ++ map SegBuildTransfer calls ++
        [SegBuildSource e src sb; SegBuildTarget e dst db] ++ map SegBuildSet dst_calls ++
        map SegBuildSet src_calls)
    else (middle, SegBuildCase 4 :: later ++ map SegBuildTransfer calls)
  end.

(** Both boundary membership tests execute; predecessor lookup follows a singleton successor. *)
Fixpoint audit_seg_build_candidates {N E U B} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (cb : audit_seg_build_callbacks N E U B) (points entries : FinSet.t N)
    (nodes : list N)
    : Map.t N E * list (audit_seg_build_event N E U B) :=
  match nodes with
  | [] => (Map.empty, [SegBuildCase 5])
  | n :: rest =>
    let '(middle, later) := audit_seg_build_candidates p cb points entries rest in
    let '(point, pcalls) := audit_finset_mem (seg_build_node_encode cb) n points in
    let '(entry, ecalls) := audit_finset_mem (seg_build_node_encode cb) n entries in
    if point || entry then
      (middle, SegBuildCase 6 :: later ++ map SegBuildSet pcalls ++ map SegBuildSet ecalls)
    else
      let '(out, out_calls) := audit_map_get (seg_build_node_encode cb) n (out_index p) in
      let successors := match out with
      Some es => es
      | None => []
      end in
      match successors with
      | [edge] =>
        let '(incoming, in_calls) := audit_map_get (seg_build_node_encode cb) n (in_index p) in
        let predecessors := match incoming with
        Some es => es
        | None => []
        end in
        match predecessors with
        | [_] =>
          let '(result, writes) := audit_map_set (seg_build_node_encode cb) n edge middle in
          (result, SegBuildCase 7 :: later ++ map SegBuildSet pcalls ++ map SegBuildSet ecalls
            ++ map SegBuildAdj out_calls ++ map SegBuildAdj in_calls ++
            map SegBuildNodeMap writes)
        | _ => (middle, SegBuildCase 8 :: later ++ map SegBuildSet pcalls ++
          map SegBuildSet ecalls ++
          map SegBuildAdj out_calls ++ map SegBuildAdj in_calls)
        end
      | _ => (middle, SegBuildCase 9 :: later ++ map SegBuildSet pcalls ++
        map SegBuildSet ecalls ++ map SegBuildAdj out_calls)
      end
  end.

(** The incoming index retains one target call and map write per edge occurrence. *)
Fixpoint audit_seg_build_incoming {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (edges : list E)
    : Map.t N E * list (audit_seg_build_event N E U B) :=
  match edges with
  | [] => (Map.empty, [SegBuildCase 10])
  | e :: rest =>
    let '(middle, later) := audit_seg_build_incoming cb rest in
    let '(dst, body) := seg_build_target cb e in
    let '(result, writes) := audit_map_set (seg_build_node_encode cb) dst e middle in
    (result, SegBuildCase 11 :: later ++ [SegBuildTarget e dst body] ++
      map SegBuildNodeMap writes)
  end.

(** Initial arcs evaluate all four source transfer applications for each edge. *)
Fixpoint audit_seg_build_arcs {N E U B} (cb : audit_seg_build_callbacks N E U B) (u : U)
    (edges : list E)
    : Map.t E (seg_arc N E) * list (audit_seg_build_event N E U B) :=
  match edges with
  | [] => (Map.empty, [SegBuildCase 12])
  | e :: rest =>
    let '(middle, later) := audit_seg_build_arcs cb u rest in
    let '(dst, body) := seg_build_target cb e in
    let '(ff, ef) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e false in
    let '(ft, et) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e true in
    let '(bf, ebf) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e false in
    let '(bt, ebt) := audit_seg_transfer_source_counted (seg_build_expr_encode cb)
      (seg_build_gen cb) (seg_build_kill cb) u e true in
    let arc := SegArc dst (SegLeaf e) (ff, ft) (bf, bt) in
    let '(result, writes) := audit_map_set (seg_build_edge_encode cb) e arc middle in
    (result, SegBuildCase 13 :: later ++ [SegBuildTarget e dst body] ++ map SegBuildTransfer ef ++
      map SegBuildTransfer et ++ map SegBuildTransfer ebf ++ map SegBuildTransfer ebt ++
      map SegBuildArcMap writes)
  end.

(** The actual initial work contains separately constructed alive, incoming and arc maps. *)
Definition audit_seg_build_initial {N E U B} (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B)
    (u : U) (edges : list E) : seg_work N E * list (audit_seg_build_event N E U B) :=
  let '(alive, alive_calls) := audit_finset_of_list (seg_build_node_encode cb) (Graph.nodes g) in
  let '(incoming, incoming_calls) := audit_seg_build_incoming cb edges in
  let '(arcs, arc_calls) := audit_seg_build_arcs cb u edges in
  (SegWork alive incoming arcs, map SegBuildSet alive_calls ++ incoming_calls ++ arc_calls).

(** Events retain each actual operand, encoder body and equality trace. *)
Inductive audit_seg_splice_event (N E B : Type) : Type :=
  | SegSpliceCase : nat -> audit_seg_splice_event N E B
  | SegSpliceSet : audit_set_event N B -> audit_seg_splice_event N E B
  | SegSpliceNodeMap : audit_map_event N E B -> audit_seg_splice_event N E B
  | SegSpliceArcMap : audit_map_event E (seg_arc N E) B -> audit_seg_splice_event N E B
  | SegSpliceEncode : E -> positive -> list B -> audit_seg_splice_event N E B
  | SegSpliceEqual : positive -> positive -> bool -> list audit_positive_eqb_event ->
    audit_seg_splice_event N E B.

Arguments SegSpliceCase {N E B} _.

Arguments SegSpliceSet {N E B} _.

Arguments SegSpliceNodeMap {N E B} _.

Arguments SegSpliceArcMap {N E B} _.

Arguments SegSpliceEncode {N E B} _ _ _.

Arguments SegSpliceEqual {N E B} _ _ _ _.

(** Two constant-size tables compose without inspecting the stored rope. *)
Definition audit_seg_splice_compose (first second : bool * bool) : bool * bool :=
  (if fst first then snd second else fst second, if snd first then snd second else fst second).

(** An actual join constructs one rope node and both composed truth tables. *)
Definition audit_seg_splice_join {N E} (first second : seg_arc N E) : seg_arc N E :=
  SegArc (seg_tip second) (SegAppend (seg_rope_value first) (seg_rope_value second))
    (audit_seg_splice_compose (seg_fw first) (seg_fw second))
    (audit_seg_splice_compose (seg_bw second) (seg_bw first)).

(** A successful merge performs the source's remove and map updates on actual intermediates. *)
Definition audit_seg_splice_merge {N E B} (encn : N -> positive * list B)
    (ence : E -> positive * list B)
    (n : N) (a b : E) (first second : seg_arc N E) (work : seg_work N E)
    : seg_work N E * list (audit_seg_splice_event N E B) :=
  let '(alive, alive_calls) := audit_finset_remove encn n (seg_alive work) in
  let '(incoming, incoming_calls) := audit_map_set encn (seg_tip second) a (seg_incoming work) in
  let '(removed, remove_calls) := audit_map_remove ence b (seg_arcs work) in
  let '(arcs, arc_calls) := audit_map_set ence a (audit_seg_splice_join first second) removed in
  (SegWork alive incoming arcs, map SegSpliceSet alive_calls ++ map SegSpliceNodeMap
    incoming_calls ++
    map SegSpliceArcMap remove_calls ++ map SegSpliceArcMap arc_calls ++ [SegSpliceCase 0]).

(** Lookup matching stops as soon as a required candidate or arc is missing. *)
Definition audit_seg_splice_source_counted {N E B} (encn : N -> positive * list B)
    (ence : E -> positive * list B) (candidates : Map.t N E) (n : N) (work : seg_work N E)
    : seg_work N E * list (audit_seg_splice_event N E B) :=
  let '(alive, alive_calls) := audit_finset_mem encn n (seg_alive work) in
  if alive then
    let '(candidate, candidate_calls) := audit_map_get encn n candidates in
    match candidate with
    | None => (work, map SegSpliceSet alive_calls ++ map SegSpliceNodeMap candidate_calls ++
      [SegSpliceCase 1])
    | Some b =>
      let '(incoming, incoming_calls) := audit_map_get encn n (seg_incoming work) in
      match incoming with
      | None => (work, map SegSpliceSet alive_calls ++ map SegSpliceNodeMap candidate_calls ++
        map SegSpliceNodeMap incoming_calls ++ [SegSpliceCase 2])
      | Some a =>
        let '(ca, ba) := ence a in let '(cb, bb) := ence b in
        let '(same, eq_calls) := audit_positive_eqb ca cb in
        let prefix := map SegSpliceSet alive_calls ++ map SegSpliceNodeMap candidate_calls ++
          map SegSpliceNodeMap incoming_calls ++ [SegSpliceEncode a ca ba; SegSpliceEncode b cb
            bb;
            SegSpliceEqual ca cb same eq_calls] in
        if same then (work, prefix ++ [SegSpliceCase 3]) else
          let '(first, first_calls) := audit_map_get ence a (seg_arcs work) in
          match first with
          | None => (work, prefix ++ map SegSpliceArcMap first_calls ++ [SegSpliceCase 4])
          | Some x =>
            let '(second, second_calls) := audit_map_get ence b (seg_arcs work) in
            match second with
            | None => (work, prefix ++ map SegSpliceArcMap first_calls ++
              map SegSpliceArcMap second_calls ++ [SegSpliceCase 5])
            | Some y =>
              let '(result, calls) := audit_seg_splice_merge encn ence n a b x y work in
              (result, prefix ++ map SegSpliceArcMap first_calls ++
                map SegSpliceArcMap second_calls ++ calls)
            end
          end
      end
    end
  else (work, map SegSpliceSet alive_calls ++ [SegSpliceCase 6]).

(** The counted operation erases to the exact source splice for arbitrary work states. *)
Definition audit_seg_splice_source_erasure_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (encn : N -> positive * list B)
    (ence : E -> positive * list B) candidates n work,
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    fst (audit_seg_splice_source_counted encn ence candidates n work) =
      AnalysesSeg.seg_splice EN EE candidates n work.

(** Work expands actual map, set and positive-equality bodies. *)
Definition audit_seg_splice_event_work {N E B} (weight : B -> nat)
    (event : audit_seg_splice_event N E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SegSpliceCase _ => 0
  | SegSpliceSet call => audit_finset_source_work body [call]
  | SegSpliceNodeMap call => audit_map_source_work body [call]
  | SegSpliceArcMap call => audit_map_source_work body [call]
  | SegSpliceEncode _ _ xs => body xs
  | SegSpliceEqual _ _ _ calls => audit_positive_eqb_source_work calls
  end.

(** Only actual client encoder bodies are external. *)
Definition audit_seg_splice_event_external {N E B} (weight : B -> nat)
    (event : audit_seg_splice_event N E B) : nat :=
  match event with
  | SegSpliceEncode _ _ body | SegSpliceSet (AuditSetMem _ _ _ _ body _) |
    SegSpliceSet (AuditSetAdd _ _ _ _ body _) | SegSpliceSet (AuditSetRemove _ _ _ _ body _) |
    SegSpliceNodeMap (AuditMapGet _ _ _ _ body _) |
    SegSpliceNodeMap (AuditMapSet _ _ _ _ _ body _) |
    SegSpliceNodeMap (AuditMapRemove _ _ _ _ body _) |
    SegSpliceArcMap (AuditMapGet _ _ _ _ body _) |
    SegSpliceArcMap (AuditMapSet _ _ _ _ _ body _) |
    SegSpliceArcMap (AuditMapRemove _ _ _ _ body _) =>
    fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Splice work includes all trace and output concatenation. *)
Definition audit_seg_splice_source_work {N E B} (weight : B -> nat)
    (events : list (audit_seg_splice_event N E B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_seg_splice_event_work weight event + n) 0 events.

(** External work uses this same invocation's captured bodies. *)
Definition audit_seg_splice_source_external {N E B} (weight : B -> nat)
    (events : list (audit_seg_splice_event N E B)) : nat :=
  fold_right (fun event n => audit_seg_splice_event_external weight event + n) 0 events.

(** The bound uses actual input key widths and map dimensions. *)
Definition audit_seg_splice_source_budget {N E} (EN : encoding N) (EE : encoding E)
    (candidates : Map.t N E) (n : N) (work : seg_work N E) : nat :=
  let cs := Map.elements candidates in let ins := Map.elements (seg_incoming work) in
  let arcs := Map.elements (seg_arcs work) in
  let nodes := n :: map fst cs ++ map fst ins ++ map (fun row => seg_tip (snd row)) arcs in
  let edges := map snd cs ++ map snd ins ++ map fst arcs in
  let nw := fold_right Nat.max 0 (map (fun x => Pos.size_nat (encode EN x)) nodes) in
  let ew := fold_right Nat.max 0 (map (fun x => Pos.size_nat (encode EE x)) edges) in
  4096 * Nat.pow (S (length nodes + length edges + nw + ew)) 6.

(** With matching encoders, the source result equals the splice and its work obeys the bound. *)
Definition audit_seg_splice_source_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (encn : N -> positive * list B)
    (ence : E -> positive * list B) candidates n work (weight : B -> nat),
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    let '(result, events) := audit_seg_splice_source_counted encn ence candidates n work in
    result = AnalysesSeg.seg_splice EN EE candidates n work /\
      audit_seg_splice_source_work weight events <=
        audit_seg_splice_source_budget EN EE candidates n work +
        audit_seg_splice_source_external weight events.

(** Each encoder budget is applied at the actual source-call key. *)
Definition audit_seg_splice_event_budget {N E B} (node_budget : N -> nat) (edge_budget : E -> nat)
    (event : audit_seg_splice_event N E B) : nat :=
  match event with
  | SegSpliceSet (AuditSetMem n _ _ _ _ _) | SegSpliceSet (AuditSetAdd n _ _ _ _ _) |
    SegSpliceSet (AuditSetRemove n _ _ _ _ _) | SegSpliceNodeMap (AuditMapGet n _ _ _ _ _) |
    SegSpliceNodeMap (AuditMapSet n _ _ _ _ _ _) | SegSpliceNodeMap (AuditMapRemove n _ _ _ _ _) =>
    node_budget n
  | SegSpliceArcMap (AuditMapGet e _ _ _ _ _) | SegSpliceArcMap (AuditMapSet e _ _ _ _ _ _) |
    SegSpliceArcMap (AuditMapRemove e _ _ _ _ _) | SegSpliceEncode e _ _ => edge_budget e
  | _ => 0
  end.

(** Under node and edge callback laws, the splice result agrees and its work obeys the bound. *)
Definition audit_seg_splice_source_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (encn : N -> positive * list B)
    (ence : E -> positive * list B) candidates n work (weight : B -> nat)
    node_source edge_source node_budget edge_budget,
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    audit_graph_external_callback_adapter encn weight node_source node_budget ->
    audit_graph_external_callback_adapter ence weight edge_source edge_budget ->
    let '(result, events) := audit_seg_splice_source_counted encn ence candidates n work in
    result = AnalysesSeg.seg_splice EN EE candidates n work /\
      audit_seg_splice_source_work weight events <=
        audit_seg_splice_source_budget EN EE candidates n work +
        fold_right (fun event total => audit_seg_splice_event_budget node_budget edge_budget event +
          total) 0 events.

(** The component contract includes its collection and equality source obligations. *)
Definition audit_seg_splice_source_contract_statement : Prop :=
  audit_seg_splice_source_erasure_statement /\ audit_seg_splice_source_statement /\
  audit_seg_splice_source_adapted_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_map_remove_source_work_bound_statement /\
  audit_finset_mem_erases_statement /\ audit_positive_eqb_source_bound_statement.

(** Rope frames retain the actual path structure and suffix. *)
Inductive audit_seg_rope_event (E : Type) : Type :=
  | SegRopeLeaf : E -> list E -> audit_seg_rope_event E
  | SegRopeAppend : seg_rope E -> seg_rope E -> list E -> audit_seg_rope_event E.

Arguments SegRopeLeaf {E} _ _.

Arguments SegRopeAppend {E} _ _ _.

(** Rope flattening follows the actual accumulator-passing source traversal. *)
Fixpoint audit_seg_rope_onto {E} (rope : seg_rope E) (tail : list E) :
    list E * list (audit_seg_rope_event E) :=
  match rope with
  | SegLeaf e => (e :: tail, [SegRopeLeaf e tail])
  | SegAppend first second =>
    let '(suffix, right_events) := audit_seg_rope_onto second tail in
    let '(result, left_events) := audit_seg_rope_onto first suffix in
    (result, SegRopeAppend first second tail :: right_events ++ left_events)
  end.

(** Finish events retain map traversal, list frames, target calls and actual writes. *)
Inductive audit_seg_finish_event (N E B : Type) : Type :=
  | SegFinishCase : nat -> audit_seg_finish_event N E B
  | SegFinishRopeMap :
    audit_map_transform_event E (seg_arc N E) (list E) (audit_seg_rope_event E) ->
    audit_seg_finish_event N E B
  | SegFinishSummary : audit_map_transform_event E (seg_arc N E) (bool * bool) unit ->
    audit_seg_finish_event N E B
  | SegFinishElements : audit_elements_event (E * list E) -> audit_seg_finish_event N E B
  | SegFinishTarget : E -> N -> list B -> audit_seg_finish_event N E B
  | SegFinishSet : audit_set_event N B -> audit_seg_finish_event N E B
  | SegFinishInterior : audit_map_event N (E * nat) B -> audit_seg_finish_event N E B
  | SegFinishList : nat -> audit_seg_finish_event N E B.

Arguments SegFinishCase {N E B} _.

Arguments SegFinishRopeMap {N E B} _.

Arguments SegFinishSummary {N E B} _.

Arguments SegFinishElements {N E B} _.

Arguments SegFinishTarget {N E B} _ _ _.

Arguments SegFinishSet {N E B} _.

Arguments SegFinishInterior {N E B} _.

Arguments SegFinishList {N E B} _.

(** The list pass removes the last edge and records each source constructor. *)
Fixpoint audit_seg_removelast {N E B} (edges : list E)
    : list E * list (audit_seg_finish_event N E B) :=
  match edges with
  | [] => ([], [SegFinishCase 0])
  | e :: rest => match rest with
    | [] => ([], [SegFinishCase 1])
    | _ :: _ => let '(later, events) := audit_seg_removelast rest in
      (e :: later, SegFinishCase 2 :: events)
    end
  end.

(** Interior position creation calls target once per retained path edge. *)
Fixpoint audit_seg_finish_positions {N E B} (target : E -> N * list B) (arc : E)
    (edges : list E) (offset : nat) : list (N * (E * nat)) * list (audit_seg_finish_event N E B) :=
  match edges with
  | [] => ([], [SegFinishCase 3])
  | e :: rest => let '(node, body) := target e in
    let '(later, events) := audit_seg_finish_positions target arc rest (S offset) in
    ((node, (arc, offset)) :: later, SegFinishCase 4 :: SegFinishTarget e node body :: events)
  end.

(** Position lists preserve each path and source flattening order. *)
Fixpoint audit_seg_finish_path_rows {N E B} (target : E -> N * list B) (paths : list (E * list E))
    : list (N * (E * nat)) * list (audit_seg_finish_event N E B) :=
  match paths with
  | [] => ([], [SegFinishCase 5])
  | (arc, path) :: rest =>
    let '(interior, remove_calls) := audit_seg_removelast path in
    let '(first, pos_calls) := audit_seg_finish_positions target arc interior 0 in
    let '(later, events) := audit_seg_finish_path_rows target rest in
    (first ++ later, SegFinishCase 6 :: remove_calls ++ pos_calls ++ events ++
      [SegFinishList (length first)])
  end.

(** Interior indexing follows the source fold-left and retains every map update. *)
Fixpoint audit_seg_finish_interior {N E B} (enc : N -> positive * list B)
    (rows : list (N * (E * nat))) (index : Map.t N (E * nat))
    : Map.t N (E * nat) * list (audit_seg_finish_event N E B) :=
  match rows with
  | [] => (index, [SegFinishCase 7])
  | (n, value) :: rest =>
    let '(next, writes) := audit_map_set enc n value index in
    let '(result, events) := audit_seg_finish_interior enc rest next in
    (result, SegFinishCase 8 :: map SegFinishInterior writes ++ events)
  end.

(** Every original node receives its actual live-set membership test. *)
Fixpoint audit_seg_finish_nodes {N E B} (enc : N -> positive * list B) (alive : FinSet.t N)
    (nodes : list N)
    : list N * list (audit_seg_finish_event N E B) :=
  match nodes with
  | [] => ([], [SegFinishCase 9])
  | n :: rest => let '(found, calls) := audit_finset_mem enc n alive in
    let '(later, events) := audit_seg_finish_nodes enc alive rest in
    (if found then n :: later else later, SegFinishCase 10 :: map SegFinishSet calls ++ events)
  end.

(** All output maps and the returned graph close over the actual captured work state. *)
Definition audit_seg_finish_source_counted {N E B} {EN : encoding N} {g : Graph.t N E}
    (EE : encoding E) (p : prepared EN g) (encn : N -> positive * list B) (target : E -> N * list B)
    (work : seg_work N E) : seg_index N E * list (audit_seg_finish_event N E B) :=
  let '(paths, path_calls) := audit_map_transform
    (fun arc => audit_seg_rope_onto (seg_rope_value arc) []) (seg_arcs work) in
  let '(path_rows, elements) := audit_map_elements paths in
  let '(bindings, position_calls) := audit_seg_finish_path_rows target path_rows in
  let '(interiors, interior_calls) := audit_seg_finish_interior encn bindings Map.empty in
  let '(forward, forward_calls) :=
    audit_map_transform (fun arc => (seg_fw arc, [])) (seg_arcs work) in
  let '(backward, backward_calls) :=
    audit_map_transform (fun arc => (seg_bw arc, [])) (seg_arcs work) in
  let '(nodes, node_calls) := audit_seg_finish_nodes encn (seg_alive work) (Graph.nodes g) in
  let graph := Graph.Make (Graph.entries g) nodes
    (fun n => if FinSet.mem EN n (seg_alive work) then succ_edges p n else []) (Graph.source g)
    (fun e => match Map.get EE e (seg_arcs work) with
      Some arc => seg_tip arc
      | None => Graph.target g e
      end) in
  (SegIndex graph paths interiors forward backward,
    map SegFinishRopeMap path_calls ++ map SegFinishElements elements ++ position_calls ++
    interior_calls ++ map SegFinishSummary forward_calls ++ map SegFinishSummary backward_calls ++
    node_calls).

(** The finished source result is the exact SEG index for the original work state. *)
Definition audit_seg_finish_source_erasure_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (enc : N -> positive * list B) (target : E -> N * list B) work,
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    fst (audit_seg_finish_source_counted EE p enc target work) =
      AnalysesSeg.seg_finish EN EE g p work.

(** Internal events retain actual captured collection and supplied callback bodies. *)
Inductive audit_seg_graph_body (N E B : Type) : Type :=
  | SegGraphSet : audit_set_event N B -> audit_seg_graph_body N E B
  | SegGraphAdj : audit_map_event N (list E) B -> audit_seg_graph_body N E B
  | SegGraphArc : audit_map_event E (seg_arc N E) B -> audit_seg_graph_body N E B
  | SegGraphTarget : E -> N -> list B -> audit_seg_graph_body N E B
  | SegGraphSource : E -> N -> list B -> audit_seg_graph_body N E B
  | SegGraphNodeEncode : N -> positive -> list B -> audit_seg_graph_body N E B
  | SegGraphEdgeEncode : E -> positive -> list B -> audit_seg_graph_body N E B
  | SegGraphCase : nat -> audit_seg_graph_body N E B.

Arguments SegGraphSet {N E B} _.

Arguments SegGraphAdj {N E B} _.

Arguments SegGraphArc {N E B} _.

Arguments SegGraphTarget {N E B} _ _ _.

Arguments SegGraphSource {N E B} _ _ _.

Arguments SegGraphNodeEncode {N E B} _ _ _.

Arguments SegGraphEdgeEncode {N E B} _ _ _.

Arguments SegGraphCase {N E B} _.

(** The generated outgoing closure first checks the captured alive set. *)
Definition audit_seg_graph_out {N E B} {EN : encoding N} {g : Graph.t N E} (p : prepared EN g)
    (enc : N -> positive * list B) (work : seg_work N E) (n : N) :
    list E * list (audit_seg_graph_body N E B) :=
  let '(alive, reads) := audit_finset_mem enc n (seg_alive work) in
  if alive then let '(found, calls) := audit_map_get enc n (out_index p) in
    (match found with
    Some edges => edges
    | None => []
    end, map SegGraphSet reads ++ map SegGraphAdj calls)
  else ([], map SegGraphSet reads ++ [SegGraphCase 0]).

(** The generated target closure falls back only when the captured arc is absent. *)
Definition audit_seg_graph_target {N E B} (enc : E -> positive * list B) (target : E -> N * list B)
    (work : seg_work N E) (e : E) : N * list (audit_seg_graph_body N E B) :=
  let '(found, reads) := audit_map_get enc e (seg_arcs work) in
  match found with
  | Some arc => (seg_tip arc, map SegGraphArc reads ++ [SegGraphCase 1])
  | None => let '(dst, body) := target e in
    (dst, map SegGraphArc reads ++ [SegGraphTarget e dst body])
  end.

(** The source closure delegates to the original graph callback at the same edge. *)
Definition audit_seg_graph_source {N E B} (source : E -> N * list B) (e : E) :
    N * list (audit_seg_graph_body N E B) :=
  let '(n, body) := source e in (n, [SegGraphSource e n body]).

(** The generated node encoder captures the actual supplied node callback. *)
Definition audit_seg_graph_node_encode {N E B} (enc : N -> positive * list B) (n : N)
    : positive * list (audit_seg_graph_body N E B) :=
  let '(code, body) := enc n in (code, [SegGraphNodeEncode n code body]).

(** The generated edge encoder captures the actual supplied edge callback. *)
Definition audit_seg_graph_edge_encode {N E B} (enc : E -> positive * list B) (e : E)
    : positive * list (audit_seg_graph_body N E B) :=
  let '(code, body) := enc e in (code, [SegGraphEdgeEncode e code body]).

(** These are the returned graph's exact outgoing, source and target callbacks. *)
Definition audit_seg_graph_callbacks_erasure_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (encn : N -> positive * list B) (ence : E -> positive * list B)
    (target source : E -> N * list B) work,
    (forall n, fst (encn n) = encode EN n) -> (forall e, fst (ence e) = encode EE e) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall e, fst (source e) = Graph.source g e) ->
    let idx := AnalysesSeg.seg_finish EN EE g p work in
    (forall n, fst (audit_seg_graph_out p encn work n) = Graph.out (seg_graph idx) n) /\
    (forall e, fst (audit_seg_graph_target ence target work e) = Graph.target (seg_graph idx) e) /\
    (forall e, fst (audit_seg_graph_source source e) = Graph.source (seg_graph idx) e).

(** Rope source work pays a fixed amount for every visited constructor. *)
Definition audit_seg_rope_source_work {E} (events : list (audit_seg_rope_event E)) : nat :=
  8 * length events.

(** Finish work expands map transformations, rope callbacks, enumeration and actual client
    bodies. *)
Definition audit_seg_finish_event_work {N E B} (weight : B -> nat)
    (event : audit_seg_finish_event N E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SegFinishCase _ => 0
  | SegFinishRopeMap call => audit_map_transform_source_work audit_seg_rope_source_work [call]
  | SegFinishSummary call => audit_map_transform_source_work (fun _ => 0) [call]
  | SegFinishElements call => audit_elements_frame_work call
  | SegFinishTarget _ _ xs => body xs
  | SegFinishSet call => audit_finset_source_work body [call]
  | SegFinishInterior call => audit_map_source_work body [call]
  | SegFinishList n => S n
  end.

(** Only original node encoders and target callbacks carry external work. *)
Definition audit_seg_finish_event_external {N E B} (weight : B -> nat)
    (event : audit_seg_finish_event N E B) : nat :=
  match event with
  | SegFinishTarget _ _ body | SegFinishSet (AuditSetMem _ _ _ _ body _) |
    SegFinishSet (AuditSetAdd _ _ _ _ body _) | SegFinishSet (AuditSetRemove _ _ _ _ body _) |
    SegFinishInterior (AuditMapGet _ _ _ _ body _) | SegFinishInterior (AuditMapSet _ _ _ _ _ body
      _) |
    SegFinishInterior (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** The full finish measure accounts for trace and position-list concatenation. *)
Definition audit_seg_finish_source_work {N E B} (weight : B -> nat)
    (events : list (audit_seg_finish_event N E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_seg_finish_event_work weight event + n) 0 events.

(** External work is summed from this execution's actual callbacks. *)
Definition audit_seg_finish_source_external {N E B} (weight : B -> nat)
    (events : list (audit_seg_finish_event N E B)) : nat :=
  fold_right (fun event n => audit_seg_finish_event_external weight event + n) 0 events.

(** Every stored rope node contributes to the input traversal size. *)
Fixpoint audit_seg_rope_input_size {E} (rope : seg_rope E) : nat :=
  match rope with
  SegLeaf _ => 1
  | SegAppend first second =>
    S (audit_seg_rope_input_size first + audit_seg_rope_input_size second)
  end.

(** The bound uses actual graph nodes, arc keys, ropes and their target encodings. *)
Definition audit_seg_finish_source_budget {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (work : seg_work N E) : nat :=
  let arcs := Map.elements (seg_arcs work) in
  let paths := flat_map (fun row => AnalysesSeg.seg_rope_edges (seg_rope_value (snd row))) arcs in
  let nodes := Graph.nodes g ++ map (Graph.target g) paths in
  let nw := fold_right Nat.max 0 (map (fun n => Pos.size_nat (encode EN n)) nodes) in
  let ew := fold_right Nat.max 0 (map (fun row => Pos.size_nat (encode EE (fst row))) arcs) in
  let ropes := fold_right (fun row n => audit_seg_rope_input_size (seg_rope_value (snd row)) + n) 0
    arcs in
  (N.to_nat 1048576%N) * Nat.pow (S (length nodes + length arcs + length paths + nw + ew + ropes +
    audit_trie_nodes (seg_arcs work) + audit_trie_output_bits (seg_arcs work))) 12.

(** With matching callbacks, finish returns the source index and obeys the input-derived bound. *)
Definition audit_seg_finish_source_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (enc : N -> positive * list B) (target : E -> N * list B) work (weight : B -> nat),
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    let '(result, events) := audit_seg_finish_source_counted EE p enc target work in
    result = AnalysesSeg.seg_finish EN EE g p work /\ audit_seg_finish_source_work weight events <=
      audit_seg_finish_source_budget EN EE g work + audit_seg_finish_source_external weight events.

(** A generated graph callback expands its actual captured primitive bodies. *)
Definition audit_seg_graph_body_work {N E B} (weight : B -> nat)
    (event : audit_seg_graph_body N E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SegGraphSet call => audit_finset_source_work body [call]
  | SegGraphAdj call => audit_map_source_work body [call]
  | SegGraphArc call => audit_map_source_work body [call]
  | SegGraphTarget _ _ xs | SegGraphSource _ _ xs | SegGraphNodeEncode _ _ xs |
    SegGraphEdgeEncode _ _ xs => body xs
  | SegGraphCase _ => 0
  end.

(** Only original graph and encoder callbacks contribute external body work. *)
Definition audit_seg_graph_body_external {N E B} (weight : B -> nat)
    (event : audit_seg_graph_body N E B) : nat :=
  match event with
  | SegGraphTarget _ _ body | SegGraphSource _ _ body | SegGraphNodeEncode _ _ body |
    SegGraphEdgeEncode _ _ body |
    SegGraphSet (AuditSetMem _ _ _ _ body _) | SegGraphSet (AuditSetAdd _ _ _ _ body _) |
    SegGraphSet (AuditSetRemove _ _ _ _ body _) | SegGraphAdj (AuditMapGet _ _ _ _ body _) |
    SegGraphAdj (AuditMapSet _ _ _ _ _ body _) | SegGraphAdj (AuditMapRemove _ _ _ _ body _) |
    SegGraphArc (AuditMapGet _ _ _ _ body _) | SegGraphArc (AuditMapSet _ _ _ _ _ body _) |
    SegGraphArc (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Callback budgets apply to the actual captured node or edge. *)
Definition audit_seg_graph_body_budget {N E B} (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat)
    (event : audit_seg_graph_body N E B) : nat :=
  match event with
  | SegGraphTarget e _ _ => target_budget e
  | SegGraphSource e _ _ => source_budget e
  | SegGraphNodeEncode n _ _ | SegGraphSet (AuditSetMem n _ _ _ _ _) |
    SegGraphSet (AuditSetAdd n _ _ _ _ _) |
    SegGraphSet (AuditSetRemove n _ _ _ _ _) | SegGraphAdj (AuditMapGet n _ _ _ _ _) |
    SegGraphAdj (AuditMapSet n _ _ _ _ _ _) | SegGraphAdj (AuditMapRemove n _ _ _ _ _) =>
    node_budget n
  | SegGraphEdgeEncode e _ _ | SegGraphArc (AuditMapGet e _ _ _ _ _) |
    SegGraphArc (AuditMapSet e _ _ _ _ _ _) |
    SegGraphArc (AuditMapRemove e _ _ _ _ _) => edge_budget e
  | _ => 0
  end.

(** Finish budgets use the actual node and edge callback input. *)
Definition audit_seg_finish_event_budget {N E B} (node_budget : N -> nat) (target_budget : E -> nat)
    (event : audit_seg_finish_event N E B) : nat :=
  match event with
  | SegFinishTarget e _ _ => target_budget e
  | SegFinishSet (AuditSetMem n _ _ _ _ _) | SegFinishSet (AuditSetAdd n _ _ _ _ _) |
    SegFinishSet (AuditSetRemove n _ _ _ _ _) | SegFinishInterior (AuditMapGet n _ _ _ _ _) |
    SegFinishInterior (AuditMapSet n _ _ _ _ _ _) | SegFinishInterior (AuditMapRemove n _ _ _ _ _)
    => node_budget n
  | _ => 0
  end.

(** Under encoder and target laws, finish returns the source index within its per-call bound. *)
Definition audit_seg_finish_source_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (enc : N -> positive * list B) (target : E -> N * list B) work (weight : B -> nat)
    node_source target_source node_budget target_budget,
    (forall n, fst (enc n) = encode EN n) -> (forall e, fst (target e) = Graph.target g e) ->
    audit_graph_external_callback_adapter enc weight node_source node_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    let '(result, events) := audit_seg_finish_source_counted EE p enc target work in
    result = AnalysesSeg.seg_finish EN EE g p work /\ audit_seg_finish_source_work weight events <=
      audit_seg_finish_source_budget EN EE g work +
      fold_right (fun event n => audit_seg_finish_event_budget node_budget target_budget event + n)
        0 events.

(** Each generated graph callback has a fixed key-width allowance before client bodies. *)
Definition audit_seg_graph_call_budget {N E} (EN : encoding N) (EE : encoding E) (n : N) (e : E) :
    nat :=
  4096 * S (Pos.size_nat (encode EN n) + Pos.size_nat (encode EE e)).

(** The generated callbacks return exact graph observations and bounded same-call work. *)
Definition audit_seg_graph_callbacks_source_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (encn : N -> positive * list B) (ence : E -> positive * list B)
    (target source : E -> N * list B) work n e (weight : B -> nat),
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    (forall x, fst (target x) = Graph.target g x) ->
    (forall x, fst (source x) = Graph.source g x) ->
    let '(out, out_calls) := audit_seg_graph_out p encn work n in
    let '(dst, dst_calls) := audit_seg_graph_target ence target work e in
    let '(src, src_calls) := audit_seg_graph_source source e in
    let idx := AnalysesSeg.seg_finish EN EE g p work in
    out = Graph.out (seg_graph idx) n /\ dst = Graph.target (seg_graph idx) e /\
    src = Graph.source (seg_graph idx) e /\
    (forall calls, calls = out_calls \/ calls = dst_calls \/ calls = src_calls ->
      fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 calls <=
        audit_seg_graph_call_budget EN EE n e +
        fold_right (fun call k => audit_seg_graph_body_external weight call + k) 0 calls).

(** The adapted callback bound prices actual captured encoder and endpoint inputs. *)
Definition audit_seg_graph_callbacks_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E) (p : prepared EN g)
    (encn : N -> positive * list B) (ence : E -> positive * list B)
    (target source : E -> N * list B) work n e (weight : B -> nat)
    node_source edge_source target_source source_source node_budget edge_budget target_budget
    source_budget,
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    (forall x, fst (target x) = Graph.target g x) ->
    (forall x, fst (source x) = Graph.source g x) ->
    audit_graph_external_callback_adapter encn weight node_source node_budget ->
    audit_graph_external_callback_adapter ence weight edge_source edge_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    let '(_, out_calls) := audit_seg_graph_out p encn work n in
    let '(_, dst_calls) := audit_seg_graph_target ence target work e in
    let '(_, src_calls) := audit_seg_graph_source source e in
    forall calls, calls = out_calls \/ calls = dst_calls \/ calls = src_calls ->
      fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 calls <=
        audit_seg_graph_call_budget EN EE n e +
        fold_right (fun call k => audit_seg_graph_body_budget node_budget edge_budget target_budget
          source_budget call + k) 0 calls.

(** Finish and generated graph contracts include concrete collection source obligations. *)
Definition audit_seg_finish_source_contract_statement : Prop :=
  audit_seg_finish_source_erasure_statement /\ audit_seg_finish_source_statement /\
  audit_seg_finish_source_adapted_statement /\ audit_seg_graph_callbacks_erasure_statement /\
  audit_seg_graph_callbacks_source_statement /\ audit_seg_graph_callbacks_adapted_statement /\
  audit_map_transform_erases_statement /\ audit_map_transform_source_bound_statement /\
  audit_map_elements_erases_statement /\ audit_map_elements_work_bound_statement.

(** Generated encoder calls return exact codes and pay fixed internal wrapper work. *)
Definition audit_seg_graph_encoders_source_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (encn : N -> positive * list B)
    (ence : E -> positive * list B) n e (weight : B -> nat),
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    let '(nc, ne) := audit_seg_graph_node_encode (E := E) encn n in
    let '(ec, ee) := audit_seg_graph_edge_encode (N := N) ence e in
    nc = encode EN n /\ ec = encode EE e /\
    fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 ne <=
      4096 + fold_right (fun call k => audit_seg_graph_body_external weight call + k) 0 ne /\
    fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 ee <=
      4096 + fold_right (fun call k => audit_seg_graph_body_external weight call + k) 0 ee.

(** Adapted wrapper bounds use the actual original node and edge encoder calls. *)
Definition audit_seg_graph_encoders_adapted_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (encn : N -> positive * list B)
    (ence : E -> positive * list B) n e (weight : B -> nat) node_source edge_source node_budget
    edge_budget,
    (forall x, fst (encn x) = encode EN x) -> (forall x, fst (ence x) = encode EE x) ->
    audit_graph_external_callback_adapter encn weight node_source node_budget ->
    audit_graph_external_callback_adapter ence weight edge_source edge_budget ->
    let '(_, ne) := audit_seg_graph_node_encode (E := E) encn n in
    let '(_, ee) := audit_seg_graph_edge_encode (N := N) ence e in
    fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 ne <=
      4096 + node_budget n /\
    fold_right (fun call k => audit_seg_graph_body_work weight call + k) 0 ee <=
      4096 + edge_budget e.

(** Both generated encoder wrappers retain their actual source and adapted work bounds. *)
Definition audit_seg_graph_encoders_contract_statement : Prop :=
  audit_seg_graph_encoders_source_statement /\ audit_seg_graph_encoders_adapted_statement.

(** The full trace retains all actual component source calls. *)
Inductive audit_seg_full_event (N E U B : Type) : Type :=
  | SegFullBuild : audit_seg_build_event N E U B -> audit_seg_full_event N E U B
  | SegFullSplice : audit_seg_splice_event N E B -> audit_seg_full_event N E U B
  | SegFullFinish : audit_seg_finish_event N E B -> audit_seg_full_event N E U B
  | SegFullCase : nat -> audit_seg_full_event N E U B.

Arguments SegFullBuild {N E U B} _.

Arguments SegFullSplice {N E U B} _.

Arguments SegFullFinish {N E U B} _.

Arguments SegFullCase {N E U B} _.

(** The splice fold retains each actual intermediate work state. *)
Fixpoint audit_seg_full_splices {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (candidates : Map.t N E) (nodes : list N) (work : seg_work N E)
    : seg_work N E * list (audit_seg_full_event N E U B) :=
  match nodes with
  | [] => (work, [SegFullCase 0])
  | n :: rest =>
    let '(next, calls) := audit_seg_splice_source_counted (seg_build_node_encode cb)
      (seg_build_edge_encode cb) candidates n work in
    let '(result, events) := audit_seg_full_splices cb candidates rest next in
    (result, SegFullCase 1 :: map SegFullSplice calls ++ events)
  end.

(** One receipt keeps the original index and final work state for later graph callbacks. *)
Record audit_seg_full_receipt (N E U B : Type) (EN : encoding N) (g : Graph.t N E) : Type :=
  SegFullReceipt {
  audit_seg_full_index : prepared EN g;
  audit_seg_full_work_state : seg_work N E;
  audit_seg_full_result : seg_index N E;
  audit_seg_full_events : list (audit_seg_full_event N E U B)
}.

Arguments SegFullReceipt {N E U B EN g} _ _ _ _.

Arguments audit_seg_full_index {N E U B EN g} _.

Arguments audit_seg_full_work_state {N E U B EN g} _.

Arguments audit_seg_full_result {N E U B EN g} _.

Arguments audit_seg_full_events {N E U B EN g} _.

(** The builder executes every source stage once and returns its coupled receipt. *)
Definition audit_seg_full_source_counted {N E U B} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E)
    (cb : audit_seg_build_callbacks N E U B) (u : U) : audit_seg_full_receipt N E U B EN g :=
  let prep_cb := AuditPrepareCallbackModel N E B (seg_build_out cb) (seg_build_target cb)
    (seg_build_node_encode cb) in
  let '(p, prep_calls) := audit_prepare_source_counted EN g prep_cb in
  let '(edges, edge_calls) := audit_seg_build_edges cb (Graph.nodes g) in
  let '(points, point_calls) := audit_seg_build_points cb u edges in
  let '(entries, entry_calls) := audit_finset_of_list (seg_build_node_encode cb) (Graph.entries g)
    in
  let '(candidates, candidate_calls) := audit_seg_build_candidates p cb points entries
    (Graph.nodes g) in
  let '(initial, initial_calls) := audit_seg_build_initial g cb u edges in
  let '(final, splice_calls) := audit_seg_full_splices cb candidates (Graph.nodes g) initial in
  let '(result, finish_calls) := audit_seg_finish_source_counted EE p (seg_build_node_encode cb)
    (seg_build_target cb) final in
  SegFullReceipt p final result
    (map (fun call => SegFullBuild (SegBuildPrepare call)) prep_calls ++
      map SegFullBuild edge_calls ++ map SegFullBuild point_calls ++
      map (fun call => SegFullBuild (SegBuildSet call)) entry_calls ++
      map SegFullBuild candidate_calls ++ map SegFullBuild initial_calls ++ splice_calls ++
      map SegFullFinish finish_calls).

(** Callback erasure ties each returned value to the graph or expression view. *)
Definition audit_seg_full_callbacks_erase {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) : Prop :=
  let g := cfg (gkview gk) in
  (forall n, fst (seg_build_node_encode cb n) = encode EN n) /\
  (forall e, fst (seg_build_edge_encode cb e) = encode EE e) /\
  (forall u, fst (seg_build_expr_encode cb u) = encode EU u) /\
  (forall n, fst (seg_build_out cb n) = Graph.out g n) /\
  (forall e, fst (seg_build_target cb e) = Graph.target g e) /\
  (forall e, fst (seg_build_source cb e) = Graph.source g e) /\
  (forall e, fst (seg_build_gen cb e) = gen gk e) /\
  (forall e u, fst (seg_build_kill cb (e, u)) = kill gk e u).

(** The same receipt returns the exact expression-specific SEG index. *)
Definition audit_seg_full_source_erasure_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) u,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_seg_full_result (audit_seg_full_source_counted EN EE (cfg (gkview gk)) cb u) =
      build_expression_seg EN EE EU gk u.

(** Builder component work expands all actual source primitives. *)
Definition audit_seg_build_event_work {N E U B} (weight : B -> nat)
    (event : audit_seg_build_event N E U B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | SegBuildCase _ => 0
  | SegBuildPrepare call => audit_prepare_source_event_work weight call
  | SegBuildOut _ _ xs | SegBuildTarget _ _ xs | SegBuildSource _ _ xs => body xs
  | SegBuildTransfer call => audit_seg_transfer_source_event_work weight call
  | SegBuildSet call => audit_finset_source_work body [call]
  | SegBuildAdj call => audit_map_source_work body [call]
  | SegBuildNodeMap call => audit_map_source_work body [call]
  | SegBuildArcMap call => audit_map_source_work body [call]
  | SegBuildOutput n => S n
  end.

(** External work contains only bodies of actual supplied callbacks. *)
Definition audit_seg_build_event_external {N E U B} (weight : B -> nat)
    (event : audit_seg_build_event N E U B) : nat :=
  match event with
  | SegBuildPrepare call => audit_prepare_source_body_work weight [call]
  | SegBuildOut _ _ body | SegBuildTarget _ _ body | SegBuildSource _ _ body |
    SegBuildSet (AuditSetMem _ _ _ _ body _) | SegBuildSet (AuditSetAdd _ _ _ _ body _) |
    SegBuildSet (AuditSetRemove _ _ _ _ body _) | SegBuildAdj (AuditMapGet _ _ _ _ body _) |
    SegBuildAdj (AuditMapSet _ _ _ _ _ body _) | SegBuildAdj (AuditMapRemove _ _ _ _ body _) |
    SegBuildNodeMap (AuditMapGet _ _ _ _ body _) | SegBuildNodeMap (AuditMapSet _ _ _ _ _ body _) |
    SegBuildNodeMap (AuditMapRemove _ _ _ _ body _) | SegBuildArcMap (AuditMapGet _ _ _ _ body _) |
    SegBuildArcMap (AuditMapSet _ _ _ _ _ body _) |
    SegBuildArcMap (AuditMapRemove _ _ _ _ body _) =>
    fold_right (fun x n => weight x + n) 0 body
  | SegBuildTransfer call => audit_seg_transfer_source_event_external weight call
  | _ => 0
  end.

(** Each full event is priced by its concrete component source model. *)
Definition audit_seg_full_event_work {N E U B} (weight : B -> nat)
    (event : audit_seg_full_event N E U B) : nat :=
  64 + match event with
  | SegFullBuild call => audit_seg_build_event_work weight call
  | SegFullSplice call => audit_seg_splice_event_work weight call
  | SegFullFinish call => audit_seg_finish_event_work weight call
  | SegFullCase _ => 0
  end.

(** External work follows the same captured full execution. *)
Definition audit_seg_full_event_external {N E U B} (weight : B -> nat)
    (event : audit_seg_full_event N E U B) : nat :=
  match event with
  | SegFullBuild call => audit_seg_build_event_external weight call
  | SegFullSplice call => audit_seg_splice_event_external weight call
  | SegFullFinish call => audit_seg_finish_event_external weight call
  | SegFullCase _ => 0
  end.

(** Whole work includes trace construction, path lists and component source frames. *)
Definition audit_seg_full_source_work {N E U B} (weight : B -> nat)
    (events : list (audit_seg_full_event N E U B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_seg_full_event_work weight event + n) 0 events.

(** The client-body allowance is derived from exactly the same source events. *)
Definition audit_seg_full_source_external {N E U B} (weight : B -> nat)
    (events : list (audit_seg_full_event N E U B)) : nat :=
  fold_right (fun event n => audit_seg_full_event_external weight event + n) 0 events.

(** Input scale includes original graph occurrences, generated expressions and encoded widths. *)
Definition audit_seg_full_input_scale {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) : nat :=
  let g := cfg (gkview gk) in let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let nodes := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges in
  let exprs := u :: flat_map (gen gk) edges in
  let nw := fold_right Nat.max 0 (map (fun n => Pos.size_nat (encode EN n)) nodes) in
  let ew := fold_right Nat.max 0 (map (fun e => Pos.size_nat (encode EE e)) edges) in
  let uw := fold_right Nat.max 0 (map (fun x => Pos.size_nat (encode EU x)) exprs) in
  Datatypes.S (length nodes + length edges + length exprs + nw + ew + uw +
    audit_prepare_source_budget EN g).

(** The full builder budget uses only the original graph and expression inputs. *)
Definition audit_seg_full_input_budget {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_seg_full_input_scale EN EE EU gk u) 64.

(** The intermediate allowance includes the actual final rope and map dimensions. *)
Definition audit_seg_full_intermediate_budget {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (work : seg_work N E) : nat :=
  audit_seg_full_input_budget EN EE EU gk u + audit_seg_finish_source_budget EN EE (cfg (gkview gk))
    work.

(** The complete builder has exact output and both original and intermediate bounds. *)
Definition audit_seg_full_source_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) u (weight : B -> nat),
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    let receipt := audit_seg_full_source_counted EN EE (cfg (gkview gk)) cb u in
    audit_seg_full_result receipt = build_expression_seg EN EE EU gk u /\
    audit_seg_full_source_work weight (audit_seg_full_events receipt) <=
      audit_seg_full_input_budget EN EE EU gk u +
      audit_seg_full_source_external weight (audit_seg_full_events receipt) /\
    audit_seg_full_source_work weight (audit_seg_full_events receipt) <=
      audit_seg_full_intermediate_budget EN EE EU gk u (audit_seg_full_work_state receipt) +
      audit_seg_full_source_external weight (audit_seg_full_events receipt).

(** Each builder event identifies the actual source callback input. *)
Definition audit_seg_build_event_budget {N E U B} (node_budget out_budget : N -> nat)
    (edge_budget target_budget source_budget gen_budget : E -> nat) (expr_budget : U -> nat)
    (kill_budget : E * U -> nat) (event : audit_seg_build_event N E U B) : nat :=
  match event with
  | SegBuildPrepare call => audit_prepare_source_event_budget node_budget out_budget target_budget
    call
  | SegBuildOut n _ _ => out_budget n
  | SegBuildTarget e _ _ => target_budget e
  | SegBuildSource e _ _ => source_budget e
  | SegBuildTransfer call => audit_seg_transfer_source_event_budget expr_budget gen_budget
    kill_budget call
  | SegBuildSet (AuditSetMem n _ _ _ _ _) | SegBuildSet (AuditSetAdd n _ _ _ _ _) |
    SegBuildSet (AuditSetRemove n _ _ _ _ _) | SegBuildAdj (AuditMapGet n _ _ _ _ _) |
    SegBuildAdj (AuditMapSet n _ _ _ _ _ _) | SegBuildAdj (AuditMapRemove n _ _ _ _ _) |
    SegBuildNodeMap (AuditMapGet n _ _ _ _ _) | SegBuildNodeMap (AuditMapSet n _ _ _ _ _ _) |
    SegBuildNodeMap (AuditMapRemove n _ _ _ _ _) => node_budget n
  | SegBuildArcMap (AuditMapGet e _ _ _ _ _) | SegBuildArcMap (AuditMapSet e _ _ _ _ _ _) |
    SegBuildArcMap (AuditMapRemove e _ _ _ _ _) => edge_budget e
  | _ => 0
  end.

(** The complete event budget follows the same actual build, splice and finish events. *)
Definition audit_seg_full_event_budget {N E U B} (node_budget out_budget : N -> nat)
    (edge_budget target_budget source_budget gen_budget : E -> nat) (expr_budget : U -> nat)
    (kill_budget : E * U -> nat) (event : audit_seg_full_event N E U B) : nat :=
  match event with
  | SegFullBuild call => audit_seg_build_event_budget node_budget out_budget edge_budget
    target_budget source_budget gen_budget expr_budget kill_budget call
  | SegFullSplice call => audit_seg_splice_event_budget node_budget edge_budget call
  | SegFullFinish call => audit_seg_finish_event_budget node_budget target_budget call
  | SegFullCase _ => 0
  end.

(** Under eight callback laws, the builder returns the source index within both adapted bounds. *)
Definition audit_seg_full_source_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) u (weight : B -> nat)
    node_source edge_source expr_source out_source target_source source_source gen_source
    kill_source
    node_budget edge_budget expr_budget out_budget target_budget source_budget gen_budget
    kill_budget,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source kill_budget ->
    let receipt := audit_seg_full_source_counted EN EE (cfg (gkview gk)) cb u in
    let external := fold_right (fun event n => audit_seg_full_event_budget node_budget out_budget
      edge_budget target_budget source_budget gen_budget expr_budget kill_budget event + n)
      0 (audit_seg_full_events receipt) in
    audit_seg_full_result receipt = build_expression_seg EN EE EU gk u /\
    audit_seg_full_source_work weight (audit_seg_full_events receipt) <=
      audit_seg_full_input_budget EN EE EU gk u + external /\
    audit_seg_full_source_work weight (audit_seg_full_events receipt) <=
      audit_seg_full_intermediate_budget EN EE EU gk u (audit_seg_full_work_state receipt) +
      external.

(** The full builder contract includes component and generated graph source obligations. *)
Definition audit_seg_full_source_contract_statement : Prop :=
  audit_seg_full_source_erasure_statement /\ audit_seg_full_source_statement /\
  audit_seg_full_source_adapted_statement /\ audit_seg_transfer_source_contract_statement /\
  audit_seg_splice_source_contract_statement /\ audit_seg_finish_source_contract_statement.

(** The builder contract combines full construction with both generated encoder source bounds. *)
Definition audit_seg_builder_contract_statement : Prop :=
  audit_seg_full_source_contract_statement /\ audit_seg_graph_encoders_contract_statement.
