(** * Erasure and counted work for PRE finalization

    These proofs relate counted finalization to the original ordered plan construction.
    For example, defining a phi preserves the exact selected parameter-edge version.
    Builds on: AnalysesAuditPrePlan, AnalysesAuditPrePlanSupport,
    AnalysesAuditSourceAdequacy and AnalysesSsaPre. *)

From Stdlib Require Import Decimal Arith Bool List PArith ZArith Lia.
From Galois.Analyses Require Import AnalysesAuditPrePlan AnalysesAuditPrePlanSupport
  AnalysesAuditSourceAdequacy
  AnalysesAvailable AnalysesSsaPre AnalysesSsaPreGraph AnalysesSsaLiveQuery.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsFinSet CollectionsTrie.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
Import List.ListNotations.

(** * Compositional erasure *)

Lemma plan_bind_value Call A B site (run : exact_counted Call A)
    (next : A -> exact_counted Call B) :
  exact_value (exact_bind site run next) = exact_value (next (exact_value run)).
Proof.
  reflexivity.
Qed.

Lemma plan_case_value Call A site (run : exact_counted Call A) :
  exact_value (exact_case site run) = exact_value run.
Proof.
  reflexivity.
Qed.

Lemma plan_call_value Call A call charge (value : A) :
  exact_value (@exact_call Call A call charge value) = value.
Proof.
  reflexivity.
Qed.

Lemma plan_return_value Call A site (value : A) :
  exact_value (@exact_return Call A site value) = value.
Proof.
  reflexivity.
Qed.

Lemma plan_lift_value Call Other A inject (run : exact_counted Call A) :
  exact_value (@exact_lift Call Other A inject run) = exact_value run.
Proof.
  reflexivity.
Qed.

Lemma plan_encode_value Call K V (inject : exact_map_call K V -> Call) E body key :
  exact_value (exact_encode inject E body key) = encode E key.
Proof.
  reflexivity.
Qed.

Lemma plan_elements_value Call K V (inject : exact_map_call K V -> Call) table :
  exact_value (exact_elements inject table) = Map.elements table.
Proof.
  reflexivity.
Qed.

Lemma plan_option_value Call A B (input : option A) (none : exact_counted Call B)
    (some : A -> exact_counted Call B) :
  exact_value (
    match input with
    | Some value =>
      some value
    | None =>
      none
    end) =
    match input with
    | Some value =>
      exact_value (some value)
    | None =>
      exact_value none
    end.
Proof.
  destruct input; reflexivity.
Qed.

Lemma plan_store_pair_value Call K V P (inject : exact_map_call K V -> Call)
    encoding body key table (result : V * P) :
  exact_value (let '(value,payload) := result in
    exact_bind 826 (exact_set inject encoding body key value table)
      (fun updated => exact_return 827 (updated,payload))) =
  let '(value,payload) := result in (Map.set encoding key value table,payload).
Proof.
  destruct result; reflexivity.
Qed.

(* Project values without reducing unused costs or event lists. *)
Local Ltac plan_erase :=
  repeat first [rewrite plan_bind_value | rewrite plan_case_value | rewrite plan_call_value |
    rewrite plan_return_value | rewrite plan_lift_value | rewrite exact_get_erases |
    rewrite exact_set_erases | rewrite plan_encode_value | rewrite plan_elements_value].

Lemma plan_flat_map_erases Call A B site (f : A -> exact_counted Call (list B)) xs :
  exact_value (exact_flat_map site f xs) = flat_map (fun x => exact_value (f x)) xs.
Proof.
  induction xs as [|x rest IH]; cbn [exact_flat_map exact_case exact_bind exact_return exact_value].
  - reflexivity.
  - rewrite exact_append_erases, IH. reflexivity.
Qed.

Lemma plan_fold_left_agrees A B (first second : B -> A -> B) xs :
  (forall state x, first state x = second state x) ->
  forall state, fold_left first xs state = fold_left second xs state.
Proof.
  intro Hagrees. induction xs as [|x rest IH]; intro state; cbn [fold_left].
  - reflexivity.
  - rewrite Hagrees. apply IH.
Qed.

Lemma plan_flat_map_agrees A B (first second : A -> list B) xs :
  (forall x, first x = second x) -> flat_map first xs = flat_map second xs.
Proof.
  intro Hagrees. induction xs as [|x rest IH]; cbn [flat_map].
  - reflexivity.
  - now rewrite Hagrees, IH.
Qed.

(** * Finalizer helpers *)

Section Finalize.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U)
  (block_body : B -> nat) (point_body : N -> nat) (edge_body : E -> nat)
  (expr_body : U -> nat).

Lemma plan_will_erases facts key :
  exact_value (pre_will_counted (BE:=BE) (N:=N) (E:=E) EB EU block_body expr_body facts key) =
    AnalysesSsaPre.pre_finalize_will EB EU facts key.
Proof.
  reflexivity.
Qed.

Lemma plan_insert_operand_erases facts (operand : frg_operand B E U) :
  exact_value (pre_insert_operand_counted (BE:=BE) (N:=N) EB EU block_body expr_body
    facts operand) =
    AnalysesSsaPre.pre_finalize_insert_operand EB EU facts operand.
Proof.
  destruct operand as [[u|u|e u|b u] real]; reflexivity.
Qed.

Lemma plan_dominates_erases tree d n :
  exact_value (pre_dominates_counted (B:=B) (BE:=BE) (E:=E) (U:=U)
    EN point_body tree d n) = dominates_b EN tree d n.
Proof.
  unfold pre_dominates_counted, dominates_b.
  plan_erase.
  destruct (Map.get EN d (tin tree)) as [x|]; plan_erase; [|reflexivity].
  destruct (Map.get EN n (tin tree)) as [y|]; plan_erase; [|reflexivity].
  destruct (Map.get EN d (tout tree)) as [z|]; plan_erase; [|reflexivity].
  destruct (Map.get EN n (tout tree)); plan_erase; reflexivity.
Qed.

Lemma plan_version_point_erases version :
  exact_value (pre_version_point_counted a version) =
    pre_version_point (pre_expression a) version.
Proof.
  destruct version; reflexivity.
Qed.

Lemma plan_available_erases tree scope definition u n :
  exact_value (pre_available_counted EB EN EE EU a block_body point_body edge_body expr_body
    tree scope definition u n) =
    AnalysesSsaPre.pre_finalize_available EB EN EE EU a tree scope definition u n.
Proof.
  unfold pre_available_counted, AnalysesSsaPre.pre_finalize_available.
  plan_erase.
  destruct (Map.get (frg_version_encoding EB EE EU) definition scope) as [version|];
    plan_erase; [|reflexivity].
  destruct (Pos.eqb (encode EU (pre_version_expr version)) (encode EU u));
    plan_erase; [|reflexivity].
  rewrite plan_version_point_erases.
  destruct (pre_version_point (pre_expression a) version) as [q|]; [|reflexivity].
  plan_erase. now rewrite plan_dominates_erases.
Qed.

Lemma plan_occurrence_erases f tree work edge :
  exact_value (pre_occurrence_counted EB EN EE EU a block_body point_body edge_body expr_body
    f tree work edge) = AnalysesSsaPre.pre_finalize_occurrence EB EN EE EU a f tree work edge.
Proof.
  destruct work as [scope plan].
  unfold pre_occurrence_counted, AnalysesSsaPre.pre_finalize_occurrence.
  plan_erase.
  destruct (pre_recomputed (pre_expression a) edge) as [u|]; plan_erase; [|reflexivity].
  destruct (Map.get EE edge (frg_occurrence_index f)) as [definition|];
    plan_erase; [|reflexivity].
  destruct (pre_total_pure (pre_expression a) u); plan_erase; [|reflexivity].
  rewrite plan_available_erases.
  destruct (AnalysesSsaPre.pre_finalize_available EB EN EE EU a tree scope definition u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) edge)); plan_erase; reflexivity.
Qed.

(** All five helper mirrors preserve flags, availability and occurrence results exactly. *)
Theorem pre_finalize_helpers_erasure :
  pre_finalize_helpers_erasure_statement EB EN EE EU a block_body point_body edge_body expr_body.
Proof.
  split; [exact plan_will_erases|].
  split; [exact plan_insert_operand_erases|].
  split; [exact plan_dominates_erases|].
  split; [exact plan_available_erases|exact plan_occurrence_erases].
Qed.

End Finalize.

Arguments pre_finalize_helpers_erasure : clear implicits.

(** * Scope and ordered node loop *)

Section Loop.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U)
  (block_body : B -> nat) (point_body : N -> nat) (edge_body : E -> nat)
  (expr_body : U -> nat).

Lemma plan_define_phi_erases scope key :
  exact_value (pre_define_phi_counted EB EE EU a block_body edge_body expr_body scope key) =
    AnalysesSsaPre.pre_finalize_define_phi EB EE EU a scope key.
Proof.
  reflexivity.
Qed.

Lemma plan_initial_erases versions :
  exact_value (pre_initial_scope_counted EB EE EU a block_body edge_body expr_body versions) =
    AnalysesSsaPre.pre_finalize_initial EB EE EU a versions.
Proof.
  unfold pre_initial_scope_counted, AnalysesSsaPre.pre_finalize_initial.
  rewrite exact_fold_left_erases. apply plan_fold_left_agrees.
  intros scope [u|u|e u|b u]; plan_erase; try reflexivity.
  destruct (pre_initial_available a u); plan_erase; reflexivity.
Qed.

Lemma plan_select_erases plan parameter incoming u version :
  exact_value (pre_select_counted (B:=B) (BE:=BE) (N:=N) EE EU edge_body expr_body
    plan parameter incoming u version) =
    AnalysesSsaPre.pre_finalize_select EE EU plan parameter incoming u version.
Proof.
  reflexivity.
Qed.

Lemma plan_argument_erases facts tree scope plan argument :
  exact_value (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body
    facts tree scope plan argument) =
    AnalysesSsaPre.pre_finalize_argument_step EB EN EE EU a facts tree scope plan argument.
Proof.
  unfold pre_argument_counted, AnalysesSsaPre.pre_finalize_argument_step.
  plan_erase. rewrite plan_will_erases.
  destruct (AnalysesSsaPre.pre_finalize_will EB EU facts
    (pre_arg_block argument, pre_arg_expression argument)); plan_erase; [|reflexivity].
  destruct (pre_phi_translate a (pre_arg_block_edge argument) (pre_arg_expression argument))
    as [value|]; plan_erase; [|reflexivity].
  rewrite plan_insert_operand_erases.
  destruct (AnalysesSsaPre.pre_finalize_insert_operand EB EU facts (pre_arg_operand argument));
    plan_erase.
  - destruct (pre_total_pure (pre_expression a) value &&
      negb (kill (pre_genkill (pre_expression a)) (pre_arg_point_edge argument) value));
      plan_erase; [apply plan_select_erases|reflexivity].
  - rewrite plan_available_erases.
    destruct (AnalysesSsaPre.pre_finalize_available EB EN EE EU a tree scope
      (frg_operand_version (pre_arg_operand argument)) value
      (Graph.source (live_graph (point_model (pre_ssa_points a))) (pre_arg_point_edge argument)));
      plan_erase; [apply plan_select_erases|reflexivity].
Qed.

Lemma plan_node_erases f facts tree points phis arguments work n :
  exact_value (pre_node_counted EB EN EE EU a block_body point_body edge_body expr_body
    f facts tree points phis arguments work n) =
    AnalysesSsaPre.pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n.
Proof.
  destruct work as [scope plan].
  unfold pre_node_counted, AnalysesSsaPre.pre_finalize_node, succ_edges, index_edges.
  plan_erase. rewrite !exact_fold_left_erases.
  assert (Hdefine : forall keys state,
    fold_left (fun state key => exact_value
      (pre_define_phi_counted EB EE EU a block_body edge_body expr_body state key)) keys state =
    fold_left (AnalysesSsaPre.pre_finalize_define_phi EB EE EU a) keys state).
  { intros keys state. apply plan_fold_left_agrees. exact plan_define_phi_erases. }
  rewrite Hdefine.
  assert (Hargument : forall args state scope,
    fold_left (fun state argument => exact_value
      (pre_argument_counted EB EN EE EU a block_body point_body edge_body expr_body
        facts tree scope state argument)) args state =
    fold_left (AnalysesSsaPre.pre_finalize_argument_step EB EN EE EU a facts tree scope)
      args state).
  { intros args state fixed. apply plan_fold_left_agrees. intros current argument.
    apply plan_argument_erases. }
  rewrite Hargument. apply plan_fold_left_agrees. intros current edge.
  apply plan_occurrence_erases.
Qed.

Lemma plan_parent_scope_erases (tree : dom_tree N)
    (outputs : Map.t N (Map.t (frg_version B E U) (pre_version E U))) initial n :
  exact_value (
    match Map.get EN n (idom tree) with
    | None =>
      exact_case 821 (exact_return 821 initial)
    | Some parent =>
      exact_case 822 (exact_bind 823
        (exact_get (PfOutputs (BE:=BE)) EN point_body parent outputs)
        (fun found => exact_case 824 (exact_return 824 (
          match found with
          | Some scope =>
            scope
          | None =>
            initial
          end))))
    end) =
  match Map.get EN n (idom tree) with
  | None =>
    initial
  | Some parent =>
    match Map.get EN parent outputs with
    | None =>
      initial
    | Some scope =>
      scope
    end
  end.
Proof.
  destruct (Map.get EN n (idom tree)) as [parent|]; plan_erase; [|reflexivity].
  reflexivity.
Qed.

Lemma plan_table_erases f facts tree points phis arguments initial work n :
  exact_value (pre_table_step_counted EB EN EE EU a block_body point_body edge_body expr_body
    f facts tree points phis arguments initial work n) =
    AnalysesSsaPre.pre_finalize_table_step EB EN EE EU a
      f facts tree points phis arguments initial work n.
Proof.
  destruct work as [outputs plan].
  unfold pre_table_step_counted, AnalysesSsaPre.pre_finalize_table_step.
  cbv beta iota zeta.
  rewrite plan_bind_value, exact_get_erases, plan_bind_value, plan_parent_scope_erases.
  rewrite plan_bind_value, plan_node_erases.
  apply plan_store_pair_value.
Qed.

(** Initial scopes, arguments, nodes and table steps erase to the original loop. *)
Theorem pre_finalize_loop_erases :
  pre_finalize_loop_erases_statement EB EN EE EU a block_body point_body edge_body expr_body.
Proof.
  split; [exact plan_initial_erases|].
  split; [exact plan_argument_erases|].
  split; [exact plan_node_erases|exact plan_table_erases].
Qed.

End Loop.

Arguments pre_finalize_loop_erases : clear implicits.

(** * Row setup and ordered plan erasure *)

Lemma plan_set_elements_value Call K (inject : exact_map_call K unit -> Call) set :
  exact_value (exact_set_elements inject set) = FinSet.elements set.
Proof.
  unfold exact_set_elements. plan_erase.
  rewrite exact_map_erases. reflexivity.
Qed.

Section Rows.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U)
  (block_body : B -> nat) (block_edge_body : BE -> nat) (point_body : N -> nat)
  (edge_body : E -> nat) (expr_body : U -> nat).

Lemma plan_point_index_erases :
  exact_value (pre_point_index_counted EBE a block_edge_body) =
    pre_point_edge_index EBE (pre_ssa_points a).
Proof.
  unfold pre_point_index_counted, pre_point_edge_index, Map.of_list, edges_of.
  plan_erase. rewrite plan_flat_map_erases.
  cbn [exact_value exact_call].
  rewrite plan_flat_map_erases, exact_fold_left_erases.
  assert (Hitems : forall edges,
    flat_map (fun edge => exact_value (Call:=pre_rows_call B BE N E U)
      (exact_bind 1302
        (exact_call (PrBlockEdge edge (block_edge_of (pre_ssa_points a) edge)) 0
          (block_edge_of (pre_ssa_points a) edge))
        (fun found =>
        match found with
        | None =>
          exact_case 1303 (exact_return 1303 [])
        | Some be =>
          exact_case 1304 (exact_return 1304 [(be,edge)])
        end))) edges =
    flat_map (fun edge =>
      match block_edge_of (pre_ssa_points a) edge with
      | Some be =>
        [(be,edge)]
      | None =>
        []
      end) edges).
  { intro edges. apply plan_flat_map_agrees. intro edge. plan_erase.
    destruct (block_edge_of (pre_ssa_points a) edge); plan_erase; reflexivity. }
  rewrite Hitems. apply plan_fold_left_agrees. intros table row. reflexivity.
Qed.

Lemma plan_phi_rows_erases f facts :
  exact_value (pre_phi_rows_counted EB EN EU a block_body point_body expr_body f facts) =
    AnalysesSsaPre.pre_finalize_phi_rows EB EN EU a f facts.
Proof.
  unfold pre_phi_rows_counted, AnalysesSsaPre.pre_finalize_phi_rows.
  plan_erase. rewrite plan_set_elements_value, plan_flat_map_erases, exact_fold_left_erases.
  assert (Hitems : forall keys,
    flat_map (fun key => exact_value (Call:=pre_rows_call B BE N E U)
      (exact_bind 1322 (exact_lift PrFinalize
        (pre_will_counted EB EU block_body expr_body facts key)) (fun will =>
      if will then exact_case 1323
        (let edge := parameter_edge (pre_ssa_points a) (fst key) in
        exact_bind 1324 (exact_call (PrFinalize (PfParameter (fst key) edge)) 0 edge) (fun edge =>
        let point := Graph.target (live_graph (point_model (pre_ssa_points a))) edge in
        exact_bind 1325 (exact_call (PrFinalize (PfTarget edge point)) 0 point)
          (fun point => exact_return 1326 [(point,key)])))
      else exact_case 1327 (exact_return 1327 [])))) keys =
    flat_map (fun key => if AnalysesSsaPre.pre_finalize_will EB EU facts key then
      [(Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) (fst key)),key)] else []) keys).
  { intro keys. apply plan_flat_map_agrees. intro key. plan_erase.
    rewrite plan_will_erases.
    destruct (AnalysesSsaPre.pre_finalize_will EB EU facts key); plan_erase; reflexivity. }
  rewrite Hitems. apply plan_fold_left_agrees. intros table item. reflexivity.
Qed.

Lemma plan_argument_rows_erases f :
  exact_value (pre_argument_rows_counted EBE EN a block_edge_body point_body f) =
    AnalysesSsaPre.pre_finalize_argument_rows EBE EN a f.
Proof.
  unfold pre_argument_rows_counted, AnalysesSsaPre.pre_finalize_argument_rows.
  plan_erase. rewrite plan_point_index_erases.
  cbn [exact_elements exact_value].
  rewrite plan_flat_map_erases, exact_fold_left_erases.
  assert (Hitems : forall (links : list (((B * U) * BE) * frg_operand B E U)),
    flat_map (fun link => exact_value (Call:=pre_rows_call B BE N E U)
      (let '(((b,u),be),op) := link in
      exact_bind 1343 (exact_get PrPointIndex EBE block_edge_body be
        (pre_point_edge_index EBE (pre_ssa_points a))) (fun found =>
      match found with
      | None =>
        exact_case 1344 (exact_return 1344 [])
      | Some edge =>
        exact_case 1345
        (let point := Graph.source (live_graph (point_model (pre_ssa_points a))) edge in
        exact_bind 1346 (exact_call (PrFinalize (PfSource edge point)) 0 point)
          (fun point => exact_return 1347 [(point,PreFinalizeArgument b u be edge op)]))
      end))) links =
    flat_map (fun link => let '(((b,u),be),op) := link in
      match Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) with
      | Some edge =>
        [(Graph.source (live_graph (point_model (pre_ssa_points a))) edge,
          PreFinalizeArgument b u be edge op)]
      | None =>
        []
      end) links).
  { intro links. apply plan_flat_map_agrees. intros [[[b u] be] operand]. plan_erase.
    destruct (Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)));
      plan_erase; reflexivity. }
  rewrite Hitems. apply plan_fold_left_agrees. intros table item. reflexivity.
Qed.

(** Point-edge, phi and argument rows preserve the legacy ordering and missing-key behavior. *)
Theorem pre_finalize_rows_erases :
  pre_finalize_rows_erases_statement EB EBE EN EU a block_body block_edge_body point_body expr_body.
Proof.
  split; [exact plan_point_index_erases|].
  split; [exact plan_phi_rows_erases|exact plan_argument_rows_erases].
Qed.

(** The ordered counted fold returns exactly the original plan, including repeated nodes. *)
Theorem pre_finalize_order_erases :
  pre_finalize_order_erases_statement EB EBE EN EE EU a
    block_body block_edge_body point_body edge_body expr_body.
Proof.
  intros f facts tree points order.
  unfold pre_finalize_order_counted. plan_erase.
  rewrite plan_phi_rows_erases, plan_argument_rows_erases, plan_initial_erases.
  rewrite exact_fold_left_erases.
  f_equal. apply plan_fold_left_agrees. intros work n. plan_erase.
  apply plan_table_erases.
Qed.

(** The actual ordered finalizer erases and meets its raw-input budget. *)
Theorem audit_pre_finalize_order_source :
  audit_pre_finalize_order_source_statement EB EBE EN EE EU a
    block_body block_edge_body point_body edge_body expr_body.
Proof.
  split.
  - exact pre_finalize_rows_erases.
  - split.
    + exact pre_finalize_order_erases.
    + intros f facts tree points order.
      apply pre_finalize_order_bound.
Qed.

End Rows.

Arguments pre_finalize_rows_erases : clear implicits.

Arguments pre_finalize_order_erases : clear implicits.

Arguments audit_pre_finalize_order_source : clear implicits.

(** * Materialization work *)

Lemma plan_bind_units Call A B site (run : exact_counted Call A)
    (next : A -> exact_counted Call B) :
  exact_units (exact_bind site run next) =
    exact_units run + 64 + exact_units (next (exact_value run)).
Proof.
  reflexivity.
Qed.

Lemma plan_case_units Call A site (run : exact_counted Call A) :
  exact_units (exact_case site run) = 64 + exact_units run.
Proof.
  reflexivity.
Qed.

Lemma plan_call_units Call A call charge (value : A) :
  exact_units (@exact_call Call A call charge value) = 64 + charge.
Proof.
  reflexivity.
Qed.

Lemma plan_return_units Call A site (value : A) :
  exact_units (@exact_return Call A site value) = 64.
Proof.
  reflexivity.
Qed.

Lemma plan_get_units Call K V (inject : exact_map_call K V -> Call) E body key table :
  exact_units (exact_get inject E body key table) =
    194 + body key + 34 * Pos.size_nat (encode E key).
Proof.
  unfold exact_get, exact_encode. rewrite plan_bind_units, !plan_call_units.
  plan_erase.
  unfold audit_encoding_weight, audit_get_weight, audit_key_bits_weight. lia.
Qed.

Lemma plan_set_units Call K V (inject : exact_map_call K V -> Call) E body key value table :
  exact_units (exact_set inject E body key value table) =
    194 + body key + 67 * Pos.size_nat (encode E key).
Proof.
  unfold exact_set, exact_encode. rewrite plan_bind_units, !plan_call_units.
  plan_erase.
  unfold audit_encoding_weight, audit_set_weight, audit_key_bits_weight. lia.
Qed.

Lemma plan_elements_units Call K V (inject : exact_map_call K V -> Call) table :
  exact_units (exact_elements inject table) =
    65 + 32 * (Datatypes.S (exact_trie_nodes table))^2 + 8 * length (Map.elements table).
Proof.
  unfold exact_elements. rewrite plan_call_units. lia.
Qed.

(* Reduce scalar work equations while preserving all unused receipt fields. *)
Local Ltac plan_work :=
  repeat first [rewrite plan_bind_units | rewrite plan_case_units | rewrite plan_call_units |
    rewrite plan_return_units | rewrite plan_get_units | rewrite plan_set_units]; plan_erase.

Lemma plan_append_units Call A site (xs ys : list A) :
  exact_units (@exact_append Call A site xs ys) = 128 + 192 * length xs.
Proof.
  induction xs as [|x rest IH]; cbn [exact_append]; plan_work; cbn [length]; lia.
Qed.

Lemma plan_fold_units Call A B site (f : B -> A -> exact_counted Call B) xs bound :
  (forall state x, In x xs -> exact_units (f state x) <= bound) ->
  forall state, exact_units (exact_fold_left site f xs state) <=
    128 + length xs * (128 + bound).
Proof.
  induction xs as [|x rest IH]; intros Hstep state; cbn [exact_fold_left]; plan_work.
  - cbn [length]. lia.
  - pose proof (Hstep state x (or_introl eq_refl)) as Hhead.
    assert (Htail : forall state x, In x rest -> exact_units (f state x) <= bound).
    { intros current item Hin. apply Hstep. right. exact Hin. }
    specialize (IH Htail (exact_value (f state x))). cbn [length]. nia.
Qed.

Lemma plan_flat_map_units Call A B site (f : A -> exact_counted Call (list B)) xs bound :
  (forall x, In x xs -> exact_units (f x) <= bound /\ length (exact_value (f x)) <= 1) ->
  exact_units (exact_flat_map site f xs) <= 128 + length xs * (512 + bound).
Proof.
  induction xs as [|x rest IH]; intro Hstep; cbn [exact_flat_map]; plan_work.
  - cbn [length]. lia.
  - rewrite plan_append_units.
    destruct (Hstep x (or_introl eq_refl)) as [Hhead Hlength].
    assert (Htail : forall x, In x rest ->
      exact_units (f x) <= bound /\ length (exact_value (f x)) <= 1).
    { intros item Hin. apply Hstep. right. exact Hin. }
    specialize (IH Htail). cbn [length]. nia.
Qed.

Lemma plan_count_ne_bound A (node : Trie.ne A) :
  forall acc, Trie.count_ne node acc <= exact_ne_nodes node + acc.
Proof.
  induction node as [r IH|v|v r IH|l IH|l IHl r IHr|l IH v|l IHl v r IHr];
    intro acc; cbn [Trie.count_ne exact_ne_nodes].
  - specialize (IH acc). lia.
  - lia.
  - specialize (IH (S acc)). lia.
  - specialize (IH acc). lia.
  - specialize (IHl acc). specialize (IHr (Trie.count_ne l acc)). lia.
  - specialize (IH acc). lia.
  - specialize (IHl acc). specialize (IHr (S (Trie.count_ne l acc))). lia.
Qed.

Lemma plan_elements_length K V (table : Map.t K V) :
  length (Map.elements table) <= exact_trie_nodes table.
Proof.
  rewrite <- Map.size_elements. unfold Map.size, Trie.size, exact_trie_nodes.
  destruct table as [|node]; [lia|]. pose proof (plan_count_ne_bound _ node 0). lia.
Qed.

Lemma plan_max_member A (weight : A -> nat) xs x :
  In x xs -> weight x <= fold_right (fun item rest => Nat.max (weight item) rest) 0 xs.
Proof.
  induction xs as [|head rest IH]; cbn [In fold_right]; intro Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma plan_flat_map_length A B (f : A -> list B) xs :
  (forall x, In x xs -> length (f x) <= 1) -> length (flat_map f xs) <= length xs.
Proof.
  induction xs as [|x rest IH]; intro Hstep; cbn [flat_map length]; [lia|].
  rewrite length_app. pose proof (Hstep x (or_introl eq_refl)) as Hhead.
  assert (Htail : forall item, In item rest -> length (f item) <= 1).
  { intros item Hin. apply Hstep. right. exact Hin. }
  specialize (IH Htail). lia.
Qed.

(** * Scalar composition of the finite work bounds *)

Lemma plan_materialize_component_bound size entries items operand callback rows :
  entries <= size -> items <= entries ->
  callback <= 128 + entries * (768 + operand) ->
  rows <= 128 + items * (128 + 1024 * (1 + operand)) ->
  callback + rows + 8 * entries <= 256 + 1928 * (size * (1 + operand)).
Proof.
  intros Hentries Hitems Hcallback Hrows.
  assert (Hcallback_factor : 768 + operand <= 768 * (1 + operand)) by lia.
  assert (Hrows_factor : 128 + 1024 * (1 + operand) <= 1152 * (1 + operand)) by lia.
  assert (Hcallback_bound : callback <= 128 + size * (768 * (1 + operand))).
  { eapply Nat.le_trans; [exact Hcallback|]. apply Nat.add_le_mono_l.
    apply Nat.mul_le_mono; assumption. }
  assert (Hrows_bound : rows <= 128 + size * (1152 * (1 + operand))).
  { eapply Nat.le_trans; [exact Hrows|]. apply Nat.add_le_mono_l.
    apply Nat.mul_le_mono; [lia|exact Hrows_factor]. }
  assert (Hsize : size <= size * (1 + operand)).
  { rewrite <- (Nat.mul_1_r size) at 1. apply Nat.mul_le_mono_l. lia. }
  assert (Hentries_product : entries <= size * (1 + operand)) by lia.
  replace (size * (768 * (1 + operand))) with (768 * (size * (1 + operand)))
    in Hcallback_bound by nia.
  replace (size * (1152 * (1 + operand))) with (1152 * (size * (1 + operand)))
    in Hrows_bound by nia.
  clear Hentries Hitems Hcallback Hrows Hcallback_factor Hrows_factor Hsize.
  remember (size * (1 + operand)) as product in Hcallback_bound, Hrows_bound,
    Hentries_product |- *.
  lia.
Qed.

Lemma plan_linear_materialize_bound phi_nodes reload_nodes phi_length reload_length
    insert_length delete_length operand insert_work delete_work insert_rows_work delete_rows_work :
  phi_length <= phi_nodes -> reload_length <= reload_nodes ->
  insert_length <= phi_length -> delete_length <= reload_length ->
  insert_work <= 128 + phi_length * 640 ->
  delete_work <= 128 + reload_length * (768 + operand) ->
  insert_rows_work <= 128 + insert_length * (128 + 1024 * (1 + operand)) ->
  delete_rows_work <= 128 + delete_length * (128 + 1024 * (1 + operand)) ->
  65 + 32 * (Datatypes.S phi_nodes)^2 + 8 * phi_length + 64 +
    (insert_work + 64 + (insert_rows_work + 64 +
      (65 + 32 * (Datatypes.S reload_nodes)^2 + 8 * reload_length + 64 +
        (delete_work + 64 + (delete_rows_work + 64 + 64))))) <=
  1090 + 32 * (Datatypes.S phi_nodes)^2 + 32 * (Datatypes.S reload_nodes)^2 +
    1928 * ((phi_nodes + reload_nodes) * (1 + operand)).
Proof.
  intros Hphis Hreloads Hilength Hdlength Hinsert Hdelete Hirows Hdrows.
  assert (Hinsert_common : insert_work <= 128 + phi_length * (768 + operand)).
  { eapply Nat.le_trans; [exact Hinsert|].
    apply Nat.add_le_mono_l, Nat.mul_le_mono_l. lia. }
  assert (Hphi_work : insert_work + insert_rows_work + 8 * phi_length <=
    256 + 1928 * (phi_nodes * (1 + operand))).
  { apply (plan_materialize_component_bound _ _ insert_length); assumption. }
  assert (Hreload_work : delete_work + delete_rows_work + 8 * reload_length <=
    256 + 1928 * (reload_nodes * (1 + operand))).
  { apply (plan_materialize_component_bound _ _ delete_length); assumption. }
  clear Hphis Hreloads Hilength Hdlength Hinsert Hinsert_common Hdelete Hirows Hdrows.
  replace ((phi_nodes + reload_nodes) * (1 + operand)) with
    (phi_nodes * (1 + operand) + reload_nodes * (1 + operand)) by nia.
  lia.
Qed.

Lemma plan_materialize_geometry_positive phi_nodes reload_nodes operand :
  let square := (1 + phi_nodes + reload_nodes)^2 in
  let product := square * (1 + operand) in
  (phi_nodes + reload_nodes) * (1 + operand) <= product /\
  square <= product /\ 1 <= product.
Proof.
  cbv zeta.
  assert (Hnodes_square : phi_nodes + reload_nodes <= (1 + phi_nodes + reload_nodes)^2).
  { cbn [Nat.pow]. nia. }
  assert (Hsquare : (1 + phi_nodes + reload_nodes)^2 <=
    (1 + phi_nodes + reload_nodes)^2 * (1 + operand)).
  { rewrite <- (Nat.mul_1_r ((1 + phi_nodes + reload_nodes)^2)) at 1.
    apply Nat.mul_le_mono_l. lia. }
  assert (Hpositive : 1 <= (1 + phi_nodes + reload_nodes)^2).
  { pose proof (Nat.pow_nonzero (1 + phi_nodes + reload_nodes) 2 ltac:(lia)). lia. }
  split.
  - apply Nat.mul_le_mono_r. exact Hnodes_square.
  - split; [exact Hsquare|]. eapply Nat.le_trans; eassumption.
Qed.

Lemma plan_materialize_geometry_bound phi_nodes reload_nodes operand :
  1090 + 32 * (Datatypes.S phi_nodes)^2 + 32 * (Datatypes.S reload_nodes)^2 +
    1928 * ((phi_nodes + reload_nodes) * (1 + operand)) <=
  4096 * (1 + phi_nodes + reload_nodes)^2 * (1 + operand).
Proof.
  assert (Hphi_square : (Datatypes.S phi_nodes)^2 <= (1 + phi_nodes + reload_nodes)^2).
  { apply Nat.pow_le_mono_l. lia. }
  assert (Hreload_square : (Datatypes.S reload_nodes)^2 <= (1 + phi_nodes + reload_nodes)^2).
  { apply Nat.pow_le_mono_l. lia. }
  destruct (plan_materialize_geometry_positive phi_nodes reload_nodes operand)
    as [Hlinear [Hsquare Hpositive]].
  cbv zeta in Hlinear, Hsquare, Hpositive.
  replace (4096 * (1 + phi_nodes + reload_nodes)^2 * (1 + operand)) with
    (4096 * ((1 + phi_nodes + reload_nodes)^2 * (1 + operand))) by nia.
  remember ((1 + phi_nodes + reload_nodes)^2 * (1 + operand)) as product eqn:Hproduct in *.
  clear Hproduct.
  remember ((phi_nodes + reload_nodes) * (1 + operand)) as linear eqn:Hlinear_value in *.
  clear Hlinear_value.
  remember ((1 + phi_nodes + reload_nodes)^2) as square eqn:Hsquare_value in *.
  clear Hsquare_value.
  remember ((Datatypes.S phi_nodes)^2) as phi_square eqn:Hphi_square_value in *.
  clear Hphi_square_value.
  remember ((Datatypes.S reload_nodes)^2) as reload_square eqn:Hreload_square_value in *.
  clear Hreload_square_value.
  lia.
Qed.

(** * Materialization of the actual plan *)

Section Materialize.

Context {S O N E U C : Type} (EE : encoding E) (EU : encoding U)
  (view : pre_expression_view S O N E U C)
  (edge_body : E -> nat) (expr_body : U -> nat) (recomputed_body : E -> nat).

Definition plan_item_weight (item : E * U) : nat :=
  edge_body (fst item) + expr_body (snd item) +
    Pos.size_nat (encode EE (fst item)) + Pos.size_nat (encode EU (snd item)).

Definition plan_insert_item (binding : ((E * E) * U) * pre_version E U) : list (E * U) :=
  match snd binding with
  | PreInserted edge expr =>
    [(edge,expr)]
  | _ =>
    []
  end.

Definition plan_delete_item (binding : E * pre_version E U) : list (E * U) :=
  match pre_recomputed view (fst binding) with
  | Some expr =>
    [(fst binding,expr)]
  | None =>
    []
  end.

Lemma plan_expression_add_erases rows item :
  exact_value (pre_expression_add_counted EE EU edge_body expr_body rows item) =
    AnalysesSsaPre.pre_finalize_add_expression EE EU rows item.
Proof.
  reflexivity.
Qed.

Lemma plan_expression_rows_erases items :
  exact_value (pre_expression_rows_counted EE EU edge_body expr_body items) =
    AnalysesSsaPre.pre_finalize_expression_rows EE EU items.
Proof.
  unfold pre_expression_rows_counted, AnalysesSsaPre.pre_finalize_expression_rows.
  rewrite exact_fold_left_erases. apply plan_fold_left_agrees.
  exact plan_expression_add_erases.
Qed.

Lemma plan_expression_add_bound rows item :
  exact_units (pre_expression_add_counted EE EU edge_body expr_body rows item) <=
    1024 * (1 + plan_item_weight item).
Proof.
  unfold pre_expression_add_counted. plan_work.
  unfold plan_item_weight. lia.
Qed.

Lemma plan_expression_rows_bound items bound :
  (forall item, In item items -> plan_item_weight item <= bound) ->
  exact_units (pre_expression_rows_counted EE EU edge_body expr_body items) <=
    128 + length items * (128 + 1024 * (1 + bound)).
Proof.
  intro Hitems. unfold pre_expression_rows_counted. apply plan_fold_units.
  intros rows item Hin. pose proof (plan_expression_add_bound rows item).
  specialize (Hitems item Hin). nia.
Qed.

Lemma plan_materialize_erases plan :
  exact_value (pre_materialize_counted EE EU view edge_body expr_body recomputed_body plan) =
    AnalysesSsaPre.pre_finalize_materialize EE EU view plan.
Proof.
  unfold pre_materialize_counted, AnalysesSsaPre.pre_finalize_materialize.
  plan_erase. cbn [exact_elements exact_value].
  rewrite !plan_flat_map_erases.
  assert (Hinsert : forall phis,
    flat_map (fun binding => exact_value
      (
      match snd binding with
      | PreInserted edge expr =>
        exact_case 613 (exact_return 613 [(edge,expr)])
      | _ =>
        exact_case 614 (exact_return 614 [])
      end : exact_counted (pre_materialize_call E U) (list (E * U)))) phis =
    flat_map plan_insert_item phis).
  { intro phis. apply plan_flat_map_agrees. intros [key version].
    destruct version; reflexivity. }
  assert (Hdelete : forall reloads,
    flat_map (fun binding => exact_value
      (exact_bind 619 (exact_call
        (PreMaterializeRecomputed (fst binding) (pre_recomputed view (fst binding)))
        (recomputed_body (fst binding)) (pre_recomputed view (fst binding)))
        (fun result =>
        match result with
        | Some expr =>
          exact_case 620 (exact_return 620 [(fst binding,expr)])
        | None =>
          exact_case 621 (exact_return 621 [])
        end))) reloads = flat_map plan_delete_item reloads).
  { intro reloads. apply plan_flat_map_agrees. intro binding. plan_erase.
    unfold plan_delete_item.
    destruct (pre_recomputed view (fst binding)); reflexivity. }
  rewrite Hinsert, Hdelete, !plan_expression_rows_erases. reflexivity.
Qed.

Lemma plan_insert_weight plan item :
  In item (flat_map plan_insert_item (Map.elements (pre_phi_versions plan))) ->
  plan_item_weight item <= pre_materialize_input_operand EE EU view
    edge_body expr_body recomputed_body plan.
Proof.
  intro Hin. apply in_flat_map in Hin. destruct Hin as [[key version] [Hbinding Hitem]].
  destruct version as [u|e u|e u|e u]; cbn [plan_insert_item snd] in Hitem;
    try contradiction.
  destruct Hitem as [Hitem|Hitem]; [subst item|contradiction].
  unfold pre_materialize_input_operand.
  pose proof (plan_max_member _ (fun binding =>
    match snd binding with
    | PreInserted edge expr =>
      edge_body edge + expr_body expr +
        Pos.size_nat (encode EE edge) + Pos.size_nat (encode EU expr)
    | _ =>
      0
    end) (Map.elements (pre_phi_versions plan)) (key,PreInserted e u) Hbinding) as Hmax.
  cbn [snd] in Hmax. unfold plan_item_weight. cbn [fst snd]. lia.
Qed.

Lemma plan_reload_weight plan binding :
  In binding (Map.elements (pre_reload_versions plan)) ->
  edge_body (fst binding) + recomputed_body (fst binding) +
    Pos.size_nat (encode EE (fst binding)) +
    match pre_recomputed view (fst binding) with
    | Some expr =>
      expr_body expr + Pos.size_nat (encode EU expr)
    | None =>
      0
    end <= pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan.
Proof.
  intro Hin. unfold pre_materialize_input_operand.
  pose proof (plan_max_member _ (fun binding =>
    edge_body (fst binding) + recomputed_body (fst binding) +
      Pos.size_nat (encode EE (fst binding)) +
      match pre_recomputed view (fst binding) with
      | Some expr =>
        expr_body expr + Pos.size_nat (encode EU expr)
      | None =>
        0
      end) (Map.elements (pre_reload_versions plan)) binding Hin) as Hmax.
  cbv beta iota zeta in Hmax |- *.
  lia.
Qed.

Lemma plan_delete_weight plan item :
  In item (flat_map plan_delete_item (Map.elements (pre_reload_versions plan))) ->
  plan_item_weight item <= pre_materialize_input_operand EE EU view
    edge_body expr_body recomputed_body plan.
Proof.
  intro Hin. apply in_flat_map in Hin. destruct Hin as [binding [Hbinding Hitem]].
  pose proof (plan_reload_weight plan binding Hbinding) as Hweight.
  unfold plan_delete_item in Hitem.
  destruct (pre_recomputed view (fst binding)) as [expr|]; [|contradiction].
  destruct Hitem as [Hitem|Hitem]; [subst item|contradiction].
  unfold plan_item_weight. cbn [fst snd]. lia.
Qed.

Lemma plan_insert_length phis : length (flat_map plan_insert_item phis) <= length phis.
Proof.
  apply plan_flat_map_length. intros [key version] Hin. destruct version; cbn; lia.
Qed.

Lemma plan_delete_length reloads : length (flat_map plan_delete_item reloads) <= length reloads.
Proof.
  apply plan_flat_map_length. intros binding Hin. unfold plan_delete_item.
  destruct (pre_recomputed view (fst binding)); cbn; lia.
Qed.

Let insertion_step (binding : ((E * E) * U) * pre_version E U)
    : exact_counted (pre_materialize_call E U) (list (E * U)) :=
  match snd binding with
  | PreInserted edge expr =>
    exact_case 613 (exact_return 613 [(edge,expr)])
  | _ =>
    exact_case 614 (exact_return 614 [])
  end.

Let deletion_step (binding : E * pre_version E U)
    : exact_counted (pre_materialize_call E U) (list (E * U)) :=
  exact_bind 619 (exact_call
    (PreMaterializeRecomputed (fst binding) (pre_recomputed view (fst binding)))
    (recomputed_body (fst binding)) (pre_recomputed view (fst binding)))
    (fun result =>
    match result with
    | Some expr =>
      exact_case 620 (exact_return 620 [(fst binding,expr)])
    | None =>
      exact_case 621 (exact_return 621 [])
    end).

Lemma plan_insert_run_erases phis :
  exact_value (exact_flat_map 612 insertion_step phis) = flat_map plan_insert_item phis.
Proof.
  rewrite plan_flat_map_erases. apply plan_flat_map_agrees. intros [key version].
  destruct version; reflexivity.
Qed.

Lemma plan_delete_run_erases reloads :
  exact_value (exact_flat_map 618 deletion_step reloads) = flat_map plan_delete_item reloads.
Proof.
  rewrite plan_flat_map_erases. apply plan_flat_map_agrees. intro binding.
  unfold deletion_step, plan_delete_item. plan_erase.
  destruct (pre_recomputed view (fst binding)); reflexivity.
Qed.

Lemma plan_insert_run_bound phis :
  exact_units (exact_flat_map 612 insertion_step phis) <= 128 + length phis * 640.
Proof.
  apply (plan_flat_map_units _ _ _ _ _ _ 128).
  intros [key version] Hin. destruct version; cbn [insertion_step snd]; plan_work;
    cbn [length]; split; lia.
Qed.

Lemma plan_delete_step_bound plan binding :
  In binding (Map.elements (pre_reload_versions plan)) ->
  exact_units (deletion_step binding) <= 256 +
    pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan /\
  length (exact_value (deletion_step binding)) <= 1.
Proof.
  intro Hin. pose proof (plan_reload_weight plan binding Hin) as Hweight.
  unfold deletion_step. plan_work.
  destruct (pre_recomputed view (fst binding)); plan_work; cbn [length]; split; lia.
Qed.

Lemma plan_delete_run_bound plan :
  exact_units (exact_flat_map 618 deletion_step (Map.elements (pre_reload_versions plan))) <=
    128 + length (Map.elements (pre_reload_versions plan)) *
      (768 + pre_materialize_input_operand EE EU view
        edge_body expr_body recomputed_body plan).
Proof.
  apply (plan_flat_map_units _ _ _ _ _ _
    (256 + pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan)).
  intros binding Hin. apply plan_delete_step_bound. exact Hin.
Qed.

Lemma plan_materialize_units plan :
  exact_units (pre_materialize_counted EE EU view edge_body expr_body recomputed_body plan) =
  65 + 32 * (Datatypes.S (exact_trie_nodes (pre_phi_versions plan)))^2 +
    8 * length (Map.elements (pre_phi_versions plan)) + 64 +
    (exact_units (exact_flat_map 612 insertion_step (Map.elements (pre_phi_versions plan))) +
    64 + (exact_units (pre_expression_rows_counted EE EU edge_body expr_body
      (flat_map plan_insert_item (Map.elements (pre_phi_versions plan)))) + 64 +
    (65 + 32 * (Datatypes.S (exact_trie_nodes (pre_reload_versions plan)))^2 +
    8 * length (Map.elements (pre_reload_versions plan)) + 64 +
    (exact_units (exact_flat_map 618 deletion_step (Map.elements (pre_reload_versions plan))) +
    64 + (exact_units (pre_expression_rows_counted EE EU edge_body expr_body
      (flat_map plan_delete_item (Map.elements (pre_reload_versions plan)))) + 64 + 64))))).
Proof.
  unfold pre_materialize_counted. fold insertion_step deletion_step.
  plan_work. rewrite !plan_elements_units.
  rewrite plan_insert_run_erases, plan_delete_run_erases. reflexivity.
Qed.

Lemma plan_materialize_work_bound plan :
  exact_units (pre_materialize_counted EE EU view edge_body expr_body recomputed_body plan) <=
    4096 * (1 + exact_trie_nodes (pre_phi_versions plan) +
      exact_trie_nodes (pre_reload_versions plan)) ^ 2 *
    (1 + pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan).
Proof.
  pose proof (plan_insert_run_bound (Map.elements (pre_phi_versions plan))) as Hinsert.
  pose proof (plan_delete_run_bound plan) as Hdelete.
  pose proof (plan_expression_rows_bound
    (flat_map plan_insert_item (Map.elements (pre_phi_versions plan)))
    (pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan)
    (plan_insert_weight plan)) as Hirows.
  pose proof (plan_expression_rows_bound
    (flat_map plan_delete_item (Map.elements (pre_reload_versions plan)))
    (pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan)
    (plan_delete_weight plan)) as Hdrows.
  pose proof (plan_insert_length (Map.elements (pre_phi_versions plan))) as Hilength.
  pose proof (plan_delete_length (Map.elements (pre_reload_versions plan))) as Hdlength.
  pose proof (plan_elements_length _ _ (pre_phi_versions plan)) as Hphis.
  pose proof (plan_elements_length _ _ (pre_reload_versions plan)) as Hreloads.
  rewrite plan_materialize_units at 1.
  eapply Nat.le_trans.
  - eapply (plan_linear_materialize_bound _ _ _ _ _ _
      (pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan));
      eassumption.
  - apply plan_materialize_geometry_bound.
Qed.

(** Materialization returns the legacy plan, preserves both version maps and meets its budget. *)
Theorem audit_pre_materialize_full_source :
  audit_pre_materialize_full_source_statement EE EU view edge_body expr_body recomputed_body.
Proof.
  intro plan. cbv zeta.
  split; [apply plan_materialize_erases|].
  split.
  - rewrite plan_materialize_erases. reflexivity.
  - split.
    + rewrite plan_materialize_erases. reflexivity.
    + eapply Nat.le_trans; [apply plan_materialize_work_bound|].
      unfold pre_materialize_input_budget.
      change (4096 * (1 + exact_trie_nodes (pre_phi_versions plan) +
        exact_trie_nodes (pre_reload_versions plan)) ^ 2 *
        (1 + pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan) <=
        (Nat.of_num_uint 65536%uint) * (1 + exact_trie_nodes (pre_phi_versions plan) +
          exact_trie_nodes (pre_reload_versions plan)) ^ 4 *
        (1 + pre_materialize_input_operand EE EU view edge_body expr_body recomputed_body plan)^4).
      set (nodes := 1 + exact_trie_nodes (pre_phi_versions plan) +
        exact_trie_nodes (pre_reload_versions plan)).
      set (width := 1 + pre_materialize_input_operand EE EU view
        edge_body expr_body recomputed_body plan).
      assert (Hnodes : 1 <= nodes) by (unfold nodes; lia).
      assert (Hwidth : 1 <= width) by (unfold width; lia).
      apply Nat.mul_le_mono.
      * apply Nat.mul_le_mono.
        { apply Nat.leb_le. vm_compute. reflexivity. }
        apply Nat.pow_le_mono_r; lia.
      * assert (Hpower : width^1 <= width^4) by (apply Nat.pow_le_mono_r; lia).
        now rewrite Nat.pow_1_r in Hpower.
Qed.

End Materialize.

Arguments audit_pre_materialize_full_source : clear implicits.
