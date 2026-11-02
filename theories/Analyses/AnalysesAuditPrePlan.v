(** * PRE finalization and materialization source

    Counted finalization selects versions and materializes the plan from actual prepared rows.
    For example, an inserted phi operand becomes an insertion row.
    Builds on: shared source counters and PRE placement. *)

From Stdlib Require Import Decimal Arith Bool List PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSsaLiveQuery AnalysesSsaPre
  AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphCore GraphDominators GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
Import List.ListNotations.

(* Definition source: PreMaterialize.v *)
(** * Complete PRE plan materialization source blocks

    Both input maps are enumerated once and each output row is built on its actual state.
    For example, a phi insertion and a reload deletion use separate occurrence streams.
    Builds on: AnalysesSsaPre and the private typed source combinators. *)

Inductive pre_materialize_call (E U : Type) : Type :=
  | PreMaterializePhi (call : exact_map_call ((E * E) * U) (pre_version E U))
  | PreMaterializeReload (call : exact_map_call E (pre_version E U))
  | PreMaterializeRows (call : exact_map_call E (FinSet.t U))
  | PreMaterializeSet (call : exact_map_call U unit)
  | PreMaterializeRecomputed (edge : E) (result : option U).

Arguments PreMaterializePhi {E U}.

Arguments PreMaterializeReload {E U}.

Arguments PreMaterializeRows {E U}.

Arguments PreMaterializeSet {E U}.

Arguments PreMaterializeRecomputed {E U}.

Section Materialize.

Context {S O N E U C : Type} (EE : encoding E) (EU : encoding U)
  (view : pre_expression_view S O N E U C).

Context (edge_body : E -> nat) (expr_body : U -> nat) (recomputed_body : E -> nat).

Definition pre_expression_add_counted (rows : Map.t E (FinSet.t U)) (item : E * U)
    : exact_counted (pre_materialize_call E U) (Map.t E (FinSet.t U)) :=
  exact_bind 600 (exact_get PreMaterializeRows EE edge_body (fst item) rows) (fun found =>
  exact_bind 601 (exact_case 601 (exact_return 601 (
    match found with
    | Some set => set
    | None => FinSet.empty end))) (fun before =>
  exact_bind 602 (exact_set PreMaterializeSet EU expr_body (snd item) tt before) (fun after =>
    exact_set PreMaterializeRows EE edge_body (fst item) after rows))).

Definition pre_expression_rows_counted (items : list (E * U))
    : exact_counted (pre_materialize_call E U) (Map.t E (FinSet.t U)) :=
  exact_fold_left 603 pre_expression_add_counted items Map.empty.

Definition pre_materialize_counted (plan : pre_plan E U)
    : exact_counted (pre_materialize_call E U) (pre_plan E U) :=
  exact_bind 610 (exact_elements PreMaterializePhi (pre_phi_versions plan)) (fun phis =>
  exact_bind 611 (exact_flat_map 612 (fun binding =>
    match snd binding with
    | PreInserted edge expr => exact_case 613 (exact_return 613 [(edge,expr)])
    | _ => exact_case 614 (exact_return 614 [])
    end) phis) (fun insertion_items =>
  exact_bind 615 (pre_expression_rows_counted insertion_items) (fun insertions =>
  exact_bind 616 (exact_elements PreMaterializeReload (pre_reload_versions plan)) (fun reloads =>
  exact_bind 617 (exact_flat_map 618 (fun binding =>
    let edge := fst binding in
    let result := pre_recomputed view edge in
    exact_bind 619 (exact_call (PreMaterializeRecomputed edge result)
      (recomputed_body edge) result) (fun result =>
        match result with
        | Some expr => exact_case 620 (exact_return 620 [(edge,expr)])
        | None => exact_case 621 (exact_return 621 [])
        end)) reloads) (fun deletion_items =>
  exact_bind 622 (pre_expression_rows_counted deletion_items) (fun deletions =>
    exact_return 623 (PrePlan insertions deletions (pre_reload_versions plan) (pre_phi_versions
      plan)))))))).

Definition pre_materialize_input_operand (plan : pre_plan E U) : nat :=
  fold_right (fun binding rest =>
    let extra :=
      match snd binding with
      | PreInserted edge expr =>
        edge_body edge + expr_body expr +
          Pos.size_nat (encode EE edge) + Pos.size_nat (encode EU expr)
      | _ => 0 end in Nat.max extra rest) 0 (Map.elements (pre_phi_versions plan)) +
  fold_right (fun binding rest =>
    let edge := fst binding in
    let extra := edge_body edge + recomputed_body edge + Pos.size_nat (encode EE edge) +
      match pre_recomputed view edge with
      | Some expr => expr_body expr + Pos.size_nat (encode EU expr)
      | None => 0 end in Nat.max extra rest) 0 (Map.elements (pre_reload_versions plan)).

Definition pre_materialize_input_budget (plan : pre_plan E U) : nat :=
  let nodes := exact_trie_nodes (pre_phi_versions plan) + exact_trie_nodes (pre_reload_versions
    plan) in
  (Nat.of_num_uint 65536%uint) * Nat.pow (Datatypes.S nodes) 4 *
    Nat.pow (Datatypes.S (pre_materialize_input_operand plan))
    4.

(** Materialization preserves both version maps and returns the plain plan within
    its input budget. *)
Definition audit_pre_materialize_full_source_statement : Prop := forall plan,
  let run := pre_materialize_counted plan in
  exact_value run = AnalysesSsaPre.pre_finalize_materialize EE EU view plan /\
  pre_reload_versions (exact_value run) = pre_reload_versions plan /\
  pre_phi_versions (exact_value run) = pre_phi_versions plan /\
  exact_units run <= pre_materialize_input_budget plan.

End Materialize.

(* Definition source: PreFinalize.v *)
(** * PRE finalize scope and operand source equations

    Every branch preserves actual intermediate scope/plan values; both strict Boolean
    operands and both expression encodings are retained. Builds on: AnalysesSsaPre. *)

Inductive pre_finalize_call (B BE N E U : Type) : Type :=
  | PfFlags (call : exact_map_call (B * U) bool)
  | PfScope (call : exact_map_call (frg_version B E U) (pre_version E U))
  | PfReload (call : exact_map_call E (pre_version E U))
  | PfPhi (call : exact_map_call ((E * E) * U) (pre_version E U))
  | PfOccurrence (call : exact_map_call E (frg_version B E U))
  | PfDom (call : exact_map_call N positive)
  | PfExpr (call : exact_map_call U unit)
  | PfNodeRows (call : exact_map_call N (list (B * U)))
  | PfArguments (call : exact_map_call N (list (pre_finalize_argument B BE E U)))
  | PfEdges (call : exact_map_call N (list E))
  | PfIdom (call : exact_map_call N N)
  | PfOutputs (call : exact_map_call N (Map.t (frg_version B E U) (pre_version E U)))
  | PfInitial (expr : U) (result : bool)
  | PfRecomputed (edge : E) (result : option U)
  | PfPure (expr : U) (result : bool)
  | PfTranslate (incoming : BE) (expr : U) (result : option U)
  | PfKill (edge : E) (expr : U) (result : bool)
  | PfParameter (block : B) (edge : E)
  | PfSource (edge : E) (point : N)
  | PfTarget (edge : E) (point : N)
  | PfExpressionTarget (edge : E) (point : N)
  | PfPositiveCompare (first second : positive) (result : bool).

Arguments PfFlags {B BE N E U}.

Arguments PfScope {B BE N E U}.

Arguments PfReload {B BE N E U}.

Arguments PfPhi {B BE N E U}.

Arguments PfOccurrence {B BE N E U}.

Arguments PfDom {B BE N E U}.

Arguments PfExpr {B BE N E U}.

Arguments PfNodeRows {B BE N E U}.

Arguments PfArguments {B BE N E U}.

Arguments PfEdges {B BE N E U}.

Arguments PfIdom {B BE N E U}.

Arguments PfOutputs {B BE N E U}.

Arguments PfInitial {B BE N E U}.

Arguments PfRecomputed {B BE N E U}.

Arguments PfPure {B BE N E U}.

Arguments PfTranslate {B BE N E U}.

Arguments PfKill {B BE N E U}.

Arguments PfParameter {B BE N E U}.

Arguments PfSource {B BE N E U}.

Arguments PfTarget {B BE N E U}.

Arguments PfExpressionTarget {B BE N E U}.

Arguments PfPositiveCompare {B BE N E U}.

Section Finalize.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U).

Context (block_body : B -> nat) (point_body : N -> nat) (edge_body : E -> nat)
  (expr_body : U -> nat).

(** Finalization traces calls while carrying the version scope and partial plan. *)
Let Call := pre_finalize_call B BE N E U.

Let Scope := Map.t (frg_version B E U) (pre_version E U).

Let Work := (Scope * pre_plan E U)%type.

Definition pre_flag_body (key : B * U) : nat :=
  64 + block_body (fst key) + expr_body (snd key) +
    32 * Pos.size_nat (encode (pair_encoding EB EU) key).

Definition pre_scope_body (version : frg_version B E U) : nat :=
  128 + 64 * Pos.size_nat (encode (frg_version_encoding EB EE EU) version) +
    match version with
    | FrUnavailable u | FrInitial u => expr_body u
    | FrFresh e u => edge_body e + expr_body u
    | FrPhi b u => block_body b + expr_body u
    end.

Definition pre_phi_body (key : (E * E) * U) : nat :=
  128 + edge_body (fst (fst key)) + edge_body (snd (fst key)) + expr_body (snd key) +
    64 * Pos.size_nat (encode (pair_encoding (pair_encoding EE EE) EU) key).

Definition pre_flag_get_counted (flags : Map.t (B * U) bool) (key : B * U)
    : exact_counted Call bool :=
  exact_bind 700 (exact_get PfFlags (pair_encoding EB EU) pre_flag_body key flags)
    (fun found => exact_case 700 (exact_return 700 (
      match found with
      | Some b => b
      | None => false end))).

Definition pre_will_counted (facts : ssapre_facts B U) (key : B * U) : exact_counted Call bool :=
  exact_bind 701 (pre_flag_get_counted (ssapre_can_available facts) key) (fun can =>
  exact_bind 702 (pre_flag_get_counted (ssapre_later facts) key) (fun later =>
    exact_return 703 (can && negb later))).

Definition pre_insert_operand_counted (facts : ssapre_facts B U) (operand : frg_operand B E U)
    : exact_counted Call bool :=
  match frg_operand_version operand with
  | FrUnavailable _ => exact_case 704 (exact_return 704 true)
  | FrPhi b u =>
    exact_case 705 (exact_bind 706 (pre_will_counted facts (b,u))
      (fun will => exact_return 707 (negb (frg_operand_real_use operand) && negb will)))
  | _ => exact_case 708 (exact_return 708 false)
  end.

Definition pre_dominates_counted (tree : dom_tree N) (d n : N) : exact_counted Call bool :=
  exact_bind 710 (exact_get PfDom EN point_body d (tin tree)) (fun first =>
    match first with
    | None => exact_case 710 (exact_return 710 false)
    | Some x => exact_case 711 (exact_bind 712 (exact_get PfDom EN point_body n (tin tree)) (fun
      second =>
        match second with
        | None => exact_case 712 (exact_return 712 false)
        | Some y => exact_case 713 (exact_bind 714 (exact_get PfDom EN point_body d (tout tree))
          (fun third =>
            match third with
            | None => exact_case 714 (exact_return 714 false)
            | Some z => exact_case 715 (exact_bind 716 (exact_get PfDom EN point_body n (tout tree))
              (fun fourth =>
                match fourth with
                | None => exact_case 716 (exact_return 716 false)
                | Some w =>
                  let first := Pos.leb x y in
                  exact_bind 717 (exact_call (PfPositiveCompare x y first)
                    (audit_binary_weight (Z.pos x) (Z.pos y)) first) (fun first =>
                  let second := Pos.leb w z in
                  exact_bind 718 (exact_call (PfPositiveCompare w z second)
                    (audit_binary_weight (Z.pos w) (Z.pos z)) second) (fun second =>
                    exact_return 719 (first && second)))
                end))
            end))
        end))
    end).

Definition pre_version_point_counted (version : pre_version E U) : exact_counted Call (option N) :=
  match version with
  | PreInitial _ =>
    exact_case 720 (exact_return 720
      (nth_error (Graph.entries (cfg (gkview (pre_genkill (pre_expression a))))) 0))
  | PreComputed e _ | PreInserted e _ | PreMerged e _ =>
    let point := Graph.target (cfg (gkview (pre_genkill (pre_expression a)))) e in
    exact_case 721 (exact_bind 722 (exact_call (PfExpressionTarget e point) 0 point)
      (fun point => exact_return 723 (Some point)))
  end.

Definition pre_available_counted (tree : dom_tree N) (scope : Scope)
    (definition : frg_version B E U) (u : U) (n : N)
    : exact_counted Call (option (pre_version E U)) :=
  exact_bind 730 (exact_get PfScope (frg_version_encoding EB EE EU) pre_scope_body definition scope)
    (fun found =>
      match found with
      | None => exact_case 731 (exact_return 731 None)
      | Some version => exact_case 732
        (exact_bind 733 (exact_encode PfExpr EU expr_body (pre_version_expr version)) (fun first =>
        exact_bind 734 (exact_encode PfExpr EU expr_body u) (fun second =>
        let same := Pos.eqb first second in
        exact_bind 735 (exact_call (PfPositiveCompare first second same)
          (audit_binary_weight (Z.pos first) (Z.pos second)) same) (fun same =>
        if same then exact_case 736 (exact_bind 737 (pre_version_point_counted version)
          (fun point =>
          match point with
          | None => exact_case 738 (exact_return 738 None)
          | Some q => exact_case 739 (exact_bind 740 (pre_dominates_counted tree q n) (fun dominates
            =>
              exact_case 741 (exact_return 741 (if dominates then Some version else None))))
          end))
        else exact_case 742 (exact_return 742 None)))))
      end).

Definition pre_select_counted (plan : pre_plan E U) (parameter incoming : E)
    (u : U) (version : pre_version E U) : exact_counted Call (pre_plan E U) :=
  exact_bind 750 (exact_set PfPhi (pair_encoding (pair_encoding EE EE) EU) pre_phi_body
    ((parameter,incoming),u) version (pre_phi_versions plan)) (fun phis =>
    exact_return 751 (PrePlan (pre_insertions plan) (pre_deletions plan) (pre_reload_versions plan)
      phis)).

Definition pre_occurrence_counted (f : factored_redundancy_graph B BE E U)
    (tree : dom_tree N) (work : Work) (edge : E) : exact_counted Call Work :=
  let '(scope,plan) := work in
  let recomputed := pre_recomputed (pre_expression a) edge in
  exact_bind 760 (exact_call (PfRecomputed edge recomputed) 0 recomputed) (fun recomputed =>
    match recomputed with
    | None => exact_case 761 (exact_return 761 work)
    | Some u =>
      exact_case 762 (exact_bind 763 (exact_get PfOccurrence EE edge_body edge
        (frg_occurrence_index f)) (fun found =>
        match found with
        | None => exact_case 764 (exact_return 764 work)
        | Some definition =>
          let pure := pre_total_pure (pre_expression a) u in
          exact_case 765 (exact_bind 766 (exact_call (PfPure u pure) 0 pure) (fun pure =>
          if pure then exact_case 767
            (let point := Graph.source (live_graph (point_model (pre_ssa_points a))) edge in
            exact_bind 768 (exact_call (PfSource edge point) 0 point) (fun point =>
            exact_bind 769 (pre_available_counted tree scope definition u point) (fun available =>
              match available with
              | Some version =>
                exact_case 770 (exact_bind 771
                  (exact_set PfReload EE edge_body edge version (pre_reload_versions plan))
                  (fun reloads =>
                  exact_return 772 (scope,PrePlan (pre_insertions plan) (pre_deletions plan)
                    reloads (pre_phi_versions plan))))
              | None =>
                exact_case 773 (exact_bind 774 (exact_set PfScope
                  (frg_version_encoding EB EE EU) pre_scope_body definition (PreComputed edge u)
                  scope)
                  (fun next => exact_return 775 (next,plan)))
              end)))
          else exact_case 776 (exact_return 776 work)))
        end))
    end).

(** The counted finalizer helpers return the original flags, dominance and occurrence results. *)
Definition pre_finalize_helpers_erasure_statement : Prop :=
  (forall facts key, exact_value (pre_will_counted facts key) = AnalysesSsaPre.pre_finalize_will EB
    EU facts key) /\
  (forall facts operand, exact_value (pre_insert_operand_counted facts operand) =
    AnalysesSsaPre.pre_finalize_insert_operand EB EU facts operand) /\
  (forall tree d n, exact_value (pre_dominates_counted tree d n) = dominates_b EN tree d n) /\
  (forall tree scope definition u n, exact_value (pre_available_counted tree scope definition u n) =
    AnalysesSsaPre.pre_finalize_available EB EN EE EU a tree scope definition u n) /\
  (forall f tree work edge, exact_value (pre_occurrence_counted f tree work edge) =
    AnalysesSsaPre.pre_finalize_occurrence EB EN EE EU a f tree work edge).

Definition pre_define_phi_counted (scope : Scope) (key : B * U) : exact_counted Call Scope :=
  let edge := parameter_edge (pre_ssa_points a) (fst key) in
  exact_bind 780 (exact_call (PfParameter (fst key) edge) 0 edge) (fun edge =>
    exact_set PfScope (frg_version_encoding EB EE EU) pre_scope_body
      (FrPhi (fst key) (snd key)) (PreMerged edge (snd key)) scope).

Definition pre_initial_scope_counted (versions : list (frg_version B E U)) : exact_counted Call
  Scope :=
  exact_fold_left 781 (fun scope version =>
    match version with
    | FrInitial u =>
      let available := pre_initial_available a u in
        exact_case 782 (exact_bind 783 (exact_call (PfInitial u available) 0 available) (fun
          available =>
        if available then exact_case 784 (exact_set PfScope (frg_version_encoding EB EE EU)
          pre_scope_body version (PreInitial u) scope)
        else exact_case 785 (exact_return 785 scope)))
    | _ => exact_case 786 (exact_return 786 scope) end) versions Map.empty.

Definition pre_argument_counted (facts : ssapre_facts B U) (tree : dom_tree N)
    (scope : Scope) (plan : pre_plan E U) (argument : pre_finalize_argument B BE E U)
    : exact_counted Call (pre_plan E U) :=
  let b := pre_arg_block argument in
  let u := pre_arg_expression argument in
  let incoming := pre_arg_point_edge argument in
  let parameter := parameter_edge (pre_ssa_points a) b in
  exact_bind 790 (exact_call (PfParameter b parameter) 0 parameter) (fun parameter =>
  exact_bind 791 (pre_will_counted facts (b,u)) (fun will =>
  if will then exact_case 792
    (let translated := pre_phi_translate a (pre_arg_block_edge argument) u in
    exact_bind 793 (exact_call (PfTranslate (pre_arg_block_edge argument) u translated) 0
      translated)
      (fun translated =>
        match translated with
        | None => exact_case 794 (exact_return 794 plan)
        | Some value => exact_case 795
          (exact_bind 796 (pre_insert_operand_counted facts (pre_arg_operand argument))
          (fun insert =>
          if insert then exact_case 797
            (let pure := pre_total_pure (pre_expression a) value in
            exact_bind 798 (exact_call (PfPure value pure) 0 pure) (fun pure =>
            let killed := kill (pre_genkill (pre_expression a)) incoming value in
            exact_bind 799 (exact_call (PfKill incoming value killed) 0 killed) (fun killed =>
            if pure && negb killed then exact_case 800
              (pre_select_counted plan parameter incoming u (PreInserted incoming value))
            else exact_case 801 (exact_return 801 plan))))
          else exact_case 802
            (let source := Graph.source (live_graph (point_model (pre_ssa_points a))) incoming in
            exact_bind 803 (exact_call (PfSource incoming source) 0 source) (fun source =>
            exact_bind 804 (pre_available_counted tree scope
              (frg_operand_version (pre_arg_operand argument)) value source) (fun found =>
              match found with
              | Some version => exact_case 805
                (pre_select_counted plan parameter incoming u version)
              | None => exact_case 806 (exact_return 806 plan)
              end)))))
        end))
  else exact_case 807 (exact_return 807 plan))).

Definition pre_node_counted (f : factored_redundancy_graph B BE E U) (facts : ssapre_facts B U)
    (tree : dom_tree N) (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (phis : Map.t N (list (B * U))) (arguments : Map.t N (list (pre_finalize_argument B BE E U)))
    (work : Work) (n : N) : exact_counted Call Work :=
  let '(scope,plan) := work in
  exact_bind 810 (exact_get PfNodeRows EN point_body n phis) (fun found =>
  exact_bind 811 (exact_case 811 (exact_return 811 (
    match found with
    | Some rows => rows
    | None => [] end))) (fun keys =>
  exact_bind 812 (exact_fold_left 812 pre_define_phi_counted keys scope) (fun scope =>
  exact_bind 813 (exact_get PfArguments EN point_body n arguments) (fun found =>
  exact_bind 814 (exact_case 814 (exact_return 814 (
    match found with
    | Some rows => rows
    | None => [] end))) (fun args =>
  exact_bind 815 (exact_fold_left 815 (pre_argument_counted facts tree scope) args plan) (fun plan
    =>
  exact_bind 816 (exact_get PfEdges EN point_body n (out_index points)) (fun found =>
  exact_bind 817 (exact_case 817 (exact_return 817 (
    match found with
    | Some edges => edges
    | None => [] end))) (fun edges =>
    exact_fold_left 818 (pre_occurrence_counted f tree) edges (scope,plan))))))))).

Definition pre_table_step_counted (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) (tree : dom_tree N)
    (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (phis : Map.t N (list (B * U))) (arguments : Map.t N (list (pre_finalize_argument B BE E U)))
    (initial : Scope) (work : Map.t N Scope * pre_plan E U) (n : N)
    : exact_counted Call (Map.t N Scope * pre_plan E U) :=
  let '(outputs,plan) := work in
  exact_bind 820 (exact_get PfIdom EN point_body n (idom tree)) (fun parent =>
  exact_bind 821 (
    match parent with
    | None => exact_case 821 (exact_return 821 initial)
    | Some parent => exact_case 822 (exact_bind 823 (exact_get PfOutputs EN point_body parent
      outputs)
        (fun found => exact_case 824 (exact_return 824 (
          match found with
          | Some scope => scope
          | None => initial end)))) end) (fun scope =>
  exact_bind 825 (pre_node_counted f facts tree points phis arguments (scope,plan) n) (fun result =>
  let '(scope,plan) := result in
  exact_bind 826 (exact_set PfOutputs EN point_body n scope outputs)
    (fun updated => exact_return 827 (updated,plan))))).

(** Erasing the counted scope and table steps recovers the original finalization loop. *)
Definition pre_finalize_loop_erases_statement : Prop :=
  (forall versions, exact_value (pre_initial_scope_counted versions) =
    AnalysesSsaPre.pre_finalize_initial EB EE EU a versions) /\
  (forall facts tree scope plan argument, exact_value (pre_argument_counted facts tree scope plan
    argument) =
    AnalysesSsaPre.pre_finalize_argument_step EB EN EE EU a facts tree scope plan argument) /\
  (forall f facts tree points phis arguments work n,
    exact_value (pre_node_counted f facts tree points phis arguments work n) =
    AnalysesSsaPre.pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n) /\
  (forall f facts tree points phis arguments initial work n,
    exact_value (pre_table_step_counted f facts tree points phis arguments initial work n) =
    AnalysesSsaPre.pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial
      work n).

End Finalize.

(* Definition source: PreFinalizeRows.v *)
(** * PRE Finalize's complete row preparation and ordered plan loop

    Card: AUD-SP. Graph backend preparation is a separate named prerequisite; this module
    takes its actual prepared graph/tree/order, never a fabricated branch or detached trace. *)
Inductive pre_rows_call (B BE N E U : Type) : Type :=
  | PrFinalize (call : pre_finalize_call B BE N E U)
  | PrPointIndex (call : exact_map_call BE E)
  | PrLinks (call : exact_map_call ((B * U) * BE) (frg_operand B E U))
  | PrPhis (call : exact_map_call (B * U) unit)
  | PrOut (point : N) (result : list E)
  | PrBlockEdge (edge : E) (result : option BE).

Arguments PrFinalize {B BE N E U}.

Arguments PrPointIndex {B BE N E U}.

Arguments PrLinks {B BE N E U}.

Arguments PrPhis {B BE N E U}.

Arguments PrOut {B BE N E U}.

Arguments PrBlockEdge {B BE N E U}.

Section Rows.

Context {S O B BE N E V K C U : Type}
  (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U)
  (block_body : B -> nat) (block_edge_body : BE -> nat) (point_body : N -> nat)
  (edge_body : E -> nat) (expr_body : U -> nat).

(** Row preparation records its own calls and nested finalization calls. *)
Let Call := pre_rows_call B BE N E U.

Definition pre_point_index_counted : exact_counted Call (Map.t BE E) :=
  exact_bind 1300 (exact_flat_map 1300 (fun n =>
    let result := Graph.out (live_graph (point_model (pre_ssa_points a))) n in
    exact_call (PrOut n result) 0 result)
      (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) (fun edges =>
  exact_bind 1301 (exact_flat_map 1301 (fun edge =>
    let result := block_edge_of (pre_ssa_points a) edge in
    exact_bind 1302 (exact_call (PrBlockEdge edge result) 0 result) (fun found =>
      match found with
      | None => exact_case 1303 (exact_return 1303 [])
      | Some be => exact_case 1304 (exact_return 1304 [(be,edge)]) end)) edges) (fun rows =>
    exact_fold_left 1305 (fun table row =>
      exact_set PrPointIndex EBE block_edge_body (fst row) (snd row) table) rows Map.empty)).

Definition pre_add_phi_row_counted (rows : Map.t N (list (B * U))) (item : N * (B * U))
    : exact_counted Call (Map.t N (list (B * U))) :=
  exact_bind 1310 (exact_get (fun c => PrFinalize (PfNodeRows c)) EN point_body (fst item) rows)
    (fun found => exact_bind 1311 (exact_case 1311 (exact_return 1311 (
      match found with
      | None => []
      | Some xs => xs end))) (fun xs =>
      exact_set (fun c => PrFinalize (PfNodeRows c)) EN point_body (fst item) (snd item :: xs)
        rows)).

Definition pre_phi_rows_counted (f : factored_redundancy_graph B BE E U) (facts : ssapre_facts B U)
    : exact_counted Call (Map.t N (list (B * U))) :=
  exact_bind 1320 (exact_set_elements PrPhis (frg_phi_index f)) (fun keys =>
  exact_bind 1321 (exact_flat_map 1321 (fun key =>
    exact_bind 1322 (exact_lift PrFinalize
      (pre_will_counted EB EU block_body expr_body facts key)) (fun will =>
    if will then exact_case 1323
      (let edge := parameter_edge (pre_ssa_points a) (fst key) in
      exact_bind 1324 (exact_call (PrFinalize (PfParameter (fst key) edge)) 0 edge) (fun edge =>
      let point := Graph.target (live_graph (point_model (pre_ssa_points a))) edge in
      exact_bind 1325 (exact_call (PrFinalize (PfTarget edge point)) 0 point)
        (fun point => exact_return 1326 [(point,key)])))
    else exact_case 1327 (exact_return 1327 []))) keys) (fun items =>
      exact_fold_left 1328 pre_add_phi_row_counted items Map.empty)).

Definition pre_add_argument_row_counted
    (rows : Map.t N (list (pre_finalize_argument B BE E U)))
    (item : N * pre_finalize_argument B BE E U)
    : exact_counted Call (Map.t N (list (pre_finalize_argument B BE E U))) :=
  exact_bind 1330 (exact_get (fun c => PrFinalize (PfArguments c)) EN point_body (fst item) rows)
    (fun found => exact_bind 1331 (exact_case 1331 (exact_return 1331 (
      match found with
      | None => []
      | Some xs => xs end))) (fun xs =>
      exact_set (fun c => PrFinalize (PfArguments c)) EN point_body (fst item) (snd item :: xs)
        rows)).

Definition pre_argument_rows_counted (f : factored_redundancy_graph B BE E U)
    : exact_counted Call (Map.t N (list (pre_finalize_argument B BE E U))) :=
  exact_bind 1340 pre_point_index_counted (fun points =>
  exact_bind 1341 (exact_elements PrLinks (frg_phi_operands f)) (fun links =>
  exact_bind 1342 (exact_flat_map 1342 (fun link => let '(((b,u),be),op) := link in
    exact_bind 1343 (exact_get PrPointIndex EBE block_edge_body be points) (fun found =>
      match found with
      | None => exact_case 1344 (exact_return 1344 [])
      | Some edge =>
        exact_case 1345
          (let point := Graph.source (live_graph (point_model (pre_ssa_points a))) edge in
          exact_bind 1346 (exact_call (PrFinalize (PfSource edge point)) 0 point)
            (fun point => exact_return 1347 [(point,PreFinalizeArgument b u be edge op)])) end))
            links)
    (fun items => exact_fold_left 1348 pre_add_argument_row_counted items Map.empty))).

Definition pre_finalize_order_counted (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) (tree : dom_tree N)
    (points : prepared EN (live_graph (point_model (pre_ssa_points a)))) (order : list N)
    : exact_counted Call (pre_plan E U) :=
  exact_bind 1350 (pre_phi_rows_counted f facts) (fun phis =>
  exact_bind 1351 (pre_argument_rows_counted f) (fun arguments =>
  exact_bind 1352 (exact_lift PrFinalize
    (pre_initial_scope_counted EB EE EU a block_body edge_body expr_body (frg_versions f))) (fun
      initial =>
  exact_bind 1353 (exact_fold_left 1353 (fun work n => exact_lift PrFinalize
    (pre_table_step_counted EB EN EE EU a block_body point_body edge_body expr_body
      f facts tree points phis arguments initial work n)) order
        (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))
      (fun result => exact_return 1354 (snd result))))).

(** Counted point, phi and argument indexes recover the original prepared rows. *)
Definition pre_finalize_rows_erases_statement : Prop :=
  pre_point_index_counted.(exact_value) = pre_point_edge_index EBE (pre_ssa_points a) /\
  (forall f facts, exact_value (pre_phi_rows_counted f facts) =
    AnalysesSsaPre.pre_finalize_phi_rows EB EN EU a f facts) /\
  (forall f, exact_value (pre_argument_rows_counted f) = AnalysesSsaPre.pre_finalize_argument_rows
    EBE EN a f).

(** The counted ordered finalizer returns the plan from the original table fold. *)
Definition pre_finalize_order_erases_statement : Prop := forall f facts tree points order,
  exact_value (pre_finalize_order_counted f facts tree points order) =
  snd (fold_left (AnalysesSsaPre.pre_finalize_table_step EB EN EE EU a f facts tree points
    (AnalysesSsaPre.pre_finalize_phi_rows EB EN EU a f facts)
    (AnalysesSsaPre.pre_finalize_argument_rows EBE EN a f)
    (AnalysesSsaPre.pre_finalize_initial EB EE EU a (frg_versions f))) order
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)).

(** Raw input support includes arbitrary parent-map values, argument translations and
    saved-definition edges, as well as the listed graph. No returned trace/work is read. *)
Definition pre_finalize_order_input_budget (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) (tree : dom_tree N)
    (points : prepared EN (live_graph (point_model (pre_ssa_points a)))) (order : list N) : nat :=
  let keys := FinSet.elements (frg_phi_index f) in
  let links := Map.elements (frg_phi_operands f) in
  let definitions := frg_versions f ++ map snd (Map.elements (frg_occurrence_index f)) ++
    map (fun row => frg_operand_version (snd row)) links in
  let blocks := Graph.nodes (block_graph (pre_ssa_points a)) ++ map fst keys ++
    map (fun row => fst (fst (fst row))) links ++
    flat_map (fun d =>
      match d with
      | FrPhi b _ => [b]
      | _ => [] end) definitions in
  let edges := edges_of (live_graph (point_model (pre_ssa_points a))) ++
    flat_map snd (Map.elements (out_index points)) ++
    map (parameter_edge (pre_ssa_points a)) blocks ++
    flat_map (fun d =>
      match d with
      | FrFresh e _ => [e]
      | _ => [] end) definitions in
  let exprs := map frg_version_expr definitions ++ map snd keys ++
    flat_map (fun row => let '(((b,u),be),_) := row in
      u ::
      match pre_phi_translate a be u with
      | Some value => [value]
      | None => [] end) links ++
    flat_map (fun e =>
      match pre_recomputed (pre_expression a) e with
      | Some u => [u]
      | None => []
        end) edges in
  let block_edges := map (fun row => snd (fst row)) links ++
    flat_map (fun e =>
      match block_edge_of (pre_ssa_points a) e with
      | Some be => [be]
      | None => []
        end) edges in
  let nodes := Graph.nodes (live_graph (point_model (pre_ssa_points a))) ++
    Graph.entries (live_graph (point_model (pre_ssa_points a))) ++
    Graph.entries (cfg (gkview (pre_genkill (pre_expression a)))) ++ order ++
    flat_map (fun row => [fst row;snd row]) (Map.elements (idom tree)) ++
    flat_map (fun e => [Graph.source (live_graph (point_model (pre_ssa_points a))) e;
      Graph.target (live_graph (point_model (pre_ssa_points a))) e;
      Graph.target (cfg (gkview (pre_genkill (pre_expression a)))) e]) edges in
  let width := fold_right Nat.max 0 (map (fun b => block_body b + Pos.size_nat (encode EB b))
    blocks) +
    fold_right Nat.max 0 (map (fun be => block_edge_body be + Pos.size_nat (encode EBE be))
      block_edges) +
    fold_right Nat.max 0 (map (fun n => point_body n + Pos.size_nat (encode EN n)) nodes) +
    fold_right Nat.max 0 (map (fun e => edge_body e + Pos.size_nat (encode EE e)) edges) +
    fold_right Nat.max 0 (map (fun u => expr_body u + Pos.size_nat (encode EU u)) exprs) +
    fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row))
      (Map.elements (tin tree) ++ Map.elements (tout tree))) in
  let geometry := 1 + length order + length blocks + length block_edges + length nodes +
    length edges + length exprs + length definitions + length keys + length links +
    exact_trie_nodes (frg_occurrence_index f) + exact_trie_nodes (frg_phi_operands f) +
    exact_trie_nodes (frg_phi_index f) + exact_trie_nodes (idom tree) +
    exact_trie_nodes (tin tree) + exact_trie_nodes (tout tree) + exact_trie_nodes (out_index points)
      in
  (Nat.of_num_uint 16777216%uint) * Nat.pow geometry 32 * Nat.pow (Datatypes.S width) 16.

(** The row and ordered-loop erasures hold and the counted finalizer fits its input budget. *)
Definition audit_pre_finalize_order_source_statement : Prop :=
  pre_finalize_rows_erases_statement /\ pre_finalize_order_erases_statement /\
  forall f facts tree points order,
    exact_units (pre_finalize_order_counted f facts tree points order) <=
      pre_finalize_order_input_budget f facts tree points order.

End Rows.
