(** * RewriteAuditIndexMatchReference

    Defines matching against a phase view and states prospective soundness and coverage contracts.
    For example, on a well-formed graph with an agreeing view, a matched hole pattern must bind
    exactly its hole.
    Builds on: RewriteMatch and
    RewriteAuditIndexReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Definition rw_view_match_candidates {K Sort V H} (EH : encoding H) (view : rw_phase_view K Sort V)
    (op : K) (ps : list (rw_pattern K Sort V H)) (a : rw_assignment H) : list rw_id :=
  match ps with
  | RWHole _ h :: _ =>
    match Map.get EH h a with
    | Some c => rw_view_parent_nodes view c
    | None => rw_view_operator_nodes view op
    end
  | _ => rw_view_operator_nodes view op
  end.

Definition rw_view_same_class {K Sort V} (view : rw_phase_view K Sort V) (a b : rw_id) : bool :=
  match rw_view_find view a, rw_view_find view b with
  | Some ra, Some rb => Pos.eqb ra rb
  | _, _ => false
  end.

Fixpoint rw_view_match_on {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (view : rw_phase_view K Sort V) (p : rw_pattern K Sort V H) (root : rw_id)
    (a : rw_assignment H) {struct p} : list (rw_assignment H) :=
  match p with
  | RWHole s h =>
    match rw_view_find view root, rw_view_sort view root with
    | Some canonical, Some ty =>
      if rw_key_eq_dec ES s ty then rw_bind EH h canonical a else []
    | _, _ => []
    end
  | RWPVar s v =>
    flat_map (fun n =>
      match rw_view_node view n with
      | Some (owner, RWNVar ty w) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EV v w then
            if rw_view_same_class view root owner then [a] else []
          else []
        else []
      | _ => []
      end) (rw_view_variable_nodes view v)
  | RWPApp s op ps =>
    flat_map (fun n =>
      match rw_view_node view n with
      | Some (owner, RWNApp ty other ids) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EK op other then
            if rw_view_same_class view root owner then
              rw_match_children (map (rw_view_match_on EK ES EV EH view) ps) ids a
            else []
          else []
        else []
      | _ => []
      end) (rw_view_match_candidates EH view op ps a)
  end.

Definition rw_view_match {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (view : rw_phase_view K Sort V) (root : rw_id)
    (pattern : rw_pattern K Sort V H) : list (rw_assignment H) :=
  rw_distinct_assignments EH (rw_view_match_on EK ES EV EH view pattern root Map.empty).

(** For a well-formed graph and agreeing view, a returned covered assignment whose
    pattern instantiates to a term represents that term at the queried root. *)
Definition rw_view_match_sound_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) view root
    (pattern : rw_pattern K Sort V H) assignment sub term,
    rw_graph_wf sig g ->
    rw_view_agrees g view ->
    In assignment (rw_view_match EK ES EV EH view root pattern) ->
    rw_covers EH g pattern assignment sub ->
    rw_instantiate sub pattern = Some term ->
    rw_represents g root term.

(** For a well-formed clean graph and agreeing view, a typed pattern instantiating to
    a represented term has a matching assignment covering its substitution. *)
Definition rw_view_match_complete_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    view root (pattern : rw_pattern K Sort V H) sub term,
    rw_graph_wf sig g -> rw_view_agrees g view -> rw_clean g ->
    rwp_typed sig (fun h => option_map rw_sort (sub h)) pattern ->
    rw_instantiate sub pattern = Some term -> rw_represents g root term ->
    exists assignment,
      In assignment (rw_view_match EK ES EV EH view root pattern) /\
      rw_covers EH g pattern assignment sub.

(** For a well-formed graph and agreeing view, each matching assignment is well formed,
    binds exactly the pattern holes, and maps them to roots. *)
Definition rw_view_match_assignment_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) view root
    (pattern : rw_pattern K Sort V H) assignment,
    rw_graph_wf sig g ->
    rw_view_agrees g view ->
    In assignment (rw_view_match EK ES EV EH view root pattern) ->
    Map.wf EH assignment /\
    (forall h, (exists c, Map.get EH h assignment = Some c) <-> In h (rwp_holes pattern)) /\
    forall h c, Map.get EH h assignment = Some c ->
      rw_find g c = Some c.

(** View matching returns no duplicate assignments. *)
Definition rw_view_match_nodup_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (view : rw_phase_view K Sort V) root (pattern : rw_pattern K Sort V H),
    NoDup (rw_view_match EK ES EV EH view root pattern).
