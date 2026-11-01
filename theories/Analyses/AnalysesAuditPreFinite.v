(** * Finite PRE objective and bounded correction

    Finite enumeration and counted checks describe supported PRE plans and their costs.
    For example, two expressions produce four ordered sublists.
    Builds on: shared source counters and PRE semantics. *)

From Stdlib Require Import Decimal Arith Bool Lia List NArith PArith.
From Galois.Analyses Require Export AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSsaLiveQuery AnalysesSsaPre
  AnalysesSsaPreGraph AnalysesSsaPreSemantics.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSemantics ViewsSsa ViewsSsaPoints.
Import List.ListNotations.

(* Definition source: PreFiniteBase.v *)

(** * Finite plan support, legality and enumeration *)

(** A version is supported when its expression and any edge occur in the supplied lists. *)
Definition audit_pre_version_supported {E U} (edges : list E) (exprs : list U)
    (v : pre_version E U) : Prop :=
  match v with
  | PreInitial u => In u exprs
  | PreComputed e u | PreInserted e u | PreMerged e u => In e edges /\ In u exprs
  end.

(** A supported plan uses well-formed maps and only the supplied edges and expressions. *)
Definition audit_pre_plan_supported {E U} (EE : encoding E) (EU : encoding U)
    (edges : list E) (exprs : list U) (p : pre_plan E U) : Prop :=
  NoDup edges /\ NoDup exprs /\
  Map.wf EE (pre_insertions p) /\ Map.wf EE (pre_deletions p) /\
  Map.wf EE (pre_reload_versions p) /\
  Map.wf (pair_encoding (pair_encoding EE EE) EU) (pre_phi_versions p) /\
  (forall e row, In (e,row) (Map.elements (pre_insertions p)) ->
    In e edges /\ FinSet.wf EU row /\ forall u, FinSet.mem EU u row = true -> In u exprs) /\
  (forall e row, In (e,row) (Map.elements (pre_deletions p)) ->
    In e edges /\ FinSet.wf EU row /\ forall u, FinSet.mem EU u row = true -> In u exprs) /\
  (forall e version, In (e,version) (Map.elements (pre_reload_versions p)) ->
    In e edges /\ audit_pre_version_supported edges exprs version) /\
  forall parameter incoming u version,
    In (((parameter,incoming),u),version) (Map.elements (pre_phi_versions p)) ->
    In parameter edges /\ In incoming edges /\ In u exprs /\
    audit_pre_version_supported edges exprs version.

Definition audit_pre_static_cost {S O N E U C} (EE : encoding E) (EU : encoding U)
    (v : pre_expression_view S O N E U C) (edges : list E) (exprs : list U)
    (p : pre_plan E U) : nat :=
  fold_right (fun e n =>
    let original :=
      match pre_recomputed v e with
      | Some u => if pre_deleted EE EU p e u then 0 else 1
      | None => 0
      end in
    original + length (filter (fun u => pre_inserted EE EU p e u) exprs) + n) 0 edges.

(** Legality combines placement and local laws with matching initial behaviors
    in both directions. *)
Definition audit_pre_legal {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) : Prop :=
  pre_placement_legal EN EE EU (pre_expression a) p /\
  pre_exit_covered a r /\ pre_phi_source_laws EBE EV a r /\
  pre_local_laws EBE EN EE EV EU a (pre_expression a) (pre_initial_available a) r p /\
  (exists s, initial (pre_source r) s) /\
  (forall s, initial (pre_source r) s -> exists t, initial (pre_target r p) t /\
    same_behaviour (pre_source r) (pre_source_end r) s
      (pre_target r p) (pre_target_end r p) t) /\
  forall t, initial (pre_target r p) t -> exists s, initial (pre_source r) s /\
    same_behaviour (pre_source r) (pre_source_end r) s
      (pre_target r p) (pre_target_end r p) t.

(** A supported legal plan is minimal when every supported legal competitor costs
    at least as much. *)
Definition audit_pre_is_minimal {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (edges : list E) (exprs : list U)
    (p : pre_plan E U) : Prop :=
  audit_pre_plan_supported EE EU edges exprs p /\ audit_pre_legal EBE EN EE EV EU a r p /\
  forall other, audit_pre_plan_supported EE EU edges exprs other ->
    audit_pre_legal EBE EN EE EV EU a r other ->
    audit_pre_static_cost EE EU (pre_expression a) edges exprs p <=
      audit_pre_static_cost EE EU (pre_expression a) edges exprs other.

Section Candidate.

  Context {E U : Type} (EE : encoding E) (EU : encoding U) (edges : list E) (exprs : list U).

  Variable enumerate : list (pre_plan E U).

  (** With unique supports, enumeration contains exactly the supported plans. *)
  Definition audit_pre_enumeration_statement : Prop :=
    NoDup edges -> NoDup exprs -> forall p,
      In p enumerate <-> audit_pre_plan_supported EE EU edges exprs p.

End Candidate.

Definition audit_pre_edge_support {N E} (EE : encoding E) (g : Graph.t N E) : list E :=
  FinSet.elements (FinSet.of_list EE (edges_of g)).

(** Edge support is duplicate free and contains exactly the graph edges. *)
Definition audit_pre_edge_support_statement : Prop :=
  forall N E (EE : encoding E) (g : Graph.t N E),
    NoDup (audit_pre_edge_support EE g) /\
    forall edge, In edge (audit_pre_edge_support EE g) <-> In edge (edges_of g).

Fixpoint audit_pre_sublists {A} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: rest =>
    let suffixes := audit_pre_sublists rest in
      suffixes ++ map (cons x) suffixes
  end.

Fixpoint audit_pre_maps {K A} (EK : encoding K) (keys : list K) (values : list A)
    : list (Map.t K A) :=
  match keys with
  | [] => [Map.empty]
  | k :: rest =>
    let tails := audit_pre_maps EK rest values in
      tails ++ flat_map (fun value => map (Map.set EK k value) tails) values
  end.

Definition audit_pre_versions {E U} (edges : list E) (exprs : list U) : list (pre_version E U) :=
  map PreInitial exprs ++
  flat_map (fun e => flat_map (fun u => [PreComputed e u; PreInserted e u; PreMerged e u]) exprs)
    edges.

Definition audit_pre_phi_keys {E U} (edges : list E) (exprs : list U) : list ((E * E) * U) :=
  flat_map (fun parameter => flat_map (fun incoming =>
    map (fun u => ((parameter,incoming),u)) exprs) edges) edges.

Definition audit_pre_enumerate {E U} (EE : encoding E) (EU : encoding U)
    (edges : list E) (exprs : list U) : list (pre_plan E U) :=
  let rows := map (FinSet.of_list EU) (audit_pre_sublists exprs) in
  let expression_maps := audit_pre_maps EE edges rows in
  let versions := audit_pre_versions edges exprs in
  let reload_maps := audit_pre_maps EE edges versions in
  let phi_maps := audit_pre_maps (pair_encoding (pair_encoding EE EE) EU)
    (audit_pre_phi_keys edges exprs) versions in
  flat_map (fun insertion => flat_map (fun deletion => flat_map (fun reload =>
    map (fun phi => PrePlan insertion deletion reload phi) phi_maps) reload_maps)
    expression_maps) expression_maps.

(** The constructed finite enumeration contains exactly the supported plans on unique supports. *)
Definition audit_pre_enumerate_exact_statement : Prop :=
  forall E U (EE : encoding E) (EU : encoding U) edges exprs,
    audit_pre_enumeration_statement EE EU edges exprs (audit_pre_enumerate EE EU edges exprs).

(** The enumeration length is the product of all finite map choices. *)
Definition audit_pre_enumerate_size_statement : Prop :=
  forall E U (EE : encoding E) (EU : encoding U) edges exprs,
    let m := length edges in
    let k := length exprs in
    let versions := k * (1 + 3 * m) in
    length (audit_pre_enumerate EE EU edges exprs) =
      Nat.pow (1 + Nat.pow 2 k) (2 * m) * Nat.pow (1 + versions) (m + m * m * k).

(** No duplicate supported-key choices remain when the input supports are duplicate free. *)
Definition audit_pre_enumerate_nodup_statement : Prop :=
  forall E U (EE : encoding E) (EU : encoding U) edges exprs,
    NoDup edges -> NoDup exprs -> NoDup (audit_pre_enumerate EE EU edges exprs).

Definition audit_pre_minimum_check {E U S O N C} (EE : encoding E) (EU : encoding U)
    (v : pre_expression_view S O N E U C) (edges : list E) (exprs : list U)
    (chosen : pre_plan E U) (candidates : list (pre_plan E U))
    (accept : pre_plan E U -> bool) : bool :=
  let chosen_cost := audit_pre_static_cost EE EU v edges exprs chosen in
  forallb (fun other => negb (accept other) ||
    Nat.leb chosen_cost (audit_pre_static_cost EE EU v edges exprs other)) candidates.

Definition pre_finite_objective {S O B BE N E V K C U}
    (EBE : encoding BE) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (p : pre_plan E U) : nat :=
  audit_pre_static_cost EE EU (pre_expression a)
    (audit_pre_edge_support EE (cfg (gkview (pre_genkill (pre_expression a)))))
    (pre_expr_universe EBE EV EU a) p.

(** A competitor is legal and supported by the actual graph edges and expression universe. *)
Definition pre_competitor_legal {S O B BE N E NT ET V K C U}
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) : Prop :=
  audit_pre_plan_supported EE EU
    (audit_pre_edge_support EE (cfg (gkview (pre_genkill (pre_expression a)))))
    (pre_expr_universe EBE EV EU a) p /\
  audit_pre_legal EBE EN EE EV EU a r p.

(** Client supplied decision is required only on the explicitly enumerated finite class. *)
Record pre_checker_laws {S O B BE N E NT ET V K C U}
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C)
    (accept : pre_plan E U -> bool) : Prop := {
  (** On enumerated plans, acceptance is equivalent to the stated legality relation. *)
  pre_checker_exact : forall p,
    In p (audit_pre_enumerate EE EU
      (audit_pre_edge_support EE (cfg (gkview (pre_genkill (pre_expression a)))))
      (pre_expr_universe EBE EV EU a)) ->
    (accept p = true <-> audit_pre_legal EBE EN EE EV EU a r p)
}.

(** For a lawful, ready input and a lawful accepting checker, acceptance and the
    finite minimum test imply that the chosen placement is a legal optimum. *)
Definition pre_objective_evidence : Prop :=
  forall S O B BE N E NT ET V K C U
      (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
      (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
      (r : pre_realizer S O N E NT ET U C) (accept : pre_plan E U -> bool),
    let edges := audit_pre_edge_support EE (cfg (gkview (pre_genkill (pre_expression a)))) in
    let exprs := pre_expr_universe EBE EV EU a in
    let candidates := audit_pre_enumerate EE EU edges exprs in
    let chosen := ssa_pre_place EB EBE EN EE EV EU a in
    pre_expr_ssa_laws EV a ->
    ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
    ready EN (live_graph (point_model (pre_ssa_points a)))
      (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
    pre_checker_laws EBE EN EE EV EU a r accept -> accept chosen = true ->
    audit_pre_minimum_check EE EU (pre_expression a) edges exprs chosen candidates accept = true ->
    pre_competitor_legal EBE EN EE EV EU a r chosen /\
    forall other, pre_competitor_legal EBE EN EE EV EU a r other ->
      pre_finite_objective EBE EE EV EU a chosen <= pre_finite_objective EBE EE EV EU a other.

Fixpoint audit_pre_choose_best {X : Type} (accept : X -> bool) (cost : X -> nat)
    (candidates : list X) : option X :=
  match candidates with
  | [] => None
  | candidate :: rest =>
    let best := audit_pre_choose_best accept cost rest in
    if accept candidate then
      match best with
      | None => Some candidate
      | Some other => if Nat.leb (cost candidate) (cost other) then Some candidate else Some other
      end
    else best
  end.

(** An accepted candidate yields an accepted member no more costly than every accepted member. *)
Definition audit_pre_choose_best_statement : Prop :=
  forall X (accept : X -> bool) (cost : X -> nat) candidates,
    (exists candidate, In candidate candidates /\ accept candidate = true) ->
    exists best, audit_pre_choose_best accept cost candidates = Some best /\
      In best candidates /\ accept best = true /\
      forall other, In other candidates -> accept other = true -> cost best <= cost other.

(** A legal competitor and an exact finite checker yield a legal minimum from the enumeration. *)
Definition audit_pre_bounded_correction_statement : Prop :=
  forall S O B BE N E NT ET V K C U
      (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
      (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C)
      (accept : pre_plan E U -> bool),
    let edges := audit_pre_edge_support EE (cfg (gkview (pre_genkill (pre_expression a)))) in
    let exprs := pre_expr_universe EBE EV EU a in
    let candidates := audit_pre_enumerate EE EU edges exprs in
    pre_checker_laws EBE EN EE EV EU a r accept ->
    (exists p, pre_competitor_legal EBE EN EE EV EU a r p) ->
    exists best, audit_pre_choose_best accept (pre_finite_objective EBE EE EV EU a) candidates =
      Some best /\
      pre_competitor_legal EBE EN EE EV EU a r best /\
      forall other, pre_competitor_legal EBE EN EE EV EU a r other ->
        pre_finite_objective EBE EE EV EU a best <= pre_finite_objective EBE EE EV EU a other.

(* Definition source: PreFiniteCost.v *)
(** * Exact finite PRE competitor enumeration and strict objective/check source models

    Card: AUD-SP. Acceptance is the genuine supplied finite checker, never an assumed optimum.
    Both strict disjunction operands and every subsequent candidate execute after rejection. *)
Fixpoint pre_sublists_counted {Call A} (xs : list A) : exact_counted Call (list (list A)) :=
  match xs with
  | [] => exact_case 1900 (exact_return 1900 [[]])
  | x :: rest =>
    exact_case 1901 (exact_bind 1902 (pre_sublists_counted rest) (fun tails =>
      exact_bind 1903 (exact_map 1903 (fun tail => exact_return 1903 (x :: tail)) tails)
        (fun with_head => exact_append 1904 tails with_head))) end.

Fixpoint pre_maps_counted {Call K A} (inject : exact_map_call K A -> Call)
    (EK : encoding K) (body : K -> nat) (keys : list K) (values : list A)
    : exact_counted Call (list (Map.t K A)) :=
  match keys with
  | [] => exact_case 1910 (exact_return 1910 [Map.empty])
  | key :: rest =>
    exact_case 1911
      (exact_bind 1912 (pre_maps_counted inject EK body rest values) (fun tails =>
      exact_bind 1913 (exact_flat_map 1913 (fun value =>
        exact_map 1914 (exact_set inject EK body key value) tails) values)
        (fun present => exact_append 1915 tails present))) end.

Inductive pre_finite_call (E U : Type) : Type :=
  | PfcRows (call : exact_map_call E (FinSet.t U))
  | PfcExprs (call : exact_map_call U unit)
  | PfcReload (call : exact_map_call E (pre_version E U))
  | PfcPhi (call : exact_map_call ((E * E) * U) (pre_version E U))
  | PfcRecomputed (edge : E) (result : option U)
  | PfcAccept (plan : pre_plan E U) (result : bool)
  | PfcNatAdd (first second result : nat)
  | PfcNatLe (first second : nat) (result : bool).

Arguments PfcRows {E U}.

Arguments PfcExprs {E U}.

Arguments PfcReload {E U}.

Arguments PfcPhi {E U}.

Arguments PfcRecomputed {E U}.

Arguments PfcAccept {E U}.

Arguments PfcNatAdd {E U}.

Arguments PfcNatLe {E U}.

Section Finite.

Context {E U : Type} (EE : encoding E) (EU : encoding U)
  (edge_body : E -> nat) (expr_body : U -> nat) (edges : list E) (exprs : list U).

(** Finite enumeration and checking share this call type. *)
Let Call := pre_finite_call E U.

Definition pre_finite_phi_body (key : (E * E) * U) :=
  128 + edge_body (fst (fst key)) + edge_body (snd (fst key)) + expr_body (snd key) +
    64 * Pos.size_nat (encode (pair_encoding (pair_encoding EE EE) EU) key).

Fixpoint pre_finite_length_counted {X} (xs : list X) : exact_counted Call nat :=
  match xs with
  | [] => exact_case 1920 (exact_return 1920 0)
  | _ :: rest =>
    exact_case 1921 (exact_bind 1921 (pre_finite_length_counted rest)
      (fun n => exact_return 1921 (S n))) end.

Definition pre_finite_add_counted x y : exact_counted Call nat :=
  let result := Nat.add x y in exact_call (PfcNatAdd x y result)
    (64 * audit_unary_conversion_weight x) result.

Definition pre_finite_le_counted x y : exact_counted Call bool :=
  let result := Nat.leb x y in exact_call (PfcNatLe x y result)
    (64 * (audit_unary_conversion_weight x + audit_unary_conversion_weight y)) result.

Definition pre_finite_versions_counted : exact_counted Call (list (pre_version E U)) :=
  exact_bind 1930 (exact_map 1930 (fun u => exact_return 1930 (PreInitial u)) exprs) (fun initial =>
  exact_bind 1931 (exact_flat_map 1931 (fun e => exact_flat_map 1932
    (fun u => exact_return 1932 [PreComputed e u;PreInserted e u;PreMerged e u]) exprs) edges)
      (fun other => exact_append 1933 initial other)).

Definition pre_finite_phi_keys_counted : exact_counted Call (list ((E * E) * U)) :=
  exact_flat_map 1934 (fun parameter => exact_flat_map 1935 (fun incoming =>
    exact_map 1936 (fun u => exact_return 1936 ((parameter,incoming),u)) exprs) edges) edges.

Definition pre_enumerate_counted : exact_counted Call (list (pre_plan E U)) :=
  exact_bind 1940 (pre_sublists_counted exprs) (fun sublists =>
  exact_bind 1941 (exact_map 1941 (exact_set_of_list PfcExprs EU expr_body) sublists) (fun rows =>
  exact_bind 1942 (pre_maps_counted PfcRows EE edge_body edges rows) (fun expression_maps =>
  exact_bind 1943 pre_finite_versions_counted (fun versions =>
  exact_bind 1944 (pre_maps_counted PfcReload EE edge_body edges versions) (fun reload_maps =>
  exact_bind 1945 pre_finite_phi_keys_counted (fun phi_keys =>
  exact_bind 1946 (pre_maps_counted PfcPhi (pair_encoding (pair_encoding EE EE) EU)
    pre_finite_phi_body phi_keys versions) (fun phi_maps =>
    exact_flat_map 1947 (fun insertion => exact_flat_map 1948 (fun deletion =>
      exact_flat_map 1949 (fun reload => exact_map 1950
        (fun phi => exact_return 1950 (PrePlan insertion deletion reload phi)) phi_maps)
          reload_maps) expression_maps) expression_maps))))))).

Definition pre_row_contains_counted (rows : Map.t E (FinSet.t U)) e u
    : exact_counted Call bool :=
  exact_bind 1951 (exact_get PfcRows EE edge_body e rows) (fun found =>
    match found with
    | None => exact_case 1952 (exact_return 1952 false)
    | Some set => exact_case 1953 (exact_set_mem PfcExprs EU expr_body u set) end).

Definition pre_static_cost_counted {S O N C} (view : pre_expression_view S O N E U C)
    (plan : pre_plan E U) : exact_counted Call nat :=
  exact_fold_right 1960 (fun e total =>
    let computed := pre_recomputed view e in
    exact_bind 1961 (exact_call (PfcRecomputed e computed) 0 computed) (fun computed =>
    exact_bind 1962 (
      match computed with
      | None => exact_case 1962 (exact_return 1962 0)
      | Some u =>
        exact_case 1963 (exact_bind 1963
          (pre_row_contains_counted (pre_deletions plan) e u)
          (fun deleted => exact_return 1964 (if deleted then 0 else 1))) end) (fun original =>
    exact_bind 1965 (exact_filter 1965 (pre_row_contains_counted (pre_insertions plan) e) exprs)
      (fun inserted =>
    exact_bind 1966 (pre_finite_length_counted inserted) (fun count =>
    exact_bind 1967 (pre_finite_add_counted original count)
      (fun here => pre_finite_add_counted here total)))))) 0 edges.

Definition pre_minimum_check_counted {S O N C} (view : pre_expression_view S O N E U C)
    (chosen : pre_plan E U) (candidates : list (pre_plan E U)) (accept : pre_plan E U -> bool)
    : exact_counted Call bool :=
  exact_bind 1970 (pre_static_cost_counted view chosen) (fun chosen_cost =>
    exact_all 1971 (fun other => let accepted := accept other in
      exact_bind 1972 (exact_call (PfcAccept other accepted) 0 accepted) (fun accepted =>
      exact_bind 1973 (pre_static_cost_counted view other) (fun other_cost =>
      exact_bind 1974 (pre_finite_le_counted chosen_cost other_cost)
        (fun minimum => exact_return 1975 (negb accepted || minimum))))) candidates).

Fixpoint pre_choose_best_counted {S O N C} (view : pre_expression_view S O N E U C)
    (accept : pre_plan E U -> bool) (candidates : list (pre_plan E U))
    : exact_counted Call (option (pre_plan E U)) :=
  match candidates with
  | [] => exact_case 1980 (exact_return 1980 None)
  | candidate :: rest =>
    exact_case 1981
      (exact_bind 1982 (pre_choose_best_counted view accept rest) (fun best =>
      let accepted := accept candidate in
      exact_bind 1983 (exact_call (PfcAccept candidate accepted) 0 accepted) (fun accepted =>
      if accepted then exact_case 1984 (
        match best with
        | None => exact_case 1985 (exact_return 1985 (Some candidate))
        | Some other =>
          exact_case 1986
            (exact_bind 1987 (pre_static_cost_counted view candidate) (fun here =>
            exact_bind 1988 (pre_static_cost_counted view other) (fun there =>
            exact_bind 1989 (pre_finite_le_counted here there)
              (fun lower => exact_return 1990 (Some (if lower then candidate else other)))))) end)
      else exact_case 1991 (exact_return 1991 best)))) end.

Definition pre_finite_geometry :=
  let m := length edges in let k := length exprs in let versions := k * (1 + 3 * m) in
  1 + m + k + Nat.pow 2 k + versions + m * m * k +
    Nat.pow (1 + Nat.pow 2 k) (2 * m) * Nat.pow (1 + versions) (m + m * m * k).

Definition pre_finite_operand_max :=
  fold_right Nat.max 0 (map (fun e => edge_body e + Pos.size_nat (encode EE e)) edges) +
  fold_right Nat.max 0 (map (fun u => expr_body u + Pos.size_nat (encode EU u)) exprs).

Definition pre_enumerate_input_budget : nat :=
  (Nat.of_num_uint 16777216%uint) * Nat.pow pre_finite_geometry 8 *
    Nat.pow (S pre_finite_operand_max) 6.

Definition pre_minimum_input_budget (candidate_count : nat) : nat :=
  (Nat.of_num_uint 1048576%uint) * Nat.pow (1 + length edges + length exprs + candidate_count) 8 *
    Nat.pow (S pre_finite_operand_max) 6.

(** Counted enumeration, cost, minimum check and choice erase and meet their stated budgets. *)
Definition audit_pre_finite_source_statement : Prop :=
  exact_value pre_enumerate_counted = audit_pre_enumerate EE EU edges exprs /\
  exact_units pre_enumerate_counted <= pre_enumerate_input_budget /\
  forall S O N C (view : pre_expression_view S O N E U C) chosen candidates accept,
    exact_value (pre_static_cost_counted view chosen) = audit_pre_static_cost EE EU view edges exprs
      chosen /\
    exact_value (pre_minimum_check_counted view chosen candidates accept) =
      audit_pre_minimum_check EE EU view edges exprs chosen candidates accept /\
    exact_units (pre_minimum_check_counted view chosen candidates accept) <=
      pre_minimum_input_budget (length candidates) /\
    exact_value (pre_choose_best_counted view accept candidates) =
      audit_pre_choose_best accept (audit_pre_static_cost EE EU view edges exprs) candidates /\
    exact_units (pre_choose_best_counted view accept candidates) <=
      pre_minimum_input_budget (length candidates).

End Finite.

(** The finite objective theorem retains the exact legality and minimum-check premises. *)
Definition audit_pre_objective_evidence_statement : Prop := pre_objective_evidence.
