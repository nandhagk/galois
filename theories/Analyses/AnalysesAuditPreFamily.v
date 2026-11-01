(** * Finite PRE family and binary arithmetic

    Counted arithmetic and discovery retain the inputs and results of PRE family construction.
    For example, incrementing a binary positive records its carry work.
    Builds on: shared source counters and expression SSA. *)

From Stdlib Require Import Decimal Arith Bool List NArith PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesSsaPreGraph.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
Import List.ListNotations.

(* Definition source: PreArithmetic.v *)
(** * PRE's library-owned arithmetic leaf bridge

    Card: AUD-SP. Fixed branch/constructor source units are used at arithmetic leaves; this
    is not a native or kernel-step measure. These equations follow the pinned Stdlib bodies.
    N.pow iteration is expanded in PreFamily, not hidden below one arithmetic call. *)

Fixpoint pre_positive_succ_body x : positive * nat :=
  match x with
  | xH => (xO xH,2)
  | xO p => (xI p,2)
  | xI p => let '(out,work) := pre_positive_succ_body p in (xO out,2+work) end.

(** The mutually recursive mirrors add positives without and with an incoming carry. *)
Fixpoint pre_positive_add_body (x y : positive) {struct x} : positive * nat :=
  match x with
  | xI p =>
    match y with
    | xI q => let '(out,work) := pre_positive_carry_body p q in (xO out,2+work)
    | xO q => let '(out,work) := pre_positive_add_body p q in (xI out,2+work)
    | xH => let '(out,work) := pre_positive_succ_body p in (xO out,2+work) end
  | xO p =>
    match y with
    | xI q => let '(out,work) := pre_positive_add_body p q in (xI out,2+work)
    | xO q => let '(out,work) := pre_positive_add_body p q in (xO out,2+work)
    | xH => (xI p,2) end
  | xH =>
    match y with
    | xI q => let '(out,work) := pre_positive_succ_body q in (xO out,2+work)
    | xO q => (xI q,2)
    | xH => (xO xH,2) end end
with pre_positive_carry_body (x y : positive) {struct x} : positive * nat :=
  match x with
  | xI p =>
    match y with
    | xI q => let '(out,work) := pre_positive_carry_body p q in (xI out,2+work)
    | xO q => let '(out,work) := pre_positive_carry_body p q in (xO out,2+work)
    | xH => let '(out,work) := pre_positive_succ_body p in (xI out,2+work) end
  | xO p =>
    match y with
    | xI q => let '(out,work) := pre_positive_carry_body p q in (xO out,2+work)
    | xO q => let '(out,work) := pre_positive_add_body p q in (xI out,2+work)
    | xH => let '(out,work) := pre_positive_succ_body p in (xO out,2+work) end
  | xH =>
    match y with
    | xI q => let '(out,work) := pre_positive_succ_body q in (xI out,2+work)
    | xO q => let '(out,work) := pre_positive_succ_body q in (xO out,2+work)
    | xH => (xI xH,2) end end.

Fixpoint pre_positive_mul_body (x y : positive) : positive * nat :=
  match x with
  | xH => (y,1)
  | xO p => let '(out,work) := pre_positive_mul_body p y in (xO out,2+work)
  | xI p =>
    let '(middle,first) := pre_positive_mul_body p y in
    let '(out,second) := pre_positive_add_body y (xO middle) in (out,2+first+second) end.

Definition pre_nadd_body x y : N * nat :=
  match x with
  | N0 => (y,1)
  | Npos p =>
    match y with
    | N0 => (x,2)
    | Npos q => let '(out,work) := pre_positive_add_body p q in (Npos out,3+work) end end.

Definition pre_nmul_body x y : N * nat :=
  match x with
  | N0 => (N0,1)
  | Npos p =>
    match y with
    | N0 => (N0,2)
    | Npos q => let '(out,work) := pre_positive_mul_body p q in (Npos out,3+work) end end.

Definition pre_nofnat_body n : N * nat :=
  match n with
  | O => (N0,1)
  | S previous =>
    let '(out,events) := audit_nat_encode previous in (Npos out,2+2*length events) end.

Definition pre_nsucc_body n : positive * nat :=
  match n with
  | N0 => (xH,1)
  | Npos p => let '(out,work) := pre_positive_succ_body p in (out,1+work) end.

(** Each arithmetic mirror returns the corresponding Stdlib result within its fixed charge. *)
Definition audit_pre_arithmetic_implementation_adequacy_statement : Prop :=
  (forall x, fst (pre_positive_succ_body x) = Pos.succ x /\
    snd (pre_positive_succ_body x) <= 8 * audit_binary_weight (Z.pos x) 1) /\
  (forall x y, fst (pre_positive_add_body x y) = Pos.add x y /\
    fst (pre_positive_carry_body x y) = Pos.add_carry x y /\
    snd (pre_positive_add_body x y) <= 8 * audit_binary_weight (Z.pos x) (Z.pos y) /\
    snd (pre_positive_carry_body x y) <= 8 * audit_binary_weight (Z.pos x) (Z.pos y)) /\
  (forall x y, fst (pre_positive_mul_body x y) = Pos.mul x y /\
    snd (pre_positive_mul_body x y) <= 8 * audit_multiply_weight (Z.pos x) (Z.pos y)) /\
  (forall x y, fst (pre_nadd_body x y) = N.add x y /\
    snd (pre_nadd_body x y) <= 8 * audit_binary_weight (Z.of_N x) (Z.of_N y) /\
    fst (pre_nmul_body x y) = N.mul x y /\
    snd (pre_nmul_body x y) <= 8 * audit_multiply_weight (Z.of_N x) (Z.of_N y)) /\
  (forall n, fst (pre_nofnat_body n) = N.of_nat n /\
    snd (pre_nofnat_body n) <= 64 * audit_unary_conversion_weight n *
      S (audit_z_bits (Z.of_N (N.of_nat n)))) /\
  (forall n, fst (pre_nsucc_body n) = N.succ_pos n /\
    snd (pre_nsucc_body n) <= 8 * audit_binary_weight (Z.of_N n) 1).

(* Definition source: PreFamily.v *)
(** * Literal memoized PRE expression-family discovery

    Card: AUD-SP. Exponentiation follows the pinned Pos.iter multiplication implementation;
    discovery preserves pending/seen states and stops at the actual empty pending list. *)
Inductive pre_family_call (B BE V U : Type) : Type :=
  | PreFamilyExpr (call : exact_map_call U unit)
  | PreFamilyEdges (call : exact_map_call BE unit)
  | PreFamilyOut (block : B) (result : list BE)
  | PreFamilyOperands (expr : U) (result : list V)
  | PreFamilyTranslate (edge : BE) (expr : U) (result : option U)
  | PreFamilyOfNat (input : nat) (result : N)
  | PreFamilyMul (first second result : positive)
  | PreFamilyNMul (first second result : N)
  | PreFamilyAdd (first second result : N)
  | PreFamilySucc (input : N) (result : positive).

Arguments PreFamilyExpr {B BE V U}.

Arguments PreFamilyEdges {B BE V U}.

Arguments PreFamilyOut {B BE V U}.

Arguments PreFamilyOperands {B BE V U}.

Arguments PreFamilyTranslate {B BE V U}.

Arguments PreFamilyOfNat {B BE V U}.

Arguments PreFamilyMul {B BE V U}.

Arguments PreFamilyNMul {B BE V U}.

Arguments PreFamilyAdd {B BE V U}.

Arguments PreFamilySucc {B BE V U}.

Section Family.

Context {S O B BE N E V K C U : Type} (EBE : encoding BE) (EU : encoding U)
  (a : pre_expr_ssa S O B BE N E V K C U) (edge_body : BE -> nat) (expr_body : U -> nat).

(** Family discovery records these calls in its counted trace. *)
Let Call := pre_family_call B BE V U.

Fixpoint pre_length_counted {X} (xs : list X) : exact_counted Call nat :=
  match xs with
  | [] => exact_case 1200 (exact_return 1200 0)
  | _ :: rest =>
    exact_case 1201 (exact_bind 1201 (pre_length_counted rest)
      (fun n => exact_return 1201 (Datatypes.S n))) end.

Definition pre_of_nat_counted n : exact_counted Call BinNums.N :=
  let result := N.of_nat n in
  exact_call (PreFamilyOfNat n result)
    (64 * audit_unary_conversion_weight n * Datatypes.S (audit_z_bits (Z.of_N result))) result.

Definition pre_nadd_counted x y : exact_counted Call BinNums.N :=
  let result := N.add x y in
  exact_call (PreFamilyAdd x y result) (8 * audit_binary_weight (Z.of_N x) (Z.of_N y)) result.

Fixpoint pre_positive_power_counted (base fuel current : positive) {struct fuel}
    : exact_counted Call positive :=
  let step value := let result := Pos.mul base value in
    exact_call (PreFamilyMul base value result)
      (8 * audit_multiply_weight (Z.pos base) (Z.pos value)) result in
  match fuel with
  | xH => exact_case 1202 (step current)
  | xO p =>
    exact_case 1203 (exact_bind 1203 (pre_positive_power_counted base p current)
      (pre_positive_power_counted base p))
  | xI p =>
    exact_case 1204 (exact_bind 1204 (pre_positive_power_counted base p current)
      (fun middle => exact_bind 1204 (pre_positive_power_counted base p middle) step)) end.

Definition pre_npower_counted base exponent : exact_counted Call BinNums.N :=
  match exponent with
  | N0 => exact_case 1205 (exact_return 1205 1%N)
  | Npos fuel =>
    match base with
    | N0 => exact_case 1206 (exact_return 1206 0%N)
    | Npos value =>
      exact_case 1207 (exact_bind 1207
        (pre_positive_power_counted value fuel xH) (fun result => exact_return 1207 (Npos result)))
          end
  end.

Definition pre_family_bound_counted : exact_counted Call BinNums.N :=
  exact_bind 1210 (pre_length_counted (pre_value_universe a)) (fun count =>
  exact_bind 1211 (pre_of_nat_counted count) (fun values =>
    exact_fold_right 1212 (fun u total =>
      let operands := pre_operands a u in
      exact_bind 1213 (exact_call (PreFamilyOperands u operands) 0 operands) (fun operands =>
      exact_bind 1214 (pre_length_counted operands) (fun count =>
      exact_bind 1215 (pre_of_nat_counted count) (fun arity =>
      exact_bind 1216 (pre_npower_counted values arity) (fun power => pre_nadd_counted power
        total)))))
      0%N (pre_seed_expressions a))).

Definition pre_family_edges_counted : exact_counted Call (list BE) :=
  exact_flat_map 1220 (fun block =>
    let edges := Graph.out (block_graph (pre_ssa_points a)) block in
    exact_call (PreFamilyOut block edges) 0 edges) (Graph.nodes (block_graph (pre_ssa_points a))).

Definition pre_translated_counted (bes : list BE) (u : U) : exact_counted Call (list U) :=
  exact_flat_map 1221 (fun be =>
    let translated := pre_phi_translate a be u in
    exact_bind 1222 (exact_call (PreFamilyTranslate be u translated) 0 translated) (fun translated
      =>
      match translated with
      | None => exact_case 1223 (exact_return 1223 [])
      | Some result => exact_case 1224 (exact_return 1224 [result]) end)) bes.

Definition pre_discover_step_counted (bes : list BE) (work : list U * FinSet.t U)
    : exact_counted Call (list U * FinSet.t U) :=
  let '(pending,seen) := work in
  match pending with
  | [] => exact_case 1230 (exact_return 1230 work)
  | u :: rest =>
    exact_case 1231
      (exact_bind 1232 (exact_set_mem PreFamilyExpr EU expr_body u seen) (fun present =>
      if present then exact_case 1233 (exact_return 1233 (rest,seen))
      else exact_case 1234
        (exact_bind 1235 (pre_translated_counted bes u) (fun next =>
        exact_bind 1236 (exact_append 1236 next rest) (fun pending =>
        exact_bind 1237 (exact_set PreFamilyExpr EU expr_body u tt seen)
          (fun seen => exact_return 1238 (pending,seen))))))) end.

Fixpoint pre_discover_run_counted (bes : list BE) (fuel : positive) (work : list U * FinSet.t U)
    : exact_counted Call (list U * FinSet.t U) :=
  match fst work with
  | [] => exact_case 1240 (exact_return 1240 work)
  | _ :: _ =>
    match fuel with
    | xH => exact_case 1241 (pre_discover_step_counted bes work)
    | xO p =>
      exact_case 1242 (exact_bind 1242 (pre_discover_run_counted bes p work)
        (pre_discover_run_counted bes p))
    | xI p =>
      exact_case 1243 (exact_bind 1243 (pre_discover_run_counted bes p work)
        (fun first => exact_bind 1243 (pre_discover_run_counted bes p first)
          (pre_discover_step_counted bes))) end end.

Definition pre_expr_universe_counted : exact_counted Call (list U) :=
  exact_bind 1250 pre_family_edges_counted (fun edges =>
  exact_bind 1251 (exact_set_of_list PreFamilyEdges EBE edge_body edges) (fun set =>
  exact_bind 1252 (exact_set_elements PreFamilyEdges set) (fun bes =>
  exact_bind 1253 (pre_length_counted (pre_seed_expressions a)) (fun count =>
  exact_bind 1254 (pre_of_nat_counted count) (fun seed_count =>
  exact_bind 1255 pre_family_bound_counted (fun family_bound =>
  exact_bind 1256 (pre_length_counted bes) (fun count =>
  exact_bind 1257 (pre_of_nat_counted count) (fun edge_count =>
  exact_bind 1258 (pre_nadd_counted 1%N edge_count) (fun edge_bound =>
  let product := N.mul family_bound edge_bound in
  exact_bind 1259 (exact_call
    (PreFamilyNMul family_bound edge_bound product)
    (8 * audit_multiply_weight (Z.of_N family_bound) (Z.of_N edge_bound)) product) (fun product =>
  exact_bind 1260 (pre_nadd_counted seed_count product) (fun bound =>
  let fuel := N.succ_pos bound in
  exact_bind 1261 (exact_call (PreFamilySucc bound fuel)
    (8 * audit_binary_weight (Z.of_N bound) 1) fuel) (fun fuel =>
  exact_bind 1262 (pre_discover_run_counted bes fuel (pre_seed_expressions a,FinSet.empty))
    (fun work => exact_set_elements PreFamilyExpr (snd work)))))))))))))).

(** Erasing discovery counters recovers binary powers, the family bound and the
    discovered universe. *)
Definition pre_discover_counted_erases_statement : Prop :=
  (forall base exponent, exact_value (pre_npower_counted base exponent) = N.pow base exponent) /\
  exact_value pre_family_bound_counted = AnalysesSsaPreGraph.pre_family_bound a /\
  (forall bes fuel work, exact_value (pre_discover_run_counted bes fuel work) =
    AnalysesSsaPreGraph.pre_discover_run EU (AnalysesSsaPreGraph.pre_translated a bes) fuel work) /\
  (forall EV : encoding V,
    exact_value pre_expr_universe_counted = pre_expr_universe EBE EV EU a).

(** Input-only observer: old pure value computations determine operand support and fuel;
    this is not the work projection or trace of the counted producer. Evaluating this
    mathematical observer is not claimed free or bounded by this represented-source bound. *)
Definition pre_family_input_budget (EV : encoding V) : nat :=
  let edges := edges_of (block_graph (pre_ssa_points a)) in
  let bes := FinSet.elements (FinSet.of_list EBE edges) in
  let family := pre_expr_universe EBE EV EU a in
  let raw_bound := (N.of_nat (length (pre_seed_expressions a)) +
    AnalysesSsaPreGraph.pre_family_bound a * (1 + N.of_nat (length bes)))%N in
  let fuel := Pos.to_nat (N.succ_pos raw_bound) in
  let expression_width := fold_right Nat.max 0
    (map (fun u => expr_body u + Pos.size_nat (encode EU u)) (pre_seed_expressions a ++ family)) in
  let edge_width := fold_right Nat.max 0
    (map (fun be => edge_body be + Pos.size_nat (encode EBE be)) edges) in
  let arities := fold_right (fun u n => length (pre_operands a u) + n) 0 (pre_seed_expressions a) in
  (Nat.of_num_uint 16777216%uint) * Nat.pow
    (1 + fuel + length edges + length (pre_seed_expressions a) +
    length (pre_value_universe a) + arities) 6 *
    Nat.pow (1 + expression_width + edge_width + audit_z_bits (Z.of_N raw_bound)) 6.

(** The family run erases to the original discovery and fits its input-only budget. *)
Definition audit_pre_family_full_source_statement : Prop :=
  audit_pre_arithmetic_implementation_adequacy_statement /\
  audit_pre_map_implementation_adequacy_statement /\ pre_discover_counted_erases_statement /\
  forall EV : encoding V, exact_units pre_expr_universe_counted <= pre_family_input_budget EV.

End Family.
