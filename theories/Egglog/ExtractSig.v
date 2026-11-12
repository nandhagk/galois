(** * Checked extraction of represented expressions

    Extraction chooses finite constructor witnesses and checks their DAG certificates.
    For example, a class containing a literal constructor can have a one-node certificate.
    Builds on: ValueSig, IndexSig, DatabaseSig and Model. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Std Loop.
From Galois.Egglog Require Import ValueSig IndexSig DatabaseSig Syntax Model.

Import List.ListNotations.

Definition extraction_row (V : Type) := (positive * list (cell V))%type.
Definition extraction_dag (V : Type) := list (positive * extraction_row V).
Definition extraction_best (V : Type) := list (positive * (N * extraction_row V)).

(** Tree cost applies constructor costs recursively and literal costs at leaves. *)
Fixpoint expression_cost {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (e : @Model.expr V) : N :=
  match e with
  | Model.ELit v => val_cost v
  | Model.EApp f es => fn_cost f (map (expression_cost fn_cost val_cost) es)
  end.
TimeFun expression_cost.

(** Missing identifiers have provisional cost zero before they enter the chosen table. *)
Fixpoint chosen_cost {V} (val_cost : V -> N) (best : extraction_best V)
    (c : cell V) : N :=
  match c with
  | Val v => val_cost v
  | Id i =>
    match best with
    | [] => 0%N
    | (j, (n, _)) :: rest =>
      if Pos.eqb i j then n else chosen_cost val_cost rest c
    end
  end.
TimeFun chosen_cost.

(** A DAG entry unfolds through earlier entries, so its witness is finite. *)
Inductive dag_represents {V} : extraction_dag V -> positive -> @Model.expr V -> Prop :=
  | dag_here pre c f k es :
      dag_cells pre k es ->
      dag_represents (pre ++ [(c, (f, k))]) c (Model.EApp f es)
  | dag_later pre c e entry : dag_represents pre c e ->
      dag_represents (pre ++ [entry]) c e
with dag_cells {V} : extraction_dag V -> list (cell V) -> list (@Model.expr V) -> Prop :=
  | dag_cells_nil g : dag_cells g [] []
  | dag_cells_val g v cs es : dag_cells g cs es ->
      dag_cells g (Val v :: cs) (Model.ELit v :: es)
  | dag_cells_id g i e cs es : dag_represents g i e -> dag_cells g cs es ->
      dag_cells g (Id i :: cs) (e :: es).

Module Type COST_OPS (V : VALUE_OPS).
  Parameter fn_cost : positive -> list N -> N.
  Parameter val_cost : V.t -> N.
End COST_OPS.

Module Type COST_LAWS (V : VALUE) (Import C : COST_OPS V).
  (** Increasing child costs cannot decrease the constructor cost. *)
  Parameter fn_cost_mono : forall f cs ds, Forall2 N.le cs ds ->
    (fn_cost f cs <= fn_cost f ds)%N.
  (** Each child costs at most its enclosing constructor. *)
  Parameter fn_cost_super : forall f cs c, In c cs -> (c <= fn_cost f cs)%N.
End COST_LAWS.

Module Type COST (V : VALUE) := COST_OPS V <+ COST_LAWS V.

Module Type COST_TIME (V : VALUE_T) (Import C : COST V).
  Parameter T_fn_cost : positive -> list N -> N.
  Parameter T_val_cost : V.t -> N.
  Parameter c_cost : N.
  (** Constructor costing pays for its child costs and their binary encodings. *)
  Parameter T_fn_cost_le : forall f cs,
    (T_fn_cost f cs <= c_cost * N.of_nat (length cs + 1) *
      N.of_nat (fold_right (fun c w => Nat.max (N.size_nat c) w) 0%nat cs + 1))%N.
  (** Literal costing pays for the encoded literal. *)
  Parameter T_val_cost_le : forall v,
    (T_val_cost v <= c_cost * N.of_nat (V.bits v + 1))%N.
End COST_TIME.

Module Type COST_T (V : VALUE_T) := COST V <+ COST_TIME V.

Module Type EXTRACT_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V).
  Parameter best : D.t -> extraction_best V.t.
  Parameter extract : D.t -> positive -> option (extraction_dag V.t).
  Parameter check_dag : D.t -> positive -> extraction_dag V.t -> option N.
End EXTRACT_OPS.

Module Type EXTRACT_SPEC (V : VALUE) (I : INDEX V) (D : DATABASE V I)
    (C : COST V) (Import X : EXTRACT_OPS V I D C).
  Definition tree_cost := expression_cost C.fn_cost C.val_cost.
  Definition cost_of := chosen_cost C.val_cost.
  Definition dag_valid (w : Model.view (V := V.t)) (c : positive)
      (g : extraction_dag V.t) : Prop :=
    NoDup (map fst g) /\
    (forall pre i f k post, g = pre ++ (i, (f, k)) :: post ->
      forall child, In (Id child) k -> In child (map fst pre)) /\
    Forall (fun entry => row w (fst (snd entry)) (snd (snd entry))
      (Some (Id (fst entry)))) g /\
    exists e, dag_represents g c e.
End EXTRACT_SPEC.

Module Type EXTRACT_LAWS (V : VALUE) (I : INDEX V) (D : DATABASE V I)
    (C : COST V) (Import X : EXTRACT_OPS V I D C)
    (Import XS : EXTRACT_SPEC V I D C X).
  (* spec: dag_cost unfold *)
  Parameter dag_cost : extraction_dag V.t -> N.
  Parameter unfold : extraction_dag V.t -> positive -> option (@Model.expr V.t).
  (** Successful unfolding agrees with finite prefix unfolding. *)
  Parameter unfold_spec : forall g c e, NoDup (map fst g) ->
    (unfold g c = Some e <-> dag_represents g c e).
  (** A chosen row belongs to its class and has its computed constructor cost. *)
  Parameter best_row : forall db c n f k, D.wf db -> D.canonical db ->
    In (c, (n, (f, k))) (best db) ->
    row (D.view db) f k (Some (Id c)) /\
      n = C.fn_cost f (map (cost_of (best db)) k).
  (** Every represented tree bounds the chosen class cost. *)
  Parameter best_optimal : forall db c e, D.wf db -> D.canonical db ->
    represents (D.view db) (Id c) e ->
    exists n ch, In (c, (n, ch)) (best db) /\ (n <= tree_cost e)%N.
  (** Every chosen cost is attained by a finite represented tree. *)
  Parameter best_attained : forall db c n ch, D.wf db -> D.canonical db ->
    In (c, (n, ch)) (best db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  (** Accepted certificates unfold to represented trees and report their DAG cost. *)
  Parameter check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\ n = dag_cost g /\
    exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e.
  (** Extraction returns a checked certificate bounded by the chosen tree cost. *)
  Parameter extract_checked : forall db c g, D.wf db -> D.canonical db ->
    extract db c = Some g -> exists n m ch,
      check_dag db c g = Some n /\ In (c, (m, ch)) (best db) /\ (n <= m)%N.
End EXTRACT_LAWS.

Module Type EXTRACT (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V) :=
  EXTRACT_OPS V I D C <+ EXTRACT_SPEC V I D C <+ EXTRACT_LAWS V I D C.

Module Type EXTRACT_TIME (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I)
    (C : COST_T V) (Import X : EXTRACT V I D C).
  (* spec: R a *)
  Parameter R a : D.t -> nat.
  Parameter T_best : D.t -> N.
  Parameter T_extract : D.t -> positive -> N.
  Parameter T_check_dag : D.t -> positive -> extraction_dag V.t -> N.
  Parameter c_ex : N.
  (* SIG-QUESTION: T_best_le has a zero right-hand side when R db is zero.
     The width factors also need to account for cost values, literal costing and
     certificate identifiers that are absent from the stored database. *)
  (** Computing best rows pays for child incidences and heap operations. *)
  Parameter T_best_le : forall db, D.wf db ->
    (T_best db <= c_ex *
      N.of_nat (R db * (a db + 1) + R db * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1))%N.
  (** Checking visits every certificate entry and its children. *)
  Parameter T_check_dag_le : forall db c g,
    (T_check_dag db c g <= c_ex * N.of_nat (length g + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1))%N.
  (** Extraction pays for best rows and traversal of the chosen witness. *)
  Parameter T_extract_le : forall db c,
    (T_extract db c <= T_best db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1))%N.
End EXTRACT_TIME.

Module Type EXTRACT_T (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I)
    (C : COST_T V) := EXTRACT V I D C <+ EXTRACT_TIME V I D C.

Module Type EXTRACT_PLAN (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I)
    (C : COST_T V) (Import X : EXTRACT_T V I D C).
  Parameter state : Type.
  Parameter initial : D.t -> state.
  Parameter step : D.t -> state -> state + extraction_best V.t.
  Parameter finalised : state -> extraction_best V.t.
  Parameter counter : state -> positive -> nat.
  Parameter children : D.t -> positive -> list positive.
  Parameter ready : state -> list (positive * N).
  Parameter heap_potential : state -> N.
  Parameter T_initial : D.t -> N.
  Parameter T_step : D.t -> state -> N.
  Parameter k_step : N.
  Definition reachable (db : D.t) (s : state) : Prop :=
    clos_refl_trans state (fun a b => step db a = inl b) (initial db) s.
  Definition knuth_inv (db : D.t) (s : state) : Prop :=
    forall c n ch, In (c, (n, ch)) (finalised s) ->
      forall e, represents (D.view db) (Id c) e -> (n <= tree_cost e)%N.
  (** Initialisation has no finalised class and establishes the minimum-cost invariant. *)
  Parameter F1_initial : forall db, D.wf db -> D.canonical db ->
    finalised (initial db) = [] /\ knuth_inv db (initial db).
  (** A row's counter counts its unfinalised identifier children. *)
  Parameter F2_counter_spec : forall db s c, reachable db s ->
    counter s c = length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (finalised s)))
      (children db c)).
  (** Every ready entry has no unfinalised child. *)
  Parameter F3_ready : forall db s c n, reachable db s ->
    In (c, n) (ready s) -> counter s c = 0.
  (** Popping the minimum ready entry keeps finalised costs optimal. *)
  Parameter F4_pop_final : forall db s s', D.wf db -> D.canonical db ->
    reachable db s -> knuth_inv db s -> step db s = inl s' -> knuth_inv db s'.
  (** Finalised entries have finite witnesses attaining their costs. *)
  Parameter F5_finalised_attained : forall db s c n ch, D.wf db ->
    reachable db s -> In (c, (n, ch)) (finalised s) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  (** The driver uses one more step than the constructor-row count. *)
  Parameter F6_best_loop : forall db, D.wf db -> D.canonical db ->
    loop_fuel (step db) (R db + 1) (initial db) = inr (best db).
  (** A continuing step pays its work through heap potential and its row allowance. *)
  Parameter T1_step_amort : forall db s s', D.wf db -> reachable db s -> knuth_inv db s ->
    step db s = inl s' ->
    (T_step db s + heap_potential s' <= heap_potential s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1))%N.
  (** Aggregating the heap and incidence charges gives the public best-row bound. *)
  Parameter T2_best_loop : forall db, D.wf db ->
    (T_best db <= c_ex *
      N.of_nat (R db * (a db + 1) + R db * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1))%N.
End EXTRACT_PLAN.

Module Type EXTRACT_ALL (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I)
    (C : COST_T V) := EXTRACT_T V I D C <+ EXTRACT_PLAN V I D C.
