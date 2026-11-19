(** * Rewrites that read derived rows and lattice values

    A clause of an equation may read the rows of relations over values and the values of
    lattice tables, as the rewrite [known x c -> Mul (Ref x) a => Scale c a] reads the rows of
    the relation [known]. [SpecReads.v] gives such clauses their meaning, and this file states
    what a run of such a specification computes. When every relation and every lattice table
    takes only values ([value_tables]), the classes of the e-graph never reach them. In every
    outcome a stored row is then a row of the meaning of the relations over values and a stored
    value is a merge of assigned values ([saturate_rows_sound], [saturate_values_sound]). At
    saturation every derived row is stored ([saturate_rows_complete]), and a rewrite step whose
    premises read the rows and the stored values of the outcome, from a represented term,
    reaches a term of its class ([saturate_reads_closed]). The same holds of a step whose
    premises read derived rows ([saturate_derived_closed]).

    For example, when [known 1 5] is a derived row, a saturated outcome that represents
    [Mul (Ref 1) (Ref 2)] by a class also represents [Scale 5 (Ref 2)] by that class.

    Main results
    - [saturate_rows_sound] In every outcome a stored row of values is a row of the meaning of
      the relations over values.
    - [saturate_values_sound] In every outcome a stored value of a lattice table is a merge of
      assigned values.
    - [saturate_reads_closed] At saturation, a rewrite step whose premises read the rows and the
      stored values of the outcome, from a represented term, reaches a term of its class.
    - [saturate_rows_complete] At saturation every derived row is stored.
    - [saturate_derived_closed] At saturation, a rewrite step whose premises read derived rows,
      from a represented term, reaches a term of its class.

    Builds on: the specifications, the meanings of lattice reads and of equations that read
    rows, their lowering, the runner, the plans of lattice reads and of rewrites, and the run
    contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice SpecReads LowerSig RunnerSig LatticeReadSig.

Import List.ListNotations.

(** * Conditions *)

(** Every relation and every lattice table takes only values, so only the constructor tables
    hold classes. *)
Definition value_tables {V} (s : spec V) : bool :=
  forallb (fun d =>
    match out d with
    | OId => true
    | _ => forallb (fun so => match so with SVal => true | SId => false end) (arg_sorts d)
    end) (tables s).

(** A clause derives a row or assigns a value. *)
Definition value_clause {V} (c : clause V) : bool :=
  match head c with
  | Derive _ _ | Assign _ _ _ => true
  | Unify _ _ | Rewrites _ _ => false
  end.

(** The specification with the tables and the input tables of [s], and the clauses of [s] that
    derive rows or assign values. *)
Definition value_part {V} (s : spec V) : spec V :=
  Spec (tables s) (inputs s) (filter value_clause (clauses s)).

(** The model of the meaning of the relations over values: one class, the rows of
    [lat_derived] as relations and the merges of [lat_merged] as lattice values. *)
Definition unit_model {V} (prim : positive -> list V -> option V)
    (merge : positive -> V -> V -> V) (s : spec V) (I : positive -> list V -> Prop) :
    @model V :=
  Model unit
    (fun r xs => exists vs, xs = map inr vs /\ lat_derived prim merge s I r vs)
    (fun _ _ => tt)
    (fun f xs v => exists ks, xs = map inr ks /\ lat_merged prim merge s I f ks v).

(** The values of the literal terms of an environment of terms. *)
Definition literal_env {V} (e : positive -> option (@expr V)) (x : positive) : option V :=
  match e x with
  | Some (ELit v) => Some v
  | _ => None
  end.

(** * Theorems *)

(** Soundness of the rows and the lattice values of a specification with equations. *)
Module Type REWRITE_READ_SOUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In every outcome of a saturation, a stored row of values without output is a row of the
      meaning of the relations over values. *)
  Parameter saturate_rows_sound : forall (s : spec V.t) rows es lim st db cs r vs,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    row (D.view db) r (map Val vs) None ->
    lat_derived V.prim V.merge s (rows_in rows) r vs.
  (** In every outcome of a saturation, a stored value of a lattice table is a merge of
      assigned values. *)
  Parameter saturate_values_sound : forall (s : spec V.t) rows es lim st db cs f ks v,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    row (D.view db) f (map Val ks) (Some (Val v)) ->
    lat_merged V.prim V.merge s (rows_in rows) f ks v.
End REWRITE_READ_SOUND.

(** Closure of a saturated outcome under rewrite steps that read its rows and values. *)
Module Type REWRITE_READ_CLOSED (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** At saturation, a rewrite step whose premises read the rows and the stored values of the
      outcome, from a represented term, reaches a term of its class. *)
  Parameter saturate_reads_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t ->
    read_step V.prim s (view_rows (D.view db)) (stored_at (D.view db)) t u ->
    represents (D.view db) (Id i) u.
End REWRITE_READ_CLOSED.

(** The derived rows of a saturated outcome, and closure under rewrite steps that read them. *)
Module Type REWRITE_READ_ROWS (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** At saturation every derived row is stored. *)
  Parameter saturate_rows_complete : forall (s : spec V.t) rows es lim db cs r vs,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    derived V.prim s (rows_in rows) r vs -> row (D.view db) r (map Val vs) None.
  (** At saturation, a rewrite step whose premises read derived rows, from a represented term,
      reaches a term of its class. *)
  Parameter saturate_derived_closed : forall (s : spec V.t) rows es lim db cs i t u,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (Saturated, db, cs) ->
    represents (D.view db) (Id i) t ->
    read_step V.prim s (derived V.prim s (rows_in rows)) no_values t u ->
    represents (D.view db) (Id i) u.
End REWRITE_READ_ROWS.

Module Type REWRITE_READ (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) :=
  REWRITE_READ_SOUND V I J D R X <+ REWRITE_READ_CLOSED V I J D R X <+
  REWRITE_READ_ROWS V I J D R X.

(** * Proof plan *)

(** The model of the meaning of the relations over values, for soundness. *)
Module Type REWRITE_READ_VALUE_PLAN (V : VALUE).
  (** The clauses of a well-sorted specification that derive rows or assign values form a
      well-sorted specification. *)
  Parameter value_part_ok : forall (s : spec V.t),
    spec_ok s = true -> spec_ok (value_part s) = true.
  (** When the relations and the lattice tables take only values, the model of the meaning
      satisfies the clauses that derive rows or assign values. *)
  Parameter unit_model_satisfies : forall (s : spec V.t) (I : positive -> list V.t -> Prop),
    spec_ok s = true -> value_tables s = true ->
    satisfies V.prim V.merge (unit_model V.prim V.merge s I) (value_part s) I.
End REWRITE_READ_VALUE_PLAN.

(** The rules of the equations, for soundness. *)
Module Type REWRITE_READ_EQUATION_PLAN (V : VALUE).
  (** The model of the meaning validates, on well-sorted environments, the rule of each clause
      of a well-sorted specification that equates two terms. *)
  Parameter equation_rule_valid : forall (s : spec V.t) (I : positive -> list V.t -> Prop) c,
    spec_ok s = true -> In c (clauses s) -> value_clause c = false ->
    rule_valid_sorted V.prim (unit_model V.prim V.merge s I) (program_sorts (spec_program s))
      (program_kind (spec_program s)) (clause_rule c).
End REWRITE_READ_EQUATION_PLAN.

(** Premises over terms read as premises over values, for closure. *)
Module Type REWRITE_READ_VALUES_PLAN.
  (** A premise that holds under an environment of terms holds under the environment of the
      values of its literal terms. *)
  Parameter read_premise_values : forall {V} (prim : positive -> list V -> option V)
      (P : positive -> list V -> Prop) (Q : positive -> list V -> V -> Prop)
      (e : positive -> option (@expr V)) p,
    read_premise prim P Q e p -> premise_lat_in prim P Q (literal_env e) p.
End REWRITE_READ_VALUES_PLAN.

(** The right sides of rewrites whose premises read rows and values, for closure. *)
Module Type REWRITE_READ_SORTS_PLAN (V : VALUE).
  (** In a well-sorted specification, the right side of a rewrite instance whose premises read
      rows and values, and whose left side a class represents in a sorted view, is an
      application. *)
  Parameter read_right_app : forall (s : spec V.t) (P : positive -> list V.t -> Prop)
      (Q : positive -> list V.t -> V.t -> Prop) (w : @view V.t) c e l r tl tr i,
    spec_ok s = true -> value_tables s = true ->
    view_sorted (program_sorts (spec_program s)) w ->
    In c (clauses s) -> head c = Rewrites l r ->
    Forall (read_premise V.prim P Q e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    represents w (Id i) tl -> exists f us, tr = EApp f us.
End REWRITE_READ_SORTS_PLAN.
