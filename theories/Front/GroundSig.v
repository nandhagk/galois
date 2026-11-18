(** * Ground equational exactness

    A run of a ground specification computes exactly the congruence of its instances on the
    terms that it represents. Two represented terms in one class of any outcome are congruent
    ([solve_sound]), two represented congruent terms share a class of a saturated outcome
    ([solve_complete]), and a saturated outcome represents each side of every instance
    ([solve_builds]). With the glue lemma of a derived program, these give the exactness of
    its equational inductive. The engine has no termination contract for programs that build
    terms, so no theorem says when a run saturates.
    For example, Steensgaard's [solve_exact] follows from them, from
    [Unification.pointer_congruence_congruent] and from [pointer_congruence_back].

    Main results
    - [solve_sound] Two represented terms in one class of any outcome are congruent.
    - [solve_complete] Two represented congruent terms share a class of a saturated outcome.
    - [solve_builds] A saturated outcome represents both sides of every instance.
    - [class_sat], [class_satisfies] The classes of a saturated outcome, extended freely, are a
      model of the outcome and of the specification.

    Builds on: the specifications, their lowering, the runner, the exact model and the run
    contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig CongruenceRefSig.

Import List.ListNotations.

(** * The model of classes *)

(** Nested inductives through sums get their induction hypotheses from this scheme. *)
Scheme All for sum.

(** A meaning in the model of a database. It is a class of the database, or a constructor
    applied freely to meanings. *)
Inductive class_term (V : Type) : Type :=
  | ClassOf (i : positive)
  | Free (f : positive) (args : list (class_term V + V)).

Arguments ClassOf {V}.
Arguments Free {V}.

(** * Theorems *)

(** Soundness of a run of a ground specification. *)
Module Type GROUND_SOUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** Two represented terms in one class of any outcome are congruent. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id i) t ->
    represents (D.view (snd (X.solve (spec_program s) rows lim))) (Id j) u ->
    same (D.view (snd (X.solve (spec_program s) rows lim))) i j ->
    congruent V.prim s (rows_in rows) t u.
End GROUND_SOUND.

(** Completeness of a saturated run of a ground specification. *)
Module Type GROUND_COMPLETE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** Two represented congruent terms share a class of a saturated outcome. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db i j t u,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    represents (D.view db) (Id i) t -> represents (D.view db) (Id j) u ->
    congruent V.prim s (rows_in rows) t u -> same (D.view db) i j.
  (** A saturated outcome represents both sides of every instance whose body holds in the
      input rows. *)
  Parameter solve_builds : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    (exists i, represents (D.view db) (Id i) tl) /\ (exists j, represents (D.view db) (Id j) tr).
End GROUND_COMPLETE.

Module Type GROUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) :=
  GROUND_SOUND V I J D R X <+ GROUND_COMPLETE V I J D R X.

(** * Proof plan *)

(** The model of the classes of a database. *)
Module Type GROUND_SPEC (V : VALUE) (I : INDEX V) (D : DATABASE V I).
  (** The cell of a meaning that is a class or a value. *)
  Definition class_cell (x : class_term V.t + V.t) : option (cell V.t) :=
    match x with
    | inl (ClassOf i) => Some (Id i)
    | inl (Free _ _) => None
    | inr v => Some (Val v)
    end.
  (** The cells of a list of meanings, when each has one. *)
  Fixpoint class_cells (xs : list (class_term V.t + V.t)) : option (list (cell V.t)) :=
    match xs with
    | [] => Some []
    | x :: rest =>
        match class_cell x, class_cells rest with
        | Some c, Some cs => Some (c :: cs)
        | _, _ => None
        end
    end.
  (** A constructor applied to meanings is the class of the output of its row, or free when
      the database has no such row. *)
  Definition class_con (db : D.t) (f : positive) (xs : list (class_term V.t + V.t)) :
      class_term V.t :=
    match class_cells xs with
    | Some k =>
        match D.old db f k with
        | Some (Some (Id j)) => ClassOf (D.repr db j)
        | _ => Free f xs
        end
    | None => Free f xs
    end.
  (** The model of a database. Its carrier is the classes extended freely, its relations are
      the relation rows of the database, and it has no lattice value. *)
  Definition class_model (db : D.t) : @model V.t :=
    {| carrier := class_term V.t;
       rel := fun r xs => exists k, class_cells xs = Some k /\ row (D.view db) r k None;
       con := class_con db;
       lat := fun _ _ _ => False |}.
  (** Each identifier means the class of its representative. *)
  Definition class_nu (db : D.t) (i : positive) : class_term V.t := ClassOf (D.repr db i).
End GROUND_SPEC.

(** Congruence in models of a ground specification. *)
Module Type GROUND_DENOTE_PLAN (V : VALUE).
  (** Congruent terms have one meaning in every model of a ground specification. *)
  Parameter congruent_denote : forall (s : spec V.t) I (M : @model V.t) t u,
    ground s = true -> satisfies V.prim V.merge M s I -> congruent V.prim s I t u ->
    denote M t = denote M u.
End GROUND_DENOTE_PLAN.

(** The model of the classes satisfies the outcome. *)
Module Type GROUND_CLASS_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  Include GROUND_SPEC V I D.
  (** The model of the classes of an outcome of a ground specification satisfies the outcome,
      with each identifier as the class of its representative. *)
  Parameter class_sat : forall (s : spec V.t) rows lim st db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (st, db) ->
    sat V.merge (class_model db) (class_nu db) (D.view db).
  (** Two identifiers of one class are in one class of a well-formed database. *)
  Parameter class_nu_same : forall db i j, D.wf db -> class_nu db i = class_nu db j ->
    same (D.view db) i j.
End GROUND_CLASS_PLAN.

(** The model of the classes satisfies the specification. *)
Module Type GROUND_SATISFIES_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  Include GROUND_SPEC V I D.
  (** The model of the classes of a saturated outcome of a ground specification is a model of
      the specification and its input rows. *)
  Parameter class_satisfies : forall (s : spec V.t) rows lim db,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    satisfies V.prim V.merge (class_model db) s (rows_in rows).
End GROUND_SATISFIES_PLAN.

(** A saturated outcome builds the instances. *)
Module Type GROUND_BUILD_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** At saturation, the rule of a union clause has built both sides of each instance whose
      body holds in the input rows, in one class. *)
  Parameter instance_built : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    exists i j, represents (D.view db) (Id i) tl /\ represents (D.view db) (Id j) tr /\
      same (D.view db) i j.
End GROUND_BUILD_PLAN.
