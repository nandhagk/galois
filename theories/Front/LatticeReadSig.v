(** * Lattice tables that clauses read

    A clause may read the value that a lattice table stores at a key, as shortest paths do with
    the clause [Equals dist [a; b] d; Holds edge [b; c; w] => Assign dist [a; c] (d + w)]. This
    file states what a run of such a specification computes, in the meaning of
    [SpecLattice.v]. In every outcome a stored value is a merge of assigned values and a stored
    row is derived, with no further condition ([solve_sound], [solve_rows_sound]). In a
    saturated outcome every assigned value is below the stored value and every derived row is
    stored ([solve_complete], [solve_rows_complete]). Completeness needs clauses that are
    monotone in the values that they read. The check [reads_ok] says that a read value is a
    variable that occurs once in its body and in no key of the head, and [monotone] says that
    the value that a clause assigns grows with the values that it reads, in the orders of the
    merges. No run then saturates when a key has an assigned value and no merge of assigned
    values there is above all of them ([unbounded_unsaturated]).

    For example, with [Pos.min] as the merge of the table of distances, a saturated outcome
    stores at each pair of nodes the length of a shortest path, and with [Pos.max] over the
    lengths of the paths around a cycle no run saturates.

    Main results
    - [solve_sound] In every outcome a stored value of a lattice table is a merge of assigned
      values.
    - [solve_rows_sound] In every outcome a stored row of values is derived.
    - [solve_complete] In a saturated outcome of a monotone specification every assigned value
      is below the stored value.
    - [solve_rows_complete] In a saturated outcome of a monotone specification every derived row
      is stored.
    - [solve_exact] In a saturated outcome of a monotone specification the stored value is a
      merge of assigned values that is above every assigned value.
    - [unbounded_unsaturated] No run of a monotone specification saturates when a key has an
      assigned value and no merge of assigned values there is above all of them.

    Builds on: the specifications that read lattice tables, their lowering, the runner and the
    run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig.

Import List.ListNotations.

(** * Conditions *)

(** A specification whose clauses may read lattice tables. No table is a constructor table, and
    every head derives a row or assigns a value. With the kind check of [spec_ok], no pattern is
    a constructor application, so the lowered program has no identifier. *)
Definition lattice_reads {V} (s : spec V) : bool :=
  forallb (fun d => match out d with OId => false | _ => true end) (tables s) &&
  forallb (fun c =>
    match head c with
    | Derive _ _ | Assign _ _ _ => true
    | _ => false
    end) (clauses s).

(** The variables that the reads of a body bind to the values that they read. *)
Definition read_vars {V} (ps : list (premise V)) : list positive :=
  flat_map (fun p =>
    match p with
    | Equals _ _ (PVar x) => [x]
    | _ => []
    end) ps.

(** The patterns of the keys of a head: the arguments of a row or of an assigned value, and the
    two sides of an equation. *)
Definition head_keys {V} (h : consequence V) : list (pat V) :=
  match h with
  | Derive _ args | Assign _ args _ => args
  | Unify l r | Rewrites l r => [l; r]
  end.

(** The number of occurrences of a variable in a list. *)
Definition occurrences (x : positive) (xs : list positive) : nat :=
  length (filter (Pos.eqb x) xs).

(** A clause reads lattice values in a monotone frame. Each read value is a variable, which
    occurs once in the body and in no key of the head. Raising a read value then changes no row
    that the body reads and no key that the head writes. *)
Definition clause_reads_ok {V} (c : clause V) : bool :=
  forallb (fun p =>
    match p with
    | Equals _ _ (PVar _) => true
    | Equals _ _ _ => false
    | _ => true
    end) (body c) &&
  forallb (fun x =>
    Nat.eqb (occurrences x (flat_map premise_vars (body c))) 1 &&
    negb (existsb (Pos.eqb x) (flat_map pat_vars (head_keys (head c)))))
    (read_vars (body c)).

(** Every clause reads lattice values in a monotone frame. *)
Definition reads_ok {V} (s : spec V) : bool := forallb clause_reads_ok (clauses s).

(** The environment [e'] raises the values that the clause [c] reads above those of [e], in the
    orders of the merges of the read tables, and agrees with [e] on every other variable. *)
Definition env_below {V} (merge : positive -> V -> V -> V) (s : spec V) (c : clause V)
    (e e' : positive -> option V) : Prop :=
  forall x, e' x = e x \/
    exists f args m u u', In (Equals f args (PVar x)) (body c) /\
      lookup_kind (tables s) f = Some (OLat m) /\ e x = Some u /\ e' x = Some u' /\
      merge m u u' = u'.

(** The value that each clause assigns grows with the values that it reads. Raising the read
    values in the orders of the merges of their tables raises the assigned value in the order
    of the merge of its table. *)
Definition monotone {V} (prim : positive -> list V -> option V)
    (merge : positive -> V -> V -> V) (s : spec V) : Prop :=
  forall c f args v m e e' u,
    In c (clauses s) -> head c = Assign f args v -> lookup_kind (tables s) f = Some (OLat m) ->
    env_below merge s c e e' -> pat_value prim e v = Some u ->
    exists u', pat_value prim e' v = Some u' /\ merge m u u' = u'.

(** A view stores at a key of a lattice table a value above [u], in the order of the merge of
    the table. *)
Definition stored_above {V} (merge : positive -> V -> V -> V) (s : spec V) (w : @view V)
    (f : positive) (ks : list V) (u : V) : Prop :=
  exists m u', lookup_kind (tables s) f = Some (OLat m) /\
    row w f (map Val ks) (Some (Val u')) /\ merge m u u' = u'.

(** A view stores the value [u] at a key of a lattice table. *)
Definition stored_at {V} (w : @view V) (f : positive) (ks : list V) (u : V) : Prop :=
  row w f (map Val ks) (Some (Val u)).

(** * Theorems *)

(** Soundness of lattice tables that clauses read. *)
Module Type LATTICE_READ_SOUND (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In every outcome a stored value of a lattice table is a merge of assigned values. *)
  Parameter solve_sound : forall (s : spec V.t) rows lim f ks v,
    spec_ok s = true -> lattice_reads s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) f (map Val ks) (Some (Val v)) ->
    lat_merged V.prim V.merge s (rows_in rows) f ks v.
  (** In every outcome a stored row of values without output is derived. *)
  Parameter solve_rows_sound : forall (s : spec V.t) rows lim r vs,
    spec_ok s = true -> lattice_reads s = true -> rows_ok s rows = true ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r (map Val vs) None ->
    lat_derived V.prim V.merge s (rows_in rows) r vs.
End LATTICE_READ_SOUND.

(** Completeness of lattice tables that clauses read, at saturation. *)
Module Type LATTICE_READ_COMPLETE (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In a saturated outcome of a monotone specification every assigned value is below the
      stored value. *)
  Parameter solve_complete : forall (s : spec V.t) rows lim db f m ks w,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\ V.merge m w v = v.
  (** In a saturated outcome of a monotone specification every derived row is stored. *)
  Parameter solve_rows_complete : forall (s : spec V.t) rows lim db r vs,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_derived V.prim V.merge s (rows_in rows) r vs ->
    row (D.view db) r (map Val vs) None.
End LATTICE_READ_COMPLETE.

(** Exactness and a condition for saturation, which follow from soundness and completeness. *)
Module Type LATTICE_READ_EXACT (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** In a saturated outcome of a monotone specification, the value stored at a key with an
      assigned value is a merge of assigned values that is above every assigned value. *)
  Parameter solve_exact : forall (s : spec V.t) rows lim db f m ks w0,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w0 ->
    exists v, row (D.view db) f (map Val ks) (Some (Val v)) /\
      lat_merged V.prim V.merge s (rows_in rows) f ks v /\
      forall w, lat_assigned V.prim V.merge s (rows_in rows) f ks w -> V.merge m w v = v.
  (** No run of a monotone specification saturates when a key has an assigned value and no
      merge of assigned values there is above all of them. *)
  Parameter unbounded_unsaturated : forall (s : spec V.t) rows lim f m ks w0,
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true -> rows_ok s rows = true ->
    monotone V.prim V.merge s -> lookup_kind (tables s) f = Some (OLat m) ->
    lat_assigned V.prim V.merge s (rows_in rows) f ks w0 ->
    (forall v, lat_merged V.prim V.merge s (rows_in rows) f ks v ->
      exists w, lat_assigned V.prim V.merge s (rows_in rows) f ks w /\ V.merge m w v <> v) ->
    fst (X.solve (spec_program s) rows lim) <> Saturated.
End LATTICE_READ_EXACT.

Module Type LATTICE_READ (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) :=
  LATTICE_READ_SOUND V I J D R X <+ LATTICE_READ_COMPLETE V I J D R X <+
  LATTICE_READ_EXACT V I J D R X.

(** * Proof plan *)

(** The model of the meaning, for soundness. *)
Module Type LATTICE_READ_MODEL_PLAN (V : VALUE).
  (** A specification that reads lattice tables has a model of its input rows whose relations
      hold only of derived rows and whose lattice values are merges of assigned values. *)
  Parameter read_model : forall (s : spec V.t) rows,
    spec_ok s = true -> lattice_reads s = true ->
    exists M : @model V.t, satisfies V.prim V.merge M s (rows_in rows) /\
      (forall r xs, rel M r xs ->
        exists vs, xs = map inr vs /\ lat_derived V.prim V.merge s (rows_in rows) r vs) /\
      (forall f xs v, lat M f xs v ->
        exists ks, xs = map inr ks /\ lat_merged V.prim V.merge s (rows_in rows) f ks v).
End LATTICE_READ_MODEL_PLAN.

(** The query of a body whose reads see the stored values, for completeness. *)
Module Type LATTICE_READ_QUERY_PLAN.
  (** The query of a body takes its fresh variables from [next] on. *)
  Parameter query_body_next : forall {V} bound next (ps : list (premise V)),
    (next <= snd (query_body bound next ps))%positive.
  (** The query of a body whose premises hold in a view, where each read sees the stored value,
      matches with fresh variables from [next] on. *)
  Parameter query_body_stored_matches : forall {V} (prim : positive -> list V -> option V)
      (w : @view V) bound next ps e (s : @env V),
    (body_top ps < next)%positive ->
    Forall (premise_lat_in prim (view_rows w) (stored_at w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\
      matches prim w (fst (fst (query_body bound next ps))) s'.
  (** The definitions of such a body, when present, compute the values of its equations, and
      then the actions that follow are present. *)
  Parameter query_body_stored_lets : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (w : @view V) bound next ps e (s : @env V) rest,
    (body_top ps < next)%positive ->
    Forall (premise_lat_in prim (view_rows w) (stored_at w) e) ps ->
    (forall x v, e x = Some v -> s x = Some (Val v)) ->
    present prim merge w s (snd (fst (query_body bound next ps)) ++ rest) ->
    exists s', (forall x, (x < next)%positive \/ (snd (query_body bound next ps) <= x)%positive ->
        s' x = s x) /\ present prim merge w s' rest.
End LATTICE_READ_QUERY_PLAN.

(** Raising the values that a clause reads to the stored values, for completeness. *)
Module Type LATTICE_READ_RAISE_PLAN.
  (** A body that reads values below the stored values holds again when its reads see the
      stored values, under an environment that raises the read values. *)
  Parameter body_reads_raise : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) (w : @view V) c e,
    clause_reads_ok c = true ->
    Forall (premise_lat_in prim (view_rows w) (stored_above merge s w) e) (body c) ->
    exists e', env_below merge s c e e' /\
      Forall (premise_lat_in prim (view_rows w) (stored_at w) e') (body c).
  (** Raising the values that a clause reads keeps the values of the keys of its head. *)
  Parameter head_keys_raise : forall {V} (prim : positive -> list V -> option V)
      (merge : positive -> V -> V -> V) (s : spec V) c e e',
    clause_reads_ok c = true -> env_below merge s c e e' ->
    pat_values prim e' (head_keys (head c)) = pat_values prim e (head_keys (head c)).
  (** A clause of a well-sorted specification that derives a row derives it into a relation. *)
  Parameter derive_head_rel : forall {V} (s : spec V) c r args,
    spec_ok s = true -> In c (clauses s) -> head c = Derive r args ->
    lookup_kind (tables s) r = Some ORel.
End LATTICE_READ_RAISE_PLAN.

(** A closed view holds the meaning, for completeness. *)
Module Type LATTICE_READ_CLOSED_PLAN (V : VALUE).
  (** A functional view that the rules of a monotone specification close, with the kinds of its
      tables and no output in its relation rows, holds every row derived from its own rows and
      stores at each key a value above each value that the clauses assign there. *)
  Parameter lower_reads_closed : forall (s : spec V.t) (w : @view V.t),
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true ->
    monotone V.prim V.merge s -> closed V.prim V.merge (spec_program s) w ->
    (forall g, kind w g = lookup_kind (tables s) g) ->
    (forall g k o, row w g k o -> lookup_kind (tables s) g = Some ORel -> o = None) ->
    (forall g k o1 o2, row w g k o1 -> row w g k o2 -> o1 = o2) ->
    (forall r vs, lat_derived V.prim V.merge s (view_rows w) r vs -> view_rows w r vs) /\
    (forall f ks u, lat_assigned V.prim V.merge s (view_rows w) f ks u ->
      stored_above V.merge s w f ks u).
End LATTICE_READ_CLOSED_PLAN.
