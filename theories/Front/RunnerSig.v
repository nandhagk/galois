(** * Running derived programs

    A derived program runs on a database that holds its input rows. [seed] loads the program
    with its planned slots and puts each input row, [solve] runs the program on the seed, and
    [holds] says whether a database has a row of values without output. [saturate] adds terms
    to the seed before the run, and [equal] says whether the run puts two terms in one class.
    The specification conditions say which programs and rows the theorems cover. [spec_ok]
    checks the sorts of the lowered program and the kinds of the patterns, and [rows_ok]
    checks that each input row belongs to an input relation and has the arity of its first
    declaration, with values at every argument.
    For example, [solve MayPoints.program (MayPoints.facts q) lim] is Andersen's analysis of
    [q].

    Main results
    - [seed_rows], [seed_ready] The seed holds exactly the input rows, and the run contracts
      apply to it.
    - [holds_spec] A lookup says whether a database has a row of values without output.
    - [seed_sat], [solve_keeps] A model of the input rows satisfies the seed, and every
      outcome keeps the input rows.
    - [T_seed_le], [T_solve_split] Seeding pays for planning, loading and each put, and a
      solve pays for its seed, planning and the run.

    Builds on: the specifications, their lowering, and the run contracts. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

(** * Conditions *)

(** The input rows of a list, as a relation. *)
Definition rows_in {V} (rows : list (positive * list V)) (r : positive) (vs : list V) : Prop :=
  In (r, vs) rows.

(** The lowered program of a specification is well sorted, and its patterns name tables of the
    right kinds. *)
Definition spec_ok {V} (s : spec V) : bool := check_program (spec_program s) && kinds_ok s.

(** The lowered program of a specification is relational. *)
Definition relational {V} (s : spec V) : bool := relational_fragment (spec_program s).

(** A term to add is well sorted. Each application is of a constructor table of the
    specification, with literals at its value arguments and applications at its class
    arguments. *)
Fixpoint term_ok {V} (s : spec V) (e : @expr V) {struct e} : bool :=
  match e with
  | ELit _ => true
  | EApp f args =>
      match lookup_kind (tables s) f, lookup_sorts (tables s) f with
      | Some OId, Some ss =>
          (fix go (ss : list sort) (args : list (@expr V)) {struct args} : bool :=
             match ss, args with
             | [], [] => true
             | SVal :: rest_ss, ELit _ :: rest => go rest_ss rest
             | SId :: rest_ss, (EApp _ _ as a) :: rest => term_ok s a && go rest_ss rest
             | _, _ => false
             end) ss args
      | _, _ => false
      end
  end.

(** Each row belongs to an input relation of the specification, and has the arity of the first
    declaration of its table, which takes only values. The engine reads the first declaration
    of a name, so a later declaration of the same name does not count. *)
Definition rows_ok {V} (s : spec V) (rows : list (positive * list V)) : bool :=
  forallb (fun row =>
    existsb (Pos.eqb (fst row)) (inputs s) &&
    match lookup_kind (tables s) (fst row), lookup_sorts (tables s) (fst row) with
    | Some ORel, Some ss =>
        Nat.eqb (length ss) (length (snd row)) &&
        forallb (fun so => match so with SVal => true | SId => false end) ss
    | _, _ => false
    end) rows.

(** * Operations *)

Module Type RUNNER_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D).
  (** The loaded program with each input row put as a value row. *)
  Parameter seed : program V.t -> list (positive * list V.t) -> D.t.
  (** The run of the program on its seed. *)
  Parameter solve : program V.t -> list (positive * list V.t) -> limits -> stop * D.t.
  (** Whether a database holds a row of values. *)
  Parameter holds : positive -> list V.t -> D.t -> bool.
  (** Add a term: a literal is its value, and an application makes the row of its constructor
      over the cells of its arguments. *)
  Parameter add_term : @expr V.t -> D.t -> cell V.t * D.t.
  (** Add terms in order. *)
  Parameter add_terms : list (@expr V.t) -> D.t -> list (cell V.t) * D.t.
  (** The run of a program on its seed and some terms, with the cells of the terms. *)
  Parameter saturate : program V.t -> list (positive * list V.t) -> list (@expr V.t) -> limits ->
    stop * D.t * list (cell V.t).
  (** Whether two cells are one class or one value. *)
  Parameter same_cell : cell V.t -> cell V.t -> D.t -> bool.
  (** Whether saturating a program with two terms puts them in one class. *)
  Parameter equal : program V.t -> list (positive * list V.t) -> limits -> @expr V.t ->
    @expr V.t -> bool.
End RUNNER_OPS.

(** * Laws *)

Module Type RUNNER_LAWS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (Import X : RUNNER_OPS V I J D R).
  (** The seed puts the rows in order into the loaded program. *)
  Parameter seed_unfold : forall p rows,
    seed p rows = fold_left (fun db row => D.put (fst row) (map Val (snd row)) None db) rows
      (R.load p (R.plan p)).
  (** A solve runs the planned program on its seed. *)
  Parameter solve_unfold : forall p rows lim,
    solve p rows lim = R.run p (R.plan p) lim (seed p rows).
  (** A row holds when its lookup finds it without output. *)
  Parameter holds_unfold : forall r vs db,
    holds r vs db = match fst (D.lookup r (map Val vs) db) with
                    | Some None => true
                    | _ => false
                    end.
  (** A literal adds nothing. *)
  Parameter add_term_lit : forall v db, add_term (ELit v) db = (Val v, db).
  (** An application adds its arguments, then the row of its constructor. *)
  Parameter add_term_app : forall f args db,
    add_term (EApp f args) db =
      let '(cs, db1) := add_terms args db in
      let '(i, db2) := D.make f cs db1 in
      (Id i, db2).
  (** No terms add nothing. *)
  Parameter add_terms_nil : forall db, add_terms [] db = ([], db).
  (** Terms are added from the first. *)
  Parameter add_terms_cons : forall e es db,
    add_terms (e :: es) db =
      let '(c, db1) := add_term e db in
      let '(cs, db2) := add_terms es db1 in
      (c :: cs, db2).
  (** A saturation adds the terms to the seed, then runs the planned program. *)
  Parameter saturate_unfold : forall p rows es lim,
    saturate p rows es lim =
      let '(cs, db) := add_terms es (seed p rows) in
      let '(st, db') := R.run p (R.plan p) lim db in
      (st, db', cs).
  (** Two classes are one when they have one representative, and two values when they are
      equal. *)
  Parameter same_cell_unfold : forall a b db,
    same_cell a b db =
      match a, b with
      | Id i, Id j => Pos.eqb (fst (D.find i db)) (fst (D.find j db))
      | Val v, Val w => V.eqb v w
      | _, _ => false
      end.
  (** Two terms are equal when saturation puts their cells in one class. *)
  Parameter equal_unfold : forall p rows lim t u,
    equal p rows lim t u =
      match saturate p rows [t; u] lim with
      | (_, db, [c; d]) => same_cell c d db
      | _ => false
      end.
End RUNNER_LAWS.

Module Type RUNNER (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) := RUNNER_OPS V I J D R <+ RUNNER_LAWS V I J D R.

(** * Time *)

Module Type RUNNER_TIME (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) (Import X : RUNNER V I J D R).
  Parameter T_seed : program V.t -> list (positive * list V.t) -> N.
  Parameter T_solve : program V.t -> list (positive * list V.t) -> limits -> N.
  Parameter c_runner : N.
  (** Seeding pays for planning, for loading and for each put at the unit and the identifier
      width of the seed, with the slots of the plan. *)
  Parameter T_seed_le : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (fold_right
          (fun row n => ((length (snd row) + 2) * (length (snd row) + 2) + n)%nat) 0%nat rows +
          1))%N.
  (** A solve pays for its seed, for planning and for the run. *)
  Parameter T_solve_split : forall p rows lim,
    (T_solve p rows lim <=
      T_seed p rows + R.T_plan p + R.T_run p (R.plan p) lim (seed p rows) + c_runner)%N.
End RUNNER_TIME.

Module Type RUNNER_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) := RUNNER V I J D R <+ RUNNER_TIME V I J D R.

(** * Facts *)

(** What the theorems need from the seed and from a lookup, for every runner. *)
Module Type RUNNER_FACTS (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R).
  (** The planned program of a specification that passes its checks passes the plan check. *)
  Parameter plan_ok : forall (s : spec V.t), spec_ok s = true ->
    R.plans_ok (spec_program s) (R.plan (spec_program s)).
  (** The seed holds exactly the input rows, as rows of values without output. *)
  Parameter seed_rows : forall (s : spec V.t) rows r k o,
    spec_ok s = true -> rows_ok s rows = true ->
    row (D.view (X.seed (spec_program s) rows)) r k o <->
      o = None /\ exists vs, k = map Val vs /\ In (r, vs) rows.
  (** The seed is well formed, canonical and loaded with the planned program, and it has no
      identifier. *)
  Parameter seed_ready : forall (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    D.wf (X.seed (spec_program s) rows) /\ D.canonical (X.seed (spec_program s) rows) /\
    R.loaded (spec_program s) (R.plan (spec_program s)) (X.seed (spec_program s) rows) /\
    R.no_ids (X.seed (spec_program s) rows).
  (** A lookup says whether a well-formed database has a row of values without output. *)
  Parameter holds_spec : forall db r vs, D.wf db ->
    X.holds r vs db = true <-> row (D.view db) r (map Val vs) None.
  (** A model of the input rows satisfies the seed under every valuation. *)
  Parameter seed_sat : forall (s : spec V.t) rows (M : @model V.t) nu,
    spec_ok s = true -> rows_ok s rows = true ->
    satisfies V.prim V.merge M s (rows_in rows) ->
    sat V.merge M nu (D.view (X.seed (spec_program s) rows)).
  (** Every outcome keeps each input row. *)
  Parameter solve_keeps : forall (s : spec V.t) rows lim r vs,
    spec_ok s = true -> rows_ok s rows = true -> In (r, vs) rows ->
    row (D.view (snd (X.solve (spec_program s) rows lim))) r (map Val vs) None.
End RUNNER_FACTS.
