(** * Running derived programs

    A derived program runs on a database that holds its input rows. [seed] loads the program
    with its planned slots and puts each input row, [solve] runs the program on the seed, and
    [holds] says whether a database has a row of values without output. [saturate] adds terms
    to the seed before the run, and [equal] says whether the run puts two terms in one class.
    The specification conditions say which programs and rows the theorems cover. [spec_ok]
    checks the sorts of the lowered program and the kinds of the patterns, and [rows_ok]
    checks that each input row belongs to an input relation and has the arity of its first
    declaration, with values at every argument. The measures [rows_work] and [term_work] count
    the arity factors that the database charges for putting the input rows and for allocating
    the constructors of a term.
    For example, [solve MayPoints.program (MayPoints.facts q) lim] is Andersen's analysis of
    [q].

    Main results
    - [seed_rows], [seed_ready] The seed holds exactly the input rows, and the run contracts
      apply to it.
    - [holds_spec] A lookup says whether a database has a row of values without output.
    - [seed_sat], [solve_keeps], [saturate_keeps] A model of the input rows satisfies the seed,
      and every outcome of a solve or a saturation keeps the input rows.
    - [T_seed_le], [T_solve_split] Seeding pays for planning, loading and each put, and a
      solve pays for its seed, planning and the run.
    - [seed_complexity], [solve_complexity], [saturate_complexity] Seeding, solving and
      saturating cost the planning, the loading, the put work of the rows, the work of the terms
      and the rounds of the run, at the unit and the identifier width of the databases.
    - [T_add_terms_amort] Adding terms gives each constructor the amortized budget of one
      allocation.
    - [holds_complexity], [same_cell_complexity], [equal_complexity] A lookup is linear in its
      key at the unit of the database, and comparing two cells pays for two finds and the bits
      of a representative.

    Builds on: the specifications, their lowering, and the run contracts. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.
Import ComplexityNotations.

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

(** * Measures *)

(** The put work of input rows. A row of [n] values pays [(n + 2) * (n + 2)], the arity factor of
    one insertion in the amortized budget of the database. *)
Definition rows_work {V} (rows : list (positive * list V)) : nat :=
  fold_right (fun row n => (length (snd row) + 2) * (length (snd row) + 2) + n) 0 rows.

(** The work of adding a term. An application of [n] arguments pays [(n + 2) * (n + 2)], the
    arity factor of one constructor in the amortized budget of the database, and a literal
    pays one. *)
Fixpoint term_work {V} (e : @expr V) : nat :=
  match e with
  | ELit _ => 1
  | EApp _ args =>
    (length args + 2) * (length args + 2) + fold_right (fun a n => term_work a + n) 0 args
  end.

(** The work of adding terms in order. *)
Definition terms_work {V} (es : list (@expr V)) : nat :=
  fold_right (fun e n => term_work e + n) 0 es.

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
  Parameter T_holds : positive -> list V.t -> D.t -> N.
  Parameter T_add_term : @expr V.t -> D.t -> N.
  Parameter T_add_terms : list (@expr V.t) -> D.t -> N.
  Parameter T_saturate : program V.t -> list (positive * list V.t) -> list (@expr V.t) ->
    limits -> N.
  Parameter T_same_cell : cell V.t -> cell V.t -> D.t -> N.
  Parameter T_equal : program V.t -> list (positive * list V.t) -> limits -> @expr V.t ->
    @expr V.t -> N.
  Parameter c_runner : N.
  Parameter c_query : N.
  Parameter c_terms : N.
  Parameter c_saturate : N.
  (** The cost of a seed at identifier bound [B] and unit bound [U]. Planning is cubic in the
      program and loading is linear in its layout. Each put pays for its arity and the slots of
      the plan, at the unit and the identifier width. *)
  Definition seed_cost (B : N) (U : nat) (p : program V.t) (rows : list (positive * list V.t))
      : N :=
    (N.of_nat ((R.size_program p + 1) * (R.size_program p + 1) * (R.size_program p + 1)) +
     R.load_cost p (R.plan p) +
     N.of_nat (U * (N.to_nat (N.log2 B) + 1) * (length (Syntax.slots V.t (R.plan p)) + 1) *
       (rows_work rows + 1)))%N.
  (** The cost of a saturation at identifier bound [B] and unit bound [U]. It adds to the cost
      of the seed each constructor of the terms and each round of the run, at the unit and the
      identifier width, and the fuel counter. With no terms it is the cost of a solve. *)
  Definition saturate_cost (B : N) (U : nat) (p : program V.t)
      (rows : list (positive * list V.t)) (es : list (@expr V.t)) (lim : limits) : N :=
    (seed_cost B U p rows +
     N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
       ((length (Syntax.slots V.t (R.plan p)) + 1) * (terms_work es + 1) +
        (R.wbits p + 1) * R.run_work p (R.plan p) lim (snd (add_terms es (seed p rows))))) +
     N.of_nat (N.size_nat (max_iter lim) + 1))%N.

  (** Seeding pays for planning, for loading and for each put at the unit and the identifier
      width of the seed, with the slots of the plan. *)
  Parameter T_seed_le : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (rows_work rows + 1))%N.
  (** Seeding, with the potential that it leaves priced at the unit bound, has the budget of
      [T_seed_le]. Loading starts without potential, and each put pays for its share of the
      deferred rebuild. *)
  Parameter T_seed_amort : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows + N.of_nat U * D.potential B (seed (spec_program s) rows) <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (rows_work rows + 1))%N.
  (** Seeding costs planning, loading and the put work of the rows, at the unit and the
      identifier width of the seed. *)
  Parameter seed_complexity :
    T_seed (spec_program s) rows ∈
      𝑂(seed_cost (D.ids (seed (spec_program s) rows)) (D.unit (seed (spec_program s) rows))
        (spec_program s) rows)
      for (s, rows) | spec_ok s = true /\ rows_ok s rows = true.

  (** A solve pays for its seed, for planning and for the run. *)
  Parameter T_solve_split : forall p rows lim,
    (T_solve p rows lim <=
      T_seed p rows + R.T_plan p + R.T_run p (R.plan p) lim (seed p rows) + c_runner)%N.
  (** A solve costs its seed and the rounds of its run. The puts and the rounds are paid at an
      identifier bound [B] and a unit bound [U] of the outcome, which bound the seed too because
      a run never lowers them, so the credit that the puts leave pays for the deferred rebuilds
      of the run. *)
  Parameter solve_complexity :
    T_solve (spec_program s) rows lim ∈ 𝑂(saturate_cost B U (spec_program s) rows [] lim)
      for (B, U, s, rows, lim) |
        spec_ok s = true /\ rows_ok s rows = true /\
        (D.ids (snd (solve (spec_program s) rows lim)) <= B)%N /\
        D.unit (snd (solve (spec_program s) rows lim)) <= U.

  (** A lookup of a row of values pays for its key at the unit of the database and for the bits
      of its values. *)
  Parameter T_holds_le : forall r vs db, D.wf db ->
    (T_holds r vs db <= c_query * N.of_nat ((length vs + 1) * D.unit db +
      fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs + 1))%N.
  (** A lookup of a row of values is linear in its key at the unit of the database and in the
      bits of its values. *)
  Parameter holds_complexity :
    T_holds r vs db ∈
      𝑂(N.of_nat ((length vs + 1) * D.unit db +
        fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs))
      for (r, vs, db) | D.wf db.

  (** Adding well-sorted terms to a database that is loaded with the planned program never
      lowers its unit. *)
  Parameter add_terms_unit : forall (s : spec V.t) es db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> D.unit db <= D.unit (snd (add_terms es db)).
  (** Adding well-sorted terms to a database that is loaded with the planned program returns
      identifier cells that the result allocates, which the bound of [equal] reads. *)
  Parameter add_terms_allocated : forall (s : spec V.t) es db i,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> In (Id i) (fst (add_terms es db)) ->
    D.allocated (snd (add_terms es db)) i.
  (** Adding a well-sorted term to a database that is loaded with the planned program gives
      each constructor the budget of one allocation in [D.T_make_amort], at the unit bound [U]
      and the identifier bound [B] of the result. The time and the potential that it leaves,
      priced at [U], stay within these budgets and the potential that it found. *)
  Parameter T_add_term_amort : forall B U (s : spec V.t) e db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    term_ok s e = true ->
    (D.ids (snd (add_term e db)) <= B)%N -> D.unit (snd (add_term e db)) <= U ->
    (T_add_term e db + N.of_nat U * D.potential B (snd (add_term e db)) <=
      N.of_nat U * (c_terms * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (term_work e) + D.potential B db))%N.
  (** Adding well-sorted terms in order has the budget of [T_add_term_amort] for each term. *)
  Parameter T_add_terms_amort : forall B U (s : spec V.t) es db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true ->
    (D.ids (snd (add_terms es db)) <= B)%N -> D.unit (snd (add_terms es db)) <= U ->
    (T_add_terms es db + N.of_nat U * D.potential B (snd (add_terms es db)) <=
      N.of_nat U * (c_terms * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (terms_work es + 1) + D.potential B db))%N.
  (** Adding a well-sorted term is linear in its work at the unit bound and the identifier
      width, with the slots of the plan, once the potential that it leaves is counted. *)
  Parameter add_term_complexity :
    T_add_term e db ∈
      𝑂(N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
        (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) * term_work e))
      amortised N.of_nat U * D.potential B db ↦ N.of_nat U * D.potential B (snd (add_term e db))
      for (B, U, s, e, db) |
        spec_ok s = true /\ D.wf db /\ R.loaded (spec_program s) (R.plan (spec_program s)) db /\
        term_ok s e = true /\ (D.ids (snd (add_term e db)) <= B)%N /\
        D.unit (snd (add_term e db)) <= U.
  (** Adding well-sorted terms is linear in their work in the same way. *)
  Parameter add_terms_complexity :
    T_add_terms es db ∈
      𝑂(N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
        (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) * terms_work es))
      amortised N.of_nat U * D.potential B db ↦
        N.of_nat U * D.potential B (snd (add_terms es db))
      for (B, U, s, es, db) |
        spec_ok s = true /\ D.wf db /\ R.loaded (spec_program s) (R.plan (spec_program s)) db /\
        forallb (term_ok s) es = true /\ (D.ids (snd (add_terms es db)) <= B)%N /\
        D.unit (snd (add_terms es db)) <= U.

  (** A saturation pays for its seed, for adding the terms, for planning and for the run. *)
  Parameter T_saturate_split : forall p rows es lim,
    (T_saturate p rows es lim <=
      T_seed p rows + T_add_terms es (seed p rows) + R.T_plan p +
      R.T_run p (R.plan p) lim (snd (add_terms es (seed p rows))) + c_saturate)%N.
  (** A saturation costs its seed, the constructors of its terms and the rounds of its run, at
      bounds [B] and [U] of the outcome. *)
  Parameter saturate_complexity :
    T_saturate (spec_program s) rows es lim ∈ 𝑂(saturate_cost B U (spec_program s) rows es lim)
      for (B, U, s, rows, es, lim) |
        spec_ok s = true /\ rows_ok s rows = true /\ forallb (term_ok s) es = true /\
        (D.ids (snd (fst (saturate (spec_program s) rows es lim))) <= B)%N /\
        D.unit (snd (fst (saturate (spec_program s) rows es lim))) <= U.

  (** Comparing two classes pays for two finds at the unit of the database and for the bits of
      the representative of the first class. Comparing two values pays for the bits of the first
      value. *)
  Parameter T_same_cell_le : forall a b db, D.wf db ->
    (forall i, In (Id i) [a; b] -> D.allocated db i) ->
    (T_same_cell a b db <=
      c_query * N.of_nat (2 * D.unit db + cell_bits V.encode (D.canon db a) + 1))%N.
  (** Comparing two cells is linear in the unit of the database and in the bits of the first
      cell after canonicalization. *)
  Parameter same_cell_complexity :
    T_same_cell a b db ∈ 𝑂(N.of_nat (D.unit db + cell_bits V.encode (D.canon db a)))
      for (a, b, db) | D.wf db /\ (forall i, In (Id i) [a; b] -> D.allocated db i).

  (** Deciding equality pays for the saturation with the two terms and for comparing their
      cells. *)
  Parameter T_equal_split : forall p rows lim t u st db c d,
    saturate p rows [t; u] lim = (st, db, [c; d]) ->
    (T_equal p rows lim t u <= T_saturate p rows [t; u] lim + T_same_cell c d db + c_saturate)%N.
  (** Deciding equality costs the saturation with the two terms and the comparison of their
      cells in the outcome. *)
  Parameter equal_complexity :
    T_equal (spec_program s) rows lim t u ∈
      𝑂(saturate_cost B U (spec_program s) rows [t; u] lim +
        N.of_nat (cell_bits V.encode (D.canon db c)))
      for (B, U, s, rows, lim, t, u, st, db, c, d) |
        spec_ok s = true /\ rows_ok s rows = true /\ term_ok s t = true /\ term_ok s u = true /\
        saturate (spec_program s) rows [t; u] lim = (st, db, [c; d]) /\
        (D.ids db <= B)%N /\ D.unit db <= U.
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
  (** Every outcome of a saturation keeps each input row. *)
  Parameter saturate_keeps : forall (s : spec V.t) rows es lim st db cs r vs,
    spec_ok s = true -> rows_ok s rows = true -> forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) -> In (r, vs) rows ->
    row (D.view db) r (map Val vs) None.
End RUNNER_FACTS.
