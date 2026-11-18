(** * Running derived programs

    A derived program runs on a database that holds its input rows. [seed] loads the program
    with its planned slots and puts each input row, [solve] runs the program on the seed, and
    [holds] looks a row up. [saturate] adds terms to the seed before the run, and [equal] says
    whether the run puts two terms in one class. The specification conditions say which
    programs and rows the theorems cover. [spec_ok] checks the sorts of the lowered program,
    and [rows_ok] checks that each input row belongs to an input table and has its arity.
    For example, [solve MayPoints.program (MayPoints.facts q) lim] is Andersen's analysis of
    [q].

    Builds on: the specifications, their lowering, and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

(** * Conditions *)

(** The input rows of a list, as a relation. *)
Definition rows_in {V} (rows : list (positive * list V)) (r : positive) (vs : list V) : Prop :=
  In (r, vs) rows.

(** The lowered program of a specification is well sorted. *)
Definition spec_ok {V} (s : spec V) : bool := check_program (spec_program s).

(** The lowered program of a specification is relational. *)
Definition relational {V} (s : spec V) : bool := relational_fragment (spec_program s).

(** A term to add is well sorted: each application is of a constructor table of the
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

(** Each row belongs to an input table of the specification and has the arity of its
    declaration. *)
Definition rows_ok {V} (s : spec V) (rows : list (positive * list V)) : bool :=
  forallb (fun row =>
    existsb (Pos.eqb (fst row)) (inputs s) &&
    existsb (fun d => Pos.eqb (name d) (fst row) &&
      Nat.eqb (length (arg_sorts d)) (length (snd row)) &&
      forallb (fun s => match s with SVal => true | SId => false end) (arg_sorts d))
      (tables s)) rows.

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
  (** A row holds when its lookup finds it. *)
  Parameter holds_unfold : forall r vs db,
    holds r vs db = match fst (D.lookup r (map Val vs) db) with
                    | Some _ => true
                    | None => false
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
