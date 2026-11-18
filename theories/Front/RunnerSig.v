(** * Running derived programs

    A derived program runs on a database that holds its input rows. [seed] loads the program
    with its planned slots and puts each input row, [solve] runs the program on the seed, and
    [holds] looks a row up. The specification conditions say which programs and rows the
    theorems cover: [spec_ok] checks the sorts of the lowered program, and [rows_ok] checks
    that each input row belongs to an input table and has its arity.
    For example, [solve Andersen.program (Andersen.facts q) lim] is Andersen's analysis of
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
End RUNNER_LAWS.

Module Type RUNNER (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) := RUNNER_OPS V I J D R <+ RUNNER_LAWS V I J D R.
