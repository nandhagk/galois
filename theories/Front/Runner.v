(** * Running derived programs

    [seed] loads a program with its planned slots and puts each input row, [solve] runs the
    program on the seed, and [holds] reads the lookup of a row.
    For example, [holds 1 [x; a] (snd (solve Andersen.program (Andersen.facts q) lim))] says
    whether [x] may point to [a].

    Builds on: the runner signature and the database and run operations. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import RunnerSig.

Import List.ListNotations.

Module RunnerCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: RUNNER_OPS V I J D R.
  (** Put one input row as a row of values without output. *)
  Definition put_row (db : D.t) (row : positive * list V.t) : D.t :=
    D.put (fst row) (map Val (snd row)) None db.
  Definition seed (p : program V.t) (rows : list (positive * list V.t)) : D.t :=
    fold_left put_row rows (R.load p (R.plan p)).
  Definition solve (p : program V.t) (rows : list (positive * list V.t)) (lim : limits) :
      stop * D.t :=
    R.run p (R.plan p) lim (seed p rows).
  Definition holds (r : positive) (vs : list V.t) (db : D.t) : bool :=
    match fst (D.lookup r (map Val vs) db) with
    | Some _ => true
    | None => false
    end.
End RunnerCode.

Module Runner (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: RUNNER V I J D R.
  Include RunnerCode V I J D R.
  Lemma seed_unfold : forall p rows,
    seed p rows = fold_left (fun db row => D.put (fst row) (map Val (snd row)) None db) rows
      (R.load p (R.plan p)).
  Proof.
    reflexivity.
  Qed.
  Lemma solve_unfold : forall p rows lim,
    solve p rows lim = R.run p (R.plan p) lim (seed p rows).
  Proof.
    reflexivity.
  Qed.
  Lemma holds_unfold : forall r vs db,
    holds r vs db = match fst (D.lookup r (map Val vs) db) with
                    | Some _ => true
                    | None => false
                    end.
  Proof.
    reflexivity.
  Qed.
End Runner.
