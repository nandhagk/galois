(** * Running derived programs

    [seed] loads a program with its planned slots and puts each input row, [solve] runs the
    program on the seed, and [holds] says whether a lookup finds a row without output.
    [saturate] also adds terms before the run, and [equal] says whether the run puts two terms
    in one class. The timed runner [RunnerT] is in [RunnerTime.v], and the facts that the
    theorems use are in [RunnerFacts.v].
    For example, [holds MayPoints.may_points_code [x; a] db] says whether [x] may point to [a]
    in the result [db] of [solve MayPoints.program (MayPoints.facts q) lim].

    Builds on: the runner signature and the database and run operations. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig Syntax Model IndexSig JoinSig DatabaseSig RunSig.
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
    | Some None => true
    | _ => false
    end.
  Fixpoint add_term (e : @expr V.t) (db : D.t) : cell V.t * D.t :=
    match e with
    | ELit v => (Val v, db)
    | EApp f args =>
        let '(cs, db1) :=
          (fix go (args : list (@expr V.t)) (db : D.t) : list (cell V.t) * D.t :=
             match args with
             | [] => ([], db)
             | a :: rest =>
                 let '(c, db1) := add_term a db in
                 let '(cs, db2) := go rest db1 in
                 (c :: cs, db2)
             end) args db in
        let '(i, db2) := D.make f cs db1 in
        (Id i, db2)
    end.
  Fixpoint add_terms (es : list (@expr V.t)) (db : D.t) : list (cell V.t) * D.t :=
    match es with
    | [] => ([], db)
    | e :: rest =>
        let '(c, db1) := add_term e db in
        let '(cs, db2) := add_terms rest db1 in
        (c :: cs, db2)
    end.
  Definition saturate (p : program V.t) (rows : list (positive * list V.t))
      (es : list (@expr V.t)) (lim : limits) : stop * D.t * list (cell V.t) :=
    let '(cs, db) := add_terms es (seed p rows) in
    let '(st, db') := R.run p (R.plan p) lim db in
    (st, db', cs).
  Definition same_cell (a b : cell V.t) (db : D.t) : bool :=
    match a, b with
    | Id i, Id j => Pos.eqb (fst (D.find i db)) (fst (D.find j db))
    | Val v, Val w => V.eqb v w
    | _, _ => false
    end.
  Definition equal (p : program V.t) (rows : list (positive * list V.t)) (lim : limits)
      (t u : @expr V.t) : bool :=
    match saturate p rows [t; u] lim with
    | (_, db, [c; d]) => same_cell c d db
    | _ => false
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
                    | Some None => true
                    | _ => false
                    end.
  Proof.
    reflexivity.
  Qed.
  Lemma add_term_lit : forall v db, add_term (ELit v) db = (Val v, db).
  Proof.
    reflexivity.
  Qed.
  Lemma add_terms_nil : forall db, add_terms [] db = ([], db).
  Proof.
    reflexivity.
  Qed.
  Lemma add_terms_cons : forall e es db,
    add_terms (e :: es) db =
      let '(c, db1) := add_term e db in
      let '(cs, db2) := add_terms es db1 in
      (c :: cs, db2).
  Proof.
    reflexivity.
  Qed.
  (** The local loop of [add_term] over the arguments is [add_terms]. *)
  Lemma add_term_app : forall f args db,
    add_term (EApp f args) db =
      let '(cs, db1) := add_terms args db in
      let '(i, db2) := D.make f cs db1 in
      (Id i, db2).
  Proof.
    intros f args db.
    simpl.
    assert (Hargs : forall db0,
      (fix go (args : list (@expr V.t)) (db : D.t) : list (cell V.t) * D.t :=
         match args with
         | [] => ([], db)
         | a :: rest =>
             let '(c, db1) := add_term a db in
             let '(cs, db2) := go rest db1 in
             (c :: cs, db2)
         end) args db0 = add_terms args db0).
    { induction args as [| a rest IHrest]; intros db0.
      - reflexivity.
      - simpl. destruct (add_term a db0) as [c db1]. rewrite IHrest. reflexivity. }
    rewrite Hargs.
    reflexivity.
  Qed.
  Lemma saturate_unfold : forall p rows es lim,
    saturate p rows es lim =
      let '(cs, db) := add_terms es (seed p rows) in
      let '(st, db') := R.run p (R.plan p) lim db in
      (st, db', cs).
  Proof.
    reflexivity.
  Qed.
  Lemma same_cell_unfold : forall a b db,
    same_cell a b db =
      match a, b with
      | Id i, Id j => Pos.eqb (fst (D.find i db)) (fst (D.find j db))
      | Val v, Val w => V.eqb v w
      | _, _ => false
      end.
  Proof.
    reflexivity.
  Qed.
  Lemma equal_unfold : forall p rows lim t u,
    equal p rows lim t u =
      match saturate p rows [t; u] lim with
      | (_, db, [c; d]) => same_cell c d db
      | _ => false
      end.
  Proof.
    reflexivity.
  Qed.
End Runner.
