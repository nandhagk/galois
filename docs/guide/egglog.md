# Egglog front end

`Galois.Front` turns an analysis written as Rocq inductive relations into a program for the
Egglog engine, and states what a run of that program computes. A client writes the analysis
once, as the inductive that defines its meaning. The command `Egglog` reads the inductive
and generates the program, the input rows, the table codes and the lemmas that connect the
engine's rows to the inductive. The reader of this guide knows Rocq inductives and modules.
It needs no earlier knowledge of Egglog.

A theorem about a run covers the program that the command read, so the program and the
meaning cannot drift apart. The theorems are stated in `theories/Front/*Sig.v`. Their proofs
are stubs that later sessions will fill, so this guide says "states" where it describes them.
The command, the generated lemmas and the runner are built and tested today.

## A first example

Reachability over a list of edges is an inductive with two constructors. The list of edges is
a parameter, and a premise `In (x, y) edges` reads one edge.

```coq
From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Derive.
Import List.ListNotations.

Inductive path (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | path_edge x y : In (x, y) edges -> path edges x y
  | path_step x y z : path edges x y -> In (y, z) edges -> path edges x z.

Egglog Path from path.
```

The command defines a module `Path`. Its main members are the following.

- `Path.program` is the engine program. It has one rule for each constructor.
- `Path.facts edges` lists the input rows, one row for each edge.
- `Path.path_code` is the code of the table that holds the rows of `path`.

The engine runs on values of one type. The test fixtures use `positive` values, which the
file `tests/Front/ExamplesTest.v` builds as follows. The functor applications name each
instance, as `docs/design/rules.md` requires.

```coq
Module ExampleValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End ExampleValue.

Module ExampleIndex := IndexCode ExampleValue.
Module ExampleJoin := JoinCode ExampleValue ExampleIndex.
Module ExampleDatabase := DatabaseCode ExampleValue ExampleIndex.
Module ExampleRun := RunCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase.
Module ExampleRunner :=
  RunnerCode ExampleValue ExampleIndex ExampleJoin ExampleDatabase ExampleRun.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.
```

The runner has three operations. `seed` loads a program and puts the input rows into a
database. `solve program rows limits` runs the program on the seed and returns a stop
reason with the final database. The reason is `Saturated` when no rule adds a row, and
`IterLimit` or `IdLimit` when a limit ended the run. `holds code row db` looks a row up in a
table. The edges 1 to 2, 2 to 3 and 3 to 4 give a path from 1 to 4 and no path back.

```coq
Local Open Scope positive_scope.

Definition chain : list (positive * positive) := [(1, 2); (2, 3); (3, 4)].

Definition chain_result : ExampleDatabase.t :=
  snd (ExampleRunner.solve Path.program (Path.facts chain) example_limits).

Example chain_saturates :
  fst (ExampleRunner.solve Path.program (Path.facts chain) example_limits) = Saturated.
Proof. vm_compute. reflexivity. Qed.

Example path_follows_three_edges :
  ExampleRunner.holds Path.path_code [1; 4] chain_result = true.
Proof. vm_compute. reflexivity. Qed.

Example edges_are_directed :
  ExampleRunner.holds Path.path_code [4; 1] chain_result = false.
Proof. vm_compute. reflexivity. Qed.
```

A lookup reads the database that the run produced. It answers `true` for a derived row. For
a run that saturated, a `false` answer says that the row is not derived. For a run that
stopped at a limit, a `false` answer says that the run has not derived the row yet, and a later iteration may derive it.

The generated lemma `Path.path_spec` connects the rows to the inductive. It says that
`path edges x y` holds exactly when the row `[x; y]` of the table `Path.path_code` is derived
from the input rows. A derived row is a row in the least set that contains the input rows and
is closed under the clauses of `Path.spec`. This is the definition `derived` in
`theories/Front/Spec.v`.

```coq
Example path_gives_derived_row :
  derived (fun _ _ => None) Path.spec (Path.inputs chain) Path.path_code [1; 4].
Proof.
  apply (proj1 (Path.path_spec (fun _ _ => None) chain 1 4)).
  apply (path_step chain 1 3 4).
  - apply (path_step chain 1 2 3).
    + apply path_edge. simpl. auto.
    + simpl. auto.
  - simpl. auto.
Qed.
```

The first argument of `path_spec` is the primitive function of the program. A program
without primitives takes any function, and the lemma holds for all of them.

A client that wants to know whether the program is inside the range of a theorem checks three
conditions by computation. `spec_ok` checks the sorts of the lowered program, `relational`
checks that the program has no rewrites, and `rows_ok` checks that each input row belongs to an
input table and has its arity.

```coq
Example path_is_covered :
  spec_ok Path.spec = true /\ relational Path.spec = true /\
  rows_ok Path.spec (Path.facts chain) = true.
Proof. vm_compute. auto. Qed.
```

## How the command reads an inductive

The command `Egglog P from R1 .. Rn.` reads the inductive relations `R1` to `Rn` together, so
that they may refer to each other. The module `P` receives the definitions that the next
sections describe. The reading follows these rules.

**Sorts.** Each argument of a relation has a sort that comes from its Rocq type. An argument of
type `positive` is a value. An argument whose type is an inductive datatype, such as `term`
below, is a class, the identifier of an equivalence class of the engine's e-graph. Any other
type is an error.

**Inputs.** A premise `In e (field q)` or `In e q` reads an input list. Here `q` is a parameter
of the relation, `field` is a record projection of `q`, and `e` is a pair or a constructor of a
datatype. A list of pairs is one input table with one row for each pair. A list of constructors
gets one input table for each constructor that a premise names, and each element is a row of
the table of its constructor. Rows from the client go into these input tables, and the engine derives the rows of all the others.

**Clauses.** Each constructor of a relation is a clause. Its premises are the clause body and
its conclusion is the head. A premise `Ri ..` of a relation over values reads that relation's
table. Binders of data are numbered as variables in binder order, and binders of propositions
are premises.

**Equations.** A relation `R t u` whose two indices have the same datatype is an equation. It
gets no table of its own, because the constructors of the datatype are its tables. The
constructors of the relation that state reflexivity, symmetry, transitivity or congruence of a
datatype constructor are the e-graph's own laws, so they give no clause. Every other
constructor is a clause. It is a union when the premises bind every variable that its two
sides use, and a rewrite otherwise.

**Generated names and numbers.** Every table code and every variable number is generated. A
reader of the generated module finds the codes as constants named after the table. A client
never writes a code or a variable number (see the rule in `docs/design/rules.md`).

## Equations

An equational relation describes a congruence over terms. The datatype `term` below has two
constructors, and `equiv` is its equality. The first four constructors of `equiv` are the
closure laws. The constructor `equiv_merge` is a union, because its premise binds `x` and `y`.
The constructor `equiv_comm` is a rewrite, because no premise binds `a` or `b`. The engine
applies the rewrite to every class that contains an `Add a b` node.

```coq
Inductive term : Type :=
  | Num (n : positive)
  | Add (a b : term).

Inductive equiv (merges : list (positive * positive)) : term -> term -> Prop :=
  | equiv_refl a : equiv merges a a
  | equiv_sym a b : equiv merges a b -> equiv merges b a
  | equiv_trans a b c : equiv merges a b -> equiv merges b c -> equiv merges a c
  | equiv_add a a' b b' : equiv merges a a' -> equiv merges b b' ->
      equiv merges (Add a b) (Add a' b')
  | equiv_merge x y : In (x, y) merges -> equiv merges (Num x) (Num y)
  | equiv_comm a b : equiv merges (Add a b) (Add b a).

Egglog Terms from equiv.

Example one_union_and_one_rewrite :
  length (clauses Terms.spec) = 2%nat /\ length Terms.rewrites = 1%nat.
Proof. vm_compute. auto. Qed.
```

The module `Terms` has the tables `Terms.input1_code` for the input list `merges` (parameter 1),
`Terms.Num_code` and `Terms.Add_code`. It also has the encoder
`Terms.encode_term`, which maps a term to the engine's expression for it, and the lemma
`Terms.equiv_congruent`. The lemma says that `equiv merges t u` gives
`congruent prim Terms.spec (Terms.inputs merges) (Terms.encode_term t) (Terms.encode_term u)`.
The relation `congruent` of `theories/Front/Spec.v` is the least congruence that contains each
instance of a clause whose body holds in the input rows.

Steensgaard's unification-based pointer analysis is an equational relation of the same kind.
The file `theories/Clients/SteensgaardSig.v` defines the terms `Cell a` and `Deref t`, where
`Deref (Cell x)` stands for what the pointer `x` points to. The equation `pointer_congruence`
has the four closure laws and one union for each kind of input. An address constraint `Addr x a`
equates `Deref (Cell x)` with `Cell a`, and a copy `Copy x y` equates `Deref (Cell x)` with
`Deref (Cell y)`. All its clauses are unions, so the program has no rewrites and is ground.

```text
Inductive pointer_term :=
  | Cell (address : positive)
  | Deref (pointer : pointer_term).

Inductive pointer_congruence (q : pointer_input) : pointer_term -> pointer_term -> Prop :=
  | Cong_refl : forall t, pointer_congruence q t t
  ...
  | Cong_addr : forall x a, In (Addr x a) (constraints q) ->
      pointer_congruence q (Deref (Cell x)) (Cell a)
  | Cong_copy : forall x y, In (Copy x y) (constraints q) ->
      pointer_congruence q (Deref (Cell x)) (Deref (Cell y))
  ...

Egglog Unification from pointer_congruence.
```

Two terms are equal in a run when the e-graph puts them in one class. The runner's `holds`
reads relations over values, so a client reads the classes of an equation through the
predicates `represents` and `same` of the engine's model (`theories/Egglog/Model.v`). The
Steensgaard client does this in `points_spec`.

Andersen's inclusion-based analysis is the relational counterpart. `Egglog MayPoints from
may_points.` in `theories/Clients/AndersenSig.v` reads the inductive with five constructors
over a record whose field `constraints` is a list of constructors, so each constructor of
`pointer_constraint` is an input table. The tests `PointsToTests` in
`tests/Front/ExamplesTest.v` run the same shape on a six-line program.

## Primitives

A primitive is a function on values that the engine calls while it runs a rule, such as
addition on `positive`. The command `Egglog Primitives P f1 .. fn.` defines a module `P` with
the constants `P.<fi>_code` and the function `P.prim`. The function `P.prim` takes a code and
a list of values and returns the result of the function with that code. Each function takes
one to three arguments of type `positive` and returns a `positive`. A program uses the set
with `Egglog Q from R1 .. Rn with P.`

```coq
Definition add_pos (x y : positive) : positive := Pos.add x y.
Definition double (x : positive) : positive := xO x.

Egglog Primitives Ops add_pos double.

(** [shifted offsets x y] says that [y] is [x] plus an offset, or twice that. *)
Inductive shifted (offsets : list (positive * positive)) : positive -> positive -> Prop :=
  | shifted_by x k : In (x, k) offsets -> shifted offsets x (add_pos x k)
  | shifted_double x k : In (x, k) offsets -> shifted offsets x (double (add_pos x k)).

Egglog Shifts from shifted with Ops.
```

The call to a registered function in a conclusion becomes a primitive pattern. A run needs a
value module whose `prim` is the one of the set. The fixtures above use a `prim` that always
returns `None`.

```coq
Module OpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Ops.prim.
  Definition merge (_ : positive) := Pos.max.
End OpsValue.

Module OpsIndex := IndexCode OpsValue.
Module OpsJoin := JoinCode OpsValue OpsIndex.
Module OpsDatabase := DatabaseCode OpsValue OpsIndex.
Module OpsRun := RunCode OpsValue OpsIndex OpsJoin OpsDatabase.
Module OpsRunner := RunnerCode OpsValue OpsIndex OpsJoin OpsDatabase OpsRun.

Definition offsets : list (positive * positive) := [(1, 2)].

Definition shifted_result : OpsDatabase.t :=
  snd (OpsRunner.solve Shifts.program (Shifts.facts offsets) example_limits).

(** The offset 2 takes 1 to 3, and doubling gives 6. *)
Example shifts_apply_the_primitives :
  OpsRunner.holds Shifts.shifted_code [1; 3] shifted_result = true /\
  OpsRunner.holds Shifts.shifted_code [1; 6] shifted_result = true /\
  OpsRunner.holds Shifts.shifted_code [1; 4] shifted_result = false.
Proof. vm_compute. auto. Qed.
```

A premise written as an equation, such as `add_pos x y = z`, is read as a primitive premise.
The command cannot yet prove the fire lemma of such a clause, and it stops with the message
that the Elpi command `Egglog` failed without a specific error. The example above puts the
call in the conclusion. This is a defect of the front end, and the limits below list it.

## The generated module

For a command `Egglog P from R1 .. Rn` the module `P` has the following members.

| Member | Meaning |
| --- | --- |
| `spec` | The specification of the constructors. It lists the tables, the input tables and one clause for each constructor (`theories/Front/Spec.v`). |
| `program` | The engine program that `spec` lowers to. |
| `rewrites` | The rewrites among the clauses. It is empty for a relational program. |
| `facts` | A function from the parameters of the first relation to the list of input rows. |
| `inputs` | The input rows as a relation `positive -> list positive -> Prop`, for the lemmas. |
| `relation` | The meaning of each table, as a relation on rows. |
| `<Table>_code` | One constant for each table. A relation has `<R>_code`, a constructor table has `<Constructor>_code`, and an input list that is a parameter has `input<i>_code`. |
| `encode_<T>` | One encoder for each datatype `T`, which maps a value of `T` to the engine's expression. |
| `<Constructor>_fires` | One lemma for each constructor, which says that the clause derives the conclusion from the premises. The command adds each to the hint database `egglog_fire`. |
| `closed` | The derived rows are closed under the clauses of `relation`. It is the converse half of the glue. |
| `<R>_spec` | For a relation over values, the equivalence of `R` with its derived row, as in `Path.path_spec`. |
| `<R>_congruent` | For an equational relation, the implication from `R t u` to the congruence of the encodings of `t` and `u`. |

Every lemma is checked, so a wrong reading stops the command. The proofs use the tactics of
`theories/Front/Derive.v`, for example `egglog_complete` and `egglog_closed`.

## The theorems

Five signatures state what a run guarantees. Each theorem takes the conditions of its kind as hypotheses. These are `spec_ok` and
`rows_ok`, together with `relational`, `ground` or `lattice_spec`, and each is stated over any value module that satisfies the
engine's laws. The proofs are stubs, so none of these theorems is proved yet.

**Relational exactness** (`RelationalSig.v`). For a relational specification, `solve_sound`
says that every row of every outcome is derived from the input rows, and `solve_complete`
says that a saturated outcome holds every derived row. So a saturated run computes exactly
the derived rows. The lemma `solve_saturates` says that a limit of at least
`2 * herbrand + 3` iterations saturates a program that has no primitives. Together with
`Path.path_spec`, these give the exactness of `path` itself. The lemma `holds_spec` says that
`holds` finds a row exactly when the database has it.

**Ground equational exactness** (`GroundSig.v`). For a ground specification, a specification
whose clauses are all unions over input rows, `solve_sound` says that two represented terms in
one class are congruent, and `solve_complete` says that two represented congruent terms share
a class in a saturated outcome. The lemma `solve_builds` says that a saturated outcome
represents both sides of every instance, and `solve_saturates` says that enough iterations and
identifiers saturate the run. With `<R>_congruent`, these give the exactness of an equational
inductive such as Steensgaard's.

**Soundness of rewriting** (`RewriteSig.v`). For a specification with rewrites, the lemma
`saturate_sound` says that two represented terms in one class have the same meaning in every
model of the specification. The theorem states soundness. Saturation with rewrites need not
terminate and need not find every congruence, so the theorem makes no completeness claim.

**Lattice tables** (`LatticeSig.v`). A lattice table keeps, for each key, the merge of the
values that the clauses assign to it. The lemma `solve_sound` says that a stored value is a
merge of assigned values, and `solve_complete` says that every assigned value is below the
stored value in a saturated outcome. The command `Egglog` does not yet derive lattice tables,
so this theorem covers specifications that a client writes by hand.

**The exact model** (`CongruenceRefSig.v`). The lemma `exact_model` says that a ground
specification has a model of its input rows in which two terms are equal exactly when they are
congruent. The ground theorem uses it to read equalities of classes as congruences.

The clients state their own results in terms of these. For example, Andersen's `solve_exact`
says that a saturated solve answers `may_points q x a` exactly (`AndersenSig.v`).

## Limits

- The engine has one value type, `positive`. An argument of any other type is an error.
- A primitive has one to three arguments. A primitive appears in the conclusion of a clause.
  An equation premise `f x = y` is read, but the command fails on the lemma that it must
  generate (see Primitives).
- The engine has no rulesets and no `run-schedule`. It has no `subsume` and no `delete`, and
  its containers cannot hold class identifiers. These features wait for engine support after
  stage 2, so the command cannot express them.
- The command derives no lattice tables, so a client writes those specifications by hand.
- The theorems of the previous section are stated and not yet proved.
- A run that stops at `IterLimit` or `IdLimit` has no completeness guarantee, so a client that
  needs the exact answer checks for `Saturated`.
