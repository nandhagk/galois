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
stopped at a limit, a `false` answer says that the run has not derived the row yet, and a later
iteration may derive it.

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
conditions by computation. `spec_ok` checks the sorts of the lowered program, and it checks
that every constructor pattern names a constructor table and every lattice premise or head
names a lattice table. `relational` checks that every table is a relation and every rule only
computes values and puts rows. `rows_ok` checks that each input row belongs to an input
relation and has the arity of the first declaration of its table, with a value at every
argument. The command already stops when `spec_ok` fails, so a derived program always passes
it.

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
type `positive` or of a registered value type (see "Value types") is a value. An argument
whose type is an inductive datatype, such as `term` below, is a class, the identifier of an
equivalence class of the engine's e-graph. Any other type is an error.

**Inputs.** A premise `In e (field q)` or `In e q` reads an input list. Here `q` is a parameter
of the relation, `field` is a record projection of `q`, and `e` is a pair or a constructor of a
datatype. A list of pairs is one input table with one row for each pair. A list of constructors
gets one input table for each constructor that a premise names, and each element is a row of
the table of its constructor. Rows from the client go into these input tables, and the engine
derives the rows of all the others.

**Clauses.** Each constructor of a relation is a clause. Its premises are the clause body and
its conclusion is the head. A premise `Ri ..` of a relation over values reads that relation's
table. Binders of data are numbered as variables in binder order, and binders of propositions
are premises. A premise `f x1 .. xn = y`, where `f` is a primitive (see Primitives), computes a
value.

**Equations.** A relation `R t u` whose two indices have the same datatype is an equation. It
gets no table of its own, because the constructors of the datatype are its tables. The
constructors of the relation that state reflexivity, symmetry, transitivity or congruence of a
datatype constructor are the e-graph's own laws, so they give no clause. Every other
constructor is a clause. It is a union when its premises bind every variable that its two sides
use, and a rewrite otherwise. A relation premise or an input premise binds the variables of its
arguments outside primitive calls, and an equation premise binds its result when its arguments
are bound.

**Rules.** Each clause becomes one engine rule. The premises become the query, and the head
becomes actions that build its terms, then put its row or join its two sides. A rewrite also
matches its left side in the query, and its last action joins the matched class with the built
right side. An equation premise whose result no other premise binds becomes an action that
computes the result. Every other primitive call in a premise becomes a check that follows the
relation and input atoms of the query.

**Generated names and numbers.** Every table code and every variable number is generated. The
codes are constants named after their tables, and the generated lemmas refer to these constants.
A client never writes a code or a variable number (see the rule in `docs/design/rules.md`).

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

Definition is_union (c : clause positive) : bool :=
  match head c with Unify _ _ => true | _ => false end.

Example one_union_and_one_rewrite :
  map is_union (clauses Terms.spec) = [true; false].
Proof. vm_compute. reflexivity. Qed.
```

The module `Terms` has the tables `Terms.merges_code` for the input list `merges`,
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

Two terms are equal in a run when the e-graph puts them in one class. The runner's
`equal program rows limits t u` adds the encodings `t` and `u` to the seed, runs the program
and says whether their classes are one. Inside proofs, a client reads the classes through the
predicates `represents` and `same` of the engine's model (`theories/Egglog/Model.v`), as the
Steensgaard client does in `points_spec`.

```coq
Example merged_numbers_are_equal :
  ExampleRunner.equal Terms.program (Terms.facts [(1, 2)]) example_limits
    (Terms.encode_term (Add (Num 1) (Num 3))) (Terms.encode_term (Add (Num 3) (Num 2))) = true.
Proof. vm_compute. reflexivity. Qed.
```

The input merges 1 with 2, and commutativity swaps the sum, so the two sums share a class.

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
one to three arguments and returns a result. Their types are `positive` or registered value
types. A program uses the set
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

A premise written as an equation, such as `add_pos x k = y`, computes `y` when no relation or
input premise binds `y`. Otherwise it checks that the call gives `y`. A call inside a premise
argument, such as `fib (Pos.succ n) b`, is a check as well, so its arguments must be variables
that a relation or input premise binds. The command stops when a clause breaks these rules.

```coq
(** [moved offsets x y] says that [y] is [x] plus an offset. *)
Inductive moved (offsets : list (positive * positive)) : positive -> positive -> Prop :=
  | move x k y : In (x, k) offsets -> add_pos x k = y -> moved offsets x y.

Egglog Moves from moved with Ops.

Example moves_compute_their_targets :
  OpsRunner.holds Moves.moved_code [1; 3]
    (snd (OpsRunner.solve Moves.program (Moves.facts offsets) example_limits)) = true.
Proof. vm_compute. reflexivity. Qed.
```

A call in the right side of a rewrite computes its value when the rule fires, so a rewrite can
fold constants. The tests `TermTests` in `tests/Front/PrimitiveTest.v` fold `2 * 3` into `6`
and join `2 * (x + 3)` with `6 + 2 * x`, as in the egglog tutorial.

## Value types

The engine runs on `positive` values. A relation over another type, such as `Z`, `N`, `bool`
or `string`, needs an encoder of that type into `positive`. An encoder is a module of the
module type `ENCODE` in `theories/Front/EncodeSig.v`. It has the type `t`, the function
`encode : t -> positive`, the function `decode : positive -> option t` and the lemma
`decode_encode : forall x, decode (encode x) = Some x`. The lemma makes `encode` injective, so
two values are equal exactly when their encodings are equal.

The command `Egglog Value T M.` registers the module `M` as the encoder of the type `T`. It
stops when `M.encode` or `M.decode` has another type, when `T` is `positive`, and when `T`
already has an encoder. A registered type is a value, as `positive` is. The file
`theories/Front/Encode.v` registers `ZEncode` for `Z`, `NEncode` for `N`, `BoolEncode` for
`bool` and `StringEncode` for `string`. A client writes the module of any other type in the
same way, and the encoder needs a time function for each function, as the other code of the
library does.

```coq
From Stdlib Require Import ZArith.
From Argent Require Import Time.
From Galois.Front Require Import EncodeSig Encode.

Inductive color : Type :=
  | Red
  | Green
  | Blue.

Module ColorEncode <: ENCODE.
  Definition t : Type := color.
  Definition encode (c : color) : positive :=
    match c with
    | Red => 1
    | Green => 2
    | Blue => 3
    end.
  Definition decode (p : positive) : option color :=
    match p with
    | 1 => Some Red
    | 2 => Some Green
    | 3 => Some Blue
    | _ => None
    end.
  TimeFun encode.
  TimeFun decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof. intros [| |]; reflexivity. Qed.
End ColorEncode.

Egglog Value color ColorEncode.
```

The command encodes a value of a registered type wherever it gives the engine a value. A row of
`facts` holds `ZEncode.encode x` for an input `x : Z`, and a literal `c : Z` in a clause becomes
the literal `ZEncode.encode c`. The generated lemmas state rows the same way, so
`Offsets.offset_spec` below relates `offset steps x y` to the derived row
`[ZEncode.encode x; ZEncode.encode y]`. A value of type `positive` has no encoder and no
wrapper, so the programs and lemmas over `positive` keep their shape.

A primitive may take registered types as well. The function `P.prim` of a set decodes each
argument, calls the function and encodes the result. It has no result when an argument does not
decode. The following program adds integers, and the run reads its rows through the encoder.

```coq
Egglog Primitives IntOps Z.add.

(** [offset steps x y] says that [y] is [x] plus a step of the list. *)
Inductive offset (steps : list (Z * Z)) : Z -> Z -> Prop :=
  | offset_by x k y : In (x, k) steps -> Z.add x k = y -> offset steps x y.

Egglog Offsets from offset with IntOps.

Module IntOpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := IntOps.prim.
  Definition merge (_ : positive) := Pos.max.
End IntOpsValue.

Module IntOpsIndex := IndexCode IntOpsValue.
Module IntOpsJoin := JoinCode IntOpsValue IntOpsIndex.
Module IntOpsDatabase := DatabaseCode IntOpsValue IntOpsIndex.
Module IntOpsRun := RunCode IntOpsValue IntOpsIndex IntOpsJoin IntOpsDatabase.
Module IntOpsRunner :=
  RunnerCode IntOpsValue IntOpsIndex IntOpsJoin IntOpsDatabase IntOpsRun.

Local Open Scope Z_scope.

Definition steps : list (Z * Z) := [(1, -3)].

Example negative_step_is_reached :
  IntOpsRunner.holds Offsets.offset_code [ZEncode.encode 1; ZEncode.encode (-2)]
    (snd (IntOpsRunner.solve Offsets.program (Offsets.facts steps) example_limits)) = true.
Proof. vm_compute. reflexivity. Qed.
```

The command adds the lemma `decode_encode` to the hint database `egglog_decode` and defines
the lemma `<M>_encode_inj`, which says that `encode` is injective, in the hint database
`egglog_inj`. The tactics that prove the generated lemmas use both. A relation of an
unregistered type stops the command with a message that names the type.

## The generated module

For a command `Egglog P from R1 .. Rn` the module `P` has the following members.

| Member | Meaning |
| --- | --- |
| `spec` | The specification of the constructors. It lists the tables, the input tables and one clause for each constructor (`theories/Front/Spec.v`). |
| `program` | The engine program that `spec` lowers to. |
| `facts` | A function from the parameters of the first relation to the list of input rows. |
| `inputs` | The input rows as a relation `positive -> list positive -> Prop`, for the lemmas. |
| `relation` | The meaning of each table, as a relation on rows. |
| `<Table>_code` | One constant for each table. A relation has `<R>_code`, a constructor table has `<Constructor>_code`, and an input list that is a parameter has `<parameter>_code`. |
| `encode_<T>` | One encoder for each datatype `T`, which maps a value of `T` to the engine's expression. |
| `<Constructor>_fires` | One lemma for each constructor, which says that the clause derives the conclusion from the premises. The command adds each to the hint database `egglog_fire`. |
| `closed` | The derived rows are closed under the clauses of `relation`. It is the converse half of the glue. |
| `<R>_spec` | For a relation over values, the equivalence of `R` with its derived row, as in `Path.path_spec`. |
| `<R>_congruent` | For an equational relation, the implication from `R t u` to the congruence of the encodings of `t` and `u`. |

Every lemma is checked, so a wrong reading stops the command. The proofs use the tactics of
`theories/Front/Derive.v`, for example `egglog_complete` and `egglog_closed`.

## The theorems

Eight signatures state what the lowering, the runner and a run guarantee. Each theorem about
a run takes the conditions of its kind as hypotheses. These are `spec_ok` and `rows_ok`,
together with `relational`, `ground` or `lattice_spec`, and each is stated over any value
module that satisfies the engine's laws. The proofs are stubs, so none of these theorems is
proved yet.

**The lowering** (`LowerSig.v`). The lemma `lower_sound` says that a row that a well-sorted
relational program derives from input rows is a derived row, and `lower_complete` says the
converse. The lemma `lower_closed` says that a view that the rules of a well-sorted
specification close, and whose relation rows have no output, holds every row derived from its
own rows. The lemma `lower_valid` says that a model of a specification that passes `spec_ok`
validates its rules. A head whose pattern has no meaning holds in every model, because an
engine rule stops at a failed primitive. Laws about single patterns relate their queries and
actions to their values, their meanings in a model and the terms that a view represents, and
laws about bodies say that the query of a body whose premises hold matches.

**The runner** (`RunnerSig.v`). The facts of the runner say that the seed holds exactly the
input rows and that the run contracts of the engine apply to it. A model of the input rows
satisfies the seed, every outcome keeps the input rows, and the lemma `holds_spec` says that
`holds` finds a row exactly when the database has it without output. The timed runner states
that seeding pays for planning, loading and each put (`T_seed_le`), and that a solve pays for
its seed, planning and the run (`T_solve_split`). Its big-O bounds count the planning, the
loading, the work of the input rows and of the added terms, and the rounds of the run, at the
unit and the identifier width of the databases (`seed_complexity`, `solve_complexity` and
`saturate_complexity`). Each put and each constructor pays its share of the deferred rebuild
at the unit bound, and the run spends that credit. A lookup is linear in its key at the unit
of the database (`holds_complexity`), and comparing two classes pays for two finds
(`same_cell_complexity`).

**Relational exactness** (`RelationalSig.v`). For a relational specification, `solve_sound`
says that every row of every outcome is derived from the input rows, and `solve_complete`
says that a saturated outcome holds every derived row. So a saturated run computes exactly
the derived rows. The lemma `solve_saturates` says that a limit of at least
`2 * herbrand + 3` iterations saturates a program that has no primitives. Together with
`Path.path_spec`, these give the exactness of `path` itself.

**Ground equational exactness** (`GroundSig.v`). A ground specification has only unions of
two constructor terms, whose premises read input rows and primitives and bind every variable
of the clause outside primitive calls. For a ground specification, `solve_sound` says that two
represented terms in one class are congruent, and `solve_complete` says that two represented
congruent terms share a class in a saturated outcome. The lemma `solve_builds` says that a
saturated outcome represents both sides of every instance. With `<R>_congruent`, these give
the exactness of an equational inductive such as Steensgaard's.

**Equality saturation** (`RewriteSig.v`). For a specification that passes `spec_ok`, with
input rows that pass `rows_ok` and terms that pass `term_ok`, the lemma `saturate_sound` says
that two represented terms in one class of any outcome have the same meaning in every model of
the specification and its input rows. The lemma `saturate_represents` says that the
cell of each added term represents it, so `equal_sound` says that `equal` answers `true` only
for terms with the same meaning in every model. At saturation, `saturate_closed` says that a
rewrite step from a represented term reaches a term of the same class.

**Lattice tables** (`LatticeSig.v`). A lattice table keeps, for each key, the merge of the
values that the clauses assign to it. A lattice specification has no constructor table, and
its clauses read relations and primitives and derive rows or assign values. The lemma
`solve_sound` says that a stored value is a merge of assigned values, and `solve_complete`
says that every assigned value is below the stored value in a saturated outcome. The command
`Egglog` does not yet derive lattice tables, so this theorem covers specifications that a
client writes by hand.

**The exact model** (`CongruenceRefSig.v`). The lemma `exact_model` says that a ground
specification has a model of its input rows in which two terms are equal exactly when they are
congruent. The ground theorem uses it to read equalities of classes as congruences. The model
comes from the reference closure of `ClosureSig.v`, whose normal forms the tests in
`tests/Front/ClosureTest.v` run.

**Cheapest terms** (`ExtractionSig.v`). The function `cheapest` extracts a checked DAG for a
class and decodes it, and it returns nothing when the engine extracts nothing. The engine keeps
one best entry for each class (`best_nodup`), so the extracted DAG has the least cost of the
class. The lemma `cheapest_represents`
says that a returned term is represented by the class, and `cheapest_optimal` says that no
term that the class represents costs less. Decoding unfolds the DAG into a tree, which can be
exponentially larger than the DAG, so `decode_complexity` and `cheapest_complexity` count the
nodes of the returned term, together with the length of the DAG and the costs of the
extraction of the engine.

The clients state their own results in terms of these. For example, Andersen's `solve_exact`
says that a saturated solve answers `may_points q x a` exactly (`AndersenSig.v`), and
Steensgaard's `solve_exact` says that a saturated solve answers
`pointer_congruence q (Deref (Cell x)) (Cell a)` exactly (`SteensgaardSig.v`).

## Limits

- A value type other than `positive` needs a registered encoder. A type without one that is an
  inductive type is read as a datatype when both indices of a relation have it, and stops the
  command where a value is needed, such as in an input pair.
- An encoder need not be onto. A primitive whose argument is a positive that decodes to no
  value has no result.
- A primitive has one to three arguments. A call inside a premise argument applies to
  variables that a relation or input premise binds, so a nested call there is not supported.
- The engine has no rulesets and no `run-schedule`. It has no `subsume` and no `delete`, and
  its containers cannot hold class identifiers. These features wait for engine support after
  stage 2, so the command cannot express them.
- The command derives no lattice tables, so a client writes those specifications by hand.
- The theorems of the previous section are stated and not yet proved.
- The engine has no termination contract for programs that build terms, so no theorem says
  when a run of a ground specification or a run with rewrites saturates.
- A rewrite step reads its premises in the input rows, so `saturate_closed` says nothing about
  a rewrite whose premises read derived rows.
- A run that stops at `IterLimit` or `IdLimit` has no completeness guarantee, so a client that
  needs the exact answer checks for `Saturated`.
