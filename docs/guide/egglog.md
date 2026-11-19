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

The command `Egglog P from R1 .. Rn.` reads the inductive relations `R1` to `Rn` together. They
may come in any order, and a premise of one relation may read any of them, so two relations may
read each other (see Relations that read each other). The order of `R1` to `Rn` fixes the order
of the tables and of the rules. The module `P` receives the definitions that the next sections
describe. The reading follows these rules.

**Sorts.** Each argument of a relation has a sort that comes from its Rocq type. An argument of
a value type is a value. A value type is `positive`, a type with a registered encoder, or a
pair, an option or a list of value types (see "Value types"). An argument
whose type is an inductive datatype, such as `term` below, is a class, the identifier of an
equivalence class of the engine's e-graph. An argument of type `list T` of a constructor of a
datatype is a class as well (see "Lists in datatypes"). Any other type is an error.

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
value. A constructor of a lattice table assigns a value, and a premise over a lattice table
reads the stored value (see Lattice tables).

**Equations.** A relation `R t u` whose two indices have the same datatype is an equation. It
gets no table of its own, because the constructors of the datatype are its tables. The
constructors of the relation that state reflexivity, symmetry, transitivity or congruence of a
datatype constructor are the e-graph's own laws, so they give no clause. The congruence of a
constructor in a list argument relates the two lists by `Forall2 R`. Every other
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
A client never writes a code or a variable number (see the rule in `docs/design/rules.md`). The
positions of rules are generated too, as the constants of rulesets (see Rulesets), so a client
writes no rule position either.

## Relations that read each other

The relations of a program can read each other through their premises, as the relations of a
mutual inductive do. For example, a walk of odd length is an edge, or a walk of even length
followed by an edge, and a walk of even length is a walk of odd length followed by an edge. The
command reads the two relations of the following mutual inductive into one program.

```coq
(** [odd_walk edges x y] says that a walk of odd length leads from [x] to [y], and
    [even_walk edges x y] says that a walk of even positive length does. *)
Inductive odd_walk (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | odd_edge x y : In (x, y) edges -> odd_walk edges x y
  | odd_step x y z : even_walk edges x y -> In (y, z) edges -> odd_walk edges x z
with even_walk (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | even_step x y z : odd_walk edges x y -> In (y, z) edges -> even_walk edges x z.

Egglog Walks from odd_walk even_walk.

Definition three_cycle : list (positive * positive) := [(1, 2); (2, 3); (3, 1)].
Definition four_cycle : list (positive * positive) := [(1, 2); (2, 3); (3, 4); (4, 1)].

(** Once around the cycle of three nodes is a walk of odd length from 1 back to 1. *)
Example three_cycle_has_odd_walk_back :
  ExampleRunner.holds Walks.odd_walk_code [1; 1]
    (snd (ExampleRunner.solve Walks.program (Walks.facts three_cycle) example_limits)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every walk from 1 back to 1 on the cycle of four nodes has a length that four divides. *)
Example four_cycle_has_no_odd_walk_back :
  ExampleRunner.holds Walks.odd_walk_code [1; 1]
    (snd (ExampleRunner.solve Walks.program (Walks.facts four_cycle) example_limits)) = false.
Proof. vm_compute. reflexivity. Qed.
```

The lemma `<R>_spec` has two halves. The half that goes from an instance of `R` to its derived
row is the lemma `<R>_derived`, and its proof needs an induction over the instances of `R`.
Rocq's principle `odd_walk_ind` gives no induction hypothesis for the premise
`even_walk edges x y` of `odd_step`, so the command builds the induction itself. It groups the
relations that read each other, here `odd_walk` and `even_walk`, and proves their lemmas
`<R>_derived` with one fixpoint that has a function for each relation of the group. The function
of a relation takes an instance apart, applies the fire lemma of its constructor, and calls the
fixpoint on each premise over a relation of the group. Such a premise is a subterm of the
instance, so the fixpoint passes Rocq's guard check, which runs when the command defines the
lemma.

A group comes after the groups that its premises read, and the lemmas `<R>_derived` of an
earlier group prove the premises over its relations. Lattice tables that read each other get
their lemmas `<R>_assigned` in the same way. The tests of `tests/Front/MutualTest.v` also run
three relations that read each other in a cycle, the relations `left` and `right` of egglog's
`schedule-demo.egg`, and two lattice tables that read each other.

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
any number of arguments and returns a result, and the arguments and the result have value
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

The function `P.prim` decodes the arguments of a call one at a time, with one step for each
argument, and then encodes the result. It has no result when the number of values in the call
differs from the number of arguments of the function.

```coq
(** Two products added, [a * b + c * d]. *)
Definition blend (a b c d : positive) : positive := Pos.add (Pos.mul a b) (Pos.mul c d).

Egglog Primitives Blends blend.

Example blend_takes_four_values :
  Blends.prim Blends.blend_code [1; 2; 3; 4] = Some 14 /\
  Blends.prim Blends.blend_code [1; 2; 3] = None.
Proof. vm_compute. auto. Qed.
```

The tests of `tests/Front/ArityTest.v` call `blend` in a conclusion and in the right side of a
rewrite, and a function of a boolean and four integers in an equation premise.

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
`bool` and `StringEncode` for `string`. The files `theories/Front/EncodeNat.v` and
`theories/Front/EncodeAscii.v` register `NatEncode` for `nat` and `AsciiEncode` for `ascii`, and
a client loads them to read these types as values. A client that does not load them reads `nat`
and `ascii` as datatypes, so a relation over two natural numbers is then an equation over the
terms of `O` and `S`. A client writes the module of any other type in the
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
`egglog_inj`. The tactics that prove the generated lemmas use both. The command also declares
`M.encode` with `simpl never`, so the encoding of a literal `c` keeps the form `M.encode c` in
the proofs, and the tactics decode it as they decode the encoding of a variable. A relation of
an unregistered type stops the command with a message that names the type.

## Pairs, options and lists of values

A pair, an option and a list of value types are value types too. The command builds their
encoders from the encoders of their parts with `encode_pair`, `encode_option` and
`encode_list` of `theories/Front/DeriveHelpers.v`, and their decoders with `decode_pair`,
`decode_option` and `decode_list`. An encoding writes each bit of a part after a one and ends
the part with a zero, so a decoder reads the parts back. The lemmas `decode_encode_pair`,
`decode_encode_option` and `decode_encode_list` say that each decoder undoes its encoder, so two
values with equal encodings are equal. A relation index, a column of an input row, an argument
of an input constructor and an argument of a primitive may each have such a type. The engine
holds such a value as one positive, so a pattern writes it as a variable or as a term without
variables.

The following program reads jobs, each with the list of the jobs that it waits for. The
premise of `idle_job` reads a job whose list is empty, and the primitive `waits_for` finds a
job in a list.

```coq
Local Open Scope positive_scope.

(** A job with its number and the numbers of the jobs that it waits for. *)
Inductive job : Type :=
  | Job (id : positive) (deps : list positive).

(** Whether the job [d] is among the jobs [ds]. *)
Definition waits_for (d : positive) (ds : list positive) : bool := existsb (Pos.eqb d) ds.

Egglog Primitives JobOps waits_for.

(** [blocked jobs i d] says that the job [i] waits for the job [d]. *)
Inductive blocked (jobs : list job) : positive -> positive -> Prop :=
  | blocked_on i ds d es : In (Job i ds) jobs -> In (Job d es) jobs ->
      waits_for d ds = true -> blocked jobs i d.

(** [idle jobs i] says that the job [i] waits for no job. *)
Inductive idle (jobs : list job) : positive -> Prop :=
  | idle_job i : In (Job i []) jobs -> idle jobs i.

Egglog Jobs from blocked idle with JobOps.

Module JobOpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := JobOps.prim.
  Definition merge (_ : positive) := Pos.max.
End JobOpsValue.

Module JobOpsIndex := IndexCode JobOpsValue.
Module JobOpsJoin := JoinCode JobOpsValue JobOpsIndex.
Module JobOpsDatabase := DatabaseCode JobOpsValue JobOpsIndex.
Module JobOpsRun := RunCode JobOpsValue JobOpsIndex JobOpsJoin JobOpsDatabase.
Module JobOpsRunner :=
  RunnerCode JobOpsValue JobOpsIndex JobOpsJoin JobOpsDatabase JobOpsRun.

Definition jobs_result : JobOpsDatabase.t :=
  snd (JobOpsRunner.solve Jobs.program (Jobs.facts [Job 1 []; Job 2 [1; 3]]) example_limits).

Example job_two_waits_for_job_one :
  JobOpsRunner.holds Jobs.blocked_code [2; 1] jobs_result = true /\
  JobOpsRunner.holds Jobs.idle_code [1] jobs_result = true /\
  JobOpsRunner.holds Jobs.idle_code [2] jobs_result = false.
Proof. vm_compute. auto. Qed.
```

A row of `Jobs.facts` holds the list of a job as one value. For the job 2, the row is
`(Jobs.Job_code, [2; encode_list id_encode [1; 3]])`, and the generated lemmas state rows the
same way. The tests of `tests/Front/CompositeTest.v` run relations over `nat`, `ascii`, pairs
of integers, options and lists, with the generated lemmas in both directions.

## Lattice tables

A lattice table keeps one value at each key, the merge of all the values that the clauses
assign at that key. For shortest paths, a key is a pair of nodes, the values are the lengths
of the paths between them, and the merge `Pos.min` keeps the shortest length. A relation whose
last index is its value can be a lattice table. The command declares it with `merge R g` after
`with P`, where `g` is a primitive of the set `P` that takes two values of the type of the last
index of `R` and returns one.

```coq
From Galois.Front Require Import SpecLattice.

Egglog Primitives PathOps Pos.add Pos.min.

(** An edge from a source node to a target node, with a weight. *)
Inductive edge : Type :=
  | Edge (source target weight : positive).

(** [dist edges a b d] says that some path from [a] to [b] has length [d]. *)
Inductive dist (edges : list edge) : positive -> positive -> positive -> Prop :=
  | dist_edge a b w : In (Edge a b w) edges -> dist edges a b w
  | dist_step a b c d w : dist edges a b d -> In (Edge b c w) edges ->
      dist edges a c (Pos.add d w).

Egglog Distances from dist with PathOps merge dist Pos.min.
```

The table `Distances.dist_code` has the kind `OLat PathOps.min_code`, and its keys are the
first two indices of `dist`. Each constructor assigns a value, so its clause has an `Assign`
head. The premise `dist edges a b d` of `dist_step` reads the value that the table stores at
`[a; b]`, so it becomes an `Equals` premise. The engine merges two values with the `merge` of
its value module, and `prim_merge PathOps.prim` merges as the primitive set computes. A lookup
of the database reads the stored value. On the following graph, the path from 1 through 2 to 3
is shorter than the direct edge, and the table stores its length.

```coq
Module PathOpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := PathOps.prim.
  Definition merge := prim_merge PathOps.prim.
End PathOpsValue.

Module PathOpsIndex := IndexCode PathOpsValue.
Module PathOpsJoin := JoinCode PathOpsValue PathOpsIndex.
Module PathOpsDatabase := DatabaseCode PathOpsValue PathOpsIndex.
Module PathOpsRun := RunCode PathOpsValue PathOpsIndex PathOpsJoin PathOpsDatabase.
Module PathOpsRunner :=
  RunnerCode PathOpsValue PathOpsIndex PathOpsJoin PathOpsDatabase PathOpsRun.

Local Open Scope positive_scope.

Definition triangle : list edge := [Edge 1 2 1; Edge 2 3 1; Edge 1 3 5].

Definition triangle_result : PathOpsDatabase.t :=
  snd (PathOpsRunner.solve Distances.program (Distances.facts triangle) example_limits).

(** The value that a database stores at a key of a lattice table, if it stores one. *)
Definition stored (f : positive) (ks : list positive) (db : PathOpsDatabase.t) :
    option positive :=
  match fst (PathOpsDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

Example shortest_distance_is_stored :
  stored Distances.dist_code [1; 3] triangle_result = Some 2.
Proof. vm_compute. reflexivity. Qed.
```

A read of a lattice table sees the stored value, which is a merge of the values that the
clauses have assigned at its key. The file `theories/Front/SpecLattice.v` gives a
specification with such reads its meaning, as four relations defined together.
`lat_assigned` holds of the values that a clause assigns at a key, `lat_merged` of the merges of
those values, which a read sees, `lat_derived` of the derived rows and `lat_body` of the bodies
that hold. On a specification without reads, `lat_derived_agrees` and `lat_assigned_agrees`
say that the derived rows and the assigned values are those of `derived` and `assigned`. The
generated lemma `Distances.dist_spec` says that `dist edges a b d` holds exactly when `d` is a
value that the clauses assign at `[a; b]`.

```coq
Example path_gives_assigned_value :
  lat_assigned PathOps.prim (prim_merge PathOps.prim) Distances.spec
    (Distances.inputs triangle) Distances.dist_code [1; 3] 2.
Proof.
  apply (proj1 (Distances.dist_spec triangle 1 3 2)).
  apply (dist_step triangle 1 2 3 1 1).
  - apply dist_edge. simpl. auto.
  - simpl. auto.
Qed.
```

The converse half of `dist_spec` needs a merge of two values of `dist` at one key to be a
value of `dist` again, because a read sees a merge. For each lattice relation that a clause of
a relation over values reads, the command proves this closure as the lemma `<R>_merges`, here
`Distances.dist_merges`. The proof succeeds when the merge returns one of its two arguments, as
`Pos.min`, `Pos.max` and `Z.min` do, or when a constructor of the relation merges two values.
The union of two sets returns neither of them, and the constructor `reaching_union` below merges
two sets.

```coq
Egglog Primitives SetOps N.lor.

(** Node [n] defines the set [s] of variables, as bits, or control flows between two nodes. *)
Inductive flow_fact : Type :=
  | Gen (node : positive) (defs : N)
  | Flow (source target : positive).

(** [reaching facts n s] says that the definitions of [s] may reach node [n]. *)
Inductive reaching (facts : list flow_fact) : positive -> N -> Prop :=
  | reaching_gen n s : In (Gen n s) facts -> reaching facts n s
  | reaching_flow m n s : reaching facts m s -> In (Flow m n) facts -> reaching facts n s
  | reaching_union n s t : reaching facts n s -> reaching facts n t ->
      reaching facts n (N.lor s t).

Egglog Reaching from reaching with SetOps merge reaching N.lor.
```

Otherwise the client proves the closure before the command, as a lemma named `<R>_merges` or as
a lemma of the hint database `egglog_merges`, and the command uses it. The command stops with a
message that names the relation when no lemma applies. The greatest common divisor of two
numbers is in general neither of them, and no constructor of `common` below merges two
divisors. The divisors at a node are still closed under `N.gcd`, by an induction that the lemma
`common_merges` writes out.

```coq
Egglog Primitives GcdOps N.gcd.

(** [common nums n d] says that [d] is the greatest common divisor of some numbers at node
    [n]. *)
Inductive common (nums : list (positive * N)) : positive -> N -> Prop :=
  | common_num n k : In (n, k) nums -> common nums n k
  | common_step n d k : common nums n d -> In (n, k) nums -> common nums n (N.gcd d k).

(** The greatest common divisor of two divisors at a node is a divisor there. *)
Lemma common_merges : forall nums n a b,
  common nums n a -> common nums n b -> common nums n (N.gcd a b).
Proof.
  intros nums n a b Ha Hb.
  induction Hb as [n k Hk | n d k _ IH Hk].
  - exact (common_step nums n a k Ha Hk).
  - rewrite N.gcd_assoc. exact (common_step nums n (N.gcd a d) k (IH Ha) Hk).
Qed.

Egglog Common from common with GcdOps merge common N.gcd.
```

The tests of `tests/Front/MergesTest.v` run this program, and a program of least common
multiples whose closure is a lemma of the hint database.

A relation over values may read a lattice table too, as `reach` does with the constructor
`reach_dist a b d : dist edges a b d -> reach edges a b` in
`Egglog Reach from dist reach with PathOps merge dist Pos.min`. In a program with lattice
tables, the lemma `<R>_spec` of such a relation relates it to `lat_derived`.

The theorems of `theories/Front/LatticeReadSig.v` describe the runs. In every outcome, a stored
value is a merge of assigned values and a stored row is derived (`solve_sound`,
`solve_rows_sound`). In a saturated outcome, every assigned value is below the stored value and
every derived row is stored (`solve_complete`, `solve_rows_complete`). Completeness needs
clauses that are monotone in the values that they read. The check `reads_ok` says that each
read value is a variable that occurs once in its body and in no key of the head. The hypothesis
`monotone` says that a larger value read gives a larger value assigned, in the orders of the
merges. For shortest paths, `d + w` grows with `d`, and the test `shortest_paths_are_monotone`
of `tests/Front/LatticeTest.v` proves `monotone` for its program with the merge
`prim_merge Ops.prim`. The lemma `monotone_agrees` of `theories/Front/LatticeRead.v` moves the
proof to any merge that agrees with it at the code of `Pos.min`.

A run of a monotone program that passes these checks saturates only when, at each key with an
assigned value, some merge of assigned values is above all of them (`unbounded_unsaturated`).
With `Pos.min` the shortest length is such a merge, so a run of shortest paths can saturate,
also on a cycle. With `Pos.max`, the lengths of the paths around a cycle have no largest one,
so no run of longest paths on a cycle saturates, and the test
`longest_paths_never_saturate_on_a_cycle` stops at its iteration limit. No theorem says that a
run with lattice tables saturates, because the engine has no termination contract for such
programs.

## Lawful merges

The theorems of lattice tables take a value module whose merge is commutative, associative and
idempotent at every code and every value. `prim_merge P.prim` returns its first argument where
the primitive has no result, and the decoder of `N` rejects the odd positives other than 1. So
`prim_merge SetOps.prim SetOps.lor_code 3 5` is 3, and the merge of 5 and 3 is 5. No
commutative merge agrees with it at every value. The file `theories/Front/LatticeMerge.v` builds
a merge with the laws at every code and every value, which agrees with `prim_merge P.prim` on
encodings.

The function `lift_merge encode decode join` joins the values that two positives encode. It
puts a positive that encodes no value below every encoding, and merges two such positives to
the larger one. A join at the code of a primitive is a module of the type `DECODED P E` of
`theories/Front/LatticeMergeSig.v`, with the laws of a semilattice and the lemma `prim_join`,
which says that the primitive computes the join on encodings. The functor `MaxMerge P` merges by
the maximum at every code, `DecodedMerge P B E D` adds the join `D` at its code to the merge
`B`, and `MergeValue P M` is the value module of positives with the primitives of `P` and the
merge `M`. The encoder `PosEncode` makes `positive` its own type of values. The following merge
takes the union of the sets of `reaching`.

```coq
From Galois.Front Require Import LatticeMergeSig LatticeMerge.

(** The union of sets of bits, at the code of [N.lor]. *)
Module LorJoin <: DECODED SetOps NEncode.
  Definition code := SetOps.lor_code.
  Definition join := N.lor.

  Lemma join_comm : forall a b, join a b = join b a.
  Proof. exact N.lor_comm. Qed.

  Lemma join_assoc : forall a b c, join a (join b c) = join (join a b) c.
  Proof. exact N.lor_assoc. Qed.

  Lemma join_idem : forall a, join a a = a.
  Proof. exact N.lor_diag. Qed.

  Lemma prim_join : forall x y,
    SetOps.prim code [NEncode.encode x; NEncode.encode y] = Some (NEncode.encode (join x y)).
  Proof. intros [| p] [| q]; reflexivity. Qed.
End LorJoin.

Module SetMerge0 := MaxMerge SetOps.
Module SetMerge := DecodedMerge SetOps SetMerge0 NEncode LorJoin.
Module SetValue := MergeValue SetOps SetMerge.

(** The positives 3 and 5 encode no value of [N], and they merge to 5 in either order. *)
Example lawful_merge_commutes :
  SetValue.merge SetOps.lor_code 3 5 = SetValue.merge SetOps.lor_code 5 3.
Proof. vm_compute. reflexivity. Qed.

(** The glue of [reaching], moved to the lawful merge. *)
Lemma reaching_spec_lawful : forall facts n s,
  reaching facts n s <->
  lat_assigned SetOps.prim SetValue.merge Reaching.spec (Reaching.inputs facts)
    Reaching.reaching_code [n] (NEncode.encode s).
Proof.
  intros facts n s.
  rewrite (Reaching.reaching_spec facts n s).
  apply SetValue.lat_merge_moves.
  - intros f m Hkind.
    exact (lat_codes_covered (tables Reaching.spec) SetMerge.codes f m eq_refl Hkind).
  - intros f m ks w Hkind Hw.
    destruct (lat_codes_covered (tables Reaching.spec) SetMerge.codes f m eq_refl Hkind)
      as [Hm | []].
    subst m. apply SetMerge.encoded_code.
    destruct (proj2 (Reaching.closed facts) f ks w Hw) as [_ [k [x [_ [Hx _]]]]].
    exists x. exact Hx.
Qed.
```

The lemma `lat_merge_moves` of `MergeValue` moves the glue lemmas to the lawful merge from two
facts. Every lattice table merges at a code of the merge, which `lat_codes_covered` checks by
computation, and every assigned value is an encoding at that code, which the generated lemma
`closed` gives. With one type of values, `lat_merge_agrees_on` of `SpecLattice.v` moves the glue
in the same way, with the predicate of the encodings. Every positive encodes itself in
`PosEncode`, so for `positive` the lawful merge agrees with `prim_merge P.prim` at every value,
and `monotone_agrees` moves a proof of `monotone` to it as well. The tests of
`tests/Front/LatticeMergeTest.v` move the glue of shortest paths and of `reaching`, move the
proof that shortest paths are monotone, and apply `solve_complete` of `LatticeReadSig.v` to
shortest paths with the lawful merge.

## Equations that read relations

A program may have relations over values beside equations, and a premise of an equation may read
a relation over values or a lattice table. In the following program, `known` propagates
constants through copies between registers, and the rewrite `scaled_known` reads it, so that a
product by a register that holds a known constant is a scaling by the constant.

```coq
From Galois.Front Require Import SpecReads.

(** A statement: register [x] holds the constant [c], or the value of register [y]. *)
Inductive stmt : Type :=
  | Init (x c : positive)
  | Copy (x y : positive).

(** [known prog x c] says that register [x] holds the constant [c]. *)
Inductive known (prog : list stmt) : positive -> positive -> Prop :=
  | known_init x c : In (Init x c) prog -> known prog x c
  | known_copy x y c : In (Copy x y) prog -> known prog y c -> known prog x c.

(** Products of registers, and their scalings by constants. *)
Inductive product : Type :=
  | Ref (x : positive)
  | Times (a b : product)
  | Scale (c : positive) (a : product).

(** [scaled prog t u] says that [t] and [u] are equal when the registers hold their known
    constants. *)
Inductive scaled (prog : list stmt) : product -> product -> Prop :=
  | scaled_refl a : scaled prog a a
  | scaled_sym a b : scaled prog a b -> scaled prog b a
  | scaled_trans a b c : scaled prog a b -> scaled prog b c -> scaled prog a c
  | scaled_times a a' b b' : scaled prog a a' -> scaled prog b b' ->
      scaled prog (Times a b) (Times a' b')
  | scaled_scale c a a' : scaled prog a a' -> scaled prog (Scale c a) (Scale c a')
  | scaled_known x c a : known prog x c -> scaled prog (Times (Ref x) a) (Scale c a).

Egglog Folds from known scaled.

(** Register 3 holds 5, and register 1 copies register 3. *)
Definition copies : list stmt := [Init 3 5; Copy 1 3].

Example product_equals_its_scaling :
  ExampleRunner.equal Folds.program (Folds.facts copies) example_limits
    (Folds.encode_product (Times (Ref 1) (Ref 2)))
    (Folds.encode_product (Scale 5 (Ref 2))) = true.
Proof. vm_compute. reflexivity. Qed.
```

The relation `known` gets its glue as in a program without equations, and `Folds.known_spec`
relates it to `derived`. The file `theories/Front/SpecReads.v` gives an equation beside
relations its meaning. `read_congruent prim s P Q` is the least congruence that contains each
instance of an equational clause whose premises read rows of `P` and values of `Q`. The lemma
`Folds.scaled_congruent` says that `scaled prog t u` gives the read congruence of the encodings
of `t` and `u` over the derived rows `derived prim Folds.spec (Folds.inputs prog)` and the empty
relation of values `no_values`. With the input rows and no values, `read_congruent` is
`congruent` (`congruent_read`), so a program of equations alone keeps its lemma `<R>_congruent`
over `congruent`. Each rewrite also gets the lemma `<C>_steps`, which says that its instance is
a step `read_step`.

```coq
(** Register 1 holds 5 through the copy from register 3. *)
Lemma one_holds_five : known copies 1 5.
Proof.
  apply (known_copy copies 1 3 5).
  - simpl. auto.
  - apply known_init. simpl. auto.
Qed.

Example scaling_is_a_step : forall prim,
  read_step prim Folds.spec (derived prim Folds.spec (Folds.inputs copies)) no_values
    (Folds.encode_product (Times (Ref 1) (Ref 2))) (Folds.encode_product (Scale 5 (Ref 2))).
Proof.
  intros prim. exact (Folds.scaled_known_steps prim copies 1 5 (Ref 2) one_holds_five).
Qed.
```

A program with lattice tables may have equations too. A premise of an equation that reads a
lattice table sees a merge of assigned values, so the glue of such a program reads the rows of
`lat_derived` and the merges of `lat_merged`. The tests of `tests/Front/RewriteReadTest.v` keep
the least bound of each register in a lattice table with the merge `Pos.min`, and a rewrite reads
it to replace the minimum of a register and a larger amount by the register.

The theorems of `theories/Front/RewriteReadSig.v` describe the runs of such programs, when every
relation and every lattice table takes only values (`value_tables`). In every outcome, a stored
row is a row of `lat_derived` and a stored value is a merge of `lat_merged`
(`saturate_rows_sound`, `saturate_values_sound`). At saturation, every derived row is stored
(`saturate_rows_complete`), and a rewrite step whose premises read the rows and the stored
values of the outcome, from a represented term, reaches a term of its class
(`saturate_reads_closed`). For a step whose premises read derived rows,
`saturate_derived_closed` says the same, and the lemma `<C>_steps` gives such a step from an
instance of the inductive. The test `class_of_product_holds_the_scaling` of
`tests/Front/RewriteReadTest.v` applies it to the program of `known`.

## Lists in datatypes

A constructor of a datatype may hold a list. An element of the list is a pair of two
components or one component, and a component is a value, a term of a datatype of the program,
or a list of such elements. For each element type `T`, the
command adds two constructor tables, `P.nil_T_code` and `P.cons_T_code`, and the encoder of the
datatype maps a list to a chain of nodes of these tables. A node of `cons_T` takes the
components of an element and the class of the rest of the list, and the chain ends in the node
of `nil_T`. A list is therefore a class of the e-graph, and the two tables are ordinary
constructor tables, so the engine and the theorems of this guide treat a list as any other
term.

The e-graph keeps its classes closed under congruence. Once the elements of two lists share
their classes, the nodes of the two lists share theirs, and so do the constructors that hold
the lists. In the same way, egglog rebuilds its vectors after a union. The following program
ports the first block of egglog's `container-rebuild.egg`. The constructor `math_vec` is the
congruence of `MyVec`. Its premise `Forall2 (math_eq unions) xs ys` relates the two lists
element by element, so the command reads `math_vec` as a closure law, which gives no clause.

```coq
Inductive math : Type :=
  | Scalar (n : positive)
  | MyVec (xs : list math).

Inductive math_eq (unions : list (positive * positive)) : math -> math -> Prop :=
  | math_refl t : math_eq unions t t
  | math_sym t u : math_eq unions t u -> math_eq unions u t
  | math_trans t u w : math_eq unions t u -> math_eq unions u w -> math_eq unions t w
  | math_vec xs ys : Forall2 (math_eq unions) xs ys -> math_eq unions (MyVec xs) (MyVec ys)
  | math_union x y : In (x, y) unions -> math_eq unions (Scalar x) (Scalar y).

Egglog Vectors from math_eq.

(** Whether saturation after the unions puts two terms in one class. *)
Definition joined (unions : list (positive * positive)) (a b : math) : bool :=
  ExampleRunner.equal Vectors.program (Vectors.facts unions) example_limits
    (Vectors.encode_math a) (Vectors.encode_math b).

Example vectors_of_joined_elements_share_a_class :
  joined [(1, 2)] (MyVec [Scalar 1; Scalar 2]) (MyVec [Scalar 2; Scalar 2]) = true.
Proof. vm_compute. reflexivity. Qed.

Example vector_of_another_length_stays_apart :
  joined [(1, 2)] (MyVec [Scalar 1]) (MyVec [Scalar 2; Scalar 2]) = false.
Proof. vm_compute. reflexivity. Qed.
```

The module `Vectors` has the tables `Vectors.nil_math_code` and `Vectors.cons_math_code`
besides the tables of `Scalar` and `MyVec`. The encoder `Vectors.encode_math` maps
`MyVec [Scalar 1]` to the following expression.

```text
EApp Vectors.MyVec_code
  [EApp Vectors.cons_math_code
     [EApp Vectors.Scalar_code [ELit 1]; EApp Vectors.nil_math_code []]]
```

The lemma `Vectors.math_eq_congruent` covers the law `math_vec`. Its proof recurses on the
hypothesis `Forall2` inside its recursion on `math_eq`, and the command checks it when it runs.

A pattern of a clause may hold a list too. The command reads `[]` as the node of `nil_T`,
`x :: t` as a node of `cons_T`, and a literal such as `[a; b]` as a chain of nodes. A variable of
type `list T` is a class, which a left side binds and a right side builds on. In the following
equation, the product of no factor is one, and the product of a list with a first factor is
that factor times the product of the rest.

```coq
Inductive arith : Type :=
  | Number (n : positive)
  | Mul (a b : arith)
  | Prod (xs : list arith).

Inductive arith_eq : arith -> arith -> Prop :=
  | arith_refl a : arith_eq a a
  | arith_sym a b : arith_eq a b -> arith_eq b a
  | arith_trans a b c : arith_eq a b -> arith_eq b c -> arith_eq a c
  | arith_mul a a' b b' : arith_eq a a' -> arith_eq b b' -> arith_eq (Mul a b) (Mul a' b')
  | arith_prod xs ys : Forall2 arith_eq xs ys -> arith_eq (Prod xs) (Prod ys)
  | prod_nil : arith_eq (Prod []) (Number 1)
  | prod_cons x t : arith_eq (Prod (x :: t)) (Mul x (Prod t))
  | mul_one a : arith_eq (Mul a (Number 1)) a.

Egglog Products from arith_eq.

Example product_is_a_multiplication :
  ExampleRunner.equal Products.program Products.facts example_limits
    (Products.encode_arith (Prod [Number 2; Number 3]))
    (Products.encode_arith (Mul (Number 2) (Number 3))) = true.
Proof. vm_compute. reflexivity. Qed.
```

A list of pairs `list (K * T)` whose keys have a value type `K` is an association list from
values to classes, in the order that the client keeps. A pattern writes each element of such a
list as a pair `(k, v)`. A lookup is two rewrites. The first one gives the value of a first pair
with the key, and the second one skips a first pair with another key, which the primitive
`Pos.eqb` tells apart. Rocq has no scheme `All` registered for pairs, so its warning
`register-all` stops a datatype that nests through pairs in a build with the flags of this
project. `theories/Front/DeriveHelpers.v` registers the scheme with `Scheme All for prod`.
Every client of `Derive` loads that file, so a datatype that nests through pairs needs no setup.

```coq
Egglog Primitives Keys Pos.eqb.

Inductive item : Type :=
  | Tag (n : positive)
  | Fields (fs : list (positive * item))
  | Get (k : positive) (r : item).

Inductive item_eq : item -> item -> Prop :=
  | item_refl a : item_eq a a
  | item_sym a b : item_eq a b -> item_eq b a
  | item_trans a b c : item_eq a b -> item_eq b c -> item_eq a c
  | get_here k v rest : item_eq (Get k (Fields ((k, v) :: rest))) v
  | get_next k k' v rest : Pos.eqb k k' = false ->
      item_eq (Get k (Fields ((k', v) :: rest))) (Get k (Fields rest)).

Egglog Items from item_eq with Keys.

Module KeysValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Keys.prim.
  Definition merge (_ : positive) := Pos.max.
End KeysValue.

Module KeysIndex := IndexCode KeysValue.
Module KeysJoin := JoinCode KeysValue KeysIndex.
Module KeysDatabase := DatabaseCode KeysValue KeysIndex.
Module KeysRun := RunCode KeysValue KeysIndex KeysJoin KeysDatabase.
Module KeysRunner := RunnerCode KeysValue KeysIndex KeysJoin KeysDatabase KeysRun.

Example lookup_finds_a_later_key :
  KeysRunner.equal Items.program Items.facts example_limits
    (Items.encode_item (Get 2 (Fields [(1, Tag 10); (2, Tag 20)])))
    (Items.encode_item (Tag 20)) = true.
Proof. vm_compute. reflexivity. Qed.
```

The cons table of the association list is `Items.cons_positive_item_code`. It takes the key,
the class of the value and the class of the rest. The tests of `tests/Front/ContainerTest.v`
also run lists of integers, nested vectors and records with a repeated key.

## Datatypes that hold datatypes

A constructor may hold a term of another datatype, directly or in a list, and a list may hold
lists. The command adds every datatype that the datatypes of the relations reach in this way to
the program, with the tables of its constructors and its own encoder. The encoder of a datatype
encodes a term of another datatype as the encoder of that datatype does. So two datatypes that
hold each other, as a mutual inductive defines them, stop the command. In the following program,
a block holds a list of instructions. A union of two values joins the instructions that store them,
and then the blocks that hold these instructions.

```coq
(** An instruction is a skip or a store of a value into a variable. *)
Inductive instr : Type :=
  | Skip
  | Store (x v : positive).

(** Blocks of instructions, and an instruction that guards a block. *)
Inductive block : Type :=
  | Block (body : list instr)
  | Guard (s : instr) (rest : block).

(** [instr_eq same s t] says that [s] and [t] are equal once the two values of each pair of
    [same] are equal. *)
Inductive instr_eq (same : list (positive * positive)) : instr -> instr -> Prop :=
  | instr_refl s : instr_eq same s s
  | instr_sym s t : instr_eq same s t -> instr_eq same t s
  | instr_trans s t u : instr_eq same s t -> instr_eq same t u -> instr_eq same s u
  | instr_same x v w : In (v, w) same -> instr_eq same (Store x v) (Store x w).

(** [block_eq same b c] says that [b] and [c] are equal, and a skip at the front of a block
    does nothing. *)
Inductive block_eq (same : list (positive * positive)) : block -> block -> Prop :=
  | block_refl b : block_eq same b b
  | block_sym b c : block_eq same b c -> block_eq same c b
  | block_trans b c d : block_eq same b c -> block_eq same c d -> block_eq same b d
  | block_skip rest : block_eq same (Block (Skip :: rest)) (Block rest).

Egglog Programs from instr_eq block_eq.

Example blocks_of_joined_instructions_are_equal :
  ExampleRunner.equal Programs.program (Programs.facts [(2, 3)]) example_limits
    (Programs.encode_block (Block [Skip; Store 1 2]))
    (Programs.encode_block (Block [Store 1 3])) = true.
Proof. vm_compute. reflexivity. Qed.
```

The list tables of the body of a block are `Programs.nil_instr_code` and
`Programs.cons_instr_code`. A list of lists, such as `rows : list (list T)`, has the tables
`nil_list_T` and `cons_list_T` of its outer list besides the tables of its rows, and each row is
a class. The tests of `tests/Front/NestingTest.v` join grids of lists of lists at their inner
elements.

## Pairs as variables and laws of lists

A pattern may write an element of a list of pairs as one variable `p`, as in `p :: rest`. The
command reads such a pair as its two sides, which are two variables of the clause. So the
clause uses `p` as an element of a list, or through `fst p` and `snd p`, and the command stops
when the clause uses `p` in another place.

A congruence law of a constructor may relate two lists of pairs by
`Forall2 (pair_rel ra rb) xs ys`. The relation `pair_rel` of `theories/Front/DeriveHelpers.v`
relates two pairs when `ra` relates their first sides and `rb` their second sides, and each of
`ra` and `rb` is the equality or the relation of the law. A law may also relate two arguments by
their equality, such as two lists of values. The command reads such laws as closure laws, which
give no clause, and the lemma `<R>_congruent` covers them. The relation of such a law nests
through `pair_rel`, which is a conjunction, so `theories/Front/DeriveHelpers.v` registers
`Scheme All for and` as well.

```coq
(** Leaves, rows of integers, objects of fields named by keys, and the value of the first
    field of an object. *)
Inductive doc : Type :=
  | Leaf (n : positive)
  | Row (vs : list Z)
  | Obj (fs : list (positive * doc))
  | Head (d : doc).

(** Equality of documents. Rows of equal integers are equal, and so are objects whose keys
    are equal and whose values are equal. The first two fields of an object swap, and [Head]
    reads the value of the first field. *)
Inductive doc_eq : doc -> doc -> Prop :=
  | doc_refl a : doc_eq a a
  | doc_sym a b : doc_eq a b -> doc_eq b a
  | doc_trans a b c : doc_eq a b -> doc_eq b c -> doc_eq a c
  | doc_row vs ws : vs = ws -> doc_eq (Row vs) (Row ws)
  | doc_obj fs gs : Forall2 (pair_rel eq doc_eq) fs gs -> doc_eq (Obj fs) (Obj gs)
  | doc_head a b : doc_eq a b -> doc_eq (Head a) (Head b)
  | obj_swap p q rest : doc_eq (Obj (p :: q :: rest)) (Obj (q :: p :: rest))
  | head_value p rest : doc_eq (Head (Obj (p :: rest))) (snd p).

Egglog Docs from doc_eq.

Example swapped_fields_are_equal :
  ExampleRunner.equal Docs.program Docs.facts example_limits
    (Docs.encode_doc (Obj [(1, Leaf 10); (2, Leaf 20)]))
    (Docs.encode_doc (Obj [(2, Leaf 20); (1, Leaf 10)])) = true.
Proof. vm_compute. reflexivity. Qed.

Example related_objects_are_congruent :
  forall fs gs, Forall2 (pair_rel eq doc_eq) fs gs ->
    congruent ExampleValue.prim Docs.spec Docs.inputs
      (Docs.encode_doc (Obj fs)) (Docs.encode_doc (Obj gs)).
Proof. intros fs gs Hall. apply Docs.doc_eq_congruent. exact (doc_obj fs gs Hall). Qed.
```

Programs with relations that read each other, lattice tables or equations that read relations
read these values and containers in the same way. In the tests of `tests/Front/CombinedTest.v`,
two relations that read each other and a lattice table read lists of values in their input
rows, and a lattice table keeps options of values. Three equations there hold lists, records
and terms of another datatype. Their premises read a relation over values, one of two
relations that read each other, and a lattice table, and two of them have rewrites that write
pairs as variables. The lemma `<R>_congruent` of each covers the laws over `Forall2 R`, over
`Forall2 (pair_rel ra rb)` and over equalities, with the read congruence as its conclusion.

## Rulesets

A ruleset is a set of constructors whose rules a schedule of egglog runs together. The
command takes the declaration `ruleset S C1 .. Ck` after the relations and after `with P`, in
any order with the declarations `merge R g`. It defines the constant `P.S` of type `list N`.
The constant holds the positions of the rules of the constructors `C1` to `Ck` in increasing
order, and each clause lowers to the rule at its own position in `P.program`, so a position
names both. Every program also defines `P.default` and `P.all`. The first holds the positions
of the rules that no ruleset lists, and the second holds the positions of all rules. A closure
law of an equation has no rule, so it has no position.

```coq
Inductive reach (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | reach_edge x y : In (x, y) edges -> reach edges x y
  | reach_step x y z : reach edges x y -> In (y, z) edges -> reach edges x z.

Inductive loop (edges : list (positive * positive)) : positive -> Prop :=
  | loop_back x : reach edges x x -> loop edges x.

Egglog Loops from reach loop
  ruleset grow reach_step
  ruleset close loop_back.

(** The tables that the premises of the clause at a rule position read. *)
Definition reads_at (s : spec positive) (i : N) : list positive :=
  match nth_error (clauses s) (N.to_nat i) with
  | Some c => flat_map (fun p => match p with Holds r _ => [r] | _ => [] end) (body c)
  | None => []
  end.

Example rulesets_list_their_rules :
  map (reads_at Loops.spec) Loops.grow = [[Loops.reach_code; Loops.edges_code]] /\
  map (reads_at Loops.spec) Loops.close = [[Loops.reach_code]] /\
  map (reads_at Loops.spec) Loops.default = [[Loops.edges_code]].
Proof. vm_compute. auto. Qed.
```

The rule of `reach_step` reads a path and an edge, the rule of `loop_back` reads a path, and
the rule of `reach_edge`, which no ruleset lists, reads an edge. The command stops when two
rulesets list one constructor, when a ruleset lists a constructor twice, when a name is no
constructor of the relations, and when a ruleset lists a closure law. It also stops when two
rulesets share a name and when a ruleset takes the name of a member of the module, such as
`all`. The engine runs the rules of a whole program, and it has no operation that runs a ruleset
alone. So a run reads no ruleset yet, and the schedules that run rulesets wait for engine
support.

## The generated module

For a command `Egglog P from R1 .. Rn` the module `P` has the following members.

| Member | Meaning |
| --- | --- |
| `spec` | The specification of the constructors. It lists the tables, the input tables and one clause for each constructor (`theories/Front/Spec.v`). |
| `program` | The engine program that `spec` lowers to. |
| `facts` | A function from the parameters of the first relation to the list of input rows. |
| `inputs` | The input rows as a relation `positive -> list positive -> Prop`, for the lemmas. |
| `relation` | The meaning of each table, as a relation on rows. |
| `lattice` | In a program with lattice tables, the meaning of the lattice tables, as a relation on codes, keys and values. |
| `<Table>_code` | One constant for each table. A relation has `<R>_code`, a constructor table has `<Constructor>_code`, and an input list that is a parameter has `<parameter>_code`. The list tables of an element type `T` have `nil_<T>_code` and `cons_<T>_code`. There a pair type `A * B` is named `<A>_<B>`, a list type `list A` is named `list_<A>` and an option type `option A` is named `option_<A>`. |
| `<S>` | For each declaration `ruleset S C1 .. Ck`, the positions of the rules of `C1` to `Ck`, as a `list N` in increasing order. |
| `default` | The positions of the rules that no ruleset lists. |
| `all` | The positions of all rules. |
| `encode_<T>` | One encoder for each datatype `T`, which maps a value of `T` to the engine's expression. It maps a list to a chain of nodes of its list tables. |
| `<Constructor>_fires` | One lemma for each constructor, which says that the clause derives the conclusion from the premises. The command adds each to the hint database `egglog_fire`. |
| `closed` | The derived rows are closed under the clauses of `relation`. It is the converse half of the glue. In a program with lattice tables, it also says that every assigned value is in `lattice`. |
| `<R>_merges` | For a lattice relation that a clause of a relation over values reads, the closure of `R` under its merge. A lemma that the client proves before the command, named `<R>_merges` or in the hint database `egglog_merges`, can give it. |
| `<R>_spec` | For a relation over values, the equivalence of `R` with its derived row, as in `Path.path_spec`. For a lattice relation, the equivalence of `R` with its assigned value, as in `Distances.dist_spec`. |
| `<R>_congruent` | For an equational relation, the implication from `R t u` to the congruence of the encodings of `t` and `u`. It covers the congruence laws over `Forall2 R`, over `Forall2 (pair_rel ra rb)` and over equalities. Beside relations over values, the conclusion is the read congruence over the meaning of the relations (see Equations that read relations). |
| `<C>_steps` | For a rewrite of an equation beside relations over values, the lemma that its instance is a step `read_step` over the meaning of the relations. |

Every lemma is checked, so a wrong reading stops the command. The proofs use the tactics that
`theories/Front/Derive.v` exports, for example `egglog_closed` of
`theories/Front/DeriveTactics.v`. The command builds the proofs of the lemmas `<R>_derived` as
fixpoints (see Relations that read each other).

## The theorems

Ten signatures state what the lowering, the runner and a run guarantee. Each theorem about
a run takes the conditions of its kind as hypotheses. These are `spec_ok` and `rows_ok`,
together with `relational`, `ground`, `lattice_spec`, `lattice_reads` or `value_tables`, and
each is stated over any value module that satisfies the engine's laws. The proofs are stubs, so
none of these theorems is proved yet.

**The lowering** (`LowerSig.v`). The lemma `lower_sound` says that a row that a well-sorted
relational program derives from input rows is a derived row, and `lower_complete` says the
converse. The lemma `lower_closed` says that a view that the rules of a well-sorted
specification close, and whose relation rows have no output, holds every row derived from its
own rows. The lemma `lower_valid` says that a model of a specification that passes `spec_ok`
validates its rules. A model needs each clause only under environments that give every variable
a meaning of the sort at which the clause uses it, as the sorted environments of the engine do.
So a rewrite such as `x * 1 => x` has models, among them the one that evaluates terms. A head
whose pattern has no meaning holds in every model, because an engine rule stops at a failed
primitive. Laws about single patterns relate their queries and
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
says that every assigned value is below the stored value in a saturated outcome. A program that
the command derives with lattice tables and no reads is a lattice specification, and
`lat_derived_agrees` and `lat_assigned_agrees` turn its glue lemmas into `derived` and
`assigned`.

**Lattice reads** (`LatticeReadSig.v`). A specification that passes `lattice_reads` has the
clauses of a lattice specification, and its premises may read lattice tables. In the meaning of
`SpecLattice.v`, `solve_sound` says that a stored value of every outcome is a merge of assigned
values, and `solve_rows_sound` says that a stored row is derived. For a specification that
passes `reads_ok` and is `monotone`, `solve_complete` and `solve_rows_complete` say that a
saturated outcome stores a value above every assigned value and every derived row. The lemma
`solve_exact` combines the two, and `unbounded_unsaturated` says that no run saturates when a
key has an assigned value and no merge of assigned values there is above all of them.

**Rewrites that read rows** (`RewriteReadSig.v`). A specification that passes `value_tables`
has relations and lattice tables that take only values, beside equations whose premises may read
them. In the meaning of `SpecLattice.v`, `saturate_rows_sound` and `saturate_values_sound` say
that a stored row of every outcome is a row of `lat_derived` and that a stored value is a merge
of `lat_merged`. At saturation, `saturate_rows_complete` says that every derived row is stored,
and `saturate_reads_closed` says that a rewrite step whose premises read the rows and the stored
values of the outcome, from a represented term, reaches a term of its class. The lemma
`saturate_derived_closed` says the same of a step whose premises read derived rows, in the
meaning of `SpecReads.v`.

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

- A value type is `positive`, a type with a registered encoder, or a pair, an option or a list
  of value types. A type without an encoder that is an inductive type is read as a datatype when
  both indices of a relation have it, and stops the command where a value is needed, such as in
  an input pair. A client reads `nat` and `ascii` as values only when it loads
  `theories/Front/EncodeNat.v` or `theories/Front/EncodeAscii.v`.
- The engine holds a pair, an option or a list of values as one positive, so a pattern writes
  such a value as a variable or as a term without variables. A pattern such as `Some x` stops
  the command, and so does `x :: xs` where the list is a value.
- An encoder need not be onto. A primitive whose argument is a positive that decodes to no
  value has no result.
- A call inside a premise argument applies to variables that a relation or input premise
  binds, so a nested call there is not supported. The command finds no encoders for a primitive
  whose type depends on an argument, such as `rev`, so a client wraps such a primitive in a
  function of a fixed type.
- The command defines the constants of rulesets. The engine runs the rules of a whole program,
  and it has no `run-schedule`, no `subsume` and no `delete`. These features wait for engine
  support after stage 2, so a run reads no ruleset and the command cannot express `subsume` or
  `delete`.
- Two datatypes that hold each other, as a mutual inductive defines them, stop the command,
  because the encoder of each would hold the encoder of the other.
- A pattern that writes an element of a list of pairs as a variable `p` uses `p` as such an
  element or through `fst p` and `snd p`, and the command stops at any other use of `p`.
- The command reads the congruence laws `Forall2 R xs ys` of a list of the datatype itself,
  `Forall2 (pair_rel ra rb) xs ys` of a list of pairs and `xs = ys` of any argument. A list of
  another datatype or of lists has no congruence law that the command reads, and the congruence
  closure of the engine still applies to the nodes of such a list.
- In an equation, a variable of a list type is a class, so the command stops when a premise
  of the equation reads the variable as a value, of an input row or of a relation over values.
- A list keeps the order and the repetitions of its elements. Sets, multisets and maps keyed
  by classes need the database to keep their keys in a normal form under the equivalence of
  classes, so they wait for a later change of the engine.
- Relations that read each other are relations over values or lattice tables, because a
  premise over an equation stops the command.
- Relations and lattice tables take only values, so the command stops at a lattice table keyed
  by a class, such as an analysis of the classes of an e-graph in egglog. The completeness of
  lattice reads of `LatticeReadSig.v` covers only specifications without constructor tables, so
  no theorem says which merge a saturated run of a program with equations stores.
- The theorems take a value module whose merge has the laws of the engine at every code and
  every value. `LatticeMerge.v` builds one from a join of decoded values at each merge code,
  which the client writes with its laws and the computation of its primitive (see Lawful
  merges). The lawful merge agrees with `prim_merge P.prim` on encodings. For `N`, `bool` and
  every other type whose decoder rejects some positive, the two differ at the other positives,
  so `monotone_agrees` cannot move a proof of `monotone` to the lawful merge, and the client
  proves `monotone` for the lawful merge itself.
- Completeness with reads assumes `reads_ok` and `monotone`. A read value that a key of the head
  or another premise uses fails `reads_ok`, and `monotone` is a hypothesis that the client
  proves, as the test of shortest paths does. A run of a program that fails either condition
  can store fewer rows and values than the relations hold, because a read sees the stored value
  and no smaller merge. The test `read_key_misses_a_value` shows such a run.
- The theorems of the previous section are stated and not yet proved.
- The engine has no termination contract for programs that build terms or have lattice tables,
  so no theorem says when a run of a ground specification, a run with rewrites or a run with
  lattice tables saturates.
- `saturate_reads_closed` and `saturate_derived_closed` cover a rewrite whose premises read the
  rows and the stored values of the outcome, or derived rows. A premise of a rewrite that reads
  a lattice table sees the value that the run stores. The inductive reads every assigned value,
  so a run may apply such a rewrite to fewer values than the inductive does, and no theorem
  relates the two.
- A run that stops at `IterLimit` or `IdLimit` has no completeness guarantee, so a client that
  needs the exact answer checks for `Saturated`.
