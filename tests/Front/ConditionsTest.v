(** * The conditions of the front-end theorems

    The checks that say which specifications, rules and rows the theorems cover, run on
    derived programs and on small changes of them. [kinds_ok] checks the kinds of the tables
    that patterns name, [rule_scoped] checks the variables of the actions of a rule, [ground]
    and [lattice_spec] pick the specifications of two theorems, [rows_ok] reads the first
    declaration of a table, and [holds] finds only rows without output.
    For example, the atoms of a union clause declared as a lattice table fail the kind check.

    Groups:
    - [KindTests] The kind check accepts derived specifications and rejects a constructor that
      names a lattice table.
    - [ScopeTests] Derived rules are scoped, and a rule without its query is not.
    - [GroundTests] A specification of unions is ground, and one with rewrites is not.
    - [LatticeTests] A relational specification is a lattice specification, and one with
      constructors is not.
    - [RowTests] Rows are checked against the first declaration of a relation.
    - [LookupTests] A lookup finds a relation row and ignores a constructor row.
    - [PatternTests] The helpers of the pattern laws read constructors, terms and values.

    Builds on: the derive command, the lowering checks, the runner conditions, the conditions of
    the theorems and the runner. *)

From Stdlib Require Import List PArith NArith Bool.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner CongruenceRefSig LatticeSig
  Derive.
Import List.ListNotations.

(** * Fixtures *)

(** Values are positives without primitives. *)
Module CheckValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End CheckValue.

Module CheckIndex := IndexCode CheckValue.
Module CheckJoin := JoinCode CheckValue CheckIndex.
Module CheckDatabase := DatabaseCode CheckValue CheckIndex.
Module CheckRun := RunCode CheckValue CheckIndex CheckJoin CheckDatabase.
Module CheckRunner := RunnerCode CheckValue CheckIndex CheckJoin CheckDatabase CheckRun.

(** Ten iterations and a hundred identifiers are far more than the fixtures need. *)
Definition check_limits : limits := Limits 10%N 100%N.

(** The code of the merge of a lattice table that a test declares. *)
Definition max_merge : positive := 1%positive.

(** The specification with every declaration of a table replaced by one declaration. *)
Definition redeclared (s : spec positive) (d : decl) : spec positive :=
  Spec (map (fun d' => if Pos.eqb (name d') (name d) then d else d') (tables s)) (inputs s)
    (clauses s).

(** The specification with one declaration put before the others, so that it shadows a later
    declaration of the same table. *)
Definition shadowed (s : spec positive) (d : decl) : spec positive :=
  Spec (d :: tables s) (inputs s) (clauses s).

(** Reachability over a list of edges. *)
Inductive path (edges : list (positive * positive)) : positive -> positive -> Prop :=
  | path_edge x y : In (x, y) edges -> path edges x y
  | path_step x y z : path edges x y -> In (y, z) edges -> path edges x z.

Egglog Path from path.

(** Terms built from atoms with a unary wrapper. *)
Inductive term : Type :=
  | Atom (n : positive)
  | Wrap (a : term).

(** Equality of terms, with the closure laws and one union for each listed pair of atoms. *)
Inductive same (merges : list (positive * positive)) : term -> term -> Prop :=
  | same_refl a : same merges a a
  | same_sym a b : same merges a b -> same merges b a
  | same_trans a b c : same merges a b -> same merges b c -> same merges a c
  | same_wrap a a' : same merges a a' -> same merges (Wrap a) (Wrap a')
  | same_merge x y : In (x, y) merges -> same merges (Atom x) (Atom y).

Egglog Terms from same.

(** Sums of numbers. *)
Inductive sum : Type :=
  | Num (n : positive)
  | Add (a b : sum).

(** Equality of sums, with the commutativity of addition as a rewrite. *)
Inductive sum_equiv : sum -> sum -> Prop :=
  | sum_refl a : sum_equiv a a
  | sum_sym a b : sum_equiv a b -> sum_equiv b a
  | sum_trans a b c : sum_equiv a b -> sum_equiv b c -> sum_equiv a c
  | sum_add a a' b b' : sum_equiv a a' -> sum_equiv b b' -> sum_equiv (Add a b) (Add a' b')
  | sum_comm a b : sum_equiv (Add a b) (Add b a).

Egglog Sums from sum_equiv.

(** * Kinds *)

Module KindTests.

  (** A relational specification passes the kind check. *)
  Example relational_specification_passes :
    kinds_ok Path.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A specification whose constructors name identifier tables passes the kind check. *)
  Example constructor_tables_pass :
    kinds_ok Terms.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The atoms declared as a lattice table. *)
  Definition lattice_atom : spec positive :=
    redeclared Terms.spec (Decl Terms.Atom_code [SVal] (OLat max_merge)).

  (** The union clause names the atoms in constructor patterns, so it fails the kind check. *)
  Example lattice_constructor_fails :
    kinds_ok lattice_atom = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The wrapper declared as a lattice table. *)
  Definition lattice_wrap : spec positive :=
    redeclared Terms.spec (Decl Terms.Wrap_code [SId] (OLat max_merge)).

  (** The wrapper occurs only in a congruence law, which gives no clause, so no pattern names
      it and the kind check passes. *)
  Example unnamed_constructor_passes :
    kinds_ok lattice_wrap = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End KindTests.

(** * Scopes *)

Module ScopeTests.

  (** The rules of a relational program are scoped. *)
  Example relational_rules_are_scoped :
    forallb rule_scoped (spec_rules Path.spec) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rules of a program that builds terms are scoped. *)
  Example building_rules_are_scoped :
    forallb rule_scoped (spec_rules Terms.spec) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rules of a program with a rewrite are scoped. *)
  Example rewriting_rules_are_scoped :
    forallb rule_scoped (spec_rules Sums.spec) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The actions of the first rule of [Terms] without its query read unbound variables. *)
  Example rule_without_its_query_is_not_scoped :
    match spec_rules Terms.spec with
    | r :: _ => rule_scoped (Rule positive [] (actions positive r))
    | [] => true
    end = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ScopeTests.

(** * Ground specifications *)

Module GroundTests.

  (** A specification whose only clause is a union over input rows is ground. *)
  Example unions_are_ground :
    ground Terms.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A specification with a rewrite is not ground. *)
  Example rewrites_are_not_ground :
    ground Sums.spec = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A relational specification is not ground, because its heads derive rows. *)
  Example relations_are_not_ground :
    ground Path.spec = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End GroundTests.

(** * Lattice specifications *)

Module LatticeTests.

  (** A relational specification is a lattice specification. *)
  Example relations_are_lattice_specifications :
    lattice_spec Path.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A specification with constructor tables is not a lattice specification. *)
  Example constructors_are_not_lattice_specifications :
    lattice_spec Terms.spec = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LatticeTests.

(** * Rows *)

Module RowTests.

  Local Open Scope positive_scope.

  (** One edge from 1 to 2. *)
  Definition one_edge : list (positive * list positive) := [(Path.edges_code, [1; 2])].

  (** An edge row passes the check against the declaration of the edges. *)
  Example edge_row_passes :
    rows_ok Path.spec one_edge = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An earlier declaration of the edges with one argument shadows the later one, so the same
      row fails the check. *)
  Example shadowed_declaration_counts :
    rows_ok (shadowed Path.spec (Decl Path.edges_code [SVal] ORel)) one_edge = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An input table declared as a constructor table rejects its rows, because the seed puts
      them without output. *)
  Example constructor_input_fails :
    rows_ok (redeclared Path.spec (Decl Path.edges_code [SVal; SVal] OId)) one_edge = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RowTests.

(** * Lookups *)

Module LookupTests.

  Local Open Scope positive_scope.

  (** The edges 1 to 2 and 2 to 3. *)
  Definition two_edges : list (positive * positive) := [(1, 2); (2, 3)].

  (** A lookup finds a derived relation row. *)
  Example lookup_finds_a_relation_row :
    CheckRunner.holds Path.path_code [1; 3]
      (snd (CheckRunner.solve Path.program (Path.facts two_edges) check_limits)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The database after adding the term [Atom 1]. *)
  Definition atom_database : CheckDatabase.t :=
    match CheckRunner.saturate Terms.program [] [Terms.encode_term (Atom 1)] check_limits with
    | (_, db, _) => db
    end.

  (** The database has the constructor row of [Atom 1], with its class as output. *)
  Example constructor_row_exists :
    match fst (CheckDatabase.lookup Terms.Atom_code [Val 1] atom_database) with
    | Some (Some (Id _)) => true
    | _ => false
    end = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A lookup ignores the constructor row, because the row has an output. *)
  Example lookup_ignores_a_constructor_row :
    CheckRunner.holds Terms.Atom_code [1] atom_database = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LookupTests.

(** * Pattern helpers *)

Module PatternTests.

  Local Open Scope positive_scope.

  (** The heads of the clauses of a relational specification have no constructor pattern. *)
  Example relational_heads_have_no_constructor :
    forallb (fun c =>
      match head c with
      | Derive _ args => forallb pat_free args
      | _ => false
      end) (clauses Path.spec) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The sides of a union of atoms are constructor patterns. *)
  Example union_sides_are_constructors :
    existsb (fun c =>
      match head c with
      | Unify l r => pat_free l || pat_free r
      | _ => false
      end) (clauses Terms.spec) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Under an environment that gives every variable the literal 5, the two sides of the union
      of atoms are the encodings of [Atom 5]. *)
  Example union_sides_have_atom_terms :
    map (fun c =>
      match head c with
      | Unify l r => pat_terms (fun _ _ => None) (fun _ => Some (ELit 5)) [l; r]
      | _ => None
      end) (clauses Terms.spec) =
    [Some [Terms.encode_term (Atom 5); Terms.encode_term (Atom 5)]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The values of an engine environment keep a value cell and drop a class cell. *)
  Example values_drop_classes :
    (val_env (V := positive) (fun _ => Some (Val 3)) 1,
     val_env (V := positive) (fun _ => Some (Id 3)) 1) = (Some 3, None).
  Proof.
    vm_compute. reflexivity.
  Qed.

End PatternTests.
