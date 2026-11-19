(** * Equations that read relations over values

    Programs whose equations read the rows of relations over values and the values of lattice
    tables, derived with [Egglog P from R1 .. Rn]. [known] propagates constants through copies,
    and the rewrite [fold_known] reads it to turn a product into a scaling by a known constant.
    [bound] keeps the least bound of each register, and the rewrite [simp_bound] reads it to drop
    a minimum with a larger amount. For example, the copy of the constant 5 from register 3 to
    register 1 makes [Mul (Ref 1) (Ref 2)] equal to [Scale 5 (Ref 2)].

    Groups:
    - [DeclarationTests] The rewrites read a relation and a lattice table, and the programs pass
      the conditions of the theorems of [RewriteReadSig.v].
    - [RunTests] Runs join the terms that the rewrites relate, and only those.
    - [GlueTests] The generated lemmas relate the equations to the read congruence and the
      rewrites to read steps.
    - [TheoremTests] [saturate_derived_closed] joins a product with its scaling in a saturated
      outcome.

    Builds on: the derive command, the meaning of equations that read rows, the theorems of
    rewrites that read rows, the lawful merges, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice SpecReads LowerSig Lower RunnerSig Runner
  RunnerFacts Derive Encode LatticeMergeSig LatticeMerge RewriteReadSig RewriteRead.
Import List.ListNotations.

(** * Fixtures *)

(** A statement of a program: register [x] holds the constant [c], or the value of register
    [y]. *)
Inductive stmt : Type :=
  | Init (x c : positive)
  | Copy (x y : positive).

(** [known prog x c] says that register [x] holds the constant [c]. *)
Inductive known (prog : list stmt) : positive -> positive -> Prop :=
  | known_init x c : In (Init x c) prog -> known prog x c
  | known_copy x y c : In (Copy x y) prog -> known prog y c -> known prog x c.

(** Products of registers, and their scalings by constants. *)
Inductive term : Type :=
  | Ref (x : positive)
  | Mul (a b : term)
  | Scale (c : positive) (a : term).

(** [fold prog t u] says that [t] and [u] are equal when the registers hold their known
    constants. A product by a register that holds [c] is the scaling by [c]. *)
Inductive fold (prog : list stmt) : term -> term -> Prop :=
  | fold_refl a : fold prog a a
  | fold_sym a b : fold prog a b -> fold prog b a
  | fold_trans a b c : fold prog a b -> fold prog b c -> fold prog a c
  | fold_mul a a' b b' : fold prog a a' -> fold prog b b' -> fold prog (Mul a b) (Mul a' b')
  | fold_scale c a a' : fold prog a a' -> fold prog (Scale c a) (Scale c a')
  | fold_known x c a : known prog x c -> fold prog (Mul (Ref x) a) (Scale c a).

Egglog Folds from known fold.

(** The minimum and the order of positives. *)
Egglog Primitives BoundOps Pos.min Pos.leb.

(** The fact that register [x] is at most [b]. *)
Inductive limit : Type :=
  | Below (x b : positive).

(** [bound facts x b] says that register [x] is at most [b]. Its merge keeps the least bound. *)
Inductive bound (facts : list limit) : positive -> positive -> Prop :=
  | bound_below x b : In (Below x b) facts -> bound facts x b.

(** Registers, fixed amounts and their minima. *)
Inductive amount : Type :=
  | Reg (x : positive)
  | Fixed (c : positive)
  | Min (a b : amount).

(** [simp facts t u] says that [t] and [u] are equal under the bounds of the registers. The
    minimum of a register and an amount at least its bound is the register. *)
Inductive simp (facts : list limit) : amount -> amount -> Prop :=
  | simp_refl a : simp facts a a
  | simp_sym a b : simp facts a b -> simp facts b a
  | simp_trans a b c : simp facts a b -> simp facts b c -> simp facts a c
  | simp_min a a' b b' : simp facts a a' -> simp facts b b' -> simp facts (Min a b) (Min a' b')
  | simp_bound x b c : bound facts x b -> Pos.leb b c = true ->
      simp facts (Min (Reg x) (Fixed c)) (Reg x).

Egglog Bounds from bound simp with BoundOps merge bound Pos.min.

(** No primitive. *)
Module NoOps <: PRIMITIVES.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
End NoOps.

Module NoMerge := MaxMerge NoOps.

(** The values of constant propagation, which has no primitive and no lattice table. *)
Module FoldValue := MergeValue NoOps NoMerge.

Module FoldIndex := IndexCode FoldValue.
Module FoldJoin := JoinCode FoldValue FoldIndex.
Module FoldDatabase := DatabaseCode FoldValue FoldIndex.
Module FoldRun := RunCode FoldValue FoldIndex FoldJoin FoldDatabase.
Module FoldRunner := RunnerCode FoldValue FoldIndex FoldJoin FoldDatabase FoldRun.

(** The minimum of positives, at the code of [Pos.min]. *)
Module MinJoin <: DECODED BoundOps PosEncode.
  Definition code := BoundOps.min_code.
  Definition join := Pos.min.

  Lemma join_comm : forall a b, join a b = join b a.
  Proof.
    exact Pos.min_comm.
  Qed.

  Lemma join_assoc : forall a b c, join a (join b c) = join (join a b) c.
  Proof.
    exact Pos.min_assoc.
  Qed.

  Lemma join_idem : forall a, join a a = a.
  Proof.
    exact Pos.min_id.
  Qed.

  Lemma prim_join : forall x y,
    BoundOps.prim code [PosEncode.encode x; PosEncode.encode y] =
      Some (PosEncode.encode (join x y)).
  Proof.
    reflexivity.
  Qed.
End MinJoin.

Module BoundMerge0 := MaxMerge BoundOps.
Module BoundMerge := DecodedMerge BoundOps BoundMerge0 PosEncode MinJoin.

(** The values of the bounds, with the lawful merge of [Pos.min]. *)
Module BoundValue := MergeValue BoundOps BoundMerge.

Module BoundIndex := IndexCode BoundValue.
Module BoundJoin := JoinCode BoundValue BoundIndex.
Module BoundDatabase := DatabaseCode BoundValue BoundIndex.
Module BoundRun := RunCode BoundValue BoundIndex BoundJoin BoundDatabase.
Module BoundRunner := RunnerCode BoundValue BoundIndex BoundJoin BoundDatabase BoundRun.

(** The value that a database of bounds stores at a key, if it stores one. *)
Definition stored (f : positive) (ks : list positive) (db : BoundDatabase.t) : option positive :=
  match fst (BoundDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** Register 3 holds 5, and register 1 copies register 3. *)
Definition prog : list stmt := [Init 3 5; Copy 1 3].

(** Register 1 is at most 10 and at most 3. *)
Definition limits_of_one : list limit := [Below 1 10; Below 1 3].

(** The kind of the head of a clause. *)
Variant head_kind : Type :=
  | KindDerive
  | KindAssign
  | KindUnify
  | KindRewrite.

(** The kind of the head of a clause. *)
Definition kind_of (c : clause positive) : head_kind :=
  match head c with
  | Derive _ _ => KindDerive
  | Assign _ _ _ => KindAssign
  | Unify _ _ => KindUnify
  | Rewrites _ _ => KindRewrite
  end.

(** The tables that the premises of a clause read, in order. *)
Definition read_tables (c : clause positive) : list positive :=
  flat_map (fun p =>
    match p with
    | Holds r _ => [r]
    | Equals f _ _ => [f]
    | Computes _ _ _ => []
    end) (body c).

(** [known prog 1 5] holds, through the copy of register 3. *)
Lemma one_is_known : known prog 1 5.
Proof.
  apply (known_copy prog 1 3 5).
  - simpl. auto.
  - apply known_init. simpl. auto.
Qed.

(** * Declarations *)

Module DeclarationTests.

  (** The clauses of [known] derive rows, and the clause of [fold_known] is a rewrite. The
      closure laws and the congruences of [fold] have no clause. *)
  Example fold_known_is_a_rewrite :
    map kind_of (clauses Folds.spec) = [KindDerive; KindDerive; KindRewrite].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrite reads the relation [known]. *)
  Example rewrite_reads_the_relation :
    map read_tables (clauses Folds.spec) =
      [[Folds.Init_code]; [Folds.Copy_code; Folds.known_code]; [Folds.known_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The rewrite of [simp_bound] reads the lattice table [bound]. *)
  Example rewrite_reads_the_lattice :
    map read_tables (clauses Bounds.spec) = [[Bounds.Below_code]; [Bounds.bound_code]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The relation of constant propagation takes only values. *)
  Example known_takes_values :
    value_tables Folds.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lattice table of the bounds takes only values. *)
  Example bound_takes_values :
    value_tables Bounds.spec = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DeclarationTests.

(** * Runs *)

Module RunTests.

  Local Open Scope positive_scope.

  (** A product by register 1, which holds 5, equals its scaling by 5. *)
  Example product_equals_its_scaling :
    FoldRunner.equal Folds.program (Folds.facts prog) example_limits
      (Folds.encode_term (Mul (Ref 1) (Ref 2))) (Folds.encode_term (Scale 5 (Ref 2))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Register 2 holds no known constant, so a product by it stays apart from a scaling. *)
  Example unknown_register_is_not_scaled :
    FoldRunner.equal Folds.program (Folds.facts prog) example_limits
      (Folds.encode_term (Mul (Ref 2) (Ref 1))) (Folds.encode_term (Scale 5 (Ref 1))) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The run derives the row [known 1 5] through the copy. *)
  Example copy_is_known :
    FoldRunner.holds Folds.known_code [1; 5]
      (snd (FoldRunner.solve Folds.program (Folds.facts prog) example_limits)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The least bound 3 of register 1 is at most 5, so the minimum with 5 is the register. *)
  Example bounded_minimum_is_the_register :
    BoundRunner.equal Bounds.program (Bounds.facts limits_of_one) example_limits
      (Bounds.encode_amount (Min (Reg 1) (Fixed 5))) (Bounds.encode_amount (Reg 1)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The least bound 3 is above 2, so the minimum with 2 stays apart from the register. *)
  Example smaller_amount_stays :
    BoundRunner.equal Bounds.program (Bounds.facts limits_of_one) example_limits
      (Bounds.encode_amount (Min (Reg 1) (Fixed 2))) (Bounds.encode_amount (Reg 1)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The lattice table stores the least bound 3 of register 1. *)
  Example least_bound_is_stored :
    stored Bounds.bound_code [1]
      (snd (BoundRunner.solve Bounds.program (Bounds.facts limits_of_one) example_limits)) =
      Some 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RunTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** An instance of [fold] is a read congruence over the derived rows. *)
  Example fold_gives_read_congruence :
    forall prim, fold prog (Mul (Ref 1) (Ref 2)) (Scale 5 (Ref 2)) ->
    read_congruent prim Folds.spec (derived prim Folds.spec (Folds.inputs prog)) no_values
      (Folds.encode_term (Mul (Ref 1) (Ref 2))) (Folds.encode_term (Scale 5 (Ref 2))).
  Proof.
    intros prim Hfold. exact (Folds.fold_congruent prim prog _ _ Hfold).
  Qed.

  (** The rewrite [fold_known] is a read step over the derived rows. *)
  Example known_rewrite_is_a_step :
    forall prim,
    read_step prim Folds.spec (derived prim Folds.spec (Folds.inputs prog)) no_values
      (Folds.encode_term (Mul (Ref 1) (Ref 2))) (Folds.encode_term (Scale 5 (Ref 2))).
  Proof.
    intros prim. exact (Folds.fold_known_steps prim prog 1 5 (Ref 2) one_is_known).
  Qed.

  (** An instance of [simp] is a read congruence over the rows and the merges of the meaning of
      lattice reads. *)
  Example simp_gives_read_congruence :
    forall t u, simp limits_of_one t u ->
    read_congruent BoundOps.prim Bounds.spec
      (lat_derived BoundOps.prim (prim_merge BoundOps.prim) Bounds.spec
        (Bounds.inputs limits_of_one))
      (lat_merged BoundOps.prim (prim_merge BoundOps.prim) Bounds.spec
        (Bounds.inputs limits_of_one))
      (Bounds.encode_amount t) (Bounds.encode_amount u).
  Proof.
    exact (Bounds.simp_congruent limits_of_one).
  Qed.

End GlueTests.

(** * Theorems *)

Module TheoremTests.

  Local Open Scope positive_scope.

  Module FoldIndexLaws := Index FoldValue.
  Module FoldJoinLaws := Join FoldValue FoldIndexLaws.
  Module FoldDatabaseLaws := Database FoldValue FoldIndexLaws.
  Module FoldRunLaws := Run FoldValue FoldIndexLaws FoldJoinLaws FoldDatabaseLaws.
  Module FoldRunnerLaws :=
    Runner FoldValue FoldIndexLaws FoldJoinLaws FoldDatabaseLaws FoldRunLaws.
  Module FoldFacts :=
    RunnerFacts FoldValue FoldIndexLaws FoldJoinLaws FoldDatabaseLaws FoldRunLaws FoldRunnerLaws.
  Module FoldTheorems := RewriteRead FoldValue FoldIndexLaws FoldJoinLaws FoldDatabaseLaws
    FoldRunLaws FoldRunnerLaws FoldFacts LowerLaws LowerPlan.

  (** In a saturated outcome, a class that represents [Mul (Ref 1) (Ref 2)] also represents
      [Scale 5 (Ref 2)], by [saturate_derived_closed] and the step lemma of [fold_known]. *)
  Example class_of_product_holds_the_scaling : forall db cs i,
    FoldRunnerLaws.saturate Folds.program (Folds.facts prog)
      [Folds.encode_term (Mul (Ref 1) (Ref 2))] example_limits = (Saturated, db, cs) ->
    represents (FoldDatabaseLaws.view db) (Id i) (Folds.encode_term (Mul (Ref 1) (Ref 2))) ->
    represents (FoldDatabaseLaws.view db) (Id i) (Folds.encode_term (Scale 5 (Ref 2))).
  Proof.
    intros db cs i Hsat Hrep.
    apply (FoldTheorems.saturate_derived_closed Folds.spec (Folds.facts prog)
      [Folds.encode_term (Mul (Ref 1) (Ref 2))] example_limits db cs i
      (Folds.encode_term (Mul (Ref 1) (Ref 2)))).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - exact Hsat.
    - exact Hrep.
    - exact (Folds.fold_known_steps FoldValue.prim prog 1 5 (Ref 2) one_is_known).
  Qed.

End TheoremTests.
