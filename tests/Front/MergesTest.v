(** * Closure of lattice tables under their merges

    A clause that reads a lattice table sees a merge of the values that the clauses assign, so
    the command proves that the relation of the table is closed under its merge, as the lemma
    [<R>_merges]. When the merge returns neither of its arguments and no constructor merges two
    values, a lemma that the client proves before the command gives the closure. The command
    finds it by the name [<R>_merges] or in the hint database [egglog_merges]. [common] keeps
    the greatest common divisor of the numbers at a node, and [multiple] their least common
    multiple. For example, the numbers 12 and 18 at node 1 give the stored divisor 6.

    Groups:
    - [ClosureTests] The lemma [<R>_merges] of the program is the lemma of the client.
    - [RunTests] Runs store the merges of the numbers at each node.
    - [GlueTests] The glue lemmas relate the relations to their assigned values.
    - [RejectionTests] The command stops when no lemma gives the closure.

    Builds on: the derive command, the meaning of lattice reads, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice RunnerSig Runner Derive Encode.
Import List.ListNotations.

(** * Fixtures *)

(** The greatest common divisor of natural numbers. *)
Egglog Primitives GcdOps N.gcd.

(** The least common multiple of natural numbers. *)
Egglog Primitives LcmOps N.lcm.

(** [common nums n d] says that [d] is the greatest common divisor of some numbers at node [n]
    of [nums]. *)
Inductive common (nums : list (positive * N)) : positive -> N -> Prop :=
  | common_num n k : In (n, k) nums -> common nums n k
  | common_step n d k : common nums n d -> In (n, k) nums -> common nums n (N.gcd d k).

(** The divisors of two sets of numbers at a node divide each other's numbers, so their greatest
    common divisor is the divisor of both sets. *)
Lemma common_merges : forall nums n a b,
  common nums n a -> common nums n b -> common nums n (N.gcd a b).
Proof.
  intros nums n a b Ha Hb.
  induction Hb as [n k Hk | n d k _ IH Hk].
  - exact (common_step nums n a k Ha Hk).
  - rewrite N.gcd_assoc. exact (common_step nums n (N.gcd a d) k (IH Ha) Hk).
Qed.

Egglog Common from common with GcdOps merge common N.gcd.

(** [multiple nums n m] says that [m] is the least common multiple of some numbers at node [n]
    of [nums]. *)
Inductive multiple (nums : list (positive * N)) : positive -> N -> Prop :=
  | multiple_num n k : In (n, k) nums -> multiple nums n k
  | multiple_step n d k : multiple nums n d -> In (n, k) nums -> multiple nums n (N.lcm d k).

(** The least common multiple of two multiples at a node is a multiple there. *)
Lemma multiple_lcm_closed : forall nums n a b,
  multiple nums n a -> multiple nums n b -> multiple nums n (N.lcm a b).
Proof.
  intros nums n a b Ha Hb.
  induction Hb as [n k Hk | n d k _ IH Hk].
  - exact (multiple_step nums n a k Ha Hk).
  - rewrite N.lcm_assoc. exact (multiple_step nums n (N.lcm a d) k (IH Ha) Hk).
Qed.

#[local] Hint Resolve multiple_lcm_closed : egglog_merges.

Egglog Multiples from multiple with LcmOps merge multiple N.lcm.

(** The values of [GcdOps], merged by the greatest common divisor. *)
Module GcdValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := GcdOps.prim.
  Definition merge := prim_merge GcdOps.prim.
End GcdValue.

Module GcdIndex := IndexCode GcdValue.
Module GcdJoin := JoinCode GcdValue GcdIndex.
Module GcdDatabase := DatabaseCode GcdValue GcdIndex.
Module GcdRun := RunCode GcdValue GcdIndex GcdJoin GcdDatabase.
Module GcdRunner := RunnerCode GcdValue GcdIndex GcdJoin GcdDatabase GcdRun.

(** The values of [LcmOps], merged by the least common multiple. *)
Module LcmValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := LcmOps.prim.
  Definition merge := prim_merge LcmOps.prim.
End LcmValue.

Module LcmIndex := IndexCode LcmValue.
Module LcmJoin := JoinCode LcmValue LcmIndex.
Module LcmDatabase := DatabaseCode LcmValue LcmIndex.
Module LcmRun := RunCode LcmValue LcmIndex LcmJoin LcmDatabase.
Module LcmRunner := RunnerCode LcmValue LcmIndex LcmJoin LcmDatabase LcmRun.

(** The value that a database of [GcdOps] stores at a key, if it stores one. *)
Definition gcd_stored (f : positive) (ks : list positive) (db : GcdDatabase.t) :
    option positive :=
  match fst (GcdDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** The value that a database of [LcmOps] stores at a key, if it stores one. *)
Definition lcm_stored (f : positive) (ks : list positive) (db : LcmDatabase.t) :
    option positive :=
  match fst (LcmDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition example_limits : limits := Limits 50%N 1000%N.

(** The numbers 12 and 18 at node 1, and 4 and 6 at node 2. *)
Definition numbers : list (positive * N) :=
  [(1%positive, 12%N); (1%positive, 18%N); (2%positive, 4%N); (2%positive, 6%N)].

(** * Closure lemmas *)

Module ClosureTests.

  (** The closure of [common] is the lemma [common_merges] of the client, found by its name. *)
  Example named_lemma_gives_the_closure : forall nums n a b,
    common nums n a -> common nums n b -> common nums n (N.gcd a b).
  Proof.
    exact Common.common_merges.
  Qed.

  (** The closure of [multiple] comes from the lemma that the client adds to the hint database
      [egglog_merges]. *)
  Example hint_gives_the_closure : forall nums n a b,
    multiple nums n a -> multiple nums n b -> multiple nums n (N.lcm a b).
  Proof.
    exact Multiples.multiple_merges.
  Qed.

End ClosureTests.

(** * Runs *)

Module RunTests.

  Local Open Scope positive_scope.

  (** The run of the greatest common divisors. *)
  Definition common_run : stop * GcdDatabase.t :=
    GcdRunner.solve Common.program (Common.facts numbers) example_limits.

  (** The run of the least common multiples. *)
  Definition multiple_run : stop * LcmDatabase.t :=
    LcmRunner.solve Multiples.program (Multiples.facts numbers) example_limits.

  (** The divisors stop shrinking, so the run saturates. *)
  Example divisors_saturate :
    fst common_run = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 1 stores 6, the greatest common divisor of 12 and 18, which neither number is. *)
  Example divisor_of_both_numbers_is_stored :
    gcd_stored Common.common_code [1] (snd common_run) = Some (NEncode.encode 6%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Node 2 stores 12, the least common multiple of 4 and 6. *)
  Example multiple_of_both_numbers_is_stored :
    lcm_stored Multiples.multiple_code [2] (snd multiple_run) = Some (NEncode.encode 12%N).
  Proof.
    vm_compute. reflexivity.
  Qed.

End RunTests.

(** * Glue *)

Module GlueTests.

  Local Open Scope positive_scope.

  (** The divisor 6 of 12 and 18 is assigned at node 1. *)
  Example divisor_gives_assigned_value :
    lat_assigned GcdOps.prim (prim_merge GcdOps.prim) Common.spec (Common.inputs numbers)
      Common.common_code [1] (NEncode.encode 6%N).
  Proof.
    apply (proj1 (Common.common_spec numbers 1 6%N)).
    apply (common_step numbers 1 12%N 18%N).
    - apply common_num. simpl. auto.
    - simpl. auto.
  Qed.

End GlueTests.

(** * Rejections *)

Module RejectionTests.

  (** [divisor] has the shape of [common], and no lemma gives its closure under [N.gcd]. *)
  Inductive divisor (nums : list (positive * N)) : positive -> N -> Prop :=
    | divisor_num n k : In (n, k) nums -> divisor nums n k
    | divisor_step n d k : divisor nums n d -> In (n, k) nums -> divisor nums n (N.gcd d k).

  (** A clause reads [divisor], and no lemma proves its closure. *)
  Fail Egglog Divisors from divisor with GcdOps merge divisor N.gcd.

End RejectionTests.
