(** * Time of cheapest terms

    The timed module of [cheapest]. It derives the time functions of decoding and of
    [cheapest], and bounds them. Decoding scans the reversed DAG once for each node of the
    returned term. [cheapest] pays for planning, for the inventory, for the extraction of the
    engine and for decoding a DAG with at most one entry for each constructor row of the
    database.
    For example, decoding the DAG of [Add (Num 1) (Num 1)] with one shared entry for [Num 1]
    scans the DAG for five nodes.

    Builds on: the extraction signature, the extraction functor, and the time contracts of the
    run and of the extraction of the engine. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig
  ExtractSig.
From Galois.Front Require Import ExtractionSig Extraction.

Import List.ListNotations.
Import ComplexityNotations.

Module ExtractionT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) (C : COST_T V) (X : EXTRACT_T V I D C) <: EXTRACTION_T V I J D R C X.
  Include Extraction V I J D R C X.
  TimeFun decode.
  TimeFun cheapest.
  Definition c_extraction : N := 1. (* STUB *)
  Definition inventory_of (p : program V.t) : list (positive * (N * nat)) :=
    X.inventory (decls V.t p) (planned_slots (R.plan p)).

  (* STUB: [List.T_rev_le] for the reversal, then an induction on the reversed DAG that charges
     each node of the returned term one scan. A scan step pays [Std.Pos.T_eqb_le] for the class
     or the child that it looks for. *)
  Lemma T_decode_le : forall g c e, decode g c = Some e ->
    (T_decode g c <= c_extraction * N.of_nat ((length g + 1) * (length g + 1) +
      (expr_size e + 1) * (length g + 1) * (Pos.size_nat c + dag_width V.encode g + 1)))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma decode_complexity :
    T_decode g c ∈
      𝑂(N.of_nat ((length g + 1) * (length g + 1) +
        (expr_size e + 1) * (length g + 1) * (Pos.size_nat c + dag_width V.encode g + 1)))
      for (g, c, e) | decode g c = Some e.
  Proof.
  Admitted. (* STUB *)

  Lemma T_cheapest_split : forall p db c,
    (T_cheapest p db c <=
      R.T_plan p + X.T_inventory (decls V.t p) (planned_slots (R.plan p)) +
      X.T_extract (inventory_of p) db c +
      match X.extract (inventory_of p) db c with
      | Some g => T_decode g c
      | None => 0
      end + c_extraction)%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [T_cheapest_split] with [R.plan_complexity], [X.inventory_complexity] and
     [X.extract_complexity]. An extracted DAG is valid by [X.extract_checked] and
     [X.check_dag_sound], so [decode_agrees_unfold] of the plan decodes it. Its entries are
     distinct constructor rows, so [X.R_spec] bounds its length, and [D.wmark_cells] bounds its
     class and its cells by the unit. *)
  Lemma cheapest_complexity :
    T_cheapest p db c ∈
      𝑂(N.of_nat ((R.size_program p + 1) * (R.size_program p + 1) * (R.size_program p + 1) +
        (layout_bits (decls V.t p) (planned_slots (R.plan p)) + 1) *
          (Nat.log2 (length (planned_slots (R.plan p))) + 1) +
        (inventory_bits (inventory_of p) + 2 * ((X.R db + 1) * (X.a db + 1)) +
          (X.R db + 1) * (Nat.log2 (X.R db) + 1)) * (D.unit db + 1) * (X.cost_width db + 1) +
        (X.R db + 1) * (X.R db + 1) +
        (result_size (cheapest p db c) + 1) * (X.R db + 1) * (D.unit db + 1)))
      for (p, db, c) | D.wf db /\ D.canonical db /\ X.ctor_inventory (inventory_of p) db.
  Proof.
  Admitted. (* STUB *)
End ExtractionT.
