(** * Cheapest terms of classes

    [cheapest] builds the constructor inventory of a program, extracts a checked DAG for a class
    and decodes it, after [best_bounded] checks that the cost that the checker reports for the
    DAG is at most the cost of every best entry of the class. [decode] finds the entry of the
    class in the reversed DAG and rebuilds its term from the entries before it.
    For example, [cheapest Math.program db i] is the encoding of [Num 3] when the class [i] of
    [db] holds [Add (Num 1) (Num 2)] and its folding.

    Builds on: the extraction signature, and the run and extraction operations of the engine. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig
  ExtractSig.
From Galois.Front Require Import ExtractionSig.

Import List.ListNotations.

Module ExtractionCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C)
    <: EXTRACTION_OPS V I J D R C X.
  Definition decode (g : extraction_dag V.t) (c : positive) : option (@expr V.t) :=
    decode_rev (rev g) c.
  Definition best_bounded (p : program V.t) (db : D.t) (c : positive)
      (g : extraction_dag V.t) : bool :=
    match X.check_dag db c g with
    | Some n =>
        let r := fst (D.find c db) in
        forallb (fun entry => negb (Pos.eqb (fst entry) r) || N.leb n (fst (snd entry)))
          (X.best (X.inventory (decls V.t p) (planned_slots (R.plan p))) db)
    | None => false
    end.
  Definition cheapest (p : program V.t) (db : D.t) (c : positive) : option (@expr V.t) :=
    match X.extract (X.inventory (decls V.t p) (planned_slots (R.plan p))) db c with
    | Some g => if best_bounded p db c g then decode g c else None
    | None => None
    end.
End ExtractionCode.

Module Extraction (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C)
    <: EXTRACTION_BASE V I J D R C X.
  Include ExtractionCode V I J D R C X.
  Lemma decode_unfold : forall g c, decode g c = decode_rev (rev g) c.
  Proof.
    reflexivity.
  Qed.
  Lemma best_bounded_unfold : forall p db c g,
    best_bounded p db c g =
      match X.check_dag db c g with
      | Some n =>
          let r := fst (D.find c db) in
          forallb (fun entry => negb (Pos.eqb (fst entry) r) || N.leb n (fst (snd entry)))
            (X.best (X.inventory (decls V.t p) (planned_slots (R.plan p))) db)
      | None => false
      end.
  Proof.
    reflexivity.
  Qed.
  Lemma cheapest_unfold : forall p db c,
    cheapest p db c =
      match X.extract (X.inventory (decls V.t p) (planned_slots (R.plan p))) db c with
      | Some g => if best_bounded p db c g then decode g c else None
      | None => None
      end.
  Proof.
    reflexivity.
  Qed.
End Extraction.

Module ExtractionT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) (C : COST_T V) (X : EXTRACT_T V I D C).
  Include Extraction V I J D R C X.
  TimeFun decode.
  TimeFun best_bounded.
  TimeFun cheapest.
End ExtractionT.

Module ExtractionPlan (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X)
    (S : EXTRACTION_SPEC V I J D R C X K) <: EXTRACTION_PLAN V I J D R C X K S.
  Lemma fits_inventory : forall p db,
    S.inventory_fits p db ->
    X.ctor_inventory (X.inventory (decls V.t p) (planned_slots (R.plan p))) db.
  Proof.
  Admitted. (* STUB *)

  Lemma decode_agrees_unfold : forall g c,
    NoDup (map fst g) -> K.decode g c = X.unfold g c.
  Proof.
  Admitted. (* STUB *)

  Lemma best_bounded_spec : forall p db c g, D.wf db -> K.best_bounded p db c g = true ->
    exists n, X.check_dag db c g = Some n /\
      forall m ch, In (D.repr db c, (m, ch))
        (X.best (X.inventory (decls V.t p) (planned_slots (R.plan p))) db) -> (n <= m)%N.
  Proof.
  Admitted. (* STUB *)
End ExtractionPlan.

Module ExtractionProofs (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X) <: EXTRACTION V I J D R C X K.
  Include EXTRACTION_SPEC V I J D R C X K.
  (** The hypotheses of the theorems as a module, so that the plan can take them. *)
  Module Fits <: EXTRACTION_SPEC V I J D R C X K.
    Include EXTRACTION_SPEC V I J D R C X K.
  End Fits.
  Module P := ExtractionPlan V I J D R C X K Fits.

  Lemma cheapest_represents : forall p db c e,
    inventory_fits p db -> K.cheapest p db c = Some e ->
    represents (D.view db) (Id c) e.
  Proof.
  Admitted. (* STUB *)

  Lemma cheapest_optimal : forall p db c e e',
    inventory_fits p db -> K.cheapest p db c = Some e ->
    represents (D.view db) (Id c) e' ->
    (X.tree_cost e <= X.tree_cost e')%N.
  Proof.
  Admitted. (* STUB *)
End ExtractionProofs.
