(** * Cheapest terms of classes

    [cheapest] returns the cheapest term that a class of a database represents. It builds the
    constructor inventory from the declarations of a program and its planned slots, asks the
    engine to extract a checked DAG for the class, and [decode] reads the DAG back as an
    expression. The engine keeps one best entry for each class ([best_nodup]), so the extracted
    DAG has the least cost of the class. A returned term is represented by the class
    ([cheapest_represents]), and no term that the class represents costs less
    ([cheapest_optimal]). The conditions [inventory_fits] say that the database matches the
    declarations and the slots of the program. Decoding unfolds the DAG into a tree, which can
    be exponentially larger than the DAG, so the time bounds count the nodes of the returned
    term ([expr_size]).
    For example, after saturating [Add (Num 1) (Num 2)] with the folding rules, [cheapest] of
    its class is the encoding of [Num 3], which costs less than the sum.

    Main results
    - [cheapest_represents] A returned term is represented by the class.
    - [cheapest_optimal] No term that the class represents costs less than the returned term.
    - [decode_complexity] Decoding reverses the DAG and scans it once for each node of the
      returned term.
    - [cheapest_complexity] The cheapest term costs planning, the inventory, the extraction of
      the engine and the decoding of a DAG with at most one entry for each constructor row.

    Builds on: the program syntax, the exact model, the run contracts and the extraction
    contracts of the engine. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig
  ExtractSig.

Import List.ListNotations.
Import ComplexityNotations.

(** * Decoding *)

(** Resolving a row of a DAG replaces literals directly and looks up its class children. *)
Fixpoint decode_cells {V} (resolve : positive -> option (@expr V)) (k : list (cell V))
    : option (list (@expr V)) :=
  match k with
  | [] => Some []
  | Val v :: rest =>
    match decode_cells resolve rest with
    | Some es => Some (ELit v :: es)
    | None => None
    end
  | Id i :: rest =>
    match resolve i, decode_cells resolve rest with
    | Some e, Some es => Some (e :: es)
    | _, _ => None
    end
  end.
TimeFun decode_cells.

(** A scan of the reversed DAG decodes the entry of a class through the entries before it. The
    scan shortens its list at every call, so it terminates structurally. *)
Fixpoint decode_rev {V} (g : extraction_dag V) (c : positive) : option (@expr V) :=
  match g with
  | [] => None
  | (i, (f, k)) :: rest =>
    if Pos.eqb c i then
      match decode_cells (decode_rev rest) k with
      | Some es => Some (EApp f es)
      | None => None
      end
    else decode_rev rest c
  end.
TimeFun decode_rev.

(** The slots that a plan reserves, in the order of the compiled plan. *)
Definition planned_slots {V} (cp : compiled V) : list (positive * list nat) :=
  match cp with
  | Compiled _ sl _ _ => sl
  end.
TimeFun planned_slots.

(** * Measures *)

(** The number of nodes of an expression. *)
Fixpoint expr_size {V} (e : @expr V) : nat :=
  match e with
  | ELit _ => 1
  | EApp _ args => S (fold_right (fun a n => expr_size a + n) 0 args)
  end.

(** The number of nodes of a returned expression, or zero when there is none. *)
Definition result_size {V} (o : option (@expr V)) : nat :=
  match o with
  | Some e => expr_size e
  | None => 0
  end.

(** The widest cell of the rows of a DAG. A scan for a child of a row compares the child with
    the identifiers of the entries, so it pays for the bits of the child. *)
Definition dag_width {V} (encode : V -> positive) (g : extraction_dag V) : nat :=
  fold_right (fun entry n =>
    fold_right (fun c m => Nat.max (cell_bits encode c) m) n (snd (snd entry))) 0 g.

(** * Operations *)

Module Type EXTRACTION_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C).
  (** The expression of a class in a DAG. *)
  Parameter decode : extraction_dag V.t -> positive -> option (@expr V.t).
  (** The cheapest term of a class, by the inventory of the declarations and planned slots. *)
  Parameter cheapest : program V.t -> D.t -> positive -> option (@expr V.t).
End EXTRACTION_OPS.

(** * Laws *)

Module Type EXTRACTION_LAWS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C)
    (Import K : EXTRACTION_OPS V I J D R C X).
  (** Decoding scans the reversed DAG. *)
  Parameter decode_unfold : forall g c, decode g c = decode_rev (rev g) c.
  (** The cheapest term decodes the extracted DAG of the class. *)
  Parameter cheapest_unfold : forall p db c,
    cheapest p db c =
      match X.extract (X.inventory (decls V.t p) (planned_slots (R.plan p))) db c with
      | Some g => decode g c
      | None => None
      end.
End EXTRACTION_LAWS.

Module Type EXTRACTION_BASE (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C) :=
  EXTRACTION_OPS V I J D R C X <+ EXTRACTION_LAWS V I J D R C X.

(** * Time *)

Module Type EXTRACTION_TIME (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (R : RUN_T V I J D) (C : COST_T V) (X : EXTRACT_T V I D C)
    (Import K : EXTRACTION_BASE V I J D R C X).
  Parameter T_decode : extraction_dag V.t -> positive -> N.
  Parameter T_cheapest : program V.t -> D.t -> positive -> N.
  Parameter c_extraction : N.
  (** The constructor inventory of a program, from its declarations and its planned slots. *)
  Definition inventory_of (p : program V.t) : list (positive * (N * nat)) :=
    X.inventory (decls V.t p) (planned_slots (R.plan p)).
  (** Decoding reverses the DAG and then scans it once for each node of the returned term. Each
      step of a scan compares an entry with the class or with a cell of the DAG. *)
  Parameter T_decode_le : forall g c e, decode g c = Some e ->
    (T_decode g c <= c_extraction * N.of_nat ((length g + 1) * (length g + 1) +
      (expr_size e + 1) * (length g + 1) * (Pos.size_nat c + dag_width V.encode g + 1)))%N.
  (** Decoding is quadratic in the length of the DAG, and linear in the returned term, in the
      length of the DAG and in the width of the compared identifiers. *)
  Parameter decode_complexity :
    T_decode g c ∈
      𝑂(N.of_nat ((length g + 1) * (length g + 1) +
        (expr_size e + 1) * (length g + 1) * (Pos.size_nat c + dag_width V.encode g + 1)))
      for (g, c, e) | decode g c = Some e.
  (** The cheapest term pays for planning, for the inventory, for the extraction and for
      decoding the extracted DAG. *)
  Parameter T_cheapest_split : forall p db c,
    (T_cheapest p db c <=
      R.T_plan p + X.T_inventory (decls V.t p) (planned_slots (R.plan p)) +
      X.T_extract (inventory_of p) db c +
      match X.extract (inventory_of p) db c with
      | Some g => T_decode g c
      | None => 0
      end + c_extraction)%N.
  (** The cheapest term costs the cube of the program for planning, the layout for the
      inventory, and the best rows and their traversal at the unit for the extraction. The
      extracted DAG has at most one entry for each constructor row, and its identifiers fit in
      the unit, so decoding costs the returned term times the constructor rows at the unit. *)
  Parameter cheapest_complexity :
    T_cheapest p db c ∈
      𝑂(N.of_nat ((R.size_program p + 1) * (R.size_program p + 1) * (R.size_program p + 1) +
        (layout_bits (decls V.t p) (planned_slots (R.plan p)) + 1) *
          (Nat.log2 (length (planned_slots (R.plan p))) + 1) +
        (inventory_bits (inventory_of p) + 2 * ((X.R db + 1) * (X.a db + 1)) +
          (X.R db + 1) * (Nat.log2 (X.R db) + 1)) * (D.unit db + 1) * (X.cost_width db + 1) +
        (X.R db + 1) * (X.R db + 1) +
        (result_size (cheapest p db c) + 1) * (X.R db + 1) * (D.unit db + 1)))
      for (p, db, c) | D.wf db /\ D.canonical db /\ X.ctor_inventory (inventory_of p) db.
End EXTRACTION_TIME.

Module Type EXTRACTION_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) (C : COST_T V) (X : EXTRACT_T V I D C) :=
  EXTRACTION_BASE V I J D R C X <+ EXTRACTION_TIME V I J D R C X.

(** * Specification *)

Module Type EXTRACTION_SPEC (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X).
  (** The database is well formed and canonical, its slots are the planned slots of the
      program, its kinds and sorts are the declared ones, and the plan gives every constructor
      the full slot of its arity. These are the conditions under which the inventory of the
      program fits the database. *)
  Definition inventory_fits (p : program V.t) (db : D.t) : Prop :=
    D.wf db /\ D.canonical db /\
    D.slots db = planned_slots (R.plan p) /\
    (forall f, kind (D.view db) f = lookup_kind (decls V.t p) f) /\
    view_sorted (lookup_sorts (decls V.t p)) (D.view db) /\
    (forall f ss, lookup_kind (decls V.t p) f = Some OId ->
      lookup_sorts (decls V.t p) f = Some ss ->
      In (f, seq 0 (S (length ss))) (planned_slots (R.plan p))).
End EXTRACTION_SPEC.

(** * Theorems *)

Module Type EXTRACTION_THEOREMS (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X)
    (Import S : EXTRACTION_SPEC V I J D R C X K).
  (** A returned term is represented by the class. *)
  Parameter cheapest_represents : forall p db c e,
    inventory_fits p db -> K.cheapest p db c = Some e ->
    represents (D.view db) (Id c) e.
  (** No term that the class represents costs less than the returned term. *)
  Parameter cheapest_optimal : forall p db c e e',
    inventory_fits p db -> K.cheapest p db c = Some e ->
    represents (D.view db) (Id c) e' ->
    (X.tree_cost e <= X.tree_cost e')%N.
End EXTRACTION_THEOREMS.

Module Type EXTRACTION (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X) :=
  EXTRACTION_SPEC V I J D R C X K <+ EXTRACTION_THEOREMS V I J D R C X K.

(** * Proof plan *)

Module Type EXTRACTION_PLAN (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (C : COST V) (X : EXTRACT V I D C)
    (K : EXTRACTION_BASE V I J D R C X)
    (Import S : EXTRACTION_SPEC V I J D R C X K).
  (** The conditions on a database give the inventory contract of the engine. *)
  Parameter fits_inventory : forall p db,
    inventory_fits p db ->
    X.ctor_inventory (X.inventory (decls V.t p) (planned_slots (R.plan p))) db.
  (** Decoding agrees with the unfolding of the engine on a DAG with distinct identifiers. *)
  Parameter decode_agrees_unfold : forall g c,
    NoDup (map fst g) -> K.decode g c = X.unfold g c.
End EXTRACTION_PLAN.
