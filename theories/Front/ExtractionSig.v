(** * Cheapest terms of classes

    [cheapest] returns the cheapest term that a class of a database represents. It builds the
    constructor inventory from the declarations of a program and its planned slots, asks the
    engine to extract a checked DAG for the class, and [decode] reads the DAG back as an
    expression. Before it decodes, [best_bounded] checks at run time that the cost that the
    checker reports for the DAG is at most the cost of every best entry of the class, and
    [cheapest] returns nothing when the check fails. A returned term is represented by the
    class ([cheapest_represents]), and no term that the class represents costs less
    ([cheapest_optimal]). The conditions [inventory_fits] say that the database matches the
    declarations and the slots of the program.
    For example, after saturating [Add (Num 1) (Num 2)] with the folding rules, [cheapest] of
    its class is the encoding of [Num 3], which costs less than the sum.

    Main results
    - [cheapest_represents] A returned term is represented by the class.
    - [cheapest_optimal] No term that the class represents costs less than the returned term.

    Builds on: the program syntax, the exact model, the run contracts and the extraction
    contracts of the engine. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig
  ExtractSig.

Import List.ListNotations.

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

(** * Operations *)

Module Type EXTRACTION_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C).
  (** The expression of a class in a DAG. *)
  Parameter decode : extraction_dag V.t -> positive -> option (@expr V.t).
  (** Whether the cost that the checker reports for a DAG of a class is at most the cost of
      every best entry of the representative of the class. *)
  Parameter best_bounded : program V.t -> D.t -> positive -> extraction_dag V.t -> bool.
  (** The cheapest term of a class, by the inventory of the declarations and planned slots. *)
  Parameter cheapest : program V.t -> D.t -> positive -> option (@expr V.t).
End EXTRACTION_OPS.

(** * Laws *)

Module Type EXTRACTION_LAWS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C)
    (Import K : EXTRACTION_OPS V I J D R C X).
  (** Decoding scans the reversed DAG. *)
  Parameter decode_unfold : forall g c, decode g c = decode_rev (rev g) c.
  (** The bound check compares the checked cost of the DAG with every best entry of the
      representative of the class. *)
  Parameter best_bounded_unfold : forall p db c g,
    best_bounded p db c g =
      match X.check_dag db c g with
      | Some n =>
          let r := fst (D.find c db) in
          forallb (fun entry => negb (Pos.eqb (fst entry) r) || N.leb n (fst (snd entry)))
            (X.best (X.inventory (decls V.t p) (planned_slots (R.plan p))) db)
      | None => false
      end.
  (** The cheapest term decodes the extracted DAG of the class when the DAG passes the bound
      check. *)
  Parameter cheapest_unfold : forall p db c,
    cheapest p db c =
      match X.extract (X.inventory (decls V.t p) (planned_slots (R.plan p))) db c with
      | Some g => if best_bounded p db c g then decode g c else None
      | None => None
      end.
End EXTRACTION_LAWS.

Module Type EXTRACTION_BASE (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (R : RUN_OPS V I J D) (C : COST_OPS V) (X : EXTRACT_OPS V I D C) :=
  EXTRACTION_OPS V I J D R C X <+ EXTRACTION_LAWS V I J D R C X.

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
  (** A DAG that passes the bound check has a checked cost at most the cost of every best
      entry of the representative of its class. *)
  Parameter best_bounded_spec : forall p db c g, D.wf db -> K.best_bounded p db c g = true ->
    exists n, X.check_dag db c g = Some n /\
      forall m ch, In (D.repr db c, (m, ch))
        (X.best (X.inventory (decls V.t p) (planned_slots (R.plan p))) db) -> (n <= m)%N.
End EXTRACTION_PLAN.
