(** * Databases with congruence rebuilding

    Databases store rows, identifier equalities and indexes of canonical tuples.
    For example, rebuilding merges two constructor outputs whose keys become equal.
    Builds on: ValueSig, IndexSig, Syntax and Model. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time.
From Galois.Egglog Require Import ValueSig IndexSig Syntax Model.

Import List.ListNotations.

Inductive cell_rel {V : Type} (R : positive -> positive -> Prop)
    : cell V -> cell V -> Prop :=
  | cell_rel_id i j : R i j -> cell_rel R (Id i) (Id j)
  | cell_rel_val v : cell_rel R (Val v) (Val v).

Definition option_list {A : Type} (o : option A) : list A :=
  match o with
  | None => []
  | Some a => [a]
  end.
TimeFun option_list.

Scheme All for cell_rel.
Scheme All for Forall2.

Inductive fd_congruence {V : Type} (w : view (V := V)) : positive -> positive -> Prop :=
  | cong_same i j : same w i j -> fd_congruence w i j
  | cong_fd f k1 k2 i j : row w f k1 (Some (Id i)) ->
      row w f k2 (Some (Id j)) ->
      Forall2 (cell_rel (fd_congruence w)) k1 k2 -> fd_congruence w i j
  | cong_sym i j : fd_congruence w i j -> fd_congruence w j i
  | cong_trans i j k : fd_congruence w i j -> fd_congruence w j k -> fd_congruence w i k.

Module Type DATABASE_OPS (V : VALUE_OPS) (I : INDEX_OPS V).
  Parameter t : Type.
  Parameter init : list decl -> list (positive * list nat) -> t.
  Parameter find : positive -> t -> positive * t.
  Parameter lookup : positive -> list (cell V.t) -> t -> option (option (cell V.t)) * t.
  Parameter make : positive -> list (cell V.t) -> t -> positive * t.
  Parameter put : positive -> list (cell V.t) -> option (cell V.t) -> t -> t.
  Parameter union : positive -> positive -> t -> t.
  Parameter rebuild : t -> t.
  Parameter index : nat -> bool -> t -> I.t.
  Parameter advance : t -> t.
  Parameter changed : t -> bool.
  Parameter ids : t -> N.
End DATABASE_OPS.

Module Type DATABASE_SPEC (V : VALUE_OPS) (I : INDEX_OPS V)
    (Import X : DATABASE_OPS V I).
End DATABASE_SPEC.

Module Type DATABASE_LAWS (V : VALUE) (I : INDEX V) (Import X : DATABASE_OPS V I).
  (* spec: wf view repr pending kind_ok old conflict fresh_id extends_by slot_of permute merged *)
  Parameter wf : t -> Prop.
  Parameter view : t -> Model.view (V := V.t).
  Parameter repr : t -> positive -> positive.
  Parameter pending : t -> nat.
  Parameter kind_ok : t -> positive -> list (cell V.t) -> option (cell V.t) -> Prop.
  Parameter old : t -> positive -> list (cell V.t) -> option (option (cell V.t)).
  Parameter conflict : t -> positive -> list (cell V.t) -> option (cell V.t) ->
    positive -> positive -> Prop.
  Parameter fresh_id : t -> positive -> Prop.
  Parameter extends_by : t -> t -> positive -> list (cell V.t) -> positive -> Prop.
  Parameter slot_of : t -> nat -> option (positive * list nat).
  Parameter permute : list nat -> list (cell V.t) -> list (cell V.t).
  Parameter merged : t -> positive -> list (option (cell V.t)) -> option (cell V.t).
  Definition canon (db : t) (c : cell V.t) : cell V.t :=
    match c with
    | Id i => Id (repr db i)
    | Val v => Val v
    end.
  Definition canonical (db : t) : Prop :=
    forall f k o, row (view db) f k o ->
    forall i, In (Id i) (k ++ option_list o) -> repr db i = i.
  Definition cong (db : t) := fd_congruence (view db).
  Definition combine (db : t) (f : positive) (previous : option (option (cell V.t)))
      (o : option (cell V.t)) : option (cell V.t) :=
    match previous, kind (view db) f, o with
    | Some (Some (Val a)), Some (OLat m), Some (Val b) => Some (Val (V.merge m a b))
    | Some old, _, _ => old
    | None, _, _ => o
    end.
  Definition out_le (db : t) (f : positive) (a b : option (cell V.t)) : Prop :=
    match a, b with
    | None, _ => True
    | Some c, Some d => cell_le V.merge (view db) f c d
    | _, _ => False
    end.
  Definition present_put (w : Model.view (V := V.t)) (f : positive)
      (k : list (cell V.t)) (o : option (cell V.t)) : Prop :=
    exists d, row w f k d /\
      match o, d with
      | None, _ => True
      | Some a, Some b => cell_le V.merge w f a b
      | _, _ => False
      end.
  (** Identifier equality is equality of representatives. *)
  Parameter same_repr : forall db i j, wf db ->
    (same (view db) i j <-> repr db i = repr db j).
  (** Initialization creates a well-formed database. *)
  Parameter wf_init : forall ds sl, wf (init ds sl).
  (** Kind-correct insertion keeps the database well formed. *)
  Parameter wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  (** Constructor allocation keeps the database well formed. *)
  Parameter wf_make : forall f k db, wf db -> wf (snd (make f k db)).
  (** Equality insertion keeps the database well formed. *)
  Parameter wf_union : forall i j db, wf db -> wf (union i j db).
  (** Rebuilding keeps the database well formed. *)
  Parameter wf_rebuild : forall db, wf db -> wf (rebuild db).
  (** Advancing clears the change flag without changing the view. *)
  Parameter wf_advance : forall db, wf db ->
    wf (advance db) /\ view (advance db) = view db /\ changed (advance db) = false.
  (** Find returns the representative without changing the view. *)
  Parameter find_spec : forall i db, wf db ->
    fst (find i db) = repr db i /\ view (snd (find i db)) = view db.
  (** Each function key has one output. *)
  Parameter row_functional : forall db f k o1 o2, wf db ->
    row (view db) f k o1 -> row (view db) f k o2 -> o1 = o2.
  (** Insertion changes precisely the canonical key and combines its output. *)
  Parameter put_rows : forall f k o db, wf db -> kind_ok db f k o ->
    let ck := map (canon db) k in let co := option_map (canon db) o in
    forall f' k' o', row (view (put f k o db)) f' k' o' <->
      (row (view db) f' k' o' /\ (f', k') <> (f, ck)) \/
      (f' = f /\ k' = ck /\ combine db f (old db f ck) co = o').
  (** Identifier output conflicts add precisely their equality closure. *)
  Parameter put_same : forall f k o db i j, wf db -> kind_ok db f k o ->
    (same (view (put f k o db)) i j <->
      clos_refl_sym_trans positive
        (fun a b => same (view db) a b \/ conflict db f k o a b) i j).
  (** A quiet insertion already has its requested row represented. *)
  Parameter put_quiet : forall f k o db, wf db -> kind_ok db f k o ->
    changed db = false -> changed (put f k o db) = false ->
    view (put f k o db) = view db /\ present_put (view db) f (map (canon db) k) o.
  (** Make reuses a canonical constructor output or allocates a fresh identifier. *)
  Parameter make_spec : forall f k db, wf db -> kind (view db) f = Some OId ->
    let '(i, db') := make f k db in
    (exists j, row (view db) f (map (canon db) k) (Some (Id j)) /\
      i = repr db j /\ db' = db) \/
    (fresh_id db i /\ row (view db') f (map (canon db) k) (Some (Id i)) /\
      extends_by db db' f k i).
  (** Union adds precisely the requested equality closure. *)
  Parameter union_same : forall i j db k l, wf db ->
    (same (view (union i j db)) k l <->
      clos_refl_sym_trans positive (fun a b => same (view db) a b \/ (a, b) = (i, j)) k l).
  (** Union queues equality work without changing rows. *)
  Parameter union_rows : forall i j db, wf db ->
    row (view (union i j db)) = row (view db).
  (** Rebuilding canonicalizes every row and empties pending work. *)
  Parameter rebuild_canonical : forall db, wf db ->
    canonical (rebuild db) /\ pending (rebuild db) = 0.
  (** Rebuilding computes functional-dependency congruence. *)
  Parameter rebuild_same : forall db i j, wf db ->
    (same (view (rebuild db)) i j <-> cong db i j).
  (** Every old row survives canonicalization and output merging. *)
  Parameter rebuild_keeps : forall db f k o, wf db -> row (view db) f k o ->
    exists o', row (view (rebuild db)) f (map (canon (rebuild db)) k) o' /\
      out_le (rebuild db) f (option_map (canon (rebuild db)) o) o'.
  (** Every rebuilt row comes from a nonempty group of old rows. *)
  Parameter rebuild_from : forall db f k' o', wf db -> row (view (rebuild db)) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view db) f (fst ko) (snd ko) /\
        map (canon (rebuild db)) (fst ko) = k') srcs /\
      o' = merged (rebuild db) f (map snd srcs).
  (** Canonical databases without pending work rebuild to themselves. *)
  Parameter rebuild_idle : forall db, wf db -> canonical db -> pending db = 0 -> rebuild db = db.
  (** A database without pending work respects constructor congruence. *)
  Parameter rebuild_congruent : forall db f k1 k2 i j, wf db -> pending db = 0 ->
    row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) ->
    Forall2 (cell_rel (same (view db))) k1 k2 -> same (view db) i j.
  (** Every indexed tuple comes from a row in its declared slot. *)
  Parameter index_all : forall db s new u, wf db -> I.mem (index s new db) u ->
    exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
      u = permute perm (k ++ option_list o).
  (** The full index contains every row in its slot. *)
  Parameter index_all_complete : forall db s f perm k o, wf db ->
    slot_of db s = Some (f, perm) -> row (view db) f k o ->
    I.mem (index s false db) (permute perm (k ++ option_list o)).
  (** Slot indexes have the declared permutation arity. *)
  Parameter index_wf : forall db s new f perm, wf db -> slot_of db s = Some (f, perm) ->
    I.wf (length perm) (index s new db).
End DATABASE_LAWS.

Module Type DATABASE (V : VALUE) (I : INDEX V) :=
  DATABASE_OPS V I <+ DATABASE_SPEC V I <+ DATABASE_LAWS V I.

Module Type DATABASE_TIME (V : VALUE_T) (I : INDEX_T V) (Import X : DATABASE V I).
  (* spec: unit slots_of potential num_slots *)
  Parameter unit : t -> nat.
  Parameter slots_of : t -> positive -> nat.
  Parameter potential : N -> t -> nat.
  Parameter num_slots : t -> nat.
  Parameter T_init : list decl -> list (positive * list nat) -> nat.
  Parameter T_find : positive -> t -> nat.
  Parameter T_lookup : positive -> list (cell V.t) -> t -> nat.
  Parameter T_make : positive -> list (cell V.t) -> t -> nat.
  Parameter T_put : positive -> list (cell V.t) -> option (cell V.t) -> t -> nat.
  Parameter T_union : positive -> positive -> t -> nat.
  Parameter T_rebuild : t -> nat.
  Parameter T_index : nat -> bool -> t -> nat.
  Parameter T_advance T_changed T_ids : t -> nat.
  Parameter c_db : nat.
  (** Initialization starts without amortized debt. *)
  Parameter potential_init : forall B ds sl, potential B (init ds sl) = 0.
  (** Insertion pays for all slots and the logarithmic identifier budget. *)
  Parameter T_put_amort : forall B f k o db, wf db -> (ids (put f k o db) <= B)%N ->
    T_put f k o db + potential B (put f k o db) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      potential B db.
  (** Constructor allocation has the same amortized budget as insertion. *)
  Parameter T_make_amort : forall B f k db, wf db -> (ids (snd (make f k db)) <= B)%N ->
    T_make f k db + potential B (snd (make f k db)) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      potential B db.
  (** Union transfers the deferred work to potential. *)
  Parameter T_union_amort : forall B i j db, wf db ->
    T_union i j db + potential B (union i j db) <= c_db * unit db + potential B db.
  (** Rebuilding spends potential on pending union work. *)
  Parameter T_rebuild_amort : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    T_rebuild db + potential B (rebuild db) <=
      c_db * (pending db + 1) * unit db + potential B db.
  (** Slot lookup pays for the slot code. *)
  Parameter T_index_le : forall s new db,
    T_index s new db <= c_db * (Nat.log2 (S s) + 1).
  (** Advancing visits every slot. *)
  Parameter T_advance_le : forall db, T_advance db <= c_db * (num_slots db + 1).
End DATABASE_TIME.

Module Type DATABASE_T (V : VALUE_T) (I : INDEX_T V) := DATABASE V I <+ DATABASE_TIME V I.

Module Type DATABASE_PLAN (V : VALUE_T) (I : INDEX_T V) (Import X : DATABASE_T V I).
End DATABASE_PLAN.

Module Type DATABASE_ALL (V : VALUE_T) (I : INDEX_T V) :=
  DATABASE_T V I <+ DATABASE_PLAN V I.
