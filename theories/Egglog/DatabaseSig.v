(** * Databases with congruence rebuilding

    Databases store rows, identifier equalities and indexes of canonical tuples.
    For example, rebuilding merges two constructor outputs whose keys become equal.
    Builds on: ValueSig, IndexSig, Syntax and Model. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Std Loop.
From Galois.Base Require Import Loop UnionFind.
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
  Parameter index : N -> bool -> t -> I.t.
  Parameter advance : t -> t.
  Parameter changed : t -> bool.
  Parameter ids : t -> N.
End DATABASE_OPS.

Module Type DATABASE_SPEC (V : VALUE_OPS) (I : INDEX_OPS V)
    (Import X : DATABASE_OPS V I).
End DATABASE_SPEC.

Module Type DATABASE_LAWS (V : VALUE) (I : INDEX V) (Import X : DATABASE_OPS V I).
  (* spec: wf view repr pending old slots *)
  Parameter wf : t -> Prop.
  Parameter view : t -> Model.view (V := V.t).
  Parameter repr : t -> positive -> positive.
  Parameter pending : t -> nat.
  Parameter old : t -> positive -> list (cell V.t) -> option (option (cell V.t)).
  Parameter slots : t -> list (positive * list nat).
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
  Definition allocated (db : t) (i : positive) : Prop := (Npos i <= ids db)%N.
  (** Slot permutations contain distinct positions within the supplied tuple. *)
  Definition slots_fit (db : t) (f : positive) (n : nat) : Prop :=
    forall perm, In (f, perm) (slots db) -> NoDup perm /\ Forall (fun i => i < n) perm.
  Definition kind_ok (db : t) (f : positive) (k : list (cell V.t))
      (o : option (cell V.t)) : Prop :=
    (forall i, In (Id i) (k ++ option_list o) -> allocated db i) /\
    slots_fit db f (length (k ++ option_list o)) /\
    match kind (view db) f, o with
    | Some ORel, None => True
    | Some OId, Some (Id _) => True
    | Some (OLat _), Some (Val _) => True
    | _, _ => False
    end.
  Definition conflict (db : t) (f : positive) (k : list (cell V.t))
      (o : option (cell V.t)) (a b : positive) : Prop :=
    old db f (map (canon db) k) = Some (Some (Id a)) /\
    option_map (canon db) o = Some (Id b).
  Definition fresh_id (db : t) (i : positive) : Prop := i = N.succ_pos (ids db).
  Definition extends_by (db db' : t) (f : positive) (k : list (cell V.t))
      (i : positive) : Prop :=
    ids db' = Npos i /\ kind (view db') = kind (view db) /\
    (forall a b, same (view db') a b <-> same (view db) a b \/ (a = i /\ b = i)) /\
    (forall f' k' o', row (view db') f' k' o' <->
      row (view db) f' k' o' \/ (f' = f /\ k' = map (canon db) k /\ o' = Some (Id i))).
  Definition slot_of (db : t) (s : N) : option (positive * list nat) :=
    nth_error (slots db) (N.to_nat s).
  Definition permute (perm : list nat) (u : list (cell V.t)) : list (cell V.t) :=
    flat_map (fun i => option_list (nth_error u i)) perm.
  Definition merged (db : t) (f : positive) (os : list (option (cell V.t)))
      : option (cell V.t) :=
    match map (option_map (canon db)) os with
    | [] => None
    | o :: rest => fold_left (fun acc o' => combine db f (Some acc) o') rest o
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
  (** Every representative represents itself. *)
  Parameter repr_idem : forall db i, wf db -> repr db (repr db i) = repr db i.
  (** Initialization creates a well-formed database. *)
  Parameter wf_init : forall ds sl, wf (init ds sl).
  (** Kind-correct insertion keeps the database well formed. *)
  Parameter wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  (** Constructor allocation keeps the database well formed. *)
  Parameter wf_make : forall f k db, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    wf (snd (make f k db)).
  (** Equality insertion keeps the database well formed. *)
  Parameter wf_union : forall i j db, wf db -> allocated db i -> allocated db j ->
    wf (union i j db).
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
  (** Stored lookup agrees with the public row observation. *)
  Parameter old_row : forall db f k o, wf db ->
    (old db f k = Some o <-> row (view db) f k o).
  (** Lookup canonicalizes its query and keeps the view and invariant. *)
  Parameter lookup_spec : forall f k db, wf db ->
    fst (lookup f k db) = old db f (map (canon db) k) /\
    view (snd (lookup f k db)) = view db /\ wf (snd (lookup f k db)).
  (** Initialization records declarations and slots and starts empty. *)
  Parameter init_view : forall ds sl f k o i j,
    (row (view (init ds sl)) f k o <-> False) /\
    (same (view (init ds sl)) i j <-> i = j) /\
    kind (view (init ds sl)) f = lookup_kind ds f /\
    slots (init ds sl) = sl /\ ids (init ds sl) = 0%N /\ pending (init ds sl) = 0.
  (** Insertion keeps layout and allocation and queues at most one loser. *)
  Parameter layout_put : forall f k o db, wf db ->
    kind (view (put f k o db)) = kind (view db) /\ slots (put f k o db) = slots db /\
    ids (put f k o db) = ids db /\ pending (put f k o db) <= pending db + 1.
  (** Make keeps layout and returns an allocated identifier. *)
  Parameter layout_make : forall f k db, wf db ->
    kind (view (snd (make f k db))) = kind (view db) /\
    slots (snd (make f k db)) = slots db /\
    (ids (snd (make f k db)) <= N.succ (ids db))%N /\
    allocated (snd (make f k db)) (fst (make f k db)) /\
    pending (snd (make f k db)) = pending db.
  (** Union keeps layout and allocation and queues at most one loser. *)
  Parameter layout_union : forall i j db, wf db ->
    kind (view (union i j db)) = kind (view db) /\ slots (union i j db) = slots db /\
    ids (union i j db) = ids db /\ pending (union i j db) <= pending db + 1.
  (** Rebuilding keeps layout and allocation. *)
  Parameter layout_rebuild : forall db, wf db ->
    kind (view (rebuild db)) = kind (view db) /\ slots (rebuild db) = slots db /\
    ids (rebuild db) = ids db.
  (** Advancing keeps the slot layout. *)
  Parameter layout_advance : forall db, slots (advance db) = slots db.
  (** Advancing keeps allocation, pending work and representatives. *)
  Parameter advance_keeps : forall db, wf db ->
    ids (advance db) = ids db /\ pending (advance db) = pending db /\
    repr (advance db) = repr db.
  (** A quiet union already holds in the old view. *)
  Parameter union_quiet : forall i j db, wf db -> changed db = false ->
    changed (union i j db) = false -> same (view db) i j.
  (** A quiet make reuses a constructor row. *)
  Parameter make_quiet : forall f k db, wf db -> changed db = false ->
    changed (snd (make f k db)) = false ->
    exists j, row (view db) f (map (canon db) k) (Some (Id j)).
  (** Every row identifier is allocated. *)
  Parameter row_allocated : forall db f k o i, wf db -> row (view db) f k o ->
    In (Id i) (k ++ option_list o) -> allocated db i.

  (** Rebuilding keeps every satisfying model and identifier interpretation. *)
  Parameter rebuild_sat : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> sat V.merge M nu (view (rebuild db)).
  (** Inserting a true, kind-correct row keeps the model. *)
  Parameter put_sat : forall (M : model (V := V.t)) nu db f k o, wf db -> kind_ok db f k o ->
    sat V.merge M nu (view db) -> holds M nu (view db) f k o ->
    sat V.merge M nu (view (put f k o db)).
  (** A justified identifier union keeps the model. *)
  Parameter union_sat : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> nu i = nu j ->
    sat V.merge M nu (view (union i j db)).
  (** Make updates its output meaning and keeps every other identifier meaning. *)
  Parameter make_sat : forall (M : model (V := V.t)) nu db f k, wf db ->
    kind (view db) f = Some OId ->
    (forall j, In (Id j) k -> allocated db j) ->
    sat V.merge M nu (view db) ->
    let '(i, db') := make f k db in
    exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con M f (map (den nu) k) /\ sat V.merge M nu' (view db').

End DATABASE_LAWS.

Module Type DATABASE (V : VALUE) (I : INDEX V) :=
  DATABASE_OPS V I <+ DATABASE_SPEC V I <+ DATABASE_LAWS V I.

Module Type DATABASE_TIME (V : VALUE_T) (I : INDEX_T V) (Import X : DATABASE V I).
  (* spec: wmark potential *)
  Parameter wmark : t -> N.
  Definition unit (db : t) : nat :=
    (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Definition slots_of (db : t) (f : positive) : nat :=
    length (filter (fun s => Pos.eqb (fst s) f) (slots db)).
  Parameter potential : N -> t -> N.
  Definition num_slots (db : t) : nat := length (slots db).
  Parameter T_init : list decl -> list (positive * list nat) -> N.
  Parameter T_find : positive -> t -> N.
  Parameter T_lookup : positive -> list (cell V.t) -> t -> N.
  Parameter T_make : positive -> list (cell V.t) -> t -> N.
  Parameter T_put : positive -> list (cell V.t) -> option (cell V.t) -> t -> N.
  Parameter T_union : positive -> positive -> t -> N.
  Parameter T_rebuild : t -> N.
  Parameter T_index : N -> bool -> t -> N.
  Parameter T_advance T_changed T_ids : t -> N.
  Parameter c_db : N.
  (** Initialization starts without amortized debt. *)
  Parameter potential_init : forall B ds sl, (potential B (init ds sl) = 0)%N.
  (** Insertion pays for all slots and the logarithmic identifier budget. *)
  Parameter T_put_amort : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * potential B (put f k o db) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  (** Constructor allocation has the same amortized budget as insertion. *)
  Parameter T_make_amort : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * potential B (snd (make f k db)) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  (** Union transfers the deferred work to potential. *)
  Parameter T_union_amort : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * potential B (union i j db) <=
      N.of_nat (unit (union i j db)) * (c_db + potential B db))%N.
  (** Rebuilding spends potential on pending union work. *)
  Parameter T_rebuild_amort : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild db + N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  (** Slot lookup pays for the slot code. *)
  Parameter T_index_le : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  (** Advancing visits every slot. *)
  Parameter T_advance_le : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  (** The high-water mark covers every stored cell encoding. *)
  Parameter wmark_cells : forall db f k o c, wf db -> row (view db) f k o ->
    In c (k ++ option_list o) -> cell_bits V.encode c <= N.size_nat (wmark db).
  (** The high-water mark covers every declared function name. *)
  Parameter wmark_names : forall db f, wf db -> kind (view db) f <> None ->
    Pos.size_nat f <= N.size_nat (wmark db).
  (** Insertion never reduces the spending unit. *)
  Parameter unit_mono_put : forall f k o db, wf db -> unit db <= unit (put f k o db).
  (** Make never reduces the spending unit. *)
  Parameter unit_mono_make : forall f k db, wf db -> unit db <= unit (snd (make f k db)).
  (** Union never reduces the spending unit. *)
  Parameter unit_mono_union : forall i j db, wf db -> unit db <= unit (union i j db).
  (** Rebuilding never reduces the spending unit. *)
  Parameter unit_mono_rebuild : forall db, wf db -> unit db <= unit (rebuild db).
  (** Advancing keeps the watermark and the amortized credit. *)
  Parameter advance_credit : forall B db, wf db ->
    wmark (advance db) = wmark db /\ (potential B (advance db) = potential B db)%N.
  (** Initialization pays for declarations and slot permutations. *)
  Parameter T_init_le : forall ds sl,
    (T_init ds sl <= c_db * N.of_nat (length ds + length sl + 1) *
      N.of_nat ((fold_right (fun s n => length (snd s) + n) 0 sl + 1)%nat) +
      c_db * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl)%nat))%N.
  (** Find traverses allocated identifiers at the database unit. *)
  Parameter T_find_le : forall i db, wf db -> allocated db i ->
    (T_find i db <= c_db * N.of_nat (unit db))%N.
  (** Lookup charges the stored unit and query cell encodings. *)
  Parameter T_lookup_le : forall f k db, wf db ->
    (T_lookup f k db <= c_db * N.of_nat (length k + 1) * N.of_nat (unit db) +
      c_db * N.of_nat ((fold_right (fun c n => cell_bits V.encode c + n) 0 k)%nat))%N.
  (** The change flag is stored. *)
  Parameter T_changed_le : forall db, (T_changed db <= c_db)%N.
  (** The allocation counter is stored. *)
  Parameter T_ids_le : forall db, (T_ids db <= c_db)%N.

End DATABASE_TIME.

Module Type DATABASE_T (V : VALUE_T) (I : INDEX_T V) := DATABASE V I <+ DATABASE_TIME V I.

Module Type DATABASE_PLAN (V : VALUE_T) (I : INDEX_T V) (Import X : DATABASE_T V I).
  Definition use_entry := (positive * list (cell V.t))%type.
  Definition stored_row := (use_entry * option (cell V.t))%type.
  Definition repair_state := (t * list use_entry)%type.

  (* spec: rows uses_entries queue next_id forest_ok class_size uf_state
     index_counters written_cells located decl_names *)
  Parameter rows : t -> list stored_row.
  Parameter uses_entries : t -> list (positive * use_entry).
  Parameter queue : t -> list positive.
  Parameter next_id : t -> positive.
  Parameter forest_ok : t -> Prop.
  Parameter class_size : t -> positive -> N.
  (** A historical row key resolves to its current stored key. *)
  Parameter located : t -> positive -> list (cell V.t) -> option (list (cell V.t)).
  Parameter k_credit k_loop k_active k_queue k_stop k_driver : N.

  Definition uses (db : t) (x : positive) (e : use_entry) : Prop :=
    In (x, e) (uses_entries db).
  Definition scheduled (db : t) (work : list use_entry) (e : use_entry) : Prop :=
    In e work \/ exists x, In x (queue db) /\ uses db x e.
  Definition row_ids (k : list (cell V.t)) (o : option (cell V.t)) (i : positive) : Prop :=
    In (Id i) (k ++ option_list o).

  (** Located historical keys resolve to stored rows of declared functions. *)
  Parameter F_forest_located : forall db f k0 k, forest_ok db -> located db f k0 = Some k ->
    exists o, In ((f, k), o) (rows db) /\ kind (view db) f <> None.

  (** Active entries retain coverage after their loser has left the queue. *)
  Definition inv_on (db : t) (work : list use_entry) : Prop :=
    (forall f k o, In ((f, k), o) (rows db) <-> row (view db) f k o) /\
    NoDup (map fst (rows db)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i ->
      exists x k0, repr db x = repr db i /\ uses db x (f, k0) /\
        located db f k0 = Some k /\ (x = repr db i \/ In x (queue db))) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i -> repr db i <> i ->
      exists k0, scheduled db work (f, k0) /\ located db f k0 = Some k) /\
    (forall s f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s false db) /\
      I.wf (length perm) (index s true db) /\
      (forall u, I.mem (index s false db) u <->
        exists k o, row (view db) f k o /\ u = permute perm (k ++ option_list o)) /\
      (forall u, I.mem (index s true db) u -> I.mem (index s false db) u)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i ->
      (i < next_id db)%positive) /\
    (forall e, In e work -> exists x, uses db x e) /\
    forest_ok db /\
    (forall f k o, row (view db) f k o -> kind_ok db f k o) /\
    NoDup (queue db) /\ pending db = length (queue db) /\
    (forall x, In x (queue db) -> allocated db x).
  Definition output_equiv (db : t) (a b : option (cell V.t)) : Prop :=
    match a, b with
    | None, None => True
    | Some c, Some d => cell_rel (same (view db)) c d
    | _, _ => False
    end.
  Definition inv (db : t) : Prop := inv_on db [].
  Definition state_inv (s : repair_state) : Prop := inv_on (fst s) (snd s).

  Definition entry_weight (db : t) (e : use_entry) : nat :=
    (length (snd e) + 1) * (slots_of db (fst e) + 1).
  Definition bucket (db : t) (x : positive) : list use_entry :=
    map snd (filter (fun xe => Pos.eqb (fst xe) x) (uses_entries db)).
  Definition use_credit (B : N) (db : t) (xe : positive * use_entry) : nat :=
    N.to_nat (N.log2 B - N.log2 (class_size db (repr db (fst xe)))) *
        entry_weight db (snd xe).
  Definition work_weight (db : t) (work : list use_entry) : nat :=
    fold_right (fun e n => entry_weight db e + n) 0 work.
  Definition queue_weight (db : t) : nat :=
    fold_right (fun x n => work_weight db (bucket db x) + 1 + n) 0 (queue db).
  Definition rebuild_potential (B : N) (db : t) : N :=
    (k_credit * N.of_nat (fold_right (fun xe n => (use_credit B db xe + n)%nat) 0%nat
      (uses_entries db)) + k_queue * N.of_nat (queue_weight db))%N.
  Definition state_potential (B : N) (s : repair_state) : N :=
    (rebuild_potential B (fst s) +
      k_active * N.of_nat (work_weight (fst s) (snd s)))%N.
  Parameter nuses npending : t -> N.
  Parameter uf_state : t -> UnionFind.t.
  Parameter index_counters : t -> list positive.
  Parameter written_cells : t -> list (cell V.t).
  Parameter decl_names : t -> list positive.
  Parameter get_uses : positive -> t -> list use_entry.
  Parameter T_get_uses : positive -> t -> N.
  Parameter pop_loser : t -> option (positive * t).
  Parameter repair_entry : use_entry -> t -> t.
  Parameter rstep : repair_state -> repair_state + t.
  Parameter rebuild_fuel : t -> N.
  Parameter rebuild_measure : repair_state -> nat.
  Parameter T_pop_loser : t -> N.
  Parameter T_repair_entry : use_entry -> t -> N.
  Parameter T_rstep : repair_state -> N.
  Parameter T_rebuild_fuel : t -> N.

  Parameter k_locate k_repair k_pop k_rstep k_slots k_layout : N.

  (* spec: row_id row_parent row_size row_current next_row *)
  Parameter row_id : t -> positive -> list (cell V.t) -> option positive.
  Parameter row_parent : t -> positive -> positive.
  Parameter row_size : t -> positive -> N.
  Parameter row_current : t -> positive -> option (list (cell V.t)).
  Parameter next_row : t -> positive.
  Parameter locate : positive -> list (cell V.t) -> t -> option (list (cell V.t)).
  Parameter T_locate : positive -> list (cell V.t) -> t -> N.
  (** Following the merge parent of a row identifier [n] times. *)
  Definition row_up (db : t) (n : nat) (r : positive) : positive :=
    Nat.iter n (row_parent db) r.
  (** A historical key resolves through a merge chain of logarithmic depth. *)
  Parameter F_row_locate : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    exists d, d <= length k * (N.to_nat (N.log2 (ids db)) + 1) /\
      row_parent db (row_up db d r) = row_up db d r /\
      located db f k = row_current db (row_up db d r).
  (** A key without a row identifier has no current row. *)
  Parameter F_row_absent : forall db work f k, inv_on db work -> row_id db f k = None ->
    located db f k = None.
  (** The executable resolution agrees with the observation. *)
  Parameter F_locate : forall db work f k, inv_on db work -> locate f k db = located db f k.
  (** Merged row groups at least double the losing group. *)
  Parameter F_row_by_size : forall db work r, inv_on db work -> row_parent db r <> r ->
    (1 <= row_size db r)%N /\ (2 * row_size db r <= row_size db (row_parent db r))%N.
  (** A row group holds at most one row per assignment of its identifier positions. *)
  Parameter F_row_group : forall db work f k r d, inv_on db work -> row_id db f k = Some r ->
    row_parent db (row_up db d r) = row_up db d r ->
    (row_size db (row_up db d r) <= (ids db + 1) ^ N.of_nat (length k))%N.
  (** Row identifiers stay below a counter that the watermark covers. *)
  Parameter F_row_counter : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    (r < next_row db)%positive /\ (row_parent db r < next_row db)%positive /\
    In (next_row db) (index_counters db).
  (** The keys of use entries are written cells. *)
  Parameter F_entry_cells : forall db work x f k c, inv_on db work -> uses db x (f, k) ->
    In c k -> In c (written_cells db).
  (** Resolution reads the key once and follows the chain at the stored width. *)
  Parameter T_locate_le : forall db work x f k, inv_on db work -> uses db x (f, k) ->
    (T_locate f k db <= k_locate * N.of_nat (length k + 1) * N.of_nat (unit db))%N.
  (** A repair, with its resolution, rekeying, slot updates and collision, pays its entry weight. *)
  Parameter T_repair_entry_le : forall db e rest, inv_on db (e :: rest) ->
    (T_repair_entry e db <= k_repair * N.of_nat (entry_weight db e) *
      N.of_nat (unit (repair_entry e db)))%N.

  (* spec: slot_place group_of group_slots proj_count slots_ok *)
  Parameter slots_ok : t -> Prop.
  Parameter slot_place : t -> N -> option (bool * N * N).
  Parameter group_of : t -> positive -> option N.
  Parameter group_slots : t -> bool -> N -> list N.
  Parameter rank_slots : list decl -> list (positive * list nat) -> list (bool * N * N).
  Parameter T_rank_slots : list decl -> list (positive * list nat) -> N.
  Parameter slots_update : bool -> positive -> list (cell V.t) -> t -> t.
  Parameter T_slots_update : bool -> positive -> list (cell V.t) -> t -> N.
  (** Every slot has a place whose group rank and offset do not exceed the slot number. *)
  Parameter F_slot_place : forall db work s f perm, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists d g j, slot_place db s = Some (d, g, j) /\ (g <= s)%N /\ (j <= s)%N /\
      nth_error (group_slots db d g) (N.to_nat j) = Some s /\
      (d = true <-> kind (view db) f <> None) /\
      (d = true -> group_of db f = Some g /\ (g < wmark db)%N).
  (** A declared group lists precisely the slots of its function, once each. *)
  Parameter F_group_slots : forall db work f g, inv_on db work -> group_of db f = Some g ->
    NoDup (group_slots db true g) /\
    forall s, In s (group_slots db true g) <-> exists perm, slot_of db s = Some (f, perm).
  (** Initialization stores the ranking of its slot list. *)
  Parameter F_init_place : forall ds sl s,
    slot_place (init ds sl) s = nth_error (rank_slots ds sl) (N.to_nat s).
  (** Ranking by first appearance is linear in the slots and the bits of the names. *)
  Parameter T_rank_slots_le : forall ds sl,
    (T_rank_slots ds sl <= k_layout * N.of_nat (length ds + length sl + 1) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0%nat sl)%nat))%N.
  (** Initialization adds the ranking to one pass over declarations and permutations. *)
  Parameter T_init_split : forall ds sl,
    (T_init ds sl <= T_rank_slots ds sl +
      k_layout * N.of_nat (length ds + length sl + 1) *
        N.of_nat ((fold_right (fun s n => length (snd s) + n) 0%nat sl + 1)%nat) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds)%nat))%N.
  (** One update of every slot of a declared function walks its group once. *)
  Parameter T_slots_update_le : forall db b f u, slots_ok db ->
    kind (view db) f <> None -> slots_fit db f (length u) ->
    (forall c, In c u -> cell_bits V.encode c <= N.size_nat (wmark (slots_update b f u db))) ->
    (T_slots_update b f u db <= k_slots * N.of_nat (slots_of db f + 1) *
      N.of_nat (length u + 1) *
      N.of_nat (unit (slots_update b f u db)))%N.

  (** A union finds both roots and links only distinct ones. *)
  Parameter F_union_roots : forall i j db, inv db -> allocated db i -> allocated db j ->
    let '(ri, u1) := UnionFind.find i (uf_state db) in
    let '(rj, u2) := UnionFind.find j u1 in
    uf_state (union i j db) =
      if Pos.eqb ri rj then u2 else snd (UnionFind.union ri rj u2).
  (** Membership and key width stay within allocation. *)
  Parameter F_uf_card : forall db work, inv_on db work ->
    UnionFind.card (uf_state db) <= 3 * N.to_nat (ids db) /\
    UnionFind.width (uf_state db) <= N.size_nat (ids db).

  Parameter proj_count : t -> N -> list (cell V.t) -> N.
  (** The count of a projected tuple is the number of rows that project onto it. *)
  Parameter F_proj_count : forall db work s f perm u, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists rs, NoDup rs /\
      (forall r, In r rs <-> In r (rows db) /\ fst (fst r) = f /\
        permute perm (snd (fst r) ++ option_list (snd r)) = u) /\
      N.to_nat (proj_count db s u) = length rs.

  (** The counter of the empty index is recorded. *)
  Parameter F_counter_one : forall db, inv db -> In 1%positive (index_counters db).

  (** The maintained invariant gives the slot facts that an update reads. *)
  Parameter F_slots_ok : forall db work, inv_on db work -> slots_ok db.
  (** A slot update keeps those facts. *)
  Parameter F_slots_ok_update : forall db b f u, slots_ok db ->
    slots_fit db f (length u) -> slots_ok (slots_update b f u db).

  (** A driver step costs its repair, or its pop and bucket read, plus a constant. *)
  Parameter T_rstep_split : forall db work,
    (T_rstep (db, work) <= k_rstep +
      match work with
      | e :: _ => T_repair_entry e db
      | [] => T_pop_loser db +
          match pop_loser db with
          | Some (x, _) => T_get_uses x db
          | None => 0
          end
      end)%N.
  (** A pop moves the selected bucket at one step per entry. *)
  Parameter T_pop_loser_le : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    (T_pop_loser db <= k_pop * N.of_nat (work_weight db (bucket db x) + 1) *
      N.of_nat (unit db))%N.
  (** An empty pop reads the stored queue. *)
  Parameter T_pop_none_le : forall db, inv db -> pop_loser db = None ->
    (T_pop_loser db <= k_pop * N.of_nat (unit db))%N.
  (** A bucket is read by one keyed lookup. *)
  Parameter T_get_uses_le : forall db work x, inv_on db work -> allocated db x ->
    (T_get_uses x db <= k_pop * N.of_nat (unit db))%N.


  (** Public well-formedness is the maintained invariant at an empty active batch. *)
  Parameter F1_inv_wf : forall db, wf db <-> inv db.
  (** The public potential is the weighted occurrence credit. *)
  Parameter F2_potential : forall B db, (potential B db = k_loop * rebuild_potential B db)%N.
  (** The unit charges identifier traversal and cell encoding widths. *)
  Parameter F3_unit : forall db,
    unit db = (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  (** Direct bucket lookup agrees with the occurrence inventory. *)
  Parameter F4_bucket : forall db work x, inv_on db work -> get_uses x db = bucket db x.
  (** An empty pop detects an empty pending queue. *)
  Parameter F4_pop_none : forall db, inv db -> (pop_loser db = None <-> queue db = []).
  (** A pop transfers its selected bucket into the active work list. *)
  Parameter F4_pop : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    queue db = x :: queue db' /\ view db' = view db /\
    (forall y e, uses db' y e <->
      (uses db y e /\ y <> x) \/ (y = repr db x /\ uses db x e)) /\
    N.to_nat (nuses db') = length (uses_entries db') /\
    inv_on db' (bucket db x).
  (** The driver consumes one active entry or dequeues one loser. *)
  Parameter F5_rstep : forall db work,
    rstep (db, work) =
      match work with
      | e :: rest => inl (repair_entry e db, rest)
      | [] =>
        match pop_loser db with
        | None => inr db
        | Some (x, db') => inl (db', get_uses x db)
        end
      end.
  (** Entries without a current row are discarded without changing the database. *)
  Parameter F6_absent : forall db f k,
    located db f k = None -> repair_entry (f, k) db = db.
  (** Repair discharges one active occurrence and retains coverage of affected rows. *)
  Parameter F7_repair_inv : forall db e rest, inv_on db (e :: rest) ->
    inv_on (repair_entry e db) rest.
  (** Continuing steps retain the queue and active-batch invariant. *)
  Parameter F8_rstep_inv : forall s s', state_inv s -> rstep s = inl s' -> state_inv s'.
  (** Repair retains kinds and identifier allocation. *)
  Parameter F9_rstep_layout : forall s s', state_inv s -> rstep s = inl s' ->
    kind (view (fst s')) = kind (view (fst s)) /\ ids (fst s') = ids (fst s).
  (** Collision unions keep the same functional-dependency closure. *)
  Parameter F10_rstep_cong : forall s s' i j, state_inv s -> rstep s = inl s' ->
    (cong (fst s') i j <-> cong (fst s) i j).
  (** Every old row survives one step at an equivalent, possibly unfinished key. *)
  Parameter F11_rstep_keeps : forall s s' f k o, state_inv s -> rstep s = inl s' ->
    row (view (fst s)) f k o ->
    exists k' o', row (view (fst s')) f k' o' /\
      Forall2 (cell_rel (same (view (fst s')))) k k' /\
      out_le (fst s') f (option_map (canon (fst s')) o) o'.
  (** Every repaired row groups a nonempty list of rows from before the step. *)
  Parameter F12_rstep_from : forall s s' f k' o', state_inv s -> rstep s = inl s' ->
    row (view (fst s')) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view (fst s)) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view (fst s')))) (fst ko) k') srcs /\
      output_equiv (fst s') o' (merged (fst s') f (map snd srcs)).
  (** A stopped driver exposes canonical rows and constructor closure. *)
  Parameter F13_rstep_done : forall s r, state_inv s -> rstep s = inr r ->
    r = fst s /\ snd s = [] /\ inv r /\ canonical r /\ pending r = 0 /\
    (forall f k1 k2 i j, row (view r) f k1 (Some (Id i)) ->
      row (view r) f k2 (Some (Id j)) ->
      Forall2 (cell_rel (same (view r))) k1 k2 -> same (view r) i j).
  (** Continuing steps strictly decrease a measure that includes active work. *)
  Parameter F14_rstep_measure : forall s s', state_inv s -> rstep s = inl s' ->
    rebuild_measure s' < rebuild_measure s.
  (** Fuel budgets logarithmic relabelings of all stored use occurrences. *)
  Parameter F15_fuel_formula : forall db, rebuild_fuel db =
    ((N.size (ids db) + 2) * (nuses db + 1) + npending db + 1)%N.
  (** Computed fuel includes the final stop call. *)
  Parameter F15_fuel_enough : forall db, inv db ->
    (N.of_nat (rebuild_measure (db, [])) < rebuild_fuel db)%N.
  (** The rebuild operation runs the same step and fuel as the plan. *)
  Parameter F16_rebuild_run : forall db, wf db ->
    loopN rstep (rebuild_fuel db) (db, []) = inr (rebuild db).

  (** Congruent cells have equal denotations in every satisfying model. *)
  Parameter F17_cong_den : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> cong db i j -> nu i = nu j.
  (** Nonempty output groups keep their model meaning through the actual merge fold. *)
  Parameter F18_merged_holds : forall (M : model (V := V.t)) nu db f k os,
    wf db -> lat_closed V.merge M (view db) -> os <> [] -> (forall i, nu (repr db i) = nu i) ->
    Forall (holds M nu (view db) f k) os ->
    holds M nu (view db) f k (merged db f os).
  (** Repair preserves satisfaction through its collision, lattice and index branches. *)
  Parameter F19_rstep_sat : forall (M : model (V := V.t)) nu s s',
    state_inv s -> rstep s = inl s' -> sat V.merge M nu (view (fst s)) ->
    sat V.merge M nu (view (fst s')).
  (** Lineage retains original row groups throughout repeated deletion and reinsertion. *)
  Definition lineage (initial current : t) : Prop :=
    forall f k o, row (view current) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view current))) (fst ko) k) srcs /\
      output_equiv current o (merged current f (map snd srcs)).
  (** Singleton source groups establish lineage before the first repair. *)
  Parameter F20_lineage_initial : forall db, inv db -> lineage db db.
  (** Actual repair flattens source groups through canonicalization and lattice merging. *)
  Parameter F21_lineage_step : forall initial s s', state_inv s ->
    rstep s = inl s' -> lineage initial (fst s) -> lineage initial (fst s').
  (** Stopped lineage gives the exact public output equation for each original group. *)
  Parameter F22_lineage_done : forall initial s r, inv initial -> state_inv s ->
    rstep s = inr r -> lineage initial r ->
    forall f k o, row (view r) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        map (canon r) (fst ko) = k) srcs /\ o = merged r f (map snd srcs).


  (** A losing root enters a class at least twice as large. *)
  Parameter T1_doubling : forall db i j x, inv db -> repr db x = x ->
    repr (union i j db) x <> x ->
    (2 * class_size db x <= class_size (union i j db) (repr (union i j db) x))%N.
  (** Initialization has no use-occurrence debt. *)
  Parameter T2_init_credit : forall B ds sl, (rebuild_potential B (init ds sl) = 0)%N.
  (** Insertion pays its executable work and new occurrence credit. *)
  Parameter T3_put_credit : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * (k_loop * rebuild_potential B (put f k o db)) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  (** Allocation pays new occurrences through the insertion budget. *)
  Parameter T4_make_credit : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * (k_loop * rebuild_potential B (snd (make f k db))) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  (** Union pays its root link and queued repair credit. *)
  Parameter T5_union_credit : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * (k_loop * rebuild_potential B (union i j db)) <=
      N.of_nat (unit (union i j db)) * (c_db + (k_loop * rebuild_potential B db)))%N.
  (** Continuing steps spend queued and active credit without a per-entry allowance. *)
  Parameter T6_rstep_go : forall B U s s', state_inv s -> (ids (fst s') <= B)%N ->
    unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + k_loop * N.of_nat U * state_potential B s' <
      k_loop * N.of_nat U * state_potential B s)%N.
  (** Stopping charges one unit of the final database. *)
  Parameter T7_rstep_stop : forall s r, state_inv s -> rstep s = inr r ->
    (T_rstep s <= k_stop * N.of_nat (unit (fst s)))%N.
  (** Continuing steps also pay the binary loop driver's per-step charge. *)
  Parameter T6a_rstep_credit : forall B U s s', state_inv s ->
    (ids (fst s') <= B)%N -> unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * state_potential B s' <=
      k_loop * N.of_nat U * state_potential B s)%N.
  (** Stopping retains result credit and spends the reserved stop allowance. *)
  Parameter T7a_stop_credit : forall B U s r, state_inv s -> unit (fst s) <= U ->
    rstep s = inr r ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * rebuild_potential B r <=
      k_loop * N.of_nat U * state_potential B s + k_stop * N.of_nat U)%N.

  (** The actual loop must fit the public budget after all use-entry charges are summed. *)
  Parameter T8_rebuild_loop : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild_fuel db + T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver +
      N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  (** The wrapper exposes fuel construction and driver overhead. *)
  Parameter T9_rebuild_driver : forall db,
    (T_rebuild db <= T_rebuild_fuel db +
      T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver)%N.
  (** Slot lookup charges its binary slot code. *)
  Parameter T10_index : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  (** Advancing clears each maintained slot once. *)
  Parameter T11_advance : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  (** Stored counters agree with the occurrence inventory and pending queue. *)
  Parameter F15_counts : forall db work, inv_on db work ->
    N.to_nat (nuses db) = length (uses_entries db) /\ N.of_nat (pending db) = npending db.
  (** The declaration inventory contains precisely the names with a kind. *)
  Parameter F_decl_names : forall db f, inv db ->
    (kind (view db) f <> None <-> In f (decl_names db)).
  (** The stored watermark is the exact historical maximum of written payloads and counters. *)
  Parameter F_wmark : forall db, inv db ->
    wmark db = fold_right N.max (N.max (nuses db) (ids db))
      (map Npos (index_counters db) ++ map Npos (decl_names db) ++
        map (fun c => match c with
          | Id i => Npos (xO i)
          | Val v => Npos (xI (V.encode v))
          end) (written_cells db)).
  (** Every slot index fits the stored counter and cell watermark. *)
  Parameter F_wmark_index : forall db s new, inv db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  (** Class sizes come from the size-based union-find. *)
  Parameter F_uf_bridge : forall db work x, inv_on db work ->
    repr db x = UnionFind.repr (uf_state db) x /\
    class_size db x = N.of_nat (UnionFind.size_of (uf_state db) x) /\
    UnionFind.wf (uf_state db).
  (** Root classes are nonempty and bounded by allocation. *)
  Parameter F_class_size : forall db work x, inv_on db work ->
    (1 <= class_size db (repr db x))%N /\
    (class_size db (repr db x) <= N.max 1 (ids db))%N.
  (** Collision unions also double the losing class. *)
  Parameter F_rstep_doubling : forall s s' x, state_inv s -> rstep s = inl s' ->
    repr (fst s) x = x -> repr (fst s') x <> x ->
    (2 * class_size (fst s) x <= class_size (fst s') (repr (fst s') x))%N.
  (** Repair never reduces the spending unit. *)
  Parameter F9b_rstep_unit : forall s s', state_inv s -> rstep s = inl s' ->
    unit (fst s) <= unit (fst s').
  (** Loop credit includes the binary driver charge. *)
  Parameter k_loop_le : (c_loopN <= k_loop)%N.
  (** Fuel construction uses stored binary counters. *)
  Parameter T7b_fuel : forall db, inv db ->
    (T_rebuild_fuel db <= k_driver * N.of_nat (unit db))%N.
  (** The [T_loopN_amort] driver retains the final database credit. *)
  Parameter T8a_loop_final : forall B U db, inv db -> (ids (rebuild db) <= B)%N ->
    unit (rebuild db) <= U ->
    (T_loopN rstep T_rstep (rebuild_fuel db) (db, []) +
      k_loop * N.of_nat U * rebuild_potential B (rebuild db) <=
      k_loop * N.of_nat U * rebuild_potential B db + k_stop * N.of_nat U +
      c_loopN * N.of_nat (N.size_nat (rebuild_fuel db) + 1))%N.

End DATABASE_PLAN.

Module Type DATABASE_ALL (V : VALUE_T) (I : INDEX_T V) :=
  DATABASE_T V I <+ DATABASE_PLAN V I.
