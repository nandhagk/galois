(** * Placeholder database operations

    Databases store rows and identifier equalities.
    For example, an initialized database supplies indexes on request.
    Builds on: DatabaseSig. *)

From Stdlib Require Import List PArith NArith Bool Relations.Relation_Operators.
From Argent Require Import Time Std Loop.
From Galois.Base Require Import Code Loop UnionFind.
From Galois.Egglog Require Import ValueSig IndexSig Syntax Model DatabaseSig.

Import List.ListNotations.

Record database_state (C : Type) := DatabaseState {
  db_forest : UnionFindCode.t;
  db_nuses : N;
  db_npending : N;
  db_wmark : N;
  db_written_cells : list C;
  db_index_counters : list positive
}.

Arguments DatabaseState {C}.
Arguments db_forest {C}.
Arguments db_nuses {C}.
Arguments db_npending {C}.
Arguments db_wmark {C}.
Arguments db_written_cells {C}.
Arguments db_index_counters {C}.

TimeFun db_forest.
TimeFun db_nuses.
TimeFun db_npending.
TimeFun db_wmark.
TimeFun db_written_cells.
TimeFun db_index_counters.

Module DatabaseCode (V : VALUE_OPS) (I : INDEX_OPS V) <: DATABASE_OPS V I.
  Definition t := database_state (cell V.t).
  (* STUB-CODE *)
  Definition init (_ : list decl) (_ : list (positive * list nat)) : t :=
    DatabaseState UnionFindCode.empty 0%N 0%N 0%N [] [].
  (* STUB-CODE *)
  Definition find (i : positive) (db : t) : positive * t :=
    let result := UnionFindCode.find i (db_forest db) in
    (fst result, DatabaseState (snd result) (db_nuses db) (db_npending db) (db_wmark db)
      (db_written_cells db) (db_index_counters db)).
  (* STUB-CODE *)
  Definition lookup (_ : positive) (_ : list (cell V.t)) (db : t)
      : option (option (cell V.t)) * t := (None, db).
  (* STUB-CODE *)
  Definition make (i : positive) (_ : list (cell V.t)) (db : t) : positive * t := (i, db).
  (* STUB-CODE *)
  Definition put (_ : positive) (_ : list (cell V.t)) (_ : option (cell V.t)) (db : t) := db.
  (* STUB-CODE *)
  Definition union (i j : positive) (db : t) :=
    if (N.leb (Npos i) (count (db_forest db)) &&
        N.leb (Npos j) (count (db_forest db)))%bool then
      let result := UnionFindCode.union i j (db_forest db) in
      let queued := match fst result with
        | None => db_npending db
        | Some _ => N.succ (db_npending db)
        end in
      DatabaseState (snd result) (db_nuses db) queued (db_wmark db)
        (db_written_cells db) (db_index_counters db)
    else db.
  (* STUB-CODE *)
  Definition db_rstep (s : t * list (positive * list (cell V.t)))
      : (t * list (positive * list (cell V.t))) + t := inr (fst s).
  Definition db_rebuild_fuel (db : t) : N :=
    ((N.size (count (db_forest db)) + 2) * (db_nuses db + 1) + db_npending db + 1)%N.
  Definition rebuild (db : t) :=
    match loopN db_rstep (db_rebuild_fuel db) (db, []) with
    | inl s => fst s
    | inr result => result
    end.
  (* STUB-CODE *)
  Definition index (_ : N) (_ : bool) (_ : t) : I.t := I.empty.
  (* STUB-CODE *)
  Definition advance (db : t) := db.
  (* STUB-CODE *)
  Definition changed (_ : t) := false.
  (* STUB-CODE *)
  Definition ids (db : t) : N := count (db_forest db).
  (* STUB-CODE *)
  Definition locate (_ : positive) (_ : list (cell V.t)) (_ : t)
      : option (list (cell V.t)) := None.
  (* STUB-CODE *)
  Definition rank_slots (_ : list decl) (_ : list (positive * list nat))
      : list (bool * N * N) := [].
  (* STUB-CODE *)
  Definition slots_update (_ : bool) (_ : positive) (_ : list (cell V.t)) (db : t) : t := db.

End DatabaseCode.

Module Database (V : VALUE) (I : INDEX V) <: DATABASE V I.
  Include DatabaseCode V I.
  Include DATABASE_SPEC V I.
  (* spec: wf view repr pending old slots *)
  Definition wf : t -> Prop := fun _ => True.
  Definition view (_ : t) : Model.view (V := V.t) :=
    {| row := fun _ _ _ => False;
       same := fun _ _ => False;
       kind := fun _ => None |}.
  Definition repr : t -> positive -> positive := fun _ i => i.
  Definition pending : t -> nat := fun _ => 0.
  Definition old (_ : t) (_ : positive) (_ : list (cell V.t))
      : option (option (cell V.t)) := None.
  Definition slots (_ : t) : list (positive * list nat) := [].
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
  Lemma same_repr : forall db i j, wf db ->
    (same (view db) i j <-> repr db i = repr db j).
  Proof. Admitted.
  (** Every representative represents itself. *)
  Lemma repr_idem : forall db i, wf db -> repr db (repr db i) = repr db i.
  Proof. Admitted.

  (** Initialization creates a well-formed database. *)
  Lemma wf_init : forall ds sl, wf (init ds sl).
  Proof. Admitted.

  (** Kind-correct insertion keeps the database well formed. *)
  Lemma wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Proof. Admitted.

  (** Constructor allocation keeps the database well formed. *)
  Lemma wf_make : forall f k db, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    wf (snd (make f k db)).
  Proof. Admitted.

  (** Equality insertion keeps the database well formed. *)
  Lemma wf_union : forall i j db, wf db -> allocated db i -> allocated db j ->
    wf (union i j db).
  Proof. Admitted.

  (** Rebuilding keeps the database well formed. *)
  Lemma wf_rebuild : forall db, wf db -> wf (rebuild db).
  Proof. Admitted.

  (** Advancing clears the change flag without changing the view. *)
  Lemma wf_advance : forall db, wf db ->
    wf (advance db) /\ view (advance db) = view db /\ changed (advance db) = false.
  Proof. Admitted.

  (** Find returns the representative without changing the view. *)
  Lemma find_spec : forall i db, wf db ->
    fst (find i db) = repr db i /\ view (snd (find i db)) = view db.
  Proof. Admitted.

  (** Each function key has one output. *)
  Lemma row_functional : forall db f k o1 o2, wf db ->
    row (view db) f k o1 -> row (view db) f k o2 -> o1 = o2.
  Proof. Admitted.

  (** Insertion changes precisely the canonical key and combines its output. *)
  Lemma put_rows : forall f k o db, wf db -> kind_ok db f k o ->
    let ck := map (canon db) k in let co := option_map (canon db) o in
    forall f' k' o', row (view (put f k o db)) f' k' o' <->
      (row (view db) f' k' o' /\ (f', k') <> (f, ck)) \/
      (f' = f /\ k' = ck /\ combine db f (old db f ck) co = o').
  Proof. Admitted.

  (** Identifier output conflicts add precisely their equality closure. *)
  Lemma put_same : forall f k o db i j, wf db -> kind_ok db f k o ->
    (same (view (put f k o db)) i j <->
      clos_refl_sym_trans positive
        (fun a b => same (view db) a b \/ conflict db f k o a b) i j).
  Proof. Admitted.

  (** A quiet insertion already has its requested row represented. *)
  Lemma put_quiet : forall f k o db, wf db -> kind_ok db f k o ->
    changed db = false -> changed (put f k o db) = false ->
    view (put f k o db) = view db /\ present_put (view db) f (map (canon db) k) o.
  Proof. Admitted.

  (** Make reuses a canonical constructor output or allocates a fresh identifier. *)
  Lemma make_spec : forall f k db, wf db -> kind (view db) f = Some OId ->
    let '(i, db') := make f k db in
    (exists j, row (view db) f (map (canon db) k) (Some (Id j)) /\
      i = repr db j /\ db' = db) \/
    (fresh_id db i /\ row (view db') f (map (canon db) k) (Some (Id i)) /\
      extends_by db db' f k i).
  Proof. Admitted.

  (** Union adds precisely the requested equality closure. *)
  Lemma union_same : forall i j db k l, wf db ->
    (same (view (union i j db)) k l <->
      clos_refl_sym_trans positive (fun a b => same (view db) a b \/ (a, b) = (i, j)) k l).
  Proof. Admitted.

  (** Union queues equality work without changing rows. *)
  Lemma union_rows : forall i j db, wf db ->
    row (view (union i j db)) = row (view db).
  Proof. Admitted.

  (** Rebuilding canonicalizes every row and empties pending work. *)
  Lemma rebuild_canonical : forall db, wf db ->
    canonical (rebuild db) /\ pending (rebuild db) = 0.
  Proof. Admitted.

  (** Rebuilding computes functional-dependency congruence. *)
  Lemma rebuild_same : forall db i j, wf db ->
    (same (view (rebuild db)) i j <-> cong db i j).
  Proof. Admitted.

  (** Every old row survives canonicalization and output merging. *)
  Lemma rebuild_keeps : forall db f k o, wf db -> row (view db) f k o ->
    exists o', row (view (rebuild db)) f (map (canon (rebuild db)) k) o' /\
      out_le (rebuild db) f (option_map (canon (rebuild db)) o) o'.
  Proof. Admitted.

  (** Every rebuilt row comes from a nonempty group of old rows. *)
  Lemma rebuild_from : forall db f k' o', wf db -> row (view (rebuild db)) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view db) f (fst ko) (snd ko) /\
        map (canon (rebuild db)) (fst ko) = k') srcs /\
      o' = merged (rebuild db) f (map snd srcs).
  Proof. Admitted.

  (** Canonical databases without pending work rebuild to themselves. *)
  Lemma rebuild_idle : forall db, wf db -> canonical db -> pending db = 0 -> rebuild db = db.
  Proof. Admitted.

  (** A database without pending work respects constructor congruence. *)
  Lemma rebuild_congruent : forall db f k1 k2 i j, wf db -> pending db = 0 ->
    row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) ->
    Forall2 (cell_rel (same (view db))) k1 k2 -> same (view db) i j.
  Proof. Admitted.

  (** Every indexed tuple comes from a row in its declared slot. *)
  Lemma index_all : forall db s new u, wf db -> I.mem (index s new db) u ->
    exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
      u = permute perm (k ++ option_list o).
  Proof. Admitted.

  (** The full index contains every row in its slot. *)
  Lemma index_all_complete : forall db s f perm k o, wf db ->
    slot_of db s = Some (f, perm) -> row (view db) f k o ->
    I.mem (index s false db) (permute perm (k ++ option_list o)).
  Proof. Admitted.

  (** Slot indexes have the declared permutation arity. *)
  Lemma index_wf : forall db s new f perm, wf db -> slot_of db s = Some (f, perm) ->
    I.wf (length perm) (index s new db).
  Proof. Admitted.

  (** Stored lookup agrees with the public row observation. *)
  Lemma old_row : forall db f k o, wf db ->
    (old db f k = Some o <-> row (view db) f k o).
  Proof. Admitted.

  (** Lookup canonicalizes its query and keeps the view and invariant. *)
  Lemma lookup_spec : forall f k db, wf db ->
    fst (lookup f k db) = old db f (map (canon db) k) /\
    view (snd (lookup f k db)) = view db /\ wf (snd (lookup f k db)).
  Proof. Admitted.

  (** Initialization records declarations and slots and starts empty. *)
  Lemma init_view : forall ds sl f k o i j,
    (row (view (init ds sl)) f k o <-> False) /\
    (same (view (init ds sl)) i j <-> i = j) /\
    kind (view (init ds sl)) f = lookup_kind ds f /\
    slots (init ds sl) = sl /\ ids (init ds sl) = 0%N /\ pending (init ds sl) = 0.
  Proof. Admitted.

  (** Insertion keeps layout and allocation and queues at most one loser. *)
  Lemma layout_put : forall f k o db, wf db ->
    kind (view (put f k o db)) = kind (view db) /\ slots (put f k o db) = slots db /\
    ids (put f k o db) = ids db /\ pending (put f k o db) <= pending db + 1.
  Proof. Admitted.

  (** Make keeps layout and returns an allocated identifier. *)
  Lemma layout_make : forall f k db, wf db ->
    kind (view (snd (make f k db))) = kind (view db) /\
    slots (snd (make f k db)) = slots db /\
    (ids (snd (make f k db)) <= N.succ (ids db))%N /\
    allocated (snd (make f k db)) (fst (make f k db)) /\
    pending (snd (make f k db)) = pending db.
  Proof. Admitted.

  (** Union keeps layout and allocation and queues at most one loser. *)
  Lemma layout_union : forall i j db, wf db ->
    kind (view (union i j db)) = kind (view db) /\ slots (union i j db) = slots db /\
    ids (union i j db) = ids db /\ pending (union i j db) <= pending db + 1.
  Proof. Admitted.

  (** Rebuilding keeps layout and allocation. *)
  Lemma layout_rebuild : forall db, wf db ->
    kind (view (rebuild db)) = kind (view db) /\ slots (rebuild db) = slots db /\
    ids (rebuild db) = ids db.
  Proof. Admitted.

  (** Advancing keeps the slot layout. *)
  Lemma layout_advance : forall db, slots (advance db) = slots db.
  Proof. Admitted.
  (** Advancing keeps allocation, pending work and representatives. *)
  Lemma advance_keeps : forall db, wf db ->
    ids (advance db) = ids db /\ pending (advance db) = pending db /\
    repr (advance db) = repr db.
  Proof. Admitted.

  (** A quiet union already holds in the old view. *)
  Lemma union_quiet : forall i j db, wf db -> changed db = false ->
    changed (union i j db) = false -> same (view db) i j.
  Proof. Admitted.

  (** A quiet make reuses a constructor row. *)
  Lemma make_quiet : forall f k db, wf db -> changed db = false ->
    changed (snd (make f k db)) = false ->
    exists j, row (view db) f (map (canon db) k) (Some (Id j)).
  Proof. Admitted.

  (** Every row identifier is allocated. *)
  Lemma row_allocated : forall db f k o i, wf db -> row (view db) f k o ->
    In (Id i) (k ++ option_list o) -> allocated db i.
  Proof. Admitted.

  (** Rebuilding keeps every satisfying model and identifier interpretation. *)
  Lemma rebuild_sat : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> sat V.merge M nu (view (rebuild db)).
  Proof. Admitted.

  (** Inserting a true, kind-correct row keeps the model. *)
  Lemma put_sat : forall (M : model (V := V.t)) nu db f k o, wf db -> kind_ok db f k o ->
    sat V.merge M nu (view db) -> holds M nu (view db) f k o ->
    sat V.merge M nu (view (put f k o db)).
  Proof. Admitted.

  (** A justified identifier union keeps the model. *)
  Lemma union_sat : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> nu i = nu j ->
    sat V.merge M nu (view (union i j db)).
  Proof. Admitted.

  (** Make updates its output meaning and keeps every other identifier meaning. *)
  Lemma make_sat : forall (M : model (V := V.t)) nu db f k, wf db ->
    kind (view db) f = Some OId ->
    (forall j, In (Id j) k -> allocated db j) ->
    sat V.merge M nu (view db) ->
    let '(i, db') := make f k db in
    exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con M f (map (den nu) k) /\ sat V.merge M nu' (view db').
  Proof. Admitted.

End Database.

Module DatabaseT (V : VALUE_T) (I : INDEX_T V) <: DATABASE_ALL V I.
  Include Database V I.
  (* spec: wmark potential *)
  (* STUB-CODE *)
  Definition wmark (db : t) : N := db_wmark db.
  Definition unit (db : t) : nat :=
    (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Definition slots_of (db : t) (f : positive) : nat :=
    length (filter (fun s => Pos.eqb (fst s) f) (slots db)).
  (* STUB-CODE *)
  Definition potential (_ : N) (_ : t) : N := 0%N.
  Definition num_slots (db : t) : nat := length (slots db).
  TimeFun init.
  TimeFun find.
  TimeFun lookup.
  TimeFun make.
  TimeFun put.
  TimeFun union.
  TimeFun db_rstep.
  TimeFun db_rebuild_fuel.
  TimeFun rebuild.
  TimeFun index.
  TimeFun advance.
  TimeFun changed.
  TimeFun ids.
  Definition c_db : N := 1. (* STUB *)
  (** Initialization starts without amortized debt. *)
  Lemma potential_init : forall B ds sl, (potential B (init ds sl) = 0)%N.
  Proof. Admitted. (* STUB *)

  (** Insertion pays for all slots and the logarithmic identifier budget. *)
  Lemma T_put_amort : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * potential B (put f k o db) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Constructor allocation has the same amortized budget as insertion. *)
  Lemma T_make_amort : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * potential B (snd (make f k db)) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Union transfers the deferred work to potential. *)
  Lemma T_union_amort : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * potential B (union i j db) <=
      N.of_nat (unit (union i j db)) * (c_db + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Rebuilding spends potential on pending union work. *)
  Lemma T_rebuild_amort : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild db + N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Slot lookup pays for the slot code. *)
  Lemma T_index_le : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Advancing visits every slot. *)
  Lemma T_advance_le : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The high-water mark covers every stored cell encoding. *)
  Lemma wmark_cells : forall db f k o c, wf db -> row (view db) f k o ->
    In c (k ++ option_list o) -> cell_bits V.encode c <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** The high-water mark covers every declared function name. *)
  Lemma wmark_names : forall db f, wf db -> kind (view db) f <> None ->
    Pos.size_nat f <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** Insertion never reduces the spending unit. *)
  Lemma unit_mono_put : forall f k o db, wf db -> unit db <= unit (put f k o db).
  Proof. Admitted. (* STUB *)

  (** Make never reduces the spending unit. *)
  Lemma unit_mono_make : forall f k db, wf db -> unit db <= unit (snd (make f k db)).
  Proof. Admitted. (* STUB *)

  (** Union never reduces the spending unit. *)
  Lemma unit_mono_union : forall i j db, wf db -> unit db <= unit (union i j db).
  Proof. Admitted. (* STUB *)

  (** Rebuilding never reduces the spending unit. *)
  Lemma unit_mono_rebuild : forall db, wf db -> unit db <= unit (rebuild db).
  Proof. Admitted. (* STUB *)
  (** Advancing keeps the watermark and the amortized credit. *)
  Lemma advance_credit : forall B db, wf db ->
    wmark (advance db) = wmark db /\ (potential B (advance db) = potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** Initialization pays for declarations and slot permutations. *)
  Lemma T_init_le : forall ds sl,
    (T_init ds sl <= c_db * N.of_nat (length ds + length sl + 1) *
      N.of_nat ((fold_right (fun s n => length (snd s) + n) 0 sl + 1)%nat) +
      c_db * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** Find traverses allocated identifiers at the database unit. *)
  Lemma T_find_le : forall i db, wf db -> allocated db i ->
    (T_find i db <= c_db * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (** Lookup charges the stored unit and query cell encodings. *)
  Lemma T_lookup_le : forall f k db, wf db ->
    (T_lookup f k db <= c_db * N.of_nat (length k + 1) * N.of_nat (unit db) +
      c_db * N.of_nat ((fold_right (fun c n => cell_bits V.encode c + n) 0 k)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** The change flag is stored. *)
  Lemma T_changed_le : forall db, (T_changed db <= c_db)%N.
  Proof. Admitted. (* STUB *)

  (** The allocation counter is stored. *)
  Lemma T_ids_le : forall db, (T_ids db <= c_db)%N.
  Proof. Admitted. (* STUB *)

  Definition use_entry := (positive * list (cell V.t))%type.
  Definition stored_row := (use_entry * option (cell V.t))%type.
  Definition repair_state := (t * list use_entry)%type.

  (* spec: rows uses_entries queue next_id forest_ok class_size uf_state
     index_counters written_cells *)
  (* STUB-CODE *)
  Definition rows : t -> list stored_row := fun _ => [].
  (* STUB-CODE *)
  Definition uses_entries : t -> list (positive * use_entry) := fun _ => [].
  (* STUB-CODE *)
  Definition queue : t -> list positive := fun _ => [].
  (* STUB-CODE *)
  Definition next_id : t -> positive := fun _ => 1%positive.
  (* STUB-CODE *)
  Definition uf_state (db : t) : UnionFind.t := db_forest db.
  (* STUB-CODE *)
  Definition class_size (db : t) (x : positive) : N :=
    N.of_nat (UnionFind.size_of (uf_state db) x).
  (** A historical row key resolves to its current stored key. *)
  (* STUB-CODE *)
  Definition located (_ : t) (_ : positive) (_ : list (cell V.t))
      : option (list (cell V.t)) := None.
  (* STUB-CODE *)
  Definition forest_ok : t -> Prop := fun _ => True.
  Definition k_credit : N := 1. (* STUB *)
  Definition k_loop : N := 1. (* STUB *)
  Definition k_active : N := 1. (* STUB *)
  Definition k_queue : N := 1. (* STUB *)
  Definition k_stop : N := 1. (* STUB *)
  Definition k_driver : N := 1. (* STUB *)

  Definition uses (db : t) (x : positive) (e : use_entry) : Prop :=
    In (x, e) (uses_entries db).
  Definition scheduled (db : t) (work : list use_entry) (e : use_entry) : Prop :=
    In e work \/ exists x, In x (queue db) /\ uses db x e.
  Definition row_ids (k : list (cell V.t)) (o : option (cell V.t)) (i : positive) : Prop :=
    In (Id i) (k ++ option_list o).

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
  (* STUB-CODE *)
  Definition nuses (db : t) : N := db_nuses db.
  (* STUB-CODE *)
  Definition npending (db : t) : N := db_npending db.
  (* STUB-CODE *)
  Definition index_counters (db : t) : list positive := db_index_counters db.
  (* STUB-CODE *)
  Definition written_cells (db : t) : list (cell V.t) := db_written_cells db.
  (* STUB-CODE *)
  Definition decl_names (_ : t) : list positive := [].
  (* STUB-CODE *)
  Definition get_uses : positive -> t -> list use_entry := fun _ _ => [].
  TimeFun get_uses.
  (* STUB-CODE *)
  Definition pop_loser : t -> option (positive * t) := fun _ => None.
  TimeFun pop_loser.
  (* STUB-CODE *)
  Definition repair_entry : use_entry -> t -> t := fun _ db => db.
  TimeFun repair_entry.
  (* STUB-CODE *)
  Definition rstep (s : repair_state) : repair_state + t := db_rstep s.
  TimeFun rstep.
  (* STUB-CODE *)
  Definition rebuild_fuel (db : t) : N := db_rebuild_fuel db.
  TimeFun rebuild_fuel.

  TimeFun locate.
  TimeFun rank_slots.
  TimeFun slots_update.
  Definition k_locate : N := 1. (* STUB *)
  Definition k_repair : N := 1. (* STUB *)
  Definition k_pop : N := 1. (* STUB *)
  Definition k_rstep : N := 1. (* STUB *)
  Definition k_slots : N := 1. (* STUB *)
  Definition k_layout : N := 1. (* STUB *)

  (* spec: row_id row_parent row_size row_current next_row *)
  (* STUB-CODE *)
  Definition row_id (_ : t) (_ : positive) (_ : list (cell V.t)) : option positive := None.
  (* STUB-CODE *)
  Definition row_parent (_ : t) (r : positive) : positive := r.
  (* STUB-CODE *)
  Definition row_size (_ : t) (_ : positive) : N := 1%N.
  (* STUB-CODE *)
  Definition row_current (_ : t) (_ : positive) : option (list (cell V.t)) := None.
  (* STUB-CODE *)
  Definition next_row (_ : t) : positive := 1%positive.
  (** Following the merge parent of a row identifier [n] times. *)
  Definition row_up (db : t) (n : nat) (r : positive) : positive :=
    Nat.iter n (row_parent db) r.
  (** A historical key resolves through a merge chain of logarithmic depth. *)
  Lemma F_row_locate : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    exists d, d <= length k * (N.to_nat (N.log2 (ids db)) + 1) /\
      row_parent db (row_up db d r) = row_up db d r /\
      located db f k = row_current db (row_up db d r).
  Proof. Admitted. (* STUB *)
  (** A key without a row identifier has no current row. *)
  Lemma F_row_absent : forall db work f k, inv_on db work -> row_id db f k = None ->
    located db f k = None.
  Proof. Admitted. (* STUB *)
  (** The executable resolution agrees with the observation. *)
  Lemma F_locate : forall db work f k, inv_on db work -> locate f k db = located db f k.
  Proof. Admitted. (* STUB *)
  (** Merged row groups at least double the losing group. *)
  Lemma F_row_by_size : forall db work r, inv_on db work -> row_parent db r <> r ->
    (1 <= row_size db r)%N /\ (2 * row_size db r <= row_size db (row_parent db r))%N.
  Proof. Admitted. (* STUB *)
  (** A row group holds at most one row per assignment of its identifier positions. *)
  Lemma F_row_group : forall db work f k r d, inv_on db work -> row_id db f k = Some r ->
    row_parent db (row_up db d r) = row_up db d r ->
    (row_size db (row_up db d r) <= (ids db + 1) ^ N.of_nat (length k))%N.
  Proof. Admitted. (* STUB *)
  (** Row identifiers stay below a counter that the watermark covers. *)
  Lemma F_row_counter : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    (r < next_row db)%positive /\ (row_parent db r < next_row db)%positive /\
    In (next_row db) (index_counters db).
  Proof. Admitted. (* STUB *)
  (** The keys of use entries are written cells. *)
  Lemma F_entry_cells : forall db work x f k c, inv_on db work -> uses db x (f, k) ->
    In c k -> In c (written_cells db).
  Proof. Admitted. (* STUB *)
  (** Resolution reads the key once and follows the chain at the stored width. *)
  Lemma T_locate_le : forall db work x f k, inv_on db work -> uses db x (f, k) ->
    (T_locate f k db <= k_locate * N.of_nat (length k + 1) * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** A repair, with its resolution, rekeying, slot updates and collision, pays its entry weight. *)
  Lemma T_repair_entry_le : forall db e rest, inv_on db (e :: rest) ->
    (T_repair_entry e db <= k_repair * N.of_nat (entry_weight db e) *
      N.of_nat (unit (repair_entry e db)))%N.
  Proof. Admitted. (* STUB *)

  (* spec: slot_place group_of group_slots proj_count *)
  (* STUB-CODE *)
  Definition slot_place (_ : t) (_ : N) : option (bool * N * N) := None.
  (* STUB-CODE *)
  Definition group_of (_ : t) (_ : positive) : option N := None.
  (* STUB-CODE *)
  Definition group_slots (_ : t) (_ : bool) (_ : N) : list N := [].
  (** Every slot has a place whose group rank and offset do not exceed the slot number. *)
  Lemma F_slot_place : forall db work s f perm, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists d g j, slot_place db s = Some (d, g, j) /\ (g <= s)%N /\ (j <= s)%N /\
      nth_error (group_slots db d g) (N.to_nat j) = Some s /\
      (d = true <-> kind (view db) f <> None) /\
      (d = true -> group_of db f = Some g /\ (g < wmark db)%N).
  Proof. Admitted. (* STUB *)
  (** A declared group lists precisely the slots of its function, once each. *)
  Lemma F_group_slots : forall db work f g, inv_on db work -> group_of db f = Some g ->
    NoDup (group_slots db true g) /\
    forall s, In s (group_slots db true g) <-> exists perm, slot_of db s = Some (f, perm).
  Proof. Admitted. (* STUB *)
  (** Initialization stores the ranking of its slot list. *)
  Lemma F_init_place : forall ds sl s,
    slot_place (init ds sl) s = nth_error (rank_slots ds sl) (N.to_nat s).
  Proof. Admitted. (* STUB *)
  (** Ranking by first appearance is linear in the slots and the bits of the names. *)
  Lemma T_rank_slots_le : forall ds sl,
    (T_rank_slots ds sl <= k_layout * N.of_nat (length ds + length sl + 1) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0%nat sl)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Initialization adds the ranking to one pass over declarations and permutations. *)
  Lemma T_init_split : forall ds sl,
    (T_init ds sl <= T_rank_slots ds sl +
      k_layout * N.of_nat (length ds + length sl + 1) *
        N.of_nat ((fold_right (fun s n => length (snd s) + n) 0%nat sl + 1)%nat) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** One update of every slot of a declared function walks its group once. *)
  Lemma T_slots_update_le : forall db work b f u, inv_on db work ->
    kind (view db) f <> None -> slots_fit db f (length u) ->
    (forall c, In c u -> cell_bits V.encode c <= N.size_nat (wmark (slots_update b f u db))) ->
    (T_slots_update b f u db <= k_slots * N.of_nat (slots_of db f + 1) *
      N.of_nat ((length u + 1) * (length u + 1)) *
      N.of_nat (unit (slots_update b f u db)))%N.
  Proof. Admitted. (* STUB *)

  (** A union finds both roots and links only distinct ones. *)
  Lemma F_union_roots : forall i j db, inv db -> allocated db i -> allocated db j ->
    let '(ri, u1) := UnionFind.find i (uf_state db) in
    let '(rj, u2) := UnionFind.find j u1 in
    uf_state (union i j db) =
      if Pos.eqb ri rj then u2 else snd (UnionFind.union ri rj u2).
  Proof. Admitted. (* STUB *)
  (** Membership and key width stay within allocation. *)
  Lemma F_uf_card : forall db work, inv_on db work ->
    UnionFind.card (uf_state db) <= 3 * N.to_nat (ids db) /\
    UnionFind.width (uf_state db) <= N.size_nat (ids db).
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition proj_count (_ : t) (_ : N) (_ : list (cell V.t)) : N := 0%N.
  (** The count of a projected tuple is the number of rows that project onto it. *)
  Lemma F_proj_count : forall db work s f perm u, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists rs, NoDup rs /\
      (forall r, In r rs <-> In r (rows db) /\ fst (fst r) = f /\
        permute perm (snd (fst r) ++ option_list (snd r)) = u) /\
      N.to_nat (proj_count db s u) = length rs.
  Proof. Admitted. (* STUB *)

  (** The counter of the empty index is recorded. *)
  Lemma F_counter_one : forall db, inv db -> In 1%positive (index_counters db).
  Proof. Admitted. (* STUB *)

  (** A driver step costs its repair, or its pop and bucket read, plus a constant. *)
  Lemma T_rstep_split : forall db work,
    (T_rstep (db, work) <= k_rstep +
      match work with
      | e :: _ => T_repair_entry e db
      | [] => T_pop_loser db +
          match pop_loser db with
          | Some (x, _) => T_get_uses x db
          | None => 0
          end
      end)%N.
  Proof. Admitted. (* STUB *)
  (** A pop moves the selected bucket at one step per entry. *)
  Lemma T_pop_loser_le : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    (T_pop_loser db <= k_pop * N.of_nat (work_weight db (bucket db x) + 1) *
      N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** An empty pop reads the stored queue. *)
  Lemma T_pop_none_le : forall db, inv db -> pop_loser db = None ->
    (T_pop_loser db <= k_pop * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** A bucket is read by one keyed lookup. *)
  Lemma T_get_uses_le : forall db work x, inv_on db work -> allocated db x ->
    (T_get_uses x db <= k_pop * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition rebuild_measure : repair_state -> nat := fun _ => 0.

  (** Public well-formedness is the maintained invariant at an empty active batch. *)
  Lemma F1_inv_wf : forall db, wf db <-> inv db.
  Proof. Admitted. (* STUB *)

  (** The public potential is the weighted occurrence credit. *)
  Lemma F2_potential : forall B db, (potential B db = k_loop * rebuild_potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** The unit charges identifier traversal and cell encoding widths. *)
  Lemma F3_unit : forall db,
    unit db = (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Proof. Admitted. (* STUB *)

  (** Direct bucket lookup agrees with the occurrence inventory. *)
  Lemma F4_bucket : forall db work x, inv_on db work -> get_uses x db = bucket db x.
  Proof. Admitted. (* STUB *)

  (** An empty pop detects an empty pending queue. *)
  Lemma F4_pop_none : forall db, inv db -> (pop_loser db = None <-> queue db = []).
  Proof. Admitted. (* STUB *)

  (** A pop transfers its selected bucket into the active work list. *)
  Lemma F4_pop : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    queue db = x :: queue db' /\ view db' = view db /\
    (forall y e, uses db' y e <->
      (uses db y e /\ y <> x) \/ (y = repr db x /\ uses db x e)) /\
    N.to_nat (nuses db') = length (uses_entries db') /\
    inv_on db' (bucket db x).
  Proof. Admitted. (* STUB *)

  (** The driver consumes one active entry or dequeues one loser. *)
  Lemma F5_rstep : forall db work,
    rstep (db, work) =
      match work with
      | e :: rest => inl (repair_entry e db, rest)
      | [] =>
        match pop_loser db with
        | None => inr db
        | Some (x, db') => inl (db', get_uses x db)
        end
      end.
  Proof. Admitted. (* STUB *)

  (** Entries without a current row are discarded without changing the database. *)
  Lemma F6_absent : forall db f k,
    located db f k = None -> repair_entry (f, k) db = db.
  Proof. Admitted. (* STUB *)

  (** Repair discharges one active occurrence and retains coverage of affected rows. *)
  Lemma F7_repair_inv : forall db e rest, inv_on db (e :: rest) ->
    inv_on (repair_entry e db) rest.
  Proof. Admitted. (* STUB *)

  (** Continuing steps retain the queue and active-batch invariant. *)
  Lemma F8_rstep_inv : forall s s', state_inv s -> rstep s = inl s' -> state_inv s'.
  Proof. Admitted. (* STUB *)

  (** Repair retains kinds and identifier allocation. *)
  Lemma F9_rstep_layout : forall s s', state_inv s -> rstep s = inl s' ->
    kind (view (fst s')) = kind (view (fst s)) /\ ids (fst s') = ids (fst s).
  Proof. Admitted. (* STUB *)

  (** Collision unions keep the same functional-dependency closure. *)
  Lemma F10_rstep_cong : forall s s' i j, state_inv s -> rstep s = inl s' ->
    (cong (fst s') i j <-> cong (fst s) i j).
  Proof. Admitted. (* STUB *)

  (** Every old row survives one step at an equivalent, possibly unfinished key. *)
  Lemma F11_rstep_keeps : forall s s' f k o, state_inv s -> rstep s = inl s' ->
    row (view (fst s)) f k o ->
    exists k' o', row (view (fst s')) f k' o' /\
      Forall2 (cell_rel (same (view (fst s')))) k k' /\
      out_le (fst s') f (option_map (canon (fst s')) o) o'.
  Proof. Admitted. (* STUB *)

  (** Every repaired row groups a nonempty list of rows from before the step. *)
  Lemma F12_rstep_from : forall s s' f k' o', state_inv s -> rstep s = inl s' ->
    row (view (fst s')) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view (fst s)) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view (fst s')))) (fst ko) k') srcs /\
      output_equiv (fst s') o' (merged (fst s') f (map snd srcs)).
  Proof. Admitted. (* STUB *)

  (** A stopped driver exposes canonical rows and constructor closure. *)
  Lemma F13_rstep_done : forall s r, state_inv s -> rstep s = inr r ->
    r = fst s /\ snd s = [] /\ inv r /\ canonical r /\ pending r = 0 /\
    (forall f k1 k2 i j, row (view r) f k1 (Some (Id i)) ->
      row (view r) f k2 (Some (Id j)) ->
      Forall2 (cell_rel (same (view r))) k1 k2 -> same (view r) i j).
  Proof. Admitted. (* STUB *)

  (** Continuing steps strictly decrease a measure that includes active work. *)
  Lemma F14_rstep_measure : forall s s', state_inv s -> rstep s = inl s' ->
    rebuild_measure s' < rebuild_measure s.
  Proof. Admitted. (* STUB *)

  (** Fuel budgets logarithmic relabelings of all stored use occurrences. *)
  Lemma F15_fuel_formula : forall db, rebuild_fuel db =
    ((N.size (ids db) + 2) * (nuses db + 1) + npending db + 1)%N.
  Proof. Admitted. (* STUB *)

  (** Computed fuel includes the final stop call. *)
  Lemma F15_fuel_enough : forall db, inv db ->
    (N.of_nat (rebuild_measure (db, [])) < rebuild_fuel db)%N.
  Proof. Admitted. (* STUB *)

  (** The rebuild operation runs the same step and fuel as the plan. *)
  Lemma F16_rebuild_run : forall db, wf db ->
    loopN rstep (rebuild_fuel db) (db, []) = inr (rebuild db).
  Proof. Admitted. (* STUB *)

  (** Congruent cells have equal denotations in every satisfying model. *)
  Lemma F17_cong_den : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> cong db i j -> nu i = nu j.
  Proof. Admitted. (* STUB *)

  (** Nonempty output groups keep their model meaning through the actual merge fold. *)
  Lemma F18_merged_holds : forall (M : model (V := V.t)) nu db f k os,
    wf db -> lat_closed V.merge M (view db) -> os <> [] -> (forall i, nu (repr db i) = nu i) ->
    Forall (holds M nu (view db) f k) os ->
    holds M nu (view db) f k (merged db f os).
  Proof. Admitted. (* STUB *)

  (** Repair preserves satisfaction through its collision, lattice and index branches. *)
  Lemma F19_rstep_sat : forall (M : model (V := V.t)) nu s s',
    state_inv s -> rstep s = inl s' -> sat V.merge M nu (view (fst s)) ->
    sat V.merge M nu (view (fst s')).
  Proof. Admitted. (* STUB *)

  (** Lineage retains original row groups throughout repeated deletion and reinsertion. *)
  Definition lineage (initial current : t) : Prop :=
    forall f k o, row (view current) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view current))) (fst ko) k) srcs /\
      output_equiv current o (merged current f (map snd srcs)).
  (** Singleton source groups establish lineage before the first repair. *)
  Lemma F20_lineage_initial : forall db, inv db -> lineage db db.
  Proof. Admitted. (* STUB *)

  (** Actual repair flattens source groups through canonicalization and lattice merging. *)
  Lemma F21_lineage_step : forall initial s s', state_inv s ->
    rstep s = inl s' -> lineage initial (fst s) -> lineage initial (fst s').
  Proof. Admitted. (* STUB *)

  (** Stopped lineage gives the exact public output equation for each original group. *)
  Lemma F22_lineage_done : forall initial s r, inv initial -> state_inv s ->
    rstep s = inr r -> lineage initial r ->
    forall f k o, row (view r) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        map (canon r) (fst ko) = k) srcs /\ o = merged r f (map snd srcs).
  Proof. Admitted. (* STUB *)


  (** A losing root enters a class at least twice as large. *)
  Lemma T1_doubling : forall db i j x, inv db -> repr db x = x ->
    repr (union i j db) x <> x ->
    (2 * class_size db x <= class_size (union i j db) (repr (union i j db) x))%N.
  Proof. Admitted. (* STUB *)

  (** Initialization has no use-occurrence debt. *)
  Lemma T2_init_credit : forall B ds sl, (rebuild_potential B (init ds sl) = 0)%N.
  Proof. Admitted. (* STUB *)

  (** Insertion pays its executable work and new occurrence credit. *)
  Lemma T3_put_credit : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * (k_loop * rebuild_potential B (put f k o db)) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Allocation pays new occurrences through the insertion budget. *)
  Lemma T4_make_credit : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * (k_loop * rebuild_potential B (snd (make f k db))) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Union pays its root link and queued repair credit. *)
  Lemma T5_union_credit : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * (k_loop * rebuild_potential B (union i j db)) <=
      N.of_nat (unit (union i j db)) * (c_db + (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Continuing steps spend queued and active credit without a per-entry allowance. *)
  Lemma T6_rstep_go : forall B U s s', state_inv s -> (ids (fst s') <= B)%N ->
    unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + k_loop * N.of_nat U * state_potential B s' <
      k_loop * N.of_nat U * state_potential B s)%N.
  Proof. Admitted. (* STUB *)

  (** Stopping charges one unit of the final database. *)
  Lemma T7_rstep_stop : forall s r, state_inv s -> rstep s = inr r ->
    (T_rstep s <= k_stop * N.of_nat (unit (fst s)))%N.
  Proof. Admitted. (* STUB *)

  (** Continuing steps also pay the binary loop driver's per-step charge. *)
  Lemma T6a_rstep_credit : forall B U s s', state_inv s ->
    (ids (fst s') <= B)%N -> unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * state_potential B s' <=
      k_loop * N.of_nat U * state_potential B s)%N.
  Proof. Admitted. (* STUB *)

  (** Stopping retains result credit and spends the reserved stop allowance. *)
  Lemma T7a_stop_credit : forall B U s r, state_inv s -> unit (fst s) <= U ->
    rstep s = inr r ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * rebuild_potential B r <=
      k_loop * N.of_nat U * state_potential B s + k_stop * N.of_nat U)%N.
  Proof. Admitted. (* STUB *)


  (** The actual loop must fit the public budget after all use-entry charges are summed. *)
  Lemma T8_rebuild_loop : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild_fuel db + T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver +
      N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** The wrapper exposes fuel construction and driver overhead. *)
  Lemma T9_rebuild_driver : forall db,
    (T_rebuild db <= T_rebuild_fuel db +
      T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver)%N.
  Proof. Admitted. (* STUB *)

  (** Slot lookup charges its binary slot code. *)
  Lemma T10_index : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Advancing clears each maintained slot once. *)
  Lemma T11_advance : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Stored counters agree with the occurrence inventory and pending queue. *)
  Lemma F15_counts : forall db work, inv_on db work ->
    N.to_nat (nuses db) = length (uses_entries db) /\ N.of_nat (pending db) = npending db.
  Proof. Admitted. (* STUB *)

  (** The declaration inventory contains precisely the names with a kind. *)
  Lemma F_decl_names : forall db f, inv db ->
    (kind (view db) f <> None <-> In f (decl_names db)).
  Proof. Admitted. (* STUB *)

  (** The stored watermark is the exact historical maximum of written payloads and counters. *)
  Lemma F_wmark : forall db, inv db ->
    wmark db = fold_right N.max (N.max (nuses db) (ids db))
      (map Npos (index_counters db) ++ map Npos (decl_names db) ++
        map (fun c => match c with
          | Id i => Npos (xO i)
          | Val v => Npos (xI (V.encode v))
          end) (written_cells db)).
  Proof. Admitted. (* STUB *)

  (** Every slot index fits the stored counter and cell watermark. *)
  Lemma F_wmark_index : forall db s new, inv db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** Class sizes come from the size-based union-find. *)
  Lemma F_uf_bridge : forall db work x, inv_on db work ->
    repr db x = UnionFind.repr (uf_state db) x /\
    class_size db x = N.of_nat (UnionFind.size_of (uf_state db) x) /\
    UnionFind.wf (uf_state db).
  Proof. Admitted. (* STUB *)

  (** Root classes are nonempty and bounded by allocation. *)
  Lemma F_class_size : forall db work x, inv_on db work ->
    (1 <= class_size db (repr db x))%N /\
    (class_size db (repr db x) <= N.max 1 (ids db))%N.
  Proof. Admitted. (* STUB *)

  (** Collision unions also double the losing class. *)
  Lemma F_rstep_doubling : forall s s' x, state_inv s -> rstep s = inl s' ->
    repr (fst s) x = x -> repr (fst s') x <> x ->
    (2 * class_size (fst s) x <= class_size (fst s') (repr (fst s') x))%N.
  Proof. Admitted. (* STUB *)

  (** Repair never reduces the spending unit. *)
  Lemma F9b_rstep_unit : forall s s', state_inv s -> rstep s = inl s' ->
    unit (fst s) <= unit (fst s').
  Proof. Admitted. (* STUB *)

  (** Loop credit includes the binary driver charge. *)
  Lemma k_loop_le : (c_loopN <= k_loop)%N.
  Proof. Admitted. (* STUB *)

  (** Fuel construction uses stored binary counters. *)
  Lemma T7b_fuel : forall db, inv db ->
    (T_rebuild_fuel db <= k_driver * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (** The [T_loopN_amort] driver retains the final database credit. *)
  Lemma T8a_loop_final : forall B U db, inv db -> (ids (rebuild db) <= B)%N ->
    unit (rebuild db) <= U ->
    (T_loopN rstep T_rstep (rebuild_fuel db) (db, []) +
      k_loop * N.of_nat U * rebuild_potential B (rebuild db) <=
      k_loop * N.of_nat U * rebuild_potential B db + k_stop * N.of_nat U +
      c_loopN * N.of_nat (N.size_nat (rebuild_fuel db) + 1))%N.
  Proof. Admitted. (* STUB *)

End DatabaseT.
