(** * Placeholder database operations

    Databases store rows and identifier equalities.
    For example, an initialized database supplies indexes on request.
    Builds on: DatabaseSig. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Std Loop.
From Galois.Egglog Require Import ValueSig IndexSig Syntax Model DatabaseSig.

Import List.ListNotations.

Module DatabaseCode (V : VALUE_OPS) (I : INDEX_OPS V) <: DATABASE_OPS V I.
  Definition t := unit.
  (* STUB-CODE *)
  Definition init (_ : list decl) (_ : list (positive * list nat)) : t := tt.
  (* STUB-CODE *)
  Definition find (i : positive) (db : t) : positive * t := (i, db).
  (* STUB-CODE *)
  Definition lookup (_ : positive) (_ : list (cell V.t)) (db : t)
      : option (option (cell V.t)) * t := (None, db).
  (* STUB-CODE *)
  Definition make (i : positive) (_ : list (cell V.t)) (db : t) : positive * t := (i, db).
  (* STUB-CODE *)
  Definition put (_ : positive) (_ : list (cell V.t)) (_ : option (cell V.t)) (db : t) := db.
  (* STUB-CODE *)
  Definition union (_ _ : positive) (db : t) := db.
  (* STUB-CODE *)
  Definition rebuild (db : t) := db.
  (* STUB-CODE *)
  Definition index (_ : nat) (_ : bool) (_ : t) : I.t := I.empty.
  (* STUB-CODE *)
  Definition advance (db : t) := db.
  (* STUB-CODE *)
  Definition changed (_ : t) := false.
  (* STUB-CODE *)
  Definition ids (_ : t) : N := 0%N.
End DatabaseCode.

Module Database (V : VALUE) (I : INDEX V) <: DATABASE V I.
  Include DatabaseCode V I.
  Include DATABASE_SPEC V I.
  
  Definition wf : t -> Prop := fun _ => True.
  Definition view : t -> Model.view (V := V.t) := fun _ => {| row := fun _ _ _ => False; same := fun _ _ => False; kind := fun _ => None |}.
  Definition repr : t -> positive -> positive := fun _ i => i.
  Definition pending : t -> nat := fun _ => 0.
  Definition kind_ok : t -> positive -> list (cell V.t) -> option (cell V.t) -> Prop := fun _ _ _ _ => True.
  Definition old : t -> positive -> list (cell V.t) -> option (option (cell V.t)) := fun _ _ _ => None.
  Definition conflict : t -> positive -> list (cell V.t) -> option (cell V.t) ->
    positive -> positive -> Prop := fun _ _ _ _ _ _ => False.
  Definition fresh_id : t -> positive -> Prop := fun _ _ => False.
  Definition extends_by : t -> t -> positive -> list (cell V.t) -> positive -> Prop := fun _ _ _ _ _ => False.
  Definition slot_of : t -> nat -> option (positive * list nat) := fun _ _ => None.
  Definition permute : list nat -> list (cell V.t) -> list (cell V.t) := fun _ k => k.
  Definition merged : t -> positive -> list (option (cell V.t)) -> option (cell V.t) := fun _ _ _ => None.
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
  
    Lemma same_repr : forall db i j, wf db ->
    (same (view db) i j <-> repr db i = repr db j).
  Proof. Admitted.
  
    Lemma wf_init : forall ds sl, wf (init ds sl).
  Proof. Admitted.
  
    Lemma wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Proof. Admitted.
  
    Lemma wf_make : forall f k db, wf db -> wf (snd (make f k db)).
  Proof. Admitted.
  
    Lemma wf_union : forall i j db, wf db -> wf (union i j db).
  Proof. Admitted.
  
    Lemma wf_rebuild : forall db, wf db -> wf (rebuild db).
  Proof. Admitted.
  
    Lemma wf_advance : forall db, wf db ->
    wf (advance db) /\ view (advance db) = view db /\ changed (advance db) = false.
  Proof. Admitted.
  
    Lemma find_spec : forall i db, wf db ->
    fst (find i db) = repr db i /\ view (snd (find i db)) = view db.
  Proof. Admitted.
  
    Lemma row_functional : forall db f k o1 o2, wf db ->
    row (view db) f k o1 -> row (view db) f k o2 -> o1 = o2.
  Proof. Admitted.
  
    Lemma put_rows : forall f k o db, wf db -> kind_ok db f k o ->
    let ck := map (canon db) k in let co := option_map (canon db) o in
    forall f' k' o', row (view (put f k o db)) f' k' o' <->
      (row (view db) f' k' o' /\ (f', k') <> (f, ck)) \/
      (f' = f /\ k' = ck /\ combine db f (old db f ck) co = o').
  Proof. Admitted.
  
    Lemma put_same : forall f k o db i j, wf db -> kind_ok db f k o ->
    (same (view (put f k o db)) i j <->
      clos_refl_sym_trans positive
        (fun a b => same (view db) a b \/ conflict db f k o a b) i j).
  Proof. Admitted.
  
    Lemma put_quiet : forall f k o db, wf db -> kind_ok db f k o ->
    changed db = false -> changed (put f k o db) = false ->
    view (put f k o db) = view db /\ present_put (view db) f (map (canon db) k) o.
  Proof. Admitted.
  
    Lemma make_spec : forall f k db, wf db -> kind (view db) f = Some OId ->
    let '(i, db') := make f k db in
    (exists j, row (view db) f (map (canon db) k) (Some (Id j)) /\
      i = repr db j /\ db' = db) \/
    (fresh_id db i /\ row (view db') f (map (canon db) k) (Some (Id i)) /\
      extends_by db db' f k i).
  Proof. Admitted.
  
    Lemma union_same : forall i j db k l, wf db ->
    (same (view (union i j db)) k l <->
      clos_refl_sym_trans positive (fun a b => same (view db) a b \/ (a, b) = (i, j)) k l).
  Proof. Admitted.
  
    Lemma union_rows : forall i j db, wf db ->
    row (view (union i j db)) = row (view db).
  Proof. Admitted.
  
    Lemma rebuild_canonical : forall db, wf db ->
    canonical (rebuild db) /\ pending (rebuild db) = 0.
  Proof. Admitted.
  
    Lemma rebuild_same : forall db i j, wf db ->
    (same (view (rebuild db)) i j <-> cong db i j).
  Proof. Admitted.
  
    Lemma rebuild_keeps : forall db f k o, wf db -> row (view db) f k o ->
    exists o', row (view (rebuild db)) f (map (canon (rebuild db)) k) o' /\
      out_le (rebuild db) f (option_map (canon (rebuild db)) o) o'.
  Proof. Admitted.
  
    Lemma rebuild_from : forall db f k' o', wf db -> row (view (rebuild db)) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view db) f (fst ko) (snd ko) /\
        map (canon (rebuild db)) (fst ko) = k') srcs /\
      o' = merged (rebuild db) f (map snd srcs).
  Proof. Admitted.
  
    Lemma rebuild_idle : forall db, wf db -> canonical db -> pending db = 0 -> rebuild db = db.
  Proof. Admitted.
  
    Lemma rebuild_congruent : forall db f k1 k2 i j, wf db -> pending db = 0 ->
    row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) ->
    Forall2 (cell_rel (same (view db))) k1 k2 -> same (view db) i j.
  Proof. Admitted.
  
    Lemma index_all : forall db s new u, wf db -> I.mem (index s new db) u ->
    exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
      u = permute perm (k ++ option_list o).
  Proof. Admitted.
  
    Lemma index_all_complete : forall db s f perm k o, wf db ->
    slot_of db s = Some (f, perm) -> row (view db) f k o ->
    I.mem (index s false db) (permute perm (k ++ option_list o)).
  Proof. Admitted.
  
    Lemma index_wf : forall db s new f perm, wf db -> slot_of db s = Some (f, perm) ->
    I.wf (length perm) (index s new db).
  Proof. Admitted.

End Database.

Module DatabaseT (V : VALUE_T) (I : INDEX_T V) <: DATABASE_ALL V I.
  Include Database V I.
  TimeFun init.
  TimeFun find.
  TimeFun lookup.
  TimeFun make.
  TimeFun put.
  TimeFun union.
  TimeFun rebuild.
  TimeFun index.
  TimeFun advance.
  TimeFun changed.
  TimeFun ids.
  Definition unit (_ : t) : nat := 0.
  Definition slots_of (_ : t) (_ : positive) : nat := 0.
  Definition potential (_ : N) (_ : t) : nat := 0.
  Definition num_slots (_ : t) : nat := 0.
  Definition c_db : nat := 1. (* STUB *)
  
                              
    Lemma potential_init : forall B ds sl, potential B (init ds sl) = 0.
  Proof. Admitted. (* STUB *)
  
    Lemma T_put_amort : forall B f k o db, wf db -> (ids (put f k o db) <= B)%N ->
    T_put f k o db + potential B (put f k o db) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T_make_amort : forall B f k db, wf db -> (ids (snd (make f k db)) <= B)%N ->
    T_make f k db + potential B (snd (make f k db)) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T_union_amort : forall B i j db, wf db ->
    T_union i j db + potential B (union i j db) <= c_db * unit db + potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T_rebuild_amort : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    T_rebuild db + potential B (rebuild db) <=
      c_db * (pending db + 1) * unit db + potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T_index_le : forall s new db,
    T_index s new db <= c_db * (Nat.log2 (S s) + 1).
  Proof. Admitted. (* STUB *)
  
    Lemma T_advance_le : forall db, T_advance db <= c_db * (num_slots db + 1).
  Proof. Admitted. (* STUB *)

  Definition use_entry := (positive * list (cell V.t))%type.
  Definition stored_row := (use_entry * option (cell V.t))%type.
  Definition repair_state := (t * list use_entry)%type.

  
    (* STUB-CODE *)
  Definition rows : t -> list stored_row := fun _ => [].
    (* STUB-CODE *)
  Definition uses_entries : t -> list (positive * use_entry) := fun _ => [].
    (* STUB-CODE *)
  Definition queue : t -> list positive := fun _ => [].
    (* STUB-CODE *)
  Definition next_id : t -> positive := fun _ => 1%positive.
    (* STUB-CODE *)
  Definition forest_ok : t -> Prop := fun _ => True.
    (* STUB-CODE *)
  Definition class_size : t -> positive -> N := fun _ _ => 0%N.
    (* STUB-CODE *)
  Definition live_use : t -> positive * use_entry -> bool := fun _ _ => false.
    (* STUB-CODE *)
  Definition max_bits : t -> nat := fun _ => 0.
  Definition k_credit := 1. (* STUB *)
  Definition k_stale := 1. (* STUB *)
  Definition k_active := 1. (* STUB *)
  Definition k_queue := 1. (* STUB *)
  Definition k_stop := 1. (* STUB *)
  Definition k_driver := 1. (* STUB *)

  Definition uses (db : t) (x : positive) (e : use_entry) : Prop :=
    In (x, e) (uses_entries db).
  Definition scheduled (db : t) (work : list use_entry) (e : use_entry) : Prop :=
    In e work \/ exists x, In x (queue db) /\ uses db x e.
  Definition row_ids (k : list (cell V.t)) (o : option (cell V.t)) (i : positive) : Prop :=
    In (Id i) (k ++ option_list o).

  
  Definition inv_on (db : t) (work : list use_entry) : Prop :=
    (forall f k o, In ((f, k), o) (rows db) <-> row (view db) f k o) /\
    NoDup (map fst (rows db)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i ->
      uses db (repr db i) (f, k)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i -> repr db i <> i ->
      scheduled db work (f, k)) /\
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
    NoDup (queue db) /\ pending db = length (queue db).
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
    if live_use db xe then
      N.to_nat (N.log2 B - N.log2 (class_size db (repr db (fst xe)))) *
        entry_weight db (snd xe)
    else 0.
  Definition stale_count (db : t) : nat :=
    length (filter (fun xe => negb (live_use db xe)) (uses_entries db)).
  
  Definition rebuild_potential (B : N) (db : t) : nat :=
    k_credit * fold_right (fun xe n => use_credit B db xe + n) 0 (uses_entries db) +
    k_stale * stale_count db.
  Definition work_weight (db : t) (work : list use_entry) : nat :=
    fold_right (fun e n => entry_weight db e + n) 0 work.
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
  Definition rstep : repair_state -> repair_state + t := fun s => inr (fst s).
  TimeFun rstep.
    (* STUB-CODE *)
  Definition rebuild_fuel : t -> nat := fun _ => 0.
  TimeFun rebuild_fuel.
    (* STUB-CODE *)
  Definition rebuild_measure : repair_state -> nat := fun _ => 0.
        
  
    Lemma F1_inv_wf : forall db, wf db <-> inv db.
  Proof. Admitted. (* STUB *)
  
    Lemma F2_potential : forall B db, potential B db = rebuild_potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma F3_unit : forall db,
    unit db = (N.to_nat (N.log2 (ids db)) + 1) * (max_bits db + 1).
  Proof. Admitted. (* STUB *)
  
    Lemma F4_bucket : forall db work x, inv_on db work -> get_uses x db = bucket db x.
  Proof. Admitted. (* STUB *)
  
    Lemma F4_pop_none : forall db, inv db -> (pop_loser db = None <-> queue db = []).
  Proof. Admitted. (* STUB *)
  
    Lemma F4_pop : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    queue db = x :: queue db' /\ view db' = view db /\
    uses_entries db' = uses_entries db /\ inv_on db' (bucket db x).
  Proof. Admitted. (* STUB *)
  
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
  
    Lemma F6_absent : forall db f k, old db f k = None -> repair_entry (f, k) db = db.
  Proof. Admitted. (* STUB *)
  
    Lemma F7_repair_inv : forall db e rest, inv_on db (e :: rest) ->
    inv_on (repair_entry e db) rest.
  Proof. Admitted. (* STUB *)
  
    Lemma F8_rstep_inv : forall s s', state_inv s -> rstep s = inl s' -> state_inv s'.
  Proof. Admitted. (* STUB *)
  
    Lemma F9_rstep_layout : forall s s', state_inv s -> rstep s = inl s' ->
    kind (view (fst s')) = kind (view (fst s)) /\ ids (fst s') = ids (fst s).
  Proof. Admitted. (* STUB *)
  
    Lemma F10_rstep_cong : forall s s' i j, state_inv s -> rstep s = inl s' ->
    (cong (fst s') i j <-> cong (fst s) i j).
  Proof. Admitted. (* STUB *)
  
    Lemma F11_rstep_keeps : forall s s' f k o, state_inv s -> rstep s = inl s' ->
    row (view (fst s)) f k o ->
    exists k' o', row (view (fst s')) f k' o' /\
      Forall2 (cell_rel (same (view (fst s')))) k k' /\
      out_le (fst s') f (option_map (canon (fst s')) o) o'.
  Proof. Admitted. (* STUB *)
  
    Lemma F12_rstep_from : forall s s' f k' o', state_inv s -> rstep s = inl s' ->
    row (view (fst s')) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view (fst s)) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view (fst s')))) (fst ko) k') srcs /\
      output_equiv (fst s') o' (merged (fst s') f (map snd srcs)).
  Proof. Admitted. (* STUB *)
  
    Lemma F13_rstep_done : forall s r, state_inv s -> rstep s = inr r ->
    r = fst s /\ snd s = [] /\ inv r /\ canonical r /\ pending r = 0 /\
    (forall f k1 k2 i j, row (view r) f k1 (Some (Id i)) ->
      row (view r) f k2 (Some (Id j)) ->
      Forall2 (cell_rel (same (view r))) k1 k2 -> same (view r) i j).
  Proof. Admitted. (* STUB *)
  
    Lemma F14_rstep_measure : forall s s', state_inv s -> rstep s = inl s' ->
    rebuild_measure s' < rebuild_measure s.
  Proof. Admitted. (* STUB *)
  
    Lemma F15_fuel_formula : forall db, rebuild_fuel db =
    (N.to_nat (N.log2 (ids db)) + 2) * (length (uses_entries db) + 1) + pending db + 1.
  Proof. Admitted. (* STUB *)
  
    Lemma F15_fuel_enough : forall db, inv db ->
    rebuild_measure (db, []) < rebuild_fuel db.
  Proof. Admitted. (* STUB *)
  
    Lemma F16_rebuild_run : forall db, wf db ->
    loop_fuel rstep (rebuild_fuel db) (db, []) = inr (rebuild db).
  Proof. Admitted. (* STUB *)

  
    Lemma F17_cong_den : forall (M : model V.merge) nu db i j, wf db ->
    sat V.merge M nu (view db) -> cong db i j -> nu i = nu j.
  Proof. Admitted. (* STUB *)
  
    Lemma F18_merged_holds : forall (M : model V.merge) nu db f k os,
    wf db -> os <> [] -> (forall i, nu (repr db i) = nu i) ->
    Forall (holds V.merge M nu (view db) f k) os ->
    holds V.merge M nu (view db) f k (merged db f os).
  Proof. Admitted. (* STUB *)
  
    Lemma F19_rstep_sat : forall (M : model V.merge) nu s s',
    state_inv s -> rstep s = inl s' -> sat V.merge M nu (view (fst s)) ->
    sat V.merge M nu (view (fst s')).
  Proof. Admitted. (* STUB *)
  
  Definition lineage (initial current : t) : Prop :=
    forall f k o, row (view current) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view current))) (fst ko) k) srcs /\
      output_equiv current o (merged current f (map snd srcs)).
  
    Lemma F20_lineage_initial : forall db, inv db -> lineage db db.
  Proof. Admitted. (* STUB *)
  
    Lemma F21_lineage_step : forall initial s s', state_inv s ->
    rstep s = inl s' -> lineage initial (fst s) -> lineage initial (fst s').
  Proof. Admitted. (* STUB *)
  
    Lemma F22_lineage_done : forall initial s r, inv initial -> state_inv s ->
    rstep s = inr r -> lineage initial r ->
    forall f k o, row (view r) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        map (canon r) (fst ko) = k) srcs /\ o = merged r f (map snd srcs).
  Proof. Admitted. (* STUB *)

  
    Lemma rebuild_sat : forall (M : model V.merge) nu db,
    sat V.merge M nu (view db) -> sat V.merge M nu (view (rebuild db)).
  Proof. Admitted. (* STUB *)
  
    Lemma put_sat : forall (M : model V.merge) nu db f k o, wf db -> kind_ok db f k o ->
    sat V.merge M nu (view db) -> holds V.merge M nu (view db) f k o ->
    sat V.merge M nu (view (put f k o db)).
  Proof. Admitted. (* STUB *)
  
    Lemma union_sat : forall (M : model V.merge) nu db i j, wf db ->
    sat V.merge M nu (view db) -> nu i = nu j ->
    sat V.merge M nu (view (union i j db)).
  Proof. Admitted. (* STUB *)
  
  
    Lemma make_sat : forall (M : model V.merge) nu db f k, wf db ->
    kind (view db) f = Some OId ->
    sat V.merge M nu (view db) ->
    let '(i, db') := make f k db in
    exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con V.merge M f (map (den V.merge nu) k) /\ sat V.merge M nu' (view db').
  Proof. Admitted. (* STUB *)

  
  
    Lemma T1_doubling : forall db i j x, inv db -> repr db x = x ->
    repr (union i j db) x <> x ->
    (2 * class_size db x <= class_size (union i j db) (repr (union i j db) x))%N.
  Proof. Admitted. (* STUB *)
  
    Lemma T2_init_credit : forall B ds sl, rebuild_potential B (init ds sl) = 0.
  Proof. Admitted. (* STUB *)
  
    Lemma T3_put_credit : forall B f k o db, wf db -> (ids (put f k o db) <= B)%N ->
    T_put f k o db + rebuild_potential B (put f k o db) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      rebuild_potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T4_make_credit : forall B f k db, wf db -> (ids (snd (make f k db)) <= B)%N ->
    T_make f k db + rebuild_potential B (snd (make f k db)) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1) * unit db +
      rebuild_potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T5_union_credit : forall B i j db, wf db ->
    T_union i j db + rebuild_potential B (union i j db) <=
      c_db * unit db + rebuild_potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T6_rstep_go : forall B s s', state_inv s -> (ids (fst s') <= B)%N ->
    rstep s = inl s' ->
    T_rstep s + potential B (fst s') < potential B (fst s) + c_db * unit (fst s).
  Proof. Admitted. (* STUB *)
  
    Lemma T7_rstep_stop : forall s r, state_inv s -> rstep s = inr r ->
    T_rstep s <= k_stop * unit (fst s).
  Proof. Admitted. (* STUB *)
  
  
    Lemma T8_rebuild_loop : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    T_rebuild_fuel db +
      T_loop_fuel rstep T_rstep (rebuild_fuel db) (db, []) + k_driver +
      potential B (rebuild db) <=
      c_db * (pending db + 1) * unit db + potential B db.
  Proof. Admitted. (* STUB *)
  
    Lemma T9_rebuild_driver : forall db,
    T_rebuild db <= T_rebuild_fuel db +
      T_loop_fuel rstep T_rstep (rebuild_fuel db) (db, []) + k_driver.
  Proof. Admitted. (* STUB *)
  
    Lemma T10_index : forall s new db,
    T_index s new db <= c_db * (Nat.log2 (S s) + 1).
  Proof. Admitted. (* STUB *)
  
    Lemma T11_advance : forall db, T_advance db <= c_db * (num_slots db + 1).
  Proof. Admitted. (* STUB *)


End DatabaseT.
