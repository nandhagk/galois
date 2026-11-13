(** * Placeholder equality saturation

    These operations provide the front end for adding expressions and running rewrites.
    For example, the placeholder returns an iteration limit on an empty database.
    Builds on: SaturateSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig Syntax Model Sorts.
From Galois.Egraph Require Import Syntax CompileSig SaturateSig.

Import List.ListNotations.

Module SaturateCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (E : RUN_OPS V I J D) (C : COMPILE_OPS V)
    <: SATURATE_OPS V I J D E C.
  (* STUB-CODE *)
  Definition check_front (_ : list decl) (_ : list (rewrite V.t)) (_ : list (rule V.t))
      (_ : list (fexpr V.t)) : option reject := None.
  (* STUB-CODE *)
  Definition add_expr (_ : fexpr V.t) (db : D.t) : positive * D.t := (1%positive, db).
  (* STUB-CODE *)
  Definition saturate (_ : list decl) (_ : list (rewrite V.t)) (_ : list (rule V.t))
      (_ : limits) (_ : list (fexpr V.t)) : reject + (stop * D.t * list positive) :=
    inr (IterLimit, D.init [] [], []).
End SaturateCode.

Module Saturate (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) <: SATURATE V I J D E C.
  Include SaturateCode V I J D E C.
  Include SATURATE_SPEC V I J D E C.
  Lemma check_front_spec : forall ds rws ans es,
    check_front ds rws ans es = None <-> front_ok ds rws ans es.
  Proof. Admitted. (* STUB *)

  Lemma check_front_report : forall ds rws ans es e,
    check_front ds rws ans es = Some e -> rejected ds rws ans es e.
  Proof. Admitted. (* STUB *)

  Lemma saturate_rejects : forall ds rws ans lim es e,
    saturate ds rws ans lim es = inl e <-> check_front ds rws ans es = Some e.
  Proof. Admitted. (* STUB *)

  Lemma add_expr_represents : forall ds e db t, D.wf db -> expr_ok ds db e ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_expr e db))) (Id (fst (add_expr e db))) t.
  Proof. Admitted. (* STUB *)

  Lemma saturate_wf : forall ds rws ans lim es st db cs,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    D.wf db /\ D.canonical db /\ (forall f, kind (D.view db) f = lookup_kind ds f) /\
    view_sorted (lookup_sorts ds) (D.view db) /\
    D.slots db = Egglog.Syntax.slots V.t (E.plan (C.compile ds rws ans)).
  Proof. Admitted. (* STUB *)

  Lemma saturate_represents : forall ds rws ans lim es st db cs n e c t,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    nth_error es n = Some e -> nth_error cs n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view db) (Id c) t.
  Proof. Admitted. (* STUB *)

  Lemma saturate_sound : forall (M : model (V := V.t)) ds rws ans lim es st db cs
      i j e1 e2,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    represents (D.view db) (Id i) e1 -> represents (D.view db) (Id j) e2 ->
    same (D.view db) i j -> denote M e1 = denote M e2.
  Proof. Admitted. (* STUB *)

  Lemma saturate_facts : forall (M : model (V := V.t)) ds rws ans lim es st db cs
      f k o ts,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    row (D.view db) f k o -> Forall2 (represents (D.view db)) k ts ->
    match lookup_kind ds f, o with
    | Some ORel, None => rel M f (map (denote M) ts)
    | Some (OLat _), Some (Val v) => lat M f (map (denote M) ts) v
    | Some OId, Some (Id i) => forall e, represents (D.view db) (Id i) e ->
        inl (con M f (map (denote M) ts)) = denote M e
    | _, _ => False
    end.
  Proof. Admitted. (* STUB *)

  Lemma ematch_complete : forall ds db rw g tau c e, D.wf db -> D.canonical db ->
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) e -> represents (D.view db) (Id c) e ->
    cond_in_db db tau (cond V.t rw) -> exists s,
      matches V.prim (D.view db) (C.flatten_lhs rw) s /\
      C.represents_on g (D.view db) tau s /\
      s (C.root_var rw) = Some (Id (D.repr db c)).
  Proof. Admitted. (* STUB *)

  Lemma saturated_closed : forall ds rws ans lim es db cs rw tau c l r,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In rw rws ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof. Admitted. (* STUB *)

  Lemma saturated_analyses : forall ds rws ans lim es db cs r s,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In r ans ->
    matches V.prim (D.view db) (query V.t r) s ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  Proof. Admitted. (* STUB *)

  Lemma saturate_limits : forall ds rws ans lim es db cs,
    saturate ds rws ans lim es = inr (IdLimit, db, cs) -> (D.ids db > max_ids lim)%N.
  Proof. Admitted. (* STUB *)

  (** Accepted inputs load into a well-formed database of the planned program. *)
  Lemma inputs_loaded : forall ds rws ans es, front_ok ds rws ans es ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    D.wf (inputs_db es (E.load p cp)) /\ E.loaded p cp (inputs_db es (E.load p cp)).
  Proof. Admitted. (* STUB *)
End Saturate.

Module SaturateT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (E : RUN_T V I J D) (C : COMPILE_T V) <: SATURATE_ALL V I J D E C.
  Include Saturate V I J D E C.
  TimeFun check_front.
  TimeFun add_expr.
  TimeFun saturate.
  Definition c_sat : N := 1. (* STUB *)
  Fixpoint T_inputs (es : list (fexpr V.t)) (db : D.t) : N :=
    match es with
    | [] => 1%N
    | e :: rest => (T_add_expr e db + 1 + T_inputs rest (snd (add_expr e db)))%N
    end.
  Lemma T_check_front_le : forall ds rws ans es,
    (T_check_front ds rws ans es <= c_sat * N.of_nat (front_size ds rws ans es + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_add_expr_amort : forall B U ds e db, D.wf db -> expr_ok ds db e ->
    (D.ids (snd (add_expr e db)) <= B)%N -> D.unit (snd (add_expr e db)) <= U ->
    (T_add_expr e db + N.of_nat U * D.potential B (snd (add_expr e db)) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (expr_work e) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_saturate_le : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + c_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          c_sat * T_inputs es (E.load p cp) +
          E.T_run p cp lim (inputs_db es (E.load p cp))
      end)%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition add_node (_ : enode V.t) (_ : list (cell V.t)) (db : D.t) : cell V.t * D.t :=
    (Id 1%positive, db).
  (* STUB-CODE *)
  Definition add_inputs (_ : list (fexpr V.t)) (db : D.t) : list positive * D.t := ([], db).
  TimeFun add_node.
  TimeFun add_inputs.
  Definition k_sat : N := 1. (* STUB *)
  Definition node_args (n : enode V.t) (cs : list (cell V.t)) : list (cell V.t) :=
    match n with
    | EApp _ ch => map (fun j => nth j cs (Id 1%positive)) ch
    | ELit _ => []
    end.
  (** The cells and the database after adding nodes in order. *)
  Fixpoint add_nodes (ns : list (enode V.t)) (cs : list (cell V.t)) (db : D.t)
      : list (cell V.t) * D.t :=
    match ns with
    | [] => (cs, db)
    | n :: rest =>
        add_nodes rest (cs ++ [fst (add_node n (node_args n cs) db)])
          (snd (add_node n (node_args n cs) db))
    end.
  Fixpoint T_add_nodes (ns : list (enode V.t)) (cs : list (cell V.t)) (db : D.t) : N :=
    match ns with
    | [] => 0%N
    | n :: rest =>
        (T_add_node n (node_args n cs) db +
          T_add_nodes rest (cs ++ [fst (add_node n (node_args n cs) db)])
            (snd (add_node n (node_args n cs) db)))%N
    end.
  Lemma F1_add_expr_step : forall ds node cells db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    match node with
    | EApp f _ => lookup_kind ds f = Some OId /\
        lookup_sorts ds f = Some (map cell_sort cells) /\ D.slots_fit db f (S (length cells))
    | ELit _ => cells = []
    end ->
    D.wf (snd (add_node node cells db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_node node cells db))) /\
    kind (D.view (snd (add_node node cells db))) = kind (D.view db) /\
    D.slots (snd (add_node node cells db)) = D.slots db /\
    (forall i, fst (add_node node cells db) = Id i ->
      D.allocated (snd (add_node node cells db)) i) /\
    cell_sort (fst (add_node node cells db)) = enode_sort node.
  Proof. Admitted. (* STUB *)

  Lemma F2_add_expr_wf : forall ds e db, D.wf db -> expr_ok ds db e ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    D.wf (snd (add_expr e db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_expr e db))) /\
    kind (D.view (snd (add_expr e db))) = kind (D.view db) /\
    D.slots (snd (add_expr e db)) = D.slots db /\
    D.allocated (snd (add_expr e db)) (fst (add_expr e db)).
  Proof. Admitted. (* STUB *)

  Lemma F3_represents_den : forall (M : model (V := V.t)) nu db c e,
    D.wf db -> sat V.merge M nu (D.view db) -> represents (D.view db) c e ->
    denote M e = den nu c.
  Proof. Admitted. (* STUB *)

  Lemma F4_inputs_sat : forall (M : model (V := V.t)) ds rws ans es,
    front_ok ds rws ans es ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    let p := C.compile ds rws ans in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p (E.plan p))))).
  Proof. Admitted. (* STUB *)

  Lemma F5_saturate_run : forall ds rws ans lim es out,
    saturate ds rws ans lim es = inr out ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    exists initial, front_ok ds rws ans es /\ E.plans_ok p cp /\ D.wf initial /\
      E.loaded p cp initial /\ add_inputs es (E.load p cp) = (snd out, initial) /\
      E.run p cp lim initial = fst out.
  Proof. Admitted. (* STUB *)

  Lemma F6_closed_represents : forall ds rws ans db rw g tau c l r,
    D.wf db -> D.canonical db -> (forall f, kind (D.view db) f = lookup_kind ds f) ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    closed V.prim V.merge (C.compile ds rws ans) (D.view db) ->
    In rw rws -> rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof. Admitted. (* STUB *)

  Lemma F7_add_inputs : forall es db,
    snd (add_inputs es db) = inputs_db es db /\
    length (fst (add_inputs es db)) = length es /\
    (T_add_inputs es db <= k_sat * T_inputs es db)%N.
  Proof. Admitted. (* STUB *)

  Lemma F8_inputs_represented : forall ds es db n e c t, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    nth_error es n = Some e -> nth_error (fst (add_inputs es db)) n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_inputs es db))) (Id c) t.
  Proof. Admitted. (* STUB *)

  Lemma F9_canonical_view : forall db, D.wf db -> D.canonical db ->
    C.canonical_view (D.view db).
  Proof. Admitted. (* STUB *)

  Lemma T1_saturate_split : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + k_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          T_add_inputs es (E.load p cp) +
          E.T_run p cp lim (snd (add_inputs es (E.load p cp)))
      end)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_k_sat : (k_sat <= c_sat)%N.
  Proof. Admitted. (* STUB *)

  (** Adding inputs pays for their nodes at the final unit and identifier budget. *)
  Lemma T_inputs_le : forall B U ds rws ans es, front_ok ds rws ans es ->
    let p := C.compile ds rws ans in
    let db0 := E.load p (E.plan p) in
    (D.ids (inputs_db es db0) <= B)%N -> D.unit (inputs_db es db0) <= U ->
    (T_inputs es db0 + N.of_nat U * D.potential B (inputs_db es db0) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db0 + 1) *
        N.of_nat (fold_right (fun e n => (expr_work e + 1 + n)%nat) 1%nat es))%N.
  Proof. Admitted. (* STUB *)
  (** Adding a flat expression folds over its nodes in order and returns its root cell. *)
  Lemma F10_add_expr_nodes : forall ds e db,
    expr_sorted (lookup_sorts ds) (lookup_kind ds) e ->
    snd (add_expr e db) = snd (add_nodes (expr_nodes V.t e) [] db) /\
    nth_error (fst (add_nodes (expr_nodes V.t e) [] db)) (expr_root V.t e) =
      Some (Id (fst (add_expr e db))).
  Proof. Admitted. (* STUB *)
  (** Adding an expression separates node insertion cost from child-index work. *)
  Lemma T3_add_expr_split : forall e db,
    (T_add_expr e db <= T_add_nodes (expr_nodes V.t e) [] db +
      k_sat * N.of_nat (expr_work e))%N.
  Proof. Admitted. (* STUB *)
  (** Adding a node pays its insertion cost and transfers the database potential. *)
  Lemma T4_add_node_amort : forall B U node cells db, D.wf db ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    match node with
    | EApp f _ => kind (D.view db) f = Some OId /\ D.slots_fit db f (S (length cells))
    | ELit _ => cells = []
    end ->
    (D.ids (snd (add_node node cells db)) <= B)%N ->
    D.unit (snd (add_node node cells db)) <= U ->
    (T_add_node node cells db + N.of_nat U * D.potential B (snd (add_node node cells db)) <=
      k_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat ((length cells + 2) * (length cells + 2)) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)
End SaturateT.
