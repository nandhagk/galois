(** * Equality saturation over the relational engine

    The front end adds flat expressions and runs compiled rewrite rules.
    For example, a saturated application of a rewrite represents its right side in the same class.
    Builds on: CompileSig and the Egglog run and database signatures. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig Syntax Model.
From Galois.Egglog Require Import Sorts.
From Galois.Egraph Require Import Syntax CompileSig.
Import List.ListNotations.

Module Type SATURATE_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (E : RUN_OPS V I J D) (C : COMPILE_OPS V).
  Parameter check_front : list decl -> list (rewrite V.t) -> list (rule V.t) ->
    list (fexpr V.t) -> option reject.
  Parameter add_expr : fexpr V.t -> D.t -> positive * D.t.
  Parameter saturate : list decl -> list (rewrite V.t) -> list (rule V.t) -> limits ->
    list (fexpr V.t) -> reject + (stop * D.t * list positive).
End SATURATE_OPS.

Module Type SATURATE_SPEC (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V)
    (Import S : SATURATE_OPS V I J D E C).
  Definition cond_in_db (db : D.t) := C.cond_in_view (D.view db).
  (** An input is well sorted for declarations that the database carries, and the slots of
      its constructors fit. *)
  Definition expr_ok (ds : list decl) (db : D.t) (e : fexpr V.t) : Prop :=
    expr_sorted (lookup_sorts ds) (lookup_kind ds) e /\
    (forall f, kind (D.view db) f = lookup_kind ds f) /\
    Forall (fun n => match n with
      | EApp f args => D.slots_fit db f (S (length args))
      | ELit _ => True
      end) (expr_nodes V.t e).
  (** A model validates the rewrites and the analysis rules, and its lattice functions are
      closed under their declared merges. *)
  Definition model_ok (M : model (V := V.t)) (ds : list decl) (rws : list (rewrite V.t))
      (ans : list (rule V.t)) : Prop :=
    Forall (valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds)) rws /\
    Forall (rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds)) ans /\
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)).
  (** The database after adding a list of inputs in order. *)
  Fixpoint inputs_db (es : list (fexpr V.t)) (db : D.t) : D.t :=
    match es with
    | [] => db
    | e :: rest => inputs_db rest (snd (add_expr e db))
    end.
End SATURATE_SPEC.

Module Type SATURATE_LAWS (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V)
    (Import S : SATURATE_OPS V I J D E C)
    (Import SS : SATURATE_SPEC V I J D E C S).
  (** The front-end check accepts exactly the well-sorted rules and inputs. *)
  Parameter check_front_spec : forall ds rws ans es,
    check_front ds rws ans es = None <-> front_ok ds rws ans es.
  (** A reported item fails its check. *)
  Parameter check_front_report : forall ds rws ans es e,
    check_front ds rws ans es = Some e -> rejected ds rws ans es e.
  (** Saturation rejects precisely what the check reports. *)
  Parameter saturate_rejects : forall ds rws ans lim es e,
    saturate ds rws ans lim es = inl e <-> check_front ds rws ans es = Some e.
  (** Every unfolding of a well-sorted input is represented by its returned class. *)
  Parameter add_expr_represents : forall ds e db t, D.wf db -> expr_ok ds db e ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_expr e db))) (Id (fst (add_expr e db))) t.
  (** A result is well formed, canonical and well sorted, and carries the declarations and
      the planned layout. *)
  Parameter saturate_wf : forall ds rws ans lim es st db cs,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    D.wf db /\ D.canonical db /\ (forall f, kind (D.view db) f = lookup_kind ds f) /\
    view_sorted (lookup_sorts ds) (D.view db) /\
    D.slots db = Egglog.Syntax.slots V.t (E.plan (C.compile ds rws ans)).
  (** The class returned for an input represents every unfolding of the input in the
      result. *)
  Parameter saturate_represents : forall ds rws ans lim es st db cs n e c t,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    nth_error es n = Some e -> nth_error cs n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view db) (Id c) t.
  (** Class equalities imply equal denotations in every model of the rules, at every
      outcome. *)
  Parameter saturate_sound : forall (M : model (V := V.t)) ds rws ans lim es st db cs
      i j e1 e2,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    represents (D.view db) (Id i) e1 -> represents (D.view db) (Id j) e2 ->
    same (D.view db) i j -> denote M e1 = denote M e2.
  (** Every row over represented terms holds of their denotations in every model of the
      rules, at every outcome. *)
  Parameter saturate_facts : forall (M : model (V := V.t)) ds rws ans lim es st db cs
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
  (** A canonical database exposes every represented left side whose condition holds. *)
  Parameter ematch_complete : forall ds db rw g tau c e, D.wf db -> D.canonical db ->
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) e -> represents (D.view db) (Id c) e ->
    cond_in_db db tau (cond V.t rw) -> exists s,
      matches V.prim (D.view db) (C.flatten_lhs rw) s /\
      C.represents_on g (D.view db) tau s /\
      s (C.root_var rw) = Some (Id (D.repr db c)).
  (** A saturated result represents each applicable rewrite's right side in the class of
      its left side. *)
  Parameter saturated_closed : forall ds rws ans lim es db cs rw tau c l r,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In rw rws ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  (** A saturated result already holds the facts of every analysis rule that matches it. *)
  Parameter saturated_analyses : forall ds rws ans lim es db cs r s,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In r ans ->
    matches V.prim (D.view db) (query V.t r) s ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  (** An identifier stop reports allocation above the caller's limit. *)
  Parameter saturate_limits : forall ds rws ans lim es db cs,
    saturate ds rws ans lim es = inr (IdLimit, db, cs) -> (D.ids db > max_ids lim)%N.
End SATURATE_LAWS.

Module Type SATURATE (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V) :=
  SATURATE_OPS V I J D E C <+ SATURATE_SPEC V I J D E C <+ SATURATE_LAWS V I J D E C.

Module Type SATURATE_TIME (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V)
    (Import S : SATURATE V I J D E C).
  Parameter T_check_front : list decl -> list (rewrite V.t) -> list (rule V.t) ->
    list (fexpr V.t) -> N.
  Parameter T_add_expr : fexpr V.t -> D.t -> N.
  Parameter T_saturate : list decl -> list (rewrite V.t) -> list (rule V.t) -> limits ->
    list (fexpr V.t) -> N.
  Parameter c_sat : N.
  (** The cost of adding a list of inputs in order, with one step per input. *)
  Fixpoint T_inputs (es : list (fexpr V.t)) (db : D.t) : N :=
    match es with
    | [] => 1%N
    | e :: rest => (T_add_expr e db + 1 + T_inputs rest (snd (add_expr e db)))%N
    end.
  (** Checking reads each declaration, rewrite, analysis rule and input once. *)
  Parameter T_check_front_le : forall ds rws ans es,
    (T_check_front ds rws ans es <= c_sat * N.of_nat (front_size ds rws ans es + 1))%N.
  (** Adding an input pays for each node and child index at the result's unit and
      identifier budget, and transfers scaled credit. *)
  Parameter T_add_expr_amort : forall B U ds e db, D.wf db -> expr_ok ds db e ->
    (D.ids (snd (add_expr e db)) <= B)%N -> D.unit (snd (add_expr e db)) <= U ->
    (T_add_expr e db + N.of_nat U * D.potential B (snd (add_expr e db)) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (expr_work e) +
      N.of_nat U * D.potential B db)%N.
  (** Saturation pays for its check and, on accepted input, for compilation, planning,
      loading, the inputs and the run. *)
  Parameter T_saturate_le : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + c_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          c_sat * T_inputs es (E.load p cp) +
          E.T_run p cp lim (inputs_db es (E.load p cp))
      end)%N.
End SATURATE_TIME.

Module Type SATURATE_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V) :=
  SATURATE V I J D E C <+ SATURATE_TIME V I J D E C.

Module Type SATURATE_PLAN (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V)
    (Import S : SATURATE_T V I J D E C).
  Parameter add_node : enode V.t -> list (cell V.t) -> D.t -> cell V.t * D.t.
  Parameter add_inputs : list (fexpr V.t) -> D.t -> list positive * D.t.
  Parameter T_add_node : enode V.t -> list (cell V.t) -> D.t -> N.
  Parameter T_add_inputs : list (fexpr V.t) -> D.t -> N.
  Parameter k_sat : N.
  (** Adding a node of declared sorts keeps the invariant, the sorts of rows and the layout,
      and returns an allocated cell of the node's sort. *)
  Parameter F1_add_expr_step : forall ds node cells db, D.wf db ->
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
  (** Adding a well-sorted input keeps the invariant, the sorts of rows and the layout. *)
  Parameter F2_add_expr_wf : forall ds e db, D.wf db -> expr_ok ds db e ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    D.wf (snd (add_expr e db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_expr e db))) /\
    kind (D.view (snd (add_expr e db))) = kind (D.view db) /\
    D.slots (snd (add_expr e db)) = D.slots db /\
    D.allocated (snd (add_expr e db)) (fst (add_expr e db)).
  (** Represented cells denote their identifier interpretation or literal value. *)
  Parameter F3_represents_den : forall (M : model (V := V.t)) nu db c e,
    D.wf db -> sat V.merge M nu (D.view db) -> represents (D.view db) c e ->
    denote M e = den nu c.
  (** Accepted inputs give a database that a valuation satisfies in every model whose
      lattice functions are closed under their merges. *)
  Parameter F4_inputs_sat : forall (M : model (V := V.t)) ds rws ans es,
    front_ok ds rws ans es ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    let p := C.compile ds rws ans in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p (E.plan p))))).
  (** An accepted call runs the engine with the planned program on the loaded inputs. *)
  Parameter F5_saturate_run : forall ds rws ans lim es out,
    saturate ds rws ans lim es = inr out ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    exists initial, front_ok ds rws ans es /\ E.plans_ok p cp /\ D.wf initial /\
      E.loaded p cp initial /\ add_inputs es (E.load p cp) = (snd out, initial) /\
      E.run p cp lim initial = fst out.
  (** Closure under the compiled rules transports a represented left side to the right
      side in the same class. *)
  Parameter F6_closed_represents : forall ds rws ans db rw g tau c l r,
    D.wf db -> D.canonical db -> (forall f, kind (D.view db) f = lookup_kind ds f) ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    closed V.prim V.merge (C.compile ds rws ans) (D.view db) ->
    In rw rws -> rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  (** Adding a list of inputs is the ordered fold of [add_expr] and pays its cost. *)
  Parameter F7_add_inputs : forall es db,
    snd (add_inputs es db) = inputs_db es db /\
    length (fst (add_inputs es db)) = length es /\
    (T_add_inputs es db <= k_sat * T_inputs es db)%N.
  (** The class returned for each input represents it after all inputs are added. *)
  Parameter F8_inputs_represented : forall ds es db n e c t, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    nth_error es n = Some e -> nth_error (fst (add_inputs es db)) n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_inputs es db))) (Id c) t.
  (** The engine's view of a well-formed canonical database is canonical. *)
  Parameter F9_canonical_view : forall db, D.wf db -> D.canonical db ->
    C.canonical_view (D.view db).
  (** Saturation pays for the check and, on accepted input, for each later phase. *)
  Parameter T1_saturate_split : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + k_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          T_add_inputs es (E.load p cp) +
          E.T_run p cp lim (snd (add_inputs es (E.load p cp)))
      end)%N.
  (** The plan constant fits under the public constant. *)
  Parameter T2_k_sat : (k_sat <= c_sat)%N.
End SATURATE_PLAN.

Module Type SATURATE_ALL (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V) :=
  SATURATE_T V I J D E C <+ SATURATE_PLAN V I J D E C.
