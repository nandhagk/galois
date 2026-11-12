(** * Equality saturation over the relational engine

    The front end adds flat expressions and runs compiled rewrite rules.
    For example, a saturated application of a rewrite represents its right side in the same class.
    Builds on: CompileSig and the Egglog run and database signatures. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.

From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig Syntax Model.
From Galois.Egraph Require Import Syntax CompileSig.

Import List.ListNotations.

Module Type SATURATE_OPS (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (E : RUN_OPS V I J D) (C : COMPILE_OPS V).
  Parameter add_expr : fexpr V.t -> D.t -> cell V.t * D.t.
  Parameter saturate : list (rewrite V.t) -> limits -> list (fexpr V.t) ->
    stop * D.t * list (cell V.t).
End SATURATE_OPS.

Module Type SATURATE_SPEC (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V)
    (Import S : SATURATE_OPS V I J D E C).
  (** Every node of the input is a declared constructor whose slots fit its tuple. *)
  Definition expr_ok (db : D.t) (e : fexpr V.t) : Prop :=
    Forall (fun n => match n with
      | EApp f args => kind (D.view db) f = Some OId /\ D.slots_fit db f (S (length args))
      | ELit _ => True
      end) (expr_nodes V.t e).

  Definition cond_in_db (db : D.t) := C.cond_in_view (D.view db).
End SATURATE_SPEC.

Module Type SATURATE_LAWS (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V)
    (Import S : SATURATE_OPS V I J D E C)
    (Import SS : SATURATE_SPEC V I J D E C S).
  (* spec: declarations *)
  Parameter declarations : list (rewrite V.t) -> list (fexpr V.t) -> list (positive * decl).
  (** The front end declares constructors only. *)
  Parameter declarations_kind : forall rws es f o,
    lookup_kind (map snd (declarations rws es)) f = Some o -> o = OId.
  (** Every input node is declared. *)
  Parameter declarations_inputs : forall rws es e f args, In e es ->
    In (EApp f args) (expr_nodes V.t e) ->
    lookup_kind (map snd (declarations rws es)) f = Some OId.
  (** Every pattern node is declared. *)
  Parameter declarations_rewrites : forall rws es rw f args, In rw rws ->
    In (PApp f args) (nodes V.t (lhs V.t rw) ++ nodes V.t (rhs V.t rw)) ->
    lookup_kind (map snd (declarations rws es)) f = Some OId.

  (** Every unfolding of an added expression is represented by its returned class. *)
  Parameter add_expr_represents : forall e db t, D.wf db -> expr_ok db e ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_expr e db))) (fst (add_expr e db)) t.
  (** Class equalities after valid rewrites imply equal denotations in every algebra. *)
  Parameter saturate_sound : forall (M : model (V := V.t)) rws lim es st db cs i j e1 e2,
    Forall (valid_rw V.prim V.merge M (lookup_kind (map snd (declarations rws es)))) rws ->
    saturate rws lim es = (st, db, cs) ->
    represents (D.view db) (Id i) e1 -> represents (D.view db) (Id j) e2 ->
    same (D.view db) i j -> denote M e1 = denote M e2.
  (** Canonical databases expose every represented left-pattern match to the engine. *)
  Parameter ematch_complete : forall db rw tau c e, D.wf db -> D.canonical db ->
    C.instantiates tau (lhs V.t rw) e -> represents (D.view db) (Id c) e ->
    cond_in_db db tau (cond V.t rw) -> exists s,
      matches V.prim (D.view db) (C.flatten_lhs rw) s /\
      s (C.root_var rw) = Some (Id (D.repr db c)).
  (** A saturated result represents each applicable rewrite's instantiated right side. *)
  Parameter saturated_closed : forall rws lim es db cs rw tau c l r,
    saturate rws lim es = (Saturated, db, cs) -> In rw rws -> app_rooted (lhs V.t rw) ->
    (forall v, r <> Model.ELit v) ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
End SATURATE_LAWS.

Module Type SATURATE (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (E : RUN V I J D) (C : COMPILE V) :=
  SATURATE_OPS V I J D E C <+ SATURATE_SPEC V I J D E C <+ SATURATE_LAWS V I J D E C.

Module Type SATURATE_TIME (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V)
    (Import S : SATURATE V I J D E C).
  Parameter c_sat : N.
  Parameter T_add_expr : fexpr V.t -> D.t -> N.
  Parameter T_saturate : list (rewrite V.t) -> limits -> list (fexpr V.t) -> N.
  Parameter T_add_expr_amort : forall B U e db, D.wf db -> expr_ok db e ->
    (D.ids (snd (add_expr e db)) <= B)%N -> D.unit (snd (add_expr e db)) <= U ->
    (T_add_expr e db + N.of_nat U * D.potential B (snd (add_expr e db)) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (fold_right (fun n acc => match n with
          | EApp _ args => ((length args + 2) * (length args + 2) * (D.num_slots db + 1) + acc)%nat
          | ELit _ => (1 + acc)%nat
          end) 1%nat (expr_nodes V.t e)) +
      N.of_nat U * D.potential B db)%N.

End SATURATE_TIME.

Module Type SATURATE_T (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V) :=
  SATURATE V I J D E C <+ SATURATE_TIME V I J D E C.

Module Type SATURATE_PLAN (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V)
    (Import S : SATURATE_T V I J D E C).
  Parameter add_node : enode V.t -> list (cell V.t) -> D.t -> cell V.t * D.t.
  Parameter add_inputs : list (fexpr V.t) -> D.t -> list (cell V.t) * D.t.
  Parameter T_add_node : enode V.t -> list (cell V.t) -> D.t -> N.
  Parameter T_add_inputs : list (fexpr V.t) -> D.t -> N.
  Parameter k_sat : N.
  (** Adding a node keeps the maintained database invariant. *)
  Parameter F1_add_expr_step : forall node classes db, D.wf db ->
    (match node with
     | EApp f _ => kind (D.view db) f = Some OId /\ D.slots_fit db f (S (length classes))
     | ELit _ => True
     end) ->
    (forall i, In (Id i) classes -> D.allocated db i) ->
    D.wf (snd (add_node node classes db)).
  (** Adding an expression keeps the maintained database invariant. *)
  Parameter F2_add_expr_wf : forall e db, D.wf db -> expr_ok db e -> D.wf (snd (add_expr e db)).
  (** Represented cells denote their identifier interpretation or literal value. *)
  Parameter F3_represents_den : forall (M : model (V := V.t)) nu db c e,
    D.wf db -> sat V.merge M nu (D.view db) -> represents (D.view db) c e ->
    denote M e = den nu c.
  (** Adding input expressions produces a database satisfying every algebra. *)
  Parameter F4_inputs_sat : forall (M : model (V := V.t)) rws es,
    let p := C.compile (declarations rws es) rws in
    let cp := E.plan p in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p cp)))).
  (** The front end checks its compiled plan before running the engine. *)
  Parameter F5_saturate_run : forall rws lim es st db cs,
    saturate rws lim es = (st, db, cs) ->
    let p := C.compile (declarations rws es) rws in
    exists cp initial, E.plans_ok p cp /\ D.wf initial /\ E.loaded p cp initial /\
      add_inputs es (E.load p cp) = (cs, initial) /\ E.run p cp lim initial = (st, db).
  (** Closure of compiled rules transports a represented left side to the same right class. *)
  Parameter F6_closed_represents : forall rws es db rw tau c l r,
    D.wf db -> D.canonical db ->
    closed V.prim V.merge (C.compile (declarations rws es) rws) (D.view db) ->
    In rw rws -> app_rooted (lhs V.t rw) -> (forall v, r <> Model.ELit v) ->
    C.instantiates tau (lhs V.t rw) l ->
    C.instantiates tau (rhs V.t rw) r -> represents (D.view db) (Id c) l ->
    cond_in_db db tau (cond V.t rw) -> represents (D.view db) (Id c) r.

  Parameter T_saturate_split : forall rws lim es,
    let p := C.compile (declarations rws es) rws in
    let cp := E.plan p in
    (T_saturate rws lim es <= C.T_compile (declarations rws es) rws + E.T_plan p +
      E.T_check_plan p cp + E.T_load p cp + T_add_inputs es (E.load p cp) +
      E.T_run p cp lim (snd (add_inputs es (E.load p cp))) + k_sat)%N.

  (* EgraphCoreRebuildSemantic.v at 87192fe fixes the semantic invariant.
     semantic_inv (initial h : Egraph.t K Sort V) : Prop :=
       EggRepresentation.structural_wf a h /\
       EggRepresentation.extends a initial h /\
       forall (H F C : Type) (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
         (rules : list (EggRule.t K Sort V H F)),
         EggRepresentation.sound a adm facts rules initial ->
         EggRepresentation.sound a adm facts rules h.
     rebuild_preserves g :
       EggRepresentation.wf a g -> EggRepresentation.extends a g (Egraph.rebuild a g).
     rebuild_sound {H F C} (adm : EggSem.t K V C -> Prop)
       (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)) g :
       EggRepresentation.wf a g -> EggRepresentation.sound a adm facts rules g ->
       EggRepresentation.sound a adm facts rules (Egraph.rebuild a g). *)
End SATURATE_PLAN.

Module Type SATURATE_ALL (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I)
    (D : DATABASE_T V I) (E : RUN_T V I J D) (C : COMPILE_T V) :=
  SATURATE_T V I J D E C <+ SATURATE_PLAN V I J D E C.
