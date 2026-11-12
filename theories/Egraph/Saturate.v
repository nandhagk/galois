(** * Placeholder equality saturation

    These operations provide the front end for adding expressions and running rewrites.
    For example, the placeholder returns an iteration limit on an empty database.
    Builds on: SaturateSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig Syntax Model.
From Galois.Egraph Require Import Syntax CompileSig SaturateSig.

Import List.ListNotations.

Module SaturateCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (E : RUN_OPS V I J D) (C : COMPILE_OPS V)
    <: SATURATE_OPS V I J D E C.
  (* STUB-CODE *)
  Definition add_expr (_ : fexpr V.t) (db : D.t) : positive * D.t := (1%positive, db).
  (* STUB-CODE *)
  Definition saturate (_ : list (rewrite V.t)) (_ : limits) (_ : list (fexpr V.t))
      : stop * D.t * list positive := (IterLimit, D.init [] [], []).
End SaturateCode.

Module Saturate (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) <: SATURATE V I J D E C.
  Include SaturateCode V I J D E C.
  Include SATURATE_SPEC V I J D E C.
  Definition declarations (_ : list (rewrite V.t)) (_ : list (fexpr V.t))
      : list (positive * decl) := [].
  Lemma add_expr_represents : forall e db t, D.wf db ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_expr e db))) (Id (fst (add_expr e db))) t.
  Proof. Admitted.
  Lemma saturate_sound : forall (M : model (V := V.t)) rws lim es st db cs i j e1 e2,
    Forall (valid_rw V.prim V.merge M (lookup_kind (map snd (declarations rws es)))) rws ->
    saturate rws lim es = (st, db, cs) ->
    represents (D.view db) (Id i) e1 -> represents (D.view db) (Id j) e2 ->
    same (D.view db) i j -> denote M e1 = denote M e2.
  Proof. Admitted.
  Lemma ematch_complete : forall db rw tau c e, D.wf db -> D.canonical db ->
    C.instantiates tau (lhs V.t rw) e -> represents (D.view db) (Id c) e ->
    cond_in_db db tau (cond V.t rw) -> exists s,
      matches V.prim (D.view db) (C.flatten_lhs rw) s /\
      s (C.root_var rw) = Some (Id (D.repr db c)).
  Proof. Admitted.
  Lemma saturated_closed : forall rws lim es db cs rw tau c l r,
    saturate rws lim es = (Saturated, db, cs) -> In rw rws ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof. Admitted.
End Saturate.

Module SaturateT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (E : RUN_T V I J D) (C : COMPILE_T V) <: SATURATE_ALL V I J D E C.
  Include Saturate V I J D E C.
  TimeFun add_expr.
  TimeFun saturate.
  (* STUB-CODE *)
  Definition add_node (_ : enode V.t) (_ : list positive) (db : D.t) : positive * D.t :=
    (1%positive, db).
  (* STUB-CODE *)
  Definition add_inputs (_ : list (fexpr V.t)) (db : D.t) : list positive * D.t := ([], db).
  TimeFun add_node.
  TimeFun add_inputs.
  Lemma F1_add_expr_step : forall node classes db, D.wf db ->
    D.wf (snd (add_node node classes db)).
  Proof. Admitted. (* STUB *)
  Lemma F2_add_expr_wf : forall e db, D.wf db -> D.wf (snd (add_expr e db)).
  Proof. Admitted. (* STUB *)
  Lemma F3_represents_den : forall (M : model (V := V.t)) nu db c e,
    D.wf db -> sat V.merge M nu (D.view db) -> represents (D.view db) c e ->
    denote M e = den nu c.
  Proof. Admitted. (* STUB *)
  Lemma F4_inputs_sat : forall (M : model (V := V.t)) rws es,
    let p := C.compile (declarations rws es) rws in
    let cp := E.plan p in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p cp)))).
  Proof. Admitted. (* STUB *)
  Lemma F5_saturate_run : forall rws lim es st db cs,
    saturate rws lim es = (st, db, cs) ->
    let p := C.compile (declarations rws es) rws in
    exists cp initial, E.plans_ok p cp /\ D.wf initial /\
      add_inputs es (E.load p cp) = (cs, initial) /\ E.run p cp lim initial = (st, db).
  Proof. Admitted. (* STUB *)
  Lemma F6_closed_represents : forall rws es db rw tau c l r,
    D.wf db -> D.canonical db ->
    closed V.prim V.merge (C.compile (declarations rws es) rws) (D.view db) ->
    In rw rws -> C.instantiates tau (lhs V.t rw) l ->
    C.instantiates tau (rhs V.t rw) r -> represents (D.view db) (Id c) l ->
    cond_in_db db tau (cond V.t rw) -> represents (D.view db) (Id c) r.
  Proof. Admitted. (* STUB *)

End SaturateT.
