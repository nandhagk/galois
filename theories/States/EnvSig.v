(** * Non-relational environments

    Environments map variables to abstract values and track unreachable states separately.
    For example, an absent binding denotes the value domain's top.
    Builds on: MapSig, StateSig and ValueSig. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.

Inductive reach (A : Type) :=
  | Unreached
  | Reached (a : A).

Arguments Unreached {A}.
Arguments Reached {A} a.

Inductive ann (K X A : Type) :=
  | ALeaf (x : X) (a : A)
  | ANode (k : K) (a : A) (kids : list (ann K X A)).

Arguments ALeaf {K X A} x a.
Arguments ANode {K X A} k a kids.

Module Type ENV_OPS (X : KEY_OPS) (M : MAP_OPS X) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L).
  Include STATE_DOMAIN_OPS X L V
    with Definition t := reach (M.t V.t)
    with Definition wparam := V.wparam.
  Parameter read : M.t V.t -> X.t -> V.t.
  Parameter annotate : M.t V.t -> term L.op X.t -> ann L.op X.t V.t.
  Parameter root : ann L.op X.t V.t -> V.t.
  Parameter refine : V.t -> ann L.op X.t V.t -> M.t V.t -> M.t V.t.
  Parameter join_map : M.t V.t -> M.t V.t -> M.t V.t.
End ENV_OPS.

Module Type ENV_SPEC (X : KEY_OPS) (M : MAP_OPS X) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (Import E : ENV_OPS X M L V).
  Definition roots (s : t) (es : list (term L.op X.t)) : list V.t := map (fun e => eval e s) es.
End ENV_SPEC.

Module Type ENV_BASE (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L) :=
  ENV_OPS X M L V <+ ENV_SPEC X M L V <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type ENV_LAWS (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L)
    (Import E : ENV_BASE X M L V).
  (** Reading an absent key returns top. *)
  Parameter read_spec : forall m x,
    read m x = match M.get x m with Some a => a | None => V.top end.
  (** Unreachable states describe no stores. *)
  Parameter gamma_unreached : forall st, ~ gamma Unreached st.
  (** Reached maps describe stores pointwise. *)
  Parameter gamma_reached : forall m st,
    gamma (Reached m) st <-> forall x, V.gamma (read m x) (st x).
End ENV_LAWS.

Module Type ENV (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L) :=
  ENV_BASE X M L V <+ ENV_LAWS X M L V.

Module Type ENV_TIME (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import E : ENV X M L V).
  Include STATE_DOMAIN_TIME X L V E.
  (* spec: tcost tcost_s *)
  Parameter tcost : M.t V.t -> term L.op X.t -> nat.
  Parameter tcost_s : t -> term L.op X.t -> nat.
  Definition esize (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0
      (map (fun kv => X.bits (fst kv) + V.size (snd kv) + 1) (M.elements m))
    end.
  Parameter T_read : M.t V.t -> X.t -> nat.
  Parameter T_annotate : M.t V.t -> term L.op X.t -> nat.
  Parameter T_root : ann L.op X.t V.t -> nat.
  Parameter T_refine : V.t -> ann L.op X.t V.t -> M.t V.t -> nat.
  Parameter T_join_map : M.t V.t -> M.t V.t -> nat.
  Parameter c_env : nat.
  (** Annotation charges each visited transfer and leaf lookup. *)
  Parameter T_annotate_le : forall m e, T_annotate m e <= c_env * tcost m e.
  (** Assumption charges both passes and guard work. *)
  Parameter T_assume_env_le : forall g es s, T_assume g es s <= c_env *
    (fold_right Nat.add 0 (map (tcost_s s) es) + V.gwork g (roots s es) + 1).
  (** Join charges the weighted sizes of both environments. *)
  Parameter T_join_env_le : forall a b, T_join a b <= c_env * (esize a + esize b + 1).
End ENV_TIME.

Module Type ENV_T (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  ENV X M L V <+ ENV_TIME X M L V.

Module Type ENV_PLAN (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import E : ENV_T X M L V).
  Definition models m st := forall x, V.gamma (read m x) (st x).
  (* spec: ann_models *)
  Parameter ann_models : (X.t -> L.val) -> ann L.op X.t V.t -> term L.op X.t -> Prop.
  (** Annotation records values covering each concrete subterm. *)
  Parameter annotate_sound : forall m st e c,
    models m st -> eval_term L.eval st e = Some c ->
    ann_models st (annotate m e) e /\ V.gamma (root (annotate m e)) c.
  (** Refinement retains a concrete execution compatible with the requested value. *)
  Parameter refine_sound : forall m st e n q c,
    models m st -> ann_models st n e -> eval_term L.eval st e = Some c ->
    V.gamma q c -> models (refine q n m) st.
  (** Refinement descends pointwise. *)
  Parameter refine_lower : forall q n m x, V.leb (read (refine q n m) x) (read m x) = true.
  (** Map join covers either input model. *)
  Parameter join_models : forall a b st,
    models a st \/ models b st -> models (join_map a b) st.
  (** Environment rank sums component ranks over stored bindings. *)
  Parameter wrank_env : forall p m, wrank p (Reached m) =
    fold_right Nat.add 0 (map (fun kv => V.wrank p (snd kv)) (M.elements m)).
  (** Annotation work counts one leaf lookup. *)
  Parameter tcost_leaf : forall m x, tcost m (Leaf x) = X.bits x + 1.
  (** Annotation work counts every child and the current transfer. *)
  Parameter tcost_node : forall m o es, tcost m (Node o es) =
    fold_right Nat.add 0 (map (tcost m) es) +
    V.work o (map (fun e => root (annotate m e)) es) + 1.
End ENV_PLAN.

Module Type ENV_ALL (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  ENV_T X M L V <+ ENV_PLAN X M L V.
