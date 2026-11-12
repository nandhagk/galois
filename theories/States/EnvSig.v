(** * Non-relational environments

    Environments map variables to abstract values and track unreachable states separately.
    For example, an absent binding denotes the value domain's top.
    Builds on: MapSig, StateSig and ValueSig. *)

From Stdlib Require Import List NArith.
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
  (** Leaf roots expose their stored abstract value. *)
  Parameter root_leaf : forall x a, root (ALeaf x a) = a.
  (** Node roots expose their stored abstract value. *)
  Parameter root_node : forall o a ns, root (ANode o a ns) = a.
  (** Leaf annotation reads the current environment. *)
  Parameter annotate_leaf : forall m x, annotate m (Leaf x) = ALeaf x (read m x).
  (** Node annotation transfers the annotated child roots. *)
  Parameter annotate_node : forall m o es, annotate m (Node o es) =
    ANode o (V.forward o (map (fun e => root (annotate m e)) es)) (map (annotate m) es).
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
  (* spec: tcost *)
  Parameter tcost : M.t V.t -> term L.op X.t -> nat.
  Definition tcost_s (s : t) (e : term L.op X.t) : nat :=
    match s with Unreached => 0 | Reached m => tcost m e end.
  Definition esize (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0
      (map (fun kv => X.bits (fst kv) + V.size (snd kv) + 1) (M.elements m))
    end.
  Definition env_wf (s : t) : Prop :=
    match s with Unreached => True | Reached m => M.wf m end.
  Parameter rsize : t -> L.guard -> list (term L.op X.t) -> nat.
  Parameter T_read : M.t V.t -> X.t -> N.
  Parameter T_annotate : M.t V.t -> term L.op X.t -> N.
  Parameter T_root : ann L.op X.t V.t -> N.
  Parameter T_refine : V.t -> ann L.op X.t V.t -> M.t V.t -> N.
  Parameter T_join_map : M.t V.t -> M.t V.t -> N.
  Parameter c_env : N.
  (** Annotation charges each visited transfer and leaf lookup. *)
  Parameter T_annotate_le : forall m e, (T_annotate m e <= c_env * N.of_nat ((tcost m e)%nat))%N.
  (** Assumption charges both passes and guard work. *)
  Parameter T_assume_env_le : forall g es s, (T_assume g es s <= c_env *
    N.of_nat ((fold_right Nat.add 0 (map (tcost_s s) es) + V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1)%nat))%N.
  (** Join charges the weighted sizes of both environments. *)
  Parameter T_join_env_le : forall a b, env_wf a -> env_wf b ->
    (T_join a b <= c_env * N.of_nat ((esize a + esize b + 1)%nat))%N.
End ENV_TIME.

Module Type ENV_T (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  ENV X M L V <+ ENV_TIME X M L V.

Module Type ENV_PLAN (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import E : ENV_T X M L V).
  Fixpoint refine_size (q : V.t) (n : ann L.op X.t V.t) (m : M.t V.t) : nat :=
    match n with
    | ALeaf x _ => Nat.max (V.size q) (V.size (read m x))
    | ANode o _ ns =>
      let qs := V.backward o q (map root ns) in
      Nat.max (V.size q)
        ((fix children ns qs m :=
          match ns, qs with
          | n :: ns, q :: qs =>
            Nat.max (refine_size q n m) (children ns qs (refine q n m))
          | _, _ => 0
          end) ns qs m)
    end.
  Definition assume_size (s : t) (g : L.guard) (es : list (term L.op X.t)) : nat :=
    match s with
    | Unreached => 0
    | Reached m =>
      let ns := map (annotate m) es in
      let qs := V.guard g (map root ns) in
      fst (fold_left (fun acc nq =>
        (Nat.max (fst acc) (refine_size (snd nq) (fst nq) (snd acc)),
          refine (snd nq) (fst nq) (snd acc))) (combine ns qs) (0, m))
    end.
  (** Request size records the largest request or stored value met by refinement. *)
  Parameter F_rsize : forall s g es, rsize s g es = assume_size s g es.
  (** Assumption checks bottoms at written leaves and charges cached two-pass refinement. *)
  Parameter T1_assume : forall g es m,
    (T_assume g es (Reached m) <= c_env * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost m) es) +
        V.gwork g (roots (Reached m) es) +
        fold_right Nat.add 0%nat (map tsize es) * (rsize (Reached m) g es + 1) + 1))%N.
  Definition models m st := forall x, V.gamma (read m x) (st x).
  Fixpoint ann_models (st : X.t -> L.val) (n : ann L.op X.t V.t)
      (e : term L.op X.t) {struct n} : Prop :=
    (forall c, eval_term L.eval st e = Some c -> V.gamma (root n) c) /\
    match n, e with
    | ALeaf x _, Leaf y => x = y
    | ANode o _ ns, Node p es => o = p /\
      (fix children (ns : list (ann L.op X.t V.t)) (es : list (term L.op X.t)) :=
        match ns, es with
        | nil, nil => True
        | n :: ns, e :: es => ann_models st n e /\ children ns es
        | _, _ => False
        end) ns es
    | _, _ => False
    end.
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
  Parameter wrank_env : forall p m, M.wf m -> wrank p (Reached m) =
    fold_right Nat.add 0 (map (fun kv => V.wrank p (snd kv)) (M.elements m)).
  (** Reached bottom detection scans stored values. *)
  Parameter F_is_bot_env : forall m, is_bot (Reached m) = M.existsb V.is_bot m.
  (** Inclusion treats every recognized bottom as least. *)
  Parameter F_leb_env : forall a b, leb a b = orb (is_bot a)
    (andb (negb (is_bot b)) (match a, b with
      | Reached ma, Reached mb => M.forall2b (fun x y =>
          V.leb (match x with Some v => v | None => V.top end)
                (match y with Some v => v | None => V.top end)) ma mb
      | _, _ => false end)).
  (** Annotation work counts one leaf lookup. *)
  Parameter tcost_leaf : forall m x, tcost m (Leaf x) = X.bits x + 1.
  (** Annotation work counts every child and the current transfer. *)
  Parameter tcost_node : forall m o es, tcost m (Node o es) =
    fold_right Nat.add 0 (map (tcost m) es) +
    V.work o (map (fun e => root (annotate m e)) es) + 1.
End ENV_PLAN.

Module Type ENV_ALL (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  ENV_T X M L V <+ ENV_PLAN X M L V.
