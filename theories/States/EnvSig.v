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
  Parameter refine_checked : V.t -> ann L.op X.t V.t -> M.t V.t -> M.t V.t * bool.
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
  (** Reached maps without recognized bottoms describe stores pointwise. *)
  Parameter gamma_reached : forall m st,
    gamma (Reached m) st <->
      M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x).
End ENV_LAWS.

Module Type ENV (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L) :=
  ENV_BASE X M L V <+ ENV_LAWS X M L V.

Module Type ENV_TIME (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import E : ENV X M L V).
  Include STATE_DOMAIN_TIME X L V E.
  (* spec: tcost rsize *)
  Parameter tcost : M.t V.t -> term L.op X.t -> nat.
  Definition tcost_s (s : t) (e : term L.op X.t) : nat :=
    match s with Unreached => 0 | Reached m => tcost m e end.
  Definition esize (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => M.nodes m + fold_right Nat.add 1
      (map (fun p =>
        match M.find p m with Some a => V.size a + 1 | None => 0 end) (M.codes m))
    end.
  Definition env_wf (s : t) : Prop :=
    match s with Unreached => True | Reached m => M.wf m end.
  Parameter rsize : t -> L.guard -> list (term L.op X.t) -> nat.
  Parameter T_read : M.t V.t -> X.t -> N.
  Parameter T_annotate : M.t V.t -> term L.op X.t -> N.
  Parameter T_root : ann L.op X.t V.t -> N.
  Parameter T_refine : V.t -> ann L.op X.t V.t -> M.t V.t -> N.
  Parameter T_refine_checked : V.t -> ann L.op X.t V.t -> M.t V.t -> N.
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
  (** Unreachable environments widen no stored component. *)
  Parameter F_wunits_unreached : wunits Unreached = 0.
  (** Reached environments visit every stored binding during widening. *)
  Parameter F_wunits_reached : forall m, wunits (Reached m) = length (M.codes m).
  (** Environment bottom is unreachable. *)
  Parameter F_bot : bot = Unreached.
  (** Environment top is an empty reached map. *)
  Parameter F_top : top = Reached M.empty.
  (** Map join merges common bindings and omits recognized bottom results. *)
  Parameter F_join_map : forall a b, join_map a b =
    M.merge (fun x y => match x, y with
      | Some a, Some b => let v := V.join a b in if V.is_bot v then None else Some v
      | _, _ => None
      end) a b.
  (** Environment join handles unreachable states before merging maps. *)
  Parameter F_join : forall a b, join a b =
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (join_map a b)
    end.
  (** Widening keeps stable states and otherwise merges common bindings. *)
  Parameter F_widen : forall p a b, widen p a b =
    if leb b a then a else
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | Some a, Some b => let v := V.widen p a b in if V.is_bot v then None else Some v
        | _, _ => None
        end) a b)
    end.
  Parameter k_env_widen : N.
  (** Widening pays for inclusion before its conditional merge. *)
  Parameter T_widen_split : forall p a b,
    (T_widen p a b <= T_leb b a + k_env_widen *
      (1 + if leb b a then 0 else
        match a, b with
        | Reached ma, Reached mb => M.T_merge
            (fun x y => match x, y with
             | Some a, Some b =>
               let v := V.widen p a b in if V.is_bot v then None else Some v
             | _, _ => None
             end)
            (fun x y => match x, y with
             | Some a, Some b => V.T_widen p a b + V.T_is_bot (V.widen p a b) + 1
             | _, _ => 1
             end) ma mb
        | _, _ => 0
        end))%N.
  (** Narrowing retains one-sided bindings and narrows common bindings. *)
  Parameter F_narrow : forall a b, narrow a b =
    if is_bot b then b else
    match a, b with
    | Unreached, _ => Unreached
    | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | None, None => None
        | Some a, None => Some a
        | None, Some b => Some b
        | Some a, Some b => Some (V.narrow a b)
        end) a b)
    end.
  (** Evaluation reads the root of the cached forward annotation. *)
  Parameter F_eval : forall e s, eval e s =
    match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  (** Assignment writes the abstract expression result at its declared variable. *)
  Parameter F_assign : forall x e s, assign x e s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x (eval e s) m)
    end.
  (** Havoc writes top at its declared variable. *)
  Parameter F_havoc : forall x s, havoc x s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x V.top m)
    end.
  (** Leaf refinement checks the bottom status of the value it writes. *)
  Parameter F_refine_leaf : forall q x a m, refine_checked q (ALeaf x a) m =
    let v := V.meet (read m x) q in (M.set x v m, V.is_bot v).
  (** Node refinement uses cached child roots and carries bottom flags through siblings. *)
  Parameter F_refine_node : forall q o a ns m, refine_checked q (ANode o a ns) m =
    let qs := V.backward o q (map root ns) in
    (fix children ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        children ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m false.
  (** Ordinary refinement projects the map of checked refinement. *)
  Parameter F_refine : forall q n m, refine q n m = fst (refine_checked q n m).
  (** Assumption performs one cached annotation pass and one checked refinement pass. *)
  Parameter F_assume : forall g es s, assume g es s =
    match s with
    | Unreached => Unreached
    | Reached m =>
      let ns := map (annotate m) es in
      let qs := V.guard g (map root ns) in
      let result := fold_left (fun result nq =>
        let next := refine_checked (snd nq) (fst nq) (fst result) in
        (fst next, orb (snd result) (snd next))) (combine ns qs) (m, false) in
      if snd result then Unreached else Reached (fst result)
    end.
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
  Fixpoint ann_work (n : ann L.op X.t V.t) : nat :=
    match n with
    | ALeaf x _ => X.bits x + 1
    | ANode o _ ns => fold_right Nat.add 0 (map ann_work ns) + V.work o (map root ns) + 1
    end.
  Fixpoint ann_size (n : ann L.op X.t V.t) : nat :=
    match n with
    | ALeaf _ _ => 1
    | ANode _ _ ns => S (fold_right Nat.add 0 (map ann_size ns))
    end.
  Parameter k_env_refine : N.
  (** Annotation records the work of its term. *)
  Parameter F_ann_work : forall m e, ann_work (annotate m e) = tcost m e.
  (** Annotation keeps the shape of its term. *)
  Parameter F_ann_size : forall m e, ann_size (annotate m e) = tsize e.
  (** Checked refinement charges cached transfers, leaf lookups and the requests it meets. *)
  Parameter T2_refine_checked : forall q n m,
    (T_refine_checked q n m <= k_env_refine *
      N.of_nat (ann_work n + ann_size n * (refine_size q n m + 1)))%N.
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
  Parameter F_size : forall s, size s = esize s.
  Parameter F_wsize : forall p, wsize p = V.wsize p.
  Parameter F_assign_work : forall x e s, assign_work x e s =
    match s with
    | Unreached => tsize e + X.bits x + 1
    | Reached m => tcost m e + esize s + X.bits x + 1
    end.
  Parameter F_havoc_work : forall x s, havoc_work x s = esize s + X.bits x + 1.
  Parameter F_eval_work : forall e s, eval_work e s =
    match s with Unreached => tsize e + 1 | Reached m => tcost m e + 1 end.
  Parameter F_assume_work : forall g es s, assume_work g es s =
    fold_right Nat.add 0 (map (tcost_s s) es) + V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1.
End ENV_PLAN.

Module Type ENV_ALL (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  ENV_T X M L V <+ ENV_PLAN X M L V.
