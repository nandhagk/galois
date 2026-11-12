(** * Non-relational environment code

    Environments map variables to abstract values and track unreachable states.
    For example, reading an absent binding returns the value domain's top.
    Builds on: EnvSig and the keyed map operations. *)

From Stdlib Require Import List Bool NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
Import List.ListNotations.

(** Variable collection prepends the leaves in their expression order. *)
Fixpoint env_vars_into {K X} (e : term K X) (acc : list X) : list X :=
  match e with
  | Leaf x => x :: acc
  | Node _ es => fold_right (fun e acc => env_vars_into e acc) acc es
  end.
TimeFun env_vars_into.

(** Variable collection traverses each expression constructor once. *)
Definition env_vars {K X} (e : term K X) : list X := env_vars_into e [].
TimeFun env_vars.

Module EnvCode (X : KEY_OPS) (M : MAP_OPS X) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) <: ENV_OPS X M L V.
  Definition t := reach (M.t V.t).
  Definition wparam := V.wparam.
  Definition read (m : M.t V.t) x :=
    match M.get x m with Some a => a | None => V.top end.
  Definition bot : t := Unreached.
  Definition top : t := Reached M.empty.
  Definition is_bot (s : t) :=
    match s with Unreached => true | Reached m => M.existsb V.is_bot m end.
  Definition option_leb a b :=
    match a, b with
    | None, None | Some _, None => true
    | None, Some b => V.leb V.top b
    | Some a, Some b => V.leb a b
    end.
  Definition leb (a b : t) :=
    orb (is_bot a) (andb (negb (is_bot b))
      (match a, b with
       | Reached a, Reached b => M.forall2b option_leb a b
       | _, _ => false
       end)).
  Definition join_map a b :=
    M.merge (fun x y => match x, y with
      | Some a, Some b =>
        let v := V.join a b in if V.is_bot v then None else Some v
      | _, _ => None
      end) a b.
  Definition join (a b : t) :=
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (join_map a b)
    end.
  Definition meet (a b : t) :=
    match a, b with
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | None, None => None
        | Some a, None => Some a
        | None, Some b => Some b
        | Some a, Some b => Some (V.meet a b)
        end) a b)
    | _, _ => Unreached
    end.
  Definition widen p (a b : t) :=
    if leb b a then a else
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | Some a, Some b =>
          let v := V.widen p a b in if V.is_bot v then None else Some v
        | _, _ => None
        end) a b)
    end.
  Definition narrow (a b : t) :=
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
  Definition root (n : ann L.op X.t V.t) := match n with ALeaf _ a | ANode _ a _ => a end.
  Fixpoint annotate (m : M.t V.t) (e : term L.op X.t) : ann L.op X.t V.t :=
    match e with
    | Leaf x => ALeaf x (read m x)
    | Node o es =>
      let ns := map (annotate m) es in ANode o (V.forward o (map root ns)) ns
    end.
  Fixpoint erase (n : ann L.op X.t V.t) : term L.op X.t :=
    match n with
    | ALeaf x _ => Leaf x
    | ANode o _ ns => Node o (map erase ns)
    end.
  Fixpoint refine_checked (q : V.t) (n : ann L.op X.t V.t) (m : M.t V.t)
      : M.t V.t * bool :=
    match n with
    | ALeaf x _ =>
      let v := V.meet (read m x) q in (M.set x v m, V.is_bot v)
    | ANode o _ ns =>
      let qs := V.backward o q (map root ns) in
      (fix go ns qs m bad :=
        match ns, qs with
        | n :: ns, q :: qs =>
          let result := refine_checked q n m in
          go ns qs (fst result) (orb bad (snd result))
        | _, _ => (m, bad)
        end) ns qs m false
    end.
  Definition refine q n m := fst (refine_checked q n m).
  Definition eval (e : term L.op X.t) (s : t) :=
    match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  Definition assign x e (s : t) :=
    match s with Unreached => Unreached | Reached m => Reached (M.set x (eval e s) m) end.
  Definition havoc x (s : t) :=
    match s with Unreached => Unreached | Reached m => Reached (M.set x V.top m) end.
  Definition vars (e : term L.op X.t) : list X.t := env_vars e.
  Definition materialize (m : M.t V.t) (xs : list X.t) :=
    fold_left (fun acc x => M.set x (read acc x) acc) xs m.
  Definition assume g es (s : t) :=
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
End EnvCode.

Module Env (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L)
    <: ENV X M L V.
  Include EnvCode X M L V.
  Include ENV_SPEC X M L V.
  Definition wrank (p : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun c =>
        match M.find c m with Some a => V.wrank p a | None => 0 end) (M.codes m))
    end.
  Definition gamma (s : t) (st : X.t -> L.val) : Prop :=
    match s with
    | Unreached => False
    | Reached m => M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x)
    end.

  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros [|a]; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* CONVERT: env_top: The variable leb_lift_bot was not found in the current environment. *)

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* CONVERT: env_core_wrank: The variable U was not found in the current environment. *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* CONVERT: env_core_wrank: The variable msum_bounded was not found in the current environment. *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* CONVERT: env_lift_weak: The reference env_lift_reduce was not found in the current *)

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof. Admitted. (* CONVERT: meaning_laws: The variable lat was not found in the current environment. *)
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st Hbot. exact Hbot.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof. Admitted. (* CONVERT: top_full: No product even after head-reduction. *)
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof. Admitted. (* CONVERT: assign_sound: The variable update_sound was not found. *)
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof. Admitted. (* CONVERT: havoc_sound: The variable update_sound was not found. *)
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof. Admitted. (* CONVERT: assume_sound: The variable refine_sound was not found. *)
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof. Admitted. (* CONVERT: abs_eval_sound: The variable term_eval_sound was not found. *)

  (** Reading an absent key returns top. *)
  Lemma read_spec : forall m x,
    read m x = match M.get x m with Some a => a | None => V.top end.
  Proof.
    intros m x.
    reflexivity.
  Qed.
  (** Leaf roots expose their stored abstract value. *)
  Lemma root_leaf : forall x a, root (ALeaf x a) = a.
  Proof. Admitted. (* STUB *)
  (** Node roots expose their stored abstract value. *)
  Lemma root_node : forall o a ns, root (ANode o a ns) = a.
  Proof. Admitted. (* STUB *)
  (** Leaf annotation reads the current environment. *)
  Lemma annotate_leaf : forall m x, annotate m (Leaf x) = ALeaf x (read m x).
  Proof. Admitted. (* STUB *)
  (** Node annotation transfers the annotated child roots. *)
  Lemma annotate_node : forall m o es, annotate m (Node o es) =
    ANode o (V.forward o (map (fun e => root (annotate m e)) es)) (map (annotate m) es).
  Proof. Admitted. (* STUB *)
  (** Unreachable states describe no stores. *)
  Lemma gamma_unreached : forall st, ~ gamma Unreached st.
  Proof.
    intros st Hbot. exact Hbot.
  Qed.
  (** Reached maps without recognized bottoms describe stores pointwise. *)
  Lemma gamma_reached : forall m st,
    gamma (Reached m) st <->
      M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x).
  Proof. Admitted. (* STUB *)
End Env.

Module EnvTimingHelpers (X : KEY_T) (M : MAP_T X) (L : LANG_T)
    (V : VALUE_DOMAIN_T L).
  Include Env X M L V.
  TimeFun read.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun option_leb.
  TimeFun leb.
  TimeFun join_map.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun root.
  TimeFun annotate.
  TimeFun erase.
  TimeFun refine_checked.
  TimeFun refine.
  TimeFun eval.
  TimeFun assign.
  TimeFun havoc.
  TimeFun vars.
  TimeFun materialize.
  TimeFun assume.
End EnvTimingHelpers.

Module EnvT (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    <: ENV_ALL X M L V.
  Include Env X M L V.
  TimeFun read.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun option_leb.
  TimeFun leb.
  TimeFun join_map.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun root.
  TimeFun annotate.
  TimeFun erase.
  TimeFun refine_checked.
  TimeFun refine.
  TimeFun eval.
  TimeFun assign.
  TimeFun havoc.
  TimeFun vars.
  TimeFun materialize.
  TimeFun assume.

  Definition size (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => M.nodes m + fold_right Nat.add 1
      (map (fun p =>
        match M.find p m with Some a => V.size a + 1 | None => 0 end) (M.codes m))
    end.
  Definition wsize (p : wparam) : nat := V.wsize p.
  Definition wunits (s : t) : nat :=
    match s with Unreached => 0 | Reached m => length (M.codes m) end.
  Fixpoint tcost (m : M.t V.t) (e : term L.op X.t) : nat :=
    match e with
    | Leaf x => X.bits x + 1
    | Node o es =>
      fold_right Nat.add 0 (map (tcost m) es) +
        V.work o (map (fun e => root (annotate m e)) es) + 1
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
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    match s with
    | Unreached => tsize e + X.bits x + 1
    | Reached m => tcost m e + size s + X.bits x + 1
    end.
  Definition havoc_work (x : X.t) (s : t) : nat := size s + X.bits x + 1.
  Definition eval_work (e : term L.op X.t) (s : t) : nat :=
    match s with Unreached => tsize e + 1 | Reached m => tcost m e + 1 end.
  Definition tcost_s (s : t) (e : term L.op X.t) : nat :=
    match s with Unreached => 0 | Reached m => tcost m e end.
  Definition rsize (s : t) (g : L.guard) (es : list (term L.op X.t)) : nat :=
    assume_size s g es.
  Definition esize (s : t) : nat := size s.
  Definition env_wf (s : t) : Prop :=
    match s with Unreached => True | Reached m => M.wf m end.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    fold_right Nat.add 0 (map (tcost_s s) es) +
      V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Definition c_state : N := 1%N. (* STUB *)
  Definition c_env : N := 1%N. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_annotate_le : forall m e,
    (T_annotate m e <= c_env * N.of_nat (tcost m e))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_env_le : forall g es s,
    (T_assume g es s <= c_env * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost_s s) es) + V.gwork g (roots s es) +
       fold_right Nat.add 0%nat (map tsize es) * (rsize s g es + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_env_le : forall a b, env_wf a -> env_wf b ->
    (T_join a b <= c_env * N.of_nat (esize a + esize b + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F_wunits_unreached : wunits Unreached = 0.
  Proof. Admitted. (* STUB *)
  Lemma F_wunits_reached : forall m, wunits (Reached m) = length (M.codes m).
  Proof. Admitted. (* STUB *)
  Lemma F_bot : bot = Unreached.
  Proof. Admitted. (* STUB *)
  Lemma F_top : top = Reached M.empty.
  Proof. Admitted. (* STUB *)
  Lemma F_join_map : forall a b, join_map a b =
    M.merge (fun x y => match x, y with
      | Some a, Some b => let v := V.join a b in if V.is_bot v then None else Some v
      | _, _ => None
      end) a b.
  Proof. Admitted. (* STUB *)
  Lemma F_join : forall a b, join a b =
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (join_map a b)
    end.
  Proof. Admitted. (* STUB *)
  Definition k_env_widen : N := 1%N. (* STUB *)
  Lemma F_widen : forall p a b, widen p a b =
    if leb b a then a else
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | Some a, Some b => let v := V.widen p a b in if V.is_bot v then None else Some v
        | _, _ => None
        end) a b)
    end.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_split : forall p a b,
    (T_widen p a b <= T_leb b a + k_env_widen *
      (1 + if leb b a then 0 else
        match a, b with
        | Reached ma, Reached mb => M.T_merge
            (fun x y => match x, y with
             | Some a, Some b => let v := V.widen p a b in if V.is_bot v then None else Some v
             | _, _ => None
             end)
            (fun x y => match x, y with
             | Some a, Some b => V.T_widen p a b + V.T_is_bot (V.widen p a b) + 1
             | _, _ => 1
             end) ma mb
        | _, _ => 0
        end))%N.
  Proof. Admitted. (* STUB *)
  Lemma F_narrow : forall a b, narrow a b =
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
  Proof. Admitted. (* STUB *)
  Lemma F_eval : forall e s, eval e s =
    match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  Proof. Admitted. (* STUB *)
  Lemma F_assign : forall x e s, assign x e s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x (eval e s) m)
    end.
  Proof. Admitted. (* STUB *)
  Lemma F_havoc : forall x s, havoc x s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x V.top m)
    end.
  Proof. Admitted. (* STUB *)
  Lemma F_refine_leaf : forall q x a m, refine_checked q (ALeaf x a) m =
    let v := V.meet (read m x) q in (M.set x v m, V.is_bot v).
  Proof. Admitted. (* STUB *)
  Lemma F_refine_node : forall q o a ns m, refine_checked q (ANode o a ns) m =
    let qs := V.backward o q (map root ns) in
    (fix children ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        children ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m false.
  Proof. Admitted. (* STUB *)
  Lemma F_refine : forall q n m,
    refine q n m = fst (refine_checked q n m).
  Proof. Admitted. (* STUB *)
  Lemma F_assume : forall g es s, assume g es s =
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
  Proof. Admitted. (* STUB *)
  Lemma F_rsize : forall s g es, rsize s g es = assume_size s g es.
  Proof. Admitted. (* STUB *)
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
  Definition k_env_refine : N := 1%N. (* STUB *)
  (** Annotation records the work of its term. *)
  Lemma F_ann_work : forall m e, ann_work (annotate m e) = tcost m e.
  Proof. Admitted. (* STUB *)
  (** Annotation keeps the shape of its term. *)
  Lemma F_ann_size : forall m e, ann_size (annotate m e) = tsize e.
  Proof. Admitted. (* STUB *)
  (** Checked refinement charges cached transfers, leaf lookups and the requests it meets. *)
  Lemma T2_refine_checked : forall q n m,
    (T_refine_checked q n m <= k_env_refine *
      N.of_nat (ann_work n + ann_size n * (refine_size q n m + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_assume : forall g es m,
    (T_assume g es (Reached m) <= c_env * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost m) es) +
        V.gwork g (roots (Reached m) es) +
        fold_right Nat.add 0%nat (map tsize es) * (rsize (Reached m) g es + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition models (m : M.t V.t) (st : X.t -> L.val) : Prop :=
    forall x, V.gamma (read m x) (st x).
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
  Lemma annotate_sound : forall m st e c,
    models m st -> eval_term L.eval st e = Some c ->
    ann_models st (annotate m e) e /\ V.gamma (root (annotate m e)) c.
  Proof. Admitted. (* STUB *)
  Lemma refine_sound : forall m st e n q c,
    models m st -> ann_models st n e -> eval_term L.eval st e = Some c ->
    V.gamma q c -> models (refine q n m) st.
  Proof. Admitted. (* STUB *)
  Lemma refine_lower : forall q n m x,
    V.leb (read (refine q n m) x) (read m x) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_models : forall a b st,
    models a st \/ models b st -> models (join_map a b) st.
  Proof. Admitted. (* STUB *)
  Lemma wrank_env : forall p m, M.wf m -> wrank p (Reached m) =
    fold_right Nat.add 0
      (map (fun kv => V.wrank p (snd kv)) (M.elements m)).
  Proof. Admitted. (* STUB *)
  Lemma F_is_bot_env : forall m, is_bot (Reached m) = M.existsb V.is_bot m.
  Proof. Admitted. (* STUB *)
  Lemma F_leb_env : forall a b, leb a b = orb (is_bot a)
    (andb (negb (is_bot b)) (match a, b with
      | Reached ma, Reached mb => M.forall2b (fun x y =>
          V.leb (match x with Some v => v | None => V.top end)
                (match y with Some v => v | None => V.top end)) ma mb
      | _, _ => false end)).
  Proof. Admitted. (* STUB *)
  Lemma tcost_leaf : forall m x, tcost m (Leaf x) = X.bits x + 1.
  Proof. Admitted. (* STUB *)
  Lemma tcost_node : forall m o es, tcost m (Node o es) =
    fold_right Nat.add 0 (map (tcost m) es) +
    V.work o (map (fun e => root (annotate m e)) es) + 1.
  Proof. Admitted. (* STUB *)
  (** Environment size agrees with its raw stored-value measure. *)
  Lemma F_size : forall s, size s = esize s.
  Proof. Admitted. (* STUB *)
  (** Environment widening parameters use the value-domain parameter size. *)
  Lemma F_wsize : forall p, wsize p = V.wsize p.
  Proof. Admitted. (* STUB *)
  (** Assignment work charges annotation and the current environment. *)
  Lemma F_assign_work : forall x e s, assign_work x e s =
    match s with
    | Unreached => tsize e + X.bits x + 1
    | Reached m => tcost m e + esize s + X.bits x + 1
    end.
  Proof. Admitted. (* STUB *)
  (** Havoc work charges the environment and the selected key. *)
  Lemma F_havoc_work : forall x s, havoc_work x s = esize s + X.bits x + 1.
  Proof. Admitted. (* STUB *)
  (** Evaluation work charges its cached forward pass. *)
  Lemma F_eval_work : forall e s, eval_work e s =
    match s with Unreached => tsize e + 1 | Reached m => tcost m e + 1 end.
  Proof. Admitted. (* STUB *)
  (** Assumption work charges the forward pass, guard and checked refinement. *)
  Lemma F_assume_work : forall g es s, assume_work g es s =
    fold_right Nat.add 0 (map (tcost_s s) es) + V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1.
  Proof. Admitted. (* STUB *)
End EnvT.
