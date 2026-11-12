(** * Non-relational environment code

    Environments map variables to abstract values and track unreachable states.
    For example, reading an absent binding returns the value domain's top.
    Builds on: EnvSig and the keyed map operations. *)

From Stdlib Require Import List Bool.
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
    | Reached m => fold_right Nat.add 0 (map (fun kv => V.wrank p (snd kv)) (M.elements m))
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
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
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
  Proof. Admitted.
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
  Proof. Admitted.
  (** Node roots expose their stored abstract value. *)
  Lemma root_node : forall o a ns, root (ANode o a ns) = a.
  Proof. Admitted.
  (** Leaf annotation reads the current environment. *)
  Lemma annotate_leaf : forall m x, annotate m (Leaf x) = ALeaf x (read m x).
  Proof. Admitted.
  (** Node annotation transfers the annotated child roots. *)
  Lemma annotate_node : forall m o es, annotate m (Node o es) =
    ANode o (V.forward o (map (fun e => root (annotate m e)) es)) (map (annotate m) es).
  Proof. Admitted.
  (** Unreachable states describe no stores. *)
  Lemma gamma_unreached : forall st, ~ gamma Unreached st.
  Proof.
    intros st Hbot. exact Hbot.
  Qed.
  (** Reached maps without recognized bottoms describe stores pointwise. *)
  Lemma gamma_reached : forall m st,
    gamma (Reached m) st <->
      M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x).
  Proof. Admitted.
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
