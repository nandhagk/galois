(** * Non-relational environment code

    Environments map variables to abstract values and track unreachable states.
    For example, reading an absent binding returns the value domain's top.
    Builds on: EnvSig and the keyed map operations. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
Import List.ListNotations.

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
  Fixpoint vars (e : term L.op X.t) : list X.t :=
    match e with
    | Leaf x => [x]
    | Node _ es => flat_map vars es
    end.
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
