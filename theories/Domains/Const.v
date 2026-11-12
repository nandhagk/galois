(** * Flat constant domain code

    Flat values distinguish bottom, one value and top.
    For example, joining distinct singleton values returns top.
    Builds on: ConstSig and the concrete language operations. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Bits Require Import Word Fun Op.
From Galois.Domains Require Import ConstSig LangSig WordSig.
Import List.ListNotations.

Module ConstCode (L : LANG_OPS) (E : VAL_EQ_OPS L) <: CONST_OPS L E.
  Definition t := flat L.val.
  Definition wparam := unit.
  Definition leb (a b : t) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => E.eqb x y
    | _, _ => false
    end.
  Definition bot : t := FBot.
  Definition top : t := FTop.
  Definition is_bot (a : t) := match a with FBot => true | _ => false end.
  Definition join (a b : t) : t :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if E.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if E.eqb x y then a else FBot
    end.
  Definition widen (_ : unit) (a b : t) := join a b.
  Definition narrow (a _ : t) := a.
  Definition point (a : t) := match a with FVal x => Some x | _ => None end.
  Definition abst (v : L.val) : t := FVal v.
  Fixpoint points (xs : list t) : option (list L.val) :=
    match xs with
    | [] => Some []
    | FVal x :: rest =>
      match points rest with
      | Some vs => Some (x :: vs)
      | None => None
      end
    | _ => None
    end.
  Definition forward (o : L.op) (xs : list t) : t :=
    if existsb is_bot xs then FBot else
      match points xs with
      | Some vs => match L.eval o vs with Some v => FVal v | None => FBot end
      | None => FTop
      end.
  Definition backward (_ : L.op) (_ : t) (xs : list t) := xs.
  Definition guard (_ : L.guard) (xs : list t) := xs.
End ConstCode.

Module ConstWordCode (L : WORD_LANGUAGE_OPS)
    <: (WORD_PAYLOAD_OPS L with Definition p := flat Z).
  Definition p := flat Z.
  Definition pleb (_ : positive) (a b : p) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => Z.eqb x y
    | _, _ => false
    end.
  Definition pjoin (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if Z.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition pmeet (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if Z.eqb x y then a else FBot
    end.
  Definition pbot (_ : positive) : p := FBot.
  Definition ptop (_ : positive) : p := FTop.
  Definition pis_bot (_ : positive) (a : p) :=
    match a with FBot => true | _ => false end.
  Definition pconst (w : positive) (z : Z) : p := FVal (L.wrap w z).
  Definition ppoint (_ : positive) (a : p) : option Z :=
    match a with FVal z => Some z | _ => None end.
End ConstWordCode.

Module ConstWordTableCode (L : WORD_LANGUAGE_OPS)
    (W : WORD_PAYLOAD_OPS L with Definition p := flat Z) <: WORD_TABLE_OPS L W.
  Definition const_is (a : flat Z) (z : Z) :=
    match a with FVal x => Z.eqb x z | _ => false end.
  Definition shortcut (o : L.op) (a b : positive * W.p) : option Z :=
    match o with
    | bvmul | bvand =>
      if const_is (snd a) 0 || const_is (snd b) 0 then Some 0 else None
    | bvor =>
      if const_is (snd a) (modulus (fst a) - 1) ||
         const_is (snd b) (modulus (fst a) - 1)
      then Some (modulus (fst a) - 1) else None
    | bvshl | bvlshr | bvashr | bvurem =>
      if const_is (snd a) 0 then Some 0 else None
    | _ => None
    end%Z.
  Definition inverse (f : Z -> Z) (a : flat Z) : flat Z :=
    match a with FVal z => FVal (f z) | _ => FTop end.
  Definition inverse_pair w (f g : Z -> Z) (a b : W.p) :=
    [W.pmeet w a (inverse f b); W.pmeet w b (inverse g a)].
  Definition backward_one o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(_, a)], FVal r =>
      [W.pmeet rw a (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end))]
    | _, _ => map snd xs
    end.
  Definition backward_two o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(w, a); (_, b)], FVal r =>
      match o with
      | bveq => if Z.eqb r 1 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvne => if Z.eqb r 0 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvadd => inverse_pair rw (fun z => wsub w r z) (fun z => wsub w r z) a b
      | bvsub => inverse_pair rw (fun z => wadd w r z) (fun z => wsub w z r) a b
      | bvxor => inverse_pair rw (fun z => wxor w r z) (fun z => wxor w r z) a b
      | _ => [a; b]
      end
    | _, _ => map snd xs
    end%Z.
  Definition wfwd o (_ : positive) (xs : list (positive * W.p)) : option W.p :=
    match o, xs with
    | (bvmul | bvand | bvor | bvshl | bvlshr | bvashr | bvurem), [a; b] =>
      Some (match shortcut o a b with Some c => FVal c | None => FTop end)
    | _, _ => None
    end.
  Definition wbwd o rw q (xs : list (positive * W.p)) : option (list W.p) :=
    match o, xs with
    | (bvnot | bvneg), [_] => Some (backward_one o rw q xs)
    | (bveq | bvne | bvadd | bvsub | bvxor), [_; _] => Some (backward_two o rw q xs)
    | _, _ => None
    end.
End ConstWordTableCode.
