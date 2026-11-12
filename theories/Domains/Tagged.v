(** * Tagged word payloads

    Tags attach widths to payloads and represent bottom and top.
    For example, joining values of different widths produces top.
    Builds on: WordSig and BitsLang. *)

From Stdlib Require Import List ZArith.
From Galois.Bits Require Import Word.
From Galois.Domains Require Import WordSig HarnessSig BitsLang.

Module TaggedCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    <: HARNESS_BASE_OPS BitsLangCode.
  Definition t := tagged W.p.
  Definition bot : t := TBot.
  Definition top : t := TAny.
  Definition is_bot (a : t) : bool :=
    match a with
    | TBot => true
    | TVal w p => W.pis_bot w p
    | TAny => false
    end.
  Definition leb (a b : t) : bool :=
    match a, b with
    | TBot, _ => true
    | _, TAny => true
    | TVal w p, TVal v q =>
      if Pos.eqb w v then W.pleb w p q else W.pis_bot w p
    | TVal w p, TBot => W.pis_bot w p
    | _, _ => false
    end.
  Definition join (a b : t) : t :=
    if is_bot a then b else if is_bot b then a else
    match a, b with
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pjoin w p q) else TAny
    | _, _ => TAny
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | TBot, _ | _, TBot => TBot
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pmeet w p q) else TBot
    end.
  Definition wparam := W.pwparam.
  Definition widen (q : wparam) (a b : t) : t :=
    if leb b a then a else
    match a, b with
    | TBot, _ => b
    | TVal w p, TVal v r =>
      if W.pis_bot w p then b else
      if Pos.eqb w v then TVal w (W.pwiden q w p r) else TAny
    | _, _ => TAny
    end.
  Definition narrow (a b : t) : t :=
    match a, b with
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pnarrow w p q) else TBot
    | _, _ => TBot
    end.
  Definition point (a : t) : option BitsLangCode.val :=
    match a with
    | TVal w p => match W.ppoint w p with Some z => Some (w, z) | None => None end
    | _ => None
    end.
  Definition abst (v : BitsLangCode.val) : t :=
    if Z.eqb (L.wrap (fst v) (snd v)) (snd v)
    then TVal (fst v) (W.pconst (fst v) (snd v)) else TAny.
End TaggedCode.
