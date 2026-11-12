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

Module TaggedTableCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    (T : WORD_TABLE_OPS L W).
  Fixpoint untag (xs : list (tagged W.p)) : option (list (positive * W.p)) :=
    match xs with
    | nil => Some nil
    | TVal w p :: rest =>
      match untag rest with
      | Some ws => Some ((w, p) :: ws)
      | None => None
      end
    | _ => None
    end.

  Fixpoint retag (ws : list positive) (ps : list W.p) : list (tagged W.p) :=
    match ws, ps with
    | w :: rest, p :: tail => TVal w p :: retag rest tail
    | _, _ => nil
    end.

  Definition fwd (o : BitsLangCode.op) (xs : list (tagged W.p)) : option (tagged W.p) :=
    match o with
    | BConst w z =>
      match xs with nil => Some (TVal w (W.pconst w z)) | _ => None end
    | BOp o =>
      match untag xs with
      | Some ws =>
        match L.result_width o (map fst ws) with
        | Some w => match T.wfwd o w ws with Some p => Some (TVal w p) | None => None end
        | None => None
        end
      | None => None
      end
    end.

  Definition bwd (o : BitsLangCode.op) (r : tagged W.p) (xs : list (tagged W.p))
      : option (list (tagged W.p)) :=
    match o, r, untag xs with
    | BOp o, TVal w p, Some ws =>
      match L.result_width o (map fst ws) with
      | Some rw =>
        if Pos.eqb w rw then
          match T.wbwd o w p ws with
          | Some ps => Some (retag (map fst ws) ps)
          | None => None
          end
        else None
      | None => None
      end
    | _, _, _ => None
    end.

  Definition grd (_ : BitsLangCode.guard) (_ : list (tagged W.p))
      : option (list (tagged W.p)) := None.
End TaggedTableCode.
