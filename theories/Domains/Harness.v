(** * Transfer harness

    The harness combines concrete singleton evaluation with abstract transfer tables.
    For example, an unmodeled forward operation returns top.
    Builds on: HarnessSig. *)

From Stdlib Require Import List.
From Galois.Domains Require Import LangSig HarnessSig.

Module HarnessCode (L : LANG_OPS) (B : HARNESS_BASE_OPS L) (T : TABLE_OPS L B)
    <: HARNESS_OPS L B T.
  Definition t := B.t.
  Definition leb := B.leb.
  Definition bot := B.bot.
  Definition is_bot := B.is_bot.
  Definition join := B.join.
  Definition top := B.top.
  Definition meet := B.meet.
  Definition wparam := B.wparam.
  Definition widen := B.widen.
  Definition narrow := B.narrow.

  Fixpoint points (xs : list B.t) : option (list L.val) :=
    match xs with
    | nil => Some nil
    | x :: rest =>
      match B.point x, points rest with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
    end.

  Definition forward (o : L.op) (xs : list B.t) : B.t :=
    if existsb B.is_bot xs then B.bot else
    match points xs with
    | Some cs => match L.eval o cs with Some c => B.abst c | None => B.bot end
    | None => match T.fwd o xs with Some r => r | None => B.top end
    end.

  Fixpoint meet_all (xs ys : list B.t) : list B.t :=
    match xs, ys with
    | x :: rest, y :: tail => B.meet x y :: meet_all rest tail
    | _, _ => xs
    end.

  Definition backward (o : L.op) (r : B.t) (xs : list B.t) : list B.t :=
    match T.bwd o r xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.

  Definition guard (g : L.guard) (xs : list B.t) : list B.t :=
    match T.grd g xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs
    end.
End HarnessCode.
