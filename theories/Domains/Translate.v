(** * Value domain translation

    Translation reuses a value domain under operator and guard mappings.
    For example, a source operator can dispatch to a target operator before transfer.
    Builds on: LangSig and ValueSig. *)

From Stdlib Require Import List.
From Galois.Domains Require Import LangSig ValueSig.

Module Type LANG_MORPHISM_OPS (L1 L2 : LANG_OPS).
  Parameter op : L1.op -> L2.op.
  Parameter guard : L1.guard -> L2.guard.
End LANG_MORPHISM_OPS.

Module TranslateCode (L1 L2 : LANG_OPS) (F : LANG_MORPHISM_OPS L1 L2)
    (D : VALUE_DOMAIN_OPS L2) <: VALUE_DOMAIN_OPS L1.
  Definition t := D.t.
  Definition leb := D.leb.
  Definition bot := D.bot.
  Definition is_bot := D.is_bot.
  Definition join := D.join.
  Definition top := D.top.
  Definition meet := D.meet.
  Definition wparam := D.wparam.
  Definition widen := D.widen.
  Definition narrow := D.narrow.
  Definition forward (o : L1.op) (xs : list t) := D.forward (F.op o) xs.
  Definition backward (o : L1.op) (r : t) (xs : list t) := D.backward (F.op o) r xs.
  Definition guard (g : L1.guard) (xs : list t) := D.guard (F.guard g) xs.
End TranslateCode.
