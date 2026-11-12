(** * Interprocedural edge presentations

    Edge kinds are stored in a trie keyed by edge identity.
    For example, an absent binding denotes an internal edge.
    Builds on: Program.IcfgSig and Base.Trie. *)

From Galois.Base Require Import KeySig Trie.
From Galois.Program Require Import CfgSig IcfgSig.

Module Type ICFG_DATA (P : TYPE) (S : KEY_OPS).
  Parameter kinds : P.t -> ptrie (edge_kind S.t).
End ICFG_DATA.

Module IcfgCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_OPS P N E) (S : KEY_OPS) (D : ICFG_DATA P S)
    <: ICFG_OPS P N E C S.
  Definition kind p e :=
    match trie_get (E.encode e) (D.kinds p) with
    | Some k => k
    | None => Intra
    end.
End IcfgCode.

Module Icfg (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (S : KEY) (D : ICFG_DATA P S) <: ICFG P N E C S.
  Include IcfgCode P N E C S D.
  Include ICFG_SPEC P N E C S.
End Icfg.
