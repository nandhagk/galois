(** * Gen/kill analyses

    This file constructs may and must lattices and dense transfers.
    For example, a generated fact survives a simultaneous kill.
    Builds on: Framework.GenKillSig and Framework.Dense. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig SetSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense GenKillSig.

Module GenKillMayDomainCode (F : KEY_OPS) (S : SET_OPS F)
    <: GENKILL_MAY_DOMAIN_OPS F S.
  Definition t := S.t.
  Definition leb := S.subset.
  Definition bot := S.empty.
  Definition is_bot x := S.subset x S.empty.
  Definition join := S.union.
End GenKillMayDomainCode.

Module GenKillMustDomainCode (F : KEY_OPS) (S : SET_OPS F)
    <: GENKILL_MUST_DOMAIN_OPS F S.
  Definition t := option S.t.
  Definition leb := genkill_must_leb S.subset.
  Definition bot : t := None.
  Definition is_bot (x : t) := match x with None => true | Some _ => false end.
  Definition join := genkill_must_join S.inter.
End GenKillMustDomainCode.

Module GenKillMayFlowCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN_OPS F S) <: GENKILL_MAY_FLOW_OPS P N E F S G L.
  Definition dir := G.dir.
  Definition boundary p (_ : N.t) := G.init p.
  Definition transfer p e a := S.union (G.gen p e) (S.diff a (G.kill p e)).
End GenKillMayFlowCode.

Module GenKillMustFlowCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN_OPS F S) <: GENKILL_MUST_FLOW_OPS P N E F S G L.
  Definition dir := G.dir.
  Definition boundary p (_ : N.t) := Some (G.init p).
  Definition transfer p e (a : option S.t) :=
    match a with
    | None => None
    | Some facts => Some (S.union (G.gen p e) (S.diff facts (G.kill p e)))
    end.
End GenKillMustFlowCode.

Module GenKillMayDomain (F : KEY) (S : SET F) <: GENKILL_MAY_DOMAIN F S.
  Include GenKillMayDomainCode F S.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
End GenKillMayDomain.

Module GenKillMustDomain (F : KEY) (S : SET F) <: GENKILL_MUST_DOMAIN F S.
  Include GenKillMustDomainCode F S.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
End GenKillMustDomain.

Module GenKillMayCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN_OPS F S) (T : GENKILL_MAY_FLOW_OPS P N E F S G L)
    <: SYSTEM_OPS L.
  Include DenseCode P N E C L T.
End GenKillMayCode.

Module GenKillMustCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN_OPS F S) (T : GENKILL_MUST_FLOW_OPS P N E F S G L)
    <: SYSTEM_OPS L.
  Include DenseCode P N E C L T.
End GenKillMustCode.

Module GenKillMay (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN F S) (T : GENKILL_MAY_FLOW_OPS P N E F S G L)
    <: GENKILL_MAY P N E C F S G L T.
  Include Dense P N E C L T.
End GenKillMay.

Module GenKillMust (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN F S) (T : GENKILL_MUST_FLOW_OPS P N E F S G L)
    <: GENKILL_MUST P N E C F S G L T.
  Include Dense P N E C L T.
End GenKillMust.
