(** * Gen/kill analyses

    This file constructs may and must lattices and dense transfers.
    For example, a generated fact survives a simultaneous kill.
    Builds on: Framework.GenKillSig and Framework.Dense. *)

From Stdlib Require Import List Bool NArith.
From Argent Require Import Time Std.
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
  Proof. Admitted. (* STUB *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
End GenKillMayDomain.

Module GenKillMustDomain (F : KEY) (S : SET F) <: GENKILL_MUST_DOMAIN F S.
  Include GenKillMustDomainCode F S.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
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

Module GenKillSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (ML : GENKILL_MAY_DOMAIN_OPS F S) (UL : GENKILL_MUST_DOMAIN_OPS F S)
    (MT : GENKILL_MAY_FLOW_OPS P N E F S G ML)
    (UT : GENKILL_MUST_FLOW_OPS P N E F S G UL)
    (May : DENSE_SYSTEM P N E C ML MT) (Must : DENSE_SYSTEM P N E C UL UT)
    <: GENKILL_SOUND P N E C F S G ML UL MT UT May Must.
  Definition route p entry path n := genkill_route (C.edges p)
    (fun e => match G.dir with Forward => C.src p e | Backward => C.dst p e end)
    (fun e => match G.dir with Forward => C.dst p e | Backward => C.src p e end)
    entry path n.
  Definition path_facts p path :=
    genkill_path S.union S.diff (G.gen p) (G.kill p) (G.init p) path.
  Definition produces p n d := exists root initial path,
    genkill_may_start (C.nodes p) (C.entries p) S.empty (G.init p) root initial /\
    route p root path n /\
    S.mem d (genkill_path S.union S.diff (G.gen p) (G.kill p) initial path) = true.
  (** Every produced path fact belongs to a may post-solution. *)
  Lemma may_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall n d, produces p n d -> S.mem d (look n) = true.
  Proof. Admitted. (* CONVERT: produces_in_post: The reference Bitvector.may_source_post_iff was not found *)
  (** Every fact generated on an actual boundary path belongs to a may post-solution. *)
  Lemma may_boundary_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall entry path n d, In entry (C.entries p) -> route p entry path n ->
      S.mem d (path_facts p path) = true -> S.mem d (look n) = true.
  Proof. Admitted. (* STUB *)
  (** A reached must post-solution contains facts present on every boundary path. *)
  Lemma must_covers : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n facts d, In entry (C.entries p) -> route p entry path n ->
      look n = Some facts -> S.mem d facts = true -> S.mem d (path_facts p path) = true.
  Proof. Admitted. (* CONVERT: must_post_keeps: The reference Bitvector.must_source_post_iff was not found *)
  (** A boundary path has a reached must value in every post-solution. *)
  Lemma must_reached : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n, In entry (C.entries p) -> route p entry path n ->
      exists facts, look n = Some facts.
  Proof. Admitted. (* STUB *)
  (** A least may post-solution equals production from empty listed starts and boundaries. *)
  Lemma may_exact : forall p look, C.wf p -> G.may = true -> May.post_solution p look ->
    (forall other, May.post_solution p other -> forall n, S.subset (look n) (other n) = true) ->
    forall n d, In n (C.nodes p) -> (S.mem d (look n) = true <-> produces p n d).
  Proof. Admitted. (* CONVERT: may_least_paths: The variable may_closure was not found *)
  (** A least reached must post-solution contains exactly the facts on all boundary paths. *)
  Lemma must_exact : forall p look, C.wf p -> G.may = false -> Must.post_solution p look ->
    (forall other, Must.post_solution p other -> forall n,
      genkill_must_leb S.subset (look n) (other n) = true) ->
    forall n facts, In n (C.nodes p) -> look n = Some facts -> forall d,
      S.mem d facts = true <-> forall entry path,
        In entry (C.entries p) -> route p entry path n -> S.mem d (path_facts p path) = true.
  Proof. Admitted. (* CONVERT: must_greatest_paths: The variable must_post_keeps was not found *)
End GenKillSound.

Module GenKillMayDomainT (F : KEY_T) (S : SET_T F)
    <: GENKILL_MAY_DOMAIN_T F S.
  Include GenKillMayDomain F S.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size := S.nodes.
  Lemma size_nodes : forall a, size a = S.nodes a.
  Proof. reflexivity. Qed.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End GenKillMayDomainT.

Module GenKillMustDomainT (F : KEY_T) (S : SET_T F)
    <: GENKILL_MUST_DOMAIN_T F S.
  Include GenKillMustDomain F S.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (a : t) :=
    match a with
    | None => 0
    | Some facts => S.nodes facts
    end.
  Lemma size_nodes : forall a,
    size a = match a with None => 0 | Some facts => S.nodes facts end.
  Proof. reflexivity. Qed.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End GenKillMustDomainT.

Module GenKillMayFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MAY_DOMAIN_T F S).
  Include GenKillMayFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
End GenKillMayFlowT.

Module GenKillMustFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MUST_DOMAIN_T F S).
  Include GenKillMustFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
End GenKillMustFlowT.

Module GenKillMayOperationalT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (F : KEY_T) (S : SET_T F)
    (G : GENKILL_T P E F S) (L : GENKILL_MAY_DOMAIN_T F S).
  Module Flow := GenKillMayFlowT P N E F S G L.
  Include GenKillMay P N E C F S G L Flow.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
End GenKillMayOperationalT.

Module GenKillMustOperationalT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (F : KEY_T) (S : SET_T F)
    (G : GENKILL_T P E F S) (L : GENKILL_MUST_DOMAIN_T F S).
  Module Flow := GenKillMustFlowT P N E F S G L.
  Include GenKillMust P N E C F S G L Flow.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
End GenKillMustOperationalT.
