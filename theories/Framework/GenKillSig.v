(** * May and must gen/kill frameworks

    Gen/kill transfer adds generated facts after removing killed facts.
    For example, a generated fact survives an edge even when that edge also kills it.
    Builds on: Framework.DenseSig, Base.SetSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List Bool NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig SetSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig.

(** Routes follow the selected forward or backward endpoints. *)
Inductive genkill_route {N E} (edges : list E) (src dst : E -> N) :
    N -> list E -> N -> Prop :=
  | Genkill_here : forall n, genkill_route edges src dst n nil n
  | Genkill_next : forall e es n, In e edges ->
      genkill_route edges src dst (dst e) es n ->
      genkill_route edges src dst (src e) (e :: es) n.

(** Path transfer follows edge order from the supplied initial fact set. *)
Definition genkill_path {E A} (union diff : A -> A -> A)
    (gen kill : E -> A) (initial : A) (path : list E) : A :=
  fold_left (fun a e => union (gen e) (diff a (kill e))) path initial.

TimeFun genkill_path.

(** May production starts with bottom at every listed node and with every actual boundary. *)
Inductive genkill_may_start {N A} (nodes entries : list N) (empty initial : A) : N -> A -> Prop :=
  | Genkill_empty : forall n, In n nodes -> genkill_may_start nodes entries empty initial n empty
  | Genkill_boundary : forall n, In n entries ->
      genkill_may_start nodes entries empty initial n initial.

(** Unreached must values are below every reached conjunction. *)
Definition genkill_must_leb {A} (subset : A -> A -> bool) (a b : option A) : bool :=
  match a, b with
  | None, _ => true
  | Some _, None => false
  | Some x, Some y => subset y x
  end.

TimeFun genkill_must_leb.

(** Joining reached must values intersects their fact sets. *)
Definition genkill_must_join {A} (inter : A -> A -> A) (a b : option A) : option A :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some x, Some y => Some (inter x y)
  end.

TimeFun genkill_must_join.

Module Type GENKILL_OPS (P E : TYPE) (F : KEY_OPS) (S : SET_OPS F).
  Parameter dir : direction.
  Parameter may : bool.
  Parameter gen kill : P.t -> E.t -> S.t.
  Parameter init : P.t -> S.t.
End GENKILL_OPS.

Module Type GENKILL_TIME (P E : TYPE) (F : KEY_T) (S : SET_T F)
    (Import G : GENKILL_OPS P E F S).
  Parameter T_gen T_kill : P.t -> E.t -> N.
  Parameter T_init : P.t -> N.
End GENKILL_TIME.

Module Type GENKILL_T (P E : TYPE) (F : KEY_T) (S : SET_T F) :=
  GENKILL_OPS P E F S <+ GENKILL_TIME P E F S.

Module Type GENKILL_MAY_DOMAIN_OPS (F : KEY_OPS) (S : SET_OPS F).
  Include LATTICE_OPS with Definition t := S.t
    with Definition leb := S.subset with Definition bot := S.empty
    with Definition is_bot := fun x => S.subset x S.empty
    with Definition join := S.union.
End GENKILL_MAY_DOMAIN_OPS.

Module Type GENKILL_MUST_DOMAIN_OPS (F : KEY_OPS) (S : SET_OPS F).
  Include LATTICE_OPS with Definition t := option S.t
    with Definition leb := genkill_must_leb S.subset
    with Definition bot := @None S.t
    with Definition is_bot := fun x : option S.t =>
      match x with None => true | Some _ => false end
    with Definition join := genkill_must_join S.inter.
End GENKILL_MUST_DOMAIN_OPS.

Module Type GENKILL_MAY_FLOW_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN_OPS F S).
  Include FLOW_OPS P N E L with Definition dir := G.dir
    with Definition boundary := fun p (_ : N.t) => G.init p
    with Definition transfer := fun p e a => S.union (G.gen p e) (S.diff a (G.kill p e)).
End GENKILL_MAY_FLOW_OPS.

Module Type GENKILL_MUST_FLOW_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN_OPS F S).
  Include FLOW_OPS P N E L with Definition dir := G.dir
    with Definition boundary := fun p (_ : N.t) => Some (G.init p)
    with Definition transfer := fun p e (a : option S.t) => match a with
      | None => None
      | Some facts => Some (S.union (G.gen p e) (S.diff facts (G.kill p e)))
      end.
End GENKILL_MUST_FLOW_OPS.

Module Type GENKILL_MAY_DOMAIN (F : KEY) (S : SET F) :=
  GENKILL_MAY_DOMAIN_OPS F S <+ LATTICE_LAWS.

Module Type GENKILL_MUST_DOMAIN (F : KEY) (S : SET F) :=
  GENKILL_MUST_DOMAIN_OPS F S <+ LATTICE_LAWS.

Module Type GENKILL_MAY_DOMAIN_T (F : KEY_T) (S : SET_T F) :=
  GENKILL_MAY_DOMAIN F S <+ LATTICE_TIME.

Module Type GENKILL_MUST_DOMAIN_T (F : KEY_T) (S : SET_T F) :=
  GENKILL_MUST_DOMAIN F S <+ LATTICE_TIME.

Module Type GENKILL_MAY_FLOW_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MAY_DOMAIN_T F S) :=
  GENKILL_MAY_FLOW_OPS P N E F S G L <+ FLOW_TIME P N E L.

Module Type GENKILL_MUST_FLOW_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MUST_DOMAIN_T F S) :=
  GENKILL_MUST_FLOW_OPS P N E F S G L <+ FLOW_TIME P N E L.

Module Type GENKILL_MAY (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN F S)
    (T : GENKILL_MAY_FLOW_OPS P N E F S G L) := DENSE P N E C L T.

Module Type GENKILL_MUST (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN F S)
    (T : GENKILL_MUST_FLOW_OPS P N E F S G L) := DENSE P N E C L T.

Module Type GENKILL_MAY_T (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_BASE_T P N E)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MAY_DOMAIN_T F S)
    (T : GENKILL_MAY_FLOW_T P N E F S G L) := DENSE_T P N E C L T.

Module Type GENKILL_MUST_T (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_BASE_T P N E)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MUST_DOMAIN_T F S)
    (T : GENKILL_MUST_FLOW_T P N E F S G L) := DENSE_T P N E C L T.

Module Type GENKILL_SOUND (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (ML : GENKILL_MAY_DOMAIN_OPS F S) (UL : GENKILL_MUST_DOMAIN_OPS F S)
    (MT : GENKILL_MAY_FLOW_OPS P N E F S G ML)
    (UT : GENKILL_MUST_FLOW_OPS P N E F S G UL)
    (May : DENSE_SYSTEM P N E C ML MT) (Must : DENSE_SYSTEM P N E C UL UT).
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
  Parameter may_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall n d, produces p n d -> S.mem d (look n) = true.
  (** Every fact generated on an actual boundary path belongs to a may post-solution. *)
  Parameter may_boundary_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall entry path n d, In entry (C.entries p) -> route p entry path n ->
      S.mem d (path_facts p path) = true -> S.mem d (look n) = true.
  (** A reached must post-solution contains facts present on every boundary path. *)
  Parameter must_covers : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n facts d, In entry (C.entries p) -> route p entry path n ->
      look n = Some facts -> S.mem d facts = true -> S.mem d (path_facts p path) = true.
  (** A boundary path has a reached must value in every post-solution. *)
  Parameter must_reached : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n, In entry (C.entries p) -> route p entry path n ->
      exists facts, look n = Some facts.
  (** A least may post-solution equals production from empty listed starts and boundaries. *)
  Parameter may_exact : forall p look, C.wf p -> G.may = true -> May.post_solution p look ->
    (forall other, May.post_solution p other -> forall n, S.subset (look n) (other n) = true) ->
    forall n d, In n (C.nodes p) -> (S.mem d (look n) = true <-> produces p n d).
  (** A least reached must post-solution contains exactly the facts on all boundary paths. *)
  Parameter must_exact : forall p look, C.wf p -> G.may = false -> Must.post_solution p look ->
    (forall other, Must.post_solution p other -> forall n,
      genkill_must_leb S.subset (look n) (other n) = true) ->
    forall n facts, In n (C.nodes p) -> look n = Some facts -> forall d,
      S.mem d facts = true <-> forall entry path,
        In entry (C.entries p) -> route p entry path n -> S.mem d (path_facts p path) = true.
End GENKILL_SOUND.
