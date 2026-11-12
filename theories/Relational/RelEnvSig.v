(** * Relational and value-state composition

    Relational environments intersect a numeric state with a value state.
    For example, a relational upper bound refines the interval returned by evaluation.
    Builds on: NumStateSig, StateSig and ValueSig. *)

From Stdlib Require Import NArith List.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Relational Require Import LinearizeSig NumStateSig.

Module Type REL_RANGE_REFINE_OPS (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L).
  Parameter refine_range : bnd -> bnd -> V.t -> V.t.
End REL_RANGE_REFINE_OPS.

Module Type REL_RANGE_REFINE_T (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L).
  Include RANGE_REFINE L N V.
  Parameter T_refine_range : bnd -> bnd -> V.t -> N.
End REL_RANGE_REFINE_T.

Module Type REL_ENV_OPS (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (F : LINEARIZE_OPS X L) (R : NUM_STATE_OPS X L F) (E : STATE_DOMAIN_OPS X L V)
    (RR : REL_RANGE_REFINE_OPS L V)
    (P : LATTICE_OPS with Definition t := (R.t * E.t)%type).
  Include STATE_DOMAIN_OPS X L V with Definition t := (R.t * E.t)%type
    with Definition leb := P.leb with Definition bot := P.bot
    with Definition is_bot := P.is_bot with Definition join := P.join
    with Definition wparam := (R.wparam * E.wparam)%type.
End REL_ENV_OPS.

Module Type REL_ENV (X : KEY) (L : LANG) (N : NUM_VIEW L) (V : VALUE_DOMAIN L)
    (F : LINEARIZE X L N) (R : NUM_STATE X L N F) (E : STATE_DOMAIN X L V)
    (RR : RANGE_REFINE L N V)
    (P : LATTICE with Definition t := (R.t * E.t)%type) :=
  REL_ENV_OPS X L V F R E RR P <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type REL_ENV_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type)
    (Import D : REL_ENV X L N V F R E RR P).
  Include STATE_DOMAIN_TIME X L V D.
  Parameter c_rel_env : N.
  (** Evaluation charges the numeric query, value evaluation and actual range refinement. *)
  Parameter T_eval_components : forall e r s, (T_eval e (r, s) <= c_rel_env *
    (R.T_range e r + E.T_eval e s +
      RR.T_refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s) + 1))%N.
  (** Assignment charges both component updates. *)
  Parameter T_assign_components : forall x e r s, (T_assign x e (r, s) <=
    c_rel_env * (R.T_assign x e r + E.T_assign x e s + 1))%N.
  (** Havoc charges both component updates. *)
  Parameter T_havoc_components : forall x r s, (T_havoc x (r, s) <=
    c_rel_env * (R.T_havoc x r + E.T_havoc x s + 1))%N.
  (** Assumption charges both component updates. *)
  Parameter T_assume_components : forall g es r s, (T_assume g es (r, s) <=
    c_rel_env * (R.T_assume g es r + E.T_assume g es s + 1))%N.
End REL_ENV_TIME.

Module Type REL_ENV_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type) :=
  REL_ENV X L N V F R E RR P <+ REL_ENV_TIME X L N V F R E RR P.

Module Type REL_ENV_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type)
    (Import D : REL_ENV_T X L N V F R E RR P).
  (** Composition denotes the intersection of numeric and value-state meanings. *)
  Parameter F1_gamma : forall r s st,
    gamma (r, s) st <-> R.ngamma r (fun x => N.num (st x)) /\ E.gamma s st.
  (** Evaluation refines the value result by the numeric range of the same expression. *)
  Parameter F2_eval : forall e r s, eval e (r, s) =
    RR.refine_range (fst (R.range e r)) (snd (R.range e r)) (E.eval e s).
  (** Assignment updates both components. *)
  Parameter F3_assign : forall x e r s, assign x e (r, s) = (R.assign x e r, E.assign x e s).
  (** Havoc updates both components. *)
  Parameter F4_havoc : forall x r s, havoc x (r, s) = (R.havoc x r, E.havoc x s).
  (** Assumption updates both components. *)
  Parameter F5_assume : forall g es r s, assume g es (r, s) = (R.assume g es r, E.assume g es s).
  (** Product widening applies the corresponding parameter to each component. *)
  Parameter F6_widen : forall p r s r' s', widen p (r, s) (r', s') =
    if is_bot (r', s') then (r, s)
    else (R.widen (fst p) r r', E.widen (snd p) s s').
  (** Product rank adds the ranks of the actual two components. *)
  Parameter F7_rank : forall p r s,
    wrank p (r, s) = R.wrank (fst p) r + E.wrank (snd p) s.
  (** Product state storage adds component storage. *)
  Parameter F8_size : forall r s, size (r, s) = R.size r + E.size s.
  (* SIG-QUESTION: P shares the pair carrier but does not pin the product operations.
     An unrelated P can choose nonbottom components for P.bot, or reverse P.leb,
     invalidating gamma_bot or gamma_mono under F1_gamma. Operation correspondence
     with the actual shared product instance is required before freezing. *)
  (* SIG-QUESTION: A numeric state lacks full LATTICE_T contracts, including T_join_le.
     The shared product parameter P needs a certified numeric lattice capability before
     the standard product time proof can be instantiated. No F1 law is assumed implicitly. *)
End REL_ENV_PLAN.

Module Type REL_ENV_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) (V : VALUE_DOMAIN_T L)
    (F : LINEARIZE_T X L N) (R : NUM_STATE_T X L N F) (E : STATE_DOMAIN_T X L V)
    (RR : REL_RANGE_REFINE_T L N V)
    (P : LATTICE_T with Definition t := (R.t * E.t)%type) :=
  REL_ENV_T X L N V F R E RR P <+ REL_ENV_PLAN X L N V F R E RR P.
