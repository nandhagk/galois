(** * Certified polyhedral states

    Polyhedra check Fourier-Motzkin producer results before using them as constraints.
    For example, widening keeps old constraints certified by the new state.
    Builds on: EnvSig, NumStateSig and LinCertSig. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig.

Local Open Scope nat_scope.

Record tracked (X : Type) := Tracked {
  row_of : lcons X;
  mults_of : list Z
}.

Arguments row_of {X} _.
Arguments mults_of {X} _.
TimeFun row_of.
TimeFun mults_of.

(** Fourier-Motzkin work keeps the original dimension in every elimination charge. *)
Fixpoint fmcost (dim mlen fuel rows bits : nat) : nat :=
  match fuel with
  | 0 => (rows + 1) * (dim + mlen + 1) * (bits + 1)
  | S k => (rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
      fmcost dim mlen k (rows^2 / 4 + rows) (2 * bits + 1)
  end.


Module Type POLY_OPS (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X).
  Include NUM_STATE_OPS X L F
    with Definition t := reach (list (lcons X.t))
    with Definition wparam := unit.
  Parameter subst : X.t -> lin X.t -> lcons X.t -> lcons X.t.
  Parameter fm_elim : X.t -> list (lcons X.t) -> list (tracked X.t).
  Parameter entail_cert : list (lcons X.t) -> lcons X.t -> option cert.
End POLY_OPS.

Module Type POLY_BASE (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  POLY_OPS X L F C <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type POLY_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) (Import D : POLY_BASE X L N F C).
  (** Reached polyhedra denote simultaneous integer solutions of their constraints. *)
  Parameter ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  (** Unreachable polyhedra have no integer solution. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End POLY_LAWS.

Module Type POLY (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  POLY_BASE X L N F C <+ POLY_LAWS X L N F C.

Module Type POLY_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : POLY X L N F C).
  Include NUM_STATE_TIME X L N F D.
  Definition normal (P : list (lcons X.t)) : Prop :=
    Forall (fun r => NoDup (map fst (lhs r))) P.
  Definition normal_s (s : t) : Prop :=
    match s with Unreached => True | Reached P => normal P end.

  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (P : list (lcons X.t)) : nat := length P + length (vars_of P).
  Definition ell (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) +
    fold_right Nat.max 0 (map C.row_key_bits P).
  Parameter T_subst : X.t -> lin X.t -> lcons X.t -> N.
  Parameter T_fm_elim : X.t -> list (lcons X.t) -> N.
  Parameter T_entail_cert : list (lcons X.t) -> lcons X.t -> N.
  Parameter c_poly : N.
  (** One elimination charges all row pairs and their tracked multipliers. *)
  Parameter T_fm_elim_le : forall x P, normal P ->
    (T_fm_elim x P <= c_poly * N.of_nat (((length P + 1)^2)%nat) *
      N.of_nat ((n P + length P + 1)%nat) * N.of_nat (((ell P + 1)^2)%nat))%N.
  (** Certificate production follows the full Fourier-Motzkin recurrence. *)
  Parameter T_entail_cert_le : forall P c, normal P -> normal (c :: nil) ->
    (T_entail_cert P c <= c_poly *
      N.of_nat (fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1)
        (ell P + C.row_bits c + C.row_key_bits c)))%N.
End POLY_TIME.

Module Type POLY_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  POLY X L N F C <+ POLY_TIME X L N F C.

Module Type POLY_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : POLY_T X L N F C).
  Definition prows (s : t) : list (lcons X.t) :=
    match s with Unreached => nil | Reached P => P end.
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (prows s)).
  Definition nell (s : t) : nat := ell (prows s) + Nat.log2 (terms s) + 1.
  (** Assignment charges row normalization and one elimination after linearization. *)
  Parameter F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (length (prows s) + 3)^2 *
      (n (prows s) + tsize e + length (prows s) + 3) *
      (nell s + X.bits x + F.bits_e e + 1)^2) + F.T_lin_of e)%N.
  (** Havoc charges row normalization and one elimination of the selected variable. *)
  Parameter F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (length (prows s) + 1)^2 * (n (prows s) + length (prows s) + 1) *
      (nell s + X.bits x + 1)^2.
  (** Assumption charges appending the rows emitted by linearization. *)
  Parameter F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat ((length (prows s) + 1) * (fold_right Nat.add 0%nat (map tsize es) + 1) *
        (F.bits_es g es + 1)) + F.T_atoms_of g es)%N.
  (** Top has no repeated coefficients. *)
  Parameter normal_top : normal_s top.
  (** Join keeps rows free of repeated keys. *)
  Parameter normal_join : forall a b, normal_s a -> normal_s b -> normal_s (join a b).
  (** Widening keeps rows free of repeated keys. *)
  Parameter normal_widen : forall p a b,
    normal_s a -> normal_s b -> normal_s (widen p a b).
  (** Narrowing keeps rows free of repeated keys. *)
  Parameter normal_narrow : forall a b, normal_s a -> normal_s b -> normal_s (narrow a b).
  (** Assignment normalizes its new rows. *)
  Parameter normal_assign : forall x e s, normal_s s -> normal_s (assign x e s).
  (** Havoc keeps rows free of repeated keys. *)
  Parameter normal_havoc : forall x s, normal_s s -> normal_s (havoc x s).
  (** Assumption normalizes the rows it adds. *)
  Parameter normal_assume : forall g es s, normal_s s -> normal_s (assume g es s).
  (** This widening has no repeated threshold search. *)
  Parameter F_wunits : forall s, wunits s = 0.
  (** Every produced row equals its tracked linear combination. *)
  Parameter fm_step_mults : forall P x r, In r (fm_elim x P) ->
    exists s, C.combine P (mults_of r) = Some s /\ lrel s = lrel (row_of r) /\
      rhs s = rhs (row_of r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (row_of r)).
  (** Successful certificates pass the independent checker. *)
  Parameter entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  (** Generated entailment certificates use rationally valid combinations. *)
  Parameter entail_cert_nocut : forall P c k, entail_cert P c = Some k -> cut k = false.
  (** Elimination keeps rows free of repeated keys. *)
  Parameter normal_fm_elim : forall x P, normal P -> normal (map row_of (fm_elim x P)).
  (** Failure to find an entailment certificate yields a rational countermodel. *)
  Parameter fm_complete_Q : forall P c, lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  (** Elimination keeps at most all opposite-sign pairs and the zero rows. *)
  Parameter fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
  (** One elimination at most doubles entry bit lengths plus a carry. *)
  Parameter ell_fm_le : forall x P, normal P ->
    ell (map row_of (fm_elim x P)) <= 2 * ell P + 1.
  (** Substitution agrees with updating the interpreted variable. *)
  Parameter subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  (** Widening rank counts the constraints that can still be dropped. *)
  Parameter wrank_rows : forall p P, wrank p (Reached P) = length P.
  Parameter keep : list (lcons X.t) -> lcons X.t -> bool.
  Definition entails (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.
  (** Inclusion and widening use the same certified keep test. *)
  Parameter F_leb_keep : forall a b, leb (Reached b) (Reached a) = forallb (keep b) a.
  (** Widening filters old constraints without adding thresholds or duplicates. *)
  Parameter F_widen_keep : forall p a b,
    widen p (Reached a) (Reached b) = Reached (filter (keep b) a).
  (** Equality inclusion checks the two inequality directions. *)
  Parameter F_leb_split : forall a b, leb (Reached a) (Reached b) =
    forallb (fun r => match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end) b.
End POLY_PLAN.

Module Type POLY_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  POLY_T X L N F C <+ POLY_PLAN X L N F C.
