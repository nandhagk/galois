(** * Linear equality states

    Karr states represent affine equalities and check producer results with certificates.
    For example, havoc removes the equalities that constrain its selected variable.
    Builds on: EnvSig, NumStateSig and LinCertSig. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig.

Local Open Scope nat_scope.

Module Type KARR_OPS (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X).
  Include NUM_STATE_OPS X L F
    with Definition t := reach (list (lcons X.t)) with Definition wparam := nat.
  Parameter subst : X.t -> lin X.t -> lcons X.t -> lcons X.t.
  Parameter affine_hull : list (lcons X.t) -> list (lcons X.t) -> list (lcons X.t).
  Parameter entail_cert : list (lcons X.t) -> lcons X.t -> option cert.
End KARR_OPS.

Module Type KARR_BASE (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  KARR_OPS X L F C <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type KARR_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) (Import D : KARR_BASE X L N F C).
  (** Reached equality systems denote their simultaneous integer solutions. *)
  Parameter ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  (** Unreachable equality systems have no solution. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End KARR_LAWS.

Module Type KARR (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  KARR_BASE X L N F C <+ KARR_LAWS X L N F C.

Module Type KARR_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : KARR X L N F C).
  Include NUM_STATE_TIME X L N F D.
  Definition normal (P : list (lcons X.t)) : Prop :=
    Forall (fun r => NoDup (map fst (lhs r))) P.
  Definition normal_s (s : t) : Prop :=
    match s with Unreached => True | Reached P => normal P end.

  Definition rows_of (s : t) : list (lcons X.t) :=
    match s with Unreached => nil | Reached P => P end.
  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (s : t) : nat := length (rows_of s) + length (vars_of (rows_of s)).
  Definition ell (s : t) : nat :=
    fold_right Nat.max 0 (map C.row_bits (rows_of s)) +
    fold_right Nat.max 0 (map C.row_key_bits (rows_of s)).
  Parameter T_subst : X.t -> lin X.t -> lcons X.t -> N.
  Parameter T_affine_hull : list (lcons X.t) -> list (lcons X.t) -> N.
  Parameter T_entail_cert : list (lcons X.t) -> lcons X.t -> N.
  Parameter c_karr : N.
  Definition ellB (dim bits : nat) : nat := dim * (bits + Nat.log2 dim + 1).
  Definition elimination_work (a b : t) : nat :=
    (n a + n b + 1)^3 * (ellB (n a + n b + 1) (ell a + ell b) + 1)^2.
  (** Substitution charges both coefficient lists and their arithmetic widths. *)
  Parameter T_subst_le : forall x f r,
    (T_subst x f r <= c_karr * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  (** Affine hull uses the same elimination work as join. *)
  Parameter T_affine_hull_le : forall a b, normal a -> normal b ->
    (T_affine_hull a b <= c_karr * N.of_nat
      (elimination_work (Reached a) (Reached b)))%N.
  (** Certificate production includes the conclusion in its elimination input. *)
  Parameter T_entail_cert_le : forall P r, normal P -> normal (r :: nil) ->
    (T_entail_cert P r <= c_karr * N.of_nat
      (elimination_work (Reached P) (Reached (r :: nil))))%N.
  (** Join charges cubic fraction-free elimination at the Hadamard bit bound. *)
  Parameter T_join_karr_le : forall a b, normal_s a -> normal_s b ->
    (T_join a b <= c_karr * N.of_nat (((n a + n b + 1)^3)%nat) *
    N.of_nat (((ellB (n a + n b + 1) (ell a + ell b) + 1)^2)%nat))%N.
End KARR_TIME.

Module Type KARR_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  KARR X L N F C <+ KARR_TIME X L N F C.

Module Type KARR_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : KARR_T X L N F C).
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (rows_of s)).
  Definition nell (s : t) : nat := ell s + Nat.log2 (terms s) + 1.
  Parameter k_cert : N.
  (** The hull has at most one row per input dimension within the Hadamard bound. *)
  Parameter affine_hull_size : forall a b, normal a -> normal b ->
    length (affine_hull a b) <= n (Reached a) + n (Reached b) /\
    ell (Reached (affine_hull a b)) <=
      ellB (n (Reached a) + n (Reached b) + 1) (ell (Reached a) + ell (Reached b)).
  (** A produced certificate costs no more to check than to produce. *)
  Parameter entail_cert_size : forall P r k, normal P -> normal (r :: nil) ->
    entail_cert P r = Some k ->
    (N.of_nat (C.csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize r + C.cbits P (mults k) + 1)) <=
      k_cert * N.of_nat (elimination_work (Reached P) (Reached (r :: nil))))%N.
  (** Assignment charges row normalization and elimination after linearization. *)
  Parameter F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + X.bits x + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
  (** Havoc charges row normalization and elimination of the selected variable. *)
  Parameter F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  (** Assumption charges row normalization and elimination with the new rows. *)
  Parameter F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) = N.of_nat (terms s * (nell s + 1) +
      (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
        (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
          (nell s + F.bits_es g es) + 1)^2) + F.T_atoms_of g es)%N.
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
  Definition in_span (P : list (lcons X.t)) (r : lcons X.t) : Prop :=
    In r P \/
    exists ms s sc, C.combine P ms = Some s /\ lrel s = REq /\ (0 < sc)%Z /\
      (forall v : X.t -> Z, eval_coef v (lhs s) = (sc * eval_coef v (lhs r))%Z) /\
      match lrel r with
      | REq => rhs s = (sc * rhs r)%Z
      | RLe => (rhs s <= sc * rhs r)%Z
      end.
  (** Join emits equality rows. *)
  Parameter join_eq : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (fun r => lrel r = REq) P.

  (** Rank counts the old equality rows. *)
  Parameter wrank_rows : forall p P, wrank p (Reached P) = length P.
  (** Join emits independent rows. *)
  Parameter join_independent : forall a b P, join (Reached a) (Reached b) = Reached P ->
    forall i r, nth_error P i = Some r -> ~ in_span (firstn i P ++ skipn (S i) P) r.
  (** Certificates decide span inclusion on raw equality systems. *)
  Parameter leb_complete_span : forall a b,
    Forall (in_span a) b -> leb (Reached a) (Reached b) = true.
  Definition false_row : lcons X.t := LCons X.t nil REq 1%Z.
  (** Successful inclusion gives span inclusion or an infeasible left system. *)
  Parameter leb_sound_span : forall a b, leb (Reached a) (Reached b) = true ->
    Forall (in_span a) b \/ in_span a false_row.
  (** An infeasible equality system is below every equality system. *)
  Parameter leb_false : forall a b, in_span a false_row -> leb (Reached a) (Reached b) = true.
  (** Join rows lie in both input spans. *)
  Parameter join_span : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (in_span a) P /\ Forall (in_span b) P.
  (** Span certificates compose through an intermediate equality system. *)
  Parameter span_trans : forall a b c, Forall (in_span a) b -> Forall (in_span b) c ->
    Forall (in_span a) c.
  Definition echelon (P : list (lcons X.t)) : Prop :=
    Forall (fun r => lrel r = REq) P /\
    (forall i r, nth_error P i = Some r -> exists x a, In (x, a) (lhs r) /\ a <> 0%Z /\
      forall j s, nth_error P j = Some s -> i <> j ->
        forall b, In (x, b) (lhs s) -> b = 0%Z).
  (* spec: bareiss_entries input_minors *)
  Parameter bareiss_entries input_minors : list (lcons X.t) -> list Z.
  (** Substitution agrees with a concrete update. *)
  Parameter subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  (** Echelon systems decide rational inclusion completely. *)
  Parameter leb_complete_Q : forall a b, echelon a ->
    (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) ->
    leb (Reached a) (Reached b) = true.
  (** Every fraction-free intermediate entry is an input minor. *)
  Parameter bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  (** Widening uses affine hull join. *)
  Parameter widen_join : forall p a b, widen p a b = if leb b a then a else join a b.
  (** Every successful entailment certificate is accepted. *)
  Parameter entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  (** State size charges all stored numeric data. *)
  Parameter k_karr : N.
  Definition mu (s : t) : nat := terms s + n s + nell s.
  Definition lat (m : nat) : nat :=
    (m + 2) * ((m + 1)^3 * (ellB (m + 1) m + 1)^2 + m^2 + 1).
  (** State size is lattice work at twice the state measure. *)
  Parameter F_size : forall s, size s = lat (2 * mu s).
  (** Lattice work on two states fits their sizes. *)
  Parameter lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  (** Leb charges lattice work on both states. *)
  Parameter T1_leb : forall a b,
    (T_leb a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  (** Join charges lattice work on both states. *)
  Parameter T1_join : forall a b,
    (T_join a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  (** Widen charges lattice work on both states. *)
  Parameter T1_widen : forall p a b,
    (T_widen p a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  (** Narrow charges lattice work on both states. *)
  Parameter T1_narrow : forall a b,
    (T_narrow a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  (** A range endpoint fits its declared work. *)
  Parameter F_range_bits : forall e s, range_bits e s = range_work e s.
  (** Range work charges the numeric query and its linearization. *)
  Parameter F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat (terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
End KARR_PLAN.

Module Type KARR_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  KARR_T X L N F C <+ KARR_PLAN X L N F C.
