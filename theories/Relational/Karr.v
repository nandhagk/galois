(** * Linear equality placeholders

    These modules provide the linear equality state interface.
    For example, certificate production returns no certificate.
    Builds on: KarrSig. *)
From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig KarrSig.
Local Open Scope nat_scope.

Module KarrCode (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X) <: KARR_OPS X L F C.
  Definition t := reach (list (lcons X.t)).
  Definition wparam := nat.
  (* STUB-CODE *)
  Definition leb (_ _ : t) := false.
  (* STUB-CODE *)
  Definition bot : t := Unreached.
  (* STUB-CODE *)
  Definition is_bot (_ : t) := false.
  (* STUB-CODE *)
  Definition join (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition top : t := Reached nil.
  (* STUB-CODE *)
  Definition meet (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition widen (_ : wparam) (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition narrow (_ _ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition assign (_ : X.t) (_ : term L.op X.t) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition havoc (_ : X.t) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition assume (_ : L.guard) (_ : list (term L.op X.t)) (_ : t) : t := Unreached.
  (* STUB-CODE *)
  Definition range (_ : term L.op X.t) (_ : t) : bnd * bnd := (NegInf, PosInf).
  (* STUB-CODE *)
  Definition subst (_ : X.t) (_ : lin X.t) (r : lcons X.t) := r.
  (* STUB-CODE *)
  Definition affine_hull (_ _ : list (lcons X.t)) : list (lcons X.t) := nil.
  (* STUB-CODE *)
  Definition entail_cert (_ : list (lcons X.t)) (_ : lcons X.t) : option cert := None.
End KarrCode.

Module Karr (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) <: KARR X L N F C.
  Include KarrCode X L F C.
  Definition wrank (_ : wparam) (_ : t) : nat := 0.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached P => Forall (sat v) P end.
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof. Admitted. (* STUB *)
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof. Admitted. (* STUB *)
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof. Admitted. (* STUB *)
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof. Admitted. (* STUB *)
End Karr.

Module KarrT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: KARR_ALL X L N F C.
  Include Karr X L N F C.
  Definition size (_ : t) : nat := 0.
  Definition wsize (_ : wparam) : nat := 0.
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
  Definition ellB (dim bits : nat) : nat := dim * (bits + Nat.log2 dim + 1).
  Definition elimination_work (a b : t) : nat :=
    (n a + n b + 1)^3 * (ellB (n a + n b + 1) (ell a + ell b) + 1)^2.
  Definition wunits (_ : t) : nat := 0.
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (rows_of s)).
  Definition nell (s : t) : nat := ell s + Nat.log2 (terms s) + 1.
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + X.bits x + F.bits_e e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    terms s * (nell s + 1) + (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
      (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
        (nell s + F.bits_es g es) + 1)^2 + N.to_nat (F.T_atoms_of g es).
  Definition range_work (_ : term L.op X.t) (_ : t) : nat := 0.
  TimeFun bot.
  TimeFun top.
  TimeFun meet.
  TimeFun leb.
  TimeFun join.
  TimeFun is_bot.
  TimeFun widen.
  TimeFun narrow.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun range.
  TimeFun subst.
  TimeFun affine_hull.
  TimeFun entail_cert.
  Definition c_num : N := 1. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_num * N.of_nat (size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_num * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat ((range_work e s + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Definition c_karr : N := 1. (* STUB *)
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_karr * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_affine_hull_le : forall a b, normal a -> normal b ->
    (T_affine_hull a b <= c_karr * N.of_nat
      (elimination_work (Reached a) (Reached b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_entail_cert_le : forall P r, normal P -> normal (r :: nil) ->
    (T_entail_cert P r <= c_karr * N.of_nat
      (elimination_work (Reached P) (Reached (r :: nil))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_karr_le : forall a b, normal_s a -> normal_s b ->
    (T_join a b <= c_karr * N.of_nat (((n a + n b + 1)^3)%nat) *
    N.of_nat (((ellB (n a + n b + 1) (ell a + ell b) + 1)^2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Assignment charges row normalization and elimination after linearization. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + X.bits x + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  (** Havoc charges row normalization and elimination of the selected variable. *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  Proof. Admitted. (* STUB *)
  (** Assumption charges row normalization and elimination with the new rows. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) = N.of_nat (terms s * (nell s + 1) +
      (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
        (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
          (nell s + F.bits_es g es) + 1)^2) + F.T_atoms_of g es)%N.
  Proof. Admitted. (* STUB *)
  (** Top has no repeated coefficients. *)
  Lemma normal_top : normal_s top.
  Proof. Admitted. (* STUB *)
  (** Join keeps rows free of repeated keys. *)
  Lemma normal_join : forall a b, normal_s a -> normal_s b -> normal_s (join a b).
  Proof. Admitted. (* STUB *)
  (** Widening keeps rows free of repeated keys. *)
  Lemma normal_widen : forall p a b,
    normal_s a -> normal_s b -> normal_s (widen p a b).
  Proof. Admitted. (* STUB *)
  (** Narrowing keeps rows free of repeated keys. *)
  Lemma normal_narrow : forall a b, normal_s a -> normal_s b -> normal_s (narrow a b).
  Proof. Admitted. (* STUB *)
  (** Assignment normalizes its new rows. *)
  Lemma normal_assign : forall x e s, normal_s s -> normal_s (assign x e s).
  Proof. Admitted. (* STUB *)
  (** Havoc keeps rows free of repeated keys. *)
  Lemma normal_havoc : forall x s, normal_s s -> normal_s (havoc x s).
  Proof. Admitted. (* STUB *)
  (** Assumption normalizes the rows it adds. *)
  Lemma normal_assume : forall g es s, normal_s s -> normal_s (assume g es s).
  Proof. Admitted. (* STUB *)
  (** This widening has no repeated threshold search. *)
  Lemma F_wunits : forall s, wunits s = 0.
  Proof. Admitted. (* STUB *)
  Definition in_span (P : list (lcons X.t)) (r : lcons X.t) : Prop :=
    exists ms s sc, C.combine P ms = Some s /\ lrel s = REq /\ (0 < sc)%Z /\
      (forall v : X.t -> Z, eval_coef v (lhs s) = (sc * eval_coef v (lhs r))%Z) /\
      rhs s = (sc * rhs r)%Z.
  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof. Admitted. (* STUB *)
  Lemma join_independent : forall a b P, join (Reached a) (Reached b) = Reached P ->
    forall i r, nth_error P i = Some r -> ~ in_span (firstn i P ++ skipn (S i) P) r.
  Proof. Admitted. (* STUB *)
  Lemma leb_complete_span : forall a b,
    Forall (in_span a) b -> leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Definition false_row : lcons X.t := LCons X.t nil REq 1%Z.
  (** Successful inclusion gives span inclusion or an infeasible left system. *)
  Lemma leb_sound_span : forall a b, leb (Reached a) (Reached b) = true ->
    Forall (in_span a) b \/ in_span a false_row.
  Proof. Admitted. (* STUB *)
  (** An infeasible equality system is below every equality system. *)
  Lemma leb_false : forall a b, in_span a false_row -> leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_span : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (in_span a) P /\ Forall (in_span b) P.
  Proof. Admitted. (* STUB *)
  Lemma span_trans : forall a b c, Forall (in_span a) b -> Forall (in_span b) c ->
    Forall (in_span a) c.
  Proof. Admitted. (* STUB *)
  Definition echelon (P : list (lcons X.t)) : Prop :=
    Forall (fun r => lrel r = REq) P /\
    (forall i r, nth_error P i = Some r -> exists x a, In (x, a) (lhs r) /\ a <> 0%Z /\
      forall j s, nth_error P j = Some s -> i <> j ->
        forall b, In (x, b) (lhs s) -> b = 0%Z).
  (* STUB-CODE *)
  Definition bareiss_entries (_ : list (lcons X.t)) : list Z := nil.
  (* STUB-CODE *)
  Definition input_minors (_ : list (lcons X.t)) : list Z := nil.
  TimeFun bareiss_entries.
  TimeFun input_minors.
  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof. Admitted. (* STUB *)
  Lemma leb_complete_Q : forall a b, echelon a ->
    (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) ->
    leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Lemma bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  Proof. Admitted. (* STUB *)
  Lemma widen_join : forall p a b, widen p a b = join a b.
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof. Admitted. (* STUB *)
End KarrT.
