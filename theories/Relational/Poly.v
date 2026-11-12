(** * Polyhedral placeholders

    These modules provide the polyhedral state interface.
    For example, certificate production returns no certificate.
    Builds on: PolySig. *)
From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig PolySig.
Local Open Scope nat_scope.

Module PolyCode (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X) <: POLY_OPS X L F C.
  Definition t := reach (list (lcons X.t)).
  Definition wparam := unit.
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
  Definition fm_elim (_ : X.t) (_ : list (lcons X.t)) : list (tracked X.t) := nil.
  (* STUB-CODE *)
  Definition entail_cert (_ : list (lcons X.t)) (_ : lcons X.t) : option cert := None.
End PolyCode.

Module Poly (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) <: POLY X L N F C.
  Include PolyCode X L F C.
  Definition wrank (_ : wparam) (_ : t) : nat := 0.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached P => Forall (sat v) P end.
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted.
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted.
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted.
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted.
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof. Admitted.
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof. Admitted.
  Lemma ngamma_top : forall v, ngamma top v.
  Proof. Admitted.
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted.
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted.
  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof. Admitted.
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof. Admitted.
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof. Admitted.
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof. Admitted.
End Poly.

Module PolyT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: POLY_ALL X L N F C.
  Include Poly X L N F C.
  Definition size (_ : t) : nat := 0.
  Definition wsize (_ : wparam) : nat := 0.
  Definition assign_work (_ : X.t) (_ : term L.op X.t) (_ : t) : nat := 0.
  Definition havoc_work (_ : X.t) (_ : t) : nat := 0.
  Definition assume_work (_ : L.guard) (_ : list (term L.op X.t)) (_ : t) : nat := 0.
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
  TimeFun fm_elim.
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
  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (P : list (lcons X.t)) : nat := length P + length (vars_of P).
  Definition ell (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) +
    fold_right Nat.max 0 (map C.row_key_bits P).
  Definition c_poly : N := 1. (* STUB *)
  Lemma T_fm_elim_le : forall x P,
    (T_fm_elim x P <= c_poly * N.of_nat (((length P + 1)^2)%nat) *
      N.of_nat ((n P + length P + 1)%nat) * N.of_nat (((ell P + 1)^2)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_entail_cert_le : forall P c,
    (T_entail_cert P c <= c_poly *
      N.of_nat (fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1)
        (ell P + C.row_bits c + C.row_key_bits c)))%N.
  Proof. Admitted. (* STUB *)
  Lemma fm_step_mults : forall P x r, In r (fm_elim x P) ->
    exists s, C.combine P (mults_of r) = Some s /\ lrel s = lrel (row_of r) /\
      rhs s = rhs (row_of r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (row_of r)).
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof. Admitted. (* STUB *)
  Lemma fm_complete_Q : forall P c, lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof. Admitted. (* STUB *)
  Lemma fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
  Proof. Admitted. (* STUB *)
  Lemma ell_fm_le : forall x P,
    ell (map row_of (fm_elim x P)) <= 2 * ell P + 1.
  Proof. Admitted. (* STUB *)
  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof. Admitted. (* STUB *)
  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition keep (_ : list (lcons X.t)) (_ : lcons X.t) : bool := false.
  TimeFun keep.
  Definition entails (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.
  Lemma F_leb_keep : forall a b, leb (Reached b) (Reached a) = forallb (keep b) a.
  Proof. Admitted. (* STUB *)
  Lemma F_widen_keep : forall p a b,
    widen p (Reached a) (Reached b) = Reached (filter (keep b) a).
  Proof. Admitted. (* STUB *)
  Lemma F_leb_split : forall a b, leb (Reached a) (Reached b) =
    forallb (fun r => match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end) b.
  Proof. Admitted. (* STUB *)
End PolyT.
