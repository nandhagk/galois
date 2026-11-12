(** * Congruence payload code

    Congruences describe residues of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: CongruenceSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import CongruenceSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module CongruenceCode (L : WORD_LANGUAGE_OPS) <: CONGRUENCE_OPS L.
  Definition p := congr.
  Definition wordb w z := (0 <=? z) && (z <? modulus w).
  Definition congr_norm w c :=
    match c with
    | CBot => CBot
    | C m r =>
      let m' := Z.abs m in
      if m' =? 0 then if wordb w r then C 0 r else CBot else
        let r' := r mod m' in
        if modulus w <=? m' then if wordb w r' then C 0 r' else CBot
        else C m' r'
    end.
  Definition raw_leb a b :=
    match a, b with
    | CBot, _ => true
    | _, CBot => false
    | C m r, C n s => (m mod n =? 0) && ((r - s) mod n =? 0)
    end.
  Definition pleb w a b := raw_leb (congr_norm w a) (congr_norm w b).
  Definition pjoin w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, c => c
    | c, CBot => c
    | C m r, C n s => congr_norm w (C (Z.gcd (Z.gcd m n) (r - s)) r)
    end.
  Definition pmeet w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C n s =>
      if r mod Z.gcd m n =? s mod Z.gcd m n then
        congr_norm w (C (Z.lcm m n) (Z.combinecong m n r s))
      else CBot
    end.
  Definition pbot (_ : positive) := CBot.
  Definition ptop (_ : positive) := C 1 0.
  Definition pis_bot w a := match congr_norm w a with CBot => true | _ => false end.
  Definition pconst w z := C 0 (L.wrap w z).
  Definition ppoint w a :=
    match congr_norm w a with C 0 r => Some r | _ => None end.
  Definition pwparam := unit.
  Definition pwiden (_ : pwparam) w a b :=
    if pleb w b a then a else pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
  Definition wrap_class w m r := congr_norm w (C (Z.gcd m (modulus w)) r).
  Definition congr_neg w a :=
    match congr_norm w a with CBot => CBot | C m r => wrap_class w m (-r) end.
  Definition congr_add w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r + s)
    | _, _ => CBot
    end.
  Definition congr_sub w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd m n) (r - s)
    | _, _ => CBot
    end.
  Definition congr_mul w a b :=
    match congr_norm w a, congr_norm w b with
    | C m r, C n s => wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
    | _, _ => CBot
    end.
  Definition congr_project source target a :=
    match congr_norm source a with CBot => CBot | C m r => wrap_class target m r end.
  Definition congr_shl w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 k =>
      if Zpos w <=? k then C 0 0 else wrap_class w (m * 2 ^ k) (r * 2 ^ k)
    | _, _ => C 1 0
    end.
  Definition congr_urem w a b :=
    match congr_norm w a, congr_norm w b with
    | CBot, _ | _, CBot => CBot
    | C m r, C 0 c => congr_norm w (C (Z.gcd m c) r)
    | _, _ => C 1 0
    end.
End CongruenceCode.

Module CongruenceTableCode (L : WORD_LANGUAGE_OPS) (D : CONGRUENCE_OPS L)
    <: WORD_TABLE_OPS L D.
  Definition wfwd o rw (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | bvneg, [(w, a)] =>
      Some (if Pos.eqb w rw then D.congr_neg rw a else D.ptop rw)
    | bvzext _, [(w, a)] =>
      Some (if Pos.leb w rw then D.congr_norm rw a else D.ptop rw)
    | bvtrunc _, [(w, a)] => Some (D.congr_project w rw a)
    | (bvadd | bvsub | bvmul | bvshl | bvurem), [(wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then
        match o with
        | bvadd => D.congr_add rw a b
        | bvsub => D.congr_sub rw a b
        | bvmul => D.congr_mul rw a b
        | bvshl => D.congr_shl rw a b
        | _ => D.congr_urem rw a b
        end else D.ptop rw)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (if Pos.eqb wa rw && Pos.eqb wb rw then D.pjoin rw a b else D.ptop rw)
    | _, _ => None
    end.
  Definition wbwd (_ : L.op) (_ : positive) (_ : D.p)
      (_ : list (positive * D.p)) : option (list D.p) := None.
End CongruenceTableCode.

Module Congruence (L : WORD_LANGUAGE) <: CONGRUENCE L.
  Include CongruenceCode L.
  Include CONGRUENCE_SPEC L.
  Definition pgamma := congr_gamma.
  Definition pwrank (_ : pwparam) (w : positive) (a : p) : nat := congr_wrank w a.
  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_raw_leb_refl was not found in the current *)
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_raw_leb_trans was not found in the current *)
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof.
  intro w. intro a. reflexivity.

  Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_join_upper was not found in the current environment. *)
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_join_upper was not found in the current environment. *)
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted. (* CONVERT: cong_meet_lower_left: The variable cong_norm_idempotent was not found. *)
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted. (* CONVERT: cong_gamma_monotone: The variable cong_norm_gamma was not found. *)
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
intros w z H. exact H.

  Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. Admitted. (* CONVERT: cong_top_sound: In environment *)
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* CONVERT: cong_meet_sound: The variable cong_norm_gamma was not found. *)
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted. (* CONVERT: cong_shape_laws: Expects a disjunctive pattern with 3 branches. *)
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
intros. split; [apply wrap_is_word|]. rewrite Z.sub_diag. reflexivity.

  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* CONVERT: cong_shape_laws: Expects a disjunctive pattern with 3 branches. *)
End Congruence.

Module CongruenceTable (L : WORD_LANGUAGE) (W : CONGRUENCE L) <: CONGRUENCE_TABLE L W.
  Include CongruenceTableCode L W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* CONVERT: cong_table_laws: No product even after head-reduction. *)
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. intros o rw q wps ys cs z Hf. discriminate Hf. Qed.
End CongruenceTable.
