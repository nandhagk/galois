(** * Congruence payload code

    Congruences describe residues of normalized words.
    For example, modulus two and residue zero describe even words.
    Builds on: CongruenceSig and the fixed-width word operations. *)

From Stdlib Require Import ZArith List Bool Wellfounded.Inverse_Image.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import CongruenceSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Record congr_crt_state : Type := {
  crt_r1 : Z;
  crt_u1 : Z;
  crt_v1 : Z;
  crt_r2 : Z;
  crt_u2 : Z;
  crt_v2 : Z
}.

TimeFun crt_r1.
TimeFun crt_u1.
TimeFun crt_v1.
TimeFun crt_r2.
TimeFun crt_u2.
TimeFun crt_v2.

Module Z.
  TimeFun Z.sgn.
  TimeFun Z.lcm.
End Z.

Module CongruenceCRT.
  (** Each iteration consumes one aligned quotient bit. *)
  Fixpoint div_scan (bits : nat) (divisor remainder quotient : Z) : Z * Z :=
    match bits with
    | O => (quotient, remainder)
    | S rest =>
      let take := (divisor <=? remainder)%Z in
      div_scan rest (Z.div2 divisor)
        (if take then remainder - divisor else remainder)
        (if take then 2 * quotient + 1 else 2 * quotient)
    end.
  TimeFun div_scan.

  Definition div_aligned (a b : Z) : Z * Z :=
    match a, b with
    | Zneg _, _ | _, Zneg _ | _, Z0 => Z.div_eucl a b
    | _, _ =>
      if (a <? b)%Z then (0, a) else
        let shift := (Z.size_nat a - Z.size_nat b)%nat in
        div_scan (S shift) (Z.shiftl b (Z.of_nat shift)) a 0
    end.
  TimeFun div_aligned.

  Definition k_div : N := 1%N. (* STUB *)
  Definition k_gcd : N := 1%N. (* STUB *)

  (** Aligned division keeps the standard quotient and remainder on its input domain. *)
  Lemma F_div_aligned : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
    div_aligned a b = Z.div_eucl a b.
  Proof. Admitted. (* STUB *)

  (** Division charges one dividend scan per quotient bit. *)
  Lemma T_div_aligned_le : forall a b, (0 <= a)%Z -> (0 < b)%Z ->
    (T_div_aligned a b <= k_div *
      N.of_nat ((Z.size_nat a - Z.size_nat b + 2) * (Z.size_nat a + 1)))%N.
  Proof. Admitted. (* STUB *)

  Definition next (s : congr_crt_state) : congr_crt_state :=
    let q := fst (div_aligned (crt_r2 s) (crt_r1 s)) in
    {| crt_r1 := crt_r2 s - q * crt_r1 s;
       crt_u1 := crt_u2 s - q * crt_u1 s;
       crt_v1 := crt_v2 s - q * crt_v1 s;
       crt_r2 := crt_r1 s;
       crt_u2 := crt_u1 s;
       crt_v2 := crt_v1 s |}.
  TimeFun next.

  Definition lt (s1 s : congr_crt_state) : Prop :=
    (Z.abs_N (crt_r1 s1) < Z.abs_N (crt_r1 s))%N.

  Definition nonnegative_remainders (s : congr_crt_state) : Prop :=
    (0 <= crt_r1 s /\ 0 <= crt_r2 s)%Z.

  (** Absolute-value initialization puts both remainders in the aligned division domain. *)
  Lemma initial_nonnegative : forall a b,
    nonnegative_remainders
      {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
         crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |}.
  Proof. Admitted. (* STUB *)

  (** Every nonterminal reachable step keeps the remainders nonnegative. *)
  Lemma next_nonnegative : forall s, nonnegative_remainders s ->
    (crt_r1 s =? 0) = false -> nonnegative_remainders (next s).
  Proof. Admitted. (* STUB *)

  (** The Euclidean remainder strictly reduces the absolute first remainder. *)
  Lemma next_decreases : forall s, (crt_r1 s =? 0) = false -> lt (next s) s.
  Proof. Admitted. (* STUB *)

  Definition step (s : congr_crt_state) :
      {s1 : congr_crt_state | lt s1 s} + (Z * Z * Z) :=
    (match crt_r1 s =? 0 as doneb return
        (crt_r1 s =? 0) = doneb -> {s1 : congr_crt_state | lt s1 s} + (Z * Z * Z) with
    | true => fun _ => inr (crt_u2 s, crt_v2 s, crt_r2 s)
    | false => fun Hnonzero => inl (exist _ (next s) (next_decreases s Hnonzero))
    end) eq_refl.
  TimeFun step.

  Definition extgcd (a b : Z) : Z * Z * Z :=
    let s := {| crt_r1 := Z.abs a; crt_u1 := Z.sgn a; crt_v1 := 0;
                crt_r2 := Z.abs b; crt_u2 := 0; crt_v2 := Z.sgn b |} in
    loop lt step s
      (Acc_intro_generator 32
        (wf_inverse_image congr_crt_state N N.lt
          (fun st => Z.abs_N (crt_r1 st)) N.lt_wf_0) s).
  TimeFun extgcd.

  (** The full Euclidean coefficient chain has quadratic input-bit work. *)
  Lemma T_extgcd_le : forall a b,
    (T_extgcd a b <= k_gcd *
      N.of_nat ((Z.size_nat a + Z.size_nat b + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)

  (** The state loop returns the exact coefficients chosen by the standard library. *)
  Lemma extgcd_agrees : forall a b, extgcd a b = Z.extgcd a b.
  Proof. Admitted. (* STUB *)

  Definition combinecong (m1 m2 r1 r2 : Z) : Z :=
    let '(u, v, d) := extgcd m1 m2 in
    if r1 mod d =? r2 mod d then
      if d =? 0 then r1
      else (v * m2 * r1 + u * m1 * r2) / d mod Z.abs (m1 * (m2 / d))
    else 0.
  TimeFun combinecong.

  (** The CRT helper keeps the standard library's exact residue, including zero moduli. *)
  Lemma combinecong_agrees : forall m1 m2 r1 r2,
    combinecong m1 m2 r1 r2 = Z.combinecong m1 m2 r1 r2.
  Proof. Admitted. (* STUB *)
End CongruenceCRT.

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
        congr_norm w (C (Z.lcm m n) (CongruenceCRT.combinecong m n r s))
      else CBot
    end.
  Definition pbot (_ : positive) := CBot.
  Definition ptop (_ : positive) := C 1 0.
  Definition pis_bot w a := match congr_norm w a with CBot => true | _ => false end.
  Definition pconst w z := C 0 (Word.wrap w z).
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
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_join_upper was not found in the current environment. *)
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted. (* CONVERT: cong_lattice_laws: The variable cong_join_upper was not found in the current environment. *)
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted. (* STUB *)
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: cong_height: In environment *)
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: cong_height: In environment *)
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted. (* STUB *)
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* CONVERT: cong_top_sound: Unable to unify "?a mod 1 = 0" with "exists z0 : Z, z - 0 = z0 * 1". *)
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* CONVERT: cong_meet_sound: The variable cong_norm_gamma was not found. *)
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted. (* CONVERT: cong_shape_laws: The variable cong_norm_gamma was not found in the current environment. *)
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted. (* STUB *)
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros. split; [apply wrap_is_word|]. rewrite Z.sub_diag. reflexivity.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* CONVERT: cong_shape_laws: Expects a disjunctive pattern with 3 branches. *)
  (** Payload concretization agrees with residue-class membership. *)
  Lemma F1_gamma : forall w a z, pgamma w a z <-> congr_gamma w a z.
  Proof. Admitted. (* STUB *)
  (** Normalization keeps precisely the same represented integers. *)
  Lemma F2_norm_gamma : forall w a z,
    pgamma w (congr_norm w a) z <-> pgamma w a z.
  Proof. Admitted. (* STUB *)
  (** Negation retains wrapped concrete negation. *)
  Lemma F6_congr_neg_sound : forall w a x,
    pgamma w a x -> pgamma w (congr_neg w a) (L.wrap w (- x)).
  Proof. Admitted. (* STUB *)
  (** Addition retains wrapped concrete addition. *)
  Lemma F7_congr_add_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_add w a b) (L.wrap w (x + y)).
  Proof. Admitted. (* STUB *)
  (** Subtraction retains wrapped concrete subtraction. *)
  Lemma F8_congr_sub_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_sub w a b) (L.wrap w (x - y)).
  Proof. Admitted. (* STUB *)
  (** Multiplication retains wrapped concrete multiplication. *)
  Lemma F9_congr_mul_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y -> pgamma w (congr_mul w a b) (L.wrap w (x * y)).
  Proof. Admitted. (* STUB *)
  (** Projection retains truncations to smaller widths. *)
  Lemma F10_congr_project_sound : forall source target a x,
    (target <= source)%positive -> pgamma source a x ->
    pgamma target (congr_project source target a) (L.wrap target x).
  Proof. Admitted. (* STUB *)
  (** Shift transfer retains the wrapped concrete shift. *)
  Lemma F11_congr_shl_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_shl w a b) (L.wrap w (Z.shiftl x y)).
  Proof. Admitted. (* STUB *)
  (** Remainder transfer retains unsigned remainder, including a zero divisor. *)
  Lemma F12_congr_urem_sound : forall w a b x y,
    pgamma w a x -> pgamma w b y ->
    pgamma w (congr_urem w a b) (L.wrap w (Z.modulo x y)).
  Proof. Admitted. (* STUB *)
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

Module CongruenceT (L : WORD_LANGUAGE_T) <: CONGRUENCE_ALL L.
  Include Congruence L.
  Definition div_aligned := CongruenceCRT.div_aligned.
  Definition extgcd := CongruenceCRT.extgcd.
  Definition T_div_aligned := CongruenceCRT.T_div_aligned.
  Definition T_extgcd := CongruenceCRT.T_extgcd.
  Definition k_div := CongruenceCRT.k_div.
  Definition k_gcd := CongruenceCRT.k_gcd.
  Definition F_div_aligned := CongruenceCRT.F_div_aligned.
  Definition extgcd_agrees := CongruenceCRT.extgcd_agrees.
  Definition T_div_aligned_le := CongruenceCRT.T_div_aligned_le.
  Definition T_extgcd_le := CongruenceCRT.T_extgcd_le.
  TimeFun wordb.
  TimeFun congr_norm.
  TimeFun raw_leb.
  TimeFun pleb.
  TimeFun pjoin.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.
  TimeFun wrap_class.
  TimeFun congr_neg.
  TimeFun congr_add.
  TimeFun congr_sub.
  TimeFun congr_mul.
  TimeFun congr_project.
  TimeFun congr_shl.
  TimeFun congr_urem.
  Definition psize (w : positive) (a : p) : nat :=
    (Pos.to_nat w + congr_bits a + 1) ^ 2.
  Definition pwsize (_ : pwparam) : nat := 0.
  Definition c_payload : N := 1%N. (* STUB *)
  Definition c_congruence : N := 1%N. (* STUB *)
  Definition k_congr_gcd : N := 1%N. (* STUB *)
  Definition k_congr_crt : N := 1%N. (* STUB *)
  Definition k_congr_transfer : N := 1%N. (* STUB *)

  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <= c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload narrowing charges both payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload inclusion charges the two payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload join charges the two payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload meet charges the two payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom recognition charges the payload size. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Point recognition charges the payload size. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Constant abstraction charges the width and literal bit size. *)
  Lemma T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Payload size uses the tagged width. *)
  Lemma psize_congr : forall w a, psize w a = ((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat.
  Proof. Admitted. (* STUB *)
  (** Normalized payloads fit two words of the width. *)
  Lemma congr_norm_bits : forall w a,
    (congr_bits (congr_norm w a) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Negation results fit two words of the width. *)
  Lemma congr_neg_bits : forall w a,
    (congr_bits (congr_neg w a) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Binary transfer results fit two words of the width. *)
  Lemma congr_binary_bits : forall w a b,
    (congr_bits (congr_add w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_sub w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_mul w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_shl w a b) <= 2 * Pos.to_nat w /\
     congr_bits (congr_urem w a b) <= 2 * Pos.to_nat w)%nat.
  Proof. Admitted. (* STUB *)
  (** Projection results fit two words of the target width. *)
  Lemma congr_project_bits : forall source target a,
    (congr_bits (congr_project source target a) <= 2 * Pos.to_nat target)%nat.
  Proof. Admitted. (* STUB *)
  (** Normalization has the published quadratic arithmetic bound. *)
  Lemma T_congr_norm_le : forall w a,
    (T_congr_norm w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Negation has the published quadratic arithmetic bound. *)
  Lemma T_congr_neg_le : forall w a,
    (T_congr_neg w a <= c_congruence * N.of_nat (((Pos.to_nat w + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Addition has the published quadratic arithmetic bound. *)
  Lemma T_congr_add_le : forall w a b,
    (T_congr_add w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Subtraction has the published quadratic arithmetic bound. *)
  Lemma T_congr_sub_le : forall w a b,
    (T_congr_sub w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Multiplication has the published quadratic arithmetic bound. *)
  Lemma T_congr_mul_le : forall w a b,
    (T_congr_mul w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Shift transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_shl_le : forall w a b,
    (T_congr_shl w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Remainder transfer has the published quadratic arithmetic bound. *)
  Lemma T_congr_urem_le : forall w a b,
    (T_congr_urem w a b <= c_congruence *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Projection charges both source and target widths. *)
  Lemma T_congr_project_le : forall source target a,
    (T_congr_project source target a <=
    c_congruence * N.of_nat
      (((Pos.to_nat source + Pos.to_nat target + congr_bits a + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Congruence multiplication has the published quadratic width bound. *)
  Lemma mul_bigO : (bigO (fun _ => True)
    (fun x : positive * (congr * congr) => N.of_nat
      (((Pos.to_nat (fst x) + congr_bits (fst (snd x)) + congr_bits (snd (snd x)) + 1) ^ 2)%nat))
    (fun x => T_congr_mul (fst x) (fst (snd x)) (snd (snd x))))%N.
  Proof. Admitted. (* STUB *)
  (** Normalization produces a canonical representation. *)
  Lemma F3_norm_canonical : forall w a, canonical w (congr_norm w a).
  Proof. Admitted. (* STUB *)
  (** Normalization is idempotent. *)
  Lemma F4_norm_idempotent : forall w a,
    congr_norm w (congr_norm w a) = congr_norm w a.
  Proof. Admitted. (* STUB *)
  (** Chinese remainder meet retains each shared integer. *)
  Lemma F5_crt_meet_sound : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* STUB *)
  (** The requested congruence rank is bounded by width plus two. *)
  Lemma F13_wrank_le : forall w a, (congr_wrank w a <= Pos.to_nat w + 2)%nat.
  Proof. Admitted. (* STUB *)
  (** Payload widening uses the normalized congruence rank. *)
  Lemma F14_pwrank : forall q w a, pwrank q w a = congr_wrank w a.
  Proof. Admitted. (* STUB *)
  (** Gcd-based joining has the published quadratic arithmetic bound. *)
  Lemma T1_join : forall w a b,
    (T_pjoin w a b <= k_congr_gcd *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Chinese remainder meet has the published quadratic arithmetic bound. *)
  Lemma T2_meet : forall w a b,
    (T_pmeet w a b <= k_congr_crt *
      N.of_nat (((Pos.to_nat w + congr_bits a + congr_bits b + 1) ^ 2)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** The result stays within its declared work budget. *)
  Lemma T_ptop_le : forall w,
    (T_ptop w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_pbot_le : forall w,
    (T_pbot w <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma ptop_size : forall w,
    (N.of_nat (psize w (ptop w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pbot_size : forall w,
    (N.of_nat (psize w (pbot w)) <= c_payload * N.of_nat ((Pos.to_nat w + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma pconst_size : forall w z,
    (N.of_nat (psize w (pconst w z)) <=
      c_payload * N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
End CongruenceT.

Module CongruenceTableT (L : WORD_LANGUAGE_T) (D : CONGRUENCE_T L)
    <: CONGRUENCE_TABLE_T L D.
  Include CongruenceTable L D.
  TimeFun wfwd.
  TimeFun wbwd.
  Definition c_word_table : N := 1%N. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (D.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** The result stays within its declared work budget. *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => D.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        D.psize rw q +
        fold_right Nat.add 0 (map (fun x => D.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End CongruenceTableT.
