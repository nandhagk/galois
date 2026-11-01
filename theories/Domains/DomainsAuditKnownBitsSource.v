(** * Complete classic known-bit forward source equations

    This file expands every legacy forward branch, including variable shifts and raw list scans.
    For example, an empty first operand still evaluates every later strict emptiness test.
    Builds on: DomainPrimitive, BitsFun and DomainsKnownBits. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsKnownBits.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
Import List.ListNotations.

Definition kb_mark {A} (body : domain_run A) : domain_run A := domain_case 500 [] body.

Definition kb_unary (site : nat) (f : Z -> Z) (z : Z) : domain_run Z :=
  (f z, [AuditArithmetic site [count_zencode z]]).

Definition kb_half (w : width) : domain_run Z :=
  index <- domain_z DzSub (Z.pos w) 1 ;; domain_z DzPow 2 index.

Definition kb_signed (w : width) (z : Z) : domain_run Z := kb_mark (
  value <- domain_wrap w z ;;
  half_value <- kb_half w ;;
  positive <- domain_compare true value half_value ;;
  if positive then (value, []) else m <- domain_modulus w ;; domain_z DzSub value m).

Definition kb_msb (w : width) (z : Z) : domain_run bool :=
  value <- domain_wrap w z ;;
  index <- domain_z DzSub (Z.pos w) 1 ;; domain_testbit value index.

Definition kb_wctz (w : width) (z : Z) : domain_run Z := kb_mark (
  value <- domain_wrap w z ;;
  zero <- domain_equal value 0 ;;
  if zero then (Z.pos w, []) else
    first <- domain_wrap w z ;;
    second <- domain_wrap w z ;;
    negated <- domain_z DzSub 0 second ;;
    isolated <- domain_z DzAnd first negated ;; kb_unary 501 Z.log2 isolated).

Definition kb_wrotl (w : width) (z amount : Z) : domain_run Z :=
  wrapped_amount <- domain_wrap w amount ;;
  k <- domain_z DzMod wrapped_amount (Z.pos w) ;;
  first <- domain_wrap w z ;;
  power <- domain_z DzPow 2 k ;;
  shifted <- domain_z DzMul first power ;;
  second <- domain_wrap w z ;;
  complement <- domain_z DzSub (Z.pos w) k ;;
  divisor <- domain_z DzPow 2 complement ;;
  rest <- domain_z DzDiv second divisor ;;
  joined <- domain_z DzAdd shifted rest ;; domain_wrap w joined.

Definition kb_word_shift (o : op) (w : width) (z amount : Z) : domain_run Z := kb_mark (
  match o with
  | bvshl => domain_wshl w z amount
  | bvlshr =>
    first_amount <- domain_wrap w amount ;;
    oversized <- domain_compare false (Z.pos w) first_amount ;;
    if oversized then (0%Z, []) else
      value <- domain_wrap w z ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;; domain_z DzDiv value power
  | bvashr =>
    first_amount <- domain_wrap w amount ;;
    oversized <- domain_compare false (Z.pos w) first_amount ;;
    if oversized then
      negative <- kb_msb w z ;;
      if negative then m <- domain_modulus w ;; domain_z DzSub m 1 else (0%Z, [])
    else
      value <- kb_signed w z ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;;
      quotient <- domain_z DzDiv value power ;; domain_wrap w quotient
  | bvrotl => kb_wrotl w z amount
  | bvrotr =>
    wrapped <- domain_wrap w amount ;;
    reduced <- domain_z DzMod wrapped (Z.pos w) ;;
    complement <- domain_z DzSub (Z.pos w) reduced ;; kb_wrotl w z complement
  | _ => domain_wrap w z
  end).

Definition kb_scalar_value (o : op) (w : width) (amount z : Z) : domain_run Z := kb_mark (
  match o with
  | bvshl | bvlshr | bvashr =>
    reduced <- domain_z DzMin amount (Z.pos w) ;; kb_word_shift o w z reduced
  | bvrotl => reduced <- domain_z DzMod amount (Z.pos w) ;; kb_wrotl w z reduced
  | bvrotr =>
    negative <- domain_z DzSub 0 amount ;;
    reduced <- domain_z DzMod negative (Z.pos w) ;; kb_wrotl w z reduced
  | _ => domain_wrap w z
  end).

(** An internal map callback executes independently at both actual endpoints. *)
Definition kb_map (sw rw : width) (f : Z -> domain_run Z) (a : tnum) : domain_run tnum :=
  upper <- domain_max sw a ;;
  first <- f upper ;;
  z <- domain_wnot rw first ;;
  lower <- domain_min sw a ;;
  second <- f lower ;;
  o <- domain_wrap rw second ;; domain_tnum z o.

Definition kb_scalar o w amount a := kb_map w w (kb_scalar_value o w amount) a.

Definition kb_not (w : width) (a : tnum) : domain_run tnum := kb_mark (
  z <- domain_wrap w (ones a) ;;
  o <- domain_wrap w (zeros a) ;; domain_tnum z o).

Definition kb_bitop (o : op) (w : width) (a b : tnum) : domain_run tnum := kb_mark (
  match o with
  | bvand =>
    z <- domain_word_bits DzOr w (zeros a) (zeros b) ;;
    v <- domain_word_bits DzAnd w (ones a) (ones b) ;; domain_tnum z v
  | bvor =>
    z <- domain_word_bits DzAnd w (zeros a) (zeros b) ;;
    v <- domain_word_bits DzOr w (ones a) (ones b) ;; domain_tnum z v
  | _ =>
    zz <- domain_word_bits DzAnd w (zeros a) (zeros b) ;;
    oo <- domain_word_bits DzAnd w (ones a) (ones b) ;;
    z <- domain_word_bits DzOr w zz oo ;;
    zo <- domain_word_bits DzAnd w (zeros a) (ones b) ;;
    oz <- domain_word_bits DzAnd w (ones a) (zeros b) ;;
    v <- domain_word_bits DzOr w zo oz ;; domain_tnum z v
  end).

Definition kb_constant (w : width) (a : tnum) : domain_run (option Z) := kb_mark (
  first <- domain_wrap w (zeros a) ;;
  second <- domain_wnot w (ones a) ;;
  equal <- domain_equal first second ;;
  if equal then value <- domain_min w a ;; domain_return 502 [] (Some value)
  else domain_return 502 [] None).

Definition kb_sub (w : width) (a b : tnum) : domain_run tnum :=
  opposite <- kb_not w b ;; domain_adc w a opposite true.

Definition kb_trailing (w : width) (a : tnum) : domain_run Z :=
  possible <- domain_wnot w (zeros a) ;; kb_wctz w possible.

Definition kb_classic_mul (w : width) (a b : tnum) : domain_run tnum := kb_mark (
  first <- kb_constant w a ;;
  match first with
  | Some x => second <- kb_constant w b ;; match second with
    | Some y =>
    product <- domain_z DzMul x y ;;
    word <- domain_wrap w product ;; domain_const w word
    | None =>
    ta <- kb_trailing w a ;;
    tb <- kb_trailing w b ;;
    trailing <- domain_z DzAdd ta tb ;;
    mask <- kb_unary 503 Z.ones trailing ;;
    z <- domain_wrap w mask ;; domain_tnum z 0
    end
  | None =>
    ta <- kb_trailing w a ;;
    tb <- kb_trailing w b ;;
    trailing <- domain_z DzAdd ta tb ;;
    mask <- kb_unary 503 Z.ones trailing ;;
    z <- domain_wrap w mask ;; domain_tnum z 0
  end).

Definition kb_bitlen (h : Z) : domain_run Z := kb_mark (
  zero <- domain_equal h 0 ;;
  if zero then (0%Z, []) else
    logarithm <- kb_unary 501 Z.log2 h ;; domain_z DzAdd logarithm 1).

Definition kb_upper (w : width) (h : Z) : domain_run tnum :=
  bits <- kb_bitlen h ;;
  mask <- kb_unary 503 Z.ones bits ;;
  z <- domain_wnot w mask ;; domain_tnum z 0.

Definition kb_stride o (w : width) d : domain_run Z := kb_mark (
  doubled <- domain_z DzMul 2 d ;;
  if tnum_rotation o then domain_z DzMod doubled (Z.pos w) else (doubled, [])).

(** The actual binary mask chooses each recursion, shift, join and normalized stride. *)
Fixpoint kb_expand o w (fuel : positive) (distance : Z) (current : tnum) : domain_run tnum :=
  kb_mark (match fuel with
  | xH => shifted <- kb_scalar o w distance current ;; domain_tnum_bits DzAnd w current shifted
  | xO rest => next <- kb_stride o w distance ;; kb_expand o w rest next current
  | xI rest =>
    next <- kb_stride o w distance ;;
    shifted <- kb_scalar o w distance current ;;
    joined <- domain_tnum_bits DzAnd w current shifted ;; kb_expand o w rest next joined
  end).

Definition kb_expand_mask o w (mask : Z) current : domain_run tnum := kb_mark (
  match mask with
  | Zpos fuel => kb_expand o w fuel 1 current
  | _ => domain_normalise w current
  end).

Definition kb_variable_raw o w (a b : tnum) : domain_run tnum := kb_mark (
  base <- domain_min w b ;;
  mask <- domain_mask w b ;;
  current <- kb_scalar o w base a ;;
  if tnum_rotation o then kb_expand_mask o w mask current else
    before <- domain_z DzSub (Z.pos w) 1 ;;
    cutoff_bits <- kb_bitlen before ;;
    cutoff <- domain_z DzPow 2 cutoff_bits ;;
    low_mask <- domain_z DzMod mask cutoff ;;
    low <- kb_expand_mask o w low_mask current ;;
    small <- domain_compare true mask cutoff ;;
    if small then (low, []) else
      oversized <- kb_scalar o w (Z.pos w) a ;; domain_tnum_bits DzAnd w low oversized).

Definition kb_variable o w (a b : tnum) : domain_run tnum := kb_mark (
  first <- domain_empty w a ;;
  second <- domain_empty w b ;;
  if first || second then domain_bottom w else kb_variable_raw o w a b).

Definition kb_order (strict : bool) w (a b : tnum) : domain_run tnum := kb_mark (
  upper_a <- domain_max w a ;;
  lower_b <- domain_min w b ;;
  first <- domain_compare strict upper_a lower_b ;;
  if first then domain_const 1%positive 1 else
    upper_b <- domain_max w b ;;
    lower_a <- domain_min w a ;;
    second <- domain_compare (negb strict) upper_b lower_a ;;
    if second then domain_const 1%positive 0 else domain_tnum 0 0).

Definition kb_equal w (a b : tnum) : domain_run tnum := kb_mark (
  meet <- domain_tnum_bits DzOr w a b ;;
  empty <- domain_empty w meet ;;
  if empty then domain_const 1%positive 0 else
    first <- kb_constant w a ;;
    match first with
    | Some x => second <- kb_constant w b ;; match second with
      | Some y => equal <- domain_equal x y ;;
      domain_const 1%positive (if equal then 1 else 0)
      | None => domain_tnum 0 0
      end
    | None => domain_tnum 0 0
    end).

Definition kb_bias w a : domain_run tnum :=
  sign <- kb_half w ;;
  constant <- domain_const w sign ;; kb_bitop bvxor w a constant.

Definition kb_compare o w a b : domain_run tnum := kb_mark (
  match o with
  | bveq => kb_equal w a b
  | bvne => equal <- kb_equal w a b ;; kb_not 1%positive equal
  | bvult => kb_order true w a b
  | bvule => kb_order false w a b
  | bvslt | bvsle =>
    first <- kb_bias w a ;;
    second <- kb_bias w b ;;
    kb_order (match o with bvslt => true | _ => false end) w first second
  | _ => domain_tnum 0 0
  end).

Definition kb_concat (w v : width) (a b : tnum) : domain_run tnum := kb_mark (
  first <- domain_wrap w (zeros a) ;;
  m1 <- domain_modulus v ;;
  scaled1 <- domain_z DzMul first m1 ;;
  second <- domain_wrap v (zeros b) ;;
  sum1 <- domain_z DzAdd scaled1 second ;;
  let target1 := Pos.add w v in
  z <- domain_wrap target1 sum1 ;;
  third <- domain_wrap w (ones a) ;;
  m2 <- domain_modulus v ;;
  scaled2 <- domain_z DzMul third m2 ;;
  fourth <- domain_wrap v (ones b) ;;
  sum2 <- domain_z DzAdd scaled2 fourth ;;
  let target2 := Pos.add w v in
  value <- domain_wrap target2 sum2 ;;
  let '(out, body) := domain_tnum z value in
  (out, AuditArithmetic 504 [N.pos w; N.pos v] ::
    AuditArithmetic 504 [N.pos w; N.pos v] :: body)).

Definition kb_unary_map o sw rw a : domain_run tnum := kb_mark (
  match o with
  | bvzext _ | bvtrunc _ => kb_map sw rw (domain_wrap rw) a
  | bvsext _ => kb_map sw rw (fun z => value <- kb_signed sw z ;; domain_wrap rw value) a
  | bvextract _ lo => kb_map sw rw (fun z =>
    let amount := Z.of_nat lo in
    let prefix := [AuditArithmetic 505 [N.of_nat lo]] in
    let '(out, body) := power <- domain_z DzPow 2 amount ;;
      quotient <- domain_z DzDiv z power ;; domain_wrap rw quotient in
    (out, prefix ++ body)) a
  | _ => domain_tnum 0 0
  end).

(** Every legacy raw forward constructor retains its native malformed-list behavior. *)
Definition kb_forward_raw_source o (args : list (width * tnum)) rw : domain_run tnum := kb_mark (
  match o, args with
  | bvnot, [(_, a)] => kb_not rw a
  | bvneg, [(_, a)] => zero <- domain_const rw 0 ;; kb_sub rw zero a
  | (bvclz | bvctz | bvpopcnt), [_] => kb_upper rw (Z.pos rw)
  | bvadd, [(_, a); (_, b)] => domain_adc rw a b false
  | bvsub, [(_, a); (_, b)] => kb_sub rw a b
  | bvmul, [(_, a); (_, b)] => kb_classic_mul rw a b
  | bvudiv, [(_, a); (_, b)] =>
    divisor <- domain_wrap rw (ones b) ;;
    zero <- domain_equal divisor 0 ;;
    if zero then domain_tnum 0 0 else upper <- domain_max rw a ;; kb_upper rw upper
  | bvurem, [(_, a); _] => upper <- domain_max rw a ;; kb_upper rw upper
  | bvsrem, [(_, a); _] =>
    sign <- kb_half rw ;;
    clear <- domain_word_bits DzAnd rw (zeros a) sign ;; domain_tnum clear 0
  | (bvand | bvor | bvxor), [(_, a); (_, b)] => kb_bitop o rw a b
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] => kb_variable o rw a b
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] => kb_compare o w a b
  | bvite, [(_, condition); (_, a); (_, b)] =>
    constant <- kb_constant 1%positive condition ;;
    match constant with
    | None => domain_tnum_bits DzAnd rw a b
    | Some value => equal <- domain_equal value 1 ;;
      domain_normalise rw (if equal then a else b)
    end
  | (bvzext _ | bvtrunc _ | bvsext _ | bvextract _ _), [(w, a)] => kb_unary_map o w rw a
  | bvconcat, [(w, a); (v, b)] => kb_concat w v a b
  | _, _ => domain_tnum 0 0
  end).

(** Strict existsb evaluates the complete recursive tail even when the head is empty. *)
Fixpoint kb_any_empty_source (args : list (width * tnum)) : domain_run bool := kb_mark (
  match args with
  | [] => (false, [])
  | (w, a) :: rest =>
    first <- domain_empty w a ;;
    later <- kb_any_empty_source rest ;;
    (first || later, [AuditCase 506 [if first then 1%N else 0%N; if later then 1%N else 0%N]])
  end).

Definition kb_forward_source o args rw : domain_run tnum := kb_mark (
  empty <- kb_any_empty_source args ;;
  if empty then domain_bottom rw else kb_forward_raw_source o args rw).

Definition kb_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditCase 500 _ => 100%nat
  | AuditArithmetic 501 [z] => S (audit_z_bits (count_zdecode z))
  | AuditArithmetic 503 [z] => audit_shift_weight 1 (count_zdecode z)
  | AuditArithmetic 504 [a; b] => audit_binary_weight (Z.of_N a) (Z.of_N b)
  | AuditArithmetic 505 [lo] => S (N.to_nat lo)
  | _ => domain_frame_weight event
  end.

Definition kb_source_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (kb_frame_weight event + total)%nat) 0%nat events.

(** Complete erasure covers every operator, raw sign/mask case and malformed operand list. *)
Definition kb_forward_source_erases_type : Prop := forall o args rw,
  fst (kb_forward_source o args rw) = tnum_forward o args rw.

(** The strict scan visits all input entries independently of where emptiness is first found. *)
Definition kb_empty_scan_source_count_type : Prop := forall args,
  (length args <= audit_case_count 500 (snd (kb_any_empty_source args)))%nat.
