(** * Modular counting statement check

    These definitions count failures of modular affine tests.
    For example, a zero modulus produces a zero sum.
    Builds on: AnalysesScev and BitsWord. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Bits Require Import BitsWord.
From Galois.Analyses Require Import AnalysesScev.

(** * Counting definitions and proposition types *)

Definition audit_floor_sum_reference (n modulus multiplier offset : N) : N :=
  snd (N.iter n (fun state =>
    let '(index, total) := state in
    (N.succ index, (total + (multiplier * index + offset) / modulus)%N))
    (0%N, 0%N)).

Record audit_floor_state : Type := AuditFloorState {
  audit_floor_n : N;
  audit_floor_m : N;
  audit_floor_a : N;
  audit_floor_b : N;
  audit_floor_acc : N;
  audit_floor_done : bool;
  audit_floor_updates : N
}.

Definition audit_floor_step (st : audit_floor_state) : audit_floor_state :=
  if audit_floor_done st then st else
  let n := audit_floor_n st in
  let m := audit_floor_m st in
  let a := audit_floor_a st in
  let b := audit_floor_b st in
  let ar := (a mod m)%N in
  let br := (b mod m)%N in
  let acc := (audit_floor_acc st + (n * N.pred n / 2) * (a / m) + n * (b / m))%N in
  let y := (ar * n + br)%N in
  if (y <? m)%N then AuditFloorState n m ar br acc true (N.succ (audit_floor_updates st))
  else AuditFloorState (y / m)%N ar m (y mod m)%N acc false (N.succ (audit_floor_updates st)).

Definition audit_floor_sum_counted (n m a b : N) : N * N * bool :=
  if (m =? 0)%N then (0%N, 0%N, false)
  else
    let final := N.iter (2 * N.size m + 1)%N audit_floor_step
      (AuditFloorState n m a b 0%N false 0%N) in
    (audit_floor_acc final, audit_floor_updates final, audit_floor_done final).

Definition audit_floor_state_bits (st : audit_floor_state) : N :=
  (N.size (audit_floor_n st) + N.size (audit_floor_m st) +
   N.size (audit_floor_a st) + N.size (audit_floor_b st) +
   N.size (audit_floor_acc st))%N.

Definition audit_floor_sum_fast (n m a b : N) : N :=
  let '(sum, _, _) := audit_floor_sum_counted n m a b in sum.

Definition audit_count_ge (floor_sum : N -> N -> N -> N -> N)
    (n modulus multiplier offset threshold : N) : N :=
  (floor_sum n modulus multiplier (offset + modulus - threshold) -
    floor_sum n modulus multiplier offset)%N.

Definition scev_mod_count (w : width) (sg : signedness) (cmp : cmp_kind)
    (a step bound : Z) (n : N) : N :=
  let word_mod := N.pos (word_period w) in
  let shift :=
    match sg with
    Unsigned =>
      0%Z
    | Signed =>
      (modulus w / 2)%Z
    end in
  let start := Z.to_N (wrap w (a + shift)) in
  let target := Z.to_N (wrap w (bound + shift)) in
  let delta := Z.to_N (wrap w step) in
  let ge k := audit_count_ge audit_floor_sum_fast n word_mod delta start k in
  match cmp with
  | CmpLt => ge target
  | CmpLe => ge (N.succ target)
  | CmpNe => (ge target - ge (N.succ target))%N
  end.

Definition audit_failed_indices (w : width) (sg : signedness) (cmp : cmp_kind)
    (a step bound : Z) (limit : N) (indices : list N) : Prop :=
  NoDup indices /\
  forall k, In k indices <->
    (k < limit)%N /\ affine_test w sg cmp a step bound k = false.

(** The count equals the number of distinct failed indices. *)
Definition scev_mod_count_exact_type : Prop := forall w sg cmp a step bound limit,
  exists indices, audit_failed_indices w sg cmp a step bound limit indices /\
    scev_mod_count w sg cmp a step bound limit = N.of_nat (length indices).

(** The fast floor sum agrees with the independent reference for positive moduli. *)
Definition audit_floor_sum_fast_correct_type : Prop := forall n m a b, (0 < m)%N ->
  audit_floor_sum_fast n m a b = audit_floor_sum_reference n m a b.

(** The counted iteration finishes within its binary fuel bound. *)
Definition audit_floor_sum_terminates_type : Prop := forall n m a b, (0 < m)%N ->
  let '(_, steps, done) := audit_floor_sum_counted n m a b in
  done = true /\ (steps <= 2 * N.size m + 1)%N.

(** Every iterated floor state satisfies the stated live-bit bound. *)
Definition audit_floor_live_bits_type : Prop := forall n m a b k, (0 < m)%N ->
  (audit_floor_state_bits
    (N.iter k audit_floor_step (AuditFloorState n m a b 0%N false 0%N)) <=
    10 * (N.size n + N.size m + N.size a + N.size b + 1))%N.

(** A zero modulus takes the explicitly specified zero-result branch. *)
Definition audit_floor_sum_zero_type : Prop := forall n a b,
  audit_floor_sum_fast n 0 a b = 0%N.
