(** * Two-step value reduction interfaces

    Reductions exchange facts between two abstractions of the same concrete word.
    For example, an interval can discard endpoints outside a congruence class.
    Builds on: ProductSig and ValueSig. *)

From Stdlib Require Import NArith.
From Argent Require Import BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig BitsLang.

Module Type REDUCTION_STEPS_OPS (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L).
  Include REDUCER_OPS A B.
  Parameter to_left : A.t * B.t -> A.t * B.t.
  Parameter to_right : A.t * B.t -> A.t * B.t.
End REDUCTION_STEPS_OPS.

Module Type REDUCTION_STEPS_LAWS (L : LANG) (A B : VALUE_DOMAIN L)
    (Import R : REDUCTION_STEPS_OPS L A B).
  (** One exchange to the left leaves the right component unchanged. *)
  Parameter left_frame : forall x, snd (to_left x) = snd x.
  (** One exchange to the right leaves the left component unchanged. *)
  Parameter right_frame : forall x, fst (to_right x) = fst x.
  (** The first exchange retains every value shared by the input pair. *)
  Parameter left_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_left (a, b))) c.
  (** The second exchange retains every value shared by the input pair. *)
  Parameter right_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    B.gamma (snd (to_right (a, b))) c.
  (** The first exchange refines the left component. *)
  Parameter left_lower : forall a b, A.leb (fst (to_left (a, b))) a = true.
  (** The second exchange refines the right component. *)
  Parameter right_lower : forall a b, B.leb (snd (to_right (a, b))) b = true.
  (** A reduction performs the two exchanges in order. *)
  Parameter reduce_steps : forall x, reduce x = to_right (to_left x).
End REDUCTION_STEPS_LAWS.

Module Type REDUCTION_STEPS (L : LANG) (A B : VALUE_DOMAIN L) :=
  REDUCTION_STEPS_OPS L A B <+ REDUCER_LAWS A B <+ VALUE_REDUCER_SOUND L A B <+
  REDUCTION_STEPS_LAWS L A B.

Module Type REDUCTION_STEPS_TIME (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import R : REDUCTION_STEPS L A B).
  Include VALUE_REDUCER_TIME L A B R.
  Parameter T_to_left T_to_right : A.t * B.t -> N.
  Parameter c_exchange : N.
  (** The left exchange charges both component sizes. *)
  Parameter T_to_left_le : forall a b, (T_to_left (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** The right exchange charges both component sizes. *)
  Parameter T_to_right_le : forall a b, (T_to_right (a, b) <=
    c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** The first exchange has linearly bounded output storage. *)
  Parameter left_size : forall a b,
    (N.of_nat (A.size (fst (to_left (a, b))) + B.size b) <=
      c_exchange * N.of_nat (A.size a + B.size b + 1))%N.
  (** Reduction has the published combined-size asymptotic budget. *)
  Parameter reduce_bigO : bigO (fun _ => True)
    (fun x => N.of_nat (A.size (fst x) + B.size (snd x) + 1)) T_reduce.
End REDUCTION_STEPS_TIME.

Module Type REDUCTION_STEPS_T (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  REDUCTION_STEPS L A B <+ REDUCTION_STEPS_TIME L A B.

Module Type REDUCTION_STEPS_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import R : REDUCTION_STEPS_T L A B).
  Parameter k_exchange : N.
  (** The two exchange soundness laws compose into reduction soundness. *)
  Parameter F1_steps_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (to_right (to_left (a, b)))) c /\
    B.gamma (snd (to_right (to_left (a, b)))) c.
  (** The two reductive exchange laws compose into componentwise descent. *)
  Parameter F2_steps_lower : forall a b,
    A.leb (fst (to_right (to_left (a, b)))) a = true /\
    B.leb (snd (to_right (to_left (a, b)))) b = true.
  (** Reduction charges each exchange at the actual intermediate value. *)
  Parameter T1_steps : forall x, (T_reduce x <= k_exchange *
    (T_to_left x + T_to_right (to_left x) + 1))%N.
End REDUCTION_STEPS_PLAN.

Module Type REDUCTION_STEPS_ALL (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  REDUCTION_STEPS_T L A B <+ REDUCTION_STEPS_PLAN L A B.

(** WrappedBits exposes the two directional exchange obligations for word values. *)
Module Type WRAPPED_BITS_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type WRAPPED_BITS (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type WRAPPED_BITS_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type WRAPPED_BITS_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : WRAPPED_BITS_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type WRAPPED_BITS_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

(** IntervalCongr exposes the two directional exchange obligations for word values. *)
Module Type INTERVAL_CONGR_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type INTERVAL_CONGR (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type INTERVAL_CONGR_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type INTERVAL_CONGR_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : INTERVAL_CONGR_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type INTERVAL_CONGR_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

(** IntervalBits exposes the two directional exchange obligations for word values. *)
Module Type INTERVAL_BITS_OPS (A B : VALUE_DOMAIN_OPS BitsLangCode) :=
  REDUCTION_STEPS_OPS BitsLangCode A B.
Module Type INTERVAL_BITS (A B : VALUE_DOMAIN BitsLang) := REDUCTION_STEPS BitsLang A B.
Module Type INTERVAL_BITS_T (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_T BitsLangT A B.
Module Type INTERVAL_BITS_PLAN (A B : VALUE_DOMAIN_T BitsLangT)
    (R : INTERVAL_BITS_T A B) := REDUCTION_STEPS_PLAN BitsLangT A B R.
Module Type INTERVAL_BITS_ALL (A B : VALUE_DOMAIN_T BitsLangT) :=
  REDUCTION_STEPS_ALL BitsLangT A B.

(* SIG-QUESTION: These soundness and descent interfaces permit identity exchanges.
   The numerical equations for the CAV bit hull/common prefix, Granger inward residue
   rounding/singleton propagation and IntervalBits exchange are still prose in the design.
   Their representation-pinned precision contracts require an F2 decision. *)
