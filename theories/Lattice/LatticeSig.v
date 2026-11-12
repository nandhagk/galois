(** * Lattice signatures

    These layers separate executable orders from laws and time bounds.
    For example, Boolean disjunction supplies a join and false supplies bottom.
    Builds on: Stdlib arithmetic and Argent time interfaces. *)

From Stdlib Require Import Arith NArith Bool.
From Argent Require Import Time.

Module Type LATTICE_OPS.
  Parameter t : Type.
  Parameter leb : t -> t -> bool.
  Parameter bot : t.
  Parameter is_bot : t -> bool.
  Parameter join : t -> t -> t.
End LATTICE_OPS.

Module Type LATTICE_LAWS (Import L : LATTICE_OPS).
  (** Every value is below itself. *)
  Parameter leb_refl  : forall a, leb a a = true.
  (** The order composes through an intermediate value. *)
  Parameter leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  (** Bottom is below every value. *)
  Parameter bot_least : forall a, leb bot a = true.
  (** The bottom test recognizes bottom. *)
  Parameter is_bot_bot : is_bot bot = true.
  (** Every recognized bottom is below every value. *)
  Parameter is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  (** Join is above its left operand. *)
  Parameter join_ub_l : forall a b, leb a (join a b) = true.
  (** Join is above its right operand. *)
  Parameter join_ub_r : forall a b, leb b (join a b) = true.
End LATTICE_LAWS.

Module Type LATTICE := LATTICE_OPS <+ LATTICE_LAWS.

Module Type LATTICE_TIME (Import L : LATTICE_OPS).
  (* spec: size *)
  Parameter size : t -> nat.
  Parameter T_leb : t -> t -> N.
  Parameter T_join : t -> t -> N.
  Parameter T_is_bot : t -> N.
  Parameter c_lat : N.
  (** Order testing takes time bounded by both value sizes. *)
  Parameter T_leb_le  : forall a b, (T_leb a b  <= c_lat * N.of_nat (size a + size b + 1))%N.
  (** Joining takes time bounded by both value sizes. *)
  Parameter T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  (** Bottom testing takes time bounded by the value size. *)
  Parameter T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
End LATTICE_TIME.

Module Type LATTICE_T := LATTICE <+ LATTICE_TIME.

(* extensions; each is a layer over LATTICE_OPS and composes with <+ *)
Module Type HAS_TOP_OPS (Import L : LATTICE_OPS).
  Parameter top : t.
End HAS_TOP_OPS.

Module Type HAS_TOP_LAWS (Import L : LATTICE_OPS) (Import T : HAS_TOP_OPS L).
  (** Top is above every value. *)
  Parameter top_greatest : forall a, leb a top = true.
End HAS_TOP_LAWS.

Module Type HAS_MEET_OPS (Import L : LATTICE_OPS).
  Parameter meet : t -> t -> t.
End HAS_MEET_OPS.

Module Type HAS_MEET_LAWS (Import L : LATTICE_OPS) (Import M : HAS_MEET_OPS L).
  (** Meet is below its left operand. *)
  Parameter meet_lb_l : forall a b, leb (meet a b) a = true.
  (** Meet is below its right operand. *)
  Parameter meet_lb_r : forall a b, leb (meet a b) b = true.
End HAS_MEET_LAWS.

Module Type HAS_MEET_TIME (Import L : LATTICE_T) (Import M : HAS_MEET_OPS L).
  Parameter T_meet : t -> t -> N.
  (** Meeting takes time bounded by both value sizes. *)
  Parameter T_meet_le : forall a b, (T_meet a b <= c_lat * N.of_nat (size a + size b + 1))%N.
End HAS_MEET_TIME.

Module Type WIDENING_OPS (Import L : LATTICE_OPS).
  Parameter wparam : Type.
  Parameter widen : wparam -> t -> t -> t.
  Parameter narrow : t -> t -> t.
End WIDENING_OPS.

Module Type WIDENING_LAWS (Import L : LATTICE_OPS) (Import W : WIDENING_OPS L).
  (* spec: wrank *)
  Parameter wrank : wparam -> t -> nat.
  (** Widening is above its previous value. *)
  Parameter widen_ub_l : forall p a b, leb a (widen p a b) = true.
  (** Widening is above its candidate value. *)
  Parameter widen_ub_r : forall p a b, leb b (widen p a b) = true.
  (** A candidate below the previous value leaves widening unchanged. *)
  Parameter widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Parameter wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  (** Widening from a nonbottom does not increase rank. *)
  Parameter wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Parameter narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
End WIDENING_LAWS.

Module Type WIDENING_TIME (Import L : LATTICE_T) (Import W : WIDENING_OPS L).
  (* spec: wsize *)
  Parameter wsize : wparam -> nat.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter T_narrow : t -> t -> N.
  (** Widening time is bounded by value and parameter sizes. *)
  Parameter T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat (size a + size b + wsize p + 1))%N.
  (** Narrowing time is bounded by both value sizes. *)
  Parameter T_narrow_le : forall a b, (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
End WIDENING_TIME.

Module Type HEIGHT (Import L : LATTICE).
  (* spec: rank height *)
  Parameter rank : t -> nat.
  Parameter height : nat.
  (** Every rank is bounded by the height. *)
  Parameter rank_le : forall a, rank a <= height.
  (** A strict order step increases rank. *)
  Parameter rank_strict : forall a b, leb a b = true -> leb b a = false -> rank a < rank b.
End HEIGHT.

Module Type LUB (Import L : LATTICE).
  (** Join is below every common upper bound. *)
  Parameter join_least : forall a b c, leb a c = true -> leb b c = true -> leb (join a b) c = true.
End LUB.

(* bundles *)
Module Type WLATTICE_OPS := LATTICE_OPS <+ WIDENING_OPS.

Module Type WLATTICE     := WLATTICE_OPS <+ LATTICE_LAWS <+ WIDENING_LAWS.

Module Type WLATTICE_T   := WLATTICE <+ LATTICE_TIME <+ WIDENING_TIME.

Module Type BLATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS <+ HAS_MEET_OPS.

Module Type BLATTICE     := BLATTICE_OPS <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS.

Module Type BLATTICE_T   := BLATTICE <+ LATTICE_TIME <+ HAS_MEET_TIME.

Module Type ALATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS <+ HAS_MEET_OPS <+ WIDENING_OPS.

Module Type ALATTICE := ALATTICE_OPS <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS
  <+ WIDENING_LAWS.

Module Type ALATTICE_T := ALATTICE <+ LATTICE_TIME <+ HAS_MEET_TIME <+ WIDENING_TIME.

Module Type HAS_TOP (L : LATTICE) := HAS_TOP_OPS L <+ HAS_TOP_LAWS L.

Module Type HAS_MEET (L : LATTICE) := HAS_MEET_OPS L <+ HAS_MEET_LAWS L.

Module Type HAS_MEET_T (L : LATTICE_T) := HAS_MEET L <+ HAS_MEET_TIME L.

Module Type WIDENING (L : LATTICE) := WIDENING_OPS L <+ WIDENING_LAWS L.

Module Type WIDENING_T (L : LATTICE_T) := WIDENING L <+ WIDENING_TIME L.

(** * Product reduction *)

Module Type REDUCER_OPS (A B : LATTICE_OPS).
  Parameter reduce : A.t * B.t -> A.t * B.t.
End REDUCER_OPS.

Module Type REDUCER_LAWS (A B : LATTICE) (Import R : REDUCER_OPS A B).
  (** Reduction lowers both components in their respective orders. *)
  Parameter reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
  Parameter reduce_mono : forall a b a' b',
  A.leb a a' = true -> B.leb b b' = true ->
  A.leb (fst (reduce (a, b))) (fst (reduce (a', b'))) = true /\
  B.leb (snd (reduce (a, b))) (snd (reduce (a', b'))) = true.
  Parameter reduce_idem : forall a b,
  A.leb (fst (reduce (a, b))) (fst (reduce (reduce (a, b)))) = true /\
  B.leb (snd (reduce (a, b))) (snd (reduce (reduce (a, b)))) = true.
End REDUCER_LAWS.

Module Type REDUCER (A B : LATTICE) := REDUCER_OPS A B <+ REDUCER_LAWS A B.

(** * Fixed disjunction cap *)

Module Type CAP.
  Parameter k : nat.
End CAP.
