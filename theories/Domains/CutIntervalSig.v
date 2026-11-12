(** * Integer intervals with a fixed endpoint budget

    Every finite endpoint fits a bit budget fixed for the extracted program.
    For example, cutting [0, 256] at eight bits gives [0, positive infinity].
    Builds on: IntervalSig, ThresholdsSig and ValueSig. *)

From Stdlib Require Import ZArith List Bool.
From Argent Require Import Time Std.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig.

Local Open Scope nat_scope.

Module Type INTERVAL_CUTOFF.
  Parameter bits : nat.
End INTERVAL_CUTOFF.

(** Finite endpoints are measured by the magnitude bit length used by raw intervals. *)
Definition cut_endpoint_ok (bits : nat) (b : bnd) : bool :=
  match b with
  | Fin z => Nat.leb (Z.size_nat z) bits
  | _ => true
  end.
TimeFun cut_endpoint_ok.

(** Nonbottom intervals have ordered endpoints and exclude empty infinite bounds. *)
Definition cut_shape_ok (a : itv) : bool :=
  match a with
  | IBot => true
  | I PosInf _ | I _ NegInf => false
  | I (Fin lo) (Fin hi) => Z.leb lo hi
  | _ => true
  end.
TimeFun cut_shape_ok.

(** The Boolean invariant checks shape and each finite endpoint independently. *)
Definition cut_interval_ok (bits : nat) (a : itv) : bool :=
  match a with
  | IBot => true
  | I lo hi => andb (cut_shape_ok a)
      (andb (cut_endpoint_ok bits lo) (cut_endpoint_ok bits hi))
  end.
TimeFun cut_interval_ok.

(** Proofs of the Boolean invariant erase from the executable carrier. *)
Definition cut_itv (bits : nat) : Type := { a : itv | cut_interval_ok bits a = true }.

Definition cut_raw {bits : nat} (a : cut_itv bits) : itv := match a with exist _ raw _ => raw end.
TimeFun cut_raw.

(** An oversized lower endpoint is replaced by negative infinity. *)
Definition cut_lower (bits : nat) (b : bnd) : bnd :=
  if cut_endpoint_ok bits b then b else NegInf.
TimeFun cut_lower.

(** An oversized upper endpoint is replaced by positive infinity. *)
Definition cut_upper (bits : nat) (b : bnd) : bnd :=
  if cut_endpoint_ok bits b then b else PosInf.
TimeFun cut_upper.

(** Empty raw intervals normalize before finite endpoints are cut outward. *)
Definition cut_interval (bits : nat) (a : itv) : itv :=
  if cut_shape_ok a then
    match a with
    | IBot => IBot
    | I lo hi => I (cut_lower bits lo) (cut_upper bits hi)
    end
  else IBot.
TimeFun cut_interval.

Module Type CUT_INTERVAL_OPS (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_OPS).
  Include VALUE_DOMAIN_OPS L with Definition t := cut_itv C.bits
    with Definition wparam := ttree.
  Parameter cut : itv -> cut_itv C.bits.
End CUT_INTERVAL_OPS.

Module Type CUT_INTERVAL_SPEC (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_OPS)
    (Import D : CUT_INTERVAL_OPS C L).
  Definition in_cut (a : t) (z : Z) : Prop :=
    match cut_raw a with
    | IBot => False
    | I lo hi => in_bnd lo hi z
    end.
  Definition endpoint_inv (a : t) : Prop := interval_bits (cut_raw a) <= C.bits.
  Definition operand_bits (xs : list t) : nat :=
    fold_right Nat.add 0 (map (fun a => interval_bits (cut_raw a)) xs).
  Definition transfer_work (o : L.op) (xs : list t) : nat :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2 + C.bits +
      match L.view o with ZConst z => Z.size_nat z | _ => 0 end.
  Definition guard_work (_ : L.guard) (xs : list t) : nat :=
    operand_bits xs + length xs + (operand_bits xs + 1) ^ 2 + C.bits.
End CUT_INTERVAL_SPEC.

Module Type CUT_INTERVAL_LAWS (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE)
    (Import D : CUT_INTERVAL_OPS C L).
  (** Cutting agrees with the total raw normalization and outward projection. *)
  Parameter cut_agrees : forall a, cut_raw (cut a) = cut_interval C.bits a.
  (** Every carrier value has normalized shape and endpoints within the fixed budget. *)
  Parameter carrier_invariant : forall (a : t),
    cut_shape_ok (cut_raw a) = true /\ interval_bits (cut_raw a) <= C.bits.
  (** Cutting an already bounded value keeps its raw representation. *)
  Parameter cut_fixed : forall (a : t), cut_raw (cut (cut_raw a)) = cut_raw a.
  (** Cutting retains every integer represented by the raw interval. *)
  Parameter cut_sound : forall a z,
    (match a with IBot => False | I lo hi => in_bnd lo hi z end) ->
    (match cut_raw (cut a) with IBot => False | I lo hi => in_bnd lo hi z end).
End CUT_INTERVAL_LAWS.

Module Type CUT_INTERVAL (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE) :=
  CUT_INTERVAL_OPS C L <+ CUT_INTERVAL_SPEC C L <+
  LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+ WIDENING_LAWS <+
  VALUE_DOMAIN_LAWS L <+ CUT_INTERVAL_LAWS C L.

Module Type CUT_INTERVAL_TIME (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) (Import D : CUT_INTERVAL C L).
  Include VALUE_DOMAIN_TIME L D.
  Parameter T_cut : itv -> N.
  Parameter c_cut : N.
  (** The cutoff pays for shape comparisons and endpoint bit scans. *)
  Parameter T_cut_le : forall a,
    (T_cut a <= c_cut * N.of_nat (interval_bits a + C.bits + 1))%N.
  (** The representation measure counts the largest finite endpoint. *)
  Parameter size_raw : forall a, size a = interval_bits (cut_raw a).
  (** The fixed cutoff bounds every value, independently of the operation and thresholds. *)
  Parameter size_bound : forall a, size a <= C.bits.
  (** Forward and backward work includes literals, list traversal and cutoff scans. *)
  Parameter work_agrees : forall o xs, work o xs = transfer_work o xs.
  (** Guard work includes operand traversal and cutoff scans. *)
  Parameter gwork_agrees : forall g xs, gwork g xs = guard_work g xs.
  (** Widening pays for unrestricted threshold values and their search paths. *)
  Parameter wsize_agrees : forall q,
    wsize q = (T.depth q + 1) * (T.tree_bits q + 1) + C.bits.
  (** Each finite side contributes at most one plus the threshold count. *)
  Parameter rank_bound : forall q a, wrank q a <= 2 * (length (T.vals q) + 1).
End CUT_INTERVAL_TIME.

Module Type CUT_INTERVAL_T (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) := CUT_INTERVAL C L <+ CUT_INTERVAL_TIME C L T.

Module Type CUT_INTERVAL_PLAN (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) (R : INTERVAL_ALL L T) (Import D : CUT_INTERVAL_T C L T).
  (** Concrete membership uses the projected inclusive interval. *)
  Parameter F_gamma : forall a z, gamma a z <-> in_cut a z.
  (** Inclusion compares normalized bounded projections directly. *)
  Parameter F_leb : forall a b, leb a b = R.leb (cut_raw a) (cut_raw b).
  (** Bottom has the normalized empty representation. *)
  Parameter F_bot : cut_raw bot = IBot.
  (** Top has two infinite endpoints. *)
  Parameter F_top : cut_raw top = I NegInf PosInf.
  (** Bottom recognition agrees with the raw domain. *)
  Parameter F_is_bot : forall a, is_bot a = R.is_bot (cut_raw a).
  (** Joining cuts the raw join before it enters the bounded carrier. *)
  Parameter F_join : forall a b,
    cut_raw (join a b) = cut_interval C.bits (R.join (cut_raw a) (cut_raw b)).
  (** Meeting cuts the normalized raw intersection. *)
  Parameter F_meet : forall a b,
    cut_raw (meet a b) = cut_interval C.bits (R.meet (cut_raw a) (cut_raw b)).
  (** Every threshold parameter is accepted and its result is cut outward. *)
  Parameter F_widen : forall q a b,
    cut_raw (widen q a b) = cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)).
  (** Narrowing cuts the raw narrowed result. *)
  Parameter F_narrow : forall a b,
    cut_raw (narrow a b) = cut_interval C.bits (R.narrow (cut_raw a) (cut_raw b)).
  (** Forward transfer cuts every raw result, including constants and shifts. *)
  Parameter F_forward : forall o xs,
    cut_raw (forward o xs) = cut_interval C.bits (R.forward o (map cut_raw xs)).
  (** Backward transfer cuts each result in its original operand position. *)
  Parameter F_backward : forall o r xs,
    map cut_raw (backward o r xs) =
      map (cut_interval C.bits) (R.backward o (cut_raw r) (map cut_raw xs)).
  (** Guard refinement cuts each returned operand. *)
  Parameter F_guard : forall g xs,
    map cut_raw (guard g xs) = map (cut_interval C.bits) (R.guard g (map cut_raw xs)).
  (** Widening rank counts thresholds beyond the retained finite endpoints. *)
  Parameter F_rank : forall q a, wrank q a = R.interval_wrank q (cut_raw a).
  (** Normalization and outward cutoff cannot increase the raw threshold rank. *)
  Parameter F_cut_rank : forall q a,
    R.interval_wrank q (cut_interval C.bits a) <= R.interval_wrank q a.
  Parameter k_cut : N.
  (** The total raw helper clock includes all endpoint inspections. *)
  Parameter T_cut_helper : forall a,
    (T_cut_interval C.bits a <= k_cut * N.of_nat (interval_bits a + C.bits + 1))%N.
  (** Packing the Boolean subtype adds constant overhead to the raw cutoff helper. *)
  Parameter T_cut_pack : forall a,
    (T_cut a <= k_cut * (T_cut_interval C.bits a + 1))%N.
  (** Forward timing includes projection traversal and cutting the actual raw result. *)
  Parameter T_forward_source : forall o xs,
    (T_forward o xs <= k_cut *
      (R.T_forward o (map cut_raw xs) +
       T_cut_interval C.bits (R.forward o (map cut_raw xs)) +
       N.of_nat (length xs) + 1))%N.
  (** Backward timing includes every returned cutoff and both list traversals. *)
  Parameter T_backward_source : forall o r xs,
    (T_backward o r xs <= k_cut *
      (R.T_backward o (cut_raw r) (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun a => (T_cut_interval C.bits a + 1)%N)
           (R.backward o (cut_raw r) (map cut_raw xs))) +
       N.of_nat (length xs) + 1))%N.
  (** Guard timing includes every returned cutoff and both list traversals. *)
  Parameter T_guard_source : forall g xs,
    (T_guard g xs <= k_cut *
      (R.T_guard g (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun a => (T_cut_interval C.bits a + 1)%N)
           (R.guard g (map cut_raw xs))) + N.of_nat (length xs) + 1))%N.
  (** Widening timing includes cutting the actual threshold-selected endpoints. *)
  Parameter T_widen_source : forall q a b,
    (T_widen q a b <= k_cut *
      (R.T_widen q (cut_raw a) (cut_raw b) +
       T_cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)) + 1))%N.
End CUT_INTERVAL_PLAN.

Module Type CUT_INTERVAL_ALL (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) (R : INTERVAL_ALL L T) :=
  CUT_INTERVAL_T C L T <+ CUT_INTERVAL_PLAN C L T R.

(* A state budget additionally needs finite variable support, canonical map storage and
   row equations. The carrier bounds every stored value by C.bits for every threshold tree.
   A generic ENV implementation does not bound its number of stored variables. *)
