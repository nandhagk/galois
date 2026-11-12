(** * Bounded disjunctive state interfaces

    Lists retain alternatives and compact joins when a fixed cap is exceeded.
    For example, cap one joins two alternatives into one state.
    Builds on: LatticeSig and StateSig. *)

From Stdlib Require Import List NArith Arith Bool.
From Argent Require Import BigO.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
Import List.ListNotations.

Module Type POS_CAP.
  Include CAP.
  (** A bounded disjunction always has room for one alternative. *)
  Parameter k_pos : 0 < k.
End POS_CAP.

Module Type DISJUNCTION_OPS (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP)
    (P : LATTICE_OPS with Definition t := list S.t).
  Include STATE_DOMAIN_OPS X L V with Definition t := list S.t
    with Definition leb := P.leb with Definition bot := P.bot
    with Definition is_bot := P.is_bot with Definition join := P.join
    with Definition wparam := S.wparam.
  Parameter compact : nat -> t -> t.
  Parameter collapse : t -> S.t.
End DISJUNCTION_OPS.

Module Type DISJUNCTION_BASE (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t) :=
  DISJUNCTION_OPS X L V S C P <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type DISJUNCTION_LAWS (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t)
    (Import D : DISJUNCTION_BASE X L V S C P).
  (** List concretization is the union of its alternatives. *)
  Parameter gamma_alternatives : forall d st, gamma d st <-> Exists (fun s => S.gamma s st) d.
  (** Inclusion uses the Hoare coverage order. *)
  Parameter leb_hoare : forall a b, leb a b = forallb (fun x => existsb (S.leb x) b) a.
  (** Joining compacts the concatenated alternatives to the fixed cap. *)
  Parameter join_compact : forall a b, join a b = compact C.k (a ++ b).
  (** Compaction retains every input alternative below some result alternative. *)
  Parameter compact_covers : forall n d x, In x d ->
    exists y, In y (compact n d) /\ S.leb x y = true.
  (** Compaction returns at most the requested positive capacity. *)
  Parameter compact_len : forall n d, length (compact n d) <= Nat.max n 1.
End DISJUNCTION_LAWS.

Module Type DISJUNCTION (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t) :=
  DISJUNCTION_BASE X L V S C P <+ DISJUNCTION_LAWS X L V S C P.

Module Type DISJUNCTION_TIME (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t)
    (Import D : DISJUNCTION X L V S C P).
  Include STATE_DOMAIN_TIME X L V D.
  Parameter T_compact : nat -> t -> N.
  Parameter T_collapse : t -> N.
  Parameter c_disjunction : N.
  (** Coverage checking charges every tested pair of alternatives. *)
  Parameter T_leb_pairs : forall a b, (T_leb a b <= c_disjunction *
    (fold_right N.add 0%N (map (fun x => fold_right N.add 0%N
      (map (fun y => S.T_leb x y + 1) b) + 1) a) + 1))%N.
  (** Assignment charges each alternative independently. *)
  Parameter T_assign_alternatives : forall x e d, (T_assign x e d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_assign x e s + 1) d) + 1))%N.
  (** Havoc charges each alternative independently. *)
  Parameter T_havoc_alternatives : forall x d, (T_havoc x d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_havoc x s + 1) d) + 1))%N.
  (** Assumption charges each alternative independently. *)
  Parameter T_assume_alternatives : forall g es d, (T_assume g es d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_assume g es s + 1) d) + 1))%N.
End DISJUNCTION_TIME.

Module Type DISJUNCTION_T (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t) :=
  DISJUNCTION X L V S C P <+ DISJUNCTION_TIME X L V S C P.

Module Type DISJUNCTION_PLAN (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t)
    (Import D : DISJUNCTION_T X L V S C P).
  Parameter pair_widen : S.wparam -> list S.t -> list S.t -> list S.t.
  Parameter T_pair_widen : S.wparam -> list S.t -> list S.t -> N.
  Parameter k_disjunction : N.
  Definition wf (d : t) : Prop :=
    length d <= C.k /\ Forall (fun s => S.is_bot s = false) d.
  (** Pair widening aligns alternatives at the same list position. *)
  Parameter F1_pair_widen : forall p a b,
    pair_widen p a b = map (fun xy => S.widen p (fst xy) (snd xy)) (combine a b).
  (** Unstable widening first attempts to retain the previous number of alternatives. *)
  Parameter F2_widen : forall p a b, widen p a b =
    if leb b a then a else
    let next := compact (length a) (join a b) in
    if Nat.eqb (length next) (length a) then pair_widen p a next
    else [S.widen p (collapse a) (collapse b)].
  (** The proposed credit adds component ranks and a collapse credit. *)
  Parameter F3_rank : forall p d, wrank p d =
    fold_right Nat.add 0 (map (S.wrank p) d) + if Nat.eqb (length d) 1 then 0 else C.k.
  (* SIG-QUESTION: The shared disjunction supplies a lattice with the Hoare order and
     capped join. The state component owns widening and narrowing, including the
     requested F2_widen algorithm. F2 must rule its bounded-rank capability and carrier. *)
  (* SIG-QUESTION: The collapse rank has no bound in terms of the component rank sum.
     Equivalent raw representatives can have unrelated ranks. The fixed C.k credit does
     not establish the inherited wrank_widen law for arbitrary S. *)
  (* SIG-QUESTION: A component rank bound under an invariant needs a corresponding
     prepared carrier, initialization and preservation route for the unconditional
     STATE_DOMAIN widening laws. Raw lists admit [bottom] and fresh alternatives of
     unbounded rank, as in F1-332. Adding an invariant premise to a rank lemma does not
     establish those unconditional laws. The current wf predicate supplies neither a
     component invariant nor a bound. F2 must rule the capability and its public route. *)
  (** Assignment maps its transfer over the alternatives. *)
  Parameter F4_assign : forall x e d, assign x e d = map (S.assign x e) d.
  (** Havoc maps its transfer over the alternatives. *)
  Parameter F5_havoc : forall x d, havoc x d = map (S.havoc x) d.
  (** Assumption maps its transfer over the alternatives. *)
  Parameter F6_assume : forall g es d, assume g es d = map (S.assume g es) d.
  (** Pair widening charges the actual aligned component calls. *)
  Parameter T1_pair_widen : forall p a b, (T_pair_widen p a b <= k_disjunction *
    (fold_right N.add 0%N (map (fun xy => S.T_widen p (fst xy) (snd xy) + 1)
      (combine a b)) + 1))%N.
  (* SIG-QUESTION: P supplies lattice operations and laws without clocks. Q30 refutes
     the proposed unconditional raw-list LATTICE_TIME join bound even with JOIN_SIZE.
     An unbounded collapse tail can grow intermediate values exponentially, or charge
     quadratic traversal with additive size growth. Thus neither a genuine shared
     clock path nor inherited T_join_le follows from this P header. F2 must rule the
     prepared carrier or actual-fold work route and its initialization/preservation
     before selecting a timed shared bundle. The proposed k-squared bound is pending. *)
End DISJUNCTION_PLAN.

Module Type DISJUNCTION_ALL (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (C : POS_CAP)
    (P : LATTICE with Definition t := list S.t) :=
  DISJUNCTION_T X L V S C P <+ DISJUNCTION_PLAN X L V S C P.
