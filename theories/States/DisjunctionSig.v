(** * Bounded disjunctive state interfaces

    Lists retain alternatives and compact joins when a fixed cap is exceeded.
    For example, cap one joins two alternatives into one state.
    Builds on: LatticeSig and StateSig. *)

From Stdlib Require Import List NArith Arith Bool.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig DisjunctionSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
Import List.ListNotations.

Module SharedDisjunction := DisjunctionSig.

Module Type POS_CAP.
  Include CAP.
  (** A bounded disjunction always has room for one alternative. *)
  Parameter k_pos : 0 < k.
End POS_CAP.

(** Candidate alternatives that no previous alternative covers. *)
Definition uncovered {A} (leb : A -> A -> bool) (old new : list A) : list A :=
  filter (fun y => negb (existsb (leb y) old)) new.
TimeFun uncovered.

(** Applies a function at the first alternative that is not recognized as bottom. *)
Fixpoint replace_first {A} (is_bot : A -> bool) (f : A -> A) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest => if is_bot x then x :: replace_first is_bot f rest else f x :: rest
  end.
TimeFun replace_first.

Module Type JOIN_UNITS (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V).
  (** A join visits no more widening units than a constant times its operands. *)
  Parameter join_wunits : forall a b,
    (N.of_nat (S.wunits (S.join a b)) <= S.c_lat * N.of_nat (S.wunits a + S.wunits b + 1))%N.
End JOIN_UNITS.

Module Type DISJUNCTION_OPS (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP)
    (P : SharedDisjunction.DISJUNCTION_OPS S C).
  Include STATE_DOMAIN_OPS X L V with Definition t := P.t
    with Definition leb := P.leb with Definition bot := P.bot
    with Definition is_bot := P.is_bot with Definition join := P.join
    with Definition wparam := S.wparam.
  Parameter compact : nat -> list S.t -> list S.t.
  Parameter collapse : list S.t -> S.t.
End DISJUNCTION_OPS.

Module Type DISJUNCTION_BASE (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION S C) :=
  DISJUNCTION_OPS X L V S C P <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type DISJUNCTION_LAWS (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION S C)
    (Import D : DISJUNCTION_BASE X L V S C P).
  (** List concretization is the union of its alternatives. *)
  Parameter gamma_alternatives : forall d st,
    gamma d st <-> Exists (fun s => S.gamma s st) (proj1_sig d).
  (** Inclusion uses the Hoare coverage order. *)
  Parameter leb_hoare : forall a b, leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  (** Joining compacts the concatenated alternatives to the fixed cap. *)
  Parameter join_compact : forall a b, join a b = P.clip (proj1_sig a ++ proj1_sig b).
  (** Raw compaction at the fixed cap agrees with the actual shared clipping operation. *)
  Parameter compact_cap : forall d, compact C.k d = proj1_sig (P.clip d).
  (** Compaction retains every input alternative below some result alternative. *)
  Parameter compact_covers : forall n d x, In x d ->
    exists y, In y (compact n d) /\ S.leb x y = true.
  (** Compaction returns at most the requested positive capacity. *)
  Parameter compact_len : forall n d, length (compact n d) <= Nat.max n 1.
  (** Collapse is above every alternative it joins. *)
  Parameter collapse_covers : forall xs x, In x xs -> S.leb x (collapse xs) = true.
End DISJUNCTION_LAWS.

Module Type DISJUNCTION (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION S C) :=
  DISJUNCTION_BASE X L V S C P <+ DISJUNCTION_LAWS X L V S C P.

Module Type DISJUNCTION_TIME (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C)
    (Import D : DISJUNCTION X L V S C P).
  Include STATE_DOMAIN_TIME X L V D
    with Definition size := P.size with Definition T_leb := P.T_leb
    with Definition T_join := P.T_join with Definition T_is_bot := P.T_is_bot.
  Parameter T_compact : nat -> list S.t -> N.
  Parameter T_collapse : list S.t -> N.
  Parameter c_disjunction : N.
  (** Assignment work is the component work of every alternative. *)
  Parameter assign_work_alternatives : forall x e d, assign_work x e d =
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  (** Havoc work is the component work of every alternative. *)
  Parameter havoc_work_alternatives : forall x d, havoc_work x d =
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  (** Assumption work is the component work of every alternative. *)
  Parameter assume_work_alternatives : forall g es d, assume_work g es d =
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  (** Evaluation work is the component work and the value size of every alternative. *)
  Parameter eval_work_alternatives : forall e d, eval_work e d =
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).
  (** Assignment charges each alternative independently. *)
  Parameter T_assign_alternatives : forall x e d, (T_assign x e d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_assign x e s + 1) (proj1_sig d)) + 1))%N.
  (** Havoc charges each alternative independently. *)
  Parameter T_havoc_alternatives : forall x d, (T_havoc x d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_havoc x s + 1) (proj1_sig d)) + 1))%N.
  (** Assumption charges each alternative independently. *)
  Parameter T_assume_alternatives : forall g es d, (T_assume g es d <= c_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_assume g es s + 1) (proj1_sig d)) + 1))%N.
  (** The state constant pays for the shared order and join. *)
  Parameter c_lat_shared : (P.c_lat <= c_lat)%N.
  (** Widening visits the units of every alternative. *)
  Parameter wunits_alternatives : forall d,
    wunits d = fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  (** The widening parameter is the component's parameter. *)
  Parameter wsize_component : forall p, wsize p = S.wsize p.
  (** Collapsing at most the cap plus one alternatives charges their sizes. *)
  Parameter T_collapse_le : forall xs, length xs <= C.k + 1 ->
    (T_collapse xs <= c_disjunction *
      N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  (** A collapse of at most the cap plus one alternatives fits their sizes. *)
  Parameter collapse_size : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.size (collapse xs)) <= c_disjunction *
      N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  (** A collapse of at most the cap plus one alternatives fits their units. *)
  Parameter collapse_wunits : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.wunits (collapse xs)) <= c_disjunction *
      N.of_nat (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
End DISJUNCTION_TIME.

Module Type DISJUNCTION_T (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C) :=
  DISJUNCTION X L V S C P <+ DISJUNCTION_TIME X L V S JS JU C P.

Module Type DISJUNCTION_PLAN (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C)
    (Import D : DISJUNCTION_T X L V S JS JU C P).
  Parameter k_disjunction : N.
  (** The time of the value joins of evaluation, along the actual accumulator. *)
  Definition eval_joins (e : term L.op X.t) (xs : list S.t) : N :=
    fst (fold_left (fun acc s =>
      ((fst acc + V.T_join (snd acc) (S.eval e s) + 1)%N,
       V.join (snd acc) (S.eval e s))) xs (0%N, V.bot)).
  (** Unstable widening widens the first nonbottom alternative with every uncovered one. *)
  Parameter F2_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  (** The rank adds the alternatives' ranks and credits a list of bottom alternatives. *)
  Parameter F3_rank : forall p d, wrank p d =
    fold_right Nat.add 0%nat (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.
  (** Assignment maps its transfer over the alternatives. *)
  Parameter F4_assign : forall x e d,
    proj1_sig (assign x e d) = map (S.assign x e) (proj1_sig d).
  (** Havoc maps its transfer over the alternatives. *)
  Parameter F5_havoc : forall x d,
    proj1_sig (havoc x d) = map (S.havoc x) (proj1_sig d).
  (** Assumption maps its transfer over the alternatives. *)
  Parameter F6_assume : forall g es d,
    proj1_sig (assume g es d) = map (S.assume g es) (proj1_sig d).
  (** Evaluation joins the values of the alternatives from bottom. *)
  Parameter F7_eval : forall e d,
    eval e d = fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
  (** Widening charges the order, the scans, one collapse and one component widening. *)
  Parameter T1_widen : forall p a b, (T_widen p a b <= k_disjunction *
    (T_leb b a + T_is_bot a + P.T_clip [S.top] + N.of_nat (length (proj1_sig a) + 1) +
     fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) +
     fold_right N.add 0%N (map (fun y => fold_right N.add 0%N
       (map (fun x => S.T_leb y x + 1) (proj1_sig a))) (proj1_sig b)) +
     fold_right N.add 0%N (map (fun x =>
       let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
       T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
       (proj1_sig a))))%N.
  (** Evaluation charges each alternative's evaluation and the value joins. *)
  Parameter T2_eval : forall e d, (T_eval e d <= k_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_eval e s + 1) (proj1_sig d)) +
     eval_joins e (proj1_sig d) + 1))%N.
  (** The value joins of a capped list charge the sizes of the evaluated values. *)
  Parameter T3_eval_joins : forall e xs, length xs <= C.k ->
    (eval_joins e xs <= k_disjunction * N.of_nat (fold_right Nat.add 0%nat
      (map (fun s => (V.size (S.eval e s) + 1)%nat) xs) + 1))%N.
End DISJUNCTION_PLAN.

Module Type DISJUNCTION_ALL (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C) :=
  DISJUNCTION_T X L V S JS JU C P <+ DISJUNCTION_PLAN X L V S JS JU C P.
