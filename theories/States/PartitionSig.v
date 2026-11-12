(** * Token-partitioned states

    A partition is a capped list of labelled states that denotes their union. Labels come
    from tokens and decide which parts join and which part a widening grows.
    For example, joining [(T, s1)] with [(E, s2); (T, s3)] gives [(T, s1 ⊔ s3); (E, s2)].
    Builds on: LatticeSig, StateSig and the state disjunction interfaces. *)

From Stdlib Require Import List NArith Arith Bool.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig.
Import List.ListNotations.

(** Lists of at most k elements. *)
Definition capped (A : Type) (k : nat) : Type := {xs : list A | Nat.leb (length xs) k = true}.

(** Compares two optional labels with a token equality test. *)
Definition label_eqb {K : Type} (eqb : K -> K -> bool) (x y : option K) : bool :=
  match x, y with
  | Some a, Some b => eqb a b
  | None, None => true
  | _, _ => false
  end.
TimeFun label_eqb.

(** Counts the token bits of an optional label. *)
Definition label_bits {K : Type} (bits : K -> nat) (x : option K) : nat :=
  match x with
  | Some k => bits k
  | None => 0
  end.

(** Measures a list of parts by their states, their labels and one unit per part. *)
Definition parts_size {K A : Type} (bits : K -> nat) (size : A -> nat)
    (ps : list (option K * A)) : nat :=
  fold_right (fun q n => size (snd q) + label_bits bits (fst q) + 1 + n) 1 ps.

(** Adds the widening units of the states of a list of parts. *)
Definition parts_units {K A : Type} (units : A -> nat) (ps : list (option K * A)) : nat :=
  fold_right (fun q n => units (snd q) + n) 0 ps.

(** Joins a list of states from its first element, with bottom for the empty list. *)
Definition collapse_with {A : Type} (bot : A) (join : A -> A -> A) (xs : list A) : A :=
  match xs with
  | [] => bot
  | x :: rest => fold_left join rest x
  end.
TimeFun collapse_with.

(** Keeps the first n parts and joins the others into one unlabelled part. *)
Fixpoint fit_tail {K A : Type} (bot : A) (join : A -> A -> A) (n : nat)
    (ps : list (option K * A)) : list (option K * A) :=
  match n, ps with
  | S m, p :: rest => p :: fit_tail bot join m rest
  | _, _ => [(None, collapse_with bot join (map snd ps))]
  end.
TimeFun fit_tail.

(** Restores a cap by joining every part after the first cap minus one parts. *)
Definition fit_parts {K A : Type} (bot : A) (join : A -> A -> A) (cap : nat)
    (ps : list (option K * A)) : list (option K * A) :=
  match cap with
  | 0 => []
  | S n => if Nat.leb (length ps) (S n) then ps else fit_tail bot join n ps
  end.
TimeFun fit_parts.

(** Joins a part into the first part with an equal label, or appends it. *)
Fixpoint insert_part {K A : Type} (eqb : K -> K -> bool) (join : A -> A -> A)
    (q : option K * A) (ps : list (option K * A)) : list (option K * A) :=
  match ps with
  | [] => [q]
  | p :: rest =>
    if label_eqb eqb (fst p) (fst q) then (fst p, join (snd p) (snd q)) :: rest
    else p :: insert_part eqb join q rest
  end.
TimeFun insert_part.

(** Inserts every part of the second list into the first, in order. *)
Definition merge_parts {K A : Type} (eqb : K -> K -> bool) (join : A -> A -> A)
    (ps qs : list (option K * A)) : list (option K * A) :=
  fold_left (fun acc q => insert_part eqb join q acc) qs ps.
TimeFun merge_parts.

(** Candidate parts above bottom that no previous part covers. *)
Definition fresh_parts {K A : Type} (leb : A -> A -> bool) (bot : A)
    (old new : list (option K * A)) : list (option K * A) :=
  uncovered (fun q p => leb (snd q) (snd p)) old
    (filter (fun q => negb (leb (snd q) bot)) new).
TimeFun fresh_parts.

(** Fresh parts whose label no previous part above bottom carries. *)
Definition stray_parts {K A : Type} (eqb : K -> K -> bool) (leb : A -> A -> bool) (bot : A)
    (old fresh : list (option K * A)) : list (option K * A) :=
  filter (fun q => negb (existsb (fun p =>
    negb (leb (snd p) bot) && label_eqb eqb (fst p) (fst q)) old)) fresh.
TimeFun stray_parts.

(** Widens every previous part above bottom with the fresh parts of its label. The first such
    part also receives the strays, and parts below bottom stay unchanged. *)
Fixpoint absorb {K A : Type} (eqb : K -> K -> bool) (leb : A -> A -> bool) (bot : A)
    (join : A -> A -> A) (widen : A -> A -> A) (strays fresh old : list (option K * A))
    : list (option K * A) :=
  match old with
  | [] => []
  | p :: rest =>
    if leb (snd p) bot then p :: absorb eqb leb bot join widen strays fresh rest
    else
      let own := filter (fun q => label_eqb eqb (fst p) (fst q)) fresh ++ strays in
      (fst p, widen (snd p) (collapse_with bot join (snd p :: map snd own))) ::
        absorb eqb leb bot join widen [] fresh rest
  end.
TimeFun absorb.

Module Type PARTITION_OPS (X Tk : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP).
  Include STATE_DOMAIN_OPS X L V with Definition t := capped (option Tk.t * S.t) C.k
    with Definition wparam := S.wparam.
  Parameter inject : Tk.t -> S.t -> t.
  Parameter merge retag : Tk.t -> t -> t.
End PARTITION_OPS.

Module Type PARTITION_BASE (X Tk : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) :=
  PARTITION_OPS X Tk L V S C <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.
Module Type PARTITION_LAWS (X Tk : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (Import D : PARTITION_BASE X Tk L V S C).
  (** A partition denotes the union of its parts' states, whatever their labels. *)
  Parameter gamma_parts : forall a st,
    gamma a st <-> Exists (fun q => S.gamma (snd q) st) (proj1_sig a).
  (** Inclusion covers every part above bottom by some part, and ignores labels. *)
  Parameter leb_cover : forall a b, leb a b = forallb (fun q => S.leb (snd q) S.bot ||
    existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig b)) (proj1_sig a).
  (** A partition is bottom when every part lies below the component bottom. *)
  Parameter is_bot_parts : forall a,
    is_bot a = forallb (fun q => S.leb (snd q) S.bot) (proj1_sig a).
  (** Bottom has no parts. *)
  Parameter bot_raw : proj1_sig bot = [].
  (** Top is one unlabelled part that holds the component top. *)
  Parameter top_raw : proj1_sig top = [(None, S.top)].
  (** Joining merges parts with equal labels and then restores the cap. *)
  Parameter join_parts : forall a b, proj1_sig (join a b) =
    fit_parts S.bot S.join C.k (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)).
  (** The widening rank adds the component ranks of the parts above bottom. *)
  Parameter wrank_parts : forall p a, wrank p a = fold_right Nat.add 0%nat (map (fun q =>
    if S.leb (snd q) S.bot then 0 else S.wrank p (snd q)) (proj1_sig a)).
  (** Injection stores one part under the given token. *)
  Parameter inject_raw : forall k s, proj1_sig (inject k s) = [(Some k, s)].
  (** Merging joins every part into one part under the given token. *)
  Parameter merge_eq : forall k a,
    merge k a = inject k (collapse_with S.bot S.join (map snd (proj1_sig a))).
  (** Retagging is merging. *)
  Parameter retag_eq : forall k a, retag k a = merge k a.
  (** Injection keeps the environments of the injected state. *)
  Parameter gamma_inject : forall k s st, S.gamma s st -> gamma (inject k s) st.
  (** Merging keeps every environment of the partition. *)
  Parameter merge_sound : forall k a st, gamma a st -> gamma (merge k a) st.
End PARTITION_LAWS.

Module Type PARTITION (X Tk : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) :=
  PARTITION_BASE X Tk L V S C <+ PARTITION_LAWS X Tk L V S C.
Module Type PARTITION_TIME (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (Import D : PARTITION X Tk L V S C).
  Include STATE_DOMAIN_TIME X L V D.
  Parameter T_inject : Tk.t -> S.t -> N.
  Parameter T_merge T_retag : Tk.t -> t -> N.
  Parameter c_partition : N.
  (** A partition is measured by its parts' states and labels. *)
  Parameter size_parts : forall a, size a = parts_size Tk.bits S.size (proj1_sig a).
  (** Widening visits the units of every part. *)
  Parameter wunits_parts : forall a, wunits a = parts_units S.wunits (proj1_sig a).
  (** The widening parameter is measured as the component measures it. *)
  Parameter wsize_component : forall p, wsize p = S.wsize p.
  (** Assignment work is the component work of every part. *)
  Parameter assign_work_parts : forall x e a, assign_work x e a =
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  (** Havoc work is the component work of every part. *)
  Parameter havoc_work_parts : forall x a, havoc_work x a =
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  (** Assumption work is the component work of every part. *)
  Parameter assume_work_parts : forall g es a, assume_work g es a =
    fold_right Nat.add 0%nat (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  (** Evaluation work is the component work and the value size of every part. *)
  Parameter eval_work_parts : forall e a, eval_work e a = fold_right Nat.add 0%nat (map (fun q =>
    S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  (** Injection charges the token and the state. *)
  Parameter T_inject_le : forall k s,
    (T_inject k s <= c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  (** Merging charges the token and the partition. *)
  Parameter T_merge_le : forall k a,
    (T_merge k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  (** Retagging charges the token and the partition. *)
  Parameter T_retag_le : forall k a,
    (T_retag k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  (** A join has size bounded by the sizes of its operands. *)
  Parameter join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
  (** A join has widening units bounded by the units of its operands. *)
  Parameter join_wunits : forall a b,
    (N.of_nat (wunits (join a b)) <= c_lat * N.of_nat (wunits a + wunits b + 1))%N.
  (** A merge has size bounded by the token and the partition. *)
  Parameter merge_size : forall k a,
    (N.of_nat (size (merge k a)) <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
End PARTITION_TIME.

Module Type PARTITION_T (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S)
    (C : POS_CAP) :=
  PARTITION X Tk L V S C <+ PARTITION_TIME X Tk L V S JS JU C.
Module Type PARTITION_PLAN (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (Import D : PARTITION_T X Tk L V S JS JU C).
  Parameter k_partition : N.
  (** The time of finding fresh parts, finding strays and absorbing them. *)
  Definition route_time (p : S.wparam) (old new : list (option Tk.t * S.t)) : N :=
    let fresh := fresh_parts S.leb S.bot old new in
    (T_fresh_parts S.leb S.T_leb S.bot old new +
     T_stray_parts Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot old fresh +
     T_absorb Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot S.join S.T_join
       (S.widen p) (S.T_widen p) (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old)%N.
  (** The time of the value joins of evaluation, along the actual accumulator. *)
  Definition eval_joins (e : term L.op X.t) (ps : list (option Tk.t * S.t)) : N :=
    fst (fold_left (fun acc q =>
      ((fst acc + V.T_join (snd acc) (S.eval e (snd q)) + 1)%N,
       V.join (snd acc) (S.eval e (snd q)))) ps (0%N, V.bot)).

  (** Assignment maps its transfer over the parts and keeps their labels. *)
  Parameter F1_assign : forall x e a, proj1_sig (assign x e a) =
    map (fun q => (fst q, S.assign x e (snd q))) (proj1_sig a).
  (** Havoc maps its transfer over the parts and keeps their labels. *)
  Parameter F2_havoc : forall x a, proj1_sig (havoc x a) =
    map (fun q => (fst q, S.havoc x (snd q))) (proj1_sig a).
  (** Assumption maps its transfer over the parts and keeps their labels. *)
  Parameter F3_assume : forall g es a, proj1_sig (assume g es a) =
    map (fun q => (fst q, S.assume g es (snd q))) (proj1_sig a).
  (** Evaluation joins the values of the parts from bottom. *)
  Parameter F4_eval : forall e a,
    eval e a = fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
  (** An unstable widening from a nonbottom partition widens the parts that receive fresh
      parts, routed by label, and keeps the length of the previous partition. *)
  Parameter F5_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    let old := proj1_sig a in
    let fresh := fresh_parts S.leb S.bot old (proj1_sig b) in
    absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old.
  (** Narrowing keeps the previous partition. *)
  Parameter F6_narrow : forall a b, narrow a b = a.
  (** A label merge has at most the parts of both lists. *)
  Parameter F7_merge_parts_length : forall ps qs,
    length (merge_parts Tk.eqb S.join ps qs) <= length ps + length qs.
  (** A collapse of a bounded number of states fits their sizes. *)
  Parameter F8_collapse_size : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.size (collapse_with S.bot S.join xs)) <= k_partition *
      N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  (** A collapse of a bounded number of states fits their widening units. *)
  Parameter F9_collapse_units : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <= k_partition *
      N.of_nat (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  (** A label merge of two capped lists fits their sizes. *)
  Parameter F10_merge_parts_size : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_size Tk.bits S.size (merge_parts Tk.eqb S.join ps qs)) <=
      k_partition * N.of_nat (parts_size Tk.bits S.size ps +
        parts_size Tk.bits S.size qs + 1))%N.
  (** A label merge of two capped lists fits their widening units. *)
  Parameter F11_merge_parts_units : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_units S.wunits (merge_parts Tk.eqb S.join ps qs)) <=
      k_partition * N.of_nat (parts_units S.wunits ps + parts_units S.wunits qs + 1))%N.
  (** Restoring the cap on at most twice the cap parts fits their size. *)
  Parameter F12_fit_size : forall ps, length ps <= 2 * C.k ->
    (N.of_nat (parts_size Tk.bits S.size (fit_parts S.bot S.join C.k ps)) <=
      k_partition * N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  (** Restoring the cap on at most twice the cap parts fits their widening units. *)
  Parameter F13_fit_units : forall (ps : list (option Tk.t * S.t)), length ps <= 2 * C.k ->
    (N.of_nat (parts_units S.wunits (fit_parts S.bot S.join C.k ps)) <=
      k_partition * N.of_nat (parts_units S.wunits ps + 1))%N.

  (** Inclusion charges a bottom test and a scan of the other partition per part. *)
  Parameter T1_leb : forall a b, (T_leb a b <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot +
      fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1) (proj1_sig b)) + 1)
      (proj1_sig a)) + 1))%N.
  (** The bottom test charges one component comparison per part. *)
  Parameter T2_is_bot : forall a, (T_is_bot a <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot + 1) (proj1_sig a)) + 1))%N.
  (** Joining charges the label merge and the cap restoration. *)
  Parameter T3_join : forall a b, (T_join a b <= k_partition *
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join (proj1_sig a) (proj1_sig b) +
     T_fit_parts S.bot S.join S.T_join C.k
       (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1))%N.
  (** A label merge of two capped lists charges their sizes. *)
  Parameter T4_merge_parts : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join ps qs <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  (** Restoring the cap on at most twice the cap parts charges their size. *)
  Parameter T5_fit_parts : forall ps, length ps <= 2 * C.k ->
    (T_fit_parts S.bot S.join S.T_join C.k ps <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  (** Widening charges the stability test, the bottom test and the routing. *)
  Parameter T6_widen : forall p a b, (T_widen p a b <= k_partition *
    (T_leb b a + T_is_bot a + route_time p (proj1_sig a) (proj1_sig b) + 1))%N.
  (** Routing within the cap charges the sizes, the units and the widening parameter. *)
  Parameter T7_route : forall p old new, length old <= C.k -> length new <= C.k ->
    (route_time p old new <= k_partition * N.of_nat
      ((parts_units S.wunits old + parts_units S.wunits new + 1) * S.wsize p +
       (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + S.wsize p + 1)))%N.
  (** A collapse of a bounded number of states charges their sizes. *)
  Parameter T8_collapse : forall xs, length xs <= 2 * C.k + 1 ->
    (T_collapse_with S.bot S.join S.T_join xs <= k_partition *
      N.of_nat (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  (** Merging charges the collapse of all states and one injection. *)
  Parameter T9_merge : forall k a, (T_merge k a <= k_partition *
    (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
     T_inject k (collapse_with S.bot S.join (map snd (proj1_sig a))) + 1))%N.
  (** Retagging charges the merge it performs. *)
  Parameter T10_retag : forall k a, (T_retag k a <= k_partition * (T_merge k a + 1))%N.
  (** Injection takes constant time. *)
  Parameter T11_inject : forall k s, (T_inject k s <= k_partition)%N.
  (** Evaluation charges each part's evaluation and the value joins. *)
  Parameter T12_eval : forall e a, (T_eval e a <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_eval e (snd q) + 1) (proj1_sig a)) +
     eval_joins e (proj1_sig a) + 1))%N.
  (** The value joins of a capped list charge the sizes of the evaluated values. *)
  Parameter T13_eval_joins : forall e ps, length ps <= C.k ->
    (eval_joins e ps <= k_partition * N.of_nat (fold_right Nat.add 0%nat
      (map (fun q => (V.size (S.eval e (snd q)) + 1)%nat) ps) + 1))%N.
  (** Assignment charges each part's transfer. *)
  Parameter T14_assign : forall x e a, (T_assign x e a <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_assign x e (snd q) + 1) (proj1_sig a)) + 1))%N.
  (** Havoc charges each part's transfer. *)
  Parameter T15_havoc : forall x a, (T_havoc x a <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_havoc x (snd q) + 1) (proj1_sig a)) + 1))%N.
  (** Assumption charges each part's transfer. *)
  Parameter T16_assume : forall g es a, (T_assume g es a <= k_partition *
    (fold_right N.add 0%N (map (fun q => S.T_assume g es (snd q) + 1) (proj1_sig a)) + 1))%N.
  (** Narrowing takes constant time. *)
  Parameter T17_narrow : forall a b, (T_narrow a b <= k_partition)%N.
End PARTITION_PLAN.

Module Type PARTITION_ALL (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S)
    (C : POS_CAP) :=
  PARTITION_T X Tk L V S JS JU C <+ PARTITION_PLAN X Tk L V S JS JU C.
