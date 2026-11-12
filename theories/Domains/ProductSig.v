(** * Value products and reduction interfaces

    Products combine two abstractions of the same concrete value.
    For example, a value belongs to a product when both components describe it.
    Builds on: ValueSig and LatticeSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.

Module Type VALUE_REDUCER_SOUND (L : LANG) (A B : VALUE_DOMAIN L)
    (R : REDUCER_OPS A B).
  (** Reduction retains values shared by both abstractions. *)
  Parameter reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (R.reduce (a, b))) c /\ B.gamma (snd (R.reduce (a, b))) c.
End VALUE_REDUCER_SOUND.

Module Type VALUE_REDUCER (L : LANG) (A B : VALUE_DOMAIN L) :=
  REDUCER A B <+ VALUE_REDUCER_SOUND L A B.

Module Type VALUE_REDUCER_TIME (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER L A B).
  Parameter T_reduce : A.t * B.t -> N.
  Parameter c_reduce : N.
  (** One reduction charges the combined component sizes. *)
  Parameter T_reduce_le : forall a b,
    (T_reduce (a, b) <= c_reduce * N.of_nat ((A.size a + B.size b + 1)%nat))%N.
  (** Reduction results fit within the charged component sizes. *)
  Parameter reduce_size_le : forall a b,
    (N.of_nat (A.size (fst (R.reduce (a, b))) + B.size (snd (R.reduce (a, b)))) <=
      c_reduce * N.of_nat (A.size a + B.size b + 1))%N.
End VALUE_REDUCER_TIME.

Module Type VALUE_REDUCER_T (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  VALUE_REDUCER L A B <+ VALUE_REDUCER_TIME L A B.

Module Type ROUNDS.
  Parameter rounds : nat.
End ROUNDS.

Module Type PRODUCT_OPS (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L).
  Include VALUE_DOMAIN_OPS L with Definition t := (A.t * B.t)%type
    with Definition wparam := (A.wparam * B.wparam)%type.
End PRODUCT_OPS.

Module Type PRODUCT (L : LANG) (A B : VALUE_DOMAIN L) :=
  PRODUCT_OPS L A B <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+
  WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.

Module Type PRODUCT_TIME (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import P : PRODUCT L A B).
  Include VALUE_DOMAIN_TIME L P.
  Parameter T_normalize : t -> N.
  Parameter c_product : N.
  (** Bottom normalization charges both component sizes. *)
  Parameter T_normalize_le : forall a b,
    (T_normalize (a, b) <= c_product * N.of_nat (A.size a + B.size b + 1))%N.
  (** Product forward transfer charges both component transfers. *)
  Parameter T_forward_components : forall o xs, (T_forward o xs <= c_product *
    (N.of_nat ((length xs)%nat) + A.T_forward o (map fst xs) + B.T_forward o (map snd xs) +
      T_normalize (A.forward o (map fst xs), B.forward o (map snd xs)) + 1))%N.
  (** Product backward transfer charges both component transfers and list assembly. *)
  Parameter T_backward_components : forall o r xs, (T_backward o r xs <= c_product *
    (N.of_nat ((length xs)%nat) + A.T_backward o (fst r) (map fst xs) +
     B.T_backward o (snd r) (map snd xs) +
     fold_right N.add 0%N (map T_normalize
       (combine (A.backward o (fst r) (map fst xs))
         (B.backward o (snd r) (map snd xs)))) + 1))%N.
  (** Product guards charge both component guards and list assembly. *)
  Parameter T_guard_components : forall g xs, (T_guard g xs <= c_product *
    (N.of_nat ((length xs)%nat) + A.T_guard g (map fst xs) + B.T_guard g (map snd xs) +
      fold_right N.add 0%N (map T_normalize
        (combine (A.guard g (map fst xs)) (B.guard g (map snd xs)))) + 1))%N.
  (** Product forward transfer has the published work bound. *)
  Parameter forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat)) (fun ox => T_forward (fst ox) (snd ox)))%N.
End PRODUCT_TIME.

Module Type PRODUCT_T (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  PRODUCT L A B <+ PRODUCT_TIME L A B.

Module Type PRODUCT_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import P : PRODUCT_T L A B).
  Parameter k_product_lists : N.
  (** Product concretization is intersection. *)
  Parameter F1_gamma : forall a b c, gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  (** Product inclusion treats recognized bottoms as least. *)
  Parameter F2_leb : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  (** Widening retains the previous pair when its candidate is bottom. *)
  Parameter F3_widen : forall p a b, widen p a b =
    if is_bot b then a
    else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  (** Product ranks add the component ranks. *)
  Parameter F4_wrank : forall p a b,
    wrank p (a, b) = A.wrank (fst p) a + B.wrank (snd p) b.
  (** Product size adds the component sizes. *)
  Parameter F5_size : forall a b, size (a, b) = A.size a + B.size b.
  (** Product bottom testing recognizes either component bottom. *)
  Parameter F6_is_bot : forall a b, is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  (** Narrowing retains a recognized bottom candidate. *)
  Parameter F7_narrow : forall a b, narrow a b =
    if is_bot b then b else (A.narrow (fst a) (fst b), B.narrow (snd a) (snd b)).
  (** Product widening units add the component units. *)
  Parameter F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  (** Inclusion charges the component tests. *)
  Parameter T1_leb : forall a b, (T_leb a b <= k_product_lists *
    (A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1))%N.
  (** Inclusion charges bottom recognition before comparing the components. *)
  Parameter T1_leb_components : forall a b, (T_leb a b <= k_product_lists *
    (A.T_is_bot (fst a) + B.T_is_bot (snd a) +
      A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1))%N.
End PRODUCT_PLAN.

Module Type PRODUCT_ALL (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  PRODUCT_T L A B <+ PRODUCT_PLAN L A B.

Module Type REDUCED_OPS (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L)
    (R : REDUCER_OPS A B) (K : ROUNDS).
  Include PRODUCT_OPS L A B.
  Parameter red : t -> t.
End REDUCED_OPS.

Module Type REDUCED (L : LANG) (A B : VALUE_DOMAIN L) (R : VALUE_REDUCER L A B)
    (K : ROUNDS) := REDUCED_OPS L A B R K <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  HAS_MEET_LAWS <+ WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.

Module Type REDUCED_TIME (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) (Import D : REDUCED L A B R K).
  Include VALUE_DOMAIN_TIME L D.
  Parameter T_red : t -> N.
  Parameter c_red : N.
  (** Iterated reduction charges the configured number of rounds. *)
  Parameter T_red_le : forall a b,
    (T_red (a, b) <= c_red * N.of_nat (K.rounds + 1) *
      N.of_nat ((A.size a + B.size b + 1)%nat))%N.
  (** Reduced transfer has the published work bound. *)
  Parameter forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat)) (fun ox => T_forward (fst ox) (snd ox)))%N.
End REDUCED_TIME.

Module Type REDUCED_T (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) :=
  REDUCED L A B R K <+ REDUCED_TIME L A B R K.

Module Type REDUCED_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) (Import D : REDUCED_T L A B R K).
  Parameter k_red : N.
  (** Reduction normalizes the configured fixed iteration's recognized bottoms. *)
  Parameter F1_red_eq : forall x, red x =
    let result := Nat.iter K.rounds R.reduce x in
    if orb (A.is_bot (fst result)) (B.is_bot (snd result))
    then (A.bot, B.bot) else result.
  (** Reduced bottom testing recognizes either component bottom. *)
  Parameter F_is_bot : forall a b, is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  (** Reduced inclusion treats recognized bottoms as least. *)
  Parameter F_leb : forall a b, leb a b =
    orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  (** Reduced widening units add the component units. *)
  Parameter F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  (** Product concretization is intersection. *)
  Parameter F2_gamma : forall a b c, gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  (** Iterated reduction retains every represented concrete value. *)
  Parameter F3_red_sound : forall x c, gamma x c -> gamma (red x) c.
  (** Iterated reduction lowers both components. *)
  Parameter F4_red_lower : forall a b,
    A.leb (fst (red (a, b))) a = true /\ B.leb (snd (red (a, b))) b = true.
  (** Widening retains the previous pair when its candidate is bottom. *)
  Parameter F5_widen : forall p a b, widen p a b =
    if is_bot b then a
    else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  (** Iteration time charges reduction at every intermediate value. *)
  Parameter T1_red_steps : forall x, (T_red x <= k_red *
    (fold_right N.add 0
      (map (fun n => R.T_reduce (Nat.iter n R.reduce x) + 1) (seq 0 K.rounds)) +
      A.T_is_bot (fst (Nat.iter K.rounds R.reduce x)) +
      B.T_is_bot (snd (Nat.iter K.rounds R.reduce x)) + 1))%N.
End REDUCED_PLAN.

Module Type REDUCED_ALL (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) :=
  REDUCED_T L A B R K <+ REDUCED_PLAN L A B R K.
