(** * Value products and reduction interfaces

    Products combine two abstractions of the same concrete value.
    For example, a value belongs to a product when both components describe it.
    Builds on: ValueSig and LatticeSig. *)

From Stdlib Require Import List.
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
  Parameter T_reduce : A.t * B.t -> nat.
  Parameter c_reduce : nat.
  (** One reduction charges the combined component sizes. *)
  Parameter T_reduce_le : forall a b,
    T_reduce (a, b) <= c_reduce * (A.size a + B.size b + 1).
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
  Parameter c_product : nat.
  (** Product forward transfer charges both component transfers. *)
  Parameter T_forward_components : forall o xs, T_forward o xs <= c_product *
    (length xs + A.T_forward o (map fst xs) + B.T_forward o (map snd xs) + 1).
  (** Product backward transfer charges both component transfers and list assembly. *)
  Parameter T_backward_components : forall o r xs, T_backward o r xs <= c_product *
    (length xs + A.T_backward o (fst r) (map fst xs) +
     B.T_backward o (snd r) (map snd xs) + 1).
  (** Product guards charge both component guards and list assembly. *)
  Parameter T_guard_components : forall g xs, T_guard g xs <= c_product *
    (length xs + A.T_guard g (map fst xs) + B.T_guard g (map snd xs) + 1).
  (** Product forward transfer has the published work bound. *)
  Parameter forward_bigO : bigO (fun _ => True)
    (fun ox => work (fst ox) (snd ox)) (fun ox => T_forward (fst ox) (snd ox)).
End PRODUCT_TIME.

Module Type PRODUCT_T (L : LANG_T) (A B : VALUE_DOMAIN_T L) :=
  PRODUCT L A B <+ PRODUCT_TIME L A B.

Module Type PRODUCT_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (Import P : PRODUCT_T L A B).
  Parameter k_product_lists : nat.
  (** Product concretization is intersection. *)
  Parameter F1_gamma : forall a b c, gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  (** Product inclusion compares both components. *)
  Parameter F2_leb : forall a b,
    leb a b = andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b)).
  (** Widening acts independently on each component. *)
  Parameter F3_widen : forall p a b, widen p a b =
    (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  (** Product ranks add the component ranks. *)
  Parameter F4_wrank : forall p a b,
    wrank p (a, b) = A.wrank (fst p) a + B.wrank (snd p) b.
  (** Product size adds the component sizes. *)
  Parameter F5_size : forall a b, size (a, b) = A.size a + B.size b.
  (** Inclusion charges the component tests. *)
  Parameter T1_leb : forall a b, T_leb a b <= k_product_lists *
    (A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1).
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
  Parameter T_red : t -> nat.
  (** Iterated reduction charges the configured number of rounds. *)
  Parameter T_red_le : forall a b,
    T_red (a, b) <= K.rounds * R.c_reduce * (A.size a + B.size b + 1).
  (** Reduced transfer has the published work bound. *)
  Parameter forward_bigO : bigO (fun _ => True)
    (fun ox => work (fst ox) (snd ox)) (fun ox => T_forward (fst ox) (snd ox)).
End REDUCED_TIME.

Module Type REDUCED_T (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) :=
  REDUCED L A B R K <+ REDUCED_TIME L A B R K.

Module Type REDUCED_PLAN (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) (Import D : REDUCED_T L A B R K).
  Parameter k_red : nat.
  (** Reduction is precisely the configured fixed iteration. *)
  Parameter F1_red_eq : forall x, red x = Nat.iter K.rounds R.reduce x.
  (** Product concretization is intersection. *)
  Parameter F2_gamma : forall a b c, gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  (** Iterated reduction retains every represented concrete value. *)
  Parameter F3_red_sound : forall x c, gamma x c -> gamma (red x) c.
  (** Iterated reduction lowers both components. *)
  Parameter F4_red_lower : forall a b,
    A.leb (fst (red (a, b))) a = true /\ B.leb (snd (red (a, b))) b = true.
  (** Widening remains componentwise. *)
  Parameter F5_widen : forall p a b, widen p a b =
    (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  (** Iteration time charges reduction at every intermediate value. *)
  Parameter T1_red_steps : forall x, T_red x <= k_red *
    (fold_right Nat.add 0
      (map (fun n => R.T_reduce (Nat.iter n R.reduce x) + 1) (seq 0 K.rounds)) + 1).
End REDUCED_PLAN.

Module Type REDUCED_ALL (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) :=
  REDUCED_T L A B R K <+ REDUCED_PLAN L A B R K.
