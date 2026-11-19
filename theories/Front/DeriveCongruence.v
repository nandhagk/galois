(** * Tactics of the glue of equations

    The command [Egglog] of [Derive.v] proves, for each equational relation [R], that every
    instance of [R] is a congruence of the encodings of its two sides. It proves this lemma
    [<R>_congruent] with [egglog_congruent], which it calls by name. The proof recurses on the
    instance. A clause of [R] holds by its fire lemma, a closure law of [R] by the same law of
    the congruence, and the congruence law of a constructor by the congruence of its arguments.

    For example, the law [math_vec] relates [MyVec xs] and [MyVec ys] when
    [Forall2 (math_eq unions) xs ys], and [egglog_list_args] proves the congruence of the two
    chains of cons nodes that encode [xs] and [ys].

    Builds on: the congruence of specifications and the hint database of fire lemmas. *)

From Stdlib Require Import List.
From Galois.Front Require Import Spec DeriveTactics.

(** * Congruence of equations *)

(** A goal [congruent _ _ _ (e xs) (e ys)], where [e] encodes lists as chains of cons nodes and
    a hypothesis [Forall2 R xs ys] relates the two lists element by element. The proof recurses
    on the hypothesis with [IHL], and [IH] gives the congruence of each pair of elements. *)
Ltac egglog_list_args IH :=
  lazymatch goal with
  | |- congruent _ _ _ (_ ?xs) (_ ?ys) =>
      lazymatch goal with
      | Hall : Forall2 _ xs ys |- _ =>
          let IHL := fresh "IHL" in
          let Hxy := fresh "Hxy" in
          let Hrest := fresh "Hrest" in
          revert xs ys Hall; fix IHL 3; intros ? ? Hall;
          destruct Hall as [| ? ? ? ? Hxy Hrest];
          [ apply congruent_refl
          | simpl; apply congruent_cong;
            apply Forall2_cons; [apply IH; exact Hxy |];
            apply Forall2_cons; [apply IHL; exact Hrest |];
            apply Forall2_nil ]
      end
  end.

(** The arguments of a congruence. Each pair of arguments is related by a hypothesis through the
    recursive call [IH], equal, or a pair of lists related element by element. *)
Ltac egglog_args IH :=
  repeat (apply Forall2_cons;
    [first [apply IH; assumption | apply congruent_refl | egglog_list_args IH] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation is a congruence of the encodings, by recursion on
    the instance with [IH]. The fire lemmas give its clauses, and the congruence rules give its
    closure laws. *)
Ltac egglog_congruent :=
  intros;
  lazymatch goal with
  | H : _ ?t ?u |- _ => revert t u H
  end;
  let IH := fresh "IH" in
  let H := fresh "H" in
  fix IH 3; intros ? ? H; destruct H;
  first
    [ solve [clear IH; eauto with egglog_fire]
    | apply congruent_refl
    | apply congruent_sym; apply IH; assumption
    | eapply congruent_trans; apply IH; eassumption
    | simpl; apply congruent_cong; egglog_args IH ].
