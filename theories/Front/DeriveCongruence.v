(** * Tactics of the glue of equations

    The command [Egglog] of [Derive.v] proves, for each equational relation [R], that every
    instance of [R] is a congruence of the encodings of its two sides. It proves this lemma
    [<R>_congruent] with [egglog_congruent], which it calls by name. The proof recurses on the
    instance. A clause of [R] holds by its fire lemma, a closure law of [R] by the same law of
    the congruence, and the congruence law of a constructor by the congruence of its arguments.
    A congruence law relates two arguments by [R], by [Forall2 R] on two lists, by an equality,
    such as two lists of values, or by [Forall2 (pair_rel ra rb)] on two lists of pairs, where
    each of [ra] and [rb] is the equality or [R].

    For example, the law [math_vec] relates [MyVec xs] and [MyVec ys] when
    [Forall2 (math_eq unions) xs ys], and [egglog_list_args] proves the congruence of the two
    chains of cons nodes that encode [xs] and [ys].

    Builds on: the congruence of specifications, the definitions that derived programs call and
    the hint database of fire lemmas. *)

From Stdlib Require Import List.
From Galois.Front Require Import Spec DeriveHelpers DeriveTactics.

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

(** The congruence of one side of two cons nodes of lists of pairs. The two sides are equal by
    [Hside], or [IH] relates them. *)
Ltac egglog_pair_side IH Hside :=
  first [rewrite Hside; apply congruent_refl | apply IH; exact Hside].

(** A goal [congruent _ _ _ (e xs) (e ys)], where [e] encodes lists of pairs as chains of cons
    nodes and a hypothesis [Forall2 (pair_rel ra rb) xs ys] relates the two lists element by
    element. The proof recurses on the hypothesis with [IHL], and each pair of sides is equal or
    related through [IH]. *)
Ltac egglog_pair_list_args IH :=
  lazymatch goal with
  | |- congruent _ _ _ (_ ?xs) (_ ?ys) =>
      lazymatch goal with
      | Hall : Forall2 (pair_rel _ _) xs ys |- _ =>
          let IHL := fresh "IHL" in
          let Hfst := fresh "Hfst" in
          let Hsnd := fresh "Hsnd" in
          let Hrest := fresh "Hrest" in
          revert xs ys Hall; fix IHL 3; intros ? ? Hall;
          destruct Hall as [| [? ?] [? ?] ? ? [Hfst Hsnd] Hrest];
          [ apply congruent_refl
          | simpl in Hfst, Hsnd |- *; apply congruent_cong;
            apply Forall2_cons; [egglog_pair_side IH Hfst |];
            apply Forall2_cons; [egglog_pair_side IH Hsnd |];
            apply Forall2_cons; [apply IHL; exact Hrest |];
            apply Forall2_nil ]
      end
  end.

(** The arguments of a congruence. Each pair of arguments is related by a hypothesis through the
    recursive call [IH], equal, a pair of lists related element by element, or a pair of lists
    of pairs related side by side. *)
Ltac egglog_args IH :=
  repeat (apply Forall2_cons;
    [first
       [ apply IH; assumption
       | apply congruent_refl
       | egglog_list_args IH
       | egglog_pair_list_args IH ] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation is a congruence of the encodings, by recursion on
    the instance with [IH]. The fire lemmas give its clauses, and the congruence rules give its
    closure laws. The equalities of a congruence law are substituted first, so that their two
    arguments are one. *)
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
    | subst; simpl; apply congruent_cong; egglog_args IH ].
