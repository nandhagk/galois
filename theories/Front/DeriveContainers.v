(** * Tactics of the congruence laws of containers

    The command [Egglog] of [Derive.v] proves the lemma [<R>_congruent] of an equational
    relation [R] with [egglog_congruent_containers], which it calls by name. The tactic tries
    [egglog_congruent] of [DeriveCongruence.v] first. Otherwise it reads two more kinds of
    hypotheses of a congruence law. An equality relates two arguments that are equal, such as
    two lists of values, and [Forall2 (pair_rel ra rb)] relates two lists of pairs element by
    element, where each of [ra] and [rb] is the equality or [R]. Beside relations over values,
    the command proves the lemma with [egglog_read_congruent_containers], which reads the same
    laws for the read congruence of [SpecReads.v].

    For example, the law [Forall2 (pair_rel eq item_eq) fs gs -> item_eq (Fields fs)
    (Fields gs)] relates two lists of fields whose keys are equal and whose values are related,
    and [egglog_pair_list_args] proves the congruence of the two chains of cons nodes that
    encode [fs] and [gs].

    Builds on: the congruence of specifications, the meaning of equations that read derived
    rows, the definitions that derived programs call and the tactics of the glue of
    equations. *)

From Stdlib Require Import List.
From Galois.Front Require Import Spec SpecReads DeriveHelpers DeriveTactics DeriveCongruence
  DeriveReads.

(** * Congruence of containers *)

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

(** The arguments of a congruence. Each pair of arguments is related by a hypothesis through
    the recursive call [IH], equal, or a pair of lists related element by element. *)
Ltac egglog_container_args IH :=
  repeat (apply Forall2_cons;
    [first
       [ apply IH; assumption
       | apply congruent_refl
       | egglog_list_args IH
       | egglog_pair_list_args IH ] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation is a congruence of the encodings, by recursion on
    the instance with [IH]. The equalities of a congruence law are substituted first, so that
    their two arguments are one. *)
Ltac egglog_congruent_lists :=
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
    | subst; simpl; apply congruent_cong; egglog_container_args IH ].

(** The lemma [<R>_congruent] of an equational relation [R], with the laws of
    [DeriveCongruence.v] or with the laws of containers. *)
Ltac egglog_congruent_containers :=
  first [egglog_congruent | egglog_congruent_lists].

(** * Read congruence of containers *)

(** The read congruence of one side of two cons nodes of lists of pairs. The two sides are equal
    by [Hside], or [IH] relates them. *)
Ltac egglog_read_pair_side IH Hside :=
  first [rewrite Hside; apply read_refl | apply IH; exact Hside].

(** A goal [read_congruent _ _ _ _ (e xs) (e ys)], where [e] encodes lists of pairs as chains
    of cons nodes and a hypothesis [Forall2 (pair_rel ra rb) xs ys] relates the two lists
    element by element, as in [egglog_pair_list_args]. *)
Ltac egglog_read_pair_list_args IH :=
  lazymatch goal with
  | |- read_congruent _ _ _ _ (_ ?xs) (_ ?ys) =>
      lazymatch goal with
      | Hall : Forall2 (pair_rel _ _) xs ys |- _ =>
          let IHL := fresh "IHL" in
          let Hfst := fresh "Hfst" in
          let Hsnd := fresh "Hsnd" in
          let Hrest := fresh "Hrest" in
          revert xs ys Hall; fix IHL 3; intros ? ? Hall;
          destruct Hall as [| [? ?] [? ?] ? ? [Hfst Hsnd] Hrest];
          [ apply read_refl
          | simpl in Hfst, Hsnd |- *; apply read_cong;
            apply Forall2_cons; [egglog_read_pair_side IH Hfst |];
            apply Forall2_cons; [egglog_read_pair_side IH Hsnd |];
            apply Forall2_cons; [apply IHL; exact Hrest |];
            apply Forall2_nil ]
      end
  end.

(** The arguments of a read congruence. Each pair of arguments is related by a hypothesis
    through the recursive call [IH], equal, or a pair of lists related element by element. *)
Ltac egglog_read_container_args IH :=
  repeat (apply Forall2_cons;
    [first
       [ apply IH; assumption
       | apply read_refl
       | egglog_read_list_args IH
       | egglog_read_pair_list_args IH ] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation that reads relations is a read congruence of the
    encodings, by recursion on the instance with [IH], as in [egglog_congruent_lists]. *)
Ltac egglog_read_congruent_lists :=
  intros;
  lazymatch goal with
  | H : _ ?t ?u |- _ => revert t u H
  end;
  let IH := fresh "IH" in
  let H := fresh "H" in
  fix IH 3; intros ? ? H; destruct H;
  first
    [ solve [clear IH; eauto with egglog_fire]
    | apply read_refl
    | apply read_sym; apply IH; assumption
    | eapply read_trans; apply IH; eassumption
    | subst; simpl; apply read_cong; egglog_read_container_args IH ].

(** The lemma [<R>_congruent] of an equational relation [R] beside relations over values, with
    the laws of [DeriveReads.v] or with the laws of containers. *)
Ltac egglog_read_congruent_containers :=
  first [egglog_read_congruent | egglog_read_congruent_lists].
