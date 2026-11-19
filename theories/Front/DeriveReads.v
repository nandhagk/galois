(** * Tactics of equations that read derived rows

    A program may have relations over values beside equations, and the clauses of its equations
    may read the rows of those relations and the values of its lattice tables. The command
    [Egglog] of [Derive.v] states the glue of such equations over the read congruence of
    [SpecReads.v], and it proves the generated lemmas with the tactics of this file, which it
    calls by name. [egglog_mixed_closed] shows that every derived row of the program is in the
    meaning of its relations, [egglog_read_leaf] proves the premises of the fire lemma of an
    equational clause, and [egglog_read_congruent] shows that every instance of an equation is a
    read congruence of the encodings of its two sides. It reads the congruence laws that
    [egglog_congruent] of [DeriveCongruence.v] reads.

    For example, the fire lemma of the rewrite [known xs x c -> Mul (Ref x) a => Scale c a] reads
    its premise [known xs x c] as a derived row by the generated lemma [known_derived].

    Builds on: the meaning of equations that read derived rows, the meaning of lattice reads, the
    derived rows of specifications, the definitions that derived programs call and the glue
    tactics of relations. *)

From Stdlib Require Import List PArith.
From Galois.Front Require Import Spec SpecFacts SpecLattice SpecReads DeriveHelpers
  DeriveTactics.

Import List.ListNotations.

(** * Relations beside equations *)

(** Every derived row of a program with equations is in the relation of the program. A clause of
    an equation derives no row, so the case of such a clause closes by its head, and
    [egglog_clause] shows the case of every other clause. *)
Ltac egglog_mixed_closed :=
  intros;
  match goal with
  | H : derived ?prim ?s ?I ?r ?vs |- ?P ?r ?vs =>
      revert H; apply (derived_least prim s I P);
      [ let Hin := fresh "Hin" in intros ? ? _ Hin; red; left; exact Hin
      | let Hc := fresh "Hc" in
        let Hh := fresh "Hh" in
        let Hb := fresh "Hb" in
        let Hvals := fresh "Hvals" in
        intros ? ? ? ? ? Hc Hh Hb Hvals;
        simpl in Hc;
        repeat match goal with
               | Hc : _ = _ \/ _ |- _ => destruct Hc as [Hc | Hc]
               | Hc : False |- _ => contradiction
               end;
        try solve [match goal with Hc : _ = ?c |- _ => subst c end; simpl in Hh;
          discriminate Hh];
        egglog_clause Hc Hh Hb Hvals ]
  end.

(** * Equations *)

(** A hole of the fire lemma of an equational clause: a leaf of [egglog_leaf], a derived row or
    an assigned value that a glue lemma of a relation over values gives, or a merge that a read
    sees, which is one assigned value. *)
Ltac egglog_read_leaf :=
  first
    [ solve [egglog_leaf]
    | solve [eauto with egglog_fire]
    | solve [apply lat_merged_one; eauto with egglog_fire] ].

(** A goal [read_congruent _ _ _ _ (e xs) (e ys)], where [e] encodes lists as chains of cons
    nodes and a hypothesis [Forall2 R xs ys] relates the two lists element by element. The proof
    recurses on the hypothesis with [IHL], and [IH] gives the congruence of each pair of
    elements. *)
Ltac egglog_read_list_args IH :=
  lazymatch goal with
  | |- read_congruent _ _ _ _ (_ ?xs) (_ ?ys) =>
      lazymatch goal with
      | Hall : Forall2 _ xs ys |- _ =>
          let IHL := fresh "IHL" in
          let Hxy := fresh "Hxy" in
          let Hrest := fresh "Hrest" in
          revert xs ys Hall; fix IHL 3; intros ? ? Hall;
          destruct Hall as [| ? ? ? ? Hxy Hrest];
          [ apply read_refl
          | simpl; apply read_cong;
            apply Forall2_cons; [apply IH; exact Hxy |];
            apply Forall2_cons; [apply IHL; exact Hrest |];
            apply Forall2_nil ]
      end
  end.

(** The read congruence of one side of two cons nodes of lists of pairs. The two sides are equal
    by [Hside], or [IH] relates them. *)
Ltac egglog_read_pair_side IH Hside :=
  first [rewrite Hside; apply read_refl | apply IH; exact Hside].

(** A goal [read_congruent _ _ _ _ (e xs) (e ys)], where [e] encodes lists of pairs as chains
    of cons nodes and a hypothesis [Forall2 (pair_rel ra rb) xs ys] relates the two lists
    element by element. The proof recurses on the hypothesis with [IHL], and each pair of sides
    is equal or related through [IH]. *)
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
    through the recursive call [IH], equal, a pair of lists related element by element, or a
    pair of lists of pairs related side by side. *)
Ltac egglog_read_args IH :=
  repeat (apply Forall2_cons;
    [first
       [ apply IH; assumption
       | apply read_refl
       | egglog_read_list_args IH
       | egglog_read_pair_list_args IH ] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation is a read congruence of the encodings, by recursion
    on the instance with [IH]. The fire lemmas give its clauses, and the congruence rules give
    its closure laws. The equalities of a congruence law are substituted first, so that their
    two arguments are one. *)
Ltac egglog_read_congruent :=
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
    | subst; simpl; apply read_cong; egglog_read_args IH ].
