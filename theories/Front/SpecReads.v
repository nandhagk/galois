(** * Equations that read derived rows and lattice values

    A clause of an equation may read the rows of a relation over values and the values of a
    lattice table, as the rewrite [known x c -> Mul (Var x) a => Scale c a] reads the rows of the
    relation [known]. This file gives such clauses a meaning over a relation [P] of rows and a
    relation [Q] of read values. [read_premise] says that a premise holds under an environment
    of terms, [read_step] is one step of rewriting, and [read_congruent] is the least congruence
    that contains every instance of an equational clause whose body holds. With the input rows
    and no read values ([no_values]) they are [congruent] and [rewrite_step] of [Spec.v]. With
    the rows of [derived], or with the rows of [lat_derived] and the merges of [lat_merged], the
    premises read what the relations over values derive.

    For example, when [known 1 5] is a derived row, the step of the rewrite above takes the term
    [Mul (Var 1) (Var 2)] to [Scale 5 (Var 2)], and the two terms are read-congruent.

    Main results
    - [input_read_premise] With no read values, a premise holds in the input rows exactly when it
      holds as an input premise.
    - [congruent_read], [rewrite_step_read] With the input rows and no read values, the meaning
      is [congruent] and [rewrite_step].
    - [read_step_mono], [read_congruent_mono] The meaning grows with the rows and the values.
    - [read_step_congruent] A step relates two read-congruent terms.
    - [congruent_rows] A congruence of the input rows is a read congruence over every relation
      of rows that contains the input rows.

    Builds on: the specifications and the models of the engine. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec.

Import List.ListNotations.

Section Reads.
Context {V : Type} (prim : positive -> list V -> option V).

(** * Meaning *)

(** The relation of read values with no value. *)
Definition no_values (f : positive) (ks : list V) (w : V) : Prop := False.

(** A premise holds under an environment of terms when its row is in [P], its read value is in
    [Q] or its primitive gives its value, with a literal term at every argument. *)
Definition read_premise (P : positive -> list V -> Prop) (Q : positive -> list V -> V -> Prop)
    (e : positive -> option (@expr V)) (p : premise V) : Prop :=
  match p with
  | Holds r args => exists vs, pat_literals prim e args = Some vs /\ P r vs
  | Equals f args v => exists ks w, pat_literals prim e args = Some ks /\
      pat_term prim e v = Some (ELit w) /\ Q f ks w
  | Computes q args v => exists vs w, pat_literals prim e args = Some vs /\
      prim q vs = Some w /\ pat_term prim e v = Some (ELit w)
  end.

(** One step of rewriting: an instance of a rewrite clause whose body reads rows of [P] and
    values of [Q]. *)
Inductive read_step (s : spec V) (P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) : @expr V -> @expr V -> Prop :=
  | read_step_clause c e l r tl tr : In c (clauses s) -> head c = Rewrites l r ->
      Forall (read_premise P Q e) (body c) -> pat_term prim e l = Some tl ->
      pat_term prim e r = Some tr -> read_step s P Q tl tr.

(** The least congruence that contains each instance of an equational clause whose body reads
    rows of [P] and values of [Q]. *)
Inductive read_congruent (s : spec V) (P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) : @expr V -> @expr V -> Prop :=
  | read_refl t : read_congruent s P Q t t
  | read_sym t u : read_congruent s P Q t u -> read_congruent s P Q u t
  | read_trans t u w : read_congruent s P Q t u -> read_congruent s P Q u w ->
      read_congruent s P Q t w
  | read_cong f ts us : Forall2 (read_congruent s P Q) ts us ->
      read_congruent s P Q (EApp f ts) (EApp f us)
  | read_clause c e l r tl tr : In c (clauses s) ->
      (head c = Unify l r \/ head c = Rewrites l r) ->
      Forall (read_premise P Q e) (body c) -> pat_term prim e l = Some tl ->
      pat_term prim e r = Some tr -> read_congruent s P Q tl tr.

(** * Input rows *)

(** With no read values, a premise holds in the input rows exactly when it holds as an input
    premise. *)
Lemma input_read_premise (I : positive -> list V -> Prop) e p :
  input_premise prim I e p <-> read_premise I no_values e p.
Proof.
  destruct p as [r args | f args v | q args v]; cbn.
  - reflexivity.
  - split; [intros [] |].
    intros [ks [w [_ [_ []]]]].
  - reflexivity.
Qed.

(** With the input rows and no read values, a step is a rewrite step of [Spec.v]. *)
Lemma rewrite_step_read (s : spec V) (I : positive -> list V -> Prop) t u :
  rewrite_step prim s I t u <-> read_step s I no_values t u.
Proof.
  split.
  - intros [c e l r tl tr Hin Hhead Hbody Hl Hr].
    apply (read_step_clause s I no_values c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
    refine (Forall_impl _ _ Hbody). intros p. apply input_read_premise.
  - intros [c e l r tl tr Hin Hhead Hbody Hl Hr].
    apply (rewrite_step_clause prim s I c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
    refine (Forall_impl _ _ Hbody). intros p. apply input_read_premise.
Qed.

(** A congruence of the input rows is a read congruence with no read values. *)
Lemma congruent_read_of (s : spec V) (I : positive -> list V -> Prop) :
  forall t u, congruent prim s I t u -> read_congruent s I no_values t u.
Proof.
  fix IH 3.
  intros t u Hcong.
  destruct Hcong as [t | t u Htu | t u w Htu Huw | f ts us Hargs
    | c e l r tl tr Hin Hhead Hbody Hl Hr].
  - apply read_refl.
  - apply read_sym. exact (IH t u Htu).
  - exact (read_trans s I no_values t u w (IH t u Htu) (IH u w Huw)).
  - apply read_cong.
    revert ts us Hargs.
    fix IHL 3.
    intros ts us Hargs.
    destruct Hargs as [| t u ts us Htu Hrest].
    + constructor.
    + constructor; [exact (IH t u Htu) | exact (IHL ts us Hrest)].
  - apply (read_clause s I no_values c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
    refine (Forall_impl _ _ Hbody). intros p. apply input_read_premise.
Qed.

(** A read congruence with no read values is a congruence of the input rows. *)
Lemma read_congruent_of (s : spec V) (I : positive -> list V -> Prop) :
  forall t u, read_congruent s I no_values t u -> congruent prim s I t u.
Proof.
  fix IH 3.
  intros t u Hcong.
  destruct Hcong as [t | t u Htu | t u w Htu Huw | f ts us Hargs
    | c e l r tl tr Hin Hhead Hbody Hl Hr].
  - apply congruent_refl.
  - apply congruent_sym. exact (IH t u Htu).
  - exact (congruent_trans prim s I t u w (IH t u Htu) (IH u w Huw)).
  - apply congruent_cong.
    revert ts us Hargs.
    fix IHL 3.
    intros ts us Hargs.
    destruct Hargs as [| t u ts us Htu Hrest].
    + constructor.
    + constructor; [exact (IH t u Htu) | exact (IHL ts us Hrest)].
  - apply (congruent_clause prim s I c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
    refine (Forall_impl _ _ Hbody). intros p. apply input_read_premise.
Qed.

(** With the input rows and no read values, the read congruence is [congruent]. *)
Lemma congruent_read (s : spec V) (I : positive -> list V -> Prop) t u :
  congruent prim s I t u <-> read_congruent s I no_values t u.
Proof.
  split; [apply congruent_read_of | apply read_congruent_of].
Qed.

(** * Monotonicity *)

(** A premise that holds with two relations holds with two larger ones. *)
Lemma read_premise_mono (P P' : positive -> list V -> Prop)
    (Q Q' : positive -> list V -> V -> Prop) e p :
  (forall r vs, P r vs -> P' r vs) -> (forall f ks w, Q f ks w -> Q' f ks w) ->
  read_premise P Q e p -> read_premise P' Q' e p.
Proof.
  intros HP HQ.
  destruct p as [r args | f args v | q args v]; cbn.
  - intros [vs [Hvs Hrow]]. exists vs. split; [exact Hvs | exact (HP r vs Hrow)].
  - intros [ks [w [Hks [Hw Hq]]]]. exists ks, w.
    split; [exact Hks |]. split; [exact Hw | exact (HQ f ks w Hq)].
  - intros Hp. exact Hp.
Qed.

(** A step grows with the rows and the values that its premises read. *)
Lemma read_step_mono (s : spec V) (P P' : positive -> list V -> Prop)
    (Q Q' : positive -> list V -> V -> Prop) t u :
  (forall r vs, P r vs -> P' r vs) -> (forall f ks w, Q f ks w -> Q' f ks w) ->
  read_step s P Q t u -> read_step s P' Q' t u.
Proof.
  intros HP HQ [c e l r tl tr Hin Hhead Hbody Hl Hr].
  apply (read_step_clause s P' Q' c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
  refine (Forall_impl _ _ Hbody). intros p. exact (read_premise_mono P P' Q Q' e p HP HQ).
Qed.

(** The read congruence grows with the rows and the values that the premises read. *)
Lemma read_congruent_mono (s : spec V) (P P' : positive -> list V -> Prop)
    (Q Q' : positive -> list V -> V -> Prop) :
  (forall r vs, P r vs -> P' r vs) -> (forall f ks w, Q f ks w -> Q' f ks w) ->
  forall t u, read_congruent s P Q t u -> read_congruent s P' Q' t u.
Proof.
  intros HP HQ.
  fix IH 3.
  intros t u Hcong.
  destruct Hcong as [t | t u Htu | t u w Htu Huw | f ts us Hargs
    | c e l r tl tr Hin Hhead Hbody Hl Hr].
  - apply read_refl.
  - apply read_sym. exact (IH t u Htu).
  - exact (read_trans s P' Q' t u w (IH t u Htu) (IH u w Huw)).
  - apply read_cong.
    revert ts us Hargs.
    fix IHL 3.
    intros ts us Hargs.
    destruct Hargs as [| t u ts us Htu Hrest].
    + constructor.
    + constructor; [exact (IH t u Htu) | exact (IHL ts us Hrest)].
  - apply (read_clause s P' Q' c e l r tl tr Hin Hhead); [| exact Hl | exact Hr].
    refine (Forall_impl _ _ Hbody). intros p. exact (read_premise_mono P P' Q Q' e p HP HQ).
Qed.

(** A step relates two read-congruent terms. *)
Lemma read_step_congruent (s : spec V) (P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) t u :
  read_step s P Q t u -> read_congruent s P Q t u.
Proof.
  intros [c e l r tl tr Hin Hhead Hbody Hl Hr].
  exact (read_clause s P Q c e l r tl tr Hin (or_intror Hhead) Hbody Hl Hr).
Qed.

(** A congruence of the input rows is a read congruence over every relation of rows that
    contains the input rows, with any read values. *)
Lemma congruent_rows (s : spec V) (I P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) t u :
  (forall r vs, I r vs -> P r vs) -> congruent prim s I t u -> read_congruent s P Q t u.
Proof.
  intros HP Hcong.
  apply (read_congruent_mono s I P no_values Q HP); [intros f ks w [] |].
  exact (congruent_read_of s I t u Hcong).
Qed.

End Reads.
