(** * Deriving engine programs from inductives

    The command [Egglog P from R1 .. Rn.] reads the inductive relations [R1] to [Rn] and
    defines a module [P] with the specification of their constructors ([P.spec]), its engine
    program ([P.program]), the input rows of their parameters ([P.inputs], [P.facts]) and the
    meaning of each table ([P.relation]). A relation over values is a table. A relation [R t u]
    over a datatype is an equation, and the constructors of the datatype are tables. A premise
    [In e (f q)] reads an input table, and a premise [Ri ..] reads a relation. Variables are
    numbered in binder order, and every table code and variable number is generated. The
    command [Egglog Value T M.] registers the encoder module [M] of a value type [T], and the
    values of [T] enter the engine through [M.encode]. After [with Ops], the declaration
    [merge R g] makes [R] a lattice table, whose last index is its value and whose merge is the
    primitive [g] of [Ops]. A constructor of [R] assigns a value, and a premise over [R] reads
    the stored value.

    For example, [Egglog Andersen from may_points.] defines [Andersen.spec] with one clause per
    constructor of [may_points], and [Andersen.facts q] lists the input rows of [q].

    Builds on: the specifications, their lowering, the meaning of lattice reads, and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Argent Require Import Time.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec SpecFacts SpecLattice LowerSig RunnerSig.

Import List.ListNotations.

(** * Primitives over encoded values

    A primitive function takes values of registered types. The primitive of a set decodes each
    argument, calls the function and encodes the result, and has no result when a decoding
    fails. [id_decode] and [id_encode] are the encoder of [positive], which is its own
    engine value. *)

Create HintDb egglog_decode.
Create HintDb egglog_inj.

Definition id_decode (p : positive) : option positive := Some p.

Definition id_encode (p : positive) : positive := p.

(** Decoding the identity encoding gives the value back. *)
Lemma id_decode_encode : forall x, id_decode (id_encode x) = Some x.
Proof.
  reflexivity.
Qed.

#[export] Hint Resolve id_decode_encode : egglog_decode.

(** An encoder that decodes its own encodings is injective. *)
Lemma encode_inj_of {A : Type} (enc : A -> positive) (dec : positive -> option A)
    (Hdec : forall x, dec (enc x) = Some x) (x y : A) : enc x = enc y -> x = y.
Proof.
  intros Henc. apply (f_equal dec) in Henc. rewrite !Hdec in Henc. injection Henc as Hxy.
  exact Hxy.
Qed.

(** The primitive of a set of arity 1, 2 or 3 on a list of engine values. *)
Definition prim1d {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R)
    (vs : list positive) : option positive :=
  match vs with
  | [a] =>
      match da a with
      | Some x => Some (er (f x))
      | None => None
      end
  | _ => None
  end.

Definition prim2d {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) (vs : list positive) : option positive :=
  match vs with
  | [a; b] =>
      match da a, db b with
      | Some x, Some y => Some (er (f x y))
      | _, _ => None
      end
  | _ => None
  end.

Definition prim3d {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R)
    (vs : list positive) : option positive :=
  match vs with
  | [a; b; c] =>
      match da a, db b, dc c with
      | Some x, Some y, Some z => Some (er (f x y z))
      | _, _, _ => None
      end
  | _ => None
  end.

(** The result of the primitive with code [c] when [p] is [c], and [rest] otherwise. *)
Definition prim_case (p c : positive) (call : list positive -> option positive)
    (vs : list positive) (rest : option positive) : option positive :=
  if Pos.eqb p c then call vs else rest.

Arguments prim1d : simpl never.
Arguments prim2d : simpl never.
Arguments prim3d : simpl never.

(** A call on decoded arguments has the encoded result. *)
Lemma prim1d_some {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R) a x :
  da a = Some x -> prim1d da er f [a] = Some (er (f x)).
Proof.
  intros Ha. unfold prim1d. rewrite Ha. reflexivity.
Qed.

Lemma prim2d_some {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) a b x y :
  da a = Some x -> db b = Some y -> prim2d da db er f [a; b] = Some (er (f x y)).
Proof.
  intros Ha Hb. unfold prim2d. rewrite Ha, Hb. reflexivity.
Qed.

Lemma prim3d_some {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R) a b c x y z :
  da a = Some x -> db b = Some y -> dc c = Some z ->
  prim3d da db dc er f [a; b; c] = Some (er (f x y z)).
Proof.
  intros Ha Hb Hc. unfold prim3d. rewrite Ha, Hb, Hc. reflexivity.
Qed.

(** A result of a call comes from decoded arguments. *)
Lemma prim1d_inv {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R) a w :
  prim1d da er f [a] = Some w -> exists x, da a = Some x /\ w = er (f x).
Proof.
  unfold prim1d. destruct (da a) as [x|]; intros Hw; try discriminate.
  injection Hw as Hw. exists x. auto.
Qed.

Lemma prim2d_inv {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) a b w :
  prim2d da db er f [a; b] = Some w ->
  exists x y, da a = Some x /\ db b = Some y /\ w = er (f x y).
Proof.
  unfold prim2d. destruct (da a) as [x|], (db b) as [y|]; intros Hw; try discriminate.
  injection Hw as Hw. exists x, y. auto.
Qed.

Lemma prim3d_inv {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R) a b c w :
  prim3d da db dc er f [a; b; c] = Some w ->
  exists x y z, da a = Some x /\ db b = Some y /\ dc c = Some z /\ w = er (f x y z).
Proof.
  unfold prim3d. destruct (da a) as [x|], (db b) as [y|], (dc c) as [z|]; intros Hw;
    try discriminate.
  injection Hw as Hw. exists x, y, z. auto.
Qed.

(** * Glue tactics

    The command proves, for each relation [R] over values, that [R] holds exactly when its row
    is derived. These tactics prove the generated lemmas. [egglog_member] and
    [egglog_unmember] move between an input element and its row. [egglog_clause] shows that
    one clause, applied to rows of the relation, gives a row of the relation. *)

Create HintDb egglog_fire discriminated.

(** A value whose encoding is a known positive: decoding the equation [encode x = k] gives the
    value [x]. *)
Ltac egglog_decode_literal Hinj e x :=
  let E := fresh "E" in
  eassert (_ (e x) = Some x) as E by (eauto with egglog_decode);
  rewrite Hinj in E; cbv in E;
  injection E as E; clear Hinj; subst.

(** Equal encodings come from equal values: the injectivity lemma of each registered encoder
    turns a hypothesis [encode x = encode y] into [x = y], and the decoder turns [encode x = k]
    for a literal [k] into the value of [k]. *)
Ltac egglog_inj :=
  repeat match goal with
  | Hinj : ?e ?x = ?e ?y |- _ =>
      let E := fresh "E" in
      assert (x = y) as E by (eauto with egglog_inj);
      clear Hinj; try subst
  | Hinj : ?e ?x = _ |- _ => is_var x; egglog_decode_literal Hinj e x
  | Hinj : _ = ?e ?x |- _ => is_var x; symmetry in Hinj; egglog_decode_literal Hinj e x
  end.

(** A hypothesis [d (e x) = Some y] that decodes an encoding gives [x = y]. *)
Ltac egglog_decoded H :=
  cbv [id_decode id_encode] in H;
  try match type of H with
  | ?d (?e ?x) = Some _ =>
      let E := fresh "E" in
      assert (d (e x) = Some x) as E by (eauto with egglog_decode);
      rewrite E in H; clear E
  end;
  injection H; clear H; intros; try subst.

(** Unfold the primitive function of a set in the goal, down to the call of its function. *)
Ltac egglog_unfold_prims :=
  repeat match goal with
  | |- context [?p ?q ?vs] =>
      lazymatch type of p with
      | positive -> list positive -> option positive => is_const p; unfold p
      end
  end;
  cbv [prim_case Pos.eqb].

(** Replace each call of a primitive function on encodings by the encoding of its result. *)
Ltac egglog_eval_prims :=
  repeat match goal with
  | |- context [@prim1d _ _ ?da ?er ?f [?a]] =>
      let E := fresh "E" in
      eassert (prim1d da er f [a] = Some _) as E
        by (eapply prim1d_some; eauto with egglog_decode);
      rewrite E; clear E
  | |- context [@prim2d _ _ _ ?da ?db ?er ?f [?a; ?b]] =>
      let E := fresh "E" in
      eassert (prim2d da db er f [a; b] = Some _) as E
        by (eapply prim2d_some; eauto with egglog_decode);
      rewrite E; clear E
  | |- context [@prim3d _ _ _ _ ?da ?db ?dc ?er ?f [?a; ?b; ?c]] =>
      let E := fresh "E" in
      eassert (prim3d da db dc er f [a; b; c] = Some _) as E
        by (eapply prim3d_some; eauto with egglog_decode);
      rewrite E; clear E
  end.

(** An equation between the values of patterns, which holds by evaluation of the primitives. *)
Ltac egglog_values :=
  simpl; egglog_unfold_prims; egglog_eval_prims; simpl; reflexivity.

(** A call of a primitive function on encoded arguments has the encoded result, which an
    equation premise [f x1 .. xn = w] names. *)
Ltac egglog_prim_goal :=
  lazymatch goal with
  | |- ?p _ _ = _ =>
      unfold p; cbv [prim_case Pos.eqb];
      first [eapply prim1d_some | eapply prim2d_some | eapply prim3d_some];
      eauto with egglog_decode
  end.

(** The goal [prim q vs = Some w] from a premise [f x1 .. xn = w] among the hypotheses. *)
Ltac egglog_prim_leaf :=
  match goal with
  | H : _ = _ |- _ = Some _ =>
      try rewrite <- H; first [reflexivity | egglog_prim_goal]
  end.

(** A row is in the rows of the inputs when its element is in its input list. *)
Ltac egglog_member :=
  lazymatch goal with
  | |- In _ (_ ++ _) => apply in_or_app; first [left; egglog_member | right; egglog_member]
  | |- In _ (flat_map _ ?l) =>
      apply in_flat_map;
      match goal with
      | H : In ?c l |- _ => exists c; split; [exact H | simpl; left; reflexivity]
      end
  | |- In _ (map _ ?l) =>
      apply in_map_iff;
      match goal with
      | H : In ?c l |- _ => exists c; split; [reflexivity | exact H]
      end
  end.

(** Prove a hole of a fire lemma: an input membership, a row of the inputs, or a primitive
    premise [f x1 .. xn = w] read as the result [Some w] of the primitive function. *)
Ltac egglog_leaf :=
  first
    [ reflexivity
    | simpl; tauto
    | red; egglog_member
    | egglog_prim_leaf
    | egglog_values ].

(** Each constructor of a relation derives its row, by induction and the fire lemmas. *)
Ltac egglog_complete :=
  intros; match goal with H : _ |- _ => induction H end; eauto with egglog_fire.

(** A row in the rows of the inputs comes from an element of an input list. *)
Ltac egglog_unmember H :=
  lazymatch type of H with
  | In _ (_ ++ _) =>
      apply in_app_or in H; destruct H as [H | H]; egglog_unmember H
  | In _ (flat_map _ _) =>
      let c := fresh "c" in
      let Hc := fresh "Hc" in
      apply in_flat_map in H; destruct H as [c [Hc H]]; destruct c; simpl in H;
      repeat match type of H with
             | _ \/ _ => destruct H as [H | H]
             | False => contradiction
             end;
      try (inversion H; subst; clear H; try egglog_inj)
  | In _ (map _ _) =>
      let p := fresh "p" in
      let Hp := fresh "Hp" in
      apply in_map_iff in H; destruct H as [p [H Hp]]; destruct p; simpl in H;
      inversion H; subst; clear H; try egglog_inj
  | In _ [] => simpl in H; contradiction
  | _ => idtac
  end.

(** Case on every lookup of an environment [e : positive -> option _] in the hypotheses. The
    environment is a variable, which keeps a value [Some w] from counting as a lookup. *)
Ltac egglog_env :=
  simpl in *;
  repeat match goal with
  | H : context [?e ?i] |- _ =>
      is_var e;
      lazymatch type of e with
      | positive -> option _ =>
          let v := fresh "v" in
          let E := fresh "E" in
          remember (e i) as v eqn:E in *; clear E; destruct v; simpl in *; try discriminate
      end
  end;
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  end.

(** A hypothesis [Hrel] that a row is in the relation of a program: an input element, or a
    row of a relation over values. *)
Ltac egglog_row Hrel :=
  red in Hrel; destruct Hrel as [Hrel | Hrel];
  [ egglog_unmember Hrel
  | repeat match type of Hrel with
           | _ \/ _ => destruct Hrel as [Hrel | Hrel]
           end;
    let Hcode := fresh "Hcode" in
    let Hvs := fresh "Hvs" in
    destruct Hrel as [Hcode Hrel]; try discriminate Hcode;
    repeat match type of Hrel with
           | exists _, _ => destruct Hrel as [? Hrel]
           end;
    destruct Hrel as [Hvs Hrel]; inversion Hvs; subst; clear Hvs; try egglog_inj ].

(** The relation of a program holds of a row of a relation over values when the relation
    holds of its indices. *)
Ltac egglog_conclude :=
  repeat match goal with |- exists _, _ => eexists end;
  split; [reflexivity | solve [econstructor; eauto]].

Ltac egglog_pick :=
  first
    [ split; [reflexivity | egglog_conclude]
    | left; split; [reflexivity | egglog_conclude]
    | right; egglog_pick ].

(** A hypothesis [p q vs = Some w] on the call of a primitive function: the arguments decode to
    values, and [w] is the encoding of the result. *)
Ltac egglog_prim_in H :=
  try (lazymatch type of H with
       | ?p _ _ = _ => is_const p; unfold p in H
       end);
  cbv [prim_case Pos.eqb] in H;
  first
    [ apply prim1d_inv in H; destruct H as [? [Ha Hw]]; egglog_decoded Ha
    | apply prim2d_inv in H; destruct H as [? [? [Ha [Hb Hw]]]];
      egglog_decoded Ha; egglog_decoded Hb
    | apply prim3d_inv in H; destruct H as [? [? [? [Ha [Hb [Hc Hw]]]]]];
      egglog_decoded Ha; egglog_decoded Hb; egglog_decoded Hc ];
  subst.

(** One clause, applied to rows of the relation of a program, gives a row of it. *)
Ltac egglog_clause Hc Hh Hb Hvals :=
  simpl in Hc;
  repeat match goal with
         | Hc : _ = _ \/ _ |- _ => destruct Hc as [Hc | Hc]
         | Hc : False |- _ => contradiction
         end;
  match goal with Hc : _ = ?c |- _ => subst c end;
  simpl in Hh, Hb, Hvals;
  match goal with
  | Hh : Derive _ _ = Derive _ _ |- _ => injection Hh; clear Hh; intros; subst
  end;
  repeat match goal with
         | Hb : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hb; destruct Hb as [? Hb]
         | Hb : Forall _ [] |- _ => clear Hb
         end;
  repeat match goal with
         | H : premise_in _ _ _ (Holds _ _) |- _ =>
             let vs := fresh "vs" in
             let Hv := fresh "Hv" in
             let Hrel := fresh "Hrel" in
             simpl in H; destruct H as [vs [Hv Hrel]]
         end;
  repeat match goal with
         | H : premise_in _ _ _ (Computes _ _ _) |- _ =>
             simpl in H; destruct H as [? [? [? [? ?]]]]
         end;
  egglog_env;
  repeat match goal with
         | Hrel : _ |- _ =>
             lazymatch type of Hrel with
             | ?Rel ?r ?vs =>
                 lazymatch type of Rel with
                 | positive -> list positive -> Prop => egglog_row Hrel
                 end
             end
         end;
  repeat match goal with
         | H : _ = Some _ |- _ => egglog_prim_in H
         end;
  try egglog_inj;
  red; right; egglog_pick.

(** The arguments of a congruence: each is related by a hypothesis or equal. *)
Ltac egglog_args :=
  repeat (apply Forall2_cons; [first [assumption | apply congruent_refl] | ]);
  apply Forall2_nil.

(** Each instance of an equational relation is a congruence of the encodings: the fire
    lemmas for its clauses and the congruence rules for its closure laws. *)
Ltac egglog_congruent :=
  intros; match goal with H : _ |- _ => induction H end;
  first
    [ solve [eauto with egglog_fire]
    | apply congruent_refl
    | apply congruent_sym; assumption
    | eapply congruent_trans; eassumption
    | simpl; apply congruent_cong; egglog_args ].

(** Every derived row is in the relation of the program. *)
Ltac egglog_closed :=
  intros;
  match goal with
  | H : derived ?prim ?s ?I ?r ?vs |- ?P ?r ?vs =>
      revert H; apply (derived_least prim s I P);
      [ let Hin := fresh "Hin" in intros ? ? _ Hin; red; left; exact Hin
      | let Hc := fresh "Hc" in
        let Hh := fresh "Hh" in
        let Hb := fresh "Hb" in
        let Hvals := fresh "Hvals" in
        intros ? ? ? ? ? Hc Hh Hb Hvals; egglog_clause Hc Hh Hb Hvals ]
  end.

(** A row of the relation of a program for a relation over values gives the relation. *)
Ltac egglog_back :=
  intros;
  match goal with Hrel : _ |- _ => egglog_row Hrel end;
  assumption.

(** * Lattice tables

    A relation whose last index is its value is a lattice table when the command declares it
    with [merge R g] after [with Ops]. Its constructors assign values, and a premise over it
    reads the stored value. The glue of such a program uses the relations of [SpecLattice.v],
    and for a lattice relation [R], [R ks v] holds exactly when [v] is a value that the clauses
    assign at [ks]. A read sees a merge of assigned values, so a relation that a clause reads
    must be closed under its merge. The command proves this closure as the lemma [<R>_merges]
    with [egglog_merges]. *)

Create HintDb egglog_merges discriminated.

(** The merge of a lattice table whose merge is the primitive with code [m]: the result of the
    primitive on the two values, or the first value when the primitive has no result. A value
    module that defines its [merge] as [prim_merge prim] merges as the primitive set computes. *)
Definition prim_merge (prim : positive -> list positive -> option positive) (m a b : positive) :
    positive :=
  match prim m [a; b] with
  | Some c => c
  | None => a
  end.

(** A relation that a clause reads is closed under its merge [g]. Either [g] returns one of its
    two arguments, which the cases of its unfolded definition show, or a constructor of the
    relation merges two values. *)
Ltac egglog_merges :=
  intros;
  first
    [ solve
        [ lazymatch goal with
          | |- _ ?v =>
              lazymatch v with
              | ?g _ _ => unfold g
              end
          end;
          repeat match goal with
                 | |- context [match ?x with _ => _ end] => destruct x
                 end;
          assumption ]
    | solve [econstructor; eassumption] ].

(** A hypothesis [Hrel] that a row is in the relation of a program with lattice tables: an
    input element, a row of a relation over values, or nothing when the program has no
    relation over values. *)
Ltac egglog_lat_row Hrel :=
  red in Hrel; destruct Hrel as [Hrel | Hrel];
  [ egglog_unmember Hrel
  | repeat match type of Hrel with
           | _ \/ _ => destruct Hrel as [Hrel | Hrel]
           end;
    lazymatch type of Hrel with
    | False => contradiction
    | _ =>
        let Hcode := fresh "Hcode" in
        let Hvs := fresh "Hvs" in
        destruct Hrel as [Hcode Hrel]; try discriminate Hcode;
        repeat match type of Hrel with
               | exists _, _ => destruct Hrel as [? Hrel]
               end;
        destruct Hrel as [Hvs Hrel]; inversion Hvs; subst; try clear Hvs; try egglog_inj
    end ].

(** A hypothesis [Hlat] that a value is in the lattice of a program: a value of a lattice
    relation at its keys. *)
Ltac egglog_lattice_row Hlat :=
  red in Hlat;
  repeat match type of Hlat with
         | _ \/ _ => destruct Hlat as [Hlat | Hlat]
         end;
  let Hcode := fresh "Hcode" in
  let Hks := fresh "Hks" in
  let Hw := fresh "Hw" in
  destruct Hlat as [Hcode Hlat]; try discriminate Hcode;
  repeat match type of Hlat with
         | exists _, _ => destruct Hlat as [? Hlat]
         end;
  destruct Hlat as [Hks [Hw Hlat]]; inversion Hks; subst; try clear Hks; try egglog_inj.

(** The lattice of a program holds of keys and a value, when [tac] proves the lattice relation
    of the chosen disjunct. *)
Ltac egglog_lat_value tac :=
  repeat match goal with |- exists _, _ => eexists end;
  split; [reflexivity | split; [reflexivity | solve [tac]]].

Ltac egglog_lat_pick tac :=
  first
    [ split; [reflexivity | egglog_lat_value tac]
    | left; split; [reflexivity | egglog_lat_value tac]
    | right; egglog_lat_pick tac ].

(** The merge of two values of the lattice of a program at one key is in the lattice. The kind
    of the table gives its merge, and the closure lemma [<R>_merges] gives the relation. *)
Ltac egglog_lat_merge :=
  let m := fresh "m" in
  let a := fresh "a" in
  let b := fresh "b" in
  let Hm := fresh "Hm" in
  let Ha := fresh "Ha" in
  let Hb := fresh "Hb" in
  intros m a b Hm Ha Hb;
  vm_compute in Hm; injection Hm as Hm; subst m;
  egglog_lattice_row Ha; egglog_lattice_row Hb;
  red; unfold prim_merge; simpl; egglog_unfold_prims; simpl; egglog_eval_prims; simpl;
  cbv [id_encode];
  egglog_lat_pick ltac:(eauto with egglog_merges).

(** The premises of one clause of a program with lattice tables, applied to rows of its relation
    and to merges of values of its lattice. A read sees a merge, which the closure lemma of its
    relation turns into a value of the lattice. *)
Ltac egglog_lat_premises Hc Hh Hb :=
  simpl in Hc;
  repeat match goal with
         | Hc : _ = _ \/ _ |- _ => destruct Hc as [Hc | Hc]
         | Hc : False |- _ => contradiction
         end;
  match goal with Hc : _ = ?c |- _ => subst c end;
  simpl in Hh, Hb;
  match goal with
  | Hh : Derive _ _ = Derive _ _ |- _ => injection Hh; clear Hh; intros; subst
  | Hh : Assign _ _ _ = Assign _ _ _ |- _ => injection Hh; clear Hh; intros; subst
  | Hh : Derive _ _ = Assign _ _ _ |- _ => discriminate Hh
  | Hh : Assign _ _ _ = Derive _ _ |- _ => discriminate Hh
  end;
  repeat match goal with
         | Hb : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hb; destruct Hb as [? Hb]
         | Hb : Forall _ [] |- _ => clear Hb
         end;
  repeat match goal with
         | H : premise_lat_in _ _ _ _ (Holds _ _) |- _ =>
             let vs := fresh "vs" in
             let Hv := fresh "Hv" in
             let Hrel := fresh "Hrel" in
             simpl in H; destruct H as [vs [Hv Hrel]]
         | H : premise_lat_in _ _ _ _ (Equals _ _ _) |- _ =>
             let ks := fresh "ks" in
             let w := fresh "w" in
             let Hk := fresh "Hk" in
             let Hw := fresh "Hw" in
             let Hlat := fresh "Hlat" in
             simpl in H; destruct H as [ks [w [Hk [Hw Hlat]]]];
             apply lat_closure_elim in Hlat; [| egglog_lat_merge]
         | H : premise_lat_in _ _ _ _ (Computes _ _ _) |- _ =>
             simpl in H; destruct H as [? [? [? [? ?]]]]
         end;
  egglog_env;
  repeat match goal with
         | Hrel : _ |- _ =>
             lazymatch type of Hrel with
             | ?Rel ?r ?vs =>
                 lazymatch type of Rel with
                 | positive -> list positive -> Prop => egglog_lat_row Hrel
                 end
             end
         end;
  repeat match goal with
         | Hlat : _ |- _ =>
             lazymatch type of Hlat with
             | ?Lat ?f ?ks ?w =>
                 lazymatch type of Lat with
                 | positive -> list positive -> positive -> Prop => egglog_lattice_row Hlat
                 end
             end
         end;
  repeat match goal with
         | H : _ = Some _ |- _ => egglog_prim_in H
         end;
  try egglog_inj.

(** Every row and every assigned value of a program with lattice tables is in the meaning of its
    tables. [lat_least_closure] reduces this to the inputs and to each clause, applied to rows of
    the relation and values of the lattice of the program. *)
Ltac egglog_lat_closed :=
  intros;
  apply lat_least_closure;
  [ let Hin := fresh "Hin" in
    intros ? ? _ Hin; red; left; exact Hin
  | let Hc := fresh "Hc" in
    let Hh := fresh "Hh" in
    let Hb := fresh "Hb" in
    let Hvals := fresh "Hvals" in
    intros ? ? ? ? ? Hc Hh Hb Hvals; egglog_lat_premises Hc Hh Hb;
    red; right; egglog_pick
  | let Hc := fresh "Hc" in
    let Hh := fresh "Hh" in
    let Hb := fresh "Hb" in
    let Hvals := fresh "Hvals" in
    let Hval := fresh "Hval" in
    intros ? ? ? ? ? ? ? Hc Hh Hb Hvals Hval; egglog_lat_premises Hc Hh Hb;
    red; egglog_lat_pick ltac:(econstructor; eauto) ].

(** A value of the lattice of a program for a lattice relation gives the relation. *)
Ltac egglog_lat_back :=
  intros;
  match goal with Hlat : _ |- _ => egglog_lattice_row Hlat end;
  assumption.

(** A row of the relation of a program with lattice tables gives its relation over values. *)
Ltac egglog_back_lat :=
  intros;
  match goal with Hrel : _ |- _ => egglog_lat_row Hrel end;
  assumption.

Elpi Db egglog.values lp:{{
  % A registered value type: the type, its encoder and its decoder.
  pred value-enc o:term, o:term, o:term.
}}.

Elpi Db egglog.prims lp:{{
  % A registered primitive: its function, its code and the primitive function of its set.
  pred prim-code o:gref, o:term, o:term.
}}.

Elpi Command Egglog.
Elpi Accumulate Db egglog.prims.
Elpi Accumulate Db egglog.values.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{

% ---------------------------------------------------------------------------------------------
% Types

pred value-type i:term.
value-type T :- coq.locate "positive" GR, T = global GR, !.
value-type T :- value-enc T _ _.

% The engine value of a value of type Ty: its encoder applied, or the value itself of positive.
pred enc-by-ty i:term, i:term, o:term.
enc-by-ty Ty X (app [Enc, X]) :- value-enc Ty Enc _, !.
enc-by-ty _ X X.

% The engine value of a value term, by the type of the term.
pred enc-term i:term, o:term.
enc-term X Y :- coq.typecheck X Ty ok, enc-by-ty Ty X Y.

% The decoder of a value type.
pred dec-of-type i:term, o:term.
dec-of-type Ty Dec :- value-enc Ty _ Dec, !.
dec-of-type Ty {{ id_decode }} :- value-type Ty, !.
dec-of-type Ty _ :- coq.error "Egglog: a primitive has type" {coq.term->string Ty}
  "which is neither positive nor a registered value type".

% The encoder of a value type.
pred enc-of-type i:term, o:term.
enc-of-type Ty Enc :- value-enc Ty Enc _, !.
enc-of-type Ty {{ id_encode }} :- value-type Ty, !.
enc-of-type Ty _ :- coq.error "Egglog: a primitive has type" {coq.term->string Ty}
  "which is neither positive nor a registered value type".

pred datatype i:term, o:inductive.
datatype (global (indt I)) I :-
  not (value-type (global (indt I))),
  coq.env.indt I tt 0 _ Arity _ _, not (Arity = sort prop).

% The type of a value of a table, which must be positive or a registered value type.
pred check-value i:term.
check-value T :- value-type T, !.
check-value T :- coq.error "Egglog: the type" {coq.term->string T}
  "is neither positive nor a registered value type. Register an encoder with Egglog Value.".

pred sort-term i:term, o:term.
sort-term T {{ SVal }} :- value-type T, !.
sort-term T {{ SId }} :- datatype T _, !.
sort-term T _ :- coq.error "Egglog: a table argument has type" {coq.term->string T}
  "which is neither a registered value type nor a datatype".

% ---------------------------------------------------------------------------------------------
% Numerals and lists

pred int->pos i:int, o:term.
int->pos 1 {{ xH }} :- !.
int->pos N {{ xO lp:P }} :- 0 is N mod 2, !, M is N div 2, int->pos M P.
int->pos N {{ xI lp:P }} :- M is N div 2, int->pos M P.

pred list->term i:term, i:list term, o:term.
list->term Ty [] {{ @nil lp:Ty }}.
list->term Ty [X | Xs] {{ @cons lp:Ty lp:X lp:T }} :- list->term Ty Xs T.

% The list of engine values of a list of value terms.
pred enc-list i:list term, o:term.
enc-list Xs L :- std.map Xs enc-term Es, list->term {{ positive }} Es L.

% ---------------------------------------------------------------------------------------------
% Tables

kind tkey type.
type tk-rel inductive -> tkey.     % a relation over values
type tk-con constructor -> tkey.   % an input constructor or a datatype constructor
type tk-src term -> tkey.          % an input list of tuples, by its projection
type tk-param int -> tkey.         % an input list of tuples that is a parameter, by position

kind table type.
type table tkey -> int -> list term -> term -> table.   % key, code, sorts, output

pred find-table i:list table, i:tkey, o:int, o:list term, o:term.
find-table [table K N S O | _] K N S O :- !.
find-table [_ | Ts] K N S O :- find-table Ts K N S O.

% The code constant of a table, once the command has defined it.
pred code-const o:tkey, o:term.

pred code-of i:list table, i:tkey, o:term.
code-of _ K P :- code-const K P, !.
code-of Ts K P :- find-table Ts K N _ _, !, int->pos N P.
code-of _ K _ :- coq.error "Egglog: no table for" K.

% ---------------------------------------------------------------------------------------------
% Parameters and binders

pred with-params i:int, i:term, i:list term, i:(list term -> prop).
with-params 0 _ Acc K :- !, std.rev Acc Ps, K Ps.
with-params N (prod Name Ty F) Acc K :- M is N - 1,
  pi p\ decl p Name Ty => with-params M (F p) [p | Acc] K.

pred is-prop i:term.
is-prop Ty :- coq.typecheck Ty S ok, coq.reduction.lazy.whd S (sort prop).

% walk Ty Vars Hyps K: binders of data become numbered variables, binders of propositions
% become hypotheses, and K receives them with the conclusion.
pred walk i:term, i:list (pair term int), i:list term,
  i:(list (pair term int) -> list term -> term -> prop).
walk (prod Name Ty F) Vars Hyps K :- is-prop Ty, !,
  pi h\ decl h Name Ty => walk (F h) Vars [Ty | Hyps] K.
walk (prod Name Ty F) Vars Hyps K :- !, std.length Vars N, I is N + 1,
  pi x\ decl x Name Ty => walk (F x) [pr x I | Vars] Hyps K.
walk C Vars Hyps K :- std.rev Vars Vs, std.rev Hyps Hs, K Vs Hs C.

pred drop i:int, i:list term, o:list term.
drop 0 L L :- !.
drop N [_ | L] R :- M is N - 1, drop M L R.

% ---------------------------------------------------------------------------------------------
% Collecting tables

pred in-premise i:term, o:term, o:term.
in-premise (app [global GR, _, Elem, Coll]) Elem Coll :- coq.locate "List.In" GR.

% input-key Elem Coll Key Args Sorts
pred input-key i:list term, i:term, i:term, o:tkey, o:list term, o:list term.
input-key Ps (app [global (indc P), T1, T2, A, B]) Coll Key [A, B] [S1, S2] :-
  coq.locate "pair" (indc P), !, sort-term T1 S1, sort-term T2 S2, source-key Ps Coll Key.
input-key _ (app [global (indc C) | Args]) _ (tk-con C) Args Sorts :- !,
  coq.env.typeof (indc C) Ty, arg-types Ty Tys, std.map Tys sort-term Sorts.
input-key _ (global (indc C)) _ (tk-con C) [] [] :- !.

pred source-key i:list term, i:term, o:tkey.
source-key Ps P (tk-param I) :- param-index Ps P 1 I, !.
source-key _ (app [Head | _]) (tk-src Head) :- !.
source-key _ C _ :- coq.error "Egglog: an input list must be a parameter or a projection of one:"
  {coq.term->string C}.

pred param-index i:list term, i:term, i:int, o:int.
param-index [P | _] P I I :- !.
param-index [_ | Ps] P I J :- K is I + 1, param-index Ps P K J.
input-key _ E _ _ _ _ :- coq.error "Egglog: an input element must be a constructor or a pair:"
  {coq.term->string E}.

pred arg-types i:term, o:list term.
arg-types (prod _ Ty F) [Ty | Tys] :- !, pi x\ arg-types (F x) Tys.
arg-types _ [].

% The datatypes that a term or type mentions, by its constructors.
pred datatypes-of-type i:term, o:list inductive.
datatypes-of-type T [I] :- datatype T I, !.
datatypes-of-type _ [].

% ---------------------------------------------------------------------------------------------
% Lattice tables

% A lattice relation, with the code of its merge in the primitive set and the merge function.
% The command assumes one clause for each declaration 'merge R g' after 'with <primitives>'.
pred lattice-of o:inductive, o:term, o:term.

% The keys and the value of the indices of a lattice relation: all of them but the last, and
% the last.
pred split-last i:list A, o:list A, o:A.
split-last [X] [] X :- !.
split-last [X | Xs] [X | Ys] L :- split-last Xs Ys L.

% The declarations 'merge R g' that follow 'with <primitives>'.
pred merge-decls i:list argument, o:list (pair string string).
merge-decls [] [].
merge-decls [str "merge", str R, str G | Rest] [pr R G | Ms] :- !, merge-decls Rest Ms.
merge-decls _ _ :- coq.error "Egglog: after 'with <primitives>', each lattice table is declared"
  "as 'merge <relation> <function>'.".

% A declared lattice relation, with the code of its merge and the merge function.
kind latdecl type.
type latdecl inductive -> term -> term -> latdecl.

% Run a goal with the lattice relations in scope.
pred with-lattices i:list latdecl, i:prop.
with-lattices [] G :- G.
with-lattices [latdecl I C F | Rest] G :- lattice-of I C F => with-lattices Rest G.

% The declaration 'merge R g'. R is a relation that the command reads, and g is a primitive of
% the set after 'with' that takes two values of the type of the last index of R and returns
% one.
pred lattice-decl i:list inductive, i:pair string string, o:latdecl.
lattice-decl Is (pr RName GName) (latdecl I Code (global GR)) :-
  coq.locate-all RName RLocs,
  if (std.mem RLocs (loc-gref (indt I0)), std.mem! Is I0) (I = I0)
     (coq.error "Egglog: the lattice table" RName "is not a relation that the command reads."),
  coq.locate-all GName GLocs,
  if (std.mem GLocs (loc-gref GR0)) (GR = GR0)
     (coq.error "Egglog: the merge" GName "of" RName "is not a function."),
  if (prim-of GR Code0) (Code = Code0)
     (coq.error "Egglog: the merge" GName "of" RName
       "is not a primitive of the set after 'with'."),
  check-merge-type I RName GR GName.

% The merge of a lattice relation takes two values of the type of its last index and returns
% one of that type.
pred check-merge-type i:inductive, i:string, i:gref, i:string.
check-merge-type I RName GR GName :-
  coq.env.indt I _ NP _ Arity _ _, index-types NP Arity Tys,
  if (Tys = []) (coq.error "Egglog: the lattice table" RName "has no index for its value.")
     true,
  std.last Tys T,
  coq.env.typeof GR GTy,
  if (GTy = prod _ A (_\ prod _ B (_\ C)), coq.unify-eq A T ok, coq.unify-eq B T ok,
      coq.unify-eq C T ok) true
     (coq.error "Egglog: the merge" GName "of" RName "must have the type"
       {coq.term->string {{ lp:T -> lp:T -> lp:T }}}).

% ---------------------------------------------------------------------------------------------
% Relations

kind rel type.
type rel inductive -> int -> bool -> list term -> rel.   % relation, parameters, equational?, sorts

% A lattice relation has the sorts of its keys, which are all its indices but the last.
pred rel-info i:inductive, o:rel.
rel-info I (rel I NP Eq Sorts) :-
  coq.env.indt I tt NP _ Arity _ _,
  index-types NP Arity Tys,
  if (lattice-of I _ _)
     (Eq = ff, std.forall Tys check-value, split-last Tys Keys _, std.map Keys sort-term Sorts)
     (if (Tys = [T, T], datatype T _) (Eq = tt, Sorts = [])
        (Eq = ff, std.forall Tys check-value, std.map Tys sort-term Sorts)).

pred index-types i:int, i:term, o:list term.
index-types 0 (prod _ Ty F) [Ty | Tys] :- !, pi x\ index-types 0 (F x) Tys.
index-types 0 _ [] :- !.
index-types N (prod _ _ F) Tys :- M is N - 1, pi x\ index-types M (F x) Tys.

% ---------------------------------------------------------------------------------------------
% Patterns

pred var-index i:list (pair term int), i:term, o:int.
var-index [pr X I | _] X I :- !.
var-index [_ | Vs] X I :- var-index Vs X I.

pred pat-of i:list table, i:list (pair term int), i:term, o:term.
pat-of _ Vars X {{ @PVar positive lp:P }} :- var-index Vars X I, !, int->pos I P.
pat-of Ts Vars (app [global (indc K) | Args]) {{ @PNode positive lp:Code lp:PArgs }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code,
  std.map Args (pat-of Ts Vars) Ps, list->term {{ pat positive }} Ps PArgs.
pat-of Ts _ (global (indc K)) {{ @PNode positive lp:Code nil }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code.
pat-of Ts Vars (app [global GR | Args]) {{ @POp positive lp:Code lp:PArgs }} :-
  prim-of GR Code, !, pats-of Ts Vars Args PArgs.
pat-of _ Vars T {{ @PVal positive lp:E }} :-
  not (std.exists Vars (v\ sigma X\ v = pr X _, occurs X T)),
  coq.typecheck T Ty ok, value-type Ty, !, enc-by-ty Ty T E.
pat-of _ _ T _ :- coq.error "Egglog: cannot read the term" {coq.term->string T}.

pred pats-of i:list table, i:list (pair term int), i:list term, o:term.
pats-of Ts Vars Args L :- std.map Args (pat-of Ts Vars) Ps, list->term {{ pat positive }} Ps L.

% ---------------------------------------------------------------------------------------------
% Premises and conclusions

pred find-rel i:list rel, i:inductive, o:int, o:bool.
find-rel [rel R NP Eq _ | _] R NP Eq :- !.
find-rel [_ | Rs] R NP Eq :- find-rel Rs R NP Eq.

pred premise-of i:list table, i:list rel, i:list term, i:list (pair term int), i:term,
  o:term.
premise-of Ts _ Ps Vars H {{ @Holds positive lp:Code lp:PArgs }} :-
  in-premise H Elem Coll, !, input-key Ps Elem Coll Key Args _, code-of Ts Key Code,
  pats-of Ts Vars Args PArgs.
premise-of Ts Rels _ Vars (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, !, drop NP All Args, code-of Ts (tk-rel R) Code,
  if (lattice-of R _ _)
     (split-last Args Keys Val, pats-of Ts Vars Keys PKeys, pat-of Ts Vars Val PVal,
      P = {{ @Equals positive lp:Code lp:PKeys lp:PVal }})
     (pats-of Ts Vars Args PArgs, P = {{ @Holds positive lp:Code lp:PArgs }}).
premise-of Ts _ _ Vars (app [global (indt Eq), _, app [global GR | Args], V])
    {{ @Computes positive lp:Code lp:PArgs lp:PV }} :-
  coq.locate "eq" (indt Eq), prim-of GR Code, !,
  pats-of Ts Vars Args PArgs, pat-of Ts Vars V PV.
premise-of _ _ _ _ H _ :- coq.error "Egglog: cannot read the premise" {coq.term->string H}.

% A closure law of an equational relation R: reflexivity, symmetry, transitivity or the
% congruence of one constructor.
pred closure-law i:inductive, i:int, i:list term, i:term.
closure-law R NP Hyps (app [global (indt R) | All]) :-
  drop NP All [L, Rt],
  std.map Hyps (h\ p\ sigma HA\ h = app [global (indt R) | HA], drop NP HA p) Pairs,
  closure-shape Pairs L Rt.

pred closure-shape i:list (list term), i:term, i:term.
closure-shape [] X X :- !.
closure-shape [[A, B]] B A :- !.
closure-shape [[A, B], [B, C]] A C :- !.
closure-shape Pairs (app [K | As]) (app [K | Bs]) :- cong-args Pairs As Bs.

pred cong-args i:list (list term), i:list term, i:list term.
cong-args [] [] [] :- !.
cong-args Ps [A | As] [A | Bs] :- !, cong-args Ps As Bs.
cong-args [[A, B] | Ps] [A | As] [B | Bs] :- cong-args Ps As Bs.

pred mentions i:term, i:list (pair term int), o:list int.
mentions T Vars Is :- std.filter Vars (v\ sigma X\ v = pr X _, occurs X T) Ws,
  std.map Ws (w\ i\ w = pr _ i) Is.

% The variables that the premises bind, in premise order: the variables of relation and input
% premises outside primitive applications, and the result of each equation premise whose
% arguments are bound.
pred bound-vars i:list term, i:list (pair term int), i:list int, o:list int.
bound-vars [] _ B B.
bound-vars [H | Hs] Vars B Out :- premise-binds H Vars B B1, bound-vars Hs Vars B1 Out.

pred premise-binds i:term, i:list (pair term int), i:list int, o:list int.
premise-binds (app [global (indt Eq), _, app [global GR | Args], V]) Vars B Out :-
  coq.locate "eq" (indt Eq), prim-code GR _ _, !,
  mentions (app [global GR | Args]) Vars Used,
  if (std.forall Used (i\ std.mem! B i), var-index Vars V I) (Out = [I | B]) (Out = B).
premise-binds H Vars B Out :- table-vars Vars H Is, std.append Is B Out.

% The variables of a term outside primitive applications.
pred table-vars i:list (pair term int), i:term, o:list int.
table-vars Vars X [I] :- var-index Vars X I, !.
table-vars _ (app [global GR | _]) [] :- prim-code GR _ _, !.
table-vars Vars (app [_ | Args]) Is :- !, std.map Args (table-vars Vars) Iss, std.flatten Iss Is.
table-vars _ _ [].

pred clause-of i:list table, i:list rel, i:rel, i:term, o:list term.
clause-of Ts Rels (rel R NP Eq _) KTy Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (vars\ hyps\ concl\ clause-body Ts Rels R NP Eq ps vars hyps concl Out)).

pred clause-body i:list table, i:list rel, i:inductive, i:int, i:bool, i:list term,
  i:list (pair term int), i:list term, i:term, o:list term.
clause-body _ _ R NP tt _ _ Hyps Concl [] :- closure-law R NP Hyps Concl, !.
clause-body Ts Rels R NP Eq Params Vars Hyps (app [global (indt R) | All]) [C] :-
  std.map Hyps (premise-of Ts Rels Params Vars) Ps, list->term {{ premise positive }} Ps Body,
  drop NP All Args,
  if (Eq = tt)
     (Args = [L, Rt], pat-of Ts Vars L PL, pat-of Ts Vars Rt PR,
      bound-vars Hyps Vars [] Bound,
      mentions (app [L, Rt]) Vars Used,
      if (std.forall Used (i\ std.mem! Bound i))
         (Head = {{ @Unify positive lp:PL lp:PR }})
         (Head = {{ @Rewrites positive lp:PL lp:PR }}))
     (code-of Ts (tk-rel R) Code,
      if (lattice-of R _ _)
         (split-last Args Keys Val, pats-of Ts Vars Keys PKeys, pat-of Ts Vars Val PVal,
          Head = {{ @Assign positive lp:Code lp:PKeys lp:PVal }})
         (pats-of Ts Vars Args PArgs, Head = {{ @Derive positive lp:Code lp:PArgs }})),
  C = {{ @Clause positive lp:Body lp:Head }}.

% ---------------------------------------------------------------------------------------------
% Collecting the tables of the relations

pred input-keys i:list rel, i:rel, i:term, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
input-keys _ (rel _ NP _ _) KTy Acc Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (_\ hyps\ _\ std.fold hyps Acc (add-input-key ps) Out)).

pred add-input-key i:list term, i:term, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
add-input-key Ps H Acc Out :- in-premise H Elem Coll, !, input-key Ps Elem Coll Key _ Sorts,
  if (std.exists Acc (p\ sigma S\ p = pr Key S)) (Out = Acc) (std.append Acc [pr Key Sorts] Out).
add-input-key _ _ Acc Acc.

pred datatype-tables i:list inductive, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
datatype-tables [] Acc Acc.
datatype-tables [I | Is] Acc Out :-
  coq.env.indt I _ _ _ _ Ks KTys,
  std.map2 Ks KTys (k\ ty\ e\ sigma Tys Ss\ arg-types ty Tys, std.map Tys sort-term Ss,
    e = pr (tk-con k) Ss) Es,
  std.append Acc Es Acc1, datatype-tables Is Acc1 Out.

pred number i:list (pair tkey (list term)), i:int, i:list inductive, o:list table.
number [] _ _ [].
number [pr K Ss | Rest] N Dts [table K N Ss Out | Ts] :-
  if (K = tk-rel R, lattice-of R Code _) (Out = {{ OLat lp:Code }})
     (if (K = tk-con C, std.exists Dts (d\ coq.env.indc C _ _ _ Ty, con-of d Ty))
        (Out = {{ OId }}) (Out = {{ ORel }})),
  M is N + 1, number Rest M Dts Ts.

pred undup i:list inductive, i:list inductive, o:list inductive.
undup [] Acc Out :- std.rev Acc Out.
undup [X | Xs] Acc Out :- std.mem! Acc X, !, undup Xs Acc Out.
undup [X | Xs] Acc Out :- undup Xs [X | Acc] Out.

pred con-of i:inductive, i:term.
con-of D (prod _ _ F) :- !, pi x\ con-of D (F x).
con-of D (global (indt D)).

pred decl-of i:list table, i:table, o:term.
decl-of Ts (table K _ Ss Out) {{ Decl lp:P lp:SL lp:Out }} :-
  code-of Ts K P, list->term {{ sort }} Ss SL.

% ---------------------------------------------------------------------------------------------
% Input sources and facts

kind source type.
type source tkey -> term -> source.   % the list (tk-src Head or tk-param I) and its element type

pred add-source i:list term, i:term, i:list source, o:list source.
add-source Ps H Acc Out :- in-premise H Elem Coll, !, source-key Ps Coll Key,
  coq.typecheck Elem Ty ok,
  if (std.exists Acc (s\ sigma T\ s = source Key T)) (Out = Acc)
     (std.append Acc [source Key Ty] Out).
add-source _ _ Acc Acc.

pred sources-of i:rel, i:term, i:list source, o:list source.
sources-of (rel _ NP _ _) KTy Acc Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (_\ hyps\ _\ std.fold hyps Acc (add-source ps) Out)).

pred source-coll i:list term, i:tkey, o:term.
source-coll Ps (tk-param I) P :- !, J is I - 1, std.nth J Ps P.
source-coll Ps (tk-src Head) (app [Head | Ps]).

pred mk-lams i:list term, i:list term, i:(list term -> term -> prop), o:term.
mk-lams [] Acc K T :- std.rev Acc Xs, K Xs T.
mk-lams [Ty | Tys] Acc K (fun `x` Ty B) :- pi x\ decl x `x` Ty => mk-lams Tys [x | Acc] K (B x).

pred row-list i:option term, i:term, o:term.
row-list none _ {{ @nil (positive * list positive) }}.
row-list (some Code) Vals
    {{ @cons (positive * list positive) (lp:Code, lp:Vals) (@nil (positive * list positive)) }}.

pred branch-of i:list table, i:constructor, i:term, o:term.
branch-of Ts K KTy B :- arg-types KTy Tys,
  if (find-table Ts (tk-con K) _ _ _) (code-of Ts (tk-con K) Code, Row = some Code)
     (Row = none),
  mk-lams Tys [] (xs\ body\ sigma Vals\ enc-list xs Vals, row-list Row Vals body) B.

pred rows-of i:list table, i:list term, i:source, o:term.
rows-of Ts Ps (source Key {{ prod lp:A lp:B }}) T :- !, check-value A, check-value B,
  code-of Ts Key Code,
  source-coll Ps Key Coll, PTy = {{ prod lp:A lp:B }},
  (pi p\ sigma E1 E2\ enc-by-ty A {{ @fst lp:A lp:B lp:p }} E1,
     enc-by-ty B {{ @snd lp:A lp:B lp:p }} E2, Row p = {{ (lp:Code, [lp:E1; lp:E2]) }}),
  RowF = fun `p` PTy Row,
  T = {{ @map lp:PTy (positive * list positive) lp:RowF lp:Coll }}.
rows-of Ts Ps (source Key (global (indt I))) T :- !, source-coll Ps Key Coll,
  coq.env.indt I _ _ _ _ Ks KTys,
  std.map2 Ks KTys (branch-of Ts) Bs,
  ElemTy = global (indt I),
  RetTy = {{ list (positive * list positive) }},
  F = fun `e` ElemTy (e\ match e (fun `e` ElemTy _\ RetTy) Bs),
  T = {{ @flat_map lp:ElemTy (positive * list positive) lp:F lp:Coll }}.
rows-of _ _ (source _ Ty) _ :- coq.error "Egglog: an input list has elements of type"
  {coq.term->string Ty} "which is neither an inductive nor a pair".

pred concat-rows i:list term, o:term.
concat-rows [] {{ @nil (positive * list positive) }}.
concat-rows [T] T :- !.
concat-rows [T | Ts] {{ @app (positive * list positive) lp:T lp:R }} :- concat-rows Ts R.

pred abs-params i:int, i:term, i:list term, i:(list term -> term -> prop), o:term.
abs-params 0 _ Acc K T :- !, std.rev Acc Ps, K Ps T.
abs-params N (prod Name Ty F) Acc K (fun Name Ty B) :- M is N - 1,
  pi p\ decl p Name Ty => abs-params M (F p) [p | Acc] K (B p).

pred mk-exists i:list term, i:list term, i:(list term -> term -> prop), o:term.
mk-exists [] Acc K T :- std.rev Acc Xs, K Xs T.
mk-exists [Ty | Tys] Acc K {{ @ex lp:Ty lp:F }} :-
  F = fun `x` Ty B, pi x\ decl x `x` Ty => mk-exists Tys [x | Acc] K (B x).

% The meaning of the rows of a relation over values: [r] is its code and [vs] its indices.
pred rel-disjunct i:list table, i:list term, i:term, i:term, i:rel, o:term.
rel-disjunct Ts Ps R0 VS (rel R NP _ _) D :-
  code-of Ts (tk-rel R) Code, coq.env.indt R _ _ _ Ar _ _, index-types NP Ar Tys,
  mk-exists Tys [] (xs\ b\ sigma Vs Args RApp\ enc-list xs Vs,
    std.append Ps xs Args, RApp = app [global (indt R) | Args],
    b = {{ lp:VS = lp:Vs /\ lp:RApp }}) Ex,
  D = {{ lp:R0 = lp:Code /\ lp:Ex }}.

pred disj i:list term, o:term.
disj [T] T :- !.
disj [T | Ts] {{ lp:T \/ lp:R }} :- disj Ts R.

pred mk-rel-fun i:list table, i:list term, i:list rel, i:term, o:term.
mk-rel-fun Ts Ps Relational FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ B r vs) :-
  pi r vs\ sigma Ds Inp\ std.map Relational (rel-disjunct Ts Ps r vs) Ds,
    Inp = {{ In (lp:r, lp:vs) lp:FB }}, disj [Inp | Ds] (B r vs).

pred mk-inputs-fun i:term, o:term.
mk-inputs-fun FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ {{ In (lp:r, lp:vs) lp:FB }}).

% The meaning of the rows of a program with lattice tables. It is a disjunction even when no
% relation over values has rows, so that the tactics read it in one way.
pred mk-lat-rel-fun i:list table, i:list term, i:list rel, i:term, o:term.
mk-lat-rel-fun Ts Ps Relational FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ B r vs) :-
  pi r vs\ sigma Ds Inp\ std.map Relational (rel-disjunct Ts Ps r vs) Ds,
    Inp = {{ In (lp:r, lp:vs) lp:FB }},
    if (Ds = []) (B r vs = {{ lp:Inp \/ False }}) (disj [Inp | Ds] (B r vs)).

% The meaning of the values of a lattice relation: [f] is its code, [ks] its keys and [w] its
% value.
pred lat-disjunct i:list table, i:list term, i:term, i:term, i:term, i:rel, o:term.
lat-disjunct Ts Ps F0 KS W0 (rel R NP _ _) D :-
  code-of Ts (tk-rel R) Code, coq.env.indt R _ _ _ Ar _ _, index-types NP Ar Tys,
  mk-exists Tys [] (xs\ b\ sigma Keys Val Ks W Args RApp\ split-last xs Keys Val,
    enc-list Keys Ks, enc-term Val W, std.append Ps xs Args,
    RApp = app [global (indt R) | Args],
    b = {{ lp:KS = lp:Ks /\ lp:W0 = lp:W /\ lp:RApp }}) Ex,
  D = {{ lp:F0 = lp:Code /\ lp:Ex }}.

% The meaning of the lattice tables of a program, as a relation on codes, keys and values.
pred mk-lat-fun i:list table, i:list term, i:list rel, o:term.
mk-lat-fun Ts Ps Lattices
    (fun `f` {{ positive }} f\ fun `ks` {{ list positive }} ks\ fun `w` {{ positive }} w\
       B f ks w) :-
  pi f ks w\ sigma Ds\ std.map Lattices (lat-disjunct Ts Ps f ks w) Ds, disj Ds (B f ks w).

pred facts-body i:list table, i:list source, i:list term, o:term.
facts-body Ts Sources Ps FB :- std.map Sources (rows-of Ts Ps) Rows, concat-rows Rows FB.

% ---------------------------------------------------------------------------------------------
% ---------------------------------------------------------------------------------------------
% Glue: each relational constructor fires its clause

% The position of an element in a list, from 0.
pred position i:list term, i:term, o:int.
position [X | _] X 0 :- !.
position [_ | L] X N :- position L X M, N is M + 1.

% A proof that the N-th element of a concrete list is in it.
pred in-proof i:int, o:term.
in-proof 0 {{ or_introl eq_refl }} :- !.
in-proof N {{ or_intror lp:P }} :- M is N - 1, in-proof M P.

% The type of a fire lemma: the constructor type with each relational premise and the
% conclusion read as derived rows.
pred fire-type i:list table, i:list rel, i:term, i:term, i:term, i:term, o:term.
fire-type Ts Rels Prim Spec I (prod N Ty F) (prod N Ty1 F1) :- !,
  derived-of Ts Rels Prim Spec I Ty Ty1,
  pi x\ decl x N Ty => fire-type Ts Rels Prim Spec I (F x) (F1 x).
fire-type Ts Rels Prim Spec I C C1 :- derived-of Ts Rels Prim Spec I C C1.

pred derived-of i:list table, i:list rel, i:term, i:term, i:term, i:term, o:term.
derived-of Ts Rels Prim Spec I (app [global (indt R) | All])
    {{ @derived positive lp:Prim lp:Spec lp:I lp:Code lp:Vs }} :-
  find-rel Rels R NP ff, !, drop NP All Idx, code-of Ts (tk-rel R) Code,
  enc-list Idx Vs.
derived-of _ _ _ _ _ T T.

% The proof of a fire lemma: lambdas over the binders and premises, and the clause applied to
% the environment of the binders.
pred fire-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term int), i:list (pair term term), i:term, o:term.
fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps (prod N Ty F) (fun N Ty1 B) :- !,
  derived-of Ts Rels Prim Spec I Ty Ty1,
  pi x\ sigma Hyps1 L J Vars1\ decl x N Ty1 =>
    if (is-prop Ty)
       (std.append Hyps [pr x Ty1] Hyps1,
        fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps1 (F x) (B x))
       (std.length Vars L, J is L + 1, std.append Vars [pr x J] Vars1,
        fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars1 Hyps (F x) (B x)).
fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, drop NP All Idx, code-of Ts (tk-rel R) Code,
  enc-list Idx Vs,
  std.map Vars (v\ x\ v = pr x _) Xs, enc-list Xs EnvL,
  Env = {{ @env_of positive lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT (@Derive positive _ lp:ArgsP) }},
  body-proof Ts Rels Prim Spec I Env Ps Hyps BodyT BodyP,
  P = {{ @derived_clause positive lp:Prim lp:Spec lp:I lp:Ck lp:Env lp:Code lp:ArgsP lp:Vs
          lp:Kn eq_refl lp:BodyP _ }}.

pred body-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term term), i:term, o:term.
body-proof _ _ Prim Spec I Env _ [] _ {{ @derived_nil positive lp:Prim lp:Spec lp:I lp:Env }}.
body-proof Ts Rels Prim Spec I Env Ps [pr _ Ty | Hs]
    {{ @cons _ (@Computes _ lp:Q lp:Args lp:V) lp:Rest }} P :- !,
  body-proof Ts Rels Prim Spec I Env Ps Hs Rest RestP,
  computes-values Ty Vs W,
  P = {{ @derived_computes positive lp:Prim lp:Spec lp:I lp:Env lp:Q lp:Args lp:V lp:Vs lp:W
          lp:Rest _ _ _ lp:RestP }}.
body-proof Ts Rels Prim Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Holds _ lp:Code lp:Args) lp:Rest }} P :-
  body-proof Ts Rels Prim Spec I Env Ps Hs Rest RestP,
  hyp-row Ts Rels Prim Spec I Ps H Ty Code Vs Row,
  P = {{ @derived_row positive lp:Prim lp:Spec lp:I lp:Env lp:Code lp:Args lp:Vs lp:Rest _
          lp:Row lp:RestP }}.

% The derived row of a premise: an input row, or the premise itself for a relation.
pred hyp-row i:list table, i:list rel, i:term, i:term, i:term, i:list term, i:term, i:term,
  o:term, o:term, o:term.
hyp-row Ts _ Prim Spec I Ps _ Ty Code Vs Row :- in-premise Ty Elem Coll, !,
  input-key Ps Elem Coll Key Args _, code-of Ts Key Code, enc-list Args Vs,
  Row = {{ @derived_input positive lp:Prim lp:Spec lp:I lp:Code lp:Vs
            _ _ }}.
hyp-row _ _ _ _ _ _ H {{ @derived positive _ _ _ lp:Code lp:Vs }} Code Vs H.

% The engine accepts the sorts of the lowered program, or the command stops before it defines
% anything.
pred check-sorts i:string, i:term.
check-sorts Name Spec :-
  coq.reduction.vm.norm {{ @spec_ok positive lp:Spec }} {{ bool }} B,
  if (B = {{ true }}) true
     (coq.error {calc ("Egglog: the engine rejects the sorts of the program " ^ Name ^ ".")}
       "A primitive in a premise argument must apply to variables that a relation premise"
       "binds, and an equation premise must compute its result from such variables.").

pred run-tactic i:string, i:sealed-goal.
run-tactic Name G :- coq.ltac.open (g\ gl\ coq.ltac.call Name [] g gl ok) G [].


% Prove a type with an Ltac tactic, which runs on every hole of the proof term.
pred prove i:string, i:term, o:term.
prove Name Ty P :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  if (std.forall Goals (run-tactic Name)) true
     (coq.error "Egglog: the tactic" Name "failed").



% ---------------------------------------------------------------------------------------------
% Primitives

% The primitive function of a program: the fixed one of its primitive set, or a bound one.
pred fixed-prim o:term.
pred bind-prim i:bool, i:(term -> term -> prop), o:term.
bind-prim _ K Out :- fixed-prim F, !, K F Out.
bind-prim IsProd K Out :- prim-type PT,
  if (IsProd = tt) (Out = prod `prim` PT B) (Out = fun `prim` PT B),
  pi prim\ decl prim `prim` PT => K prim (B prim).

% The code of a primitive in the primitive set that the command names after [with]. A
% primitive of another set, or of no named set, stops the command.
pred prim-of i:gref, o:term.
prim-of GR Code :- fixed-prim F, prim-code GR Code F, !.
prim-of GR _ :- prim-code GR _ _, !, coq.error "Egglog:" {coq.gref->id GR}
  "is a primitive of a set that the command does not name after 'with'".

% The arguments and the result of a primitive premise [f x1 .. xn = w].
pred computes-values i:term, o:term, o:term.
computes-values (app [global (indt _), _, app [_ | Xs], W0]) Vs W :-
  enc-list Xs Vs, enc-term W0 W.

% The primitive function among the arguments of a lemma that quantifies over it.
pred prim-args i:term, o:list term.
prim-args _ [] :- fixed-prim _, !.
prim-args P [P].

% The arity of a primitive.
pred prim-arity i:term, o:int.
prim-arity (prod _ _ F) N :- !, (pi x\ prim-arity (F x) M), N is M + 1.
prim-arity _ 0.

% The type of the result of a function type.
pred prim-result i:term, o:term.
prim-result (prod _ _ F) R :- !, pi x\ prim-result (F x) R.
prim-result R R.

% The call of a function on engine values: its arguments are decoded and its result is encoded.
pred prim-apply i:int, i:term, i:term, o:term.
prim-apply N F Ty Call :- arg-types Ty Tys, prim-result Ty R,
  std.map Tys dec-of-type Decs, enc-of-type R Enc, prim-apply-with N F Decs Enc Call.

pred prim-apply-with i:int, i:term, i:list term, i:term, o:term.
prim-apply-with 1 F [Da] E {{ @prim1d _ _ lp:Da lp:E lp:F }} :- !.
prim-apply-with 2 F [Da, Db] E {{ @prim2d _ _ _ lp:Da lp:Db lp:E lp:F }} :- !.
prim-apply-with 3 F [Da, Db, Dc] E
    {{ @prim3d _ _ _ _ lp:Da lp:Db lp:Dc lp:E lp:F }} :- !.
prim-apply-with N _ _ _ _ :-
  coq.error "Egglog: a primitive has arity" N "and only 1 to 3 are supported".

% The body of the primitive function of a set: a test of each code in turn.
pred prim-body i:list (pair term term), i:term, i:term, o:term.
prim-body [] _ _ {{ @None positive }}.
prim-body [pr Code Call | Rest] P Vs {{ prim_case lp:P lp:Code lp:Call lp:Vs lp:R }} :-
  prim-body Rest P Vs R.

pred define-prims i:list gref, i:int, o:list (pair gref term), o:list (pair term term).
define-prims [] _ [] [].
define-prims [GR | GRs] N [pr GR (global (const C)) | Cs] [pr (global (const C)) Call | Bs] :-
  int->pos N P, Name is {coq.gref->id GR} ^ "_code",
  coq.env.add-const Name P {{ positive }} @transparent! C,
  coq.env.typeof GR Ty, prim-arity Ty A, prim-apply A (global GR) Ty Call,
  M is N + 1, define-prims GRs M Cs Bs.

pred params-binders i:int, i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
params-binders 0 _ _ Acc K T :- !, std.rev Acc Ps, K Ps T.
params-binders N (prod Name Ty F) IsProd Acc K Out :- M is N - 1,
  if (IsProd = tt) (Out = prod Name Ty B) (Out = fun Name Ty B),
  pi p\ decl p Name Ty => params-binders M (F p) IsProd [p | Acc] K (B p).

pred prim-type o:term.
prim-type {{ positive -> list positive -> option positive }}.

% The type and proof of the fire lemma of one constructor, whose clause is the Idx-th.
pred fire-lemma i:list table, i:list rel, i:term, i:term, i:int, i:term, i:term, i:int,
  o:term, o:term.
fire-lemma Ts Rels Spec Inputs NP KTy Ck Idx Ty P :-
  in-proof Idx Kn,
  bind-prim tt (prim\ ty\ params-binders NP KTy tt [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps], fire-type Ts Rels prim Spec I Inst t) ty) Ty,
  bind-prim ff (prim\ p\ params-binders NP KTy ff [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps],
    fire-proof Ts Rels prim Spec I Ck Kn ps [] [] Inst t) p) P.

pred idx-binders i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
idx-binders (prod N0 Ty F) IsProd Acc K Out :- !, std.length Acc I, idx-name N0 I N,
  if (IsProd = tt) (Out = prod N Ty B) (Out = fun N Ty B),
  pi x\ decl x N Ty => idx-binders (F x) IsProd [x | Acc] K (B x).
idx-binders _ _ Acc K T :- std.rev Acc Xs, K Xs T.

% The name of an index binder: its own name, or a letter by its position when it has none.
pred idx-name i:name, i:int, o:name.
idx-name N I M :- coq.name->id N "_", I < 8, !,
  std.nth I ["a", "b", "c", "d", "e", "f", "g", "h"] S, coq.id->name S M.
idx-name N _ N.

% forall prim params idx, R params idx -> derived prim spec (inputs params) code idx
pred complete-type i:list table, i:term, i:term, i:rel, o:term.
complete-type Ts Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ enc-list xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = prod `H` RApp
          (_\ {{ @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }})) t) ty) Ty.

% forall params idx, relation params code idx -> R params idx
pred back-type i:list table, i:term, i:rel, o:term.
back-type Ts Relation (rel R NP _ _) T :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp Rel\ enc-list xs Vs,
      std.append ps xs Args, RApp = app [global (indt R) | Args],
      Rel = app [Relation | {std.append ps [Code, Vs]}], c = prod `H` Rel (_\ RApp)) t) T.

% forall prim params r vs, derived prim spec (inputs params) r vs -> relation params r vs
pred closed-type i:term, i:term, i:term, i:int, i:term, o:term.
closed-type Spec Inputs Relation NP Arity Ty :-
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma I Rel\ I = app [Inputs | ps],
      Rel = app [Relation | ps],
      t = {{ forall (r : positive) (vs : list positive),
               @derived positive lp:prim lp:Spec lp:I r vs -> lp:Rel r vs }}) ty) Ty.

% The equivalence of R with its derived rows, from the two directions.
pred spec-proof i:list table, i:rel, i:term, i:term, i:term, i:term, o:term.
spec-proof Ts (rel R NP _ _) Complete Back Closed _Inputs P :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim ff (prim\ pf\ sigma PA\ prim-args prim PA,
    params-binders NP Arity ff [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst ff [] (xs\ c\ sigma Vs Args C1 B1 K1 CA KA\
        enc-list xs Vs,
        std.append ps xs Args, std.append PA Args CA, std.append PA ps KA,
        C1 = app [Complete | CA], B1 = app [Back | Args], K1 = app [Closed | KA],
        c = {{ conj lp:C1 (fun h => lp:B1 (lp:K1 lp:Code lp:Vs h)) }}) t) pf) P.

% forall prim params idx, R params idx <-> derived prim spec (inputs params) code idx
pred spec-type i:list table, i:term, i:term, i:rel, o:term.
spec-type Ts Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ enc-list xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = {{ lp:RApp <-> @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }}) t) ty) Ty.

% Define the glue of the relational relations of a program.
pred define-glue i:list table, i:list rel, i:list term, i:term, i:term, i:term.
define-glue Ts Rels ClauseList Spec Inputs Relation :-
  std.filter Rels (r\ r = rel _ _ ff _) Relational,
  Relational = [rel R1 NP _ _ | _], !,
  coq.env.indt R1 _ _ _ Arity1 _ _,
  std.forall Relational (define-fires Ts Rels ClauseList Spec Inputs),
  closed-type Spec Inputs Relation NP Arity1 ClosedTy,
  prove "egglog_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  std.forall Relational (define-spec Ts Spec Inputs Relation (global (const ClosedC))).

define-glue _ _ _ _ _ _.

pred define-fires i:list table, i:list rel, i:list term, i:term, i:term, i:rel.
define-fires Ts Rels ClauseList Spec Inputs (rel R NP Eq Ss) :-
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Ck Idx Ty P C Name\
    clause-of Ts Rels (rel R NP Eq Ss) kty [Ck], position ClauseList Ck Idx,
    fire-lemma Ts Rels Spec Inputs NP kty Ck Idx Ty P,
    prove "egglog_leaf" Ty P,
    Name is {coq.gref->id (indc k)} ^ "_fires",
    coq.env.add-const Name P Ty @opaque! C,
    coq.hints.add-resolve (const C) "egglog_fire" 0 _).

pred define-spec i:list table, i:term, i:term, i:term, i:term, i:rel.
define-spec Ts Spec Inputs Relation Closed (rel R NP Eq Ss) :-
  RName = {coq.gref->id (indt R)},
  complete-type Ts Spec Inputs (rel R NP Eq Ss) CTy,
  prove "egglog_complete" CTy CP,
  coq.env.add-const {calc (RName ^ "_derived")} CP CTy @opaque! CC,
  back-type Ts Relation (rel R NP Eq Ss) BTy,
  prove "egglog_back" BTy BP,
  coq.env.add-const {calc (RName ^ "_back")} BP BTy @opaque! BC,
  spec-proof Ts (rel R NP Eq Ss) (global (const CC)) (global (const BC)) Closed Inputs SP,
  spec-type Ts Spec Inputs (rel R NP Eq Ss) STy,
  std.assert-ok! (coq.elaborate-skeleton SP STy SP1) "Egglog: the glue lemma failed",
  coq.env.add-const {calc (RName ^ "_spec")} SP1 STy @opaque! _.

% ---------------------------------------------------------------------------------------------
% The name of the code constant of a table. A parameter that is an input list names its table.
pred code-name i:list string, i:table, o:string.
code-name _ (table (tk-rel R) _ _ _) N :- !, N is {coq.gref->id (indt R)} ^ "_code".
code-name _ (table (tk-con K) _ _ _) N :- !, N is {coq.gref->id (indc K)} ^ "_code".
code-name _ (table (tk-src (global GR)) _ _ _) N :- !, N is {coq.gref->id GR} ^ "_code".
code-name PNames (table (tk-param I) _ _ _) N :- std.nth {calc (I - 1)} PNames P,
  N is P ^ "_code".

% The names of the first N binders of a type: the parameters of a relation.
pred param-names i:int, i:term, o:list string.
param-names 0 _ [] :- !.
param-names N (prod Name _ F) [S | Ss] :- coq.name->id Name S, M is N - 1,
  pi x\ param-names M (F x) Ss.

% Define the code constant of a table.
pred define-code i:list string, i:table, o:pair tkey term.
define-code PNames T (pr K (global (const C))) :- T = table K N _ _,
  code-name PNames T Name, int->pos N P,
  coq.env.add-const Name P {{ positive }} @transparent! C.

% ---------------------------------------------------------------------------------------------
% Encoders of datatypes

% The expression of a constructor argument: the encoder on the datatype, a literal on a value.
pred encode-arg i:inductive, i:term, i:term, i:term, o:term.
encode-arg D F Ty X {{ lp:F lp:X }} :- Ty = global (indt D), !.
encode-arg _ _ Ty X {{ @Model.ELit positive lp:E }} :- value-type Ty, !, enc-by-ty Ty X E.
encode-arg _ _ Ty _ _ :- coq.error "Egglog: a datatype argument has type"
  {coq.term->string Ty} "which is neither positive nor the datatype itself".

pred encode-branch i:list table, i:inductive, i:term, i:constructor, i:term, o:term.
encode-branch Ts D F K KTy B :- arg-types KTy Tys, code-of Ts (tk-con K) Code,
  mk-lams Tys [] (xs\ body\ sigma Es L\ std.map2 Tys xs (encode-arg D F) Es,
    list->term {{ @Model.expr positive }} Es L, body = {{ @Model.EApp positive lp:Code lp:L }}) B.

pred encoder i:list table, i:inductive, o:term.
encoder Ts D Fix :-
  T = global (indt D), RetTy = {{ @Model.expr positive }},
  coq.env.indt D _ _ _ _ Ks KTys,
  (pi f\ std.map2 Ks KTys (encode-branch Ts D f) (Bs f)),
  Fix = fix `encode` 0 {{ lp:T -> lp:RetTy }}
          (f\ fun `t` T (t\ match t (fun `t` T _\ RetTy) (Bs f))).

pred define-encoder i:list table, i:inductive, o:pair inductive term.
define-encoder Ts D (pr D (global (const C))) :- encoder Ts D Fix,
  std.assert-ok! (coq.elaborate-skeleton Fix Ty FixE) "Egglog: an ill-typed encoder",
  Name is "encode_" ^ {coq.gref->id (indt D)},
  coq.env.add-const Name FixE Ty @transparent! C.

% ---------------------------------------------------------------------------------------------
% Glue of an equational relation: each relation instance is a congruence of encodings

pred enc-of i:list (pair inductive term), i:term, o:term.
enc-of Encs (global (indt D)) E :- std.exists Encs (p\ p = pr D E), !.

% The type of the fire lemma of an equational constructor.
pred eq-fire-type i:inductive, i:int, i:list (pair inductive term), i:term, i:term, i:term,
  i:term, o:term.
eq-fire-type R NP Encs Prim Spec I (prod N Ty F) (prod N Ty F1) :- !,
  pi x\ decl x N Ty => eq-fire-type R NP Encs Prim Spec I (F x) (F1 x).
eq-fire-type R NP Encs Prim Spec I (app [global (indt R) | All])
    {{ @congruent positive lp:Prim lp:Spec lp:I lp:TL lp:TR }} :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt].

% The term of a binder in the environment of an equational clause.
pred binder-expr i:list (pair inductive term), i:term, i:term, o:term.
binder-expr _ Ty X {{ @Model.ELit positive lp:E }} :- value-type Ty, !, enc-by-ty Ty X E.
binder-expr Encs Ty X (app [Enc, X]) :- enc-of Encs Ty Enc.

pred eq-fire-proof i:list table, i:inductive, i:int, i:list (pair inductive term), i:term,
  i:term, i:term, i:term, i:term, i:list term, i:list term, i:list term, i:term, o:term.
eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps (prod N Ty F) (fun N Ty B) :- !,
  pi x\ sigma Vals1 Hyps1 E\ decl x N Ty =>
    if (is-prop Ty)
       (std.append Hyps [x] Hyps1,
        eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps1 (F x) (B x))
       (binder-expr Encs Ty x E, std.append Vals [E] Vals1,
        eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals1 Hyps (F x) (B x)).
eq-fire-proof _ R NP Encs Prim Spec I Ck Kn _ Vals Hyps (app [global (indt R) | All]) P :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt],
  list->term {{ @Model.expr positive }} Vals EnvL,
  Env = {{ @env_of (@Model.expr positive) lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT lp:Head }},
  if (Head = {{ @Unify positive lp:PL lp:PR }})
     (Which = {{ or_introl eq_refl }})
     (Head = {{ @Rewrites positive lp:PL lp:PR }}, Which = {{ or_intror eq_refl }}),
  eq-body-proof Prim I Env Hyps BodyT BodyP,
  P = {{ @congruent_clause positive lp:Prim lp:Spec lp:I lp:Ck lp:Env lp:PL lp:PR lp:TL lp:TR
          lp:Kn lp:Which lp:BodyP _ _ }}.

% The premises of a ground clause hold in the input rows: one hole per input row or primitive.
pred eq-body-proof i:term, i:term, i:term, i:list term, i:term, o:term.
eq-body-proof Prim I Env [] _ {{ @Forall_nil _ (@input_premise positive lp:Prim lp:I lp:Env) }}.
eq-body-proof Prim I Env [H | Hs] {{ @cons _ lp:Prem lp:Rest }} P :-
  eq-body-proof Prim I Env Hs Rest RestP,
  input-premise-proof H Prem PP,
  P = {{ @Forall_cons _ (@input_premise positive lp:Prim lp:I lp:Env) lp:Prem lp:Rest
          lp:PP lp:RestP }}.

pred input-premise-proof i:term, i:term, o:term.
input-premise-proof H {{ @Computes _ _ _ _ }}
    {{ ex_intro _ lp:Vs (ex_intro _ lp:W (conj _ (conj _ _))) }} :- !,
  coq.typecheck H Ty ok, computes-values Ty Vs W.
input-premise-proof _ _ {{ ex_intro _ _ (conj eq_refl _) }}.

% forall prim params t u, R params t u -> congruent prim spec (inputs params) (enc t) (enc u)
pred congruent-type i:list (pair inductive term), i:term, i:term, i:rel, o:term.
congruent-type Encs Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, index-types NP Arity [T, _], enc-of Encs T Enc,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Args RApp I TL TR A B\ std.append ps xs Args,
        RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        xs = [A, B], TL = app [Enc, A], TR = app [Enc, B],
        c = prod `H` RApp
          (_\ {{ @congruent positive lp:prim lp:Spec lp:I lp:TL lp:TR }})) t) ty) Ty.

pred define-eq-glue i:list table, i:list rel, i:list term, i:list (pair inductive term),
  i:term, i:term, i:rel.
define-eq-glue Ts Rels ClauseList Encs Spec Inputs (rel R NP tt Ss) :- !,
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Cs Ck\
    clause-of Ts Rels (rel R NP tt Ss) kty Cs,
    if (Cs = [Ck])
       (sigma Idx Kn Ty P C Name\ position ClauseList Ck Idx, in-proof Idx Kn,
        bind-prim tt (prim\ ty\ params-binders NP kty tt [] (ps\ t\ sigma Inst I\
          coq.subst-prod ps kty Inst, I = app [Inputs | ps],
          eq-fire-type R NP Encs prim Spec I Inst t) ty) Ty,
        bind-prim ff (prim\ pf\ params-binders NP kty ff [] (ps\ t\ sigma Inst I\
          coq.subst-prod ps kty Inst, I = app [Inputs | ps],
          eq-fire-proof Ts R NP Encs prim Spec I Ck Kn ps [] [] Inst t) pf) P,
        prove "egglog_leaf" Ty P,
        Name is {coq.gref->id (indc k)} ^ "_fires",
        coq.env.add-const Name P Ty @opaque! C,
        coq.hints.add-resolve (const C) "egglog_fire" 0 _)
       true),
  congruent-type Encs Spec Inputs (rel R NP tt Ss) CTy,
  prove "egglog_congruent" CTy CP,
  coq.env.add-const {calc ({coq.gref->id (indt R)} ^ "_congruent")} CP CTy @opaque! _.
define-eq-glue _ _ _ _ _ _ _.

% -------------------------------------------------------------------------------------------
% Glue of a program with lattice tables

% The meaning of the indices of a relation over values in a program with lattice tables: a
% value that the clauses assign at the keys for a lattice relation, and a row otherwise.
pred lat-meaning i:term, i:term, i:term, i:term, i:inductive, i:term, i:list term, o:term.
lat-meaning Prim Merge Spec I R Code Xs T :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W,
  T = {{ @lat_assigned positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Ks lp:W }}.
lat-meaning Prim Merge Spec I _ Code Xs T :- enc-list Xs Vs,
  T = {{ @lat_derived positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Vs }}.

% A premise or the conclusion of a fire lemma, with a relation over values read by its meaning.
pred lat-derived-of i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, o:term.
lat-derived-of Ts Rels Prim Merge Spec I (app [global (indt R) | All]) T :-
  find-rel Rels R NP ff, !, drop NP All Idx, code-of Ts (tk-rel R) Code,
  lat-meaning Prim Merge Spec I R Code Idx T.
lat-derived-of _ _ _ _ _ _ T T.

% The type of a fire lemma: the constructor type with each premise and the conclusion over a
% relation over values read by its meaning.
pred lat-fire-type i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, o:term.
lat-fire-type Ts Rels Prim Merge Spec I (prod N Ty F) (prod N Ty1 F1) :- !,
  lat-derived-of Ts Rels Prim Merge Spec I Ty Ty1,
  pi x\ decl x N Ty => lat-fire-type Ts Rels Prim Merge Spec I (F x) (F1 x).
lat-fire-type Ts Rels Prim Merge Spec I C C1 :- lat-derived-of Ts Rels Prim Merge Spec I C C1.

% The proof of a fire lemma: lambdas over the binders and premises, and the clause of the
% constructor applied to the environment of the binders.
pred lat-fire-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, i:term,
  i:list term, i:list (pair term int), i:list (pair term term), i:term, o:term.
lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps (prod N Ty F) (fun N Ty1 B) :- !,
  lat-derived-of Ts Rels Prim Merge Spec I Ty Ty1,
  pi x\ sigma Hyps1 L J Vars1\ decl x N Ty1 =>
    if (is-prop Ty)
       (std.append Hyps [pr x Ty1] Hyps1,
        lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps1 (F x) (B x))
       (std.length Vars L, J is L + 1, std.append Vars [pr x J] Vars1,
        lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars1 Hyps (F x) (B x)).
lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, drop NP All Idx, code-of Ts (tk-rel R) Code,
  std.map Vars (v\ x\ v = pr x _) Xs, enc-list Xs EnvL,
  Env = {{ @env_of positive lp:EnvL }},
  if (lattice-of R _ _)
     (split-last Idx Keys Val, enc-list Keys Ks, enc-term Val W,
      Ck = {{ @Clause positive lp:BodyT (@Assign positive _ lp:ArgsP lp:VP) }},
      lat-body-proof Ts Prim Merge Spec I Env Ps Hyps BodyT BodyP,
      P = {{ @lat_assigned_clause positive lp:Prim lp:Merge lp:Spec lp:I lp:Ck lp:Env lp:Code
              lp:ArgsP lp:VP lp:Ks lp:W lp:Kn eq_refl lp:BodyP _ _ }})
     (enc-list Idx Vs,
      Ck = {{ @Clause positive lp:BodyT (@Derive positive _ lp:ArgsP) }},
      lat-body-proof Ts Prim Merge Spec I Env Ps Hyps BodyT BodyP,
      P = {{ @lat_derived_clause positive lp:Prim lp:Merge lp:Spec lp:I lp:Ck lp:Env lp:Code
              lp:ArgsP lp:Vs lp:Kn eq_refl lp:BodyP _ }}).

% The proof of a body: a row for each relation premise, the merge of one assigned value for
% each read of a lattice table, and holes for the primitive premises.
pred lat-body-proof i:list table, i:term, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term term), i:term, o:term.
lat-body-proof _ Prim Merge Spec I Env _ [] _
    {{ @lat_body_nil positive lp:Prim lp:Merge lp:Spec lp:I lp:Env }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr _ Ty | Hs]
    {{ @cons _ (@Computes _ lp:Q lp:Args lp:V) lp:Rest }} P :- !,
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  computes-values Ty Vs W,
  P = {{ @lat_body_computes positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Q lp:Args lp:V
          lp:Vs lp:W lp:Rest _ _ _ lp:RestP }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Equals _ lp:Code lp:Args lp:V) lp:Rest }} P :- !,
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  Ty = {{ @lat_assigned positive _ _ _ _ _ lp:Ks lp:W }},
  P = {{ @lat_body_read positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Code lp:Args lp:V
          lp:Ks lp:W lp:Rest _ _
          (@lat_merged_one positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Ks lp:W lp:H)
          lp:RestP }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Holds _ lp:Code lp:Args) lp:Rest }} P :-
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  lat-hyp-row Ts Prim Merge Spec I Ps Ty Code H Vs Row,
  P = {{ @lat_body_row positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Code lp:Args lp:Vs
          lp:Rest _ lp:Row lp:RestP }}.

% The row of a relation premise: an input row, or the premise itself for a relation over values.
pred lat-hyp-row i:list table, i:term, i:term, i:term, i:term, i:list term, i:term, i:term,
  i:term, o:term, o:term.
lat-hyp-row Ts Prim Merge Spec I Ps Ty Code _ Vs Row :- in-premise Ty Elem Coll, !,
  input-key Ps Elem Coll Key Args _, code-of Ts Key Code, enc-list Args Vs,
  Row = {{ @lat_derived_input positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Vs _ _ }}.
lat-hyp-row _ _ _ _ _ _ {{ @lat_derived positive _ _ _ _ lp:Code lp:Vs }} Code H Vs H.

% Define the fire lemma of each constructor of a relation over values.
pred define-lat-fires i:list table, i:list rel, i:list term, i:term, i:term, i:term, i:term,
  i:rel.
define-lat-fires Ts Rels ClauseList Prim Merge Spec Inputs (rel R NP Eq Ss) :-
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Ck Idx Kn Ty P C Name\
    clause-of Ts Rels (rel R NP Eq Ss) kty [Ck], position ClauseList Ck Idx, in-proof Idx Kn,
    params-binders NP kty tt [] (ps\ t\ sigma Inst I\ coq.subst-prod ps kty Inst,
      I = app [Inputs | ps], lat-fire-type Ts Rels Prim Merge Spec I Inst t) Ty,
    params-binders NP kty ff [] (ps\ t\ sigma Inst I\ coq.subst-prod ps kty Inst,
      I = app [Inputs | ps], lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn ps [] [] Inst t) P,
    prove "egglog_leaf" Ty P,
    Name is {coq.gref->id (indc k)} ^ "_fires",
    coq.env.add-const Name P Ty @opaque! C,
    coq.hints.add-resolve (const C) "egglog_fire" 0 _).

% A body reads the lattice table with code [Code].
pred body-reads i:term, i:term.
body-reads {{ @cons _ (@Equals _ lp:C _ _) _ }} Code :- C = Code, !.
body-reads {{ @cons _ _ lp:Rest }} Code :- body-reads Rest Code.

% Some clause reads the lattice relation.
pred read-lattice i:list table, i:list term, i:rel.
read-lattice Ts ClauseList (rel R _ _ _) :- code-of Ts (tk-rel R) Code,
  std.exists ClauseList (c\ sigma B\ c = {{ @Clause positive lp:B _ }}, body-reads B Code).

% forall params keys a b, R params keys a -> R params keys b -> R params keys (g a b)
pred merges-type i:rel, i:term, o:term.
merges-type (rel R NP _ _) G Ty :-
  coq.env.indt R _ _ _ Arity _ _, index-types NP Arity Tys, std.last Tys VTy,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ merges-body R ps xs G VTy c) t) Ty.

pred merges-body i:inductive, i:list term, i:list term, i:term, i:term, o:term.
merges-body R Ps Xs G VTy (prod `other` VTy B) :-
  split-last Xs Keys A, std.append Ps Xs ArgsA,
  pi b\ sigma KB KM ArgsB ArgsM\
    std.append Keys [b] KB, std.append Ps KB ArgsB,
    std.append Keys [app [G, A, b]] KM, std.append Ps KM ArgsM,
    B b = prod `Ha` (app [global (indt R) | ArgsA])
      (_\ prod `Hb` (app [global (indt R) | ArgsB]) (_\ app [global (indt R) | ArgsM])).

% Prove a type with an Ltac tactic, which runs on every hole of the proof term, or stop the
% command with a message.
pred prove-or i:string, i:term, o:term, i:string.
prove-or Name Ty P Msg :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  if (std.forall Goals (run-tactic Name)) true (coq.error Msg).

% Define the lemma that a lattice relation that a clause reads is closed under its merge.
pred define-merges i:rel.
define-merges (rel R NP Eq Ss) :-
  lattice-of R _ G, merges-type (rel R NP Eq Ss) G Ty,
  RName = {coq.gref->id (indt R)},
  prove-or "egglog_merges" Ty P
    {calc ("Egglog: a clause reads the lattice table " ^ RName ^ ", so " ^ RName ^
      " must be closed under its merge. The merge must return one of its two arguments, or" ^
      " a constructor of " ^ RName ^ " must merge two of its values.")},
  coq.env.add-const {calc (RName ^ "_merges")} P Ty @opaque! C,
  coq.hints.add-resolve (const C) "egglog_merges" 0 _.

% forall params, (forall r vs, lat_derived .. r vs -> relation params r vs) /\
%   (forall f ks w, lat_assigned .. f ks w -> lattice params f ks w)
pred lat-closed-type i:term, i:term, i:term, i:term, i:term, i:term, i:int, i:term, o:term.
lat-closed-type Prim Merge Spec Inputs Relation Lattice NP Arity Ty :-
  params-binders NP Arity tt [] (ps\ t\ sigma I Rel Lat\ I = app [Inputs | ps],
    Rel = app [Relation | ps], Lat = app [Lattice | ps],
    t = {{ (forall (r : positive) (vs : list positive),
              @lat_derived positive lp:Prim lp:Merge lp:Spec lp:I r vs -> lp:Rel r vs) /\
           (forall (f : positive) (ks : list positive) (w : positive),
              @lat_assigned positive lp:Prim lp:Merge lp:Spec lp:I f ks w -> lp:Lat f ks w) }})
    Ty.

% forall params idx, R params idx -> its meaning
pred lat-complete-type i:list table, i:term, i:term, i:term, i:term, i:rel, o:term.
lat-complete-type Ts Prim Merge Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp I M\ std.append ps xs Args,
      RApp = app [global (indt R) | Args], I = app [Inputs | ps],
      lat-meaning Prim Merge Spec I R Code xs M,
      c = prod `H` RApp (_\ M)) t) Ty.

% The meaning of a relation over values among the tables of a program: its lattice for a
% lattice relation, and its relation otherwise.
pred table-meaning i:term, i:term, i:inductive, i:list term, i:term, i:list term, o:term.
table-meaning _ Lattice R Ps Code Xs M :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W,
  std.append Ps [Code, Ks, W] Args, M = app [Lattice | Args].
table-meaning Relation _ _ Ps Code Xs M :- enc-list Xs Vs,
  std.append Ps [Code, Vs] Args, M = app [Relation | Args].

% forall params idx, the meaning of the tables holds of the indices -> R params idx
pred lat-back-type i:list table, i:term, i:term, i:rel, o:term.
lat-back-type Ts Relation Lattice (rel R NP _ _) T :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp Mean\ std.append ps xs Args,
      RApp = app [global (indt R) | Args],
      table-meaning Relation Lattice R ps Code xs Mean,
      c = prod `H` Mean (_\ RApp)) t) T.

% forall params idx, R params idx <-> its meaning
pred lat-spec-type i:list table, i:term, i:term, i:term, i:term, i:rel, o:term.
lat-spec-type Ts Prim Merge Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp I M\ std.append ps xs Args,
      RApp = app [global (indt R) | Args], I = app [Inputs | ps],
      lat-meaning Prim Merge Spec I R Code xs M,
      c = {{ lp:RApp <-> lp:M }}) t) Ty.

% The half of the lemma [closed] that gives the meaning of the tables for a relation over
% values.
pred closed-part i:inductive, i:term, i:term, i:list term, o:term.
closed-part R K Code Xs {{ proj2 lp:K lp:Code lp:Ks lp:W }} :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W.
closed-part _ K Code Xs {{ proj1 lp:K lp:Code lp:Vs }} :- enc-list Xs Vs.

% The equivalence of a relation over values with its meaning, from the two directions.
pred lat-spec-proof i:list table, i:rel, i:term, i:term, i:term, o:term.
lat-spec-proof Ts (rel R NP _ _) Complete Back Closed P :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity ff [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst ff [] (xs\ c\ sigma Args C1 B1 K1 Sel\ std.append ps xs Args,
      C1 = app [Complete | Args], B1 = app [Back | Args], K1 = app [Closed | ps],
      closed-part R K1 Code xs Sel,
      c = {{ conj lp:C1 (fun h => lp:B1 (lp:Sel h)) }}) t) P.

% Define the glue of a relation over values: its meaning from the relation, the relation from
% the meaning of the tables, and their equivalence.
pred define-lat-spec i:list table, i:term, i:term, i:term, i:term, i:term, i:term, i:term,
  i:rel.
define-lat-spec Ts Prim Merge Spec Inputs Relation Lattice Closed (rel R NP Eq Ss) :-
  RName = {coq.gref->id (indt R)},
  if (lattice-of R _ _) (Suffix = "_assigned", BackTac = "egglog_lat_back")
     (Suffix = "_derived", BackTac = "egglog_back_lat"),
  lat-complete-type Ts Prim Merge Spec Inputs (rel R NP Eq Ss) CTy,
  prove-or "egglog_complete" CTy CP
    {calc ("Egglog: the tactic egglog_complete failed on " ^ RName ^ ". The command reads" ^
      " the relations in the order that it names them, so name each relation that a premise" ^
      " of " ^ RName ^ " reads before " ^ RName ^ ".")},
  coq.env.add-const {calc (RName ^ Suffix)} CP CTy @opaque! CC,
  coq.hints.add-resolve (const CC) "egglog_fire" 0 _,
  lat-back-type Ts Relation Lattice (rel R NP Eq Ss) BTy,
  prove BackTac BTy BP,
  coq.env.add-const {calc (RName ^ "_back")} BP BTy @opaque! BC,
  lat-spec-proof Ts (rel R NP Eq Ss) (global (const CC)) (global (const BC)) Closed SP,
  lat-spec-type Ts Prim Merge Spec Inputs (rel R NP Eq Ss) STy,
  std.assert-ok! (coq.elaborate-skeleton SP STy SP1) "Egglog: the glue lemma failed",
  coq.env.add-const {calc (RName ^ "_spec")} SP1 STy @opaque! _.

% Define the glue of a program with lattice tables: the fire lemmas, the closure of each lattice
% relation that a clause reads under its merge, the lemma [closed], and the glue of each
% relation over values.
pred define-lat-glue i:list table, i:list rel, i:list rel, i:list term, i:term, i:term, i:term,
  i:term.
define-lat-glue Ts Rels Lattices ClauseList Spec Inputs Relation Lattice :-
  fixed-prim Prim, Merge = {{ prim_merge lp:Prim }},
  std.filter Rels (r\ r = rel _ _ ff _) ValueRels,
  std.forall ValueRels (define-lat-fires Ts Rels ClauseList Prim Merge Spec Inputs),
  std.filter Lattices (read-lattice Ts ClauseList) Read,
  std.forall Read define-merges,
  Rels = [rel R1 NP _ _ | _], coq.env.indt R1 _ _ _ Arity1 _ _,
  lat-closed-type Prim Merge Spec Inputs Relation Lattice NP Arity1 ClosedTy,
  prove "egglog_lat_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  std.forall ValueRels
    (define-lat-spec Ts Prim Merge Spec Inputs Relation Lattice (global (const ClosedC))).

% -------------------------------------------------------------------------------------------
% The command

main [str "Primitives", str Name | Fs] :- !,
  std.map Fs (a\ g\ sigma N\ a = str N, coq.locate N g) GRs,
  coq.env.begin-module Name none,
  define-prims GRs 1 Codes Calls,
  (pi p vs\ prim-body Calls p vs (B p vs)),
  PrimT = fun `p` {{ positive }} (p\ fun `vs` {{ list positive }} (vs\ B p vs)),
  std.assert-ok! (coq.elaborate-skeleton PrimT PTy PrimE) "Egglog: an ill-typed primitive set",
  coq.env.add-const "prim" PrimE PTy @transparent! PrimC,
  coq.env.end-module _,
  std.forall Codes (c\ sigma GR Code\ c = pr GR Code,
    coq.elpi.accumulate library "egglog.prims"
      (clause _ _ (prim-code GR Code (global (const PrimC))))).
main [str Name, str "from" | Rest] :- !,
  split-with Rest RelNames Opt Merges,
  if (Opt = some Set)
     (coq.locate {calc (Set ^ ".prim")} PrimGR,
      (fixed-prim (global PrimGR) => derive-program Name RelNames Merges))
     (derive-program Name RelNames Merges).
main [str "Value", str Ty, str Mod] :- !, register-value Ty Mod.
main _ :- coq.error "Usage: Egglog <name> from <relation> .. <relation> [with <primitives>"
  "[merge <relation> <function>] ..], or Egglog Primitives <name> <function> .. <function>.".

% Register a value type with its encoder module: a later program encodes the values of the type.
pred register-value i:string, i:string.
register-value Ty Mod :-
  coq.locate Ty TyGR, T = global TyGR,
  if (value-type T) (coq.error "Egglog:" Ty "is already a value type") true,
  coq.locate {calc (Mod ^ ".encode")} EncGR, Enc = global EncGR,
  coq.locate {calc (Mod ^ ".decode")} DecGR, Dec = global DecGR,
  coq.locate {calc (Mod ^ ".decode_encode")} LemGR, Lem = global LemGR,
  std.assert-ok! (coq.typecheck Enc {{ lp:T -> positive }})
    "Egglog: the encoder is not a function from the type to positive",
  std.assert-ok! (coq.typecheck Dec {{ positive -> option lp:T }})
    "Egglog: the decoder is not a function from positive to the type",
  std.assert-ok! (coq.typecheck Lem {{ forall x : lp:T, lp:Dec (lp:Enc x) = Some x }})
    "Egglog: decode_encode does not say that decoding undoes encoding",
  std.assert-ok! (coq.elaborate-skeleton {{ @encode_inj_of lp:T lp:Enc lp:Dec lp:Lem }} InjTy InjE)
    "Egglog: the injectivity lemma is ill-typed",
  coq.env.add-const {calc (Mod ^ "_encode_inj")} InjE InjTy @opaque! InjC,
  coq.hints.add-resolve (const InjC) "egglog_inj" 0 _,
  coq.hints.add-resolve LemGR "egglog_decode" 0 _,
  coq.elpi.accumulate library "egglog.values" (clause _ _ (value-enc T Enc Dec)).

% The relations, the primitive set after 'with', and the declarations of lattice tables after it.
pred split-with i:list argument, o:list argument, o:option string,
  o:list (pair string string).
split-with [] [] none [].
split-with [str "with", str Set | Ms] [] (some Set) Merges :- !, merge-decls Ms Merges.
split-with [str "merge" | _] _ _ _ :- !,
  coq.error "Egglog: the merge of a lattice table is a primitive, so a lattice table needs a"
    "primitive set. Write 'with <primitives> merge <relation> <function>'.".
split-with [A | As] [A | Bs] O Ms :- split-with As Bs O Ms.

% Each relation is declared a lattice table at most once.
pred distinct-lattices i:list latdecl.
distinct-lattices [].
distinct-lattices [latdecl I _ _ | Rest] :-
  if (std.exists Rest (d\ d = latdecl I _ _))
     (coq.error "Egglog: the lattice table" {coq.gref->id (indt I)} "is declared twice.") true,
  distinct-lattices Rest.

pred derive-program i:string, i:list argument, i:list (pair string string).
derive-program Name RelNames Merges :-
  std.map RelNames (a\ i\ sigma N\ a = str N, coq.locate N (indt i)) Is,
  std.map Merges (lattice-decl Is) Decls,
  distinct-lattices Decls,
  with-lattices Decls (derive-relations Name Is).

% Derive the program of the relations, with the lattice tables in scope.
pred derive-relations i:string, i:list inductive.
derive-relations Name Is :-
  std.map Is rel-info Rels,
  if (std.exists Rels (r\ r = rel _ _ tt _), lattice-of _ _ _)
     (coq.error "Egglog: a program with lattice tables reads no equation.") true,
  std.filter Rels (r\ r = rel _ _ ff _) ValueRels,
  std.filter ValueRels (r\ sigma I\ r = rel I _ _ _, not (lattice-of I _ _)) Relational,
  std.filter ValueRels (r\ sigma I\ r = rel I _ _ _, lattice-of I _ _) Lattices,
  std.map ValueRels (r\ e\ sigma I Ss\ r = rel I _ _ Ss, e = pr (tk-rel I) Ss) RelKeys,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _,
    coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (input-keys Rels r) b) InputKeys,
  std.map Rels (r\ ds\ sigma I NP Ar Tys\ r = rel I NP _ _, coq.env.indt I _ _ _ Ar _ _,
    index-types NP Ar Tys, std.flatten {std.map Tys datatypes-of-type} ds) DtLists,
  std.flatten DtLists Dts0, undup Dts0 [] Dts,
  datatype-tables Dts [] DtKeys,
  std.flatten [RelKeys, InputKeys, DtKeys] Keys,
  number Keys 1 Dts Tables,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _, coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (sources-of r) b) Sources,
  std.forall Sources time-source,
  Rels = [rel R1 NP1 _ _ | _], coq.env.indt R1 _ _ _ Arity1 _ _,
  param-names NP1 Arity1 PNames,
  coq.env.begin-module Name none,
  std.map Tables (define-code PNames) Consts,
  with-codes Consts
    (derive-module Name Rels Relational Lattices InputKeys Dts Tables Sources NP1 Arity1).

% Derive the time function of a generated constant beside it, with Argent.
pred time-function i:string.
time-function S :- new_safe M, (verify-memo M => timefun S _).

% Derive the time function of a projection that an input table reads, unless it has one. It
% runs before the module of the program opens, beside the projection.
pred time-source i:source.
time-source (source (tk-src (global GR)) _) :- not (timed GR _), !,
  coq.gref->path GR Path, std.string.concat "." {std.append Path [{coq.gref->id GR}]} S,
  time-function S.
time-source _.

% Run a goal with the code constants of the tables.
pred with-codes i:list (pair tkey term), i:prop.
with-codes [] G :- G.
with-codes [pr K C | Rest] G :- code-const K C => with-codes Rest G.

% The constants of the module of a program, after its code constants.
pred derive-module i:string, i:list rel, i:list rel, i:list rel,
  i:list (pair tkey (list term)), i:list inductive, i:list table, i:list source, i:int, i:term.
derive-module Name Rels Relational Lattices InputKeys Dts Tables Sources NP1 Arity1 :-
  std.map Tables (decl-of Tables) Decls, list->term {{ decl }} Decls DeclT,
  std.map-filter Tables (t\ c\ sigma K\ t = table K _ _ _,
    std.exists InputKeys (p\ sigma S\ p = pr K S), code-of Tables K c) InputCodes,
  list->term {{ positive }} InputCodes InputT,
  std.fold Rels [] (r\ a\ b\ sigma I KTys Cs\ r = rel I _ _ _,
    coq.env.indt I _ _ _ _ _ KTys,
    std.map KTys (clause-of Tables Rels r) Cs, std.flatten [a | Cs] b) ClauseList,
  list->term {{ clause positive }} ClauseList ClausesT,
  Spec = {{ @Spec positive lp:DeclT lp:InputT lp:ClausesT }},
  std.assert-ok! (coq.typecheck Spec {{ spec positive }}) "Egglog: ill-typed specification",
  check-sorts Name Spec,
  coq.env.add-const "spec" Spec {{ spec positive }} @transparent! SpecC,
  SpecT = global (const SpecC),
  coq.env.add-const "program" {{ @spec_program positive lp:SpecT }}
    {{ program positive }} @transparent! _,
  abs-params NP1 Arity1 [] (ps\ fb\ facts-body Tables Sources ps fb) FactsT,
  std.assert-ok! (coq.elaborate-skeleton FactsT FactsTy FactsE) "Egglog: ill-typed facts",
  coq.env.add-const "facts" FactsE FactsTy @transparent! _,
  time-function "facts",
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    mk-inputs-fun FB f) InputsT,
  std.assert-ok! (coq.elaborate-skeleton InputsT InputsTy InputsE) "Egglog: ill-typed inputs",
  coq.env.add-const "inputs" InputsE InputsTy @transparent! InputsC,
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    if (Lattices = []) (mk-rel-fun Tables ps Relational FB f)
       (mk-lat-rel-fun Tables ps Relational FB f)) RelationT,
  std.assert-ok! (coq.elaborate-skeleton RelationT RelTy RelationE)
    "Egglog: ill-typed relation",
  coq.env.add-const "relation" RelationE RelTy @transparent! RelationC,
  if (Lattices = [])
     (define-glue Tables Rels ClauseList SpecT (global (const InputsC))
        (global (const RelationC)))
     (abs-params NP1 Arity1 [] (ps\ f\ mk-lat-fun Tables ps Lattices f) LatticeT,
      std.assert-ok! (coq.elaborate-skeleton LatticeT LatticeTy LatticeE)
        "Egglog: ill-typed lattice",
      coq.env.add-const "lattice" LatticeE LatticeTy @transparent! LatticeC,
      define-lat-glue Tables Rels Lattices ClauseList SpecT (global (const InputsC))
        (global (const RelationC)) (global (const LatticeC))),
  std.map Dts (define-encoder Tables) Encs,
  std.forall Dts (d\ time-function {calc ("encode_" ^ {coq.gref->id (indt d)})}),
  std.forall Rels (define-eq-glue Tables Rels ClauseList Encs SpecT (global (const InputsC))),
  coq.env.end-module _.

}}.
#[synterp] Elpi Accumulate lp:{{
main [str "Primitives", str Name | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main [str Name, str "from" | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main [str "Value", _, _] :- !.
main _.
}}.
Elpi Export Egglog.
