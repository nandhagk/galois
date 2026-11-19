(** * Tactics of the glue of relations

    The command [Egglog] of [Derive.v] proves the lemmas that relate a relation over values to
    the rows of its program with these tactics, which it calls by name. They move between input
    elements and rows, show that each constructor derives its row, and show that every derived
    row is in the relation of the program.

    For example, [egglog_member] shows that the row [(Copy_code, [x; y])] is in the input rows
    of a list that holds [Copy x y].

    Builds on: the derived rows of specifications and the tactics on values and primitives. *)

From Stdlib Require Import List PArith.
From Galois.Front Require Import Spec SpecFacts DerivePrimitives.

Import List.ListNotations.

(** * Glue tactics

    The command proves, for each relation [R] over values, that [R] holds exactly when its row
    is derived. These tactics prove the generated lemmas. [egglog_member] and
    [egglog_unmember] move between an input element and its row. [egglog_clause] shows that
    one clause, applied to rows of the relation, gives a row of the relation. *)

Create HintDb egglog_fire discriminated.

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

(** Try the disjuncts of the relation of a program in order, and prove the first whose code is
    the code of the row with [egglog_conclude]. *)
Ltac egglog_pick :=
  first
    [ split; [reflexivity | egglog_conclude]
    | left; split; [reflexivity | egglog_conclude]
    | right; egglog_pick ].

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
