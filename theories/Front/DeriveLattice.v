(** * Merges and tactics of lattice tables

    A lattice table of a program that the command [Egglog] of [Derive.v] derives merges its
    values with a primitive of the primitive set of the program. [prim_merge] computes that
    merge from the primitive function of the set, and the glue lemmas of the program use it.
    The command proves these lemmas with the tactics of this file, which it calls by name. They
    read a premise over a lattice table as a merge of assigned values, and show that every row
    and every assigned value of the program is in the meaning of its tables.

    For example, for the primitive set [Ops] of [Egglog Primitives Ops Pos.add Pos.min Pos.max],
    [prim_merge Ops.prim Ops.min_code a b] is [Pos.min a b].

    Builds on: the meaning of lattice reads, the definitions that derived programs call and the
    glue tactics of relations. *)

From Stdlib Require Import List PArith.
From Galois.Front Require Import Spec SpecLattice DeriveHelpers DerivePrimitives DeriveTactics.

Import List.ListNotations.

(** * Lattice tables

    A relation whose last index is its value is a lattice table when the command declares it
    with [merge R g] after [with Ops]. Its constructors assign values, and a premise over it
    reads the stored value. The glue of such a program uses the relations of [SpecLattice.v],
    and for a lattice relation [R], [R ks v] holds exactly when [v] is a value that the clauses
    assign at [ks]. A read sees a merge of assigned values, so a relation that a clause reads
    must be closed under its merge. The command proves this closure as the lemma [<R>_merges]
    with [egglog_merges], or with a lemma [<R>_merges] that the client proves before the
    command, through [egglog_merges_by]. *)

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
    two arguments, which the cases of its unfolded definition show, a constructor of the
    relation merges two values, or a lemma of the hint database [egglog_merges] gives the
    closure. A client registers such a lemma before the command, and the command registers
    each lemma [<R>_merges] that it defines. *)
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
    | solve [econstructor; eassumption]
    | solve [eauto with egglog_merges] ].

(** A relation is closed under its merge by the lemma [lem], which the client proves before the
    command and names [<R>_merges]. *)
Ltac egglog_merges_by lem :=
  intros; solve [eapply lem; eassumption].

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

(** Try the disjuncts of the lattice of a program in order, and prove the first whose code is the
    code of the table with [egglog_lat_value tac]. *)
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
    relation turns into a value of the lattice. A clause of an equation derives no row and
    assigns no value, so its case closes by its head. *)
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
  | Hh : Unify _ _ = _ |- _ => discriminate Hh
  | Hh : Rewrites _ _ = _ |- _ => discriminate Hh
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
