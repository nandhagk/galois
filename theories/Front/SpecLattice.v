(** * Specifications that read lattice tables

    A clause may read the value that a lattice table stores at a key, with a premise
    [Equals f args v]. The engine stores at each key the merge of the values that the clauses
    assign there, so a read sees such a merge, and the clause derives a row or assigns a value
    from it. This file gives these specifications their meaning, as four relations defined
    together. [lat_derived] holds of the derived rows, [lat_assigned] of the values that a clause
    assigns at a key, [lat_merged] of the merges of assigned values that a read sees, and
    [lat_body] of the bodies that hold. A read sees a merge of assigned values, because the
    engine reads the stored merge. A merge that picks one of its arguments, such as [Pos.min],
    gives an assigned value again. The union of two sets of definitions need not be assigned
    itself. On a specification without reads, [lat_derived] and [lat_assigned] agree with
    [derived] and [assigned] of [Spec.v].

    For example, with [Pos.min] as the merge of the table [dist], the clause
    [Equals dist [a; b] d; Holds edge [b; c; w] => Assign dist [a; c] (d + w)] assigns at the key
    [[a; c]] the length of every path from [a] to [c] that ends with an edge, and a read of
    [dist] at [[a; b]] sees the length of a shortest path among those that it merges.

    Main results
    - [lat_least] The meaning is contained in every relation of rows that contains the inputs
      and every relation of values that the clauses close, when reads see a relation that
      contains the values and is closed under the merges.
    - [lat_least_closure] The same, when reads see the merges of the values.
    - [lat_mono] The meaning grows with the input rows.
    - [derived_lat], [assigned_lat] Derived rows and assigned values keep their meaning.
    - [lat_derived_agrees], [lat_assigned_agrees] Without reads, the meaning is that of
      [derived] and [assigned].
    - [fold_lat_merged], [lat_merged_fold] A merge that a read sees is a fold of the merge over
      assigned values.
    - [lat_merge_agrees] The meaning depends on the merge only at the codes of lattice tables.

    Builds on: the specifications and their facts, and the models of the engine. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec SpecFacts.

Import List.ListNotations.

Section Lattice.
Context {V : Type} (prim : positive -> list V -> option V) (merge : positive -> V -> V -> V).

(** * Meaning *)

(** The rows derived from the input rows [I], the values that the clauses assign at a key, the
    merges of those values that a read sees, and the bodies that hold under an environment. A
    merge combines two values at one key of a lattice table with the merge of its declaration. *)
Inductive lat_derived (s : spec V) (I : positive -> list V -> Prop) :
    positive -> list V -> Prop :=
  | lat_derived_input r vs : In r (inputs s) -> I r vs -> lat_derived s I r vs
  | lat_derived_clause c e r args vs : In c (clauses s) -> head c = Derive r args ->
      lat_body s I e (body c) -> pat_values prim e args = Some vs -> lat_derived s I r vs
with lat_assigned (s : spec V) (I : positive -> list V -> Prop) :
    positive -> list V -> V -> Prop :=
  | lat_assigned_clause c e f args v ks w : In c (clauses s) -> head c = Assign f args v ->
      lat_body s I e (body c) -> pat_values prim e args = Some ks ->
      pat_value prim e v = Some w -> lat_assigned s I f ks w
with lat_merged (s : spec V) (I : positive -> list V -> Prop) :
    positive -> list V -> V -> Prop :=
  | lat_merged_one f ks w : lat_assigned s I f ks w -> lat_merged s I f ks w
  | lat_merged_merge f m ks a b : lookup_kind (tables s) f = Some (OLat m) ->
      lat_merged s I f ks a -> lat_merged s I f ks b -> lat_merged s I f ks (merge m a b)
with lat_body (s : spec V) (I : positive -> list V -> Prop) :
    (positive -> option V) -> list (premise V) -> Prop :=
  | lat_body_nil e : lat_body s I e []
  | lat_body_row e r args vs rest : pat_values prim e args = Some vs -> lat_derived s I r vs ->
      lat_body s I e rest -> lat_body s I e (Holds r args :: rest)
  | lat_body_read e f args v ks w rest : pat_values prim e args = Some ks ->
      pat_value prim e v = Some w -> lat_merged s I f ks w -> lat_body s I e rest ->
      lat_body s I e (Equals f args v :: rest)
  | lat_body_computes e q args v vs w rest : pat_values prim e args = Some vs ->
      prim q vs = Some w -> pat_value prim e v = Some w -> lat_body s I e rest ->
      lat_body s I e (Computes q args v :: rest).

Scheme lat_derived_min := Minimality for lat_derived Sort Prop
  with lat_assigned_min := Minimality for lat_assigned Sort Prop
  with lat_merged_min := Minimality for lat_merged Sort Prop
  with lat_body_min := Minimality for lat_body Sort Prop.

Combined Scheme lat_mut_ind from lat_derived_min, lat_assigned_min, lat_merged_min,
  lat_body_min.

(** A premise holds under an environment, when its row is in [P], its read value is in [Q] or
    its primitive gives its value. *)
Definition premise_lat_in (P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) (e : positive -> option V) (p : premise V) : Prop :=
  match p with
  | Holds r args => exists vs, pat_values prim e args = Some vs /\ P r vs
  | Equals f args v => exists ks w, pat_values prim e args = Some ks /\
      pat_value prim e v = Some w /\ Q f ks w
  | Computes q args v => exists vs w, pat_values prim e args = Some vs /\ prim q vs = Some w /\
      pat_value prim e v = Some w
  end.

(** No clause reads a lattice table. *)
Definition no_reads (s : spec V) : bool :=
  forallb (fun c =>
    forallb (fun p => match p with Equals _ _ _ => false | _ => true end) (body c))
    (clauses s).

(** * Least relations *)

(** The meaning is contained in every relation [P] of rows that contains the input rows and
    every relation [A] of values that the clauses close, when the reads see a relation [Q] that
    contains [A] and is closed under the merges. *)
Lemma lat_least (s : spec V) (I P : positive -> list V -> Prop)
    (A Q : positive -> list V -> V -> Prop) :
  (forall r vs, In r (inputs s) -> I r vs -> P r vs) ->
  (forall f ks w, A f ks w -> Q f ks w) ->
  (forall f m ks a b, lookup_kind (tables s) f = Some (OLat m) -> Q f ks a -> Q f ks b ->
    Q f ks (merge m a b)) ->
  (forall c e r args vs, In c (clauses s) -> head c = Derive r args ->
    Forall (premise_lat_in P Q e) (body c) -> pat_values prim e args = Some vs -> P r vs) ->
  (forall c e f args v ks w, In c (clauses s) -> head c = Assign f args v ->
    Forall (premise_lat_in P Q e) (body c) -> pat_values prim e args = Some ks ->
    pat_value prim e v = Some w -> A f ks w) ->
  (forall r vs, lat_derived s I r vs -> P r vs) /\
  (forall f ks w, lat_assigned s I f ks w -> A f ks w) /\
  (forall f ks w, lat_merged s I f ks w -> Q f ks w).
Proof.
  intros Hinputs Hreads Hmerge Hderive Hassign.
  enough (Hall : (forall r vs, lat_derived s I r vs -> P r vs) /\
      (forall f ks w, lat_assigned s I f ks w -> A f ks w) /\
      (forall f ks w, lat_merged s I f ks w -> Q f ks w) /\
      (forall e ps, lat_body s I e ps -> Forall (premise_lat_in P Q e) ps)).
  { destruct Hall as [Hrows [Hvalues [Hmerged _]]].
    split; [exact Hrows |]. split; [exact Hvalues | exact Hmerged]. }
  apply (lat_mut_ind s I P A Q (fun e ps => Forall (premise_lat_in P Q e) ps)).
  - exact Hinputs.
  - intros c e r args vs Hin Hhead _ Hbody Hvalues.
    exact (Hderive c e r args vs Hin Hhead Hbody Hvalues).
  - intros c e f args v ks w Hin Hhead _ Hbody Hkeys Hvalue.
    exact (Hassign c e f args v ks w Hin Hhead Hbody Hkeys Hvalue).
  - intros f ks w _ Hw.
    exact (Hreads f ks w Hw).
  - intros f m ks a b Hkind _ Ha _ Hb.
    exact (Hmerge f m ks a b Hkind Ha Hb).
  - intros e.
    constructor.
  - intros e r args vs rest Hvalues _ Hrow _ Hrest.
    constructor; [exists vs; split; assumption | exact Hrest].
  - intros e f args v ks w rest Hkeys Hvalue _ Hread _ Hrest.
    constructor; [exists ks, w; repeat split; assumption | exact Hrest].
  - intros e q args v vs w rest Hvalues Hprim Hvalue _ Hrest.
    constructor; [exists vs, w; repeat split; assumption | exact Hrest].
Qed.

(** The merges of values of a relation [A] at one key of a lattice table. *)
Inductive lat_closure (s : spec V) (A : positive -> list V -> V -> Prop) (f : positive)
    (ks : list V) : V -> Prop :=
  | lat_closure_one w : A f ks w -> lat_closure s A f ks w
  | lat_closure_merge m a b : lookup_kind (tables s) f = Some (OLat m) ->
      lat_closure s A f ks a -> lat_closure s A f ks b -> lat_closure s A f ks (merge m a b).

(** A relation that is closed under the merge of a table at a key holds of the merges of its
    values there. *)
Lemma lat_closure_elim (s : spec V) (A : positive -> list V -> V -> Prop) f ks w :
  (forall m a b, lookup_kind (tables s) f = Some (OLat m) -> A f ks a -> A f ks b ->
    A f ks (merge m a b)) ->
  lat_closure s A f ks w -> A f ks w.
Proof.
  intros Hclosed Hw.
  induction Hw as [w Hw | m a b Hkind _ IHa _ IHb].
  - exact Hw.
  - exact (Hclosed m a b Hkind IHa IHb).
Qed.

(** The meaning is contained in every relation [P] of rows that contains the input rows and
    every relation [A] of values that the clauses close, when the reads see the merges of the
    values of [A]. *)
Lemma lat_least_closure (s : spec V) (I P : positive -> list V -> Prop)
    (A : positive -> list V -> V -> Prop) :
  (forall r vs, In r (inputs s) -> I r vs -> P r vs) ->
  (forall c e r args vs, In c (clauses s) -> head c = Derive r args ->
    Forall (premise_lat_in P (lat_closure s A) e) (body c) ->
    pat_values prim e args = Some vs -> P r vs) ->
  (forall c e f args v ks w, In c (clauses s) -> head c = Assign f args v ->
    Forall (premise_lat_in P (lat_closure s A) e) (body c) ->
    pat_values prim e args = Some ks -> pat_value prim e v = Some w -> A f ks w) ->
  (forall r vs, lat_derived s I r vs -> P r vs) /\
  (forall f ks w, lat_assigned s I f ks w -> A f ks w).
Proof.
  intros Hinputs Hderive Hassign.
  destruct (lat_least s I P A (lat_closure s A) Hinputs (lat_closure_one s A)
    (fun f m ks a b Hkind Ha Hb => lat_closure_merge s A f ks m a b Hkind Ha Hb)
    Hderive Hassign) as [Hrows [Hvalues _]].
  split; [exact Hrows | exact Hvalues].
Qed.

(** A body whose premises hold in the meaning holds. *)
Lemma lat_body_intro (s : spec V) (I : positive -> list V -> Prop) e ps :
  Forall (premise_lat_in (lat_derived s I) (lat_merged s I) e) ps -> lat_body s I e ps.
Proof.
  intros Hps.
  induction Hps as [| p ps Hp _ IHps].
  - apply lat_body_nil.
  - destruct p as [r args | f args v | q args v]; cbn in Hp.
    + destruct Hp as [vs [Hvalues Hrow]].
      exact (lat_body_row s I e r args vs ps Hvalues Hrow IHps).
    + destruct Hp as [ks [w [Hkeys [Hvalue Hmerged]]]].
      exact (lat_body_read s I e f args v ks w ps Hkeys Hvalue Hmerged IHps).
    + destruct Hp as [vs [w [Hvalues [Hprim Hvalue]]]].
      exact (lat_body_computes s I e q args v vs w ps Hvalues Hprim Hvalue IHps).
Qed.

(** The meaning grows with the input rows. *)
Lemma lat_mono (s : spec V) (I1 I2 : positive -> list V -> Prop) :
  (forall r vs, I1 r vs -> I2 r vs) ->
  (forall r vs, lat_derived s I1 r vs -> lat_derived s I2 r vs) /\
  (forall f ks w, lat_assigned s I1 f ks w -> lat_assigned s I2 f ks w) /\
  (forall f ks w, lat_merged s I1 f ks w -> lat_merged s I2 f ks w).
Proof.
  intros Hsub.
  apply lat_least.
  - intros r vs Hin HI.
    exact (lat_derived_input s I2 r vs Hin (Hsub r vs HI)).
  - exact (lat_merged_one s I2).
  - exact (lat_merged_merge s I2).
  - intros c e r args vs Hin Hhead Hbody Hvalues.
    exact (lat_derived_clause s I2 c e r args vs Hin Hhead (lat_body_intro s I2 e _ Hbody)
      Hvalues).
  - intros c e f args v ks w Hin Hhead Hbody Hkeys Hvalue.
    exact (lat_assigned_clause s I2 c e f args v ks w Hin Hhead (lat_body_intro s I2 e _ Hbody)
      Hkeys Hvalue).
Qed.

(** * Specifications without reads *)

(** A premise that holds in a relation of rows holds with any relation of read values. *)
Lemma premise_in_lat (P : positive -> list V -> Prop) (Q : positive -> list V -> V -> Prop) e p :
  premise_in prim P e p -> premise_lat_in P Q e p.
Proof.
  destruct p as [r args | f args v | q args v]; cbn; intros Hp; [exact Hp | contradiction |
    exact Hp].
Qed.

(** A premise that holds with some relation of read values, and reads no lattice table, holds
    in its relation of rows. *)
Lemma premise_lat_in_no_read (P : positive -> list V -> Prop)
    (Q : positive -> list V -> V -> Prop) e p :
  match p with Equals _ _ _ => false | _ => true end = true ->
  premise_lat_in P Q e p -> premise_in prim P e p.
Proof.
  destruct p as [r args | f args v | q args v]; cbn; intros Hok Hp;
    [exact Hp | discriminate Hok | exact Hp].
Qed.

(** A body whose premises hold in the derived rows holds. *)
Lemma derived_body_intro (s : spec V) (I : positive -> list V -> Prop) e ps :
  Forall (premise_in prim (derived prim s I) e) ps -> derived_body prim s I e ps.
Proof.
  intros Hps.
  induction Hps as [| p ps Hp _ IHps].
  - apply derived_nil.
  - destruct p as [r args | f args v | q args v]; cbn in Hp.
    + destruct Hp as [vs [Hvalues Hrow]].
      exact (derived_row prim s I e r args vs ps Hvalues Hrow IHps).
    + contradiction.
    + destruct Hp as [vs [w [Hvalues [Hprim Hvalue]]]].
      exact (derived_computes prim s I e q args v vs w ps Hvalues Hprim Hvalue IHps).
Qed.

(** A derived row is a row of the meaning. *)
Lemma derived_lat (s : spec V) (I : positive -> list V -> Prop) r vs :
  derived prim s I r vs -> lat_derived s I r vs.
Proof.
  revert r vs.
  apply derived_least.
  - intros r vs Hin HI.
    exact (lat_derived_input s I r vs Hin HI).
  - intros c e r args vs Hin Hhead Hbody Hvalues.
    apply (lat_derived_clause s I c e r args vs Hin Hhead); [| exact Hvalues].
    apply lat_body_intro.
    exact (Forall_impl _ (premise_in_lat (lat_derived s I) (lat_merged s I) e) Hbody).
Qed.

(** A body that holds without reads holds in the meaning. *)
Lemma derived_body_lat (s : spec V) (I : positive -> list V -> Prop) e ps :
  derived_body prim s I e ps -> lat_body s I e ps.
Proof.
  intros Hbody.
  induction Hbody as [e | e r args vs rest Hvalues Hrow _ IHrest
    | e q args v vs w rest Hvalues Hprim Hvalue _ IHrest].
  - apply lat_body_nil.
  - exact (lat_body_row s I e r args vs rest Hvalues (derived_lat s I r vs Hrow) IHrest).
  - exact (lat_body_computes s I e q args v vs w rest Hvalues Hprim Hvalue IHrest).
Qed.

(** An assigned value is a value of the meaning. *)
Lemma assigned_lat (s : spec V) (I : positive -> list V -> Prop) f ks w :
  assigned prim s I f ks w -> lat_assigned s I f ks w.
Proof.
  intros [c e f' args v ks' w' Hin Hhead Hbody Hkeys Hvalue].
  exact (lat_assigned_clause s I c e f' args v ks' w' Hin Hhead (derived_body_lat s I e _ Hbody)
    Hkeys Hvalue).
Qed.

(** Without reads, the rows and the values of the meaning are derived rows and assigned
    values. *)
Lemma lat_no_reads (s : spec V) (I : positive -> list V -> Prop) :
  no_reads s = true ->
  (forall r vs, lat_derived s I r vs -> derived prim s I r vs) /\
  (forall f ks w, lat_assigned s I f ks w -> assigned prim s I f ks w).
Proof.
  intros Hnone.
  unfold no_reads in Hnone. rewrite forallb_forall in Hnone.
  assert (Hbody : forall c e, In c (clauses s) ->
      Forall (premise_lat_in (derived prim s I) (fun _ _ _ => True) e) (body c) ->
      derived_body prim s I e (body c)).
  { intros c e Hin Hps.
    apply derived_body_intro.
    pose proof (Hnone c Hin) as Hnot. rewrite forallb_forall in Hnot.
    rewrite Forall_forall in Hps |- *.
    intros p Hp.
    exact (premise_lat_in_no_read _ _ e p (Hnot p Hp) (Hps p Hp)). }
  enough (Hall : (forall r vs, lat_derived s I r vs -> derived prim s I r vs) /\
      (forall f ks w, lat_assigned s I f ks w -> assigned prim s I f ks w) /\
      (forall f ks w, lat_merged s I f ks w -> True)).
  { destruct Hall as [Hrows [Hvalues _]]. split; [exact Hrows | exact Hvalues]. }
  apply lat_least.
  - intros r vs Hin HI.
    exact (derived_input prim s I r vs Hin HI).
  - intros; trivial.
  - intros; trivial.
  - intros c e r args vs Hin Hhead Hps Hvalues.
    exact (derived_clause prim s I c e r args vs Hin Hhead (Hbody c e Hin Hps) Hvalues).
  - intros c e f args v ks w Hin Hhead Hps Hkeys Hvalue.
    exact (assigned_clause prim s I c e f args v ks w Hin Hhead (Hbody c e Hin Hps) Hkeys
      Hvalue).
Qed.

(** Without reads, the rows of the meaning are the derived rows. *)
Lemma lat_derived_agrees (s : spec V) (I : positive -> list V -> Prop) r vs :
  no_reads s = true -> lat_derived s I r vs <-> derived prim s I r vs.
Proof.
  intros Hnone.
  split.
  - exact (proj1 (lat_no_reads s I Hnone) r vs).
  - exact (derived_lat s I r vs).
Qed.

(** Without reads, the values of the meaning are the assigned values. *)
Lemma lat_assigned_agrees (s : spec V) (I : positive -> list V -> Prop) f ks w :
  no_reads s = true -> lat_assigned s I f ks w <-> assigned prim s I f ks w.
Proof.
  intros Hnone.
  split.
  - exact (proj2 (lat_no_reads s I Hnone) f ks w).
  - exact (assigned_lat s I f ks w).
Qed.

(** * Merges as folds *)

(** A fold of the merge of a lattice table over assigned values is a merge that a read sees. *)
Lemma fold_lat_merged (s : spec V) (I : positive -> list V -> Prop) f m ks w ws :
  lookup_kind (tables s) f = Some (OLat m) ->
  lat_assigned s I f ks w -> Forall (lat_assigned s I f ks) ws ->
  lat_merged s I f ks (fold_left (merge m) ws w).
Proof.
  intros Hkind Hw Hws.
  assert (Hacc : forall a, lat_merged s I f ks a ->
      lat_merged s I f ks (fold_left (merge m) ws a)).
  { induction Hws as [| w' ws' Hw' _ IHws]; intros a Ha; cbn [fold_left].
    - exact Ha.
    - apply IHws.
      exact (lat_merged_merge s I f m ks a w' Hkind Ha (lat_merged_one s I f ks w' Hw')). }
  exact (Hacc w (lat_merged_one s I f ks w Hw)).
Qed.

Section Folds.
Variable (m : positive).
Hypothesis merge_comm : forall a b, merge m a b = merge m b a.
Hypothesis merge_assoc : forall a b c, merge m a (merge m b c) = merge m (merge m a b) c.

(** Merging a value into a fold merges it into the start of the fold. *)
Lemma merge_fold_right ws x y :
  merge m (fold_left (merge m) ws x) y = fold_left (merge m) ws (merge m x y).
Proof.
  revert x.
  induction ws as [| w ws IHws]; intros x; cbn [fold_left].
  - reflexivity.
  - rewrite IHws.
    f_equal.
    rewrite <- !merge_assoc, (merge_comm w y).
    reflexivity.
Qed.

(** The merge of two folds is one fold over both lists. *)
Lemma merge_folds ws ws' x y :
  merge m (fold_left (merge m) ws x) (fold_left (merge m) ws' y) =
    fold_left (merge m) (ws ++ y :: ws') x.
Proof.
  rewrite fold_left_app. cbn [fold_left].
  rewrite (merge_comm (fold_left (merge m) ws x) (fold_left (merge m) ws' y)).
  rewrite merge_fold_right.
  rewrite (merge_comm y (fold_left (merge m) ws x)).
  reflexivity.
Qed.

End Folds.

(** With a commutative and associative merge, a merge that a read sees is a fold of the merge
    over assigned values. *)
Lemma lat_merged_fold (s : spec V) (I : positive -> list V -> Prop) f m ks v :
  (forall a b, merge m a b = merge m b a) ->
  (forall a b c, merge m a (merge m b c) = merge m (merge m a b) c) ->
  lookup_kind (tables s) f = Some (OLat m) ->
  lat_merged s I f ks v ->
  exists w ws, lat_assigned s I f ks w /\ Forall (lat_assigned s I f ks) ws /\
    v = fold_left (merge m) ws w.
Proof.
  intros Hcomm Hassoc Hkind Hv.
  revert Hkind.
  induction Hv as [f ks w Hw | f m' ks a b Hkind' _ IHa _ IHb]; intros Hkind.
  - exists w, []. split; [exact Hw |]. split; [constructor | reflexivity].
  - rewrite Hkind in Hkind'. injection Hkind' as Hm. subst m'.
    destruct (IHa Hkind) as [wa [wsa [Hwa [Hwsa Ha]]]].
    destruct (IHb Hkind) as [wb [wsb [Hwb [Hwsb Hb]]]].
    subst a b.
    exists wa, (wsa ++ wb :: wsb).
    split; [exact Hwa |]. split.
    + apply Forall_app. split; [exact Hwsa | constructor; assumption].
    + exact (merge_folds m Hcomm Hassoc wsa wsb wa wb).
Qed.

End Lattice.

(** * Merges *)

(** The meaning with one merge is contained in the meaning with another merge that agrees with
    it at the codes of the lattice tables. *)
Lemma lat_merge_sub {V : Type} (prim : positive -> list V -> option V)
    (merge1 merge2 : positive -> V -> V -> V) (s : spec V) (I : positive -> list V -> Prop) :
  (forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> merge1 m a b = merge2 m a b) ->
  (forall r vs, lat_derived prim merge1 s I r vs -> lat_derived prim merge2 s I r vs) /\
  (forall f ks w, lat_assigned prim merge1 s I f ks w -> lat_assigned prim merge2 s I f ks w) /\
  (forall f ks w, lat_merged prim merge1 s I f ks w -> lat_merged prim merge2 s I f ks w).
Proof.
  intros Hagree.
  apply lat_least.
  - intros r vs Hin HI.
    exact (lat_derived_input prim merge2 s I r vs Hin HI).
  - exact (lat_merged_one prim merge2 s I).
  - intros f m ks a b Hkind Ha Hb.
    rewrite (Hagree f m a b Hkind).
    exact (lat_merged_merge prim merge2 s I f m ks a b Hkind Ha Hb).
  - intros c e r args vs Hin Hhead Hbody Hvalues.
    exact (lat_derived_clause prim merge2 s I c e r args vs Hin Hhead
      (lat_body_intro prim merge2 s I e _ Hbody) Hvalues).
  - intros c e f args v ks w Hin Hhead Hbody Hkeys Hvalue.
    exact (lat_assigned_clause prim merge2 s I c e f args v ks w Hin Hhead
      (lat_body_intro prim merge2 s I e _ Hbody) Hkeys Hvalue).
Qed.

(** The meaning depends on the merge only at the codes of the lattice tables. *)
Lemma lat_merge_agrees {V : Type} (prim : positive -> list V -> option V)
    (merge1 merge2 : positive -> V -> V -> V) (s : spec V) (I : positive -> list V -> Prop) :
  (forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> merge1 m a b = merge2 m a b) ->
  (forall r vs, lat_derived prim merge1 s I r vs <-> lat_derived prim merge2 s I r vs) /\
  (forall f ks w, lat_assigned prim merge1 s I f ks w <-> lat_assigned prim merge2 s I f ks w) /\
  (forall f ks w, lat_merged prim merge1 s I f ks w <-> lat_merged prim merge2 s I f ks w).
Proof.
  intros Hagree.
  assert (Hback : forall f m a b, lookup_kind (tables s) f = Some (OLat m) ->
      merge2 m a b = merge1 m a b).
  { intros f m a b Hkind. symmetry. exact (Hagree f m a b Hkind). }
  destruct (lat_merge_sub prim merge1 merge2 s I Hagree) as [Hrows [Hvalues Hmerged]].
  destruct (lat_merge_sub prim merge2 merge1 s I Hback) as [Hrows' [Hvalues' Hmerged']].
  split; [intros r vs; split; [apply Hrows | apply Hrows'] |].
  split; [intros f ks w; split; [apply Hvalues | apply Hvalues'] |].
  intros f ks w; split; [apply Hmerged | apply Hmerged'].
Qed.
