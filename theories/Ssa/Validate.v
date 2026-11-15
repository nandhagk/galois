(** * Translation and SSA validation

    The translation checker follows each instruction and checks the supplied entry renamings.
    For example, it accepts a renamed return only when both returns read corresponding values.
    Builds on: ValidateSig. *)

From Stdlib Require Import List PArith NArith Bool Arith Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.

Module ValidateSig.
  TimeFun source_bodies.
  TimeFun target_bodies.
  TimeFun cert_envs.
  TimeFun cert_rows.
End ValidateSig.

(** An index preserves the first binding of every association-list key. *)
Fixpoint val_index {A} (rows : list (positive * A)) : ptrie A :=
  match rows with
  | [] => Empty
  | (x, value) :: rest => PTrieCode.set x value (val_index rest)
  end.
TimeFun val_index.

Fixpoint val_set (xs : list positive) : ptrie unit :=
  match xs with
  | [] => Empty
  | x :: rest => PTrieCode.set x tt (val_set rest)
  end.
TimeFun val_set.

Definition val_mem (xs : ptrie unit) (x : positive) : bool :=
  match trie_get x xs with Some _ => true | None => false end.
TimeFun val_mem.

Definition val_maps (rho : ptrie positive) (x y : positive) : bool :=
  match trie_get x rho with Some z => Pos.eqb y z | None => false end.
TimeFun val_maps.

Definition val_inverse (rho : renaming) : ptrie positive :=
  val_index (map (fun xy => (snd xy, fst xy)) rho).
TimeFun val_inverse.

Definition val_injective (rho : renaming) : bool :=
  let inverse := val_inverse rho in
  forallb (fun xy => val_maps inverse (snd xy) (fst xy)) rho.
TimeFun val_injective.

Fixpoint val_args (rho : ptrie positive) (known : ptrie unit)
    (xs ys : list positive) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr =>
    val_mem known x && val_maps rho x y && val_args rho known xr yr
  | _, _ => false
  end.
TimeFun val_args.

(** The last parameter binding wins, exactly as in the language interpreter. *)
Fixpoint val_bind_symbols (ps args : list positive) (m : ptrie positive)
    : option (ptrie positive) :=
  match ps, args with
  | [], [] => Some m
  | p :: pr, x :: xr => val_bind_symbols pr xr (PTrieCode.set p x m)
  | _, _ => None
  end.
TimeFun val_bind_symbols.

Definition val_symbol (m : ptrie positive) (x : positive) : positive :=
  match trie_get x m with Some y => y | None => x end.
TimeFun val_symbol.

Definition val_row_sizes {A} (rows : list (positive * list A)) : ptrie nat :=
  val_index (map (fun item => (fst item, length (snd item))) rows).
TimeFun val_row_sizes.

Definition val_size (sizes : ptrie nat) (b : positive) : nat :=
  match trie_get b sizes with Some n => n | None => 0 end.
TimeFun val_size.

Fixpoint val_add (xs : list positive) (known : ptrie unit) : ptrie unit :=
  match xs with
  | [] => known
  | x :: rest => PTrieCode.set x tt (val_add rest known)
  end.
TimeFun val_add.

Fixpoint val_unique (xs : list positive) (seen : ptrie unit) : bool :=
  match xs with
  | [] => true
  | x :: rest => if val_mem seen x then false else
      val_unique rest (PTrieCode.set x tt seen)
  end.
TimeFun val_unique.

Fixpoint val_same_length (xs ys : list positive) : bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xr, _ :: yr => val_same_length xr yr
  | _, _ => false
  end.
TimeFun val_same_length.

Definition val_home_rows {K G} (bs : list (positive * block positive K G))
    : list (positive * positive) :=
  flat_map (fun item => map (fun x => (x, fst item)) (block_defs (snd item))) bs.
TimeFun val_home_rows.

Definition val_use {K} (ic : list (positive * K * list positive))
    (out : list positive) (x : positive) (i : nat) : Prop :=
  (exists op args dst, nth_error ic i = Some (dst, op, args) /\ In x args) \/
  (i = length ic /\ In x out).

Lemma val_mem_set : forall seen x y,
  val_mem (PTrieCode.set x tt seen) y = true <-> y = x \/ val_mem seen y = true.
Proof.
  intros seen x y; destruct (Pos.eq_dec y x) as [Heq|Hneq].
  - subst y; unfold val_mem; rewrite PTrie.get_set_same; tauto.
  - unfold val_mem at 1; rewrite PTrie.get_set_other by exact Hneq.
    change (val_mem seen y = true <-> y = x \/ val_mem seen y = true); tauto.
Qed.

Lemma val_unique_sound : forall xs seen, val_unique xs seen = true ->
  NoDup xs /\ forall x, In x xs -> val_mem seen x = false.
Proof.
  induction xs as [|x rest IH]; intros seen Hcheck; cbn [val_unique] in Hcheck.
  - split; [constructor|intros y Hin; contradiction].
  - destruct (val_mem seen x) eqn:Hfresh; [discriminate|].
    destruct (IH _ Hcheck) as [Hnd Hdisjoint]; split.
    + constructor; [|exact Hnd]; intro Hin.
      specialize (Hdisjoint x Hin); unfold val_mem in Hdisjoint;
        rewrite PTrie.get_set_same in Hdisjoint; discriminate.
    + intros y [Heq|Hin]; [subst y; exact Hfresh|].
      specialize (Hdisjoint y Hin); destruct (Pos.eq_dec y x) as [Heq|Hneq].
      * subst y; exact Hfresh.
      * unfold val_mem in Hdisjoint; rewrite PTrie.get_set_other in Hdisjoint by exact Hneq;
          exact Hdisjoint.
Qed.

Lemma val_add_member : forall xs known x,
  val_mem (val_add xs known) x = true <-> In x xs \/ val_mem known x = true.
Proof.
  induction xs as [|y rest IH]; intros known x; cbn [val_add]; [cbn; tauto|].
  rewrite val_mem_set, IH; cbn; intuition congruence.
Qed.

Lemma val_same_length_sound : forall xs ys,
  val_same_length xs ys = true -> length xs = length ys.
Proof.
  induction xs as [|x rest IH]; intros ys Hcheck; destruct ys as [|y yr];
    cbn [val_same_length] in Hcheck; try discriminate; [reflexivity|].
  cbn; f_equal; apply IH; exact Hcheck.
Qed.

Lemma val_index_lookup {A} : forall (rows : list (positive * A)) x,
  trie_get x (val_index rows) = lookup x rows.
Proof.
  induction rows as [|[y value] rest IH]; intro x; cbn [val_index lookup].
  - apply PTrie.get_empty.
  - destruct (Pos.eqb x y) eqn:Hxy.
    + apply Pos.eqb_eq in Hxy; subst x; apply PTrie.get_set_same.
    + apply Pos.eqb_neq in Hxy; rewrite PTrie.get_set_other by exact Hxy; apply IH.
Qed.

Lemma val_index_block {K G} : forall (bs : list (positive * block positive K G)) b,
  trie_get b (val_index bs) = find_block b bs.
Proof.
  intros bs b; rewrite val_index_lookup; induction bs as [|[id body] rest IH].
  - reflexivity.
  - cbn [lookup find_block]; destruct (Pos.eqb b id); auto.
Qed.

Lemma val_row_lookup {A} : forall (m : ptrie (list (positive * A))) b x,
  lookup x (index_row m b) =
    match trie_get b m with Some row => lookup x row | None => None end.
Proof.
  intros m b x; unfold index_row; destruct (trie_get b m); reflexivity.
Qed.

Lemma val_set_member : forall xs x, val_mem (val_set xs) x = true <-> In x xs.
Proof.
  induction xs as [|y rest IH]; intro x; cbn [val_set].
  - unfold val_mem; rewrite PTrie.get_empty; cbn; split; [discriminate|contradiction].
  - destruct (Pos.eq_dec x y) as [Heq|Hneq].
    + subst x; unfold val_mem; rewrite PTrie.get_set_same; cbn; tauto.
    + unfold val_mem at 1; rewrite PTrie.get_set_other by exact Hneq.
      change (val_mem (val_set rest) x = true <-> y = x \/ In x rest).
      rewrite IH; split; intro Hin; [right; exact Hin|destruct Hin; congruence || assumption].
Qed.

Lemma val_maps_spec : forall rho x y,
  val_maps rho x y = true <-> trie_get x rho = Some y.
Proof.
  intros rho x y; unfold val_maps; destruct (trie_get x rho) as [z|].
  - rewrite Pos.eqb_eq; split; congruence.
  - split; discriminate.
Qed.

Lemma val_lookup_in {A} : forall (rho : list (positive * A)) x y,
  lookup x rho = Some y -> In (x, y) rho.
Proof.
  induction rho as [|[z value] rest IH]; intros x y Hlookup; cbn [lookup] in Hlookup.
  - discriminate.
  - destruct (Pos.eqb x z) eqn:Hxz.
    + apply Pos.eqb_eq in Hxz; inversion Hlookup; subst; left; reflexivity.
    + right; eapply IH; exact Hlookup.
Qed.

Lemma val_home_source {K G} : forall (bs : list (positive * block positive K G)) x b,
  trie_get x (val_index (val_home_rows bs)) = Some b ->
  exists body, In (b, body) bs /\ In x (block_defs body).
Proof.
  intros bs x b Hget; rewrite val_index_lookup in Hget; apply val_lookup_in in Hget.
  unfold val_home_rows in Hget; apply in_flat_map in Hget as [[id body] [Hin Hrow]].
  apply in_map_iff in Hrow as [y [Heq Hy]]; cbn in Heq; injection Heq as Heqx Heqb;
    subst y id; exists body; auto.
Qed.

Lemma val_cfg_graph_edge {E} : forall vs es (src dst : E -> positive) e,
  In e es -> Spec.edge (cfg_graph vs es src dst) (src e) (dst e).
Proof.
  intros vs es src dst; induction es as [|a rest IH]; intros e Hin; [contradiction|].
  change (In (dst e) (index_row (PTrieCode.set (src a)
    (dst a :: succs (cfg_graph vs rest src dst) (src a))
    (succ (cfg_graph vs rest src dst))) (src e))).
  unfold index_row at 1.
  destruct (Pos.eq_dec (src e) (src a)) as [Heq|Hneq].
  - rewrite Heq, PTrie.get_set_same; cbn.
    destruct Hin as [Ha|Hin].
    + subst e; left; reflexivity.
    + right; specialize (IH e Hin); unfold Spec.edge in IH.
      rewrite Heq in IH; exact IH.
  - rewrite PTrie.get_set_other by exact Hneq.
    destruct Hin as [Ha|Hin]; [subst e; contradiction|]; apply IH; exact Hin.
Qed.

Lemma val_cfg_graph_path {E} : forall vs es (src dst : E -> positive) a route b,
  presentation_path es src dst a route b -> Spec.path (cfg_graph vs es src dst) a route b.
Proof.
  intros vs es src dst a route b Hpath; induction Hpath as [n|e rest target Hin Hpath IH].
  - apply Spec.path_refl.
  - eapply Spec.path_step; [apply val_cfg_graph_edge; exact Hin|exact IH].
Qed.

Definition val_inverse_ok (rho : renaming) (inverse : ptrie positive) : Prop :=
  forall x y, lookup x rho = Some y -> trie_get y inverse = Some x.

Lemma val_injective_sound : forall rho,
  val_injective rho = true -> val_inverse_ok rho (val_inverse rho).
Proof.
  intros rho Hcheck x y Hlookup; unfold val_injective in Hcheck.
  rewrite forallb_forall in Hcheck.
  specialize (Hcheck (x, y) (val_lookup_in rho x y Hlookup)).
  apply val_maps_spec in Hcheck; exact Hcheck.
Qed.

Lemma val_lookup_cons {A} (x y : positive) (value : A) rho :
  lookup x ((y, value) :: rho) = if Pos.eqb x y then Some value else lookup x rho.
Proof. reflexivity. Qed.

Lemma val_inverse_extend : forall rho inverse x y,
  val_inverse_ok rho inverse ->
  (match trie_get y inverse with Some owner => Pos.eqb x owner | None => true end) = true ->
  val_inverse_ok ((x, y) :: rho) (PTrieCode.set y x inverse).
Proof.
  intros rho inverse x y Hinv Hfresh z value Hlookup.
  rewrite val_lookup_cons in Hlookup; destruct (Pos.eqb z x) eqn:Hzx.
  - apply Pos.eqb_eq in Hzx; inversion Hlookup; subst; apply PTrie.get_set_same.
  - apply Pos.eqb_neq in Hzx.
    pose proof (Hinv z value Hlookup) as Hold.
    assert (Hneq : value <> y).
    { intro Heq; subst value; rewrite Hold in Hfresh; apply Pos.eqb_eq in Hfresh;
        congruence. }
    rewrite PTrie.get_set_other by exact Hneq; exact Hold.
Qed.

Definition val_agrees {A} (rho : renaming) (xs : list positive) (ss si : env A) : Prop :=
  forall x, In x xs -> exists y, lookup x rho = Some y /\ lookup y ss = lookup x si.

Lemma val_args_read {A} : forall xs ys rho live (ss si : env A),
  val_args (val_index rho) (val_set live) xs ys = true ->
  val_agrees rho live ss si -> read_vars ss ys = read_vars si xs.
Proof.
  induction xs as [|x rest IH]; intros ys rho live ss si Hargs Hagree;
    destruct ys as [|y yr]; cbn [val_args] in Hargs; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hargs as [Hhead Htail].
    apply andb_true_iff in Hhead as [Hknown Hmap].
    apply val_set_member in Hknown; apply val_maps_spec in Hmap.
    rewrite val_index_lookup in Hmap.
    destruct (Hagree x Hknown) as [z [Hz Hvalue]].
    rewrite Hmap in Hz; injection Hz as Heq; subst z.
    cbn [read_vars]; rewrite Hvalue, (IH yr rho live ss si Htail Hagree); reflexivity.
Qed.

Lemma val_agrees_extend {A} : forall rho inverse live x y (value : A) ss si,
  val_inverse_ok rho inverse -> val_agrees rho live ss si ->
  (match trie_get y inverse with Some owner => Pos.eqb x owner | None => true end) = true ->
  val_agrees ((x, y) :: rho) (x :: live) ((y, value) :: ss) ((x, value) :: si).
Proof.
  intros rho inverse live x y value ss si Hinv Hagree Hfresh z Hin.
  destruct (Pos.eq_dec z x) as [Heq|Hneq].
  - subst z; exists y; cbn [lookup]; rewrite !Pos.eqb_refl; auto.
  - destruct Hin as [Heq|Hin]; [congruence|].
    destruct (Hagree z Hin) as [v [Hv Hvalue]].
    assert (Hvy : v <> y).
    { intro Heq; subst v; rewrite (Hinv z y Hv) in Hfresh.
      apply Pos.eqb_eq in Hfresh; congruence. }
    apply Pos.eqb_neq in Hneq; apply Pos.eqb_neq in Hvy.
    exists v; cbn [lookup]; rewrite Hneq, Hvy; auto.
Qed.

Lemma val_args_length : forall rho known xs ys,
  val_args rho known xs ys = true -> length xs = length ys.
Proof.
  intros rho known xs; induction xs as [|x rest IH]; intros ys Hargs;
    destruct ys as [|y yr]; cbn [val_args] in Hargs; try discriminate; [reflexivity|].
  apply andb_true_iff in Hargs as [_ Htail]; cbn; f_equal; apply IH; exact Htail.
Qed.

Lemma val_args_covers : forall xs ys rho known x,
  val_args (val_index rho) known xs ys = true -> In x xs ->
  exists y, lookup x rho = Some y.
Proof.
  induction xs as [|z rest IH]; intros ys rho known x Hcheck Hin;
    destruct ys as [|y yr]; cbn [val_args] in Hcheck; try discriminate; [contradiction|].
  apply andb_true_iff in Hcheck as [Hhead Htail].
  destruct Hin as [Heq|Hin].
  - subst x; apply andb_true_iff in Hhead as [_ Hmap]; apply val_maps_spec in Hmap.
    rewrite val_index_lookup in Hmap; exists y; exact Hmap.
  - eapply IH; [exact Htail|exact Hin].
Qed.

Lemma val_bind_length {A} : forall xs (values : list A) s,
  length xs = length values -> exists entered, bind_vars xs values s = Some entered.
Proof.
  induction xs as [|x rest IH]; intros values s Hlength; destruct values as [|v vr];
    cbn in Hlength; try discriminate.
  - exists s; reflexivity.
  - cbn [bind_vars]; apply IH; lia.
Qed.

Lemma val_bind_length_of {A} : forall xs (values : list A) s entered,
  bind_vars xs values s = Some entered -> length xs = length values.
Proof.
  induction xs as [|x rest IH]; intros values s entered Hbind;
    destruct values as [|v vr]; cbn [bind_vars] in Hbind; try discriminate; [reflexivity|].
  cbn; f_equal; eapply IH; exact Hbind.
Qed.

Lemma val_bind_related {A} : forall xs ys values rho known inverse (ss si : env A) entered_i,
  val_args (val_index rho) known xs ys = true -> val_inverse_ok rho inverse ->
  (forall x y, lookup x rho = Some y -> lookup y ss = lookup x si) ->
  bind_vars xs values si = Some entered_i ->
  exists entered_s, bind_vars ys values ss = Some entered_s /\
    forall x y, lookup x rho = Some y -> lookup y entered_s = lookup x entered_i.
Proof.
  induction xs as [|x rest IH]; intros ys values rho known inverse ss si entered_i
    Hargs Hinv Hagree Hbind; destruct ys as [|y yr]; cbn [val_args] in Hargs;
    try discriminate; destruct values as [|value vr]; cbn [bind_vars] in Hbind;
    try discriminate.
  - injection Hbind as Heq; subst entered_i; exists ss; split; [reflexivity|exact Hagree].
  - apply andb_true_iff in Hargs as [Hhead Htail].
    apply andb_true_iff in Hhead as [_ Hmap]; apply val_maps_spec in Hmap;
      rewrite val_index_lookup in Hmap.
    cbn [bind_vars]; eapply IH; [exact Htail|exact Hinv| |exact Hbind].
    intros z v Hz; destruct (Pos.eq_dec z x) as [Heq|Hneq].
    + subst z; rewrite Hmap in Hz; injection Hz as Heq; subst v.
      cbn [lookup]; rewrite !Pos.eqb_refl; reflexivity.
    + assert (Hvy : v <> y).
      { intro Heq; subst v; pose proof (Hinv z y Hz) as Hzinv.
        rewrite (Hinv x y Hmap) in Hzinv; injection Hzinv as Heq; congruence. }
      apply Pos.eqb_neq in Hneq; apply Pos.eqb_neq in Hvy.
      cbn [lookup]; rewrite Hneq, Hvy; apply Hagree; exact Hz.
Qed.

Definition val_defined {A} (xs : list positive) (s : env A) : Prop :=
  forall x, In x xs -> exists value, lookup x s = Some value.

Lemma val_read_defined {A} : forall xs (s : env A),
  val_defined xs s -> exists values, read_vars s xs = Some values.
Proof.
  induction xs as [|x rest IH]; intros s Hdefined.
  - exists []; reflexivity.
  - destruct (Hdefined x (or_introl eq_refl)) as [value Hvalue].
    destruct (IH s) as [values Hvalues].
    { intros y Hin; apply Hdefined; right; exact Hin. }
    exists (value :: values); cbn [read_vars]; rewrite Hvalue, Hvalues; reflexivity.
Qed.

Lemma val_defined_extend {A} : forall xs x (value : A) s,
  val_defined xs s -> val_defined (x :: xs) ((x, value) :: s).
Proof.
  intros xs x value s Hdefined y Hin; destruct (Pos.eq_dec y x) as [Heq|Hneq].
  - subst y; exists value; cbn [lookup]; rewrite Pos.eqb_refl; reflexivity.
  - destruct Hin as [Heq|Hin]; [congruence|].
    destruct (Hdefined y Hin) as [old Hold].
    exists old; cbn [lookup]; apply Pos.eqb_neq in Hneq; rewrite Hneq; exact Hold.
Qed.

Lemma val_exec_defined {K A} (eval : K -> list A -> option A) : forall ic live si si',
  exec_code eval ic si = Some si' -> val_defined live si ->
  val_defined (map (fun i => fst (fst i)) ic ++ live) si'.
Proof.
  induction ic as [|[[x op] args] rest IH]; intros live si si' Hexec Hdefined.
  - cbn [exec_code] in Hexec; injection Hexec as Heq; subst si'; exact Hdefined.
  - cbn [exec_code] in Hexec; destruct (read_vars si args) as [values|];
      [|discriminate]; destruct (eval op values) as [value|]; [|discriminate].
    pose proof (val_defined_extend live x value si Hdefined) as Hnext.
    specialize (IH (x :: live) ((x, value) :: si) si' Hexec Hnext).
    intros y Hin; apply IH; cbn in Hin |- *; rewrite in_app_iff in Hin |- *; cbn; tauto.
Qed.

Lemma val_bind_defined {A} : forall ps values live (s entered : env A),
  bind_vars ps values s = Some entered -> val_defined live s ->
  val_defined (ps ++ live) entered.
Proof.
  induction ps as [|p rest IH]; intros values live s entered Hbind Hdefined;
    destruct values as [|value vr]; cbn [bind_vars] in Hbind; try discriminate.
  - injection Hbind as Heq; subst entered; exact Hdefined.
  - specialize (IH vr (p :: live) ((p, value) :: s) entered Hbind
      (val_defined_extend live p value s Hdefined)).
    intros x Hin; apply IH; cbn in Hin |- *; rewrite in_app_iff in Hin |- *; cbn; tauto.
Qed.

Lemma val_bind_symbols_sound {A} : forall ps args m bound (old current : env A) values,
  val_bind_symbols ps args m = Some bound -> read_vars old args = Some values ->
  (forall y, lookup y current = lookup (val_symbol m y) old) ->
  exists entered, bind_vars ps values current = Some entered /\
    forall y, lookup y entered = lookup (val_symbol bound y) old.
Proof.
  induction ps as [|p rest IH]; intros args m bound old current values Hbind Hread Hagree;
    destruct args as [|x xr]; cbn [val_bind_symbols] in Hbind; try discriminate.
  - injection Hbind as Heq; subst bound; cbn [read_vars] in Hread;
      injection Hread as Heq; subst values; exists current; split; [reflexivity|exact Hagree].
  - cbn [read_vars] in Hread; destruct (lookup x old) as [value|] eqn:Hvalue;
      [|discriminate]; destruct (read_vars old xr) as [vr|] eqn:Htail; [|discriminate].
    injection Hread as Heq; subst values; cbn [bind_vars].
    eapply IH; [exact Hbind|exact Htail|].
    intro y; destruct (Pos.eq_dec y p) as [Heq|Hneq].
    + subst y; cbn [lookup]; rewrite Pos.eqb_refl; unfold val_symbol.
      rewrite PTrie.get_set_same; symmetry; exact Hvalue.
    + cbn [lookup]; apply Pos.eqb_neq in Hneq as Htest; rewrite Htest.
      unfold val_symbol; rewrite PTrie.get_set_other by exact Hneq; apply Hagree.
Qed.

(** Deduplication never removes the last occurrence of a listed block identifier. *)
Lemma val_first_blocks_ids {K G} : forall (bs : list (positive * block positive K G)) b,
  In b (map fst bs) -> In b (map fst (first_blocks bs)).
Proof.
  assert (Hfold : forall (xs : list (positive * block positive K G)) seen kept,
    (forall b, trie_get b seen <> None -> In b (map fst kept)) -> forall b,
    In b (map fst xs) \/ In b (map fst kept) ->
    In b (map fst (snd (fold_left (fun acc item =>
      match trie_get (fst item) (fst acc) with
      | Some _ => acc
      | None => (PTrieCode.set (fst item) tt (fst acc), item :: snd acc)
      end) xs (seen, kept))))).
  { induction xs as [|[id body] rest IH]; intros seen kept Hseen b Hin.
    - cbn in Hin |- *; tauto.
    - cbn [fold_left fst snd] in *.
      change ((id = b \/ In b (map fst rest)) \/ In b (map fst kept)) in Hin.
      destruct (trie_get id seen) as [u|] eqn:Hget.
      + eapply IH; [exact Hseen|].
        destruct Hin as [[Heq|Hin]|Hin].
        * subst b; right; apply Hseen; rewrite Hget; discriminate.
        * left; exact Hin.
        * right; exact Hin.
      + eapply IH.
        * intros x Hpresent; destruct (Pos.eq_dec x id) as [Heq|Hneq].
          -- subst x; left; reflexivity.
          -- right; apply Hseen; rewrite PTrie.get_set_other in Hpresent by exact Hneq;
              exact Hpresent.
        * cbn; tauto. }
  intros bs b Hin; unfold first_blocks; rewrite rev_append_rev, app_nil_r, map_rev.
  apply (proj1 (in_rev _ b)); eapply Hfold; [|left; exact Hin].
  intros x Hpresent; rewrite PTrie.get_empty in Hpresent; contradiction.
Qed.

(** Cost accounting uses first-match indexes and charges each selected key once. *)

Lemma val_max_nat a b : graph_max a b = Nat.max a b.
Proof.
  revert b; induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.

Lemma val_width_member xs x : In x xs -> Pos.size_nat x <= vertex_width xs.
Proof.
  induction xs as [|a rest IH]; cbn [vertex_width fold_right]; intro Hin.
  - contradiction.
  - rewrite val_max_nat; fold (vertex_width rest); destruct Hin as [Heq|Hin].
    + subst x; apply Nat.le_max_l.
    + specialize (IH Hin); pose proof (Nat.le_max_r (Pos.size_nat a) (vertex_width rest));
        lia.
Qed.

Lemma val_function_width {K G} (p : func positive K G) x :
  In x (function_ids p) -> Pos.size_nat x <= function_width p.
Proof.
  intro Hin; unfold function_width; rewrite val_max_nat.
  eapply Nat.le_trans; [apply val_width_member; exact Hin|apply Nat.le_max_l].
Qed.

Lemma val_block_width {K G} (p : func positive K G) b body :
  In (b, body) (blocks _ _ _ p) -> Pos.size_nat b <= function_width p.
Proof.
  intro Hin; apply val_function_width; unfold function_ids; right.
  apply in_or_app; right; apply in_flat_map; exists (b, body); split; [exact Hin|].
  cbn; left; reflexivity.
Qed.

Lemma val_cert_env_width c b row :
  In (b, row) (fst c) -> Pos.size_nat b <= vertex_width (cert_ids c).
Proof.
  intro Hin; apply val_width_member; unfold cert_ids; apply in_or_app; left.
  apply in_flat_map; exists (b, row); split; [exact Hin|]; cbn; left; reflexivity.
Qed.

Lemma val_cert_live_width c b row :
  In (b, row) (snd c) -> Pos.size_nat b <= vertex_width (cert_ids c).
Proof.
  intro Hin; apply val_width_member; unfold cert_ids; apply in_or_app; right.
  apply in_flat_map; exists (b, row); split; [exact Hin|]; cbn; left; reflexivity.
Qed.

Lemma val_cert_rows c : length (fst c) + length (snd c) <= cert_size c.
Proof.
  destruct c as [envs lives]; unfold cert_size; cbn [fst snd].
  assert (Henv : length envs <=
    fold_right (fun row n => 1 + 2 * length (snd row) + n) 0 envs).
  { induction envs as [|[b row] rest IH]; cbn [length fold_right snd] in *; lia. }
  assert (Hlive : length lives <=
    fold_right (fun row n => 1 + length (snd row) + n) 0 lives).
  { induction lives as [|[b row] rest IH]; cbn [length fold_right snd] in *; lia. }
  lia.
Qed.

Lemma val_index_time {A} : forall (rows : list (positive * A)) w,
  (forall x a, In (x, a) rows -> Pos.size_nat x <= w) ->
  (T_val_index rows <=
    (PTrieT.c_trie + 2) * N.of_nat (length rows) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction rows as [|[x a] rest IH]; intros w Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply (Hwidth x a); left; reflexivity).
    specialize (IH w ltac:(intros y value Hin; apply (Hwidth y value); right; exact Hin)).
    pose proof (PTrieT.T_set_le A x a (val_index rest)) as Hset.
    time_unfold @T_val_index; cbn [length]; rewrite Nat2N.inj_succ.
    rewrite !Nat2N.inj_add in Hset |- *; time_cbn; nia.
Qed.

Lemma val_set_time : forall xs w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_val_set xs <=
    (PTrieT.c_trie + 2) * N.of_nat (length xs) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros w Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply Hwidth; left; reflexivity).
    specialize (IH w ltac:(intros y Hin; apply Hwidth; right; exact Hin)).
    pose proof (PTrieT.T_set_le unit x tt (val_set rest)) as Hset.
    time_unfold T_val_set; cbn [length]; rewrite Nat2N.inj_succ.
    rewrite !Nat2N.inj_add in Hset |- *; time_cbn; nia.
Qed.

Lemma val_mem_time : forall known x w, Pos.size_nat x <= w ->
  (T_val_mem known x <= 3 * N.of_nat (w + 1))%N.
Proof.
  intros known x w Hwidth; time_unfold T_val_mem.
  rewrite PTrieT.trie_get_clock; destruct (trie_get x known); time_cbn; nia.
Qed.

Lemma val_maps_time : forall rho x y w, Pos.size_nat x <= w -> Pos.size_nat y <= w ->
  (T_val_maps rho x y <= 4 * N.of_nat (w + 1))%N.
Proof.
  intros rho x y w Hx Hy; time_unfold T_val_maps; rewrite PTrieT.trie_get_clock.
  destruct (trie_get x rho) as [z|]; [pose proof (Pos.T_eqb_le y z)|]; time_cbn; nia.
Qed.

Lemma val_nat_leb_right : forall n m,
  (Nat.T_leb n m <= N.of_nat m + 1)%N.
Proof.
  intros n m; revert n; induction m as [|m IH]; intros [|n]; time_step.
Qed.

Lemma val_map_time {A B} : forall (f : A -> B) Tf xs,
  (ListDef.T_map f Tf xs <= N.of_nat (length xs) + 1 +
    fold_right N.add 0%N (map Tf xs))%N.
Proof.
  intros f Tf xs; induction xs; time_step.
Qed.

Lemma val_forallb_time {A} : forall (f : A -> bool) Tf xs,
  (List.T_forallb f Tf xs <= 2 * N.of_nat (length xs) + 1 +
    fold_right N.add 0%N (map Tf xs))%N.
Proof.
  intros f Tf xs; induction xs; time_step.
Qed.

Lemma val_forallb_uniform {A} : forall (f : A -> bool) Tf xs k,
  (forall x, In x xs -> (Tf x <= k)%N) ->
  (List.T_forallb f Tf xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intros f Tf xs; induction xs as [|x rest IH]; intros k Hbound.
  - time_step.
  - pose proof (Hbound x ltac:(left; reflexivity)) as Hhead.
    specialize (IH k ltac:(intros y Hin; apply Hbound; right; exact Hin)); time_step.
Qed.

Lemma val_inverse_time : forall rho w,
  (forall x y, In (x, y) rho -> Pos.size_nat x <= w /\ Pos.size_nat y <= w) ->
  (T_val_inverse rho <=
    (PTrieT.c_trie + 8) * N.of_nat (length rho) * N.of_nat (w + 1) + 3)%N.
Proof.
  intros rho w Hwidth.
  pose proof (val_index_time (map (fun xy => (snd xy, fst xy)) rho) w
    ltac:(intros y x Hin; apply in_map_iff in Hin as [[a b] [Heq Hin]];
      cbn in Heq; injection Heq as Hb Ha; subst a b;
      exact (proj2 (Hwidth x y Hin)))) as Hindex.
  pose proof (ListDef.T_map_le (fun xy : positive * positive => (snd xy, fst xy))
    (fun xy => (1 + (Datatypes.T_snd xy + Datatypes.T_fst xy))%N) 3%N rho
    ltac:(intro xy; time_simpl; time_cbn; nia)) as Hmap.
  time_unfold T_val_inverse; rewrite length_map in Hindex;
    revert Hmap; time_simpl; intro Hmap;
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.

Lemma val_injective_time : forall rho w,
  (forall x y, In (x, y) rho -> Pos.size_nat x <= w /\ Pos.size_nat y <= w) ->
  (T_val_injective rho <=
    (PTrieT.c_trie + 20) * N.of_nat (length rho) * N.of_nat (w + 1) + 5)%N.
Proof.
  intros rho w Hwidth; pose proof (val_inverse_time rho w Hwidth) as Hinv.
  pose proof (val_forallb_uniform
    (fun xy : positive * positive => val_maps (val_inverse rho) (snd xy) (fst xy))
    (fun xy => (1 + (Datatypes.T_snd xy + Datatypes.T_fst xy +
      T_val_maps (val_inverse rho) (snd xy) (fst xy)))%N) rho
    (7 * N.of_nat (w + 1))%N ltac:(intros [x y] Hin;
      destruct (Hwidth x y Hin) as [Hx Hy];
      pose proof (val_maps_time (val_inverse rho) y x w Hy Hx);
      time_simpl; time_cbn; nia)) as Hscan.
  time_unfold T_val_injective; revert Hscan; time_simpl; intro Hscan;
    rewrite !Nat2N.inj_add in *;
    time_cbn_all; nia.
Qed.

Lemma val_args_time : forall xs ys rho known w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (forall y, In y ys -> Pos.size_nat y <= w) ->
  (T_val_args rho known xs ys <= 10 * N.of_nat (length xs) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros ys rho known w Hxs Hys.
  - time_step.
  - destruct ys as [|y yr].
    + time_step.
    + assert (Hx : Pos.size_nat x <= w) by (apply Hxs; left; reflexivity).
      assert (Hy : Pos.size_nat y <= w) by (apply Hys; left; reflexivity).
      specialize (IH yr rho known w
        ltac:(intros z Hin; apply Hxs; right; exact Hin)
        ltac:(intros z Hin; apply Hys; right; exact Hin)).
      pose proof (val_mem_time known x w Hx) as Hmem.
      pose proof (val_maps_time rho x y w Hx Hy) as Hmaps; time_step.
Qed.

Lemma val_add_time : forall xs known w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_val_add xs known <=
    (PTrieT.c_trie + 2) * N.of_nat (length xs) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros known w Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply Hwidth; left; reflexivity).
    specialize (IH known w ltac:(intros y Hin; apply Hwidth; right; exact Hin)).
    pose proof (PTrieT.T_set_le unit x tt (val_add rest known)) as Hset.
    time_unfold T_val_add; time_cbn; nia.
Qed.

Lemma val_sum_add {A} : forall (f g : A -> nat) xs,
  fold_right (fun x n => f x + g x + n) 0 xs =
    fold_right (fun x n => f x + n) 0 xs + fold_right (fun x n => g x + n) 0 xs.
Proof.
  intros f g xs; induction xs; cbn; lia.
Qed.

Lemma val_sum_mono {A} : forall (f g : A -> nat) xs,
  (forall x, In x xs -> f x <= g x) ->
  fold_right (fun x n => f x + n) 0 xs <= fold_right (fun x n => g x + n) 0 xs.
Proof.
  intros f g xs; induction xs as [|x rest IH]; intro Hbound; cbn; [lia|].
  pose proof (Hbound x ltac:(left; reflexivity)) as Hhead.
  specialize (IH ltac:(intros y Hin; apply Hbound; right; exact Hin)); lia.
Qed.

Lemma val_sum_absent : forall ids key amount, ~ In key ids ->
  fold_right (fun b n => (if Pos.eqb b key then amount else 0) + n) 0 ids = 0.
Proof.
  induction ids as [|b rest IH]; intros key amount Hnone; cbn; [reflexivity|].
  destruct (Pos.eqb b key) eqn:Hkey.
  - apply Pos.eqb_eq in Hkey; subst b; exfalso; apply Hnone; left; reflexivity.
  - apply IH; intro Hin; apply Hnone; right; exact Hin.
Qed.

Lemma val_sum_single : forall ids key amount, NoDup ids ->
  fold_right (fun b n => (if Pos.eqb b key then amount else 0) + n) 0 ids <= amount.
Proof.
  induction ids as [|b rest IH]; intros key amount Hdistinct; cbn; [lia|].
  inversion Hdistinct as [|? ? Hnone Htail]; subst.
  destruct (Pos.eqb b key) eqn:Hkey.
  - apply Pos.eqb_eq in Hkey; subst b; rewrite val_sum_absent by exact Hnone; lia.
  - apply IH; exact Htail.
Qed.

Lemma val_lookup_sum {A} : forall (rows : list (positive * A)) ids (weight : A -> nat),
  NoDup ids ->
  fold_right (fun b n =>
    (match lookup b rows with Some value => weight value | None => 0 end) + n) 0 ids <=
      fold_right (fun item n => weight (snd item) + n) 0 rows.
Proof.
  induction rows as [|[key value] rest IH]; intros ids weight Hdistinct.
  - clear Hdistinct; induction ids; cbn [lookup fold_right]; auto.
  - specialize (IH ids weight Hdistinct).
    pose proof (val_sum_single ids key (weight value) Hdistinct) as Hone.
    pose proof (val_sum_mono
      (fun b => match lookup b ((key, value) :: rest) with
        Some a => weight a | None => 0 end)
      (fun b => (if Pos.eqb b key then weight value else 0) +
        match lookup b rest with Some a => weight a | None => 0 end) ids
      ltac:(intros b Hin; cbn [lookup]; destruct (Pos.eqb b key); lia)) as Hstep.
    cbn beta in Hstep.
    rewrite (val_sum_add (fun b => if Pos.eqb b key then weight value else 0)
      (fun b => match lookup b rest with Some a => weight a | None => 0 end) ids) in Hstep.
    cbn beta in Hstep; cbn [fold_right snd]; lia.
Qed.

Lemma val_nat_sum {A} : forall (f : A -> nat) xs,
  fold_right N.add 0%N (map (fun x => N.of_nat (f x)) xs) =
    N.of_nat (fold_right (fun x n => f x + n) 0 xs).
Proof.
  intros f xs; induction xs; cbn [map fold_right]; [reflexivity|].
  rewrite Nat2N.inj_add, IHxs; reflexivity.
Qed.

Lemma val_sum_time {A} : forall (f : A -> nat) (Tf : A -> N) xs c w,
  (forall x, In x xs -> (Tf x <= c * N.of_nat (f x) * w)%N) ->
  (fold_right N.add 0%N (map Tf xs) <=
    c * N.of_nat (fold_right (fun x n => (f x + n)%nat) 0%nat xs) * w)%N.
Proof.
  intros f Tf xs; induction xs as [|x rest IH]; intros c w Hbound.
  - time_cbn; nia.
  - pose proof (Hbound x ltac:(left; reflexivity)) as Hhead.
    specialize (IH c w ltac:(intros y Hin; apply Hbound; right; exact Hin));
      cbn [map fold_right]; rewrite Nat2N.inj_add; nia.
Qed.

Lemma val_unique_time : forall xs seen w,
  (forall x, In x xs -> Pos.size_nat x <= w) ->
  (T_val_unique xs seen <=
    (PTrieT.c_trie + 5) * N.of_nat (length xs) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction xs as [|x rest IH]; intros seen w Hwidth.
  - time_step.
  - assert (Hx : Pos.size_nat x <= w) by (apply Hwidth; left; reflexivity).
    specialize (IH (PTrieCode.set x tt seen) w
      ltac:(intros y Hin; apply Hwidth; right; exact Hin)).
    pose proof (val_mem_time seen x w Hx) as Hmem.
    pose proof (PTrieT.T_set_le unit x tt seen) as Hset.
    time_unfold T_val_unique; destruct (val_mem seen x); time_cbn; nia.
Qed.

Lemma val_bind_symbols_time : forall args ps m w,
  (forall p, In p ps -> Pos.size_nat p <= w) ->
  (T_val_bind_symbols ps args m <=
    (PTrieT.c_trie + 2) * N.of_nat (length args) * N.of_nat (w + 1) + 1)%N.
Proof.
  induction args as [|x xr IH]; intros ps m w Hwidth; destruct ps as [|p pr].
  - time_step.
  - time_step.
  - time_step.
  - assert (Hp : Pos.size_nat p <= w) by (apply Hwidth; left; reflexivity).
    specialize (IH pr (PTrieCode.set p x m) w
      ltac:(intros y Hin; apply Hwidth; right; exact Hin)).
    pose proof (PTrieT.T_set_le positive p x m) as Hset.
    time_unfold T_val_bind_symbols; time_cbn; nia.
Qed.

Lemma val_same_length_time : forall xs ys,
  (T_val_same_length xs ys <= N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xr IH]; intros [|y yr]; time_step.
Qed.

Lemma val_symbol_time : forall m x w, Pos.size_nat x <= w ->
  (T_val_symbol m x <= 3 * N.of_nat (w + 1))%N.
Proof.
  intros m x w Hx; time_unfold T_val_symbol; rewrite PTrieT.trie_get_clock.
  destruct (trie_get x m); time_cbn; nia.
Qed.

Lemma val_size_time : forall m x w, Pos.size_nat x <= w ->
  (T_val_size m x <= 3 * N.of_nat (w + 1))%N.
Proof.
  intros m x w Hx; time_unfold T_val_size; rewrite PTrieT.trie_get_clock.
  destruct (trie_get x m); time_cbn; nia.
Qed.

Lemma val_row_time {A} : forall (m : ptrie (list A)) x w, Pos.size_nat x <= w ->
  (T_index_row m x <= 3 * N.of_nat (w + 1))%N.
Proof.
  intros m x w Hx; time_unfold @T_index_row; rewrite PTrieT.trie_get_clock.
  destruct (trie_get x m); time_cbn; nia.
Qed.

Lemma val_fold_left_uniform {A B} : forall (f : A -> B -> A) Tf xs k,
  (forall acc x, In x xs -> (Tf acc x <= k)%N) -> forall acc,
  (List.T_fold_left f Tf xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros f Tf xs; induction xs as [|x rest IH]; intros k Hbound acc.
  - time_step.
  - pose proof (Hbound acc x ltac:(left; reflexivity)) as Hhead.
    specialize (IH k ltac:(intros state y Hin; apply Hbound; right; exact Hin) (f acc x));
      time_step.
Qed.

Fixpoint val_selected {K G} (seen : ptrie unit)
    (bs : list (positive * block positive K G)) : list (positive * block positive K G) :=
  match bs with
  | [] => []
  | item :: rest =>
    match trie_get (fst item) seen with
    | Some _ => val_selected seen rest
    | None => item :: val_selected (PTrieCode.set (fst item) tt seen) rest
    end
  end.

Lemma val_selected_fold {K G} (bs : list (positive * block positive K G)) seen acc :
  snd (fold_left (fun state item =>
    match trie_get (fst item) (fst state) with
    | Some _ => state
    | None => (PTrieCode.set (fst item) tt (fst state), item :: snd state)
    end) bs (seen, acc)) = rev (val_selected seen bs) ++ acc.
Proof.
  revert seen acc; induction bs as [|item rest IH]; intros seen acc.
  - reflexivity.
  - cbn [fold_left val_selected fst snd].
    destruct (trie_get (fst item) seen) as [[]|].
    + apply IH.
    + rewrite IH; cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma val_first_selected {K G} (bs : list (positive * block positive K G)) :
  first_blocks bs = val_selected Empty bs.
Proof.
  unfold first_blocks; rewrite val_selected_fold, app_nil_r, rev_append_rev, app_nil_r.
  apply rev_involutive.
Qed.

Lemma val_selected_in {K G} (bs : list (positive * block positive K G)) seen item :
  In item (val_selected seen bs) -> In item bs /\ trie_get (fst item) seen = None.
Proof.
  revert seen; induction bs as [|a rest IH]; intros seen Hin.
  - contradiction.
  - cbn [val_selected] in Hin.
    destruct (trie_get (fst a) seen) as [[]|] eqn:Hseen.
    + destruct (IH seen Hin) as [Hrest Hnone]; split; [right; exact Hrest|exact Hnone].
    + destruct Hin as [Heq|Hin].
      * subst item; split; [left; reflexivity|exact Hseen].
      * destruct (IH _ Hin) as [Hrest Hnone]; split; [right; exact Hrest|].
        destruct (Pos.eq_dec (fst item) (fst a)) as [Heq|Hneq].
        -- rewrite Heq, PTrie.get_set_same in Hnone; discriminate.
        -- rewrite PTrie.get_set_other in Hnone by exact Hneq; exact Hnone.
Qed.

Lemma val_selected_nodup {K G} (bs : list (positive * block positive K G)) seen :
  NoDup (map fst (val_selected seen bs)).
Proof.
  revert seen; induction bs as [|a rest IH]; intro seen.
  - constructor.
  - cbn [val_selected]; destruct (trie_get (fst a) seen) as [[]|].
    + apply IH.
    + cbn [map]; constructor; [|apply IH].
      intros Hin; apply in_map_iff in Hin as [item [Heq Hin]].
      apply val_selected_in in Hin as [_ Hnone].
      rewrite Heq, PTrie.get_set_same in Hnone; discriminate.
Qed.

Lemma val_selected_sum {K G} : forall (bs : list (positive * block positive K G)) seen
    (weight : positive * block positive K G -> nat),
  fold_right (fun item n => weight item + n) 0 (val_selected seen bs) <=
    fold_right (fun item n => weight item + n) 0 bs.
Proof.
  induction bs as [|a rest IH]; intros seen weight; cbn [val_selected fold_right]; [lia|].
  destruct (trie_get (fst a) seen) as [[]|]; cbn [fold_right].
  - specialize (IH seen weight); lia.
  - specialize (IH (PTrieCode.set (fst a) tt seen) weight); lia.
Qed.

Lemma val_selected_length {K G} (bs : list (positive * block positive K G)) seen :
  length (val_selected seen bs) <= length bs.
Proof.
  revert seen; induction bs as [|a rest IH]; intro seen; cbn [val_selected]; [lia|].
  destruct (trie_get (fst a) seen) as [[]|]; cbn [length].
  - specialize (IH seen); lia.
  - specialize (IH (PTrieCode.set (fst a) tt seen)); lia.
Qed.

Lemma val_row_sizes_map_time {A} : forall (rows : list (positive * list A)),
  (ListDef.T_map (fun item => (fst item, length (snd item)))
    (fun item => (1 + (Datatypes.T_fst item + (Datatypes.T_snd item +
      Datatypes.T_length (snd item))))%N) rows <=
    6 * N.of_nat (length rows) +
      N.of_nat (fold_right (fun item n => (length (snd item) + n)%nat) 0%nat rows) + 1)%N.
Proof.
  induction rows as [|[b row] rest IH].
  - time_step.
  - pose proof (Datatypes.T_length_le row) as Hlength;
      revert IH; time_simpl; intro IH; time_step.
Qed.

Lemma val_row_sizes_time {A} : forall (rows : list (positive * list A)) w,
  (forall b row, In (b, row) rows -> Pos.size_nat b <= w) ->
  (T_val_row_sizes rows <= (PTrieT.c_trie + 10) *
    N.of_nat (length rows + fold_right (fun item n => (length (snd item) + n)%nat) 0%nat rows) *
    N.of_nat (w + 1) + 3)%N.
Proof.
  intros rows w Hwidth.
  pose proof (val_index_time (map (fun item => (fst item, length (snd item))) rows) w
    ltac:(intros b n Hin; apply in_map_iff in Hin as [[key row] [Heq Hin]];
      cbn in Heq; injection Heq as Hkey Hn; subst key;
      exact (Hwidth b row Hin))) as Hindex.
  pose proof (val_row_sizes_map_time rows) as Hmap.
  time_unfold @T_val_row_sizes; rewrite length_map in Hindex;
    revert Hmap; time_simpl; intro Hmap; rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.

Lemma val_forallb_extra {A} : forall (f : A -> bool) Tf work xs k,
  (forall x, In x xs -> (Tf x <= work x + k)%N) ->
  (List.T_forallb f Tf xs <= (k + 2) * N.of_nat (length xs) + 1 +
    fold_right N.add 0%N (map work xs))%N.
Proof.
  intros f Tf work xs; induction xs as [|x rest IH]; intros k Hbound.
  - time_step.
  - pose proof (Hbound x ltac:(left; reflexivity)) as Hhead.
    specialize (IH k ltac:(intros y Hin; apply Hbound; right; exact Hin)).
    time_unfold List.T_forallb; time_simpl; time_cbn; nia.
Qed.

Lemma val_first_time {K G} : forall (bs : list (positive * block positive K G)) w,
  (forall b body, In (b, body) bs -> Pos.size_nat b <= w) ->
  (T_first_blocks bs <=
    (PTrieT.c_trie + 16) * N.of_nat (length bs + 1) * N.of_nat (w + 1))%N.
Proof.
  intros bs w Hwidth; time_unfold @T_first_blocks; time_simpl.
  lazymatch goal with
  | |- context [List.T_fold_left ?f ?Tf bs (Empty, [])] =>
    pose proof (val_fold_left_uniform f Tf bs
      ((PTrieT.c_trie + 12) * N.of_nat (w + 1))%N
      ltac:(intros [seen kept] [b body] Hin;
        pose proof (Hwidth b body Hin) as Hb;
        pose proof (PTrieT.T_set_le unit b tt seen) as Hset;
        time_cbn; rewrite PTrieT.trie_get_clock;
        destruct (trie_get b seen); time_simpl; time_cbn; nia) (Empty, [])) as Hfold
  end.
  lazymatch goal with
  | |- context [List.T_rev_append ?items []] =>
    assert (Hlength : length items <= length bs)
      by (rewrite val_selected_fold, app_nil_r, length_rev; apply val_selected_length);
    pose proof (List.T_rev_append_le items []) as Hrev
  end.
  rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
Qed.
Definition val_cfg_row_count (vs : list positive) (rows : ptrie (list positive)) : nat :=
  fold_right (fun v n => length (index_row rows v) + n) 0 vs.

Lemma val_cfg_row_count_empty vs : val_cfg_row_count vs Empty = 0.
Proof.
  induction vs as [|v rest IH]; [reflexivity|].
  unfold val_cfg_row_count at 1; cbn [fold_right].
  unfold index_row at 1. rewrite PTrie.get_empty. exact IH.
Qed.

Lemma val_cfg_row_count_other vs rows id values : ~ In id vs ->
  val_cfg_row_count vs (PTrieCode.set id values rows) = val_cfg_row_count vs rows.
Proof.
  induction vs as [|a rest IH]; intro Hfresh; [reflexivity|].
  unfold val_cfg_row_count at 1 2; cbn [fold_right].
  assert (Ha : a <> id) by (intro Heq; subst a; apply Hfresh; now left).
  unfold index_row at 1. rewrite PTrie.get_set_other by exact Ha.
  fold (val_cfg_row_count rest (PTrieCode.set id values rows)).
  fold (val_cfg_row_count rest rows). rewrite IH; [reflexivity|].
  intro Hin; apply Hfresh; now right.
Qed.

Lemma val_cfg_row_count_cons vs rows id value : NoDup vs -> In id vs ->
  val_cfg_row_count vs (PTrieCode.set id (value :: index_row rows id) rows) =
    S (val_cfg_row_count vs rows).
Proof.
  induction vs as [|a rest IH]; intros Hdistinct Hin; [contradiction|].
  inversion Hdistinct as [|v vs' Hfresh Hrest]; subst.
  unfold val_cfg_row_count at 1 2; cbn [fold_right].
  fold (val_cfg_row_count rest (PTrieCode.set id (value :: index_row rows id) rows)).
  fold (val_cfg_row_count rest rows).
  destruct (Pos.eq_dec a id) as [Heq|Hneq].
  - subst a. unfold index_row at 1. rewrite PTrie.get_set_same. cbn [length].
    rewrite val_cfg_row_count_other by exact Hfresh. reflexivity.
  - unfold index_row at 1. rewrite PTrie.get_set_other by exact Hneq.
    rewrite IH by (first [exact Hrest|destruct Hin as [Heq|Hin]; [congruence|exact Hin]]).
    change (length (index_row rows a) + S (val_cfg_row_count rest rows) =
      S (length (index_row rows a) + val_cfg_row_count rest rows)). lia.
Qed.

(** Indexed CFG edge counts retain every supplied occurrence exactly once. *)
Lemma val_cfg_edge_count {E} vs es (src dst : E -> positive) :
  NoDup vs -> (forall e, In e es -> In (src e) vs) ->
  graph_e (cfg_graph vs es src dst) = length es.
Proof.
  intro Hdistinct. induction es as [|a rest IH]; intro Hsources.
  - apply val_cfg_row_count_empty.
  - change (val_cfg_row_count vs (PTrieCode.set (src a)
      (dst a :: index_row (succ (cfg_graph vs rest src dst)) (src a))
      (succ (cfg_graph vs rest src dst))) = S (length rest)).
    rewrite val_cfg_row_count_cons; [|exact Hdistinct|apply Hsources; now left].
    f_equal. apply IH. intros e Hin; apply Hsources; now right.
Qed.

Lemma val_cfg_target {E} vs es (src dst : E -> positive) u v :
  In v (succs (cfg_graph vs es src dst) u) -> exists e, In e es /\ dst e = v.
Proof.
  induction es as [|a rest IH].
  - change (In v (index_row Empty u) -> exists e, In e [] /\ dst e = v).
    unfold index_row; rewrite PTrie.get_empty; contradiction.
  - change (In v (index_row (PTrieCode.set (src a)
      (dst a :: succs (cfg_graph vs rest src dst) (src a))
      (succ (cfg_graph vs rest src dst))) u) -> exists e, In e (a :: rest) /\ dst e = v).
    unfold index_row at 1. destruct (Pos.eq_dec u (src a)) as [Heq|Hneq].
    + rewrite Heq, PTrie.get_set_same. intros [Htarget|Hin].
      * exists a; split; [now left|exact Htarget].
      * rewrite <- Heq in Hin. destruct (IH Hin) as [e [Hedge Htarget]].
        exists e; split; [now right|exact Htarget].
    + rewrite PTrie.get_set_other by exact Hneq. intro Hin.
      destruct (IH Hin) as [e [Hedge Htarget]]. exists e; split; [now right|exact Htarget].
Qed.

Lemma val_cfg_graph_max a b : graph_max a b = Nat.max a b.
Proof.
  revert b; induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.

Lemma val_cfg_fold_max_le {A} (xs : list A) (weight : A -> nat) width :
  (forall x, In x xs -> weight x <= width) ->
  fold_right (fun x n => graph_max (weight x) n) 0 xs <= width.
Proof.
  induction xs as [|x rest IH]; intro Hweight; [cbn [fold_right]; lia|].
  cbn [fold_right]. rewrite val_cfg_graph_max. apply Nat.max_lub.
  - apply Hweight; now left.
  - apply IH. intros y Hin; apply Hweight; now right.
Qed.

Lemma val_cfg_vertex_width_le vs width :
  (forall v, In v vs -> Pos.size_nat v <= width) -> vertex_width vs <= width.
Proof.
  induction vs as [|v rest IH]; intro Hwidth; [cbn [vertex_width fold_right]; lia|].
  cbn [vertex_width fold_right]. rewrite val_cfg_graph_max.
  fold (vertex_width rest). apply Nat.max_lub.
  - apply Hwidth; now left.
  - apply IH. intros x Hin; apply Hwidth; now right.
Qed.

(** CFG width is bounded by its listed vertices and supplied targets. *)
Lemma val_cfg_width {E} vs es (src dst : E -> positive) width :
  (forall v, In v vs -> Pos.size_nat v <= width) ->
  (forall e, In e es -> Pos.size_nat (dst e) <= width) ->
  graph_width (cfg_graph vs es src dst) <= width.
Proof.
  intros Hnodes Htargets. unfold graph_width, cfg_graph at 1.
  rewrite val_cfg_graph_max. apply Nat.max_lub.
  - now apply val_cfg_vertex_width_le.
  - change (fold_right (fun v n => graph_max
      (vertex_width (succs (cfg_graph vs es src dst) v)) n) 0 vs <= width).
    assert (Hrow : forall v, vertex_width (succs (cfg_graph vs es src dst) v) <= width).
    { intro v; apply val_cfg_vertex_width_le. intros target Hin.
      destruct (val_cfg_target _ _ _ _ _ _ Hin) as [e [Hedge Heq]].
      subst target; now apply Htargets. }
    apply val_cfg_fold_max_le. intros v Hin; apply Hrow.
Qed.


Lemma val_code_charge : forall r l s c rho live code ops width total,
  (r <= c)%N -> (l <= c)%N -> (s <= c)%N -> (12 <= c)%N ->
  (rho + live + code <= total)%N ->
  (r * rho * width + l * live * width + s * code * width + s * ops + 12 <=
    c * total * width + c * (ops + 1))%N.
Proof.
  intros r l s c rho live code ops width total Hr Hl Hs Hc Hcount.
  assert (Hrho : (r * rho * width <= c * rho * width)%N)
    by (apply N.mul_le_mono_r; apply N.mul_le_mono_r; exact Hr).
  assert (Hlive : (l * live * width <= c * live * width)%N)
    by (apply N.mul_le_mono_r; apply N.mul_le_mono_r; exact Hl).
  assert (Hcode : (s * code * width <= c * code * width)%N)
    by (apply N.mul_le_mono_r; apply N.mul_le_mono_r; exact Hs).
  assert (Hops : (s * ops <= c * ops)%N) by (apply N.mul_le_mono_r; exact Hs).
  eapply N.le_trans with (m :=
    (c * rho * width + c * live * width + c * code * width + c * ops + c)%N).
  - repeat apply N.add_le_mono; assumption.
  - replace (c * rho * width + c * live * width + c * code * width + c * ops + c)%N
      with (c * (rho + live + code) * width + c * (ops + 1))%N by ring.
    apply N.add_le_mono; [|apply N.le_refl].
    apply N.mul_le_mono_r; apply N.mul_le_mono_l; exact Hcount.
Qed.

Definition val_body_vars {K G} (body : block positive K G) : list positive :=
  params _ _ _ body ++ flat_map (fun '(x, _, args) => x :: args)
    (code _ _ _ body) ++ exit_uses (term _ _ _ body).

Definition val_body_units {K G} (body : block positive K G) : nat :=
  length (val_body_vars body) + length (code _ _ _ body) + 1.

Lemma val_function_units {K G} (p : func positive K G) :
  fold_right (fun item n => val_body_units (snd item) + n) 0 (blocks _ _ _ p) <=
    function_size p.
Proof.
  destruct p as [start ins bs]; unfold function_size, function_vars; cbn [blocks inputs].
  rewrite length_app; induction bs as [|[b body] rest IH]; cbn [flat_map fold_right length snd].
  - lia.
  - unfold val_body_units, val_body_vars in *; rewrite !length_app in *;
      cbn beta in *; lia.
Qed.

Lemma val_code_vars_length {K} : forall (ic : list (positive * K * list positive)),
  length (flat_map (fun '(x, _, args) => x :: args) ic) =
    length ic + fold_right (fun i n => length (snd i) + n) 0 ic.
Proof.
  induction ic as [|[[x op] args] rest IH]; cbn [flat_map fold_right length snd]; [reflexivity|].
  rewrite length_app, IH; cbn [length]; lia.
Qed.

Lemma val_body_counts {K G} (body : block positive K G) :
  length (params _ _ _ body) + length (code _ _ _ body) +
    fold_right (fun i n => length (snd i) + n) 0 (code _ _ _ body) +
    length (exit_uses (term _ _ _ body)) + 1 <= val_body_units body.
Proof.
  unfold val_body_units, val_body_vars; rewrite !length_app, val_code_vars_length; lia.
Qed.

Lemma val_entry_width {K G} (p : func positive K G) :
  Pos.size_nat (entry _ _ _ p) <= function_width p.
Proof.
  apply val_function_width; left; reflexivity.
Qed.

Lemma val_input_width {K G} (p : func positive K G) x :
  In x (inputs _ _ _ p) -> Pos.size_nat x <= function_width p.
Proof.
  intro Hin; apply val_function_width; unfold function_ids; right; apply in_or_app; left;
    unfold function_vars; apply in_or_app; left; exact Hin.
Qed.

Lemma val_body_var_width {K G} (p : func positive K G) b body x :
  In (b, body) (blocks _ _ _ p) -> In x (val_body_vars body) ->
    Pos.size_nat x <= function_width p.
Proof.
  intros Hin Hvar; apply val_function_width; unfold function_ids; right;
    apply in_or_app; left; unfold function_vars; apply in_or_app; right.
  apply in_flat_map; exists (b, body); split; [exact Hin|exact Hvar].
Qed.

Lemma val_target_width {K G} (p : func positive K G) b body target :
  In (b, body) (blocks _ _ _ p) -> In target (exit_targets (term _ _ _ body)) ->
    Pos.size_nat target <= function_width p.
Proof.
  intros Hin Htarget; apply val_function_width; unfold function_ids; right;
    apply in_or_app; right; apply in_flat_map; exists (b, body); split; [exact Hin|].
  right; exact Htarget.
Qed.

Lemma val_cert_pair_width c b row x y : In (b, row) (fst c) -> In (x, y) row ->
  Pos.size_nat x <= vertex_width (cert_ids c) /\
    Pos.size_nat y <= vertex_width (cert_ids c).
Proof.
  intros Hrow Hpair.
  assert (Hids : forall z, In z [x; y] -> In z (cert_ids c)).
  { intros z Hz; unfold cert_ids; apply in_or_app; left; apply in_flat_map;
      exists (b, row); split; [exact Hrow|].
    right; apply in_flat_map; exists (x, y); split; [exact Hpair|exact Hz]. }
  split; apply val_width_member; apply Hids; cbn; auto.
Qed.

Lemma val_cert_member_width c b row x : In (b, row) (snd c) -> In x row ->
  Pos.size_nat x <= vertex_width (cert_ids c).
Proof.
  intros Hrow Hvar; apply val_width_member; unfold cert_ids; apply in_or_app; right;
    apply in_flat_map; exists (b, row); split; [exact Hrow|right; exact Hvar].
Qed.

Lemma val_selected_find {K G} (bs : list (positive * block positive K G)) seen b :
  find_block b (val_selected seen bs) =
    match trie_get b seen with Some _ => None | None => find_block b bs end.
Proof.
  revert seen; induction bs as [|[a body] rest IH]; intro seen.
  - cbn [val_selected find_block]; destruct (trie_get b seen); reflexivity.
  - cbn [val_selected fst]; destruct (trie_get a seen) as [[]|] eqn:Hseen.
    + rewrite IH; cbn [find_block]; destruct (Pos.eqb b a) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq; subst b; rewrite Hseen; reflexivity.
    + cbn [find_block]; destruct (Pos.eqb b a) eqn:Heq.
      * apply Pos.eqb_eq in Heq; subst b; rewrite Hseen; reflexivity.
      * rewrite IH, PTrie.get_set_other by (apply Pos.eqb_neq; exact Heq); reflexivity.
Qed.

Lemma val_first_find {K G} (bs : list (positive * block positive K G)) b :
  find_block b (first_blocks bs) = find_block b bs.
Proof.
  rewrite val_first_selected, val_selected_find, PTrie.get_empty; reflexivity.
Qed.

Lemma val_row_sizes_lookup {A} : forall (rows : list (positive * list A)) b,
  val_size (val_row_sizes rows) b = length (index_row (val_index rows) b).
Proof.
  intros rows b; unfold val_size, val_row_sizes, index_row; rewrite !val_index_lookup.
  induction rows as [|[key values] rest IH]; cbn [map lookup fst snd]; [reflexivity|].
  destruct (Pos.eqb b key); [reflexivity|exact IH].
Qed.

Lemma val_sum_time2 {A} : forall (f g : A -> nat) (Tf : A -> N) xs c w,
  (forall x, In x xs -> (Tf x <= c * N.of_nat (f x) * w + c * N.of_nat (g x))%N) ->
  (fold_right N.add 0%N (map Tf xs) <=
    c * N.of_nat (fold_right (fun x n => (f x + n)%nat) 0%nat xs) * w +
    c * N.of_nat (fold_right (fun x n => (g x + n)%nat) 0%nat xs))%N.
Proof.
  intros f g Tf xs; induction xs as [|x rest IH]; intros c w Hbound.
  - time_cbn; nia.
  - pose proof (Hbound x ltac:(left; reflexivity)) as Hhead.
    specialize (IH c w ltac:(intros y Hin; apply Hbound; right; exact Hin));
      cbn [map fold_right]; rewrite !Nat2N.inj_add; nia.
Qed.

Lemma val_pos_eqb_right : forall x y,
  (Pos.T_eqb x y <= N.of_nat (Pos.size_nat y))%N.
Proof.
  intros x y; revert x; induction y; intros [x|x|]; time_step.
Qed.

Module ValidateCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (E : TYPE)
    (C : CFG_INDEXED_OPS Q PosKeyCode E) (S : SSA_OPS Q PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) <: VALIDATE_OPS O K G P Q R E C S DG D.
  Definition tables (p s : P.t) (c : cert) : check_tables O.K O.G :=
    CheckTables (val_index (blocks _ _ _ p)) (val_index (blocks _ _ _ s))
      (val_index (fst c)) (val_index (snd c)).

  (** Reject oversized destination rows before any block check scans them repeatedly.
      Canonical live-only rows fit the predecessor's live variables and code definitions. *)
  Definition row_budget (p : P.t) (c : cert) : bool :=
    let env_sizes := val_row_sizes (fst c) in
    let live_sizes := val_row_sizes (snd c) in
    forallb (fun item =>
      let allowance := length (code _ _ _ (snd item)) + val_size env_sizes (fst item) +
        val_size live_sizes (fst item) + 1 in
      forallb (fun target => Nat.leb (val_size env_sizes target) allowance &&
        Nat.leb (val_size live_sizes target) allowance)
        (exit_targets (term _ _ _ (snd item)))) (first_blocks (blocks _ _ _ p)).

  Definition check_entry (p s : P.t) (c : cert) (t : check_tables O.K O.G) : bool :=
    if row_budget p c then
    let rho := index_row (cert_envs t) (entry _ _ _ p) in
    let known := val_set (inputs _ _ _ p) in
    Pos.eqb (entry _ _ _ p) (entry _ _ _ s) &&
    match trie_get (entry _ _ _ p) (source_bodies t),
      trie_get (entry _ _ _ s) (target_bodies t) with
    | Some ib, Some sb =>
      match params _ _ _ ib, params _ _ _ sb with
      | [], [] =>
        val_injective rho &&
        val_args (val_index rho) known (inputs _ _ _ p) (inputs _ _ _ s) &&
        forallb (val_mem known) (index_row (cert_rows t) (entry _ _ _ p))
      | _, _ => false
      end
    | _, _ => false
    end
    else false.

  Fixpoint code_scan (ic sc : list (positive * O.K * list positive))
      (rho : renaming) (forward inverse : ptrie positive) (known : ptrie unit)
      : option renaming :=
    match ic, sc with
    | [], [] => Some rho
    | (x, op, args) :: ir, (y, sop, sargs) :: sr =>
      if K.eqb op sop && val_args forward known args sargs &&
        match trie_get y inverse with Some owner => Pos.eqb x owner | None => true end
      then code_scan ir sr ((x, y) :: rho) (PTrieCode.set x y forward)
        (PTrieCode.set y x inverse) (PTrieCode.set x tt known)
      else None
    | _, _ => None
    end.

  Definition check_code (ic sc : list (positive * O.K * list positive))
      (rho : renaming) (live : list positive) : option renaming :=
    if val_injective rho then
      code_scan ic sc rho (val_index rho) (val_inverse rho) (val_set live)
    else None.

  Definition available_target (rho : ptrie positive) (inverse : ptrie positive)
      (known : ptrie unit) (y : positive) : bool :=
    match trie_get y inverse with
    | Some x => val_mem known x && val_maps rho x y
    | None => false
    end.

  Definition check_target (t : check_tables O.K O.G) (target : positive)
      (rho : renaming) (known : ptrie unit) (args : list positive) : bool :=
    match trie_get target (source_bodies t), trie_get target (target_bodies t) with
    | Some ib, Some sb =>
      match params _ _ _ ib, val_bind_symbols (params _ _ _ sb) args Empty with
      | [], Some bound =>
        let forward := val_index rho in
        let inverse := val_inverse rho in
        let next := val_index (index_row (cert_envs t) target) in
        forallb (available_target forward inverse known) args &&
        forallb (fun x => val_mem known x &&
          match trie_get x next, trie_get x forward with
          | Some y, Some z => Pos.eqb (val_symbol bound y) z
          | _, _ => false
          end) (index_row (cert_rows t) target)
      | _, _ => false
      end
    | _, _ => false
    end.

  Definition check_arm (t : check_tables O.K O.G) (target : positive)
      (rho : renaming) (known : ptrie unit) (ie se : exit positive O.G)
      (choice : bool) : bool :=
    match edge_choice ie choice, edge_choice se choice with
    | Some (u, []), Some (v, args) =>
      if Pos.eqb u target then Pos.eqb u v && check_target t target rho known args
      else true
    | None, None => true
    | _, _ => false
    end.

  Definition check_edge (t : check_tables O.K O.G) (b target : positive)
      (rho : renaming) : bool :=
    match trie_get b (source_bodies t), trie_get b (target_bodies t) with
    | Some ib, Some sb =>
      let known := val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
        index_row (cert_rows t) b) in
      check_arm t target rho known (term _ _ _ ib) (term _ _ _ sb) true &&
      check_arm t target rho known (term _ _ _ ib) (term _ _ _ sb) false
    | _, _ => false
    end.

  Definition check_exit (t : check_tables O.K O.G) (b : positive)
      (ib sb : block positive O.K O.G) (rho : renaming) : bool :=
    let forward := val_index rho in
    let known := val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
      index_row (cert_rows t) b) in
    match term _ _ _ ib, term _ _ _ sb with
    | Return xs, Return ys => val_args forward known xs ys
    | Jump u [], Jump v _ => Pos.eqb u v && check_edge t b u rho
    | Branch g xs u [] v [], Branch h ys su _ sv _ =>
      G.eqb g h && val_args forward known xs ys && Pos.eqb u su && Pos.eqb v sv &&
        check_edge t b u rho && check_edge t b v rho
    | _, _ => false
    end.

  Definition check_block (t : check_tables O.K O.G) (b : positive) : bool :=
    match trie_get b (source_bodies t), trie_get b (target_bodies t) with
    | Some ib, Some sb =>
      match params _ _ _ ib with
      | [] =>
        match check_code (code _ _ _ ib) (code _ _ _ sb)
          (index_row (cert_envs t) b) (index_row (cert_rows t) b) with
        | Some rho => check_exit t b ib sb rho
        | None => false
        end
      | _ => false
      end
    | _, _ => false
    end.

  Definition check (p s : P.t) (c : cert) : bool :=
    let t := tables p s c in
    if check_entry p s c t then
      forallb (fun item => check_block t (fst item)) (first_blocks (blocks _ _ _ p))
    else false.

  Definition dom_cert (s : P.t) : ptrie positive * list positive :=
    D.build (DG.prepare (cfg_graph (C.nodes (R.prepare s))
      (C.edges (R.prepare s)) (C.src (R.prepare s)) (C.dst (R.prepare s)))) (entry _ _ _ s).

  Definition ssa_edge_shape (bodies : ptrie (block positive O.K O.G)) target args : bool :=
    match trie_get target bodies with
    | Some body => val_same_length args (params _ _ _ body)
    | None => false
    end.

  Definition ssa_exit_shape (bodies : ptrie (block positive O.K O.G))
      (e : exit positive O.G) : bool :=
    match e with
    | Jump target args => ssa_edge_shape bodies target args
    | Branch _ _ yes yes_args no no_args =>
      ssa_edge_shape bodies yes yes_args && ssa_edge_shape bodies no no_args
    | Return _ => true
    end.

  Definition ssa_precheck (s : P.t) : bool :=
    let bs := blocks _ _ _ s in
    let bodies := val_index bs in
    val_unique (map fst bs) Empty &&
    val_unique (inputs _ _ _ s ++ flat_map (fun item => block_defs (snd item)) bs) Empty &&
    match trie_get (entry _ _ _ s) bodies with Some _ => true | None => false end &&
    forallb (fun item => ssa_exit_shape bodies (term _ _ _ (snd item))) bs.

  Definition ssa_cross (tree : domtree) (homes : ptrie positive) (b x : positive) : bool :=
    match trie_get x homes with
    | Some d => negb (Pos.eqb d b) && D.dominates_b tree d b
    | None => false
    end.

  Fixpoint ssa_local (tree : domtree) (homes : ptrie positive) (b : positive)
      (known : ptrie unit) (ic : list (positive * O.K * list positive))
      (out : list positive) : bool :=
    match ic with
    | [] => forallb (fun x => val_mem known x || ssa_cross tree homes b x) out
    | (dst, _, args) :: rest =>
      if forallb (fun x => val_mem known x || ssa_cross tree homes b x) args then
        ssa_local tree homes b (PTrieCode.set dst tt known) rest out
      else false
    end.

  Definition check_ssa (s : P.t) : bool :=
    if ssa_precheck s then
      let g := DG.prepare (cfg_graph (C.nodes (R.prepare s))
        (C.edges (R.prepare s)) (C.src (R.prepare s)) (C.dst (R.prepare s))) in
      let '(m, order) := dom_cert s in
      if D.check g (entry _ _ _ s) m order then
        let tree := D.tree g (entry _ _ _ s) m order in
        let homes := val_index (val_home_rows (blocks _ _ _ s)) in
        let inputs := val_set (inputs _ _ _ s) in
        forallb (fun item => ssa_local tree homes (fst item)
          (val_add (params _ _ _ (snd item)) inputs) (code _ _ _ (snd item))
          (exit_uses (term _ _ _ (snd item)))) (blocks _ _ _ s)
      else false
    else false.
End ValidateCode.

Module Validate (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (E : TYPE)
    (C : CFG Q PosKey E) (S : SSA Q PosKey E C PosKey K G)
    (DG : DIGRAPH) (D : DOM) (B : LANG_SSA_LINK O K G Q R E C S)
    <: VALIDATE O K G P Q R E C S DG D B.
  Include ValidateCode O K G P Q R E C S DG D.
  Include VALIDATE_SPEC O K G P Q R E C S DG D.

  Lemma tables_agree : forall p s c b,
    trie_get b (source_bodies (tables p s c)) = find_block b (blocks _ _ _ p) /\
    trie_get b (target_bodies (tables p s c)) = find_block b (blocks _ _ _ s) /\
    trie_get b (cert_envs (tables p s c)) = lookup b (fst c) /\
    index_row (cert_rows (tables p s c)) b = cert_live c b.
  Proof.
    intros p s c b; unfold tables; cbn [source_bodies target_bodies cert_envs cert_rows].
    rewrite !val_index_block, val_index_lookup; repeat split.
    unfold index_row, cert_live; rewrite val_index_lookup; reflexivity.
  Qed.

  Lemma check_checks : forall p s c, check p s c = true ->
    check_entry p s c (tables p s c) = true /\ forall b body,
      In (b, body) (blocks _ _ _ p) -> check_block (tables p s c) b = true.
  Proof.
    intros p s c Hcheck; unfold check in Hcheck.
    destruct (check_entry p s c (tables p s c)) eqn:Hentry; [|discriminate].
    rename Hcheck into Hblocks.
    split; [reflexivity|]; intros b body Hin.
    assert (Hid : In b (map fst (first_blocks (blocks _ _ _ p)))).
    { apply val_first_blocks_ids; apply in_map_iff; exists (b, body); auto. }
    apply in_map_iff in Hid as [item [Heq Hitem]]; rewrite forallb_forall in Hblocks.
    specialize (Hblocks item Hitem); rewrite Heq in Hblocks; exact Hblocks.
  Qed.

  Lemma check_block_found : forall p s c b ib,
    check p s c = true -> find_block b (blocks _ _ _ p) = Some ib ->
    check_block (tables p s c) b = true.
  Proof.
    intros p s c b ib Hcheck Hfind; apply (proj2 (check_checks p s c Hcheck) b ib).
    apply val_lookup_in; rewrite <- val_index_lookup, val_index_block; exact Hfind.
  Qed.

  (** Reachable entries carry actual values for every variable required by the certificate.
      This rules out premature failure while the target evaluates its edge arguments. *)
  Definition state_ready (p s : P.t) (c : cert)
      (ss si : machine_state O.C) : Prop :=
    let '(bs, actuals_s, es) := ss in
    let '(bi, actuals_i, ei) := si in
    bs = bi /\
    match find_block bs (blocks _ _ _ s), find_block bi (blocks _ _ _ p) with
    | Some sb, Some ib =>
      exists entered_s entered_i,
        bind_vars (params _ _ _ sb) actuals_s es = Some entered_s /\
        bind_vars (params _ _ _ ib) actuals_i ei = Some entered_i /\
        val_agrees (index_row (cert_envs (tables p s c)) bi)
          (index_row (cert_rows (tables p s c)) bi) entered_s entered_i /\
        val_defined (index_row (cert_rows (tables p s c)) bi) entered_i
    | _, _ => False
    end.

  Definition outcome_ready p s c (os oi : machine_state O.C + result O.C) : Prop :=
    match os, oi with
    | inl ss, inl si => state_ready p s c ss si
    | inr rs, inr ri => rs = ri
    | _, _ => False
    end.

  Lemma available_target_defined : forall rho live (ss si : env O.C) args,
    forallb (available_target (val_index rho) (val_inverse rho) (val_set live)) args = true ->
    val_agrees rho live ss si -> val_defined live si -> val_defined args ss.
  Proof.
    intros rho live ss si args Hcheck Hagree Hdefined y Hin.
    rewrite forallb_forall in Hcheck; specialize (Hcheck y Hin).
    unfold available_target in Hcheck; destruct (trie_get y (val_inverse rho)) as [x|];
      [|discriminate].
    apply andb_true_iff in Hcheck as [Hknown Hmap].
    apply val_set_member in Hknown; apply val_maps_spec in Hmap;
      rewrite val_index_lookup in Hmap.
    destruct (Hagree x Hknown) as [z [Hz Hvalue]].
    rewrite Hmap in Hz; injection Hz as Heq; subst z.
    destruct (Hdefined x Hknown) as [value Hsource].
    exists value; rewrite Hvalue; exact Hsource.
  Qed.

  Lemma check_target_ready : forall p s c target rho live args ss si,
    check_target (tables p s c) target rho (val_set live) args = true ->
    val_agrees rho live ss si -> val_defined live si ->
    exists passed, read_vars ss args = Some passed /\
      state_ready p s c (target, passed, ss) (target, [], si).
  Proof.
    intros p s c target rho live args ss si Hcheck Hagree Hdefined.
    unfold check_target in Hcheck.
    destruct (trie_get target (source_bodies (tables p s c))) as [ib|] eqn:Hib;
      [|discriminate].
    destruct (trie_get target (target_bodies (tables p s c))) as [sb|] eqn:Hsb;
      [|discriminate].
    destruct (params _ _ _ ib) as [|parameter parameters] eqn:Hip; [|discriminate].
    destruct (val_bind_symbols (params _ _ _ sb) args Empty) as [bound|] eqn:Hbound;
      [|discriminate].
    apply andb_true_iff in Hcheck as [Hargs Hlive].
    destruct (val_read_defined args ss
      (available_target_defined rho live ss si args Hargs Hagree Hdefined)) as [passed Hread].
    destruct (val_bind_symbols_sound (params _ _ _ sb) args Empty bound ss ss passed
      Hbound Hread) as [entered [Hbind Hvalues]].
    { intro y; unfold val_symbol; rewrite PTrie.get_empty; reflexivity. }
    exists passed; split; [exact Hread|].
    unfold state_ready; split; [reflexivity|].
    pose proof (tables_agree p s c target) as [Hsource [Htarget _]].
    rewrite Hsource in Hib; rewrite Htarget in Hsb; rewrite Hib, Hsb.
    exists entered, si; rewrite Hip; split; [exact Hbind|]; split; [reflexivity|].
    rewrite forallb_forall in Hlive; split.
    - intros x Hin; specialize (Hlive x Hin).
      apply andb_true_iff in Hlive as [Hknown Hmap]; apply val_set_member in Hknown.
      rewrite !val_index_lookup in Hmap.
      destruct (lookup x (index_row (cert_envs (tables p s c)) target)) as [y|] eqn:Hnext;
        [|discriminate].
      destruct (lookup x rho) as [z|] eqn:Hcurrent; [|discriminate].
      apply Pos.eqb_eq in Hmap; exists y; split; [reflexivity|].
      destruct (Hagree x Hknown) as [v [Hv Heq]].
      rewrite Hcurrent in Hv; injection Hv as Heqv; subst v.
      rewrite Hvalues, Hmap; exact Heq.
    - intros x Hin; specialize (Hlive x Hin).
      apply andb_true_iff in Hlive as [Hknown _]; apply val_set_member in Hknown.
      apply Hdefined; exact Hknown.
  Qed.

  (** A successful instruction scan preserves the indexed renaming relation. *)
  Lemma code_scan_sim : forall ic sc rho inverse live rho' ss si,
    val_inverse_ok rho inverse ->
    code_scan ic sc rho (val_index rho) inverse (val_set live) = Some rho' ->
    val_agrees rho live ss si ->
    match exec_code O.eval sc ss, exec_code O.eval ic si with
    | None, None => True
    | Some ss', Some si' =>
      val_agrees rho' (map (fun i => fst (fst i)) ic ++ live) ss' si'
    | _, _ => False
    end.
  Proof.
    induction ic as [|[[x op] args] ir IH];
      intros sc rho inverse live rho' ss si Hinv Hcheck Hagree;
      destruct sc as [|[[y sop] sargs] sr]; cbn [code_scan] in Hcheck;
      try discriminate.
    - injection Hcheck as Heq; subst rho'; exact Hagree.
    - destruct (K.eqb op sop && val_args (val_index rho) (val_set live) args sargs &&
        match trie_get y inverse with Some owner => Pos.eqb x owner | None => true end)
        eqn:Hhead; [|discriminate].
      apply andb_true_iff in Hhead as [Hfirst Hfresh].
      apply andb_true_iff in Hfirst as [Hop Hargs].
      destruct (K.eqb_spec op sop) as [Heq|Hneq]; [subst sop|discriminate].
      pose proof (val_args_read args sargs rho live ss si Hargs Hagree) as Hread.
      cbn [exec_code]; rewrite Hread.
      destruct (read_vars si args) as [values|]; [|exact I].
      destruct (O.eval op values) as [value|]; [|exact I].
      pose proof (val_inverse_extend rho inverse x y Hinv Hfresh) as Hnextinv.
      pose proof (val_agrees_extend rho inverse live x y value ss si Hinv Hagree Hfresh)
        as Hnextagree.
      specialize (IH sr ((x, y) :: rho) (PTrieCode.set y x inverse) (x :: live)
        rho' ((y, value) :: ss) ((x, value) :: si) Hnextinv Hcheck Hnextagree).
      destruct (exec_code O.eval sr ((y, value) :: ss)) as [ss'|];
        destruct (exec_code O.eval ir ((x, value) :: si)) as [si'|];
        try contradiction; [|exact I].
      intros z Hin; apply IH; cbn in Hin |- *.
      rewrite in_app_iff in Hin |- *; cbn; tauto.
  Qed.

  (** The public code checker establishes the instruction simulation without assumptions
      about the concrete operator semantics. *)
  Lemma check_code_sim : forall ic sc rho live rho' ss si,
    check_code ic sc rho live = Some rho' -> val_agrees rho live ss si ->
    match exec_code O.eval sc ss, exec_code O.eval ic si with
    | None, None => True
    | Some ss', Some si' =>
      val_agrees rho' (map (fun i => fst (fst i)) ic ++ live) ss' si'
    | _, _ => False
    end.
  Proof.
    intros ic sc rho live rho' ss si Hcheck Hagree; unfold check_code in Hcheck.
    destruct (val_injective rho) eqn:Hinj; [|discriminate].
    eapply code_scan_sim; [apply val_injective_sound; exact Hinj|exact Hcheck|exact Hagree].
  Qed.

  Lemma check_input_arity : forall p s c, check p s c = true ->
    length (inputs _ _ _ s) = length (inputs _ _ _ p).
  Proof.
    intros p s c Hcheck; pose proof (proj1 (check_checks p s c Hcheck)) as Hentry.
    unfold check_entry in Hentry; destruct (row_budget p c); [|discriminate].
    apply andb_true_iff in Hentry as [_ Hentry].
    destruct (trie_get (entry _ _ _ p) (source_bodies (tables p s c))) as [ib|];
      [|discriminate].
    destruct (trie_get (entry _ _ _ s) (target_bodies (tables p s c))) as [sb|];
      [|discriminate].
    destruct (params _ _ _ ib); [|discriminate]; destruct (params _ _ _ sb); [|discriminate].
    apply andb_true_iff in Hentry as [Hfirst _]; apply andb_true_iff in Hfirst as [_ Hargs].
    symmetry; eapply val_args_length; exact Hargs.
  Qed.

  Lemma entry_ready : forall p s c ins si,
    check p s c = true -> bind_vars (inputs _ _ _ p) ins [] = Some si ->
    exists ss, bind_vars (inputs _ _ _ s) ins [] = Some ss /\
      state_ready p s c (entry _ _ _ s, [], ss) (entry _ _ _ p, [], si).
  Proof.
    intros p s c ins si Hcheck Hbind.
    pose proof (proj1 (check_checks p s c Hcheck)) as Hentry.
    unfold check_entry in Hentry; destruct (row_budget p c); [|discriminate].
    apply andb_true_iff in Hentry as [Hid Hentry].
    apply Pos.eqb_eq in Hid.
    destruct (trie_get (entry _ _ _ p) (source_bodies (tables p s c))) as [ib|] eqn:Hib;
      [|discriminate].
    destruct (trie_get (entry _ _ _ s) (target_bodies (tables p s c))) as [sb|] eqn:Hsb;
      [|discriminate].
    destruct (params _ _ _ ib) as [|ip ips] eqn:Hip; [|discriminate].
    destruct (params _ _ _ sb) as [|sp sps] eqn:Hsp; [|discriminate].
    apply andb_true_iff in Hentry as [Hfirst Hlive].
    apply andb_true_iff in Hfirst as [Hinj Hargs].
    pose proof (val_injective_sound _ Hinj) as Hinverse.
    destruct (val_bind_related (inputs _ _ _ p) (inputs _ _ _ s) ins
      (index_row (cert_envs (tables p s c)) (entry _ _ _ p))
      (val_set (inputs _ _ _ p)) _ [] [] si Hargs Hinverse) as [ss [Hss Hrelated]].
    { intros x y _; reflexivity. }
    { exact Hbind. }
    exists ss; split; [exact Hss|]; unfold state_ready; split; [symmetry; exact Hid|].
    rewrite (proj1 (tables_agree p s c (entry _ _ _ p))) in Hib.
    rewrite (proj1 (proj2 (tables_agree p s c (entry _ _ _ s)))) in Hsb.
    rewrite Hib, Hsb; exists ss, si; rewrite Hip, Hsp; cbn [bind_vars].
    split; [reflexivity|]; split; [reflexivity|]; split.
    - intros x Hin; rewrite forallb_forall in Hlive; specialize (Hlive x Hin).
      apply val_set_member in Hlive.
      destruct (val_args_covers _ _ _ _ x Hargs Hlive) as [y Hmap].
      exists y; split; [exact Hmap|]; apply Hrelated; exact Hmap.
    - pose proof (val_bind_defined (inputs _ _ _ p) ins [] [] si Hbind) as Hdefined.
      assert (Hempty : @val_defined O.C [] []).
      { intros x Hin; contradiction. }
      specialize (Hdefined Hempty); rewrite app_nil_r in Hdefined.
      intros x Hin; apply Hdefined; rewrite forallb_forall in Hlive.
      apply val_set_member; apply Hlive; exact Hin.
  Qed.

  Lemma check_arm_target : forall t target rho known ie se choice args,
    check_arm t target rho known ie se choice = true ->
    edge_choice ie choice = Some (target, []) ->
    edge_choice se choice = Some (target, args) ->
    check_target t target rho known args = true.
  Proof.
    intros t target rho known ie se choice args Hcheck Hie Hse.
    unfold check_arm in Hcheck; rewrite Hie, Hse, !Pos.eqb_refl in Hcheck; exact Hcheck.
  Qed.

  Lemma check_edge_target : forall p s c b target rho ib sb choice args,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    check_edge (tables p s c) b target rho = true ->
    edge_choice (term _ _ _ ib) choice = Some (target, []) ->
    edge_choice (term _ _ _ sb) choice = Some (target, args) ->
    check_target (tables p s c) target rho
      (val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
        index_row (cert_rows (tables p s c)) b)) args = true.
  Proof.
    intros p s c b target rho ib sb choice args Hib Hsb Hcheck Hie Hse.
    unfold check_edge in Hcheck.
    pose proof (tables_agree p s c b) as [Hsource [Htarget _]].
    rewrite Hsource, Htarget, Hib, Hsb in Hcheck.
    apply andb_true_iff in Hcheck as [Hyes Hno].
    destruct choice.
    - exact (check_arm_target _ _ _ _ _ _ true _ Hyes Hie Hse).
    - exact (check_arm_target _ _ _ _ _ _ false _ Hno Hie Hse).
  Qed.

  Definition finish (e : exit positive O.G) (s : env O.C)
      : machine_state O.C + result O.C :=
    match e with
    | Jump next actuals =>
      match read_vars s actuals with
      | Some values => inl (next, values, s)
      | None => inr Wrong
      end
    | Branch guard operands yes yes_args no no_args =>
      match read_vars s operands with
      | None => inr Wrong
      | Some values =>
        match O.test guard values with
        | None => inr Wrong
        | Some choice =>
          let next := if choice then yes else no in
          let actuals := if choice then yes_args else no_args in
          match read_vars s actuals with
          | Some passed => inl (next, passed, s)
          | None => inr Wrong
          end
        end
      end
    | Return values =>
      match read_vars s values with
      | Some returned => inr (Returned returned)
      | None => inr Wrong
      end
    end.

  Lemma check_exit_ready : forall p s c b ib sb rho ss si,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    check_exit (tables p s c) b ib sb rho = true ->
    val_agrees rho (map (fun i => fst (fst i)) (code _ _ _ ib) ++
      index_row (cert_rows (tables p s c)) b) ss si ->
    val_defined (map (fun i => fst (fst i)) (code _ _ _ ib) ++
      index_row (cert_rows (tables p s c)) b) si ->
    outcome_ready p s c (finish (term _ _ _ sb) ss) (finish (term _ _ _ ib) si).
  Proof.
    intros p s c b ib sb rho ss si Hib Hsb Hcheck Hagree Hdefined.
    unfold check_exit in Hcheck.
    destruct (term _ _ _ ib) as [u ia|g xs u ua v va|xs] eqn:Hie;
      destruct (term _ _ _ sb) as [su sa|h ys su usa sv vsa|ys] eqn:Hse;
      try discriminate.
    all: try (destruct ia as [|ix ir]; [|discriminate]).
    all: try (destruct ua as [|ux ur]; [|discriminate]).
    all: try (destruct va as [|vx vr]; [|discriminate]).
    all: try discriminate.
    - apply andb_true_iff in Hcheck as [Hid Hedge]; apply Pos.eqb_eq in Hid; subst su.
      assert (Htarget : check_target (tables p s c) u rho
        (val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
          index_row (cert_rows (tables p s c)) b)) sa = true).
      { eapply check_edge_target with (choice := true); [exact Hib|exact Hsb|exact Hedge| |];
          rewrite ?Hie, ?Hse; reflexivity. }
      destruct (check_target_ready p s c u rho _ sa ss si Htarget Hagree Hdefined)
        as [passed [Hread Hready]].
      cbn [finish]; rewrite Hread; exact Hready.
    - repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[[Hguard Hargs] Hyes] Hno] Hedgeyes] Hedgeno].
      destruct (G.eqb_spec g h) as [Heq|Hneq]; [subst h|discriminate].
      apply Pos.eqb_eq in Hyes; apply Pos.eqb_eq in Hno; subst su sv.
      pose proof (val_args_read xs ys rho _ ss si Hargs Hagree) as Hread.
      cbn [finish]; rewrite Hread.
      destruct (read_vars si xs) as [values|]; [|reflexivity].
      destruct (O.test g values) as [choice|]; [|reflexivity]; destruct choice.
      + assert (Htarget : check_target (tables p s c) u rho
          (val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
            index_row (cert_rows (tables p s c)) b)) usa = true).
        { eapply check_edge_target with (choice := true);
            [exact Hib|exact Hsb|exact Hedgeyes| |]; rewrite ?Hie, ?Hse; reflexivity. }
        destruct (check_target_ready p s c u rho _ usa ss si Htarget Hagree Hdefined)
          as [passed [Hpassed Hready]].
        rewrite Hpassed; exact Hready.
      + assert (Htarget : check_target (tables p s c) v rho
          (val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
            index_row (cert_rows (tables p s c)) b)) vsa = true).
        { eapply check_edge_target with (choice := false);
            [exact Hib|exact Hsb|exact Hedgeno| |]; rewrite ?Hie, ?Hse; reflexivity. }
        destruct (check_target_ready p s c v rho _ vsa ss si Htarget Hagree Hdefined)
          as [passed [Hpassed Hready]].
        rewrite Hpassed; exact Hready.
    - pose proof (val_args_read xs ys rho _ ss si Hcheck Hagree) as Hread.
      cbn [finish]; rewrite Hread; destruct (read_vars si xs); reflexivity.
  Qed.

  Lemma step_ready : forall p s c ss si,
    check p s c = true -> state_ready p s c ss si ->
    outcome_ready p s c (step O.eval O.test s ss) (step O.eval O.test p si).
  Proof.
    intros p s c [[bs actuals_s] es] [[bi actuals_i] ei] Hcheck Hready.
    destruct Hready as [Heq Hready]; cbn in Heq; subst bs.
    cbn in Hready.
    destruct (find_block bi (blocks _ _ _ s)) as [sb|] eqn:Hsb; [|contradiction].
    destruct (find_block bi (blocks _ _ _ p)) as [ib|] eqn:Hib; [|contradiction].
    destruct Hready as [entered_s [entered_i [Hbinds [Hbindi [Hagree Hdefined]]]]].
    pose proof (check_block_found p s c bi ib Hcheck Hib) as Hblock.
    unfold check_block in Hblock.
    pose proof (tables_agree p s c bi) as [Hsource [Htarget _]].
    rewrite Hsource, Htarget, Hib, Hsb in Hblock.
    destruct (params _ _ _ ib) as [|ip ips] eqn:Hip; [|discriminate].
    destruct (check_code (code _ _ _ ib) (code _ _ _ sb)
      (index_row (cert_envs (tables p s c)) bi)
      (index_row (cert_rows (tables p s c)) bi)) as [rho|] eqn:Hcode; [|discriminate].
    pose proof (check_code_sim _ _ _ _ rho entered_s entered_i Hcode Hagree) as Hsim.
    unfold step; rewrite Hsb, Hib, Hbinds, Hip, Hbindi.
    destruct (exec_code O.eval (code _ _ _ sb) entered_s) as [finished_s|] eqn:Hexecs;
      destruct (exec_code O.eval (code _ _ _ ib) entered_i) as [finished_i|] eqn:Hexeci;
      try contradiction; [|reflexivity].
    change (outcome_ready p s c (finish (term _ _ _ sb) finished_s)
      (finish (term _ _ _ ib) finished_i)).
    eapply check_exit_ready; [exact Hib|exact Hsb|exact Hblock|exact Hsim|].
    eapply val_exec_defined; [exact Hexeci|exact Hdefined].
  Qed.

  Lemma loop_ready : forall p s c n ss si,
    check p s c = true -> state_ready p s c ss si ->
    outcome_ready p s c (loop_fuel (step O.eval O.test s) n ss)
      (loop_fuel (step O.eval O.test p) n si).
  Proof.
    intros p s c n; induction n as [|n IH]; intros ss si Hcheck Hready.
    - exact Hready.
    - pose proof (step_ready p s c ss si Hcheck Hready) as Hstep.
      cbn [loop_fuel].
      destruct (step O.eval O.test s ss) as [ss'|rs];
        destruct (step O.eval O.test p si) as [si'|ri]; try contradiction.
      + apply IH; [exact Hcheck|exact Hstep].
      + exact Hstep.
  Qed.

  Lemma check_sound : forall p s c, imp_form p -> check p s c = true ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof.
    intros p s c _ Hcheck n ins; unfold run_with.
    destruct (bind_vars (inputs _ _ _ p) ins []) as [si|] eqn:Hbindi.
    - destruct (entry_ready p s c ins si Hcheck Hbindi) as [ss [Hbinds Hready]].
      rewrite Hbinds; pose proof (loop_ready p s c n _ _ Hcheck Hready) as Hloop.
      destruct (loop_fuel (step O.eval O.test s) n (entry _ _ _ s, [], ss)) as [ss'|rs];
        destruct (loop_fuel (step O.eval O.test p) n (entry _ _ _ p, [], si)) as [si'|ri];
        try contradiction; [reflexivity|exact Hloop].
    - destruct (bind_vars (inputs _ _ _ s) ins []) as [ss|] eqn:Hbinds; [|reflexivity].
      pose proof (val_bind_length_of _ _ _ _ Hbinds) as Hlength.
      rewrite (check_input_arity p s c Hcheck) in Hlength.
      destruct (val_bind_length (inputs _ _ _ p) ins [] Hlength) as [si Hbind].
      rewrite Hbindi in Hbind; discriminate.
  Qed.

  Lemma ssa_edge_shape_sound : forall s target args,
    ssa_edge_shape (val_index (blocks _ _ _ s)) target args = true ->
    edge_shape s target args.
  Proof.
    intros s target args Hcheck; unfold ssa_edge_shape in Hcheck;
      rewrite val_index_block in Hcheck.
    destruct (find_block target (blocks _ _ _ s)) as [body|] eqn:Hfind; [|discriminate].
    exists body; split.
    - apply val_lookup_in; rewrite <- val_index_lookup, val_index_block; exact Hfind.
    - apply val_same_length_sound; exact Hcheck.
  Qed.

  Lemma ssa_exit_shape_sound : forall s e,
    ssa_exit_shape (val_index (blocks _ _ _ s)) e = true -> exit_shape s e.
  Proof.
    intros s e; destruct e; cbn [ssa_exit_shape exit_shape]; intro Hcheck.
    - apply ssa_edge_shape_sound; exact Hcheck.
    - apply andb_true_iff in Hcheck as [Hyes Hno]; split;
        apply ssa_edge_shape_sound; assumption.
    - exact I.
  Qed.

  Lemma ssa_precheck_sound : forall s, ssa_precheck s = true ->
    NoDup (map fst (blocks _ _ _ s)) /\
    NoDup (inputs _ _ _ s ++ concat (map (fun item => block_defs (snd item))
      (blocks _ _ _ s))) /\
    (exists body, In (entry _ _ _ s, body) (blocks _ _ _ s)) /\
    forall id body, In (id, body) (blocks _ _ _ s) -> exit_shape s (term _ _ _ body).
  Proof.
    intros s Hcheck; unfold ssa_precheck in Hcheck; repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[[Hids Hdefs] Hentry] Hshapes].
    split; [apply (proj1 (val_unique_sound _ _ Hids))|].
    split.
    - pose proof (proj1 (val_unique_sound _ _ Hdefs)) as Hnd.
      rewrite flat_map_concat_map in Hnd; exact Hnd.
    - split.
      + rewrite val_index_block in Hentry.
        destruct (find_block (entry _ _ _ s) (blocks _ _ _ s)) as [body|] eqn:Hfind;
          [|discriminate].
        exists body; apply val_lookup_in; rewrite <- val_index_lookup, val_index_block;
          exact Hfind.
      + intros id body Hin; rewrite forallb_forall in Hshapes.
        apply ssa_exit_shape_sound; exact (Hshapes (id, body) Hin).
  Qed.

  Lemma ssa_targets_listed : forall s : P.t,
    (forall id body, In (id, body) (blocks _ _ _ s) -> exit_shape s (term _ _ _ body)) ->
    targets_listed s.
  Proof.
    intros s Hshapes id body target Hin Htarget; specialize (Hshapes id body Hin).
    destruct (term _ _ _ body) as [u args|g xs u ua v va|xs];
      cbn [exit_shape exit_targets] in *; try contradiction.
    - destruct Htarget as [Heq|Hfalse]; [subst target|contradiction].
      destruct Hshapes as [dest [Hdest _]]; apply in_map_iff; exists (u, dest); auto.
    - destruct Hshapes as [Hyes Hno]; destruct Htarget as [Heq|[Heq|Hfalse]];
        try contradiction; subst target.
      + destruct Hyes as [dest [Hdest _]]; apply in_map_iff; exists (u, dest); auto.
      + destruct Hno as [dest [Hdest _]]; apply in_map_iff; exists (v, dest); auto.
  Qed.

  Lemma checked_dominance : forall s m order d b,
    NoDup (map fst (blocks _ _ _ s)) -> targets_listed s ->
    D.check (graph s) (entry _ _ _ s) m order = true ->
    D.dominates_b (D.tree (graph s) (entry _ _ _ s) m order) d b = true ->
    Lang.dominates s d b.
  Proof.
    intros s m order d b Hids Htargets Hchecked Hquery route Hpath.
    pose proof (proj2 (B.paths_agree s (entry _ _ _ s) route b Hids Htargets) Hpath)
      as Hpresent.
    assert (Hgraphpath : Spec.path (base (graph s)) (entry _ _ _ s) route b).
    { unfold graph; rewrite DG.prepare_base; apply val_cfg_graph_path; exact Hpresent. }
    assert (Hreach : reach (base (graph s)) [entry _ _ _ s] b).
    { exists (entry _ _ _ s), route; split; [left; reflexivity|exact Hgraphpath]. }
    destruct (D.dominates_b_spec (graph s) (entry _ _ _ s) m order d b Hchecked Hreach)
      as [Hdom|Hnot]; [apply Hdom; exact Hgraphpath|discriminate].
  Qed.

  Lemma ssa_local_sound : forall tree homes b ic out known,
    ssa_local tree homes b known ic out = true -> forall x i, val_use ic out x i ->
    val_mem known x = true \/
    (exists j op args, j < i /\ nth_error ic j = Some (x, op, args)) \/
    ssa_cross tree homes b x = true.
  Proof.
    intros tree homes b ic; induction ic as [|[[dst op] args] rest IH];
      intros out known Hcheck x i Huse.
    - cbn [ssa_local] in Hcheck; rewrite forallb_forall in Hcheck.
      destruct Huse as [[k [ys [v [Hnth _]]]]|[Hi Hin]].
      + destruct i; discriminate.
      + specialize (Hcheck x Hin); apply orb_true_iff in Hcheck; tauto.
    - cbn [ssa_local] in Hcheck.
      destruct (forallb (fun x => val_mem known x || ssa_cross tree homes b x) args)
        eqn:Hargs; [|discriminate].
      destruct i as [|i].
      + destruct Huse as [[k [ys [v [Hnth Hin]]]]|[Hi _]]; [|cbn in Hi; lia].
        cbn in Hnth; injection Hnth as Hv Hk Hys; subst v k ys.
        rewrite forallb_forall in Hargs; specialize (Hargs x Hin);
          apply orb_true_iff in Hargs; tauto.
      + assert (Htail : val_use rest out x i).
        { destruct Huse as [[k [ys [v [Hnth Hin]]]]|[Hi Hin]].
          - left; exists k, ys, v; exact (conj Hnth Hin).
          - right; split; [cbn in Hi; lia|exact Hin]. }
        destruct (IH out (PTrieCode.set dst tt known) Hcheck x i Htail)
          as [Hknown|[[j [k [ys [Hlt Hnth]]]]|Hcross]].
        * apply val_mem_set in Hknown; destruct Hknown as [Heq|Hknown].
          -- subst x; right; left; exists 0, op, args; split; [lia|reflexivity].
          -- left; exact Hknown.
        * right; left; exists (S j), k, ys; split; [lia|exact Hnth].
        * right; right; exact Hcross.
  Qed.

  Lemma check_ssa_sound : forall s, check_ssa s = true -> ssa_wf s.
  Proof.
    intros s Hcheck; unfold check_ssa in Hcheck.
    destruct (ssa_precheck s) eqn:Hpre; [|discriminate]; fold (graph s) in Hcheck.
    destruct (dom_cert s) as [m order] eqn:Hcert.
    destruct (D.check (graph s) (entry _ _ _ s) m order) eqn:Hdom; [|discriminate].
    destruct (ssa_precheck_sound s Hpre) as [Hids [Hdefs [Hentry Hshapes]]].
    split; [exact Hids|]; split; [exact Hdefs|]; split; [|auto].
    intros id body x i Hin Huse; rewrite forallb_forall in Hcheck;
      specialize (Hcheck (id, body) Hin).
    destruct (ssa_local_sound _ _ id (code _ _ _ body) (exit_uses (term _ _ _ body))
      _ Hcheck x i Huse) as [Hknown|[Hbefore|Hcross]].
    - apply val_add_member in Hknown; destruct Hknown as [Hparam|Hinput].
      + right; left; left; exact Hparam.
      + left; apply val_set_member; exact Hinput.
    - right; left; right; exact Hbefore.
    - unfold ssa_cross in Hcross.
      destruct (trie_get x (val_index (val_home_rows (blocks _ _ _ s)))) as [d|] eqn:Hhome;
        [|discriminate].
      apply andb_true_iff in Hcross as [Hneq Hquery].
      apply negb_true_iff in Hneq; apply Pos.eqb_neq in Hneq.
      destruct (val_home_source _ x d Hhome) as [def_body [Hlisted Hdefinition]].
      right; right; exists d, def_body; split; [exact Hlisted|]; split; [exact Hneq|];
        split; [exact Hdefinition|].
      eapply checked_dominance; [exact Hids|apply ssa_targets_listed; exact Hshapes|
        exact Hdom|exact Hquery].
  Qed.
  Lemma check_core_ssa_sound : forall s, check_ssa s = true -> S.wf (R.prepare s).
  Proof.
    intros s Hcheck; apply B.wf_from_lang; apply check_ssa_sound; exact Hcheck.
  Qed.
End Validate.

Module ValidateT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (E : KEY_T)
    (C : CFG_T Q PosKeyT E) (S : SSA_T Q PosKeyT E C PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (B : LANG_SSA_LINK O K G Q R E C S)
    <: VALIDATE_ALL O K G P Q R E C S DG D B.
  Include Validate O K G P Q R E C S DG D B.
  TimeFun tables.
  TimeFun row_budget.
  TimeFun check_entry.
  TimeFun code_scan.
  TimeFun check_code.
  TimeFun available_target.
  TimeFun check_target.
  TimeFun check_arm.
  TimeFun check_edge.
  TimeFun check_exit.
  TimeFun check_block.
  TimeFun check.
  TimeFun dom_cert.
  TimeFun ssa_edge_shape.
  TimeFun ssa_exit_shape.
  TimeFun ssa_precheck.
  TimeFun ssa_cross.
  TimeFun ssa_local.
  TimeFun check_ssa.
  TimeFun graph.
  Definition c_val : N := 1. (* STUB *)
  Definition dom_bound s := N.of_nat ((graph_n (base (graph s)) +
    graph_e (base (graph s)) + 1) * (Nat.log2 (graph_n (base (graph s))) + 1)).
  Definition check_width (p s : P.t) (c : cert) :=
    function_width p + function_width s + vertex_width (cert_ids c).
  Definition op_bits (p : P.t) :=
    fold_right (fun item n =>
      fold_right (fun i m => K.bits (snd (fst i)) + m) 0 (code _ _ _ (snd item)) +
      match term _ _ _ (snd item) with
      | Branch g _ _ _ _ _ => G.bits g
      | _ => 0
      end + n) 0 (blocks _ _ _ p).


  Definition val_scan_cost : N := (4 * PTrieT.c_trie + K.c_key + 64)%N.

  Lemma code_scan_time : forall ic sc rho forward inverse known w,
    (forall i, In i (ic ++ sc) ->
      Pos.size_nat (fst (fst i)) <= w /\
      forall x, In x (snd i) -> Pos.size_nat x <= w) ->
    (T_code_scan ic sc rho forward inverse known <= val_scan_cost *
      N.of_nat (length ic +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat ic) * N.of_nat (w + 1) +
      val_scan_cost * N.of_nat (fold_right
        (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic) + 1)%N.
  Proof.
    induction ic as [|[[x op] args] rest IH]; intros sc rho forward inverse known w Hwidth.
    - time_step.
    - destruct sc as [|[[y sop] sargs] sr].
      + time_step.
      + destruct (Hwidth (x, op, args) ltac:(left; reflexivity)) as [Hx Hargs].
        destruct (Hwidth (y, sop, sargs)
          ltac:(apply in_or_app; right; left; reflexivity)) as [Hy Hsargs].
        cbn [fst snd] in Hx, Hy, Hargs, Hsargs.
        assert (Htail : forall i, In i (rest ++ sr) ->
          Pos.size_nat (fst (fst i)) <= w /\
          forall z, In z (snd i) -> Pos.size_nat z <= w).
        { intros i Hin; apply Hwidth; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
          - apply in_or_app; left; right; exact Hin.
          - apply in_or_app; right; right; exact Hin. }
        specialize (IH sr ((x, y) :: rho) (PTrieCode.set x y forward)
          (PTrieCode.set y x inverse) (PTrieCode.set x tt known) w Htail).
        pose proof (K.T_eqb_le op sop) as Hop.
        pose proof (val_args_time args sargs forward known w Hargs Hsargs) as Harg.
        pose proof (PTrieT.T_set_le positive x y forward) as Hforward.
        pose proof (PTrieT.T_set_le positive y x inverse) as Hinverse.
        pose proof (PTrieT.T_set_le unit x tt known) as Hknown.
        assert (Howner :
          ((match trie_get y inverse with Some owner => Pos.T_eqb x owner | None => 0 end)
            <= N.of_nat w)%N).
        { destruct (trie_get y inverse) as [owner|].
          - pose proof (Pos.T_eqb_le x owner); lia.
          - lia. }
        time_unfold T_code_scan; rewrite PTrieT.trie_get_clock;
          time_simpl; time_cbn; unfold val_scan_cost in *.
        destruct (K.eqb op sop && val_args forward known args sargs &&
          match trie_get y inverse with Some owner => Pos.eqb x owner | None => true end);
          time_cbn; nia.
  Qed.

  (** The optional scan is bounded by paying for every code-checking phase. *)
  Lemma code_clock : forall ic sc rho live,
    (T_check_code ic sc rho live <=
      1 + T_val_injective rho + T_val_index rho + T_val_inverse rho + T_val_set live +
        T_code_scan ic sc rho (val_index rho) (val_inverse rho) (val_set live))%N.
  Proof.
    intros ic sc rho live; time_unfold T_check_code; destruct (val_injective rho); lia.
  Qed.

  (** Code checking is linear in its lists at any width bounding their identifiers. *)
  Lemma code_time_from_width : forall ic sc rho live w,
    (forall x, In x live -> Pos.size_nat x <= w) ->
    (forall x y, In (x, y) rho -> Pos.size_nat x <= w /\ Pos.size_nat y <= w) ->
    (forall i, In i (ic ++ sc) -> Pos.size_nat (fst (fst i)) <= w /\
      forall x, In x (snd i) -> Pos.size_nat x <= w) ->
    (T_check_code ic sc rho live <= (8 * PTrieT.c_trie + 4 * K.c_key + 256) *
      N.of_nat (length rho + length live + length ic + length sc +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (ic ++ sc) + 1) *
      N.of_nat (w + 1) +
      (8 * PTrieT.c_trie + 4 * K.c_key + 256) * N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))%N.
  Proof.
    intros ic sc rho live w Hlive Hrho Hcode.
    pose proof (val_injective_time rho w Hrho) as Hinjective.
    pose proof (val_index_time rho w
      ltac:(intros x y Hin; exact (proj1 (Hrho x y Hin)))) as Hindex.
    pose proof (val_inverse_time rho w Hrho) as Hinverse.
    pose proof (val_set_time live w Hlive) as Hset.
    pose proof (code_scan_time ic sc rho (val_index rho) (val_inverse rho)
      (val_set live) w Hcode) as Hscan.
    assert (Hargs : fold_right (fun i n => length (snd i) + n) 0 ic <=
      fold_right (fun i n => length (snd i) + n) 0 (ic ++ sc)).
    { clear - ic sc; induction ic as [|i rest IH]; cbn; lia. }
    set (cost := (8 * PTrieT.c_trie + 4 * K.c_key + 256)%N).
    pose proof (code_clock ic sc rho live) as Hclock.
    pose proof (proj1 (N.add_le_mono_l _ _ 1%N) Hinjective) as Hstart.
    pose proof (N.add_le_mono _ _ _ _ Hstart Hindex) as Hindexed.
    pose proof (N.add_le_mono _ _ _ _ Hindexed Hinverse) as Hinverted.
    pose proof (N.add_le_mono _ _ _ _ Hinverted Hset) as Hknown.
    pose proof (N.add_le_mono _ _ _ _ Hknown Hscan) as Hsum.
    lazymatch type of Hsum with
    | (_ <= ?rhs)%N => replace rhs with
        ((3 * PTrieT.c_trie + 30) * N.of_nat (length rho) * N.of_nat (w + 1) +
          (PTrieT.c_trie + 2) * N.of_nat (length live) * N.of_nat (w + 1) +
          val_scan_cost * N.of_nat (length ic +
            fold_right (fun i n => (length (snd i) + n)%nat) 0%nat ic) * N.of_nat (w + 1) +
          val_scan_cost * N.of_nat
            (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic) + 12)%N
        in Hsum by ring
    end.
    eapply N.le_trans; [exact Hclock|]; eapply N.le_trans; [exact Hsum|].
    fold cost.
    replace (N.of_nat
      (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))
      with (N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic) + 1)%N by lia.
    apply val_code_charge.
    - unfold cost; lia.
    - unfold cost; lia.
    - unfold cost, val_scan_cost; lia.
    - unfold cost; lia.
    - clear Hinjective Hindex Hinverse Hset Hscan Hclock Hstart Hindexed Hinverted Hknown Hsum;
        lia.

  Qed.

  (** The code-checking budget uses the maximum identifier width of its input lists. *)
  Lemma code_time : forall ic sc rho live,
    (T_check_code ic sc rho live <= (8 * PTrieT.c_trie + 4 * K.c_key + 256) *
      N.of_nat (length rho + length live + length ic + length sc +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (ic ++ sc) + 1) *
      N.of_nat (vertex_width (live ++
        flat_map (fun xy => [fst xy; snd xy]) rho ++
        flat_map (fun i => fst (fst i) :: snd i) (ic ++ sc)) + 1) +
      (8 * PTrieT.c_trie + 4 * K.c_key + 256) * N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))%N.
  Proof.
    intros ic sc rho live.
    set (w := vertex_width (live ++
      flat_map (fun xy => [fst xy; snd xy]) rho ++
      flat_map (fun i => fst (fst i) :: snd i) (ic ++ sc))).
    assert (Hlive : forall x, In x live -> Pos.size_nat x <= w).
    { intros x Hin; unfold w; apply val_width_member; apply in_or_app; left; exact Hin. }
    assert (Hrho : forall x y, In (x, y) rho ->
      Pos.size_nat x <= w /\ Pos.size_nat y <= w).
    { intros x y Hin; split; unfold w; apply val_width_member;
        apply in_or_app; right; apply in_or_app; left; apply in_flat_map;
        exists (x, y); split; [exact Hin|cbn; auto|exact Hin|cbn; auto]. }
    assert (Hcode : forall i, In i (ic ++ sc) ->
      Pos.size_nat (fst (fst i)) <= w /\
      forall x, In x (snd i) -> Pos.size_nat x <= w).
    { intros i Hin; split.
      - unfold w; apply val_width_member; apply in_or_app; right; apply in_or_app; right;
          apply in_flat_map; exists i; split; [exact Hin|left; reflexivity].
      - intros x Hx; unfold w; apply val_width_member; apply in_or_app; right;
          apply in_or_app; right; apply in_flat_map; exists i; split;
          [exact Hin|right; exact Hx]. }
    exact (code_time_from_width ic sc rho live w Hlive Hrho Hcode).
  Qed.

  Lemma tables_time : forall p s c,
    (T_tables p s c <= (8 * (PTrieT.c_trie + 2)) *
      N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1))%N.
  Proof.
    intros p s c.
    pose proof (val_index_time (blocks _ _ _ p) (check_width p s c)
      ltac:(intros b body Hin; pose proof (val_block_width p b body Hin);
        unfold check_width; lia)) as Hp.
    pose proof (val_index_time (blocks _ _ _ s) (check_width p s c)
      ltac:(intros b body Hin; pose proof (val_block_width s b body Hin);
        unfold check_width; lia)) as Hs.
    pose proof (val_index_time (fst c) (check_width p s c)
      ltac:(intros b row Hin; pose proof (val_cert_env_width c b row Hin);
        unfold check_width; lia)) as He.
    pose proof (val_index_time (snd c) (check_width p s c)
      ltac:(intros b row Hin; pose proof (val_cert_live_width c b row Hin);
        unfold check_width; lia)) as Hl.
    pose proof (val_cert_rows c) as Hrows.
    assert (Hbp : length (blocks _ _ _ p) <= function_size p)
      by (unfold function_size; lia).
    assert (Hbs : length (blocks _ _ _ s) <= function_size s)
      by (unfold function_size; lia).
    set (width := N.of_nat (check_width p s c + 1)).
    set (count := (N.of_nat (length (blocks _ _ _ p)) +
      N.of_nat (length (blocks _ _ _ s)) + N.of_nat (length (fst c)) +
      N.of_nat (length (snd c)))%N).
    assert (Hcount : (count + 1 <=
      N.of_nat (function_size p + function_size s + cert_size c + 1))%N).
    { unfold count; lia. }
    assert (Hclock : (T_tables p s c <= (PTrieT.c_trie + 2) * count * width + 9)%N).
    { pose proof (N.add_le_mono _ _ _ _ Hp Hs) as Hps.
      pose proof (N.add_le_mono _ _ _ _ Hps He) as Hpse.
      pose proof (N.add_le_mono _ _ _ _ Hpse Hl) as Hsum.
      lazymatch type of Hsum with
      | (_ <= ?rhs)%N => replace rhs with
          ((PTrieT.c_trie + 2) * count * width + 4)%N in Hsum
          by (unfold count, width; ring)
      end.
      clear Hp Hs He Hl Hps Hpse Hrows Hbp Hbs Hcount;
        time_unfold T_tables; time_simpl; lia. }
    assert (Hmono : ((PTrieT.c_trie + 2) * (count + 1) * width <=
      (PTrieT.c_trie + 2) *
        N.of_nat (function_size p + function_size s + cert_size c + 1) * width)%N).
    { apply N.mul_le_mono_r; apply N.mul_le_mono_l; exact Hcount. }
    assert (Hwidth : (1 <= width)%N) by (unfold width; lia).
    clear Hp Hs He Hl Hrows Hbp Hbs Hcount; fold width; nia.
  Qed.

  Lemma checks_time : forall p s c,
    (T_check p s c <= T_tables p s c +
      (8 * (PTrieT.c_trie + 16)) * N.of_nat (function_size p + 1) *
        N.of_nat (check_width p s c + 1) +
      T_check_entry p s c (tables p s c) +
      fold_right N.add 0%N (map (fun item => T_check_block (tables p s c) (fst item))
        (first_blocks (blocks _ _ _ p))))%N.
  Proof.
    intros p s c.
    pose proof (val_first_time (blocks _ _ _ p) (check_width p s c)
      ltac:(intros b body Hin; pose proof (val_block_width p b body Hin);
        unfold check_width; lia)) as Hfirst.
    assert (Hlength : length (first_blocks (blocks _ _ _ p)) <= length (blocks _ _ _ p)).
    { rewrite val_first_selected; apply val_selected_length. }
    assert (Hsource : length (blocks _ _ _ p) <= function_size p)
      by (unfold function_size; lia).
    assert (Hsize : (N.of_nat (length (blocks _ _ _ p) + 1) <=
      N.of_nat (function_size p + 1))%N) by lia.
    assert (Hfirst' : (T_first_blocks (blocks _ _ _ p) <= (PTrieT.c_trie + 16) *
      N.of_nat (function_size p + 1) * N.of_nat (check_width p s c + 1))%N).
    { eapply N.le_trans; [exact Hfirst|].
      apply N.mul_le_mono_r; apply N.mul_le_mono_l; exact Hsize. }
    clear Hfirst Hsize.
    time_unfold T_check; time_simpl.
    destruct (check_entry p s c (tables p s c)).
    - lazymatch goal with
      | |- context [List.T_forallb ?f ?Tf ?bs] =>
        pose proof (val_forallb_extra f Tf
          (fun item => T_check_block (tables p s c) (fst item)) bs 2%N
          ltac:(intros item Hin; time_simpl; time_cbn; nia)) as Hscan
      end.
      assert (Hwidth : (1 <= N.of_nat (check_width p s c + 1))%N) by lia.
      assert (Hsmall : (4 * N.of_nat (length (first_blocks (blocks _ _ _ p))) + 3 <=
        (PTrieT.c_trie + 16) * N.of_nat (function_size p + 1) *
          N.of_nat (check_width p s c + 1))%N).
      { assert (Hbase : (4 * N.of_nat (length (first_blocks (blocks _ _ _ p))) + 3 <=
          16 * N.of_nat (function_size p + 1))%N) by lia.
        assert (Hcoeff : (16 <= (PTrieT.c_trie + 16) *
          N.of_nat (check_width p s c + 1))%N) by nia.
        eapply N.le_trans; [exact Hbase|].
        replace ((PTrieT.c_trie + 16) * N.of_nat (function_size p + 1) *
          N.of_nat (check_width p s c + 1))%N with
          (((PTrieT.c_trie + 16) * N.of_nat (check_width p s c + 1)) *
            N.of_nat (function_size p + 1))%N by ring.
        apply N.mul_le_mono_r; exact Hcoeff. }
      set (budget := ((PTrieT.c_trie + 16) * N.of_nat (function_size p + 1) *
        N.of_nat (check_width p s c + 1))%N) in Hfirst', Hsmall.
      replace ((8 * (PTrieT.c_trie + 16)) * N.of_nat (function_size p + 1) *
        N.of_nat (check_width p s c + 1))%N with (8 * budget)%N by (unfold budget; ring).
      clear Hlength Hsource Hwidth; lia.
    - clear Hfirst' Hlength Hsource.
      assert (Hsize : (1 <= N.of_nat (function_size p + 1))%N) by lia.
      assert (Hwidth : (1 <= N.of_nat (check_width p s c + 1))%N) by lia.
      nia.
  Qed.

  (** Translation checking charges both functions and the supplied certificate. *)
  Lemma T_check_le : forall p s c,
    (T_check p s c <= c_val * N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1) + c_val * N.of_nat (op_bits p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** SSA checking includes the core dominator construction budget. *)
  Lemma T_check_ssa_le : forall s,
    (T_check_ssa s <= c_val * (N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Translation checking has the published certificate-sensitive bit-cost bound. *)
  Lemma check_bigO : bigO (fun _ : P.t * P.t * cert => True)
    (fun '(p, s, c) => N.of_nat ((function_size p + function_size s + cert_size c + 1) *
      (check_width p s c + 1) + op_bits p + 1)) (fun '(p, s, c) => T_check p s c).
  Proof. Admitted. (* STUB *)
  (** SSA checking has the published syntax and dominator bit-cost bound. *)
  Lemma check_ssa_bigO : bigO (fun _ : P.t => True)
    (fun s => ((N.of_nat (function_size s + 1) + dom_bound s) *
      N.of_nat (function_width s + 1))%N) T_check_ssa.
  Proof. Admitted. (* STUB *)
  Definition k_entry : N := 1. (* STUB *)
  Definition k_code : N := 1. (* STUB *)
  Definition k_edge : N := 1. (* STUB *)
  Definition k_blocks : N := (8 * (PTrieT.c_trie + 16))%N.
  Definition k_ssa : N := 1. (* STUB *)
  Definition agrees (rho : renaming) (xs : list positive) (ss si : env O.C) :=
    forall x, In x xs -> exists y, lookup x rho = Some y /\ lookup y ss = lookup x si.
  Definition code_defs (xs : list (positive * O.K * list positive)) :=
    map (fun i => fst (fst i)) xs.
  Lemma F1_checks : forall p s c, check p s c = true ->
    check_entry p s c (tables p s c) = true /\ forall b body,
      In (b, body) (blocks _ _ _ p) -> check_block (tables p s c) b = true.
  Proof.
    exact check_checks.
  Qed.
  Lemma F2_code_sim : forall ic sc rho rho' live ss si,
    check_code ic sc rho live = Some rho' -> agrees rho live ss si ->
    match exec_code O.eval sc ss, exec_code O.eval ic si with
    | None, None => True
    | Some ss', Some si' => agrees rho' (code_defs ic ++ live) ss' si'
    | _, _ => False
    end.
  Proof.
    intros ic sc rho rho' live ss si Hcheck Hagree.
    exact (check_code_sim ic sc rho live rho' ss si Hcheck Hagree).
  Qed.
  Lemma F3_edge_sim : forall p s c b target rho ss si sa ia sb ib sx ix choice,
    check p s c = true -> check_edge (tables p s c) b target rho = true ->
    find_block b (blocks _ _ _ s) = Some sb ->
    find_block b (blocks _ _ _ p) = Some ib ->
    edge_choice (term _ _ _ sb) choice = Some (target, sx) ->
    edge_choice (term _ _ _ ib) choice = Some (target, ix) ->
    read_vars ss sx = Some sa -> read_vars si ix = Some ia ->
    agrees rho (cert_live c target) ss si ->
    state_sim p s c (target, sa, ss) (target, ia, si).
  Proof.
    intros p s c b target rho ss si sa ia sb ib sx ix choice _ Hedge Hsb Hib
      Hse Hie Hreads Hreadi Hagree.
    unfold check_edge in Hedge; pose proof (tables_agree p s c b) as [Hsource [Htarget _]].
    rewrite Hsource, Htarget, Hib, Hsb in Hedge.
    apply andb_true_iff in Hedge as [Hyes Hno].
    assert (Harm : check_arm (tables p s c) target rho
      (val_set (map (fun i => fst (fst i)) (code _ _ _ ib) ++
        index_row (cert_rows (tables p s c)) b)) (term _ _ _ ib) (term _ _ _ sb) choice = true).
    { destruct choice; assumption. }
    unfold check_arm in Harm; rewrite Hie, Hse in Harm; destruct ix; [|discriminate].
    cbn [read_vars] in Hreadi; injection Hreadi as Heq; subst ia.
    rewrite !Pos.eqb_refl in Harm; cbn in Harm; unfold check_target in Harm.
    destruct (trie_get target (source_bodies (tables p s c))) as [it|] eqn:Hit;
      [|discriminate].
    destruct (trie_get target (target_bodies (tables p s c))) as [st|] eqn:Hst;
      [|discriminate].
    destruct (params _ _ _ it) eqn:Hip; [|discriminate].
    destruct (val_bind_symbols (params _ _ _ st) sx Empty) as [bound|] eqn:Hbound;
      [|discriminate].
    apply andb_true_iff in Harm as [_ Hlive].
    destruct (val_bind_symbols_sound _ _ _ _ ss ss sa Hbound Hreads)
      as [entered [Hbind Hvalues]].
    { intro y; unfold val_symbol; rewrite PTrie.get_empty; reflexivity. }
    unfold state_sim; split; [reflexivity|].
    pose proof (tables_agree p s c target) as [Hsrc [Htgt [Henv Hrow]]].
    rewrite Hsrc in Hit; rewrite Htgt in Hst; rewrite Hit, Hst, Hbind, Hip.
    cbn [bind_vars]; intros x Hin; rewrite forallb_forall in Hlive.
    assert (Hmember : In x (index_row (cert_rows (tables p s c)) target)).
    { rewrite Hrow; exact Hin. }
    specialize (Hlive x Hmember); apply andb_true_iff in Hlive as [_ Hmap].
    rewrite !val_index_lookup in Hmap.
    destruct (lookup x (index_row (cert_envs (tables p s c)) target)) as [y|] eqn:Hnext;
      [|discriminate]; destruct (lookup x rho) as [z|] eqn:Hcurrent; [|discriminate].
    apply Pos.eqb_eq in Hmap; destruct (Hagree x Hin) as [v [Hv Heq]].
    rewrite Hcurrent in Hv; injection Hv as Heqv; subst v; exists y; split.
    - rewrite val_row_lookup in Hnext; unfold cert_env; rewrite <- Henv; exact Hnext.
    - rewrite Hvalues, Hmap; exact Heq.
  Qed.
  Lemma F4_block_sim : forall p s c ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (step O.eval O.test s ss) (step O.eval O.test p si).
  Proof. Admitted. (* PLAN-DEFECT: option equality permits absent live values; an SSA
    edge can fail while reading a parameter argument that the imperative edge does not read.
    The public theorem uses state_ready and step_ready, which also track defined live values. *)
  Lemma F5_entry_sim : forall p s c ins ss si,
    imp_form p -> check p s c = true ->
    bind_vars (inputs _ _ _ s) ins [] = Some ss ->
    bind_vars (inputs _ _ _ p) ins [] = Some si ->
    state_sim p s c (entry _ _ _ s, [], ss) (entry _ _ _ p, [], si).
  Proof.
    intros p s c ins ss si _ Hcheck Hss Hsi.
    destruct (entry_ready p s c ins si Hcheck Hsi) as [entered [Hentered Hready]].
    rewrite Hss in Hentered; injection Hentered as Heq; subst entered.
    destruct Hready as [Hid Hready]; unfold state_sim; split; [exact Hid|]; cbn in Hready.
    destruct (find_block (entry _ _ _ s) (blocks _ _ _ s)) as [sb|]; [|contradiction].
    destruct (find_block (entry _ _ _ p) (blocks _ _ _ p)) as [ib|]; [|contradiction].
    destruct Hready as [es [ei [Hbs [Hbi [Hagree _]]]]]; rewrite Hbs, Hbi.
    intros x Hin; pose proof (tables_agree p s c (entry _ _ _ p)) as [_ [_ [Henv Hrow]]].
    rewrite <- Hrow in Hin; destruct (Hagree x Hin) as [y [Hmap Hvalue]].
    exists y; split; [|exact Hvalue]; unfold cert_env; rewrite <- Henv.
    rewrite val_row_lookup in Hmap; exact Hmap.
  Qed.
  Lemma F6_input_arity : forall p s c, check p s c = true ->
    length (inputs _ _ _ s) = length (inputs _ _ _ p).
  Proof.
    exact check_input_arity.
  Qed.
  Lemma F7_run_sim : forall p s c n ss si,
    imp_form p -> check p s c = true -> state_sim p s c ss si ->
    outcome_sim p s c (loop_fuel (step O.eval O.test s) n ss)
      (loop_fuel (step O.eval O.test p) n si).
  Proof. Admitted. (* PLAN-DEFECT: the one-step counterexample to F4_block_sim also
    refutes this statement at fuel one; loop_ready supplies the required stronger invariant. *)
  Lemma F8_dom_checked : forall s, check_ssa s = true ->
    D.check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) = true.
  Proof.
    intros s Hcheck; unfold check_ssa in Hcheck.
    destruct (ssa_precheck s); [|discriminate]; fold (graph s) in Hcheck.
    destruct (dom_cert s) as [m order]; cbn [fst snd].
    destruct (D.check (graph s) (entry _ _ _ s) m order); [reflexivity|discriminate].
  Qed.
  Lemma F9_ssa_wf : forall s, check_ssa s = true -> ssa_wf s.
  Proof.
    exact check_ssa_sound.
  Qed.
  (** Graph preparation and certificate work fit the syntax and dominator budget. *)
  Lemma T1_dom : forall s,
    (T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) <=
      k_ssa * (N.of_nat (function_size s + 1) + dom_bound s) *
        N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Entry checking charges both input lists and the indexed certificate row. *)
  Lemma T2b_entry : forall p s c,
    (T_check_entry p s c (tables p s c) <= k_entry *
      N.of_nat (length (inputs _ _ _ p) + length (inputs _ _ _ s) +
        length (cert_live c (entry _ _ _ p)) + 1) *
      N.of_nat (check_width p s c + 1))%N.
  Proof. Admitted. (* PLAN-DEFECT: a singleton empty return with entry row
    repeat (1,1) n has constant input/live lengths and width, but indexing and scanning
    the environment row takes unbounded work. The precheck also pays for other rows. *)
  (** Code checking indexes its initial renaming and reads both instruction streams once. *)
  Lemma T2c_code : forall ic sc rho live,
    (T_check_code ic sc rho live <= k_code *
      N.of_nat (length rho + length live + length ic + length sc +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (ic ++ sc) + 1) *
      N.of_nat (vertex_width (live ++
        flat_map (fun xy => [fst xy; snd xy]) rho ++
        flat_map (fun i => fst (fst i) :: snd i) (ic ++ sc)) + 1) +
      k_code * N.of_nat
        (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat ic + 1))%N.
  Proof. Admitted. (* OPEN: code_time proves this bound with a private constant.
    k_code stays 1 because the shared T2a_block budget is false, and the session permits
    a constant change only after every field using that constant is proved. *)
  (** Indexed edge checking charges the two exits and the destination certificate row. *)
  Lemma T2d_edge : forall p s c b target rho ib sb,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    (T_check_edge (tables p s c) b target rho <= k_edge *
      N.of_nat (length rho + length (exit_uses (term _ _ _ ib)) +
        length (exit_uses (term _ _ _ sb)) + length (cert_live c target) + 1) *
      N.of_nat (check_width p s c +
        vertex_width (flat_map (fun xy => [fst xy; snd xy]) rho) + 1))%N.
  Proof. Admitted. (* PLAN-DEFECT: with empty Jump 2 exits, rho=[] and empty live rows,
    a destination environment row repeat (1,1) n is indexed although n is absent from
    this budget. The public check rejects oversized destination rows before block checks. *)
  (** Translation checking indexes the certificate, checks the entry and every source block. *)
  Lemma T2_checks : forall p s c,
    (T_check p s c <= T_tables p s c +
      k_blocks * N.of_nat (function_size p + 1) * N.of_nat (check_width p s c + 1) +
      T_check_entry p s c (tables p s c) +
      fold_right N.add 0%N (map (fun item => T_check_block (tables p s c) (fst item))
        (first_blocks (blocks _ _ _ p))))%N.
  Proof.
    exact checks_time.
  Qed.
  (** One block check charges its two bodies, its operands, its live row, its exit and its
      operators. *)
  Lemma T2a_block : forall p s c b ib,
    find_block b (blocks _ _ _ p) = Some ib ->
    (T_check_block (tables p s c) b <= k_code *
      N.of_nat (length (block_defs ib) + length (exit_uses (term _ _ _ ib)) +
        length (code _ _ _ ib) +
        fold_right (fun i n => (length (snd i) + n)%nat) 0%nat (code _ _ _ ib) +
        length (cert_live c b) + 1) *
      N.of_nat (check_width p s c + 1) +
      k_code * N.of_nat (fold_right (fun i n => (K.bits (snd (fst i)) + n)%nat) 0%nat
        (code _ _ _ ib) +
        match term _ _ _ ib with
        | Branch g _ _ _ _ _ => G.bits g
        | _ => 0
        end + 1))%N.
  Proof. Admitted. (* PLAN-DEFECT: an empty return block with entry environment row
    repeat (1,1) n performs unbounded indexing work, while every listed size stays fixed.
    The target body and outgoing environment rows are also absent from this local budget. *)
  (** SSA checking adds the strict local-order and dominance queries to the graph phase. *)
  Lemma T3_ssa : forall s,
    (T_check_ssa s <= T_graph s + T_dom_cert s +
      D.T_check (graph s) (entry _ _ _ s) (fst (dom_cert s)) (snd (dom_cert s)) +
      k_ssa * N.of_nat (function_size s + 1) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The tables retain the first body and certificate row for each identifier. *)
  Lemma F0_tables : forall p s c b,
    trie_get b (source_bodies (tables p s c)) = find_block b (blocks _ _ _ p) /\
    trie_get b (target_bodies (tables p s c)) = find_block b (blocks _ _ _ s) /\
    trie_get b (cert_envs (tables p s c)) = lookup b (fst c) /\
    index_row (cert_rows (tables p s c)) b = cert_live c b.
  Proof.
    exact tables_agree.
  Qed.
  (** Building lookup tables scans the functions and certificate once. *)
  Lemma T0_tables : forall p s c,
    (T_tables p s c <= k_blocks *
      N.of_nat (function_size p + function_size s + cert_size c + 1) *
      N.of_nat (check_width p s c + 1))%N.
  Proof.
    intros p s c; eapply N.le_trans; [exact (tables_time p s c)|].
    unfold k_blocks; apply N.mul_le_mono_r; apply N.mul_le_mono_r; lia.
  Qed.
End ValidateT.
