(** * Translation and SSA validation

    The translation checker follows each instruction and checks the supplied entry renamings.
    For example, it accepts a renamed return only when both returns read corresponding values.
    Builds on: ValidateSig. *)

From Stdlib Require Import List PArith NArith Bool Lia.
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
  match trie_get x rho with Some z => Pos.eqb z y | None => false end.
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
  (match trie_get y inverse with Some owner => Pos.eqb owner x | None => true end) = true ->
  val_inverse_ok ((x, y) :: rho) (PTrieCode.set y x inverse).
Proof.
  intros rho inverse x y Hinv Hfresh z value Hlookup.
  rewrite val_lookup_cons in Hlookup; destruct (Pos.eqb z x) eqn:Hzx.
  - apply Pos.eqb_eq in Hzx; inversion Hlookup; subst; apply PTrie.get_set_same.
  - apply Pos.eqb_neq in Hzx.
    pose proof (Hinv z value Hlookup) as Hold.
    assert (Hneq : value <> y).
    { intro Heq; subst value; rewrite Hold in Hfresh; apply Pos.eqb_eq in Hfresh;
        contradiction. }
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
  (match trie_get y inverse with Some owner => Pos.eqb owner x | None => true end) = true ->
  val_agrees ((x, y) :: rho) (x :: live) ((y, value) :: ss) ((x, value) :: si).
Proof.
  intros rho inverse live x y value ss si Hinv Hagree Hfresh z Hin.
  destruct (Pos.eq_dec z x) as [Heq|Hneq].
  - subst z; exists y; cbn [lookup]; rewrite !Pos.eqb_refl; auto.
  - destruct Hin as [Heq|Hin]; [congruence|].
    destruct (Hagree z Hin) as [v [Hv Hvalue]].
    assert (Hvy : v <> y).
    { intro Heq; subst v; rewrite (Hinv z y Hv) in Hfresh.
      apply Pos.eqb_eq in Hfresh; contradiction. }
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

Module ValidateCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (E : TYPE)
    (C : CFG_INDEXED_OPS Q PosKeyCode E) (S : SSA_OPS Q PosKeyCode E C PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) <: VALIDATE_OPS O K G P Q R E C S DG D.
  Definition tables (p s : P.t) (c : cert) : check_tables O.K O.G :=
    CheckTables (val_index (blocks _ _ _ p)) (val_index (blocks _ _ _ s))
      (val_index (fst c)) (val_index (snd c)).

  Definition check_entry (p s : P.t) (_ : cert) (t : check_tables O.K O.G) : bool :=
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
    end.

  Fixpoint code_scan (ic sc : list (positive * O.K * list positive))
      (rho : renaming) (forward inverse : ptrie positive) (known : ptrie unit)
      : option renaming :=
    match ic, sc with
    | [], [] => Some rho
    | (x, op, args) :: ir, (y, sop, sargs) :: sr =>
      if K.eqb op sop && val_args forward known args sargs &&
        match trie_get y inverse with Some owner => Pos.eqb owner x | None => true end
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
    check_entry p s c t &&
      forallb (fun item => check_block t (fst item)) (first_blocks (blocks _ _ _ p)).

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
    intros p s c Hcheck; apply andb_true_iff in Hcheck as [Hentry Hblocks].
    split; [exact Hentry|]; intros b body Hin.
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
        match trie_get y inverse with Some owner => Pos.eqb owner x | None => true end)
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
    unfold check_entry in Hentry; apply andb_true_iff in Hentry as [_ Hentry].
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
    unfold check_entry in Hentry; apply andb_true_iff in Hentry as [Hid Hentry].
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
  Definition k_blocks : N := 1. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  (** Indexed edge checking charges the two exits and the destination certificate row. *)
  Lemma T2d_edge : forall p s c b target rho ib sb,
    find_block b (blocks _ _ _ p) = Some ib ->
    find_block b (blocks _ _ _ s) = Some sb ->
    (T_check_edge (tables p s c) b target rho <= k_edge *
      N.of_nat (length rho + length (exit_uses (term _ _ _ ib)) +
        length (exit_uses (term _ _ _ sb)) + length (cert_live c target) + 1) *
      N.of_nat (check_width p s c +
        vertex_width (flat_map (fun xy => [fst xy; snd xy]) rho) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Translation checking indexes the certificate, checks the entry and every source block. *)
  Lemma T2_checks : forall p s c,
    (T_check p s c <= T_tables p s c +
      k_blocks * N.of_nat (function_size p + 1) * N.of_nat (check_width p s c + 1) +
      T_check_entry p s c (tables p s c) +
      fold_right N.add 0%N (map (fun item => T_check_block (tables p s c) (fst item))
        (first_blocks (blocks _ _ _ p))))%N.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
End ValidateT.
