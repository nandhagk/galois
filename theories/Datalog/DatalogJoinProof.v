(** * Exact prepared join indexes

    Preparation and incremental insertion maintain an extensional row-index invariant.
    For example, resetting a frontier bucket removes its old rows before inserting the batch.
    Builds on: DatalogJoin and the public Map and FinSet specifications. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire DatalogJoin.
Import List.ListNotations Cost.Notations Join.

Module JoinProof.

(** List equivalence observes membership and permits different bucket insertion orders. *)
Definition list_equiv {A} (xs ys : list A) := forall x, In x xs <-> In x ys.

Lemma select_equation {A} mask (xs : list A) :
  select mask xs =
  match mask, xs with
  | [], [] => Some []
  | keep :: rest, x :: tail =>
    option_map (fun ys => if keep then x :: ys else ys) (select rest tail)
  | _, _ => None
  end.
Proof.
  destruct mask, xs; reflexivity.
Qed.

Lemma select_instance {A B} (f : A -> bool) (g : A -> B) ts :
  select (map f ts) (map g ts) = Some (map g (filter f ts)).
Proof.
  induction ts as [|t ts IH]; rewrite select_equation; [reflexivity |].
  cbn [map filter]; rewrite IH; destruct (f t); reflexivity.
Qed.

Lemma index_get_equation idx key :
  index_get idx key = match Map.get tuple_encoding key idx with
  | Some rows => rows
  | None => []
  end.
Proof.
  apply Map.find_or_equation.
Qed.

Lemma index_add_equation mask row idx :
  index_add mask row idx =
  match select mask row with
  | None => idx
  | Some key => Map.set tuple_encoding key (row :: index_get idx key) idx
  end.
Proof.
  unfold index_add, index_add_c; rewrite Cost.value_bind.
  fold (@select positive mask row); destruct (select mask row); reflexivity.
Qed.

Lemma index_add_wf mask row idx :
  Map.wf tuple_encoding idx -> Map.wf tuple_encoding (index_add mask row idx).
Proof.
  intro Hwf; rewrite index_add_equation; destruct (select mask row).
  - apply Map.wf_set, Hwf.
  - exact Hwf.
Qed.

Lemma index_add_members mask row idx key cs :
  Map.wf tuple_encoding idx ->
  (In cs (index_get (index_add mask row idx) key) <->
    In cs (index_get idx key) \/ (cs = row /\ select mask row = Some key)).
Proof.
  intro Hwf; rewrite index_add_equation; destruct (select mask row) as [k |] eqn:Hkey.
  - rewrite index_get_equation, Map.get_set by exact Hwf.
    destruct (BaseEq.eqb_spec tuple_encoding tuple_encoding_laws key k) as [Heq | Hne].
    + subst k; cbn [In]; intuition congruence.
    + fold (index_get idx key); intuition congruence.
  - intuition discriminate.
Qed.

Lemma extend_index_equation mask rows idx :
  extend_index mask rows idx = fold_right (index_add mask) idx rows.
Proof.
  unfold extend_index, extend_index_c; apply value_fold_right_c.
Qed.

Lemma extend_index_wf mask rows idx :
  Map.wf tuple_encoding idx -> Map.wf tuple_encoding (extend_index mask rows idx).
Proof.
  rewrite extend_index_equation; intro Hwf; induction rows as [|row rows IH].
  - exact Hwf.
  - apply index_add_wf, IH.
Qed.

Lemma extend_index_members mask rows idx key cs :
  Map.wf tuple_encoding idx ->
  (In cs (index_get (extend_index mask rows idx) key) <->
    In cs (index_get idx key) \/ (In cs rows /\ select mask cs = Some key)).
Proof.
  intro Hwf; rewrite extend_index_equation; induction rows as [|row rows IH].
  - cbn [fold_right In]; tauto.
  - cbn [fold_right]; rewrite index_add_members.
    + rewrite IH; cbn [In]; intuition congruence.
    + rewrite <- extend_index_equation; apply extend_index_wf, Hwf.
Qed.

Lemma bound_term_equation bound t :
  bound_term bound t =
  match t with
  | TConst _ => true
  | TVar v => existsb (Nat.eqb v) bound
  end.
Proof.
  destruct t; [apply value_existsb_c | reflexivity].
Qed.

Lemma variables_equation ts :
  variables ts = filter_map (fun t => match t with TVar v => Some v | TConst _ => None end) ts.
Proof.
  unfold variables, variables_c; apply value_filter_map_c.
Qed.

Lemma variables_spec ts v : In v (variables ts) <-> In (TVar v) ts.
Proof.
  rewrite variables_equation, in_filter_map; split.
  - intros [[w | c] [Hin Heq]]; [injection Heq as <-; exact Hin | discriminate].
  - intro Hin; exists (TVar v); auto.
Qed.

(** An index is valid when each bucket has precisely its source relation's selected rows. *)
Definition node_exact {P} (env : P -> Cost.t relation) (n : node P) :=
  Map.wf tuple_encoding (table n) /\
  forall key row, In row (index_get (table n) key) <->
    member row (Cost.value (env (pred (source n)))) = true /\ select (mask n) row = Some key.

(** The plan shape fixes its source atoms, position masks and precomputed bound-term order. *)
Fixpoint shape {P} (bound : list nat) (ps : list (atom P)) (plan : plan_state P) : Prop :=
  match ps, plan with
  | [], [] => True
  | a :: rest, n :: tail =>
    source n = a /\
    mask n = map (bound_term bound) (args a) /\
    key_terms n = filter (bound_term bound) (args a) /\
    shape (variables (args a) ++ bound) rest tail
  | _, _ => False
  end.

(** Ready plans separate their fixed layout from the maintained bucket contents. *)
Definition ready {P} bound ps env (plan : plan_state P) :=
  shape bound ps plan /\ Forall (node_exact env) plan.

Lemma prepare_from_equation {P} bound (ps : list (atom P)) env :
  prepare_from bound ps env =
  match ps with
  | [] => []
  | a :: rest =>
    Node a (map (bound_term bound) (args a)) (filter (bound_term bound) (args a))
      (extend_index (map (bound_term bound) (args a))
        (FinSet.elements (set_raw (Cost.value (env (pred a))))) Map.empty) ::
    prepare_from (variables (args a) ++ bound) rest env
  end.
Proof.
  destruct ps as [|a ps]; [reflexivity |].
  unfold prepare_from at 1; cbn [prepare_from_c]; repeat rewrite Cost.value_bind.
  rewrite value_map_c, value_filter_c, value_app_c; reflexivity.
Qed.

(** Preparation establishes the complete layout and row-index invariant without caller proofs. *)
Theorem join_prepare_ready {P} bound (ps : list (atom P)) env :
  ready bound ps env (prepare_from bound ps env).
Proof.
  revert bound; induction ps as [|a ps IH]; intro bound; rewrite prepare_from_equation.
  - split; [exact I | constructor].
  - destruct (IH (variables (args a) ++ bound)) as [Hshape Hnodes].
    split; [cbn [shape source mask key_terms]; auto |].
    constructor; [|exact Hnodes]; split.
    + apply extend_index_wf, Map.wf_empty.
    + intros key row; cbn [table source mask].
      rewrite extend_index_members by apply Map.wf_empty.
      rewrite index_get_equation, Map.get_empty; cbn [In].
      rewrite (FinSet.elements_spec tuple_encoding tuple_encoding_laws
        row _ (proj2_sig (Cost.value (env (pred a))))).
      unfold member; tauto.
Qed.

(** The public program-shaped preparation entry point produces a ready empty-binding plan. *)
Theorem prepare_ready {P} (prog : program P) ps env :
  ready [] ps env (prepare prog ps env).
Proof.
  exact (join_prepare_ready [] ps env).
Qed.

Lemma probe_equation {P} (n : node P) bs :
  probe n bs = flat_map (fun b =>
    filter_map (fun row => bind_terms (args (source n)) row b)
      (index_get (table n) (map (inst (binding_value b)) (key_terms n)))) bs.
Proof.
  unfold probe, probe_c; rewrite value_fold_right_c.
  unfold probe_one_c; induction bs as [|b bs IH]; cbn [fold_right flat_map]; [reflexivity |].
  repeat rewrite Cost.value_bind; rewrite value_app_c, value_filter_map_c.
  rewrite instantiate_equation, IH; reflexivity.
Qed.

Lemma probe_members {P} (n : node P) bs b' :
  In b' (probe n bs) <->
  exists b row, In b bs /\
    In row (index_get (table n) (map (inst (binding_value b)) (key_terms n))) /\
    bind_terms (args (source n)) row b = Some b'.
Proof.
  rewrite probe_equation, in_flat_map; split.
  - intros [b [Hb Hin]]; apply in_filter_map in Hin as [row [Hrow Hbind]].
    exists b, row; auto.
  - intros [b [row [Hb [Hrow Hbind]]]]; exists b; split; [exact Hb |].
    apply in_filter_map; exists row; auto.
Qed.

(** Incoming bindings must assign each variable used to build an index key. *)
Definition covers bound b := forall v, In v bound -> exists c, binding_get b v = Some c.

Lemma covers_extends bound b b' :
  covers bound b -> binding_extends b b' -> covers bound b'.
Proof.
  intros Hcovers Hext v Hv; destruct (Hcovers v Hv) as [c Hc].
  exists c; apply Hext, Hc.
Qed.

Lemma covers_next {P} bound (a : atom P) b b' row :
  covers bound b -> bind_terms (args a) row b = Some b' ->
  covers (variables (args a) ++ bound) b'.
Proof.
  intros Hcovers Hbind; destruct (bind_terms_sound _ _ _ _ Hbind) as [Hext [_ Hvars]].
  intros v Hv; apply in_app_iff in Hv as [Hv | Hv].
  - apply Hvars, variables_spec, Hv.
  - apply (covers_extends bound b b' Hcovers Hext), Hv.
Qed.

Lemma bound_inst_extends bound ts b b' :
  covers bound b -> binding_extends b b' ->
  map (inst (binding_value b)) (filter (bound_term bound) ts) =
    map (inst (binding_value b')) (filter (bound_term bound) ts).
Proof.
  intros Hcovers Hext; apply map_ext_in; intros [v | c] Hin; [|reflexivity].
  apply filter_In in Hin as [_ Hbound]; rewrite bound_term_equation in Hbound.
  apply existsb_exists in Hbound as [w [Hw Heq]]; apply Nat.eqb_eq in Heq; subst w.
  destruct (Hcovers v Hw) as [d Hd].
  pose proof (Hext v d Hd) as Hd'.
  change (binding_value b v = binding_value b' v).
  unfold binding_value, binding_value_c; rewrite !Cost.value_map.
  change ((match binding_get b v with Some c => c | None => 1%positive end) =
    (match binding_get b' v with Some c => c | None => 1%positive end)).
  rewrite Hd, Hd'; reflexivity.
Qed.

Lemma matching_key bound ts row b b' :
  covers bound b -> bind_terms ts row b = Some b' ->
  select (map (bound_term bound) ts) row =
    Some (map (inst (binding_value b)) (filter (bound_term bound) ts)).
Proof.
  intros Hcovers Hbind.
  destruct (bind_terms_sound _ _ _ _ Hbind) as [Hext [Hrow _]].
  rewrite (Hrow _ (binding_value_agrees b')), select_instance.
  rewrite (bound_inst_extends bound ts b b' Hcovers Hext); reflexivity.
Qed.

Lemma probe_agrees {P} bound (a : atom P) n env bs :
  source n = a ->
  mask n = map (bound_term bound) (args a) ->
  key_terms n = filter (bound_term bound) (args a) ->
  node_exact env n ->
  (forall b, In b bs -> covers bound b) ->
  list_equiv (probe n bs) (join_atom a env bs).
Proof.
  intros Hsource Hmask Hkeys [_ Hindex] Hcovers b'.
  rewrite probe_members, join_atom_members; split.
  - intros [b [row [Hb [Hrow Hbind]]]]; exists b, row; split; [exact Hb |].
    rewrite Hsource in Hbind; split; [|exact Hbind].
    apply Hindex in Hrow; rewrite Hsource in Hrow; exact (proj1 Hrow).
  - intros [b [row [Hb [Hrow Hbind]]]]; exists b, row; split; [exact Hb | split].
    + apply Hindex; rewrite Hsource, Hmask, Hkeys; split; [exact Hrow |].
      apply (matching_key bound _ _ _ b'); [apply Hcovers, Hb | exact Hbind].
    + rewrite Hsource; exact Hbind.
Qed.

Lemma join_atom_inputs {P} (a : atom P) env bs bs' :
  list_equiv bs bs' -> list_equiv (join_atom a env bs) (join_atom a env bs').
Proof.
  intros Hbs b; rewrite !join_atom_members; split.
  - intros [b0 [cs [Hb Hrest]]]; exists b0, cs; split; [apply Hbs, Hb | exact Hrest].
  - intros [b0 [cs [Hb Hrest]]]; exists b0, cs; split; [apply Hbs, Hb | exact Hrest].
Qed.

Lemma run_from_equation {P} (plan : plan_state P) bs :
  run_from plan bs =
  match plan with
  | [] => bs
  | n :: rest => run_from rest (probe n bs)
  end.
Proof.
  destruct plan; reflexivity.
Qed.

Lemma run_from_agrees {P} bound (ps : list (atom P)) env plan bs bs' :
  ready bound ps env plan ->
  list_equiv bs bs' ->
  (forall b, In b bs -> covers bound b) ->
  list_equiv (run_from plan bs) (join_positive_ref ps env bs').
Proof.
  revert bound plan bs bs'; induction ps as [|a ps IH];
    intros bound [|n plan] bs bs' [Hshape Hnodes] Hbs Hcovers;
    try contradiction.
  - exact Hbs.
  - cbn [shape] in Hshape; destruct Hshape as [Hsource [Hmask [Hkeys Htail]]].
    pose proof (Forall_inv Hnodes) as Hnode.
    pose proof (Forall_inv_tail Hnodes) as Hrest.
    rewrite run_from_equation, join_positive_equation.
    apply (IH (variables (args a) ++ bound)).
    + split; assumption.
    + intro b; rewrite (probe_agrees bound a n env bs Hsource Hmask Hkeys Hnode Hcovers b).
      apply join_atom_inputs, Hbs.
    + intros b Hb; apply probe_members in Hb as [b0 [row [Hb0 [_ Hbind]]]].
      rewrite Hsource in Hbind; eapply covers_next; [apply Hcovers, Hb0 | exact Hbind].
Qed.

(** Every prepared or incrementally maintained plan agrees with the reference binding join. *)
Theorem join_run_agrees {P} ps env (plan : plan_state P) :
  ready [] ps env plan ->
  list_equiv (run plan) (join_positive_ref ps env [[]]).
Proof.
  intro Hready; apply (run_from_agrees [] ps env plan [[]] [[]] Hready).
  - intro b; reflexivity.
  - intros b _ v Hbad; contradiction.
Qed.

Lemma fire_members {P} (r : rule P) env plan ts :
  member ts (fire r env plan) = true <->
  exists b, In b (run plan) /\ negative_ok r env b = true /\
    ts = map (inst (binding_value b)) (args (head r)).
Proof.
  unfold fire, fire_c; repeat rewrite Cost.value_bind.
  rewrite value_filter_c, value_map_c.
  change (member ts (set_of_list tuple_encoding
    (map (fun b => Cost.value (instantiate_c b (args (head r))))
      (filter (negative_ok r env) (run plan)))) = true <->
    exists b, In b (run plan) /\ negative_ok r env b = true /\
      ts = map (inst (binding_value b)) (args (head r))).
  rewrite relation_of_list, in_map_iff; split.
  - intros [b [Heq Hin]]; apply filter_In in Hin.
    rewrite instantiate_equation in Heq; exists b; intuition congruence.
  - intros [b [Hin [Hnegative Heq]]]; exists b; split.
    + rewrite instantiate_equation; symmetry; exact Heq.
    + apply filter_In; auto.
Qed.

(** Indexed firing agrees with the existing public firing owner on every tuple membership. *)
Theorem join_fire_agrees {P} (prog : program P) r env plan ts :
  ready [] (positive_atoms (body r)) env plan ->
  member ts (fire r env plan) = member ts (fire_rule prog r env).
Proof.
  intro Hready; apply eq_true_iff_eq.
  rewrite fire_members; unfold member; rewrite fire_rule_members; split.
  - intros [b [Hin Hrest]]; exists b; split; [|exact Hrest].
    apply (join_run_agrees _ _ _ Hready b), Hin.
  - intros [b [Hin Hrest]]; exists b; split; [|exact Hrest].
    apply (join_run_agrees _ _ _ Hready b), Hin.
Qed.

(** Safe indexed firing returns all and only heads of valuations satisfying the source body. *)
Theorem join_fire_exact {P} (prog : program P) (r : rule P) env plan :
  ready [] (positive_atoms (body r)) env plan -> safe_rule r -> forall ts,
  member ts (fire r env plan) = true <->
  exists sigma, ts = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a))) = true) /\
    (forall a, In (LNeg a) (body r) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a))) = false).
Proof.
  intros Hready Hsafe ts; rewrite (join_fire_agrees prog r env plan ts Hready).
  apply fire_rule_exact, Hsafe.
Qed.

Definition updated_env {P} (reset : P -> Cost.t bool) (rows : P -> Cost.t (list tuple))
    (env : P -> Cost.t relation) p :=
  if Cost.value (reset p) then set_of_list tuple_encoding (Cost.value (rows p))
  else Cost.value (set_union_c tuple_encoding (Cost.value (env p))
    (set_of_list tuple_encoding (Cost.value (rows p)))).

Lemma updated_env_members {P} reset rows (env : P -> Cost.t relation) p row :
  member row (updated_env reset rows env p) = true <->
  In row (Cost.value (rows p)) \/
    (Cost.value (reset p) = false /\ member row (Cost.value (env p)) = true).
Proof.
  unfold updated_env; destruct (Cost.value (reset p)).
  - rewrite relation_of_list; intuition discriminate.
  - change (member row (join relation_lattice (Cost.value (env p))
      (set_of_list tuple_encoding (Cost.value (rows p)))) = true <->
      In row (Cost.value (rows p)) \/ (false = false /\
        member row (Cost.value (env p)) = true)).
    rewrite relation_join, orb_true_iff, relation_of_list; tauto.
Qed.

Lemma insert_rows_equation {P} reset rows (plan : plan_state P) :
  insert_rows reset rows plan =
  map (fun n => Node (source n) (mask n) (key_terms n)
    (extend_index (mask n) (Cost.value (rows (pred (source n))))
      (if Cost.value (reset (pred (source n))) then Map.empty else table n))) plan.
Proof.
  unfold insert_rows, insert_rows_c; rewrite value_map_c; reflexivity.
Qed.

(** Insertion maintains the same fixed plan layout and the exact extended or reset row contents. *)
Theorem join_insert_ready {P} bound ps env (plan : plan_state P) reset rows :
  ready bound ps env plan ->
  ready bound ps (fun p => Cost.ret (updated_env reset rows env p))
    (insert_rows reset rows plan).
Proof.
  intros [Hshape Hnodes]; split.
  - clear Hnodes; rewrite insert_rows_equation; revert bound ps Hshape.
    induction plan as [|n plan IH]; intros bound [|a ps] Hshape; try contradiction.
    + exact I.
    + cbn [shape map source mask key_terms] in *.
      destruct Hshape as [Ha [Hm [Hk Htail]]].
      split; [exact Ha | split; [exact Hm | split; [exact Hk | apply IH, Htail]]].
  - rewrite insert_rows_equation, Forall_map; apply Forall_forall.
    intros n Hn; rewrite Forall_forall in Hnodes; destruct (Hnodes n Hn) as [Hwf Hindex].
    split; cbn [table source mask].
    + apply extend_index_wf; destruct (Cost.value (reset (pred (source n))));
        [apply Map.wf_empty | exact Hwf].
    + intros key row; rewrite extend_index_members by
        (destruct (Cost.value (reset (pred (source n))));
          [apply Map.wf_empty | exact Hwf]).
      rewrite Cost.value_ret, updated_env_members.
      destruct (Cost.value (reset (pred (source n)))) eqn:Hreset.
      * rewrite index_get_equation, Map.get_empty; cbn [In]; intuition discriminate.
      * rewrite Hindex; tauto.
Qed.

(** Updated and freshly prepared plans return the same binding set on the extended rows. *)
Theorem join_insert_agrees {P} (prog : program P) ps env plan reset rows :
  ready [] ps env plan ->
  list_equiv (run (insert_rows reset rows plan))
    (run (prepare prog ps (fun p => Cost.ret (updated_env reset rows env p)))).
Proof.
  intros Hready b.
  rewrite (join_run_agrees ps _ _ (join_insert_ready [] ps env plan reset rows Hready) b).
  symmetry; apply join_run_agrees, join_prepare_ready.
Qed.

End JoinProof.
Import JoinProof.
