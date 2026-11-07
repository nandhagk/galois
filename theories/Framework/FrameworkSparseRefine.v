(** * Sound refinement of sparse facts

    Guard refinement retains concrete bindings through the prepared sparse engine.
    For example, an equality on an operation result can refine its immediate operands.
    Builds on: FrameworkSparse, DomainsValue and ProgramStrict. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeAdjoin.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink
  ProgramSsa ProgramStrict ProgramEdgeProjection.
From Galois.Domains Require Import DomainsValue.
From Galois.Framework Require Import FrameworkUtil FrameworkSparse.
Import List.ListNotations Cost.Notations.

Module SparseRefine.

(** Prepared plans retain the ordered guards and their immediate definitions. *)
Definition plans_c {N E V K G A} (P : Sparse.t N E V K G A) e :=
  let* gs := Cost.step ;; Ssa.guards_c (Sparse.ssa P) e in
  map_c (Sparse.guard_plan_c (Sparse.ssa P)) gs.

Definition plans {N E V K G A} (P : Sparse.t N E V K G A) e :=
  Cost.value (plans_c P e).

(** Guard preparation retains the syntax reader and its invocation tick before mapping plans. *)
Theorem plans_cost_equation {N E V K G A} (P : Sparse.t N E V K G A) e :
  Cost.ticks (plans_c P e) =
    (1 + Cost.ticks (Ssa.guards_c (Sparse.ssa P) e) +
      Cost.ticks (map_c (Sparse.guard_plan_c (Sparse.ssa P))
        (Ssa.guards (Sparse.ssa P) e)))%N.
Proof.
  unfold plans_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Dependencies include subjects and exactly one level of operation operands. *)
Definition dependencies_c {N E V K G A} (P : Sparse.t N E V K G A) e :=
  let* ps := plans_c P e in fw_flat_map_c Sparse.guard_deps_c ps.

Definition dependencies {N E V K G A} (P : Sparse.t N E V K G A) e :=
  Cost.value (dependencies_c P e).

(** A supplied fact replaces the selected key before the shared ordered refinement. *)
Definition refine_fact_c {N E V K G A} (P : Sparse.t N E V K G A)
    (sigma_c : Sparse.unknown N E V -> Cost.t (option A)) e z a :=
  let* ps := plans_c P e in
  let* deps := dependencies_c P e in
  let* xs := app_c [z] deps in
  let* fs := map_c (fun x =>
    let* same := eqb_c (Ssa.val_enc (Sparse.ssa P)) x z in
    if same then Cost.ret a else Cost.step ;; sigma_c (Sparse.UVal x)) xs in
  let* result := Sparse.refine_c P ps xs fs in
  match result with
  | None => Cost.ret None
  | Some m => Map.find_or_c (Ssa.val_enc (Sparse.ssa P)) None z m
  end.

Definition refine_fact {N E V K G A} (P : Sparse.t N E V K G A) sigma e z a :=
  Cost.value (refine_fact_c P (fun u => Cost.ret (sigma u)) e z a).

(** Reading the selected initial fact retains the reader's cost and invocation overhead. *)
Definition refine_on_edge_c {N E V K G A} (P : Sparse.t N E V K G A)
    (sigma_c : Sparse.unknown N E V -> Cost.t (option A)) e z :=
  let* a := Cost.step ;; sigma_c (Sparse.UVal z) in
  refine_fact_c P sigma_c e z a.

(** Edge refinement starts at the stored fact. *)
Definition refine_on_edge {N E V K G A} (P : Sparse.t N E V K G A) sigma e z :=
  Cost.value (refine_on_edge_c P (fun u => Cost.ret (sigma u)) e z).

(** Feasibility uses the same snapshot, guards and dependency test as the edge row. *)
Definition edge_feasible_c {N E V K G A} (P : Sparse.t N E V K G A)
    (sigma_c : Sparse.unknown N E V -> Cost.t (option A)) e :=
  let* ps := plans_c P e in
  let* xs := dependencies_c P e in
  let* fs := map_c (fun x => Cost.step ;; sigma_c (Sparse.UVal x)) xs in
  let* result := Sparse.refine_c P ps xs fs in
  match result with
  | None => Cost.ret false
  | Some m => Sparse.feasible_c (Ssa.val_enc (Sparse.ssa P)) (Sparse.dom P) xs m
  end.

Definition edge_feasible {N E V K G A} (P : Sparse.t N E V K G A) sigma e :=
  Cost.value (edge_feasible_c P (fun u => Cost.ret (sigma u)) e).

(** The costed reader's values determine the same ordered snapshot refinement. *)
Theorem refine_fact_c_equation {N E V K G A} (P : Sparse.t N E V K G A)
    sigma_c e z a :
  Cost.value (refine_fact_c P sigma_c e z a) =
    match Cost.value (Sparse.refine_c P (plans P e) (z :: dependencies P e)
      (map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
        then a else Cost.value (sigma_c (Sparse.UVal x))) (z :: dependencies P e))) with
    | None => None
    | Some m => Map.find_or (Ssa.val_enc (Sparse.ssa P)) None z m
    end.
Proof.
  unfold refine_fact_c; autorewrite with galois_cost.
  change ([z] ++ Cost.value (dependencies_c P e)) with (z :: dependencies P e).
  assert (Hmap : map (fun x => Cost.value
    (let* same := eqb_c (Ssa.val_enc (Sparse.ssa P)) x z in
     if same then Cost.ret a else Cost.step ;; sigma_c (Sparse.UVal x)))
    (z :: dependencies P e) =
    map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
      then a else Cost.value (sigma_c (Sparse.UVal x))) (z :: dependencies P e)).
  { apply map_ext; intro x; rewrite Cost.value_bind.
    fold (eqb (Ssa.val_enc (Sparse.ssa P)) x z).
    destruct (eqb (Ssa.val_enc (Sparse.ssa P)) x z);
      autorewrite with galois_cost; reflexivity. }
  rewrite Hmap; fold (plans P e).
  destruct (Cost.value (Sparse.refine_c P (plans P e) (z :: dependencies P e)
    (map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
      then a else Cost.value (sigma_c (Sparse.UVal x))) (z :: dependencies P e))));
    reflexivity.
Qed.

(** Pure refinement is a ret-valued reader adapter with unchanged functional behavior. *)
Theorem refine_fact_equation {N E V K G A} (P : Sparse.t N E V K G A) sigma e z a :
  refine_fact P sigma e z a =
    match Cost.value (Sparse.refine_c P (plans P e) (z :: dependencies P e)
      (map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
        then a else sigma (Sparse.UVal x)) (z :: dependencies P e))) with
    | None => None
    | Some m => Map.find_or (Ssa.val_enc (Sparse.ssa P)) None z m
    end.
Proof.
  unfold refine_fact; rewrite refine_fact_c_equation; reflexivity.
Qed.

(** Pointwise reader agreement suffices without equality of functions. *)
Theorem refine_fact_c_agrees {N E V K G A} (P : Sparse.t N E V K G A)
    sigma_c sigma e z a :
  (forall u, Cost.value (sigma_c u) = sigma u) ->
  Cost.value (refine_fact_c P sigma_c e z a) = refine_fact P sigma e z a.
Proof.
  intro Hagrees; rewrite refine_fact_c_equation, refine_fact_equation.
  assert (Hmap : map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
      then a else Cost.value (sigma_c (Sparse.UVal x))) (z :: dependencies P e) =
    map (fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
      then a else sigma (Sparse.UVal x)) (z :: dependencies P e)).
  { apply map_ext; intro x; rewrite Hagrees; reflexivity. }
  rewrite Hmap; reflexivity.
Qed.

(** The edge adapter starts from the assignment's selected stored fact. *)
Theorem refine_on_edge_equation {N E V K G A} (P : Sparse.t N E V K G A) sigma e z :
  refine_on_edge P sigma e z = refine_fact P sigma e z (sigma (Sparse.UVal z)).
Proof.
  unfold refine_on_edge, refine_on_edge_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Pointwise reader agreement also preserves the selected initial edge fact. *)
Theorem refine_on_edge_c_agrees {N E V K G A} (P : Sparse.t N E V K G A)
    sigma_c sigma e z :
  (forall u, Cost.value (sigma_c u) = sigma u) ->
  Cost.value (refine_on_edge_c P sigma_c e z) = refine_on_edge P sigma e z.
Proof.
  intro Hagrees; unfold refine_on_edge_c; autorewrite with galois_cost.
  rewrite refine_on_edge_equation, Hagrees; apply refine_fact_c_agrees; exact Hagrees.
Qed.

(** The selected read and the remaining refinement both retain their actual charges. *)
Theorem refine_on_edge_cost_equation {N E V K G A} (P : Sparse.t N E V K G A)
    sigma_c e z :
  Cost.ticks (refine_on_edge_c P sigma_c e z) =
    (1 + Cost.ticks (sigma_c (Sparse.UVal z)) +
      Cost.ticks (refine_fact_c P sigma_c e z (Cost.value (sigma_c (Sparse.UVal z)))))%N.
Proof.
  unfold refine_on_edge_c; autorewrite with galois_cost; lia.
Qed.

(** The costed feasibility reader supplies exactly the edge row's dependency snapshot. *)
Theorem edge_feasible_c_equation {N E V K G A} (P : Sparse.t N E V K G A) sigma_c e :
  Cost.value (edge_feasible_c P sigma_c e) =
    match Cost.value (Sparse.refine_c P (plans P e) (dependencies P e)
      (map (fun x => Cost.value (sigma_c (Sparse.UVal x))) (dependencies P e))) with
    | None => false
    | Some m =>
      Cost.value (Sparse.feasible_c (Ssa.val_enc (Sparse.ssa P)) (Sparse.dom P)
        (dependencies P e) m)
    end.
Proof.
  unfold edge_feasible_c; autorewrite with galois_cost.
  fold (plans P e) (dependencies P e).
  assert (Hmap : map (fun x => Cost.value (Cost.step ;; sigma_c (Sparse.UVal x)))
    (dependencies P e) =
    map (fun x => Cost.value (sigma_c (Sparse.UVal x))) (dependencies P e)).
  { apply map_ext; intro x; autorewrite with galois_cost; reflexivity. }
  rewrite Hmap.
  destruct (Cost.value (Sparse.refine_c P (plans P e) (dependencies P e)
    (map (fun x => Cost.value (sigma_c (Sparse.UVal x))) (dependencies P e))));
    reflexivity.
Qed.

(** The pure feasibility adapter preserves the original accepted and rejected results. *)
Theorem edge_feasible_equation {N E V K G A} (P : Sparse.t N E V K G A) sigma e :
  edge_feasible P sigma e =
    match Cost.value (Sparse.refine_c P (plans P e) (dependencies P e)
      (map (fun x => sigma (Sparse.UVal x)) (dependencies P e))) with
    | None => false
    | Some m =>
      Cost.value (Sparse.feasible_c (Ssa.val_enc (Sparse.ssa P)) (Sparse.dom P)
        (dependencies P e) m)
    end.
Proof.
  unfold edge_feasible; rewrite edge_feasible_c_equation; reflexivity.
Qed.

(** Pointwise reader agreement preserves feasibility without an extensionality principle. *)
Theorem edge_feasible_c_agrees {N E V K G A} (P : Sparse.t N E V K G A)
    sigma_c sigma e :
  (forall u, Cost.value (sigma_c u) = sigma u) ->
  Cost.value (edge_feasible_c P sigma_c e) = edge_feasible P sigma e.
Proof.
  intro Hagrees; rewrite edge_feasible_c_equation, edge_feasible_equation.
  assert (Hmap : map (fun x => Cost.value (sigma_c (Sparse.UVal x))) (dependencies P e) =
    map (fun x => sigma (Sparse.UVal x)) (dependencies P e)).
  { apply map_ext; intro x; apply Hagrees. }
  rewrite Hmap; reflexivity.
Qed.

(** A map covers each bound value in its supplied read scope. *)
Definition covers {V A C} (EV : encoding V) (gam : concretisation A C)
    (val : V -> option C) (scope : list V) (m : Map.t V (option A)) : Prop :=
  Map.wf EV m /\ forall x c, In x scope -> val x = Some c ->
    gamma (lift_bot_gamma gam) (Map.find_or EV None x m) c.

Local Lemma zip_equation {X A} (xs : list X) (fs : list A) :
  Cost.value (Sparse.zip_c xs fs) = combine xs fs.
Proof.
  revert fs; induction xs as [|x xs IH]; intros [|a fs]; cbn [Sparse.zip_c combine];
    autorewrite with galois_cost; rewrite ?IH; reflexivity.
Qed.

(** Collection retains the witnesses attached to every operand occurrence. *)
Theorem collect_sound {A C} (gam : concretisation A C) fs cs :
  Forall2 (gamma (lift_bot_gamma gam)) fs cs ->
  exists values, Cost.value (Sparse.collect_c fs) = Some values /\
    Forall2 (gamma gam) values cs.
Proof.
  intro Hfs; induction Hfs as [|[a|] c fs cs Ha Hfs IH]; try contradiction.
  - exists []; split; [reflexivity|constructor].
  - destruct IH as [values [Hcollect Hvalues]].
    exists (a :: values); cbn [Sparse.collect_c]; autorewrite with galois_cost.
    rewrite Hcollect; split; [reflexivity|constructor; assumption].
Qed.

Local Lemma find_set {V A} (EV : encoding V) x y (a : A) m :
  Map.wf EV m ->
  Map.find_or EV None x (Map.set EV y (Some a) m) =
    if eqb EV x y then Some a else Map.find_or EV None x m.
Proof.
  intro Hwf; rewrite !Map.find_or_equation, Map.get_set by exact Hwf.
  destruct (eqb EV x y); reflexivity.
Qed.

Local Lemma put_equation {V A} (EV : encoding V) xs (fs : list A) m :
  Cost.value (Sparse.put_values_c EV xs fs m) =
    fold_right (fun va m => Map.set EV (fst va) (Some (snd va)) m) m (combine xs fs).
Proof.
  unfold Sparse.put_values_c; rewrite Cost.value_bind, zip_equation, value_fold_right_c.
  reflexivity.
Qed.

Local Lemma put_sound {V A C} (EV : encoding V) (HE : encoding_laws EV)
    (gam : concretisation A C) val scope xs fs cs m :
  covers EV gam val scope m ->
  Forall2 (fun x c => val x = Some c) xs cs ->
  Forall2 (gamma gam) fs cs ->
  covers EV gam val scope (Cost.value (Sparse.put_values_c EV xs fs m)).
Proof.
  intros Hm Hxs; revert fs.
  induction Hxs as [|x c xs cs Hx Hxs IH]; intros fs Hfs;
    inversion Hfs as [|a d fs' ds Ha Htail]; subst.
  - exact Hm.
  - rewrite put_equation.
    cbn [combine fold_right fst snd].
    rewrite <- put_equation.
    pose proof (IH fs' Htail) as [Hwf Hcovered]; split.
    + apply Map.wf_set; exact Hwf.
    + intros y v Hy Hv; rewrite find_set by exact Hwf.
      destruct (eqb EV y x) eqn:Heq.
      * apply (eqb_true_iff EV HE) in Heq; subst y; rewrite Hx in Hv.
        injection Hv as <-; exact Ha.
      * apply Hcovered; assumption.
Qed.

Local Lemma snapshot_lookup {V A} (EV : encoding V) (HE : encoding_laws EV)
    (f : V -> option A) xs x :
  In x xs ->
  Map.find_or EV None x
    (Cost.value (Sparse.snapshot_c EV xs (map f xs))) = f x.
Proof.
  intro Hin; unfold Sparse.snapshot_c; rewrite Cost.value_bind, zip_equation.
  change (Map.find_or EV None x (Map.of_list EV (combine xs (map f xs))) = f x).
  rewrite Map.find_or_equation, Map.of_list_get.
  assert (Hfold : forall ys old,
    (In x ys \/ old = Some (f x)) ->
    fold_left (fun old kv =>
      if eqb EV x (fst kv) then Some (snd kv) else old)
      (combine ys (map f ys)) old = Some (f x)).
  { intro ys; induction ys as [|y ys IH]; intros old Hpresent.
    - cbn in *; destruct Hpresent as [Hbad|Heq]; [contradiction|exact Heq].
    - cbn [combine map fold_left fst snd]; apply IH.
      destruct (eqb EV x y) eqn:Heq.
      + apply (eqb_true_iff EV HE) in Heq; subst y; right; reflexivity.
      + destruct Hpresent as [[Heqxy|Hinys]|Hold].
        * subst y; rewrite (eqb_refl EV x) in Heq; discriminate.
        * left; exact Hinys.
        * right; exact Hold. }
  rewrite Hfold; [reflexivity|left; exact Hin].
Qed.

(** A snapshot covers its read scope without requiring distinct keys. *)
Theorem snapshot_sound {V A C} (EV : encoding V) (HE : encoding_laws EV)
    (gam : concretisation A C) val xs f :
  (forall x c, In x xs -> val x = Some c -> gamma (lift_bot_gamma gam) (f x) c) ->
  covers EV gam val xs (Cost.value (Sparse.snapshot_c EV xs (map f xs))).
Proof.
  intro Hfacts; split.
  - unfold Sparse.snapshot_c; rewrite Cost.value_bind.
    apply Map.wf_of_list.
  - intros x c Hin Hval; rewrite snapshot_lookup; [apply Hfacts| |]; assumption.
Qed.

Local Lemma read_sound {V A C} (EV : encoding V) (gam : concretisation A C)
    val scope m xs cs :
  covers EV gam val scope m -> incl xs scope ->
  Forall2 (fun x c => val x = Some c) xs cs ->
  exists fs, Cost.value (Sparse.collect_c (Cost.value (Sparse.read_values_c EV m xs))) =
    Some fs /\ Forall2 (gamma gam) fs cs.
Proof.
  intros Hm Hin Hxs; unfold Sparse.read_values_c; rewrite value_map_c.
  apply collect_sound.
  induction Hxs as [|x c xs cs Hx Hxs IH]; cbn [map]; constructor.
  - apply (proj2 Hm); [apply Hin; left; reflexivity|exact Hx].
  - apply IH; intros y Hy; apply Hin; right; exact Hy.
Qed.

Local Lemma guard_plan_equation {N E V K G} (P : Ssa.t N E V K G) g ys :
  Cost.value (Sparse.guard_plan_c P (g, ys)) =
    (g, ys, map (fun y => (y, Ssa.def P y)) ys).
Proof.
  unfold Sparse.guard_plan_c; autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma plans_equation {N E V K G A} (P : Sparse.t N E V K G A) e :
  plans P e = map (fun gd =>
    (fst gd, snd gd, map (fun y => (y, Ssa.def (Sparse.ssa P) y)) (snd gd)))
    (Ssa.guards (Sparse.ssa P) e).
Proof.
  unfold plans, plans_c; rewrite Cost.value_bind, value_map_c.
  apply map_ext; intros [g ys]; apply guard_plan_equation.
Qed.

Local Lemma deps_equation {N V K G} g ys defs :
  Cost.value (@Sparse.guard_deps_c N V K G (g, ys, defs)) =
    ys ++ flat_map (fun vd => match snd vd with Op _ args => args | _ => [] end) defs.
Proof.
  unfold Sparse.guard_deps_c; rewrite Cost.value_bind, fw_flat_map_value, value_app_c.
  reflexivity.
Qed.

Local Lemma flat_map_map {X Y Z} (f : Y -> list Z) (g : X -> Y) xs :
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.

Section Engine.
Context {N E V K G A C : Type} (P : Sparse.t N E V K G A)
  (M : ValueSem.t C K G) (gam : concretisation A C)
  (HE : encoding_laws (Ssa.val_enc (Sparse.ssa P)))
  (HD : value_laws (Sparse.dom P) M gam)
  (val : V -> option C) (scope : list V).
Let EV := Ssa.val_enc (Sparse.ssa P).
Let D := Sparse.dom P.
Let covered := covers EV gam val scope.

Local Lemma back_one_sound m x k args :
  covered m -> In x scope -> incl args scope ->
  (exists cs c, Forall2 (fun y d => val y = Some d) args cs /\
    val x = Some c /\ ValueSem.eval M k cs = Some c) ->
  covered (Cost.value (Sparse.back_one_c (N := N) EV D m (x, Op k args))).
Proof.
  intros Hm Hxin Hin [cs [c [Hargs [Hx Hop]]]].
  unfold Sparse.back_one_c; cbn [fst snd]; autorewrite with galois_cost.
  fold (Map.find_or EV None x m).
  destruct (Map.find_or EV None x m) as [a|] eqn:Hresult; [|exact Hm].
  destruct (Cost.value (Sparse.collect_c (Cost.value (Sparse.read_values_c EV m args))))
    as [fs|] eqn:Hcollect; [|exact Hm].
  autorewrite with galois_cost.
  apply put_sound with (cs := cs); [exact HE|exact Hm|exact Hargs|].
  destruct (read_sound EV gam val scope m args cs Hm Hin Hargs)
    as [fs' [Hcollect' Hfs]].
  rewrite Hcollect in Hcollect'; injection Hcollect' as <-.
  apply (back_sound HD k a fs cs c); try assumption.
  pose proof (proj2 Hm x c Hxin Hx) as Ha; rewrite Hresult in Ha; exact Ha.
Qed.

Local Lemma back_list_sound defs m :
  covered m ->
  (forall x d, In (x, d) defs ->
    In x scope /\
    match d with
    | Op k args => incl args scope /\
        exists cs c, Forall2 (fun y v => val y = Some v) args cs /\
          val x = Some c /\ ValueSem.eval M k cs = Some c
    | _ => True
    end) ->
  covered (Cost.value (fold_left_c (Sparse.back_one_c (N := N) EV D) defs m)).
Proof.
  rewrite value_fold_left_c; revert m.
  induction defs as [|[x d] defs IH]; intros m Hm Hdefs; [exact Hm|].
  cbn [fold_left]; apply IH.
  - destruct (Hdefs x d (or_introl eq_refl)) as [Hx Hd].
    destruct d as [k args|b i|]; [apply back_one_sound; tauto|exact Hm|exact Hm].
  - intros y d' Hin; apply Hdefs; right; exact Hin.
Qed.

Local Lemma one_guard_sound g ys m :
  covered m ->
  incl (ys ++ flat_map (fun y =>
    match Ssa.def (Sparse.ssa P) y with Op _ args => args | _ => [] end) ys) scope ->
  (exists cs, Forall2 (fun y c => val y = Some c) ys cs /\ ValueSem.holds M g cs) ->
  (forall x k args, In x ys -> Ssa.def (Sparse.ssa P) x = Op k args ->
    exists cs c, Forall2 (fun y d => val y = Some d) args cs /\
      val x = Some c /\ ValueSem.eval M k cs = Some c) ->
  exists m', Cost.value (Sparse.guard_one_c EV D m
    (g, ys, map (fun y => (y, Ssa.def (Sparse.ssa P) y)) ys)) = Some m' /\ covered m'.
Proof.
  intros Hm Hin [cs [Hys Hholds]] Hops.
  assert (Hsubjects : incl ys scope).
  { intros x Hx; apply Hin, in_or_app; left; exact Hx. }
  destruct (read_sound EV gam val scope m ys cs Hm Hsubjects Hys)
    as [fs [Hcollect Hfs]].
  unfold Sparse.guard_one_c; autorewrite with galois_cost; rewrite Hcollect.
  autorewrite with galois_cost; eexists; split; [reflexivity|].
  rewrite <- value_fold_left_c.
  apply back_list_sound.
  - apply put_sound with (cs := cs); try assumption.
    apply (guard_sound HD); assumption.
  - intros x d Hxd; apply in_map_iff in Hxd.
    destruct Hxd as [y [Heq Hy]]; inversion Heq; subst y d.
    split; [apply Hsubjects; exact Hy|].
    destruct (Ssa.def (Sparse.ssa P) x) as [k args|b i|] eqn:Hdef;
      [split|exact I|exact I].
    + intros y Harg; apply Hin, in_or_app; right.
      apply in_flat_map; exists x; split; [exact Hy|rewrite Hdef; exact Harg].
    + apply Hops; assumption.
Qed.

(** Ordered guards preserve coverage of the entire retained snapshot. *)
Theorem guards_sound e ps m :
  ps = plans P e -> covered m ->
  incl (dependencies P e) scope ->
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y c => val y = Some c) ys cs /\ ValueSem.holds M g cs) ->
  (forall g ys x k args, In (g, ys) (Ssa.guards (Sparse.ssa P) e) -> In x ys ->
    Ssa.def (Sparse.ssa P) x = Op k args ->
    exists cs c, Forall2 (fun y d => val y = Some d) args cs /\
      val x = Some c /\ ValueSem.eval M k cs = Some c) ->
  exists m', Cost.value (Sparse.guards_c EV D ps m) = Some m' /\ covered m'.
Proof.
  intros -> Hm Hdeps Hguards Hops.
  assert (Hplan : forall gd, In gd (plans P e) ->
    forall m, covered m ->
    exists m', Cost.value (Sparse.guard_one_c EV D m gd) = Some m' /\ covered m').
  { intros gd Hgd m0 Hm0; rewrite plans_equation in Hgd.
    apply in_map_iff in Hgd; destruct Hgd as [[g ys] [<- Hguard]].
    apply one_guard_sound; [exact Hm0| |apply Hguards; exact Hguard|].
    - intros x Hx; apply Hdeps.
      unfold dependencies, dependencies_c; rewrite Cost.value_bind, fw_flat_map_value.
      apply in_flat_map; exists
        (g, ys, map (fun y => (y, Ssa.def (Sparse.ssa P) y)) ys); split.
      + fold (plans P e); rewrite plans_equation.
        apply in_map_iff; exists (g, ys); split; [reflexivity|].
        exact Hguard.
      + rewrite deps_equation, flat_map_map; exact Hx.
    - intros x k args Hx Hdef; apply (Hops g ys); assumption. }
  unfold Sparse.guards_c; rewrite value_fold_left_c.
  assert (Hfold : forall gs m0, incl gs (plans P e) -> covered m0 ->
    exists m', fold_left (fun acc gd =>
      Cost.value (match acc with
        | None => Cost.ret None
        | Some m => Sparse.guard_one_c EV D m gd
        end)) gs (Some m0) = Some m' /\ covered m').
  { intro gs; induction gs as [|gd gs IH]; intros m0 Hin Hm0.
    - exists m0; split; [reflexivity|exact Hm0].
    - destruct (Hplan gd (Hin gd (or_introl eq_refl)) m0 Hm0)
        as [m1 [Hone Hm1]].
      cbn [fold_left]; rewrite Hone; apply IH; [|exact Hm1].
      intros q Hq; apply Hin; right; exact Hq. }
  apply Hfold; [apply incl_refl|exact Hm].
Qed.

End Engine.

(** The row's snapshot and guard engine retain every bound scoped value. *)
Theorem refine_snapshot_sound {N E V K G A C} (P : Sparse.t N E V K G A)
    (M : ValueSem.t C K G) (gam : concretisation A C)
    (HE : encoding_laws (Ssa.val_enc (Sparse.ssa P)))
    (HD : value_laws (Sparse.dom P) M gam) (val : V -> option C) e xs f :
  incl (dependencies P e) xs ->
  (forall x c, In x xs -> val x = Some c -> gamma (lift_bot_gamma gam) (f x) c) ->
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y c => val y = Some c) ys cs /\ ValueSem.holds M g cs) ->
  (forall g ys x k args, In (g, ys) (Ssa.guards (Sparse.ssa P) e) -> In x ys ->
    Ssa.def (Sparse.ssa P) x = Op k args ->
    exists cs c, Forall2 (fun y d => val y = Some d) args cs /\
      val x = Some c /\ ValueSem.eval M k cs = Some c) ->
  exists m', Cost.value (Sparse.refine_c P (plans P e) xs (map f xs)) = Some m' /\
    covers (Ssa.val_enc (Sparse.ssa P)) gam val xs m'.
Proof.
  intros Hin Hfacts Hguards Hops.
  unfold Sparse.refine_c; rewrite Cost.value_bind.
  apply (guards_sound P M gam HE HD val xs e); try assumption; [reflexivity|].
  apply snapshot_sound; assumption.
Qed.

(** A fact containing a concrete value cannot compare below empty bottom. *)
Theorem inhabited_not_bottom {A C K G} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam a c :
  value_laws D M gam -> gamma gam a c ->
  negb (leb (ValueAbs.lat D) a (bot (ValueAbs.lat D))) = true.
Proof.
  intros HD Ha; apply negb_true_iff.
  destruct (leb (ValueAbs.lat D) a (bot (ValueAbs.lat D))) eqn:Hle; [|reflexivity].
  exfalso; apply (bot_empty HD c).
  eapply (gamma_monotone (gamma_ok HD)); eassumption.
Qed.

(** All dependencies of satisfying guards are bound in the same valuation. *)
Theorem dependencies_bound {N E V K G A C} (P : Sparse.t N E V K G A)
    (M : ValueSem.t C K G) (val : V -> option C) e :
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y c => val y = Some c) ys cs /\ ValueSem.holds M g cs) ->
  (forall g ys x k args, In (g, ys) (Ssa.guards (Sparse.ssa P) e) -> In x ys ->
    Ssa.def (Sparse.ssa P) x = Op k args ->
    exists cs c, Forall2 (fun y d => val y = Some d) args cs /\
      val x = Some c /\ ValueSem.eval M k cs = Some c) ->
  forall x, In x (dependencies P e) -> exists c, val x = Some c.
Proof.
  intros Hguards Hops x Hx.
  unfold dependencies, dependencies_c in Hx.
  rewrite Cost.value_bind, fw_flat_map_value in Hx.
  apply in_flat_map in Hx; destruct Hx as [gd [Hgd Hx]].
  fold (plans P e) in Hgd.
  rewrite plans_equation in Hgd; apply in_map_iff in Hgd.
  destruct Hgd as [[g ys] [<- Hguard]].
  rewrite deps_equation, flat_map_map in Hx; apply in_app_or in Hx.
  assert (Hbound : forall xs cs, Forall2 (fun y c => val y = Some c) xs cs ->
    forall y, In y xs -> exists c, val y = Some c).
  { intros xs cs Hxs; induction Hxs as [|y c xs cs Hy Hxs IH]; intros z Hz.
    - contradiction.
    - destruct Hz as [<-|Hz]; [exists c; exact Hy|apply IH; exact Hz]. }
  destruct Hx as [Hx|Hx].
  - destruct (Hguards g ys Hguard) as [cs [Hys _]]; eapply Hbound; eassumption.
  - apply in_flat_map in Hx; destruct Hx as [y [Hy Hx]].
    destruct (Ssa.def (Sparse.ssa P) y) as [k args|b i|] eqn:Hdef;
      try contradiction.
    destruct (Hops g ys y k args Hguard Hy Hdef) as [cs [c [Hargs _]]].
    eapply Hbound; eassumption.
Qed.

(** The engine's feasibility test accepts a covered list of bound dependencies. *)
Theorem feasible_sound {V A C K G} (EV : encoding V) (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam val xs m :
  value_laws D M gam -> covers EV gam val xs m ->
  (forall x, In x xs -> exists c, val x = Some c) ->
  Cost.value (Sparse.feasible_c EV D xs m) = true.
Proof.
  intros HD Hm Hbound; unfold Sparse.feasible_c; rewrite value_forallb_c.
  apply forallb_forall; intros x Hx; autorewrite with galois_cost.
  destruct (Hbound x Hx) as [c Hval].
  pose proof (proj2 Hm x c Hx Hval) as Ha.
  fold (Map.find_or EV None x m).
  destruct (Map.find_or EV None x m) as [a|]; [|contradiction].
  autorewrite with galois_cost.
  apply (inhabited_not_bottom D M gam a c HD Ha).
Qed.

Section PublicSoundness.
Context {S O N E V K G A C : Type} (P : Sparse.t N E V K G A)
  (sl : SsaLink.t S O N E V C) (M : ValueSem.t C K G) (gam : concretisation A C)
  (HE : encoding_laws (Ssa.val_enc (Sparse.ssa P)))
  (HD : value_laws (Sparse.dom P) M gam)
  (sigma : Sparse.unknown N E V -> option A) (s : S).
Let val := SsaLink.val sl s.
Hypothesis Hfacts : forall x c, val x = Some c ->
  gamma (lift_bot_gamma gam) (sigma (Sparse.UVal x)) c.

(** Refinement retains a supplied fact under local guard witnesses and operation equations. *)
Theorem refine_fact_sound e z a c :
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y d => val y = Some d) ys cs /\ ValueSem.holds M g cs) ->
  guard_ops_consistent (Sparse.ssa P) sl (ValueSem.eval M) s e ->
  val z = Some c -> gamma (lift_bot_gamma gam) a c ->
  gamma (lift_bot_gamma gam) (refine_fact P sigma e z a) c.
Proof.
  intros Hguards Hops Hz Ha.
  let f := constr:(fun x => if eqb (Ssa.val_enc (Sparse.ssa P)) x z
    then a else sigma (Sparse.UVal x)) in
  destruct (refine_snapshot_sound P M gam HE HD val e
    (z :: dependencies P e) f) as [m [Href Hm]].
  - intros x Hx; right; exact Hx.
  - intros x d _ Hx; destruct (eqb (Ssa.val_enc (Sparse.ssa P)) x z) eqn:Heq.
    + apply (eqb_true_iff _ HE) in Heq; subst x; rewrite Hz in Hx.
      injection Hx as <-; exact Ha.
    + apply Hfacts; exact Hx.
  - exact Hguards.
  - exact Hops.
  - rewrite refine_fact_equation.
    rewrite Href; apply (proj2 Hm); [left; reflexivity|exact Hz].
Qed.

(** Refinement of the stored fact retains every currently bound value. *)
Theorem refine_on_edge_sound e z c :
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y d => val y = Some d) ys cs /\ ValueSem.holds M g cs) ->
  guard_ops_consistent (Sparse.ssa P) sl (ValueSem.eval M) s e ->
  val z = Some c ->
  gamma (lift_bot_gamma gam) (refine_on_edge P sigma e z) c.
Proof.
  intros Hguards Hops Hz; rewrite refine_on_edge_equation.
  apply refine_fact_sound; try assumption.
  apply Hfacts; exact Hz.
Qed.

(** Satisfying guard witnesses force the shared feasibility test to accept. *)
Theorem edge_feasible_local_sound e :
  (forall g ys, In (g, ys) (Ssa.guards (Sparse.ssa P) e) ->
    exists cs, Forall2 (fun y d => val y = Some d) ys cs /\ ValueSem.holds M g cs) ->
  guard_ops_consistent (Sparse.ssa P) sl (ValueSem.eval M) s e ->
  edge_feasible P sigma e = true.
Proof.
  intros Hguards Hops.
  destruct (refine_snapshot_sound P M gam HE HD val e (dependencies P e)
    (fun x => sigma (Sparse.UVal x))) as [m [Href Hm]].
  - apply incl_refl.
  - intros x c _ Hx; apply Hfacts; exact Hx.
  - exact Hguards.
  - exact Hops.
  - rewrite edge_feasible_equation.
    rewrite Href; apply (feasible_sound _ _ M gam val); try assumption.
    eapply dependencies_bound; eassumption.
Qed.

End PublicSoundness.

(** Every concretely taken edge passes feasibility under sound source facts. *)
Theorem edge_feasible_sound {S O N E V K G A C} (m : semantics S O)
    (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
    (M : ValueSem.t C K G) gam sigma :
  encoding_laws (Ssa.val_enc (Sparse.ssa P)) ->
  ssa_laws m (Sparse.ssa P) sl (ValueSem.eval M) (ValueSem.holds M) ->
  value_laws (Sparse.dom P) M gam ->
  forall s l t e, reachable_state m s -> step m s l t ->
  Link.taken (SsaLink.link sl) s l t e ->
  (forall x c, SsaLink.val sl s x = Some c ->
    gamma (lift_bot_gamma gam) (sigma (Sparse.UVal x)) c) ->
  edge_feasible P sigma e = true.
Proof.
  intros HE HS HD s l t e Hreach Hstep Htaken Hfacts.
  apply (edge_feasible_local_sound P sl M gam HE HD sigma s Hfacts).
  - eapply (guards_hold HS); eassumption.
  - eapply (guard_op_defined HS); eassumption.
Qed.

(** Dominance refinement charges every edge and reuses the frozen single-edge engine. *)
Definition refined_fact_c {N E V K G A} (P : Sparse.t N E V K G A)
    (ctx : dom_context N E) (sigma_c : Sparse.unknown N E V -> Cost.t (option A)) b z :=
  let* es := dominating_edges_in_c ctx b in
  let* a := Cost.step ;; sigma_c (Sparse.UVal z) in
  fold_left_c (fun a e => refine_fact_c P sigma_c e z a) es a.

Definition refined_fact {N E V K G A} (P : Sparse.t N E V K G A) ctx sigma b z :=
  Cost.value (refined_fact_c P ctx (fun u => Cost.ret (sigma u)) b z).

Local Lemma fold_left_agrees {X A} (f g : A -> X -> A) xs a :
  (forall a x, f a x = g a x) -> fold_left f xs a = fold_left g xs a.
Proof.
  intro Hagrees; revert a; induction xs as [|x xs IH]; intro a; cbn [fold_left].
  - reflexivity.
  - rewrite Hagrees; apply IH.
Qed.

(** The costed fold starts at the selected reader value and preserves query order. *)
Theorem refined_fact_c_equation {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z :
  Cost.value (refined_fact_c P ctx sigma_c b z) =
    fold_left (fun a e => Cost.value (refine_fact_c P sigma_c e z a))
      (dominating_edges_in ctx b) (Cost.value (sigma_c (Sparse.UVal z))).
Proof.
  unfold refined_fact_c; autorewrite with galois_cost; reflexivity.
Qed.

(** The public equation exposes the ancestor-ordered fold and its stored initial fact. *)
Theorem refined_fact_equation {N E V K G A} (P : Sparse.t N E V K G A) ctx sigma b z :
  refined_fact P ctx sigma b z =
    fold_left (fun a e => refine_fact P sigma e z a)
      (dominating_edges_in ctx b) (sigma (Sparse.UVal z)).
Proof.
  unfold refined_fact; rewrite refined_fact_c_equation; reflexivity.
Qed.

(** Pointwise reader agreement preserves every intermediate ordinary-fold value. *)
Theorem refined_fact_c_agrees {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c sigma b z :
  (forall u, Cost.value (sigma_c u) = sigma u) ->
  Cost.value (refined_fact_c P ctx sigma_c b z) = refined_fact P ctx sigma b z.
Proof.
  intro Hagrees; rewrite refined_fact_c_equation, refined_fact_equation, Hagrees.
  apply fold_left_agrees; intros a e; apply refine_fact_c_agrees; exact Hagrees.
Qed.

(** The ordinary fold retains the query, initial reader and every reached edge charge. *)
Theorem refined_fact_cost_equation {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z :
  Cost.ticks (refined_fact_c P ctx sigma_c b z) =
    (Cost.ticks (dominating_edges_in_c ctx b) + 1 +
      Cost.ticks (sigma_c (Sparse.UVal z)) +
      Cost.ticks (fold_left_c (fun a e => refine_fact_c P sigma_c e z a)
        (dominating_edges_in ctx b) (Cost.value (sigma_c (Sparse.UVal z)))))%N.
Proof.
  unfold refined_fact_c; autorewrite with galois_cost.
  fold (dominating_edges_in ctx b); lia.
Qed.

(** The fold adds linear traversal overhead to a uniform bound on one edge refinement. *)
Theorem refined_fact_cost {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z k :
  (forall a e, (Cost.ticks (refine_fact_c P sigma_c e z a) <= k)%N) ->
  (Cost.ticks (refined_fact_c P ctx sigma_c b z) <=
    Cost.ticks (dominating_edges_in_c ctx b) + 1 + Cost.ticks (sigma_c (Sparse.UVal z)) +
      N.of_nat (length (dominating_edges_in ctx b)) * (k + 1))%N.
Proof.
  intro Hbound; rewrite refined_fact_cost_equation.
  pose proof (ticks_fold_left_c_le (fun a e => refine_fact_c P sigma_c e z a) k
    (dominating_edges_in ctx b) (Cost.value (sigma_c (Sparse.UVal z))) Hbound) as Hfold.
  lia.
Qed.

(** Semantically dominating guards retain a bound value throughout the ordered fold. *)
Theorem refine_dominating_edges_sound {S O N E V K G A C} (m : semantics S O)
    (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
    (M : ValueSem.t C K G) gam sigma s z c :
  encoding_laws (Ssa.val_enc (Sparse.ssa P)) ->
  ssa_laws m (Sparse.ssa P) sl (ValueSem.eval M) (ValueSem.holds M) ->
  strict_ssa_laws m (Sparse.ssa P) sl -> value_laws (Sparse.dom P) M gam ->
  reachable_state m s ->
  (forall x d, SsaLink.val sl s x = Some d ->
    gamma (lift_bot_gamma gam) (sigma (Sparse.UVal x)) d) ->
  SsaLink.val sl s z = Some c ->
  forall es a, Forall (fun e => edge_dominates (Cfg.graph (Ssa.cfg (Sparse.ssa P)))
    e (Link.point (SsaLink.link sl) s)) es ->
  gamma (lift_bot_gamma gam) a c ->
  gamma (lift_bot_gamma gam) (fold_left (fun a e => refine_fact P sigma e z a) es a) c.
Proof.
  intros HE HS HT HD Hreach Hfacts Hz es; induction es as [|e es IH];
    intros a Hedges Ha; [exact Ha|].
  inversion Hedges as [|? ? Hdom Htail]; subst; cbn [fold_left].
  apply IH; [exact Htail|].
  destruct (dominated_guard_holds m (Sparse.ssa P) sl (ValueSem.eval M)
    (ValueSem.holds M) HS HT s e Hreach Hdom) as [Hguards Hops].
  apply (refine_fact_sound P sl M gam HE HD sigma s Hfacts); assumption.
Qed.

(** A supplied ready graph and exact tree justify refinement at every reachable read. *)
Theorem refined_fact_sound {S O N E V K G A C} (m : semantics S O)
    (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
    (M : ValueSem.t C K G) gam sigma (p : Prepared.t N E) tree :
  Prepared.graph p = Cfg.graph (Ssa.cfg (Sparse.ssa P)) ->
  Prepared.ready p -> Dom.exact p tree ->
  encoding_laws (Ssa.val_enc (Sparse.ssa P)) ->
  ssa_laws m (Sparse.ssa P) sl (ValueSem.eval M) (ValueSem.holds M) ->
  strict_ssa_laws m (Sparse.ssa P) sl -> value_laws (Sparse.dom P) M gam ->
  forall s z c, reachable_state m s ->
  (forall x d, SsaLink.val sl s x = Some d ->
    gamma (lift_bot_gamma gam) (sigma (Sparse.UVal x)) d) ->
  SsaLink.val sl s z = Some c ->
  gamma (lift_bot_gamma gam)
    (refined_fact P (make_dom_context p tree) sigma (Link.point (SsaLink.link sl) s) z) c.
Proof.
  intros Hgraph Hready Htree HE HS HT HD s z c Hreach Hfacts Hz.
  rewrite refined_fact_equation; eapply refine_dominating_edges_sound; try eassumption.
  - apply Forall_forall; intros e Hin; rewrite <- Hgraph.
    eapply dominating_edges_in_sound; eassumption.
  - apply Hfacts; exact Hz.
Qed.

(** Occurrence contexts allow repeated client edge values without assuming a tree producer. *)
Definition refined_fact_projected_c {N E V K G A} (P : Sparse.t N E V K G A)
    (ctx : dom_context N (E * nat))
    (sigma_c : Sparse.unknown N E V -> Cost.t (option A)) b z :=
  let* es := dominating_edges_projected_c ctx b in
  let* a := Cost.step ;; sigma_c (Sparse.UVal z) in
  fold_left_c (fun a e => refine_fact_c P sigma_c e z a) es a.

Definition refined_fact_projected {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma b z :=
  Cost.value (refined_fact_projected_c P ctx (fun u => Cost.ret (sigma u)) b z).

(** The projected costed fold retains each query occurrence in order. *)
Theorem refined_fact_projected_c_equation {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z :
  Cost.value (refined_fact_projected_c P ctx sigma_c b z) =
    fold_left (fun a e => Cost.value (refine_fact_c P sigma_c e z a))
      (dominating_edges_projected ctx b) (Cost.value (sigma_c (Sparse.UVal z))).
Proof.
  unfold refined_fact_projected_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Projected refinement preserves the query's order and multiplicity. *)
Theorem refined_fact_projected_equation {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma b z :
  refined_fact_projected P ctx sigma b z =
    fold_left (fun a e => refine_fact P sigma e z a)
      (dominating_edges_projected ctx b) (sigma (Sparse.UVal z)).
Proof.
  unfold refined_fact_projected; rewrite refined_fact_projected_c_equation; reflexivity.
Qed.

(** Pointwise reader agreement preserves projected-fold values without function equality. *)
Theorem refined_fact_projected_c_agrees {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c sigma b z :
  (forall u, Cost.value (sigma_c u) = sigma u) ->
  Cost.value (refined_fact_projected_c P ctx sigma_c b z) =
    refined_fact_projected P ctx sigma b z.
Proof.
  intro Hagrees; rewrite refined_fact_projected_c_equation, refined_fact_projected_equation.
  rewrite Hagrees; apply fold_left_agrees; intros a e.
  apply refine_fact_c_agrees; exact Hagrees.
Qed.

(** Projected folds retain the actual projection, initial read and edge callback costs. *)
Theorem refined_fact_projected_cost_equation {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z :
  Cost.ticks (refined_fact_projected_c P ctx sigma_c b z) =
    (Cost.ticks (dominating_edges_projected_c ctx b) + 1 +
      Cost.ticks (sigma_c (Sparse.UVal z)) +
      Cost.ticks (fold_left_c (fun a e => refine_fact_c P sigma_c e z a)
        (dominating_edges_projected ctx b) (Cost.value (sigma_c (Sparse.UVal z)))))%N.
Proof.
  unfold refined_fact_projected_c; autorewrite with galois_cost.
  fold (dominating_edges_projected ctx b); lia.
Qed.

(** Projection retains its charged query before the same linearly bounded fold. *)
Theorem refined_fact_projected_cost {N E V K G A} (P : Sparse.t N E V K G A)
    ctx sigma_c b z k :
  (forall a e, (Cost.ticks (refine_fact_c P sigma_c e z a) <= k)%N) ->
  (Cost.ticks (refined_fact_projected_c P ctx sigma_c b z) <=
    Cost.ticks (dominating_edges_projected_c ctx b) + 1 +
      Cost.ticks (sigma_c (Sparse.UVal z)) +
      N.of_nat (length (dominating_edges_projected ctx b)) * (k + 1))%N.
Proof.
  intro Hbound; rewrite refined_fact_projected_cost_equation.
  pose proof (ticks_fold_left_c_le (fun a e => refine_fact_c P sigma_c e z a) k
    (dominating_edges_projected ctx b) (Cost.value (sigma_c (Sparse.UVal z))) Hbound) as Hfold.
  lia.
Qed.

(** A ready occurrence graph and its supplied exact tree justify duplicate-tolerant refinement. *)
Theorem refined_fact_projected_sound {S O N E V K G A C} (m : semantics S O)
    (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
    (M : ValueSem.t C K G) gam sigma (p : Prepared.t N (E * nat)) tree :
  Prepared.graph p = EdgeProjection.occurrence_graph (Cfg.graph (Ssa.cfg (Sparse.ssa P))) ->
  Prepared.ready p -> Dom.exact p tree ->
  encoding_laws (Ssa.val_enc (Sparse.ssa P)) ->
  ssa_laws m (Sparse.ssa P) sl (ValueSem.eval M) (ValueSem.holds M) ->
  strict_ssa_laws m (Sparse.ssa P) sl -> value_laws (Sparse.dom P) M gam ->
  forall s z c, reachable_state m s ->
  (forall x d, SsaLink.val sl s x = Some d ->
    gamma (lift_bot_gamma gam) (sigma (Sparse.UVal x)) d) ->
  SsaLink.val sl s z = Some c ->
  gamma (lift_bot_gamma gam) (refined_fact_projected P (make_dom_context p tree)
    sigma (Link.point (SsaLink.link sl) s) z) c.
Proof.
  intros Hgraph Hready Htree HE HS HT HD s z c Hreach Hfacts Hz.
  rewrite refined_fact_projected_equation.
  eapply refine_dominating_edges_sound; try eassumption.
  - apply Forall_forall; intros e Hin; rewrite dominating_edges_projected_equation in Hin.
    apply in_map_iff in Hin; destruct Hin as [ei [<- Hin]].
    eapply EdgeProjection.edge_dominance_project.
    + apply EdgeProjection.occurrence_projection.
    + rewrite <- Hgraph; eapply dominating_edges_in_sound; eassumption.
  - apply Hfacts; exact Hz.
Qed.

End SparseRefine.
