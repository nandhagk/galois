(** * Cut-point certificates

    Expansion seeds the stored cut values and reconstructs planned unknowns in order.
    For example, storing a loop head lets its acyclic successors be reconstructed.
    Builds on: FixpointIndex, FixpointEval, FixpointCheck and FixpointCycles. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex FixpointCheck
  FixpointCycles.
Import List.ListNotations Cost.Notations.

(** A certificate stores cut keys, their values and a non-cut reconstruction order. *)
Record cut_certificate (X A : Type) := CutCertificate {
  cuts : FinSet.t X;
  stored : assignment X A;
  plan : list X
}.

Arguments CutCertificate {X A}.
Arguments cuts {X A}.
Arguments stored {X A}.
Arguments plan {X A}.

(** Valid plans cover every output and place each non-cut dependency before its consumers. *)
Definition plan_valid {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) cut order :=
  NoDup order /\ (forall x, In x order -> FinSet.mem EX x cut = false) /\
  (forall c, In c (System.constraints S) -> forall x,
    x = System.target S c \/ In x (side_targets SS c) ->
    FinSet.mem EX x cut = true \/ In x order) /\
  forall before x after, order = before ++ x :: after ->
    forall c, In c (contributors_of EX ix x) -> forall y, In y (deps SS c) ->
    FinSet.mem EX y cut = true \/ In y before \/ contributors_of EX ix y = [].

Section Expansion.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).

Fixpoint prepare_c (xs : list X) (seen : FinSet.t X) : Cost.t (option (FinSet.t X)) :=
  match xs with
  | [] => Cost.ret (Some seen)
  | x :: rest =>
    Cost.step ;;
    let* present := FinSet.mem_c EX x seen in
    if present then Cost.ret None
    else let* next := FinSet.add_c EX x seen in prepare_c rest next
  end.

Definition coverage_c (SS : System.static S) covered :=
  forallb_c (fun c =>
    Cost.step ;;
    let* x := System.target_c S c in
    Cost.step ;;
    let* sides := System.side_targets_c SS c in
    forallb_c (fun y => FinSet.mem_c EX y covered) (x :: sides))
    (System.constraints S).

Fixpoint ordered_c (SS : System.static S) (ix : sys_index X C) xs seen : Cost.t bool :=
  match xs with
  | [] => Cost.ret true
  | x :: rest =>
    Cost.step ;;
    let* cs := contributors_of_c EX ix x in
    let* ready := forallb_c (fun c =>
      Cost.step ;;
      let* reads := System.deps_c SS c in
      forallb_c (fun y =>
        let* present := FinSet.mem_c EX y seen in
        if present then Cost.ret true
        else let* contributors := contributors_of_c EX ix y in
          Cost.ret (match contributors with [] => true | _ :: _ => false end)) reads) cs in
    if ready then let* next := FinSet.add_c EX x seen in ordered_c SS ix rest next
    else Cost.ret false
  end.

Definition check_plan_c (SS : System.static S) ix (cert : cut_certificate X A) :=
  let* prepared := prepare_c (plan cert) (cuts cert) in
  match prepared with
  | None => Cost.ret false
  | Some covered =>
    let* covers := coverage_c SS covered in
    if covers then ordered_c SS ix (plan cert) (cuts cert) else Cost.ret false
  end.

Fixpoint seed_c (xs : list X) (values : assignment X A) : Cost.t (assignment X A) :=
  match xs with
  | [] => Cost.ret Map.empty
  | x :: rest =>
    Cost.step ;;
    let* tail := seed_c rest values in
    let* value := lookup_c EX L values x in Map.set_c EX x value tail
  end.

(** Gathering freezes query reads for one planned key and applies only its outputs. *)
Fixpoint gather_c (x : X) cs (input current : assignment X A) : Cost.t (assignment X A) :=
  match cs with
  | [] => Cost.ret current
  | c :: rest =>
    Cost.step ;;
    let* r := Eval.outputs_c S (lookup_c EX L input) c in
    let* selected := filter_c (fun xa => eqb_c EX (fst xa) x) (fst r) in
    let* next := Update.apply_c EX L (join_c L) selected current in
    gather_c x rest input (fst next)
  end.

Fixpoint compute_c (ix : sys_index X C) xs (current : assignment X A)
    : Cost.t (assignment X A) :=
  match xs with
  | [] => Cost.ret current
  | x :: rest =>
    Cost.step ;;
    let* cs := contributors_of_c EX ix x in
    let* next := gather_c x cs current current in compute_c ix rest next
  end.

(** Expansion validates its plan and independently checks the reconstructed full assignment. *)
Definition expand_c (SS : System.static S) ix (cert : cut_certificate X A)
    : Cost.t (option (assignment X A)) :=
  let* valid := check_plan_c SS ix cert in
  if valid then
    let* xs := FinSet.elements_c (cuts cert) in
    let* initial := seed_c xs (stored cert) in
    let* candidate := compute_c ix (plan cert) initial in
    let* accepted := check_post_c L S (lookup_c EX L candidate) in
    Cost.ret (if accepted then Some candidate else None)
  else Cost.ret None.

Definition expand SS ix cert := Cost.value (expand_c SS ix cert).

(** An accepted expansion is a full post-solution, independently of index or plan trust. *)
Theorem expand_post_sound SS ix cert m :
  expand SS ix cert = Some m -> post_solution L S (lookup EX L m).
Proof.
  unfold expand, expand_c; autorewrite with galois_cost.
  intro Hexpand.
  destruct (Cost.value (check_plan_c SS ix cert)) eqn:Hplan; [|discriminate].
  autorewrite with galois_cost in Hexpand.
  fold (FinSet.elements (cuts cert)) in Hexpand.
  remember (Cost.value (compute_c ix (plan cert)
    (Cost.value (seed_c (FinSet.elements (cuts cert)) (stored cert))))) as candidate
    eqn:Hcandidate in Hexpand.
  destruct (Cost.value (check_post_c L S (lookup_c EX L candidate))) eqn:Hcheck;
    autorewrite with galois_cost in Hexpand; [|discriminate].
  injection Hexpand as <-.
  rewrite (check_post_c_spec L S _ (lookup EX L candidate)) in Hcheck by reflexivity.
  apply check_post_sound, Hcheck.
Qed.

(** Reconstruction costs include plan validation, seeding, gathering and full certification. *)
Theorem expand_cost SS ix cert budget :
  let xs := FinSet.elements (cuts cert) in
  let initial := Cost.value (seed_c xs (stored cert)) in
  let candidate := Cost.value (compute_c ix (plan cert) initial) in
  check_budget L S (lookup_c EX L candidate) budget ->
  (Cost.ticks (expand_c SS ix cert) <=
    Cost.ticks (check_plan_c SS ix cert) +
    Cost.ticks (FinSet.elements_c (cuts cert)) +
    Cost.ticks (seed_c xs (stored cert)) +
    Cost.ticks (compute_c ix (plan cert) initial) + budget)%N.
Proof.
  cbn zeta; intro Hbudget.
  unfold expand_c; rewrite Cost.ticks_bind.
  destruct (Cost.value (check_plan_c SS ix cert)); autorewrite with galois_cost.
  - pose proof (check_post_cost L S _ budget Hbudget) as Hcost.
    fold (FinSet.elements (cuts cert)).
    destruct (Cost.value (check_post_c L S
      (lookup_c EX L (Cost.value (compute_c ix (plan cert)
        (Cost.value (seed_c (FinSet.elements (cuts cert)) (stored cert))))))));
      autorewrite with galois_cost; nia.
  - nia.
Qed.

Section Preservation.
Context (HE : encoding_laws EX).

Local Lemma prepare_disjoint xs seen covered :
  FinSet.wf EX seen -> Cost.value (prepare_c xs seen) = Some covered ->
  forall p, FinSet.mem EX p seen = true -> ~ In p xs.
Proof.
  revert seen; induction xs as [|x xs IH]; intros seen Hwf Hprepared p Hp Hin.
  - contradiction.
  - cbn [prepare_c] in Hprepared; autorewrite with galois_cost in Hprepared.
    fold (FinSet.mem EX x seen) in Hprepared.
    destruct (FinSet.mem EX x seen) eqn:Hx; [discriminate|].
    autorewrite with galois_cost in Hprepared.
    fold (FinSet.add EX x seen) in Hprepared.
    destruct Hin as [<-|Hin]; [congruence|].
    apply (IH _ (FinSet.wf_add EX x seen Hwf) Hprepared p); [|exact Hin].
    rewrite FinSet.mem_add by exact Hwf; rewrite Hp, orb_true_r; reflexivity.
Qed.

Local Lemma seed_wf xs values : Map.wf EX (Cost.value (seed_c xs values)).
Proof.
  induction xs as [|x xs IH]; [apply Map.wf_empty|].
  cbn [seed_c]; autorewrite with galois_cost.
  change (Map.wf EX (Map.set EX x (lookup EX L values x) (Cost.value (seed_c xs values)))).
  apply Map.wf_set, IH.
Qed.

Local Lemma seed_member xs values p :
  In p xs -> lookup EX L (Cost.value (seed_c xs values)) p = lookup EX L values p.
Proof.
  induction xs as [|x xs IH]; intro Hin; [contradiction|].
  cbn [seed_c]; autorewrite with galois_cost.
  change (lookup EX L (Map.set EX x (lookup EX L values x)
    (Cost.value (seed_c xs values))) p = lookup EX L values p).
  rewrite lookup_equation, Map.get_set by apply seed_wf.
  destruct (eqb EX p x) eqn:Hpx.
  - apply (eqb_true_iff EX HE) in Hpx; now subst p.
  - destruct Hin as [<-|Hin]; [rewrite eqb_refl in Hpx; discriminate|].
    change (lookup EX L (Cost.value (seed_c xs values)) p = lookup EX L values p).
    apply IH, Hin.
Qed.

Local Lemma gather_wf x cs input current :
  Map.wf EX current -> Map.wf EX (Cost.value (gather_c x cs input current)).
Proof.
  revert current; induction cs as [|c cs IH]; intros current Hwf; [exact Hwf|].
  cbn [gather_c]; autorewrite with galois_cost.
  apply IH, Update.apply_wf, Hwf.
Qed.

Local Lemma gather_preserves x cs input current p :
  Map.wf EX current -> p <> x ->
  lookup EX L (Cost.value (gather_c x cs input current)) p = lookup EX L current p.
Proof.
  revert current; induction cs as [|c cs IH]; intros current Hwf Hne; [reflexivity|].
  cbn [gather_c]; autorewrite with galois_cost.
  rewrite IH by (assumption || apply Update.apply_wf, Hwf).
  apply (Update.apply_preserves EX HE L); [exact Hwf|].
  intros y b Hin; rewrite ?value_filter_c in Hin.
  apply filter_In in Hin as [_ Heq]; cbn [fst] in Heq.
  change (eqb EX y x = true) in Heq.
  apply (eqb_true_iff EX HE) in Heq; now subst y.
Qed.

Local Lemma compute_wf ix xs current :
  Map.wf EX current -> Map.wf EX (Cost.value (compute_c ix xs current)).
Proof.
  revert current; induction xs as [|x xs IH]; intros current Hwf; [exact Hwf|].
  cbn [compute_c]; autorewrite with galois_cost; apply IH, gather_wf, Hwf.
Qed.

Local Lemma compute_preserves ix xs current p :
  Map.wf EX current -> ~ In p xs ->
  lookup EX L (Cost.value (compute_c ix xs current)) p = lookup EX L current p.
Proof.
  revert current; induction xs as [|x xs IH]; intros current Hwf Houtside; [reflexivity|].
  cbn [compute_c]; autorewrite with galois_cost.
  rewrite IH; [apply gather_preserves|apply gather_wf, Hwf|].
  - exact Hwf.
  - intro Heq; subst p; apply Houtside; now left.
  - intro Hin; apply Houtside; now right.
Qed.

(** Accepted expansion preserves the exact stored values at every cut key. *)
Theorem expand_preserves SS ix cert m :
  FinSet.wf EX (cuts cert) -> expand SS ix cert = Some m ->
  forall p, FinSet.mem EX p (cuts cert) = true ->
    lookup EX L m p = lookup EX L (stored cert) p.
Proof.
  intros Hwf; unfold expand, expand_c; autorewrite with galois_cost; intro Hexpand.
  destruct (Cost.value (check_plan_c SS ix cert)) eqn:Hplan; [|discriminate].
  assert (Hdisjoint : forall p, FinSet.mem EX p (cuts cert) = true -> ~ In p (plan cert)).
  { unfold check_plan_c in Hplan; rewrite Cost.value_bind in Hplan.
    destruct (Cost.value (prepare_c (plan cert) (cuts cert))) as [covered|] eqn:Hprepared;
      [|discriminate].
    exact (prepare_disjoint _ _ _ Hwf Hprepared). }
  autorewrite with galois_cost in Hexpand; fold (FinSet.elements (cuts cert)) in Hexpand.
  remember (Cost.value (compute_c ix (plan cert)
    (Cost.value (seed_c (FinSet.elements (cuts cert)) (stored cert))))) as candidate
    eqn:Hcandidate in Hexpand.
  destruct (Cost.value (check_post_c L S (lookup_c EX L candidate)));
    autorewrite with galois_cost in Hexpand; [|discriminate].
  injection Hexpand as <-; intros p Hp; rewrite Hcandidate.
  rewrite compute_preserves by (apply seed_wf || apply Hdisjoint, Hp).
  apply seed_member, (FinSet.elements_spec EX HE p _ Hwf), Hp.
Qed.

End Preservation.

(** Accepted cut expansion is a full post-solution and retains all stored cut values. *)
Theorem expand_sound (HE : encoding_laws EX) SS ix cert m :
  FinSet.wf EX (cuts cert) -> expand SS ix cert = Some m ->
  post_solution L S (lookup EX L m) /\
  forall p, FinSet.mem EX p (cuts cert) = true ->
    lookup EX L m p = lookup EX L (stored cert) p.
Proof.
  intros Hwf Hexpand; split.
  - exact (expand_post_sound SS ix cert m Hexpand).
  - exact (expand_preserves HE SS ix cert m Hwf Hexpand).
Qed.

End Expansion.

Arguments expand_c {X C A} EX L S SS ix cert : simpl never.
Arguments expand {X C A} EX L S SS ix cert : simpl never.
