(** * Semi-naive batch and index equations

    Ground batches and predicate indexes expose the same tuples through their public memberships.
    For example, extending one predicate leaves every other predicate's relation unchanged.
    Builds on: DatalogSemiNaiveSyntax and public Map, FinSet and relation specifications. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogJoin DatalogJoinProof DatalogJoinPreparedFire DatalogSolve DatalogSemiNaive
  DatalogSemiNaiveSyntax.
Import List.ListNotations Cost.Notations SemiNaive SemiNaiveSyntax.
Local Open Scope nat_scope.

Module SemiNaiveIndex.

(** Ground encodings inherit injectivity from the supplied predicate laws and tuple codec. *)
Theorem ground_encoding_laws {P} (prog : program P) :
  encoding_laws (penc prog) -> encoding_laws (ground_encoding prog).
Proof.
  intro HE; apply pair_encoding_laws; [exact HE | apply tuple_encoding_laws].
Qed.

Lemma mem_of_list {A} (E : encoding A) (HE : encoding_laws E) x xs :
  FinSet.mem E x (FinSet.of_list E xs) = true <-> In x xs.
Proof.
  rewrite FinSet.mem_of_list, existsb_exists; split.
  - intros [y [Hy Heq]]; apply (eqb_true_iff E HE) in Heq; subst y; exact Hy.
  - intro Hx; exists x; split; [exact Hx | apply eqb_refl].
Qed.

Lemma rel_of_equation {P} (prog : program P) db p :
  rel_of prog db p =
    match Map.get (penc prog) p db with Some rel => rel | None => bot relation_lattice end.
Proof.
  apply lookup_equation.
Qed.

Lemma rel_empty {P} (prog : program P) p ts :
  member ts (rel_of prog Map.empty p) = false.
Proof.
  rewrite rel_of_equation, Map.get_empty; apply relation_bot.
Qed.

Lemma relation_add row fresh rel :
  member row (set_add tuple_encoding fresh rel) = true <->
    row = fresh \/ member row rel = true.
Proof.
  unfold member; rewrite set_add_raw, FinSet.mem_add by exact (proj2_sig rel).
  rewrite orb_true_iff, (eqb_true_iff _ tuple_encoding_laws); reflexivity.
Qed.

Lemma add_atoms_equation {P} (prog : program P) xs db :
  add_atoms prog xs db =
    fold_right (fun f acc => Map.set (penc prog) (fst f)
      (set_add tuple_encoding (snd f) (rel_of prog acc (fst f))) acc) db xs.
Proof.
  unfold add_atoms, add_atoms_c; rewrite value_fold_right_c.
  apply f_equal2; [|reflexivity].
  reflexivity.
Qed.

Lemma add_atoms_wf {P} (prog : program P) xs db :
  Map.wf (penc prog) db -> Map.wf (penc prog) (add_atoms prog xs db).
Proof.
  rewrite add_atoms_equation; intro Hdb; induction xs as [|f xs IH];
    cbn [fold_right]; [exact Hdb | apply Map.wf_set, IH].
Qed.

(** A batch extends exactly the listed predicate-tuple pairs and retains all prior members. *)
Theorem add_atoms_exact {P} (prog : program P) (HE : encoding_laws (penc prog)) xs db p ts :
  Map.wf (penc prog) db ->
  (member ts (rel_of prog (add_atoms prog xs db) p) = true <->
    member ts (rel_of prog db p) = true \/ In (p, ts) xs).
Proof.
  intro Hdb; induction xs as [|[q row] xs IH]; [cbn [In]; tauto |].
  rewrite add_atoms_equation; cbn [fold_right fst snd].
  rewrite <- (add_atoms_equation prog xs db).
  rewrite rel_of_equation, Map.get_set by (apply add_atoms_wf, Hdb).
  destruct (BaseEq.eqb_spec (penc prog) HE p q) as [Heq | Hne].
  - subst q; fold (rel_of prog (add_atoms prog xs db) p).
    rewrite relation_add, IH; cbn [In]; intuition congruence.
  - fold (rel_of prog (add_atoms prog xs db) p).
    rewrite IH; cbn [In]; intuition congruence.
Qed.

Lemma current_equation {P} (prog : program P) st k lower acc p :
  current prog st k lower acc p =
    if Nat.eqb (level st p) k then rel_of prog acc p else Cost.value (lower p).
Proof.
  unfold current, current_c; repeat rewrite Cost.value_bind.
  fold (level st p); destruct (Nat.eqb (level st p) k); reflexivity.
Qed.

Lemma tagged_equation {P} (prog : program P) st k lower acc front p side :
  tagged prog st k lower acc front (p, side) =
    if side then rel_of prog front p else current prog st k lower acc p.
Proof.
  destruct side; reflexivity.
Qed.

Lemma prepare_job_equation {P} (prog : program P) env spec :
  Cost.value (prepare_job_c prog env spec) =
    Job (fst spec) (snd spec) (tag_rule (fst spec) (snd spec))
      (Join.prepare (tag_program prog)
        (positive_atoms (body (tag_rule (fst spec) (snd spec)))) env).
Proof.
  reflexivity.
Qed.

Lemma seed_rules_equation {P} (prog : program P) rs lower :
  Cost.value (seed_rules_c prog rs lower) =
    flat_map (fun r => map (fun row => (pred (head r), row))
      (FinSet.elements (set_raw (PreparedFire.fire prog r lower)))) rs.
Proof.
  unfold seed_rules_c; rewrite value_fold_right_c.
  induction rs as [|r rs IH]; cbn [fold_right flat_map]; [reflexivity |].
  repeat rewrite Cost.value_bind; rewrite value_app_c, value_map_c, IH; reflexivity.
Qed.

Definition seed_atoms {P} (prog : program P) facts st lower k :=
  filter (fun f => Nat.eqb (level st (fst f)) k) facts ++
    Cost.value (seed_rules_c prog (fst (classify st k (rules prog))) lower).

Lemma initial_equation {P} (prog : program P) facts st lower k :
  initial prog facts st lower k =
    let known := FinSet.of_list (ground_encoding prog) (seed_atoms prog facts st lower k) in
    let indexed := add_atoms prog (FinSet.elements known) Map.empty in
    State known known indexed indexed
      (map (fun spec => Cost.value
        (prepare_job_c prog (tagged_c prog st k lower indexed indexed) spec))
        (snd (classify st k (rules prog)))).
Proof.
  unfold initial, initial_c; repeat rewrite Cost.value_bind.
  rewrite value_filter_c, value_app_c, value_map_c; reflexivity.
Qed.

(** Initial seeds belong to the selected stratum, including every nonrecursive rule output. *)
Theorem seed_atoms_level {P} (prog : program P) facts st lower k f :
  In f (seed_atoms prog facts st lower k) -> level st (fst f) = k.
Proof.
  unfold seed_atoms; rewrite in_app_iff, seed_rules_equation.
  intros [Hfact | Hrule].
  - apply filter_In in Hfact as [_ Hlevel]; apply Nat.eqb_eq, Hlevel.
  - apply in_flat_map in Hrule as [r [Hr Hrow]].
    apply classify_seeds in Hr as [_ [Hlevel _]].
    apply in_map_iff in Hrow as [row [<- _]]; exact Hlevel.
Qed.

Lemma candidates_equation {P} (prog : program P) st lower k s :
  candidates prog st lower k s =
    FinSet.of_list (ground_encoding prog)
      (flat_map (fun j => map (fun row => (pred (head (source_rule j)), row))
        (FinSet.elements (set_raw
          (Join.fire (tagged_rule j)
            (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j)))))
        (jobs s)).
Proof.
  unfold candidates, candidates_c; rewrite Cost.value_bind.
  apply (f_equal (FinSet.of_list (ground_encoding prog))).
  rewrite value_fold_right_c.
  induction (jobs s) as [|j js IH]; cbn [fold_right flat_map]; [reflexivity |].
  repeat rewrite Cost.value_bind; rewrite value_app_c, value_map_c, IH; reflexivity.
Qed.

Lemma fresh_equation {P} (prog : program P) st lower k s :
  fresh prog st lower k s = FinSet.diff (candidates prog st lower k s) (accumulated s).
Proof.
  reflexivity.
Qed.

Lemma candidates_wf {P} (prog : program P) st lower k s :
  FinSet.wf (ground_encoding prog) (candidates prog st lower k s).
Proof.
  rewrite candidates_equation; apply FinSet.wf_of_list.
Qed.

Lemma fresh_wf {P} (prog : program P) st lower k s :
  FinSet.wf (ground_encoding prog) (accumulated s) ->
  FinSet.wf (ground_encoding prog) (fresh prog st lower k s).
Proof.
  intro Hacc; rewrite fresh_equation; apply FinSet.wf_diff; [apply candidates_wf | exact Hacc].
Qed.

Lemma batch_rows_equation {P} (prog : program P) batch q :
  Cost.value (batch_rows_c prog batch q) =
    FinSet.elements (set_raw (rel_of prog batch (fst q))).
Proof.
  reflexivity.
Qed.

Lemma update_job_equation {P} (prog : program P) batch j :
  Cost.value (update_job_c prog batch j) =
    Job (source_rule j) (pivot j) (tagged_rule j)
      (Join.insert_rows (fun q => Cost.ret (snd q)) (batch_rows_c prog batch) (plan j)).
Proof.
  reflexivity.
Qed.

Lemma advance_equation {P} (prog : program P) s batch :
  advance prog s batch =
    let rows := FinSet.elements batch in
    let indexed := add_atoms prog rows (accumulated_index s) in
    let next_front := add_atoms prog rows Map.empty in
    State (FinSet.union (accumulated s) batch) batch indexed next_front
      (map (fun j => Cost.value (update_job_c prog next_front j)) (jobs s)).
Proof.
  unfold advance, advance_c; repeat rewrite Cost.value_bind; rewrite value_map_c; reflexivity.
Qed.

Lemma step_equation {P} (prog : program P) st lower k s :
  step prog st lower k s =
    if FinSet.is_empty (fresh prog st lower k s) then inr s
    else inl (advance prog s (fresh prog st lower k s)).
Proof.
  unfold step, step_c; repeat rewrite Cost.value_bind.
  fold (@fresh P prog st lower k s).
  fold (FinSet.is_empty (fresh prog st lower k s)).
  destruct (FinSet.is_empty (fresh prog st lower k s)); reflexivity.
Qed.

Lemma plan_ready_ext {Q} bound ps env env' (plan : Join.plan_state Q) :
  (forall q row, member row (Cost.value (env q)) = member row (Cost.value (env' q))) ->
  JoinProof.ready bound ps env plan -> JoinProof.ready bound ps env' plan.
Proof.
  intros Henv [Hshape Hnodes]; split; [exact Hshape |].
  rewrite Forall_forall in Hnodes |- *; intros n Hn.
  destruct (Hnodes n Hn) as [Hwf Hindex]; split; [exact Hwf |].
  intros key row; rewrite Hindex, Henv; reflexivity.
Qed.

End SemiNaiveIndex.
Import SemiNaiveIndex.
