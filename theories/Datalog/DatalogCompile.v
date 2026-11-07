(** * Compilation of one Datalog stratum

    A rule query reads its same-level positives and fires against fixed lower relations.
    For example, a lower negative predicate contributes no query read.
    Builds on: DatalogFire, DatalogStratify and FixpointAnalysis. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseCode.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Module Constraint.

(** A rule identifier retains its head so even an invalid identifier has a total target. *)
Inductive t (P : Type) :=
  | FromRule (i : nat) (h : P)
  | FromFact (p : P).

Arguments FromRule {P}.
Arguments FromFact {P}.

Definition encoding {P} (E : BaseEncoding.encoding P) : BaseEncoding.encoding (t P) :=
  Encoding (fun c =>
    match c with
    | FromRule i h =>
      Cost.step ;;
      let* p := encode_c E h in
      Cost.step ;;
      Cost.map xO (encode_c (codec_enc (pair_codec nat_codec positive_codec)) (i, p))
    | FromFact p => Cost.step ;; Cost.map xI (encode_c E p)
    end).

(** Constructor tags and injective payload encodings give injective constraint keys. *)
Theorem encoding_law {P} (E : BaseEncoding.encoding P) :
  encoding_laws E -> encoding_laws (encoding E).
Proof.
  intro HE; constructor; intros [i h | p] [j h' | p'] Heq; try discriminate.
  - change (xO (encode (codec_enc (pair_codec nat_codec positive_codec)) (i, encode E h)) =
      xO (encode (codec_enc (pair_codec nat_codec positive_codec)) (j, encode E h'))) in Heq.
    apply (f_equal (fun p => match p with xO q => q | _ => xH end)) in Heq.
    change (encode (codec_enc (pair_codec nat_codec positive_codec)) (i, encode E h) =
      encode (codec_enc (pair_codec nat_codec positive_codec)) (j, encode E h')) in Heq.
    apply (encode_injective (codec_laws_injective _
      (pair_codec_laws _ _ nat_codec_laws positive_codec_laws))) in Heq.
    injection Heq as Hi Hh; apply (encode_injective HE) in Hh; subst j h'; reflexivity.
  - change (xI (encode E p) = xI (encode E p')) in Heq.
    apply (f_equal (fun p => match p with xI q => q | _ => xH end)) in Heq.
    change (encode E p = encode E p') in Heq.
    apply (encode_injective HE) in Heq; subst p'; reflexivity.
Qed.

Definition target {P} (c : t P) := match c with FromRule _ h => h | FromFact p => p end.

End Constraint.

Fixpoint rule_at_c {P} (rs : list (rule P)) i : Cost.t (option (rule P)) :=
  Cost.step ;;
  match rs, i with
  | [], _ => Cost.ret None
  | r :: _, 0 => Cost.ret (Some r)
  | _ :: rest, S i' => rule_at_c rest i'
  end.

Definition rule_at {P} rs i := Cost.value (@rule_at_c P rs i).

Lemma rule_at_spec {P} (rs : list (rule P)) i : rule_at rs i = nth_error rs i.
Proof.
  revert i; induction rs as [|r rs IH]; intros [|i]; try reflexivity.
  apply IH.
Qed.

Fixpoint rule_constraints_c {P} (st : stratification P) k i (rs : list (rule P))
    : Cost.t (list (Constraint.t P)) :=
  match rs with
  | [] => Cost.ret []
  | r :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* lev := level_c st (pred (head r)) in
    let* tail := rule_constraints_c st k (S i) rest in
    Cost.ret (if Nat.eqb lev k then Constraint.FromRule i (pred (head r)) :: tail else tail)
  end.

Definition rule_constraints {P} st k i rs := Cost.value (@rule_constraints_c P st k i rs).

Definition stratum_constraints_c {P} (prog : program P) (facts : list (ground_atom P)) st k :=
  let* cs := rule_constraints_c st k 0 (rules prog) in
  let* fs := filter_c (fun f =>
    Cost.step ;; Cost.map (fun n => Nat.eqb n k) (level_c st (fst f))) facts in
  let* ds := map_c (fun f => Cost.ret (Constraint.FromFact (fst f))) fs in
  app_c cs ds.

Definition stratum_constraints {P} prog facts st k :=
  Cost.value (@stratum_constraints_c P prog facts st k).

Definition level_dependencies_c {P} (st : stratification P) k (r : rule P) :=
  let* ps := positive_atoms_c (body r) in
  let* selected := filter_c (fun a =>
    Cost.step ;; Cost.map (fun n => Nat.eqb n k) (level_c st (pred a))) ps in
  map_c (fun a => Cost.ret (pred a)) selected.

Definition level_dependencies {P} st k r := Cost.value (@level_dependencies_c P st k r).

Lemma level_dependencies_equation {P} (st : stratification P) k r :
  level_dependencies st k r =
    map pred (filter (fun a => Nat.eqb (level st (pred a)) k) (positive_atoms (body r))).
Proof.
  unfold level_dependencies, level_dependencies_c; repeat rewrite Cost.value_bind.
  rewrite value_map_c, value_filter_c; reflexivity.
Qed.

Lemma level_dependencies_member {P} (st : stratification P) k r a :
  In (LPos a) (body r) -> level st (pred a) = k ->
  In (pred a) (level_dependencies st k r).
Proof.
  intros Ha Hlevel; rewrite level_dependencies_equation.
  apply in_map, filter_In; split; [apply positive_atoms_spec, Ha |].
  rewrite Hlevel; apply Nat.eqb_refl.
Qed.

(** The read continuation retains the complete encoding and lookup costs. *)
Fixpoint read_value_c {P} (E : encoding P) (ps : list P) (vs : list relation) p
    : Cost.t relation :=
  match ps, vs with
  | q :: qs, v :: rest =>
    Cost.step ;;
    let* same := eqb_c E p q in
    if same then Cost.ret v else read_value_c E qs rest p
  | _, _ => Cost.ret (bot relation_lattice)
  end.

Definition read_value {P} E ps vs p := Cost.value (@read_value_c P E ps vs p).

Lemma read_value_member {P} (E : encoding P) (HE : encoding_laws E) ps s p :
  In p ps -> read_value E ps (map s ps) p = s p.
Proof.
  induction ps as [|q ps IH]; intro Hin; [contradiction |].
  unfold read_value at 1; cbn [read_value_c map]; repeat rewrite Cost.value_bind.
  fold (eqb E p q); destruct (eqb E p q) eqn:Heq.
  - apply (eqb_true_iff _ HE) in Heq; subst q; reflexivity.
  - change (read_value E ps (map s ps) p = s p); apply IH.
    destruct Hin as [Heq' | Hin]; [subst q; rewrite eqb_refl in Heq; discriminate | exact Hin].
Qed.

Lemma read_value_absent {P} (E : encoding P) ps vs p :
  (forall q, In q ps -> eqb E p q = false) ->
  read_value E ps vs p = bot relation_lattice.
Proof.
  revert vs; induction ps as [|q ps IH]; intros [|v vs] Hout; try reflexivity.
  unfold read_value at 1; cbn [read_value_c]; repeat rewrite Cost.value_bind.
  fold (eqb E p q); rewrite Hout by now left.
  apply IH; intros a Ha; apply Hout; now right.
Qed.

Definition stratum_env_c {P} (prog : program P) (st : stratification P)
    (lower : P -> Cost.t relation) k ds vs p :=
  Cost.step ;;
  let* lev := level_c st p in
  if Nat.eqb lev k then read_value_c (penc prog) ds vs p
  else Cost.step ;; lower p.

Definition stratum_env {P} prog st lower k ds vs p :=
  Cost.value (@stratum_env_c P prog st lower k ds vs p).

Lemma stratum_env_equation {P} (prog : program P) st lower k ds vs p :
  stratum_env prog st lower k ds vs p =
    if Nat.eqb (level st p) k then read_value (penc prog) ds vs p
    else Cost.value (lower p).
Proof.
  unfold stratum_env, stratum_env_c; repeat rewrite Cost.value_bind.
  fold (level st p); destruct (Nat.eqb (level st p) k); reflexivity.
Qed.

Definition facts_at_c {P} (prog : program P) (facts : list (ground_atom P)) p :=
  let* selected := filter_c (fun f => eqb_c (penc prog) p (fst f)) facts in
  let* tuples := map_c (fun f => Cost.ret (snd f)) selected in
  set_of_list_c tuple_encoding tuples.

Definition facts_at {P} prog facts p := Cost.value (@facts_at_c P prog facts p).

Lemma facts_at_exact {P} (prog : program P) (HE : encoding_laws (penc prog)) facts p ts :
  member ts (facts_at prog facts p) = true <-> In (p, ts) facts.
Proof.
  unfold facts_at, facts_at_c; repeat rewrite Cost.value_bind.
  rewrite value_map_c, value_filter_c.
  change (member ts (set_of_list tuple_encoding
    (map snd (filter (fun f => eqb (penc prog) p (fst f)) facts))) = true <->
    In (p, ts) facts).
  rewrite relation_of_list, in_map_iff; split.
  - intros [[q us] [Heq Hin]]; cbn in Heq; subst us.
    apply filter_In in Hin as [Hin Hq]; apply (eqb_true_iff _ HE) in Hq.
    cbn in Hq; subst q; exact Hin.
  - intro Hin; exists (p, ts); split; [reflexivity |].
    apply filter_In; split; [exact Hin | apply eqb_refl].
Qed.

Definition stratum_rhs_c {P} (prog : program P) facts st lower k (c : Constraint.t P)
    : Cost.t (Query.t P relation) :=
  match c with
  | Constraint.FromRule i _ =>
    let* found := rule_at_c (rules prog) i in
    match found with
    | None => Cost.ret (Query.Ret (bot relation_lattice))
    | Some r =>
      let* ds := level_dependencies_c st k r in
      ask_all_c ds (fun vs =>
        Cost.map Query.Ret (fire_rule_c prog r (stratum_env_c prog st lower k ds vs)))
    end
  | Constraint.FromFact p => Cost.map Query.Ret (facts_at_c prog facts p)
  end.

(** Preparing the constraint list charges traversal and level callbacks once. *)
Definition stratum_system_c {P} (prog : program P) facts st lower k :=
  let* cs := stratum_constraints_c prog facts st k in
  Cost.ret (System.Make cs
    (fun c => Cost.ret (Constraint.target c))
    (stratum_rhs_c prog facts st lower k)).

Definition stratum_system {P} prog facts st lower k :=
  Cost.value (@stratum_system_c P prog facts st lower k).

Definition stratum_deps_c {P} (prog : program P) st k (c : Constraint.t P) :=
  match c with
  | Constraint.FromRule i _ =>
    let* found := rule_at_c (rules prog) i in
    match found with
    | Some r => level_dependencies_c st k r
    | None => Cost.ret []
    end
  | Constraint.FromFact _ => Cost.ret []
  end.

(** Static summaries contain computational callbacks and no law fields. *)
Definition stratum_static {P} (prog : program P) facts st lower k :
    System.static (stratum_system prog facts st lower k) :=
  System.Static (stratum_deps_c prog st k) (fun _ => Cost.ret []).

Lemma stratum_rhs_equation {P} (prog : program P) facts st lower k c :
  System.rhs (stratum_system prog facts st lower k) c =
  match c with
  | Constraint.FromRule i _ =>
    match rule_at (rules prog) i with
    | None => Query.Ret (bot relation_lattice)
    | Some r =>
      let ds := level_dependencies st k r in
      ask_all ds (fun vs =>
        Cost.map Query.Ret (fire_rule_c prog r (stratum_env_c prog st lower k ds vs)))
    end
  | Constraint.FromFact p => Query.Ret (facts_at prog facts p)
  end.
Proof.
  destruct c as [i h | p]; [|reflexivity].
  change (Cost.value (stratum_rhs_c prog facts st lower k (Constraint.FromRule i h)) =
    match rule_at (rules prog) i with
    | None => Query.Ret (bot relation_lattice)
    | Some r => ask_all (level_dependencies st k r) (fun vs =>
        Cost.map Query.Ret (fire_rule_c prog r
          (stratum_env_c prog st lower k (level_dependencies st k r) vs)))
    end).
  unfold stratum_rhs_c; rewrite Cost.value_bind; fold (@rule_at P (rules prog) i).
  destruct (rule_at (rules prog) i); reflexivity.
Qed.

Lemma stratum_sides_nil {P} (prog : program P) facts st lower k c s :
  Query.sides (System.rhs (stratum_system prog facts st lower k) c) s = [].
Proof.
  rewrite stratum_rhs_equation; destruct c as [i h | p]; [|reflexivity].
  destruct (rule_at (rules prog) i); [|reflexivity].
  rewrite (proj2 (proj2 (ask_all_spec _ _ _))); reflexivity.
Qed.

(** Every compiled read is declared and compiled queries produce no side contributions. *)
Theorem stratum_static_laws {P} (prog : program P) facts st lower k :
  System.static_laws (stratum_static prog facts st lower k).
Proof.
  constructor.
  - intros [i h | p] s; rewrite stratum_rhs_equation; [|apply incl_refl].
    change (incl
      (Query.reads
        (match rule_at (rules prog) i with
         | Some r => ask_all (level_dependencies st k r) (fun vs =>
             Cost.map Query.Ret (fire_rule_c prog r
               (stratum_env_c prog st lower k (level_dependencies st k r) vs)))
         | None => Query.Ret (bot relation_lattice)
         end) s)
      (Cost.value (stratum_deps_c prog st k (Constraint.FromRule i h)))).
    unfold stratum_deps_c; rewrite Cost.value_bind; fold (@rule_at P (rules prog) i).
    destruct (rule_at (rules prog) i) as [r |]; [|apply incl_refl].
    rewrite (proj1 (ask_all_spec _ _ _)).
    change (incl (level_dependencies st k r ++ []) (level_dependencies st k r)).
    rewrite app_nil_r; apply incl_refl.
  - intros c s; rewrite stratum_sides_nil; apply incl_refl.
Qed.

(** Analysis preparation uses the current costed system and a joining flat policy. *)
Definition stratum_analysis_c {P} (prog : program P) facts st lower k :=
  let* sys := stratum_system_c prog facts st lower k in
  Cost.ret (Analysis.Make (penc prog) (Constraint.encoding (penc prog)) relation_lattice sys
    (System.Static (stratum_deps_c prog st k) (fun _ => Cost.ret [])) (Policy.flat P)).

Definition stratum_analysis {P} prog facts st lower k :=
  Cost.value (@stratum_analysis_c P prog facts st lower k).

(** Injective predicate keys supply all separate analysis laws. *)
Theorem stratum_analysis_laws {P} (prog : program P) facts st lower k :
  encoding_laws (penc prog) -> Analysis.laws (stratum_analysis prog facts st lower k).
Proof.
  intro HE; constructor.
  - exact HE.
  - apply Constraint.encoding_law, HE.
  - apply relation_laws.
  - apply stratum_static_laws.
Qed.

(** The observational environment supplies the values selected by an ask_all trace. *)
Definition rule_env {P} (prog : program P) st lower k (s : P -> relation) r :=
  stratum_env_c prog st lower k (level_dependencies st k r)
    (map s (level_dependencies st k r)).

Lemma rule_rhs_eval {P} (prog : program P) facts st lower k s i h r :
  rule_at (rules prog) i = Some r ->
  Query.eval (System.rhs (stratum_system prog facts st lower k) (Constraint.FromRule i h)) s =
    fire_rule prog r (rule_env prog st lower k s r).
Proof.
  intro Hrule; rewrite stratum_rhs_equation, Hrule.
  rewrite (proj1 (proj2 (ask_all_spec _ _ _))); reflexivity.
Qed.

Lemma rule_env_same {P} (prog : program P) (HE : encoding_laws (penc prog))
    st lower k s r a :
  In (LPos a) (body r) -> level st (pred a) = k ->
  Cost.value (rule_env prog st lower k s r (pred a)) = s (pred a).
Proof.
  intros Ha Hlevel.
  change (stratum_env prog st lower k (level_dependencies st k r)
    (map s (level_dependencies st k r)) (pred a) = s (pred a)).
  rewrite stratum_env_equation, Hlevel, Nat.eqb_refl.
  apply read_value_member; [exact HE | apply level_dependencies_member; assumption].
Qed.

Lemma rule_env_lower {P} (prog : program P) st lower k s r p :
  level st p <> k -> Cost.value (rule_env prog st lower k s r p) = Cost.value (lower p).
Proof.
  intro Hne.
  change (stratum_env prog st lower k (level_dependencies st k r)
    (map s (level_dependencies st k r)) p = Cost.value (lower p)).
  rewrite stratum_env_equation; apply Nat.eqb_neq in Hne; rewrite Hne; reflexivity.
Qed.
