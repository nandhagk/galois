(** * Expression SSA inputs and positional substitution

    A PRE context carries computational presentations and supplied graph preparations.
    For example, parallel incoming edges read separate argument lists at the same block.
    Builds on: ProgramSsaPoints, FrameworkBitvector, GraphPrepared and GraphDomSpec. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseRel.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Framework Require Import FrameworkBitvector.
Import List.ListNotations Cost.Notations.

Module Pre.

(** The client supplies syntax readers without semantic or termination evidence. *)
Record client (B BE N E V K G C U : Type) := Client {
  points : SsaPoints.t B BE N E V;
  ssa : Ssa.t B BE V K G;
  expr : Bitvector.t N E U;
  pure_c : U -> Cost.t bool;
  recomputed_c : E -> Cost.t (option U);
  seeds : list U;
  values : list V;
  shape_c : U -> Cost.t positive;
  operands_c : U -> Cost.t (list V);
  eval : U -> (V -> option C) -> option C;
  translate_c : BE -> U -> Cost.t (option U);
  initial_c : U -> Cost.t bool;
  exit_point_c : N -> Cost.t bool
}.
Arguments Client {B BE N E V K G C U}.
Arguments points {B BE N E V K G C U}.
Arguments ssa {B BE N E V K G C U}.
Arguments expr {B BE N E V K G C U}.
Arguments pure_c {B BE N E V K G C U}.
Arguments recomputed_c {B BE N E V K G C U}.
Arguments seeds {B BE N E V K G C U}.
Arguments values {B BE N E V K G C U}.
Arguments shape_c {B BE N E V K G C U}.
Arguments operands_c {B BE N E V K G C U}.
Arguments eval {B BE N E V K G C U}.
Arguments translate_c {B BE N E V K G C U}.
Arguments initial_c {B BE N E V K G C U}.
Arguments exit_point_c {B BE N E V K G C U}.

(** The dictionaries are data and their injectivity belongs to the separate laws. *)
Record encs (B BE N E V U : Type) := Encs {
  eb : encoding B;
  ebe : encoding BE;
  en : encoding N;
  ee : encoding E;
  ev : encoding V;
  eu : encoding U
}.
Arguments Encs {B BE N E V U}.
Arguments eb {B BE N E V U}.
Arguments ebe {B BE N E V U}.
Arguments en {B BE N E V U}.
Arguments ee {B BE N E V U}.
Arguments ev {B BE N E V U}.
Arguments eu {B BE N E V U}.

(** The caller supplies both preparations and the block dominator tree. *)
Record ctx (B BE N E V K G C U : Type) := Context {
  input : client B BE N E V K G C U;
  keys : encs B BE N E V U;
  blocks : Prepared.t B BE;
  point_graph : Prepared.t N E;
  dom : Dom.tree
}.
Arguments Context {B BE N E V K G C U}.
Arguments input {B BE N E V K G C U}.
Arguments keys {B BE N E V K G C U}.
Arguments blocks {B BE N E V K G C U}.
Arguments point_graph {B BE N E V K G C U}.
Arguments dom {B BE N E V K G C U}.

Section Context.
Context {B BE N E V K G C U : Type}.
Variable c : ctx B BE N E V K G C U.

Definition pure u := Cost.value (pure_c (input c) u).
Definition recomputed e := Cost.value (recomputed_c (input c) e).
Definition shape u := Cost.value (shape_c (input c) u).
Definition operands u := Cost.value (operands_c (input c) u).
Definition translate be u := Cost.value (translate_c (input c) be u).
Definition initial u := Cost.value (initial_c (input c) u).
Definition exit_point n := Cost.value (exit_point_c (input c) n).
Definition block_cfg := SsaPoints.block_cfg (points (input c)).
Definition point_cfg := Vars.cfg (SsaPoints.point_model (points (input c))).
Definition bg := Cfg.graph block_cfg.
Definition pg := Cfg.graph point_cfg.

(** Translation steps retain the listed incoming edge identity. *)
Definition family_step u v : Prop :=
  exists be, In be (Cfg.edges block_cfg) /\ translate be u = Some v.

(** The shared family predicate is the least finite translation closure of the seeds. *)
Definition family u : Prop :=
  exists seed, In seed (seeds (input c)) /\ Rel.star family_step seed u.

(** Every supplied seed belongs to the translation family. *)
Theorem family_seed u :
  In u (seeds (input c)) -> family u.
Proof.
  intro Hu; exists u; split; [exact Hu|constructor].
Qed.

(** A listed successful translation extends the same least family. *)
Theorem family_translate {u be v} :
  family u -> In be (Cfg.edges block_cfg) -> translate be u = Some v -> family v.
Proof.
  intros [seed [Hseed Hpath]] Hbe Htranslate.
  exists seed; split; [exact Hseed|].
  eapply Rel.star_trans; [exact Hpath|].
  econstructor; [exists be; split; eassumption|constructor].
Qed.

(** Any predicate containing the seeds and closed under translation contains the family. *)
Theorem family_induction (P : U -> Prop) :
  (forall u, In u (seeds (input c)) -> P u) ->
  (forall u be v, P u -> In be (Cfg.edges block_cfg) ->
    translate be u = Some v -> P v) ->
  forall u, family u -> P u.
Proof.
  intros Hseed Hstep u [seed [Hin Hpath]].
  eapply Rel.star_invariant; [|exact Hpath|apply Hseed; exact Hin].
  intros x y Hx [be [Hbe Htranslate]]; eapply Hstep; eassumption.
Qed.

(** Pairing stops at the shorter input and charges each visited pair. *)
Fixpoint zip_c {X Y} (xs : list X) (ys : list Y) : Cost.t (list (X * Y)) :=
  match xs, ys with
  | x :: xs, y :: ys =>
    Cost.step ;;
    let* rest := zip_c xs ys in Cost.ret ((x, y) :: rest)
  | _, _ => Cost.ret []
  end.

(** Charged positional pairing agrees with the standard simultaneous assignment list. *)
Theorem zip_value {X Y} (xs : list X) (ys : list Y) :
  Cost.value (zip_c xs ys) = combine xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; [reflexivity|reflexivity|reflexivity|].
  cbn [zip_c combine]; autorewrite with galois_cost; rewrite IH; reflexivity.
Qed.

Definition substitution_c be :=
  Cost.step ;;
  let* b := Graph.target_c bg be in
  Cost.step ;;
  let* ps := SsaPoints.block_params_c (points (input c)) b in
  Cost.step ;;
  let* args := SsaPoints.block_edge_args_c (points (input c)) be in
  let* pairs := zip_c ps args in
  Map.of_list_c (ev (keys c)) pairs.

Definition substitution be := Cost.value (substitution_c be).

(** Substitution maps target parameters to arguments from this particular incoming edge. *)
Theorem substitution_equation be :
  substitution be = Map.of_list (ev (keys c))
    (combine (SsaPoints.block_params (points (input c)) (Graph.target bg be))
      (SsaPoints.block_edge_args (points (input c)) be)).
Proof.
  unfold substitution, substitution_c; autorewrite with galois_cost.
  rewrite zip_value; reflexivity.
Qed.

(** One prepared substitution can serve every operand of a translated expression. *)
Definition substitute_c (table : Map.t V V) x :=
  Map.find_or_c (ev (keys c)) x x table.

Definition substitute table x := Cost.value (substitute_c table x).
Definition phi_operand be x := substitute (substitution be) x.
Definition phi_env be (env : V -> option C) x := env (phi_operand be x).

Definition killed_c e u :=
  Cost.step ;;
  let* xs := Bitvector.kill_c (expr (input c)) e in
  existsb_c (eqb_c (eu (keys c)) u) xs.
Definition killed e u := Cost.value (killed_c e u).

(** Gen/kill membership uses the context dictionary and retains the ordered source list. *)
Theorem killed_equation e u :
  killed e u = existsb (eqb (eu (keys c)) u) (Bitvector.kill (expr (input c)) e).
Proof.
  unfold killed, killed_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Shape laws bound syntax without assuming any discovery or output correctness result. *)
Record shape_laws : Prop := ShapeLaws {
  params_nodup : forall b, NoDup (SsaPoints.block_params (points (input c)) b);
  occurrences_seeded : forall e u, recomputed e = Some u -> In u (seeds (input c));
  initials_in_family : forall u, initial u = true -> family u;
  finite_operands : forall u, family u -> incl (operands u) (values (input c));
  shape_identity : forall u v, family u -> family v ->
    shape u = shape v -> operands u = operands v -> u = v;
  shape_arity : forall u v, family u -> family v ->
    shape u = shape v -> length (operands u) = length (operands v);
  closed_translation : forall be u, In be (Cfg.edges block_cfg) -> family u ->
    exists v, translate be u = Some v;
  translation_shape : forall be u v, family u -> translate be u = Some v ->
    shape v = shape u;
  translation_operands : forall be u v, family u -> In be (Cfg.edges block_cfg) ->
    translate be u = Some v -> operands v = map (phi_operand be) (operands u);
  translation_pure : forall be u v, pure u = true -> translate be u = Some v ->
    pure v = true
}.

(** Graph laws certify source correspondence and the supplied preparations and tree. *)
Record graph_laws : Prop := GraphLaws {
  eb_laws : encoding_laws (eb (keys c));
  ebe_laws : encoding_laws (ebe (keys c));
  en_laws : encoding_laws (en (keys c));
  ee_laws : encoding_laws (ee (keys c));
  ev_laws : encoding_laws (ev (keys c));
  eu_laws : encoding_laws (eu (keys c));
  point_laws : ssa_point_laws (points (input c));
  strict_points : reachable_point_ssa (points (input c));
  ssa_block_graph : bg = Cfg.graph (Ssa.cfg (ssa (input c)));
  expression_point_graph : pg = Cfg.graph (Bitvector.cfg (expr (input c)));
  blocks_source : Prepared.graph (blocks c) = bg;
  points_source : Prepared.graph (point_graph c) = pg;
  blocks_ready : Prepared.ready (blocks c);
  points_ready : Prepared.ready (point_graph c);
  tree_exact : Dom.exact (blocks c) (dom c);
  reachable_blocks : forall b, In b (Graph.nodes bg) -> reachable bg b;
  reachable_points : forall n, In n (Graph.nodes pg) -> reachable pg n;
  entry_position : exists b n, Graph.entries bg = [b] /\ Graph.entries pg = [n] /\
    nth_error (SsaPoints.points_in_block (points (input c)) b) 0 = Some n;
  entry_no_incoming : forall b be, In b (Graph.entries bg) ->
    In be (Cfg.edges block_cfg) -> Graph.target bg be <> b
}.

(** Kill laws connect expression changes to static SSA definition occurrences. *)
Record kill_laws : Prop := KillLaws {
  kill_operand : forall e u, In e (Cfg.edges point_cfg) ->
    family u -> killed e u = true ->
    exists x, In x (operands u) /\
      In x (edge_def (SsaPoints.point_model (points (input c))) e);
  def_home : forall e x, In e (Cfg.edges point_cfg) ->
    In x (edge_def (SsaPoints.point_model (points (input c))) e) ->
    Ssa.home (ssa (input c)) x =
      SsaPoints.block_of_point (points (input c)) (Graph.source pg e);
  cross_no_defs : forall e be, In e (Cfg.edges point_cfg) ->
    SsaPoints.block_edge_of (points (input c)) e = Some be ->
    edge_def (SsaPoints.point_model (points (input c))) e = [];
  real_internal : forall e u, recomputed e = Some u ->
    SsaPoints.block_edge_of (points (input c)) e = None /\
    forall b, e <> SsaPoints.parameter_edge (points (input c)) b
}.

(** Environment laws do not mention concrete machines or assume a cache invariant. *)
Record runtime_laws : Prop := RuntimeLaws {
  operand_support : forall u env1 env2,
    (forall x, In x (operands u) -> env1 x = env2 x) ->
    eval (input c) u env1 = eval (input c) u env2;
  translation_eval : forall be u v env, In be (Cfg.edges block_cfg) -> family u ->
    translate be u = Some v -> eval (input c) u (phi_env be env) = eval (input c) v env
}.

(** All structural obligations belong to one proof-only context certificate. *)
Record laws : Prop := Laws {
  shapes : shape_laws;
  graphs : graph_laws;
  kills : kill_laws;
  runtime : runtime_laws
}.

End Context.

(** Unique-key assignment lists select each pair independently of insertion order. *)
Lemma assignment_member {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (pairs : list (X * Y)) :
  NoDup (map fst pairs) ->
  forall x y, In (x, y) pairs -> Map.get enc x (Map.of_list enc pairs) = Some y.
Proof.
  intro Hnodup; intros x y Hin; rewrite Map.of_list_get.
  assert (Hunique : forall z, In (x, z) pairs -> z = y).
  { induction pairs as [|[a b] rest IH]; [contradiction|].
    inversion Hnodup as [|key keys Hfresh Htail]; subst.
    intros z Hz; cbn [In] in Hin, Hz.
    destruct Hin as [Heq|Hin], Hz as [Heq'|Hz].
    - congruence.
    - inversion Heq; subst a b; exfalso; apply Hfresh; exact (in_map fst _ _ Hz).
    - inversion Heq'; subst a b; exfalso; apply Hfresh; exact (in_map fst _ _ Hin).
    - exact (IH Htail Hin z Hz). }
  clear Hnodup.
  assert (Hfold : forall xs old,
    (forall z, In (x, z) xs -> z = y) ->
    old = Some y \/ In (x, y) xs ->
    fold_left (fun acc kv => if eqb enc x (fst kv) then Some (snd kv) else acc)
      xs old = Some y).
  { induction xs as [|[a b] rest IH]; intros old Hsame Hhit; cbn [fold_left fst snd].
    - destruct Hhit as [Hhit|[]]; exact Hhit.
    - destruct (eqb enc x a) eqn:Hkey.
      + apply (eqb_true_iff enc HE) in Hkey; subst a.
        assert (Hb : b = y) by (apply Hsame; now left).
        subst b; apply IH; [intros z Hz; apply Hsame; now right|now left].
      + apply IH.
        * intros z Hz; apply Hsame; now right.
        * destruct Hhit as [Hhit|[Heq|Hhit]].
          -- now left.
          -- inversion Heq; subst a b; rewrite eqb_refl in Hkey; discriminate.
          -- now right. }
  apply Hfold; [exact Hunique|now right].
Qed.

(** Assignments whose keys omit a query leave that query absent. *)
Lemma assignment_frame {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (pairs : list (X * Y)) :
  forall x, ~ In x (map fst pairs) -> Map.get enc x (Map.of_list enc pairs) = None.
Proof.
  intros x Houtside; rewrite Map.of_list_get.
  assert (Hfold : forall xs : list (X * Y), ~ In x (map fst xs) ->
    fold_left (fun acc kv => if eqb enc x (fst kv) then Some (snd kv) else acc)
      xs None = None).
  { induction xs as [|[a b] rest IH]; intro Hfresh; [reflexivity|].
    cbn [fold_left fst snd]; destruct (eqb enc x a) eqn:Hkey.
    - apply (eqb_true_iff enc HE) in Hkey; subst a; exfalso; apply Hfresh; now left.
    - apply IH; intro Hin; apply Hfresh; now right. }
  apply Hfold; exact Houtside.
Qed.

Local Lemma combine_member {X Y} (xs : list X) (ys : list Y) :
  forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y ->
    In (x, y) (combine xs ys).
Proof.
  revert ys; induction xs as [|a xs IH]; intros [|b ys] [|i] x y Hx Hy;
    cbn in Hx, Hy |- *; try discriminate.
  - inversion Hx; inversion Hy; subst; now left.
  - right; eapply IH; eassumption.
Qed.

Local Lemma combine_keys {X Y} (xs : list X) (ys : list Y) :
  length xs = length ys -> map fst (combine xs ys) = xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlength;
    cbn in Hlength |- *; try discriminate; [reflexivity|].
  f_equal; apply IH; lia.
Qed.

Section SubstitutionLaws.
Context {B BE N E V K G C U : Type}.
Variable c : ctx B BE N E V K G C U.

(** Each parameter reads its positional argument in the same pre-edge environment. *)
Theorem phi_env_parameter :
  laws c ->
  forall be i x y env, In be (Cfg.edges (block_cfg c)) ->
    nth_error (SsaPoints.block_params (points (input c)) (Graph.target (bg c) be)) i =
      Some x ->
    nth_error (SsaPoints.block_edge_args (points (input c)) be) i = Some y ->
    phi_env c be env x = env y.
Proof.
  intros Hlaw be i x y env Hbe Hx Hy.
  unfold phi_env, phi_operand, substitute, substitute_c.
  fold (Map.find_or (ev (keys c)) x x (substitution c be)).
  rewrite Map.find_or_equation, substitution_equation.
  assert (Hnodup : NoDup (map fst
    (combine (SsaPoints.block_params (points (input c)) (Graph.target (bg c) be))
      (SsaPoints.block_edge_args (points (input c)) be)))).
  { rewrite combine_keys.
    + apply (params_nodup c (shapes c Hlaw)).
    + symmetry; exact (phi_args_length (point_laws c (graphs c Hlaw)) be Hbe). }
  rewrite (assignment_member _ (ev_laws c (graphs c Hlaw)) _ Hnodup x y).
  - reflexivity.
  - eapply combine_member; eassumption.
Qed.

(** Simultaneous assignment leaves every nonparameter value unchanged. *)
Theorem phi_env_frame :
  laws c ->
  forall be x env, In be (Cfg.edges (block_cfg c)) ->
    ~ In x (SsaPoints.block_params (points (input c)) (Graph.target (bg c) be)) ->
    phi_env c be env x = env x.
Proof.
  intros Hlaw be x env Hbe Houtside.
  unfold phi_env, phi_operand, substitute, substitute_c.
  fold (Map.find_or (ev (keys c)) x x (substitution c be)).
  rewrite Map.find_or_equation, substitution_equation.
  rewrite (assignment_frame _ (ev_laws c (graphs c Hlaw))).
  - reflexivity.
  - rewrite combine_keys; [exact Houtside|].
    symmetry; exact (phi_args_length (point_laws c (graphs c Hlaw)) be Hbe).
Qed.

(** Operand substitution composes the original environment without sequential updates. *)
Theorem phi_env_substitution be env {x} :
  phi_env c be env x = env (phi_operand c be x).
Proof.
  reflexivity.
Qed.

End SubstitutionLaws.

End Pre.
