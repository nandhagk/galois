(** * Persistent dominator-scoped numbering

    Each dominator child inherits its parent's completed symbol table by value.
    For example, equal expressions in sibling scopes do not reuse one another's leaders.
    Builds on: GraphDomSpec, AnalysesEqualitySignature and AnalysesEqualityRefine. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern
  BaseUnionFind.
From Galois.Lattice Require Import LatticePartition LatticePartitionOps.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityRefine.
Import List.ListNotations Cost.Notations Numbering NumberingSignature.

Local Open Scope nat_scope.

Module NumberingScope.

Section Scopes.
Context {N E V K G : Type} (np : problem N E V K G)
  (HV : encoding_laws (Ssa.val_enc (ssa np))).
Let syntax := ssa np.
Let EV := Ssa.val_enc syntax.
Let EN := Cfg.node_enc (Ssa.cfg syntax).
Let values := Ssa.values syntax.
Let part := partition_t EV.
Let symbols_t := Map.t positive V.

(** A persistent symbol table stores only leaders from the fixed inventory. *)
Definition symbols_wf (symbols : symbols_t) : Prop :=
  Map.wf positive_encoding symbols /\
  forall id leader, Map.get positive_encoding id symbols = Some leader -> In leader values.

Local Lemma symbols_empty : symbols_wf Map.empty.
Proof.
  split; [apply Map.wf_empty|]; intros id leader Hget.
  rewrite Map.get_empty in Hget; discriminate.
Qed.

Local Lemma symbols_set symbols id leader :
  symbols_wf symbols -> In leader values ->
  symbols_wf (Map.set positive_encoding id leader symbols).
Proof.
  intros [Hwf Hrange] Hleader; split; [now apply Map.wf_set|].
  intros key result Hget; rewrite Map.get_set_raw in Hget.
  destruct (eqb positive_encoding key id).
  - injection Hget as <-; exact Hleader.
  - now apply (Hrange key result).
Qed.

(** Joining two listed leaders preserves the internally maintained finite partition support. *)
Theorem union_supported p x y :
  NumberingRefine.supported np p -> In x values -> In y values ->
  NumberingRefine.supported np (partition_union EV HV x y p).
Proof.
  intros [Hp Hsupport] Hx Hy; split.
  - destruct p; [discriminate|contradiction].
  - intros a b Hab; apply partition_union_spec in Hab.
    destruct Hab as [Hold|[[Hax Hyb]|[Hay Hxb]]]; [now apply Hsupport| |].
    + right; split.
      * destruct (Hsupport a x Hax) as [->|[Ha _]]; assumption.
      * destruct (Hsupport y b Hyb) as [<-|[_ Hb]]; assumption.
    + right; split.
      * destruct (Hsupport a y Hay) as [->|[Ha _]]; assumption.
      * destruct (Hsupport x b Hxb) as [<-|[_ Hb]]; assumption.
Qed.

(** A block visit extends its local symbols and threads the global interner and candidate. *)
Record local_state : Type := Local {
  symbols : symbols_t;
  leaders : Map.t V V;
  interned : Intern.t sig_key;
  candidate : part
}.

(** Local states retain the actual Map, interner and partition certificates. *)
Definition local_wf s : Prop :=
  symbols_wf (symbols s) /\
  Map.wf EV (leaders s) /\
  Intern.wf sig_encoding (interned s) /\
  NumberingRefine.supported np (candidate s).

(** Stable source leaders keep symbol keys independent of union-find root choices. *)
Definition leader_class_c table x : Cost.t positive :=
  let* leader := Map.find_or_c EV x x table in
  Cost.step ;; encode_c EV leader.

Definition visit_value_c forms s x : Cost.t local_state :=
  let* key := signature_c np forms (leader_class_c (leaders s)) x in
  let* allocated := Intern.intern_c sig_encoding key (interned s) in
  let* leader := Map.get_c positive_encoding (fst allocated) (symbols s) in
  match leader with
  | Some y =>
    let* assignments := Map.set_c EV x y (leaders s) in
    let* joined := partition_union_c EV HV y x (candidate s) in
    Cost.ret (Local (symbols s) assignments (snd allocated) joined)
  | None =>
    let* table := Map.set_c positive_encoding (fst allocated) x (symbols s) in
    let* assignments := Map.set_c EV x x (leaders s) in
    Cost.ret (Local table assignments (snd allocated) (candidate s))
  end.

Definition visit_value forms s x := Cost.value (visit_value_c forms s x).

(** A value visit uses one complete signature and the returned stable interner ID. *)
Theorem visit_value_equation forms s x :
  visit_value forms s x =
  let allocated := Intern.intern sig_encoding
    (signature np forms (leader_class_c (leaders s)) x) (interned s) in
  match Map.get positive_encoding (fst allocated) (symbols s) with
  | Some y =>
    Local (symbols s) (Map.set EV x y (leaders s))
      (snd allocated) (partition_union EV HV y x (candidate s))
  | None =>
    Local (Map.set positive_encoding (fst allocated) x (symbols s))
      (Map.set EV x x (leaders s)) (snd allocated) (candidate s)
  end.
Proof.
  unfold visit_value, visit_value_c; autorewrite with galois_cost.
  fold (signature np forms (leader_class_c (leaders s)) x).
  fold (Intern.intern sig_encoding
    (signature np forms (leader_class_c (leaders s)) x) (interned s)).
  fold (@Map.get positive V positive_encoding
    (fst (Intern.intern sig_encoding (signature np forms (leader_class_c (leaders s)) x)
      (interned s))) (symbols s)).
  destruct (Map.get positive_encoding
    (fst (Intern.intern sig_encoding (signature np forms (leader_class_c (leaders s)) x)
      (interned s))) (symbols s)); reflexivity.
Qed.

(** Every value visit preserves certificates and leader origins without a caller result premise. *)
Theorem visit_value_wf forms s x :
  local_wf s -> In x values -> local_wf (visit_value forms s x).
Proof.
  intros [Hsymbols [Hleaders [Hintern Hcandidate]]] Hx; rewrite visit_value_equation.
  set (allocated := Intern.intern sig_encoding
    (signature np forms (leader_class_c (leaders s)) x) (interned s)).
  assert (Hallocated : Intern.wf sig_encoding (snd allocated)).
  { apply Intern.intern_wf; [apply sig_encoding_laws|exact Hintern]. }
  cbn zeta.
  destruct (Map.get positive_encoding (fst allocated) (symbols s)) as [y|] eqn:Hget.
  - split; [exact Hsymbols|split; [now apply Map.wf_set|split; [exact Hallocated|]]].
    apply union_supported; [exact Hcandidate| |exact Hx].
    exact (proj2 Hsymbols _ _ Hget).
  - split; [apply symbols_set; assumption|split; [now apply Map.wf_set|split; assumption]].
Qed.

Definition visit_block_c forms xs s : Cost.t local_state :=
  fold_left_c (fun s x => Cost.step ;; visit_value_c forms s x) xs s.

Definition visit_block forms xs s := Cost.value (visit_block_c forms xs s).

(** A block fold preserves origins and forest/interner invariants for its listed definitions. *)
Theorem visit_block_wf forms xs s :
  Forall (fun x => In x values) xs -> local_wf s -> local_wf (visit_block forms xs s).
Proof.
  intros Hxs; unfold visit_block, visit_block_c; rewrite value_fold_left_c.
  change (local_wf s ->
    local_wf (fold_left (fun s x => visit_value forms s x) xs s)).
  revert s; induction Hxs as [|x rest Hx Hrest IH]; intros s Hs; [exact Hs|].
  cbn [fold_left]; apply IH, visit_value_wf; assumption.
Qed.

(** Immutable traversal preparation indexes value homes and dominator children once. *)
Record environment : Type := Environment {
  prepared_graph : Prepared.t N E;
  templates : Map.t V (template V);
  home_table : Index.t N V;
  child_table : Index.t positive (positive * positive)
}.

(** Home buckets retain the finite source inventory from which they were constructed. *)
Definition environment_wf env : Prop :=
  forall b x, In x (Index.find EN b (home_table env)) -> In x values.

Definition block_c env id table assignments dictionary p : Cost.t local_state :=
  let* name := Prepared.name_of_c (prepared_graph env) id in
  let* xs := match name with
    | None => Cost.ret []
    | Some b => Index.find_c EN b (home_table env)
    end in
  visit_block_c (templates env) xs (Local table assignments dictionary p).

Definition block env id table assignments dictionary p :=
  Cost.value (block_c env id table assignments dictionary p).

(** Block processing reads its prepared home bucket and inherits the supplied parent scope. *)
Theorem block_equation env id table assignments dictionary p :
  block env id table assignments dictionary p =
  visit_block (templates env)
    (match Prepared.name_of (prepared_graph env) id with
     | None => []
     | Some b => Index.find EN b (home_table env)
     end) (Local table assignments dictionary p).
Proof.
  unfold block, block_c; rewrite Cost.value_bind.
  fold (Prepared.name_of (prepared_graph env) id).
  destruct (Prepared.name_of (prepared_graph env) id); reflexivity.
Qed.

(** A prepared block preserves all local certificates and leader origins. *)
Theorem block_wf env id table assignments dictionary p :
  environment_wf env -> local_wf (Local table assignments dictionary p) ->
  local_wf (block env id table assignments dictionary p).
Proof.
  intros Henv Hlocal; rewrite block_equation; apply visit_block_wf; [|exact Hlocal].
  destruct (Prepared.name_of (prepared_graph env) id) as [b|]; [|constructor].
  apply Forall_forall; intros x Hx; exact (Henv b x Hx).
Qed.

Definition task := (positive * symbols_t)%type.

(** Each pending child carries a persistent snapshot of its parent's completed symbols. *)
Record walk_state : Type := Walk {
  todo : list task;
  seen : FinSet.t positive;
  assignments : Map.t V V;
  dictionary : Intern.t sig_key;
  partition : part
}.

Definition walk_wf s : Prop :=
  Forall (fun entry => symbols_wf (snd entry)) (todo s) /\
  FinSet.wf positive_encoding (seen s) /\
  Map.wf EV (assignments s) /\
  Intern.wf sig_encoding (dictionary s) /\
  NumberingRefine.supported np (partition s).

Definition walk_step_c env s : Cost.t (walk_state + walk_state) :=
  match todo s with
  | [] => Cost.ret (inr s)
  | (id, table) :: rest =>
    let* visited := FinSet.mem_c positive_encoding id (seen s) in
    if visited then Cost.ret (inl
      (Walk rest (seen s) (assignments s) (dictionary s) (partition s)))
    else
      let* finished := block_c env id table (assignments s) (dictionary s) (partition s) in
      let* children := Index.find_c positive_encoding id (child_table env) in
      let* tasks := map_c (fun edge => Cost.ret (fst edge, symbols finished)) children in
      let* pending := app_c tasks rest in
      let* marked := FinSet.add_c positive_encoding id (seen s) in
      Cost.ret (inl
        (Walk pending marked (leaders finished) (interned finished) (candidate finished)))
  end.

(** The traversal equation preserves child order and snapshots the same completed parent table. *)
Theorem walk_step_equation env s :
  Cost.value (walk_step_c env s) =
  match todo s with
  | [] => inr s
  | (id, table) :: rest =>
    if FinSet.mem positive_encoding id (seen s)
    then inl (Walk rest (seen s) (assignments s) (dictionary s) (partition s))
    else
      let finished := block env id table (assignments s) (dictionary s) (partition s) in
      inl (Walk
        (map (fun edge => (fst edge, symbols finished))
          (Index.find positive_encoding id (child_table env)) ++ rest)
        (FinSet.add positive_encoding id (seen s))
        (leaders finished) (interned finished) (candidate finished))
  end.
Proof.
  unfold walk_step_c; destruct (todo s) as [|[id table] rest]; [reflexivity|].
  autorewrite with galois_cost; fold (FinSet.mem positive_encoding id (seen s)).
  destruct (FinSet.mem positive_encoding id (seen s)); [reflexivity|].
  autorewrite with galois_cost; rewrite ?value_map_c, ?value_app_c; reflexivity.
Qed.

(** Traversal preserves certificates for both continuing and stopped states. *)
Theorem walk_step_wf env s :
  environment_wf env -> walk_wf s ->
  match Cost.value (walk_step_c env s) with
  | inl next => walk_wf next
  | inr final => walk_wf final
  end.
Proof.
  intros Henv [Htasks [Hseen [Hleaders [Hdictionary Hpartition]]]].
  rewrite walk_step_equation.
  destruct (todo s) as [|[id table] rest] eqn:Htodo.
  - split; [rewrite Htodo; exact Htasks|].
    split; [exact Hseen|split; [exact Hleaders|split; [exact Hdictionary|exact Hpartition]]].
  - inversion Htasks as [|entry tail Htable Hrest]; subst.
    destruct (FinSet.mem positive_encoding id (seen s)).
    + split; [exact Hrest|].
      split; [exact Hseen|split; [exact Hleaders|split; [exact Hdictionary|exact Hpartition]]].
    + assert (Hblock : local_wf
        (block env id table (assignments s) (dictionary s) (partition s))).
      { apply block_wf; [exact Henv|].
        split; [exact Htable|split; [exact Hleaders|split; assumption]]. }
      destruct Hblock as [Hsymbols [Hassignments [Hintern Hcandidate]]].
      split.
      * apply Forall_app; split; [|exact Hrest].
        apply Forall_forall; intros entry Hin; apply in_map_iff in Hin as [edge [<- _]].
        exact Hsymbols.
      * split; [now apply FinSet.wf_add|].
        split; [exact Hassignments|split; assumption].
Qed.

(** The generic run relation transports the proved traversal invariant through either outcome. *)
Theorem walk_runs_wf env n start result :
  environment_wf env -> runs (walk_step_c env) n start result -> walk_wf start ->
  match result with
  | inl s => walk_wf s
  | inr s => walk_wf s
  end.
Proof.
  intros Henv Hrun; induction Hrun as [s|n s final Hstop|n s next result Hnext Hrun IH];
    intro Hstart.
  - exact Hstart.
  - pose proof (walk_step_wf env s Henv Hstart) as Hstep; rewrite Hstop in Hstep; exact Hstep.
  - apply IH; pose proof (walk_step_wf env s Henv Hstart) as Hstep.
    rewrite Hnext in Hstep; exact Hstep.
Qed.

(** The discrete seed is reached and supports no non-reflexive equality. *)
Definition discrete : part := Some (exist _ UnionFind.make (UnionFind.wf_make EV)).

Theorem discrete_supported : NumberingRefine.supported np discrete.
Proof.
  split; [discriminate|]; intros x y Heq; left.
  apply UnionFind.make_equiv in Heq; exact Heq.
Qed.

Definition initial roots : walk_state :=
  Walk (map (fun id => (id, Map.empty)) roots) FinSet.empty Map.empty Intern.empty discrete.

(** Preparation establishes the complete traversal invariant for every root list. *)
Theorem initial_wf roots : walk_wf (initial roots).
Proof.
  split.
  - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin as [id [<- _]].
    apply symbols_empty.
  - split; [apply FinSet.wf_empty|split; [apply Map.wf_empty|]].
    split; [apply Intern.wf_empty|apply discrete_supported].
Qed.

Definition prepare_scope_c (tree : Dom.tree) : Cost.t (environment * list positive * positive) :=
  let* graph := Prepared.prepare_c EN (Cfg.graph (Ssa.cfg syntax)) in
  let* forms := prepare_c np in
  let* homes := Index.group_by_c EN (Ssa.home_c syntax) values in
  let* parents := Map.elements_c (Dom.idom tree) in
  let* children := Index.group_by_c positive_encoding
    (fun edge => Cost.ret (snd edge)) parents in
  let* ids := Prepared.present_c (Prepared.id_of_c graph)
    (Graph.nodes (Cfg.graph (Ssa.cfg syntax))) in
  let* roots := filter_c (fun id =>
    let* parent := Map.get_c positive_encoding id (Dom.idom tree) in
    Cost.ret (match parent with None => true | Some _ => false end)) ids in
  let* root_count := length_c roots in
  let* edge_count := length_c parents in
  Cost.ret (Environment graph forms homes children, roots,
    Pos.of_succ_nat (root_count + edge_count)).

Definition prepare_scope tree := Cost.value (prepare_scope_c tree).

(** The actual preparation supplies the immutable home-bucket invariant. *)
Theorem prepare_scope_wf tree :
  environment_wf (fst (fst (prepare_scope tree))).
Proof.
  intros b x Hx.
  assert (Hhomes : home_table (fst (fst (prepare_scope tree))) =
    Index.group_by EN (Ssa.home syntax) values).
  { unfold prepare_scope, prepare_scope_c; autorewrite with galois_cost.
    rewrite Index.group_by_c_value; reflexivity. }
  rewrite Hhomes, Index.find_group_by, filter_In in Hx; tauto.
Qed.

Definition walk_c env roots fuel := iterate (walk_step_c env) fuel (initial roots).

Definition final_state (result : walk_state + walk_state) :=
  match result with inl s => s | inr s => s end.

(** Both raw traversal outcomes retain the actual finite seed support needed by refinement. *)
Theorem walk_candidate_supported env roots fuel :
  environment_wf env ->
  NumberingRefine.supported np (partition (final_state (Cost.value (walk_c env roots fuel)))).
Proof.
  intro Henv.
  pose proof (walk_runs_wf env _ _ _ Henv
    (iterate_value (walk_step_c env) fuel (initial roots)) (initial_wf roots)) as Hwf.
  unfold walk_c; destruct (Cost.value (iterate (walk_step_c env) fuel (initial roots)));
    exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
Qed.

(** The raw candidate retains traversal exhaustion instead of hiding skipped work. *)
Definition scoped_candidate_c tree : Cost.t (walk_state + walk_state) :=
  let* prepared := prepare_scope_c tree in
  let '(env, roots, fuel) := prepared in walk_c env roots fuel.

(** A report distinguishes a drained scope queue from an exhausted scope budget. *)
Record report : Type := Report {
  scopes_finished : bool;
  result : NumberingRefine.outcome np
}.

Definition dominator_c tree : Cost.t report :=
  let* prepared := prepare_scope_c tree in
  let '(env, roots, fuel) := prepared in
  let* scoped := walk_c env roots fuel in
  let* count := length_c values in
  let* finished := NumberingRefine.finish_c np HV (templates env)
    (partition (final_state scoped)) (Pos.of_succ_nat count) in
  Cost.ret (Report (match scoped with inl _ => false | inr _ => true end) finished).

Definition dominator_numbering tree :=
  NumberingRefine.candidate_of np (result (Cost.value (dominator_c tree))).

(** The checked producer uses the same static template table as the prepared scope traversal. *)
Theorem prepare_scope_templates tree :
  templates (fst (fst (prepare_scope tree))) = prepare np.
Proof.
  unfold prepare_scope, prepare_scope_c; autorewrite with galois_cost; reflexivity.
Qed.

(** The scoped report preserves the raw traversal status and finishes its actual candidate. *)
Theorem dominator_equation tree :
  Cost.value (dominator_c tree) =
  let '(env, roots, fuel) := prepare_scope tree in
  let scoped := Cost.value (walk_c env roots fuel) in
  Report (match scoped with inl _ => false | inr _ => true end)
    (Cost.value (NumberingRefine.finish_c np HV (templates env)
      (partition (final_state scoped)) (Pos.of_succ_nat (length values)))).
Proof.
  unfold dominator_c; rewrite Cost.value_bind; fold (prepare_scope tree).
  destruct (prepare_scope tree) as [[env roots] fuel].
  rewrite !Cost.value_bind, value_length_c; reflexivity.
Qed.

(** Every scoped producer result passes the public checker, including partial raw scope walks. *)
Theorem dominator_checked tree : check np (dominator_numbering tree) = true.
Proof.
  pose proof (prepare_scope_wf tree) as Henv.
  pose proof (prepare_scope_templates tree) as Htemplates.
  destruct (prepare_scope tree) as [[env roots] fuel] eqn:Hprepared.
  cbn [fst] in Henv, Htemplates.
  pose proof (walk_candidate_supported env roots fuel Henv) as Hsupport.
  destruct (NumberingRefine.finish_finishes np HV (templates env)
    (partition (final_state (Cost.value (walk_c env roots fuel)))) Hsupport)
    as [[p rounds] [Hfinish [Hchecked Hrounds]]].
  assert (Hp : p <> None).
  { exact (proj1 (proj1 (NumberingRefine.check_with_spec np HV (templates env) p) Hchecked)). }
  unfold dominator_numbering; rewrite dominator_equation, Hprepared; cbn [result].
  unfold NumberingRefine.finish_c; rewrite Cost.value_map.
  change (check np (NumberingRefine.candidate_of np
    (NumberingRefine.decode np (Cost.value
      (iterate (NumberingRefine.advance_c np HV (templates env))
        (Pos.of_succ_nat (length values))
        (partition (final_state (Cost.value (walk_c env roots fuel))), 0))))) = true).
  eapply eq_trans.
  - exact (f_equal (fun raw => check np
      (NumberingRefine.candidate_of np (NumberingRefine.decode np raw))) Hfinish).
  - destruct p as [u|]; [|contradiction].
    change (check np (Some u) = true).
    rewrite check_with_prepared, <- Htemplates; exact Hchecked.
Qed.

End Scopes.

End NumberingScope.
