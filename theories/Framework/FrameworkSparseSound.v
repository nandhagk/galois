(** * Executable edges and covered SSA values

    Sparse post-solutions cover concrete runs in three layers of named lemmas.
    For example, a taken edge propagates its refined argument into a block parameter.
    Builds on: FrameworkSparseRefine, ProgramSteps and DomainsValue. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeAdjoin.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink
  ProgramSsa ProgramRuns.
From Galois.Domains Require Import DomainsValue.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkRows FrameworkSparse
  FrameworkSparseRefine.
Import List.ListNotations Cost.Notations Sparse.

Module SparseSound.

(** Executability distinguishes fresh unreachable bottom from every reached component fact. *)
Definition executable {A} (a : option A) : bool :=
  match a with Some _ => true | None => false end.

(** Entry bindings originate in entry parameters and satisfy their supplied facts. *)
Definition sparse_entry_ok {S O N E V K G A C} (m : semantics S O)
    (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
    (gam : concretisation A C) : Prop :=
  forall s x c, initial m s -> SsaLink.val sl s x = Some c ->
    exists b i, Ssa.def (ssa P) x = Param b i /\
      In b (Graph.entries (Cfg.graph (Ssa.cfg (ssa P)))) /\
      gamma gam (entry_arg P x) c.

(** * The prepared row interpretation *)

(* This local view describes rows. It never substitutes a different refinement algorithm. *)
Local Definition row {N E V K G A} (P : Sparse.t N E V K G A)
    (c : constraint N E V) : Rows.t (unknown N E V) (option A) :=
  let S := ssa P in
  let D := dom P in
  let graph := Cfg.graph (Ssa.cfg S) in
  match c with
  | CBlockEntry b => Rows.Make (UBlock b) [] (fun _ => Cost.ret (Some (ValueAbs.top D)))
  | CEntryFact v => Rows.Make (UVal v) []
      (fun _ => Cost.step ;; Cost.map Some (entry_arg_c P v))
  | CArbitrary v => Rows.Make (UVal v) [] (fun _ => Cost.ret (Some (ValueAbs.top D)))
  | COp v =>
    match Ssa.def S v with
    | Op k args => Rows.Make (UVal v) (map UVal args) (fun fs =>
        let* values := collect_c fs in
        match values with
        | None => Cost.ret None
        | Some vs => Cost.step ;; Cost.map Some (ValueAbs.op_c D k vs)
        end)
    | _ => Rows.Make (UVal v) [] (fun _ => Cost.ret None)
    end
  | CEdge e =>
    Rows.Make (UEdge e)
      (UBlock (Graph.source graph e) :: map UVal (SparseRefine.dependencies P e))
      (fun fs =>
        match fs with
        | Some _ :: rest =>
          let* refined := refine_c P (SparseRefine.plans P e)
            (SparseRefine.dependencies P e) rest in
          match refined with
          | None => Cost.ret None
          | Some m =>
            let* feasible := feasible_c (Ssa.val_enc S) D (SparseRefine.dependencies P e) m in
            Cost.ret (if feasible then Some (ValueAbs.top D) else None)
          end
        | _ => Cost.ret None
        end)
  | CBlock e => Rows.Make (UBlock (Graph.target graph e)) [UEdge e]
      (fun fs => Cost.ret (match fs with a :: _ => a | _ => None end))
  | CArg e i =>
    match nth_error (Ssa.params S (Graph.target graph e)) i, nth_error (Ssa.args S e) i with
    | Some y, Some z => Rows.Make (UVal y)
        (UEdge e :: map UVal (z :: SparseRefine.dependencies P e)) (fun fs =>
        match fs with
        | Some _ :: rest =>
          let* refined := refine_c P (SparseRefine.plans P e)
            (z :: SparseRefine.dependencies P e) rest in
          match refined with
          | None => Cost.ret None
          | Some m => Map.find_or_c (Ssa.val_enc S) None z m
          end
        | _ => Cost.ret None
        end)
    | _, _ => Rows.Make (UEdge e) [] (fun _ => Cost.ret None)
    end
  end.

Local Lemma value_rows_canonical {N E V K G A} (P : Sparse.t N E V K G A) entries v c r :
  In (c, r) (Cost.value (value_row_c P entries v)) -> r = row P c.
Proof.
  unfold value_row_c; autorewrite with galois_cost.
  fold (Ssa.def (ssa P) v).
  destruct (Ssa.def (ssa P) v) as [k args|b i|] eqn:Hdef.
  - intros [Heq|Hbad]; [|contradiction].
    inversion Heq; subst c r; unfold row; rewrite Hdef.
    rewrite value_map_c; reflexivity.
  - autorewrite with galois_cost.
    fold (FinSet.mem (Cfg.node_enc (Ssa.cfg (ssa P))) b entries).
    destruct (FinSet.mem (Cfg.node_enc (Ssa.cfg (ssa P))) b entries);
      intros Hin; [destruct Hin as [Heq|Hbad]|]; try contradiction.
    inversion Heq; reflexivity.
  - intros [Heq|Hbad]; [inversion Heq; reflexivity|contradiction].
Qed.

Local Lemma edge_rows_equation {N E V K G A} (P : Sparse.t N E V K G A) e :
  Cost.value (edge_rows_c P e) =
    (CEdge e, row P (CEdge e)) :: (CBlock e, row P (CBlock e)) ::
      map (fun i => (CArg e i, row P (CArg e i))) (seq 0 (length (Ssa.args (ssa P) e))).
Proof.
  unfold edge_rows_c; autorewrite with galois_cost.
  rewrite fw_flat_map_value, fw_seq_value.
  fold (Ssa.args (ssa P) e).
  assert (Hplans : map (fun x => Cost.value (guard_plan_c (ssa P) x))
    (Cost.value (Ssa.guards_c (ssa P) e)) = SparseRefine.plans P e).
  { unfold SparseRefine.plans, SparseRefine.plans_c.
    rewrite Cost.value_bind, value_map_c; reflexivity. }
  rewrite Hplans.
  assert (Hdeps : flat_map (fun x => Cost.value (guard_deps_c x))
    (SparseRefine.plans P e) = SparseRefine.dependencies P e).
  { unfold SparseRefine.dependencies, SparseRefine.dependencies_c.
    rewrite Cost.value_bind, fw_flat_map_value; reflexivity. }
  rewrite Hdeps.
  f_equal; f_equal.
  apply map_ext; intro i.
  rewrite !Cost.value_bind, !fw_nth_value.
  fold (Graph.target (Cfg.graph (Ssa.cfg (ssa P))) e).
  fold (Ssa.params (ssa P) (Graph.target (Cfg.graph (Ssa.cfg (ssa P))) e)).
  unfold row.
  destruct (nth_error (Ssa.params (ssa P)
    (Graph.target (Cfg.graph (Ssa.cfg (ssa P))) e)) i) as [y|];
    destruct (nth_error (Ssa.args (ssa P) e) i) as [z|];
    autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma prepare_equation {N E V K G A} (P : Sparse.t N E V K G A) :
  Cost.value (prepare_c P) =
    map (fun b => (CBlockEntry b, row P (CBlockEntry b)))
      (Graph.entries (Cfg.graph (Ssa.cfg (ssa P)))) ++
    flat_map (fun v => Cost.value (value_row_c P
      (FinSet.of_list (Cfg.node_enc (Ssa.cfg (ssa P)))
        (Graph.entries (Cfg.graph (Ssa.cfg (ssa P))))) v)) (Ssa.values (ssa P)) ++
    flat_map (fun e => Cost.value (edge_rows_c P e)) (Cfg.edges (Ssa.cfg (ssa P))).
Proof.
  unfold prepare_c; autorewrite with galois_cost.
  rewrite !fw_flat_map_value, fw_edges_value; reflexivity.
Qed.

Local Lemma prepared_canonical {N E V K G A} (P : Sparse.t N E V K G A) c r :
  In (c, r) (Cost.value (prepare_c P)) -> r = row P c.
Proof.
  rewrite prepare_equation; intro Hin; apply in_app_or in Hin.
  destruct Hin as [Hin|Hin].
  - apply in_map_iff in Hin; destruct Hin as [b [Heq _]]; inversion Heq; reflexivity.
  - apply in_app_or in Hin; destruct Hin as [Hin|Hin]; apply in_flat_map in Hin.
    + destruct Hin as [v [_ Hin]]; eapply value_rows_canonical; exact Hin.
    + destruct Hin as [e [_ Hin]]; rewrite edge_rows_equation in Hin.
      destruct Hin as [Heq|[Heq|Hin]]; try (inversion Heq; reflexivity).
      apply in_map_iff in Hin; destruct Hin as [i [Heq _]]; inversion Heq; reflexivity.
Qed.

Local Lemma table_lookup {X Y} (enc : encoding X) (HE : encoding_laws enc)
    (f : X -> Y) pairs c r :
  (forall c r, In (c, r) pairs -> r = f c) -> In (c, r) pairs ->
  Map.get enc c (Map.of_list enc pairs) = Some (f c).
Proof.
  intros Hcanonical Hin; rewrite Map.of_list_get.
  assert (Hfold : forall ps old,
    (forall k v, In (k, v) ps -> v = f k) ->
    (In (c, r) ps \/ old = Some (f c)) ->
    fold_left (fun old kv =>
      if eqb enc c (fst kv) then Some (snd kv) else old) ps old = Some (f c)).
  { intro ps; induction ps as [|[k v] ps IH]; intros old Hps Hpresent.
    - cbn in Hpresent; tauto.
    - cbn [fold_left fst snd]; apply IH.
      + intros a b Hab; apply Hps; right; exact Hab.
      + destruct (eqb enc c k) eqn:Heq.
        * apply (eqb_true_iff enc HE) in Heq; subst k; right.
          f_equal; apply Hps; left; reflexivity.
        * destruct Hpresent as [[Heqpair|Hinps]|Hold].
          -- inversion Heqpair; subst k; rewrite eqb_refl in Heq; discriminate.
          -- left; exact Hinps.
          -- right; exact Hold. }
  apply Hfold; [exact Hcanonical|left; exact Hin].
Qed.

Section Rows.
Context {N E V K G A : Type} (P : Sparse.t N E V K G A) (entry : N)
  (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (ssa P))))
  (HE : encoding_laws (Cfg.edge_enc (Ssa.cfg (ssa P))))
  (HV : encoding_laws (Ssa.val_enc (ssa P))).

Local Lemma listed_row c :
  In c (Sparse.rows P) ->
  Cost.value (get_c P entry (Map.of_list (row_enc P) (Cost.value (prepare_c P))) c) =
    row P c.
Proof.
  unfold Sparse.rows; intro Hin; apply in_map_iff in Hin.
  destruct Hin as [[c' r] [Heq Hin]]; cbn in Heq; subst c'.
  unfold get_c; fold (Map.find_or (row_enc P)
    (Rows.Make (UBlock entry) [] (fun _ => Cost.ret None)) c
    (Map.of_list (row_enc P) (Cost.value (prepare_c P)))).
  rewrite Map.find_or_equation.
  rewrite (table_lookup (row_enc P) (constraint_enc_laws _ _ _ HN HE HV)
    (row P) _ c r (prepared_canonical P) Hin); reflexivity.
Qed.

(** Every listed prepared row contributes its interpreted bound to a post-solution. *)
Theorem sparse_row_bound sigma c :
  post_solution (Analysis.lat (sparse_analysis P entry))
    (Analysis.system (sparse_analysis P entry)) sigma ->
  In c (Sparse.rows P) ->
  leb (lift_bot (ValueAbs.lat (dom P)))
    (Cost.value (Rows.eval_c (row P c) (map sigma (Rows.reads (row P c)))))
    (sigma (Rows.target (row P c))) = true.
Proof.
  intros Hpost Hin.
  assert (Hconstraints : In c (System.constraints
    (Analysis.system (sparse_analysis P entry)))).
  { unfold sparse_analysis, analysis, analysis_c; autorewrite with galois_cost.
    exact Hin. }
  pose proof (proj1 (Hpost c Hconstraints)) as Hbound.
  unfold sparse_analysis, analysis, analysis_c in Hbound; autorewrite with galois_cost in Hbound.
  change (leb (lift_bot (ValueAbs.lat (dom P)))
    (Query.eval (Rows.query (Cost.value (get_c P entry
      (Map.of_list (row_enc P) (Cost.value (prepare_c P))) c))) sigma)
    (sigma (Rows.target (Cost.value (get_c P entry
      (Map.of_list (row_enc P) (Cost.value (prepare_c P))) c)))) = true) in Hbound.
  rewrite listed_row in Hbound by exact Hin.
  rewrite (proj1 (proj2 (Rows.query_spec _ _))) in Hbound; exact Hbound.
Qed.

Local Lemma entry_row b :
  In b (Graph.entries (Cfg.graph (Ssa.cfg (ssa P)))) -> In (CBlockEntry b) (Sparse.rows P).
Proof.
  intro Hb; unfold Sparse.rows; apply in_map_iff; exists (CBlockEntry b, row P (CBlockEntry b)).
  split; [reflexivity|rewrite prepare_equation; apply in_or_app; left].
  apply in_map_iff; exists b; split; [reflexivity|exact Hb].
Qed.

Local Lemma value_row v c r :
  In v (Ssa.values (ssa P)) ->
  In (c, r) (Cost.value (value_row_c P
    (FinSet.of_list (Cfg.node_enc (Ssa.cfg (ssa P)))
      (Graph.entries (Cfg.graph (Ssa.cfg (ssa P))))) v)) ->
  In c (Sparse.rows P).
Proof.
  intros Hv Hr; unfold Sparse.rows; apply in_map_iff; exists (c, r); split; [reflexivity|].
  rewrite prepare_equation; apply in_or_app; right; apply in_or_app; left.
  apply in_flat_map; exists v; split; assumption.
Qed.

Local Lemma edge_row e c :
  In e (Cfg.edges (Ssa.cfg (ssa P))) ->
  In c (CEdge e :: CBlock e :: map (CArg e) (seq 0 (length (Ssa.args (ssa P) e)))) ->
  In c (Sparse.rows P).
Proof.
  intros He Hc; unfold Sparse.rows; apply in_map_iff; exists (c, row P c).
  split; [reflexivity|]; rewrite prepare_equation.
  apply in_or_app; right; apply in_or_app; right; apply in_flat_map; exists e.
  split; [exact He|rewrite edge_rows_equation].
  destruct Hc as [<-|[<-|Hc]]; [left; reflexivity|right; left; reflexivity|].
  apply in_map_iff in Hc; destruct Hc as [i [<- Hi]]; right; right.
  apply in_map_iff; exists i; split; [reflexivity|exact Hi].
Qed.

End Rows.

(** A reached lower bound forces its upper fact to be executable. *)
Theorem reached_upper {A} (L : lattice A) a b :
  leb (lift_bot L) (Some a) b = true -> executable b = true.
Proof.
  rewrite leb_lift_bot; destruct b; [reflexivity|discriminate].
Qed.

Section Soundness.
Context {S O N E V K G A C : Type} (m : semantics S O)
  (P : Sparse.t N E V K G A) (sl : SsaLink.t S O N E V C)
  (M : ValueSem.t C K G) (gam : concretisation A C) (entry : N)
  (sigma : unknown N E V -> option A).
Let SS := ssa P.
Let D := dom P.
Let graph := Cfg.graph (Ssa.cfg SS).
Let lk := SsaLink.link sl.
Let LG := lift_bot_gamma gam.
Let LB := lift_bot (ValueAbs.lat D).
Hypothesis HN : encoding_laws (Cfg.node_enc (Ssa.cfg SS)).
Hypothesis HE : encoding_laws (Cfg.edge_enc (Ssa.cfg SS)).
Hypothesis HV : encoding_laws (Ssa.val_enc SS).
Hypothesis HS : ssa_laws m SS sl (ValueSem.eval M) (ValueSem.holds M).
Hypothesis HD : value_laws D M gam.
Hypothesis Hentry : sparse_entry_ok m P sl gam.
Hypothesis Hpost : post_solution (Analysis.lat (sparse_analysis P entry))
  (Analysis.system (sparse_analysis P entry)) sigma.

(** The value part of the invariant covers every binding in one state. *)
Definition sparse_values_sound s : Prop :=
  forall x c, SsaLink.val sl s x = Some c -> gamma LG (sigma (UVal x)) c.

(** The simultaneous invariant couples executable control with covered bindings. *)
Definition sparse_invariant s : Prop :=
  executable (sigma (UBlock (Link.point lk s))) = true /\ sparse_values_sound s.

Local Lemma gamma_upper a b c :
  leb LB a b = true -> gamma LG a c -> gamma LG b c.
Proof.
  apply (gamma_monotone (lift_bot_gamma_laws _ _ (gamma_ok HD))).
Qed.

Local Lemma bound c :
  In c (Sparse.rows P) ->
  leb LB (Cost.value (Rows.eval_c (row P c) (map sigma (Rows.reads (row P c)))))
    (sigma (Rows.target (row P c))) = true.
Proof.
  apply (sparse_row_bound P entry HN HE HV sigma c Hpost).
Qed.

(** Entry rows mark the concrete initial block executable. *)
Theorem sparse_entry_block s :
  initial m s -> executable (sigma (UBlock (Link.point lk s))) = true.
Proof.
  intro Hs; apply (reached_upper (ValueAbs.lat D) (ValueAbs.top D)).
  apply (bound (CBlockEntry (Link.point lk s))).
  apply entry_row; apply (entry_points (link_ok HS)); exact Hs.
Qed.

(** Entry parameter rows cover all initial bindings. *)
Theorem sparse_initial_value s x c :
  initial m s -> SsaLink.val sl s x = Some c -> gamma LG (sigma (UVal x)) c.
Proof.
  intros Hs Hval; destruct (Hentry s x c Hs Hval) as [b [i [Hdef [Hb Ha]]]].
  assert (Hreach : reachable_state m s).
  { exists s, []; split; [exact Hs|constructor]. }
  assert (Hr : In (CEntryFact x) (Sparse.rows P)).
  { eapply value_row.
    - eapply (coverage HS); eassumption.
    - unfold value_row_c; autorewrite with galois_cost.
      fold SS; fold (Ssa.def SS x); fold SS in Hdef.
      rewrite Hdef; autorewrite with galois_cost.
      fold (FinSet.mem (Cfg.node_enc (Ssa.cfg SS)) b
        (FinSet.of_list (Cfg.node_enc (Ssa.cfg SS)) (Graph.entries graph))).
      assert (Hmem : FinSet.mem (Cfg.node_enc (Ssa.cfg SS)) b
        (FinSet.of_list (Cfg.node_enc (Ssa.cfg SS)) (Graph.entries graph)) = true).
      { rewrite FinSet.mem_of_list; apply existsb_exists; exists b.
        split; [exact Hb|apply eqb_refl]. }
      fold graph.
      fold (FinSet.of_list (Cfg.node_enc (Ssa.cfg SS)) (Graph.entries graph)).
      fold (FinSet.mem (Cfg.node_enc (Ssa.cfg SS)) b
        (FinSet.of_list (Cfg.node_enc (Ssa.cfg SS)) (Graph.entries graph))).
      rewrite Hmem; left; reflexivity. }
  eapply gamma_upper; [exact (bound _ Hr)|exact Ha].
Qed.

(** Initial states satisfy the simultaneous control and value invariant. *)
Theorem sparse_initial_invariant s : initial m s -> sparse_invariant s.
Proof.
  intro Hs; split; [apply sparse_entry_block; exact Hs|].
  intros x c Hval; eapply sparse_initial_value; eassumption.
Qed.

Local Lemma argument_facts s xs cs :
  sparse_values_sound s ->
  Forall2 (fun x c => SsaLink.val sl s x = Some c) xs cs ->
  Forall2 (gamma LG) (map (fun x => sigma (UVal x)) xs) cs.
Proof.
  intros Hfacts Hxs; induction Hxs as [|x c xs cs Hx Hxs IH]; cbn [map]; constructor.
  - apply Hfacts; exact Hx.
  - exact IH.
Qed.

(** An unchanged binding keeps its already established fact. *)
Theorem sparse_unchanged_value s x c :
  sparse_values_sound s -> SsaLink.val sl s x = Some c -> gamma LG (sigma (UVal x)) c.
Proof.
  intros Hfacts Hval; apply Hfacts; exact Hval.
Qed.

(** Operation rows cover the result of a concrete operation over covered operands. *)
Theorem sparse_operation_value s x c k args cs :
  In x (Ssa.values SS) -> sparse_values_sound s -> Ssa.def SS x = Op k args ->
  Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs ->
  ValueSem.eval M k cs = Some c -> gamma LG (sigma (UVal x)) c.
Proof.
  intros Hx Hfacts Hdef Hargs Hop.
  assert (Hr : In (COp x) (Sparse.rows P)).
  { eapply value_row; [exact Hx|].
    unfold value_row_c; autorewrite with galois_cost.
    fold SS; fold (Ssa.def SS x); rewrite Hdef; left; reflexivity. }
  pose proof (bound _ Hr) as Hbound.
  unfold row in Hbound; fold SS D in Hbound; rewrite Hdef in Hbound.
  cbn [Rows.eval_c Rows.reads Rows.target] in Hbound.
  rewrite map_map in Hbound.
  destruct (SparseRefine.collect_sound gam _ _ (argument_facts s args cs Hfacts Hargs))
    as [fs [Hcollect Hfs]].
  rewrite Cost.value_bind, Hcollect in Hbound; autorewrite with galois_cost in Hbound.
  eapply gamma_upper; [exact Hbound|].
  apply (op_sound HD k fs cs c); assumption.
Qed.

(** Arbitrary definitions are covered by the value dictionary's full top. *)
Theorem sparse_arbitrary_value x c :
  In x (Ssa.values SS) -> Ssa.def SS x = Arbitrary -> gamma LG (sigma (UVal x)) c.
Proof.
  intros Hx Hdef.
  assert (Hr : In (CArbitrary x) (Sparse.rows P)).
  { eapply value_row; [exact Hx|].
    unfold value_row_c; autorewrite with galois_cost.
    fold SS; fold (Ssa.def SS x); rewrite Hdef; left; reflexivity. }
  eapply gamma_upper; [exact (bound _ Hr)|apply (top_full HD)].
Qed.

(** Taken-edge rows accept satisfying guards and mark the edge executable. *)
Theorem sparse_taken_edge s l t e :
  reachable_state m s -> step m s l t -> Link.taken lk s l t e ->
  sparse_invariant s -> executable (sigma (UEdge e)) = true.
Proof.
  intros Hreach Hstep Htaken [Hblock Hfacts].
  destruct (link_taken_edge m (Ssa.cfg SS) lk s l t e (link_ok HS) Hreach Hstep Htaken)
    as [He [Hsource _]].
  assert (Hr : In (CEdge e) (Sparse.rows P)).
  { apply edge_row with (e := e); [exact He|left; reflexivity]. }
  pose proof (bound _ Hr) as Hbound.
  cbn [row Rows.reads Rows.eval_c Rows.target map] in Hbound.
  fold SS D graph in Hbound; fold graph in Hsource.
  rewrite Hsource in Hbound; rewrite map_map in Hbound.
  destruct (sigma (UBlock (Link.point lk s))) as [a|]; [|discriminate].
  rewrite Cost.value_bind in Hbound.
  assert (Hfeasible : SparseRefine.edge_feasible P sigma e = true).
  { eapply SparseRefine.edge_feasible_sound; eassumption. }
  rewrite SparseRefine.edge_feasible_equation in Hfeasible.
  destruct (Cost.value (refine_c P (SparseRefine.plans P e) (SparseRefine.dependencies P e)
    (map (fun x => sigma (UVal x)) (SparseRefine.dependencies P e)))) as [fm|]
    eqn:Href; [|discriminate].
  rewrite Cost.value_bind in Hbound; fold SS D in Hfeasible.
  rewrite Hfeasible in Hbound; rewrite Cost.value_ret in Hbound.
  eapply reached_upper; exact Hbound.
Qed.

(** Parameter rows retain the same concrete argument witness after guard refinement. *)
Theorem sparse_parameter_value s l t x c e b i z :
  reachable_state m s -> step m s l t -> sparse_invariant s ->
  Ssa.def SS x = Param b i -> Link.taken lk s l t e -> Graph.target graph e = b ->
  nth_error (Ssa.args SS e) i = Some z -> SsaLink.val sl s z = Some c ->
  gamma LG (sigma (UVal x)) c.
Proof.
  intros Hreach Hstep Hinv Hdef Htaken Htarget Harg Hz.
  pose proof (sparse_taken_edge s l t e Hreach Hstep Htaken Hinv) as Hexec.
  destruct (link_taken_edge m (Ssa.cfg SS) lk s l t e (link_ok HS) Hreach Hstep Htaken)
    as [He _].
  assert (Hparam : nth_error (Ssa.params SS (Graph.target graph e)) i = Some x).
  { rewrite Htarget; apply (param_defs HS x b i Hdef). }
  assert (Hr : In (CArg e i) (Sparse.rows P)).
  { apply edge_row with (e := e); [exact He|right; right].
    apply in_map; apply in_seq; split; [lia|].
    fold SS; apply (proj1 (nth_error_Some _ _)); rewrite Harg; discriminate. }
  pose proof (bound _ Hr) as Hbound; unfold row in Hbound; fold SS D graph in Hbound.
  rewrite Hparam, Harg in Hbound; cbn [Rows.target Rows.reads Rows.eval_c map] in Hbound.
  rewrite map_map in Hbound.
  destruct (sigma (UEdge e)) as [a|]; [|discriminate].
  rewrite Cost.value_bind in Hbound.
  destruct (SparseRefine.refine_snapshot_sound P M gam HV HD (SsaLink.val sl s) e
    (z :: SparseRefine.dependencies P e) (fun x => sigma (UVal x)))
    as [fm [Href Hfm]].
  - intros y Hy; right; exact Hy.
  - intros y d _ Hy; apply (proj2 Hinv); exact Hy.
  - eapply (guards_hold HS); eassumption.
  - eapply (guard_op_defined HS); eassumption.
  - change (Cost.value (refine_c P (SparseRefine.plans P e)
      (z :: SparseRefine.dependencies P e)
      (sigma (UVal z) :: map (fun x => sigma (UVal x)) (SparseRefine.dependencies P e))) =
      Some fm) in Href.
    rewrite Href in Hbound.
    eapply gamma_upper; [exact Hbound|].
    apply (proj2 Hfm); [left; reflexivity|exact Hz].
Qed.

(** A step preserves executable control through its stay or taken-edge witness. *)
Theorem sparse_successor_block s l t :
  reachable_state m s -> step m s l t -> sparse_invariant s ->
  executable (sigma (UBlock (Link.point lk t))) = true.
Proof.
  intros Hreach Hstep Hinv.
  destruct (edge_covers (link_ok HS) s l t Hreach Hstep) as [Hstay|[e Htaken]].
  - pose proof (stays_point (link_ok HS) s l t Hreach Hstep Hstay) as Hpoint.
    fold lk in Hpoint; rewrite Hpoint; exact (proj1 Hinv).
  - destruct (link_taken_edge m (Ssa.cfg SS) lk s l t e (link_ok HS) Hreach Hstep Htaken)
      as [He [_ Htarget]].
    fold lk graph in Htarget.
    pose proof (sparse_taken_edge s l t e Hreach Hstep Htaken Hinv) as Hexec.
    assert (Hr : In (CBlock e) (Sparse.rows P)).
    { apply edge_row with (e := e); [exact He|right; left; reflexivity]. }
    pose proof (bound _ Hr) as Hbound.
    change (leb LB (sigma (UEdge e)) (sigma (UBlock (Graph.target graph e))) = true)
      in Hbound.
    rewrite <- Htarget; destruct (sigma (UEdge e)) as [a|]; [|discriminate].
    eapply reached_upper; exact Hbound.
Qed.

(** Unchanged, operation, parameter and arbitrary origins each preserve value coverage. *)
Theorem sparse_successor_values s l t :
  reachable_state m s -> step m s l t -> sparse_invariant s -> sparse_values_sound t.
Proof.
  intros Hreach Hstep Hinv x c Hval.
  assert (Hx : In x (Ssa.values SS)).
  { eapply (coverage HS); [eapply reachable_state_step; eassumption|exact Hval]. }
  destruct (value_origin HS x c s l t Hreach Hstep Hval) as [Hsame|Horigin].
  - apply (sparse_unchanged_value s x c (proj2 Hinv) Hsame).
  - destruct Horigin as [[k [args [cs [Hdef [Hargs Hop]]]]]|Horigin].
    + eapply sparse_operation_value; [exact Hx|exact (proj2 Hinv)|eassumption|eassumption|].
      exact Hop.
    + destruct Horigin as [[e [b [i [z [Hdef [Htaken [Htarget [Harg Hz]]]]]]]]|Hdef].
      * eapply sparse_parameter_value; eassumption.
      * eapply sparse_arbitrary_value; eassumption.
Qed.

(** One semantic step preserves the coupled invariant. *)
Theorem sparse_invariant_step s l t :
  reachable_state m s -> sparse_invariant s -> step m s l t -> sparse_invariant t.
Proof.
  intros Hreach Hinv Hstep; split.
  - eapply sparse_successor_block; eassumption.
  - eapply sparse_successor_values; eassumption.
Qed.

(** Reachability lifts the initial and step lemmas to all finite concrete runs. *)
Theorem sparse_reachable_invariant s : reachable_state m s -> sparse_invariant s.
Proof.
  apply (reachable_ind m sparse_invariant sparse_initial_invariant sparse_invariant_step).
Qed.

(** Every reachable block, taken edge and bound value is covered by a sparse post-solution. *)
Theorem sparse_sound :
  (forall s, reachable_state m s -> executable (sigma (UBlock (Link.point lk s))) = true) /\
  (forall s l t e, reachable_state m s -> step m s l t -> Link.taken lk s l t e ->
    executable (sigma (UEdge e)) = true) /\
  (forall s x c, reachable_state m s -> SsaLink.val sl s x = Some c ->
    gamma (lift_bot_gamma gam) (sigma (UVal x)) c).
Proof.
  split; [intros s Hs; exact (proj1 (sparse_reachable_invariant s Hs))|split].
  - intros s l t e Hs Hstep Htaken; eapply sparse_taken_edge; try eassumption.
    apply sparse_reachable_invariant; exact Hs.
  - intros s x c Hs Hval; exact (proj2 (sparse_reachable_invariant s Hs) x c Hval).
Qed.

End Soundness.

End SparseSound.
