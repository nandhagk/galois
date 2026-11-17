(** * Function calls and resolver graphs

    Inventories and resolver tables retain site and target order.
    For example, repeated targets produce repeated graph successors.
    Builds on: Program.CallsSig and Base.Trie. *)

From Stdlib Require Import List Arith NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie.
From Galois.Graph Require Import Data Spec.
From Galois.Program Require Import SemanticsSig CallsSig.

Module Nat.
  TimeFun Nat.max.
End Nat.

Definition call_edge_target {F S} (edge : call_edge F S) : F :=
  match edge with
  | CallEdge _ target => target
  end.

TimeFun call_edge_target.

Record calls_tables (F S : Type) := CallsTables {
  call_functions : list F;
  call_inventory : list (S * F);
  call_roots : list F;
  call_sites : ptrie (list S);
  call_callers : ptrie F;
  call_default_caller : F;
  call_targets : ptrie (list F)
}.

Arguments CallsTables {F S}.
Arguments call_functions {F S}.
Arguments call_inventory {F S}.
Arguments call_roots {F S}.
Arguments call_sites {F S}.
Arguments call_callers {F S}.
Arguments call_default_caller {F S}.
Arguments call_targets {F S}.

TimeFun call_functions.
TimeFun call_inventory.
TimeFun call_roots.
TimeFun call_sites.
TimeFun call_callers.
TimeFun call_default_caller.
TimeFun call_targets.

Module Type CALLS_DATA (P : TYPE) (F S : KEY_OPS).
  Parameter tables : P.t -> calls_tables F.t S.t.
End CALLS_DATA.

Module Type CALLS_DATA_TIME (P : TYPE) (F S : KEY_T)
    (Import D : CALLS_DATA P F S).
  Parameter T_tables : P.t -> N.
  Parameter c_tables : N.
  Parameter T_tables_le : forall p, (T_tables p <= c_tables)%N.
End CALLS_DATA_TIME.

Module Type CALLS_DATA_T (P : TYPE) (F S : KEY_T) :=
  CALLS_DATA P F S <+ CALLS_DATA_TIME P F S.

Module CallsCode (P : TYPE) (F S : KEY_OPS) (D : CALLS_DATA P F S)
    <: CALLS_OPS P F S.
  Definition functions p := call_functions (D.tables p).
  Definition calls p := call_inventory (D.tables p).
  Definition roots p := call_roots (D.tables p).
  Definition sites_of p f :=
    match trie_get (F.encode f) (call_sites (D.tables p)) with
    | Some sites => sites
    | None => nil
    end.
  Definition caller_of p site :=
    match trie_get (S.encode site) (call_callers (D.tables p)) with
    | Some f => f
    | None => call_default_caller (D.tables p)
    end.
  Definition resolve p site :=
    match trie_get (S.encode site) (call_targets (D.tables p)) with
    | Some fs => fs
    | None => nil
    end.
  Definition call_graph p :=
    Digraph (map F.encode (functions p))
      (fold_left (fun adj f => PTrieCode.set (F.encode f)
        (map (fun e => F.encode (call_edge_target e))
          (call_edges (resolve p) (sites_of p f))) adj)
        (functions p) PTrieCode.empty).
End CallsCode.

Module Calls (P : TYPE) (F S : KEY) (D : CALLS_DATA P F S) <: CALLS P F S.
  Include CallsCode P F S D.
  Include CALLS_SPEC P F S.

  Definition wf p :=
    NoDup (functions p) /\ incl (roots p) (functions p) /\
    (forall f site, In site (sites_of p f) ->
      caller_of p site = f /\ In f (functions p)) /\
    (forall site f, In f (resolve p site) -> In f (functions p)) /\
    calls p = flat_map (fun f =>
      flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).

  Lemma calls_spec : forall p, wf p -> calls p = flat_map (fun f =>
    flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).
  Proof.
    intros p [_ [_ [_ [_ Hcalls]]]]. exact Hcalls.
  Qed.

  Lemma functions_nodup : forall p, wf p -> NoDup (functions p).
  Proof.
    intros p [Hfunctions _]; exact Hfunctions.
  Qed.
  Lemma roots_listed : forall p, wf p -> incl (roots p) (functions p).
  Proof.
    intros p [_ [Hroots _]]; exact Hroots.
  Qed.
  Lemma sites_caller : forall p f site, wf p -> In site (sites_of p f) ->
    caller_of p site = f /\ In f (functions p).
  Proof.
    intros p f site [_ [_ [Hsites _]]]; apply Hsites.
  Qed.
  Lemma resolve_listed : forall p site f, wf p -> In f (resolve p site) ->
    In f (functions p).
  Proof.
    intros p site f [_ [_ [_ [Hresolve _]]]]; apply Hresolve.
  Qed.
  Lemma call_graph_nodes : forall p, verts (call_graph p) = map F.encode (functions p).
  Proof.
    reflexivity.
  Qed.

  (** Inserting a function again retains its same outgoing adjacency list. *)
  Lemma adjacency_lookup : forall p f fs adj,
    trie_get (F.encode f) adj = Some (map (fun e => F.encode (call_edge_target e))
      (call_edges (resolve p) (sites_of p f))) \/ In f fs ->
    trie_get (F.encode f)
      (fold_left (fun acc g => PTrieCode.set (F.encode g)
        (map (fun e => F.encode (call_edge_target e))
          (call_edges (resolve p) (sites_of p g))) acc) fs adj) =
    Some (map (fun e => F.encode (call_edge_target e))
      (call_edges (resolve p) (sites_of p f))).
  Proof.
    intros p f fs; induction fs as [|g fs IH]; intros adj Hin; cbn [fold_left].
    - destruct Hin as [Hget|[]]; exact Hget.
    - apply IH; destruct (F.eqb_spec f g) as [<-|Hneq].
      + left; apply PTrie.get_set_same.
      + destruct Hin as [Hget|[Heq|Hin]].
        * left; rewrite PTrie.get_set_other; [exact Hget|].
          intro Hcode; apply Hneq; now apply F.encode_inj.
        * symmetry in Heq; contradiction.
        * now right.
  Qed.

  Lemma call_graph_out : forall p f, wf p -> In f (functions p) ->
    succs (call_graph p) (F.encode f) =
      map (fun e => F.encode (edge_callee e)) (call_edges (resolve p) (sites_of p f)).
  Proof.
    intros p f Hwf Hf; unfold call_graph, succs.
    rewrite (adjacency_lookup p f (functions p) PTrieCode.empty (or_intror Hf)).
    apply map_ext; intros [site g]; reflexivity.
  Qed.
  Lemma call_graph_wf : forall p, wf p -> wf_graph (call_graph p).
  Proof.
    intros p Hwf; split.
    - rewrite call_graph_nodes; pose proof (functions_nodup p Hwf) as Hdistinct.
      induction Hdistinct as [|f fs Hfresh Hdistinct IH]; cbn [map]; constructor.
      + intro Hin; apply in_map_iff in Hin; destruct Hin as [g [Hcode Hg]].
        apply F.encode_inj in Hcode; subst g; contradiction.
      + exact IH.
    - intros u v Hu Huv; rewrite call_graph_nodes in Hu |- *.
      apply in_map_iff in Hu; destruct Hu as [f [<- Hf]].
      unfold edge in Huv; rewrite (call_graph_out p f Hwf Hf) in Huv.
      apply in_map_iff in Huv; destruct Huv as [[site g] [<- Hcall]].
      cbn [edge_callee]; apply in_map.
      unfold call_edges in Hcall; apply in_flat_map in Hcall.
      destruct Hcall as [site' [Hsite Hcall]].
      apply in_map_iff in Hcall; destruct Hcall as [g' [Heq Htarget]].
      injection Heq as <- <-; eapply resolve_listed; eassumption.
  Qed.
End Calls.

Module CallsSound (P : TYPE) (F S : KEY) (C : CALLS P F S)
    (M : SEMANTICS P) (L : CALLS_LINK P F S C M) <: CALLS_SOUND P F S C M L.
  Lemma reachable_frames_linked : forall p s, C.wf p ->
    reachable (M.initial p) (M.step p) s ->
    frames_linked (C.sites_of p) (C.caller_of p) (C.resolve p) (L.here s) (L.frames s).
  Proof.
    intros p s Hwf Hreach; induction Hreach as [s Hinitial|s t Hreach IH Hstep].
    - rewrite (proj2 (L.initial_roots p s Hinitial)); exact I.
    - destruct (L.step_shape p s t Hreach Hstep) as
        [[Hhere Hstack]|[[site [Hsite [Hcallee Hstack]]]|[f [site [Hstack Hhere]]]]].
      + rewrite Hhere, Hstack; exact IH.
      + rewrite Hstack; cbn [frames_linked].
        split; [exact (proj1 (C.sites_caller p (L.here s) site Hwf Hsite))|].
        split; [exact Hsite|]. split; assumption.
      + rewrite Hstack in IH; cbn [frames_linked] in IH.
        destruct IH as [_ [_ [_ Htail]]]; now rewrite Hhere.
  Qed.

  (** Appending a graph edge extends a path without changing its root. *)
  Lemma path_extend : forall g u vs v w, path g u vs v -> edge g v w ->
    exists ws, path g u ws w.
  Proof.
    intros g u vs v w Hpath; induction Hpath as [v|u v vs z Hedge Hpath IH];
      intro Hlast.
    - exists (v :: w :: nil); econstructor; [exact Hlast|constructor].
    - destruct (IH Hlast) as [ws Htail].
      exists (u :: ws); econstructor; eassumption.
  Qed.

  (** A resolved call extends reachability in the encoded function graph. *)
  Lemma resolved_reachable : forall p f site g, C.wf p ->
    In f (C.functions p) -> In site (C.sites_of p f) -> In g (C.resolve p site) ->
    reach (C.call_graph p) (C.graph_roots p) (F.encode f) ->
    reach (C.call_graph p) (C.graph_roots p) (F.encode g).
  Proof.
    intros p f site g Hwf Hf Hsite Hg [root [vs [Hroot Hpath]]].
    assert (Hedge : edge (C.call_graph p) (F.encode f) (F.encode g)).
    { unfold edge; rewrite (C.call_graph_out p f Hwf Hf).
      apply in_map_iff; exists (CallEdge site g); split; [reflexivity|].
      unfold call_edges; apply in_flat_map; exists site; split; [exact Hsite|].
      now apply in_map. }
    destruct (path_extend _ _ _ _ _ Hpath Hedge) as [ws Hextended].
    exists root, ws; now split.
  Qed.

  Lemma active_reachable : forall p s f, C.wf p ->
    reachable (M.initial p) (M.step p) s -> In f (L.active s) ->
    reach (C.call_graph p) (C.graph_roots p) (F.encode f).
  Proof.
    intros p s f Hwf Hreach; revert f.
    induction Hreach as [s Hinitial|s t Hreach IH Hstep]; intros f Hin.
    - destruct (L.initial_roots p s Hinitial) as [Hroot Hstack].
      unfold L.active in Hin; rewrite Hstack in Hin; destruct Hin as [<-|[]].
      exists (F.encode (L.here s)), (F.encode (L.here s) :: nil).
      split; [unfold C.graph_roots; now apply in_map|constructor].
    - unfold L.active in Hin.
      destruct (L.step_shape p s t Hreach Hstep) as
        [[Hhere Hstack]|[[site [Hsite [Hcallee Hstack]]]|[g [site [Hstack Hhere]]]]].
      + rewrite Hhere, Hstack in Hin; exact (IH f Hin).
      + rewrite Hstack in Hin; cbn [map fst] in Hin; destruct Hin as [<-|Hin].
        * eapply resolved_reachable; [exact Hwf| |exact Hsite|exact Hcallee|].
          -- apply (L.frames_listed p s Hreach); now left.
          -- apply IH; now left.
        * exact (IH f Hin).
      + rewrite Hhere in Hin; apply IH; unfold L.active; rewrite Hstack.
        right; exact Hin.
  Qed.
End CallsSound.

Module CallsT (P : TYPE) (F S : KEY_T) (D : CALLS_DATA_T P F S)
    <: CALLS_ALL P F S.
  Include Calls P F S D.
  TimeFun functions.
  TimeFun calls.
  TimeFun roots.
  TimeFun sites_of.
  TimeFun caller_of.
  TimeFun resolve.
  TimeFun call_graph.
  TimeFun out_edges.
  TimeFun sites.
  TimeFun targets.
  TimeFun graph_roots.
  TimeFun function_width.

  Definition call_graph_work p :=
    (T_functions p +
      fold_right N.add 0%N (map (fun f => T_sites_of p f + F.T_encode f)%N (functions p)) +
      fold_right N.add 0%N (map (T_resolve p) (sites p)) +
      fold_right N.add 0%N (map F.T_encode (targets p)) +
      N.of_nat (length (functions p) + length (sites p) + length (targets p) + 1) *
        N.of_nat (function_width p + 1))%N.

  (** Mapping charges the sum of its callback costs and one step per element. *)
  Local Lemma map_time_sum {A B} (f : A -> B) (T_f : A -> N) : forall xs,
    ListDef.T_map f T_f xs =
      (fold_right N.add 0%N (map T_f xs) + N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; time_unfold ListDef.T_map; time_cbn_all; lia.
  Qed.

  (** A fold with state-independent callback budgets pays their sum. *)
  Local Lemma fold_time_sum {A B} (f : A -> B -> A) (T_f : A -> B -> N)
      (budget : B -> N) : forall xs a,
    (forall st x, In x xs -> (T_f st x <= budget x)%N) ->
    (List.T_fold_left f T_f xs a <=
      fold_right N.add 0%N (map budget xs) + 2 * N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intros a Hcost.
    - time_step.
    - pose proof (Hcost a x (or_introl eq_refl)) as Hhead.
      specialize (IH (f a x) (fun st y Hin => Hcost st y (or_intror Hin))).
      time_step.
  Qed.

  (** Summing an appended inventory splits at the append boundary. *)
  Local Lemma sum_app {A} (cost : A -> N) : forall xs ys,
    fold_right N.add 0%N (map cost (xs ++ ys)) =
      (fold_right N.add 0%N (map cost xs) + fold_right N.add 0%N (map cost ys))%N.
  Proof.
    induction xs as [|x xs IH]; intro ys; cbn [app map fold_right]; rewrite ?IH; lia.
  Qed.

  (** A flattened inventory's sum is the sum of its constituent inventories. *)
  Local Lemma sum_flat_map {A B} (items : A -> list B) (cost : B -> N) : forall xs,
    fold_right N.add 0%N (map cost (flat_map items xs)) =
    fold_right N.add 0%N
      (map (fun x => fold_right N.add 0%N (map cost (items x))) xs).
  Proof.
    induction xs as [|x xs IH]; cbn [flat_map map fold_right]; [reflexivity|].
    rewrite sum_app, IH; reflexivity.
  Qed.

  (** Pointwise addition distributes over finite cost sums. *)
  Local Lemma sum_add {A} (left right : A -> N) : forall xs,
    fold_right N.add 0%N (map (fun x => left x + right x)%N xs) =
      (fold_right N.add 0%N (map left xs) + fold_right N.add 0%N (map right xs))%N.
  Proof.
    induction xs as [|x xs IH]; cbn [map fold_right]; rewrite ?IH; lia.
  Qed.

  (** Multiplication by a constant distributes over finite cost sums. *)
  Local Lemma sum_scale {A} (cost : A -> N) c : forall xs,
    fold_right N.add 0%N (map (fun x => c * cost x)%N xs) =
      (c * fold_right N.add 0%N (map cost xs))%N.
  Proof.
    induction xs as [|x xs IH]; cbn [map fold_right]; rewrite ?IH; nia.
  Qed.

  (** A constant cost contributes once for every inventory entry. *)
  Local Lemma sum_constant {A} c : forall xs : list A,
    fold_right N.add 0%N (map (fun _ => c) xs) = (c * N.of_nat (length xs))%N.
  Proof.
    induction xs as [|x xs IH]; cbn [map fold_right length]; rewrite ?IH;
      time_cbn_all; nia.
  Qed.

  (** Pointwise bounds give bounds on the corresponding finite sums. *)
  Local Lemma sum_le {A} (left right : A -> N) : forall xs,
    (forall x, In x xs -> (left x <= right x)%N) ->
    (fold_right N.add 0%N (map left xs) <=
      fold_right N.add 0%N (map right xs))%N.
  Proof.
    induction xs as [|x xs IH]; intro Hpoint; cbn [map fold_right]; [lia|].
    pose proof (Hpoint x (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y Hin => Hpoint y (or_intror Hin))); lia.
  Qed.

  (** Flattening preserves the total number of target occurrences. *)
  Local Lemma sum_lengths {A B} (items : A -> list B) : forall xs,
    fold_right N.add 0%N (map (fun x => N.of_nat (length (items x))) xs) =
      N.of_nat (length (flat_map items xs)).
  Proof.
    induction xs as [|x xs IH]; cbn [flat_map map fold_right]; [reflexivity|].
    rewrite length_app, Nat2N.inj_add, IH; reflexivity.
  Qed.

  (** Each row's extra unit contributes one unit per outer inventory entry. *)
  Local Lemma sum_lengths_succ {A B} (items : A -> list B) : forall xs,
    fold_right N.add 0%N (map (fun x => N.of_nat (length (items x) + 1)) xs) =
      N.of_nat (length (flat_map items xs) + length xs).
  Proof.
    induction xs as [|x xs IH]; cbn [flat_map map fold_right length]; [reflexivity|].
    rewrite length_app, IH; time_cbn_all; lia.
  Qed.

  (** Grouping targets by function preserves the complete target inventory. *)
  Local Lemma targets_partition : forall p,
    targets p = flat_map (fun f => flat_map (resolve p) (sites_of p f)) (functions p).
  Proof.
    intro p; unfold targets, sites.
    induction (functions p) as [|f fs IH]; cbn [flat_map]; [reflexivity|].
    rewrite flat_map_app, IH; reflexivity.
  Qed.

  (** Projecting tagged call edges recovers the resolver targets in order. *)
  Local Lemma call_edges_targets : forall p ss,
    map call_edge_target (call_edges (resolve p) ss) = flat_map (resolve p) ss.
  Proof.
    intros p ss; unfold call_edges.
    induction ss as [|site ss IH]; cbn [flat_map]; [reflexivity|].
    rewrite map_app, map_map, IH; cbn [call_edge_target].
    now rewrite map_id.
  Qed.

  (** The tagged edge list has one entry per resolver target occurrence. *)
  Local Lemma call_edges_length : forall p ss,
    length (call_edges (resolve p) ss) = length (flat_map (resolve p) ss).
  Proof.
    intros p ss; rewrite <- (length_map call_edge_target), call_edges_targets; reflexivity.
  Qed.

  (** Every listed function fits the maximum code width used for adjacency insertion. *)
  Local Lemma listed_function_width : forall p f, In f (functions p) ->
    F.bits f <= function_width p.
  Proof.
    intros p f Hin; unfold function_width.
    assert (Hmember : In f (functions p ++ targets p)) by (apply in_or_app; now left).
    clear Hin; induction (functions p ++ targets p) as [|g fs IH]; [contradiction|].
    cbn [map fold_right]; destruct Hmember as [<-|Hmember].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hmember|apply Nat.le_max_r].
  Qed.

  Definition c_calls : N :=
    (2 * D.c_tables + F.c_key + S.c_key + 136 * (1024 + 1))%N.

  (** The common coefficient covers the fixed reader and key-operation coefficients. *)
  Local Lemma reader_coefficient :
    (2 * D.c_tables + F.c_key + S.c_key + 16 <= c_calls)%N.
  Proof.
    unfold c_calls; lia.
  Qed.

  (** The common coefficient also covers the composed graph construction factors. *)
  Local Lemma graph_coefficient : (136 * (1024 + 1) <= c_calls)%N.
  Proof.
    unfold c_calls; lia.
  Qed.

  (** A reader with fixed cost fits every output-length budget. *)
  Local Lemma fixed_reader_bound : forall cost n,
    (cost <= D.c_tables + 2)%N ->
    (cost <= c_calls * N.of_nat (n + 1))%N.
  Proof.
    intros cost n Hcost; pose proof reader_coefficient as Hcoefficient.
    rewrite Nat2N.inj_add; time_cbn; nia.
  Qed.

  Lemma T_calls_le : forall p,
    (T_calls p <= c_calls * N.of_nat (length (calls p) + 1))%N.
  Proof.
    intro p; apply fixed_reader_bound.
    pose proof (D.T_tables_le p) as Htables; unfold T_calls, T_call_inventory; lia.
  Qed.

  (** A site contributes exactly its resolver targets to its outgoing list. *)
  Lemma F1_call_edge : forall p f site target,
    In site (sites_of p f) -> In target (resolve p site) ->
    In (CallEdge site target) (out_edges p f).
  Proof.
    intros p f site target Hsite Htarget; unfold out_edges, call_edges.
    apply in_flat_map; exists site; split; [exact Hsite|now apply in_map].
  Qed.
  Definition k_edges : N := 16%N.
  Definition k_adj : N := (8 * (1024 + 1))%N.

  Lemma T_functions_le : forall p,
    (T_functions p <= c_calls * N.of_nat (length (functions p) + 1))%N.
  Proof.
    intro p; apply fixed_reader_bound.
    pose proof (D.T_tables_le p) as Htables; unfold T_functions, T_call_functions; lia.
  Qed.

  Lemma T_roots_le : forall p,
    (T_roots p <= c_calls * N.of_nat (length (roots p) + 1))%N.
  Proof.
    intro p; apply fixed_reader_bound.
    pose proof (D.T_tables_le p) as Htables; unfold T_roots, T_call_roots; lia.
  Qed.

  Lemma T_sites_of_le : forall p f,
    (T_sites_of p f <= c_calls * N.of_nat (F.bits f + length (sites_of p f) + 1))%N.
  Proof.
    intros p f.
    pose proof (PTrieT.T_trie_get_le (list S.t) (F.encode f)
      (call_sites (D.tables p))) as Hget.
    pose proof (D.T_tables_le p) as Htables.
    pose proof (F.T_encode_le f) as Hencode.
    eapply N.le_trans with
      (m := ((F.c_key + D.c_tables + 4) * N.of_nat (F.bits f + 1))%N).
    - unfold T_sites_of; unfold T_call_sites, F.bits in *.
      time_cbn_all; nia.
    - apply N.mul_le_mono.
      + pose proof reader_coefficient; lia.
      + lia.
  Qed.

  Lemma T_caller_of_le : forall p site,
    (T_caller_of p site <= c_calls * N.of_nat (S.bits site + 1))%N.
  Proof.
    intros p site.
    pose proof (PTrieT.T_trie_get_le F.t (S.encode site)
      (call_callers (D.tables p))) as Hget.
    pose proof (D.T_tables_le p) as Htables.
    pose proof (S.T_encode_le site) as Hencode.
    eapply N.le_trans with
      (m := ((S.c_key + 2 * D.c_tables + 6) * N.of_nat (S.bits site + 1))%N).
    - unfold T_caller_of.
      unfold T_call_callers, T_call_default_caller, S.bits in *.
      destruct (trie_get (S.encode site) (call_callers (D.tables p)));
        time_cbn_all; nia.
    - apply N.mul_le_mono_r; pose proof reader_coefficient; lia.
  Qed.

  Lemma T_resolve_le : forall p site,
    (T_resolve p site <= c_calls * N.of_nat (S.bits site + length (resolve p site) + 1))%N.
  Proof.
    intros p site.
    pose proof (PTrieT.T_trie_get_le (list F.t) (S.encode site)
      (call_targets (D.tables p))) as Hget.
    pose proof (D.T_tables_le p) as Htables.
    pose proof (S.T_encode_le site) as Hencode.
    eapply N.le_trans with
      (m := ((S.c_key + D.c_tables + 4) * N.of_nat (S.bits site + 1))%N).
    - unfold T_resolve; unfold T_call_targets, S.bits in *.
      time_cbn_all; nia.
    - apply N.mul_le_mono.
      + pose proof reader_coefficient; lia.
      + lia.
  Qed.

  (** The call inventory is linear in its output. *)
  Lemma calls_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (length (calls p))) T_calls.
  Proof.
    apply bigO_intro with (c := c_calls).
    intros p _; pose proof (T_calls_le p) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Site enumeration is linear in the function key and the returned sites. *)
  Lemma sites_of_bigO : bigO (X := P.t * F.t) (fun _ => True)
    (fun '(p, f) => N.of_nat (F.bits f + length (sites_of p f)))
    (fun '(p, f) => T_sites_of p f).
  Proof.
    apply bigO_intro with (c := c_calls).
    intros [p f] _; pose proof (T_sites_of_le p f) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Caller lookup is linear in the site key. *)
  Lemma caller_of_bigO : bigO (X := P.t * S.t) (fun _ => True)
    (fun '(_, site) => N.of_nat (S.bits site)) (fun '(p, site) => T_caller_of p site).
  Proof.
    apply bigO_intro with (c := c_calls).
    intros [p site] _; pose proof (T_caller_of_le p site) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Resolution is linear in the site key and the returned functions. *)
  Lemma resolve_bigO : bigO (X := P.t * S.t) (fun _ => True)
    (fun '(p, site) => N.of_nat (S.bits site + length (resolve p site)))
    (fun '(p, site) => T_resolve p site).
  Proof.
    apply bigO_intro with (c := c_calls).
    intros [p site] _; pose proof (T_resolve_le p site) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** The function inventory is linear in its output. *)
  Lemma functions_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (length (functions p))) T_functions.
  Proof.
    apply bigO_intro with (c := c_calls).
    intros p _; pose proof (T_functions_le p) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** The root inventory is linear in its output. *)
  Lemma roots_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (length (roots p))) T_roots.
  Proof.
    apply bigO_intro with (c := c_calls).
    intros p _; pose proof (T_roots_le p) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Each resolver read includes at least one charged operation. *)
  Local Lemma resolve_time_positive : forall p site, (1 <= T_resolve p site)%N.
  Proof.
    intros p site; time_unfold T_resolve; time_cbn; lia.
  Qed.

  (** Actual resolver clocks pay for one traversal of the site list. *)
  Local Lemma resolver_sum_length : forall p ss,
    (N.of_nat (length ss) <= fold_right N.add 0%N (map (T_resolve p) ss))%N.
  Proof.
    intros p ss; induction ss as [|site ss IH]; cbn [length map fold_right].
    - lia.
    - pose proof (resolve_time_positive p site); rewrite Nat2N.inj_succ; lia.
  Qed.

  (** Building tagged edges pays each resolver and each output occurrence. *)
  Local Lemma call_edges_time : forall p ss,
    (T_call_edges (resolve p) (fun site => T_resolve p site) ss <=
      8 * (fold_right N.add 0%N (map (T_resolve p) ss) +
        N.of_nat (length ss + length (flat_map (resolve p) ss) + 1)))%N.
  Proof.
    intros p ss; induction ss as [|site ss IH].
    - time_unfold @T_call_edges; time_unfold @Code.List.T_flat_map; time_cbn; nia.
    - pose proof (ListDef.T_map_le (CallEdge site) (fun _ : F.t => 1%N) 1%N
        (resolve p site) (fun _ => N.le_refl 1)) as Hmap.
      pose proof (Datatypes.T_app_le (map (CallEdge site) (resolve p site))
        (call_edges (resolve p) ss)) as Happ.
      unfold call_edges in Happ.
      unfold T_call_edges in IH; time_unfold @T_call_edges.
      time_unfold @Code.List.T_flat_map; time_cbn_all.
      rewrite !length_app, !length_map in *; time_cbn_all; lia.
  Qed.

  (** Tagged-edge construction charges at least one unit for each output occurrence. *)
  Local Lemma call_edges_output_le : forall p ss,
    (N.of_nat (length (flat_map (resolve p) ss)) <=
      T_call_edges (resolve p) (fun site => T_resolve p site) ss)%N.
  Proof.
    intros p ss; induction ss as [|site ss IH].
    - time_unfold @T_call_edges; time_unfold @Code.List.T_flat_map; time_cbn; lia.
    - unfold T_call_edges in IH; time_unfold @T_call_edges.
      time_unfold @Code.List.T_flat_map; rewrite map_time_sum.
      cbn [flat_map length]; rewrite length_app; time_cbn_all; lia.
  Qed.

  (** Outgoing-edge construction pays for the length of its result. *)
  Local Lemma out_edges_output_le : forall p f,
    (N.of_nat (length (flat_map (resolve p) (sites_of p f))) <= T_out_edges p f)%N.
  Proof.
    intros p f; pose proof (call_edges_output_le p (sites_of p f)) as Houtput.
    time_unfold T_out_edges; time_cbn; lia.
  Qed.

  (** The outgoing-row clock includes its site reader and tagged-edge construction. *)
  Local Lemma out_edges_steps_le : forall p f,
    (T_sites_of p f + T_call_edges (resolve p) (fun site => T_resolve p site) (sites_of p f) <=
      T_out_edges p f)%N.
  Proof.
    intros p f; time_unfold T_out_edges; time_cbn; lia.
  Qed.

  (** Encoding tagged targets charges their encoded values and a fixed projection cost. *)
  Local Lemma encoded_edges_time : forall p ss clock,
    (forall e, (clock e <= F.T_encode (call_edge_target e) + 3)%N) ->
    (ListDef.T_map (fun e => F.encode (call_edge_target e)) clock
      (call_edges (resolve p) ss) <=
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) ss)) +
        4 * N.of_nat (length (flat_map (resolve p) ss)) + 1)%N.
  Proof.
    intros p ss clock Hclock; rewrite map_time_sum.
    pose proof (sum_le clock (fun e => F.T_encode (call_edge_target e) + 3)%N
      (call_edges (resolve p) ss) (fun e _ => Hclock e)) as Hsum.
    rewrite sum_add, sum_constant in Hsum.
    rewrite <- (map_map call_edge_target F.T_encode (call_edges (resolve p) ss)),
      call_edges_targets in Hsum.
    rewrite call_edges_length in *; lia.
  Qed.

  Lemma T1_out_edges : forall p f,
    (T_out_edges p f <= k_edges * (T_sites_of p f +
      fold_right N.add 0%N (map (T_resolve p) (sites_of p f)) +
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
      N.of_nat (length (flat_map (resolve p) (sites_of p f)) + 1)))%N.
  Proof.
    intros p f; pose proof (call_edges_time p (sites_of p f)) as Hedges.
    pose proof (resolver_sum_length p (sites_of p f)) as Hsites.
    unfold k_edges; time_unfold T_out_edges; time_cbn_all; lia.
  Qed.

  Lemma T2_adjacency : forall p,
    (T_call_graph p <= k_adj * (T_functions p +
      fold_right N.add 0%N (map (fun f => T_out_edges p f + F.T_encode f +
        fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))))%N
        (functions p)) +
      N.of_nat (length (functions p) + 1) * N.of_nat (function_width p + 1)))%N.
  Proof.
    intro p; time_unfold T_call_graph.
    match goal with
    | |- context [Std.List.T_fold_left ?update ?clock (functions p) ?initial] =>
      assert (Hfold : (Std.List.T_fold_left update clock (functions p) initial <=
        fold_right N.add 0%N (map (fun f => 4 * (1024 + 1) *
          (T_out_edges p f + F.T_encode f +
            fold_right N.add 0%N
              (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
            N.of_nat (function_width p + 1)))%N (functions p)) +
          2 * N.of_nat (length (functions p)) + 1)%N)
    end.
    { apply fold_time_sum; intros adj f Hin; cbn beta iota zeta.
      pose proof (listed_function_width p f Hin) as Hwidth.
      pose proof (out_edges_output_le p f) as Houtput.
      pose proof (out_edges_steps_le p f) as Hsteps.
      pose proof (PTrieT.T_set_le (list positive) (F.encode f)
        (map (fun e => F.encode (call_edge_target e))
          (call_edges (resolve p) (sites_of p f))) adj) as Hset.
      unfold PTrieT.c_trie in Hset; unfold F.bits in Hwidth.
      match goal with
      | |- context [ListDef.T_map _ ?clock _] =>
        assert (Hmap : (ListDef.T_map (fun e => F.encode (call_edge_target e)) clock
          (call_edges (resolve p) (sites_of p f)) <=
            fold_right N.add 0%N
              (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
            4 * N.of_nat (length (flat_map (resolve p) (sites_of p f))) + 1)%N)
      end.
      { apply encoded_edges_time; intros [site g]; time_unfold @T_call_edge_target;
          time_cbn; lia. }
      time_cbn_all; lia. }
    assert (Hfunctions :
      ListDef.T_map F.encode (fun f => F.T_encode f) (functions p) =
        (fold_right N.add 0%N (map F.T_encode (functions p)) +
          N.of_nat (length (functions p)) + 1)%N).
    { apply map_time_sum. }
    rewrite (sum_scale (fun f => T_out_edges p f + F.T_encode f +
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
      N.of_nat (function_width p + 1))%N (4 * (1024 + 1))%N (functions p)) in Hfold.
    rewrite (sum_add (fun f => T_out_edges p f + F.T_encode f +
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))))%N
      (fun _ => N.of_nat (function_width p + 1)) (functions p)), sum_constant in Hfold.
    assert (Hencodes : (fold_right N.add 0%N (map F.T_encode (functions p)) <=
      fold_right N.add 0%N (map (fun f => T_out_edges p f + F.T_encode f +
        fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))))%N
        (functions p)))%N).
    { apply sum_le; intros f Hin; lia. }
    unfold k_adj; time_cbn_all; nia.
  Qed.

  (** Summing outgoing-row bounds recovers the program's reader and target inventories. *)
  Local Lemma out_edges_sum : forall p,
    (fold_right N.add 0%N (map (T_out_edges p) (functions p)) <= k_edges *
      (fold_right N.add 0%N (map (T_sites_of p) (functions p)) +
        fold_right N.add 0%N (map (T_resolve p) (sites p)) +
        fold_right N.add 0%N (map F.T_encode (targets p)) +
        N.of_nat (length (targets p) + length (functions p))))%N.
  Proof.
    intro p; pose proof (sum_le (T_out_edges p)
      (fun f => k_edges * (T_sites_of p f +
        fold_right N.add 0%N (map (T_resolve p) (sites_of p f)) +
        fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
        N.of_nat (length (flat_map (resolve p) (sites_of p f)) + 1)))%N
      (functions p) (fun f _ => T1_out_edges p f)) as Hsum.
    rewrite (sum_scale (fun f => T_sites_of p f +
      fold_right N.add 0%N (map (T_resolve p) (sites_of p f)) +
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))) +
      N.of_nat (length (flat_map (resolve p) (sites_of p f)) + 1))%N
      k_edges (functions p)) in Hsum.
    rewrite (sum_add (fun f => T_sites_of p f +
      fold_right N.add 0%N (map (T_resolve p) (sites_of p f)) +
      fold_right N.add 0%N (map F.T_encode (flat_map (resolve p) (sites_of p f))))%N
      (fun f => N.of_nat (length (flat_map (resolve p) (sites_of p f)) + 1))
      (functions p)) in Hsum.
    rewrite (sum_add (fun f => T_sites_of p f +
      fold_right N.add 0%N (map (T_resolve p) (sites_of p f)))%N
      (fun f => fold_right N.add 0%N
        (map F.T_encode (flat_map (resolve p) (sites_of p f)))) (functions p)) in Hsum.
    rewrite (sum_add (T_sites_of p)
      (fun f => fold_right N.add 0%N (map (T_resolve p) (sites_of p f))) (functions p)),
      sum_lengths_succ in Hsum.
    rewrite <- (sum_flat_map (sites_of p) (T_resolve p) (functions p)) in Hsum.
    rewrite <- (sum_flat_map (fun f => flat_map (resolve p) (sites_of p f))
      F.T_encode (functions p)) in Hsum.
    rewrite <- targets_partition in Hsum; exact Hsum.
  Qed.

  (** Graph construction charges the inventory readers and encoded adjacency work. *)
  Lemma T_call_graph_le : forall p,
    (T_call_graph p <= c_calls * call_graph_work p)%N.
  Proof.
    intro p; pose proof (T2_adjacency p) as Hadjacency.
    pose proof (out_edges_sum p) as Hrows.
    eapply N.le_trans with (m := (136 * (1024 + 1) * call_graph_work p)%N).
    - unfold call_graph_work, k_adj, k_edges in *.
      rewrite (sum_add (fun f => T_out_edges p f + F.T_encode f)%N
        (fun f => fold_right N.add 0%N
          (map F.T_encode (flat_map (resolve p) (sites_of p f)))) (functions p)),
        (sum_add (T_out_edges p) F.T_encode (functions p)) in Hadjacency.
      rewrite (sum_add (T_sites_of p) F.T_encode (functions p)).
      rewrite <- (sum_flat_map (fun f => flat_map (resolve p) (sites_of p f))
        F.T_encode (functions p)) in Hadjacency.
      rewrite <- targets_partition in Hadjacency.
      time_cbn_all; nia.
    - apply N.mul_le_mono_r; exact graph_coefficient.
  Qed.

  (** Call graph construction has the aggregate reader and bit-width bound. *)
  Lemma call_graph_bigO : bigO (fun _ : P.t => True) call_graph_work T_call_graph.
  Proof.
    exists c_calls; intros p Htrue; pose proof (T_call_graph_le p); nia.
  Qed.
End CallsT.
