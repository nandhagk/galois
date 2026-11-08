(** * Primitive costs for the nested engine

    Callback prices, query sizes and encoded-key widths bound actual nested-machine calls.
    For example, one output includes both its value update and its delay-counter lookup and write.
    Builds on: FixpointNestedCost and public query, map, set and index cost contracts. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointNested FixpointNestedProof FixpointNestedCost.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module NestedPrimitive.

(** Primitive budgets contain sizes and client callback prices rather than owned-helper costs. *)
Record budget := Budget {
  query_nodes : nat;
  query_outputs : nat;
  declared_reads : nat;
  declared_sides : nat;
  encoding_ticks : N;
  key_digits : N;
  continuation_ticks : N;
  lattice_ticks : N;
  policy_ticks : N;
  system_ticks : N
}.

(** Relevant keys include code vertices and every declared input or output occurrence. *)
Definition key {X C A} (a : Analysis.t X C A) (p : Nested.code X) x : Prop :=
  In x (Nested.vertices p) \/ In x (NestedCost.universe a) \/
  exists c, In c (System.constraints (Analysis.system a)) /\ In x (deps (Analysis.static a) c).

(** The model bounds only primitive callbacks, encoded widths and query or metadata sizes. *)
Record model {X C A} (a : Analysis.t X C A) (p : Nested.code X) (b : budget) : Prop := Model {
  key_budget : forall x, key a p x ->
    (Cost.ticks (encode_c (Analysis.key_enc a) x) <= encoding_ticks b)%N /\
    (key_bits (Analysis.key_enc a) x <= key_digits b)%N;
  compare_budget : forall x y,
    (Cost.ticks (leb_c (Analysis.lat a) x y) <= lattice_ticks b)%N;
  join_budget : forall x y,
    (Cost.ticks (join_c (Analysis.lat a) x y) <= lattice_ticks b)%N;
  widen_budget : forall x y,
    (Cost.ticks (widen_c (Analysis.lat a) x y) <= lattice_ticks b)%N;
  policy_budget : forall x, In x (NestedCost.universe a) ->
    (Cost.ticks (Policy.widen_at_c (Analysis.policy a) x) <= policy_ticks b)%N;
  target_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (System.target_c (Analysis.system a) c) <= system_ticks b)%N;
  rhs_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (System.rhs_c (Analysis.system a) c) <= system_ticks b)%N;
  deps_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (System.deps_c (Analysis.static a) c) <= system_ticks b)%N;
  sides_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (System.side_targets_c (Analysis.static a) c) <= system_ticks b)%N;
  deps_size : forall c, In c (System.constraints (Analysis.system a)) ->
    length (deps (Analysis.static a) c) <= declared_reads b;
  sides_size : forall c, In c (System.constraints (Analysis.system a)) ->
    length (side_targets (Analysis.static a) c) <= declared_sides b;
  query_budget : forall m c, In c (System.constraints (Analysis.system a)) ->
    Query.within (continuation_ticks b)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m) (query_nodes b)
      (System.rhs (Analysis.system a) c);
  output_budget : forall m c, In c (System.constraints (Analysis.system a)) ->
    S (length (Query.sides (System.rhs (Analysis.system a) c)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m))) <= query_outputs b
}.

Definition access_k (b : budget) := (1 + encoding_ticks b + key_digits b)%N.
Definition output_k (b : budget) :=
  (5 * access_k b + 5 + policy_ticks b + 2 * lattice_ticks b)%N.
Definition evaluation_k (b : budget) :=
  (2 + 2 * system_ticks b +
    N.of_nat (query_nodes b) * (3 + access_k b + continuation_ticks b) +
    N.of_nat (query_outputs b) * output_k b)%N.

(** Code size counts all constructors, including empty bodies and suffixes. *)
Fixpoint nodes {X} (q : Nested.code X) : nat :=
  match q with
  | Nested.End => 1
  | Nested.Visit _ rest => S (nodes rest)
  | Nested.Component _ body rest => S (nodes body + nodes rest)
  end.

Definition walk_k {X} (q : Nested.code X) := (N.of_nat (nodes q) * (1 + N.of_nat (nodes q)))%N.

Definition non_index_k {X C A} (a : Analysis.t X C A) (p : Nested.code X) (b : budget) :=
  (2 * walk_k p +
    2 * N.of_nat (length (Nested.vertices p)) * (3 + encoding_ticks b + key_digits b) +
    N.of_nat (length (System.constraints (Analysis.system a))) *
      (2 + system_ticks b + access_k b) +
    N.of_nat (Policy.delay (Analysis.policy a)))%N.

(** The driver bound uses code size and declared row/output counts without preparing an index. *)
Definition driver_bound {X C A} (a : Analysis.t X C A) (HT : Terminates.t a)
    (p : Nested.code X) (b : budget) :=
  (1 + length (Nested.vertices p) * (length (System.constraints (Analysis.system a)) + 3)) *
    (1 + (Nested.depth p + 1) * bound (Terminates.hgt HT) *
      (length (System.constraints (Analysis.system a)) * (1 + declared_sides b))).

(** Both inventories fit inside the code-constructor count, retaining duplicate entries. *)
Theorem inventory_size {X} (q : Nested.code X) :
  length (Nested.heads q) <= length (Nested.vertices q) /\
  length (Nested.vertices q) <= nodes q.
Proof.
  induction q; cbn [Nested.heads Nested.vertices nodes length];
    rewrite ?length_app; intuition lia.
Qed.

(** Every component head is also in the traversal inventory. *)
Theorem heads_vertices {X} (q : Nested.code X) :
  incl (Nested.heads q) (Nested.vertices q).
Proof.
  induction q as [|x rest IH|h body IHbody rest IHrest]; intros y Hy.
  - contradiction.
  - right; apply IH, Hy.
  - cbn [Nested.heads] in Hy; cbn [Nested.vertices].
    destruct Hy as [<-|Hy]; [now left|].
    right; apply in_app_iff in Hy as [Hy|Hy]; apply in_or_app;
      [left; apply IHbody|right; apply IHrest]; exact Hy.
Qed.

(** Charged metadata walks are bounded by code size, including each actual append traversal. *)
Theorem metadata_cost {X} (q : Nested.code X) :
  (Cost.ticks (Nested.vertices_c q) <= walk_k q)%N /\
  (Cost.ticks (Nested.heads_c q) <= walk_k q)%N.
Proof.
  induction q as [|x rest [IHv IHh]|h body [IHvb IHhb] rest [IHvr IHhr]].
  - split; change (1 <= 2)%N; lia.
  - unfold walk_k in *; cbn [Nested.vertices_c Nested.heads_c nodes].
    autorewrite with galois_cost; rewrite Nat2N.inj_succ; split; nia.
  - pose proof (inventory_size body) as [Hheads Hvertices].
    unfold walk_k in *; cbn [Nested.vertices_c Nested.heads_c nodes].
    autorewrite with galois_cost.
    rewrite Nested.vertices_equation, Nested.heads_equation.
    rewrite Nat2N.inj_succ, Nat2N.inj_add; split; nia.
Qed.

Section Calls.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (b : budget) (HM : model a p b).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let U := NestedCost.universe a.

Local Lemma filter_size {T} (f : T -> bool) xs : length (filter f xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn [filter length]; [lia|].
  destruct (f x); cbn [length]; lia.
Qed.

(** Every actual contributor bucket retains at most the original row-occurrence count. *)
Theorem bucket_size x :
  length (contributors_of EX (index_system EX S (Analysis.static a)) x) <=
    length (System.constraints S).
Proof.
  rewrite (contributors_occurrences EX (Analysis.key_laws Hl) S (Analysis.static a) x).
  apply filter_size.
Qed.

(** Code geometry is bounded using actual row multiplicity and the number of visited vertices. *)
Theorem work_size :
  NestedCost.work EX (index_system EX S (Analysis.static a)) p <=
    length (Nested.vertices p) * (length (System.constraints S) + 3).
Proof.
  assert (Hwork : forall q,
    NestedCost.work EX (index_system EX S (Analysis.static a)) q <=
      length (Nested.vertices q) * (length (System.constraints S) + 3)).
  { intro q; induction q as [|x rest IH|h body IHbody rest IHrest];
      cbn [NestedCost.work Nested.vertices length]; rewrite ?length_app.
    - lia.
    - pose proof (bucket_size x); nia.
    - pose proof (bucket_size h); nia. }
  apply Hwork.
Qed.

(** Static output occurrences are bounded without discarding repeated rows or side entries. *)
Theorem universe_size :
  length U <= length (System.constraints S) * (1 + declared_sides b).
Proof.
  unfold U, NestedCost.universe; fold S.
  assert (Hrows : forall cs, incl cs (System.constraints S) ->
    length (flat_map (fun c => System.target S c :: side_targets (Analysis.static a) c) cs) <=
      length cs * (1 + declared_sides b)).
  { intro cs; induction cs as [|c cs IH]; intro Hlisted; [cbn; lia|].
    assert (Hc : In c (System.constraints S)) by (apply Hlisted; now left).
    pose proof (sides_size _ _ _ HM c Hc) as Hsides.
    specialize (IH ltac:(intros row Hr; apply Hlisted; now right)).
    cbn [flat_map]; rewrite length_app; cbn [length]; nia. }
  apply Hrows; intros c Hc; exact Hc.
Qed.

(** A map lookup is bounded by its actual encoder price and encoded key width. *)
Theorem get_cost {V} (m : Map.t X V) x :
  key a p x -> (Cost.ticks (Map.get_c EX x m) <= access_k b)%N.
Proof.
  intro Hkey; destruct (key_budget _ _ _ HM x Hkey) as [He Hb].
  rewrite Map.get_cost; fold (key_bits EX x); unfold access_k; unfold EX in *; lia.
Qed.

(** A map write has the same width budget regardless of the current map's contents. *)
Theorem set_cost {V} (m : Map.t X V) x v :
  key a p x -> (Cost.ticks (Map.set_c EX x v m) <= access_k b)%N.
Proof.
  intro Hkey; destruct (key_budget _ _ _ HM x Hkey) as [He Hb].
  rewrite Map.set_cost; fold (key_bits EX x); unfold access_k; unfold EX in *; lia.
Qed.

(** Output operators include head membership, policy invocation and the chosen lattice callback. *)
Theorem operator_cost hs delay x count old value :
  In x U ->
  (Cost.ticks (Nested.op_c a hs delay x count old value) <=
    access_k b + 2 + policy_ticks b + lattice_ticks b)%N.
Proof.
  intro Hx.
  pose proof (get_cost hs x (or_intror (or_introl Hx))) as Hmem.
  pose proof (policy_budget _ _ _ HM x Hx) as Hpolicy.
  pose proof (join_budget _ _ _ HM old value) as Hjoin.
  pose proof (widen_budget _ _ _ HM old value) as Hwiden.
  rewrite Map.get_cost in Hmem.
  unfold Nested.op_c; autorewrite with galois_cost.
  rewrite FinSet.mem_cost; fold EX.
  destruct (Cost.value (FinSet.mem_c EX x hs) &&
    Cost.value (Policy.widen_at_c (Analysis.policy a) x) && N.leb delay count);
    autorewrite with galois_cost; lia.
Qed.

(** Every ordered output retains its update rule, counter lookup and possible counter write. *)
Theorem updates_cost hs delay outs m counts :
  (forall x v, In (x, v) outs -> In x U) ->
  (Cost.ticks (Nested.updates_c a hs delay outs m counts) <=
    N.of_nat (length outs) * output_k b)%N.
Proof.
  revert m counts; induction outs as [|[x value] rest IH]; intros m counts Hkeys.
  - reflexivity.
  - assert (Hx : In x U) by exact (Hkeys x value (or_introl eq_refl)).
    assert (Hrest : forall y v, In (y, v) rest -> In y U).
    { intros y v Hin; exact (Hkeys y v (or_intror Hin)). }
    pose proof (get_cost counts x (or_intror (or_introl Hx))) as Hcount.
    pose proof (get_cost m x (or_intror (or_introl Hx))) as Hlookup.
    pose proof (set_cost m x (Cost.value
      (Nested.op_c a hs delay x (Map.find_or EX 0%N x counts) (lookup EX L m x) value))
      (or_intror (or_introl Hx))) as Hwrite.
    pose proof (set_cost counts x (N.succ (Map.find_or EX 0%N x counts))
      (or_intror (or_introl Hx))) as Hcounter.
    pose proof (operator_cost hs delay x (Map.find_or EX 0%N x counts)
      (lookup EX L m x) value Hx) as Hop.
    pose proof (compare_budget _ _ _ HM value (lookup EX L m x)) as Hcompare.
    assert (Hrule : (Cost.ticks (Update.rule_c EX L
      (Nested.op_c a hs delay x (Map.find_or EX 0%N x counts)) m x value) <=
      3 * access_k b + 4 + policy_ticks b + 2 * lattice_ticks b)%N).
    { rewrite Update.rule_cost, lookup_cost.
      destruct (leb L value (lookup EX L m x)); fold EX L in Hcompare |- *; lia. }
    cbn [Nested.updates_c]; autorewrite with galois_cost.
    fold EX L.
    fold (Map.find_or EX 0%N x counts).
    fold (Update.rule EX L
      (Nested.op_c a hs delay x (Map.find_or EX 0%N x counts)) m x value).
    set (first := Update.rule EX L
      (Nested.op_c a hs delay x (Map.find_or EX 0%N x counts)) m x value).
    rewrite Map.find_or_cost.
    destruct (snd first);
      autorewrite with galois_cost; fold (Map.find_or EX 0%N x counts) in *.
    + fold (Map.set EX x (N.succ (Map.find_or EX 0%N x counts)) counts).
      specialize (IH (fst first) (Map.set EX x (N.succ (Map.find_or EX 0%N x counts)) counts)
        Hrest); unfold output_k in IH |- *; cbn [length]; rewrite Nat2N.inj_succ; nia.
    + specialize (IH (fst first) counts Hrest).
      unfold output_k in IH |- *; cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

Local Lemma output_keys c m x v :
  In c (System.constraints S) ->
  In (x, v) (fst (Eval.outputs S c (lookup EX L m))) -> In x U.
Proof.
  intros Hc Hout; unfold U, NestedCost.universe; apply in_flat_map.
  exists c; split; [exact Hc|].
  rewrite Eval.outputs_spec in Hout; cbn [fst] in Hout.
  destruct Hout as [Hsame|Hside]; [injection Hsame as <- <-; now left|].
  right; apply (System.sides_within (Analysis.static_law Hl) c (lookup EX L m)).
  apply in_map_iff; exists (x, v); auto.
Qed.

(** Complete evaluation/update envelopes follow from selected query paths and primitive budgets. *)
Theorem evaluation_cost hs delay c m counts :
  In c (System.constraints S) ->
  (Cost.ticks (Eval.outputs_c S (lookup_c EX L m) c) +
    Cost.ticks (Nested.updates_c a hs delay
      (fst (Eval.outputs S c (lookup EX L m))) m counts) <= evaluation_k b)%N.
Proof.
  intro Hc.
  assert (Hreads : forall x, In x (Query.reads (System.rhs S c) (lookup EX L m)) ->
    (Cost.ticks (lookup_c EX L m x) <= access_k b)%N).
  { intros x Hread; rewrite lookup_cost; apply get_cost.
    right; right; exists c; split; [exact Hc|].
    exact (System.reads_within (Analysis.static_law Hl) c (lookup EX L m) x Hread). }
  pose proof (Query.run_c_cost_on (System.rhs S c) (lookup_c EX L m)
    (lookup EX L m) (query_nodes b) (continuation_ticks b) (access_k b)
    (query_budget _ _ _ HM m c Hc) (fun _ => eq_refl) Hreads) as Hquery.
  pose proof (target_budget _ _ _ HM c Hc) as Htarget.
  pose proof (rhs_budget _ _ _ HM c Hc) as Hrhs.
  pose proof (updates_cost hs delay (fst (Eval.outputs S c (lookup EX L m))) m counts
    (fun x v Hout => output_keys c m x v Hc Hout)) as Hupdates.
  pose proof (output_budget _ _ _ HM m c Hc) as Houts.
  fold EX L S in Htarget, Hrhs, Houts.
  assert (Hlength : length (fst (Eval.outputs S c (lookup EX L m))) <= query_outputs b).
  { rewrite Eval.outputs_spec; cbn [fst length]; exact Houts. }
  rewrite Eval.outputs_cost; unfold evaluation_k.
  nia.
Qed.

(** Coverage retains distinct recursion and target-invocation ticks on every examined row. *)
Theorem cover_cost vs cs :
  incl cs (System.constraints S) ->
  (Cost.ticks (Nested.cover_c a vs cs) <=
    N.of_nat (length cs) * (2 + system_ticks b + access_k b))%N.
Proof.
  induction cs as [|c cs IH]; intro Hlisted; [reflexivity|].
  assert (Hc : In c (System.constraints S)) by (apply Hlisted; now left).
  assert (Hkey : key a p (System.target S c)).
  { right; left; unfold NestedCost.universe; apply in_flat_map.
    exists c; split; [exact Hc|now left]. }
  pose proof (get_cost vs _ Hkey) as Hmem.
  rewrite Map.get_cost in Hmem.
  pose proof (target_budget _ _ _ HM c Hc) as Htarget.
  specialize (IH ltac:(intros row Hr; apply Hlisted; now right)).
  cbn [Nested.cover_c]; autorewrite with galois_cost.
  fold EX S; fold (System.target S c).
  destruct (Cost.value (FinSet.mem_c EX (System.target S c) vs));
    autorewrite with galois_cost; rewrite FinSet.mem_cost;
    fold EX S in Htarget |- *; cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Set preparation prices each inventory cell and every actual encoded-key insertion. *)
Theorem vertex_set_cost :
  (Cost.ticks (FinSet.of_list_c EX (Nested.vertices p)) <=
    N.of_nat (length (Nested.vertices p)) * (3 + encoding_ticks b + key_digits b))%N.
Proof.
  apply (FinSet.of_list_numeric_cost Map.cost_laws_hold).
  intros x Hx; apply (key_budget _ _ _ HM x); now left.
Qed.

(** Head-set preparation uses the same finite inventory key budget. *)
Theorem head_set_cost :
  (Cost.ticks (FinSet.of_list_c EX (Nested.heads p)) <=
    N.of_nat (length (Nested.vertices p)) * (3 + encoding_ticks b + key_digits b))%N.
Proof.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold EX (Nested.heads p)
    (encoding_ticks b) (key_digits b)
    ltac:(intros x Hx; apply (key_budget _ _ _ HM x); left;
      apply heads_vertices, Hx)) as Hcost.
  pose proof (proj1 (inventory_size p)); nia.
Qed.

End Calls.

(** Unary conversion charges exactly one tick per traversed delay constructor. *)
Theorem delay_cost n : Cost.ticks (Nested.delay_c n) = N.of_nat n.
Proof.
  induction n; [reflexivity|].
  cbn [Nested.delay_c]; autorewrite with galois_cost; rewrite IHn, Nat2N.inj_succ; lia.
Qed.

Section Cursor.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (ix : sys_index X C) (hs : FinSet.t X) (delay : N).

(** Runtime code pointers and saved continuations contain only keys from the supplied code. *)
Definition cursor_keys (s : Nested.State.t X C A) : Prop :=
  incl (Nested.vertices (Nested.State.pointer s)) (Nested.vertices p) /\
  Forall (fun f =>
    incl (Nested.vertices (Nested.Frame.pass f)) (Nested.vertices p) /\
    incl (Nested.vertices (Nested.Frame.rest f)) (Nested.vertices p)) (Nested.State.frames s).

Local Lemma component_keys (h : X) (body rest : Nested.code X) (xs : list X) :
  incl (Nested.vertices (Nested.Component h body rest)) xs ->
  incl (Nested.vertices (Nested.Visit h body)) xs /\ incl (Nested.vertices rest) xs.
Proof.
  intro Hkeys; split.
  - intros x Hx; apply Hkeys; cbn [Nested.vertices] in Hx |- *.
    destruct Hx as [<-|Hx]; [now left|right; apply in_or_app; now left].
  - intros x Hx; apply Hkeys; right; apply in_or_app; now right.
Qed.

Local Lemma cursor_step s next :
  cursor_keys s -> Nested.step a p ix hs delay s = inl next -> cursor_keys next.
Proof.
  intros [Hptr Hframes] Hstep; unfold Nested.step, Nested.step_c in Hstep.
  destruct (Nested.State.ready s) as [|c rest].
  2: { autorewrite with galois_cost in Hstep; injection Hstep as <-; now split. }
  destruct (Nested.State.pointer s) as [|x rest|h body rest].
  - destruct (Nested.State.frames s) as [|f fs].
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s)); [discriminate|].
      injection Hstep as <-; split; [intros y Hy; exact Hy|constructor].
    + inversion Hframes as [|g gs [Hpass Hrest] Htail]; subst g gs.
      destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        injection Hstep as <-; split; [exact Hrest|exact Htail|exact Hpass|].
      constructor; [exact (conj Hpass Hrest)|exact Htail].
  - autorewrite with galois_cost in Hstep; injection Hstep as <-; split; [|exact Hframes].
    intros y Hy; apply Hptr; now right.
  - destruct (component_keys h body rest (Nested.vertices p) Hptr) as [Hpass Hrest].
    injection Hstep as <-; split; [exact Hpass|].
    constructor; [exact (conj Hpass Hrest)|exact Hframes].
Qed.

(** Every actual iterator continuation prefix preserves the finite code-key inventory. *)
Theorem prefix_cursor n last :
  runs (Nested.step_c a p ix hs delay) n (Nested.start p) (inl last) -> cursor_keys last.
Proof.
  intro Hrun.
  assert (Hstep : forall s, cursor_keys s ->
    match Cost.value (Nested.step_c a p ix hs delay s) with
    | inl next => cursor_keys next
    | inr _ => True
    end).
  { intros s Hs; fold (Nested.step a p ix hs delay s).
    destruct (Nested.step a p ix hs delay s) as [next|done] eqn:Hstep; [|constructor].
    exact (cursor_step s next Hs Hstep). }
  exact (NestedProof.runs_property (Nested.step_c a p ix hs delay)
    cursor_keys (fun _ => True) Hstep n (Nested.start p) (inl last) Hrun
    ltac:(split; [intros x Hx; exact Hx|constructor])).
Qed.

End Cursor.

Section Preparation.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (b : budget) (HM : model a p b).
Let EX := Analysis.key_enc a.
Let ix := index_system EX (Analysis.system a) (Analysis.static a).
Let hs := FinSet.of_list EX (Nested.heads p).
Let delay := N.of_nat (Policy.delay (Analysis.policy a)).

(** Reached dispatch keys have the finite code inventory's lookup price. *)
Theorem bucket_cost s x rest :
  NestedCost.prefix a p s -> Nested.State.pointer s = Nested.Visit x rest ->
  (Cost.ticks (contributors_of_c EX ix x) <= access_k b)%N.
Proof.
  intros [n Hprefix] Hpointer; rewrite contributors_cost; apply (get_cost a p b HM).
  left.
  destruct (prefix_cursor a p ix hs delay n s Hprefix) as [Hkeys Hframes].
  apply Hkeys; rewrite Hpointer; now left.
Qed.

(** Non-index preparation costs follow from primitive widths, code size and callback data. *)
Theorem non_index_cost :
  (Cost.ticks (Nested.vertices_c p) +
    Cost.ticks (FinSet.of_list_c EX (Nested.vertices p)) +
    Cost.ticks (Nested.cover_c a (FinSet.of_list EX (Nested.vertices p))
      (System.constraints (Analysis.system a))) +
    Cost.ticks (Nested.heads_c p) +
    Cost.ticks (FinSet.of_list_c EX (Nested.heads p)) +
    Cost.ticks (Nested.delay_c (Policy.delay (Analysis.policy a))) <= non_index_k a p b)%N.
Proof.
  destruct (metadata_cost p) as [Hv Hh].
  pose proof (vertex_set_cost a p b HM) as Hvs.
  pose proof (head_set_cost a p b HM) as Hhs.
  pose proof (cover_cost a p b HM (FinSet.of_list EX (Nested.vertices p))
    (System.constraints (Analysis.system a)) (fun c Hc => Hc)) as Hcover.
  rewrite delay_cost.
  unfold non_index_k; fold EX in Hvs, Hhs, Hcover; nia.
Qed.

End Preparation.

Section Composition.
Context {X C A : Type} (a : Analysis.t X C A) (p : Nested.code X)
  (Hl : Analysis.laws a) (HT : Terminates.t a)
  (b : budget) (HM : model a p b).
Let EX := Analysis.key_enc a.
Let ix := index_system EX (Analysis.system a) (Analysis.static a).
Let hs := FinSet.of_list EX (Nested.heads p).
Let delay := N.of_nat (Policy.delay (Analysis.policy a)).

(** The existing exact fuel budget is bounded entirely by primitive/code size data. *)
Theorem fuel_budget_size :
  NestedCost.fuel_budget a HT p <= driver_bound a HT p b.
Proof.
  pose proof (work_size a p Hl) as Hwork.
  pose proof (universe_size a p b HM) as Houtputs.
  unfold NestedCost.fuel_budget, driver_bound; fold EX in Hwork |- *.
  apply Nat.mul_le_mono; [lia|].
  apply Nat.add_le_mono_l.
  replace ((Nested.depth p + 1) *
    (length (NestedCost.universe a) * bound (Terminates.hgt HT))) with
    (((Nested.depth p + 1) * bound (Terminates.hgt HT)) *
      length (NestedCost.universe a)) by nia.
  apply Nat.mul_le_mono_l; exact Houtputs.
Qed.

(** Primitive local calls construct the relative model after the owner prices index setup. *)
Theorem relative_model index_k :
  (Cost.ticks (index_system_c EX (Analysis.system a) (Analysis.static a)) <= index_k)%N ->
  NestedCost.cost_model a HT p (evaluation_k b) (access_k b) (non_index_k a p b + index_k)%N.
Proof.
  intro Hindex; constructor.
  - intros s c rest Hprefix Hvalid Hready.
    assert (Hc : In c (System.constraints (Analysis.system a))).
    { destruct Hvalid as [Hcontrol [Hgood Hlisted]]; apply Hlisted; rewrite Hready; now left. }
    exact (evaluation_cost a p Hl b HM hs delay c
      (Nested.State.values s) (Nested.State.counters s) Hc).
  - intros s x rest Hprefix Hvalid Hready Hpointer.
    exact (bucket_cost a p b HM s x rest Hprefix Hpointer).
  - pose proof (non_index_cost a p b HM) as Hsetup.
    fold EX in Hsetup |- *; nia.
Qed.

(** The relative whole-run bound now needs only the separately owned index-preparation price. *)
Theorem cost_from_index fuel index_k :
  Analysis.joining a -> Nested.code_ok a p ->
  (Cost.ticks (index_system_c EX (Analysis.system a) (Analysis.static a)) <= index_k)%N ->
  (Cost.ticks (Nested.run_c a p fuel) <= non_index_k a p b + index_k +
    (evaluation_k b + access_k b + 2) *
      (N.of_nat (NestedCost.fuel_budget a HT p) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  intros Hjoining Hcode Hindex.
  exact (NestedCost.nested_cost a Hl HT Hjoining p fuel
    (evaluation_k b) (access_k b) (non_index_k a p b + index_k)%N Hcode
    (relative_model index_k Hindex)).
Qed.

End Composition.

End NestedPrimitive.
Import NestedPrimitive.
