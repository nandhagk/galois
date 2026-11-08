(** * Loop tables from hierarchy tokens

    Loop tables index the headers and innermost ownership of the same hierarchy used by the WTO.
    For example, a nested opening records its current header as its immediate loop parent.
    Builds on: GraphHierSpec and GraphHier. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphHierSpec GraphHier
  GraphHierExact GraphWeakOrderFacts GraphHierCycles GraphLoopStructure.
Import List.ListNotations Cost.Notations.

Module LoopForest.

Definition own_c v stack (owners : Map.t positive positive) :=
  match stack with
  | [] => Cost.ret owners
  | h :: _ => Map.set_c positive_encoding v h owners
  end.

Definition own v stack owners := Cost.value (own_c v stack owners).

(** Empty enclosing stacks leave ownership absent; nonempty stacks record their actual head. *)
Theorem own_equation v stack owners :
  own v stack owners =
  match stack with
  | [] => owners
  | h :: _ => Map.set positive_encoding v h owners
  end.
Proof.
  destruct stack; reflexivity.
Qed.

(** One token pass constructs both partial maps and the outer-first header listing. *)
Fixpoint scan_c stack w : Cost.t Loops.t :=
  match w with
  | [] => Cost.ret (Loops.Make Map.empty Map.empty [])
  | Wto.WVertex v :: rest =>
    Cost.step ;;
    let* tail := scan_c stack rest in
    let* owners := own_c v stack (Loops.innermost tail) in
    Cost.ret (Loops.Make (Loops.loop_parent tail) owners (Loops.headers tail))
  | Wto.WOpen h :: rest =>
    Cost.step ;;
    let* tail := scan_c (h :: stack) rest in
    let* owners := Map.set_c positive_encoding h h (Loops.innermost tail) in
    let* parents := own_c h stack (Loops.loop_parent tail) in
    Cost.ret (Loops.Make parents owners (h :: Loops.headers tail))
  | Wto.WClose :: rest => Cost.step ;; scan_c (tl stack) rest
  end.

Definition scan stack w := Cost.value (scan_c stack w).

(** Token scanning exposes only the two partial-map insertions justified by its current stack. *)
Theorem scan_equation stack w :
  scan stack w =
  match w with
  | [] => Loops.Make Map.empty Map.empty []
  | Wto.WVertex v :: rest =>
    let tail := scan stack rest in
    Loops.Make (Loops.loop_parent tail) (own v stack (Loops.innermost tail))
      (Loops.headers tail)
  | Wto.WOpen h :: rest =>
    let tail := scan (h :: stack) rest in
    Loops.Make (own h stack (Loops.loop_parent tail))
      (Map.set positive_encoding h h (Loops.innermost tail)) (h :: Loops.headers tail)
  | Wto.WClose :: rest => scan (tl stack) rest
  end.
Proof.
  destruct w as [|[v|h|] rest]; reflexivity.
Qed.

(** Projection construction emits and scans the supplied forest without another SCC computation. *)
Definition of_forest_c f :=
  let* tokens := Wto.of_forest_c f in scan_c [] tokens.

Definition of_forest f := Cost.value (of_forest_c f).

(** Loop projection is the table scan of that exact forest's token projection. *)
Theorem of_forest_equation f : of_forest f = scan [] (Wto.of_forest f).
Proof.
  reflexivity.
Qed.

Definition compute_c {V E} (p : Prepared.t V E) roots :=
  let* forest := HierRun.compute_c p (Scope.Make FinSet.empty None) roots in
  of_forest_c forest.

Definition compute {V E} (p : Prepared.t V E) roots := Cost.value (compute_c p roots).

(** Loop production projects the same hierarchy producer used for weak-order production. *)
Theorem compute_equation {V E} (p : Prepared.t V E) roots :
  compute p roots =
    of_forest (HierRun.compute p (Scope.Make FinSet.empty None) roots).
Proof.
  unfold compute, compute_c. rewrite Cost.value_bind. reflexivity.
Qed.

Local Lemma own_wf v stack m :
  Map.wf positive_encoding m -> Map.wf positive_encoding (own v stack m).
Proof.
  intro Hwf. rewrite own_equation. destruct stack; [exact Hwf|now apply Map.wf_set].
Qed.

(** Token scanning always constructs canonical parent and ownership maps. *)
Theorem scan_wf stack w :
  Map.wf positive_encoding (Loops.loop_parent (scan stack w)) /\
    Map.wf positive_encoding (Loops.innermost (scan stack w)).
Proof.
  revert stack. induction w as [|[v|h|] rest IH]; intro stack; rewrite scan_equation.
  - split; apply Map.wf_empty.
  - cbn [Loops.loop_parent Loops.innermost]. split; [exact (proj1 (IH stack))|].
    apply own_wf. exact (proj2 (IH stack)).
  - cbn [Loops.loop_parent Loops.innermost]. split.
    + apply own_wf. exact (proj1 (IH (h :: stack))).
    + apply Map.wf_set. exact (proj2 (IH (h :: stack))).
  - apply IH.
Qed.

(** Every stored header is exactly an opening token, including an empty-body self-loop. *)
Theorem scan_headers stack w h :
  In h (Loops.headers (scan stack w)) <-> In (Wto.WOpen h) w.
Proof.
  revert stack. induction w as [|[v|head|] rest IH]; intro stack; rewrite scan_equation;
    cbn [Loops.headers In].
  - reflexivity.
  - rewrite IH. split; [now right|intros [Hbad|Hin]; [discriminate|exact Hin]].
  - rewrite IH. split; intros [Heq|Hin].
    + left. now subst head.
    + now right.
    + left. now inversion Heq.
    + now right.
  - rewrite IH. split; [now right|intros [Hbad|Hin]; [discriminate|exact Hin]].
Qed.

(** Every header of a token scan occurs in that token list's vertex order. *)
Theorem header_in_order stack w h :
  In h (Loops.headers (scan stack w)) -> In h (Wto.order w).
Proof.
  rewrite scan_headers. revert stack.
  induction w as [|[v|head|] rest IH]; intros stack Hin; [contradiction| | |];
    rewrite Wto.order_equation.
  - destruct Hin as [Hbad|Hin]; [discriminate|right; now apply (IH stack)].
  - destruct Hin as [Heq|Hin]; [inversion Heq; now left|].
    right. now apply (IH (head :: stack)).
  - destruct Hin as [Hbad|Hin]; [discriminate|now apply (IH (tl stack))].
Qed.

(** Duplicate-free token orders have duplicate-free header listings. *)
Theorem scan_headers_unique stack w :
  NoDup (Wto.order w) -> NoDup (Loops.headers (scan stack w)).
Proof.
  revert stack. induction w as [|[v|h|] rest IH]; intros stack Hnodup;
    rewrite scan_equation; rewrite Wto.order_equation in Hnodup.
  - constructor.
  - cbn [Loops.headers]. inversion Hnodup as [|head tail Hfresh Htail]; subst.
    now apply IH.
  - cbn [Loops.headers]. inversion Hnodup as [|head tail Hfresh Htail]; subst.
    constructor; [|now apply IH].
    intro Hin. apply Hfresh. exact (header_in_order (h :: stack) rest h Hin).
  - now apply IH.
Qed.

Local Lemma own_get_spec v stack m :
  Map.wf positive_encoding m -> Map.get positive_encoding v m = None ->
  forall x h,
  Map.get positive_encoding x (own v stack m) = Some h <->
    (x = v /\ exists rest, stack = h :: rest) \/
      Map.get positive_encoding x m = Some h.
Proof.
  intros Hwf Hnone x h. rewrite own_equation.
  destruct stack as [|head rest].
  - split; [now right|intros [[_ [tail Hbad]]|Hget]; [discriminate|exact Hget]].
  - destruct (Pos.eq_dec x v) as [->|Hne].
    + rewrite Map.get_set_same by exact Hwf. rewrite Hnone. split.
      * intro Heq. inversion Heq; subst head. left. split; [reflexivity|now exists rest].
      * intros [[_ [tail Heq]]|Hbad]; [now inversion Heq|discriminate].
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
        by assumption. split; [now right|].
      intros [[Heq _]|Hget]; [contradiction|exact Hget].
Qed.

Local Lemma annotation_cons (v : positive) (stack : list positive)
    (rows : list (positive * list positive)) x h :
  (x = v /\ exists rest, stack = h :: rest) \/
    (exists rest, In (x, h :: rest) rows) <->
  exists rest, In (x, h :: rest) ((v, stack) :: rows).
Proof.
  split.
  - intros [[-> [rest ->]]|[rest Hin]]; exists rest; [now left|now right].
  - intros [rest [Heq|Hin]].
    + inversion Heq; subst. left. split; [reflexivity|now exists rest].
    + right. now exists rest.
Qed.

Local Lemma annotation_member stack w v heads :
  In (v, heads) (Wto.annotate stack w) -> In v (Wto.order w).
Proof.
  intro Hin. rewrite <- (WeakOrderFacts.annotation_order w stack).
  apply in_map with (f := fst) in Hin. exact Hin.
Qed.

(** Scanning indexes exactly the innermost head of each nonempty annotation stack. *)
Theorem scan_innermost stack w :
  NoDup (Wto.order w) -> forall v h,
  Map.get positive_encoding v (Loops.innermost (scan stack w)) = Some h <->
    exists rest, In (v, h :: rest) (Wto.annotate stack w).
Proof.
  revert stack. induction w as [|[x|x|] rest IH]; intros stack Hnodup v h;
    rewrite scan_equation, Wto.annotate_equation.
  - cbn [Loops.innermost]. rewrite Map.get_empty.
    split; [discriminate|intros [tail Hfalse]; contradiction].
  - rewrite Wto.order_equation in Hnodup.
    inversion Hnodup as [|head tail Hfresh Htail]; subst.
    cbn [Loops.innermost].
    assert (Hnone : Map.get positive_encoding x (Loops.innermost (scan stack rest)) = None).
    { destruct (Map.get positive_encoding x (Loops.innermost (scan stack rest)))
        as [head|] eqn:Hget; [|reflexivity].
      apply (proj1 (IH stack Htail x head)) in Hget.
      destruct Hget as [ancestors Hrow].
      exfalso. exact (Hfresh (annotation_member stack rest x _ Hrow)). }
    rewrite own_get_spec by (try apply (proj2 (scan_wf stack rest)); exact Hnone).
    rewrite (IH stack Htail). apply annotation_cons.
  - rewrite Wto.order_equation in Hnodup.
    inversion Hnodup as [|head tail Hfresh Htail]; subst.
    cbn [Loops.innermost].
    assert (Hnone :
      Map.get positive_encoding x (Loops.innermost (scan (x :: stack) rest)) = None).
    { destruct (Map.get positive_encoding x (Loops.innermost (scan (x :: stack) rest)))
        as [head|] eqn:Hget; [|reflexivity].
      apply (proj1 (IH (x :: stack) Htail x head)) in Hget.
      destruct Hget as [ancestors Hrow].
      exfalso. exact (Hfresh (annotation_member (x :: stack) rest x _ Hrow)). }
    rewrite <- (own_equation x (x :: stack) _).
    rewrite own_get_spec by (try apply (proj2 (scan_wf (x :: stack) rest)); exact Hnone).
    rewrite (IH (x :: stack) Htail). apply annotation_cons.
  - rewrite Wto.order_equation in Hnodup. apply IH, Hnodup.
Qed.

(** An opening occurrence records the enclosing stack immediately before its own push. *)
Inductive opening : list positive -> list Wto.token -> positive -> list positive -> Prop :=
  | opening_here : forall stack h rest, opening stack (Wto.WOpen h :: rest) h stack
  | opening_vertex : forall stack v rest h ancestors,
      opening stack rest h ancestors -> opening stack (Wto.WVertex v :: rest) h ancestors
  | opening_open : forall stack v rest h ancestors,
      opening (v :: stack) rest h ancestors -> opening stack (Wto.WOpen v :: rest) h ancestors
  | opening_close : forall stack rest h ancestors,
      opening (tl stack) rest h ancestors -> opening stack (Wto.WClose :: rest) h ancestors.

(** Opening evidence identifies an actual opening token in the same token list. *)
Theorem opening_token stack w h ancestors :
  opening stack w h ancestors -> In (Wto.WOpen h) w.
Proof.
  intro Hopen. induction Hopen; [now left|now right|now right|now right].
Qed.

(** Every opening token has its actual incoming enclosing stack. *)
Theorem token_opening stack w h :
  In (Wto.WOpen h) w -> exists ancestors, opening stack w h ancestors.
Proof.
  revert stack. induction w as [|[v|v|] rest IH]; intros stack Hin; [contradiction| | |].
  - destruct Hin as [Hbad|Hin]; [discriminate|].
    destruct (IH stack Hin) as [ancestors Hopen]. exists ancestors. now constructor.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. exists stack. constructor.
    + destruct (IH (v :: stack) Hin) as [ancestors Hopen].
      exists ancestors. now apply opening_open.
  - destruct Hin as [Hbad|Hin]; [discriminate|].
    destruct (IH (tl stack) Hin) as [ancestors Hopen]. exists ancestors. now constructor.
Qed.

(** Opening annotations place the opened header at the front of its actual enclosing stack. *)
Theorem opening_row stack w h ancestors :
  opening stack w h ancestors ->
    In (h, h :: ancestors) (Wto.annotate stack w).
Proof.
  intro Hopen. induction Hopen; rewrite Wto.annotate_equation.
  - now left.
  - now right.
  - now right.
  - exact IHHopen.
Qed.

(** Parent lookups correspond exactly to nonempty incoming stacks at opening occurrences. *)
Theorem scan_parent stack w :
  NoDup (Wto.order w) -> forall h outer,
  Map.get positive_encoding h (Loops.loop_parent (scan stack w)) = Some outer <->
    exists rest, opening stack w h (outer :: rest).
Proof.
  revert stack. induction w as [|[v|v|] rest IH]; intros stack Hnodup h outer;
    rewrite scan_equation.
  - cbn [Loops.loop_parent]. rewrite Map.get_empty. split; [discriminate|].
    intros [ancestors Hopen]. inversion Hopen.
  - rewrite Wto.order_equation in Hnodup.
    inversion Hnodup as [|head tail Hfresh Htail]; subst.
    cbn [Loops.loop_parent]. rewrite (IH stack Htail). split.
    + intros [ancestors Hopen]. exists ancestors. now apply opening_vertex.
    + intros [ancestors Hopen]. inversion Hopen; subst. eauto.
  - rewrite Wto.order_equation in Hnodup.
    inversion Hnodup as [|head tail Hfresh Htail]; subst.
    cbn [Loops.loop_parent].
    assert (Hnone :
      Map.get positive_encoding v (Loops.loop_parent (scan (v :: stack) rest)) = None).
    { destruct (Map.get positive_encoding v (Loops.loop_parent (scan (v :: stack) rest)))
        as [parent|] eqn:Hget; [|reflexivity].
      apply (proj1 (IH (v :: stack) Htail v parent)) in Hget.
      destruct Hget as [ancestors Hopen].
      exfalso. apply Hfresh. apply (header_in_order (v :: stack) rest v).
      rewrite scan_headers. exact (opening_token _ _ _ _ Hopen). }
    rewrite own_get_spec by (try apply (proj1 (scan_wf (v :: stack) rest)); exact Hnone).
    rewrite (IH (v :: stack) Htail). split.
    + intros [[-> [ancestors ->]]|[ancestors Hopen]].
      * exists ancestors. constructor.
      * exists ancestors. now apply opening_open.
    + intros [ancestors Hopen]. inversion Hopen; subst; eauto.
  - rewrite Wto.order_equation in Hnodup. rewrite (IH (tl stack) Hnodup). split.
    + intros [ancestors Hopen]. exists ancestors. now apply opening_close.
    + intros [ancestors Hopen]. inversion Hopen; subst; eauto.
Qed.

(** The loop projection satisfies every table field of the fixed exact-loop contract. *)
Theorem of_forest_exact {V E} (p : Prepared.t V E) scope roots f :
  Hier.exact p scope roots f -> Loops.exact p scope roots f (of_forest f).
Proof.
  intro Hexact.
  assert (Hunique : NoDup (Wto.order (Wto.of_forest f))).
  { rewrite (proj2 WeakOrderFacts.order_members).
    now destruct Hexact. }
  constructor.
  - exact Hexact.
  - intro h. rewrite of_forest_equation, scan_headers. split.
    + intro Htoken.
      destruct (token_opening [] (Wto.of_forest f) h Htoken) as [ancestors Hopen].
      exists ancestors. split; [exact Htoken|now apply opening_row].
    + intros [ancestors [Htoken _]]. exact Htoken.
  - rewrite of_forest_equation. now apply scan_headers_unique.
  - rewrite of_forest_equation. apply scan_wf.
  - intros h outer. rewrite of_forest_equation, scan_parent by exact Hunique.
    split.
    + intros [ancestors Hopen]. exists ancestors. split.
      * rewrite scan_headers. exact (opening_token _ _ _ _ Hopen).
      * exact (opening_row _ _ _ _ Hopen).
    + intros [ancestors [Hheader Hrow]].
      rewrite scan_headers in Hheader.
      destruct (token_opening [] (Wto.of_forest f) h Hheader) as [actual Hopen].
      pose proof (WeakOrderFacts.annotation_functional _ [] h _ _ Hunique
        (opening_row _ _ _ _ Hopen) Hrow) as Heq.
      inversion Heq; subst actual. now exists ancestors.
  - intros v h. rewrite of_forest_equation. now apply scan_innermost.
Qed.

(** Ready preparation gives every exact-loop field for the shared-hierarchy projection. *)
Theorem compute_exact {V E} (p : Prepared.t V E) roots :
  Prepared.ready p ->
  Loops.exact p (Scope.Make FinSet.empty None) roots
    (HierRun.compute p (Scope.Make FinSet.empty None) roots) (compute p roots).
Proof.
  intro Hready. rewrite compute_equation.
  apply of_forest_exact, HierExact.compute_exact, Hready.
Qed.

(** Loop membership reads the component subtree rather than a materialized per-loop set. *)
Definition in_loop := LoopStructure.in_loop.

(** The actual producer's component subtrees are nested or disjoint. *)
Theorem nested {V E} (p : Prepared.t V E) roots :
  Prepared.ready p ->
  let f := HierRun.compute p (Scope.Make FinSet.empty None) roots in
  forall h body k inside,
  LoopStructure.component f h body -> LoopStructure.component f k inside ->
  incl (h :: Hier.members body) (k :: Hier.members inside) \/
  incl (k :: Hier.members inside) (h :: Hier.members body) \/
  (forall v, In v (h :: Hier.members body) -> ~ In v (k :: Hier.members inside)).
Proof.
  intros Hready f. apply LoopStructure.nested_occurrences.
  pose proof (HierExact.compute_exact p (Scope.Make FinSet.empty None) roots Hready) as Hexact.
  now destruct Hexact.
Qed.

(** Every nonempty scoped cycle of an exact forest lies under one of its actual loop headers. *)
Theorem forest_covers {V E} (p : Prepared.t V E) scope roots f v es :
  Hier.exact p scope roots f ->
  Search.scoped_reachable p scope roots v -> Search.scoped_path p scope v es v ->
  es <> [] -> exists h, In h (Loops.headers (of_forest f)) /\ in_loop f h v.
Proof.
  intros Hexact Hreach Hcycle Hnonempty.
  destruct (LoopStructure.covers p scope roots f v es Hexact Hreach Hcycle Hnonempty)
    as [h [body [Hcomponent Hmember]]].
  exists h. split.
  - rewrite of_forest_equation, scan_headers. exact (LoopStructure.component_open _ _ _ Hcomponent).
  - exists body. auto.
Qed.

(** Every rooted node on a nonempty cycle belongs to a loop of the actual hierarchy projection. *)
Theorem covers {V E} (p : Prepared.t V E) roots v es :
  Prepared.ready p ->
  Search.scoped_reachable p (Scope.Make FinSet.empty None) roots v ->
  Search.scoped_path p (Scope.Make FinSet.empty None) v es v ->
  es <> [] ->
  exists h, In h (Loops.headers (compute p roots)) /\
    in_loop (HierRun.compute p (Scope.Make FinSet.empty None) roots) h v.
Proof.
  intros Hready Hreach Hcycle Hnonempty. rewrite compute_equation.
  apply (forest_covers p (Scope.Make FinSet.empty None) roots _ v es);
    [apply HierExact.compute_exact, Hready|exact Hreach|exact Hcycle|].
  exact Hnonempty.
Qed.

End LoopForest.
