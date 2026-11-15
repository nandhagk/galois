(** * Balanced IFDS path-edge constraints

    Finite rules combine caller and callee path edges at matched returns.
    For example, an internal edge propagates one fact without changing stack level.
    Builds on: Framework.IfdsSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool NArith PArith Arith Lia.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import KeySig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig.

(** Enumerate finite rules with binary occurrence identifiers. *)
Fixpoint path_number {N E F} (next : positive) (rules : list (path_rule N E F))
    : list (path_row N E F) :=
  match rules with
  | nil => nil
  | r :: rest => PathRow next r :: path_number (Pos.succ next) rest
  end.
TimeFun path_number.

(** Numbering preserves the rule inventory and its occurrence order. *)
Lemma path_number_rules {N E F} : forall next (rules : list (path_rule N E F)),
  map path_row_rule (path_number next rules) = rules.
Proof.
  intros next rules; revert next.
  induction rules as [|rule rules IH]; intro next; cbn [path_number map].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Propagating an empty collection of facts keeps it empty. *)
Lemma path_fold_nil {E F} (flow : E -> F -> list F) : forall path,
  fold_left (fun facts e => flat_map (flow e) facts) path nil = nil.
Proof.
  induction path as [|e path IH]; cbn [fold_left flat_map]; assumption || reflexivity.
Qed.

(** Independent input collections propagate independently along the same path. *)
Lemma path_fold_app {E F} (flow : E -> F -> list F) : forall path left right,
  fold_left (fun facts e => flat_map (flow e) facts) path (left ++ right) =
    fold_left (fun facts e => flat_map (flow e) facts) path left ++
    fold_left (fun facts e => flat_map (flow e) facts) path right.
Proof.
  induction path as [|e path IH]; intros left right; cbn [fold_left].
  - reflexivity.
  - rewrite flat_map_app; apply IH.
Qed.

(** Propagation from a list is the concatenation of its singleton propagations. *)
Lemma path_fold_facts {E F} (flow : E -> F -> list F) : forall path facts,
  fold_left (fun facts e => flat_map (flow e) facts) path facts =
    flat_map (fun d => path_facts flow d path) facts.
Proof.
  intros path facts; induction facts as [|d facts IH].
  - apply path_fold_nil.
  - change (fold_left (fun facts e => flat_map (flow e) facts)
      path ((d :: nil) ++ facts) =
      path_facts flow d path ++ flat_map (fun x => path_facts flow x path) facts).
    rewrite path_fold_app, IH; reflexivity.
Qed.

(** Concatenating paths composes their fact relations in occurrence order. *)
Lemma path_facts_app {E F} (flow : E -> F -> list F) : forall d left right,
  path_facts flow d (left ++ right) =
    flat_map (fun x => path_facts flow x right) (path_facts flow d left).
Proof.
  intros d left right; unfold path_facts at 1.
  rewrite fold_left_app, path_fold_facts; reflexivity.
Qed.

(** A one-edge path has exactly the edge's flow results. *)
Lemma path_facts_single {E F} (flow : E -> F -> list F) : forall d e,
  path_facts flow d (e :: nil) = flow e d.
Proof.
  intros d e; unfold path_facts; cbn [fold_left flat_map]; apply app_nil_r.
Qed.

(** The first edge chooses the input fact of the remaining path. *)
Lemma path_facts_cons {E F} (flow : E -> F -> list F) : forall d e path,
  path_facts flow d (e :: path) =
    flat_map (fun x => path_facts flow x path) (flow e d).
Proof.
  intros d e path.
  change (path_facts flow d ((e :: nil) ++ path) =
    flat_map (fun x => path_facts flow x path) (flow e d)).
  rewrite path_facts_app, path_facts_single; reflexivity.
Qed.

(** Rule enumeration retains seed, internal and matched-call occurrences. *)
Definition path_rules {N E F Site} (site_eqb : Site -> Site -> bool)
    (kind : E -> edge_kind Site) (dst : E -> N) (facts : list F)
    (flow : E -> F -> list F) (seeds : list (N * F)) (edges : list E)
    : list (path_rule N E F) :=
  map (fun nd => PathIdentity (fst nd) (snd nd)) seeds ++
  flat_map (fun e => match kind e with
    | Call _ => flat_map (fun x => map (fun d => PathIdentity (dst e) d) (flow e x)) facts
    | _ => nil
    end) edges ++
  flat_map (fun d0 => flat_map (fun e => match kind e with
    | Intra | CallToReturn _ => flat_map
        (fun x => map (fun y => PathStep d0 e x y) (flow e x)) facts
    | _ => nil
    end) edges) facts ++
  flat_map (fun d0 => flat_map (fun call => match kind call with
    | Call site => flat_map (fun ret => match kind ret with
      | Return site' => if site_eqb site site' then
          flat_map (fun x => flat_map (fun a => flat_map (fun b =>
            map (fun y => PathReturn d0 call ret x a b y) (flow ret b)) facts)
            (flow call x)) facts
        else nil
      | _ => nil
      end) edges
    | _ => nil
    end) edges) facts.
TimeFun path_rules.

(** Pending dependencies are read in order and passed to the rule evaluator. *)
Definition path_query {N E F A} (finish : path_rule N E F -> list A -> A)
    (rule : path_rule N E F) (pending : list (path_edge N F)) (received : list A)
    : query (path_edge N F) A (path_frame N E F A) :=
  match pending with
  | nil => Ret (finish rule (rev_append received nil))
  | x :: xs => Ask x (PathFrame N E F A rule xs received)
  end.
TimeFun path_query.

Definition bool_query {N F} (pending : list (path_edge N F)) (acc : bool)
    : query (path_edge N F) bool (bool_frame N F) :=
  match pending with
  | nil => Ret acc
  | x :: xs => Ask x (BoolFrame N F xs acc)
  end.
TimeFun bool_query.

Module IfdsCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (FL : FLOW_FUN_OPS P N E F) (R : IFDS_RULES_OPS P N E F) (L : IFDS_LATTICE_OPS) <: IFDS_OPS P N E F L.
  Definition prog := P.t.
  Definition key := path_edge N.t F.t.
  Definition row := path_row N.t E.t F.t.
  Definition frame := bool_frame N.t F.t.
  Definition key_code := path_edge_code N.encode F.encode.
  Definition key_eqb (x y : key) :=
    F.eqb (fst x) (fst y) && N.eqb (fst (snd x)) (fst (snd y)) &&
      F.eqb (snd (snd x)) (snd (snd y)).
  Definition rows p : list row := path_number 1%positive
    (R.rules p).
  Definition target p (r : row) : key := match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Definition deps p (r : row) : list key := match path_row_rule r with
    | PathIdentity _ _ => nil
    | PathStep d0 e x _ => (d0, (C.src p e, x)) :: nil
    | PathReturn d0 call ret x a b _ =>
        (d0, (C.src p call, x)) :: (a, (C.src p ret, b)) :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
  Definition start p (r : row) : query key bool frame := bool_query (deps p r) true.
  Definition resume (_ : prog) (f : frame) (a : bool) : query key bool frame :=
    bool_query (bool_frame_pending _ _ f) (bool_frame_acc _ _ f && a).
End IfdsCode.

Module IfdsLatticeCode <: IFDS_LATTICE_OPS.
  Definition t := bool.
  Definition leb (a b : bool) := negb a || b.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
End IfdsLatticeCode.

Module IfdsLattice <: IFDS_LATTICE.
  Include IfdsLatticeCode.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros []; reflexivity.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [] [] []; cbn [leb negb orb]; congruence.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros []; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [] []; cbn [is_bot leb negb orb]; congruence.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
End IfdsLattice.

Module IfdsLatticeT <: IFDS_LATTICE_T.
  Include IfdsLattice.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (_ : t) := 1%nat.
  Definition c_lat : N := 1%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    reflexivity.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [] []; unfold c_lat, size; time_step.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [] []; unfold c_lat, size; time_step.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros []; unfold c_lat, size; time_step.
  Qed.
End IfdsLatticeT.

Module Ifds (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY)
    (FL : FLOW_FUN P N E C F) (R : IFDS_RULES P N E C Site I F FL) (L : IFDS_LATTICE) <: IFDS P N E C Site I F FL L.
  Include IfdsCode P N E C Site I F FL R L.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := R.wf p.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    intros [d [n x]] [d' [n' x']] Hcode.
    unfold key_code, path_edge_code, pair_code in Hcode; cbn [fst snd] in Hcode.
    destruct (glue_inj _ _ _ _ Hcode) as [Hd Hrest].
    destruct (glue_inj _ _ _ _ Hrest) as [Hn Hx].
    apply F.encode_inj in Hd; apply N.encode_inj in Hn; apply F.encode_inj in Hx.
    now subst.
  Qed.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    intros [d [n x]] [d' [n' x']].
    unfold key_eqb; cbn [fst snd].
    destruct (F.eqb_spec d d'), (N.eqb_spec n n'), (F.eqb_spec x x');
      cbn [andb]; constructor; congruence.
  Qed.
  (** Boolean rules combine the caller and callee at a matched return. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => true
     | PathStep d0 e x _ => look (d0, (C.src p e, x))
     | PathReturn d0 call ret x a b _ =>
         look (d0, (C.src p call, x)) && look (a, (C.src p ret, b))
     end, nil).
  Proof.
    intros p [code rule] look; destruct rule; reflexivity.
  Qed.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p r look _ _; rewrite eval_spec; discriminate.
  Qed.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [code rule] s u _ _ Hagree.
    rewrite !eval_spec; destruct rule; cbn [path_row_rule] in *.
    - reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)); reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)),
        (Hagree _ (or_intror (or_introl eq_refl))); reflexivity.
  Qed.

  (** A continuing Boolean query only asks keys still present in its input list. *)
  Lemma bool_query_asks : forall p look n pending value q acc x f,
    loop_fuel (eval_step (resume p) look) n (bool_query pending value, nil) =
      inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x pending.
  Proof.
    intros p look n; induction n as [|n IH];
      intros pending value q acc x f Hloop Hask.
    - cbn [loop_fuel] in Hloop; injection Hloop as <- <-.
      destruct pending as [|y pending]; cbn [bool_query peel fst] in Hask.
      + discriminate.
      + injection Hask as <- <-; now left.
    - destruct pending as [|y pending];
        cbn [loop_fuel bool_query eval_step peel resume fst snd
          bool_frame_pending bool_frame_acc] in Hloop.
      + discriminate.
      + right; eapply IH; eassumption.
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p r look n q acc x f _ _ Hloop Hask.
    eapply bool_query_asks; eassumption.
  Qed.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p r look a ss x b _ _ Heval Hin.
    rewrite eval_spec in Heval; injection Heval as <- <-; contradiction.
  Qed.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p r look a ss _ _ Heval.
    rewrite eval_spec in Heval; injection Heval as <- <-; reflexivity.
  Qed.
  Include IFDS_SPEC P N E C Site I F FL L.
  (** The system encodes all three path-edge components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof.
    reflexivity.
  Qed.
  (** The row inventory contains exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule, wf p ->
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof.
    intros p rule Hwf; unfold rows, enabled.
    rewrite <- (R.rules_enabled p rule Hwf).
    split.
    - intros [r [Hin Hrule]]; rewrite <- Hrule.
      rewrite <- (path_number_rules 1%positive (R.rules p)).
      apply in_map; exact Hin.
    - intro Hin.
      assert (Hmap : In rule (map path_row_rule (path_number 1%positive (R.rules p)))).
      { now rewrite path_number_rules. }
      apply in_map_iff in Hmap; destruct Hmap as [r [Hrule Hr]].
      exists r; now split.
  Qed.
  (** Rule targets follow their destination edge or identity point. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof.
    reflexivity.
  Qed.
End Ifds.

Module IfdsT (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T)
    (FL : FLOW_FUN_T P N E C F) (R : IFDS_RULES_T P N E C Site I F FL)
    (L : IFDS_LATTICE_T) <: IFDS_T P N E C Site I F FL L.
  Include Ifds P N E C Site I F FL R L.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun deps.
  TimeFun sides.
  TimeFun start.
  TimeFun resume.
  Definition row_work p s := N.of_nat (length (rows p) + s + L.size true + 1).
  Definition path_kw (p : prog) : nat := fold_right Nat.max 0
    (flat_map (fun r => map key_bits (writes p r ++ deps p r)) (rows p)).
  Definition kw := path_kw.
  Definition c_sys : N := 1%N. (* STUB *)
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof.
    intros p s t Hst; unfold row_work; lia.
  Qed.

  (** A maximum bounds every width that occurs in its inventory. *)
  Lemma path_width_member : forall widths width, In width widths ->
    width <= fold_right Nat.max 0 widths.
  Proof.
    induction widths as [|head widths IH]; intros width Hin.
    - contradiction.
    - destruct Hin as [<-|Hin]; cbn [fold_right].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH width Hin)|apply Nat.le_max_r].
  Qed.
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p r x _ Hr Hx; unfold kw, path_kw.
    apply path_width_member, in_flat_map.
    exists r; split; [exact Hr|now apply in_map].
  Qed.
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p [code rule] look s a ss _ _ Hlook Heval.
    rewrite eval_spec in Heval; destruct rule as [n d|d0 e x y|d0 call ret x b c y];
      cbn [path_row_rule] in Heval.
    - injection Heval as <- <-; split; [unfold row_work; lia|constructor].
    - injection Heval as <- <-; split; [|constructor].
      pose proof (Hlook (d0, (C.src p e, x))); unfold row_work; lia.
    - destruct (look (d0, (C.src p call, x))) eqn:Hcaller;
        cbn [andb] in Heval; injection Heval as <- <-; split; try constructor.
      + pose proof (Hlook (b, (C.src p ret, c))); unfold row_work; lia.
      + pose proof (Hlook (d0, (C.src p call, x))) as Hsize.
        rewrite Hcaller in Hsize; unfold row_work; lia.
  Qed.
End IfdsT.

Module IfdsSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (A : IFDS P N E C Site I F FL L)
    <: IFDS_SOUND P N E C Site I F FL L A.
  (** A post-solution satisfies the implication described by each enabled rule. *)
  Lemma enabled_holds : forall p look, A.wf p -> A.post_solution p look ->
    forall rule, A.enabled p rule ->
      match rule with
      | PathIdentity n d => look (d, (n, d)) = true
      | PathStep d0 e x y =>
          look (d0, (C.src p e, x)) = true -> look (d0, (C.dst p e, y)) = true
      | PathReturn d0 call ret x a b y =>
          look (d0, (C.src p call, x)) = true ->
          look (a, (C.src p ret, b)) = true -> look (d0, (C.dst p ret, y)) = true
      end.
  Proof.
    intros p look Hwf Hpost rule Henabled.
    destruct (proj2 (A.rows_spec p rule Hwf) Henabled) as [r [Hin Hrule]].
    pose proof (Hpost r Hin) as Hrow.
    rewrite A.eval_spec, A.target_spec, Hrule in Hrow.
    destruct rule as [n d|d0 e x y|d0 call ret x a b y]; cbn [row_ok] in Hrow.
    - change (look (d, (n, d)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
    - intro Hinput; rewrite Hinput in Hrow.
      change (look (d0, (C.dst p e, y)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
    - intros Hcaller Hcallee; rewrite Hcaller, Hcallee in Hrow.
      change (look (d0, (C.dst p ret, y)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
  Qed.

  (** Entering a listed call supplies an identity edge for each supported callee input. *)
  Lemma call_identity : forall p look, A.wf p -> A.post_solution p look ->
    forall call site x a, In call (C.edges p) -> I.kind p call = Call site ->
      In x (FL.facts p) -> In a (FL.flow p call x) ->
      look (a, (C.dst p call, a)) = true.
  Proof.
    intros p look Hwf Hpost call site x a Hcall Hkind Hx Ha.
    apply (enabled_holds p look Hwf Hpost (PathIdentity (C.dst p call) a)).
    right; exists call, site, x; repeat split; assumption || reflexivity.
  Qed.

  (** A matched return combines the suspended caller edge with the callee result. *)
  Lemma return_holds : forall p look, A.wf p -> A.post_solution p look ->
    forall d0 call ret site x a b y,
      In d0 (FL.facts p) -> In call (C.edges p) -> In ret (C.edges p) ->
      I.kind p call = Call site -> I.kind p ret = Return site ->
      In x (FL.facts p) -> In a (FL.flow p call x) -> In b (FL.facts p) ->
      In y (FL.flow p ret b) -> look (d0, (C.src p call, x)) = true ->
      look (a, (C.src p ret, b)) = true -> look (d0, (C.dst p ret, y)) = true.
  Proof.
    intros p look Hwf Hpost d0 call ret site x a b y Hd0 Hcall Hret
      Hcall_kind Hret_kind Hx Ha Hb Hy Hcaller Hcallee.
    apply (enabled_holds p look Hwf Hpost (PathReturn d0 call ret x a b y)).
    - split; [exact Hd0|]. split; [exact Hcall|]. split; [exact Hret|].
      split; [exists site; now split|].
      split; [exact Hx|]. split; [exact Ha|]. now split.
    - exact Hcaller.
    - exact Hcallee.
  Qed.

  (** Balanced paths preserve both finite fact support and their origin's path edge. *)
  Lemma path_propagates : forall p look, A.wf p -> A.post_solution p look ->
    forall n path m,
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) n path m ->
      forall d0 x y, In d0 (FL.facts p) -> In x (FL.facts p) ->
        look (d0, (n, x)) = true -> In y (path_facts (FL.flow p) x path) ->
        In y (FL.facts p) /\ look (d0, (m, y)) = true.
  Proof.
    intros p look Hwf Hpost n path m Hpath.
    induction Hpath as [n|e He Hkind|n m t left right Hleft IHleft Hright IHright|
      call ret site inside Hcall Hret Hcall_kind Hret_kind Hinside IHinside];
      intros d0 x y Hd0 Hx Hlook Hy.
    - cbn [path_facts fold_left] in Hy; destruct Hy as [<-|[]]; now split.
    - rewrite path_facts_single in Hy; split.
      + eapply FL.flow_closed; eassumption.
      + apply (enabled_holds p look Hwf Hpost (PathStep d0 e x y)).
        * split; [exact Hd0|]. split; [exact He|].
          split; [exact Hkind|]. now split.
        * exact Hlook.
    - rewrite path_facts_app in Hy; apply in_flat_map in Hy.
      destruct Hy as [z [Hz Hy]].
      destruct (IHleft d0 x z Hd0 Hx Hlook Hz) as [Hz_supported Hz_look].
      exact (IHright d0 z y Hd0 Hz_supported Hz_look Hy).
    - rewrite path_facts_cons in Hy; apply in_flat_map in Hy.
      destruct Hy as [a [Ha Hy]].
      rewrite path_facts_app in Hy; apply in_flat_map in Hy.
      destruct Hy as [b [Hb Hy]]; rewrite path_facts_single in Hy.
      pose proof (FL.flow_closed p call x a Hcall Hx Ha) as Ha_supported.
      pose proof (call_identity p look Hwf Hpost call site x a Hcall
        Hcall_kind Hx Ha) as Ha_look.
      destruct (IHinside a a b Ha_supported Ha_supported Ha_look Hb)
        as [Hb_supported Hb_look].
      split.
      + eapply FL.flow_closed; eassumption.
      + exact (return_holds p look Hwf Hpost d0 call ret site x a b y Hd0 Hcall Hret
          Hcall_kind Hret_kind Hx Ha Hb_supported Hy Hlook Hb_look).
  Qed.

  (** Every seeded balanced path is included in every Boolean post-solution. *)
  Lemma covers : forall p look, A.wf p -> A.post_solution p look ->
    forall entry d0 n path d, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In d (path_facts (FL.flow p) d0 path) -> look (d0, (n, d)) = true.
  Proof.
    intros p look Hwf Hpost entry d0 n path d Hseed Hpath Hd.
    pose proof (FL.seeds_facts p entry d0 Hseed) as Hd0.
    assert (Hidentity : look (d0, (entry, d0)) = true).
    { apply (enabled_holds p look Hwf Hpost (PathIdentity entry d0)).
      now left. }
    exact (proj2 (path_propagates p look Hwf Hpost entry path n Hpath
      d0 d0 d Hd0 Hd0 Hidentity Hd)).
  Qed.
End IfdsSound.
