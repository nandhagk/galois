(** * Balanced IFDS path-edge constraints

    Finite rules combine caller and callee path edges at matched returns.
    For example, an internal edge propagates one fact without changing stack level.
    Builds on: Framework.IfdsSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool NArith PArith.
From Argent Require Import Time Std Loop.
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
  Proof. Admitted. (* STUB *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
End IfdsLattice.

Module IfdsLatticeT <: IFDS_LATTICE_T.
  Include IfdsLattice.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (_ : t) := 1%nat.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End IfdsLatticeT.

Module Ifds (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY)
    (FL : FLOW_FUN P N E C F) (R : IFDS_RULES P N E C Site I F FL) (L : IFDS_LATTICE) <: IFDS P N E C Site I F FL L.
  Include IfdsCode P N E C Site I F FL R L.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := R.wf p.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. Admitted. (* STUB *)
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted. (* STUB *)
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted. (* STUB *)
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted. (* STUB *)
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof. Admitted. (* STUB *)
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted. (* STUB *)
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted. (* STUB *)
  Include IFDS_SPEC P N E C Site I F FL L.
  (** The system encodes all three path-edge components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof. Admitted. (* STUB *)
  (** The row inventory contains exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule, wf p ->
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof. Admitted. (* STUB *)
  (** Rule targets follow their destination edge or identity point. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof. Admitted. (* STUB *)
  (** Boolean rules combine the caller and callee at a matched return. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => true
     | PathStep d0 e x _ => look (d0, (C.src p e, x))
     | PathReturn d0 call ret x a b _ =>
         look (d0, (C.src p call, x)) && look (a, (C.src p ret, b))
     end, nil).
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
End IfdsT.

Module IfdsSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (A : IFDS P N E C Site I F FL L)
    <: IFDS_SOUND P N E C Site I F FL L A.
  Lemma covers : forall p look, A.wf p -> A.post_solution p look ->
    forall entry d0 n path d, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In d (path_facts (FL.flow p) d0 path) -> look (d0, (n, d)) = true.
  Proof. Admitted. (* CONVERT: ifds_post_balanced: The reference TabPaths.balanced_induction was not found *)
End IfdsSound.
