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

Module IfdsCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (FL : FLOW_FUN_OPS P N E F) (L : IFDS_LATTICE_OPS) <: IFDS_OPS P N E F L.
  Definition prog := P.t.
  Definition key := path_edge N.t F.t.
  Definition row := path_row N.t E.t F.t.
  Definition frame := path_frame N.t E.t F.t bool.
  Definition key_code := path_edge_code N.encode F.encode.
  Definition key_eqb (x y : key) :=
    F.eqb (fst x) (fst y) && N.eqb (fst (snd x)) (fst (snd y)) &&
      F.eqb (snd (snd x)) (snd (snd y)).
  Definition rows p : list row := path_number 1%positive
    (path_rules Site.eqb (I.kind p) (C.dst p) (FL.facts p) (FL.flow p)
      (FL.seeds p) (C.edges p)).
  Definition row_code (r : row) := path_row_code r.
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
  Definition finish (r : path_rule N.t E.t F.t) (xs : list bool) : bool :=
    match r, xs with
    | PathIdentity _ _, _ => true
    | PathStep _ _ _ _, a :: _ => a
    | PathReturn _ _ _ _ _ _ _, a :: b :: _ => a && b
    | _, _ => false
    end.
  Definition start p (r : row) : query key bool frame :=
    path_query finish (path_row_rule r) (deps p r) nil.
  Definition resume (_ : prog) (f : frame) (a : bool) : query key bool frame :=
    match f with
    | PathFrame _ _ _ _ rule pending received => path_query finish rule pending (a :: received)
    end.
  Definition rows_of p (x : key) : list row :=
    filter (fun r => key_eqb x (target p r)) (rows p).
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
  Proof. Admitted.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
End IfdsLattice.

Module Ifds (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY)
    (FL : FLOW_FUN P N E C F) (L : IFDS_LATTICE) <: IFDS P N E C Site I F FL L.
  Include IfdsCode P N E C Site I F FL L.
  Include SYSTEM_SPEC L.
  Definition wf (_ : prog) := True.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. Admitted.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof. Admitted.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted.
  (** Row codes distinguish rows within each program. *)
  Lemma row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof. Admitted.
  (** The index lists exactly the rows that may write the requested key. *)
  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof. Admitted.
  Include IFDS_SPEC P N E C Site I F FL L.
  (** The system encodes all three path-edge components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof. Admitted.
  (** The row identifier is its assigned binary occurrence identity. *)
  Lemma row_code_spec : row_code = path_row_code.
  Proof. Admitted.
  (** The row inventory contains exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule,
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof. Admitted.
  (** Rule targets follow their destination edge or identity point. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof. Admitted.
  (** Boolean rules combine the caller and callee at a matched return. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => true
     | PathStep d0 e x _ => look (d0, (C.src p e, x))
     | PathReturn d0 call ret x a b _ =>
         look (d0, (C.src p call, x)) && look (a, (C.src p ret, b))
     end, nil).
  Proof. Admitted.
End Ifds.

Module IfdsSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (A : IFDS P N E C Site I F FL L)
    <: IFDS_SOUND P N E C Site I F FL L A.
  Lemma covers : forall p look, A.post_solution p look ->
    forall entry d0 n path d, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In d (path_facts (FL.flow p) d0 path) -> look (d0, (n, d)) = true.
  Proof. Admitted. (* CONVERT: ifds_post_balanced: The reference TabPaths.balanced_induction was not found *)
End IfdsSound.
