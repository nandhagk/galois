(** * Systems of query rows

    Systems describe rows and the keys each row may read or write.
    For example, a row can read a predecessor and contribute to its target and an alarm key.
    Builds on: Fixpoint.Query and Lattice.LatticeSig. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query.

Module Type SYSTEM_OPS (L : LATTICE_OPS).
  Parameter prog key row frame : Type.
  Parameter key_code : key -> positive.
  Parameter key_eqb : key -> key -> bool.
  Parameter rows : prog -> list row.
  Parameter target : prog -> row -> key.
  Parameter start : prog -> row -> query key L.t frame.
  Parameter resume : prog -> frame -> L.t -> query key L.t frame.
  Parameter deps : prog -> row -> list key.
  Parameter sides : prog -> row -> list key.
End SYSTEM_OPS.

Module Type SYSTEM_SPEC (L : LATTICE_OPS) (Import S : SYSTEM_OPS L).
  Definition val := L.t.
  Definition eval (p : prog) (r : row) (look : key -> L.t)
      : option (L.t * list (key * L.t)) :=
    eval_query (resume p) look (Datatypes.S (length (deps p r))) (start p r).
  (** Listed rows must accept their primary and side contributions. *)
  Definition post_on (p : prog) (rs : list row) (look : key -> L.t) : Prop :=
    forall r, In r rs -> row_ok L.leb look (target p r) (eval p r look) = true.
  (** A post-solution passes every row of the program. *)
  Definition post_solution (p : prog) (look : key -> L.t) : Prop :=
    post_on p (rows p) look.
  Definition writes (p : prog) (r : row) : list key := target p r :: sides p r.
  Definition below (s u : key -> L.t) : Prop := forall x, L.leb (s x) (u x) = true.
  (** Increasing the lookup increases each result and its side contributions. *)
  Definition monotone (p : prog) : Prop :=
    forall r s u, In r (rows p) -> below s u ->
      out_leb L.leb (eval p r s) (eval p r u).
  Definition key_bits (x : key) : nat := Pos.size_nat (key_code x).
End SYSTEM_SPEC.

Module Type SYSTEM_LAWS (L : LATTICE) (Import S : SYSTEM_OPS L)
    (Import SS : SYSTEM_SPEC L S).
  (* spec: wf *)
  Parameter wf : prog -> Prop.
  (** Codes distinguish all system keys. *)
  Parameter key_code_inj : forall a b, key_code a = key_code b -> a = b.
  (** Key equality decides equality of system keys. *)
  Parameter key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  (** Declared rows finish within their dependency-derived fuel. *)
  Parameter eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  (** A row observes its declared dependencies. *)
  Parameter reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  (** A row asks only its declared dependencies. *)
  Parameter asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  (** Side contributions use declared side keys. *)
  Parameter sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  (** Side contributions fit the declared occurrence budget. *)
  Parameter sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
End SYSTEM_LAWS.

Module Type SYSTEM (L : LATTICE) :=
  SYSTEM_OPS L <+ SYSTEM_SPEC L <+ SYSTEM_LAWS L.

Module Type SYSTEM_TIME (L : LATTICE_T) (Import S : SYSTEM L).
  Parameter T_key_code : key -> N.
  Parameter T_key_eqb : key -> key -> N.
  Parameter T_rows : prog -> N.
  Parameter T_target : prog -> row -> N.
  Parameter T_start : prog -> row -> N.
  Parameter T_resume : prog -> frame -> L.t -> N.
  Parameter T_deps : prog -> row -> N.
  Parameter T_sides : prog -> row -> N.
  (* spec: row_work kw *)
  Parameter row_work : prog -> nat -> N.
  Parameter kw : prog -> nat.
  Parameter c_sys : N.
  (** Step budgets grow with the size of abstract values. *)
  Parameter row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  (** The program key budget covers all declared reads and writes. *)
  Parameter key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  (** Encoding costs are linear in the resulting code size. *)
  Parameter T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  (** Equality costs are bounded by the first key's code size. *)
  Parameter T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  (** Enumerating rows costs linear time in the output length. *)
  Parameter T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  (** Target lookup fits the row budget. *)
  Parameter T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  (** Starting a row fits the row budget. *)
  Parameter T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  (** Resuming a frame that a listed row reaches pays for the sizes of the lookup values. *)
  Parameter T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  (** Dependency enumeration pays for every key occurrence. *)
  Parameter T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  (** Side enumeration pays for every key occurrence. *)
  Parameter T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  (** Row output sizes fit the transfer budget. *)
  Parameter eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
End SYSTEM_TIME.

Module Type SYSTEM_T (L : LATTICE_T) := SYSTEM L <+ SYSTEM_TIME L.

Module Type BUDGET (L : WLATTICE_T) (S : SYSTEM_T L).
  (* spec: inv vsize wunits wmax *)
  Parameter inv : S.prog -> L.t -> Prop.
  Parameter vsize : S.prog -> nat.
  Parameter wunits : S.prog -> nat.
  Parameter wmax : S.prog -> L.wparam -> nat.
  (** Bottom satisfies the client's invariant. *)
  Parameter inv_bot : forall p, inv p L.bot.
  (** Join keeps the invariant. *)
  Parameter inv_join : forall p a b, inv p a -> inv p b -> inv p (L.join a b).
  (** Narrowing keeps the invariant. *)
  Parameter inv_narrow : forall p a b, inv p a -> inv p b -> inv p (L.narrow a b).
  (** Widening keeps the invariant. *)
  Parameter inv_widen : forall p w a b,
    inv p a -> inv p b -> inv p (L.widen w a b).
  (** Every row contribution satisfies the invariant on invariant lookups. *)
  Parameter inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) ->
    (forall x, inv p (look x)) -> S.eval p r look = Some (a, ss) ->
    inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  (** The invariant bounds representation size. *)
  Parameter size_le : forall p a, inv p a -> L.size a <= vsize p.
  (** The invariant bounds the number of widened components. *)
  Parameter wunits_le : forall p a, inv p a -> L.wunits a <= wunits p.
  (** The invariant bounds widening rank for every parameter. *)
  Parameter wrank_le : forall p w a, inv p a -> L.wrank w a <= wmax p w.
End BUDGET.

Module Type LOCAL_OPS (L : LATTICE_OPS) (Import S : SYSTEM_OPS L).
  Parameter row_code : row -> positive.
  Parameter rows_of : prog -> key -> list row.
End LOCAL_OPS.

Module Type LOCAL_SYSTEM_OPS (L : LATTICE_OPS) := SYSTEM_OPS L <+ LOCAL_OPS L.

Module Type LOCAL_LAWS (L : LATTICE) (Import S : SYSTEM L)
    (Import X : LOCAL_OPS L S).
  (** Row codes distinguish rows within each program. *)
  Parameter row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  (** The index lists exactly the rows that may write the requested key. *)
  Parameter rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
End LOCAL_LAWS.

Module Type LOCAL_SYSTEM (L : LATTICE) :=
  SYSTEM L <+ LOCAL_OPS L <+ LOCAL_LAWS L.

Module Type LOCAL_TIME (L : LATTICE_T) (Import S : LOCAL_SYSTEM L).
  Parameter T_row_code : row -> N.
  Parameter T_rows_of : prog -> key -> N.
  Parameter c_loc : N.
  (** Row encoding costs are linear in the resulting code size. *)
  Parameter T_row_code_le : forall r,
    (T_row_code r <= c_loc * N.of_nat (Pos.size_nat (row_code r) + 1))%N.
  (** Indexed lookup pays for its key and every returned row. *)
  Parameter T_rows_of_le : forall p x, wf p ->
    (T_rows_of p x <= c_loc * N.of_nat (length (rows_of p x) + key_bits x + 1))%N.
End LOCAL_TIME.

Module Type LOCAL_SYSTEM_T (L : LATTICE_T) :=
  LOCAL_SYSTEM L <+ SYSTEM_TIME L <+ LOCAL_TIME L.
