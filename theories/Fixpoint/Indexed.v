(** * Prepared row indexes

    Preparation numbers rows and indexes their declared writes.
    For example, repeated writes by one row occupy one index entry per key.
    Builds on: Fixpoint.IndexedSig and Base.Trie. *)

From Stdlib Require Import List PArith Arith NArith Bool.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig IndexedSig.

Module IndexedCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: INDEXED_OPS L S.
  Definition prog := indexed S.prog S.row.
  Definition key := S.key.
  Definition row := (positive * S.row)%type.
  Definition frame := S.frame.
  Definition key_code := S.key_code.
  Definition key_eqb := S.key_eqb.
  Definition rows (p : prog) := numbered_rows p.
  Definition target (p : prog) (r : row) := S.target (program p) (snd r).
  Definition start (p : prog) (r : row) := S.start (program p) (snd r).
  Definition resume (p : prog) := S.resume (program p).
  Definition deps (p : prog) (r : row) := S.deps (program p) (snd r).
  Definition sides (p : prog) (r : row) := S.sides (program p) (snd r).
  Definition row_code (r : row) := fst r.
  Definition rows_of (p : prog) (x : key) :=
    match trie_get (key_code x) (write_index p) with
    | Some rs => rs
    | None => nil
    end.
  Fixpoint number_from (id : positive) (rs : list S.row) : list row :=
    match rs with
    | nil => nil
    | r :: rest => (id, r) :: number_from (Pos.succ id) rest
    end.
  Definition index_row p (r : row) idx :=
    let keys := fold_left (fun seen x => PTrieCode.set (key_code x) tt seen)
      (S.target p (snd r) :: S.sides p (snd r)) Empty in
    fold_right (fun entry acc =>
      let code := fst entry in
      let previous := match trie_get code acc with Some rs => rs | None => nil end in
      PTrieCode.set code (r :: previous) acc) idx (PTrieCode.elements keys).
  Definition prepare p :=
    let rs := number_from 1%positive (S.rows p) in
    Indexed S.prog S.row p rs (fold_right (index_row p) Empty rs).
End IndexedCode.

Module Indexed (L : LATTICE) (S : SYSTEM L) <: INDEXED L S.
  Include IndexedCode L S.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := S.wf (program p) /\ p = prepare (program p).
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. Admitted.
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted.
  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted.
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof. Admitted.
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted.
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted.
  Lemma row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof. Admitted.
  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof. Admitted.
  Lemma prepare_program : forall p, program (prepare p) = p.
  Proof. Admitted.
  Lemma prepare_rows : forall p, List.map snd (rows (prepare p)) = S.rows p.
  Proof. Admitted.
  Lemma eval_prepare : forall p r look, In r (rows (prepare p)) ->
    eval (prepare p) r look = S.eval p (snd r) look.
  Proof. Admitted.
  Lemma wf_prepare : forall p, S.wf p -> wf (prepare p).
  Proof. Admitted.
  (** Prepared targets agree with the original rows. *)
  Lemma prepare_target : forall p r, In r (rows (prepare p)) ->
    target (prepare p) r = S.target p (snd r).
  Proof. Admitted.
  (** Prepared dependencies agree with the original rows. *)
  Lemma prepare_deps : forall p r, In r (rows (prepare p)) ->
    deps (prepare p) r = S.deps p (snd r).
  Proof. Admitted.
  (** Prepared side declarations agree with the original rows. *)
  Lemma prepare_sides : forall p r, In r (rows (prepare p)) ->
    sides (prepare p) r = S.sides p (snd r).
  Proof. Admitted.
  (** Preparation keeps precisely the original post-solutions. *)
  Lemma prepare_post : forall p look,
    post_solution (prepare p) look <-> S.post_solution p look.
  Proof. Admitted.
End Indexed.

Module IndexedT (L : LATTICE_T) (S : SYSTEM_T L) <: INDEXED_T L S.
  Include Indexed L S.
  Definition row_work (p : prog) (B : nat) : N := S.row_work (program p) B.
  Definition kw (p : prog) : nat := S.kw (program p).
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  TimeFun row_code.
  TimeFun rows_of.
  TimeFun number_from.
  TimeFun index_row.
  TimeFun prepare.

  Definition c_sys : N := 1. (* STUB *)
  Definition c_loc : N := 1. (* STUB *)

  Lemma row_work_mono : forall p s s', s <= s' ->
    (row_work p s <= row_work p s')%N.
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
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
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
  Lemma T_resume_le : forall p f a, wf p ->
    (T_resume p f a <= c_sys * (row_work p (L.size a) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_row_code_le : forall r,
    (T_row_code r <= c_loc * N.of_nat (Pos.size_nat (row_code r) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_rows_of_le : forall p x, wf p ->
    (T_rows_of p x <= c_loc * N.of_nat (length (rows_of p x) + key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition c_idx : N := 1. (* STUB *)

  (** Preparation keeps the original key-width budget. *)
  Lemma prepare_kw : forall p, kw (prepare p) = S.kw p.
  Proof. Admitted. (* STUB *)
  (** Preparation keeps the original row-work budget. *)
  Lemma prepare_row_work : forall p s, row_work (prepare p) s = S.row_work p s.
  Proof. Admitted. (* STUB *)

  Lemma T_prepare_le : forall p, S.wf p ->
    (T_prepare p <= c_idx * (
      N.of_nat ((length (S.rows p) +
        fold_right Nat.add 0
          (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
            (S.rows p)) + 1)%nat) *
      N.of_nat (S.kw p + Nat.log2 (length (S.rows p)) + 1) +
      N.of_nat (length (S.rows p)) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)
End IndexedT.
