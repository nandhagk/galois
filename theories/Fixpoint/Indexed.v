(** * Prepared row indexes

    Preparation numbers rows and indexes their declared writes.
    For example, repeated writes by one row occupy one index entry per key.
    Builds on: Fixpoint.IndexedSig and Base.Trie. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig IndexedSig.

Module IndexedCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: INDEXED_OPS L S.
  Definition prog := indexed S.prog S.row.
  Definition key := S.key.
  Definition row := (positive * S.row)%type.
  Definition frame := S.frame.
  Definition key_code := S.key_code.
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
  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted.
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted.
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted.
  Lemma row_code_inj : forall p a b, In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof. Admitted. (* SIG-QUESTION: arbitrary indexed records can repeat a row code. *)
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
End Indexed.
