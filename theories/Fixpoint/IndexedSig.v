(** * Indexed system preparation

    Prepared systems number rows and index all keys that rows may write.
    For example, a row with one side contribution appears in two write-index lists.
    Builds on: Fixpoint.SystemSig and Base.Trie. *)

From Stdlib Require Import List PArith Arith NArith.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.

Record indexed (P R : Type) := Indexed {
  program : P;
  numbered_rows : list (positive * R);
  write_index : PTrieCode.t (list (positive * R))
}.

Arguments program {P R} _.
Arguments numbered_rows {P R} _.
Arguments write_index {P R} _.

Module Type INDEXED_OPS (L : LATTICE_OPS) (S : SYSTEM_OPS L).
  Include LOCAL_SYSTEM_OPS L
    with Definition prog := indexed S.prog S.row
    with Definition key := S.key
    with Definition row := (positive * S.row)%type
    with Definition frame := S.frame.
  Parameter prepare : S.prog -> prog.
End INDEXED_OPS.

Module Type INDEXED_SYSTEM (L : LATTICE) (S : SYSTEM L) :=
  INDEXED_OPS L S <+ SYSTEM_SPEC L <+ SYSTEM_LAWS L <+ LOCAL_LAWS L.

Module Type INDEXED_LAWS (L : LATTICE) (S : SYSTEM L)
    (Import I : INDEXED_SYSTEM L S).
  (** Preparation keeps the underlying program. *)
  Parameter prepare_program : forall p, program (prepare p) = p.
  (** Numbering retains the original row order and multiplicity. *)
  Parameter prepare_rows : forall p, List.map snd (rows (prepare p)) = S.rows p.
  (** Prepared row evaluation agrees with the underlying system. *)
  Parameter eval_prepare : forall p r look, In r (rows (prepare p)) ->
    eval (prepare p) r look = S.eval p (snd r) look.
  (** Prepared well-formedness follows from the original system. *)
  Parameter wf_prepare : forall p, S.wf p -> wf (prepare p).
End INDEXED_LAWS.

Module Type INDEXED (L : LATTICE) (S : SYSTEM L) :=
  INDEXED_SYSTEM L S <+ INDEXED_LAWS L S.

Module Type INDEXED_TIME (L : LATTICE_T) (S : SYSTEM_T L) (Import I : INDEXED L S).
  Include SYSTEM_TIME L I.
  Include LOCAL_TIME L I.
  Parameter T_prepare : S.prog -> N.
  Parameter c_idx : N.
  (** Preparation pays for rows, dependency occurrences and encoded keys. *)
  Parameter T_prepare_le : forall p, S.wf p ->
    (T_prepare p <= c_idx *
      N.of_nat ((length (S.rows p) +
        fold_right Nat.add 0
          (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
            (S.rows p)) + 1)%nat) *
      N.of_nat (S.kw p + Nat.log2 (length (S.rows p)) + 1))%N.
End INDEXED_TIME.

Module Type INDEXED_T (L : LATTICE_T) (S : SYSTEM_T L) :=
  INDEXED L S <+ INDEXED_TIME L S.
