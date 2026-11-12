(** * Full solution checking

    The checker evaluates each row and checks every value written by the row. *)

From Stdlib Require Import List.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.

Module CheckCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: CHECK_OPS L S.
  Definition look (m : kmap S.key L.t) (x : S.key) : L.t :=
    look_or S.key_code L.bot m x.

  Definition check_rows (p : S.prog) (rs : list S.row) (m : kmap S.key L.t) : bool :=
    forallb (fun r => row_ok L.leb (look m) (S.target p r)
      (eval_query (S.resume p) (look m) (S (length (S.deps p r))) (S.start p r))) rs.

  Definition check (p : S.prog) (m : kmap S.key L.t) : bool :=
    check_rows p (S.rows p) m.
End CheckCode.

Module Check (L : LATTICE) (S : SYSTEM L) <: CHECK L S.
  Include CheckCode L S.

  Lemma look_spec : forall m x, look m x = look_or S.key_code L.bot m x.
  Proof. reflexivity. Qed.

  Lemma check_rows_iff : forall p rs m,
    check_rows p rs m = true <-> S.post_on p rs (look m).
  Proof.
    intros p rs m; unfold check_rows, S.post_on, S.eval.
    apply forallb_forall.
  Qed.

  Lemma check_spec : forall p m, check p m = check_rows p (S.rows p) m.
  Proof. reflexivity. Qed.

  Lemma check_sound : forall p m, check p m = true -> S.post_solution p (look m).
  Proof.
    intros p m Hcheck; apply check_rows_iff; exact Hcheck.
  Qed.
End Check.
