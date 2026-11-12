(** * Full solution checking

    The checker evaluates each row and checks every value written by the row. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Tactics Std.
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

Module CheckT (L : LATTICE_T) (S : SYSTEM_T L) <: CHECK_T L S.
  Include Check L S.
  TimeFun look.
  TimeFun check_rows.
  TimeFun check.

  Definition c_chk : N := 1. (* STUB *)

  Lemma T_look_le : forall m x,
    (T_look m x <= c_chk * N.of_nat (S.key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_rows_le : forall p rs m B, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x, L.size (look m x) <= B) ->
    (T_check_rows p rs m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs) + 1)%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_le : forall p m B, S.wf p ->
    (forall x, L.size (look m x) <= B) ->
    (T_check p m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
          (S.rows p)) + 1)%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
  Proof. Admitted. (* STUB *)
End CheckT.
