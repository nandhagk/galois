(** * Checking system post-solutions

    Checkers validate all contributions against a finite candidate store.
    For example, an absent binding is read as bottom.
    Builds on: Fixpoint.SystemSig, Fixpoint.Query and Base.MapSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.

Module Type CHECK_OPS (L : LATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter look : kmap S.key L.t -> S.key -> L.t.
  Parameter check_rows : S.prog -> list S.row -> kmap S.key L.t -> bool.
  Parameter check : S.prog -> kmap S.key L.t -> bool.
End CHECK_OPS.

Module Type CHECK_LAWS (L : LATTICE) (S : SYSTEM L) (Import C : CHECK_OPS L S).
  (** Lookup uses bottom for absent bindings. *)
  Parameter look_spec : forall m x, look m x = look_or S.key_code L.bot m x.
  (** Row checking reflects the post-solution property on the selected rows. *)
  Parameter check_rows_iff : forall p rs m,
    check_rows p rs m = true <-> S.post_on p rs (look m).
  (** Checking a program checks all its rows. *)
  Parameter check_spec : forall p m, check p m = check_rows p (S.rows p) m.
  (** Every accepted candidate is a post-solution. *)
  Parameter check_sound : forall p m, check p m = true -> S.post_solution p (look m).
End CHECK_LAWS.

Module Type CHECK (L : LATTICE) (S : SYSTEM L) := CHECK_OPS L S <+ CHECK_LAWS L S.

Module Type CHECK_TIME (L : LATTICE_T) (S : SYSTEM_T L) (Import C : CHECK L S).
  Parameter T_look : kmap S.key L.t -> S.key -> N.
  Parameter T_check_rows : S.prog -> list S.row -> kmap S.key L.t -> N.
  Parameter T_check : S.prog -> kmap S.key L.t -> N.
  Parameter c_chk : N.
  (** Lookup accounts for encoding and trie traversal. *)
  Parameter T_look_le : forall m x,
    (T_look m x <= c_chk * N.of_nat (S.key_bits x + 1))%N.
  (** Row checking accounts for each declared read and side contribution. *)
  Parameter T_check_rows_le : forall p rs m B, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x, L.size (look m x) <= B) ->
    (T_check_rows p rs m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs))%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
  (** Whole-program checking uses the same row budget. *)
  Parameter T_check_le : forall p m B, S.wf p ->
    (forall x, L.size (look m x) <= B) ->
    (T_check p m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)))%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
End CHECK_TIME.

Module Type CHECK_T (L : LATTICE_T) (S : SYSTEM_T L) := CHECK L S <+ CHECK_TIME L S.
