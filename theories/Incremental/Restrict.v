(** * Placeholder restricted systems

    A restricted program stores the original program, frozen values and selected rows.
    For example, selecting no rows retains an empty row list.
    Builds on: RestrictSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Incremental Require Import RestrictSig.

Import List.ListNotations.

Record restricted_program (P K A R : Type) := {
  original : P;
  seeds : list (K * A);
  selected : list R
}.

TimeFun original.
TimeFun seeds.
TimeFun selected.

Module RestrictedCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L) <: LOCAL_SYSTEM_OPS L.
  Definition prog := restricted_program S.prog S.key L.t S.row.
  Definition key := S.key.
  Definition row := S.row.
  Definition frame := S.frame.
  Definition key_code := S.key_code.
  (* STUB-CODE *)
  Definition rows (p : prog) : list row := selected _ _ _ _ p.
  (* STUB-CODE *)
  Definition target (p : prog) : row -> key := S.target (original _ _ _ _ p).
  (* STUB-CODE *)
  Definition start (p : prog) : row -> query key L.t frame := S.start (original _ _ _ _ p).
  (* STUB-CODE *)
  Definition resume (p : prog) : frame -> L.t -> query key L.t frame :=
    S.resume (original _ _ _ _ p).
  (* STUB-CODE *)
  Definition deps (p : prog) : row -> list key := S.deps (original _ _ _ _ p).
  (* STUB-CODE *)
  Definition sides (p : prog) : row -> list key := S.sides (original _ _ _ _ p).
  Definition row_code := S.row_code.
  (* STUB-CODE *)
  Definition rows_of (_ : prog) (_ : key) : list row := [].
End RestrictedCode.

Module RestrictCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L).
  Module RS := RestrictedCode L S.
  Module Code <: RESTRICT_OPS L S RS.
    (* STUB-CODE *)
    Definition mk (p : S.prog) (fz : list (S.key * L.t)) (rs : list S.row) : RS.prog :=
      {| original := p; seeds := fz; selected := rs |}.
  End Code.
End RestrictCode.

Module Restricted (L : LATTICE) (S : LOCAL_SYSTEM L) <: LOCAL_SYSTEM L.
  Include RestrictedCode L S.
  Include SYSTEM_SPEC L.
  Definition wf (_ : prog) : Prop := True.
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. Admitted.

  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted.

  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted.

  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted.

  Lemma row_code_inj : forall p a b, In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof. Admitted.

  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof. Admitted.

End Restricted.

Module RestrictedT (L : LATTICE_T) (S : LOCAL_SYSTEM_T L) <: LOCAL_SYSTEM_T L.
  Include Restricted L S.
  TimeFun key_code.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  TimeFun row_code.
  TimeFun rows_of.
  Definition row_work (_ : prog) (_ : nat) : N := 0%N.
  Definition kw (_ : prog) : nat := 0.
  Definition c_sys : N := 1. (* STUB *)
  Definition c_loc : N := 1. (* STUB *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof. Admitted. (* STUB *)

  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)

  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
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
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_row_code_le : forall r,
    (T_row_code r <= c_loc * N.of_nat (Pos.size_nat (row_code r) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_rows_of_le : forall p x, wf p ->
    (T_rows_of p x <= c_loc * N.of_nat (length (rows_of p x) + key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)

End RestrictedT.

Module Restrict (L : LATTICE) (S : LOCAL_SYSTEM L).
  Module RS := Restricted L S.
  Module Impl <: RESTRICT L S RS.
    Module C := RestrictCode L S.
    Include C.Code.
    Include RESTRICT_SPEC L S RS.
  Lemma restrict_post : forall p fz rs s, RS.post_solution (mk p fz rs) s ->
    (forall r, In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true) /\
    (forall x v, In (x, v) fz -> L.leb v (s x) = true).
  Proof. Admitted.

  Lemma restrict_complete : forall p fz rs s, S.post_solution p s ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x v, In (x, v) fz -> L.leb v (s x) = true) ->
    RS.post_solution (mk p fz rs) s.
  Proof. Admitted.

  Lemma mk_wf : forall p fz rs, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) -> RS.wf (mk p fz rs).
  Proof. Admitted.

  End Impl.
End Restrict.

Module RestrictT (L : LATTICE_T) (S : LOCAL_SYSTEM_T L).
  Module RS := RestrictedT L S.
  Module Impl <: RESTRICT_ALL L S RS.
    Module Plain := Restrict L S.
    Include Plain.Impl.
    TimeFun mk.
    Definition c_res : N := 1. (* STUB *)
  Lemma T_mk_le : forall p fz rs,
    (T_mk p fz rs <= c_res *
      N.of_nat ((fold_right Nat.add 0
        (map (fun r => Pos.size_nat (S.row_code r) + 1) rs) +
       fold_right Nat.add 0
        (map (fun xv => S.key_bits (fst xv) + L.size (snd xv) + 1) fz) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

  Lemma restrict_writes : forall p fz rs s r, RS.post_solution (mk p fz rs) s ->
    In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true.
  Proof. Admitted. (* STUB *)

  End Impl.
End RestrictT.
