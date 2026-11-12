(** * Checked narrowing passes

    Narrowing refines a candidate and falls back when checking fails.
    For example, a failed candidate check keeps the input store.
    Builds on: Fixpoint.CheckSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List NArith PArith.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.

Module Type NARROW_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (C : CHECK_OPS L S).
  Parameter narrow_candidate : S.prog -> kmap S.key L.t -> kmap S.key L.t.
  Parameter narrow_pass : S.prog -> kmap S.key L.t -> kmap S.key L.t.
  Parameter refine : S.prog -> nat -> kmap S.key L.t -> kmap S.key L.t.
End NARROW_OPS.

Module Type NARROW_SPEC (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (C : CHECK_OPS L S) (Import R : NARROW_OPS L S C).
  Definition contrib (p : S.prog) (m : kmap S.key L.t) (x : S.key) : L.t :=
    fold_left (fun acc r =>
      match eval_query (S.resume p) (C.look m) (Datatypes.S (length (S.deps p r)))
          (S.start p r) with
      | Some (a, ss) =>
        fold_left (fun acc2 yb =>
            if Pos.eqb (S.key_code (fst yb)) (S.key_code x)
            then L.join acc2 (snd yb) else acc2)
          ss (if Pos.eqb (S.key_code (S.target p r)) (S.key_code x)
              then L.join acc a else acc)
      | None => acc
      end) (S.rows p) L.bot.
  Definition writtenb (p : S.prog) (x : S.key) : bool :=
    existsb (fun r => existsb (fun y => Pos.eqb (S.key_code y) (S.key_code x))
      (S.target p r :: S.sides p r)) (S.rows p).
End NARROW_SPEC.

Module Type NARROW_LAWS (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S)
    (Import R : NARROW_OPS L S C)
    (Import RS : NARROW_SPEC L S C R).
  (** The candidate narrows joined contributions only when they lie below the old value. *)
  Parameter narrow_candidate_spec : forall p m x, S.wf p ->
    C.look (narrow_candidate p m) x =
      if writtenb p x then
        (let a := C.look m x in let b := contrib p m x in
         if L.leb b a then L.narrow a b else a)
      else C.look m x.
  (** A pass accepts the candidate precisely when its check succeeds. *)
  Parameter narrow_pass_spec : forall p m,
    narrow_pass p m = if C.check p (narrow_candidate p m)
      then narrow_candidate p m else m.
  (** Refinement performs the requested number of checked passes. *)
  Parameter refine_spec : forall p n m,
    refine p n m = Nat.iter n (narrow_pass p) m.
  (** Checked narrowing keeps a post-solution. *)
  Parameter narrow_pass_post : forall p m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (narrow_pass p m)).
  (** A pass lowers every lookup value. *)
  Parameter narrow_pass_below : forall p m x,
    L.leb (C.look (narrow_pass p m) x) (C.look m x) = true.
  (** Monotone systems accept the narrowing candidate of a post-solution. *)
  Parameter narrow_pass_exact_mono : forall p, S.monotone p -> forall m,
    S.post_solution p (C.look m) -> C.check p (narrow_candidate p m) = true.
  (** Repeated checked passes keep a post-solution. *)
  Parameter refine_post : forall p n m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (refine p n m)).
  (** Repeated passes lower every lookup value. *)
  Parameter refine_below : forall p n m x,
    L.leb (C.look (refine p n m) x) (C.look m x) = true.
End NARROW_LAWS.

Module Type NARROW (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S) :=
  NARROW_OPS L S C <+ NARROW_SPEC L S C <+ NARROW_LAWS L S C.

Module Type NARROW_TIME (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S)
    (B : BUDGET L S) (Import R : NARROW L S C).
  Parameter T_narrow_candidate : S.prog -> kmap S.key L.t -> N.
  Parameter T_narrow_pass : S.prog -> kmap S.key L.t -> N.
  Parameter T_refine : S.prog -> nat -> kmap S.key L.t -> N.
  Parameter c_nar : N.
  Definition pass_work (p : S.prog) : N :=
    (N.of_nat ((fold_right Nat.add 0
      (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)) + 1)%nat) *
    (S.row_work p (B.vsize p) + N.of_nat (S.kw p) +
      L.c_lat * N.of_nat (B.vsize p + 1) + 1))%N.
  (** One pass fits a budgeted row sweep. *)
  Parameter T_narrow_pass_le : forall p m, S.wf p ->
    (forall x, B.inv p (C.look m x)) -> (T_narrow_pass p m <= c_nar * pass_work p)%N.
  (** Every refinement pass fits the same invariant budget. *)
  Parameter T_refine_le : forall p k m, S.wf p ->
    (forall x, B.inv p (C.look m x)) ->
    (T_refine p k m <= c_nar * N.of_nat (k + 1) * pass_work p)%N.
End NARROW_TIME.

Module Type NARROW_T (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S) (B : BUDGET L S) :=
  NARROW L S C <+ NARROW_TIME L S C B.
