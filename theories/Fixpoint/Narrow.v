(** * Checked narrowing

    Each pass aggregates row contributions against a frozen store.
    For example, a rejected candidate leaves the input store unchanged.
    Builds on: Fixpoint.NarrowSig and Fixpoint.Query. *)

From Stdlib Require Import List PArith.
From Stdlib Require Import NArith.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Code MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig NarrowSig.
Import Code.List.

Module NarrowCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L) (C : CHECK_OPS L S)
    <: NARROW_OPS L S C.
  Definition collect_one (sums : kmap S.key L.t) (xa : S.key * L.t) :=
    let '(x, a) := xa in
    let old := look_or S.key_code L.bot sums x in
    PTrieCode.set (S.key_code x) (x, L.join old a) sums.
  Definition collect_row p m sums r :=
    match eval_query (S.resume p) (C.look m) (Datatypes.S (length (S.deps p r)))
        (S.start p r) with
    | None => sums
    | Some (a, sides) => fold_left collect_one ((S.target p r, a) :: sides) sums
    end.
  Definition eval_all p m := fold_left (collect_row p m) (S.rows p) Empty.
  Definition narrow_one old sums acc (x : S.key) :=
    let code := S.key_code x in
    let aggregate := look_or S.key_code L.bot sums x in
    let before := C.look old x in
    let after := if L.leb aggregate before then L.narrow before aggregate else before in
    PTrieCode.set code (x, after) acc.
  Definition narrow_candidate p m :=
    let sums := eval_all p m in
    fold_left (narrow_one m sums)
      (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) m.
  Definition narrow_pass p m :=
    let candidate := narrow_candidate p m in
    if C.check p candidate then candidate else m.
  Definition refine p n m :=
    match loop_fuel (fun st => @inl (kmap S.key L.t) unit (narrow_pass p st)) n m with
    | inl result => result
    | inr _ => m
    end.
End NarrowCode.

Module Narrow (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S) <: NARROW L S C.
  Include NarrowCode L S C.
  Include NARROW_SPEC L S C.
  Lemma narrow_candidate_spec : forall p m x, S.wf p ->
    C.look (narrow_candidate p m) x =
      if writtenb p x then
        (let a := C.look m x in let b := contrib p m x in
         if L.leb b a then L.narrow a b else a)
      else C.look m x.
  Proof. Admitted. (* STUB *)
  Lemma narrow_pass_spec : forall p m,
    narrow_pass p m = if C.check p (narrow_candidate p m) then narrow_candidate p m else m.
  Proof. Admitted. (* STUB *)
  Lemma refine_spec : forall p n m, refine p n m = Nat.iter n (narrow_pass p) m.
  Proof. Admitted. (* STUB *)
  Lemma narrow_pass_post : forall p m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (narrow_pass p m)).
  Proof. Admitted. (* STUB *)
  Lemma narrow_pass_below : forall p m x,
    L.leb (C.look (narrow_pass p m) x) (C.look m x) = true.
  Proof. Admitted. (* STUB *)
  Lemma narrow_pass_exact_mono : forall p, S.monotone p -> forall m,
    S.post_solution p (C.look m) -> C.check p (narrow_candidate p m) = true.
  Proof. Admitted. (* STUB *)
  Lemma refine_post : forall p n m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (refine p n m)).
  Proof. Admitted. (* STUB *)
  Lemma refine_below : forall p n m x,
    L.leb (C.look (refine p n m) x) (C.look m x) = true.
  Proof. Admitted. (* STUB *)
End Narrow.

Module NarrowT (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S) (B : BUDGET L S)
    <: NARROW_T L S C B.
  Include Narrow L S C.
  TimeFun collect_one.
  TimeFun collect_row.
  TimeFun eval_all.
  TimeFun narrow_one.
  TimeFun narrow_candidate.
  TimeFun narrow_pass.
  TimeFun refine.

  Definition c_nar : N := 1%N. (* STUB *)
  Definition pass_work (p : S.prog) : N :=
    (N.of_nat ((fold_right Nat.add 0
      (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)) + 1)%nat) *
    (S.row_work p (B.vsize p) + N.of_nat (S.kw p) +
      L.c_lat * N.of_nat (B.vsize p + 1) + 1))%N.
  (** One pass fits a budgeted row sweep. *)
  Lemma T_narrow_pass_le : forall p m, S.wf p ->
    (forall x, B.inv p (C.look m x)) -> (T_narrow_pass p m <= c_nar * pass_work p)%N.
  Proof. Admitted. (* STUB *)
  (** Every refinement pass fits the same invariant budget. *)
  Lemma T_refine_le : forall p k m, S.wf p ->
    (forall x, B.inv p (C.look m x)) ->
    (T_refine p k m <= c_nar * N.of_nat (k + 1) * pass_work p)%N.
  Proof. Admitted. (* STUB *)
End NarrowT.
