(** * Checked narrowing

    Each pass aggregates row contributions against a frozen store.
    For example, a rejected candidate leaves the input store unchanged.
    Builds on: Fixpoint.NarrowSig and Fixpoint.Query. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig NarrowSig.

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
  Definition narrow_one old sums acc (x : S.key) :=
    let code := S.key_code x in
    let aggregate := look_or S.key_code L.bot sums x in
    let before := C.look old x in
    let after := if L.leb aggregate before then L.narrow before aggregate else before in
    PTrieCode.set code (x, after) acc.
  Definition narrow_candidate p m :=
    let sums := fold_left (collect_row p m) (S.rows p) Empty in
    fold_left (narrow_one m sums)
      (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) m.
  Definition narrow_pass p m :=
    let candidate := narrow_candidate p m in
    if C.check p candidate then candidate else m.
  Definition refine p n m := Nat.iter n (narrow_pass p) m.
End NarrowCode.

Module Narrow (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S) <: NARROW L S C.
  Include NarrowCode L S C.
  Lemma narrow_pass_spec : forall p m,
    narrow_pass p m = if C.check p (narrow_candidate p m) then narrow_candidate p m else m.
  Proof. Admitted.
  Lemma refine_spec : forall p n m, refine p n m = Nat.iter n (narrow_pass p) m.
  Proof. Admitted.
  Lemma narrow_pass_post : forall p m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (narrow_pass p m)).
  Proof. Admitted.
  Lemma narrow_pass_below : forall p m x,
    L.leb (C.look (narrow_pass p m) x) (C.look m x) = true.
  Proof. Admitted. (* SIG-QUESTION: arbitrary stores can contain mismatched encoded keys. *)
  Lemma narrow_pass_exact_mono : forall p, S.monotone p -> forall m,
    S.post_solution p (C.look m) -> C.check p (narrow_candidate p m) = true.
  Proof. Admitted. (* SIG-QUESTION: weak narrowing laws do not guarantee acceptance. *)
  Lemma refine_post : forall p n m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (refine p n m)).
  Proof. Admitted.
  Lemma refine_below : forall p n m x,
    L.leb (C.look (refine p n m) x) (C.look m x) = true.
  Proof. Admitted. (* SIG-QUESTION: arbitrary stores can contain mismatched encoded keys. *)
End Narrow.
