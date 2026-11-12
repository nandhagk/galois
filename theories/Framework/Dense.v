(** * Dense dataflow systems *)
From Stdlib Require Import List.
From Argent Require Import Loop.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig.
Import List.ListNotations.

Module DenseCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    <: SYSTEM_OPS L.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with
    | Seed n => n
    | Flow e => match T.dir with Forward => C.dst p e | Backward => C.src p e end
    end.
  Definition start p (r : row) : query key L.t frame :=
    match r with
    | Seed n => Ret (T.boundary p n)
    | Flow e => Ask (match T.dir with Forward => C.src p e | Backward => C.dst p e end) e
    end.
  Definition resume p (e : frame) a : query key L.t frame := Ret (T.transfer p e a).
  Definition deps p (r : row) : list key :=
    match r with
    | Seed _ => []
    | Flow e => [match T.dir with Forward => C.src p e | Backward => C.dst p e end]
    end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End DenseCode.

Module Dense (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    <: SYSTEM L <: DENSE_SYSTEM P N E C L T.
  Include DenseCode P N E C L T.
  Include SYSTEM_SPEC L.

  Definition wf (_ : prog) := True.

  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. exact N.encode_inj. Qed.

  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof. intros p [n|e] look _ _; discriminate. Qed.

  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [n|e] s u _ _ Hread; [reflexivity|].
    change (Some (T.transfer p e (s (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), (@nil (key * L.t))) = Some (T.transfer p e (u (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), (@nil (key * L.t)))).
    rewrite Hread by (simpl; auto); reflexivity.
  Qed.

  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [n|e] look a ss x b _ _ Heval Hin;
      unfold eval, deps, start, resume in Heval; simpl in Heval;
      inversion Heval; subst; contradiction.
  Qed.

  Lemma rows_spec : forall p, rows p = map Seed (C.entries p) ++ map Flow (C.edges p).
  Proof. reflexivity. Qed.
  Lemma target_seed : forall p n, target p (Seed n) = n.
  Proof. reflexivity. Qed.
  Lemma target_flow : forall p e, target p (Flow e) =
    match T.dir with Forward => C.dst p e | Backward => C.src p e end.
  Proof. reflexivity. Qed.
  Lemma eval_seed : forall p n look, eval p (Seed n) look = Some (T.boundary p n, nil).
  Proof. reflexivity. Qed.
  Lemma eval_flow : forall p e look, eval p (Flow e) look = Some
    (T.transfer p e (look (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), nil).
  Proof. reflexivity. Qed.
End Dense.
