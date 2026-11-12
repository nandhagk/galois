(** * Abstract interpretation of ordered actions *)
From Stdlib Require Import List.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig InterpSig.
Import List.ListNotations.

Module InterpCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN_OPS X L V) <: SYSTEM_OPS D.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with Seed n => n | Flow e => C.dst p e end.
  Definition start p (r : row) : query key D.t frame :=
    match r with Seed _ => Ret D.top | Flow e => Ask (C.src p e) e end.
  Definition resume p (e : frame) st : query key D.t frame :=
    Ret (fold_left (fun st a =>
      match a with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) (A.actions p e) st).
  Definition deps p (r : row) : list key :=
    match r with Seed _ => [] | Flow e => [C.src p e] end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End InterpCode.

Module Interp (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN X L V)
    <: SYSTEM D <: INTERP_SYSTEM P N E C X L V A D.
  Include InterpCode P N E C X L V A D.
  Include SYSTEM_SPEC D.

  Definition wf (_ : prog) := True.

  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. exact N.encode_inj. Qed.

  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof. intros p [n|e] look _ _; discriminate. Qed.

  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [n|e] s u _ _ Hread; [reflexivity|].
    assert (Hsrc : s (C.src p e) = u (C.src p e)) by (apply Hread; simpl; auto).
    unfold eval, deps, start, resume, eval_query, eval_step; simpl; now rewrite Hsrc.
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
  Lemma target_flow : forall p e, target p (Flow e) = C.dst p e.
  Proof. reflexivity. Qed.
  Lemma eval_seed : forall p n look, eval p (Seed n) look = Some (D.top, nil).
  Proof. reflexivity. Qed.
  Lemma eval_flow : forall p e look, eval p (Flow e) look = Some
    (fold_left (fun st a =>
      match a with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) (A.actions p e) (look (C.src p e)), nil).
  Proof. reflexivity. Qed.
End Interp.
