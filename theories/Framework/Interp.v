(** * Abstract interpretation of ordered actions *)
From Stdlib Require Import List Bool NArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.
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
  Definition key_eqb := N.eqb.
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

  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted.

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

  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted.

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

Module InterpSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (A : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) (M : SEMANTICS P) (K : INTERP_LINK P N E C X L A M).
  Module S := Interp P N E C X L V A D.
  Include Interp P N E C X L V A D.
  Module Sound <: INTERP_SOUND P N E C X L V A D S M K.
  Lemma covers : forall p look, post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> D.gamma (look (K.point s)) (K.store s).
  Proof. Admitted. (* CONVERT: sound: Unexpected name (no introduction patterns were expected in the *)
  End Sound.
  Include Sound.
End InterpSound.

Module InterpT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V)
    (B : INTERP_ENVELOPE P E X L V A D) <: INTERP_T P N E C X L V A D B.
  Include Interp P N E C X L V A D.
  Include INTERP_COST_SPEC P N E C X L V A D B.
  Definition row_work := interp_work.
  Definition kw := interp_kw.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  Definition c_sys : N := 1%N. (* STUB *)
  (** Step budgets grow with the size of abstract values. *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof. Admitted. (* STUB *)
  (** The program key budget covers all declared reads and writes. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)
  (** Encoding costs are linear in the resulting code size. *)
  Lemma T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Equality costs are bounded by the first key's code size. *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Enumerating rows costs linear time in the output length. *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Target lookup fits the row budget. *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Starting a row fits the row budget. *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Resuming a frame accounts for the size of the supplied abstract value. *)
  Lemma T_resume_le : forall p f a, wf p ->
    (T_resume p f a <= c_sys * (row_work p (D.size a) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Dependency enumeration pays for every key occurrence. *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Side enumeration pays for every key occurrence. *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Row output sizes fit the transfer budget. *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, D.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (D.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (D.size (snd xb)) <= row_work p s)%N) ss.
  Proof. Admitted. (* STUB *)
End InterpT.
