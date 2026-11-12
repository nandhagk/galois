(** * Dense dataflow systems *)
From Stdlib Require Import List Relation_Operators Bool NArith.
From Argent Require Import Loop Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.
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
  Definition key_eqb := N.eqb.
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

  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted.

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

  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted.

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

Module DenseSound (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P) (K : FLOW_LINK P N E C L T M).
  Module S := Dense P N E C L T.
  Include Dense P N E C L T.
  Module Sound <: DENSE_SOUND P N E C L T S M K.
  Lemma covers : forall p look, T.dir = Forward -> post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> K.gamma (look (K.point s)) s.
  Proof. Admitted. (* CONVERT: forward_invariant_sound: No product even after head-reduction. *)
  End Sound.
  Include Sound.
End DenseSound.

Module DenseBackwardSound (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P) (K : BACKWARD_LINK P N E C L T M).
  Module S := Dense P N E C L T.
  Include Dense P N E C L T.
  Module Sound <: DENSE_BACKWARD_SOUND P N E C L T S M K.
  (** Backward post-solutions cover finite suffixes ending at a terminal state. *)
  Lemma covers_backward : forall p look, T.dir = Backward -> post_solution p look ->
    forall s t, clos_refl_trans M.state (M.step p) s t -> K.terminal p t ->
      K.gamma (look (K.point s)) s.
  Proof. Admitted. (* CONVERT: backward_witness_sound: No product even after head-reduction. *)
  End Sound.
  Include Sound.
End DenseBackwardSound.

Module DenseT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (L : LATTICE_T) (T : FLOW_T P N E L)
    <: DENSE_T P N E C L T.
  Include Dense P N E C L T.
  Definition row_work := T.flow_work.
  Definition kw (p : prog) : nat := fold_right Nat.max 0
    (List.map N.bits (C.entries p ++
      flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))).
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
    (T_resume p f a <= c_sys * (row_work p (L.size a) + 1))%N.
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
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof. Admitted. (* STUB *)
End DenseT.
