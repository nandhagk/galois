(** * Sparse SSA analyses

    Sparse rows collect operand values before applying an abstract operation.
    For example, an incoming operand is copied to its destination parameter.

    Main results
    - [key_code_spec] Value keys retain the supplied key encoding.
    - [rows_spec] On a well-formed presentation, rows retain entry, definition and
      incoming-operand occurrence order.
    - [rows_complexity] Listing the rows is linear in their number, O(n) for n rows.
    - [start_complexity] Starting a row is linear in the row budget at the empty value,
      O(row_work p 0).
    - [deps_complexity] Listing the dependencies of a row is linear in their number times the key
      width, O((d + 1)(w + 1)) for d dependencies and key width w.
    - [target_complexity] The target of a listed row fits the row budget at the empty value,
      O(row_work p 0).
    - [sides_complexity] Listing the sides of a row is linear in their number times the key width,
      O((s + 1)(w + 1)) for s sides and key width w.

    Builds on: Framework.SparseSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Argent Require Import Time Tactics Std Loop Complexity.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig SsaSig SemanticsSig.
From Galois.Framework Require Import SparseSig.
Import ComplexityNotations.

Module List.
  TimeFun Stdlib.Lists.List.flat_map.
End List.

Definition sparse_read {X K A} (forward : K -> list A -> A)
    (op : K) (pending : list X) (received : list A)
    : query X A (sparse_frame X K A) :=
  match pending with
  | nil => Ret (forward op (rev_append received nil))
  | x :: xs => Ask x (SparseRead X K A op xs received)
  end.

TimeFun sparse_read.

Module SparseCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (L : LANG_OPS)
    (K : TYPE with Definition t := L.op) (G : TYPE with Definition t := L.guard)
    (S : SSA_OPS P N E C X K G) (V : VALUE_DOMAIN_OPS L)
    (T : SSA_TRANSFER_OPS P X L V) <: SPARSE_OPS P E X L V.
  Definition prog := P.t.
  Definition key := X.t.
  Definition row := sparse_row E.t X.t.
  Definition frame := sparse_frame X.t L.op V.t.
  Definition key_code := X.encode.
  Definition key_eqb := X.eqb.
  Definition rows p : list row :=
    map SparseSeed (S.entry_params p) ++
    map SparseDef (S.values p) ++
    map (fun r => SparseArg (fst r) (fst (snd r)) (snd (snd r))) (S.arg_rows p).
  Definition target (_ : prog) (r : row) : key :=
    match r with
    | SparseSeed x => x
    | SparseDef x => x
    | SparseArg _ x _ => x
    end.
  Definition start p (r : row) : query key V.t frame :=
    match r with
    | SparseSeed x => Ret (T.seed p x)
    | SparseDef x => match S.def p x with
      | Op op xs => sparse_read V.forward op xs nil
      | Param _ _ => Ret V.bot
      | Arbitrary => Ret V.top
      end
    | SparseArg _ _ y => Ask y (SparseCopy X.t L.op V.t)
    end.
  Definition resume (_ : prog) (f : frame) (a : V.t) : query key V.t frame :=
    match f with
    | SparseRead _ _ _ op xs acc => sparse_read V.forward op xs (a :: acc)
    | SparseCopy _ _ _ => Ret a
    end.
  Definition deps p (r : row) : list key :=
    match r with
    | SparseSeed _ => nil
    | SparseDef x => match S.def p x with Op _ xs => xs | _ => nil end
    | SparseArg _ _ y => y :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
End SparseCode.

Module Sparse (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard) (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    <: SPARSE P N E C X L K G S V T.
  Include SparseCode P N E C X L K G S V T.
  Include SYSTEM_SPEC V.
  Definition wf (_ : prog) := True.

  (** Reading an operand list returns its values in the original operand order. *)
  Lemma read_result : forall p look op xs received,
    loop_fuel (eval_step (resume p) look) (Datatypes.S (length xs))
      (sparse_read V.forward op xs received, nil) =
      inr (V.forward op (rev received ++ map look xs), nil).
  Proof.
    intros p look op xs; induction xs as [|x xs IH]; intro received.
    - cbn [length loop_fuel sparse_read eval_step peel fst snd].
      now rewrite rev_append_rev, !app_nil_r.
    - change (loop_fuel (eval_step (resume p) look) (Datatypes.S (length xs))
        (sparse_read V.forward op xs (look x :: received), nil) =
        inr (V.forward op (rev received ++ look x :: map look xs), nil)).
      rewrite IH; cbn [rev].
      now rewrite <- app_assoc.
  Qed.

  (** Each row returns its declarative contribution without side effects. *)
  Lemma eval_result : forall p r look, eval p r look = Some
    (match r with
     | SparseSeed x => T.seed p x
     | SparseDef x => match S.def p x with
       | Op op xs => V.forward op (map look xs)
       | Param _ _ => V.bot
       | Arbitrary => V.top
       end
     | SparseArg _ _ y => look y
     end, nil).
  Proof.
    intros p [x|x|e x y] look.
    - reflexivity.
    - unfold eval, deps, start; destruct (S.def p x) as [op xs|b i|].
      + unfold eval_query; rewrite read_result; reflexivity.
      + reflexivity.
      + reflexivity.
    - reflexivity.
  Qed.

  (** A prefix of an operand reader can ask only an unconsumed operand. *)
  Lemma read_asks : forall p look n op xs received q acc x f,
    loop_fuel (eval_step (resume p) look) n
      (sparse_read V.forward op xs received, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x xs.
  Proof.
    intros p look n; induction n as [|n IH];
      intros op xs received q acc x f Hloop Hask.
    - cbn [loop_fuel] in Hloop; injection Hloop as <- <-.
      destruct xs as [|y ys]; cbn [sparse_read peel fst] in Hask.
      + discriminate.
      + injection Hask as <- <-; now left.
    - destruct xs as [|y ys].
      + discriminate Hloop.
      + cbn [loop_fuel sparse_read eval_step peel fst snd resume] in Hloop.
        right; eapply IH; eassumption.
  Qed.

  (** Returning immediately cannot produce a later read. *)
  Lemma ret_no_ask : forall p look n a q acc x f,
    loop_fuel (eval_step (resume p) look) n (Ret a, nil) = inl (q, acc) ->
    fst (peel q acc) <> inr (x, f).
  Proof.
    intros p look [|n] a q acc x f Hloop.
    - injection Hloop as <- <-; discriminate.
    - discriminate.
  Qed.

  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    exact X.encode_inj.
  Qed.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact X.eqb_spec.
  Qed.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p r look _ _; rewrite eval_result; discriminate.
  Qed.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [x|x|e x y] s u _ _ Hagree; rewrite !eval_result.
    - reflexivity.
    - destruct (S.def p x) as [op xs|b i|] eqn:Hdef; try reflexivity.
      assert (Hmap : map s xs = map u xs).
      { apply map_ext_in; intros y Hy; apply Hagree.
        unfold deps; now rewrite Hdef. }
      now rewrite Hmap.
    - rewrite Hagree; [reflexivity|now left].
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [y|y|e y z] look n q acc x f _ _ Hloop Hask.
    - exfalso; eapply ret_no_ask; eassumption.
    - cbn [start] in Hloop; cbn [deps].
      destruct (S.def p y) as [op xs|b i|].
      + eapply read_asks; eassumption.
      + exfalso; eapply ret_no_ask; eassumption.
      + exfalso; eapply ret_no_ask; eassumption.
    - destruct n as [|n].
      + injection Hloop as <- <-; injection Hask as <- <-; now left.
      + cbn [start loop_fuel eval_step peel fst snd resume] in Hloop.
        exfalso; eapply ret_no_ask; eassumption.
  Qed.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p r look a ss x b _ _ Heval Hin.
    rewrite eval_result in Heval; injection Heval as _ <-; contradiction.
  Qed.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p r look a ss _ _ Heval.
    rewrite eval_result in Heval; injection Heval as _ <-; reflexivity.
  Qed.
  (** Value keys retain the supplied key encoding. *)
  Lemma key_code_spec : key_code = X.encode.
  Proof.
    reflexivity.
  Qed.
  (** Value equality retains the supplied key test. *)
  Lemma key_eqb_def : key_eqb = X.eqb.
  Proof.
    reflexivity.
  Qed.
  (** Rows retain entry, definition and incoming-operand occurrence order. *)
  Lemma rows_spec : forall p, S.wf p -> rows p =
    map SparseSeed (flat_map (S.params p) (C.entries p)) ++
    map SparseDef (S.values p) ++
    flat_map (fun e => map (fun xy => SparseArg e (fst xy) (snd xy)) (S.args p e))
      (C.edges p).
  Proof.
    intros p Hwf; unfold rows.
    rewrite S.entry_params_spec, S.arg_rows_spec by exact Hwf.
    do 2 f_equal; generalize (C.edges p); intro es.
    induction es as [|e es IH]; cbn [flat_map].
    - reflexivity.
    - now rewrite map_app, map_map, IH.
  Qed.
  (** Seed rows target their value. *)
  Lemma target_seed : forall p x, target p (SparseSeed x) = x.
  Proof.
    reflexivity.
  Qed.
  (** Definition rows target their defined value. *)
  Lemma target_def : forall p x, target p (SparseDef x) = x.
  Proof.
    reflexivity.
  Qed.
  (** Incoming-operand rows target the destination parameter. *)
  Lemma target_arg : forall p e x y, target p (SparseArg e x y) = x.
  Proof.
    reflexivity.
  Qed.
  (** Seeds have no dependencies and return their client's entry fact. *)
  Lemma eval_seed : forall p x look, eval p (SparseSeed x) look = Some (T.seed p x, nil).
  Proof.
    intros; apply eval_result.
  Qed.
  (** Definitions apply the domain transfer or supply top for arbitrary bindings. *)
  Lemma eval_def : forall p x look, eval p (SparseDef x) look = Some
    (match S.def p x with
     | Op op xs => V.forward op (map look xs)
     | Param _ _ => V.bot
     | Arbitrary => V.top
     end, nil).
  Proof.
    intros; apply eval_result.
  Qed.
  (** Incoming operands contribute their value to the destination parameter. *)
  Lemma eval_arg : forall p e x y look,
    eval p (SparseArg e x y) look = Some (look y, nil).
  Proof.
    intros; apply eval_result.
  Qed.
End Sparse.

Module SparseT (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (X : KEY_T) (L : LANG_T) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA_T P N E C X K G) (V : VALUE_DOMAIN_T L)
    (T : SSA_TRANSFER_T P X L V)
    (B : SPARSE_ENVELOPE P N E C X L K G S V)
    <: SPARSE_T P N E C X L K G S V T B.
  Include Sparse P N E C X L K G S V T.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  Definition value_bits (p : prog) : nat :=
    fold_right Nat.max 0 (map (fun r => X.bits (target p r)) (rows p)).
  Definition row_work p s :=
    (V.c_val * N.of_nat (B.op_work p s + 1) +
      N.of_nat ((B.op_arity p + 1) * (s + 1) + T.seed_work p +
        value_bits p + V.size V.top + V.size V.bot + 1))%N.
  Definition sparse_kw (p : prog) : nat := fold_right Nat.max 0
    (flat_map (fun r => map key_bits (writes p r ++ deps p r)) (rows p)).
  Definition kw := sparse_kw.
  Definition c_sys : N := (128 * (X.c_key + S.c_ssa + T.c_seed + 1))%N.

  (** A listed definition row originates in the prepared value inventory. *)
  Lemma definition_listed : forall p x,
    In (SparseDef x) (rows p) -> In x (S.values p).
  Proof.
    intros p x Hrow; unfold rows in Hrow.
    apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow].
    - apply in_map_iff in Hrow as [y [Hsame _]]; discriminate.
    - apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow].
      + apply in_map_iff in Hrow as [y [Hsame Hy]]; now injection Hsame as <-.
      + apply in_map_iff in Hrow as [r [Hsame _]]; discriminate.
  Qed.

  (** Every list member is below the list's maximum. *)
  Lemma max_member : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs.
  Proof.
    intro xs; induction xs as [|y xs IH]; intros x Hin; [contradiction|].
    cbn [fold_right]; destruct Hin as [Hsame|Hin].
    - subst y; apply Nat.le_max_l.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  (** Every target key fits the program's target-width budget. *)
  Lemma target_bits : forall p r, In r (rows p) -> X.bits (target p r) <= value_bits p.
  Proof.
    intros p r Hr; unfold value_bits; apply max_member.
    apply in_map_iff; exists r; auto.
  Qed.

  (** A bounded lookup supplies a bounded list of operands. *)
  Lemma lookup_sizes : forall (look : X.t -> V.t) xs s,
    (forall x, V.size (look x) <= s) ->
    Forall (fun a => V.size a <= s) (map look xs).
  Proof.
    intros look xs s Hsize; induction xs as [|x xs IH]; cbn [map]; constructor; auto.
  Qed.

  (** The prepared operator envelope bounds each listed operation's lookup operands. *)
  Lemma lookup_work : forall p x op xs look s,
    In (SparseDef x) (rows p) -> S.def p x = Op op xs ->
    (forall y, V.size (look y) <= s) ->
    V.work op (map look xs) <= B.op_work p s.
  Proof.
    intros p x op xs look s Hrow Hdef Hsize.
    apply (B.op_work_le p x op xs (map look xs) s).
    - now apply definition_listed.
    - exact Hdef.
    - apply length_map.
    - now apply lookup_sizes.
  Qed.

  (** A reached read frame remembers exactly its consumed operand prefix. *)
  Lemma read_frame : forall p look n op xs received q acc x f,
    loop_fuel (eval_step (resume p) look) n
      (sparse_read V.forward op xs received, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    exists before after, xs = before ++ x :: after /\
      f = SparseRead X.t L.op V.t op after (rev (map look before) ++ received).
  Proof.
    intros p look n; induction n as [|n IH];
      intros op xs received q acc x f Hloop Hask.
    - injection Hloop as <- <-; destruct xs as [|y ys].
      + discriminate Hask.
      + injection Hask as <- <-; exists nil, ys; split; reflexivity.
    - destruct xs as [|y ys]; [discriminate Hloop|].
      cbn [loop_fuel sparse_read eval_step peel fst snd resume] in Hloop.
      destruct (IH op ys (look y :: received) q acc x f Hloop Hask)
        as [before [after [Hrest Hframe]]].
      exists (y :: before), after; split.
      + cbn; now rewrite Hrest.
      + rewrite Hframe; cbn [map rev]; now rewrite <- app_assoc.
  Qed.

  (** Returning the final operand restores the original lookup order. *)
  Lemma final_operands : forall (look : X.t -> V.t) before x,
    rev_append (look x :: rev (map look before)) nil = map look (before ++ x :: nil).
  Proof.
    intros look before x; rewrite rev_append_rev, app_nil_r; cbn [rev].
    now rewrite rev_involutive, map_app.
  Qed.

  (** Step budgets grow with the sizes of the lookup values. *)
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof.
    intros p s t Hst; pose proof (B.op_work_mono p s t Hst) as Hwork.
    unfold row_work; time_cbn_all; nia.
  Qed.

  (** Every declared read or write key fits the maximum listed key width. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p r x _ Hrow Hx; unfold kw, sparse_kw; apply max_member.
    apply in_flat_map; exists r; split; [exact Hrow|now apply in_map].
  Qed.

  (** Key encoding pays for its own output bit length. *)
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intro x; pose proof (X.T_encode_le x) as Hcost.
    unfold T_key_code, key_bits, key_code, c_sys; unfold X.bits in Hcost; nia.
  Qed.

  (** Key comparison pays for the first key's bit length. *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros a b; pose proof (X.T_eqb_le a b) as Hcost.
    unfold T_key_eqb, key_bits, key_code, c_sys; unfold X.bits in Hcost; nia.
  Qed.

  (** Cached inventories make row enumeration linear in its output. *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof.
    intros p _; unfold c_sys; time_step.
    pose proof (ListDef.T_map_le (@SparseSeed E.t X.t) (fun _ => 1%N) 1%N
      (S.entry_params p) (fun _ => N.le_refl 1)) as Hseed.
    pose proof (ListDef.T_map_le (@SparseDef E.t X.t) (fun _ => 1%N) 1%N
      (S.values p) (fun _ => N.le_refl 1)) as Hdefs.
    pose proof (ListDef.T_map_le
      (fun r : E.t * (X.t * X.t) => SparseArg (fst r) (fst (snd r)) (snd (snd r)))
      (fun _ => (1 + (1 + (1 + 1 + (1 + 1))))%N) 6%N
      (S.arg_rows p) (fun _ => N.le_refl 6)) as Hargs.
    unfold rows; rewrite !length_app, !length_map in *; time_cbn_all; nia.
  Qed.

  (** Projecting a row target has constant overhead. *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [x|x|e x y] _ _; unfold c_sys; time_step.
  Qed.

  (** Starting each listed row fits the prepared reader and transfer budgets. *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p r _ Hrow; pose proof (target_bits p r Hrow) as Hbits.
    destruct r as [x|x|e x y]; cbn [target] in Hbits.
    - pose proof (T.T_seed_le p x) as Hseed.
      unfold c_sys, row_work; time_step.
    - pose proof (S.T_def_le p x) as Hreader; unfold S.operands in Hreader.
      pose proof (definition_listed p x Hrow) as Hlisted.
      destruct (S.def p x) as [op xs|b i|] eqn:Hdef.
      + pose proof (B.op_arity_le p x op xs Hlisted Hdef) as Harity.
        destruct xs as [|y ys].
        * assert (Hwork : V.work op nil <= B.op_work p 0).
          { apply (B.op_work_le p x op nil nil 0); try assumption; constructor. }
          pose proof (V.T_forward_le op nil) as Hforward.
          time_unfold T_start; time_simpl; rewrite Hdef.
          time_unfold @T_sparse_read; time_simpl.
          unfold c_sys, row_work; time_cbn; time_pose; time_cbn_all; nia.
        * time_unfold T_start; time_simpl; rewrite Hdef.
          time_unfold @T_sparse_read; time_simpl.
          unfold c_sys, row_work; time_cbn; time_pose; time_cbn_all; nia.
      + time_unfold T_start; time_simpl; rewrite Hdef.
        unfold c_sys, row_work; time_cbn; time_pose; time_cbn_all; nia.
      + time_unfold T_start; time_simpl; rewrite Hdef.
        unfold c_sys, row_work; time_cbn; time_pose; time_cbn_all; nia.
    - unfold c_sys; time_step.
  Qed.

  (** Actual reader frames pay only for a prefix of their listed operation. *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, V.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p [y|y|e y z] look s n q acc x f _ Hrow Hsize Hloop Hask.
    - exfalso; eapply ret_no_ask; eassumption.
    - cbn [start] in Hloop; destruct (S.def p y) as [op xs|b i|] eqn:Hdef.
      + destruct (read_frame p look n op xs nil q acc x f Hloop Hask)
          as [before [after [Hxs Hframe]]].
        rewrite app_nil_r in Hframe; subst f.
        pose proof (B.op_arity_le p y op xs (definition_listed p y Hrow) Hdef) as Harity.
        assert (Hlength : length before + 1 + length after <= B.op_arity p).
        { rewrite Hxs, length_app in Harity; cbn [length] in Harity; lia. }
        destruct after as [|z zs].
        * assert (Hvalues : rev_append (look x :: rev (map look before)) nil =
            map look xs) by (rewrite final_operands, Hxs; reflexivity).
          pose proof (lookup_work p y op xs look s Hrow Hdef Hsize) as Hwork.
          pose proof (V.T_forward_le op (map look xs)) as Hforward.
          assert (Hbudget : (V.T_forward op (map look xs) <=
            V.c_val * N.of_nat (B.op_work p s + 1))%N).
          { eapply N.le_trans; [exact Hforward|].
            apply N.mul_le_mono_l, time_of_nat_le, Nat.add_le_mono_r; exact Hwork. }
          pose proof (List.T_rev_append_le (look x :: rev (map look before)) nil) as Hreverse.
          time_unfold T_resume; time_unfold @T_sparse_read; time_simpl.
          rewrite Hvalues; unfold c_sys, row_work; time_cbn_all.
          rewrite length_rev, length_map in Hreverse; time_cbn_all; nia.
        * time_unfold T_resume; time_unfold @T_sparse_read; time_simpl.
          unfold c_sys; time_cbn; nia.
      + exfalso; eapply ret_no_ask; eassumption.
      + exfalso; eapply ret_no_ask; eassumption.
    - destruct n as [|n].
      + injection Hloop as <- <-; injection Hask as <- <-; unfold c_sys; time_step.
      + cbn [start loop_fuel eval_step peel fst snd resume] in Hloop.
        exfalso; eapply ret_no_ask; eassumption.
  Qed.

  (** Dependency readers pay for their row key and returned operand occurrences. *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r _ Hrow.
    assert (Hkey : X.bits (target p r) <= kw p).
    { apply (key_bits_le p r (target p r) I Hrow); now left. }
    destruct r as [x|x|e x y]; unfold c_sys.
    - time_step.
    - pose proof (S.T_def_le p x) as Hdef; cbn [target] in Hkey.
      change (S.T_def p x <= S.c_ssa *
        N.of_nat (X.bits x + length (deps p (SparseDef x)) + 1))%N in Hdef.
      assert (Hclock : T_deps p (SparseDef x) = (1 + S.T_def p x)%N).
      { unfold T_deps; destruct (S.def p x); reflexivity. }
      assert (Hwidth : X.bits x + length (deps p (SparseDef x)) + 1 <=
        (length (deps p (SparseDef x)) + 1) * (kw p + 1)).
      { clear -Hkey; nia. }
      apply time_of_nat_le in Hwidth; rewrite Nat2N.inj_mul in Hwidth.
      set (budget := (N.of_nat (length (deps p (SparseDef x)) + 1) *
        N.of_nat (kw p + 1))%N) in *.
      assert (Hnonzero : (1 <= budget)%N).
      { clear -budget; unfold budget; rewrite !Nat2N.inj_add.
        change (N.of_nat 1) with 1%N; nia. }
      assert (Hread : (S.T_def p x <= S.c_ssa * budget)%N).
      { eapply N.le_trans; [exact Hdef|now apply N.mul_le_mono_l]. }
      rewrite Hclock, <- N.mul_assoc; fold budget.
      clearbody budget; clear -Hread Hnonzero.
      eapply N.le_trans with (m := ((S.c_ssa + 1) * budget)%N).
      + rewrite N.mul_add_distr_r, N.mul_1_l; lia.
      + apply N.mul_le_mono_r; lia.
    - time_step.
  Qed.
  (** Sparse rows declare no side keys. *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r _ _; unfold c_sys; time_step.
  Qed.
  (** Every completed contribution fits the prepared value and operator budgets. *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, V.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (V.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (V.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p r look s a ss _ Hrow Hsize Heval.
    rewrite eval_result in Heval; injection Heval as <- <-; split; [|constructor].
    destruct r as [x|x|e x y].
    - eapply N.le_trans; [apply time_of_nat_le; exact (T.seed_size p x)|].
      unfold row_work; rewrite !Nat2N.inj_add; lia.
    - destruct (S.def p x) as [op xs|b i|] eqn:Hdef.
      + pose proof (lookup_work p x op xs look s Hrow Hdef Hsize) as Hwork.
        pose proof (V.forward_size op (map look xs)) as Hforward.
        eapply N.le_trans; [exact Hforward|].
        eapply N.le_trans with (m := (V.c_val * N.of_nat (B.op_work p s + 1))%N).
        * apply N.mul_le_mono_l, time_of_nat_le, Nat.add_le_mono_r; exact Hwork.
        * unfold row_work; lia.
      + unfold row_work; rewrite !Nat2N.inj_add; lia.
      + unfold row_work; rewrite !Nat2N.inj_add; lia.
    - pose proof (time_of_nat_le _ _ (Hsize y)) as Hy.
      unfold row_work; rewrite !Nat2N.inj_add, !Nat2N.inj_mul.
      change (N.of_nat 1) with 1%N; clear -Hy; nia.
  Qed.
  (** Listing the rows is linear in their number. *)
  Lemma rows_complexity : T_rows p ∈ 𝑂(N.of_nat (length (rows p))) for p | wf p.
  Proof.
    apply bigO_intro with (c := c_sys); intros p Hwf.
    pose proof (T_rows_le p Hwf) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.
  (** Starting a listed row fits the empty-value row budget. *)
  Lemma start_complexity :
    T_start p r ∈ 𝑂(row_work p 0) for (p, r) | wf p /\ In r (rows p).
  Proof.
    apply bigO_intro with (c := c_sys); intros [p r] [Hwf Hin].
    pose proof (T_start_le p r Hwf Hin) as Htime.
    change (T_start p r <= c_sys * row_work p 0 + c_sys)%N; nia.
  Qed.
  (** Dependencies cost their number times the key width. *)
  Lemma deps_complexity :
    T_deps p r ∈ 𝑂(N.of_nat ((length (deps p r) + 1) * (kw p + 1)))
      for (p, r) | wf p /\ In r (rows p).
  Proof.
    apply bigO_intro with (c := c_sys); intros [p r] [Hwf Hin].
    pose proof (T_deps_le p r Hwf Hin) as Htime.
    change (T_deps p r <=
      c_sys * N.of_nat ((length (deps p r) + 1) * (kw p + 1)) + c_sys)%N.
    rewrite Nat2N.inj_mul; nia.
  Qed.
  (** Finding the target fits the empty-value row budget. *)
  Lemma target_complexity :
    T_target p r ∈ 𝑂(row_work p 0) for (p, r) | wf p /\ In r (rows p).
  Proof.
    apply bigO_intro with (c := c_sys); intros [p r] [Hwf Hin].
    pose proof (T_target_le p r Hwf Hin) as Htime.
    change (T_target p r <= c_sys * row_work p 0 + c_sys)%N; nia.
  Qed.
  (** Side keys cost their number times the key width. *)
  Lemma sides_complexity :
    T_sides p r ∈ 𝑂(N.of_nat ((length (sides p r) + 1) * (kw p + 1)))
      for (p, r) | wf p /\ In r (rows p).
  Proof.
    apply bigO_intro with (c := c_sys); intros [p r] [Hwf Hin].
    pose proof (T_sides_le p r Hwf Hin) as Htime.
    change (T_sides p r <=
      c_sys * N.of_nat ((length (sides p r) + 1) * (kw p + 1)) + c_sys)%N.
    rewrite Nat2N.inj_mul; nia.
  Qed.
End SparseT.

Module SparseSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard) (Val : TYPE with Definition t := L.val)
    (S : SSA P N E C X K G) (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    (A : SPARSE P N E C X L K G S V T) (M : SEMANTICS P)
    (CL : CFG_LINK P N E C M) (SL : SSA_LINK P N E C X K G Val S M CL)
    (IL : SPARSE_INITIAL_LINK P N E C X L K G Val S V T M CL SL)
    <: SPARSE_SOUND P N E C X L K G Val S V T A M CL SL IL.

  (** A post-solution bounds the primary contribution of each listed row. *)
  Lemma row_bound : forall p look r a,
    A.post_solution p look -> In r (A.rows p) ->
    A.eval p r look = Some (a, nil) -> V.leb a (look (A.target p r)) = true.
  Proof.
    intros p look r a Hpost Hr Heval.
    specialize (Hpost r Hr); rewrite Heval in Hpost.
    cbn [row_ok] in Hpost; now apply andb_true_iff in Hpost as [Hpost _].
  Qed.

  (** Entry rows lift the client's seed facts to the post-solution. *)
  Lemma seed_covers : forall p look b x c,
    S.wf p -> A.post_solution p look -> In b (C.entries p) ->
    In x (S.params p b) -> V.gamma (T.seed p x) c -> V.gamma (look x) c.
  Proof.
    intros p look b x c Hwf Hpost Hb Hx Hgamma.
    assert (Hr : In (SparseSeed x) (A.rows p)).
    { rewrite A.rows_spec by exact Hwf; apply in_or_app; left.
      apply in_map; apply in_flat_map; exists b; auto. }
    pose proof (row_bound p look (SparseSeed x) (T.seed p x) Hpost Hr
      (A.eval_seed p x look)) as Hbound.
    rewrite A.target_seed in Hbound; eapply V.gamma_mono; eassumption.
  Qed.

  (** Operation rows lift a sound concrete operation result to the post-solution. *)
  Lemma operation_covers : forall p look x op xs cs c,
    S.wf p -> A.post_solution p look -> In x (S.values p) ->
    S.def p x = Op op xs -> Forall2 V.gamma (map look xs) cs ->
    SL.eval op cs = Some c -> V.gamma (look x) c.
  Proof.
    intros p look x op xs cs c Hwf Hpost Hx Hdef Hargs Heval.
    assert (Hr : In (SparseDef x) (A.rows p)).
    { rewrite A.rows_spec by exact Hwf; apply in_or_app; right.
      apply in_or_app; left; now apply in_map. }
    assert (Hrow : A.eval p (SparseDef x) look =
      Some (V.forward op (map look xs), nil)).
    { rewrite A.eval_def, Hdef; reflexivity. }
    pose proof (row_bound p look (SparseDef x) _ Hpost Hr Hrow) as Hbound.
    rewrite A.target_def in Hbound; eapply V.gamma_mono; [exact Hbound|].
    apply (V.forward_sound op (map look xs) cs c Hargs).
    now rewrite <- IL.eval_agrees.
  Qed.

  (** Incoming rows lift the source operand fact to the destination parameter. *)
  Lemma argument_covers : forall p look e x y c,
    S.wf p -> A.post_solution p look -> In e (C.edges p) ->
    In (x, y) (S.args p e) -> V.gamma (look y) c -> V.gamma (look x) c.
  Proof.
    intros p look e x y c Hwf Hpost He Harg Hgamma.
    assert (Hr : In (SparseArg e x y) (A.rows p)).
    { rewrite A.rows_spec by exact Hwf; apply in_or_app; right.
      apply in_or_app; right; apply in_flat_map; exists e; split; [exact He|].
      apply in_map_iff; exists (x, y); auto. }
    pose proof (row_bound p look (SparseArg e x y) _ Hpost Hr
      (A.eval_arg p e x y look)) as Hbound.
    rewrite A.target_arg in Hbound; eapply V.gamma_mono; eassumption.
  Qed.

  (** Arbitrary definitions contribute top and therefore cover every concrete value. *)
  Lemma arbitrary_covers : forall p look x c,
    S.wf p -> A.post_solution p look -> In x (S.values p) ->
    S.def p x = Arbitrary -> V.gamma (look x) c.
  Proof.
    intros p look x c Hwf Hpost Hx Hdef.
    assert (Hr : In (SparseDef x) (A.rows p)).
    { rewrite A.rows_spec by exact Hwf; apply in_or_app; right.
      apply in_or_app; left; now apply in_map. }
    assert (Hrow : A.eval p (SparseDef x) look = Some (V.top, nil)).
    { rewrite A.eval_def, Hdef; reflexivity. }
    pose proof (row_bound p look (SparseDef x) V.top Hpost Hr Hrow) as Hbound.
    rewrite A.target_def in Hbound.
    eapply V.gamma_mono; [exact Hbound|apply V.gamma_top].
  Qed.

  (** Pointwise covered bindings supply an operation's corresponding operand facts. *)
  Lemma operand_facts : forall look s xs cs,
    Forall2 (fun y d => SL.venv s y = Some d) xs cs ->
    (forall y d, In y xs -> SL.venv s y = Some d -> V.gamma (look y) d) ->
    Forall2 V.gamma (map look xs) cs.
  Proof.
    intros look s xs cs Hargs; induction Hargs as [|x c xs cs Hx Hargs IH];
      intro Hfacts; cbn [map]; constructor.
    - apply Hfacts; [now left|exact Hx].
    - apply IH; intros y d Hy Hd; apply Hfacts; [now right|exact Hd].
  Qed.

  (** An operand of an operation at an entry has the same definition home. *)
  Lemma initial_operand_home : forall p s x op xs y,
    S.wf p -> M.initial p s -> In x (S.values p) ->
    S.def p x = Op op xs -> S.home p x = CL.point s -> In y xs ->
    S.home p y = S.home p x.
  Proof.
    intros p s x op xs y Hwf Hinitial Hx Hdef Hhome Hy.
    destruct (S.op_args_dominate p x op xs y Hwf Hx Hdef Hy) as [_ Hdom].
    rewrite Hhome in Hdom |- *.
    specialize (Hdom (CL.point s) (CL.point s :: nil)
      (CL.init_entry p s Hinitial)).
    assert (Hpath : presentation_path (C.edges p) (C.src p) (C.dst p)
      (CL.point s) (CL.point s :: nil) (CL.point s)) by constructor.
    specialize (Hdom Hpath); cbn in Hdom; destruct Hdom as [Hsame|Hfalse].
    - symmetry; exact Hsame.
    - contradiction.
  Qed.

  (** Well-founded operation dependencies propagate the initial seed facts. *)
  Lemma initial_covers : forall p look s,
    S.wf p -> A.post_solution p look -> M.initial p s ->
    forall x c, SL.venv s x = Some c -> V.gamma (look x) c.
  Proof.
    intros p look s Hwf Hpost Hinitial.
    refine (well_founded_induction (S.op_args_acyclic p Hwf)
      (fun x => forall c, SL.venv s x = Some c -> V.gamma (look x) c) _).
    intros x IH c Hvalue.
    assert (Hreach : reachable (M.initial p) (M.step p) s) by now constructor.
    pose proof (SL.coverage p s x c Hreach Hvalue) as Hx.
    destruct (IL.initial_binding p s x c Hinitial Hvalue)
      as [[b [Hb [Hparam Hseed]]]|[[op [xs [cs [Hdef [Hhome [Hargs Heval]]]]]]|Hdef]].
    - eapply seed_covers; eassumption.
    - eapply (operation_covers p look x op xs cs c); try eassumption.
      eapply operand_facts; [exact Hargs|].
      intros y d Hy Hd; apply (IH y); [|exact Hd].
      split; [exact Hx|]; split.
      + eapply initial_operand_home; eassumption.
      + exists op, xs; auto.
    - eapply arbitrary_covers; eassumption.
  Qed.

  (** A step covers changed bindings by induction within their definition home. *)
  Lemma step_covers : forall p look s t,
    S.wf p -> A.post_solution p look -> reachable (M.initial p) (M.step p) s ->
    M.step p s t ->
    (forall x c, SL.venv s x = Some c -> V.gamma (look x) c) ->
    forall x c, SL.venv t x = Some c -> V.gamma (look x) c.
  Proof.
    intros p look s t Hwf Hpost Hreach Hstep Hfacts.
    destruct (CL.step_edge p s t Hreach Hstep) as [edge [Htaken _]].
    refine (well_founded_induction (S.op_args_acyclic p Hwf)
      (fun x => forall c, SL.venv t x = Some c -> V.gamma (look x) c) _).
    intros x IH c Hvalue.
    assert (Ht : reachable (M.initial p) (M.step p) t) by (econstructor 2; eassumption).
    pose proof (SL.coverage p t x c Ht Hvalue) as Hx.
    destruct (SL.value_origin p s t x c Hreach Hstep Hvalue)
      as [Hsame|[[op [xs [cs [Hdef [Hargs Heval]]]]]|[Hparam|Hdef]]].
    - now apply Hfacts.
    - destruct (N.eqb_spec (S.home p x) (CL.point t)) as [Hhome|Haway].
      + eapply (operation_covers p look x op xs cs c); try eassumption.
        eapply operand_facts; [exact Hargs|]; intros y d Hy Hd.
        destruct (N.eqb_spec (S.home p y) (S.home p x)) as [Hsamehome|Hother].
        * apply (IH y); [|exact Hd].
          split; [exact Hx|]; split; [exact Hsamehome|exists op, xs; auto].
        * apply Hfacts; rewrite <- (SL.frame_on_edge p s t edge y Hreach Hstep Htaken);
            [exact Hd|now rewrite <- Hhome].
      + apply Hfacts; rewrite <- (SL.frame_on_edge p s t edge x Hreach Hstep Htaken);
          assumption.
    - destruct Hparam as [e [b [i [y [Hdef [Hedge [Hdst [Harg Hy]]]]]]]].
      eapply (argument_covers p look e x y c); try eassumption.
      + exact (IL.taken_listed p s t e Hreach Hstep Hedge).
      + now apply nth_error_In in Harg.
      + now apply Hfacts.
    - eapply arbitrary_covers; eassumption.
  Qed.

  (** Sparse post-solutions cover every binding in every reachable state. *)
  Lemma covers : forall p look, S.wf p -> A.post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s ->
      forall x c, SL.venv s x = Some c -> V.gamma (look x) c.
  Proof.
    intros p look Hwf Hpost s Hreach; induction Hreach as [s Hinitial|s t Hreach IH Hstep].
    - eapply initial_covers; eassumption.
    - eapply step_covers; eassumption.
  Qed.
End SparseSound.
