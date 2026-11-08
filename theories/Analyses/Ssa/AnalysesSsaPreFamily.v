(** * Finite expression families and memoized discovery

    Discovery translates each newly memoized expression along every ordered block edge.
    For example, duplicate arrivals consume work without repeating the translation callbacks.
    Builds on: AnalysesSsaPreContext, CostLoop, BaseSet and FrameworkUtil. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseRel.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Framework Require Import FrameworkUtil.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext.
Import List.ListNotations Cost.Notations.

Module PreFamily.

Local Open Scope nat_scope.

Definition in_family {B BE N E V K G C U} (c : Pre.ctx B BE N E V K G C U) :=
  Pre.family c.

(** A unary list is counted directly into a binary accumulator without a unary numeric cast. *)
Definition count_c {X} (xs : list X) :=
  fold_left_c (fun n (_ : X) => Cost.ret (N.succ n)) xs 0%N.
Definition count {X} (xs : list X) := Cost.value (count_c xs).

(** Counting a list returns its length as a binary natural. *)
Theorem count_value {X} (xs : list X) :
  count xs = N.of_nat (length xs).
Proof.
  unfold count, count_c; rewrite value_fold_left_c.
  assert (Hacc : forall ys : list X, forall n,
    fold_left (fun n (_ : X) => N.succ n) ys n = (n + N.of_nat (length ys))%N).
  { induction ys as [|x ys IH]; intro n; cbn [fold_left length].
    - lia.
    - rewrite IH, Nat2N.inj_succ; lia. }
  rewrite Hacc; lia.
Qed.

(** Every counted occurrence consumes one traversal tick. *)
Theorem count_cost {X} (xs : list X) :
  Cost.ticks (count_c xs) = N.of_nat (length xs).
Proof.
  unfold count_c.
  assert (Hacc : forall ys : list X, forall n,
    Cost.ticks (fold_left_c (fun n (_ : X) => Cost.ret (N.succ n)) ys n) =
      N.of_nat (length ys)).
  { induction ys as [|x ys IH]; intro n.
    - rewrite ticks_fold_left_c_nil; reflexivity.
    - rewrite ticks_fold_left_c_cons, Cost.ticks_ret, Cost.value_ret, IH.
      cbn [length]; rewrite Nat2N.inj_succ; lia. }
  apply Hacc.
Qed.

(** A binary arithmetic operand pays for all of its stored bits. *)
Definition bits_c n :=
  match n with
  | N0 => Cost.step
  | Npos p => Cost.tick_bits p
  end.

Definition binary_width n :=
  match n with
  | N0 => 1%N
  | Npos p => N.pos (Pos.size p)
  end.

(** Binary operands pay one tick per stored bit, including the representation of zero. *)
Theorem bits_cost n : Cost.ticks (bits_c n) = binary_width n.
Proof.
  destruct n; [reflexivity|apply Cost.ticks_tick_bits].
Qed.

(** Multiplication visits both bit streams at their schoolbook product bound. *)
Fixpoint product_bits_c (a : N) (b : positive) : Cost.t unit :=
  bits_c a ;;
  match b with
  | xH => Cost.ret tt
  | xO q => product_bits_c a q
  | xI q => product_bits_c a q
  end.

(** Schoolbook multiplication retains the product of the two operand bit widths. *)
Theorem product_bits_cost a b :
  Cost.ticks (product_bits_c a b) = (binary_width a * N.pos (Pos.size b))%N.
Proof.
  induction b as [b IH|b IH|]; cbn [product_bits_c];
    autorewrite with galois_cost; rewrite bits_cost.
  - rewrite IH; change (N.pos (Pos.size (xI b))) with (N.succ (N.pos (Pos.size b))); nia.
  - rewrite IH; change (N.pos (Pos.size (xO b))) with (N.succ (N.pos (Pos.size b))); nia.
  - cbn [Pos.size]; nia.
Qed.

Definition add_c a b :=
  bits_c a ;; bits_c b ;; Cost.ret (a + b)%N.
Definition multiply_c a b :=
  match b with
  | N0 => Cost.step ;; Cost.ret 0%N
  | Npos p => product_bits_c a p ;; Cost.ret (a * b)%N
  end.

Definition power_c {X} n (arity : list X) :=
  fold_left_c (fun p _ => multiply_c p n) arity 1%N.

(** Charged addition returns the ordinary binary sum. *)
Theorem add_value a b : Cost.value (add_c a b) = (a + b)%N.
Proof.
  unfold add_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Bound addition charges both binary operands before constructing the sum. *)
Theorem add_cost a b :
  Cost.ticks (add_c a b) = (binary_width a + binary_width b)%N.
Proof.
  unfold add_c; autorewrite with galois_cost; rewrite !bits_cost; lia.
Qed.

(** Bound multiplication charges its zero case or both operands' schoolbook bit work. *)
Theorem multiply_cost a b :
  Cost.ticks (multiply_c a b) =
    match b with
    | N0 => 1%N
    | Npos p => (binary_width a * N.pos (Pos.size p))%N
    end.
Proof.
  destruct b; unfold multiply_c; autorewrite with galois_cost;
    [reflexivity|rewrite product_bits_cost; lia].
Qed.

(** Charged multiplication returns the ordinary binary product. *)
Theorem multiply_value a b : Cost.value (multiply_c a b) = (a * b)%N.
Proof.
  unfold multiply_c; destruct b; autorewrite with galois_cost; [lia|reflexivity].
Qed.

(** Structural exponentiation visits the operand list without constructing operand tuples. *)
Theorem power_value {X} n (xs : list X) :
  Cost.value (power_c n xs) = N.pow n (N.of_nat (length xs)).
Proof.
  unfold power_c; rewrite value_fold_left_c.
  assert (Hacc : forall ys : list X, forall p,
    fold_left (fun acc (_ : X) => Cost.value (multiply_c acc n)) ys p =
      (p * N.pow n (N.of_nat (length ys)))%N).
  { induction ys as [|x ys IH]; intro p; cbn [fold_left length].
    - rewrite N.pow_0_r; lia.
    - rewrite multiply_value, IH, Nat2N.inj_succ, N.pow_succ_r'; nia. }
  rewrite Hacc; lia.
Qed.

Section Family.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition family_bound_c :=
  let* n := count_c (Pre.values (Pre.input c)) in
  fold_right_c (fun seed total =>
    Cost.step ;;
    let* operands := Pre.operands_c (Pre.input c) seed in
    let* choices := power_c n operands in
    add_c choices total) 0%N (Pre.seeds (Pre.input c)).
Definition family_bound := Cost.value family_bound_c.

(** The executable bound counts signatures using binary arithmetic and charged readers. *)
Theorem family_bound_equation :
  family_bound =
    fold_right (fun u total =>
      (N.pow (N.of_nat (length (Pre.values (Pre.input c))))
        (N.of_nat (length (Pre.operands c u))) + total)%N)
      0%N (Pre.seeds (Pre.input c)).
Proof.
  unfold family_bound, family_bound_c; rewrite Cost.value_bind.
  fold (count (Pre.values (Pre.input c))); rewrite count_value, value_fold_right_c.
  induction (Pre.seeds (Pre.input c)) as [|u rest IH]; [reflexivity|].
  cbn [fold_right]; rewrite !Cost.value_bind, add_value, power_value, IH; reflexivity.
Qed.

Fixpoint translated_c bes u : Cost.t (list U) :=
  match bes with
  | [] => Cost.ret []
  | be :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* value := Pre.translate_c (Pre.input c) be u in
    let* tail := translated_c rest u in
    Cost.ret (match value with None => tail | Some v => v :: tail end)
  end.
Definition translated bes u := Cost.value (translated_c bes u).

(** Translation preserves ordered edge occurrences, including duplicate translated expressions. *)
Theorem translated_equation bes u :
  translated bes u = flat_map (fun be =>
    match Pre.translate c be u with None => [] | Some v => [v] end) bes.
Proof.
  unfold translated; induction bes as [|be rest IH]; [reflexivity|].
  cbn [translated_c flat_map]; autorewrite with galois_cost; rewrite IH.
  fold (Pre.translate c be u); destruct (Pre.translate c be u); reflexivity.
Qed.

(** Every translated arrival has a witness at its original incoming edge occurrence. *)
Theorem translated_member bes u :
  forall v, In v (translated bes u) <->
    exists be, In be bes /\ Pre.translate c be u = Some v.
Proof.
  rewrite translated_equation; intro v; rewrite in_flat_map; split.
  - intros [be [Hbe Hv]]; destruct (Pre.translate c be u) as [w|] eqn:Htranslate;
      [|contradiction].
    destruct Hv as [<-|[]]; exists be; auto.
  - intros [be [Hbe Htranslate]]; exists be; split; [exact Hbe|].
    rewrite Htranslate; now left.
Qed.

(** Translation emits at most one arrival for each ordered incoming edge occurrence. *)
Theorem translated_length bes u :
  length (translated bes u) <= length bes.
Proof.
  induction bes as [|be rest IH]; [reflexivity|].
  rewrite translated_equation in IH |- *.
  cbn [flat_map]; rewrite length_app.
  destruct (Pre.translate c be u); cbn [length]; lia.
Qed.

(** Successful client translation agrees with simultaneous environment substitution. *)
Theorem translation_agrees :
  Pre.laws c ->
  forall be u v env, In be (Cfg.edges (Pre.block_cfg c)) ->
    in_family c u -> Pre.translate c be u = Some v ->
    Pre.eval (Pre.input c) u (Pre.phi_env c be env) = Pre.eval (Pre.input c) v env.
Proof.
  intro Hlaw; exact (Pre.translation_eval c (Pre.runtime c Hlaw)).
Qed.

(* Tuple enumeration appears in proofs alone. The executable bound uses power_c. *)
Fixpoint operand_tuples {X} (values : list X) (arity : nat) : list (list X) :=
  match arity with
  | O => [[]]
  | S n => flat_map (fun x => map (cons x) (operand_tuples values n)) values
  end.

Local Lemma operand_tuples_exact {X} (values xs : list X) :
  In xs (operand_tuples values (length xs)) <-> incl xs values.
Proof.
  induction xs as [|x xs IH]; cbn [operand_tuples length].
  - split; [intros _ y Hfalse; contradiction|intros _; now left].
  - rewrite in_flat_map; split.
    + intros [v [Hv Hmap]]; apply in_map_iff in Hmap.
      destruct Hmap as [ys [Heq Hys]]; inversion Heq; subst v ys.
      intros y [<-|Hy]; [exact Hv|exact (proj1 IH Hys y Hy)].
    + intro Hsub; exists x; split; [apply Hsub; now left|].
      apply in_map_iff; exists xs; split; [reflexivity|].
      apply IH; intros y Hy; apply Hsub; now right.
Qed.

Local Lemma operand_tuples_length {X} (values : list X) arity :
  length (operand_tuples values arity) = Nat.pow (length values) arity.
Proof.
  induction arity as [|arity IH]; [reflexivity|].
  cbn [operand_tuples Nat.pow].
  assert (Hcount : forall vs : list X,
    length (flat_map (fun x => map (cons x) (operand_tuples values arity)) vs) =
      length vs * length (operand_tuples values arity)).
  { intro vs; induction vs as [|x vs IHvs]; cbn [flat_map length]; [reflexivity|].
    rewrite length_app, length_map, IHvs; lia. }
  rewrite Hcount, IH; reflexivity.
Qed.

Definition signatures :=
  flat_map (fun seed => map (fun xs => (Pre.shape c seed, xs))
    (operand_tuples (Pre.values (Pre.input c)) (length (Pre.operands c seed))))
    (Pre.seeds (Pre.input c)).

Local Lemma family_seed_shape :
  Pre.laws c ->
  forall u, in_family c u ->
    exists seed, In seed (Pre.seeds (Pre.input c)) /\
      Pre.shape c u = Pre.shape c seed /\
      length (Pre.operands c u) = length (Pre.operands c seed).
Proof.
  intros Hlaw u [seed [Hseed Hpath]].
  assert (Hinvariant : forall v, Rel.star (Pre.family_step c) seed v ->
    Pre.family c v /\ Pre.shape c v = Pre.shape c seed /\
      length (Pre.operands c v) = length (Pre.operands c seed)).
  { intros v Hv.
    eapply (Rel.star_invariant (Pre.family_step c)
      (fun v => Pre.family c v /\ Pre.shape c v = Pre.shape c seed /\
        length (Pre.operands c v) = length (Pre.operands c seed))).
    - intros x y [Hx [Hshape Harity]] [be [Hbe Htranslate]].
      assert (Hy : Pre.family c y) by (eapply Pre.family_translate; eassumption).
      pose proof (Pre.translation_shape c (Pre.shapes c Hlaw) be x y Hx Htranslate)
        as Hstep.
      split; [exact Hy|]; split; [congruence|].
      rewrite (Pre.shape_arity c (Pre.shapes c Hlaw) y x Hy Hx Hstep); exact Harity.
    - exact Hv.
    - split; [apply Pre.family_seed; exact Hseed|auto]. }
  exists seed; split; [exact Hseed|exact (proj2 (Hinvariant u Hpath))].
Qed.

Local Lemma family_signature :
  Pre.laws c ->
  forall u, in_family c u -> In (Pre.shape c u, Pre.operands c u) signatures.
Proof.
  intros Hlaw u Hu.
  destruct (family_seed_shape Hlaw u Hu) as [seed [Hseed [Hshape Harity]]].
  unfold signatures; apply in_flat_map; exists seed; split; [exact Hseed|].
  apply in_map_iff; exists (Pre.operands c u); split; [congruence|].
  rewrite <- Harity; apply operand_tuples_exact.
  exact (Pre.finite_operands c (Pre.shapes c Hlaw) u Hu).
Qed.

Local Lemma signatures_length :
  N.of_nat (length signatures) = family_bound.
Proof.
  rewrite family_bound_equation; unfold signatures.
  induction (Pre.seeds (Pre.input c)) as [|seed rest IH]; [reflexivity|].
  cbn [flat_map fold_right]; rewrite length_app, length_map, operand_tuples_length.
  rewrite Nat2N.inj_add, Nat2N.inj_pow, IH; reflexivity.
Qed.

(** Any duplicate-free list of family members fits the computed signature bound. *)
Theorem family_cardinal :
  Pre.laws c ->
  forall xs, NoDup xs -> Forall (in_family c) xs ->
    (N.of_nat (length xs) <= family_bound)%N.
Proof.
  intros Hlaw xs Hnodup Hfamily.
  set (signature := fun u => (Pre.shape c u, Pre.operands c u)).
  assert (Hinject : forall u v, In u xs -> In v xs -> signature u = signature v -> u = v).
  { intros u v Hu Hv Heq; inversion Heq as [[Hshape Hoperands]].
    apply (Pre.shape_identity c (Pre.shapes c Hlaw) u v).
    - exact (proj1 (Forall_forall _ _) Hfamily u Hu).
    - exact (proj1 (Forall_forall _ _) Hfamily v Hv).
    - exact Hshape.
    - exact Hoperands. }
  assert (Hmap : NoDup (map signature xs)).
  { clear Hfamily; induction Hnodup as [|u xs Hfresh Hnodup IH]; [constructor|].
    cbn [map]; constructor.
    - intro Hin; apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; apply Hfresh.
      assert (u = v) by
        (apply Hinject; [now left|now right|symmetry; exact Heq]).
      subst u; exact Hv.
    - apply IH; intros a b Ha Hb; apply Hinject; now right. }
  rewrite <- signatures_length.
  apply (proj1 (N.compare_le_iff _ _)); rewrite <- Nat2N.inj_compare.
  apply (proj2 (Nat.compare_le_iff _ _)).
  rewrite <- (length_map signature xs).
  apply NoDup_incl_length; [exact Hmap|].
  intros pair Hin; apply in_map_iff in Hin; destruct Hin as [u [<- Hu]].
  apply family_signature; [exact Hlaw|exact (proj1 (Forall_forall _ _) Hfamily u Hu)].
Qed.

End Family.

(** A discovery engine shares one key dictionary and one charged successor callback. *)
Record engine (X : Type) := Engine {
  key : encoding X;
  next_c : X -> Cost.t (list X)
}.
Arguments Engine {X}.
Arguments key {X}.
Arguments next_c {X}.

Definition state X := (list X * FinSet.t X)%type.

Section Worklist.
Context {X : Type}.
Variable m : engine X.

Definition next x := Cost.value (next_c m x).

Definition step_c (work : state X) : Cost.t (state X + state X) :=
  match work with
  | ([], _) => Cost.ret (inr work)
  | (x :: rest, seen) =>
    let* known := FinSet.mem_c (key m) x seen in
    if known then Cost.ret (inl (rest, seen)) else
      Cost.step ;;
      let* fresh := next_c m x in
      let* pending := app_c fresh rest in
      let* seen := FinSet.add_c (key m) x seen in
      Cost.ret (inl (pending, seen))
  end.

Definition step (work : state X) :=
  match work with
  | ([], _) => inr work
  | (x :: rest, seen) =>
    if FinSet.mem (key m) x seen then inl (rest, seen)
    else inl (next x ++ rest, FinSet.add (key m) x seen)
  end.

(** One pop tests memo membership and translates only a previously unseen expression. *)
Theorem step_value work : Cost.value (step_c work) = step work.
Proof.
  destruct work as [[|x rest] seen]; [reflexivity|].
  unfold step_c, step; rewrite Cost.value_bind.
  fold (FinSet.mem (key m) x seen); destruct (FinSet.mem (key m) x seen);
    autorewrite with galois_cost; rewrite ?value_app_c; reflexivity.
Qed.

Definition result_state (r : state X + state X) :=
  match r with
  | inl work => work
  | inr work => work
  end.

Definition valid (P : X -> Prop) (work : state X) : Prop :=
  FinSet.wf (key m) (snd work) /\
  Forall P (FinSet.elements (snd work)) /\ Forall P (fst work).

Definition available (work : state X) x : Prop :=
  FinSet.mem (key m) x (snd work) = true \/ In x (fst work).

Definition covers seeds (work : state X) : Prop :=
  (forall x, In x seeds -> available work x) /\
  (forall x y, FinSet.mem (key m) x (snd work) = true -> In y (next x) ->
    available work y).

Variable HE : encoding_laws (key m).
Context {P : X -> Prop}.

Local Lemma added_valid x rest seen :
  (forall a b, P a -> In b (next a) -> P b) ->
  valid P (x :: rest, seen) ->
  valid P (next x ++ rest, FinSet.add (key m) x seen).
Proof.
  intros Hnext [Hwf [Hseen Hpending]].
  pose proof (Forall_inv Hpending) as Hx.
  pose proof (Forall_inv_tail Hpending) as Hrest.
  assert (Hnewwf : FinSet.wf (key m) (FinSet.add (key m) x seen)) by
    (apply FinSet.wf_add; exact Hwf).
  split; [exact Hnewwf|]; split.
  - apply Forall_forall; intros y Hy.
    apply (FinSet.elements_spec (key m) HE) in Hy; [|exact Hnewwf].
    cbn [snd] in Hy.
    rewrite FinSet.mem_add in Hy by exact Hwf.
    apply Bool.orb_true_iff in Hy; destruct Hy as [Hsame|Hy].
    + apply (eqb_true_iff _ HE) in Hsame; subst y; exact Hx.
    + apply (proj1 (Forall_forall _ _) Hseen y).
      apply (FinSet.elements_spec (key m) HE); assumption.
  - apply Forall_app; split; [|exact Hrest].
    apply Forall_forall; intros y Hy; eapply Hnext; eassumption.
Qed.

Local Lemma valid_step work :
  (forall a b, P a -> In b (next a) -> P b) ->
  valid P work -> valid P (result_state (step work)).
Proof.
  intros Hnext Hvalid; destruct work as [[|x rest] seen]; [exact Hvalid|].
  cbn [step result_state]; destruct (FinSet.mem (key m) x seen).
  - destruct Hvalid as [Hwf [Hseen Hpending]].
    split; [exact Hwf|]; split; [exact Hseen|exact (Forall_inv_tail Hpending)].
  - apply added_valid; assumption.
Qed.

Local Lemma available_step work :
  FinSet.wf (key m) (snd work) ->
  forall x, available work x -> available (result_state (step work)) x.
Proof.
  destruct work as [[|y rest] seen]; [intros _ x H; exact H|].
  intro Hwf.
  unfold available, step; cbn [fst snd].
  destruct (FinSet.mem (key m) y seen) eqn:Hseen; cbn [result_state fst snd].
  - intros x [Hmem|[<-|Hin]]; [now left|now left|now right].
  - intros x [Hmem|[<-|Hin]].
    + left; rewrite FinSet.mem_add by exact Hwf.
      rewrite Hmem, Bool.orb_true_r; reflexivity.
    + left; rewrite FinSet.mem_add by exact Hwf.
      rewrite eqb_refl; reflexivity.
    + right; apply in_or_app; now right.
Qed.

Local Lemma covers_step seeds work :
  FinSet.wf (key m) (snd work) ->
  covers seeds work -> covers seeds (result_state (step work)).
Proof.
  intros Hwf [Hseeds Hclosure]; split.
  - intros x Hin; apply available_step; [exact Hwf|apply Hseeds; exact Hin].
  - destruct work as [[|x rest] seen]; [exact Hclosure|].
    cbn [step]; destruct (FinSet.mem (key m) x seen) eqn:Hseen.
    + intros y z Hy Hz.
      pose proof (available_step (x :: rest, seen) Hwf z (Hclosure y z Hy Hz)) as Hkeep.
      cbn [step] in Hkeep; rewrite Hseen in Hkeep; exact Hkeep.
    + cbn [result_state snd]; intros y z Hy Hz.
      rewrite FinSet.mem_add in Hy by exact Hwf.
      apply Bool.orb_true_iff in Hy; destruct Hy as [Heq|Hy].
      * apply (eqb_true_iff _ HE) in Heq; subst y.
        right; apply in_or_app; now left.
      * pose proof (available_step (x :: rest, seen) Hwf z (Hclosure y z Hy Hz)) as Hkeep.
        cbn [step] in Hkeep; rewrite Hseen in Hkeep; exact Hkeep.
Qed.

(** The memo table stays canonical and every queued expression stays in the family. *)
Lemma run_valid {budget work result} :
  (forall a b, P a -> In b (next a) -> P b) ->
  valid P work -> runs step_c budget work result -> valid P (result_state result).
Proof.
  intros Hnext Hvalid Hrun; revert Hvalid.
  induction Hrun as [work|budget work result Hstop|
    budget work mid result Hstep Hrun IH]; intro Hvalid.
  - exact Hvalid.
  - rewrite step_value in Hstop.
    pose proof (valid_step work Hnext Hvalid) as Hkeep; rewrite Hstop in Hkeep; exact Hkeep.
  - apply IH.
    rewrite step_value in Hstep.
    pose proof (valid_step work Hnext Hvalid) as Hkeep; rewrite Hstep in Hkeep; exact Hkeep.
Qed.

Local Lemma run_covers seeds {budget work result} :
  (forall a b, P a -> In b (next a) -> P b) ->
  valid P work -> covers seeds work ->
  runs step_c budget work result -> covers seeds (result_state result).
Proof.
  intros Hnext Hvalid Hcovers Hrun; revert Hvalid Hcovers.
  induction Hrun as [work|budget work result Hstop|
    budget work mid result Hstep Hrun IH]; intros Hvalid Hcovers.
  - exact Hcovers.
  - rewrite step_value in Hstop.
    pose proof (covers_step seeds work (proj1 Hvalid) Hcovers) as Hkeep.
    rewrite Hstop in Hkeep; exact Hkeep.
  - rewrite step_value in Hstep; apply IH.
    + pose proof (valid_step work Hnext Hvalid) as Hkeep.
      rewrite Hstep in Hkeep; exact Hkeep.
    + pose proof (covers_step seeds work (proj1 Hvalid) Hcovers) as Hkeep.
      rewrite Hstep in Hkeep; exact Hkeep.
Qed.

Local Lemma size_empty :
  FinSet.size (@FinSet.empty X) = 0.
Proof.
  rewrite FinSet.size_elements.
  destruct (FinSet.elements (@FinSet.empty X)) as [|x rest] eqn:Helements; [reflexivity|].
  assert (Hmember : FinSet.mem (key m) x (@FinSet.empty X) = true).
  { apply (FinSet.elements_spec _ HE); [apply FinSet.wf_empty|rewrite Helements; now left]. }
  rewrite FinSet.mem_empty in Hmember; discriminate.
Qed.

Local Lemma size_add x seen :
  FinSet.wf (key m) seen -> FinSet.mem (key m) x seen = false ->
    FinSet.size (FinSet.add (key m) x seen) = S (FinSet.size seen).
Proof.
  intros Hwf Hfresh; rewrite !FinSet.size_elements.
  assert (Hnewwf : FinSet.wf (key m) (FinSet.add (key m) x seen)) by
    (apply FinSet.wf_add; exact Hwf).
  change (length (FinSet.elements (FinSet.add (key m) x seen)) =
    length (x :: FinSet.elements seen)).
  apply Permutation_length.
  apply NoDup_Permutation.
  - apply (FinSet.elements_nodup (key m)); exact Hnewwf.
  - constructor.
    + intro Hin; apply (FinSet.elements_spec _ HE) in Hin; [congruence|exact Hwf].
    + apply (FinSet.elements_nodup (key m)); exact Hwf.
  - intro y; rewrite (FinSet.elements_spec _ HE) by exact Hnewwf.
    rewrite FinSet.mem_add by exact Hwf.
    rewrite Bool.orb_true_iff, (eqb_true_iff _ HE).
    cbn [In]; rewrite (FinSet.elements_spec _ HE) by exact Hwf; intuition congruence.
Qed.

Definition potential capacity degree (work : state X) :=
  ((capacity - FinSet.size (snd work)) * (degree + 1) + length (fst work))%nat.

Local Lemma potential_decreases capacity degree work :
  (forall xs, NoDup xs -> Forall P xs -> length xs <= capacity) ->
  (forall x, length (next x) <= degree) ->
  (forall a b, P a -> In b (next a) -> P b) ->
  valid P work ->
  forall mid, step work = inl mid ->
    potential capacity degree mid < potential capacity degree work.
Proof.
  intros Hcard Hdegree Hnext Hvalid mid Hstep.
  destruct work as [[|x rest] seen]; [discriminate|].
  cbn [step] in Hstep; destruct (FinSet.mem (key m) x seen) eqn:Hmem;
    inversion Hstep; subst mid.
  - unfold potential; cbn [fst snd length]; lia.
  - pose proof (added_valid x rest seen Hnext Hvalid) as [Hnewwf [Hnew _]].
    assert (Hbound : FinSet.size (FinSet.add (key m) x seen) <= capacity).
    { rewrite FinSet.size_elements; apply Hcard; [apply (FinSet.elements_nodup (key m))|];
        assumption. }
    rewrite (size_add x seen (proj1 Hvalid) Hmem) in Hbound.
    unfold potential; cbn [fst snd].
    rewrite (size_add x seen (proj1 Hvalid) Hmem), length_app.
    pose proof (Hdegree x); cbn [length]; nia.
Qed.

(** Exhaustion consumes distinct units of a decreasing family/worklist potential. *)
Lemma run_exhaustion_bound capacity degree :
  (forall xs, NoDup xs -> Forall P xs -> length xs <= capacity) ->
  (forall x, length (next x) <= degree) ->
  (forall a b, P a -> In b (next a) -> P b) ->
  forall budget work final, valid P work ->
    runs step_c budget work (inl final) ->
    potential capacity degree final + budget <= potential capacity degree work.
Proof.
  intros Hcard Hdegree Hnext budget work final Hvalid Hrun.
  remember (inl final) as result eqn:Hresult; revert final Hvalid Hresult.
  induction Hrun as [work|budget work result Hstop|
    budget work mid result Hstep Hrun IH]; intros final Hvalid Hresult.
  - inversion Hresult; subst; lia.
  - discriminate.
  - assert (Hmid : valid P mid).
    { rewrite step_value in Hstep.
      pose proof (valid_step work Hnext Hvalid) as Hkeep.
      rewrite Hstep in Hkeep; exact Hkeep. }
    specialize (IH final Hmid Hresult).
    rewrite step_value in Hstep.
    pose proof (potential_decreases capacity degree work Hcard Hdegree Hnext Hvalid mid Hstep).
    lia.
Qed.

(** A successful discovery result has no unprocessed arrivals. *)
Lemma run_stopped_empty {budget work final} :
  runs step_c budget work (inr final) -> fst final = [].
Proof.
  intro Hrun.
  destruct (runs_inr_stop step_c _ _ _ Hrun) as [used [last [_ [_ Hstop]]]].
  rewrite step_value in Hstop; destruct last as [[|x rest] seen]; cbn [step] in Hstop.
  - inversion Hstop; reflexivity.
  - destruct (FinSet.mem (key m) x seen); discriminate.
Qed.

Definition credit capacity degree a t (work : state X) : N :=
  (N.of_nat (capacity - FinSet.size (snd work)) *
      (a + t + 1 + N.of_nat degree * (a + 3)) +
    N.of_nat (length (fst work)) * (a + 2))%N.

Local Lemma credit_step {capacity degree a t work} :
  (forall xs, NoDup xs -> Forall P xs -> length xs <= capacity) ->
  (forall x, P x ->
    (1 + Cost.ticks (encode_c (key m) x) + key_bits (key m) x <= a)%N /\
    (Cost.ticks (next_c m x) <= t)%N /\ length (next x) <= degree) ->
  (forall x y, P x -> In y (next x) -> P y) ->
  valid P work ->
  match Cost.value (step_c work) with
  | inl mid => valid P mid /\
      (Cost.ticks (step_c work) + credit capacity degree a t mid + 2 <=
        credit capacity degree a t work)%N
  | inr _ => (Cost.ticks (step_c work) <= credit capacity degree a t work)%N
  end.
Proof.
  intros Hcard Hbounds Hnext Hvalid.
  rewrite step_value.
  destruct work as [[|x rest] seen];
    [cbn [step_c]; rewrite Cost.ticks_ret; apply N.le_0_l|].
  pose proof (Forall_inv (proj2 (proj2 Hvalid))) as Hx.
  destruct (Hbounds x Hx) as [Hkey [Hnextcost Hlength]].
  cbn [step]; destruct (FinSet.mem (key m) x seen) eqn:Hmem.
  - split.
    + pose proof (valid_step (x :: rest, seen) Hnext Hvalid) as Hkeep.
      cbn [step] in Hkeep; rewrite Hmem in Hkeep; exact Hkeep.
    + unfold step_c; rewrite Cost.ticks_bind; fold (FinSet.mem (key m) x seen).
      rewrite Hmem, Cost.ticks_ret, FinSet.mem_cost.
      unfold credit; cbn [fst snd length]; rewrite Nat2N.inj_succ.
      unfold key_bits in Hkey; nia.
  - pose proof (added_valid x rest seen Hnext Hvalid) as Hnew.
    split; [exact Hnew|].
    assert (Hcap : FinSet.size (FinSet.add (key m) x seen) <= capacity).
    { rewrite FinSet.size_elements; apply Hcard.
      - apply (FinSet.elements_nodup (key m)); exact (proj1 Hnew).
      - exact (proj1 (proj2 Hnew)). }
    pose proof (size_add x seen (proj1 Hvalid) Hmem) as Hsize.
    unfold step_c; rewrite Cost.ticks_bind; fold (FinSet.mem (key m) x seen).
    rewrite Hmem; autorewrite with galois_cost.
    rewrite FinSet.add_cost, FinSet.mem_cost.
    fold (next x).
    unfold credit; cbn [fst snd]; rewrite Hsize, length_app.
    cbn [length]; rewrite !Nat2N.inj_add, !Nat2N.inj_sub.
    rewrite ?Nat2N.inj_succ.
    assert (HcapN : (N.of_nat (S (FinSet.size seen)) <= N.of_nat capacity)%N) by lia.
    rewrite Nat2N.inj_succ in HcapN.
    assert (HlengthN : (N.of_nat (length (next x)) <= N.of_nat degree)%N) by lia.
    unfold key_bits in Hkey; nia.
Qed.

End Worklist.

Section Discovery.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition engine_for bes :=
  Engine (Pre.eu (Pre.keys c)) (translated_c c bes).

Definition setup_c :=
  let* bes := fw_edges_c (Pre.block_cfg c) in
  let* roots := count_c (Pre.seeds (Pre.input c)) in
  let* degree := count_c bes in
  let* capacity := family_bound_c c in
  let* one_more := add_c 1%N degree in
  let* credit := multiply_c capacity one_more in
  let* bound := add_c roots credit in
  bits_c bound ;;
  Cost.ret (bes, N.succ_pos bound).

Definition setup := Cost.value setup_c.

(** Setup retains all edge occurrences and builds the adequate positive budget in binary. *)
Theorem setup_equation :
  setup =
    (Cfg.edges (Pre.block_cfg c),
      N.succ_pos (N.of_nat (length (Pre.seeds (Pre.input c))) +
        family_bound c * (1 + N.of_nat (length (Cfg.edges (Pre.block_cfg c)))))%N).
Proof.
  unfold setup, setup_c; rewrite Cost.value_bind, fw_edges_value.
  rewrite Cost.value_bind; fold (count (Pre.seeds (Pre.input c))); rewrite count_value.
  rewrite Cost.value_bind; fold (count (Cfg.edges (Pre.block_cfg c))); rewrite count_value.
  rewrite Cost.value_bind; fold (family_bound c).
  unfold add_c; autorewrite with galois_cost; rewrite multiply_value; reflexivity.
Qed.

Definition discover_state_c :=
  let* config := setup_c in
  iterate (step_c (engine_for (fst config))) (snd config)
    (Pre.seeds (Pre.input c), FinSet.empty).

Definition discover_c : Cost.t (list U + list U) :=
  let* result := discover_state_c in
  match result with
  | inl work => Cost.map (@inl (list U) (list U)) (FinSet.elements_c (snd work))
  | inr work => Cost.map (@inr (list U) (list U)) (FinSet.elements_c (snd work))
  end.

Definition discover := Cost.value discover_c.

(** Raw discovery exposes exhaustion and its partial memoized family as a separate outcome. *)
Definition universe :=
  match discover with
  | inl partial => partial
  | inr complete => complete
  end.

Local Lemma universe_state :
  universe = FinSet.elements (snd (result_state (Cost.value discover_state_c))).
Proof.
  unfold universe, discover, discover_c; rewrite Cost.value_bind.
  destruct (Cost.value discover_state_c); rewrite Cost.value_map; reflexivity.
Qed.

Local Lemma discovery_run :
  let config := setup in
  runs (step_c (engine_for (fst config))) (Pos.to_nat (snd config))
    (Pre.seeds (Pre.input c), FinSet.empty) (Cost.value discover_state_c).
Proof.
  unfold discover_state_c; rewrite Cost.value_bind; apply iterate_value.
Qed.

Local Lemma discovery_parameters bes :
  Pre.laws c -> incl bes (Cfg.edges (Pre.block_cfg c)) ->
  (forall u v, in_family c u -> In v (next (engine_for bes) u) -> in_family c v) /\
  (forall xs, NoDup xs -> Forall (in_family c) xs ->
    length xs <= N.to_nat (family_bound c)) /\
  valid (engine_for bes) (in_family c) (Pre.seeds (Pre.input c), FinSet.empty).
Proof.
  intros Hlaw Hbes; split.
  - intros u v Hu Hv; apply (translated_member c bes u) in Hv.
    destruct Hv as [be [Hbe Htranslate]].
    eapply Pre.family_translate; [exact Hu|apply Hbes; exact Hbe|exact Htranslate].
  - split.
    + intros xs Hnodup Hfamily.
      pose proof (family_cardinal c Hlaw xs Hnodup Hfamily) as Hbound.
      lia.
    + split; [apply FinSet.wf_empty|]; split; apply Forall_forall.
      * intros u Hu; apply (FinSet.elements_spec _ (Pre.eu_laws c (Pre.graphs c Hlaw)))
          in Hu; [cbn [snd] in Hu; rewrite FinSet.mem_empty in Hu; discriminate|
          apply FinSet.wf_empty].
      * intros u Hu; apply Pre.family_seed; exact Hu.
Qed.

Local Lemma positive_budget n :
  Pos.to_nat (N.succ_pos n) = S (N.to_nat n).
Proof.
  destruct n as [|p]; [reflexivity|]; cbn; rewrite Pos2Nat.inj_succ; reflexivity.
Qed.

(** The shape/operand capacity pays every pop and leaves budget for the stopping callback. *)
Theorem discover_adequate :
  Pre.laws c -> exists final, Cost.value discover_state_c = inr final.
Proof.
  intro Hlaw.
  pose proof discovery_run as Hrun; rewrite setup_equation in Hrun; cbn [fst snd] in Hrun.
  set (bes := Cfg.edges (Pre.block_cfg c)) in *.
  destruct (discovery_parameters bes Hlaw (fun _ H => H)) as [Hnext [Hcard Hvalid]].
  destruct (Cost.value discover_state_c) as [final|final] eqn:Hresult; [|now exists final].
  pose proof (run_exhaustion_bound (engine_for bes)
    (Pre.eu_laws c (Pre.graphs c Hlaw)) (N.to_nat (family_bound c)) (length bes)
    Hcard (translated_length c bes) Hnext _ _ _ Hvalid Hrun) as Hbound.
  rewrite positive_budget in Hbound.
  unfold potential in Hbound; cbn [fst snd] in Hbound.
  pose proof (size_empty (engine_for bes) (Pre.eu_laws c (Pre.graphs c Hlaw))) as HemptySize.
  rewrite ?HemptySize in Hbound.
  rewrite N2Nat.inj_add, N2Nat.inj_mul, N2Nat.inj_add, !Nat2N.id in Hbound.
  change (N.to_nat 1%N) with 1 in Hbound; nia.
Qed.

Local Lemma discovered_valid :
  Pre.laws c ->
  valid (engine_for (Cfg.edges (Pre.block_cfg c))) (in_family c)
    (result_state (Cost.value discover_state_c)).
Proof.
  intro Hlaw.
  destruct (discovery_parameters (Cfg.edges (Pre.block_cfg c)) Hlaw (fun _ H => H))
    as [Hnext [_ Hvalid]].
  eapply run_valid; [exact (Pre.eu_laws c (Pre.graphs c Hlaw))|exact Hnext|exact Hvalid|].
  pose proof discovery_run as Hrun; rewrite setup_equation in Hrun; exact Hrun.
Qed.

(** Discovery returns exactly the least translation family and enumerates every member once. *)
Theorem universe_exact :
  Pre.laws c ->
  NoDup universe /\ forall u, In u universe <-> in_family c u.
Proof.
  intro Hlaw.
  set (bes := Cfg.edges (Pre.block_cfg c)).
  set (m := engine_for bes).
  pose proof (Pre.eu_laws c (Pre.graphs c Hlaw)) as HE.
  destruct (discovery_parameters bes Hlaw (fun _ H => H)) as [Hnext [_ Hinitial]].
  destruct (discover_adequate Hlaw) as [final Hfinal].
  pose proof discovery_run as Hrun; rewrite setup_equation in Hrun.
  rewrite Hfinal in Hrun; cbn [fst snd] in Hrun.
  pose proof (run_stopped_empty m Hrun) as Hempty.
  pose proof (discovered_valid Hlaw) as Hvalid; rewrite Hfinal in Hvalid.
  cbn [result_state] in Hvalid.
  destruct Hvalid as [Hwf [Hfamily Hpending]].
  assert (Hinitial_covers : covers m (Pre.seeds (Pre.input c))
    (Pre.seeds (Pre.input c), FinSet.empty)).
  { split; [intros u Hu; now right|].
    intros u v Hfalse; cbn [snd] in Hfalse.
    rewrite FinSet.mem_empty in Hfalse; discriminate. }
  pose proof (run_covers m HE (Pre.seeds (Pre.input c)) Hnext Hinitial
    Hinitial_covers Hrun) as [Hseeds Hclosed].
  assert (Havailable : forall u, available m final u -> FinSet.mem (key m) u (snd final) = true).
  { intros u [Hu|Hu]; [exact Hu|rewrite Hempty in Hu; contradiction]. }
  assert (Hcomplete : forall u, in_family c u -> FinSet.mem (key m) u (snd final) = true).
  { apply (Pre.family_induction c).
    - intros u Hu; apply Havailable; apply Hseeds; exact Hu.
    - intros u be v Hu Hbe Htranslate; apply Havailable.
      apply (Hclosed u v Hu); apply (translated_member c bes u); exists be; auto. }
  rewrite universe_state, Hfinal; cbn [result_state]; split.
  - apply (FinSet.elements_nodup (Pre.eu (Pre.keys c))); exact Hwf.
  - intro u; split.
    + intro Hu; exact (proj1 (Forall_forall _ _) Hfamily u Hu).
    + intro Hu; apply (FinSet.elements_spec _ HE); [exact Hwf|apply Hcomplete; exact Hu].
Qed.

(** Numeric budgets constrain primitive work without carrying any algorithm correctness premise. *)
Record budgets := Budgets {
  key_budget : BinNums.N;
  callback_budget : BinNums.N
}.

Definition construction_work := Cost.ticks setup_c.
Definition materialization_work :=
  Cost.ticks (FinSet.elements_c (snd (result_state (Cost.value discover_state_c)))).
Definition discovered_count := N.of_nat (length universe).
Definition edge_count := N.of_nat (length (Cfg.edges (Pre.block_cfg c))).
Definition seed_count := N.of_nat (length (Pre.seeds (Pre.input c))).
Definition fuel_width := N.pos (Pos.size (snd setup)).

Local Lemma translation_cost (b : budgets) :
  (forall be u, In be (Cfg.edges (Pre.block_cfg c)) -> in_family c u ->
    (Cost.ticks (Pre.translate_c (Pre.input c) be u) <= callback_budget b)%N) ->
  forall u, in_family c u ->
    (Cost.ticks (translated_c c (Cfg.edges (Pre.block_cfg c)) u) <=
      edge_count * (2 + callback_budget b))%N.
Proof.
  intros Hcallback u Hu.
  assert (Hsum : forall bes, incl bes (Cfg.edges (Pre.block_cfg c)) ->
    (Cost.ticks (translated_c c bes u) <=
      N.of_nat (length bes) * (2 + callback_budget b))%N).
  { induction bes as [|be rest IH]; intro Hsub;
      [cbn [translated_c]; rewrite Cost.ticks_ret; cbn; lia|].
    cbn [translated_c length]; rewrite Nat2N.inj_succ.
    autorewrite with galois_cost.
    pose proof (Hcallback be u (Hsub be (or_introl eq_refl)) Hu) as Hbe.
    assert (Hrest : incl rest (Cfg.edges (Pre.block_cfg c))).
    { intros edge Hedge; apply Hsub; now right. }
    specialize (IH Hrest).
    destruct (Cost.value (Pre.translate_c (Pre.input c) be u)); nia. }
  apply Hsum; intros be Hbe; exact Hbe.
Qed.

Local Lemma discover_ticks :
  Cost.ticks discover_c =
    (construction_work +
      Cost.ticks (iterate (step_c (engine_for (fst setup))) (snd setup)
        (Pre.seeds (Pre.input c), FinSet.empty)) +
      materialization_work)%N.
Proof.
  unfold discover_c; rewrite Cost.ticks_bind.
  assert (Hfinish :
    Cost.ticks
      (match Cost.value discover_state_c with
       | inl work => Cost.map (@inl (list U) (list U)) (FinSet.elements_c (snd work))
       | inr work => Cost.map (@inr (list U) (list U)) (FinSet.elements_c (snd work))
       end) = materialization_work).
  { unfold materialization_work; destruct (Cost.value discover_state_c);
      rewrite Cost.ticks_map; reflexivity. }
  rewrite Hfinish; unfold discover_state_c; rewrite Cost.ticks_bind; reflexivity.
Qed.

Definition discovery_credit b (work : state U) :=
  credit (length universe) (length (Cfg.edges (Pre.block_cfg c))) (key_budget b)
    (edge_count * (2 + callback_budget b)) work.

Local Lemma discovery_step_credit b :
  Pre.laws c ->
  (forall u, in_family c u ->
    (1 + Cost.ticks (encode_c (Pre.eu (Pre.keys c)) u) +
      key_bits (Pre.eu (Pre.keys c)) u <= key_budget b)%N) ->
  (forall be u, In be (Cfg.edges (Pre.block_cfg c)) -> in_family c u ->
    (Cost.ticks (Pre.translate_c (Pre.input c) be u) <= callback_budget b)%N) ->
  let m := engine_for (Cfg.edges (Pre.block_cfg c)) in
  forall work, valid m (in_family c) work ->
    match Cost.value (step_c m work) with
    | inl mid => valid m (in_family c) mid /\
        (Cost.ticks (step_c m work) + discovery_credit b mid + 2 <=
          discovery_credit b work)%N
    | inr _ => (Cost.ticks (step_c m work) + 0 <= 0 + discovery_credit b work)%N
    end.
Proof.
  intros Hlaw Hkey Hcallback m work Hwork.
  pose proof (Pre.eu_laws c (Pre.graphs c Hlaw)) as HE.
  assert (Hcard : forall xs, NoDup xs -> Forall (in_family c) xs ->
    length xs <= length universe).
  { intros xs Hnodup Hfamily; apply NoDup_incl_length; [exact Hnodup|].
    intros x Hx; apply (proj2 (universe_exact Hlaw) x).
    exact (proj1 (Forall_forall _ _) Hfamily x Hx). }
  destruct (discovery_parameters (Cfg.edges (Pre.block_cfg c)) Hlaw (fun _ H => H))
    as [Hnext _].
  assert (Hbounds : forall u, in_family c u ->
    (1 + Cost.ticks (encode_c (key m) u) + key_bits (key m) u <= key_budget b)%N /\
    (Cost.ticks (next_c m u) <= edge_count * (2 + callback_budget b))%N /\
    length (next m u) <= length (Cfg.edges (Pre.block_cfg c))).
  { intros u Hu; split; [apply Hkey; exact Hu|]; split.
    - apply translation_cost; assumption.
    - apply translated_length. }
  pose proof (credit_step m HE Hcard Hbounds Hnext Hwork) as Hcredit.
  unfold discovery_credit.
  destruct (Cost.value (step_c m work)); [exact Hcredit|lia].
Qed.

(** Discovery work is linear in discovered members and ordered edges, plus construction and width. *)
Theorem discover_cost (b : budgets) :
  Pre.laws c ->
  (forall u, in_family c u ->
    (1 + Cost.ticks (encode_c (Pre.eu (Pre.keys c)) u) +
      key_bits (Pre.eu (Pre.keys c)) u <= key_budget b)%N) ->
  (forall be u, In be (Cfg.edges (Pre.block_cfg c)) -> in_family c u ->
    (Cost.ticks (Pre.translate_c (Pre.input c) be u) <= callback_budget b)%N) ->
  (Cost.ticks discover_c <= construction_work + materialization_work +
    discovered_count *
      (key_budget b + edge_count * (2 + callback_budget b) + 1 +
        edge_count * (key_budget b + 3)) +
    seed_count * (key_budget b + 2) + 2 * fuel_width)%N.
Proof.
  intros Hlaw Hkey Hcallback.
  pose proof (Pre.eu_laws c (Pre.graphs c Hlaw)) as HE.
  set (bes := Cfg.edges (Pre.block_cfg c)).
  set (m := engine_for bes).
  destruct (discovery_parameters bes Hlaw (fun _ H => H)) as [_ [_ Hvalid]].
  pose proof (discovery_step_credit b Hlaw Hkey Hcallback) as Hstep.
  pose proof (iterate_terminal_credit (step_c m) (valid m (in_family c))
    (credit (length universe) (length bes) (key_budget b)
      (edge_count * (2 + callback_budget b))) (fun _ => 0%N) 0%N
    Hstep
    (snd setup) (Pre.seeds (Pre.input c), FinSet.empty) Hvalid) as Hcost.
  unfold credit in Hcost; cbn [fst snd] in Hcost.
  pose proof (size_empty m HE) as HemptySize.
  rewrite ?HemptySize in Hcost.
  rewrite Nat.sub_0_r in Hcost.
  rewrite discover_ticks.
  assert (Hedges : fst setup = bes) by (rewrite setup_equation; reflexivity).
  rewrite Hedges; fold m.
  unfold discovered_count, seed_count, fuel_width.
  assert (Hdegree : N.of_nat (length bes) = edge_count) by reflexivity.
  rewrite Hdegree in Hcost.
  destruct (Cost.value (iterate (step_c m) (snd setup)
    (Pre.seeds (Pre.input c), FinSet.empty))); nia.
Qed.

End Discovery.

End PreFamily.
