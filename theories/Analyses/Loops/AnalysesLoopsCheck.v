(** * Indexed scalar-evolution plan checking

    The checker validates source shapes and earlier-phi dependencies using shared Memo tables.
    For example, a changed earlier-phi observation selects a new context key for the same tree.
    Builds on: AnalysesLoopsRecognise, BaseMemo, BaseMap and ProgramSsa. *)

From Stdlib Require Import List Bool Arith NArith ZArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseMemo BasePrepared.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import AnalysesLoopsRecognise.
Import List.ListNotations Cost.Notations Recognise.

Module PlanCheck.

Definition binary_c {N V K} (EV : encoding V) (body_c : N -> Cost.t bool)
    (values : Map.t V (N * definition N V K)) (flag_c : K -> Cost.t bool) x a b :=
  let* found := Map.get_c EV x values in
  match found with
  | Some (n, Op o [arg_a; arg_b]) =>
    Cost.step ;;
    let* inside := body_c n in
    Cost.step ;;
    let* flagged := flag_c o in
    let* same_a := eqb_c EV arg_a a in
    let* same_b := eqb_c EV arg_b b in
    Cost.ret (inside && flagged && same_a && same_b)
  | _ => Cost.ret false
  end.

Definition binary {N V K} EV body_c values flag_c x a b :=
  Cost.value (@binary_c N V K EV body_c values flag_c x a b).

(** Binary checking observes the exact ordered source operands and the selected operation flag. *)
Theorem binary_equation {N V K} (EV : encoding V) body_c values flag_c x a b :
  @binary N V K EV body_c values flag_c x a b =
  match Map.get EV x values with
  | Some (n, Op o [arg_a; arg_b]) =>
    Cost.value (body_c n) && Cost.value (flag_c o) && eqb EV arg_a a && eqb EV arg_b b
  | _ => false
  end.
Proof.
  unfold binary, binary_c; autorewrite with galois_cost.
  fold (Map.get EV x values).
  destruct (Map.get EV x values) as [[n [o args|header i|]]|]; try reflexivity.
  destruct args as [|arg_a [|arg_b [|extra rest]]]; autorewrite with galois_cost; reflexivity.
Qed.

Definition constant_c {N V K C} (EV : encoding V) (body_c : N -> Cost.t bool)
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C) x z :=
  let* found := Map.get_c EV x values in
  match found with
  | Some (n, Op o []) =>
    Cost.step ;;
    let* inside := body_c n in
    Cost.step ;;
    let* literal := const_op_c so o in
    Cost.step ;;
    Cost.ret (inside && match literal with Some actual => Z.eqb actual z | None => false end)
  | _ => Cost.ret false
  end.

Definition constant {N V K C} EV body_c values so x z :=
  Cost.value (@constant_c N V K C EV body_c values so x z).

(** Constant checking retains the literal tag and its exact integer payload. *)
Theorem constant_equation {N V K C} (EV : encoding V) body_c values so x z :
  @constant N V K C EV body_c values so x z =
  match Map.get EV x values with
  | Some (n, Op o []) =>
    Cost.value (body_c n) &&
      match const_op so o with Some actual => Z.eqb actual z | None => false end
  | _ => false
  end.
Proof.
  unfold constant, constant_c; autorewrite with galois_cost; fold (Map.get EV x values).
  destruct (Map.get EV x values) as [[n [o args|header i|]]|]; try reflexivity.
  destruct args; autorewrite with galois_cost; reflexivity.
Qed.

Definition check_result V := (bool * FinSet.t V)%type.
Definition failed {V} : check_result V := (false, FinSet.empty).

(** Source binary conditions name the stored ordered definition and its primitive operation law. *)
Definition binary_shape {N V K} (EV : encoding V) body_c
    (values : Map.t V (N * definition N V K)) flag_c x a b : Prop :=
  exists n o, Map.get EV x values = Some (n, Op o [a; b]) /\
    Cost.value (body_c n) = true /\ Cost.value (flag_c o) = true.

(** The binary gate decides the source-definition conditions without assumptions about its output. *)
Theorem binary_correct {N V K} (EV : encoding V) (HE : encoding_laws EV)
    body_c values flag_c x a b :
  @binary N V K EV body_c values flag_c x a b = true <->
    binary_shape EV body_c values flag_c x a b.
Proof.
  rewrite binary_equation; unfold binary_shape.
  destruct (Map.get EV x values) as [[n d]|].
  - destruct d as [o args|header i|].
    + destruct args as [|arg_a [|arg_b [|extra rest]]];
        try (split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate]).
      rewrite !Bool.andb_true_iff, !eqb_true_iff by exact HE.
      split.
      * intros [[[Hinside Hflag] Ha] Hb]; subst arg_a arg_b.
        exists n, o; repeat split; assumption.
      * intros [n' [o' [Hshape [Hinside Hflag]]]].
        inversion Hshape; subst; repeat split; assumption.
    + split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
    + split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
  - split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
Qed.

(** Expression conditions describe source definitions, primitive observations and lower-rank leaves. *)
Inductive expression_conditions {N V K C} (EV : encoding V) body_c
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C) (before : V -> bool)
    : scev_expr V -> Prop :=
  | Outside_condition : forall x n d,
      Map.get EV x values = Some (n, d) -> Cost.value (body_c n) = false ->
      expression_conditions EV body_c values so before (SOutside x)
  | Phi_condition : forall x n d,
      Map.get EV x values = Some (n, d) -> before x = true ->
      expression_conditions EV body_c values so before (SPhi x)
  | Add_condition : forall x a b,
      binary_shape EV body_c values (add_op_c so) x (scev_expr_root a) (scev_expr_root b) ->
      expression_conditions EV body_c values so before a ->
      expression_conditions EV body_c values so before b ->
      expression_conditions EV body_c values so before (SAdd x a b)
  | Mul_condition : forall x a b,
      binary_shape EV body_c values (mul_op_c so) x (scev_expr_root a) (scev_expr_root b) ->
      expression_conditions EV body_c values so before a ->
      expression_conditions EV body_c values so before b ->
      expression_conditions EV body_c values so before (SMul x a b)
  | Constant_condition : forall x z n o,
      Map.get EV x values = Some (n, Op o []) -> Cost.value (body_c n) = true ->
      const_op so o = Some z ->
      expression_conditions EV body_c values so before (SConst x z).

(** The independent tree reference preserves failed-prefix behavior and dependency-set results. *)
Fixpoint expression_reference {N V K C} (EV : encoding V) body_c
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C)
    (before : V -> bool) (e : scev_expr V) : check_result V :=
  match e with
  | SOutside x =>
    (match Map.get EV x values with
    | Some (n, _) => negb (Cost.value (body_c n))
    | None => false
    end, FinSet.empty)
  | SPhi x => (Map.mem EV x values && before x, FinSet.add EV x FinSet.empty)
  | SConst x z => (constant EV body_c values so x z, FinSet.empty)
  | SAdd x a b | SMul x a b =>
    let flag_c := match e with SAdd _ _ _ => add_op_c so | _ => mul_op_c so end in
    if binary EV body_c values flag_c x (scev_expr_root a) (scev_expr_root b) then
      let ra := expression_reference EV body_c values so before a in
      if fst ra then
        let rb := expression_reference EV body_c values so before b in
        (fst rb, FinSet.union (snd ra) (snd rb))
      else failed
    else failed
  end.

(** Tree checking is rank-sensitive only at its explicitly named phi leaves. *)
Theorem expression_reference_support {N V K C} (EV : encoding V) body_c
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C) left right e :
  (forall x, In x (scev_expression_phis e) -> left x = right x) ->
  expression_reference EV body_c values so left e =
    expression_reference EV body_c values so right e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; intro Hagree;
    cbn [expression_reference]; try reflexivity.
  - rewrite Hagree; [reflexivity|left; reflexivity].
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; auto.
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; auto.
Qed.

Local Lemma binary_accepts {V} (local : bool) (ra rb : check_result V) :
  fst (if local then if fst ra then (fst rb, FinSet.union (snd ra) (snd rb))
    else failed else failed) = true <->
  local = true /\ fst ra = true /\ fst rb = true.
Proof.
  destruct ra as [va da], rb as [vb db], local, va, vb; cbn; intuition discriminate.
Qed.

(** Literal checking decides the stored nullary definition and its exact primitive literal. *)
Theorem constant_correct {N V K C} (EV : encoding V) body_c values (so : scev_ops K C) x z :
  @constant N V K C EV body_c values so x z = true <->
  exists n o, Map.get EV x values = Some (n, Op o []) /\
    Cost.value (body_c n) = true /\ const_op so o = Some z.
Proof.
  rewrite constant_equation.
  destruct (Map.get EV x values) as [[n d]|].
  - destruct d as [o args|header i|].
    + destruct args as [|arg rest].
      * rewrite Bool.andb_true_iff.
        destruct (const_op so o) as [literal|] eqn:Hliteral.
        -- rewrite Z.eqb_eq; split.
           ++ intros [Hinside Heq]; subst literal.
              exists n, o; repeat split; assumption.
           ++ intros [n' [o' [Hshape [Hinside Hvalue]]]].
              inversion Hshape; subst; split; congruence.
        -- split.
           ++ intros [_ Hfalse]; discriminate.
           ++ intros [n' [o' [Hshape [_ Hvalue]]]]; inversion Hshape; subst; congruence.
      * split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
    + split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
    + split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
  - split; [discriminate|intros [n' [o' [Hshape _]]]; discriminate].
Qed.

(** Tree acceptance is equivalent to independently stated source shapes and phi observations. *)
Theorem expression_conditions_correct {N V K C} (EV : encoding V) (HE : encoding_laws EV)
    body_c values (so : scev_ops K C) before e :
  fst (@expression_reference N V K C EV body_c values so before e) = true <->
    expression_conditions EV body_c values so before e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z].
  - cbn [expression_reference fst].
    destruct (Map.get EV x values) as [[n d]|] eqn:Hget.
    + rewrite Bool.negb_true_iff; split.
      * intro Houtside; econstructor; eassumption.
      * intro Hconditions; inversion Hconditions; subst; congruence.
    + split; [discriminate|intro Hconditions; inversion Hconditions; subst; congruence].
  - cbn [expression_reference fst]; rewrite Bool.andb_true_iff, Map.mem_spec.
    split.
    + intros [[[n d] Hget] Hbefore]; econstructor; eassumption.
    + intro Hconditions; inversion Hconditions; subst.
      split; [eexists; eassumption|assumption].
  - change (fst (if binary EV body_c values (add_op_c so) x
        (scev_expr_root a) (scev_expr_root b) then
      if fst (expression_reference EV body_c values so before a) then
        (fst (expression_reference EV body_c values so before b),
          FinSet.union (snd (expression_reference EV body_c values so before a))
            (snd (expression_reference EV body_c values so before b)))
      else failed else failed) = true <->
      expression_conditions EV body_c values so before (SAdd x a b)).
    rewrite binary_accepts, binary_correct, IHa, IHb by exact HE.
    split.
    + intros [Hshape [Ha Hb]]; constructor; assumption.
    + intro Hconditions; inversion Hconditions; subst; repeat split; assumption.
  - change (fst (if binary EV body_c values (mul_op_c so) x
        (scev_expr_root a) (scev_expr_root b) then
      if fst (expression_reference EV body_c values so before a) then
        (fst (expression_reference EV body_c values so before b),
          FinSet.union (snd (expression_reference EV body_c values so before a))
            (snd (expression_reference EV body_c values so before b)))
      else failed else failed) = true <->
      expression_conditions EV body_c values so before (SMul x a b)).
    rewrite binary_accepts, binary_correct, IHa, IHb by exact HE.
    split.
    + intros [Hshape [Ha Hb]]; constructor; assumption.
    + intro Hconditions; inversion Hconditions; subst; repeat split; assumption.
  - cbn [expression_reference fst]; rewrite constant_correct.
    split.
    + intros [n [o [Hget [Hinside Hliteral]]]]; econstructor; eassumption.
    + intro Hconditions; inversion Hconditions; subst; do 2 eexists; repeat split; eassumption.
Qed.

Definition query {V} before e : context_key V bool :=
  (e, List.map (fun x => (x, before x)) (scev_expression_phis e)).

Definition check_encoding {V} (EV : encoding V) := context_encoding EV bool_encoding.
Definition check_memo V := Memo.t (context_key V bool) (check_result V).

Definition check_reference {N V K C} EV body_c values (so : scev_ops K C)
    (key : context_key V bool) :=
  @expression_reference N V K C EV body_c values so
    (context_lookup EV false (snd key)) (fst key).

Local Lemma query_reference {N V K C} (EV : encoding V) (HE : encoding_laws EV)
    body_c values (so : scev_ops K C) before e :
  @check_reference N V K C EV body_c values so (query before e) =
    expression_reference EV body_c values so before e.
Proof.
  unfold check_reference, query; cbn [fst snd].
  apply expression_reference_support; intros x Hin; apply context_lookup_project; assumption.
Qed.

(** Checker-table validity is independent of later rank changes. *)
Definition check_valid {N V K C} EV body_c values (so : scev_ops K C) (m : check_memo V) :=
  Map.wf (check_encoding EV) m /\
    Memo.valid (check_encoding EV) (@check_reference N V K C EV body_c values so) m.

Definition check_run_result V := memo_result (context_key V bool) (check_result V) unit.

(** A result couples the complete tree-reference observation to validity of its returned table. *)
Definition expression_result_valid {N V K C} EV body_c values (so : scev_ops K C)
    before e (result : check_run_result V) : Prop :=
  let '((value, table), _) := result in
  value = @expression_reference N V K C EV body_c values so before e /\
    check_valid EV body_c values so table.

Definition check_binary_c {V} (EV : encoding V) (local_c : Cost.t bool)
    (ra_c rb_c : check_memo V -> Cost.t (check_run_result V)) (m : check_memo V) :=
  let* accepted := local_c in
  if accepted then
    Cost.step ;;
    let* first := ra_c m in
    let '((ra, ma), _) := first in
    if fst ra then
      Cost.step ;;
      let* second := rb_c ma in
      let '((rb, mb), _) := second in
      let* deps := FinSet.union_c (snd ra) (snd rb) in
      Cost.ret (((fst rb, deps), mb), tt)
    else Cost.ret ((failed, ma), tt)
  else Cost.ret ((failed, m), tt).

(** Every checker miss threads the actual child-returned table through the next child. *)
Fixpoint scev_check_expr_c {N V K C} (EV : encoding V) body_c
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C)
    (before_c : V -> Cost.t bool) (e : scev_expr V) (m : check_memo V)
    : Cost.t (check_run_result V) :=
  Cost.step ;;
  let* key := context_prepare_c EV bool_encoding before_c e in
  let* out := memo_run_c key (fun table side =>
    match e with
    | SOutside x =>
      let* found := Map.get_c EV x values in
      match found with
      | Some (n, _) =>
        Cost.step ;;
        let* inside := body_c n in
        Cost.ret (((negb inside, FinSet.empty), table), side)
      | None => Cost.ret ((failed, table), side)
      end
    | SPhi x =>
      let* listed := Map.mem_c EV x values in
      Cost.step ;;
      let* earlier := before_c x in
      let* empty := FinSet.empty_c in
      let* deps := FinSet.add_c EV x empty in
      Cost.ret (((listed && earlier, deps), table), side)
    | SConst x z =>
      let* accepted := constant_c EV body_c values so x z in
      Cost.ret (((accepted, FinSet.empty), table), side)
    | SAdd x a b | SMul x a b =>
      let flag_c := match e with SAdd _ _ _ => add_op_c so | _ => mul_op_c so end in
      check_binary_c EV (binary_c EV body_c values flag_c x (scev_expr_root a) (scev_expr_root b))
        (scev_check_expr_c EV body_c values so before_c a)
        (scev_check_expr_c EV body_c values so before_c b) table
    end) m tt in
  Cost.ret (fst out).

Local Lemma check_binary_correct {N V K C} (EV : encoding V) body_c values
    (so : scev_ops K C) before local_c ra_c rb_c a b m :
  (forall table, check_valid EV body_c values so table ->
    expression_result_valid EV body_c values so before a (Cost.value (ra_c table))) ->
  (forall table, check_valid EV body_c values so table ->
    expression_result_valid EV body_c values so before b (Cost.value (rb_c table))) ->
  @check_valid N V K C EV body_c values so m ->
  let '((result, table), _) := Cost.value (check_binary_c EV local_c ra_c rb_c m) in
  result = (if Cost.value local_c then
    let ra := expression_reference EV body_c values so before a in
    if fst ra then
      let rb := expression_reference EV body_c values so before b in
      (fst rb, FinSet.union (snd ra) (snd rb))
    else failed else failed) /\ check_valid EV body_c values so table.
Proof.
  intros Ha Hb Hm; unfold check_binary_c; autorewrite with galois_cost.
  destruct (Cost.value local_c); [|split; [reflexivity|exact Hm]].
  autorewrite with galois_cost.
  specialize (Ha m Hm).
  destruct (Cost.value (ra_c m)) as [[[va da] ma] []].
  destruct Ha as [Ha Hma]; cbn [fst].
  rewrite <- Ha; cbn [fst snd]; destruct va.
  - autorewrite with galois_cost; specialize (Hb ma Hma).
    destruct (Cost.value (rb_c ma)) as [[[vb db] mb] []].
    destruct Hb as [Hb Hmb]; autorewrite with galois_cost.
    rewrite <- Hb; split; [reflexivity|exact Hmb].
  - autorewrite with galois_cost; split; [reflexivity|exact Hma].
Qed.

(** Expression checking equals the full independent reference and maintains the shared Memo. *)
Theorem scev_check_expr_correct {N V K C} (EV : encoding V) (HE : encoding_laws EV)
    body_c values (so : scev_ops K C) before_c e m :
  check_valid EV body_c values so m ->
  expression_result_valid EV body_c values so (fun x => Cost.value (before_c x)) e
    (Cost.value (@scev_check_expr_c N V K C EV body_c values so before_c e m)).
Proof.
  revert m; induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z];
    intros m [Hwf Hvalid]; cbn [scev_check_expr_c]; autorewrite with galois_cost;
    rewrite context_prepare_value.
  all: match goal with
  | |- expression_result_valid _ _ _ _ ?before ?source ?result =>
    let Href := fresh "Hquery" in
    pose proof (query_reference EV HE body_c values so before source) as Href;
    unfold expression_result_valid; rewrite <- Href;
    apply (memo_result_forget_side (check_encoding EV)
      (check_reference EV body_c values so) (fun _ : unit => True) (query before source) result)
  end.
  all: eapply memo_run_agrees;
    [apply context_encoding_laws; [exact HE|exact bool_encoding_laws] |
      apply PreparedKey.prepare_valid | exact Hwf | exact Hvalid | exact I |].
  all: intros table [] Htable Hreference _;
    rewrite PreparedKey.prepare_key; unfold memo_result_valid.
  - autorewrite with galois_cost; fold (Map.get EV x values).
    destruct (Map.get EV x values) as [[n d]|] eqn:Hfound; autorewrite with galois_cost;
      (split; [|exact (conj Htable (conj Hreference I))]).
    + etransitivity; [|symmetry; exact Hquery].
      cbn [expression_reference]; rewrite Hfound; reflexivity.
    + etransitivity; [|symmetry; exact Hquery].
      cbn [expression_reference]; rewrite Hfound; reflexivity.
  - autorewrite with galois_cost; split; [symmetry; exact Hquery|].
    exact (conj Htable (conj Hreference I)).
  - pose proof (check_binary_correct EV body_c values so (fun y => Cost.value (before_c y))
      (binary_c EV body_c values (add_op_c so) x (scev_expr_root a) (scev_expr_root b))
      (scev_check_expr_c EV body_c values so before_c a)
      (scev_check_expr_c EV body_c values so before_c b) a b table
      IHa IHb (conj Htable Hreference)) as Hpair.
    destruct (Cost.value (check_binary_c EV
      (binary_c EV body_c values (add_op_c so) x (scev_expr_root a) (scev_expr_root b))
      (scev_check_expr_c EV body_c values so before_c a)
      (scev_check_expr_c EV body_c values so before_c b) table)) as [[result updated] []].
    destruct Hpair as [Hresult [Hupdated Hmeaning]].
    split; [etransitivity; [exact Hresult|symmetry; exact Hquery]|].
    exact (conj Hupdated (conj Hmeaning I)).
  - pose proof (check_binary_correct EV body_c values so (fun y => Cost.value (before_c y))
      (binary_c EV body_c values (mul_op_c so) x (scev_expr_root a) (scev_expr_root b))
      (scev_check_expr_c EV body_c values so before_c a)
      (scev_check_expr_c EV body_c values so before_c b) a b table
      IHa IHb (conj Htable Hreference)) as Hpair.
    destruct (Cost.value (check_binary_c EV
      (binary_c EV body_c values (mul_op_c so) x (scev_expr_root a) (scev_expr_root b))
      (scev_check_expr_c EV body_c values so before_c a)
      (scev_check_expr_c EV body_c values so before_c b) table)) as [[result updated] []].
    destruct Hpair as [Hresult [Hupdated Hmeaning]].
    split; [etransitivity; [exact Hresult|symmetry; exact Hquery]|].
    exact (conj Hupdated (conj Hmeaning I)).
  - autorewrite with galois_cost; split; [symmetry; exact Hquery|].
    exact (conj Htable (conj Hreference I)).
Qed.

(** * Indexed source and plan metadata *)

Record rank_index (V : Type) := Ranks {
  ranks : Map.t V nat;
  distinct : bool;
  final : option V
}.
Arguments Ranks {V}.
Arguments ranks {V}.
Arguments distinct {V}.
Arguments final {V}.

Fixpoint rank_index_c {V} (EV : encoding V) (start : nat) (bs : list (scev_binding V))
    : Cost.t (rank_index V) :=
  match bs with
  | [] => Cost.ret (Ranks Map.empty true None)
  | b :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* tail := rank_index_c EV (S start) rest in
    let* seen := Map.mem_c EV (sb_phi b) (ranks tail) in
    let* table := Map.set_c EV (sb_phi b) start (ranks tail) in
    Cost.ret (Ranks table (negb seen && distinct tail)
      (match final tail with Some x => Some x | None => Some (sb_phi b) end))
  end.

Definition prepare_ranks {V} EV start bs := Cost.value (@rank_index_c V EV start bs).

(** Rank preparation stores the first occurrence, duplicate flag and last phi without rescanning. *)
Theorem prepare_ranks_equation {V} (EV : encoding V) start bs :
  prepare_ranks EV start bs =
  match bs with
  | [] => Ranks Map.empty true None
  | b :: rest =>
    let tail := prepare_ranks EV (S start) rest in
    Ranks (Map.set EV (sb_phi b) start (ranks tail))
      (negb (Map.mem EV (sb_phi b) (ranks tail)) && distinct tail)
      (match final tail with Some x => Some x | None => Some (sb_phi b) end)
  end.
Proof.
  destruct bs; reflexivity.
Qed.

Fixpoint argument_index_c {V} (start : nat) (xs : list V) : Cost.t (Map.t nat V) :=
  match xs with
  | [] => Map.empty_c
  | x :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* tail := argument_index_c (S start) rest in
    Map.set_c nat_encoding start x tail
  end.

Definition argument_index {V} start xs := Cost.value (@argument_index_c V start xs).

Record static_index (N V K : Type) := Index {
  indexed_values : Map.t V (N * definition N V K);
  entry_args : Map.t nat V;
  back_args : Map.t nat V;
  phi_index : rank_index V
}.
Arguments Index {N V K}.
Arguments indexed_values {N V K}.
Arguments entry_args {N V K}.
Arguments back_args {N V K}.
Arguments phi_index {N V K}.

(** Preparation reads the inventory and each incoming argument list once before checking. *)
Definition prepare_index_c {N E V K G} (lv : loop_view N E V K G) inventory p :=
  let* values := scev_inventory_index_c (lssa lv) inventory in
  Cost.step ;;
  let* incoming := Ssa.args_c (lssa lv) (lentry lv) in
  let* entry := argument_index_c O incoming in
  Cost.step ;;
  let* feedback := Ssa.args_c (lssa lv) (lback lv) in
  let* back := argument_index_c O feedback in
  let* phis := rank_index_c (Ssa.val_enc (lssa lv)) O (sp_bindings p) in
  Cost.ret (Index values entry back phis).

Definition prepare_index {N E V K G} lv inventory p :=
  Cost.value (@prepare_index_c N E V K G lv inventory p).

Definition phi_before_c {N V K} (EV : encoding V) (ix : static_index N V K) rank x :=
  let* found := Map.get_c EV x (ranks (phi_index ix)) in
  Cost.step ;;
  Cost.ret (match found with Some i => Nat.ltb i rank | None => false end).

Definition phi_before {N V K} EV ix rank x :=
  Cost.value (@phi_before_c N V K EV ix rank x).

Definition binding_gate_c {N E V K G} (lv : loop_view N E V K G)
    (ix : static_index N V K) (b : scev_binding V) :=
  let EV := Ssa.val_enc (lssa lv) in
  let EN := Cfg.node_enc (Ssa.cfg (lssa lv)) in
  let* phi := Map.get_c EV (sb_phi b) (indexed_values ix) in
  let* base := Map.get_c EV (sb_base b) (indexed_values ix) in
  let* update := Map.get_c EV (sb_update_value b) (indexed_values ix) in
  match phi, base, update with
  | Some (n, Param header i), Some (base_n, _), Some (update_n, _) =>
    let* home_ok := eqb_c EN n (lheader lv) in
    let* header_ok := eqb_c EN header (lheader lv) in
    Cost.step ;;
    let* base_inside := lbody_c lv base_n in
    Cost.step ;;
    let* update_inside := lbody_c lv update_n in
    let* incoming := Map.get_c nat_encoding i (entry_args ix) in
    let* feedback := Map.get_c nat_encoding i (back_args ix) in
    match incoming, feedback with
    | Some a, Some u =>
      let* base_ok := eqb_c EV a (sb_base b) in
      let* update_ok := eqb_c EV u (sb_update_value b) in
      Cost.ret (home_ok && header_ok && negb base_inside && update_inside && base_ok && update_ok)
    | _, _ => Cost.ret false
    end
  | _, _, _ => Cost.ret false
  end.

Definition binding_gate {N E V K G} lv ix b :=
  Cost.value (@binding_gate_c N E V K G lv ix b).

Definition update_gate_c {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) (ix : static_index N V K) (b : scev_binding V) :=
  let EV := Ssa.val_enc (lssa lv) in
  match sb_kind b, sb_other b with
  | SDoubleUpdate, None =>
    Cost.map (andb (sb_phi_first b))
      (binary_c EV (lbody_c lv) (indexed_values ix) (add_op_c so)
        (sb_update_value b) (sb_phi b) (sb_phi b))
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    let root := scev_expr_root e in
    let flag_c := match sb_kind b with SAddUpdate => add_op_c so | _ => mul_op_c so end in
    let* same := eqb_c EV root (sb_phi b) in
    let* shape := binary_c EV (lbody_c lv) (indexed_values ix) flag_c (sb_update_value b)
      (if sb_phi_first b then sb_phi b else root)
      (if sb_phi_first b then root else sb_phi b) in
    Cost.ret (negb same && shape)
  | _, _ => Cost.ret false
  end.

Definition update_gate {N E V K G C} lv so ix b :=
  Cost.value (@update_gate_c N E V K G C lv so ix b).

(** Binding checking combines source-header, ordered-update and earlier-expression conditions. *)
Definition binding_reference {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) before (b : scev_binding V) : option (FinSet.t V) :=
  if binding_gate lv ix b && update_gate lv so ix b then
    match sb_kind b, sb_other b with
    | SDoubleUpdate, None => Some FinSet.empty
    | SAddUpdate, Some e | SMulUpdate, Some e =>
      let result := expression_reference (Ssa.val_enc (lssa lv))
        (lbody_c lv) (indexed_values ix) so before e in
      if fst result then Some (snd result) else None
    | _, _ => None
    end
  else None.

Definition check_binding_key V := (scev_binding V * list (V * bool))%type.
Definition check_binding_encoding {V} (EV : encoding V) :=
  pair_encoding (binding_encoding EV) (list_key_encoding (pair_encoding EV bool_encoding)).
Definition check_binding_query {V} before (b : scev_binding V) : check_binding_key V :=
  (b, List.map (fun x => (x, before x)) (scev_binding_phis b)).

Definition binding_context_reference {N E V K G C} lv (so : scev_ops K C) ix
    (key : check_binding_key V) :=
  @binding_reference N E V K G C lv so ix
    (context_lookup (Ssa.val_enc (lssa lv)) false (snd key)) (fst key).

Local Lemma binding_query_reference {N E V K G C} (lv : loop_view N E V K G)
    (HE : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix before b :
  binding_context_reference lv so ix (check_binding_query before b) =
    binding_reference lv so ix before b.
Proof.
  unfold binding_context_reference, check_binding_query; cbn [fst snd].
  unfold binding_reference.
  destruct (binding_gate lv ix b && update_gate lv so ix b); [|reflexivity].
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [sb_kind sb_other]; try reflexivity.
  all: rewrite (expression_reference_support _ _ _ _ _ before e); [reflexivity|].
  all: intros x Hin; apply context_lookup_project; assumption.
Qed.

Definition check_binding_prepare_c {V} (EV : encoding V) before_c (b : scev_binding V) :=
  let* phis :=
    match sb_other b with None => Cost.ret [] | Some e => expression_phis_c e end in
  let* entries := map_c (fun x =>
    Cost.step ;; Cost.map (fun observation => (x, observation)) (before_c x)) phis in
  PreparedKey.prepare_c (check_binding_encoding EV) (b, entries).

Local Lemma check_binding_prepare_value {V} (EV : encoding V) before_c (b : scev_binding V) :
  Cost.value (check_binding_prepare_c EV before_c b) =
    PreparedKey.prepare (check_binding_encoding EV)
      (check_binding_query (fun x => Cost.value (before_c x)) b).
Proof.
  unfold check_binding_prepare_c; autorewrite with galois_cost.
  destruct (sb_other b) as [e|] eqn:Hother;
    unfold check_binding_query, scev_binding_phis; rewrite Hother;
    autorewrite with galois_cost; rewrite ?expression_phis_value; reflexivity.
Qed.

Definition check_binding_memo V := Memo.t (check_binding_key V) (option (FinSet.t V)).

(** A binding table stores source checks under the projected earlier-phi observations. *)
Definition check_binding_valid {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix (m : check_binding_memo V) :=
  Map.wf (check_binding_encoding (Ssa.val_enc (lssa lv))) m /\
    Memo.valid (check_binding_encoding (Ssa.val_enc (lssa lv)))
      (binding_context_reference lv so ix) m.

Definition check_binding_miss_c {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) (ix : static_index N V K) before_c (b : scev_binding V)
    (m : check_binding_memo V) (expressions : check_memo V) :=
  let* header := binding_gate_c lv ix b in
  let* update := update_gate_c lv so ix b in
  if header && update then
    match sb_kind b, sb_other b with
    | SDoubleUpdate, None => Cost.ret ((Some FinSet.empty, m), expressions)
    | SAddUpdate, Some e | SMulUpdate, Some e =>
      let* checked := scev_check_expr_c (Ssa.val_enc (lssa lv))
        (lbody_c lv) (indexed_values ix) so before_c e expressions in
      let '((result, table), _) := checked in
      Cost.ret (((if fst result then Some (snd result) else None), m), table)
    | _, _ => Cost.ret ((None, m), expressions)
    end
  else Cost.ret ((None, m), expressions).

(** Binding queries use the common Memo operation and share the actual expression checker table. *)
Definition scev_check_binding_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix before_c b m expressions :=
  let* key := check_binding_prepare_c (Ssa.val_enc (lssa lv)) before_c b in
  Cost.map fst (memo_run_c key (check_binding_miss_c lv so ix before_c b) m expressions).

Local Lemma check_binding_miss_correct {N E V K G C} (lv : loop_view N E V K G)
    (HE : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C)
    ix before_c b m expressions :
  check_binding_valid lv so ix m ->
  check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions ->
  let '((result, updated), expressions') := Cost.value
    (check_binding_miss_c lv so ix before_c b m expressions) in
  result = binding_reference lv so ix (fun x => Cost.value (before_c x)) b /\
    check_binding_valid lv so ix updated /\
    check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions'.
Proof.
  intros Hbinding Hexpressions.
  unfold check_binding_miss_c, binding_reference; autorewrite with galois_cost.
  fold (binding_gate lv ix b); fold (update_gate lv so ix b).
  destruct (binding_gate lv ix b && update_gate lv so ix b);
    [|split; [reflexivity|split; assumption]].
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [sb_kind sb_other]; autorewrite with galois_cost;
    try (split; [reflexivity|split; assumption]).
  all: pose proof (scev_check_expr_correct (Ssa.val_enc (lssa lv)) HE
      (lbody_c lv) (indexed_values ix) so before_c e expressions Hexpressions) as Hexpr;
    destruct (Cost.value (scev_check_expr_c (Ssa.val_enc (lssa lv))
      (lbody_c lv) (indexed_values ix) so before_c e expressions))
      as [[result table] []]; destruct Hexpr as [Hresult Htable];
    autorewrite with galois_cost; rewrite <- Hresult.
  all: split; [reflexivity|split; assumption].
Qed.

(** Binding checking returns its full reference option and maintains both shared checker tables. *)
Theorem scev_check_binding_correct {N E V K G C} (lv : loop_view N E V K G)
    (HE : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C)
    ix before_c b m expressions :
  check_binding_valid lv so ix m ->
  check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions ->
  let '((result, updated), expressions') := Cost.value
    (scev_check_binding_c lv so ix before_c b m expressions) in
  result = binding_reference lv so ix (fun x => Cost.value (before_c x)) b /\
    check_binding_valid lv so ix updated /\
    check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions'.
Proof.
  intros [Hwf Hvalid] Hexpressions.
  unfold scev_check_binding_c; autorewrite with galois_cost.
  rewrite check_binding_prepare_value.
  pose proof (memo_run_agrees (check_binding_encoding (Ssa.val_enc (lssa lv)))
    ltac:(apply pair_encoding_laws; [apply binding_encoding_laws; exact HE |
      apply list_key_encoding_laws, pair_encoding_laws; [exact HE|exact bool_encoding_laws]])
    (binding_context_reference lv so ix)
    (check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so)
    (PreparedKey.prepare _ (check_binding_query (fun x => Cost.value (before_c x)) b))
    (check_binding_miss_c lv so ix before_c b) m expressions
    (PreparedKey.prepare_valid _ _) Hwf Hvalid Hexpressions) as Hrun.
  assert (Hmiss : forall table exprs,
    Map.wf (check_binding_encoding (Ssa.val_enc (lssa lv))) table ->
    Memo.valid (check_binding_encoding (Ssa.val_enc (lssa lv)))
      (binding_context_reference lv so ix) table ->
    check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so exprs ->
    memo_result_valid (check_binding_encoding (Ssa.val_enc (lssa lv)))
      (binding_context_reference lv so ix)
      (check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so)
      (check_binding_query (fun x => Cost.value (before_c x)) b)
      (Cost.value (check_binding_miss_c lv so ix before_c b table exprs))).
  { intros table exprs Htable Hreference Hexprs.
    pose proof (check_binding_miss_correct lv HE so ix before_c b table exprs
      (conj Htable Hreference) Hexprs) as Hlocal.
    destruct (Cost.value (check_binding_miss_c lv so ix before_c b table exprs))
      as [[result updated] exprs'].
    destruct Hlocal as [Hresult [[Hupdated Hmeaning] Hexprs']].
    split.
    - rewrite binding_query_reference by exact HE; exact Hresult.
    - exact (conj Hupdated (conj Hmeaning Hexprs')). }
  specialize (Hrun Hmiss).
  destruct (fst (Cost.value (memo_run_c _ _ _ _))) as [[result updated] exprs'].
  destruct Hrun as [Hresult [Hupdated [Hmeaning Hexprs]]].
  split.
  - rewrite PreparedKey.prepare_key, binding_query_reference in Hresult by exact HE.
    exact Hresult.
  - split; [split; assumption|exact Hexprs].
Qed.

(** * Independent binding conditions *)

(** Header conditions identify the indexed parameter, outside base and selected incoming values. *)
Definition header_conditions {N E V K G} (lv : loop_view N E V K G)
    (ix : static_index N V K) (b : scev_binding V) : Prop :=
  let EV := Ssa.val_enc (lssa lv) in
  match Map.get EV (sb_phi b) (indexed_values ix),
      Map.get EV (sb_base b) (indexed_values ix),
      Map.get EV (sb_update_value b) (indexed_values ix) with
  | Some (n, Param header i), Some (base_n, _), Some (update_n, _) =>
    n = lheader lv /\ header = lheader lv /\ lbody lv base_n = false /\
      lbody lv update_n = true /\
      Map.get nat_encoding i (entry_args ix) = Some (sb_base b) /\
      Map.get nat_encoding i (back_args ix) = Some (sb_update_value b)
  | _, _, _ => False
  end.

(** Header checking decides the indexed source-header conditions. *)
Theorem binding_gate_correct {N E V K G} (lv : loop_view N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (lssa lv))))
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) ix b :
  binding_gate lv ix b = true <-> header_conditions lv ix b.
Proof.
  unfold binding_gate, binding_gate_c, header_conditions; autorewrite with galois_cost.
  fold (Map.get (Ssa.val_enc (lssa lv)) (sb_phi b) (indexed_values ix)).
  fold (Map.get (Ssa.val_enc (lssa lv)) (sb_base b) (indexed_values ix)).
  fold (Map.get (Ssa.val_enc (lssa lv)) (sb_update_value b) (indexed_values ix)).
  destruct (Map.get _ (sb_phi b) (indexed_values ix)) as [[n d]|];
    [|autorewrite with galois_cost; intuition discriminate].
  destruct (Map.get _ (sb_base b) (indexed_values ix)) as [[base_n base_d]|];
    [|destruct d; autorewrite with galois_cost; intuition discriminate].
  destruct (Map.get _ (sb_update_value b) (indexed_values ix)) as [[update_n update_d]|];
    [|destruct d; autorewrite with galois_cost; intuition discriminate].
  destruct d as [o args|header i|]; autorewrite with galois_cost;
    try (intuition discriminate).
  autorewrite with galois_cost.
  fold (Map.get nat_encoding i (entry_args ix)).
  fold (Map.get nat_encoding i (back_args ix)).
  destruct (Map.get nat_encoding i (entry_args ix)) as [a|] eqn:Hentry;
    destruct (Map.get nat_encoding i (back_args ix)) as [u|] eqn:Hback;
    autorewrite with galois_cost; try (split; [discriminate|intuition discriminate]).
  change ((eqb (Cfg.node_enc (Ssa.cfg (lssa lv))) n (lheader lv) &&
    eqb (Cfg.node_enc (Ssa.cfg (lssa lv))) header (lheader lv) &&
    negb (lbody lv base_n) && lbody lv update_n &&
    eqb (Ssa.val_enc (lssa lv)) a (sb_base b) &&
    eqb (Ssa.val_enc (lssa lv)) u (sb_update_value b)) = true <->
    n = lheader lv /\ header = lheader lv /\ lbody lv base_n = false /\
      lbody lv update_n = true /\ Some a = Some (sb_base b) /\
      Some u = Some (sb_update_value b)).
  rewrite !Bool.andb_true_iff, Bool.negb_true_iff,
    !eqb_true_iff by assumption.
  intuition congruence.
Qed.

(** Update conditions retain the ordinary operand order and the distinguished doubling shape. *)
Definition update_conditions {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) (b : scev_binding V) : Prop :=
  let EV := Ssa.val_enc (lssa lv) in
  match sb_kind b, sb_other b with
  | SDoubleUpdate, None =>
    sb_phi_first b = true /\ binary_shape EV (lbody_c lv) (indexed_values ix) (add_op_c so)
      (sb_update_value b) (sb_phi b) (sb_phi b)
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    let root := scev_expr_root e in
    root <> sb_phi b /\
      binary_shape EV (lbody_c lv) (indexed_values ix)
        (match sb_kind b with SAddUpdate => add_op_c so | _ => mul_op_c so end)
        (sb_update_value b) (if sb_phi_first b then sb_phi b else root)
        (if sb_phi_first b then root else sb_phi b)
  | _, _ => False
  end.

(** Update checking decides its independent operand-shape conditions for all binding forms. *)
Theorem update_gate_correct {N E V K G C} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix b :
  update_gate lv so ix b = true <-> update_conditions lv so ix b.
Proof.
  unfold update_gate, update_gate_c, update_conditions.
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [sb_kind sb_other sb_phi_first sb_update_value sb_phi];
    autorewrite with galois_cost; try (intuition discriminate).
  all: repeat match goal with
  | |- context [Cost.value (eqb_c ?EV ?x ?y)] =>
    change (Cost.value (eqb_c EV x y)) with (eqb EV x y)
  | |- context [Cost.value (@binary_c ?N ?V ?K ?EV ?body ?values ?flag ?x ?a ?b)] =>
    change (Cost.value (@binary_c N V K EV body values flag x a b))
      with (@binary N V K EV body values flag x a b)
  end.
  all: rewrite ?Bool.andb_true_iff, ?Bool.negb_true_iff,
    ?eqb_false_iff, ?binary_correct by exact HV.
  all: reflexivity.
Qed.

Fixpoint expression_dependencies {V} (EV : encoding V) (e : scev_expr V) : FinSet.t V :=
  match e with
  | SPhi x => FinSet.add EV x FinSet.empty
  | SAdd _ a b | SMul _ a b =>
    FinSet.union (expression_dependencies EV a) (expression_dependencies EV b)
  | _ => FinSet.empty
  end.

Definition binding_dependencies {V} (EV : encoding V) (b : scev_binding V) : FinSet.t V :=
  match sb_other b with Some e => expression_dependencies EV e | None => FinSet.empty end.

(** Accepted expression results contain the dependency set computed independently from syntax. *)
Theorem expression_dependencies_correct {N V K C} (EV : encoding V) body_c values
    (so : scev_ops K C) before e :
  fst (@expression_reference N V K C EV body_c values so before e) = true ->
  snd (expression_reference EV body_c values so before e) = expression_dependencies EV e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; try (intro H; reflexivity).
  all: cbn [expression_reference expression_dependencies].
  all: destruct (binary EV body_c values _ x (scev_expr_root a) (scev_expr_root b));
    [|discriminate].
  all: destruct (expression_reference EV body_c values so before a) as [va da] eqn:Ha;
    destruct va; [|discriminate].
  all: destruct (expression_reference EV body_c values so before b) as [vb db] eqn:Hb;
    cbn [fst snd]; intro Haccepted; subst vb.
  all: specialize (IHa eq_refl); specialize (IHb eq_refl);
    cbn [snd] in IHa, IHb; rewrite IHa, IHb; reflexivity.
Qed.

(** Binding conditions combine independent header, update and expression conditions. *)
Definition binding_conditions {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    (ix : static_index N V K) before (b : scev_binding V) : Prop :=
  header_conditions lv ix b /\ update_conditions lv so ix b /\
  match sb_kind b, sb_other b with
  | SDoubleUpdate, None => True
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    expression_conditions (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so before e
  | _, _ => False
  end.

(** Binding results use the independently syntax-derived dependency sets on every accepted branch. *)
Theorem binding_dependencies_correct {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) ix before b :
  binding_reference lv so ix before b =
    if binding_gate lv ix b && update_gate lv so ix b then
      match sb_kind b, sb_other b with
      | SDoubleUpdate, None => Some (binding_dependencies (Ssa.val_enc (lssa lv)) b)
      | SAddUpdate, Some e | SMulUpdate, Some e =>
        if fst (expression_reference (Ssa.val_enc (lssa lv)) (lbody_c lv)
          (indexed_values ix) so before e)
        then Some (binding_dependencies (Ssa.val_enc (lssa lv)) b) else None
      | _, _ => None
      end
    else None.
Proof.
  unfold binding_reference.
  destruct (binding_gate lv ix b && update_gate lv so ix b); [|reflexivity].
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [sb_kind sb_other binding_dependencies]; try reflexivity.
  all: destruct (fst (expression_reference (Ssa.val_enc (lssa lv)) (lbody_c lv)
    (indexed_values ix) so before e)) eqn:Haccepted; [|reflexivity].
  all: f_equal; apply expression_dependencies_correct; exact Haccepted.
Qed.

(** A binding reference returns the syntax-derived set if and only if its source conditions hold. *)
Theorem binding_conditions_correct {N E V K G C} (lv : loop_view N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (lssa lv))))
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix before b :
  binding_reference lv so ix before b =
    Some (binding_dependencies (Ssa.val_enc (lssa lv)) b) <->
  binding_conditions lv so ix before b.
Proof.
  rewrite binding_dependencies_correct.
  unfold binding_conditions.
  rewrite <- (binding_gate_correct lv HN HV ix b), <- (update_gate_correct lv HV so ix b).
  destruct (binding_gate lv ix b), (update_gate lv so ix b); cbn;
    try (split; [discriminate|intuition discriminate]).
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [sb_kind sb_other]; try (intuition discriminate).
  all: rewrite <- expression_conditions_correct by exact HV.
  all: destruct (fst (expression_reference (Ssa.val_enc (lssa lv)) (lbody_c lv)
    (indexed_values ix) so before e)); intuition discriminate.
Qed.

Local Lemma binding_result_cases {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) ix before b :
  binding_reference lv so ix before b = None \/
  binding_reference lv so ix before b =
    Some (binding_dependencies (Ssa.val_enc (lssa lv)) b).
Proof.
  rewrite binding_dependencies_correct.
  destruct (binding_gate lv ix b && update_gate lv so ix b); [|auto].
  destruct b as [phi base update kind [e|] first]; destruct kind; cbn [sb_kind sb_other]; auto.
  all: destruct (fst (expression_reference (Ssa.val_enc (lssa lv)) (lbody_c lv)
    (indexed_values ix) so before e)); auto.
Qed.

(** * Whole-plan traversal *)

Fixpoint bindings_reference {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix rank (bs : list (scev_binding V)) (checked : list (V * FinSet.t V)) :=
  match bs with
  | [] => Some checked
  | b :: rest =>
    match binding_reference lv so ix (phi_before (Ssa.val_enc (lssa lv)) ix rank) b with
    | None => None
    | Some deps => bindings_reference lv so ix (S rank) rest ((sb_phi b, deps) :: checked)
    end
  end.

Fixpoint check_bindings_c {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix rank (bs : list (scev_binding V)) (checked : list (V * FinSet.t V))
    (m : check_binding_memo V) (expressions : check_memo V)
    : Cost.t ((option (list (V * FinSet.t V)) * check_binding_memo V) * check_memo V) :=
  match bs with
  | [] => Cost.ret ((Some checked, m), expressions)
  | b :: rest =>
    Cost.step ;;
    let* current := scev_check_binding_c lv so ix
      (phi_before_c (Ssa.val_enc (lssa lv)) ix rank) b m expressions in
    let '((result, updated), expressions') := current in
    match result with
    | None => Cost.ret ((None, updated), expressions')
    | Some deps =>
      Cost.step ;;
      check_bindings_c lv so ix (S rank) rest ((sb_phi b, deps) :: checked) updated expressions'
    end
  end.

(** Binding-list conditions describe each source binding at its original ordered position. *)
Fixpoint bindings_conditions {N E V K G C} (lv : loop_view N E V K G) (so : scev_ops K C)
    ix rank (bs : list (scev_binding V)) : Prop :=
  match bs with
  | [] => True
  | b :: rest =>
    binding_conditions lv so ix (phi_before (Ssa.val_enc (lssa lv)) ix rank) b /\
      bindings_conditions lv so ix (S rank) rest
  end.

Definition dependency_rows {V} (EV : encoding V) (bs : list (scev_binding V)) :=
  List.map (fun b => (sb_phi b, binding_dependencies EV b)) bs.

(** Accepted reference rows are exactly the syntax-derived reverse rows under the source conditions. *)
Theorem bindings_conditions_correct {N E V K G C} (lv : loop_view N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (lssa lv))))
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix bs :
  forall rank checked rows,
  bindings_reference lv so ix rank bs checked = Some rows <->
  bindings_conditions lv so ix rank bs /\
    rows = rev (dependency_rows (Ssa.val_enc (lssa lv)) bs) ++ checked.
Proof.
  induction bs as [|b rest IH]; intros rank checked rows.
  - cbn [bindings_reference bindings_conditions dependency_rows List.map rev app].
    split; [intro Heq; split; [exact I|congruence]|intros [_ ->]; reflexivity].
  - cbn [bindings_reference bindings_conditions].
    destruct (binding_result_cases lv so ix
      (phi_before (Ssa.val_enc (lssa lv)) ix rank) b) as [Hnone|Hsome].
    + rewrite Hnone; split; [discriminate|intros [[Hbinding _] _]].
      apply (proj2 (binding_conditions_correct lv HN HV so ix _ b)) in Hbinding.
      congruence.
    + rewrite Hsome, IH.
      assert (Hbinding : binding_conditions lv so ix
        (phi_before (Ssa.val_enc (lssa lv)) ix rank) b).
      { apply binding_conditions_correct; assumption. }
      cbn [dependency_rows List.map rev].
      rewrite <- app_assoc; cbn [app]; tauto.
Qed.

(** Ordered binding checks agree on both full reverse dependency rows and rejected prefixes. *)
Theorem check_bindings_correct {N E V K G C} (lv : loop_view N E V K G)
    (HE : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix bs :
  forall rank checked m expressions, check_binding_valid lv so ix m ->
  check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions ->
  let '((result, updated), expressions') :=
    Cost.value (check_bindings_c lv so ix rank bs checked m expressions) in
  result = bindings_reference lv so ix rank bs checked /\
    check_binding_valid lv so ix updated /\
    check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv) (indexed_values ix) so expressions'.
Proof.
  induction bs as [|b rest IH]; intros rank checked m expressions Hm Hexpressions.
  - split; [reflexivity|split; assumption].
  - pose proof (scev_check_binding_correct lv HE so ix
      (phi_before_c (Ssa.val_enc (lssa lv)) ix rank) b m expressions Hm Hexpressions) as Hhead.
    cbn [check_bindings_c]; autorewrite with galois_cost.
    destruct (Cost.value (scev_check_binding_c lv so ix
      (phi_before_c (Ssa.val_enc (lssa lv)) ix rank) b m expressions))
      as [[[deps|] updated] expressions'];
      destruct Hhead as [Hresult [Hupdated Hexprs]].
    + change (Some deps = binding_reference lv so ix
        (phi_before (Ssa.val_enc (lssa lv)) ix rank) b) in Hresult.
      cbn [bindings_reference]; rewrite <- Hresult; autorewrite with galois_cost.
      apply IH; assumption.
    + change (None = binding_reference lv so ix
        (phi_before (Ssa.val_enc (lssa lv)) ix rank) b) in Hresult.
      cbn [bindings_reference]; rewrite <- Hresult; autorewrite with galois_cost.
      split; [reflexivity|split; assumption].
Qed.

Fixpoint dependencies_c {V} (EV : encoding V) (rows : list (V * FinSet.t V))
    (needed : FinSet.t V) : Cost.t bool :=
  match rows with
  | [] => Cost.ret true
  | (x, deps) :: rest =>
    Cost.step ;;
    let* member := FinSet.mem_c EV x needed in
    if member then
      let* needed' := FinSet.union_c needed deps in
      dependencies_c EV rest needed'
    else Cost.ret false
  end.

(** Connectivity requires each reverse-ordered binding to be needed by the target or a later binding. *)
Fixpoint dependency_chain {V} (EV : encoding V) (rows : list (V * FinSet.t V))
    (needed : FinSet.t V) : Prop :=
  match rows with
  | [] => True
  | (x, deps) :: rest =>
    FinSet.mem EV x needed = true /\ dependency_chain EV rest (FinSet.union needed deps)
  end.

(** Reverse dependency checking decides the independently stated connectivity chain. *)
Theorem dependencies_correct {V} (EV : encoding V) rows needed :
  Cost.value (dependencies_c EV rows needed) = true <-> dependency_chain EV rows needed.
Proof.
  revert needed; induction rows as [|[x deps] rest IH]; intro needed.
  - cbn; tauto.
  - cbn [dependencies_c dependency_chain]; autorewrite with galois_cost.
    fold (FinSet.mem EV x needed).
    destruct (FinSet.mem EV x needed) eqn:Hmember; autorewrite with galois_cost.
    + rewrite IH; tauto.
    + split; [discriminate|intros [Hfalse _]; discriminate].
Qed.

(** Indexed plan execution retains both checker tables even when a structural gate rejects the plan. *)
Definition scev_plan_check_index_c {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) (ix : static_index N V K) (p : scev_plan V) :=
  let EV := Ssa.val_enc (lssa lv) in
  let* bindings := @Memo.empty_c (check_binding_key V) (option (FinSet.t V)) in
  let* expressions := @Memo.empty_c (context_key V bool) (check_result V) in
  let* listed := Map.mem_c EV (sp_target p) (indexed_values ix) in
  if listed && distinct (phi_index ix) then
    match final (phi_index ix) with
    | Some target =>
      let* same := eqb_c EV target (sp_target p) in
      if same then
        let* checked := check_bindings_c lv so ix O (sp_bindings p) [] bindings expressions in
        let '((rows, bindings'), expressions') := checked in
        match rows with
        | None => Cost.ret ((false, bindings'), expressions')
        | Some rows =>
          let* empty := FinSet.empty_c in
          let* target := FinSet.add_c EV (sp_target p) empty in
          Cost.map (fun accepted => ((accepted, bindings'), expressions'))
            (dependencies_c EV rows target)
        end
      else Cost.ret ((false, bindings), expressions)
    | None => Cost.ret ((false, bindings), expressions)
    end
  else Cost.ret ((false, bindings), expressions).

Definition scev_plan_check_c {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) inventory p :=
  let* ix := prepare_index_c lv inventory p in
  Cost.map (fun out => fst (fst out)) (scev_plan_check_index_c lv so ix p).

Definition scev_plan_check {N E V K G C} lv so inventory p :=
  Cost.value (@scev_plan_check_c N E V K G C lv so inventory p).

(** Public checking observes its single prepared-index execution and the tables returned by it. *)
Theorem scev_plan_check_equation {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) inventory p :
  scev_plan_check lv so inventory p =
    fst (fst (Cost.value (scev_plan_check_index_c lv so (prepare_index lv inventory p) p))).
Proof.
  reflexivity.
Qed.

(** Prepared index observations are the original source inventory, incoming lists and plan ranks. *)
Theorem prepare_index_equation {N E V K G} (lv : loop_view N E V K G) inventory p :
  prepare_index lv inventory p =
    Index (scev_inventory_index (lssa lv) inventory)
      (argument_index O (Ssa.args (lssa lv) (lentry lv)))
      (argument_index O (Ssa.args (lssa lv) (lback lv)))
      (prepare_ranks (Ssa.val_enc (lssa lv)) O (sp_bindings p)).
Proof.
  reflexivity.
Qed.

Local Lemma prepare_ranks_mem {V} (EV : encoding V) (HV : encoding_laws EV) bs :
  forall start x, Map.mem EV x (ranks (prepare_ranks EV start bs)) = true <->
    In x (List.map sb_phi bs).
Proof.
  induction bs as [|b rest IH]; intros start x; rewrite prepare_ranks_equation;
    cbn [ranks List.map].
  - rewrite Map.mem_spec; split; [intros [v Hget]; rewrite Map.get_empty in Hget; discriminate|
      contradiction].
  - rewrite Map.mem_spec, Map.get_set_raw.
    destruct (eqb_spec EV HV x (sb_phi b)) as [Hequal|Hdifferent].
    + subst x; split; [intro; left; reflexivity|intro; exists start; reflexivity].
    + rewrite <- Map.mem_spec, IH; cbn [In]; intuition congruence.
Qed.

(** The prepared duplicate flag reflects uniqueness of the actual binding-phi list. *)
Theorem prepare_ranks_distinct {V} (EV : encoding V) (HV : encoding_laws EV) bs :
  forall start, distinct (prepare_ranks EV start bs) = true <->
    NoDup (List.map sb_phi bs).
Proof.
  induction bs as [|b rest IH]; intro start; rewrite prepare_ranks_equation;
    cbn [distinct List.map].
  - split; [intro; constructor|intro; reflexivity].
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, IH.
    split.
    + intros [Hfresh Hdistinct]; constructor; [|exact Hdistinct].
      intro Hin; apply (proj2 (prepare_ranks_mem EV HV rest (S start) (sb_phi b))) in Hin.
      congruence.
    + intro Hnodup; inversion Hnodup as [|phi phis Hfresh Hdistinct]; subst.
      split; [|exact Hdistinct].
      destruct (Map.mem EV (sb_phi b) (ranks (prepare_ranks EV (S start) rest))) eqn:Hmember;
        [|reflexivity].
      apply prepare_ranks_mem in Hmember; [contradiction|exact HV].
Qed.

Fixpoint last_phi {V} (bs : list (scev_binding V)) : option V :=
  match bs with
  | [] => None
  | b :: rest => match last_phi rest with Some x => Some x | None => Some (sb_phi b) end
  end.

(** The final indexed phi is the last phi in the original source-order binding list. *)
Theorem prepare_ranks_final {V} (EV : encoding V) bs :
  forall start, final (prepare_ranks EV start bs) = last_phi bs.
Proof.
  induction bs as [|b rest IH]; intro start; rewrite prepare_ranks_equation;
    cbn [final last_phi]; [reflexivity|rewrite IH; reflexivity].
Qed.

Local Lemma prepare_index_member {N E V K G} (lv : loop_view N E V K G)
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) inventory p x :
  Map.mem (Ssa.val_enc (lssa lv)) x (indexed_values (prepare_index lv inventory p)) = true <->
    In x inventory.
Proof.
  rewrite prepare_index_equation; cbn [indexed_values].
  rewrite Map.mem_spec, scev_inventory_index_get by exact HV.
  assert (Hlisted : existsb (eqb (Ssa.val_enc (lssa lv)) x) inventory = true <-> In x inventory).
  { rewrite existsb_exists; split.
    - intros [y [Hin Heq]]; apply eqb_true_iff in Heq; [subst y; exact Hin|exact HV].
    - intro Hin; exists x; split; [exact Hin|apply eqb_true_iff; [exact HV|reflexivity]]. }
  rewrite <- Hlisted; destruct (existsb _ inventory).
  - split; [intro; reflexivity|intro; eexists; reflexivity].
  - split; [intros [value Hget]; discriminate|discriminate].
Qed.

(** Plan conditions require source membership, unique ordered phis and exact source connectivity. *)
Definition scev_plan_conditions {N E V K G C} (lv : loop_view N E V K G)
    (so : scev_ops K C) inventory (p : scev_plan V) : Prop :=
  let ix := prepare_index lv inventory p in
  In (sp_target p) inventory /\ NoDup (List.map sb_phi (sp_bindings p)) /\
    last_phi (sp_bindings p) = Some (sp_target p) /\
    bindings_conditions lv so ix O (sp_bindings p) /\
    dependency_chain (Ssa.val_enc (lssa lv))
      (rev (dependency_rows (Ssa.val_enc (lssa lv)) (sp_bindings p)))
      (FinSet.add (Ssa.val_enc (lssa lv)) (sp_target p) FinSet.empty).

(** The indexed checker decides target, binding-source and syntax-connectivity conditions. *)
Theorem scev_plan_check_index_correct {N E V K G C} (lv : loop_view N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (lssa lv))))
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) ix p :
  fst (fst (Cost.value (scev_plan_check_index_c lv so ix p))) = true <->
  Map.mem (Ssa.val_enc (lssa lv)) (sp_target p) (indexed_values ix) = true /\
    distinct (phi_index ix) = true /\ final (phi_index ix) = Some (sp_target p) /\
    bindings_conditions lv so ix O (sp_bindings p) /\
    dependency_chain (Ssa.val_enc (lssa lv))
      (rev (dependency_rows (Ssa.val_enc (lssa lv)) (sp_bindings p)))
      (FinSet.add (Ssa.val_enc (lssa lv)) (sp_target p) FinSet.empty).
Proof.
  assert (Hbindings : check_binding_valid lv so ix Memo.empty).
  { split.
    - change (Map.wf (check_binding_encoding (Ssa.val_enc (lssa lv)))
        (@Map.empty (check_binding_key V) (option (FinSet.t V)))); apply Map.wf_empty.
    - apply Memo.valid_empty. }
  assert (Hexpressions : check_valid (Ssa.val_enc (lssa lv)) (lbody_c lv)
      (indexed_values ix) so Memo.empty).
  { split.
    - change (Map.wf (check_encoding (Ssa.val_enc (lssa lv)))
        (@Map.empty (context_key V bool) (check_result V))); apply Map.wf_empty.
    - apply Memo.valid_empty. }
  pose proof (check_bindings_correct lv HV so ix (sp_bindings p) O []
    Memo.empty Memo.empty Hbindings Hexpressions) as Hrun.
  unfold scev_plan_check_index_c; autorewrite with galois_cost.
  fold (@Memo.empty (check_binding_key V) (option (FinSet.t V))).
  fold (@Memo.empty (context_key V bool) (check_result V)).
  fold (Map.mem (Ssa.val_enc (lssa lv)) (sp_target p) (indexed_values ix)).
  destruct (Map.mem _ (sp_target p) (indexed_values ix)), (distinct (phi_index ix));
    cbn; try (intuition discriminate).
  destruct (final (phi_index ix)) as [last|]; [|intuition discriminate].
  autorewrite with galois_cost.
  change (Cost.value (eqb_c (Ssa.val_enc (lssa lv)) last (sp_target p)))
    with (eqb (Ssa.val_enc (lssa lv)) last (sp_target p)).
  destruct (eqb_spec _ HV last (sp_target p)) as [Hequal|Hdifferent];
    [subst last|autorewrite with galois_cost; cbn [fst]; intuition congruence].
  autorewrite with galois_cost.
  destruct (Cost.value (check_bindings_c lv so ix O (sp_bindings p) []
    Memo.empty Memo.empty)) as [[rows bindings] expressions].
  destruct Hrun as [Hrows _]; destruct rows as [rows|].
  - autorewrite with galois_cost.
    assert (Hsource : bindings_conditions lv so ix O (sp_bindings p) /\
      rows = rev (dependency_rows (Ssa.val_enc (lssa lv)) (sp_bindings p))).
    { symmetry in Hrows.
      apply (proj1 (bindings_conditions_correct lv HN HV so ix (sp_bindings p)
        O [] rows)) in Hrows.
      destruct Hrows as [Hsource Hrows]; rewrite app_nil_r in Hrows; auto. }
    destruct Hsource as [Hsource ->].
    cbn [fst]; fold (@FinSet.empty V).
    rewrite dependencies_correct; intuition.
  - autorewrite with galois_cost; split; [discriminate|].
    intros [_ [_ [_ [Hsource _]]]].
    assert (Hsome : bindings_reference lv so ix O (sp_bindings p) [] =
      Some (rev (dependency_rows (Ssa.val_enc (lssa lv)) (sp_bindings p)))).
    { apply bindings_conditions_correct; [exact HN|exact HV|].
      split; [exact Hsource|symmetry; apply app_nil_r]. }
    congruence.
Qed.

(** Public plan checking decides independent source, uniqueness and target-connectivity conditions. *)
Theorem scev_plan_check_correct {N E V K G C} (lv : loop_view N E V K G)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (lssa lv))))
    (HV : encoding_laws (Ssa.val_enc (lssa lv))) (so : scev_ops K C) inventory p :
  scev_plan_check lv so inventory p = true <-> scev_plan_conditions lv so inventory p.
Proof.
  unfold scev_plan_check, scev_plan_check_c; autorewrite with galois_cost.
  fold (prepare_index lv inventory p).
  rewrite scev_plan_check_index_correct by assumption.
  unfold scev_plan_conditions.
  rewrite prepare_index_member by exact HV.
  rewrite prepare_index_equation at 1 2; cbn [phi_index].
  rewrite prepare_ranks_distinct by exact HV.
  rewrite prepare_ranks_final; reflexivity.
Qed.

End PlanCheck.
