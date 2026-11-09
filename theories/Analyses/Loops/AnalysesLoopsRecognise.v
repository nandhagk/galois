(** * Prepared scalar-evolution recognition

    Recognition separates source syntax, prepared inventories and context-sensitive Memo queries.
    For example, a completed phi can be reused after an unrelated environment binding is added.
    Builds on: AnalysesLoopsChrec, AnalysesLoopsIdioms, BaseMemo and ProgramSsa. *)

From Stdlib Require Import List Bool Arith NArith ZArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseMemo BasePrepared.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec AnalysesLoopsIdioms.
Import List.ListNotations Cost.Notations Chrec.

Module Recognise.

(** A loop test fixes the observed phi, bound, comparison and signedness. *)
Record loop_test (V : Type) : Type := LoopTest {
  t_cmp : cmp_kind;
  t_sign : signedness;
  t_lhs : V;
  t_bound : iexpr V
}.
Arguments LoopTest {V}.
Arguments t_cmp {V}.
Arguments t_sign {V}.
Arguments t_lhs {V}.
Arguments t_bound {V}.

(** Loop presentations contain computational source readers and no semantic links. *)
Record loop_view (N E V K G : Type) : Type := LoopView {
  lssa : Ssa.t N E V K G;
  lheader : N;
  lbody_c : N -> Cost.t bool;
  lentry : E;
  lback : E;
  ltest : option (loop_test V)
}.
Arguments LoopView {N E V K G}.
Arguments lssa {N E V K G}.
Arguments lheader {N E V K G}.
Arguments lbody_c {N E V K G}.
Arguments lentry {N E V K G}.
Arguments lback {N E V K G}.
Arguments ltest {N E V K G}.

Definition lbody {N E V K G} (lv : loop_view N E V K G) n :=
  Cost.value (lbody_c lv n).

(** Recognition flags and word observations retain their client callback charges. *)
Record scev_ops (K C : Type) : Type := ScevOps {
  width_of : positive;
  to_Z_c : C -> Cost.t Z;
  add_op_c : K -> Cost.t bool;
  mul_op_c : K -> Cost.t bool;
  const_op_c : K -> Cost.t (option Z)
}.
Arguments ScevOps {K C}.
Arguments width_of {K C}.
Arguments to_Z_c {K C}.
Arguments add_op_c {K C}.
Arguments mul_op_c {K C}.
Arguments const_op_c {K C}.

Definition to_Z {K C} (so : scev_ops K C) c := Cost.value (to_Z_c so c).
Definition add_op {K C} (so : scev_ops K C) o := Cost.value (add_op_c so o).
Definition mul_op {K C} (so : scev_ops K C) o := Cost.value (mul_op_c so o).
Definition const_op {K C} (so : scev_ops K C) o := Cost.value (const_op_c so o).

(** Pure client primitives have an explicit one-tick lifting boundary. *)
Definition ops_of_pure {K C} w (observe : C -> Z) add mul literal : scev_ops K C :=
  ScevOps w (Cost.lift (fun _ => 1%N) observe)
    (Cost.lift (fun _ => 1%N) add) (Cost.lift (fun _ => 1%N) mul)
    (Cost.lift (fun _ => 1%N) literal).

(** Source expressions retain result identities and ordered operands. *)
Inductive scev_expr (V : Type) : Type :=
  | SOutside (x : V)
  | SPhi (x : V)
  | SAdd (x : V) (a b : scev_expr V)
  | SMul (x : V) (a b : scev_expr V)
  | SConst (x : V) (z : Z).
Arguments SOutside {V}.
Arguments SPhi {V}.
Arguments SAdd {V}.
Arguments SMul {V}.
Arguments SConst {V}.

(** Binding kinds use the single update table's closed set of supported shapes. *)
Definition scev_update := Idiom.kind.
Abbreviation SAddUpdate := Idiom.SAdd.
Abbreviation SMulUpdate := Idiom.SMul.
Abbreviation SDoubleUpdate := Idiom.SDouble.

Record scev_binding (V : Type) : Type := ScevBinding {
  sb_phi : V;
  sb_base : V;
  sb_update_value : V;
  sb_kind : scev_update;
  sb_other : option (scev_expr V);
  sb_phi_first : bool
}.
Arguments ScevBinding {V}.
Arguments sb_phi {V}.
Arguments sb_base {V}.
Arguments sb_update_value {V}.
Arguments sb_kind {V}.
Arguments sb_other {V}.
Arguments sb_phi_first {V}.

(** Plans order completed phi dependencies before their users and finish at their target. *)
Record scev_plan (V : Type) : Type := ScevPlan {
  sp_bindings : list (scev_binding V);
  sp_target : V
}.
Arguments ScevPlan {V}.
Arguments sp_bindings {V}.
Arguments sp_target {V}.

Definition scev_expr_root {V} (e : scev_expr V) : V :=
  match e with
  | SOutside x | SPhi x | SAdd x _ _ | SMul x _ _ | SConst x _ => x
  end.

Fixpoint scev_expression_phis {V} (e : scev_expr V) : list V :=
  match e with
  | SPhi x => [x]
  | SAdd _ a b | SMul _ a b => scev_expression_phis a ++ scev_expression_phis b
  | _ => []
  end.

Fixpoint scev_expr_operations {V} (e : scev_expr V) : list V :=
  match e with
  | SAdd x a b | SMul x a b => x :: scev_expr_operations a ++ scev_expr_operations b
  | SConst x _ => [x]
  | _ => []
  end.

Definition scev_binding_phis {V} (b : scev_binding V) : list V :=
  match sb_other b with Some e => scev_expression_phis e | None => [] end.

Definition scev_plan_operations {V} (p : scev_plan V) : list V :=
  flat_map (fun b => sb_update_value b ::
    match sb_other b with Some e => scev_expr_operations e | None => [] end) (sp_bindings p).

(** A miss threads the same shared table through its actual recursive child computations. *)
Definition memo_result K R S := ((R * Memo.t K R) * S)%type.

Definition memo_run_c {K R S} (key : PreparedKey.t K)
    (miss_c : Memo.t K R -> S -> Cost.t (memo_result K R S))
    (table : Memo.t K R) (side : S) : Cost.t (memo_result K R S * bool) :=
  let* old := PreparedKey.get_c key table in
  match old with
  | Some result => Cost.ret (((result, table), side), true)
  | None =>
    Cost.step ;;
    let* fresh := miss_c table side in
    let '((result, updated), side') := fresh in
    let* stored := PreparedKey.set_c key result updated in
    Cost.ret (((result, stored), side'), false)
  end.

(** Common agreement includes returned data, table validity and the threaded side-state invariant. *)
Definition memo_result_valid {K R S} (E : encoding K) (reference : K -> R)
    (P : S -> Prop) (key : K) (result : memo_result K R S) : Prop :=
  let '((value, table), side) := result in
  value = reference key /\ Map.wf E table /\ Memo.valid E reference table /\ P side.

(** Prepared Memo execution has one agreement contract for all four recognition applications. *)
Theorem memo_run_agrees {K R S} (E : encoding K) (HE : encoding_laws E)
    (reference : K -> R) (P : S -> Prop) key miss_c table side :
  PreparedKey.valid E key -> Map.wf E table -> Memo.valid E reference table -> P side ->
  (forall m s, Map.wf E m -> Memo.valid E reference m -> P s ->
    memo_result_valid E reference P (PreparedKey.key key) (Cost.value (miss_c m s))) ->
  memo_result_valid E reference P (PreparedKey.key key)
    (fst (Cost.value (memo_run_c key miss_c table side))).
Proof.
  intros Hkey Hwf Hvalid Hside Hmiss.
  unfold memo_run_c; rewrite Cost.value_bind.
  fold (PreparedKey.get key table).
  rewrite (PreparedKey.prepared_get_agrees E key table Hkey).
  destruct (Map.get E (PreparedKey.key key) table) as [value|] eqn:Hget.
  - rewrite Cost.value_ret.
    split; [exact (Hvalid _ _ Hget)|]; repeat split; assumption.
  - specialize (Hmiss table side Hwf Hvalid Hside).
    autorewrite with galois_cost.
    destruct (Cost.value (miss_c table side)) as [[value updated] side'].
    autorewrite with galois_cost.
    destruct Hmiss as [Hvalue [Hupdated [Hreference Hside']]].
    cbn [fst memo_result_valid].
    fold (PreparedKey.set key value updated).
    rewrite (proj1 (PreparedKey.prepared_update_agrees E key value updated Hkey)).
    split; [exact Hvalue|]; split; [apply Map.wf_set; exact Hupdated|].
    split; [|exact Hside'].
    intros k found Hfound; rewrite Map.get_set in Hfound by exact Hupdated.
    destruct (eqb_spec E HE k (PreparedKey.key key)) as [Heq|Hdifferent].
    + subst k; injection Hfound as Heq; subst found; exact Hvalue.
    + exact (Hreference k found Hfound).
Qed.

Local Lemma memo_result_forget_side {K R S} E reference P key
    (result : memo_result K R S) :
  memo_result_valid E reference P key result ->
  let '((value, table), _) := result in
  value = reference key /\ Map.wf E table /\ Memo.valid E reference table.
Proof.
  destruct result as [[value table] side].
  intros [Hvalue [Hwf [Hvalid _]]]; repeat split; assumption.
Qed.

(** Reference translation interprets precisely the declared expression tree. *)
Fixpoint scev_translate_expr {V} (lookup : V -> option (Chrec.t V)) (e : scev_expr V)
    : option (Chrec.t V) :=
  match e with
  | SOutside x => Some (CInv (IVar x))
  | SPhi x => lookup x
  | SConst _ z => Some (CInv (IWordConst z))
  | SAdd _ a b =>
    match scev_translate_expr lookup a, scev_translate_expr lookup b with
    | Some ca, Some cb => Some (chrec_add ca cb)
    | _, _ => None
    end
  | SMul _ a b =>
    match scev_translate_expr lookup a, scev_translate_expr lookup b with
    | Some ca, Some cb => Some (chrec_mul ca cb)
    | _, _ => None
    end
  end.

(** Binding translation dispatches every supported update through the actual idiom table. *)
Definition scev_translate_binding {V} (lookup : V -> option (Chrec.t V)) (b : scev_binding V)
    : option (Chrec.t V) :=
  match sb_kind b, sb_other b with
  | SDoubleUpdate, None => Idiom.apply SDoubleUpdate (CInv (IVar (sb_base b))) None
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    match scev_translate_expr lookup e with
    | Some other => Idiom.apply (sb_kind b) (CInv (IVar (sb_base b))) (Some other)
    | None => None
    end
  | _, _ => None
  end.

(** * Charged structural keys *)

(** Structural keys distinguish operand order, source identities and tagged literals. *)
Fixpoint scev_expr_code_c {V} (EV : encoding V) (e : scev_expr V)
    : Cost.t positive :=
  Cost.step ;;
  match e with
  | SOutside x =>
    Cost.step ;;
    let* p := encode_c EV x in
    Cost.step ;;
    encode_c (codec_enc (list_codec positive_codec)) [1%positive; p]
  | SPhi x =>
    Cost.step ;;
    let* p := encode_c EV x in
    Cost.step ;;
    encode_c (codec_enc (list_codec positive_codec)) [2%positive; p]
  | SAdd x a b | SMul x a b =>
    Cost.step ;;
    let* p := encode_c EV x in
    let* ca := scev_expr_code_c EV a in
    let* cb := scev_expr_code_c EV b in
    let tag := match e with SAdd _ _ _ => 3%positive | _ => 4%positive end in
    Cost.step ;;
    encode_c (codec_enc (list_codec positive_codec)) [tag; p; ca; cb]
  | SConst x z =>
    Cost.step ;;
    let* p := encode_c EV x in
    Cost.step ;;
    let* literal := encode_c Z_encoding z in
    Cost.step ;;
    encode_c (codec_enc (list_codec positive_codec)) [5%positive; p; literal]
  end.

Definition scev_expr_code {V} (EV : encoding V) e := Cost.value (scev_expr_code_c EV e).

Definition scev_expr_encoding {V} (EV : encoding V) : encoding (scev_expr V) :=
  Encoding (scev_expr_code_c EV).

(** The key equation exposes constructor tags without exposing the serializer implementation. *)
Theorem scev_expr_code_equation {V} (EV : encoding V) e :
  scev_expr_code EV e =
  encode (codec_enc (list_codec positive_codec))
    (match e with
    | SOutside x => [1%positive; encode EV x]
    | SPhi x => [2%positive; encode EV x]
    | SAdd x a b => [3%positive; encode EV x; scev_expr_code EV a; scev_expr_code EV b]
    | SMul x a b => [4%positive; encode EV x; scev_expr_code EV a; scev_expr_code EV b]
    | SConst x z => [5%positive; encode EV x; encode Z_encoding z]
    end).
Proof.
  destruct e; reflexivity.
Qed.

(** Lawful value encodings make complete structural expression keys injective. *)
Theorem scev_expr_encoding_laws {V} (EV : encoding V) :
  encoding_laws EV -> encoding_laws (scev_expr_encoding EV).
Proof.
  intro HE; constructor.
  change (forall a b, scev_expr_code EV a = scev_expr_code EV b -> a = b).
  induction a as [x|x|x a IHa b IHb|x a IHa b IHb|x z];
    intros other Hcode; rewrite (scev_expr_code_equation EV other) in Hcode;
    destruct other; rewrite scev_expr_code_equation in Hcode;
    apply (encode_injective
      (codec_laws_injective _ (list_codec_laws _ positive_codec_laws))) in Hcode;
    inversion Hcode; subst; f_equal;
    first [apply (encode_injective HE); assumption |
      apply (encode_injective Z_encoding_laws); assumption |
      apply IHa; assumption | apply IHb; assumption].
Qed.

(** * Support-sensitive query keys *)

Definition tree_encoding {A} (tree_c : A -> Cost.t code) : encoding A :=
  Encoding (fun a => Cost.step ;; let* tree := tree_c a in code_encode_c tree).

Local Lemma tree_encoding_injective {A} (tree_c : A -> Cost.t code) :
  (forall a b, Cost.value (tree_c a) = Cost.value (tree_c b) -> a = b) ->
  encoding_laws (tree_encoding tree_c).
Proof.
  intro Hinjective; constructor; intros a b Hcode.
  change (code_encode (Cost.value (tree_c a)) =
    code_encode (Cost.value (tree_c b))) in Hcode.
  apply (f_equal code_decode) in Hcode.
  rewrite !code_decode_encode in Hcode.
  apply Hinjective; congruence.
Qed.

Fixpoint iexpr_tree_c {V} (EV : encoding V) (e : iexpr V) : Cost.t code :=
  Cost.step ;;
  match e with
  | IVar x =>
    Cost.step ;;
    let* p := encode_c EV x in Cost.ret (Node [Atom 1; Atom p])
  | IConst z | IWordConst z =>
    Cost.step ;;
    let* p := encode_c Z_encoding z in
    Cost.ret (Node [Atom (match e with IConst _ => 2 | _ => 3 end); Atom p])
  | IAdd a b | IMul a b =>
    let* ca := iexpr_tree_c EV a in
    let* cb := iexpr_tree_c EV b in
    Cost.ret (Node [Atom (match e with IAdd _ _ => 4 | _ => 5 end); ca; cb])
  end.

Local Lemma iexpr_tree_injective {V} (EV : encoding V) (HE : encoding_laws EV) a :
  forall b, Cost.value (iexpr_tree_c EV a) = Cost.value (iexpr_tree_c EV b) -> a = b.
Proof.
  induction a as [x|z|z|a IHa b IHb|a IHa b IHb]; intros other Hcode;
    destruct other; cbn [iexpr_tree_c] in Hcode;
    autorewrite with galois_cost in Hcode; inversion Hcode; subst; f_equal;
    first [apply (encode_injective HE); assumption |
      apply (encode_injective Z_encoding_laws); assumption |
      apply IHa; assumption | apply IHb; assumption].
Qed.

Fixpoint chrec_tree_c {V} (EV : encoding V) (c : Chrec.t V) : Cost.t code :=
  Cost.step ;;
  match c with
  | CInv e => Cost.map (fun tree => Node [Atom 1; tree]) (iexpr_tree_c EV e)
  | CRec a b | CGeo a b | CSum a b | CProduct a b =>
    let* ca := chrec_tree_c EV a in
    let* cb := chrec_tree_c EV b in
    Cost.ret (Node [Atom
      (match c with CRec _ _ => 2 | CGeo _ _ => 3 | CSum _ _ => 4 | _ => 5 end); ca; cb])
  end.

Local Lemma chrec_tree_injective {V} (EV : encoding V) (HE : encoding_laws EV) a :
  forall b, Cost.value (chrec_tree_c EV a) = Cost.value (chrec_tree_c EV b) -> a = b.
Proof.
  induction a as [e|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa b IHb];
    intros other Hcode; destruct other; cbn [chrec_tree_c] in Hcode;
    autorewrite with galois_cost in Hcode; inversion Hcode; subst; f_equal;
    first [eapply iexpr_tree_injective; eassumption |
      apply IHa; assumption | apply IHb; assumption].
Qed.

Definition chrec_encoding {V} (EV : encoding V) := tree_encoding (chrec_tree_c EV).

(** Entire recurrence syntax, including coefficients and tagged words, participates in cache keys. *)
Theorem chrec_encoding_laws {V} (EV : encoding V) :
  encoding_laws EV -> encoding_laws (chrec_encoding EV).
Proof.
  intro HE; apply tree_encoding_injective; apply chrec_tree_injective; exact HE.
Qed.

Definition optional_chrec_encoding {V} (EV : encoding V) : encoding (option (Chrec.t V)) :=
  tree_encoding (fun c =>
    match c with
    | None => Cost.ret (Node [])
    | Some c => Cost.map (fun tree => Node [tree]) (chrec_tree_c EV c)
    end).

Local Lemma optional_chrec_encoding_laws {V} (EV : encoding V) :
  encoding_laws EV -> encoding_laws (optional_chrec_encoding EV).
Proof.
  intro HE; apply tree_encoding_injective; intros [a|] [b|] Hcode;
    autorewrite with galois_cost in Hcode; try discriminate; [|reflexivity].
  injection Hcode as Htree; f_equal; eapply chrec_tree_injective; eassumption.
Qed.

Definition list_key_encoding {A} (EA : encoding A) : encoding (list A) :=
  tree_encoding (fun xs =>
    Cost.map Node (map_c (fun x =>
      Cost.step ;; Cost.map Atom (encode_c EA x)) xs)).

Local Lemma list_key_encoding_laws {A} (EA : encoding A) :
  encoding_laws EA -> encoding_laws (list_key_encoding EA).
Proof.
  intro HE; apply tree_encoding_injective; intros xs ys Hcode.
  rewrite !Cost.value_map, !value_map_c in Hcode.
  autorewrite with galois_cost in Hcode.
  injection Hcode as Hlist; revert ys Hlist.
  induction xs as [|x xs IH]; intros [|y ys] Hlist; try discriminate; [reflexivity|].
  injection Hlist as Hhead Htail.
  f_equal.
  - apply (encode_injective HE); exact Hhead.
  - apply IH; exact Htail.
Qed.

(** A context key keeps only the observations at phi leaves, including missing values. *)
Definition context_key V A := (scev_expr V * list (V * A))%type.

Definition context_encoding {V A} (EV : encoding V) (EA : encoding A) :=
  pair_encoding (scev_expr_encoding EV) (list_key_encoding (pair_encoding EV EA)).

Local Lemma context_encoding_laws {V A} (EV : encoding V) (EA : encoding A) :
  encoding_laws EV -> encoding_laws EA -> encoding_laws (context_encoding EV EA).
Proof.
  intros HE HA; apply pair_encoding_laws.
  - apply scev_expr_encoding_laws; exact HE.
  - apply list_key_encoding_laws, pair_encoding_laws; assumption.
Qed.

Fixpoint context_lookup {V A} (EV : encoding V) (default : A) (entries : list (V * A))
    (x : V) : A :=
  match entries with
  | [] => default
  | (y, value) :: rest =>
    if eqb EV x y then value else context_lookup EV default rest x
  end.

Fixpoint expression_phis_c {V} (e : scev_expr V) : Cost.t (list V) :=
  Cost.step ;;
  match e with
  | SPhi x => Cost.ret [x]
  | SAdd _ a b | SMul _ a b =>
    let* pa := expression_phis_c a in
    let* pb := expression_phis_c b in
    app_c pa pb
  | _ => Cost.ret []
  end.

Local Lemma expression_phis_value {V} (e : scev_expr V) :
  Cost.value (expression_phis_c e) = scev_expression_phis e.
Proof.
  induction e; cbn [expression_phis_c scev_expression_phis];
    autorewrite with galois_cost; rewrite ?value_app_c, ?IHe1, ?IHe2; reflexivity.
Qed.

Definition context_prepare_c {V A} (EV : encoding V) (EA : encoding A)
    (observe_c : V -> Cost.t A) (e : scev_expr V) : Cost.t (PreparedKey.t (context_key V A)) :=
  let* phis := expression_phis_c e in
  let* entries := map_c (fun x =>
    Cost.step ;;
    Cost.map (fun value => (x, value)) (observe_c x)) phis in
  PreparedKey.prepare_c (context_encoding EV EA) (e, entries).

Local Lemma context_prepare_value {V A} (EV : encoding V) (EA : encoding A)
    (observe_c : V -> Cost.t A) e :
  Cost.value (context_prepare_c EV EA observe_c e) =
    PreparedKey.prepare (context_encoding EV EA)
      (e, List.map (fun x => (x, Cost.value (observe_c x))) (scev_expression_phis e)).
Proof.
  unfold context_prepare_c; autorewrite with galois_cost.
  rewrite expression_phis_value; reflexivity.
Qed.

Local Lemma context_lookup_project {V A} (EV : encoding V) (HE : encoding_laws EV)
    (default : A) (observe : V -> A) xs x :
  In x xs ->
  context_lookup EV default (List.map (fun y => (y, observe y)) xs) x = observe x.
Proof.
  induction xs as [|y rest IH]; [contradiction|].
  intro Hin; cbn [List.map context_lookup].
  destruct (eqb_spec EV HE x y) as [Hequal|Hdifferent].
  - subst y; reflexivity.
  - apply IH; destruct Hin as [Hequal|Hin]; [congruence|exact Hin].
Qed.

(** Translation observes exactly its phi support, so unrelated context entries cannot affect it. *)
Theorem scev_translate_expr_support {V} (a b : V -> option (Chrec.t V)) e :
  (forall x, In x (scev_expression_phis e) -> a x = b x) ->
  scev_translate_expr a e = scev_translate_expr b e.
Proof.
  induction e as [x|x|x l IHl r IHr|x l IHl r IHr|x z]; intro Hagree;
    cbn [scev_translate_expr]; try reflexivity.
  - apply Hagree; left; reflexivity.
  - rewrite IHl, IHr; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; auto.
  - rewrite IHl, IHr; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; auto.
Qed.

(** Unchanged observations at phi leaves give the same complete key under any outside changes. *)
Theorem context_projection_agrees {V A} (a b : V -> A) (e : scev_expr V) :
  (forall x, In x (scev_expression_phis e) -> a x = b x) ->
  List.map (fun x => (x, a x)) (scev_expression_phis e) =
    List.map (fun x => (x, b x)) (scev_expression_phis e).
Proof.
  intro Hagree; apply map_ext_in; intros x Hin; rewrite Hagree by exact Hin; reflexivity.
Qed.

Fixpoint expression_nodes {V} (e : scev_expr V) : N :=
  match e with
  | SAdd _ a b | SMul _ a b => (1 + expression_nodes a + expression_nodes b)%N
  | _ => 1%N
  end.

Local Lemma expression_phis_length {V} (e : scev_expr V) :
  (N.of_nat (length (scev_expression_phis e)) <= expression_nodes e)%N.
Proof.
  induction e; cbn [scev_expression_phis expression_nodes length]; try lia;
    rewrite length_app, Nat2N.inj_add; nia.
Qed.

(** The support traversal pays for every copied list cell, including duplicated phi occurrences. *)
Theorem expression_phis_cost {V} (e : scev_expr V) :
  (Cost.ticks (expression_phis_c e) <= expression_nodes e * expression_nodes e)%N.
Proof.
  induction e; cbn [expression_phis_c expression_nodes];
    autorewrite with galois_cost; try reflexivity;
    rewrite !expression_phis_value;
    pose proof (expression_phis_length e1); nia.
Qed.

(** * Memo-threaded expression compilation *)

Definition compile_key V := context_key V (option (Chrec.t V)).

Definition compile_encoding {V} (EV : encoding V) :=
  context_encoding EV (optional_chrec_encoding EV).

Definition compile_query {V} (lookup : V -> option (Chrec.t V)) e : compile_key V :=
  (e, List.map (fun x => (x, lookup x)) (scev_expression_phis e)).

Definition compile_reference {V} (EV : encoding V) (query : compile_key V) :=
  scev_translate_expr (context_lookup EV None (snd query)) (fst query).

Local Lemma compile_query_reference {V} (EV : encoding V) (HE : encoding_laws EV)
    lookup e :
  compile_reference EV (compile_query lookup e) = scev_translate_expr lookup e.
Proof.
  unfold compile_reference, compile_query; cbn [fst snd].
  apply scev_translate_expr_support; intros x Hin.
  apply context_lookup_project; assumption.
Qed.

Definition compile_memo V := Memo.t (compile_key V) (option (Chrec.t V)).

(** Context-keyed validity is independent of the current environment. *)
Definition compile_valid {V} (EV : encoding V) (m : compile_memo V) : Prop :=
  Map.wf (compile_encoding EV) m /\ Memo.valid (compile_encoding EV) (compile_reference EV) m.

Definition compile_result {V} := memo_result (compile_key V) (option (Chrec.t V)) unit.

(** Expression results couple the current translation to validity of the same returned table. *)
Definition compile_expr_result_valid {V} (EV : encoding V) lookup e
    (result : @compile_result V) : Prop :=
  let '((value, table), _) := result in
  value = scev_translate_expr lookup e /\ compile_valid EV table.

Definition compile_pair_c {V}
    (combine_c : Chrec.t V -> Chrec.t V -> Cost.t (Chrec.t V))
    (recurse_a recurse_b : compile_memo V -> Cost.t (@compile_result V))
    (m : compile_memo V) : Cost.t (@compile_result V) :=
  let* first := recurse_a m in
  let '((ca, ma), _) := first in
  match ca with
  | None => Cost.ret ((None, ma), tt)
  | Some a =>
    let* second := recurse_b ma in
    let '((cb, mb), _) := second in
    match cb with
    | None => Cost.ret ((None, mb), tt)
    | Some b =>
      Cost.step ;;
      let* result := combine_c a b in
      Cost.ret ((Some result, mb), tt)
    end
  end.

(** Every recursive miss receives the table returned by the preceding child. *)
Fixpoint scev_compile_expr_c {V} (EV : encoding V)
    (lookup_c : V -> Cost.t (option (Chrec.t V))) (e : scev_expr V)
    (m : compile_memo V) : Cost.t (@compile_result V) :=
  Cost.step ;;
  let* key := context_prepare_c EV (optional_chrec_encoding EV) lookup_c e in
  let* result := memo_run_c key (fun table side =>
    match e with
    | SOutside x => Cost.ret ((Some (CInv (IVar x)), table), side)
    | SPhi x =>
      Cost.step ;;
      let* found := lookup_c x in
      Cost.ret ((found, table), side)
    | SConst _ z => Cost.ret ((Some (CInv (IWordConst z)), table), side)
    | SAdd _ a b =>
      compile_pair_c chrec_add_c (scev_compile_expr_c EV lookup_c a)
        (scev_compile_expr_c EV lookup_c b) table
    | SMul _ a b =>
      compile_pair_c chrec_mul_c (scev_compile_expr_c EV lookup_c a)
        (scev_compile_expr_c EV lookup_c b) table
    end) m tt in
  Cost.ret (fst result).

Definition scev_compile_expr {V} (EV : encoding V) lookup_c e m :=
  Cost.value (@scev_compile_expr_c V EV lookup_c e m).

Local Lemma compile_pair_correct {V} (EV : encoding V)
    (lookup : V -> option (Chrec.t V)) combine_c combine a b ra rb m :
  (forall x y, Cost.value (combine_c x y) = combine x y) ->
  (forall table, compile_valid EV table ->
    compile_expr_result_valid EV lookup a (Cost.value (ra table))) ->
  (forall table, compile_valid EV table ->
    compile_expr_result_valid EV lookup b (Cost.value (rb table))) ->
  compile_valid EV m ->
  let '((result, table), _) := Cost.value (compile_pair_c combine_c ra rb m) in
  result =
    match scev_translate_expr lookup a, scev_translate_expr lookup b with
    | Some ca, Some cb => Some (combine ca cb)
    | _, _ => None
    end /\ compile_valid EV table.
Proof.
  intros Hcombine Ha Hb Hm.
  specialize (Ha m Hm).
  unfold compile_pair_c; autorewrite with galois_cost.
  destruct (Cost.value (ra m)) as [[[ca|] ma] []];
    destruct Ha as [Hca [Hwf Hvalid]].
  - specialize (Hb ma (conj Hwf Hvalid)).
    autorewrite with galois_cost.
    destruct (Cost.value (rb ma)) as [[[cb|] mb] []];
      destruct Hb as [Hcb [Hwf' Hvalid']]; autorewrite with galois_cost;
      cbn [fst snd]; rewrite <- Hca, <- Hcb.
    + split.
      * cbn; rewrite Hcombine; reflexivity.
      * exact (conj Hwf' Hvalid').
    + split; [reflexivity|exact (conj Hwf' Hvalid')].
  - autorewrite with galois_cost.
    rewrite <- Hca; split; [reflexivity|exact (conj Hwf Hvalid)].
Qed.

(** Compilation returns the full reference option and maintains the recursively shared Memo. *)
Theorem scev_compile_expr_correct {V} (EV : encoding V) (HE : encoding_laws EV)
    (lookup_c : V -> Cost.t (option (Chrec.t V))) e m :
  compile_valid EV m ->
  compile_expr_result_valid EV (fun x => Cost.value (lookup_c x))
    e (scev_compile_expr EV lookup_c e m).
Proof.
  assert (Hencoding : encoding_laws (compile_encoding EV)).
  { apply context_encoding_laws; [exact HE|apply optional_chrec_encoding_laws; exact HE]. }
  revert m; induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z];
    intros m [Hwf Hvalid]; unfold scev_compile_expr at 1;
    cbn [scev_compile_expr_c]; autorewrite with galois_cost;
    rewrite context_prepare_value.
  all: match goal with
  | |- compile_expr_result_valid _ ?lookup ?source ?result =>
    let Href := fresh "Hquery" in
    pose proof (compile_query_reference EV HE lookup source) as Href;
    unfold compile_expr_result_valid;
    rewrite <- Href;
    apply (memo_result_forget_side (compile_encoding EV) (compile_reference EV)
      (fun _ : unit => True) (compile_query lookup source) result)
  end.
  all: eapply memo_run_agrees;
    [exact Hencoding | apply PreparedKey.prepare_valid | exact Hwf | exact Hvalid | exact I |].
  all: intros table [] Htable Hreference _.
  all: rewrite PreparedKey.prepare_key; unfold memo_result_valid.
  - split; [symmetry; exact Hquery|]; repeat split; assumption.
  - autorewrite with galois_cost.
    split; [symmetry; exact Hquery|]; repeat split; assumption.
  - pose proof (compile_pair_correct EV _ chrec_add_c chrec_add a b
      (scev_compile_expr_c EV lookup_c a) (scev_compile_expr_c EV lookup_c b) table
      (fun _ _ => eq_refl) IHa IHb (conj Htable Hreference)) as Hpair.
    destruct (Cost.value (compile_pair_c chrec_add_c
      (scev_compile_expr_c EV lookup_c a) (scev_compile_expr_c EV lookup_c b) table))
      as [[result updated] []].
    destruct Hpair as [Hresult [Hupdated Hmeaning]].
    split; [etransitivity; [exact Hresult|symmetry; exact Hquery]|].
    repeat split; assumption.
  - pose proof (compile_pair_correct EV _ chrec_mul_c chrec_mul a b
      (scev_compile_expr_c EV lookup_c a) (scev_compile_expr_c EV lookup_c b) table
      (fun _ _ => eq_refl) IHa IHb (conj Htable Hreference)) as Hpair.
    destruct (Cost.value (compile_pair_c chrec_mul_c
      (scev_compile_expr_c EV lookup_c a) (scev_compile_expr_c EV lookup_c b) table))
      as [[result updated] []].
    destruct Hpair as [Hresult [Hupdated Hmeaning]].
    split; [etransitivity; [exact Hresult|symmetry; exact Hquery]|].
    repeat split; assumption.
  - split; [symmetry; exact Hquery|]; repeat split; assumption.
Qed.

(** * Memo-threaded binding and plan compilation *)

Definition binding_tree_c {V} (EV : encoding V) (b : scev_binding V) : Cost.t code :=
  Cost.step ;;
  Cost.step ;;
  let* phi := encode_c EV (sb_phi b) in
  Cost.step ;;
  let* base := encode_c EV (sb_base b) in
  Cost.step ;;
  let* update := encode_c EV (sb_update_value b) in
  let* other :=
    match sb_other b with
    | None => Cost.ret (Node [])
    | Some e => Cost.map (fun p => Node [Atom p]) (scev_expr_code_c EV e)
    end in
  let kind : positive :=
    match sb_kind b with
    | SAddUpdate => 1%positive
    | SMulUpdate => 2%positive
    | SDoubleUpdate => 3%positive
    end in
  Cost.ret (Node [Atom phi; Atom base; Atom update; Atom kind; other;
    Atom (if sb_phi_first b then 1 else 2)]).

Definition binding_encoding {V} (EV : encoding V) := tree_encoding (binding_tree_c EV).

Local Lemma binding_encoding_laws {V} (EV : encoding V) :
  encoding_laws EV -> encoding_laws (binding_encoding EV).
Proof.
  intro HE; apply tree_encoding_injective.
  intros [phi base update kind other first] [phi' base' update' kind' other' first'] Hcode.
  destruct kind, kind', other as [e|], other' as [e'|], first, first';
    cbn [binding_tree_c sb_phi sb_base sb_update_value sb_kind sb_other sb_phi_first] in Hcode;
    autorewrite with galois_cost in Hcode; inversion Hcode; subst; f_equal;
    first [apply (encode_injective HE); assumption |
      f_equal; apply (encode_injective (scev_expr_encoding_laws EV HE)); assumption].
Qed.

Definition binding_key V := (scev_binding V * list (V * option (Chrec.t V)))%type.

Definition binding_query {V} lookup (b : scev_binding V) : binding_key V :=
  (b, List.map (fun x => (x, lookup x)) (scev_binding_phis b)).

Definition binding_context_encoding {V} (EV : encoding V) :=
  pair_encoding (binding_encoding EV)
    (list_key_encoding (pair_encoding EV (optional_chrec_encoding EV))).

Definition binding_reference {V} (EV : encoding V) (query : binding_key V) :=
  scev_translate_binding (context_lookup EV None (snd query)) (fst query).

Local Lemma binding_query_reference {V} (EV : encoding V) (HE : encoding_laws EV) lookup b :
  binding_reference EV (binding_query lookup b) = scev_translate_binding lookup b.
Proof.
  unfold binding_reference, binding_query; cbn [fst snd].
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [scev_translate_binding sb_kind sb_base sb_other]; try reflexivity.
  all: rewrite (scev_translate_expr_support _ lookup e); [reflexivity|].
  all: intros x Hin; apply context_lookup_project; [exact HE|exact Hin].
Qed.

Definition binding_prepare_c {V} (EV : encoding V)
    (lookup_c : V -> Cost.t (option (Chrec.t V))) (b : scev_binding V) :=
  let* phis :=
    match sb_other b with
    | None => Cost.ret []
    | Some e => expression_phis_c e
    end in
  let* entries := map_c (fun x =>
    Cost.step ;; Cost.map (fun value => (x, value)) (lookup_c x)) phis in
  PreparedKey.prepare_c (binding_context_encoding EV) (b, entries).

Local Lemma binding_prepare_value {V} (EV : encoding V) lookup_c (b : scev_binding V) :
  Cost.value (binding_prepare_c EV lookup_c b) =
  PreparedKey.prepare (binding_context_encoding EV)
    (binding_query (fun x => Cost.value (lookup_c x)) b).
Proof.
  unfold binding_prepare_c; autorewrite with galois_cost.
  destruct (sb_other b) as [e|] eqn:Hother;
    unfold binding_query, scev_binding_phis; rewrite Hother;
    autorewrite with galois_cost; rewrite ?expression_phis_value; reflexivity.
Qed.

Definition binding_memo V := Memo.t (binding_key V) (option (Chrec.t V)).

(** Binding summaries retain a context-independent reference meaning and a map invariant. *)
Definition binding_valid {V} (EV : encoding V) (m : binding_memo V) : Prop :=
  Map.wf (binding_context_encoding EV) m /\
    Memo.valid (binding_context_encoding EV) (binding_reference EV) m.

Definition binding_miss_c {V} (EV : encoding V)
    (lookup_c : V -> Cost.t (option (Chrec.t V))) (b : scev_binding V)
    (m : binding_memo V) (expressions : compile_memo V)
    : Cost.t (memo_result (binding_key V) (option (Chrec.t V)) (compile_memo V)) :=
  let base := CInv (IVar (sb_base b)) in
  match sb_kind b, sb_other b with
  | SDoubleUpdate, None =>
    Cost.step ;;
    Cost.map (fun result => ((result, m), expressions)) (Idiom.apply_c SDoubleUpdate base None)
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    let* compiled := scev_compile_expr_c EV lookup_c e expressions in
    let '((other, updated), _) := compiled in
    match other with
    | None => Cost.ret ((None, m), updated)
    | Some c =>
      Cost.step ;;
      Cost.map (fun result => ((result, m), updated))
        (Idiom.apply_c (sb_kind b) base (Some c))
    end
  | _, _ => Cost.ret ((None, m), expressions)
  end.

(** Binding compilation uses the same Memo operation and threads the expression table as side data. *)
Definition scev_compile_binding_c {V} (EV : encoding V) lookup_c (b : scev_binding V)
    (m : binding_memo V) (expressions : compile_memo V) :=
  let* key := binding_prepare_c EV lookup_c b in
  Cost.map fst (memo_run_c key (binding_miss_c EV lookup_c b) m expressions).

Local Lemma binding_miss_correct {V} (EV : encoding V) (HE : encoding_laws EV)
    lookup_c b m expressions :
  binding_valid EV m -> compile_valid EV expressions ->
  let '((result, updated), expressions') := Cost.value
    (binding_miss_c EV lookup_c b m expressions) in
  result = scev_translate_binding (fun x => Cost.value (lookup_c x)) b /\
    binding_valid EV updated /\ compile_valid EV expressions'.
Proof.
  intros Hbinding Hexpressions.
  destruct b as [phi base update kind [e|] first]; destruct kind;
    cbn [binding_miss_c sb_kind sb_other sb_base scev_translate_binding];
    autorewrite with galois_cost; try (split; [reflexivity|split; assumption]).
  all: pose proof (scev_compile_expr_correct EV HE lookup_c e expressions Hexpressions) as Hexpr;
    unfold scev_compile_expr in Hexpr;
    destruct (Cost.value (scev_compile_expr_c EV lookup_c e expressions))
      as [[[c|] table] []]; destruct Hexpr as [Hresult Htable];
    autorewrite with galois_cost; rewrite <- Hresult.
  all: split; [reflexivity|split; assumption].
Qed.

(** Binding compilation returns the reference option and maintains both actual shared tables. *)
Theorem scev_compile_binding_correct {V} (EV : encoding V) (HE : encoding_laws EV)
    lookup_c b m expressions :
  binding_valid EV m -> compile_valid EV expressions ->
  let '((result, updated), expressions') := Cost.value
    (scev_compile_binding_c EV lookup_c b m expressions) in
  result = scev_translate_binding (fun x => Cost.value (lookup_c x)) b /\
    binding_valid EV updated /\ compile_valid EV expressions'.
Proof.
  intros [Hwf Hvalid] Hexpressions.
  unfold scev_compile_binding_c; autorewrite with galois_cost.
  rewrite binding_prepare_value.
  pose proof (memo_run_agrees (binding_context_encoding EV)
    ltac:(apply pair_encoding_laws; [apply binding_encoding_laws; exact HE |
      apply list_key_encoding_laws, pair_encoding_laws;
        [exact HE|apply optional_chrec_encoding_laws; exact HE]])
    (binding_reference EV) (compile_valid EV)
    (PreparedKey.prepare (binding_context_encoding EV)
      (binding_query (fun x => Cost.value (lookup_c x)) b))
    (binding_miss_c EV lookup_c b) m expressions
    (PreparedKey.prepare_valid _ _) Hwf Hvalid Hexpressions) as Hrun.
  assert (Hmiss : forall table exprs,
    Map.wf (binding_context_encoding EV) table ->
    Memo.valid (binding_context_encoding EV) (binding_reference EV) table ->
    compile_valid EV exprs ->
    memo_result_valid (binding_context_encoding EV) (binding_reference EV) (compile_valid EV)
      (binding_query (fun x => Cost.value (lookup_c x)) b)
      (Cost.value (binding_miss_c EV lookup_c b table exprs))).
  { intros table exprs Htable Hreference Hexprs.
    pose proof (binding_miss_correct EV HE lookup_c b table exprs
      (conj Htable Hreference) Hexprs) as Hlocal.
    destruct (Cost.value (binding_miss_c EV lookup_c b table exprs))
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

(** Reference compilation folds the declared bindings in order using their independent translations. *)
Fixpoint scev_translate_bindings {V} (EV : encoding V) (bs : list (scev_binding V))
    (env : Map.t V (Chrec.t V)) : option (Map.t V (Chrec.t V)) :=
  match bs with
  | [] => Some env
  | b :: rest =>
    match scev_translate_binding (fun x => Map.get EV x env) b with
    | Some c => scev_translate_bindings EV rest (Map.set EV (sb_phi b) c env)
    | None => None
    end
  end.

(** Compiling a later binding retains both tables and keys its queries by the extended environment. *)
Fixpoint scev_compile_bindings_c {V} (EV : encoding V) (bs : list (scev_binding V))
    (env : Map.t V (Chrec.t V)) (m : binding_memo V) (expressions : compile_memo V)
    : Cost.t ((option (Map.t V (Chrec.t V)) * binding_memo V) * compile_memo V) :=
  match bs with
  | [] => Cost.ret ((Some env, m), expressions)
  | b :: rest =>
    Cost.step ;;
    let* compiled := scev_compile_binding_c EV (fun x => Map.get_c EV x env) b m expressions in
    let '((result, updated), expressions') := compiled in
    match result with
    | None => Cost.ret ((None, updated), expressions')
    | Some c =>
      let* env' := Map.set_c EV (sb_phi b) c env in
      scev_compile_bindings_c EV rest env' updated expressions'
    end
  end.

(** Whole binding-list compilation agrees on failures as well as successful environments. *)
Theorem scev_compile_bindings_correct {V} (EV : encoding V) (HE : encoding_laws EV) bs :
  forall env m expressions, binding_valid EV m -> compile_valid EV expressions ->
  let '((result, updated), expressions') := Cost.value
    (scev_compile_bindings_c EV bs env m expressions) in
  result = scev_translate_bindings EV bs env /\
    binding_valid EV updated /\ compile_valid EV expressions'.
Proof.
  induction bs as [|b rest IH]; intros env m expressions Hbinding Hexpressions.
  - split; [reflexivity|split; assumption].
  - pose proof (scev_compile_binding_correct EV HE (fun x => Map.get_c EV x env)
      b m expressions Hbinding Hexpressions) as Hhead.
    cbn [scev_compile_bindings_c]; autorewrite with galois_cost.
    destruct (Cost.value (scev_compile_binding_c EV (fun x => Map.get_c EV x env)
      b m expressions)) as [[[c|] updated] expressions'];
      destruct Hhead as [Hresult [Hupdated Hexprs]].
    + change (Some c = scev_translate_binding (fun x => Map.get EV x env) b) in Hresult.
      cbn [scev_translate_bindings]; rewrite <- Hresult; autorewrite with galois_cost.
      apply IH; assumption.
    + change (None = scev_translate_binding (fun x => Map.get EV x env) b) in Hresult.
      cbn [scev_translate_bindings]; rewrite <- Hresult; autorewrite with galois_cost.
      split; [reflexivity|split; assumption].
Qed.

Definition scev_translate_plan {V} (EV : encoding V) (p : scev_plan V) :=
  match scev_translate_bindings EV (sp_bindings p) Map.empty with
  | Some env => Map.get EV (sp_target p) env
  | None => None
  end.

(** A plan execution exposes the actual compiler tables used to build its recurrence. *)
Definition scev_compile_plan_execution_c {V} (EV : encoding V) (p : scev_plan V) :=
  let* compiled := scev_compile_bindings_c EV (sp_bindings p) Map.empty Memo.empty Memo.empty in
  let '((result, bindings), expressions) := compiled in
  match result with
  | None => Cost.ret ((None, bindings), expressions)
  | Some env =>
    Cost.map (fun found => ((found, bindings), expressions)) (Map.get_c EV (sp_target p) env)
  end.

Definition scev_compile_plan_c {V} (EV : encoding V) (p : scev_plan V) :=
  Cost.map (fun result => fst (fst result)) (scev_compile_plan_execution_c EV p).

Definition scev_compile_plan {V} (EV : encoding V) p :=
  Cost.value (@scev_compile_plan_c V EV p).

(** Public compilation initializes both Memo invariants and returns the entire reference option. *)
Theorem scev_compile_plan_correct {V} (EV : encoding V) (HE : encoding_laws EV) p :
  scev_compile_plan EV p = scev_translate_plan EV p.
Proof.
  assert (Hbindings : binding_valid EV (@Memo.empty (binding_key V) (option (Chrec.t V)))).
  { split.
    - change (Map.wf (binding_context_encoding EV) (@Map.empty _ (option (Chrec.t V)))).
      apply Map.wf_empty.
    - apply Memo.valid_empty. }
  assert (Hexpressions : compile_valid EV (@Memo.empty (compile_key V) (option (Chrec.t V)))).
  { split.
    - change (Map.wf (compile_encoding EV) (@Map.empty _ (option (Chrec.t V)))).
      apply Map.wf_empty.
    - apply Memo.valid_empty. }
  pose proof (scev_compile_bindings_correct EV HE (sp_bindings p) Map.empty
    Memo.empty Memo.empty Hbindings Hexpressions) as Hcompile.
  unfold scev_compile_plan, scev_compile_plan_c, scev_compile_plan_execution_c.
  autorewrite with galois_cost.
  destruct (Cost.value (scev_compile_bindings_c EV (sp_bindings p)
    Map.empty Memo.empty Memo.empty)) as [[result bindings] expressions].
  destruct Hcompile as [Hresult _]; unfold scev_translate_plan; rewrite <- Hresult.
  destruct result; autorewrite with galois_cost; reflexivity.
Qed.

(** * Charged source inventory preparation *)

Fixpoint scev_inventory_index_c {N E V K G} (sv : Ssa.t N E V K G) (inventory : list V)
    : Cost.t (Map.t V (N * definition N V K)) :=
  match inventory with
  | [] => Map.empty_c
  | x :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* n := Ssa.home_c sv x in
    Cost.step ;;
    let* d := Ssa.def_c sv x in
    let* table := scev_inventory_index_c sv rest in
    Map.set_c (Ssa.val_enc sv) x (n, d) table
  end.

Definition scev_inventory_index {N E V K G} (sv : Ssa.t N E V K G) inventory :=
  Cost.value (scev_inventory_index_c sv inventory).

(** Preparation records each listed value's source readers without changing duplicate behavior. *)
Theorem scev_inventory_index_equation {N E V K G} (sv : Ssa.t N E V K G) inventory :
  scev_inventory_index sv inventory =
  match inventory with
  | [] => Map.empty
  | x :: rest =>
    Map.set (Ssa.val_enc sv) x (Ssa.home sv x, Ssa.def sv x)
      (scev_inventory_index sv rest)
  end.
Proof.
  destruct inventory; reflexivity.
Qed.

(** Every prepared inventory satisfies the public map representation invariant. *)
Theorem scev_inventory_index_wf {N E V K G} (sv : Ssa.t N E V K G) inventory :
  Map.wf (Ssa.val_enc sv) (scev_inventory_index sv inventory).
Proof.
  induction inventory; rewrite scev_inventory_index_equation.
  - apply Map.wf_empty.
  - apply Map.wf_set; exact IHinventory.
Qed.

(** Indexed lookup is present exactly on the inventory and retains both source observations. *)
Theorem scev_inventory_index_get {N E V K G} (sv : Ssa.t N E V K G)
    (HE : encoding_laws (Ssa.val_enc sv)) inventory x :
  Map.get (Ssa.val_enc sv) x (scev_inventory_index sv inventory) =
    if existsb (eqb (Ssa.val_enc sv) x) inventory
    then Some (Ssa.home sv x, Ssa.def sv x) else None.
Proof.
  induction inventory as [|y rest IH]; rewrite scev_inventory_index_equation.
  - apply Map.get_empty.
  - rewrite Map.get_set by apply scev_inventory_index_wf.
    cbn [existsb].
    destruct (eqb_spec (Ssa.val_enc sv) HE x y) as [Hequal|Hdifferent].
    + subst y; reflexivity.
    + exact IH.
Qed.

(** Reader, encoder and key-width budgets bound actual preparation, including repeated entries. *)
Theorem scev_inventory_index_cost {N E V K G} (sv : Ssa.t N E V K G)
    inventory h d e b :
  (forall x, In x inventory ->
    (Cost.ticks (Ssa.home_c sv x) <= h)%N /\
    (Cost.ticks (Ssa.def_c sv x) <= d)%N /\
    (Cost.ticks (encode_c (Ssa.val_enc sv) x) <= e)%N /\
    (key_bits (Ssa.val_enc sv) x <= b)%N) ->
  (Cost.ticks (scev_inventory_index_c sv inventory) <=
    N.of_nat (length inventory) * (4 + h + d + e + b))%N.
Proof.
  induction inventory as [|x rest IH]; intro Hbounds.
  - reflexivity.
  - specialize (IH (fun y Hy => Hbounds y (or_intror Hy))).
    destruct (Hbounds x (or_introl eq_refl)) as [Hhome [Hdef [Hencode Hbits]]].
    cbn [scev_inventory_index_c]; autorewrite with galois_cost.
    rewrite Map.set_cost; fold (key_bits (Ssa.val_enc sv) x).
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

End Recognise.
