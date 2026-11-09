(** * Prepared congruence signatures

    Syntax, incoming arguments, class anchors and signature IDs are prepared before checking.
    For example, two pure additions pass when their operand class lists agree.
    Builds on: AnalysesEqualityProblem, AnalysesEqualityIncoming and BaseIntern. *)

From Stdlib Require Import List Bool Arith Lia Wf_nat NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseCode BaseMap BaseSet BaseIndex
  BaseIntern BaseUnionFind.
From Galois.Lattice Require Import LatticePartition.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramLink ProgramSsa
  ProgramStrict.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualityIncoming.
Import List.ListNotations Cost.Notations Numbering.

Local Open Scope nat_scope.

Module NumberingSignature.

(** Constructor tags distinguish operation, parameter and singleton signatures.
    Operator and block payloads are encoded once during syntax preparation. *)
Inductive sig_key : Type :=
  | SigOp (op : positive) (operand_classes : list positive)
  | SigParam (block : positive) (incoming_classes : list positive)
  | SigSingle (value : positive).

Definition wire := ((positive * list positive) +
  ((positive * list positive) + positive))%type.

Definition wire_codec : codec wire :=
  sum_codec (pair_codec positive_codec (list_codec positive_codec))
    (sum_codec (pair_codec positive_codec (list_codec positive_codec)) positive_codec).

Definition to_wire (key : sig_key) : wire :=
  match key with
  | SigOp op args => inl (op, args)
  | SigParam block args => inr (inl (block, args))
  | SigSingle value => inr (inr value)
  end.

Definition of_wire (w : wire) : sig_key :=
  match w with
  | inl (op, args) => SigOp op args
  | inr (inl (block, args)) => SigParam block args
  | inr (inr value) => SigSingle value
  end.

(** The signature codec is derived from the public sum, pair and list codecs. *)
Definition sig_codec : codec sig_key :=
  Codec (Encoding (fun key => encode_c (codec_enc wire_codec) (to_wire key)))
    (fun bits => option_map of_wire (decode wire_codec bits)).

(** Signature decoding recovers each constructor and every payload. *)
Theorem sig_codec_laws : codec_laws sig_codec.
Proof.
  assert (Hwire : codec_laws wire_codec).
  { apply sum_codec_laws.
    - apply pair_codec_laws; [apply positive_codec_laws|].
      apply list_codec_laws, positive_codec_laws.
    - apply sum_codec_laws; [|apply positive_codec_laws].
      apply pair_codec_laws; [apply positive_codec_laws|].
      apply list_codec_laws, positive_codec_laws. }
  constructor; intro key.
  change (option_map of_wire (decode wire_codec
    (encode (codec_enc wire_codec) (to_wire key))) = Some key).
  rewrite (decode_encode Hwire); destruct key; reflexivity.
Qed.

Definition sig_encoding := codec_enc sig_codec.

(** Derived signature keys have an injective encoding. *)
Theorem sig_encoding_laws : encoding_laws sig_encoding.
Proof.
  apply codec_laws_injective, sig_codec_laws.
Qed.

(** Tabulation uses the existing costed map constructor and retains every callback charge. *)
Definition tabulate_c {A B} (E : encoding A) (f : A -> Cost.t B) xs :
    Cost.t (Map.t A B) :=
  let* rows := map_c (fun x => Cost.step ;; Cost.map (fun y => (x, y)) (f x)) xs in
  Map.of_list_c E rows.

Definition tabulate {A B} (E : encoding A) (f : A -> Cost.t B) xs :=
  Cost.value (tabulate_c E f xs).

(** Tabulation stores callback values at their input keys. *)
Theorem tabulate_equation {A B} (E : encoding A) (f : A -> Cost.t B) xs :
  tabulate E f xs = Map.of_list E (map (fun x => (x, Cost.value (f x))) xs).
Proof.
  unfold tabulate, tabulate_c; rewrite Cost.value_bind, value_map_c; reflexivity.
Qed.

(** Every tabulated map satisfies its actual encoding-dependent representation invariant. *)
Theorem tabulate_wf {A B} (E : encoding A) (f : A -> Cost.t B) xs :
  Map.wf E (tabulate E f xs).
Proof.
  rewrite tabulate_equation; apply Map.wf_of_list.
Qed.

Local Lemma tabulate_lookup_fold {A B} (E : encoding A) (HE : encoding_laws E)
    (f : A -> B) xs x old :
  fold_left (fun previous kv =>
    if eqb E x (fst kv) then Some (snd kv) else previous)
    (map (fun a => (a, f a)) xs) old =
  if existsb (eqb E x) xs then Some (f x) else old.
Proof.
  revert old; induction xs as [|a rest IH]; intro old; [reflexivity|].
  cbn [map fold_left existsb fst snd].
  destruct (eqb_spec E HE x a) as [->|Hne]; cbn [orb]; rewrite IH.
  - destruct (existsb (eqb E a) rest); reflexivity.
  - reflexivity.
Qed.

(** Every listed key reads its callback value, even when the inventory contains duplicates. *)
Theorem tabulate_get {A B} (E : encoding A) (HE : encoding_laws E)
    (f : A -> Cost.t B) xs x :
  In x xs -> Map.get E x (tabulate E f xs) = Some (Cost.value (f x)).
Proof.
  intro Hx; rewrite tabulate_equation, Map.of_list_get, (tabulate_lookup_fold E HE).
  assert (Hpresent : existsb (eqb E x) xs = true).
  { apply existsb_exists; exists x; split; [exact Hx|apply eqb_refl]. }
  now rewrite Hpresent.
Qed.

(** Unlisted keys have no cached entry under a lawful dictionary. *)
Theorem tabulate_absent {A B} (E : encoding A) (HE : encoding_laws E)
    (f : A -> Cost.t B) xs x :
  ~ In x xs -> Map.get E x (tabulate E f xs) = None.
Proof.
  intro Hx; rewrite tabulate_equation, Map.of_list_get, (tabulate_lookup_fold E HE).
  destruct (existsb (eqb E x) xs) eqn:Hpresent; [|reflexivity].
  apply existsb_exists in Hpresent as [a [Ha Heq]].
  apply (eqb_true_iff E HE) in Heq; subst a; contradiction.
Qed.

(** A listed cache entry never uses its fallback value. *)
Theorem tabulate_find_or {A B} (E : encoding A) (HE : encoding_laws E)
    (f : A -> Cost.t B) xs x fallback :
  In x xs ->
  Cost.value (Map.find_or_c E fallback x (tabulate E f xs)) = Cost.value (f x).
Proof.
  intro Hx; change (Map.find_or E fallback x (tabulate E f xs) = Cost.value (f x)).
  rewrite Map.find_or_equation, (tabulate_get E HE) by exact Hx; reflexivity.
Qed.

(** A template caches all class-independent syntax and boundary validation. *)
Inductive template (V : Type) : Type :=
  | TOp (op : positive) (args : list V)
  | TParam (block : positive) (args : list V)
  | TSingle (value : positive).

Arguments TOp {V}.
Arguments TParam {V}.
Arguments TSingle {V}.

(** A static basis owns the shared inventory, entry set and incoming index. *)
Record basis (N V : Type) := Basis {
  inventory : FinSet.t V;
  entries : FinSet.t N;
  incoming : Index.t N (NumberingIncoming.row N V)
}.

Arguments Basis {N V}.
Arguments inventory {N V}.
Arguments entries {N V}.
Arguments incoming {N V}.

Section Static.
Context {N E V K G : Type} (np : problem N E V K G).
Let p := ssa np.
Let EV := Ssa.val_enc p.
Let EN := Cfg.node_enc (Ssa.cfg p).
Let graph := Cfg.graph (Ssa.cfg p).

(** Static preparation builds each inventory and incoming index once. *)
Definition basis_c : Cost.t (basis N V) :=
  let* listed := FinSet.of_list_c EV (Ssa.values p) in
  let* roots := FinSet.of_list_c EN (Graph.entries graph) in
  let* rows := NumberingIncoming.prepare_c p in
  Cost.ret (Basis listed roots rows).

Definition prepared_basis := Cost.value basis_c.

Definition single_c x : Cost.t (template V) :=
  Cost.step ;; Cost.map TSingle (encode_c EV x).

(** A malformed operand boundary gets the value's own singleton signature. *)
Definition form_c (b : basis N V) x : Cost.t (template V) :=
  Cost.step ;;
  let* def := Ssa.def_c p x in
  match def with
  | Op op args =>
    Cost.step ;;
    let* pure := pure_c np op in
    if pure then
      let* listed := forallb_c (fun y => FinSet.mem_c EV y (inventory b)) args in
      if listed then
        Cost.step ;; Cost.map (fun code => TOp code args) (encode_c (op_enc np) op)
      else single_c x
    else single_c x
  | Param block i =>
    let* entry := FinSet.mem_c EN block (entries b) in
    if entry then single_c x else
      let* rows := Index.find_c EN block (incoming b) in
      let* args := NumberingIncoming.read_rows_c rows i in
      match args with
      | None => single_c x
      | Some args =>
        let* listed := forallb_c (fun y => FinSet.mem_c EV y (inventory b)) args in
        if listed then
          Cost.step ;; Cost.map (fun code => TParam code args) (encode_c EN block)
        else single_c x
      end
  | Arbitrary => single_c x
  end.

Definition form b x := Cost.value (form_c b x).

(** The pure form equation exposes boundary decisions without repeating preparation. *)
Theorem form_equation b x :
  form b x =
  match Ssa.def p x with
  | Op op args =>
    if pure np op && forallb (fun y => FinSet.mem EV y (inventory b)) args
    then TOp (encode (op_enc np) op) args else TSingle (encode EV x)
  | Param block i =>
    if FinSet.mem EN block (entries b) then TSingle (encode EV x)
    else match NumberingIncoming.read_rows (Index.find EN block (incoming b)) i with
    | None => TSingle (encode EV x)
    | Some args =>
      if forallb (fun y => FinSet.mem EV y (inventory b)) args
      then TParam (encode EN block) args else TSingle (encode EV x)
    end
  | Arbitrary => TSingle (encode EV x)
  end.
Proof.
  unfold form, form_c; autorewrite with galois_cost; fold (Ssa.def p x).
  destruct (Ssa.def p x) as [op args|block i|]; [| |reflexivity].
  - autorewrite with galois_cost.
    unfold pure; destruct (Cost.value (pure_c np op)); cbn [andb].
    + autorewrite with galois_cost.
      change (Cost.value
        (if forallb (fun y => FinSet.mem EV y (inventory b)) args
         then Cost.step ;; Cost.map (fun code => TOp code args) (encode_c (op_enc np) op)
         else single_c x) =
        if forallb (fun y => FinSet.mem EV y (inventory b)) args
        then TOp (encode (op_enc np) op) args else TSingle (encode EV x)).
      destruct (forallb (fun y => FinSet.mem EV y (inventory b)) args); reflexivity.
    + reflexivity.
  - autorewrite with galois_cost; fold (FinSet.mem EN block (entries b)).
    destruct (FinSet.mem EN block (entries b)); [reflexivity|].
    autorewrite with galois_cost; fold (Index.find EN block (incoming b)).
    fold (NumberingIncoming.read_rows (Index.find EN block (incoming b)) i).
    destruct (NumberingIncoming.read_rows (Index.find EN block (incoming b)) i) as [args|].
    + autorewrite with galois_cost.
      change (Cost.value
        (if forallb (fun y => FinSet.mem EV y (inventory b)) args
         then Cost.step ;; Cost.map (fun code => TParam code args) (encode_c EN block)
         else single_c x) =
        if forallb (fun y => FinSet.mem EV y (inventory b)) args
        then TParam (encode EN block) args else TSingle (encode EV x)).
      destruct (forallb (fun y => FinSet.mem EV y (inventory b)) args); reflexivity.
    + reflexivity.
Qed.

(** Prepared syntax is a map, so no signature query scans the value inventory. *)
Definition prepare_c : Cost.t (Map.t V (template V)) :=
  let* b := basis_c in tabulate_c EV (form_c b) (Ssa.values p).

Definition prepare := Cost.value prepare_c.

(** The prepared template table stores the result of one shared static basis. *)
Theorem prepare_equation :
  prepare = tabulate EV (form_c prepared_basis) (Ssa.values p).
Proof.
  reflexivity.
Qed.

(** The static basis retains the exact public inventory, entries and incoming observations. *)
Theorem basis_equation :
  prepared_basis =
  Basis (FinSet.of_list EV (Ssa.values p)) (FinSet.of_list EN (Graph.entries graph))
    (NumberingIncoming.prepare p).
Proof.
  reflexivity.
Qed.

End Static.

(** Instantiating a template retains the charge of each operand-class callback. *)
Definition instantiate_c {V} (cls : V -> Cost.t positive) (t : template V) :
    Cost.t sig_key :=
  match t with
  | TOp op args => Cost.map (SigOp op) (map_c (fun y => Cost.step ;; cls y) args)
  | TParam block args => Cost.map (SigParam block) (map_c (fun y => Cost.step ;; cls y) args)
  | TSingle value => Cost.ret (SigSingle value)
  end.

(** Instantiated signatures preserve constructor identity and the full operand class order. *)
Theorem instantiate_equation {V} (cls : V -> Cost.t positive) (t : template V) :
  Cost.value (instantiate_c cls t) =
  match t with
  | TOp op args => SigOp op (map (fun y => Cost.value (cls y)) args)
  | TParam block args => SigParam block (map (fun y => Cost.value (cls y)) args)
  | TSingle value => SigSingle value
  end.
Proof.
  destruct t; cbn [instantiate_c]; autorewrite with galois_cost;
    rewrite ?value_map_c; reflexivity.
Qed.

(** A signature query performs a cached template lookup and visits that template's operands. *)
Definition signature_c {N E V K G} (np : problem N E V K G)
    (forms : Map.t V (template V)) (cls : V -> Cost.t positive) x : Cost.t sig_key :=
  let* form := Map.get_c (Ssa.val_enc (ssa np)) x forms in
  match form with
  | Some t => instantiate_c cls t
  | None =>
    Cost.step ;; Cost.map SigSingle (encode_c (Ssa.val_enc (ssa np)) x)
  end.

Definition signature {N E V K G} (np : problem N E V K G) forms cls x :=
  Cost.value (signature_c np forms cls x).

(** Listed values use the prepared form and every unlisted value remains a singleton. *)
Theorem signature_equation {N E V K G} (np : problem N E V K G)
    (HV : encoding_laws (Ssa.val_enc (ssa np))) cls x :
  In x (Ssa.values (ssa np)) ->
  signature np (prepare np) cls x =
    Cost.value (instantiate_c cls (form np (prepared_basis np) x)).
Proof.
  intro Hx; unfold signature, signature_c; rewrite Cost.value_bind.
  fold (@Map.get V (template V) (Ssa.val_enc (ssa np)) x (prepare np)).
  rewrite prepare_equation, (tabulate_get _ HV) by exact Hx; reflexivity.
Qed.

(** Class lookup calls the actual supplied partition's UnionFind with its own dictionary. *)
Definition class_c {V} (EV : encoding V) (p : partition_t EV) x : Cost.t positive :=
  match p with
  | None => Cost.ret 1%positive
  | Some u =>
    let* found := UnionFind.find_c EV x (proj1_sig u) in
    Cost.step ;; encode_c EV (fst found)
  end.

Definition class {V} (EV : encoding V) (p : partition_t EV) x :=
  Cost.value (class_c EV p x).

(** Encoded representative equality recognises the supplied partition's equivalence. *)
Theorem class_spec {V} (EV : encoding V) (HV : encoding_laws EV) p x y :
  class EV p x = class EV p y <-> partition_equiv EV p x y.
Proof.
  destruct p as [u|]; [|split; intros; reflexivity].
  change (encode EV (fst (UnionFind.find EV x (proj1_sig u))) =
    encode EV (fst (UnionFind.find EV y (proj1_sig u))) <->
    UnionFind.equiv EV (proj1_sig u) x y).
  rewrite UnionFind.equiv_equation; split.
  - apply (encode_injective HV).
  - intros ->; reflexivity.
Qed.

(** The checker domain includes partition support, so unsupported nontrivial classes are checked. *)
Definition domain_c {V} (EV : encoding V) (values : list V) (p : partition_t EV) :=
  match p with
  | None => Cost.ret values
  | Some u =>
    let* keys := UnionFind.keys_c EV (proj1_sig u) in app_c values keys
  end.

Definition domain {V} (EV : encoding V) values p := Cost.value (domain_c EV values p).

(** Every listed value belongs to the checker domain, regardless of the proposed partition. *)
Theorem domain_values {V} (EV : encoding V) values p x :
  In x values -> In x (domain EV values p).
Proof.
  destruct p as [u|]; intro Hx; [|exact Hx].
  unfold domain, domain_c; rewrite Cost.value_bind, value_app_c.
  change (In x (values ++ UnionFind.keys EV (proj1_sig u))); apply in_or_app; now left.
Qed.

(** A prepared check caches class codes, signature IDs and one stable anchor per class. *)
Record prepared (V : Type) := Prepared {
  checked_values : list V;
  class_table : Map.t V positive;
  key_table : Map.t V sig_key;
  signature_table : Map.t V (option positive);
  signature_intern : Intern.t sig_key;
  anchors : Index.t positive V
}.

Arguments Prepared {V}.
Arguments checked_values {V}.
Arguments class_table {V}.
Arguments key_table {V}.
Arguments signature_table {V}.
Arguments signature_intern {V}.
Arguments anchors {V}.

(** Missing class cache entries retain the encoded identity of the queried value. *)
Definition cached_class_c {V} (EV : encoding V) (table : Map.t V positive) x :=
  let* found := Map.get_c EV x table in
  match found with
  | Some id => Cost.ret id
  | None => Cost.step ;; encode_c EV x
  end.

Definition cached_class {V} (EV : encoding V) table x :=
  Cost.value (cached_class_c EV table x).

Section Check.
Context {N E V K G : Type} (np : problem N E V K G).
Let EV := Ssa.val_enc (ssa np).

(** Check preparation performs each full-domain pass once before per-value comparisons. *)
Definition prepare_check_c forms (p : partition_t EV) : Cost.t (prepared V) :=
  let* values := domain_c EV (Ssa.values (ssa np)) p in
  let* classes := tabulate_c EV (class_c EV p) values in
  let cls := cached_class_c EV classes in
  let* keys := tabulate_c EV (signature_c np forms cls) values in
  let key := fun x => Map.find_or_c EV (SigSingle 1%positive) x keys in
  let* all_keys := map_c key values in
  let* intern := Intern.of_list_c sig_encoding all_keys in
  let* signatures := tabulate_c EV
    (fun x => Cost.step ;;
      let* sig := key x in Intern.find_c sig_encoding sig intern) values in
  let* heads := Index.group_by_c positive_encoding cls values in
  Cost.ret (Prepared values classes keys signatures intern heads).

Definition prepare_check forms p := Cost.value (prepare_check_c forms p).

(** Preparation exposes its cached passes through public container value contracts. *)
Theorem prepare_check_equation forms p :
  prepare_check forms p =
  let values := domain EV (Ssa.values (ssa np)) p in
  let classes := tabulate EV (class_c EV p) values in
  let cls := cached_class_c EV classes in
  let keys := tabulate EV (signature_c np forms cls) values in
  let key := fun x => Map.find_or_c EV (SigSingle 1%positive) x keys in
  let intern := Intern.of_list sig_encoding (map (fun x => Cost.value (key x)) values) in
  Prepared values classes keys
    (tabulate EV (fun x => Cost.step ;;
      let* sig := key x in Intern.find_c sig_encoding sig intern) values)
    intern (Index.group_by positive_encoding (fun x => Cost.value (cls x)) values).
Proof.
  unfold prepare_check, prepare_check_c; autorewrite with galois_cost.
  rewrite ?value_map_c, Index.group_by_c_value; reflexivity.
Qed.

(** Cached class lookup agrees with the actual forest on the whole prepared domain. *)
Theorem cached_class_agrees (HV : encoding_laws EV) p x :
  In x (domain EV (Ssa.values (ssa np)) p) ->
  cached_class EV
    (tabulate EV (class_c EV p) (domain EV (Ssa.values (ssa np)) p)) x = class EV p x.
Proof.
  intro Hx; unfold cached_class, cached_class_c; rewrite Cost.value_bind.
  fold (@Map.get V positive EV x
    (tabulate EV (class_c EV p) (domain EV (Ssa.values (ssa np)) p))).
  rewrite (tabulate_get EV HV) by exact Hx; reflexivity.
Qed.

(** A successful interner lookup recovers its complete original signature key. *)
Theorem intern_same (intern : Intern.t sig_key) a b id :
  Intern.wf sig_encoding intern ->
  Intern.find sig_encoding a intern = Some id ->
  Intern.find sig_encoding b intern = Some id -> a = b.
Proof.
  intros Hwf Ha Hb.
  pose proof (Intern.key_of_find sig_encoding a id intern Hwf Ha) as Hkeya.
  pose proof (Intern.key_of_find sig_encoding b id intern Hwf Hb) as Hkeyb.
  congruence.
Qed.

(** Each comparison uses cached IDs and the head of the already prepared class bucket. *)
Definition check_value_c (pr : prepared V) x : Cost.t bool :=
  let* cls := cached_class_c EV (class_table pr) x in
  let* bucket := Index.find_c positive_encoding cls (anchors pr) in
  match bucket with
  | [] => Cost.ret false
  | anchor :: _ =>
    let* lhs := Map.get_c EV x (signature_table pr) in
    let* rhs := Map.get_c EV anchor (signature_table pr) in
    match lhs, rhs with
    | Some (Some a), Some (Some b) => positive_eqb_c a b
    | _, _ => Cost.ret false
    end
  end.

(** None is unreachable and is explicitly rejected as a numbering candidate. *)
Definition check_c (p : partition_t EV) : Cost.t bool :=
  match p with
  | None => Cost.ret false
  | Some _ =>
    let* forms := prepare_c np in
    let* prepared := prepare_check_c forms p in
    forallb_c (fun x => Cost.step ;; check_value_c prepared x) (checked_values prepared)
  end.

Definition check p := Cost.value (check_c p).

(** Per-value comparisons have no syntax traversal and compare cached dense IDs only. *)
Theorem check_value_equation pr x :
  Cost.value (check_value_c pr x) =
  match Index.find positive_encoding (cached_class EV (class_table pr) x) (anchors pr) with
  | [] => false
  | anchor :: _ =>
    match Map.get EV x (signature_table pr), Map.get EV anchor (signature_table pr) with
    | Some (Some a), Some (Some b) => Pos.eqb a b
    | _, _ => false
    end
  end.
Proof.
  unfold check_value_c; autorewrite with galois_cost.
  fold (cached_class EV (class_table pr) x).
  fold (Index.find positive_encoding (cached_class EV (class_table pr) x) (anchors pr)).
  destruct (Index.find positive_encoding (cached_class EV (class_table pr) x) (anchors pr))
    as [|anchor rest]; [reflexivity|].
  autorewrite with galois_cost.
  fold (Map.get EV x (signature_table pr)); fold (Map.get EV anchor (signature_table pr)).
  destruct (Map.get EV x (signature_table pr)) as [[a|]|],
    (Map.get EV anchor (signature_table pr)) as [[b|]|]; try reflexivity.
  apply positive_eqb_equation.
Qed.

(** The checker explicitly separates unreachable input from the prepared reached check. *)
Theorem check_equation p :
  check p =
  match p with
  | None => false
  | Some _ =>
    let pr := prepare_check (prepare np) p in
    forallb (fun x => Cost.value (check_value_c pr x)) (checked_values pr)
  end.
Proof.
  destruct p as [u|]; [|reflexivity].
  unfold check, check_c; autorewrite with galois_cost.
  reflexivity.
Qed.

(** Accepted members of one cached class have the same successfully looked-up signature ID. *)
Theorem check_ids_equal pr x y :
  forallb (fun v => Cost.value (check_value_c pr v)) (checked_values pr) = true ->
  In x (checked_values pr) -> In y (checked_values pr) ->
  cached_class EV (class_table pr) x = cached_class EV (class_table pr) y ->
  exists id, Map.get EV x (signature_table pr) = Some (Some id) /\
    Map.get EV y (signature_table pr) = Some (Some id).
Proof.
  intros Hall Hx Hy Hclass.
  pose proof (proj1 (forallb_forall _ _) Hall x Hx) as Hcx.
  pose proof (proj1 (forallb_forall _ _) Hall y Hy) as Hcy.
  change (Cost.value (check_value_c pr x) = true) in Hcx.
  change (Cost.value (check_value_c pr y) = true) in Hcy.
  rewrite check_value_equation in Hcx, Hcy; rewrite Hclass in Hcx.
  destruct (Index.find positive_encoding (cached_class EV (class_table pr) y) (anchors pr))
    as [|anchor rest]; [discriminate|].
  destruct (Map.get EV x (signature_table pr)) as [[a|]|] eqn:Hxid;
    try discriminate.
  destruct (Map.get EV y (signature_table pr)) as [[b|]|] eqn:Hyid;
    try discriminate.
  destruct (Map.get EV anchor (signature_table pr)) as [[c|]|];
    try discriminate.
  apply Pos.eqb_eq in Hcx, Hcy; subst a b.
  exists c; split; reflexivity.
Qed.

(** The checker establishes equal complete signatures for arbitrary proposed reached classes.
    Only the supplied value encoding's injectivity is needed for the prepared caches. *)
Theorem check_signatures (HV : encoding_laws EV) p x y :
  check p = true ->
  In x (Ssa.values (ssa np)) -> In y (Ssa.values (ssa np)) ->
  partition_equiv EV p x y ->
  let values := domain EV (Ssa.values (ssa np)) p in
  let cls := cached_class_c EV (tabulate EV (class_c EV p) values) in
  signature np (prepare np) cls x = signature np (prepare np) cls y.
Proof.
  intros Hcheck Hx Hy Hrelated; cbn zeta.
  assert (Hdx : In x (domain EV (Ssa.values (ssa np)) p)) by now apply domain_values.
  assert (Hdy : In y (domain EV (Ssa.values (ssa np)) p)) by now apply domain_values.
  set (pr := prepare_check (prepare np) p).
  assert (Hclasses :
    cached_class EV (class_table pr) x = cached_class EV (class_table pr) y).
  { unfold pr; rewrite prepare_check_equation; cbn [class_table].
    rewrite !cached_class_agrees by assumption.
    apply (proj2 (class_spec EV HV p x y)); exact Hrelated. }
  assert (Hall :
    forallb (fun v => Cost.value (check_value_c pr v)) (checked_values pr) = true).
  { rewrite check_equation in Hcheck; destruct p; [exact Hcheck|discriminate]. }
  assert (Hpx : In x (checked_values pr)).
  { unfold pr; rewrite prepare_check_equation; exact Hdx. }
  assert (Hpy : In y (checked_values pr)).
  { unfold pr; rewrite prepare_check_equation; exact Hdy. }
  destruct (check_ids_equal pr x y Hall Hpx Hpy Hclasses) as [id [Hix Hiy]].
  unfold pr in Hix, Hiy; rewrite prepare_check_equation in Hix, Hiy.
  cbn [signature_table] in Hix, Hiy.
  rewrite (tabulate_get EV HV) in Hix by exact Hdx.
  rewrite (tabulate_get EV HV) in Hiy by exact Hdy.
  autorewrite with galois_cost in Hix, Hiy.
  fold (@Intern.find sig_key sig_encoding) in Hix, Hiy.
  rewrite (tabulate_find_or EV HV) in Hix by exact Hdx.
  rewrite (tabulate_find_or EV HV) in Hiy by exact Hdy.
  injection Hix as Hix; injection Hiy as Hiy.
  eapply intern_same; [apply Intern.wf_of_list, sig_encoding_laws|exact Hix|exact Hiy].
Qed.

(** The raw unreachable partition is rejected without silently exposing a numbering result. *)
Theorem check_unreached : check None = false.
Proof.
  reflexivity.
Qed.

End Check.

(** List-set membership reflects the finite inventory under the supplied actual encoding law. *)
Theorem listed_spec {A} (E : encoding A) (HE : encoding_laws E) xs x :
  FinSet.mem E x (FinSet.of_list E xs) = true <-> In x xs.
Proof.
  rewrite FinSet.mem_of_list, existsb_exists; split.
  - intros [y [Hy Heq]]; apply (eqb_true_iff E HE) in Heq; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply eqb_refl].
Qed.

Section Congruence.
Context {N E V K G : Type} (np : problem N E V K G)
  (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (ssa np))))
  (HV : encoding_laws (Ssa.val_enc (ssa np)))
  (HK : encoding_laws (op_enc np)).
Let syntax := ssa np.
Let EV := Ssa.val_enc syntax.
Let EN := Cfg.node_enc (Ssa.cfg syntax).
Let graph := Cfg.graph (Ssa.cfg syntax).
Let values := Ssa.values syntax.

(** Prepared forms keep exactly the legacy operation and non-entry parameter boundary. *)
Theorem form_cases x :
  form np (prepared_basis np) x = TSingle (encode EV x) \/
  (exists op args, Ssa.def syntax x = Op op args /\ pure np op = true /\
    Forall (fun y => In y values) args /\
    form np (prepared_basis np) x = TOp (encode (op_enc np) op) args) \/
  (exists b i args, Ssa.def syntax x = Param b i /\ ~ In b (Graph.entries graph) /\
    NumberingIncoming.read_rows (Index.find EN b (NumberingIncoming.prepare syntax)) i =
      Some args /\
    Forall (fun y => In y values) args /\
    form np (prepared_basis np) x = TParam (encode EN b) args).
Proof.
  rewrite form_equation, basis_equation; cbn [inventory entries incoming].
  fold syntax EV EN graph values.
  destruct (Ssa.def syntax x) as [op args|b i|] eqn:Hdef; [| |now left].
  - destruct (pure np op && forallb
      (fun y => FinSet.mem EV y (FinSet.of_list EV values)) args) eqn:Hready; [|now left].
    apply andb_true_iff in Hready as [Hp Ha].
    right; left; exists op, args; repeat split; try assumption.
    apply Forall_forall; intros y Hy.
    apply (proj1 (listed_spec EV HV values y)).
    exact (proj1 (forallb_forall _ _) Ha y Hy).
  - destruct (FinSet.mem EN b (FinSet.of_list EN (Graph.entries graph))) eqn:Hentry;
      [now left|].
    destruct (NumberingIncoming.read_rows
      (Index.find EN b (NumberingIncoming.prepare syntax)) i) as [args|] eqn:Hargs;
      [|now left].
    destruct (forallb (fun y => FinSet.mem EV y (FinSet.of_list EV values)) args)
      eqn:Hlisted; [|now left].
    right; right; exists b, i, args; repeat split; try assumption.
    + intro Hb; apply (proj2 (listed_spec EN HN _ b)) in Hb; congruence.
    + apply Forall_forall; intros y Hy; apply (proj1 (listed_spec EV HV values y)).
      exact (proj1 (forallb_forall _ _) Hlisted y Hy).
Qed.

Variable candidate : partition_t EV.
Let all := domain EV values candidate.
Let cls := cached_class_c EV (tabulate EV (class_c EV candidate) all).

(** Related values are listed members of the actual proposed partition. *)
Definition related x y : Prop :=
  In x values /\ In y values /\ partition_equiv EV candidate x y.

(** Cached operand class equality reflects the actual supplied forest equivalence. *)
Theorem operand_classes x y :
  In x values -> In y values -> Cost.value (cls x) = Cost.value (cls y) ->
  related x y.
Proof.
  intros Hx Hy Heq; split; [exact Hx|split; [exact Hy|]].
  pose proof (cached_class_agrees np HV candidate x
    (domain_values EV values candidate x Hx)) as Hclassx.
  pose proof (cached_class_agrees np HV candidate y
    (domain_values EV values candidate y Hy)) as Hclassy.
  change (Cost.value (cls x) = class EV candidate x) in Hclassx.
  change (Cost.value (cls y) = class EV candidate y) in Hclassy.
  apply (proj1 (class_spec EV HV candidate x y)); congruence.
Qed.

Local Lemma argument_classes xs ys :
  Forall (fun y => In y values) xs -> Forall (fun y => In y values) ys ->
  map (fun y => Cost.value (cls y)) xs = map (fun y => Cost.value (cls y)) ys ->
  Forall2 related xs ys.
Proof.
  intro Hxs; revert ys; induction Hxs as [|x xs Hx Hxs IH]; intros ys Hys Heq;
    inversion Hys as [|y tail Hy Htail]; subst; cbn [map] in Heq; try discriminate.
  - constructor.
  - injection Heq as Hhead Hrest; constructor.
    + apply operand_classes; assumption.
    + apply IH; assumption.
Qed.

(** Each listed signature exposes either identity, a pure operation, or one parameter column. *)
Theorem signature_cases x : In x values ->
  signature np (prepare np) cls x = SigSingle (encode EV x) \/
  (exists op args, Ssa.def syntax x = Op op args /\ pure np op = true /\
    Forall (fun y => In y values) args /\
    signature np (prepare np) cls x =
      SigOp (encode (op_enc np) op) (map (fun y => Cost.value (cls y)) args)) \/
  (exists b i args, Ssa.def syntax x = Param b i /\ ~ In b (Graph.entries graph) /\
    NumberingIncoming.read_rows (Index.find EN b (NumberingIncoming.prepare syntax)) i =
      Some args /\
    Forall (fun y => In y values) args /\
    signature np (prepare np) cls x =
      SigParam (encode EN b) (map (fun y => Cost.value (cls y)) args)).
Proof.
  intro Hx; rewrite (signature_equation np HV cls x Hx).
  destruct (form_cases x) as [Hsingle|[Hop|Hparam]].
  - rewrite Hsingle, instantiate_equation; now left.
  - destruct Hop as [op [args [Hdef [Hp [Hargs Hform]]]]].
    rewrite Hform, instantiate_equation; right; left.
    exists op, args; repeat split; assumption.
  - destruct Hparam as [b [i [args [Hdef [Hentry [Hread [Hargs Hform]]]]]]].
    rewrite Hform, instantiate_equation; right; right.
    exists b, i, args; repeat split; assumption.
Qed.

(** Congruence relates operand classes and arguments of the same actual incoming edge. *)
Definition congruent x y : Prop :=
  x = y \/
  (exists op xs ys, Ssa.def syntax x = Op op xs /\ Ssa.def syntax y = Op op ys /\
    pure np op = true /\ Forall2 related xs ys) \/
  (exists b i j, Ssa.def syntax x = Param b i /\ Ssa.def syntax y = Param b j /\
    ~ In b (Graph.entries graph) /\
    forall e, In e (Cfg.edges (Ssa.cfg syntax)) -> Graph.target graph e = b ->
    exists a d, nth_error (Ssa.args syntax e) i = Some a /\
      nth_error (Ssa.args syntax e) j = Some d /\ related a d).

(** Equal complete signatures imply structural congruence without assuming value equality. *)
Theorem signature_congruent x y :
  In x values -> In y values ->
  signature np (prepare np) cls x = signature np (prepare np) cls y ->
  congruent x y.
Proof.
  intros Hx Hy Heq.
  destruct (signature_cases x Hx) as [Sx|[Sx|Sx]];
    destruct (signature_cases y Hy) as [Sy|[Sy|Sy]].
  - rewrite Sx, Sy in Heq; injection Heq as Hcode; left; now apply (encode_injective HV).
  - destruct Sy as [op [args [_ [_ [_ Sy]]]]]; rewrite Sx, Sy in Heq; discriminate.
  - destruct Sy as [b [i [args [_ [_ [_ [_ Sy]]]]]]]; rewrite Sx, Sy in Heq; discriminate.
  - destruct Sx as [op [args [_ [_ [_ Sx]]]]]; rewrite Sx, Sy in Heq; discriminate.
  - destruct Sx as [op [xs [Hdx [Hp [Hxs Sx]]]]].
    destruct Sy as [other [ys [Hdy [_ [Hys Sy]]]]].
    rewrite Sx, Sy in Heq; injection Heq as Hop Hargs.
    apply (encode_injective HK) in Hop; subst other; right; left.
    exists op, xs, ys; repeat split; try assumption; apply argument_classes; assumption.
  - destruct Sx as [op [args [_ [_ [_ Sx]]]]].
    destruct Sy as [b [i [other_args [_ [_ [_ [_ Sy]]]]]]].
    rewrite Sx, Sy in Heq; discriminate.
  - destruct Sx as [b [i [args [_ [_ [_ [_ Sx]]]]]]]; rewrite Sx, Sy in Heq; discriminate.
  - destruct Sx as [b [i [args [_ [_ [_ [_ Sx]]]]]]].
    destruct Sy as [op [other_args [_ [_ [_ Sy]]]]]; rewrite Sx, Sy in Heq; discriminate.
  - destruct Sx as [b [i [xs [Hdx [Hentry [Hreadx [Hxs Sx]]]]]]].
    destruct Sy as [other [j [ys [Hdy [_ [Hready [Hys Sy]]]]]]].
    rewrite Sx, Sy in Heq; injection Heq as Hb Hargs.
    apply (encode_injective HN) in Hb; subst other.
    right; right; exists b, i, j; repeat split; try assumption.
    intros e He Htarget.
    assert (Hin : In (b, NumberingIncoming.argument_index (Ssa.args syntax e))
      (Index.find EN b (NumberingIncoming.prepare syntax))).
    { rewrite <- Htarget; apply NumberingIncoming.incoming_member; assumption. }
    destruct (NumberingIncoming.read_rows_pair (fun z => Cost.value (cls z))
      _ _ _ _ _ b _ Hreadx Hready Hargs Hin)
      as [a [d [Ha [Hd [Hax [Hdy' Had]]]]]].
    rewrite !NumberingIncoming.argument_index_get in Ha, Hd.
    exists a, d; split; [exact Ha|split; [exact Hd|]].
    apply operand_classes; [| |exact Had].
    + exact (proj1 (Forall_forall _ _) Hxs a Hax).
    + exact (proj1 (Forall_forall _ _) Hys d Hdy').
Qed.

(** Acceptance proves congruence for every listed pair in each arbitrary proposed class. *)
Theorem check_congruent x y :
  check np candidate = true -> related x y -> congruent x y.
Proof.
  intros Hcheck [Hx [Hy Heq]]; apply signature_congruent; [exact Hx|exact Hy|].
  apply (check_signatures np HV candidate x y); assumption.
Qed.

End Congruence.

Section Observations.
Context {H S O N E V K G C : Type} (m : semantics S O)
  (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
  (eval : K -> list C -> option C) (ob : obs H S N E V)
  (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (ssa np))))
  (HV : encoding_laws (Ssa.val_enc (ssa np)))
  (HK : encoding_laws (op_enc np)) (candidate : partition_t (Ssa.val_enc (ssa np))).
Hypothesis Hobs : obs_laws m np sl eval ob.
Hypothesis Hcheck : check np candidate = true.

Local Lemma observed_arguments h rx ry xs ys cs ds :
  (forall a b c d,
    observation_rank ob h a + observation_rank ob h b < rx + ry ->
    related np candidate a b -> observation_ready ob h a -> observation_ready ob h b ->
    SsaLink.val sl (observation_state ob h) a = Some c ->
    SsaLink.val sl (observation_state ob h) b = Some d -> c = d) ->
  Forall2 (related np candidate) xs ys ->
  Forall2 (fun a c => observation_ready ob h a /\ observation_rank ob h a < rx /\
    SsaLink.val sl (observation_state ob h) a = Some c) xs cs ->
  Forall2 (fun b d => observation_ready ob h b /\ observation_rank ob h b < ry /\
    SsaLink.val sl (observation_state ob h) b = Some d) ys ds -> cs = ds.
Proof.
  intros Hsmaller Hrelated; revert cs ds.
  induction Hrelated as [|a b xs ys Hab Hrelated IH]; intros cs ds Hcs Hds.
  - inversion Hcs; inversion Hds; reflexivity.
  - inversion Hcs as [|a' c xs' cs' [Hra [Hrank_a Hval_a]] Htail_a]; subst.
    inversion Hds as [|b' d ys' ds' [Hrb [Hrank_b Hval_b]] Htail_b]; subst.
    f_equal.
    + eapply Hsmaller; try eassumption; lia.
    + apply IH; assumption.
Qed.

(** Ready, defined members of a checked class agree by descent on their observation ranks. *)
Theorem observations_equal h x y c d :
  related np candidate x y -> observation_ready ob h x -> observation_ready ob h y ->
  SsaLink.val sl (observation_state ob h) x = Some c ->
  SsaLink.val sl (observation_state ob h) y = Some d -> c = d.
Proof.
  assert (Hrank : forall n h x y c d,
    observation_rank ob h x + observation_rank ob h y = n ->
    related np candidate x y -> observation_ready ob h x -> observation_ready ob h y ->
    SsaLink.val sl (observation_state ob h) x = Some c ->
    SsaLink.val sl (observation_state ob h) y = Some d -> c = d).
  { intro n; induction n as [n IH] using lt_wf_ind;
      intros h' a b ca cb Hsum Hab Hra Hrb Hva Hvb.
    destruct (check_congruent np HN HV HK candidate a b Hcheck Hab)
      as [Heq|[Hops|Hparams]].
    - subst b; congruence.
    - destruct Hops as [op [xs [ys [Hda [Hdb [Hp Hargs]]]]]].
      destruct (observed_op Hobs h' a op xs ca Hra Hda Hp Hva) as [cs [Hcs Heca]].
      destruct (observed_op Hobs h' b op ys cb Hrb Hdb Hp Hvb) as [ds [Hds Hecb]].
      assert (Hsame : cs = ds).
      { eapply observed_arguments; [|exact Hargs|exact Hcs|exact Hds].
        intros u v cu cv Hless Huv Hru Hrv Hvu Hvv.
        eapply (IH (observation_rank ob h' u + observation_rank ob h' v));
          [lia|reflexivity|exact Huv|exact Hru|exact Hrv|exact Hvu|exact Hvv]. }
      subst ds; congruence.
    - destruct Hparams as [block [i [j [Hda [Hdb [Hentry Hargs]]]]]].
      destruct (observed_param Hobs h' a block i ca Hra Hda Hentry Hva)
        as [e [ha [za [la [ta [tra [Hpa [He [Htarget [Hza [Hrza [Hrank_a
          [Hvza Hactual_a]]]]]]]]]]]]].
      destruct (observed_param Hobs h' b block j cb Hrb Hdb Hentry Hvb)
        as [f [hb [zb [lb [tb [trb [Hpb [Hf [Htarget_b [Hzb [Hrzb [Hrank_b
          [Hvzb Hactual_b]]]]]]]]]]]]].
      rewrite Hpa in Hpb; injection Hpb as <- <-.
      destruct (Hargs e He Htarget) as [u [v [Hu [Hv Huv]]]].
      rewrite Hza in Hu; injection Hu as <-.
      rewrite Hzb in Hv; injection Hv as <-.
      eapply (IH (observation_rank ob ha za + observation_rank ob ha zb));
        [lia|reflexivity|exact Huv|exact Hrza|exact Hrzb|exact Hvza|exact Hvzb]. }
  apply (Hrank (observation_rank ob h x + observation_rank ob h y) h x y c d eq_refl).
Qed.

End Observations.

(** A ready defined classmate holds the freshly bound value in the same observation context. *)
Theorem check_sound {H S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (eval : K -> list C -> option C) (holds : G -> list C -> Prop) (ob : obs H S N E V)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (ssa np))))
    (HV : encoding_laws (Ssa.val_enc (ssa np))) (HK : encoding_laws (op_enc np))
    (candidate : partition_t (Ssa.val_enc (ssa np))) :
  ssa_laws m (ssa np) sl eval holds -> strict_ssa_laws m (ssa np) sl ->
  obs_laws m np sl eval ob -> check np candidate = true ->
  forall x y s events s' c, partition_equiv (Ssa.val_enc (ssa np)) candidate x y ->
    reachable_state m s -> step m s events s' ->
    In x (Ssa.values (ssa np)) -> In y (Ssa.values (ssa np)) ->
    SsaLink.val sl s' x = Some c -> SsaLink.val sl s x <> Some c ->
    (strictly_dominates (Cfg.graph (Ssa.cfg (ssa np)))
       (Ssa.home (ssa np) y) (Ssa.home (ssa np) x) \/
      exists b i j, Ssa.def (ssa np) x = Param b i /\ Ssa.def (ssa np) y = Param b j) ->
    (exists h d, observation_state ob h = s' /\ observation_ready ob h x /\
      observation_ready ob h y /\ SsaLink.val sl s' y = Some d) ->
    SsaLink.val sl s' y = Some c.
Proof.
  intros Hssa Hstrict Hobs Hcheck x y s events s' c Heq Hreachable Hstep Hx Hy
    Hval Hnew Hscope [h [d [Hstate [Hrx [Hry Hyval]]]]].
  subst s'.
  assert (Hcd : c = d).
  { apply (observations_equal m np sl eval ob HN HV HK candidate Hobs Hcheck h x y c d).
    - split; [exact Hx|split; [exact Hy|exact Heq]].
    - exact Hrx.
    - exact Hry.
    - exact Hval.
    - exact Hyval. }
  now rewrite Hcd.
Qed.

(** Ready defined class members agree at any dominated use in their shared observation context. *)
Theorem use_sound {H S O N E V K G C} (m : semantics S O)
    (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
    (eval : K -> list C -> option C) (holds : G -> list C -> Prop) (ob : obs H S N E V)
    (HN : encoding_laws (Cfg.node_enc (Ssa.cfg (ssa np))))
    (HV : encoding_laws (Ssa.val_enc (ssa np))) (HK : encoding_laws (op_enc np))
    (candidate : partition_t (Ssa.val_enc (ssa np))) :
  ssa_laws m (ssa np) sl eval holds -> strict_ssa_laws m (ssa np) sl ->
  obs_laws m np sl eval ob -> check np candidate = true ->
  forall x y s, partition_equiv (Ssa.val_enc (ssa np)) candidate x y ->
    reachable_state m s ->
    In x (Ssa.values (ssa np)) -> In y (Ssa.values (ssa np)) ->
    strictly_dominates (Cfg.graph (Ssa.cfg (ssa np))) (Ssa.home (ssa np) x)
      (Link.point (SsaLink.link sl) s) ->
    strictly_dominates (Cfg.graph (Ssa.cfg (ssa np))) (Ssa.home (ssa np) y)
      (Link.point (SsaLink.link sl) s) ->
    (exists h c d, observation_state ob h = s /\ observation_ready ob h x /\
      observation_ready ob h y /\ SsaLink.val sl s x = Some c /\ SsaLink.val sl s y = Some d) ->
    exists c, SsaLink.val sl s x = Some c /\ SsaLink.val sl s y = Some c.
Proof.
  intros Hssa Hstrict Hobs Hcheck x y s Heq Hreachable Hx Hy Hdomx Hdomy
    [h [c [d [Hstate [Hrx [Hry [Hvalx Hvaly]]]]]]].
  subst s; exists c; split; [exact Hvalx|].
  assert (Hcd : c = d).
  { apply (observations_equal m np sl eval ob HN HV HK candidate Hobs Hcheck h x y c d).
    - split; [exact Hx|split; [exact Hy|exact Heq]].
    - exact Hrx.
    - exact Hry.
    - exact Hvalx.
    - exact Hvaly. }
  now rewrite Hcd.
Qed.

End NumberingSignature.
