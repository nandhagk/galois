(** * Prepared scalar-evolution identities

    Source descriptors retain paid diagnostics and dependency support beside dense node IDs.
    For example, a query reads cached support and interns a vector of observation IDs.
    Builds on: BaseIntern, BaseMemoState and BaseCode. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import
  BaseEncoding BaseCode BaseEq BaseMap BaseMemo BaseMemoState BaseIntern BaseInternCost.
Import List.ListNotations Cost.Notations.

Module ScevPrepared.

(** Descriptors carry raw source data without defining another source syntax. *)
Record node (A D : Type) := Node {
  node_id : positive;
  original : A;
  diagnostic : positive;
  dependencies : list D
}.
Arguments Node {A D}.
Arguments node_id {A D}.
Arguments original {A D}.
Arguments diagnostic {A D}.
Arguments dependencies {A D}.

(** Structural codes are interned during preparation and source payloads are read by dense ID. *)
Record sources (A : Type) := Sources {
  codes : Intern.t positive;
  payloads : Map.t positive A
}.
Arguments Sources {A}.
Arguments codes {A}.
Arguments payloads {A}.

(** Source labels agree with their allocated structural codes. *)
Definition sources_wf {A} (E : encoding A) (s : sources A) : Prop :=
  Intern.wf positive_encoding (codes s) /\ Map.wf positive_encoding (payloads s) /\
  forall i source, Map.get positive_encoding i (payloads s) = Some source ->
    Intern.key_of i (codes s) = Some (encode E source).

(** Preparation extensions retain every earlier dense source observation. *)
Definition sources_extend {A} (s s' : sources A) : Prop :=
  forall i source, Map.get positive_encoding i (payloads s) = Some source ->
    Map.get positive_encoding i (payloads s') = Some source.

(** A descriptor records the source and support represented by the same allocated ID. *)
Definition node_valid {A D} (E : encoding A) (support : A -> list D)
    (s : sources A) (p : node A D) : Prop :=
  Map.get positive_encoding (node_id p) (payloads s) = Some (original p) /\
  diagnostic p = encode E (original p) /\ dependencies p = support (original p).

(** Empty source preparation initializes both public containers. *)
Definition empty_c {A} : Cost.t (sources A) :=
  let* names := Intern.empty_c in
  let* rows := Map.empty_c in
  Cost.ret (Sources names rows).

(** Empty source data has no allocated descriptor. *)
Definition empty {A} : sources A := Cost.value empty_c.

(** Empty construction establishes source consistency internally. *)
Theorem empty_wf {A} (E : encoding A) : sources_wf E empty.
Proof.
  split; [apply Intern.wf_empty|]. split; [apply Map.wf_empty|].
  intros i source Hget.
  change (Map.get positive_encoding i Map.empty = Some source) in Hget.
  rewrite Map.get_empty in Hget. discriminate.
Qed.

(** Actual Intern updates preserve old inverse observations without unfolding the allocator. *)
Theorem intern_key_of_preserved {K} (E : encoding K) (HE : encoding_laws E) key state :
  Intern.wf E state ->
  MemoState.extends (fun s i => Intern.key_of i s) state (snd (Intern.intern E key state)).
Proof.
  intros Hwf i old Hkey.
  apply (Intern.key_of_find E old i).
  - now apply Intern.intern_wf.
  - apply (Intern.find_intern_old E HE old key i state Hwf).
    exact (Intern.find_key_of E old i state Hwf Hkey).
Qed.

(** Smart constructors can register already-paid codes and support without scanning raw syntax. *)
Definition intern_node_c {A D} (source : A) code (support : list D) (s : sources A) :=
  let* allocated := Intern.intern_c positive_encoding code (codes s) in
  let* stored := Map.set_c positive_encoding (fst allocated) source (payloads s) in
  Cost.ret (Node (fst allocated) source code support, Sources (snd allocated) stored).

Local Lemma intern_node_value {A D} (source : A) code (support : list D) s :
  Cost.value (intern_node_c source code support s) =
    let allocated := Intern.intern positive_encoding code (codes s) in
    (Node (fst allocated) source code support,
      Sources (snd allocated)
        (Map.set positive_encoding (fst allocated) source (payloads s))).
Proof.
  unfold intern_node_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma stored_source_unique {A} (E : encoding A) (HE : encoding_laws E)
    s source code :
  sources_wf E s -> code = encode E source ->
  forall old,
    Map.get positive_encoding (fst (Intern.intern positive_encoding code (codes s)))
      (payloads s) = Some old -> old = source.
Proof.
  intros [Hnames [Hrows Hlink]] Hcode old Hget.
  pose proof (Hlink _ _ Hget) as Hmeaning.
  pose proof (intern_key_of_preserved positive_encoding positive_encoding_laws code
    (codes s) Hnames _ _ Hmeaning) as Hretained.
  pose proof (Intern.key_of_intern positive_encoding positive_encoding_laws code
    (codes s) Hnames) as Hnew.
  apply (encode_injective HE). congruence.
Qed.

(** Registering a correctly coded source preserves every old source and the registry invariant. *)
Theorem intern_node_correct {A D} (E : encoding A) (HE : encoding_laws E)
    (source : A) code (support : list D) s :
  sources_wf E s -> code = encode E source ->
  let result := Cost.value (intern_node_c source code support s) in
  sources_wf E (snd result) /\ sources_extend s (snd result) /\
    Map.get positive_encoding (node_id (fst result)) (payloads (snd result)) = Some source /\
    original (fst result) = source /\ diagnostic (fst result) = code /\
    dependencies (fst result) = support.
Proof.
  intros Hwf Hcode.
  pose proof Hwf as [Hnames [Hrows Hlink]].
  pose proof (Intern.intern_wf positive_encoding positive_encoding_laws code
    (codes s) Hnames) as Hnames'.
  pose proof (Intern.key_of_intern positive_encoding positive_encoding_laws code
    (codes s) Hnames) as Hnew.
  rewrite intern_node_value. cbn [fst snd node_id original diagnostic dependencies payloads codes].
  split.
  - split; [exact Hnames'|]. split; [now apply Map.wf_set|].
    intros i found Hget. cbn [payloads codes] in Hget |- *.
    rewrite Map.get_set in Hget by exact Hrows.
    destruct (eqb_spec positive_encoding positive_encoding_laws i
      (fst (Intern.intern positive_encoding code (codes s)))) as [Heq|Hne].
    + subst i. injection Hget as <-. now rewrite <- Hcode.
    + apply (intern_key_of_preserved positive_encoding positive_encoding_laws code
        (codes s) Hnames). exact (Hlink _ _ Hget).
  - split.
    + intros i old Hget. cbn [payloads codes]. rewrite Map.get_set by exact Hrows.
      destruct (eqb_spec positive_encoding positive_encoding_laws i
        (fst (Intern.intern positive_encoding code (codes s)))) as [Heq|Hne].
      * subst i. f_equal. symmetry.
        exact (stored_source_unique E HE s source code Hwf Hcode old Hget).
      * exact Hget.
    + split; [now apply Map.get_set_same|]. repeat split; reflexivity.
Qed.

(** Raw callers pay their source encoding and support traversal once at preparation. *)
Definition prepare_c {A D} (E : encoding A) (support_c : A -> Cost.t (list D))
    source (s : sources A) :=
  let* code := encode_c E source in
  let* support := support_c source in
  intern_node_c source code support s.

(** Preparation derives descriptor correspondence from its actual encoding and support callback. *)
Theorem prepare_correct {A D} (E : encoding A) (HE : encoding_laws E)
    (support_c : A -> Cost.t (list D)) source s :
  sources_wf E s ->
  let result := Cost.value (prepare_c E support_c source s) in
  sources_wf E (snd result) /\ sources_extend s (snd result) /\
    node_valid E (fun a => Cost.value (support_c a)) (snd result) (fst result) /\
    original (fst result) = source.
Proof.
  intro Hwf. unfold prepare_c. autorewrite with galois_cost.
  fold (encode E source).
  pose proof (intern_node_correct E HE source (encode E source)
    (Cost.value (support_c source)) s Hwf eq_refl) as Hresult.
  destruct (Cost.value (intern_node_c source (encode E source)
    (Cost.value (support_c source)) s)) as [p updated].
  destruct Hresult as [Hupdated [Hextend [Hget [Hsource [Hcode Hsupport]]]]].
  split; [exact Hupdated|]. split; [exact Hextend|]. split; [|exact Hsource].
  unfold node_valid. cbn [fst snd] in *.
  rewrite Hsource, Hcode, Hsupport. now split.
Qed.

(** Query signatures contain the dense node identity and the ordered observation identities. *)
Definition query := (positive * list positive)%type.

Definition query_encoding : encoding query :=
  pair_encoding positive_encoding (codec_enc (list_codec positive_codec)).

(** Compact query encoding distinguishes node identity, order and repeated observations. *)
Theorem query_encoding_laws : encoding_laws query_encoding.
Proof.
  apply pair_encoding_laws; [exact positive_encoding_laws|].
  apply codec_laws_injective, list_codec_laws, positive_codec_laws.
Qed.

(** Query construction reads cached support and never encodes the raw source or its diagnostics. *)
Definition query_c {A D} (observe_c : D -> Cost.t positive) (p : node A D) :=
  let* ids := map_c (fun d => Cost.step ;; observe_c d) (dependencies p) in
  Cost.ret (node_id p, ids).

(** Query construction retains support ordering and every actual observation attempt. *)
Theorem query_value {A D} (observe_c : D -> Cost.t positive) (p : node A D) :
  Cost.value (query_c observe_c p) =
    (node_id p, List.map (fun d => Cost.value (observe_c d)) (dependencies p)).
Proof.
  unfold query_c. autorewrite with galois_cost. reflexivity.
Qed.

(** Every dependency occurrence pays its traversal, observation invocation and callback charge. *)
Theorem query_cost {A D} (observe_c : D -> Cost.t positive) (p : node A D) :
  Cost.ticks (query_c observe_c p) =
    fold_right (fun d n => (2 + Cost.ticks (observe_c d) + n)%N) 0%N (dependencies p).
Proof.
  unfold query_c. autorewrite with galois_cost.
  induction (dependencies p) as [|d rest IH]; cbn [fold_right];
    autorewrite with galois_cost; [reflexivity|lia].
Qed.

(** Signature widths use dense node and observation widths, independently of diagnostic width. *)
Theorem query_bits i ids :
  key_bits query_encoding (i, ids) =
    (13 + 2 * key_bits positive_encoding i + 4 * N.of_nat (length ids) +
      4 * fold_right (fun j n => key_bits positive_encoding j + n)%N 0%N ids)%N.
Proof.
  transitivity (7 + 2 * key_bits positive_encoding i +
    2 * key_bits (codec_enc (list_codec positive_codec)) ids)%N.
  - apply pair_encoding_bits.
  - rewrite list_codec_bits. fold positive_encoding. lia.
Qed.

(** The signature serializer's coefficient is derived from the public scalar, list and pair laws. *)
Definition query_encode_k := (7 + 2 * encode_k)%N.

(** Query serialization has a closed coefficient and no caller-supplied helper price. *)
Theorem query_encoding_cost : encoding_cost_laws query_encoding query_encode_k.
Proof.
  unfold query_encoding, query_encode_k.
  replace (7 + 2 * encode_k)%N with (1 + (1 + encode_k + 2) + encode_k + 3)%N by lia.
  apply pair_encoding_cost_laws; [exact positive_encoding_cost_laws|].
  apply list_codec_cost_laws. exact positive_encoding_cost_laws.
Qed.

(** Compact context registration pays construction and actual interning on every attempt. *)
Definition register_c {A D} (observe_c : D -> Cost.t positive) (p : node A D)
    (contexts : Intern.t query) :=
  let* key := query_c observe_c p in
  Intern.intern_c query_encoding key contexts.

(** Registration retains the actual context allocation result. *)
Theorem register_value {A D} (observe_c : D -> Cost.t positive) (p : node A D) contexts :
  Cost.value (register_c observe_c p contexts) =
    Intern.intern query_encoding (Cost.value (query_c observe_c p)) contexts.
Proof.
  unfold register_c. rewrite Cost.value_bind. reflexivity.
Qed.

(** The registration charge includes repeated observations, key serialization and frontier width. *)
Theorem register_cost {A D} (observe_c : D -> Cost.t positive) (p : node A D) contexts :
  (Cost.ticks (register_c observe_c p contexts) <=
    fold_right (fun d n => 2 + Cost.ticks (observe_c d) + n)%N 0%N (dependencies p) +
    InternCost.intern_k +
    2 * (Cost.ticks (encode_c query_encoding (Cost.value (query_c observe_c p))) +
      key_bits query_encoding (Cost.value (query_c observe_c p))) +
    N.pos (Pos.size (Intern.next contexts)))%N.
Proof.
  unfold register_c. rewrite Cost.ticks_bind.
  pose proof (InternCost.intern_cost Map.cost_laws_hold query_encoding
    (Cost.value (query_c observe_c p)) contexts) as Hcost.
  rewrite query_cost. lia.
Qed.

(** All registration attempts pay support work and the derived compact-key and frontier terms. *)
Theorem register_numeric_cost {A D} (observe_c : D -> Cost.t positive)
    (p : node A D) contexts :
  (Cost.ticks (register_c observe_c p contexts) <=
    fold_right (fun d n => 2 + Cost.ticks (observe_c d) + n)%N 0%N (dependencies p) +
    InternCost.intern_k + 2 * (query_encode_k + 1) *
      key_bits query_encoding (Cost.value (query_c observe_c p)) +
    N.pos (Pos.size (Intern.next contexts)))%N.
Proof.
  pose proof (register_cost observe_c p contexts) as Hregister.
  pose proof (encode_cost_bound query_encoding_cost (Cost.value (query_c observe_c p))) as Hencode.
  nia.
Qed.

(** Returned context IDs fit the dense final context table even on a repeated request. *)
Theorem registered_id_bits {A D} (observe_c : D -> Cost.t positive) (p : node A D) contexts :
  Intern.wf query_encoding contexts ->
  let registered := Cost.value (register_c observe_c p contexts) in
  (key_bits positive_encoding (fst registered) <=
    N.pos (Pos.size (Pos.of_succ_nat (Intern.size (snd registered)))))%N.
Proof.
  intro Hwf. rewrite register_value.
  apply (InternCost.dense_id_bits query_encoding query_encoding_laws
    (Cost.value (query_c observe_c p))).
  - now apply Intern.intern_wf; [exact query_encoding_laws|].
  - now apply Intern.find_intern.
Qed.

Fixpoint decode_ids {B} (values : Intern.t B) (ids : list positive) : option (list B) :=
  match ids with
  | [] => Some []
  | i :: rest =>
    match Intern.key_of i values, decode_ids values rest with
    | Some value, Some tail => Some (value :: tail)
    | _, _ => None
    end
  end.

Local Lemma decode_ids_observed {D B} (values : Intern.t B)
    (observe_id : D -> positive) (observe : D -> B) deps :
  (forall d, In d deps -> Intern.key_of (observe_id d) values = Some (observe d)) ->
  decode_ids values (List.map observe_id deps) = Some (List.map observe deps).
Proof.
  induction deps as [|d rest IH]; intro Hobserve; [reflexivity|].
  cbn [List.map decode_ids].
  rewrite Hobserve by now left.
  rewrite IH; [reflexivity|intros x Hx; apply Hobserve; now right].
Qed.

(** Decoding a cached snapshot is stable under actual observation-registry extension. *)
Theorem decode_ids_preserved {B} (values values' : Intern.t B) ids decoded :
  MemoState.extends (fun s i => Intern.key_of i s) values values' ->
  decode_ids values ids = Some decoded -> decode_ids values' ids = Some decoded.
Proof.
  intro Hextend; revert decoded; induction ids as [|i rest IH]; intros decoded Hdecode.
  - exact Hdecode.
  - cbn [decode_ids] in *.
    destruct (Intern.key_of i values) as [value|] eqn:Hvalue; [|discriminate].
    destruct (decode_ids values rest) as [tail|] eqn:Htail; [|discriminate].
    rewrite (Hextend i value Hvalue), (IH tail eq_refl). exact Hdecode.
Qed.

(** Query meaning decodes the source and dependency observations before applying a pure reference. *)
Definition query_meaning {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R) (source_rows : sources A)
    (values : Intern.t B) (key : query) : option R :=
  match Map.get positive_encoding (fst key) (payloads source_rows),
    decode_ids values (snd key) with
  | Some source, Some observations =>
    Some (reference source (combine (support source) observations))
  | _, _ => None
  end.

Local Lemma combine_observed {D B} (observe : D -> B) deps :
  combine deps (List.map observe deps) = List.map (fun d => (d, observe d)) deps.
Proof.
  induction deps as [|d rest IH]; cbn [List.map combine]; [reflexivity|now rewrite IH].
Qed.

(** Allocated observation identities establish query meaning without a compiler-result premise. *)
Theorem query_meaning_allocated {A D B R} (E : encoding A) (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values
    (observe_c : D -> Cost.t positive) (observe : D -> B) p :
  node_valid E support source_rows p ->
  (forall d, In d (dependencies p) ->
    Intern.key_of (Cost.value (observe_c d)) values = Some (observe d)) ->
  query_meaning support reference source_rows values (Cost.value (query_c observe_c p)) =
    Some (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p))).
Proof.
  intros [Hsource [Hcode Hsupport]] Hobserve.
  pose proof (decode_ids_observed values _ observe _ Hobserve) as Hdecode.
  rewrite query_value.
  change (match Map.get positive_encoding (node_id p) (payloads source_rows) with
    | Some source =>
      match decode_ids values (List.map (fun d => Cost.value (observe_c d)) (dependencies p)) with
      | Some observations => Some (reference source (combine (support source) observations))
      | None => None
      end
    | None => None
    end = Some (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p)))).
  rewrite Hsource.
  transitivity (Some (reference (original p)
    (combine (support (original p)) (List.map observe (dependencies p))))).
  - exact (f_equal (fun observations =>
      option_map (fun xs => reference (original p) (combine (support (original p)) xs))
        observations) Hdecode).
  - rewrite <- Hsupport, combine_observed. reflexivity.
Qed.

(** Earlier defined query meanings survive both source preparation and observation allocation. *)
Theorem query_meaning_preserved {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows source_rows' values values' key value :
  sources_extend source_rows source_rows' ->
  MemoState.extends (fun s i => Intern.key_of i s) values values' ->
  query_meaning support reference source_rows values key = Some value ->
  query_meaning support reference source_rows' values' key = Some value.
Proof.
  intros Hsource Hvalues Hmeaning. unfold query_meaning in *.
  destruct (Map.get positive_encoding (fst key) (payloads source_rows))
    as [source|] eqn:Hrow; [|discriminate].
  destruct (decode_ids values (snd key)) as [observations|] eqn:Hdecode; [|discriminate].
  rewrite (Hsource _ _ Hrow), (decode_ids_preserved values values' _ _ Hvalues Hdecode).
  exact Hmeaning.
Qed.

(** Registered compact contexts have meanings only when both their source and observations decode. *)
Definition context_meaning {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values
    (contexts : Intern.t query) i :=
  match Intern.key_of i contexts with
  | Some key => query_meaning support reference source_rows values key
  | None => None
  end.

(** Registration makes the same decoded query available at its returned dense context ID. *)
Theorem register_meaning {A D B R} (E : encoding A) (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values observe_c observe p contexts :
  node_valid E support source_rows p -> Intern.wf query_encoding contexts ->
  (forall d, In d (dependencies p) ->
    Intern.key_of (Cost.value (observe_c d)) values = Some (observe d)) ->
  let registered := Cost.value (register_c observe_c p contexts) in
  context_meaning support reference source_rows values (snd registered) (fst registered) =
    Some (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p))).
Proof.
  intros Hnode Hcontexts Hobserve. rewrite register_value.
  unfold context_meaning.
  rewrite (Intern.key_of_intern query_encoding query_encoding_laws _ _ Hcontexts).
  exact (query_meaning_allocated E support reference _ _ _ _ _ Hnode Hobserve).
Qed.

(** One shared transport rule covers growth of the source, observation and context registries. *)
Theorem context_meaning_preserved {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R)
    source_rows source_rows' values values' contexts contexts' i value :
  sources_extend source_rows source_rows' ->
  MemoState.extends (fun s j => Intern.key_of j s) values values' ->
  MemoState.extends (fun s j => Intern.key_of j s) contexts contexts' ->
  context_meaning support reference source_rows values contexts i = Some value ->
  context_meaning support reference source_rows' values' contexts' i = Some value.
Proof.
  intros Hsource Hvalues Hcontexts Hmeaning. unfold context_meaning in *.
  destruct (Intern.key_of i contexts) as [key|] eqn:Hkey; [|discriminate].
  rewrite (Hcontexts i key Hkey).
  exact (query_meaning_preserved support reference _ _ _ _ _ _ Hsource Hvalues Hmeaning).
Qed.

(** A real compact-context allocation preserves earlier meanings in the same fixed source snapshot. *)
Theorem register_preserved {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values
    (observe_c : D -> Cost.t positive) (p : node A D) contexts :
  Intern.wf query_encoding contexts ->
  MemoState.extends (context_meaning support reference source_rows values)
    contexts (snd (Cost.value (register_c observe_c p contexts))).
Proof.
  intros Hwf i value Hmeaning. rewrite register_value.
  eapply context_meaning_preserved; [| | |exact Hmeaning].
  - intros j source Hget. exact Hget.
  - apply MemoState.extends_refl.
  - now apply intern_key_of_preserved; [exact query_encoding_laws|].
Qed.

(** Query execution carries the growing context registry and arbitrary consumer side data together. *)
Definition memo_c {A D R S} observe_c (p : node A D)
    (miss_c : Memo.t positive R -> (Intern.t query * S) ->
      Cost.t (MemoState.result R (Intern.t query * S)))
    table (state : Intern.t query * S) :=
  let* registered := register_c observe_c p (fst state) in
  MemoState.run_c (fst registered) miss_c table (snd registered, snd state).

(** A context's semantic interpretation ignores diagnostic and child-cache side data. *)
Definition memo_meaning {A D B R S} (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values (state : Intern.t query * S) :=
  context_meaning support reference source_rows values (fst state).

(** Shared agreement derives the allocated-query premise and transports the same child-returned state. *)
Theorem memo_agrees {A D B R S} (E : encoding A) (support : A -> list D)
    (reference : A -> list (D * B) -> R) source_rows values
    (side_valid : S -> Prop) observe_c observe p miss_c table state :
  node_valid E support source_rows p ->
  Intern.wf query_encoding (fst state) -> side_valid (snd state) ->
  MemoState.valid (memo_meaning support reference source_rows values) state table ->
  (forall d, In d (dependencies p) ->
    Intern.key_of (Cost.value (observe_c d)) values = Some (observe d)) ->
  (forall m current i,
    MemoState.valid (memo_meaning support reference source_rows values) current m ->
    Intern.wf query_encoding (fst current) -> side_valid (snd current) ->
    Intern.key_of i (fst current) = Some (Cost.value (query_c observe_c p)) ->
    Map.get positive_encoding i m = None ->
    MemoState.result_valid (memo_meaning support reference source_rows values)
      (fun s => Intern.wf query_encoding (fst s) /\ side_valid (snd s))
      current (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p)))
      (Cost.value (miss_c m current))) ->
  MemoState.result_valid (memo_meaning support reference source_rows values)
    (fun s => Intern.wf query_encoding (fst s) /\ side_valid (snd s))
    state (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p)))
    (fst (Cost.value (memo_c observe_c p miss_c table state))).
Proof.
  intros Hnode Hwf Hside Hvalid Hobserve Hmiss.
  pose proof (register_preserved support reference source_rows values observe_c p
    (fst state) Hwf) as Hextend.
  pose proof (register_meaning E support reference source_rows values observe_c observe p
    (fst state) Hnode Hwf Hobserve) as Hmeaning.
  pose proof (Intern.intern_wf query_encoding query_encoding_laws
    (Cost.value (query_c observe_c p)) (fst state) Hwf) as Hregistered.
  pose proof (Intern.key_of_intern query_encoding query_encoding_laws
    (Cost.value (query_c observe_c p)) (fst state) Hwf) as Hkey.
  rewrite <- register_value in Hregistered.
  rewrite <- register_value in Hkey.
  unfold memo_c. rewrite Cost.value_bind.
  remember (Cost.value (register_c observe_c p (fst state))) as registered.
  assert (Hstate : MemoState.extends (memo_meaning support reference source_rows values)
    state (snd registered, snd state)).
  { intros i value Hvalue. exact (Hextend i value Hvalue). }
  pose proof (MemoState.valid_transport _ _ _ _ Hstate Hvalid) as Hcache.
  pose proof (MemoState.run_agrees (memo_meaning support reference source_rows values)
    (fun s => Intern.wf query_encoding (fst s) /\ side_valid (snd s))
    (fst registered) _ miss_c table (snd registered, snd state)
    Hcache (conj Hregistered Hside) Hmeaning
    (fun Habsent => Hmiss table _ (fst registered)
      Hcache Hregistered Hside Hkey Habsent)) as Hagrees.
  rewrite <- MemoState.run_c_value in Hagrees.
  destruct (Cost.value (MemoState.run_c (fst registered) miss_c table
    (snd registered, snd state))) as [[[result updated] final] hit].
  change (MemoState.result_valid (memo_meaning support reference source_rows values)
    (fun s => Intern.wf query_encoding (fst s) /\ side_valid (snd s))
    (snd registered, snd state)
    (reference (original p) (List.map (fun d => (d, observe d)) (dependencies p)))
    ((result, updated), final)) in Hagrees.
  destruct Hagrees as [Hresult [Hupdated [Hfinal Hextension]]].
  split; [exact Hresult|]. split; [exact Hupdated|]. split; [exact Hfinal|].
  exact (MemoState.extends_trans _ _ _ _ Hstate Hextension).
Qed.

(** Query execution exposes registration, lookup, selected miss and insertion as the actual costs. *)
Theorem memo_cost_equation {A D R S} observe_c (p : node A D)
    (miss_c : Memo.t positive R -> (Intern.t query * S) ->
      Cost.t (MemoState.result R (Intern.t query * S))) table state :
  Cost.ticks (memo_c observe_c p miss_c table state) =
    (Cost.ticks (register_c observe_c p (fst state)) +
      let registered := Cost.value (register_c observe_c p (fst state)) in
      Cost.ticks (MemoState.run_c (fst registered) miss_c table
        (snd registered, snd state)))%N.
Proof.
  unfold memo_c. rewrite Cost.ticks_bind. reflexivity.
Qed.

(** Source registration pays interning of the supplied diagnostic and the dense payload insertion. *)
Theorem intern_node_cost {A D} (source : A) code (support : list D) s :
  Cost.ticks (intern_node_c source code support s) =
    (Cost.ticks (Intern.intern_c positive_encoding code (codes s)) +
      Cost.ticks (Map.set_c positive_encoding
        (fst (Intern.intern positive_encoding code (codes s))) source (payloads s)))%N.
Proof.
  unfold intern_node_c. autorewrite with galois_cost.
  fold (Intern.intern positive_encoding code (codes s)). lia.
Qed.

(** Raw preparation charges the source encoder, support callback and the actual registry update. *)
Theorem prepare_cost {A D} (E : encoding A) (support_c : A -> Cost.t (list D)) source s :
  Cost.ticks (prepare_c E support_c source s) =
    (Cost.ticks (encode_c E source) + Cost.ticks (support_c source) +
      Cost.ticks (intern_node_c source (encode E source)
        (Cost.value (support_c source)) s))%N.
Proof.
  unfold prepare_c. autorewrite with galois_cost. fold (encode E source). lia.
Qed.

End ScevPrepared.
