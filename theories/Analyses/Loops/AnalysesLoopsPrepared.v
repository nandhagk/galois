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
  Cost.step ;;
  let* code := encode_c E source in
  Cost.step ;;
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
    (2 + Cost.ticks (encode_c E source) + Cost.ticks (support_c source) +
      Cost.ticks (intern_node_c source (encode E source)
        (Cost.value (support_c source)) s))%N.
Proof.
  unfold prepare_c. autorewrite with galois_cost. fold (encode E source). lia.
Qed.

(** A recursive consumer retains source, observation and context allocations together. *)
Record registry (A B : Type) := Registry {
  source_names : sources A;
  value_names : Intern.t B;
  context_names : Intern.t query
}.
Arguments Registry {A B}.
Arguments source_names {A B}.
Arguments value_names {A B}.
Arguments context_names {A B}.

(** Registry well-formedness concerns allocation and decoding independently of any compiler. *)
Definition registry_wf {A B} (EA : encoding A) (EB : encoding B) (r : registry A B) :=
  sources_wf EA (source_names r) /\ Intern.wf EB (value_names r) /\
    Intern.wf query_encoding (context_names r).

(** Extensions preserve the actual public observations of all three registries. *)
Definition registry_extends {A B} (a b : registry A B) : Prop :=
  sources_extend (source_names a) (source_names b) /\
  MemoState.extends (fun s i => Intern.key_of i s) (value_names a) (value_names b) /\
  MemoState.extends (fun s i => Intern.key_of i s) (context_names a) (context_names b).

(** An unchanged registry preserves all its observations. *)
Theorem registry_extends_refl {A B} (r : registry A B) : registry_extends r r.
Proof.
  split; [intros i source Hget; exact Hget|].
  split; apply MemoState.extends_refl.
Qed.

(** Consecutive actual allocation extensions compose. *)
Theorem registry_extends_trans {A B} (a b c : registry A B) :
  registry_extends a b -> registry_extends b c -> registry_extends a c.
Proof.
  intros [Hab [Hvalues Hcontexts]] [Hbc [Hvalues' Hcontexts']].
  split; [intros i source Hget; apply Hbc, Hab, Hget|].
  split; eapply MemoState.extends_trans; eassumption.
Qed.

(** Registry meanings decode the immutable observations named by each cached context. *)
Definition registry_meaning {A D B R} (support : A -> list D)
    (reference : A -> list (D * B) -> R) (r : registry A B) :=
  context_meaning support reference (source_names r) (value_names r) (context_names r).

(** The previously proved three-registry transport supplies every consumer's cache transport. *)
Theorem registry_meaning_preserved {A D B R} support reference (a b : registry A B) :
  registry_extends a b ->
  MemoState.extends (@registry_meaning A D B R support reference) a b.
Proof.
  intros [Hsource [Hvalues Hcontexts]] i value Hmeaning.
  exact (context_meaning_preserved support reference _ _ _ _ _ _ _ _
    Hsource Hvalues Hcontexts Hmeaning).
Qed.

(** Snapshot capture interns each actual observation and threads the returned value registry. *)
Fixpoint capture_c {D B} (EB : encoding B) (observe_c : D -> Cost.t B)
    (deps : list D) (values : Intern.t B) : Cost.t (list positive * Intern.t B) :=
  match deps with
  | [] => Cost.ret ([], values)
  | d :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* observed := observe_c d in
    let* allocated := Intern.intern_c EB observed values in
    let* tail := capture_c EB observe_c rest (snd allocated) in
    Cost.ret (fst allocated :: fst tail, snd tail)
  end.

(** Capture charges each occurrence and continues from its actual returned observation registry. *)
Theorem capture_cost_equation {D B} (EB : encoding B) (observe_c : D -> Cost.t B) deps values :
  Cost.ticks (capture_c EB observe_c deps values) =
    match deps with
    | [] => 0%N
    | d :: rest =>
      (2 + Cost.ticks (observe_c d) +
        Cost.ticks (Intern.intern_c EB (Cost.value (observe_c d)) values) +
        Cost.ticks (capture_c EB observe_c rest
          (snd (Intern.intern EB (Cost.value (observe_c d)) values))))%N
    end.
Proof.
  destruct deps as [|d rest]; cbn [capture_c]; autorewrite with galois_cost;
    [reflexivity|fold (Intern.intern EB (Cost.value (observe_c d)) values); lia].
Qed.

(** Actual snapshot IDs decode in the final value registry and every earlier value survives. *)
Theorem capture_correct {D B} (EB : encoding B) (HB : encoding_laws EB)
    (observe_c : D -> Cost.t B) deps values :
  Intern.wf EB values ->
  let captured := Cost.value (capture_c EB observe_c deps values) in
  Intern.wf EB (snd captured) /\
  MemoState.extends (fun s i => Intern.key_of i s) values (snd captured) /\
  decode_ids (snd captured) (fst captured) =
    Some (List.map (fun d => Cost.value (observe_c d)) deps).
Proof.
  revert values; induction deps as [|d rest IH]; intros values Hwf.
  - split; [exact Hwf|]. split; [apply MemoState.extends_refl|reflexivity].
  - cbn [capture_c]. autorewrite with galois_cost.
    fold (Intern.intern EB (Cost.value (observe_c d)) values).
    pose proof (Intern.intern_wf EB HB (Cost.value (observe_c d)) values Hwf) as Hfirst.
    pose proof (intern_key_of_preserved EB HB (Cost.value (observe_c d)) values Hwf)
      as Hextend.
    pose proof (Intern.key_of_intern EB HB (Cost.value (observe_c d)) values Hwf) as Hkey.
    specialize (IH _ Hfirst).
    destruct (Cost.value (capture_c EB observe_c rest
      (snd (Intern.intern EB (Cost.value (observe_c d)) values)))) as [ids final].
    destruct IH as [Hfinal [Htail Hdecode]].
    cbn [fst snd] in Hfinal, Htail, Hdecode.
    split; [exact Hfinal|]. split.
    + exact (MemoState.extends_trans _ _ _ _ Hextend Htail).
    + cbn [fst snd List.map decode_ids].
      rewrite (Htail _ _ Hkey), Hdecode. reflexivity.
Qed.

(** Query preparation charges the raw boundary, observation capture and compact context allocation. *)
Definition prepare_query_c {A D B} (EA : encoding A) (EB : encoding B)
    (support_c : A -> Cost.t (list D)) (observe_c : D -> Cost.t B)
    source (r : registry A B) :=
  let* prepared := prepare_c EA support_c source (source_names r) in
  let* captured := capture_c EB observe_c (dependencies (fst prepared)) (value_names r) in
  let* context := Intern.intern_c query_encoding
    (node_id (fst prepared), fst captured) (context_names r) in
  Cost.ret (fst context, Registry (snd prepared) (snd captured) (snd context)).

(** Query preparation retains raw boundary, observed-value interning and compact-context charges. *)
Theorem prepare_query_cost_equation {A D B} (EA : encoding A) (EB : encoding B)
    (support_c : A -> Cost.t (list D)) (observe_c : D -> Cost.t B) source (r : registry A B) :
  Cost.ticks (prepare_query_c EA EB support_c observe_c source r) =
    let prepared := Cost.value (prepare_c EA support_c source (source_names r)) in
    let captured :=
      Cost.value (capture_c EB observe_c (dependencies (fst prepared)) (value_names r)) in
    (Cost.ticks (prepare_c EA support_c source (source_names r)) +
      Cost.ticks (capture_c EB observe_c (dependencies (fst prepared)) (value_names r)) +
      Cost.ticks (Intern.intern_c query_encoding
        (node_id (fst prepared), fst captured) (context_names r)))%N.
Proof.
  unfold prepare_query_c. autorewrite with galois_cost. lia.
Qed.

(** The allocated query has its decoded meaning before any miss callback runs. *)
Theorem prepare_query_correct {A D B R} (EA : encoding A) (HA : encoding_laws EA)
    (EB : encoding B) (HB : encoding_laws EB) (support_c : A -> Cost.t (list D))
    (reference : A -> list (D * B) -> R) observe_c source r :
  registry_wf EA EB r ->
  let prepared := Cost.value (prepare_query_c EA EB support_c observe_c source r) in
  registry_wf EA EB (snd prepared) /\ registry_extends r (snd prepared) /\
  registry_meaning (fun a => Cost.value (support_c a)) reference (snd prepared) (fst prepared) =
    Some (reference source
      (List.map (fun d => (d, Cost.value (observe_c d))) (Cost.value (support_c source)))).
Proof.
  intros [Hsources [Hvalues Hcontexts]].
  pose proof (prepare_correct EA HA support_c source (source_names r) Hsources) as Hsource.
  unfold prepare_query_c. autorewrite with galois_cost.
  destruct (Cost.value (prepare_c EA support_c source (source_names r))) as [p sources'].
  destruct Hsource as [Hsources' [Hsource_ext [Hnode Horiginal]]].
  cbn [fst snd] in Hsources', Hsource_ext, Hnode, Horiginal |- *.
  pose proof (capture_correct EB HB observe_c (dependencies p) (value_names r) Hvalues) as Hcap.
  destruct (Cost.value (capture_c EB observe_c (dependencies p) (value_names r)))
    as [ids values'].
  destruct Hcap as [Hvalues' [Hvalue_ext Hdecode]].
  cbn [fst snd] in Hvalues', Hvalue_ext, Hdecode |- *.
  fold (Intern.intern query_encoding (node_id p, ids) (context_names r)).
  pose proof (Intern.intern_wf query_encoding query_encoding_laws
    (node_id p, ids) (context_names r) Hcontexts) as Hcontexts'.
  pose proof (intern_key_of_preserved query_encoding query_encoding_laws
    (node_id p, ids) (context_names r) Hcontexts) as Hcontext_ext.
  pose proof (Intern.key_of_intern query_encoding query_encoding_laws
    (node_id p, ids) (context_names r) Hcontexts) as Hcontext_key.
  split; [exact (conj Hsources' (conj Hvalues' Hcontexts'))|].
  split; [exact (conj Hsource_ext (conj Hvalue_ext Hcontext_ext))|].
  unfold registry_meaning; cbn [fst snd source_names value_names context_names].
  unfold context_meaning. rewrite Hcontext_key.
  unfold query_meaning. cbn [fst snd].
  destruct Hnode as [Hrow [Hcode Hdeps]].
  rewrite Hrow. cbv beta iota zeta.
  transitivity (Some (reference (original p)
    (combine (Cost.value (support_c (original p)))
      (List.map (fun d => Cost.value (observe_c d)) (dependencies p))))).
  - exact (f_equal (fun observations =>
      option_map (fun xs => reference (original p)
        (combine (Cost.value (support_c (original p))) xs)) observations) Hdecode).
  - rewrite <- Hdeps, combine_observed, Horiginal, Hdeps, Horiginal. reflexivity.
Qed.

(** Sessions pair the dense cache with the registry that gives every stored ID its meaning. *)
Definition session A B R := (Memo.t positive R * registry A B)%type.
Definition answer A B R S := ((R * session A B R) * S)%type.

(** Session validity is independent of the consumer's current environment and diagnostic trace. *)
Definition session_valid {A D B R} EA EB support reference (m : session A B R) : Prop :=
  registry_wf EA EB (snd m) /\
    MemoState.valid (@registry_meaning A D B R support reference) (snd m) (fst m).

(** A result retains its actual allocation extension beside semantic cache validity. *)
Definition answer_valid {A D B R S} EA EB support reference (P : S -> Prop)
    (initial : session A B R) expected (out : answer A B R S) : Prop :=
  let '((value, updated), side) := out in
  value = expected /\ @session_valid A D B R EA EB support reference updated /\
    registry_extends (snd initial) (snd updated) /\ P side.

(** Forgetting extension and side evidence retains the result and its returned cache validity. *)
Theorem answer_forget {A D B R S} EA EB support reference (P : S -> Prop)
    (initial : session A B R) expected (out : answer A B R S) :
  @answer_valid A D B R S EA EB support reference P initial expected out ->
  let '((value, updated), _) := out in
  value = expected /\ session_valid EA EB support reference updated.
Proof.
  destruct out as [[value updated] side].
  intros [Hvalue [Hvalid _]]. exact (conj Hvalue Hvalid).
Qed.

(** Empty sessions construct all owned registries and the shared cache through costed interfaces. *)
Definition session_empty_c {A B R} : Cost.t (session A B R) :=
  let* rows := @empty_c A in
  let* values := @Intern.empty_c B in
  let* contexts := @Intern.empty_c query in
  let* table := @Memo.empty_c positive R in
  Cost.ret (table, Registry rows values contexts).

Definition session_empty {A B R} : session A B R := Cost.value session_empty_c.

Arguments session_empty_c {A B R} : simpl never.
Arguments session_empty {A B R} : simpl never.

(** Empty-session validity needs neither a semantic environment nor any allocated query. *)
Theorem session_empty_valid {A D B R} EA EB support reference :
  @session_valid A D B R EA EB support reference session_empty.
Proof.
  split.
  - split; [apply empty_wf|]. split; apply Intern.wf_empty.
  - apply MemoState.valid_empty.
Qed.

Definition unpack {A B R S} (out : answer A B R S)
    : MemoState.result R (registry A B * S) :=
  let '((value, (table, names)), side) := out in ((value, table), (names, side)).

Local Lemma answer_unpack_valid {A D B R S} EA EB support reference (P : S -> Prop)
    (protected : registry A B) (current : session A B R) events expected out :
  registry_extends protected (snd current) ->
  @answer_valid A D B R S EA EB support reference P current expected out ->
  MemoState.result_valid
    (fun state => registry_meaning support reference (fst state))
    (fun state => registry_wf EA EB (fst state) /\ P (snd state) /\
      registry_extends protected (fst state))
    (snd current, events) expected (unpack out).
Proof.
  intros Hprotected Hout.
  destruct out as [[value [table names]] side].
  destruct Hout as [Hvalue [[Hnames Htable] [Hextends Hside]]].
  split; [exact Hvalue|]. split; [exact Htable|]. split.
  - split; [exact Hnames|]. split; [exact Hside|].
    exact (registry_extends_trans _ _ _ Hprotected Hextends).
  - exact (registry_meaning_preserved _ _ _ _ Hextends).
Qed.

Definition pack {A B R S} (out : MemoState.result R (registry A B * S))
    : answer A B R S :=
  let '((value, table), (names, side)) := out in ((value, (table, names)), side).

(** A selected miss retains the recursively returned source, value and context registries. *)
Definition run_c {A D B R S} EA EB support_c observe_c source
    (miss_c : session A B R -> S -> Cost.t (answer A B R S)) m side :=
  let* prepared := @prepare_query_c A D B EA EB support_c observe_c source (snd m) in
  let* out := MemoState.run_c (fst prepared)
    (fun table current => Cost.map unpack (miss_c (table, fst current) (snd current)))
    (fst m) (snd prepared, side) in
  Cost.ret (pack (fst out), snd out).

(** Dense-cache execution retains its prepared state, selected callback and insertion charges. *)
Theorem run_cost_equation {A D B R S} EA EB support_c observe_c source
    (miss_c : session A B R -> S -> Cost.t (answer A B R S)) m side :
  Cost.ticks (@run_c A D B R S EA EB support_c observe_c source miss_c m side) =
    let prepared := Cost.value (prepare_query_c EA EB support_c observe_c source (snd m)) in
    (Cost.ticks (prepare_query_c EA EB support_c observe_c source (snd m)) +
      Cost.ticks (MemoState.run_c (fst prepared)
        (fun table current => Cost.map unpack (miss_c (table, fst current) (snd current)))
        (fst m) (snd prepared, side)))%N.
Proof.
  unfold run_c. autorewrite with galois_cost. lia.
Qed.

(** One agreement theorem derives the query meaning and all actual registry transports. *)
Theorem run_agrees {A D B R S} (EA : encoding A) (HA : encoding_laws EA)
    (EB : encoding B) (HB : encoding_laws EB) (support_c : A -> Cost.t (list D))
    (reference : A -> list (D * B) -> R) (P : S -> Prop) observe_c source miss_c m side :
  session_valid EA EB (fun a => Cost.value (support_c a)) reference m -> P side ->
  (forall current events i,
    session_valid EA EB (fun a => Cost.value (support_c a)) reference current -> P events ->
    registry_meaning (fun a => Cost.value (support_c a)) reference (snd current) i =
      Some (reference source
        (List.map (fun d => (d, Cost.value (observe_c d))) (Cost.value (support_c source)))) ->
    Map.get positive_encoding i (fst current) = None ->
    answer_valid EA EB (fun a => Cost.value (support_c a)) reference P current
      (reference source
        (List.map (fun d => (d, Cost.value (observe_c d))) (Cost.value (support_c source))))
      (Cost.value (miss_c current events))) ->
  answer_valid EA EB (fun a => Cost.value (support_c a)) reference P m
    (reference source
      (List.map (fun d => (d, Cost.value (observe_c d))) (Cost.value (support_c source))))
    (fst (Cost.value (@run_c A D B R S EA EB support_c observe_c source miss_c m side))).
Proof.
  intros [Hwf Hvalid] Hside Hmiss.
  pose proof (prepare_query_correct EA HA EB HB support_c reference observe_c source (snd m) Hwf)
    as Hprepared.
  unfold run_c. rewrite Cost.value_bind.
  remember (Cost.value (prepare_query_c EA EB support_c observe_c source (snd m))) as prepared.
  destruct Hprepared as [Hprepared [Hextension Hmeaning]].
  pose proof (registry_meaning_preserved (fun a => Cost.value (support_c a)) reference
    _ _ Hextension) as Htransport.
  pose proof (MemoState.valid_transport _ _ _ _ Htransport Hvalid) as Hcache.
  set (meaning := fun current : registry A B * S =>
    registry_meaning (fun a => Cost.value (support_c a)) reference (fst current)).
  set (invariant := fun current : registry A B * S =>
    registry_wf EA EB (fst current) /\ P (snd current) /\
      registry_extends (snd m) (fst current)).
  assert (Hlocal : Map.get positive_encoding (fst prepared) (fst m) = None ->
    MemoState.result_valid meaning invariant (snd prepared, side)
      (reference source
        (List.map (fun d => (d, Cost.value (observe_c d))) (Cost.value (support_c source))))
      (Cost.value (Cost.map unpack (miss_c (fst m, snd prepared) side)))).
  { intro Habsent.
    specialize (Hmiss (fst m, snd prepared) side (fst prepared)
      (conj Hprepared Hcache) Hside Hmeaning Habsent).
    rewrite Cost.value_map.
    exact (answer_unpack_valid EA EB _ reference P (snd m) (fst m, snd prepared) side _ _
      Hextension Hmiss). }
  pose proof (MemoState.run_agrees meaning invariant (fst prepared) _
    (fun table current => Cost.map unpack (miss_c (table, fst current) (snd current))) (fst m)
    (snd prepared, side) Hcache (conj Hprepared (conj Hside Hextension))
    Hmeaning Hlocal) as Hagrees.
  rewrite <- MemoState.run_c_value in Hagrees.
  rewrite Cost.value_bind.
  destruct (Cost.value (MemoState.run_c (fst prepared)
    (fun table current => Cost.map unpack (miss_c (table, fst current) (snd current)))
    (fst m) (snd prepared, side))) as [[[value table] [names events]] hit].
  autorewrite with galois_cost.
  destruct Hagrees as [Hvalue [Htable [[Hnames [Hevents Hextends]] _]]].
  split; [exact Hvalue|]. split; [exact (conj Hnames Htable)|].
  exact (conj Hextends Hevents).
Qed.

End ScevPrepared.
