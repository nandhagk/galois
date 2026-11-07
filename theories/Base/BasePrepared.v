(** * Prepared encoded keys

    A prepared key stores its original value and the code used by map operations.
    For example, repeated lookups of a prepared list key reuse its serialized code.
    Builds on: BaseEncoding, BaseCode and BaseMap. *)

From Stdlib Require Import List NArith Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap.
Import Cost.Notations.

Module PreparedKey.

(** Prepared data carries no validity proof and can be received from untrusted clients. *)
Record t (K : Type) := Key {
  key : K;
  code : positive
}.
Arguments Key {K} key code.
Arguments key {K} _.
Arguments code {K} _.

(** Validity connects the cached code to this particular encoding dictionary. *)
Definition valid {K} (E : encoding K) (p : t K) : Prop :=
  code p = encode E (key p).

(** Preparation invokes the encoder once and retains its complete charge. *)
Definition prepare_c {K} (E : encoding K) (k : K) : Cost.t (t K) :=
  Cost.step ;; Cost.map (Key k) (encode_c E k).

(** Preparation retains the original key beside its code. *)
Definition prepare {K} (E : encoding K) k := Cost.value (prepare_c E k).

(** Prepared lookup uses the cached code without an encoding dictionary. *)
Definition get_c {K V} (p : t K) (m : Map.t K V) := Map.get_code_c (code p) m.
Definition get {K V} (p : t K) (m : Map.t K V) := Cost.value (get_c p m).

(** Prepared insertion stores the original key at the cached code. *)
Definition set_c {K V} (p : t K) (v : V) (m : Map.t K V) :=
  Map.set_code_c (code p) (key p) v m.
Definition set {K V} (p : t K) (v : V) (m : Map.t K V) := Cost.value (set_c p v m).

(** Prepared removal traverses the cached code. *)
Definition remove_c {K V} (p : t K) (m : Map.t K V) :=
  Map.remove_code_c (code p) m.
Definition remove {K V} (p : t K) (m : Map.t K V) := Cost.value (remove_c p m).

(** Prepared membership observes lookup at the cached code. *)
Definition mem_c {K V} (p : t K) (m : Map.t K V) :=
  Cost.map (fun o => match o with Some _ => true | None => false end) (get_c p m).
Definition mem {K V} (p : t K) (m : Map.t K V) := Cost.value (mem_c p m).

(** Preparation's value is independent of the encoder's charge. *)
Theorem prepare_equation {K} (E : encoding K) k :
  prepare E k = Key k (encode E k).
Proof.
  reflexivity.
Qed.

(** Every locally prepared key is valid for its encoding. *)
Theorem prepare_valid {K} (E : encoding K) k : valid E (prepare E k).
Proof.
  reflexivity.
Qed.

(** Preparation keeps the original key exactly. *)
Theorem prepare_key {K} (E : encoding K) k : key (prepare E k) = k.
Proof.
  reflexivity.
Qed.

(** A valid cached code refines ordinary lookup for every raw map. *)
Theorem prepared_get_agrees {K V} (E : encoding K) (p : t K) (m : Map.t K V) :
  valid E p -> get p m = Map.get E (key p) m.
Proof.
  intro Hvalid. change (Map.get_code (code p) m = Map.get E (key p) m).
  rewrite Map.get_equation, <- Hvalid. reflexivity.
Qed.

(** Valid codes identify keys when the encoding is injective. *)
Theorem prepared_code_injective {K} (E : encoding K) (HE : encoding_laws E)
    (p q : t K) :
  valid E p -> valid E q -> code p = code q -> key p = key q.
Proof.
  intros Hp Hq Heq. apply (encode_injective HE). congruence.
Qed.

(** Valid prepared insertion and removal agree with key-based map updates. *)
Theorem prepared_update_agrees {K V} (E : encoding K) (p : t K)
    (v : V) (m : Map.t K V) :
  valid E p ->
  set p v m = Map.set E (key p) v m /\ remove p m = Map.remove E (key p) m.
Proof.
  intro Hp. split.
  - change (Map.set_code (code p) (key p) v m = Map.set E (key p) v m).
    rewrite Map.set_equation, <- Hp. reflexivity.
  - change (Map.remove_code (code p) m = Map.remove E (key p) m).
    rewrite Map.remove_equation, <- Hp. reflexivity.
Qed.

(** Valid prepared membership agrees with ordinary map membership. *)
Theorem prepared_mem_agrees {K V} (E : encoding K) (p : t K) (m : Map.t K V) :
  valid E p -> mem p m = Map.mem E (key p) m.
Proof.
  intro Hp. apply eq_true_iff_eq. rewrite Map.mem_spec.
  unfold mem, mem_c. rewrite Cost.value_map. fold (get p m).
  rewrite (prepared_get_agrees E p m Hp).
  destruct (Map.get E (key p) m) as [v|]; split; intro H.
  - now exists v.
  - reflexivity.
  - discriminate.
  - destruct H as [v Hget]. discriminate.
Qed.

(** Insertion through a valid cached code preserves the map's representation invariant. *)
Theorem wf_set {K V} (E : encoding K) (p : t K) (v : V) (m : Map.t K V) :
  valid E p -> Map.wf E m -> Map.wf E (set p v m).
Proof.
  intros Hp Hwf. rewrite (proj1 (prepared_update_agrees E p v m Hp)).
  now apply Map.wf_set.
Qed.

(** Removal through a valid cached code preserves the map's representation invariant. *)
Theorem wf_remove {K V} (E : encoding K) (p : t K) (m : Map.t K V) :
  valid E p -> Map.wf E m -> Map.wf E (remove p m).
Proof.
  intros Hp Hwf.
  change (Map.wf E (Map.remove_code (code p) m)).
  rewrite Hp, <- Map.remove_equation. now apply Map.wf_remove.
Qed.

(** Prepared pair widths include the landed codec's node and delimiter bits. *)
Theorem prepared_pair_bits {A B} (CA : codec A) (CB : codec B) a b :
  N.pos (Pos.size (code (prepare (codec_enc (pair_codec CA CB)) (a, b)))) =
    (7 + 2 * key_bits (codec_enc CA) a + 2 * key_bits (codec_enc CB) b)%N.
Proof.
  apply pair_codec_bits.
Qed.

(** Prepared list widths retain each element's delimiter and the empty-node code. *)
Theorem prepared_list_bits {A} (CA : codec A) xs :
  N.pos (Pos.size (code (prepare (codec_enc (list_codec CA)) xs))) =
    (3 + 2 * N.of_nat (length xs) +
      2 * fold_right (fun x n => key_bits (codec_enc CA) x + n)%N 0%N xs)%N.
Proof.
  apply list_codec_bits.
Qed.

(** Prepared lookup makes precisely the cached-code call and never re-encodes the key. *)
Theorem get_code_cost {K V} (p : t K) (m : Map.t K V) :
  Cost.ticks (get_c p m) = Cost.ticks (Map.get_code_c (code p) m).
Proof.
  reflexivity.
Qed.

(** Under the public map laws a prepared lookup is bounded by its cached code width. *)
Theorem get_cost {K V} (HC : Map.cost_laws) (p : t K) (m : Map.t K V) :
  (Cost.ticks (get_c p m) <= N.pos (Pos.size (code p)))%N.
Proof.
  rewrite get_code_cost. apply (Map.get_code_cost HC).
Qed.

(** Preparing a key pays one callback-overhead tick and the encoder's full charge. *)
Theorem prepare_cost {K} (E : encoding K) k :
  Cost.ticks (prepare_c E k) = (1 + Cost.ticks (encode_c E k))%N.
Proof.
  unfold prepare_c. autorewrite with galois_cost. reflexivity.
Qed.

Arguments prepare_c {K} E k : simpl never.
Arguments prepare {K} E k : simpl never.
Arguments get_c {K V} p m : simpl never.
Arguments get {K V} p m : simpl never.
Arguments set_c {K V} p v m : simpl never.
Arguments set {K V} p v m : simpl never.
Arguments remove_c {K V} p m : simpl never.
Arguments remove {K V} p m : simpl never.
Arguments mem_c {K V} p m : simpl never.
Arguments mem {K V} p m : simpl never.

End PreparedKey.
