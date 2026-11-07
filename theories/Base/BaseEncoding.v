(** * Key dictionaries and scalar codecs

    Encodings compute positive keys and keep injectivity in a separate law record.
    For example, the boolean [false] has code one.
    Builds on: Stdlib binary numbers and CostMonad. *)

From Stdlib Require Import Bool NArith ZArith Lia.
From Galois.Cost Require Import CostMonad.
Import Cost.Notations.

(** An encoding supplies a costed key computation without requiring laws. *)
Record encoding (K : Type) : Type := Encoding {
  encode_c : K -> Cost.t positive
}.
Arguments Encoding {K} _.
Arguments encode_c {K} _ _.

(** The executable key is the value of the costed computation. *)
Definition encode {K} (E : encoding K) (x : K) : positive :=
  Cost.value (encode_c E x).

(** Key size includes the leading binary digit. *)
Definition key_bits {K} (E : encoding K) (x : K) : N :=
  N.pos (Pos.size (encode E x)).

(** Injectivity is independent of the dictionary's computational fields. *)
Record encoding_laws {K} (E : encoding K) : Prop := Encoding_laws {
  encode_injective : forall x y, encode E x = encode E y -> x = y
}.
Arguments encode_injective {K E} _ x y _.

(** A pure primitive is lifted at the word-RAM convention of one tick per call. *)
Definition of_pure {K} (f : K -> positive) : encoding K :=
  Encoding (Cost.lift (fun _ => 1%N) f).

(** Lifting a primitive does not change its returned key. *)
Theorem of_pure_equation {K} (f : K -> positive) x :
  encode (of_pure f) x = f x.
Proof.
  apply Cost.value_lift.
Qed.

(** Pure primitives charge one tick. *)
Theorem of_pure_cost {K} (f : K -> positive) x :
  Cost.ticks (encode_c (of_pure f) x) = 1%N.
Proof.
  change (Cost.ticks (Cost.lift (fun _ => 1%N) f x) = 1%N).
  rewrite Cost.ticks_lift. reflexivity.
Qed.

(** A codec adds a partial decoder to an encoding. *)
Record codec (K : Type) : Type := Codec {
  codec_enc : encoding K;
  decode : positive -> option K
}.
Arguments Codec {K} _ _.
Arguments codec_enc {K} _.
Arguments decode {K} _ _.

(** A lawful decoder recovers every encoded value. *)
Record codec_laws {K} (C : codec K) : Prop := Codec_laws {
  decode_encode : forall x, decode C (encode (codec_enc C) x) = Some x
}.
Arguments decode_encode {K C} _ x.

(** A decoder round trip implies injectivity without any equality assumption on keys. *)
Theorem codec_laws_injective {K} (C : codec K) :
  codec_laws C -> encoding_laws (codec_enc C).
Proof.
  intros HC. constructor. intros x y Hcode.
  pose proof (decode_encode HC x) as Hx.
  rewrite Hcode, (decode_encode HC y) in Hx.
  now injection Hx.
Qed.

(** Numeric cost assumptions are separate from computational and injectivity records. *)
Record encoding_cost_laws {K} (E : encoding K) (k : N) : Prop := Encoding_cost_laws {
  encode_cost_bound : forall x, (Cost.ticks (encode_c E x) <= k * key_bits E x)%N
}.
Arguments encode_cost_bound {K E k} _ x.

(** The serialization overhead constant is independent of component dictionaries. *)
Definition encode_k : N := 8.

(** Pure scalar primitives satisfy the unit numeric cost bound. *)
Theorem of_pure_cost_laws {K} (f : K -> positive) :
  encoding_cost_laws (of_pure f) 1.
Proof.
  constructor. intro x. rewrite of_pure_cost.
  unfold key_bits. destruct (Pos.size (encode (of_pure f) x)); cbn; lia.
Qed.

(** Positive values are their own codes. *)
Definition positive_codec : codec positive := Codec (of_pure (fun p => p)) (@Some positive).

(** Positive decoding recovers the original value. *)
Theorem positive_codec_laws : codec_laws positive_codec.
Proof.
  constructor. reflexivity.
Qed.

(** Binary naturals retain the legacy successor layout. *)
Definition N_codec : codec N :=
  Codec (of_pure N.succ_pos) (fun p => Some (N.pred (N.pos p))).

(** Successor encoding and predecessor decoding cancel on naturals. *)
Theorem N_codec_laws : codec_laws N_codec.
Proof.
  constructor. intro n.
  change (Some (N.pred (N.pos (N.succ_pos n))) = Some n).
  now rewrite N.succ_pos_spec, N.pred_succ.
Qed.

(** Unary naturals retain the legacy positive-successor layout. *)
Definition nat_codec : codec nat :=
  Codec (of_pure Pos.of_succ_nat) (fun p => Some (Nat.pred (Pos.to_nat p))).

(** Converting a unary successor to positive and back recovers the natural. *)
Theorem nat_codec_laws : codec_laws nat_codec.
Proof.
  constructor. intro n.
  change (Some (Nat.pred (Pos.to_nat (Pos.of_succ_nat n))) = Some n).
  now rewrite SuccNat2Pos.id_succ.
Qed.

(** Signed codes use one for zero and a low sign bit for nonzero values. *)
Definition Z_codec : codec Z :=
  Codec (of_pure (fun z =>
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end)) (fun p => Some
    (match p with
    | xH => Z0
    | xO q => Zpos q
    | xI q => Zneg q
    end)).

(** Sign tags distinguish zero, positive and negative inputs. *)
Theorem Z_codec_laws : codec_laws Z_codec.
Proof.
  constructor. intros [|p|p]; reflexivity.
Qed.

(** Booleans use one for false and two for true and reject other codes. *)
Definition bool_codec : codec bool :=
  Codec (of_pure (fun b : bool => if b then 2%positive else 1%positive))
    (fun p =>
      match p with
      | xH => Some false
      | xO xH => Some true
      | _ => None
      end).

(** Both boolean codes decode to the matching boolean. *)
Theorem bool_codec_laws : codec_laws bool_codec.
Proof.
  constructor. intros []; reflexivity.
Qed.

(** Unit uses one and rejects every other code. *)
Definition unit_codec : codec unit :=
  Codec (of_pure (fun _ => xH))
    (fun p =>
      match p with
      | xH => Some tt
      | _ => None
      end).

(** The unique unit code decodes successfully. *)
Theorem unit_codec_laws : codec_laws unit_codec.
Proof.
  constructor. intros []; reflexivity.
Qed.

(** The positive encoding exposes the scalar codec's costed computation. *)
Definition positive_encoding := codec_enc positive_codec.

(** The binary natural encoding exposes the scalar codec's costed computation. *)
Definition N_encoding := codec_enc N_codec.

(** The unary natural encoding exposes the scalar codec's costed computation. *)
Definition nat_encoding := codec_enc nat_codec.

(** The signed encoding exposes the scalar codec's costed computation. *)
Definition Z_encoding := codec_enc Z_codec.

(** The boolean encoding exposes the scalar codec's costed computation. *)
Definition bool_encoding := codec_enc bool_codec.

(** The unit encoding exposes the scalar codec's costed computation. *)
Definition unit_encoding := codec_enc unit_codec.

(** The positive scalar encoding is injective. *)
Theorem positive_encoding_laws : encoding_laws positive_encoding.
Proof.
  exact (codec_laws_injective _ positive_codec_laws).
Qed.

(** The binary natural scalar encoding is injective. *)
Theorem N_encoding_laws : encoding_laws N_encoding.
Proof.
  exact (codec_laws_injective _ N_codec_laws).
Qed.

(** The unary natural scalar encoding is injective. *)
Theorem nat_encoding_laws : encoding_laws nat_encoding.
Proof.
  exact (codec_laws_injective _ nat_codec_laws).
Qed.

(** The signed scalar encoding is injective. *)
Theorem Z_encoding_laws : encoding_laws Z_encoding.
Proof.
  exact (codec_laws_injective _ Z_codec_laws).
Qed.

(** The boolean scalar encoding is injective. *)
Theorem bool_encoding_laws : encoding_laws bool_encoding.
Proof.
  exact (codec_laws_injective _ bool_codec_laws).
Qed.

(** The unit scalar encoding is injective. *)
Theorem unit_encoding_laws : encoding_laws unit_encoding.
Proof.
  exact (codec_laws_injective _ unit_codec_laws).
Qed.

(** Positive scalar calls obey the unit numeric law. *)
Theorem positive_encoding_cost_laws : encoding_cost_laws positive_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Binary natural scalar calls obey the unit numeric law. *)
Theorem N_encoding_cost_laws : encoding_cost_laws N_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Unary natural scalar calls obey the unit numeric law. *)
Theorem nat_encoding_cost_laws : encoding_cost_laws nat_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Signed scalar calls obey the unit numeric law. *)
Theorem Z_encoding_cost_laws : encoding_cost_laws Z_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Boolean scalar calls obey the unit numeric law. *)
Theorem bool_encoding_cost_laws : encoding_cost_laws bool_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Unit scalar calls obey the unit numeric law. *)
Theorem unit_encoding_cost_laws : encoding_cost_laws unit_encoding 1.
Proof.
  apply of_pure_cost_laws.
Qed.

(** Numeric encoding bounds are available independently of injectivity. *)
Theorem encode_cost_le {K} (E : encoding K) k :
  encoding_cost_laws E k ->
  forall x, (Cost.ticks (encode_c E x) <= k * key_bits E x)%N.
Proof.
  exact (fun H => encode_cost_bound H).
Qed.

(** Pullback calls a costed conversion and then the target dictionary, charging both callbacks. *)
Definition encoding_comap {A B} (f_c : A -> Cost.t B) (E : encoding B) : encoding A :=
  Encoding (fun x =>
    Cost.step ;;
    let* y := f_c x in
    Cost.step ;;
    encode_c E y).

(** Pullback keys are target keys of converted values. *)
Theorem encoding_comap_equation {A B} (f_c : A -> Cost.t B) (E : encoding B) x :
  encode (encoding_comap f_c E) x = encode E (Cost.value (f_c x)).
Proof.
  reflexivity.
Qed.

(** An injective conversion pulls back the target's injectivity law. *)
Theorem encoding_comap_laws {A B} (f_c : A -> Cost.t B) (E : encoding B) :
  (forall x y, Cost.value (f_c x) = Cost.value (f_c y) -> x = y) ->
  encoding_laws E -> encoding_laws (encoding_comap f_c E).
Proof.
  intros Hinj HE. constructor. intros x y Hcode.
  apply Hinj. apply (encode_injective HE).
  exact Hcode.
Qed.

(** Pullback exposes the conversion and encoding costs explicitly. *)
Theorem encoding_comap_cost {A B} (f_c : A -> Cost.t B) (E : encoding B) x :
  Cost.ticks (encode_c (encoding_comap f_c E) x) =
    (2 + Cost.ticks (f_c x) + Cost.ticks (encode_c E (Cost.value (f_c x))))%N.
Proof.
  unfold encoding_comap. cbn [encode_c].
  autorewrite with galois_cost. lia.
Qed.

(** Numeric pullback bounds require a bound on conversion work as well as target calls. *)
Theorem encoding_comap_encode_cost_le {A B} (f_c : A -> Cost.t B) (E : encoding B)
    (k w : N) x :
  encoding_cost_laws E k ->
  (Cost.ticks (f_c x) <= w * key_bits E (Cost.value (f_c x)))%N ->
  (Cost.ticks (encode_c (encoding_comap f_c E) x) <=
    (k + w + 2) * key_bits (encoding_comap f_c E) x)%N.
Proof.
  intros HE Hf. rewrite encoding_comap_cost.
  pose proof (encode_cost_bound HE (Cost.value (f_c x))) as Hcost.
  unfold key_bits in *. rewrite encoding_comap_equation.
  assert (0 < N.pos (Pos.size (encode E (Cost.value (f_c x)))))%N by lia.
  nia.
Qed.
