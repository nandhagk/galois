(** * Code serialization and derived tree tests

    The examples cover universal trees, composite codecs and a recursive client codec.
    For example, the client tree stores positive leaves under binary branches.
    Builds on: BaseCode, BaseEncoding and BaseKeyTactics. *)

From Stdlib Require Import Bool List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseKeyTactics.
Import List.ListNotations Cost.Notations.

Local Open Scope positive_scope.

Inductive tree : Type :=
  | Leaf (p : positive)
  | Branch (left right : tree).

Fixpoint tree_to_code_c (t : tree) : Cost.t code :=
  Cost.step ;;
  match t with
  | Leaf p => Cost.ret (Atom p)
  | Branch l r =>
    let* lc := tree_to_code_c l in
    let* rc := tree_to_code_c r in
    Cost.ret (Node [lc; rc])
  end.

Fixpoint tree_of_code (c : code) : option tree :=
  match c with
  | Atom p => Some (Leaf p)
  | Node [lc; rc] =>
    match tree_of_code lc, tree_of_code rc with
    | Some l, Some r => Some (Branch l r)
    | _, _ => None
    end
  | _ => None
  end.

Example tree_roundtrip :
  forall t, tree_of_code (Cost.value (tree_to_code_c t)) = Some t.
Proof.
  solve_roundtrip.
Qed.

Definition tree_codec : codec tree := derive tree_to_code_c tree_of_code tree_roundtrip.

Example recursive_tree_codec :
  decode tree_codec
    (encode (codec_enc tree_codec) (Branch (Leaf 1) (Branch (Leaf 2) (Leaf 3)))) =
  Some (Branch (Leaf 1) (Branch (Leaf 2) (Leaf 3))).
Proof.
  vm_compute. reflexivity.
Qed.

Example tree_rejects_wrong_arity :
  decode tree_codec (code_encode (Node [Atom 1])) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example code_nested_roundtrip :
  code_decode (code_encode (Node [Atom 3; Node []; Node [Atom 1]])) =
    Some (Node [Atom 3; Node []; Node [Atom 1]]).
Proof.
  vm_compute. reflexivity.
Qed.

Example code_rejects_truncation :
  (code_decode 1, code_decode (stream_positive [false; true; false])) = (None, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example code_rejects_trailing_bits :
  code_decode (stream_positive (emit_tree (Atom 1) [true])) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example code_empty_boundary : code_decode (code_encode (Node [])) = Some (Node []).
Proof.
  vm_compute. reflexivity.
Qed.

Example composite_roundtrips :
  (decode (pair_codec positive_codec nat_codec)
      (encode (codec_enc (pair_codec positive_codec nat_codec)) (1%positive, 2%nat)),
    decode (list_codec positive_codec)
      (encode (codec_enc (list_codec positive_codec)) [1; 2]),
    decode (option_codec positive_codec)
      (encode (codec_enc (option_codec positive_codec)) (Some 3)),
    decode (sum_codec positive_codec bool_codec)
      (encode (codec_enc (sum_codec positive_codec bool_codec)) (inr true))) =
  (Some (1%positive, 2%nat), Some [1%positive; 2%positive], Some (Some 3%positive),
    Some (@inr positive bool true)).
Proof.
  vm_compute. reflexivity.
Qed.

Example composite_rejects :
  (decode (pair_codec positive_codec positive_codec) (code_encode (Node [Atom 1])),
    decode (list_codec positive_codec) (code_encode (Node [Node []])),
    decode (option_codec positive_codec) (code_encode (Node [Atom 1; Atom 2])),
    decode (sum_codec positive_codec bool_codec) (code_encode (Node []))) =
  (None, None, None, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example composite_empty_boundaries :
  (decode (list_codec positive_codec) (encode (codec_enc (list_codec positive_codec)) []),
    decode (option_codec positive_codec)
      (encode (codec_enc (option_codec positive_codec)) None)) = (Some [], Some None).
Proof.
  vm_compute. reflexivity.
Qed.

Example pair_ticks :
  Cost.ticks (encode_c (codec_enc (pair_codec positive_codec positive_codec)) (1, 2)) = 40%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example pair_bits :
  key_bits (codec_enc (pair_codec positive_codec positive_codec)) (1, 2) = 13%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition costly_scalar : codec positive :=
  Codec (Encoding (Cost.lift (fun _ => 1000%N) (fun p => p))) (@Some positive).

Example pair_accounts_for_component_ticks :
  Cost.ticks (encode_c (codec_enc (pair_codec costly_scalar costly_scalar)) (1, 2)) = 2038%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** * Encoding-only public clients *)

(** Nested composition needs encoding laws without supplying any decoder. *)
Example encoding_only_nested_injective {A B C D}
    (EA : encoding A) (EB : encoding B) (EC : encoding C) (ED : encoding D)
    (HA : encoding_laws EA) (HB : encoding_laws EB)
    (HC : encoding_laws EC) (HD : encoding_laws ED)
    (x y : (A + B) * (C * D)) :
  encode (pair_encoding (sum_encoding EA EB) (pair_encoding EC ED)) x =
    encode (pair_encoding (sum_encoding EA EB) (pair_encoding EC ED)) y -> x = y.
Proof.
  apply (encode_injective
    (pair_encoding_laws _ _ (sum_encoding_laws _ _ HA HB) (pair_encoding_laws _ _ HC HD))).
Qed.

(** Pair clients can retain arbitrary component and serializer charges symbolically. *)
Example encoding_only_pair_cost {A B} (EA : encoding A) (EB : encoding B) a b :
  Cost.ticks (encode_c (pair_encoding EA EB) (a, b)) =
    (3 + Cost.ticks (encode_c EA a) + Cost.ticks (encode_c EB b) +
      Cost.ticks (code_encode_c (Node [Atom (encode EA a); Atom (encode EB b)])))%N.
Proof.
  apply pair_encoding_cost_equation.
Qed.

(** Sum clients retain the selected charge without a premise about the unused side. *)
Example encoding_only_sum_cost {A B} (EA : encoding A) (EB : encoding B) b :
  Cost.ticks (encode_c (sum_encoding EA EB) (inr b)) =
    (2 + Cost.ticks (encode_c EB b) +
      Cost.ticks (code_encode_c (Node [Node [Atom (encode EB b)]])))%N.
Proof.
  exact (sum_encoding_cost_equation EA EB (inr b)).
Qed.

(** Numeric laws compose through nested pair and sum encodings under component premises. *)
Example encoding_only_nested_cost_laws {A B C}
    (EA : encoding A) (EB : encoding B) (EC : encoding C) ka kb kc :
  encoding_cost_laws EA ka -> encoding_cost_laws EB kb -> encoding_cost_laws EC kc ->
  encoding_cost_laws (pair_encoding EA (sum_encoding EB EC))
    (ka + (kb + kc + encode_k + 2) + encode_k + 3).
Proof.
  intros HA HB HC.
  apply pair_encoding_cost_laws.
  - exact HA.
  - now apply sum_encoding_cost_laws.
Qed.

(** Pair wire agreement holds for arbitrary codecs without their law premises. *)
Example encoding_pair_codec_wire {A B} (CA : codec A) (CB : codec B) a b :
  encode (pair_encoding (codec_enc CA) (codec_enc CB)) (a, b) =
    encode (codec_enc (pair_codec CA CB)) (a, b).
Proof.
  rewrite pair_encoding_equation, pair_codec_equation. reflexivity.
Qed.

(** Sum wire agreement holds for arbitrary codecs without their law premises. *)
Example encoding_sum_codec_wire {A B} (CA : codec A) (CB : codec B) x :
  encode (sum_encoding (codec_enc CA) (codec_enc CB)) x =
    encode (codec_enc (sum_codec CA CB)) x.
Proof.
  rewrite sum_encoding_equation, sum_codec_equation. reflexivity.
Qed.

(** Side separation holds even when component encodings have no injectivity laws. *)
Example encoding_only_tags {A B} (EA : encoding A) (EB : encoding B) a b :
  encode (sum_encoding EA EB) (inl a) <> encode (sum_encoding EA EB) (inr b).
Proof.
  apply sum_encoding_disjoint.
Qed.

(** An encoding-only fixture returns positive inputs with a caller-chosen charge. *)
Definition charged_encoding (charge : N) : encoding positive :=
  Encoding (Cost.lift (fun _ => charge) (fun p => p)).

(** The empty carrier supplies an encoding without constructing any input or decoder. *)
Definition empty_encoding : encoding Empty_set :=
  Encoding (fun x : Empty_set => match x with end).

(** Encoding-only pair serialization keeps component order. *)
Example encoding_only_pair_positive :
  code_decode (encode (pair_encoding (charged_encoding 1) (charged_encoding 1)) (1, 2)) =
    Some (Node [Atom 1; Atom 2]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Reversing distinct pair components changes the serialized code. *)
Example encoding_only_pair_negative :
  Pos.eqb
    (encode (pair_encoding (charged_encoding 1) (charged_encoding 1)) (1, 2))
    (encode (pair_encoding (charged_encoding 1) (charged_encoding 1)) (2, 1)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Equal component codes on different sum sides have different serialized keys. *)
Example encoding_only_sum_negative :
  Pos.eqb
    (encode (sum_encoding (charged_encoding 1) (charged_encoding 1)) (inl 1))
    (encode (sum_encoding (charged_encoding 1) (charged_encoding 1)) (inr 1)) = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Either inhabited sum side serializes when the other carrier is empty. *)
Example encoding_only_empty_side :
  (code_decode (encode (sum_encoding (charged_encoding 1) empty_encoding) (inl 1)),
    code_decode (encode (sum_encoding empty_encoding (charged_encoding 1)) (inr 1))) =
    (Some (Node [Atom 1]), Some (Node [Node [Atom 1]])).
Proof.
  vm_compute. reflexivity.
Qed.

(** Output widths include pair tags and both sum tag shapes at the smallest atom. *)
Example encoding_only_widths :
  (key_bits (pair_encoding (charged_encoding 1) (charged_encoding 1)) (1, 2),
    key_bits (sum_encoding (charged_encoding 1) empty_encoding) (inl 1),
    key_bits (sum_encoding empty_encoding (charged_encoding 1)) (inr 1)) =
    (13%N, 7%N, 10%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Exact observations retain both pair calls and the single selected sum call. *)
Example encoding_only_ticks :
  (Cost.ticks (encode_c (pair_encoding (charged_encoding 1) (charged_encoding 1)) (1, 2)),
    Cost.ticks (encode_c (sum_encoding (charged_encoding 1) empty_encoding) (inl 1)),
    Cost.ticks (encode_c (sum_encoding empty_encoding (charged_encoding 1)) (inr 1))) =
    (40%N, 22%N, 31%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** Expensive encoders retain their charges at the same output widths. *)
Example encoding_only_expensive_ticks :
  (Cost.ticks (encode_c (pair_encoding (charged_encoding 1000) (charged_encoding 1000)) (1, 2)),
    Cost.ticks (encode_c (sum_encoding (charged_encoding 1000) (charged_encoding 1)) (inl 1)),
    Cost.ticks (encode_c (sum_encoding (charged_encoding 1) (charged_encoding 1000)) (inr 1))) =
    (2038%N, 1021%N, 1030%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** An expensive unused sum encoder contributes no charge. *)
Example encoding_only_unused_ticks :
  (Cost.ticks (encode_c (sum_encoding (charged_encoding 1000) (charged_encoding 1)) (inr 1)),
    Cost.ticks (encode_c (sum_encoding (charged_encoding 1) (charged_encoding 1000)) (inl 1))) =
    (31%N, 22%N).
Proof.
  vm_compute. reflexivity.
Qed.
