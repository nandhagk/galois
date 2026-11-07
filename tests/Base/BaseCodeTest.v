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
