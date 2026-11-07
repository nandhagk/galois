(** * Framework preparation and keys

    Shared traversals retain callback charges and composite key conversions.
    For example, flattening two singleton callback results copies both cells.
    Builds on: CostList, BaseCode and ProgramCfg. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
Import List.ListNotations Cost.Notations.

(** Flattening charges traversal, callback invocation and copying of each result. *)
Definition fw_flat_map_c {A B} (f : A -> Cost.t (list B)) xs :=
  fold_right_c (fun x rest =>
    Cost.step ;;
    let* ys := f x in
    app_c ys rest) [] xs.

(** Flattening preserves callback-list order and duplicate occurrences. *)
Theorem fw_flat_map_value {A B} (f : A -> Cost.t (list B)) xs :
  Cost.value (fw_flat_map_c f xs) = flat_map (fun x => Cost.value (f x)) xs.
Proof.
  unfold fw_flat_map_c; rewrite value_fold_right_c.
  induction xs as [|x xs IH]; cbn [fold_right flat_map].
  - reflexivity.
  - autorewrite with galois_cost; rewrite IH; reflexivity.
Qed.

(** Edge enumeration retains outgoing callback charges during preparation. *)
Definition fw_edges_c {N E} (c : Cfg.t N E) :=
  fw_flat_map_c (Graph.out_c (Cfg.graph c)) (Graph.nodes (Cfg.graph c)).

(** Charged edge preparation has the presentation's exact occurrence order. *)
Theorem fw_edges_value {N E} (c : Cfg.t N E) :
  Cost.value (fw_edges_c c) = Cfg.edges c.
Proof.
  unfold fw_edges_c; rewrite fw_flat_map_value; reflexivity.
Qed.

(** Indexed selection charges every traversed list cell. *)
Fixpoint fw_nth_c {A} (xs : list A) i : Cost.t (option A) :=
  Cost.step ;;
  match xs, i with
  | [], _ => Cost.ret None
  | x :: _, O => Cost.ret (Some x)
  | _ :: rest, S i => fw_nth_c rest i
  end.

(** Indexed selection returns the ordinary optional list element. *)
Theorem fw_nth_value {A} (xs : list A) i :
  Cost.value (fw_nth_c xs i) = nth_error xs i.
Proof.
  revert i; induction xs as [|x xs IH]; intros [|i]; cbn [fw_nth_c nth_error];
    autorewrite with galois_cost; auto.
Qed.

(** Slot enumeration charges every emitted index. *)
Fixpoint fw_seq_c start count : Cost.t (list nat) :=
  match count with
  | O => Cost.ret []
  | S count => Cost.step ;; Cost.map (cons start) (fw_seq_c (S start) count)
  end.

(** Charged slot enumeration keeps increasing legacy argument indices. *)
Theorem fw_seq_value start count :
  Cost.value (fw_seq_c start count) = seq start count.
Proof.
  revert start; induction count as [|n IH]; intro start; cbn [fw_seq_c seq];
    autorewrite with galois_cost; rewrite ?IH; reflexivity.
Qed.

Module FrameworkKey.

Definition pair_c {A B} (EA : encoding A) (EB : encoding B) (x : A * B) :=
  Cost.step ;;
  let* a := encode_c EA (fst x) in
  Cost.step ;;
  let* b := encode_c EB (snd x) in
  Cost.ret (a, b).

(** Pair dictionaries retain both component charges and the binary pair serializer. *)
Definition pair {A B} (EA : encoding A) (EB : encoding B) :=
  encoding_comap (pair_c EA EB) (codec_enc (pair_codec positive_codec positive_codec)).

(** Injective component keys distinguish pairs. *)
Theorem pair_laws {A B} (EA : encoding A) (EB : encoding B) :
  encoding_laws EA -> encoding_laws EB -> encoding_laws (pair EA EB).
Proof.
  intros HA HB; apply encoding_comap_laws.
  - intros [a b] [c d] Heq.
    change ((encode EA a, encode EB b) = (encode EA c, encode EB d)) in Heq.
    inversion Heq as [[Ha Hb]].
    apply (encode_injective HA) in Ha; apply (encode_injective HB) in Hb.
    subst; reflexivity.
  - apply codec_laws_injective, pair_codec_laws; apply positive_codec_laws.
Qed.

Definition sum_c {A B} (EA : encoding A) (EB : encoding B) (x : A + B) :=
  Cost.step ;;
  match x with
  | inl a => Cost.map (@inl positive positive) (encode_c EA a)
  | inr b => Cost.map (@inr positive positive) (encode_c EB b)
  end.

(** Sum dictionaries preserve the alternative as well as its component key. *)
Definition sum {A B} (EA : encoding A) (EB : encoding B) :=
  encoding_comap (sum_c EA EB) (codec_enc (sum_codec positive_codec positive_codec)).

(** Injectivity of both alternatives gives injectivity of their tagged sum. *)
Theorem sum_laws {A B} (EA : encoding A) (EB : encoding B) :
  encoding_laws EA -> encoding_laws EB -> encoding_laws (sum EA EB).
Proof.
  intros HA HB; apply encoding_comap_laws.
  - intros [a|b] [c|d] Heq;
      cbn [sum_c] in Heq; autorewrite with galois_cost in Heq;
      inversion Heq as [Hcode]; f_equal;
      first [apply (encode_injective HA), Hcode|apply (encode_injective HB), Hcode].
  - apply codec_laws_injective, sum_codec_laws; apply positive_codec_laws.
Qed.

(** Optional keys use a unit alternative for the distinguished zero fact. *)
Definition option {A} (E : encoding A) : encoding (option A) :=
  encoding_comap
    (fun x => Cost.ret (match x with None => inl tt | Some a => inr a end))
    (sum unit_encoding E).

(** Optional keys are injective when ordinary fact keys are injective. *)
Theorem option_laws {A} (E : encoding A) :
  encoding_laws E -> encoding_laws (option E).
Proof.
  intro HE; apply encoding_comap_laws.
  - intros [a|] [b|] Heq; cbn in Heq; congruence.
  - apply sum_laws; [apply unit_encoding_laws|exact HE].
Qed.

(** List key conversion charges every component and every visited cell. *)
Definition list {A} (E : encoding A) : encoding (List.list A) :=
  encoding_comap (map_c (fun x => Cost.step ;; encode_c E x))
    (codec_enc (list_codec positive_codec)).

(** Elementwise injectivity lifts to ordered lists, including empty lists. *)
Theorem list_laws {A} (E : encoding A) :
  encoding_laws E -> encoding_laws (list E).
Proof.
  intro HE; apply encoding_comap_laws.
  - intros xs ys Hcode; rewrite !value_map_c in Hcode.
    change (map (encode E) xs = map (encode E) ys) in Hcode.
    revert ys Hcode; induction xs as [|x xs IH]; intros [|y ys] Hcode;
      cbn in Hcode; try discriminate; [reflexivity|].
    inversion Hcode as [[Hxy Hrest]].
    f_equal; [apply (encode_injective HE), Hxy|apply IH, Hrest].
  - apply codec_laws_injective, list_codec_laws, positive_codec_laws.
Qed.

End FrameworkKey.
