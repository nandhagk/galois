(** * Constructive tree serialization and composite codecs

    Trees have a self-delimiting bit grammar and a decoder with a proved fuel bound.
    For example, a node can hold the two atoms used by a pair codec.
    Builds on: BaseEncoding, BaseKeyTactics and CostMonad. *)

From Stdlib Require Import Bool List Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseKeyTactics.
Import List.ListNotations Cost.Notations.

Scheme All for list.

(** A universal code distinguishes scalar atoms from lists of child codes. *)
Inductive code : Type :=
  | Atom (p : positive)
  | Node (cs : list code).

(** Nested induction supplies a hypothesis for every child of a node. *)
Theorem code_ind_all (P : code -> Prop)
    (HA : forall p, P (Atom p))
    (HN : forall cs, Forall P cs -> P (Node cs)) :
  forall c, P c.
Proof.
  fix IH 1. intros [p|cs].
  - apply HA.
  - apply HN. induction cs as [|c cs IHcs].
    + constructor.
    + constructor.
      * apply IH.
      * exact IHcs.
Qed.

(** Each positive digit emits a two-bit symbol, ending in false,true. *)
Fixpoint emit_code_c (p : positive) (rest : list bool) : Cost.t (list bool) :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (false :: true :: rest)
  | xO q => Cost.map (fun bs => false :: false :: bs) (emit_code_c q rest)
  | xI q => Cost.map (fun bs => true :: true :: bs) (emit_code_c q rest)
  end.

(** Delimited positive symbols are the values of their charged emission. *)
Definition emit_code p rest := Cost.value (emit_code_c p rest).

(** Emission preserves the legacy two-bit symbol layout. *)
Theorem emit_code_equation p rest :
  emit_code p rest =
    match p with
    | xH => false :: true :: rest
    | xO q => false :: false :: emit_code q rest
    | xI q => true :: true :: emit_code q rest
    end.
Proof.
  destruct p; reflexivity.
Qed.

(** Reading delimited positive codes rejects truncated and invalid symbols. *)
Fixpoint read_code (bs : list bool) : option (positive * list bool) :=
  match bs with
  | false :: true :: rest => Some (xH, rest)
  | false :: false :: rest =>
    match read_code rest with
    | Some (p, suffix) => Some (xO p, suffix)
    | None => None
    end
  | true :: true :: rest =>
    match read_code rest with
    | Some (p, suffix) => Some (xI p, suffix)
    | None => None
    end
  | _ => None
  end.

(** A positive symbol round trip leaves any supplied suffix untouched. *)
Theorem read_emit_code p rest : read_code (emit_code p rest) = Some (p, rest).
Proof.
  induction p; rewrite emit_code_equation; cbn [read_code]; now rewrite ?IHp.
Qed.

(** Atoms start with false, nodes with true, and child lists use cons and nil tags. *)
Fixpoint emit_tree_c (c : code) (rest : list bool) : Cost.t (list bool) :=
  Cost.step ;;
  match c with
  | Atom p => Cost.map (cons false) (emit_code_c p rest)
  | Node cs =>
    Cost.map (cons true)
      ((fix emit_children_c (xs : list code) : Cost.t (list bool) :=
        Cost.step ;;
        match xs with
        | [] => Cost.ret (false :: rest)
        | x :: xs =>
          let* suffix := emit_children_c xs in
          Cost.map (cons true) (emit_tree_c x suffix)
        end) cs)
  end.

(** Pure tree emission is the value of the costed emitter. *)
Definition emit_tree c rest := Cost.value (emit_tree_c c rest).

(** The pure child-list equation is useful independently of its costed implementation. *)
Fixpoint emit_children (cs : list code) (rest : list bool) : list bool :=
  match cs with
  | [] => false :: rest
  | c :: cs => true :: emit_tree c (emit_children cs rest)
  end.

Local Lemma emit_children_value cs rest :
  Cost.value
    ((fix go (xs : list code) : Cost.t (list bool) :=
      Cost.step ;;
      match xs with
      | [] => Cost.ret (false :: rest)
      | x :: xs =>
        let* suffix := go xs in
        Cost.map (cons true) (emit_tree_c x suffix)
      end) cs) = emit_children cs rest.
Proof.
  induction cs as [|c cs IH]; cbn [emit_children];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

(** Tree emission follows the tagged grammar and threads a suffix without append. *)
Theorem emit_tree_equation c rest :
  emit_tree c rest =
    match c with
    | Atom p => false :: emit_code p rest
    | Node cs => true :: emit_children cs rest
    end.
Proof.
  destruct c; unfold emit_tree; cbn [emit_tree_c];
    autorewrite with galois_cost; try reflexivity.
  now rewrite emit_children_value.
Qed.

(** A stream stores bits from least significant to most significant, with a final one. *)
Fixpoint stream_positive_c (bs : list bool) : Cost.t positive :=
  Cost.step ;;
  match bs with
  | [] => Cost.ret xH
  | b :: bs =>
    Cost.map (fun p => if b then xI p else xO p) (stream_positive_c bs)
  end.

(** Pure stream construction is the value of its costed traversal. *)
Definition stream_positive bs := Cost.value (stream_positive_c bs).

(** Stream construction adds one binary digit per supplied bit. *)
Theorem stream_positive_equation bs :
  stream_positive bs =
    match bs with
    | [] => xH
    | b :: bs => if b then xI (stream_positive bs) else xO (stream_positive bs)
    end.
Proof.
  destruct bs as [|[] bs]; reflexivity.
Qed.

(** Removing the leading one recovers the least-significant-first bit stream. *)
Fixpoint positive_stream (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: positive_stream q
  | xI q => true :: positive_stream q
  end.

(** Turning a stream into a positive and back keeps every bit. *)
Theorem positive_stream_roundtrip bs : positive_stream (stream_positive bs) = bs.
Proof.
  induction bs as [|[] bs IH]; rewrite stream_positive_equation;
    cbn [positive_stream]; now rewrite ?IH.
Qed.

(** Serialization length counts node tags, child-list tags and doubled atom digits. *)
Fixpoint code_weight (c : code) : nat :=
  match c with
  | Atom p => 1 + 2 * Pos.size_nat p
  | Node cs =>
    1 + (fix weight_children (xs : list code) : nat :=
      match xs with
      | [] => 1
      | x :: xs => 1 + code_weight x + weight_children xs
      end) cs
  end.

(** A child list contributes one cons tag per tree and one final nil tag. *)
Fixpoint children_weight (cs : list code) : nat :=
  match cs with
  | [] => 1
  | c :: cs => 1 + code_weight c + children_weight cs
  end.

Local Lemma code_weight_node cs : code_weight (Node cs) = 1 + children_weight cs.
Proof.
  reflexivity.
Qed.

Local Lemma emit_code_length p rest :
  length (emit_code p rest) = 2 * Pos.size_nat p + length rest.
Proof.
  induction p; rewrite emit_code_equation; cbn [Pos.size_nat length]; lia.
Qed.

(** The emitted length is the structural weight plus the untouched suffix length. *)
Theorem emit_tree_length c : forall rest,
  length (emit_tree c rest) = code_weight c + length rest.
Proof.
  induction c using code_ind_all; intro rest; rewrite emit_tree_equation.
  - cbn [length code_weight]. rewrite emit_code_length. lia.
  - cbn [length]. rewrite code_weight_node.
    enough (Hlen : length (emit_children cs rest) = children_weight cs + length rest) by lia.
    induction H as [|c cs Hc Hcs IH]; cbn [emit_children children_weight length].
    + lia.
    + rewrite Hc, IH. lia.
Qed.

(** Fuel counts grammar constructors and is shared by the tree and child-list parser. *)
Fixpoint read_tree (fuel : nat) (bs : list bool) : option (code * list bool) :=
  match fuel with
  | O => None
  | S n =>
    match bs with
    | false :: rest =>
      match read_code rest with
      | Some (p, suffix) => Some (Atom p, suffix)
      | None => None
      end
    | true :: rest =>
      match read_children n rest with
      | Some (cs, suffix) => Some (Node cs, suffix)
      | None => None
      end
    | [] => None
    end
  end
with read_children (fuel : nat) (bs : list bool) : option (list code * list bool) :=
  match fuel with
  | O => None
  | S n =>
    match bs with
    | false :: rest => Some ([], rest)
    | true :: rest =>
      match read_tree n rest with
      | Some (c, suffix) =>
        match read_children n suffix with
        | Some (cs, suffix') => Some (c :: cs, suffix')
        | None => None
        end
      | None => None
      end
    | [] => None
    end
  end.

(** Sufficient fuel parses an emitted tree and returns its original suffix. *)
Theorem read_emit_tree c : forall fuel rest,
  code_weight c <= fuel ->
  read_tree fuel (emit_tree c rest) = Some (c, rest).
Proof.
  induction c using code_ind_all; intros [|n] rest Hfuel;
    rewrite emit_tree_equation; cbn [code_weight] in Hfuel; try lia.
  - cbn [read_tree]. now rewrite read_emit_code.
  - cbn [read_tree]. change (1 + children_weight cs <= S n) in Hfuel.
    assert (Hchildren : forall fuel,
      children_weight cs <= fuel ->
      read_children fuel (emit_children cs rest) = Some (cs, rest)).
    { clear Hfuel. induction H as [|c cs Hc Hcs IH]; intros [|m] Hbound;
        cbn [children_weight] in Hbound; try lia.
      - reflexivity.
      - cbn [emit_children read_children].
        rewrite Hc by lia. rewrite IH by lia. reflexivity. }
    rewrite Hchildren by lia. reflexivity.
Qed.

(** Serialization charges its structural emission, stream construction and result traversal. *)
Definition code_encode_c (c : code) : Cost.t positive :=
  let* bs := emit_tree_c c [] in
  let* p := stream_positive_c bs in
  Cost.tick_bits p ;;
  Cost.ret p.

(** The executable tree key is the serializer's value projection. *)
Definition code_encode c := Cost.value (code_encode_c c).

(** Serialized keys are precisely the emitted tree stream with a final one bit. *)
Theorem code_encode_equation c : code_encode c = stream_positive (emit_tree c []).
Proof.
  reflexivity.
Qed.

(** Decoding rejects malformed trees and valid trees followed by unused bits. *)
Definition code_decode (p : positive) : option code :=
  let bs := positive_stream p in
  match read_tree (length bs) bs with
  | Some (c, []) => Some c
  | _ => None
  end.

(** The constructive parser recovers every serialized tree. *)
Theorem code_decode_encode c : code_decode (code_encode c) = Some c.
Proof.
  rewrite code_encode_equation. unfold code_decode.
  rewrite positive_stream_roundtrip, emit_tree_length.
  rewrite read_emit_tree by lia. reflexivity.
Qed.

Local Lemma stream_positive_size bs :
  N.pos (Pos.size (stream_positive bs)) = (1 + N.of_nat (length bs))%N.
Proof.
  induction bs as [|[] bs IH]; rewrite stream_positive_equation;
    cbn [Pos.size length]; rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Serialized bit count is linear in constructor tags and atom digit sizes. *)
Theorem code_encode_bits c :
  N.pos (Pos.size (code_encode c)) = (1 + N.of_nat (code_weight c))%N.
Proof.
  rewrite code_encode_equation, stream_positive_size, emit_tree_length.
  now rewrite Nat.add_0_r.
Qed.

Local Lemma emit_code_cost p rest :
  Cost.ticks (emit_code_c p rest) = N.pos (Pos.size p).
Proof.
  induction p; cbn [emit_code_c]; autorewrite with galois_cost;
    cbn [Pos.size]; lia.
Qed.

Local Lemma size_nat_N p : N.of_nat (Pos.size_nat p) = N.pos (Pos.size p).
Proof.
  induction p; cbn [Pos.size_nat Pos.size];
    rewrite ?Nat2N.inj_succ; lia.
Qed.

Local Lemma emit_tree_cost c : forall rest,
  (Cost.ticks (emit_tree_c c rest) <= N.of_nat (code_weight c))%N.
Proof.
  induction c using code_ind_all; intro rest; cbn [emit_tree_c];
    autorewrite with galois_cost.
  - rewrite emit_code_cost. cbn [code_weight].
    rewrite Nat2N.inj_add, Nat2N.inj_mul, size_nat_N.
    change (1 + N.pos (Pos.size p) <= 1 + 2 * N.pos (Pos.size p))%N. lia.
  - rewrite code_weight_node, Nat2N.inj_add.
    enough (Hcs :
      (Cost.ticks
        ((fix go (xs : list code) : Cost.t (list bool) :=
          Cost.step ;;
          match xs with
          | [] => Cost.ret (false :: rest)
          | x :: xs =>
            let* suffix := go xs in
            Cost.map (cons true) (emit_tree_c x suffix)
          end) cs) <= N.of_nat (children_weight cs))%N) by lia.
    induction H as [|c cs Hc Hcs IH]; cbn [children_weight];
      autorewrite with galois_cost; rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ.
    + reflexivity.
    + specialize (Hc (Cost.value
        ((fix go (xs : list code) : Cost.t (list bool) :=
          Cost.step ;;
          match xs with
          | [] => Cost.ret (false :: rest)
          | x :: xs =>
            let* suffix := go xs in
            Cost.map (cons true) (emit_tree_c x suffix)
          end) cs))). lia.
Qed.

Local Lemma stream_positive_cost bs :
  Cost.ticks (stream_positive_c bs) = (1 + N.of_nat (length bs))%N.
Proof.
  induction bs; cbn [stream_positive_c]; autorewrite with galois_cost;
    cbn [length]; rewrite ?Nat2N.inj_succ; lia.
Qed.

(** Serialization has a fixed overhead bound independent of client callbacks. *)
Theorem code_encode_cost c :
  (Cost.ticks (code_encode_c c) <= encode_k * N.pos (Pos.size (code_encode c)))%N.
Proof.
  unfold code_encode_c. autorewrite with galois_cost.
  change
    (Cost.ticks (emit_tree_c c []) +
      (Cost.ticks (stream_positive_c (emit_tree c [])) +
        (N.pos (Pos.size (stream_positive (emit_tree c []))) + 0)) <=
      encode_k * N.pos (Pos.size (code_encode c)))%N.
  rewrite stream_positive_cost, stream_positive_size, emit_tree_length, code_encode_bits.
  pose proof (emit_tree_cost c []) as Hcost.
  unfold encode_k. rewrite Nat.add_0_r. nia.
Qed.

(** Derivation composes a charged client conversion with the universal serializer. *)
Definition derive {T} (to_code : T -> Cost.t code) (of_code : code -> option T)
    (_rt : forall x, of_code (Cost.value (to_code x)) = Some x) : codec T :=
  Codec
    (Encoding (fun x =>
      Cost.step ;;
      let* c := to_code x in
      code_encode_c c))
    (fun p =>
      match code_decode p with
      | Some c => of_code c
      | None => None
      end).

(** Derived keys serialize the value returned by the client conversion. *)
Theorem derive_equation {T} to_code of_code rt (x : T) :
  encode (codec_enc (derive to_code of_code rt)) x = code_encode (Cost.value (to_code x)).
Proof.
  reflexivity.
Qed.

(** A client round trip and the universal round trip establish the derived codec law. *)
Theorem derive_laws {T} to_code of_code rt :
  @codec_laws T (derive to_code of_code rt).
Proof.
  constructor. intro x.
  change
    (match code_decode (code_encode (Cost.value (to_code x))) with
    | Some c => of_code c
    | None => None
    end = Some x).
  now rewrite code_decode_encode, rt.
Qed.

(** Derivation exposes conversion work and bounds serialization independently of it. *)
Theorem derive_cost {T} to_code of_code rt (x : T) :
  (Cost.ticks (encode_c (codec_enc (derive to_code of_code rt)) x) <=
    1 + Cost.ticks (to_code x) +
      encode_k * key_bits (codec_enc (derive to_code of_code rt)) x)%N.
Proof.
  change
    (Cost.ticks (Cost.step ;; (let* c := to_code x in code_encode_c c)) <=
      1 + Cost.ticks (to_code x) +
        encode_k * key_bits (codec_enc (derive to_code of_code rt)) x)%N.
  autorewrite with galois_cost.
  pose proof (code_encode_cost (Cost.value (to_code x))) as Hcode.
  unfold key_bits. rewrite derive_equation. lia.
Qed.

(** A numeric derived bound requires an explicit bound for the client's conversion. *)
Theorem derive_encode_cost_le {T} to_code of_code rt (x : T) k :
  (Cost.ticks (to_code x) <=
    k * key_bits (codec_enc (derive to_code of_code rt)) x)%N ->
  (Cost.ticks (encode_c (codec_enc (derive to_code of_code rt)) x) <=
    (k + encode_k + 1) * key_bits (codec_enc (derive to_code of_code rt)) x)%N.
Proof.
  intro Hconvert. pose proof (derive_cost to_code of_code rt x) as Hcost.
  assert (Hbits : (0 < key_bits (codec_enc (derive to_code of_code rt)) x)%N).
  { unfold key_bits. lia. }
  nia.
Qed.

(** Pair conversion calls each component dictionary once and charges both callbacks. *)
Definition pair_to_code_c {A B} (CA : codec A) (CB : codec B) (xy : A * B) :
    Cost.t code :=
  Cost.step ;;
  let* p := encode_c (codec_enc CA) (fst xy) in
  Cost.step ;;
  let* q := encode_c (codec_enc CB) (snd xy) in
  Cost.ret (Node [Atom p; Atom q]).

(** Pair decoding rejects every shape other than exactly two component atoms. *)
Definition pair_of_code {A B} (CA : codec A) (CB : codec B) (c : code) : option (A * B) :=
  match c with
  | Node [Atom p; Atom q] =>
    match decode CA p, decode CB q with
    | Some a, Some b => Some (a, b)
    | _, _ => None
    end
  | _ => None
  end.

(** Component decoder laws recover a converted pair. *)
Theorem pair_roundtrip {A B} (CA : codec A) (CB : codec B)
    (HA : codec_laws CA) (HB : codec_laws CB) :
  forall xy, pair_of_code CA CB (Cost.value (pair_to_code_c CA CB xy)) = Some xy.
Proof.
  solve_roundtrip.
Qed.

(** Pair dictionaries need no component laws to compute. *)
Definition pair_codec {A B} (CA : codec A) (CB : codec B) : codec (A * B) :=
  Codec
    (Encoding (fun xy =>
      Cost.step ;;
      let* c := pair_to_code_c CA CB xy in
      code_encode_c c))
    (fun p =>
      match code_decode p with
      | Some c => pair_of_code CA CB c
      | None => None
      end).

(** Pair codec laws require exactly the two component codec laws. *)
Theorem pair_codec_laws {A B} (CA : codec A) (CB : codec B) :
  codec_laws CA -> codec_laws CB -> codec_laws (pair_codec CA CB).
Proof.
  intros HA HB.
  exact (derive_laws _ _ (pair_roundtrip CA CB HA HB)).
Qed.

(** A list conversion charges each recursion step and each component callback. *)
Fixpoint list_atoms_c {A} (CA : codec A) (xs : list A) : Cost.t (list code) :=
  Cost.step ;;
  match xs with
  | [] => Cost.ret []
  | x :: xs =>
    Cost.step ;;
    let* p := encode_c (codec_enc CA) x in
    Cost.map (cons (Atom p)) (list_atoms_c CA xs)
  end.

(** List decoding rejects non-atoms and any rejected component code. *)
Fixpoint list_of_atoms {A} (CA : codec A) (cs : list code) : option (list A) :=
  match cs with
  | [] => Some []
  | Atom p :: cs =>
    match decode CA p, list_of_atoms CA cs with
    | Some x, Some xs => Some (x :: xs)
    | _, _ => None
    end
  | _ => None
  end.

(** A list conversion wraps its charged sequence of atoms in a node. *)
Definition list_to_code_c {A} (CA : codec A) (xs : list A) : Cost.t code :=
  Cost.map Node (list_atoms_c CA xs).

(** List codecs require a node whose children are component atoms. *)
Definition list_of_code {A} (CA : codec A) (c : code) : option (list A) :=
  match c with
  | Node cs => list_of_atoms CA cs
  | _ => None
  end.

(** List element conversion round trips by structural induction. *)
Theorem list_atoms_roundtrip {A} (CA : codec A) (HA : codec_laws CA) :
  forall xs, list_of_atoms CA (Cost.value (list_atoms_c CA xs)) = Some xs.
Proof.
  solve_roundtrip.
Qed.

(** Lists use a node containing one atom per component code. *)
Definition list_codec {A} (CA : codec A) : codec (list A) :=
  Codec
    (Encoding (fun xs =>
      Cost.step ;;
      let* c := list_to_code_c CA xs in
      code_encode_c c))
    (fun p =>
      match code_decode p with
      | Some c => list_of_code CA c
      | None => None
      end).

(** Component round trips imply the list round trip, including the empty list. *)
Theorem list_codec_laws {A} (CA : codec A) :
  codec_laws CA -> codec_laws (list_codec CA).
Proof.
  intros HA.
  exact (derive_laws (list_to_code_c CA) (list_of_code CA) (list_atoms_roundtrip CA HA)).
Qed.

(** Options distinguish an empty node from a node holding one atom. *)
Definition option_to_code_c {A} (CA : codec A) (x : option A) : Cost.t code :=
  match x with
  | None => Cost.ret (Node [])
  | Some a =>
    Cost.step ;;
    Cost.map (fun p => Node [Atom p]) (encode_c (codec_enc CA) a)
  end.

(** Option decoding rejects every shape except an empty node or a single atom. *)
Definition option_of_code {A} (CA : codec A) (c : code) : option (option A) :=
  match c with
  | Node [] => Some None
  | Node [Atom p] => option_map (@Some A) (decode CA p)
  | _ => None
  end.

(** Option conversion recovers presence and absence using the component law. *)
Theorem option_roundtrip {A} (CA : codec A) (HA : codec_laws CA) :
  forall x, option_of_code CA (Cost.value (option_to_code_c CA x)) = Some x.
Proof.
  solve_roundtrip.
Qed.

(** Option dictionaries compute without any component proof. *)
Definition option_codec {A} (CA : codec A) : codec (option A) :=
  Codec
    (Encoding (fun x =>
      Cost.step ;;
      let* c := option_to_code_c CA x in
      code_encode_c c))
    (fun p =>
      match code_decode p with
      | Some c => option_of_code CA c
      | None => None
      end).

(** Option codec laws follow from the component codec law. *)
Theorem option_codec_laws {A} (CA : codec A) :
  codec_laws CA -> codec_laws (option_codec CA).
Proof.
  intro HA. exact (derive_laws _ _ (option_roundtrip CA HA)).
Qed.

(** Sums distinguish a direct atom from a nested node and charge the selected callback. *)
Definition sum_to_code_c {A B} (CA : codec A) (CB : codec B) (x : A + B) : Cost.t code :=
  Cost.step ;;
  match x with
  | inl a => Cost.map (fun p => Node [Atom p]) (encode_c (codec_enc CA) a)
  | inr b => Cost.map (fun p => Node [Node [Atom p]]) (encode_c (codec_enc CB) b)
  end.

(** Sum decoding chooses the component decoder from the direct or nested atom shape. *)
Definition sum_of_code {A B} (CA : codec A) (CB : codec B) (c : code) : option (A + B) :=
  match c with
  | Node [Atom p] => option_map (@inl A B) (decode CA p)
  | Node [Node [Atom p]] => option_map (@inr A B) (decode CB p)
  | _ => None
  end.

(** Sum conversion preserves both alternatives under their component laws. *)
Theorem sum_roundtrip {A B} (CA : codec A) (CB : codec B)
    (HA : codec_laws CA) (HB : codec_laws CB) :
  forall x, sum_of_code CA CB (Cost.value (sum_to_code_c CA CB x)) = Some x.
Proof.
  solve_roundtrip.
Qed.

(** Sum dictionaries need no laws to compute either alternative. *)
Definition sum_codec {A B} (CA : codec A) (CB : codec B) : codec (A + B) :=
  Codec
    (Encoding (fun x =>
      Cost.step ;;
      let* c := sum_to_code_c CA CB x in
      code_encode_c c))
    (fun p =>
      match code_decode p with
      | Some c => sum_of_code CA CB c
      | None => None
      end).

(** Sum codec laws use the law for each alternative. *)
Theorem sum_codec_laws {A B} (CA : codec A) (CB : codec B) :
  codec_laws CA -> codec_laws CB -> codec_laws (sum_codec CA CB).
Proof.
  intros HA HB. exact (derive_laws _ _ (sum_roundtrip CA CB HA HB)).
Qed.

(** * Component-relative and numeric cost contracts *)

(** List conversion returns the component keys in their original order. *)
Theorem list_atoms_equation {A} (CA : codec A) xs :
  Cost.value (list_atoms_c CA xs) = map (fun x => Atom (encode (codec_enc CA) x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [list_atoms_c map];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

(** Pair keys are nodes containing the two component codes. *)
Theorem pair_codec_equation {A B} (CA : codec A) (CB : codec B) a b :
  encode (codec_enc (pair_codec CA CB)) (a, b) =
    code_encode (Node [Atom (encode (codec_enc CA) a); Atom (encode (codec_enc CB) b)]).
Proof.
  reflexivity.
Qed.

(** List keys contain one atom per component key. *)
Theorem list_codec_equation {A} (CA : codec A) xs :
  encode (codec_enc (list_codec CA)) xs =
    code_encode (Node (map (fun x => Atom (encode (codec_enc CA) x)) xs)).
Proof.
  change (code_encode (Node (Cost.value (list_atoms_c CA xs))) =
    code_encode (Node (map (fun x => Atom (encode (codec_enc CA) x)) xs))).
  now rewrite list_atoms_equation.
Qed.

(** Option keys distinguish absence from a single component atom. *)
Theorem option_codec_equation {A} (CA : codec A) x :
  encode (codec_enc (option_codec CA)) x =
    code_encode
      (match x with
      | None => Node []
      | Some a => Node [Atom (encode (codec_enc CA) a)]
      end).
Proof.
  destruct x; reflexivity.
Qed.

(** Sum keys distinguish a direct atom from an atom inside a nested node. *)
Theorem sum_codec_equation {A B} (CA : codec A) (CB : codec B) x :
  encode (codec_enc (sum_codec CA CB)) x =
    code_encode
      (match x with
      | inl a => Node [Atom (encode (codec_enc CA) a)]
      | inr b => Node [Node [Atom (encode (codec_enc CB) b)]]
      end).
Proof.
  destruct x; reflexivity.
Qed.

Local Lemma atoms_weight {A} (f : A -> positive) xs :
  N.of_nat (children_weight (map (fun x => Atom (f x)) xs)) =
    (1 + 2 * N.of_nat (length xs) +
      2 * fold_right (fun x n => N.pos (Pos.size (f x)) + n)%N 0%N xs)%N.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [map children_weight code_weight length fold_right].
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ, !Nat2N.inj_mul, size_nat_N, IH.
    nia.
Qed.

(** Atom-list serialization is linear in the number and total bits of its components. *)
Theorem code_atoms_bits {A} (f : A -> positive) xs :
  N.pos (Pos.size (code_encode (Node (map (fun x => Atom (f x)) xs)))) =
    (3 + 2 * N.of_nat (length xs) +
      2 * fold_right (fun x n => N.pos (Pos.size (f x)) + n)%N 0%N xs)%N.
Proof.
  rewrite code_encode_bits, code_weight_node, Nat2N.inj_add, atoms_weight.
  lia.
Qed.

(** Pair output size dominates both component sizes, without requiring any codec laws. *)
Theorem pair_codec_bits {A B} (CA : codec A) (CB : codec B) a b :
  key_bits (codec_enc (pair_codec CA CB)) (a, b) =
    (7 + 2 * key_bits (codec_enc CA) a + 2 * key_bits (codec_enc CB) b)%N.
Proof.
  unfold key_bits. rewrite pair_codec_equation.
  change (N.pos (Pos.size (code_encode (Node
    (map (fun p => Atom p) [encode (codec_enc CA) a; encode (codec_enc CB) b])))) =
    (7 + 2 * N.pos (Pos.size (encode (codec_enc CA) a)) +
      2 * N.pos (Pos.size (encode (codec_enc CB) b)))%N).
  rewrite code_atoms_bits. cbn [length fold_right]. lia.
Qed.

(** List output size dominates the sum of component sizes and the list traversal length. *)
Theorem list_codec_bits {A} (CA : codec A) xs :
  key_bits (codec_enc (list_codec CA)) xs =
    (3 + 2 * N.of_nat (length xs) +
      2 * fold_right (fun x n => key_bits (codec_enc CA) x + n)%N 0%N xs)%N.
Proof.
  unfold key_bits. rewrite list_codec_equation, code_atoms_bits. reflexivity.
Qed.

(** Option size includes a constant tag overhead and twice the selected component size. *)
Theorem option_codec_bits {A} (CA : codec A) x :
  key_bits (codec_enc (option_codec CA)) x =
    match x with
    | None => 3%N
    | Some a => (5 + 2 * key_bits (codec_enc CA) a)%N
    end.
Proof.
  unfold key_bits. rewrite option_codec_equation. destruct x as [a|].
  - change (N.pos (Pos.size (code_encode
      (Node (map (fun p => Atom p) [encode (codec_enc CA) a])))) =
      (5 + 2 * N.pos (Pos.size (encode (codec_enc CA) a)))%N).
    rewrite code_atoms_bits. cbn [length fold_right]. lia.
  - reflexivity.
Qed.

(** Sum size includes the chosen tag shape and twice the selected component size. *)
Theorem sum_codec_bits {A B} (CA : codec A) (CB : codec B) x :
  key_bits (codec_enc (sum_codec CA CB)) x =
    match x with
    | inl a => (5 + 2 * key_bits (codec_enc CA) a)%N
    | inr b => (8 + 2 * key_bits (codec_enc CB) b)%N
    end.
Proof.
  unfold key_bits. rewrite sum_codec_equation. destruct x as [a|b].
  - change (N.pos (Pos.size (code_encode
      (Node (map (fun p => Atom p) [encode (codec_enc CA) a])))) =
      (5 + 2 * N.pos (Pos.size (encode (codec_enc CA) a)))%N).
    rewrite code_atoms_bits. cbn [length fold_right]. lia.
  - rewrite code_encode_bits. cbn [code_weight].
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_succ, size_nat_N. nia.
Qed.

(** Pair cost includes both component calls and a fixed serialization-overhead bound. *)
Theorem pair_codec_cost {A B} (CA : codec A) (CB : codec B) a b :
  (Cost.ticks (encode_c (codec_enc (pair_codec CA CB)) (a, b)) <=
    3 + Cost.ticks (encode_c (codec_enc CA) a) +
      Cost.ticks (encode_c (codec_enc CB) b) +
      encode_k * key_bits (codec_enc (pair_codec CA CB)) (a, b))%N.
Proof.
  pose proof (code_encode_cost
    (Node [Atom (encode (codec_enc CA) a); Atom (encode (codec_enc CB) b)])) as Hcode.
  unfold pair_codec at 1. unfold pair_to_code_c. cbn [codec_enc encode_c fst snd].
  autorewrite with galois_cost.
  unfold key_bits in *. rewrite pair_codec_equation.
  unfold encode in *. lia.
Qed.

(** List conversion charges every traversal step and every component callback. *)
Theorem list_atoms_cost {A} (CA : codec A) xs :
  Cost.ticks (list_atoms_c CA xs) =
    (1 + 2 * N.of_nat (length xs) +
      fold_right (fun x n => Cost.ticks (encode_c (codec_enc CA) x) + n)%N 0%N xs)%N.
Proof.
  induction xs as [|x xs IH]; cbn [list_atoms_c length fold_right];
    autorewrite with galois_cost; rewrite ?IH, ?Nat2N.inj_succ; lia.
Qed.

(** List cost includes all component calls, traversal steps and serialization work. *)
Theorem list_codec_cost {A} (CA : codec A) xs :
  (Cost.ticks (encode_c (codec_enc (list_codec CA)) xs) <=
    2 + 2 * N.of_nat (length xs) +
      fold_right (fun x n => Cost.ticks (encode_c (codec_enc CA) x) + n)%N 0%N xs +
      encode_k * key_bits (codec_enc (list_codec CA)) xs)%N.
Proof.
  pose proof (code_encode_cost (Node (Cost.value (list_atoms_c CA xs)))) as Hcode.
  unfold list_codec at 1. cbn [codec_enc encode_c].
  unfold list_to_code_c. autorewrite with galois_cost. rewrite list_atoms_cost.
  unfold key_bits. rewrite list_codec_equation, <- list_atoms_equation. lia.
Qed.

(** Option cost charges the selected component and serialization, with no call on absence. *)
Theorem option_codec_cost {A} (CA : codec A) x :
  (Cost.ticks (encode_c (codec_enc (option_codec CA)) x) <=
    2 +
      match x with
      | None => 0
      | Some a => Cost.ticks (encode_c (codec_enc CA) a)
      end +
      encode_k * key_bits (codec_enc (option_codec CA)) x)%N.
Proof.
  destruct x as [a|].
  - pose proof (code_encode_cost (Node [Atom (encode (codec_enc CA) a)])) as Hcode.
    unfold option_codec at 1. cbn [codec_enc encode_c option_to_code_c].
    autorewrite with galois_cost.
    unfold key_bits. rewrite option_codec_equation.
    unfold encode in *. lia.
  - pose proof (code_encode_cost (Node [])) as Hcode.
    unfold option_codec at 1. cbn [codec_enc encode_c option_to_code_c].
    autorewrite with galois_cost.
    unfold key_bits. rewrite option_codec_equation. lia.
Qed.

(** Sum cost includes exactly the selected component callback and serialization work. *)
Theorem sum_codec_cost {A B} (CA : codec A) (CB : codec B) x :
  (Cost.ticks (encode_c (codec_enc (sum_codec CA CB)) x) <=
    2 +
      match x with
      | inl a => Cost.ticks (encode_c (codec_enc CA) a)
      | inr b => Cost.ticks (encode_c (codec_enc CB) b)
      end +
      encode_k * key_bits (codec_enc (sum_codec CA CB)) x)%N.
Proof.
  destruct x as [a|b].
  - pose proof (code_encode_cost (Node [Atom (encode (codec_enc CA) a)])) as Hcode.
    unfold sum_codec at 1. cbn [codec_enc encode_c sum_to_code_c].
    autorewrite with galois_cost.
    unfold sum_to_code_c. autorewrite with galois_cost.
    unfold key_bits. rewrite sum_codec_equation. unfold encode in *. lia.
  - pose proof (code_encode_cost (Node [Node [Atom (encode (codec_enc CB) b)]])) as Hcode.
    unfold sum_codec at 1. cbn [codec_enc encode_c sum_to_code_c].
    autorewrite with galois_cost.
    unfold sum_to_code_c. autorewrite with galois_cost.
    unfold key_bits. rewrite sum_codec_equation. unfold encode in *. lia.
Qed.

(** Numeric pair cost depends on explicit component numeric laws. *)
Theorem pair_codec_encode_cost_le {A B} (CA : codec A) (CB : codec B) ka kb a b :
  encoding_cost_laws (codec_enc CA) ka ->
  encoding_cost_laws (codec_enc CB) kb ->
  (Cost.ticks (encode_c (codec_enc (pair_codec CA CB)) (a, b)) <=
    (ka + kb + encode_k + 3) * key_bits (codec_enc (pair_codec CA CB)) (a, b))%N.
Proof.
  intros HA HB.
  pose proof (pair_codec_cost CA CB a b) as Hcost.
  pose proof (encode_cost_bound HA a) as Ha.
  pose proof (encode_cost_bound HB b) as Hb.
  rewrite pair_codec_bits in *. nia.
Qed.

Local Lemma component_cost_sum {A} (CA : codec A) k
    (Hcost : encoding_cost_laws (codec_enc CA) k) xs :
  (fold_right (fun x n => Cost.ticks (encode_c (codec_enc CA) x) + n)%N 0%N xs <=
    k * fold_right (fun x n => key_bits (codec_enc CA) x + n)%N 0%N xs)%N.
Proof.
  induction xs as [|x xs IH]; cbn [fold_right].
  - lia.
  - pose proof (encode_cost_bound Hcost x). nia.
Qed.

(** Numeric list cost uses a component law and the output's domination of total key size. *)
Theorem list_codec_encode_cost_le {A} (CA : codec A) k xs :
  encoding_cost_laws (codec_enc CA) k ->
  (Cost.ticks (encode_c (codec_enc (list_codec CA)) xs) <=
    (k + encode_k + 2) * key_bits (codec_enc (list_codec CA)) xs)%N.
Proof.
  intro HA.
  pose proof (list_codec_cost CA xs) as Hcost.
  pose proof (component_cost_sum CA k HA xs) as Hcalls.
  rewrite list_codec_bits in *. nia.
Qed.

(** Numeric option cost needs a law for the present component, even when absence is allowed. *)
Theorem option_codec_encode_cost_le {A} (CA : codec A) k x :
  encoding_cost_laws (codec_enc CA) k ->
  (Cost.ticks (encode_c (codec_enc (option_codec CA)) x) <=
    (k + encode_k + 2) * key_bits (codec_enc (option_codec CA)) x)%N.
Proof.
  intro HA. pose proof (option_codec_cost CA x) as Hcost.
  destruct x as [a|]; rewrite option_codec_bits in *.
  - pose proof (encode_cost_bound HA a). nia.
  - nia.
Qed.

(** Numeric sum cost uses both component laws and charges the alternative actually taken. *)
Theorem sum_codec_encode_cost_le {A B} (CA : codec A) (CB : codec B) ka kb x :
  encoding_cost_laws (codec_enc CA) ka ->
  encoding_cost_laws (codec_enc CB) kb ->
  (Cost.ticks (encode_c (codec_enc (sum_codec CA CB)) x) <=
    (ka + kb + encode_k + 2) * key_bits (codec_enc (sum_codec CA CB)) x)%N.
Proof.
  intros HA HB. pose proof (sum_codec_cost CA CB x) as Hcost.
  destruct x as [a|b]; rewrite sum_codec_bits in *.
  - pose proof (encode_cost_bound HA a). nia.
  - pose proof (encode_cost_bound HB b). nia.
Qed.

(** Built-in pair codecs propagate separate numeric laws. *)
Theorem pair_codec_cost_laws {A B} (CA : codec A) (CB : codec B) ka kb :
  encoding_cost_laws (codec_enc CA) ka ->
  encoding_cost_laws (codec_enc CB) kb ->
  encoding_cost_laws (codec_enc (pair_codec CA CB)) (ka + kb + encode_k + 3).
Proof.
  intros HA HB. constructor. intros [a b].
  now apply pair_codec_encode_cost_le.
Qed.

(** Built-in list codecs propagate the component numeric law. *)
Theorem list_codec_cost_laws {A} (CA : codec A) k :
  encoding_cost_laws (codec_enc CA) k ->
  encoding_cost_laws (codec_enc (list_codec CA)) (k + encode_k + 2).
Proof.
  intro HA. constructor. intro xs. now apply list_codec_encode_cost_le.
Qed.

(** Built-in option codecs propagate the component numeric law. *)
Theorem option_codec_cost_laws {A} (CA : codec A) k :
  encoding_cost_laws (codec_enc CA) k ->
  encoding_cost_laws (codec_enc (option_codec CA)) (k + encode_k + 2).
Proof.
  intro HA. constructor. intro x. now apply option_codec_encode_cost_le.
Qed.

(** Built-in sum codecs propagate both component numeric laws. *)
Theorem sum_codec_cost_laws {A B} (CA : codec A) (CB : codec B) ka kb :
  encoding_cost_laws (codec_enc CA) ka ->
  encoding_cost_laws (codec_enc CB) kb ->
  encoding_cost_laws (codec_enc (sum_codec CA CB)) (ka + kb + encode_k + 2).
Proof.
  intros HA HB. constructor. intro x. now apply sum_codec_encode_cost_le.
Qed.

(** * Encoding-only pair and sum composition *)

(** Pair encodings serialize two component atoms and charge each component callback. *)
Definition pair_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A * B) :=
  Encoding (fun xy =>
    Cost.step ;;
    Cost.step ;;
    let* p := encode_c EA (fst xy) in
    Cost.step ;;
    let* q := encode_c EB (snd xy) in
    code_encode_c (Node [Atom p; Atom q])).

(** Sum encodings serialize the selected atom under the existing direct or nested node tag. *)
Definition sum_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A + B) :=
  Encoding (fun x =>
    Cost.step ;;
    Cost.step ;;
    match x with
    | inl a =>
      let* p := encode_c EA a in
      code_encode_c (Node [Atom p])
    | inr b =>
      let* p := encode_c EB b in
      code_encode_c (Node [Node [Atom p]])
    end).

(** Pair encoding uses the same serialized two-atom layout as pair codecs. *)
Theorem pair_encoding_equation {A B} (EA : encoding A) (EB : encoding B) a b :
  encode (pair_encoding EA EB) (a, b) =
    code_encode (Node [Atom (encode EA a); Atom (encode EB b)]).
Proof.
  reflexivity.
Qed.

(** Sum encoding uses the same serialized side tags as sum codecs. *)
Theorem sum_encoding_equation {A B} (EA : encoding A) (EB : encoding B) x :
  encode (sum_encoding EA EB) x =
    code_encode
      (match x with
      | inl a => Node [Atom (encode EA a)]
      | inr b => Node [Node [Atom (encode EB b)]]
      end).
Proof.
  destruct x; reflexivity.
Qed.

Local Lemma serialized_code_injective c d : code_encode c = code_encode d -> c = d.
Proof.
  intro Hcode. apply (f_equal code_decode) in Hcode.
  rewrite !code_decode_encode in Hcode. now injection Hcode.
Qed.

(** Pair injectivity requires the two component encoding laws and no component decoders. *)
Theorem pair_encoding_laws {A B} (EA : encoding A) (EB : encoding B) :
  encoding_laws EA -> encoding_laws EB -> encoding_laws (pair_encoding EA EB).
Proof.
  intros HA HB. constructor. intros [a b] [a' b'] Hcode.
  rewrite !pair_encoding_equation in Hcode.
  apply serialized_code_injective in Hcode. injection Hcode as Ha Hb.
  f_equal.
  - exact (encode_injective HA _ _ Ha).
  - exact (encode_injective HB _ _ Hb).
Qed.

(** Sum tags distinguish the two sides even when their component codes coincide. *)
Theorem sum_encoding_disjoint {A B} (EA : encoding A) (EB : encoding B) a b :
  encode (sum_encoding EA EB) (inl a) <> encode (sum_encoding EA EB) (inr b).
Proof.
  intro Hcode. rewrite !sum_encoding_equation in Hcode.
  apply serialized_code_injective in Hcode. discriminate.
Qed.

(** Sum injectivity requires the two component encoding laws and no component decoders. *)
Theorem sum_encoding_laws {A B} (EA : encoding A) (EB : encoding B) :
  encoding_laws EA -> encoding_laws EB -> encoding_laws (sum_encoding EA EB).
Proof.
  intros HA HB. constructor. intros [a|b] [a'|b'] Hcode;
    rewrite !sum_encoding_equation in Hcode;
    apply serialized_code_injective in Hcode; try discriminate.
  - injection Hcode as Ha. f_equal. exact (encode_injective HA _ _ Ha).
  - injection Hcode as Hb. f_equal. exact (encode_injective HB _ _ Hb).
Qed.

(** Pair width counts both component widths and all serializer tags without law premises. *)
Theorem pair_encoding_bits {A B} (EA : encoding A) (EB : encoding B) a b :
  key_bits (pair_encoding EA EB) (a, b) =
    (7 + 2 * key_bits EA a + 2 * key_bits EB b)%N.
Proof.
  unfold key_bits. rewrite pair_encoding_equation, code_encode_bits.
  cbn [code_weight].
  rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_succ, !size_nat_N. nia.
Qed.

(** Sum width counts the selected component and its side tag without law premises. *)
Theorem sum_encoding_bits {A B} (EA : encoding A) (EB : encoding B) x :
  key_bits (sum_encoding EA EB) x =
    match x with
    | inl a => (5 + 2 * key_bits EA a)%N
    | inr b => (8 + 2 * key_bits EB b)%N
    end.
Proof.
  unfold key_bits. rewrite sum_encoding_equation. destruct x as [a|b];
    rewrite code_encode_bits; cbn [code_weight];
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_succ, size_nat_N; nia.
Qed.

(** Pair cost retains both actual component charges and the actual serializer charge. *)
Theorem pair_encoding_cost_equation {A B} (EA : encoding A) (EB : encoding B) a b :
  Cost.ticks (encode_c (pair_encoding EA EB) (a, b)) =
    (3 + Cost.ticks (encode_c EA a) + Cost.ticks (encode_c EB b) +
      Cost.ticks (code_encode_c (Node [Atom (encode EA a); Atom (encode EB b)])))%N.
Proof.
  unfold pair_encoding. cbn [encode_c fst snd]. autorewrite with galois_cost.
  unfold encode. lia.
Qed.

(** Sum cost retains the selected component charge and the actual serializer charge. *)
Theorem sum_encoding_cost_equation {A B} (EA : encoding A) (EB : encoding B) x :
  Cost.ticks (encode_c (sum_encoding EA EB) x) =
    match x with
    | inl a =>
      (2 + Cost.ticks (encode_c EA a) +
        Cost.ticks (code_encode_c (Node [Atom (encode EA a)])))%N
    | inr b =>
      (2 + Cost.ticks (encode_c EB b) +
        Cost.ticks (code_encode_c (Node [Node [Atom (encode EB b)]])))%N
    end.
Proof.
  destruct x; unfold sum_encoding; cbn [encode_c]; autorewrite with galois_cost;
    unfold encode; lia.
Qed.

(** Pair serialization overhead is bounded separately from arbitrary component charges. *)
Theorem pair_encoding_cost {A B} (EA : encoding A) (EB : encoding B) a b :
  (Cost.ticks (encode_c (pair_encoding EA EB) (a, b)) <=
    3 + Cost.ticks (encode_c EA a) + Cost.ticks (encode_c EB b) +
      encode_k * key_bits (pair_encoding EA EB) (a, b))%N.
Proof.
  rewrite pair_encoding_cost_equation.
  pose proof (code_encode_cost (Node [Atom (encode EA a); Atom (encode EB b)])) as Hcode.
  unfold key_bits. rewrite pair_encoding_equation. lia.
Qed.

(** Sum serialization overhead is bounded separately from the selected component charge. *)
Theorem sum_encoding_cost {A B} (EA : encoding A) (EB : encoding B) x :
  (Cost.ticks (encode_c (sum_encoding EA EB) x) <=
    2 +
      match x with
      | inl a => Cost.ticks (encode_c EA a)
      | inr b => Cost.ticks (encode_c EB b)
      end +
      encode_k * key_bits (sum_encoding EA EB) x)%N.
Proof.
  rewrite sum_encoding_cost_equation. unfold key_bits. rewrite sum_encoding_equation.
  destruct x as [a|b].
  - pose proof (code_encode_cost (Node [Atom (encode EA a)])) as Hcode. lia.
  - pose proof (code_encode_cost (Node [Node [Atom (encode EB b)]])) as Hcode. lia.
Qed.

(** Numeric pair bounds require explicit numeric laws for both component encodings. *)
Theorem pair_encoding_encode_cost_le {A B} (EA : encoding A) (EB : encoding B) ka kb a b :
  encoding_cost_laws EA ka -> encoding_cost_laws EB kb ->
  (Cost.ticks (encode_c (pair_encoding EA EB) (a, b)) <=
    (ka + kb + encode_k + 3) * key_bits (pair_encoding EA EB) (a, b))%N.
Proof.
  intros HA HB.
  pose proof (pair_encoding_cost EA EB a b) as Hcost.
  pose proof (encode_cost_bound HA a) as Ha.
  pose proof (encode_cost_bound HB b) as Hb.
  rewrite pair_encoding_bits in *. nia.
Qed.

(** Numeric sum bounds require explicit numeric laws for both possible component encodings. *)
Theorem sum_encoding_encode_cost_le {A B} (EA : encoding A) (EB : encoding B) ka kb x :
  encoding_cost_laws EA ka -> encoding_cost_laws EB kb ->
  (Cost.ticks (encode_c (sum_encoding EA EB) x) <=
    (ka + kb + encode_k + 2) * key_bits (sum_encoding EA EB) x)%N.
Proof.
  intros HA HB. pose proof (sum_encoding_cost EA EB x) as Hcost.
  destruct x as [a|b]; rewrite sum_encoding_bits in *.
  - pose proof (encode_cost_bound HA a). nia.
  - pose proof (encode_cost_bound HB b). nia.
Qed.

(** Pair composition propagates numeric laws independently of injectivity. *)
Theorem pair_encoding_cost_laws {A B} (EA : encoding A) (EB : encoding B) ka kb :
  encoding_cost_laws EA ka -> encoding_cost_laws EB kb ->
  encoding_cost_laws (pair_encoding EA EB) (ka + kb + encode_k + 3).
Proof.
  intros HA HB. constructor. intros [a b]. now apply pair_encoding_encode_cost_le.
Qed.

(** Sum composition propagates numeric laws independently of injectivity. *)
Theorem sum_encoding_cost_laws {A B} (EA : encoding A) (EB : encoding B) ka kb :
  encoding_cost_laws EA ka -> encoding_cost_laws EB kb ->
  encoding_cost_laws (sum_encoding EA EB) (ka + kb + encode_k + 2).
Proof.
  intros HA HB. constructor. intro x. now apply sum_encoding_encode_cost_le.
Qed.
