(** * Encoders for common value types

    The modules [BoolEncode], [ZEncode], [NEncode] and [StringEncode] encode booleans,
    integers, natural numbers and strings as positives. Each is registered with [Egglog Value],
    so a relation over such values derives a program with [Derive.v] without further setup.
    Every encoding is a bijection onto the positives that it uses. The encoder of a string
    appends the bits of each character, least significant bit first, and ends with a one.

    For example, [ZEncode.encode (-3)] is [3~1], and [StringEncode.decode] reads the bits back
    to the string.

    Builds on: the encoder signature and the derive command. *)

From Stdlib Require Import PArith ZArith NArith String Ascii List.
From Argent Require Import Time.
From Galois.Front Require Import EncodeSig Derive.

Import List.ListNotations.

(** * Booleans *)

Module BoolEncode <: ENCODE.
  Definition t : Type := bool.
  Definition encode (b : bool) : positive := if b then xO xH else xH.
  Definition decode (p : positive) : option bool :=
    match p with
    | xH => Some false
    | xO xH => Some true
    | _ => None
    end.
  TimeFun encode.
  TimeFun decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros [|]; reflexivity.
  Qed.
End BoolEncode.

Egglog Value bool BoolEncode.

(** * Integers *)

Module ZEncode <: ENCODE.
  Definition t : Type := Z.
  Definition encode (z : Z) : positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Definition decode (p : positive) : option Z :=
    match p with
    | xH => Some Z0
    | xO q => Some (Zpos q)
    | xI q => Some (Zneg q)
    end.
  TimeFun encode.
  TimeFun decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.
End ZEncode.

Egglog Value Z ZEncode.

(** * Natural numbers *)

Module NEncode <: ENCODE.
  Definition t : Type := N.
  Definition encode (n : N) : positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Definition decode (p : positive) : option N :=
    match p with
    | xH => Some N0
    | xO q => Some (Npos q)
    | xI _ => None
    end.
  TimeFun encode.
  TimeFun decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros [|p]; reflexivity.
  Qed.
End NEncode.

Egglog Value N NEncode.

(** * Strings *)

Module StringEncode <: ENCODE.
  Definition t : Type := string.

  (** The bits of a character, least significant first, in front of [rest]. *)
  Definition char_bits (c : ascii) (rest : list bool) : list bool :=
    match c with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 => b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest
    end.

  TimeFun char_bits.

  (** The bits of a string. *)
  Fixpoint string_bits (s : string) : list bool :=
    match s with
    | EmptyString => []
    | String c s' => char_bits c (string_bits s')
    end.
  TimeFun string_bits.

  (** The positive whose bits are the list, from the least significant, ended by a one. *)
  Fixpoint bits_pos (l : list bool) : positive :=
    match l with
    | [] => xH
    | true :: l' => xI (bits_pos l')
    | false :: l' => xO (bits_pos l')
    end.
  TimeFun bits_pos.

  (** The bits of a positive, without its final one. *)
  Fixpoint pos_bits (p : positive) : list bool :=
    match p with
    | xH => []
    | xI q => true :: pos_bits q
    | xO q => false :: pos_bits q
    end.
  TimeFun pos_bits.

  (** The string of a list of bits, when its length is a multiple of eight. *)
  Fixpoint bits_string (l : list bool) : option string :=
    match l with
    | [] => Some EmptyString
    | b0 :: l1 =>
        match l1 with
        | b1 :: l2 =>
            match l2 with
            | b2 :: l3 =>
                match l3 with
                | b3 :: l4 =>
                    match l4 with
                    | b4 :: l5 =>
                        match l5 with
                        | b5 :: l6 =>
                            match l6 with
                            | b6 :: l7 =>
                                match l7 with
                                | b7 :: l8 =>
                                    match bits_string l8 with
                                    | Some s => Some (String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) s)
                                    | None => None
                                    end
                                | [] => None
                                end
                            | [] => None
                            end
                        | [] => None
                        end
                    | [] => None
                    end
                | [] => None
                end
            | [] => None
            end
        | [] => None
        end
    end.
  TimeFun bits_string.

  Definition encode (s : string) : positive := bits_pos (string_bits s).
  Definition decode (p : positive) : option string := bits_string (pos_bits p).
  TimeFun encode.
  TimeFun decode.

  Lemma pos_bits_pos : forall l, pos_bits (bits_pos l) = l.
  Proof.
    induction l as [| [|] l IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma bits_string_bits : forall s, bits_string (string_bits s) = Some s.
  Proof.
    induction s as [| [b0 b1 b2 b3 b4 b5 b6 b7] s IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros s. unfold decode, encode. rewrite pos_bits_pos. apply bits_string_bits.
  Qed.
End StringEncode.

Egglog Value string StringEncode.
