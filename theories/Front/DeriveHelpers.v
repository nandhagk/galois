(** * Definitions that derived programs call

    The command [Egglog] of [Derive.v] derives programs and lemmas that use the definitions of
    this file. Engine values are positives, and [id_encode] and [id_decode] make [positive] its
    own value type. A pair, an option and a list of value types are value types as well, and
    [encode_pair], [encode_option] and [encode_list] encode them from the encoders of their
    parts. A primitive set calls each of its functions through a chain of steps [prim_arg],
    one for each argument, and a final [prim_ret]. Each step decodes one argument, and the final
    one encodes the result. [prim_case] selects a function by its code. Two pairs are related by
    [pair_rel] when their sides are, which the congruence law of a list of pairs states. The
    file also registers the schemes [All] of pairs and of conjunctions, so that a client of the
    command can declare a datatype that holds a list of pairs and a law over [pair_rel].

    For example, [prim_arg da (prim_arg db (prim_ret er)) f [a; b]] decodes [a] with [da] and
    [b] with [db], and gives [Some (er (f x y))] when they decode to [x] and [y].

    Main results
    - [encode_inj_of] An encoder that decodes its own encodings is injective.
    - [decode_encode_pair], [decode_encode_option] and [decode_encode_list] The decoders of
      pairs, options and lists undo their encoders.
    - [prim_arg_cons] and [prim_arg_inv] A step of a call decodes one argument.
    - [prim_case_hit] and [prim_case_miss] The primitive function of a set selects the call of
      a code by comparing codes.

    Builds on: Stdlib lists and binary arithmetic, and Argent time functions. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Std.

Import List.ListNotations.

(** * Values

    A value of a registered type is the positive of its encoder. [id_decode] and [id_encode]
    are the encoder of [positive], which is its own engine value. *)

Create HintDb egglog_decode.
Create HintDb egglog_inj.

Definition id_decode (p : positive) : option positive := Some p.

Definition id_encode (p : positive) : positive := p.

TimeFun id_decode id_encode.

(** Decoding the identity encoding gives the value back. *)
Lemma id_decode_encode : forall x, id_decode (id_encode x) = Some x.
Proof.
  reflexivity.
Qed.

#[export] Hint Resolve id_decode_encode : egglog_decode.

(** An encoder that decodes its own encodings is injective. *)
Lemma encode_inj_of {A : Type} (enc : A -> positive) (dec : positive -> option A)
    (Hdec : forall x, dec (enc x) = Some x) (x y : A) : enc x = enc y -> x = y.
Proof.
  intros Henc. apply (f_equal dec) in Henc. rewrite !Hdec in Henc. injection Henc as Hxy.
  exact Hxy.
Qed.

(** * Pairs, options and lists of values

    A positive is a list of bits, from the least significant one, that ends in its leading
    one. [push_bits a r] writes the bits of [a] below its leading one in front of [r], the most
    significant bit first and each after a one, so a zero in place of that one ends them. The
    encoding of a pair writes the bits of its first side, a zero and its second side. The
    encoding of a nonempty list writes a zero, the bits of its first element, a zero and the
    encoding of the rest, and the encoding of the empty list is one. *)

(** The bits of [a] in front of [r], the most significant bit first and each after a one. *)
Fixpoint push_bits (a r : positive) : positive :=
  match a with
  | xH => r
  | xO a' => push_bits a' (xI (xO r))
  | xI a' => push_bits a' (xI (xI r))
  end.

(** The positive that [push_bits] wrote in front of [p], with its bits after those of [t], and
    the rest of [p]. *)
Fixpoint pop_bits (p t : positive) : option (positive * positive) :=
  match p with
  | xI (xO q) => pop_bits q (xO t)
  | xI (xI q) => pop_bits q (xI t)
  | xO r => Some (t, r)
  | _ => None
  end.

(** The encoding of a pair, from the encoders of its two sides. *)
Definition encode_pair {A B : Type} (ea : A -> positive) (eb : B -> positive) (x : A * B) :
    positive :=
  push_bits (ea (fst x)) (xO (eb (snd x))).

(** The pair of a positive, when it encodes one. *)
Definition decode_pair {A B : Type} (da : positive -> option A) (db : positive -> option B)
    (p : positive) : option (A * B) :=
  match pop_bits p xH with
  | Some (a, b) =>
      match da a, db b with
      | Some x, Some y => Some (x, y)
      | _, _ => None
      end
  | None => None
  end.

(** The encoding of an option is one for nothing, and the encoding of a value after a zero. *)
Definition encode_option {A : Type} (ea : A -> positive) (o : option A) : positive :=
  match o with
  | None => xH
  | Some x => xO (ea x)
  end.

(** The option of a positive, when it encodes one. *)
Definition decode_option {A : Type} (da : positive -> option A) (p : positive) :
    option (option A) :=
  match p with
  | xH => Some None
  | xO q =>
      match da q with
      | Some x => Some (Some x)
      | None => None
      end
  | xI _ => None
  end.

(** The encoding of a list, from the encoder of its elements. *)
Fixpoint encode_list {A : Type} (ea : A -> positive) (l : list A) : positive :=
  match l with
  | [] => xH
  | x :: rest => xO (push_bits (ea x) (xO (encode_list ea rest)))
  end.

(** The elements that [encode_list] wrote in [p] after a first zero, where the bits of the first
    element come after those of [t]. *)
Fixpoint pop_list {A : Type} (da : positive -> option A) (p t : positive) : option (list A) :=
  match p with
  | xI (xO q) => pop_list da q (xO t)
  | xI (xI q) => pop_list da q (xI t)
  | xO r =>
      match da t, r with
      | Some x, xH => Some [x]
      | Some x, xO q =>
          match pop_list da q xH with
          | Some l => Some (x :: l)
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

(** The list of a positive, when it encodes one. *)
Definition decode_list {A : Type} (da : positive -> option A) (p : positive) :
    option (list A) :=
  match p with
  | xH => Some []
  | xO q => pop_list da q xH
  | xI _ => None
  end.

TimeFun push_bits pop_bits encode_pair decode_pair encode_option decode_option encode_list
  pop_list decode_list.

(** The bits of [a] below its leading one after the bits of [t]. *)
Fixpoint graft (t a : positive) : positive :=
  match a with
  | xH => t
  | xO a' => xO (graft t a')
  | xI a' => xI (graft t a')
  end.

(** Grafting the bits of [a] onto one gives [a]. *)
Lemma graft_one (a : positive) : graft xH a = a.
Proof.
  induction a as [a IH | a IH |]; simpl; [rewrite IH | rewrite IH |]; reflexivity.
Qed.

(** Popping the bits that [push_bits] wrote moves them after the bits of [t]. *)
Lemma pop_push (a r t : positive) : pop_bits (push_bits a r) t = pop_bits r (graft t a).
Proof.
  revert r t.
  induction a as [a IH | a IH |]; intros r t; simpl.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
Qed.

(** Popping the elements of a list reads the bits that [push_bits] wrote in the same way. *)
Lemma pop_list_push {A : Type} (da : positive -> option A) (a r t : positive) :
  pop_list da (push_bits a r) t = pop_list da r (graft t a).
Proof.
  revert r t.
  induction a as [a IH | a IH |]; intros r t; simpl.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
Qed.

(** The decoder of pairs undoes the encoder of pairs. *)
Lemma decode_encode_pair {A B : Type} (ea : A -> positive) (da : positive -> option A)
    (eb : B -> positive) (db : positive -> option B) :
  (forall x, da (ea x) = Some x) -> (forall y, db (eb y) = Some y) ->
  forall p, decode_pair da db (encode_pair ea eb p) = Some p.
Proof.
  intros Ha Hb [x y].
  unfold decode_pair, encode_pair. simpl.
  rewrite pop_push, graft_one. simpl.
  rewrite Ha, Hb. reflexivity.
Qed.

(** The decoder of options undoes the encoder of options. *)
Lemma decode_encode_option {A : Type} (ea : A -> positive) (da : positive -> option A) :
  (forall x, da (ea x) = Some x) -> forall o, decode_option da (encode_option ea o) = Some o.
Proof.
  intros Ha [x |]; simpl; [rewrite Ha |]; reflexivity.
Qed.

(** The elements of a nonempty list come back from the bits after its first zero. *)
Lemma pop_list_encode {A : Type} (ea : A -> positive) (da : positive -> option A) :
  (forall x, da (ea x) = Some x) ->
  forall l x, pop_list da (push_bits (ea x) (xO (encode_list ea l))) xH = Some (x :: l).
Proof.
  intros Ha l.
  induction l as [| y l IH]; intros x; rewrite pop_list_push, graft_one; simpl; rewrite Ha.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** The decoder of lists undoes the encoder of lists. *)
Lemma decode_encode_list {A : Type} (ea : A -> positive) (da : positive -> option A) :
  (forall x, da (ea x) = Some x) -> forall l, decode_list da (encode_list ea l) = Some l.
Proof.
  intros Ha [| x l]; simpl.
  - reflexivity.
  - exact (pop_list_encode ea da Ha l x).
Qed.

(** The tactic [simpl] leaves the encoders alone, as it does the registered ones, so that the
    encoding of a literal keeps its form, which the glue tactics decode. *)
Arguments encode_pair : simpl never.
Arguments encode_option : simpl never.
Arguments encode_list : simpl never.

#[export] Hint Resolve decode_encode_pair decode_encode_option decode_encode_list :
  egglog_decode.

(** Two pairs are related when [ra] relates their first sides and [rb] their second sides. *)
Definition pair_rel {A B : Type} (ra : A -> A -> Prop) (rb : B -> B -> Prop) (p q : A * B) :
    Prop :=
  ra (fst p) (fst q) /\ rb (snd p) (snd q).

(** * Primitives over encoded values

    A primitive function takes values of value types. The primitive of a set decodes each
    argument, calls the function and encodes the result, and has no result when a decoding
    fails or the number of values is not the number of arguments. *)

(** The last step of a call encodes the result [r] when no value is left. *)
Definition prim_ret {R : Type} (er : R -> positive) (r : R) (vs : list positive) :
    option positive :=
  match vs with
  | [] => Some (er r)
  | _ :: _ => None
  end.

(** A step of a call decodes the first value with [da] and gives it to [f], and it gives the
    rest of the values to the next step [k]. *)
Definition prim_arg {A F : Type} (da : positive -> option A)
    (k : F -> list positive -> option positive) (f : A -> F) (vs : list positive) :
    option positive :=
  match vs with
  | [] => None
  | a :: rest =>
      match da a with
      | Some x => k (f x) rest
      | None => None
      end
  end.

(** The result of the primitive with code [c] when [p] is [c], and [rest] otherwise. *)
Definition prim_case (p c : positive) (call : list positive -> option positive)
    (vs : list positive) (rest : option positive) : option positive :=
  if Pos.eqb p c then call vs else rest.

Arguments prim_ret : simpl never.
Arguments prim_arg : simpl never.

(** The primitive function of a set selects the call of a code that equals its own. *)
Lemma prim_case_hit (p c : positive) call vs rest :
  Pos.eqb p c = true -> prim_case p c call vs rest = call vs.
Proof.
  intros Heq. unfold prim_case. rewrite Heq. reflexivity.
Qed.

(** The primitive function of a set passes over the call of another code. *)
Lemma prim_case_miss (p c : positive) call vs rest :
  Pos.eqb p c = false -> prim_case p c call vs rest = rest.
Proof.
  intros Hneq. unfold prim_case. rewrite Hneq. reflexivity.
Qed.

(** The last step of a call encodes the result. *)
Lemma prim_ret_nil {R : Type} (er : R -> positive) (r : R) : prim_ret er r [] = Some (er r).
Proof.
  reflexivity.
Qed.

(** A step of a call on a decoded value gives the value to the function. *)
Lemma prim_arg_cons {A F : Type} (da : positive -> option A)
    (k : F -> list positive -> option positive) (f : A -> F) a vs x :
  da a = Some x -> prim_arg da k f (a :: vs) = k (f x) vs.
Proof.
  intros Ha. cbv [prim_arg]. rewrite Ha. reflexivity.
Qed.

(** A result of the last step of a call is the encoding of its result. *)
Lemma prim_ret_inv {R : Type} (er : R -> positive) (r : R) w :
  prim_ret er r [] = Some w -> w = er r.
Proof.
  cbv [prim_ret]. intros Hw. injection Hw as Hw. symmetry. exact Hw.
Qed.

(** A result of a step of a call comes from a decoded value. *)
Lemma prim_arg_inv {A F : Type} (da : positive -> option A)
    (k : F -> list positive -> option positive) (f : A -> F) a vs w :
  prim_arg da k f (a :: vs) = Some w -> exists x, da a = Some x /\ k (f x) vs = Some w.
Proof.
  cbv [prim_arg]. destruct (da a) as [x |]; intros Hw; [| discriminate].
  exists x. split; [reflexivity | exact Hw].
Qed.

(** * Lists of pairs

    A datatype of a program may hold a list of pairs, such as a list of fields from keys to
    terms, and the congruence law of such a list relates two lists by [pair_rel], which is a
    conjunction. Rocq declares such a datatype, or such a relation, with the warning
    [register-all] when no scheme [All] of pairs, or of conjunctions, is registered, and the
    flags of this project make that warning an error. The registrations below take effect in
    every file that requires this one, so every client of the command can declare them. *)

(** Nested inductives through pairs get their induction hypotheses from this scheme. *)
Scheme All for prod.

(** Relations nested through [pair_rel] get their induction hypotheses from this scheme. *)
Scheme All for and.
