(** * Operator boundary examples

    Operators validate dynamic words before evaluating arithmetic and width changes.
    For example, unequal widths reject addition and concatenation accepts them.
    Builds on: Word, Fun, Op and BaseEncoding. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import Word Fun Op.
Import List.ListNotations.

Open Scope Z_scope.

(** Normalization fixes in-range endpoints and wraps raw values outside the range. *)
Example normalization_boundaries :
  normalize_word (8%positive, 0) = (8%positive, 0) /\
  normalize_word (8%positive, 255) = (8%positive, 255) /\
  normalize_word (8%positive, 256) = (8%positive, 0) /\
  normalize_word (8%positive, -1) = (8%positive, 255).
Proof.
  vm_compute. repeat split.
Qed.

(** Arithmetic wraps at the modulus, including the minimum signed value. *)
Example arithmetic_overflow :
  eval_op bvadd [(8%positive, 200); (8%positive, 100)] = Some (8%positive, 44) /\
  eval_op bvmul [(8%positive, 20); (8%positive, 20)] = Some (8%positive, 144) /\
  eval_op bvsub [(8%positive, 0); (8%positive, 1)] = Some (8%positive, 255) /\
  eval_op bvneg [(8%positive, 128)] = Some (8%positive, 128).
Proof.
  vm_compute. repeat split.
Qed.

(** Unsigned and signed division have their specified zero-divisor results. *)
Example zero_divisor :
  eval_op bvudiv [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 255) /\
  eval_op bvurem [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 7) /\
  eval_op bvsdiv [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 1) /\
  eval_op bvsrem [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249) /\
  eval_op bvsmod [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249).
Proof.
  vm_compute. repeat split.
Qed.

(** Comparisons distinguish signed from unsigned order and normalize equality inputs. *)
Example comparisons :
  eval_op bvult [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 0) /\
  eval_op bvslt [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 1) /\
  eval_op bveq [(8%positive, -1); (8%positive, 255)] = Some (1%positive, 1) /\
  eval_op bvne [(8%positive, 0); (8%positive, 255)] = Some (1%positive, 1) /\
  eval_op bvule [(8%positive, 5); (8%positive, 5)] = Some (1%positive, 1) /\
  eval_op bvsle [(8%positive, 128); (8%positive, 127)] = Some (1%positive, 1).
Proof.
  vm_compute. repeat split.
Qed.

(** Width changes preserve their intended high and low parts. *)
Example width_changes :
  eval_op (bvzext 8%positive) [(8%positive, 255)] = Some (16%positive, 255) /\
  eval_op (bvsext 8%positive) [(8%positive, 255)] = Some (16%positive, 65535) /\
  eval_op (bvtrunc 4%positive) [(8%positive, 165)] = Some (4%positive, 5) /\
  eval_op (bvextract 7 4) [(8%positive, 165)] = Some (4%positive, 10) /\
  eval_op bvconcat [(4%positive, 10); (4%positive, 5)] = Some (8%positive, 165).
Proof.
  vm_compute. repeat split.
Qed.

(** Zero extension wraps malformed integers at the source width before widening. *)
Example zext_normalization :
  eval_op (bvzext 8%positive) [(8%positive, 127)] = Some (16%positive, 127) /\
  eval_op (bvzext 8%positive) [(8%positive, -1)] = Some (16%positive, 255) /\
  eval_op (bvzext 8%positive) [(8%positive, 256)] = Some (16%positive, 0) /\
  eval_op (bvzext 8%positive) [(8%positive, 257)] = Some (16%positive, 1) /\
  eval_op (bvzext 1%positive) [(1%positive, -1)] = Some (2%positive, 1) /\
  eval_op (bvzext 1%positive) [(1%positive, 0)] = Some (2%positive, 0).
Proof.
  vm_compute. repeat split.
Qed.

(** Sign extension distinguishes the sign-bit boundary after source normalization. *)
Example sext_normalization :
  eval_op (bvsext 8%positive) [(8%positive, 127)] = Some (16%positive, 127) /\
  eval_op (bvsext 8%positive) [(8%positive, 128)] = Some (16%positive, 65408) /\
  eval_op (bvsext 8%positive) [(8%positive, -1)] = Some (16%positive, 65535) /\
  eval_op (bvsext 8%positive) [(8%positive, 256)] = Some (16%positive, 0) /\
  eval_op (bvsext 8%positive) [(8%positive, 384)] = Some (16%positive, 65408) /\
  eval_op (bvsext 1%positive) [(1%positive, 1)] = Some (2%positive, 3) /\
  eval_op (bvsext 1%positive) [(1%positive, 0)] = Some (2%positive, 0).
Proof.
  vm_compute. repeat split.
Qed.

(** Truncation accepts equal widths and width one while rejecting a wider target. *)
Example trunc_normalization :
  eval_op (bvtrunc 4%positive) [(8%positive, 165)] = Some (4%positive, 5) /\
  eval_op (bvtrunc 4%positive) [(8%positive, -1)] = Some (4%positive, 15) /\
  eval_op (bvtrunc 4%positive) [(8%positive, 256)] = Some (4%positive, 0) /\
  eval_op (bvtrunc 4%positive) [(8%positive, 271)] = Some (4%positive, 15) /\
  eval_op (bvtrunc 8%positive) [(8%positive, 257)] = Some (8%positive, 1) /\
  eval_op (bvtrunc 1%positive) [(1%positive, -1)] = Some (1%positive, 1) /\
  eval_op (bvtrunc 1%positive) [(8%positive, 2)] = Some (1%positive, 0) /\
  eval_op (bvtrunc 9%positive) [(8%positive, -1)] = None.
Proof.
  vm_compute. repeat split.
Qed.

(** Concatenation normalizes each operand at its own width and retains operand order. *)
Example concat_normalization :
  eval_op bvconcat [(4%positive, 10); (8%positive, 5)] = Some (12%positive, 2565) /\
  eval_op bvconcat [(4%positive, -1); (8%positive, -2)] = Some (12%positive, 4094) /\
  eval_op bvconcat [(4%positive, 17); (8%positive, 258)] = Some (12%positive, 258) /\
  eval_op bvconcat [(4%positive, 16); (8%positive, 256)] = Some (12%positive, 0) /\
  eval_op bvconcat [(1%positive, 1); (1%positive, 1)] = Some (2%positive, 3) /\
  eval_op bvconcat [(1%positive, 0); (1%positive, 0)] = Some (2%positive, 0).
Proof.
  vm_compute. repeat split.
Qed.

(** Resize and concatenation reject missing and surplus operands even for malformed integers. *)
Example resize_concat_bad_arities :
  eval_op (bvzext 1%positive) [] = None /\
  eval_op (bvzext 1%positive) [(1%positive, -1); (1%positive, 2)] = None /\
  eval_op (bvsext 1%positive) [] = None /\
  eval_op (bvsext 1%positive) [(1%positive, -1); (1%positive, 2)] = None /\
  eval_op (bvtrunc 1%positive) [] = None /\
  eval_op (bvtrunc 1%positive) [(1%positive, -1); (1%positive, 2)] = None /\
  eval_op bvconcat [] = None /\
  eval_op bvconcat [(1%positive, -1)] = None /\
  eval_op bvconcat [(1%positive, -1); (1%positive, 2); (1%positive, 0)] = None.
Proof.
  vm_compute. repeat split.
Qed.

(** A client resizes a symbolic concatenation using only the public value equations. *)
Example resize_concat_symbolic_client : forall extra target wa wb x y,
  (match eval_op bvconcat [(wa, x); (wb, y)] with
   | Some (w, z) =>
     (eval_op (bvzext extra) [(w, z)],
      eval_op (bvsext extra) [(w, z)],
      eval_op (bvtrunc target) [(w, z)])
   | None => (None, None, None)
   end) =
  let w := (wa + wb)%positive in
  let z := wrap w (wrap wa x * modulus wb + wrap wb y) in
  (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w z)),
   Some ((w + extra)%positive, wrap (w + extra)%positive (signed w z)),
   if Pos.leb target w then Some (target, wrap target (wrap w z)) else None).
Proof.
  intros extra target wa wb x y.
  rewrite eval_op_concat.
  rewrite eval_op_zext, eval_op_sext, eval_op_trunc.
  reflexivity.
Qed.

(** Width checking rejects bad arities, mismatches and invalid extraction bounds. *)
Example invalid_operands :
  eval_op bvnot [] = None /\ eval_op bvnot [(8%positive, 0); (8%positive, 0)] = None /\
  eval_op bvadd [(8%positive, 0); (4%positive, 0)] = None /\
  eval_op bvite [(2%positive, 1); (8%positive, 1); (8%positive, 2)] = None /\
  eval_op bvite [(1%positive, 1); (8%positive, 1); (4%positive, 2)] = None /\
  eval_op (bvtrunc 9%positive) [(8%positive, 1)] = None /\
  eval_op (bvextract 2 3) [(8%positive, 1)] = None /\
  eval_op (bvextract 8 0) [(8%positive, 1)] = None.
Proof.
  vm_compute. repeat split.
Qed.

(** Count operators distinguish zero from a word with two separated set bits. *)
Example counts :
  map (fun o => eval_op o [(8%positive, 40)]) [bvclz; bvctz; bvpopcnt] =
    [Some (8%positive, 2); Some (8%positive, 3); Some (8%positive, 2)] /\
  map (fun o => eval_op o [(8%positive, 0)]) [bvclz; bvctz; bvpopcnt] =
    [Some (8%positive, 8); Some (8%positive, 8); Some (8%positive, 0)].
Proof.
  vm_compute. repeat split.
Qed.

(** Parameterized operator encodings discriminate tags and extraction bounds. *)
Example operator_codes :
  Pos.eqb (snd (snd (op_code (bvextract 7 0)))) (snd (snd (op_code (bvextract 7 1))))
    = false /\
  Nat.eqb (fst (op_code (bvzext 4%positive)))
    (fst (op_code (bvsext 4%positive))) = false.
Proof.
  vm_compute. repeat split.
Qed.

Definition representative_ops : list op :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl;
   bvrotr; bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 3%positive;
   bvsext 3%positive; bvtrunc 2%positive; bvextract 2 1; bvconcat].

(** The constructor tags are distinct across every operator representative. *)
Example descriptor_codes_unique :
  map (fun o => fst (op_code o)) representative_ops = seq 0 33.
Proof.
  vm_compute. reflexivity.
Qed.


(** Binary width checks apply to arithmetic and shift amounts even for malformed integers. *)
Example fun2_width_boundaries :
  eval_op bvadd [(8%positive, -1); (8%positive, 257)] = Some (8%positive, 0) /\
  eval_op bvadd [(8%positive, -1); (4%positive, 257)] = None /\
  eval_op bvshl [(8%positive, 1); (8%positive, 1)] = Some (8%positive, 2) /\
  eval_op bvshl [(8%positive, 1); (1%positive, 1)] = None /\
  eval_op bvadd [(1%positive, -1); (1%positive, 3)] = Some (1%positive, 0).
Proof.
  vm_compute. repeat split.
Qed.

(** Comparisons reject unequal input widths even though their result width is one. *)
Example cmp_width_boundaries :
  eval_op bveq [(8%positive, -1); (8%positive, 255)] = Some (1%positive, 1) /\
  eval_op bveq [(8%positive, -1); (4%positive, 255)] = None /\
  eval_op bvult [(8%positive, 1); (8%positive, 2)] = Some (1%positive, 1) /\
  eval_op bvult [(8%positive, 1); (4%positive, 2)] = None /\
  eval_op bvslt [(8%positive, -1); (8%positive, 0)] = Some (1%positive, 1) /\
  eval_op bvslt [(8%positive, -1); (1%positive, 0)] = None /\
  eval_op bvult [(1%positive, 0); (1%positive, 1)] = Some (1%positive, 1).
Proof.
  vm_compute. repeat split.
Qed.

(** Selection checks both branch widths and the condition width before choosing a branch. *)
Example ite_width_boundaries :
  eval_op bvite [(1%positive, 3); (8%positive, -1); (8%positive, 257)] =
    Some (8%positive, 255) /\
  eval_op bvite [(1%positive, 2); (8%positive, -1); (8%positive, 257)] =
    Some (8%positive, 1) /\
  eval_op bvite [(1%positive, 1); (8%positive, 7); (4%positive, 7)] = None /\
  eval_op bvite [(1%positive, 0); (8%positive, 7); (4%positive, 7)] = None /\
  eval_op bvite [(2%positive, 1); (8%positive, 7); (8%positive, 7)] = None /\
  eval_op bvite [(2%positive, 0); (8%positive, 7); (8%positive, 7)] = None /\
  eval_op bvite [(2%positive, 1); (1%positive, 1); (1%positive, 0)] = None /\
  eval_op bvite [(1%positive, -1); (1%positive, 3); (1%positive, 0)] =
    Some (1%positive, 1).
Proof.
  vm_compute. repeat split.
Qed.

(** A symbolic binary client recovers its value formula after inverting operand widths. *)
Example fun2_width_symbolic_client : forall o f wa wb x y r,
  word_fun2 o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r ->
  r = (wa, eval_binary_tag f wa x y).
Proof.
  intros o f wa wb x y r Hfun Hresult.
  pose proof (eval_op_fun2_width o f wa wb x y r Hfun Hresult) as Hwidth.
  subst wb. rewrite (eval_op_fun2 o wa x y f Hfun) in Hresult.
  congruence.
Qed.

(** A symbolic comparison client recovers its boolean word after inverting operand widths. *)
Example cmp_width_symbolic_client : forall o f wa wb x y r,
  word_cmp o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r ->
  r = (1%positive, if eval_comparison_tag f wa x y then 1 else 0).
Proof.
  intros o f wa wb x y r Hfun Hresult.
  pose proof (eval_op_cmp_width o f wa wb x y r Hfun Hresult) as Hwidth.
  subst wb. rewrite (eval_op_cmp o wa x y f Hfun) in Hresult.
  congruence.
Qed.

(** A symbolic selection client recovers its value formula after inverting all width checks. *)
Example ite_width_symbolic_client : forall wc wa wb c x y r,
  eval_op bvite [(wc, c); (wa, x); (wb, y)] = Some r ->
  r = (wa, if wrap 1%positive c =? 1 then wrap wa x else wrap wa y).
Proof.
  intros wc wa wb c x y r Hresult.
  destruct (eval_op_ite_width wc wa wb c x y r Hresult) as [Hcondition Hbranches].
  subst wc wb. rewrite eval_op_ite in Hresult.
  injection Hresult as Hvalue.
  symmetry. exact Hvalue.
Qed.
