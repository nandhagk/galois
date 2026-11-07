(** * Complete operator-grid agreement

    Every operator is compared with its legacy instance on boundary and malformed operands.
    For example, the Cartesian grid includes negative and above-modulus raw values.
    Builds on: BitsOp, BitsExpr and their legacy implementations. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From GaloisLegacy.Bits Require BitsOp BitsExpr.
Import List.ListNotations.

Open Scope Z_scope.

Module Old := GaloisLegacy.Bits.BitsOp.
Module OldExpr := GaloisLegacy.Bits.BitsExpr.Bits.

Definition to_legacy (o : op) : Old.op :=
  match o with
  | bvnot => Old.bvnot
  | bvneg => Old.bvneg
  | bvclz => Old.bvclz
  | bvctz => Old.bvctz
  | bvpopcnt => Old.bvpopcnt
  | bvadd => Old.bvadd
  | bvsub => Old.bvsub
  | bvmul => Old.bvmul
  | bvudiv => Old.bvudiv
  | bvurem => Old.bvurem
  | bvsdiv => Old.bvsdiv
  | bvsrem => Old.bvsrem
  | bvsmod => Old.bvsmod
  | bvand => Old.bvand
  | bvor => Old.bvor
  | bvxor => Old.bvxor
  | bvshl => Old.bvshl
  | bvlshr => Old.bvlshr
  | bvashr => Old.bvashr
  | bvrotl => Old.bvrotl
  | bvrotr => Old.bvrotr
  | bveq => Old.bveq
  | bvne => Old.bvne
  | bvult => Old.bvult
  | bvule => Old.bvule
  | bvslt => Old.bvslt
  | bvsle => Old.bvsle
  | bvite => Old.bvite
  | bvzext n => Old.bvzext n
  | bvsext n => Old.bvsext n
  | bvtrunc t => Old.bvtrunc t
  | bvextract hi lo => Old.bvextract hi lo
  | bvconcat => Old.bvconcat
  end.

Definition operators : list op :=
  [bvnot; bvneg; bvclz; bvctz; bvpopcnt; bvadd; bvsub; bvmul; bvudiv; bvurem;
   bvsdiv; bvsrem; bvsmod; bvand; bvor; bvxor; bvshl; bvlshr; bvashr; bvrotl;
   bvrotr; bveq; bvne; bvult; bvule; bvslt; bvsle; bvite; bvzext 3%positive;
   bvsext 3%positive; bvtrunc 2%positive; bvextract 2 1; bvconcat].

Definition widths : list width := [1%positive; 2%positive; 3%positive; 8%positive].

Definition samples w : list Z :=
  [-1; 0; 1; 2; modulus w - 1; modulus w; modulus w + 1; 255; 1000].

Fixpoint tuples (n : nat) (alphabet : list word) : list (list word) :=
  match n with
  | O => [[]]
  | S n => flat_map (fun x => map (cons x) (tuples n alphabet)) alphabet
  end.

Definition operands (o : op) w : list (list word) :=
  let alphabet := map (fun z => (w, z)) (samples w) in
  tuples (arity o) alphabet ++
    if Nat.eqb (arity o) 3 then
      flat_map (fun c => map (cons (1%positive, c)) (tuples 2 alphabet)) (samples 1%positive)
    else [].

Definition mismatched (xs : list word) : list word :=
  match xs with
  | [] => []
  | (w, x) :: rest => ((w + 1)%positive, x) :: rest
  end.

Definition grid o w : list (list word) :=
  operands o w ++ map mismatched (operands o w) ++ [[]; repeat (w, 0) (S (arity o))].

Definition word_eqb (x y : word) : bool :=
  Pos.eqb (fst x) (fst y) && Z.eqb (snd x) (snd y).

Definition option_word_eqb (x y : option word) : bool :=
  match x, y with
  | Some a, Some b => word_eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition option_width_eqb (x y : option width) : bool :=
  match x, y with
  | Some a, Some b => Pos.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition code_eqb (x y : nat * (positive * positive)) : bool :=
  Nat.eqb (fst x) (fst y) &&
    Pos.eqb (fst (snd x)) (fst (snd y)) && Pos.eqb (snd (snd x)) (snd (snd y)).

Definition agrees o xs : bool :=
  option_word_eqb (eval_op o xs) (Old.eval_op (to_legacy o) xs) &&
  option_width_eqb (result_width o (map fst xs)) (Old.result_width (to_legacy o) (map fst xs)).

Definition metadata_agrees o : bool :=
  Nat.eqb (arity o) (Old.arity (to_legacy o)) &&
  Bool.eqb (commutative o) (Old.commutative (to_legacy o)) &&
  code_eqb (op_code o) (Old.op_code (to_legacy o)).

(** The grid includes one representative of each distinct legacy constructor tag. *)
Example all_operators_covered :
  length operators = 33%nat /\ map (fun o => fst (op_code o)) operators = seq 0 33.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Arity, symmetry and constructor-and-parameter codes agree for every operator. *)
Example operator_metadata_agrees : forallb metadata_agrees operators = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Evaluation and result-width checks agree on every operand list in the Cartesian grid. *)
Example operator_grid_agrees :
  forallb (fun o => forallb (fun w => forallb (agrees o) (grid o w)) widths) operators = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition parameter_cases w : list op :=
  [bvzext 1%positive; bvzext 8%positive; bvsext 1%positive; bvsext 8%positive;
   bvtrunc 1%positive; bvtrunc w; bvtrunc (w + 1)%positive;
   bvextract 0 0; bvextract (Pos.to_nat w - 1) 0;
   bvextract (Pos.to_nat w) 0; bvextract 0 1].

(** Parameter boundaries include identity truncation, widening rejection and invalid extraction. *)
Example parameter_grid_agrees :
  forallb (fun w => forallb (fun o => metadata_agrees o &&
    forallb (agrees o) (grid o w)) (parameter_cases w)) widths = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition expression_agrees o w xs : bool :=
  option_word_eqb
    (Expr.eval eval_op (Expr.env_of (1%positive, 0) xs)
      (Expr.App o (Expr.vars (arity o))))
    (OldExpr.eval (OldExpr.env_of xs)
      (OldExpr.App (to_legacy o) (OldExpr.vars (Old.arity (to_legacy o))))) &&
  option_word_eqb
    (Expr.eval eval_op (Expr.env_of (1%positive, 0) [])
      (Expr.App o [Expr.Const w (-1)]))
    (OldExpr.eval (OldExpr.env_of []) (OldExpr.App (to_legacy o) [OldExpr.Const w (-1)])).

(** Variable applications and raw constants agree across the same operator and operand grid. *)
Example expression_grid_agrees :
  forallb (fun o => forallb (fun w =>
    forallb (expression_agrees o w) (grid o w)) widths) operators = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Nested applications agree on normalized variables, selection and failed arguments. *)
Example nested_expressions_agree :
  option_word_eqb
    (Expr.eval eval_op (Expr.env_of (1%positive, 0) [(8%positive, 200); (8%positive, 100)])
      (Expr.App bvite [Expr.Const 1%positive 3;
        Expr.App bvadd [Expr.Var 0; Expr.Var 1]; Expr.Const 8%positive 17]))
    (OldExpr.eval (OldExpr.env_of [(8%positive, 200); (8%positive, 100)])
      (OldExpr.App Old.bvite [OldExpr.Const 1%positive 3;
        OldExpr.App Old.bvadd [OldExpr.Var 0; OldExpr.Var 1]; OldExpr.Const 8%positive 17])) &&
  option_word_eqb
    (Expr.eval eval_op (Expr.env_of (1%positive, 0) [])
      (Expr.App bvnot [Expr.App bvadd []]))
    (OldExpr.eval (OldExpr.env_of []) (OldExpr.App Old.bvnot [OldExpr.App Old.bvadd []]))
    = true.
Proof.
  vm_compute. reflexivity.
Qed.
