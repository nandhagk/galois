(** * Word bridge and guard fixtures

    Guards exercise complete, mixed-width and partial concrete languages.
    For example, mixed widths enable truth while leaving disequality capability disabled.
    Builds on: DomainsPoint, DomainsTagged and DomainsBitsValue. *)

From Stdlib Require Import List ZArith Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Domains Require Import DomainsValue DomainsNumeric DomainsTagged DomainsPoint
  DomainsBitsValue.
Import List.ListNotations Expr.

Definition point_numeric := tagged_domain point_word_domain.
Definition point_meaning := tagged_gamma point_gamma.

Definition word_bridge : op_bridge expr word :=
  {| op_expr_c := fun e => Cost.ret (Some e);
     to_word_c := fun c => Cost.ret (Some (fst c, wrap (fst c) (snd c)));
     truth_words := true;
     differ_words_c := fun _ => Cost.ret false |}.

Definition word_values := bits_values point_numeric word_bridge TAny.
Definition p (w z : Z) : tagged point := TVal (Z.to_pos w) (PVal z).
Definition run_guard g xs := ValueAbs.guard word_values g xs.

Definition bool_bridge : op_bridge unit bool :=
  {| op_expr_c := fun _ => Cost.ret None;
     to_word_c := fun b : bool => Cost.ret (Some (1%positive, if b then 1%Z else 0%Z));
     truth_words := true;
     differ_words_c := fun _ => Cost.ret true |}.

Definition bool_values := bits_values point_numeric bool_bridge TAny.

Definition partial_bridge : op_bridge unit (option word) :=
  {| op_expr_c := fun _ => Cost.ret None;
     to_word_c := fun c =>
       Cost.ret
         (match c with
          | Some (w, z) => Some (w, wrap w z)
          | None => None
          end);
     truth_words := false;
     differ_words_c := fun _ => Cost.ret false |}.

Example numeric_instance_laws : numeric_laws point_numeric point_meaning.
Proof. exact (tagged_numeric_laws point_word_domain point_gamma point_word_laws). Qed.

(** The fixed-width Boolean bridge inhabits every enabled guard capability. *)
Theorem bool_bridge_laws :
  op_bridge_laws bool_bridge (fun _ _ => None) (fun b => b).
Proof.
  constructor.
  - intros [] w Hw; inversion Hw; [apply one_is_word|apply zero_is_word].
  - intros k cs c e He. discriminate He.
  - intros [] w Hw; inversion Hw; reflexivity.
  - intros H []. all: eexists; reflexivity.
  - intros d H []. all: eexists; reflexivity.
  - intros [] [] wc wd Hcap Hc Hd; inversion Hc; inversion Hd; reflexivity.
  - intros [] [] w Hcap Hc Hd; vm_compute in Hc, Hd; congruence.
Qed.

(** The point-based open Boolean dictionary has proved value laws. *)
Theorem bool_value_laws :
  value_laws bool_values (bits_sem bool_bridge (fun _ _ => None) (fun b => b))
    (numeric_conc point_numeric point_meaning bool_bridge).
Proof.
  apply bits_values_laws.
  - exact numeric_instance_laws.
  - exact bool_bridge_laws.
  - intros. exact I.
  - reflexivity.
Qed.

Example bridge_arithmetic :
  ValueAbs.op word_values (App bvadd [Var 0; Var 1]) [p 32 1; p 32 1] = p 32 2.
Proof. vm_compute. reflexivity. Qed.

Example truth_positive : run_guard (Truth true) [p 32 7] = [p 32 7].
Proof. vm_compute. reflexivity. Qed.

Example truth_rejected : run_guard (Truth true) [p 32 0] = [TBot].
Proof. vm_compute. reflexivity. Qed.

Example truth_boundary : run_guard (Truth false) [p 1 0] = [p 1 0].
Proof. vm_compute. reflexivity. Qed.

Example truth_unknown_width : run_guard (Truth true) [TAny] = [TAny].
Proof. vm_compute. reflexivity. Qed.

Example false_unknown_width : run_guard (Truth false) [TAny] = [TAny].
Proof. vm_compute. reflexivity. Qed.

Example equal_positive : run_guard (Equal (32%positive, 7%Z)) [p 32 7] = [p 32 7].
Proof. vm_compute. reflexivity. Qed.

Example equal_rejected : run_guard (Equal (32%positive, 7%Z)) [p 32 6] = [TBot].
Proof. vm_compute. reflexivity. Qed.

Example equal_boundary : run_guard (Equal (1%positive, 1%Z)) [TAny] = [p 1 1].
Proof. vm_compute. reflexivity. Qed.

Example differ_positive : ValueAbs.guard bool_values (Differ false) [p 1 1] = [p 1 1].
Proof. vm_compute. reflexivity. Qed.

Example differ_rejected : ValueAbs.guard bool_values (Differ true) [p 1 1] = [TBot].
Proof. vm_compute. reflexivity. Qed.

Example differ_boundary : ValueAbs.guard bool_values (Differ true) [p 1 0] = [p 1 0].
Proof. vm_compute. reflexivity. Qed.

Example differ_mixed_width_fallback :
  run_guard (Differ (32%positive, 7%Z)) [p 1 1] = [p 1 1].
Proof. vm_compute. reflexivity. Qed.

Example partial_truth_fallback :
  ValueAbs.guard (bits_values point_numeric partial_bridge TAny) (Truth true) [p 32 0] =
    [p 32 0].
Proof. vm_compute. reflexivity. Qed.

Example partial_differ_fallback :
  ValueAbs.guard (bits_values point_numeric partial_bridge TAny) (Differ None) [TAny] = [TAny].
Proof. vm_compute. reflexivity. Qed.

Example test_positive :
  run_guard (Test (App bvadd [Var 0; Var 1]) true) [p 32 1; p 32 1] =
    [p 32 1; p 32 1].
Proof. vm_compute. reflexivity. Qed.

Example test_rejected :
  run_guard (Test (App bvadd [Var 0; Var 1]) false) [p 32 1; p 32 1] = [TBot; TBot].
Proof. vm_compute. reflexivity. Qed.

Example test_boundary :
  run_guard (Test (App (bvtrunc 1%positive) [Var 0]) false) [p 32 2] = [p 32 2].
Proof. vm_compute. reflexivity. Qed.

Example comparison_truth :
  run_guard (Test (App bvult [Var 0; Var 1]) true) [p 32 1; p 32 2] =
    [p 32 1; p 32 2].
Proof. vm_compute. reflexivity. Qed.

Example malformed_expression_bottom :
  ValueAbs.op word_values (App bvadd [Var 0]) [p 32 1] = TBot.
Proof. vm_compute. reflexivity. Qed.

Example empty_guard_support : run_guard (Test (Const 1%positive 1) true) [] = [].
Proof. vm_compute. reflexivity. Qed.

Example malformed_guard_arity :
  run_guard (Truth true) [p 1 0; p 32 0] = [p 1 0; p 32 0].
Proof. vm_compute. reflexivity. Qed.

Example point_empty_operand :
  pforward point_word_domain bvadd [(1%positive, PBot)] 1%positive = PBot.
Proof. vm_compute. reflexivity. Qed.

Example point_wrap_boundary : pconst point_word_domain 1%positive 2 = PVal 0.
Proof. vm_compute. reflexivity. Qed.

Definition expensive_bool_bridge : op_bridge unit bool :=
  {| op_expr_c := fun _ => Cost.bind (Cost.tick 11) (fun _ => Cost.ret None);
     to_word_c := fun b : bool =>
       Cost.bind (Cost.tick 13)
         (fun _ => Cost.ret (Some (1%positive, if b then 1%Z else 0%Z)));
     truth_words := true;
     differ_words_c := fun _ => Cost.bind (Cost.tick 17) (fun _ => Cost.ret true) |}.

(** Adding callback charges leaves every Boolean bridge capability law unchanged. *)
Theorem expensive_bool_bridge_laws :
  op_bridge_laws expensive_bool_bridge (fun _ _ => None) (fun b => b).
Proof.
  constructor.
  - exact (bridge_word bool_bridge_laws).
  - exact (bridge_eq bool_bridge_laws).
  - exact (bridge_truth bool_bridge_laws).
  - exact (truth_total bool_bridge_laws).
  - exact (differ_total bool_bridge_laws).
  - exact (differ_width bool_bridge_laws).
  - exact (differ_injective bool_bridge_laws).
Qed.

Definition expensive_bool_values := bits_values point_numeric expensive_bool_bridge TAny.

Example expensive_capability_and_conversion_keep_values :
  ValueAbs.guard expensive_bool_values (Differ false) [p 1 1] =
  ValueAbs.guard bool_values (Differ false) [p 1 1].
Proof. vm_compute. reflexivity. Qed.

Example capability_and_conversion_ticks_are_retained :
  Cost.ticks (ValueAbs.guard_c expensive_bool_values (Differ false) [p 1 1]) =
    (Cost.ticks (ValueAbs.guard_c bool_values (Differ false) [p 1 1]) + 30)%N.
Proof. vm_compute. reflexivity. Qed.

Example conversion_ticks_are_retained_for_equality :
  Cost.ticks (ValueAbs.guard_c expensive_bool_values (Equal true) [p 1 1]) =
    (Cost.ticks (ValueAbs.guard_c bool_values (Equal true) [p 1 1]) + 13)%N.
Proof. vm_compute. reflexivity. Qed.

Example expression_lookup_ticks_are_retained :
  Cost.ticks (ValueAbs.op_c expensive_bool_values tt []) =
    (Cost.ticks (ValueAbs.op_c bool_values tt []) + 11)%N.
Proof. vm_compute. reflexivity. Qed.
