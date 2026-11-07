(** * Transfer dispatch fixtures

    Two entries exercise arity selection independently of concrete points.
    For example, a missing entry gives top after point collection fails.
    Builds on: DomainsTransfer. *)

From Stdlib Require Import List Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Domains Require Import DomainsTransfer.
Import List.ListNotations.

Definition dispatch_table :
    Transfer.table (option (option nat)) (option nat) nat unit :=
  {| Transfer.fwd := fun k n =>
       Cost.ret
         (if Nat.eqb k 1 then Some (fun _ _ => Cost.ret (Some (10 + n))) else
          if Nat.eqb k 2 then Some (fun _ _ => Cost.ret (Some (20 + n))) else None);
     Transfer.bwd := fun _ _ => Cost.ret None |}.

Definition dispatch_shape :
    Transfer.shape (option (option nat)) (option nat) nat unit nat :=
  {| Transfer.eval_c := fun k xs =>
       Cost.ret (if Nat.eqb k 0 then None else Some (fold_right Nat.add 0 xs));
     Transfer.point_c := fun a => Cost.ret (match a with Some p => p | None => None end);
     Transfer.is_empty_c := fun a => Cost.ret (match a with None => true | _ => false end);
     Transfer.inj_c := fun _ n => Cost.ret (Some n);
     Transfer.bot_out := fun _ => Some 0;
     Transfer.top_out := fun _ => None;
     Transfer.keep_c := fun a => Cost.ret (match a with Some p => p | None => Some 0 end) |}.

Definition dispatch k xs := Transfer.forward dispatch_table dispatch_shape k tt xs.

Example empty_operand : dispatch 1 [None; Some None] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example all_points : dispatch 1 [Some (Some 2); Some (Some 3)] = Some 5.
Proof. vm_compute. reflexivity. Qed.

Example failed_concrete : dispatch 0 [Some (Some 2)] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example missing_entry : dispatch 3 [Some None] = None.
Proof. vm_compute. reflexivity. Qed.

Example arity_one : dispatch 1 [Some None] = Some 11.
Proof. vm_compute. reflexivity. Qed.

Example arity_two : dispatch 1 [Some None; Some None] = Some 12.
Proof. vm_compute. reflexivity. Qed.

Example arity_three : dispatch 2 [Some None; Some None; Some None] = Some 23.
Proof. vm_compute. reflexivity. Qed.

Example variadic_arity : dispatch 2 [Some None; Some None; Some None; Some None] = Some 24.
Proof. vm_compute. reflexivity. Qed.

Example zero_arity_point_path : dispatch 2 [] = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example default_backward :
  Transfer.backward dispatch_table dispatch_shape 1 tt None [Some (Some 2); Some None] =
    [Some 2; None].
Proof. vm_compute. reflexivity. Qed.

Example short_circuit_ticks :
  Cost.ticks (Transfer.forward_c dispatch_table dispatch_shape 1 tt [None; Some None]) = 2%N.
Proof. vm_compute. reflexivity. Qed.
