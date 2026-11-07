(** * Word operation examples

    These computations cover division, shifts and population counts at boundaries.
    For example, division by zero yields the all-ones word.
    Builds on: BitsFun. *)

From Stdlib Require Import ZArith.
From Galois.Bits Require Import BitsWord BitsFun.

Open Scope Z_scope.

(** Arithmetic handles ordinary inputs, overflow, negative integers and above-modulus inputs. *)
Example arithmetic_value_boundaries :
  wadd 8%positive 2 3 = 5 /\ wadd 8%positive 255 1 = 0 /\
  wadd 8%positive (-1) 258 = 1 /\
  wsub 8%positive 5 3 = 2 /\ wsub 8%positive 0 1 = 255 /\
  wsub 8%positive (-1) 258 = 253 /\
  wmul 8%positive 2 3 = 6 /\ wmul 8%positive 128 2 = 0 /\
  wmul 8%positive (-1) 258 = 254 /\
  wneg 8%positive 1 = 255 /\ wneg 8%positive 128 = 128 /\
  wneg 8%positive (-257) = 1 /\ wneg 8%positive 256 = 0 /\
  wadd 1%positive 1 1 = 0 /\ wsub 1%positive 0 1 = 1 /\
  wmul 1%positive 1 1 = 1 /\ wneg 1%positive 1 = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** A symbolic arithmetic client uses the primitive value equations without unfolding. *)
Example arithmetic_value_symbolic_client : forall w x y,
  wadd w (wsub w x y) (wmul w (wneg w x) y) =
    wrap w (wrap w (x - y) + wrap w (wrap w (- x) * y)).
Proof.
  intros w x y.
  rewrite wadd_value, wsub_value, wmul_value, wneg_value.
  reflexivity.
Qed.

Example operation_boundaries :
  wudiv 8%positive 7 0 = 255 /\
  wsdiv 8%positive 249 0 = 1 /\
  wshl 8%positive 129 8 = 0 /\
  washr 8%positive 129 8 = 255 /\
  wpopcnt 1%positive 1 = 1 /\
  wpopcnt 8%positive 257 = 1 /\
  wpopcnt 64%positive (2 ^ 64 - 1) = 64.
Proof.
  vm_compute. repeat split.
Qed.

(** Width one retains both signed values and the count of the zero word. *)
Example width_one :
  wnot 1%positive 1 = 0 /\ wneg 1%positive 1 = 1 /\
  signed 1%positive 1 = -1 /\
  wclz 1%positive 0 = 1 /\ wctz 1%positive 1 = 0 /\ wpopcnt 1%positive 1 = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** Population count distinguishes zero, negative wrapping and above-modulus values. *)
Example popcount_boundaries :
  wpopcnt 1%positive 0 = 0 /\ wpopcnt 1%positive 2 = 0 /\
  wpopcnt 8%positive (-1) = 8 /\ popcount (-1) = 0 /\ popcount 0 = 0 /\
  wpopcnt 64%positive (2 ^ 64) = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** The digit traversal charges leading zeros no recursion steps. *)
Example popcount_recursion_steps :
  popcount_steps_pos 1%positive = 1%nat /\
  popcount_steps_pos 255%positive = 8%nat /\
  popcount_steps_pos 256%positive = 9%nat.
Proof.
  vm_compute. repeat split.
Qed.
