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

(** Signed division and residues cover every sign pair, wrapped zero divisors and overflow. *)
Example signed_division_value_boundaries :
  wsdiv 8%positive 7 3 = 2 /\ wsdiv 8%positive (-7) 3 = 254 /\
  wsdiv 8%positive 7 (-3) = 254 /\ wsdiv 8%positive (-7) (-3) = 2 /\
  wsdiv 8%positive 128 (-1) = 128 /\
  wsdiv 8%positive 263 256 = 255 /\ wsdiv 8%positive (-7) 256 = 1 /\
  wsrem 8%positive 7 3 = 1 /\ wsrem 8%positive (-7) 3 = 255 /\
  wsrem 8%positive 7 (-3) = 1 /\ wsrem 8%positive (-7) (-3) = 255 /\
  wsrem 8%positive 128 (-1) = 0 /\ wsrem 8%positive (-7) 256 = 249 /\
  wsmod 8%positive 7 3 = 1 /\ wsmod 8%positive (-7) 3 = 2 /\
  wsmod 8%positive 7 (-3) = 254 /\ wsmod 8%positive (-7) (-3) = 255 /\
  wsmod 8%positive (-6) 3 = 0 /\ wsmod 8%positive 128 (-1) = 0 /\
  wsmod 8%positive 263 256 = 7 /\ wsmod 8%positive (-7) 256 = 249 /\
  wsdiv 1%positive 1 1 = 1 /\ wsrem 1%positive 1 1 = 0 /\
  wsmod 1%positive 1 1 = 0.
Proof.
  vm_compute. repeat split.
Qed.

(** Shifts test normalized amounts at zero, below the width, at the width and beyond it. *)
Example shift_value_boundaries :
  wshl 8%positive 129 0 = 129 /\ wshl 8%positive 129 7 = 128 /\
  wshl 8%positive 129 8 = 0 /\ wshl 8%positive (-1) (-1) = 0 /\
  wshl 8%positive 257 256 = 1 /\ wshl 8%positive 257 257 = 2 /\
  wlshr 8%positive 129 0 = 129 /\ wlshr 8%positive 129 7 = 1 /\
  wlshr 8%positive 129 8 = 0 /\ wlshr 8%positive (-1) (-1) = 0 /\
  wlshr 8%positive 257 256 = 1 /\ wlshr 8%positive 258 257 = 1 /\
  washr 8%positive (-127) 0 = 129 /\ washr 8%positive (-127) 7 = 255 /\
  washr 8%positive (-127) 8 = 255 /\ washr 8%positive 127 8 = 0 /\
  washr 8%positive (-1) (-1) = 255 /\ washr 8%positive 127 (-1) = 0 /\
  washr 8%positive 384 256 = 128 /\ washr 8%positive 384 257 = 192 /\
  wshl 1%positive 1 1 = 0 /\ wlshr 1%positive 1 1 = 0 /\
  washr 1%positive 1 1 = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** Comparisons distinguish signed order, equality and source-width normalization. *)
Example comparison_value_boundaries :
  wult 8%positive 1 2 = true /\ wult 8%positive (-1) 0 = false /\
  wult 8%positive 256 257 = true /\ wult 8%positive 255 (-1) = false /\
  wule 8%positive 1 2 = true /\ wule 8%positive (-1) 0 = false /\
  wule 8%positive 255 (-1) = true /\ wule 8%positive 256 0 = true /\
  wslt 8%positive (-1) 0 = true /\ wslt 8%positive 127 128 = false /\
  wslt 8%positive 384 127 = true /\ wslt 8%positive 255 (-1) = false /\
  wsle 8%positive (-1) 0 = true /\ wsle 8%positive 127 128 = false /\
  wsle 8%positive 255 (-1) = true /\ wsle 8%positive 256 0 = true /\
  wult 1%positive 0 1 = true /\ wule 1%positive 1 1 = true /\
  wslt 1%positive 1 0 = true /\ wsle 1%positive 1 1 = true.
Proof.
  vm_compute. repeat split.
Qed.

(** A symbolic client selects the negative-input division and remainder branches publicly. *)
Example signed_division_value_symbolic_client : forall w x y,
  msb w x = true -> msb w y = true ->
  (wsdiv w x y, wsrem w x y) =
    (wudiv w (wneg w x) (wneg w y), wneg w (wurem w (wneg w x) (wneg w y))).
Proof.
  intros w x y Hx Hy.
  rewrite wsdiv_value, wsrem_value, Hx, Hy.
  reflexivity.
Qed.

(** A symbolic client keeps the zero-residue modulus branch for negative inputs. *)
Example signed_modulus_value_symbolic_client : forall w x y,
  msb w x = true -> msb w y = true ->
  wurem w (wneg w x) (wneg w y) = 0 -> wsmod w x y = 0.
Proof.
  intros w x y Hx Hy Hrem.
  rewrite wsmod_value, Hx, Hy.
  cbn beta iota zeta.
  rewrite Hrem.
  reflexivity.
Qed.

(** A symbolic client handles large wrapped shifts without unfolding the shift functions. *)
Example shift_value_symbolic_client : forall w x y,
  (Zpos w <=? wrap w y) = true ->
  (wshl w x y, wlshr w x y, washr w x y) =
    (0, 0, if msb w x then modulus w - 1 else 0).
Proof.
  intros w x y Hlarge.
  rewrite wshl_value, wlshr_value, washr_value, Hlarge.
  reflexivity.
Qed.

(** A symbolic client exposes signed and unsigned comparisons through their value equations. *)
Example comparison_value_symbolic_client : forall w x y,
  (wult w x y, wule w x y, wslt w x y, wsle w x y) =
    (wrap w x <? wrap w y, wrap w x <=? wrap w y,
     signed w x <? signed w y, signed w x <=? signed w y).
Proof.
  intros w x y.
  rewrite wult_value, wule_value, wslt_value, wsle_value.
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
