(** * Memo cost fixtures

    Computed charges distinguish callback misses, cached hits and empty traversals.
    For example, the second lookup of key two avoids a hundred-tick callback.
    Builds on: BaseMemoCost. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo BaseMemoCost.
Import List.ListNotations.

Definition charged_successor := Cost.lift (fun _ => 100%N) S.

Example memo_miss_hit_counts :
  (Cost.ticks (Memo.get_or_c nat_encoding charged_successor 2 Memo.empty),
    Cost.ticks (Memo.get_or_c nat_encoding charged_successor 2
      (snd (Memo.get_or nat_encoding S 2 Memo.empty)))) = (109, 4)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_second_is_cheaper :
  (Cost.ticks (Memo.get_or_c nat_encoding charged_successor 2%nat
      (snd (Memo.get_or nat_encoding S 2%nat Memo.empty))) <
    Cost.ticks (Memo.get_or_c nat_encoding charged_successor 2%nat Memo.empty))%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_empty_ticks :
  Cost.ticks (Memo.map_memo_c nat_encoding charged_successor [] Memo.empty) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_new_key_ticks :
  Cost.ticks (Memo.get_or_c nat_encoding charged_successor 3
    (snd (Memo.get_or nat_encoding S 2 Memo.empty))) = 111%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_numeric_bound_client {K V} (E : encoding K) (f_c : K -> Cost.t V)
    xs (m : Memo.t K V) e b c :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N /\
    (Cost.ticks (f_c k) <= c)%N) ->
  (Cost.ticks (Memo.map_memo_c E f_c xs m) <=
    N.of_nat (length xs) * (4 + 2 * (e + b) + c))%N.
Proof.
  apply (MemoCost.map_memo_numeric_cost Map.cost_laws_hold).
Qed.
