(** * Seeded restriction observations

    Restrictions retain selected row occurrences and append constant seed rows.
    For example, selecting [1; 2; 0; 1] preserves both the order and the repeated row.

    Groups:
    - [RowTests] The rows that a restriction keeps and appends, in order.
    - [OutputTests] The reads, side contributions and acceptance of the restricted rows.
    - [FootprintTests] The finite closure of a run over a footprint.

    Builds on: Incremental.Restrict and Fixpoint.Query. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Incremental Require Import Restrict.
Import List.ListNotations.

(** * Fixtures *)

(** A pair of Boolean components, ordered and joined componentwise. *)
Module PairOps <: LATTICE_OPS.
  Definition t := (bool * bool)%type.
  Definition leb (a b : t) := implb (fst a) (fst b) && implb (snd a) (snd b).
  Definition bot : t := (false, false).
  Definition is_bot (a : t) := negb (fst a) && negb (snd a).
  Definition join (a b : t) := (orb (fst a) (fst b), orb (snd a) (snd b)).
End PairOps.

(** A system with five rows, where row 2 writes its side contribution to key 0. *)
Module Direct <: LOCAL_SYSTEM_OPS PairOps.
  Definition prog := bool.
  Definition key := nat.
  Definition row := nat.
  Definition frame := unit.
  Definition key_code := Pos.of_succ_nat.
  Definition key_eqb := Nat.eqb.
  Definition rows (p : bool) := if p then [3; 1; 2; 0; 1] else [].
  Definition target (_ : bool) (r : nat) :=
    if Nat.eqb r 2 then 10 else if Nat.eqb r 3 then 20 else r.
  Definition start (_ : bool) (r : nat) : query key PairOps.t frame :=
    match r with
    | 0 => Ask 1 tt
    | 1 => Ask 0 tt
    | 2 => Side 0 (true, false) (Ret (false, false))
    | _ => Ret (true, true)
    end.
  Definition resume (_ : bool) (_ : unit) (a : PairOps.t) : query key PairOps.t frame := Ret a.
  Definition deps (_ : bool) (r : nat) :=
    match r with 0 => [1] | 1 => [0] | _ => [] end.
  Definition sides (_ : bool) (r : nat) := if Nat.eqb r 2 then [0; 42] else [].
  Definition row_code := Pos.of_succ_nat.
  Definition rows_of (p : bool) (x : nat) :=
    filter (fun r => existsb (Nat.eqb x) (target p r :: sides p r)) (rows p).
End Direct.

Module R := RestrictCode PairOps Direct.
Module RestrictedOps := R.RS.
Module View.
  Include RestrictedOps.
  Include SYSTEM_SPEC PairOps.
End View.

(** The selected row occurrences, with row 1 repeated. *)
Definition selected_rows := [1; 2; 0; 1].

(** Seed bindings for keys 42 and 99, with key 42 bound twice. *)
Definition seed_bindings : list (nat * PairOps.t) :=
  [(42, (true, false)); (42, (false, true)); (99, (true, true))].

(** The restriction of the direct system to the selected rows and the seed bindings. *)
Definition mixed := R.Code.mk true seed_bindings selected_rows.

(** * Rows *)

Module RowTests.

  (** A restriction with no selected rows and no seeds has no rows. *)
  Example empty_restriction_has_no_rows : R.RS.rows (R.Code.mk false [] []) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed alone gives one seed row, with its binding. *)
  Example seed_alone_gives_one_seed_row :
    R.RS.rows (R.Code.mk false [(42, (true, false))] []) = [inr (42, (true, false))].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Restriction keeps the selected rows in order, including the repeated row. *)
  Example restriction_keeps_order_and_duplicate_rows :
    map (fun r => match r with inl r => r | inr _ => 99 end)
      (R.RS.rows (R.Code.mk true [] selected_rows)) = [1; 2; 0; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The seed rows follow the selected rows, with the repeated seed for key 42 kept. *)
  Example restriction_appends_repeated_seeds : R.RS.rows mixed =
    [inl 1; inl 2; inl 0; inl 1;
     inr (42, (true, false)); inr (42, (false, true)); inr (99, (true, true))].
  Proof.
    vm_compute; reflexivity.
  Qed.

End RowTests.

(** * Outputs *)

Module OutputTests.

  (** The original rows keep their targets, reads and side contributions after restriction. *)
  Example original_rows_keep_outputs :
    map (fun r => (R.RS.target mixed (inl r),
      View.eval mixed (inl r) (fun _ => (true, false)))) selected_rows =
    [(1, Some ((true, false), []));
     (10, Some ((false, false), [(0, (true, false))]));
     (0, Some ((true, false), []));
     (1, Some ((true, false), []))].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Each seed row returns its bound value and has no reads. *)
  Example seed_rows_return_their_values :
    map (fun xv => View.eval mixed (inr xv) (fun _ => (false, false))) seed_bindings =
    [Some ((true, false), []); Some ((false, true), []); Some ((true, true), [])].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed row has no reads and no side contributions. *)
  Example seed_row_has_no_reads :
    R.RS.deps mixed (inr (42, (true, false))) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed row has no side contributions. *)
  Example seed_row_has_no_sides :
    R.RS.sides mixed (inr (42, (true, false))) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed row writes its own key. *)
  Example seed_row_writes_its_key :
    View.writes mixed (inr (42, (true, false))) = [42].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed row rejects a lookup whose values lie below its own value. *)
  Example seed_rejects_lookup_below_value :
    row_ok PairOps.leb (fun _ => (false, false)) 42
      (View.eval mixed (inr (42, (true, false))) (fun _ => (false, false))) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A seed row accepts a lookup whose values lie above its own value. *)
  Example seed_accepts_lookup_above_value :
    row_ok PairOps.leb (fun _ => (true, true)) 42
      (View.eval mixed (inr (42, (true, false))) (fun _ => (true, true))) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End OutputTests.

(** * Footprint *)

Module FootprintTests.

  (** The footprint run from row [1] over three rows, with every output allowed. *)
  Definition fp_example :=
    footprint_run Nat.eqb (@fst (list nat) (list nat)) (@snd (list nat) (list nat))
      (fun _ => true) [1] [([2], [3]); ([1], [2]); ([5], [6])].

  (** A row that is skipped at first is activated later and its footprint is seen. *)
  Example skipped_row_is_seen_in_order :
    footprint_seen fp_example = [3; 2; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The footprint selects the activated rows, in the order they are activated. *)
  Example activated_rows_are_selected_in_order :
    footprint_selected fp_example = [([1], [2]); ([2], [3])].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A row that is never activated stays pending. *)
  Example unactivated_row_stays_pending :
    footprint_pending fp_example = [([5], [6])].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A footprint run over a duplicated row sees each occurrence once in its list. *)
  Definition fp_duplicate :=
    footprint_run Nat.eqb (@fst (list nat) (list nat)) (@snd (list nat) (list nat))
      (fun _ => true) [1] [([1], [2]); ([1], [2])].

  (** The duplicated row's occurrences are seen as two entries. *)
  Example duplicate_occurrences_are_seen :
    footprint_seen fp_duplicate = [2; 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Both occurrences of the duplicated row are selected. *)
  Example duplicate_occurrences_are_selected :
    length (footprint_selected fp_duplicate) = 2.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A row whose output is disallowed stays pending and does not reach the seen list. *)
  Definition fp_disallowed :=
    footprint_run Nat.eqb (@fst (list nat) (list nat)) (@snd (list nat) (list nat))
      (fun x => negb (Nat.eqb x 2))
      [1] [([1], [2]); ([2], [3])].

  (** The disallowed output leaves only the first key in the seen list. *)
  Example disallowed_output_is_not_seen :
    footprint_seen fp_disallowed = [1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The row with the disallowed output stays pending. *)
  Example disallowed_output_stays_pending :
    footprint_pending fp_disallowed = [([2], [3])].
  Proof.
    vm_compute; reflexivity.
  Qed.

End FootprintTests.
