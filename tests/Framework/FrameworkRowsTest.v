(** * Arbitrary prepared-row clients

    Row reflection retains arbitrary charged readers and ordered read lists.
    For example, the contract accepts an empty row inventory without inspecting the reader.
    Builds on: FrameworkRows and FixpointSystem. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Framework Require Import FrameworkRows.
Import List.ListNotations.

(** An importing client obtains row reflection for an entirely arbitrary costed reader. *)
Example arbitrary_reader_reflection {X C A} (L : lattice A) cs
    (get_c : C -> Cost.t (Rows.t X A)) sigma :
  post_solution L (Rows.system cs get_c) sigma <->
    forall c, In c cs ->
      leb L
        (Cost.value (Rows.eval_c (Cost.value (get_c c))
          (map sigma (Rows.reads (Cost.value (get_c c))))))
        (sigma (Rows.target (Cost.value (get_c c)))) = true.
Proof.
  apply Rows.post_solution_iff.
Qed.

(** An empty inventory imposes no obligations on any reader or assignment. *)
Example empty_rows {X C A} (L : lattice A) (get_c : C -> Cost.t (Rows.t X A)) sigma :
  post_solution L (Rows.system [] get_c) sigma.
Proof.
  apply Rows.post_solution_iff; intros c Hin; inversion Hin.
Qed.

Definition two_reads : Rows.t bool bool :=
  Rows.Make true [true; false] (fun values =>
    Cost.ret (match values with x :: y :: _ => andb x (negb y) | _ => false end)).

Example ordered_row_accepts :
  post_solution bool_lattice (Rows.system [tt] (fun _ => Cost.ret two_reads))
    negb.
Proof.
  apply Rows.post_solution_iff; intros [] Hin; vm_compute; reflexivity.
Qed.

Definition reversed_reads : Rows.t bool bool :=
  Rows.Make true [false; true] (Rows.eval_c two_reads).

Example reversed_row_rejects :
  ~ post_solution bool_lattice (Rows.system [tt] (fun _ => Cost.ret reversed_reads)) negb.
Proof.
  intro Hpost.
  pose proof (proj1 (Rows.post_solution_iff bool_lattice [tt]
    (fun _ => Cost.ret reversed_reads) negb) Hpost) as Hrows.
  specialize (Hrows tt (or_introl eq_refl)); discriminate Hrows.
Qed.

Definition constant_row : Rows.t bool bool :=
  Rows.Make false [] (fun _ => Cost.ret true).

Example constant_row_rejects_bottom :
  ~ post_solution bool_lattice (Rows.system [tt] (fun _ => Cost.ret constant_row))
    (fun _ => false).
Proof.
  intro Hpost.
  pose proof (proj1 (Rows.post_solution_iff bool_lattice [tt]
    (fun _ => Cost.ret constant_row) (fun _ => false)) Hpost) as Hrows.
  specialize (Hrows tt (or_introl eq_refl)); discriminate Hrows.
Qed.
