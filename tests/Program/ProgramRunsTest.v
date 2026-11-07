(** * Histories over a counter

    A counter links its unique transition to a unique graph edge.
    For example, the empty history retains its initial state.
    Builds on: ProgramRuns. *)

From Stdlib Require Import List Arith.
From Galois.Program Require Import ProgramSemantics ProgramLink ProgramRuns.
Import List.ListNotations.

Definition counter : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s l t => l = [] /\ t = S s).

Definition link : Link.t nat unit nat nat :=
  Link.Make (fun s => s) (fun s _ _ e => e = s) (fun _ _ _ => False).

Example one_edge : run_edges counter link 0 [0] 1.
Proof.
  eapply run_take with (l := []).
  - vm_compute; split; reflexivity.
  - reflexivity.
  - constructor.
Qed.

Example two_edges : run_edges counter link 0 [0; 1] 2.
Proof.
  eapply run_edges_app with (u := 1) (es1 := [0]) (es2 := [1]).
  - exact one_edge.
  - eapply run_take with (l := []); [split; reflexivity|reflexivity|constructor].
Qed.

Example wrong_edge_rejected : ~ Link.taken link 0 [] 1 1.
Proof.
  vm_compute; discriminate.
Qed.

Example empty_history : run_edges counter link 0 [] 0.
Proof.
  constructor.
Qed.

Example history_has_run : exists tr, exec counter 0 tr 2.
Proof.
  eapply run_edges_exec; exact two_edges.
Qed.
