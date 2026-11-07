(** * Certification of arbitrary solvers

    The wrapper validates every candidate returned by an untrusted computational solver.
    For example, a solver that returns bottom for a positive constant is rejected.
    Builds on: FixpointSolver, FixpointCheck and BaseCertify. *)

From Stdlib Require Import Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseCertify.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis FixpointSolver FixpointCheck.
Import Cost.Notations.

(** Certification consumes an already charged check and uses its reflected boolean once. *)
Definition certify_checked_c {W} (P : W -> Prop) (check_c : W -> Cost.t bool)
    (sound : forall w, Cost.value (check_c w) = true -> P w) w
    : Cost.t (option {w | P w}) :=
  Cost.step ;;
  let* checked := Cost.refine (check_c w)
    (P := fun b => Cost.value (check_c w) = b) eq_refl in
  Cost.ret
    (match certify (fun _ : unit => P w) (fun _ => proj1_sig checked)
      (fun _ H => sound w (eq_trans (proj2_sig checked) H)) tt with
    | None => None
    | Some proof => Some (exist P w (proj2_sig proof))
    end).

(** Certification charges one checker invocation tick and retains the entire callee charge. *)
Theorem certify_checked_cost {W} (P : W -> Prop) check_c sound w :
  Cost.ticks (certify_checked_c P check_c sound w) =
    (1 + Cost.ticks (check_c w))%N.
Proof.
  unfold certify_checked_c; autorewrite with galois_cost; lia.
Qed.

(** Successful certification retains its original candidate exactly. *)
Theorem certify_checked_spec {W} (P : W -> Prop) check_c sound w :
  (exists r, Cost.value (certify_checked_c P check_c sound w) = Some r /\
    proj1_sig r = w) <-> Cost.value (check_c w) = true.
Proof.
  unfold certify_checked_c; autorewrite with galois_cost.
  cbn [proj1_sig proj2_sig].
  rewrite certify_equation.
  destruct (bool_dec (Cost.value (check_c w)) true) as [Hcheck|Hcheck].
  - split; [intros _; exact Hcheck|].
    intros _; eexists; split; reflexivity.
  - split; [intros [r [H _]]; discriminate|contradiction].
Qed.

(** Map candidate checking retains every underlying map lookup charge. *)
Theorem map_check_sound {X C A} (a : Analysis.t X C A) m :
  Cost.value (check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) m)) = true ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  rewrite (check_post_c_spec _ _ _ (lookup (Analysis.key_enc a) (Analysis.lat a) m))
    by reflexivity.
  apply check_post_sound.
Qed.

Definition candidate_c {X C A} (a : Analysis.t X C A) (m : assignment X A) :=
  Cost.map
    (option_map (fun r => exist (post_solution (Analysis.lat a) (Analysis.system a))
      (lookup (Analysis.key_enc a) (Analysis.lat a) (proj1_sig r)) (proj2_sig r)))
    (certify_checked_c
      (fun n => post_solution (Analysis.lat a) (Analysis.system a)
        (lookup (Analysis.key_enc a) (Analysis.lat a) n))
      (fun n => check_post_c (Analysis.lat a) (Analysis.system a)
        (lookup_c (Analysis.key_enc a) (Analysis.lat a) n))
      (map_check_sound a) m).

(** Candidate certification adds exactly its checker invocation tick to full-check work. *)
Theorem candidate_cost {X C A} (a : Analysis.t X C A) m :
  Cost.ticks (candidate_c a m) =
    (1 + Cost.ticks (check_post_c (Analysis.lat a) (Analysis.system a)
      (lookup_c (Analysis.key_enc a) (Analysis.lat a) m)))%N.
Proof.
  unfold candidate_c; rewrite Cost.ticks_map, certify_checked_cost; reflexivity.
Qed.

(** Arbitrary candidates are checked independently of solver law evidence. *)
Definition analyze_with_c {X C A} (sv : Solver.t X C A) (a : Analysis.t X C A) fuel
    : Cost.t (Outcome.t X A
      {s : X -> A | post_solution (Analysis.lat a) (Analysis.system a) s}) :=
  Cost.step ;;
  let* result := Solver.run_c sv a fuel in
  match result with
  | Outcome.OutOfFuel m => Cost.ret (Outcome.OutOfFuel m)
  | Outcome.Rejected why => Cost.ret (Outcome.Rejected why)
  | Outcome.Solved m =>
    let* checked := candidate_c a m in
    Cost.ret (match checked with
      | Some s => Outcome.Solved s
      | None => Outcome.Rejected Reason.Check_failed
      end)
  end.

Definition analyze_with {X C A} (sv : Solver.t X C A) (a : Analysis.t X C A) fuel :=
  Cost.value (analyze_with_c sv a fuel).

(** Every certified result is a post-solution even when the producer is unlawful. *)
Theorem analyze_with_sound {X C A} (sv : Solver.t X C A) (a : Analysis.t X C A) fuel s :
  analyze_with sv a fuel = Outcome.Solved s ->
  post_solution (Analysis.lat a) (Analysis.system a) (proj1_sig s).
Proof.
  intro H; exact (proj2_sig s).
Qed.

(** A solved certified result comes from a candidate with the same lookup function. *)
Theorem analyze_with_candidate {X C A} (sv : Solver.t X C A)
    (a : Analysis.t X C A) fuel s :
  analyze_with sv a fuel = Outcome.Solved s ->
  exists m, Solver.run sv a fuel = Outcome.Solved m /\
    proj1_sig s = lookup (Analysis.key_enc a) (Analysis.lat a) m.
Proof.
  unfold analyze_with, analyze_with_c; autorewrite with galois_cost.
  fold (Solver.run sv a fuel).
  destruct (Solver.run sv a fuel) as [m|m|why] eqn:Hrun;
    [|discriminate|discriminate].
  unfold candidate_c, certify_checked_c; autorewrite with galois_cost.
  cbn [proj1_sig proj2_sig].
  rewrite certify_equation; destruct (bool_dec _ true) as [Hcheck|Hcheck]; [|discriminate].
  intro H; injection H as <-; exists m; split; reflexivity.
Qed.

(** A sound producer's solved candidate passes certification. *)
Theorem analyze_with_accepts {X C A} (sv : Solver.t X C A)
    (a : Analysis.t X C A) fuel m :
  Solver.run sv a fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m) ->
  exists s, analyze_with sv a fuel = Outcome.Solved s.
Proof.
  intros Hrun Hpost; unfold analyze_with, analyze_with_c; autorewrite with galois_cost.
  fold (Solver.run sv a fuel); rewrite Hrun.
  assert (Haccepted : Cost.value (check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) m)) = true).
  { rewrite (check_post_c_spec _ _ _ (lookup (Analysis.key_enc a) (Analysis.lat a) m))
      by reflexivity.
    apply check_post_iff, Hpost. }
  rewrite Cost.value_bind; unfold candidate_c, certify_checked_c.
  autorewrite with galois_cost; cbn [proj1_sig proj2_sig].
  rewrite certify_equation; destruct (bool_dec _ true) as [Hcheck|Hcheck]; [|contradiction].
  cbn [option_map]; eexists; reflexivity.
Qed.
