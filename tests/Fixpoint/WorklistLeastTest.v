(** * Concrete worklist leastness clients

    A repeated-row Boolean system checks the leastness certificate and concrete solver results.
    For example, repeated side contributions stay below every accepting post-solution.
    Builds on: WorklistLeast, Worklist, Policy and Heap. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Argent Require Import Loop.
From Galois.Base Require Import MapSig Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Worklist
  WorklistLeast.

Import List.ListNotations.

Module LeastBool <: WLATTICE.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow := andb.
  Definition wrank (_ : unit) (_ : bool) := 0%nat.

  (** Boolean implication is reflexive. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros []; reflexivity.
  Qed.

  (** Boolean implication is transitive. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** False is below both Boolean values. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros []; reflexivity.
  Qed.

  (** The bottom test recognizes false. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.

  (** A recognized bottom is below every Boolean value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [] []; cbn; congruence.
  Qed.

  (** Disjunction includes the left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.

  (** Disjunction includes the right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.

  (** Boolean widening includes the previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros [] [] []; reflexivity.
  Qed.

  (** Boolean widening includes the new value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros [] [] []; reflexivity.
  Qed.

  (** A covered contribution leaves the Boolean value unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** There is no strict widening step from the only nonbottom value. *)
  Lemma wrank_widen : forall p a b,
    is_bot a = false -> leb b a = false -> wrank p (widen p a b) < wrank p a.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.

  (** The constant widening rank cannot increase. *)
  Lemma wrank_widen_le : forall p a b,
    is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros [] [] []; cbn; lia.
  Qed.

  (** Conjunction lies between an ordered pair. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [] []; cbn; intuition congruence.
  Qed.
End LeastBool.

Module LeastBoolLub <: LUB LeastBool.
  (** Boolean disjunction is below every common upper bound. *)
  Lemma join_least : forall a b c,
    LeastBool.leb a c = true -> LeastBool.leb b c = true ->
    LeastBool.leb (LeastBool.join a b) c = true.
  Proof.
    intros [] [] []; cbn; congruence.
  Qed.
End LeastBoolLub.

Module RepeatedSides <: SYSTEM LeastBool.
  Definition prog := bool.
  Definition key := positive.
  Definition row := unit.
  Definition frame := unit.
  Definition key_code (x : key) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : prog) : list row := [tt; tt].
  Definition target (_ : prog) (_ : row) := 1%positive.
  Definition start (p : prog) (_ : row) : query key bool frame :=
    Side 2%positive p (Side 2%positive false (Ret p)).
  Definition resume (_ : prog) (_ : frame) (a : bool) : query key bool frame := Ret a.
  Definition deps (_ : prog) (_ : row) : list key := [].
  Definition sides (_ : prog) (_ : row) : list key := [2; 2]%positive.
  Include SYSTEM_SPEC LeastBool.
  Definition wf (_ : prog) : Prop := True.

  (** Positive keys encode themselves injectively. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    intros a b Hcode; exact Hcode.
  Qed.

  (** Positive equality decides equality of keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact Pos.eqb_spec.
  Qed.

  (** The query returns after peeling its two side contributions. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p [] look _ _; discriminate.
  Qed.

  (** Constant contributions are independent of the lookup function. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [] s u _ _ _; reflexivity.
  Qed.

  (** This query never reaches an ask instruction. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [] look [|n] q acc x f _ _ Hrun Hask.
    - cbn [loop_fuel start] in Hrun; injection Hrun as <- <-; discriminate Hask.
    - discriminate Hrun.
  Qed.

  (** Both side contributions use the declared key. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [] look a ss x b _ _ Heval Hin; injection Heval as <- <-.
    cbn [In] in Hin; destruct Hin as [Heq|[Heq|Hfalse]];
      [inversion Heq; now left|inversion Heq; now left|contradiction Hfalse].
  Qed.

  (** The repeated side declarations pay for both output occurrences. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p [] look a ss _ _ Heval; injection Heval as <- <-; reflexivity.
  Qed.
End RepeatedSides.

Module LeastPolicy := Policy LeastBool.
Module LeastProof := WorklistLeast LeastBool LeastBoolLub RepeatedSides LeastPolicy HeapCode.
Module LeastSolver := LeastProof.V.

(** The certificate implements the frozen interface for its concrete solver instance. *)
Module LeastContract <: SOLVER_LEAST LeastBool LeastBoolLub RepeatedSides LeastSolver.
  Include LeastProof.Certificate.
End LeastContract.

Definition least_large_priorities : policy unit :=
  Policy unit
    (PTrieCode.set 1%positive 1048576%positive
      (PTrieCode.set 2%positive 2097152%positive PTrieCode.empty))
    PTrieCode.empty tt 0.

(** Large priorities introduce no hidden priority-width precondition into leastness. *)
Lemma least_large_priorities_free : LeastContract.widening_free least_large_priorities.
Proof.
  intro c; apply PTrie.get_empty.
Qed.

Definition least_observe (result : outcome (kmap positive bool)) :=
  match result with
  | Solved m => Some (map (look_or RepeatedSides.key_code LeastBool.bot m) [1; 2; 3]%positive)
  | _ => None
  end.

(** Repeated rows and side outputs produce true only at their declared destinations. *)
Example least_repeated_side_values :
  least_observe (LeastSolver.run true least_large_priorities 8%N) =
    Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** Bottom contributions preserve the initial bottom store. *)
Example least_bottom_values :
  least_observe (LeastSolver.run false least_large_priorities 8%N) =
    Some [false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** Zero solver fuel returns the actual empty partial store. *)
Example least_zero_fuel :
  LeastSolver.run true least_large_priorities 0%N = OutOfFuel PTrieCode.empty.
Proof.
  vm_compute; reflexivity.
Qed.

(** Constant query outputs are monotone independently of their lookup argument. *)
Lemma repeated_sides_monotone : forall p, RepeatedSides.monotone p.
Proof.
  intros p [] s u _ _; cbn [RepeatedSides.eval RepeatedSides.start RepeatedSides.deps
    eval_query loop_fuel eval_step peel rev_append out_leb fst snd].
  split; [apply LeastBool.leb_refl|].
  constructor; [split; [reflexivity|apply LeastBool.leb_refl]|].
  constructor; [split; [reflexivity|apply LeastBool.leb_refl]|constructor].
Qed.

(** The importing client obtains the bound for every accepting comparison function. *)
Theorem least_concrete_client : forall p fuel m u,
  LeastSolver.run p least_large_priorities fuel = Solved m ->
  RepeatedSides.post_solution p u -> forall x,
    LeastBool.leb (look_or RepeatedSides.key_code LeastBool.bot m x) (u x) = true.
Proof.
  intros p fuel m u Hrun Hpost.
  apply (LeastContract.run_least p least_large_priorities fuel m u).
  - exact I.
  - apply repeated_sides_monotone.
  - exact least_large_priorities_free.
  - exact Hrun.
  - exact Hpost.
Qed.
