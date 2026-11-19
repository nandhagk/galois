(** * Values and containers beside the other features of the command

    Programs that combine the values and the containers of [Egglog] with relations that read
    each other, lattice tables and equations that read relations, run on the engine, with their
    generated lemmas. A list of values in an input row is one value, a datatype may hold another
    datatype, a list or a list of pairs, and a pattern may write an element of a list of pairs
    as a variable. The other features read these programs as they read any other.
    For example, the union [leaf_known] of [term_eq] reads the relation [known], and the run
    joins the sum [Sum [Leaf (Ref 1); Leaf (Const 2)]] with the sum
    [Sum [Leaf (Const 5); Leaf (Const 2)]] once register 1 holds 5.

    Groups:
    - [MutualTests] Two relations that read each other over jobs whose lists of waits are values.
    - [LatticeTests] A lattice table whose clauses read lists of values, and a lattice table of
      optional bounds.
    - [ReadTests] An equation over terms that hold atoms, lists, records and tuples, whose union
      reads a relation and whose rewrite moves pairs written as variables.
    - [ScheduleTests] An equation over schedules that hold lists, whose union reads relations
      that read each other.
    - [BoundTests] An equation over amounts that hold records, whose rewrites read a lattice
      table.
    - [GlueTests] The generated lemmas of these programs in both directions.
    - [RejectionTests] A relation of an equation reads a list that the equation holds as a
      class.

    Builds on: the derive command, the encoders, the meaning of equations that read rows, the
    meaning of lattice reads, the runner and the engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Index Join Database Run.
From Galois.Front Require Import Spec SpecLattice SpecReads RunnerSig Runner Encode Derive.
Import List.ListNotations.

Local Open Scope positive_scope.

(** * Fixtures *)

(** Saturation stops after at most 50 iterations and allocates at most 1000 identifiers. *)
Definition test_limits : limits := Limits 50%N 1000%N.

(** A job with its number and the numbers of the jobs that it waits for. *)
Inductive job : Type :=
  | Job (id : positive) (deps : list positive).

(** Whether the job [d] is among the jobs [ds]. *)
Definition waits_for (d : positive) (ds : list positive) : bool := existsb (Pos.eqb d) ds.

Egglog Primitives JobOps waits_for.

(** [waits jobs d e] says that the job [d] waits for the job [e]. *)
Inductive waits (jobs : list job) : positive -> positive -> Prop :=
  | waits_on d ds e es : In (Job d ds) jobs -> In (Job e es) jobs -> waits_for e ds = true ->
      waits jobs d e.

(** [odd_wait jobs i e] and [even_wait jobs i e] say that a chain of waits of odd or of even
    length leads from the job [i] to the job [e]. *)
Inductive odd_wait (jobs : list job) : positive -> positive -> Prop :=
  | odd_once i e : waits jobs i e -> odd_wait jobs i e
  | odd_more i d e : even_wait jobs i d -> waits jobs d e -> odd_wait jobs i e
with even_wait (jobs : list job) : positive -> positive -> Prop :=
  | even_more i d e : odd_wait jobs i d -> waits jobs d e -> even_wait jobs i e.

(** [free jobs i] says that the job [i] waits for no job. *)
Inductive free (jobs : list job) : positive -> Prop :=
  | free_job i : In (Job i []) jobs -> free jobs i.

Egglog Waits from odd_wait even_wait waits free with JobOps.

(** A schedule is a job, or a list of schedules that run in order. *)
Inductive sched : Type :=
  | Task (i : positive)
  | Seq (ss : list sched).

(** [sched_eq jobs s t] says that [s] and [t] run the same jobs. A job that waits for another
    through a chain of odd length runs after it. *)
Inductive sched_eq (jobs : list job) : sched -> sched -> Prop :=
  | sched_refl s : sched_eq jobs s s
  | sched_sym s t : sched_eq jobs s t -> sched_eq jobs t s
  | sched_trans s t u : sched_eq jobs s t -> sched_eq jobs t u -> sched_eq jobs s u
  | sched_seq ss ts : Forall2 (sched_eq jobs) ss ts -> sched_eq jobs (Seq ss) (Seq ts)
  | sched_after i e : odd_wait jobs i e -> sched_eq jobs (Task i) (Seq [Task e; Task i]).

Egglog Schedules from odd_wait even_wait waits sched_eq with JobOps.

(** The waits of a job, the sum of positives and their minimum. *)
Egglog Primitives HopOps waits_for Pos.add Pos.min.

(** [hops jobs i e n] says that a chain of [n] waits leads from the job [i] to the job [e]. Its
    merge keeps the shortest chain. *)
Inductive hops (jobs : list job) : positive -> positive -> positive -> Prop :=
  | hops_once i ds e es : In (Job i ds) jobs -> In (Job e es) jobs -> waits_for e ds = true ->
      hops jobs i e 1
  | hops_more i d n ds e es : hops jobs i d n -> In (Job d ds) jobs -> In (Job e es) jobs ->
      waits_for e ds = true -> hops jobs i e (Pos.add n 1).

Egglog Hops from hops with HopOps merge hops Pos.min.

(** The tighter of two optional bounds, where [None] is no bound. *)
Definition tighter (a b : option positive) : option positive :=
  match a, b with
  | Some x, Some y => Some (Pos.min x y)
  | Some x, None => Some x
  | None, _ => b
  end.

Egglog Primitives CapOps tighter.

(** [cap caps n c] says that the node [n] has the optional bound [c]. Its merge keeps the
    tighter bound. *)
Inductive cap (caps : list (positive * option positive)) : positive -> option positive -> Prop :=
  | cap_given n c : In (n, c) caps -> cap caps n c.

Egglog Caps from cap with CapOps merge cap tighter.

(** A statement of a program says that register [x] holds the constant [c], or the value of
    register [y]. *)
Inductive stmt : Type :=
  | Init (x c : positive)
  | Copy (x y : positive).

(** [known prog x c] says that register [x] holds the constant [c]. *)
Inductive known (prog : list stmt) : positive -> positive -> Prop :=
  | known_init x c : In (Init x c) prog -> known prog x c
  | known_copy x y c : In (Copy x y) prog -> known prog y c -> known prog x c.

(** Atoms are registers and constants. *)
Inductive atom : Type :=
  | Ref (x : positive)
  | Const (c : positive).

(** A term is an atom, a sum of a list of terms, a record of fields named by keys, or a tuple of
    values. *)
Inductive term : Type :=
  | Leaf (a : atom)
  | Sum (ts : list term)
  | Rec (fs : list (positive * term))
  | Tuple (vs : list positive).

(** [term_eq prog t u] says that [t] and [u] are equal when the registers hold their known
    constants, and the first two fields of a record swap. *)
Inductive term_eq (prog : list stmt) : term -> term -> Prop :=
  | term_refl a : term_eq prog a a
  | term_sym a b : term_eq prog a b -> term_eq prog b a
  | term_trans a b c : term_eq prog a b -> term_eq prog b c -> term_eq prog a c
  | term_sum ts us : Forall2 (term_eq prog) ts us -> term_eq prog (Sum ts) (Sum us)
  | term_record fs gs : Forall2 (pair_rel eq (term_eq prog)) fs gs ->
      term_eq prog (Rec fs) (Rec gs)
  | term_tuple vs ws : vs = ws -> term_eq prog (Tuple vs) (Tuple ws)
  | leaf_known x c : known prog x c -> term_eq prog (Leaf (Ref x)) (Leaf (Const c))
  | rec_swap p q rest : term_eq prog (Rec (p :: q :: rest)) (Rec (q :: p :: rest)).

Egglog Terms from known term_eq.

(** The minimum and the order of positives. *)
Egglog Primitives BoundOps Pos.min Pos.leb.

(** The fact that register [x] is at most [b]. *)
Inductive limit : Type :=
  | Below (x b : positive).

(** [bound facts x b] says that register [x] is at most [b]. Its merge keeps the least bound. *)
Inductive bound (facts : list limit) : positive -> positive -> Prop :=
  | bound_below x b : In (Below x b) facts -> bound facts x b.

(** Registers, fixed amounts, their minima, and records of amounts named by keys. *)
Inductive amount : Type :=
  | Reg (x : positive)
  | Fixed (c : positive)
  | Min (a b : amount)
  | Named (fs : list (positive * amount)).

(** [simp facts t u] says that [t] and [u] are equal under the bounds of the registers. The
    minimum of a register and an amount at least its bound is the register, and a record of one
    field is the amount of the field. *)
Inductive simp (facts : list limit) : amount -> amount -> Prop :=
  | simp_refl a : simp facts a a
  | simp_sym a b : simp facts a b -> simp facts b a
  | simp_trans a b c : simp facts a b -> simp facts b c -> simp facts a c
  | simp_min a a' b b' : simp facts a a' -> simp facts b b' -> simp facts (Min a b) (Min a' b')
  | simp_named fs gs : Forall2 (pair_rel eq (simp facts)) fs gs ->
      simp facts (Named fs) (Named gs)
  | simp_bound x b c : bound facts x b -> Pos.leb b c = true ->
      simp facts (Min (Reg x) (Fixed c)) (Reg x)
  | named_one p : simp facts (Named [p]) (snd p).

Egglog Bounds from bound simp with BoundOps merge bound Pos.min.

(** The values of the jobs, whose primitive set is [JobOps]. *)
Module JobValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := JobOps.prim.
  Definition merge (_ : positive) := Pos.max.
End JobValue.

Module JobIndex := IndexCode JobValue.
Module JobJoin := JoinCode JobValue JobIndex.
Module JobDatabase := DatabaseCode JobValue JobIndex.
Module JobRun := RunCode JobValue JobIndex JobJoin JobDatabase.
Module JobRunner := RunnerCode JobValue JobIndex JobJoin JobDatabase JobRun.

(** The values of the chains of waits, whose lattice table merges with [prim_merge]. *)
Module HopValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := HopOps.prim.
  Definition merge := prim_merge HopOps.prim.
End HopValue.

Module HopIndex := IndexCode HopValue.
Module HopJoin := JoinCode HopValue HopIndex.
Module HopDatabase := DatabaseCode HopValue HopIndex.
Module HopRun := RunCode HopValue HopIndex HopJoin HopDatabase.
Module HopRunner := RunnerCode HopValue HopIndex HopJoin HopDatabase HopRun.

(** The values of the optional bounds, whose lattice table merges with [prim_merge]. *)
Module CapValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := CapOps.prim.
  Definition merge := prim_merge CapOps.prim.
End CapValue.

Module CapIndex := IndexCode CapValue.
Module CapJoin := JoinCode CapValue CapIndex.
Module CapDatabase := DatabaseCode CapValue CapIndex.
Module CapRun := RunCode CapValue CapIndex CapJoin CapDatabase.
Module CapRunner := RunnerCode CapValue CapIndex CapJoin CapDatabase CapRun.

(** The values of the terms, whose program calls no primitive. *)
Module PlainValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End PlainValue.

Module PlainIndex := IndexCode PlainValue.
Module PlainJoin := JoinCode PlainValue PlainIndex.
Module PlainDatabase := DatabaseCode PlainValue PlainIndex.
Module PlainRun := RunCode PlainValue PlainIndex PlainJoin PlainDatabase.
Module PlainRunner := RunnerCode PlainValue PlainIndex PlainJoin PlainDatabase PlainRun.

(** The values of the bounds, whose lattice table merges with [prim_merge]. *)
Module BoundValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := BoundOps.prim.
  Definition merge := prim_merge BoundOps.prim.
End BoundValue.

Module BoundIndex := IndexCode BoundValue.
Module BoundJoin := JoinCode BoundValue BoundIndex.
Module BoundDatabase := DatabaseCode BoundValue BoundIndex.
Module BoundRun := RunCode BoundValue BoundIndex BoundJoin BoundDatabase.
Module BoundRunner := RunnerCode BoundValue BoundIndex BoundJoin BoundDatabase BoundRun.

(** Job 1 waits for job 2, job 2 waits for job 3, and job 3 waits for no job. *)
Definition chain : list job := [Job 1 [2]; Job 2 [3]; Job 3 []].

(** Job 1 waits for jobs 2 and 3, and job 2 waits for job 3. *)
Definition shortcut : list job := [Job 1 [2; 3]; Job 2 [3]; Job 3 []].

(** Node 1 has the bounds 5, none and 3. *)
Definition caps_of_one : list (positive * option positive) := [(1, Some 5); (1, None); (1, Some 3)].

(** Register 3 holds 5, and register 1 copies register 3. *)
Definition prog : list stmt := [Init 3 5; Copy 1 3].

(** Register 1 is at most 10 and at most 3. *)
Definition limits_of_one : list limit := [Below 1 10; Below 1 3].

(** The value that a database stores at a key of a lattice table, if it stores one. *)
Definition hop_stored (f : positive) (ks : list positive) (db : HopDatabase.t) :
    option positive :=
  match fst (HopDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** The value that a database stores at a key of a lattice table, if it stores one. *)
Definition cap_stored (f : positive) (ks : list positive) (db : CapDatabase.t) :
    option positive :=
  match fst (CapDatabase.lookup f (map Val ks) db) with
  | Some (Some (Val v)) => Some v
  | _ => None
  end.

(** [known prog 1 5] holds, through the copy of register 3. *)
Lemma one_is_known : known prog 1 5.
Proof.
  apply (known_copy prog 1 3 5).
  - simpl. auto.
  - apply known_init. simpl. auto.
Qed.

(** Job 1 waits for job 2 in [chain]. *)
Lemma one_waits_for_two : waits chain 1 2.
Proof.
  apply (waits_on chain 1 [2] 2 [3]).
  - simpl. auto.
  - simpl. auto.
  - reflexivity.
Qed.

(** Job 2 waits for job 3 in [chain]. *)
Lemma two_waits_for_three : waits chain 2 3.
Proof.
  apply (waits_on chain 2 [3] 3 []).
  - simpl. auto.
  - simpl. auto.
  - reflexivity.
Qed.

(** * Relations that read each other over lists of values *)

Module MutualTests.

  (** The database after a run of [Waits] on [chain]. *)
  Definition waits_result : JobDatabase.t :=
    snd (JobRunner.solve Waits.program (Waits.facts chain) test_limits).

  (** A row of [Waits.facts] holds the list of waits of a job as one value. *)
  Example row_holds_the_list :
    In (Waits.Job_code, [2; encode_list id_encode [3]]) (Waits.facts chain).
  Proof.
    vm_compute. auto.
  Qed.

  (** The chain from job 1 to job 2 has length one, and the chain to job 3 has length two. *)
  Example chains_alternate :
    JobRunner.holds Waits.odd_wait_code [1; 2] waits_result = true /\
    JobRunner.holds Waits.even_wait_code [1; 3] waits_result = true /\
    JobRunner.holds Waits.odd_wait_code [1; 3] waits_result = false.
  Proof.
    vm_compute. auto.
  Qed.

  (** The literal empty list of [free_job] reads the jobs that wait for nothing. *)
  Example empty_list_reads_free_jobs :
    JobRunner.holds Waits.free_code [3] waits_result = true /\
    JobRunner.holds Waits.free_code [1] waits_result = false.
  Proof.
    vm_compute. auto.
  Qed.

End MutualTests.

(** * Lattice tables over lists and options of values *)

Module LatticeTests.

  (** The shortest chain from job 1 to job 3 is the direct wait. *)
  Example shortest_chain_is_stored :
    hop_stored Hops.hops_code [1; 3]
      (snd (HopRunner.solve Hops.program (Hops.facts shortcut) test_limits)) = Some 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The run reaches a saturated outcome, because the shortest chains are stored. *)
  Example hops_saturate :
    fst (HopRunner.solve Hops.program (Hops.facts shortcut) test_limits) = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The table of bounds stores the encoding of the tighter bound 3. *)
  Example tighter_bound_is_stored :
    cap_stored Caps.cap_code [1]
      (snd (CapRunner.solve Caps.program (Caps.facts caps_of_one) test_limits)) =
      Some (encode_option id_encode (Some 3)).
  Proof.
    vm_compute. reflexivity.
  Qed.

End LatticeTests.

(** * Equations that read relations over terms with containers *)

Module ReadTests.

  (** Whether saturating [Terms] after [prog] puts two terms in one class. *)
  Definition same_term (a b : term) : bool :=
    PlainRunner.equal Terms.program (Terms.facts prog) test_limits
      (Terms.encode_term a) (Terms.encode_term b).

  (** Register 1 holds 5, so a sum with it is a sum with the constant. *)
  Example sum_reads_known_register :
    same_term (Sum [Leaf (Ref 1); Leaf (Const 2)]) (Sum [Leaf (Const 5); Leaf (Const 2)]) =
      true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The fields of a record swap, and the value of a field reads the known register. *)
  Example record_swaps_and_reads :
    same_term (Rec [(1, Leaf (Ref 1)); (2, Tuple [7])])
      (Rec [(2, Tuple [7]); (1, Leaf (Const 5))]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Register 2 holds no known constant. *)
  Example unknown_register_stays :
    same_term (Leaf (Ref 2)) (Leaf (Const 5)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two tuples of different values stay apart. *)
  Example different_tuples_stay :
    same_term (Tuple [1; 2]) (Tuple [2; 1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ReadTests.

(** * Equations that read relations that read each other *)

Module ScheduleTests.

  (** Whether saturating [Schedules] after [chain] puts two schedules in one class. *)
  Definition same_sched (s t : sched) : bool :=
    JobRunner.equal Schedules.program (Schedules.facts chain) test_limits
      (Schedules.encode_sched s) (Schedules.encode_sched t).

  (** Job 1 waits for job 2 through a chain of length one, so it runs after job 2, also inside
      a sequence. *)
  Example task_runs_after_its_wait :
    same_sched (Seq [Task 1; Task 3]) (Seq [Seq [Task 2; Task 1]; Task 3]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Job 1 waits for job 3 through a chain of length two only. *)
  Example even_chain_gives_no_order :
    same_sched (Task 1) (Seq [Task 3; Task 1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ScheduleTests.

(** * Equations that read lattice tables over records *)

Module BoundTests.

  (** Whether saturating [Bounds] after [limits_of_one] puts two amounts in one class. *)
  Definition same_amount (a b : amount) : bool :=
    BoundRunner.equal Bounds.program (Bounds.facts limits_of_one) test_limits
      (Bounds.encode_amount a) (Bounds.encode_amount b).

  (** A record of one field is its amount, and the least bound 3 drops the minimum with 5. *)
  Example single_field_is_its_bounded_amount :
    same_amount (Named [(4, Min (Reg 1) (Fixed 5))]) (Reg 1) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The least bound 3 is above 2, so the minimum with 2 stays. *)
  Example smaller_amount_stays :
    same_amount (Named [(4, Min (Reg 1) (Fixed 2))]) (Reg 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BoundTests.

(** * Glue *)

Module GlueTests.

  (** A chain of even length from job 1 to job 3 gives its derived row, through the fixpoint of
      the relations that read each other. *)
  Example even_wait_gives_derived_row :
    derived JobOps.prim Waits.spec (Waits.inputs chain) Waits.even_wait_code [1; 3].
  Proof.
    apply (proj1 (Waits.even_wait_spec chain 1 3)).
    exact (even_more chain 1 2 3 (odd_once chain 1 2 one_waits_for_two) two_waits_for_three).
  Qed.

  (** A derived row of [free] gives a job that waits for nothing. *)
  Example derived_row_gives_free :
    derived JobOps.prim Waits.spec (Waits.inputs chain) Waits.free_code [3] -> free chain 3.
  Proof.
    intros Hrow. exact (proj2 (Waits.free_spec chain 3) Hrow).
  Qed.

  (** A value of [hops] gives an assigned value of its table. *)
  Example hops_give_assigned_value :
    hops shortcut 1 3 1 ->
    lat_assigned HopOps.prim (prim_merge HopOps.prim) Hops.spec (Hops.inputs shortcut)
      Hops.hops_code [1; 3] 1.
  Proof.
    intros Hhops. exact (proj1 (Hops.hops_spec shortcut 1 3 1) Hhops).
  Qed.

  (** An optional bound gives the assigned encoding of the option. *)
  Example cap_gives_assigned_option :
    cap caps_of_one 1 None ->
    lat_assigned CapOps.prim (prim_merge CapOps.prim) Caps.spec (Caps.inputs caps_of_one)
      Caps.cap_code [1] (encode_option id_encode None).
  Proof.
    intros Hcap. exact (proj1 (Caps.cap_spec caps_of_one 1 None) Hcap).
  Qed.

  (** Two records whose keys are equal and whose values are equal are a read congruence. *)
  Example related_records_are_read_congruent :
    forall prim fs gs, Forall2 (pair_rel eq (term_eq prog)) fs gs ->
    read_congruent prim Terms.spec (derived prim Terms.spec (Terms.inputs prog)) no_values
      (Terms.encode_term (Rec fs)) (Terms.encode_term (Rec gs)).
  Proof.
    intros prim fs gs Hall.
    exact (Terms.term_eq_congruent prim prog _ _ (term_record prog fs gs Hall)).
  Qed.

  (** Two equal tuples are a read congruence. *)
  Example equal_tuples_are_read_congruent :
    forall prim vs,
    read_congruent prim Terms.spec (derived prim Terms.spec (Terms.inputs prog)) no_values
      (Terms.encode_term (Tuple vs)) (Terms.encode_term (Tuple vs)).
  Proof.
    intros prim vs.
    exact (Terms.term_eq_congruent prim prog _ _ (term_tuple prog vs vs eq_refl)).
  Qed.

  (** The swap of two fields written as variables is a read step. *)
  Example swap_is_a_read_step :
    forall prim p q rest,
    read_step prim Terms.spec (derived prim Terms.spec (Terms.inputs prog)) no_values
      (Terms.encode_term (Rec (p :: q :: rest))) (Terms.encode_term (Rec (q :: p :: rest))).
  Proof.
    intros prim p q rest. exact (Terms.rec_swap_steps prim prog p q rest).
  Qed.

  (** An instance of [sched_eq] is a read congruence over the rows of relations that read each
      other. *)
  Example schedule_gives_read_congruence :
    forall s t, sched_eq chain s t ->
    read_congruent JobOps.prim Schedules.spec
      (derived JobOps.prim Schedules.spec (Schedules.inputs chain)) no_values
      (Schedules.encode_sched s) (Schedules.encode_sched t).
  Proof.
    exact (Schedules.sched_eq_congruent chain).
  Qed.

  (** An instance of [simp] over records is a read congruence over the meaning of lattice
      reads. *)
  Example simp_gives_read_congruence :
    forall t u, simp limits_of_one t u ->
    read_congruent BoundOps.prim Bounds.spec
      (lat_derived BoundOps.prim (prim_merge BoundOps.prim) Bounds.spec
        (Bounds.inputs limits_of_one))
      (lat_merged BoundOps.prim (prim_merge BoundOps.prim) Bounds.spec
        (Bounds.inputs limits_of_one))
      (Bounds.encode_amount t) (Bounds.encode_amount u).
  Proof.
    exact (Bounds.simp_congruent limits_of_one).
  Qed.

End GlueTests.

(** * Rejections *)

Module RejectionTests.

  (** [listed rows vs] says that some row of [rows] holds the list [vs]. *)
  Inductive listed (rows : list (positive * list positive)) : list positive -> Prop :=
    | listed_row k vs : In (k, vs) rows -> listed rows vs.

  (** Tags, and tuples of values. *)
  Inductive tagged : Type :=
    | Tag (n : positive)
    | Tup (vs : list positive).

  (** A listed tuple is the tag 1. *)
  Inductive tagged_eq (rows : list (positive * list positive)) : tagged -> tagged -> Prop :=
    | tagged_refl a : tagged_eq rows a a
    | tagged_listed vs : listed rows vs -> tagged_eq rows (Tup vs) (Tag 1).

  (** In an equation, a variable of a list type is a class, so a premise over a relation of
      lists of values cannot read it. *)
  Fail Egglog Listed from listed tagged_eq.

End RejectionTests.
