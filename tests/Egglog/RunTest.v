(** * Rule plans, saturation runs and relational leastness

    Relational leastness needs sorted comparison views. A comparison view with an identifier
    output can satisfy a relational put, because [present] does not constrain the output of a
    put without a result. For example, the rule with no query atoms that inserts the nullary
    relation [1] is closed in a view containing only its identifier-output row, and that view
    is not sorted for the program.

    The second part runs the planner, the plan checker and the saturation loop of the code
    tower on small programs. For example, transitive closure over the chain of edges from 1
    to 4 saturates with the six paths of the chain.
    Builds on: Syntax, Model, Sorts, the code towers of Index, Join and Database, and Run. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts Index Join Database Run.

Import List.ListNotations.

Definition leastness_program {V : Type} : program V :=
  Program V [Decl 1%positive [] ORel] [Rule V [] [Put 1%positive [] None]].

Definition leastness_comparison {V : Type} : view (V := V) :=
  {| row := fun f k o => f = 1%positive /\ k = [] /\ o = Some (Id 1%positive);
     same := eq;
     kind := lookup_kind [Decl 1%positive [] ORel] |}.

(** The comparison has the declared relation kind despite its wrongly sorted row. *)
Example leastness_comparison_kind {V : Type} :
  kind (@leastness_comparison V) 1%positive = Some ORel.
Proof.
  reflexivity.
Qed.

(** Relational closure alone does not require the output of the witnessing row to be absent. *)
Example leastness_comparison_closed {V : Type}
    (prim : positive -> list V -> option V) (merge : positive -> V -> V -> V) :
  closed prim merge leastness_program leastness_comparison.
Proof.
  intros r s Hr Hmatch.
  destruct Hr as [<- | []].
  cbn [actions present].
  exists [], (Some (Id 1%positive)).
  split; [constructor |].
  repeat split.
Qed.

(** The comparison omits the relation row that leastness claims it must contain. *)
Example leastness_comparison_missing {V : Type} :
  ~ row (@leastness_comparison V) 1%positive [] None.
Proof.
  intros [_ [_ Hout]].
  discriminate.
Qed.

(** The empty-query rule derives the missing relation row from any seed view. *)
Example leastness_derivation {V : Type} (prim : positive -> list V -> option V)
    (seed : view (V := V)) :
  derives prim leastness_program seed 1%positive [].
Proof.
  eapply derive_rule with (r := Rule V [] [Put 1%positive [] None])
    (s := fun _ => None).
  - now left.
  - constructor.
  - constructor. constructor.
Qed.

(** The comparison fails the sorted-view premise of leastness, because its relation row has
    an identifier output. *)
Example leastness_comparison_unsorted {V : Type} :
  ~ view_sorted (program_sorts (@leastness_program V)) (@leastness_comparison V).
Proof.
  intros Hsorted.
  assert (Hrow : row (@leastness_comparison V) 1%positive [] (Some (Id 1%positive)))
    by (repeat split).
  destruct (Hsorted _ _ _ Hrow) as [kind_out [_ [Hkind Hout]]].
  cbn in Hkind.
  injection Hkind as <-.
  cbn in Hout.
  discriminate Hout.
Qed.

(** * Plans and runs *)

(** Values are positives. Primitive [1] adds two values and primitive [2] returns a value below
    five. *)
Module PlanValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (p : positive) (vs : list t) : option t :=
    match p, vs with
    | 1%positive, [a; b] => Some (Pos.add a b)
    | 2%positive, [a] => if Pos.ltb a 5 then Some a else None
    | _, _ => None
    end.
  Definition merge (_ : positive) := Pos.max.
End PlanValue.

Module PlanIndex := IndexCode PlanValue.
Module PlanJoin := JoinCode PlanValue PlanIndex.
Module PlanDatabase := DatabaseCode PlanValue PlanIndex.
Module PlanRun := RunCode PlanValue PlanIndex PlanJoin PlanDatabase.

Definition val (v : positive) : cell positive := Val v.

(** The cell of each queried key of a function after a run. *)
Definition lookups (f : positive) (db : PlanDatabase.t) (ks : list (list (cell positive)))
    : list (option (option (cell positive))) :=
  map (fun k => fst (PlanDatabase.lookup f k db)) ks.

(** Paths [2] close the edges [1]. *)
Definition closure_program : program positive :=
  Program positive [Decl 1 [SVal; SVal] ORel; Decl 2 [SVal; SVal] ORel]
    [Rule positive [Fun positive 1 [Var 1; Var 2] None] [Put 2 [Var 1; Var 2] None];
     Rule positive [Fun positive 2 [Var 1; Var 2] None; Fun positive 1 [Var 2; Var 3] None]
       [Put 2 [Var 1; Var 3] None]].

(** Each relation has one slot that its atoms share. Each rule has a naive plan and one
    semi-naive plan per atom, and the shared variable [2] joins the path slot with the edge
    slot. *)
Example closure_plan :
  PlanRun.plan closure_program =
    Compiled positive [(1%positive, [0; 1]); (2%positive, [0; 1])]
      [CPlan positive 0 (JPlan 2 [[0; 1]]) [All positive 0] [1; 2]%positive [];
       CPlan positive 1 (JPlan 3 [[0; 1]; [1; 2]]) [All positive 1; All positive 0]
         [1; 2; 3]%positive []]
      [CPlan positive 0 (JPlan 2 [[0; 1]]) [New positive 0] [1; 2]%positive [];
       CPlan positive 1 (JPlan 3 [[0; 1]; [1; 2]]) [New positive 1; All positive 0]
         [1; 2; 3]%positive [];
       CPlan positive 1 (JPlan 3 [[0; 1]; [1; 2]]) [All positive 1; New positive 0]
         [1; 2; 3]%positive []].
Proof.
  vm_compute. reflexivity.
Qed.

(** The checker accepts the plan of the two-rule program. *)
Example closure_plan_checked :
  PlanRun.check_plan closure_program (PlanRun.plan closure_program) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The checker rejects a post filter that the query does not need, naive plans that read new
    rows and a slot list in another order. *)
Example closure_plan_tampered :
  let cp := PlanRun.plan closure_program in
  map (PlanRun.check_plan closure_program)
    [Compiled positive (Syntax.slots positive cp)
       (CPlan positive 0 (JPlan 2 [[0; 1]]) [All positive 0] [1; 2]%positive [0] ::
          tl (naive positive cp)) (seminaive positive cp);
     Compiled positive (Syntax.slots positive cp) (seminaive positive cp) (naive positive cp);
     Compiled positive (rev (Syntax.slots positive cp)) (naive positive cp)
       (seminaive positive cp)] =
    [false; false; false].
Proof.
  vm_compute. reflexivity.
Qed.

Definition closure_seed : PlanDatabase.t :=
  let db := PlanRun.load closure_program (PlanRun.plan closure_program) in
  let db := PlanDatabase.put 1 [val 1; val 2] None db in
  let db := PlanDatabase.put 1 [val 2; val 3] None db in
  PlanDatabase.put 1 [val 3; val 4] None db.

(** On the seed, every job of the naive and of the semi-naive round copies an edge, so each
    belongs to the first rule. *)
Example closure_jobs :
  let cp := PlanRun.plan closure_program in
  (map (fun j => rule_ix positive (fst j)) (PlanRun.jobs closure_program cp true closure_seed),
   map (fun j => rule_ix positive (fst j)) (PlanRun.jobs closure_program cp false closure_seed)) =
    ([0; 0; 0]%N, [0; 0; 0]%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** The run saturates with the six paths of the chain and no path back. *)
Example closure_run :
  let result := PlanRun.run closure_program (PlanRun.plan closure_program) (Limits 10 100)
    closure_seed in
  (fst result,
   lookups 2 (snd result)
     [[val 1; val 2]; [val 2; val 3]; [val 3; val 4]; [val 1; val 3]; [val 2; val 4];
      [val 1; val 4]; [val 2; val 1]; [val 4; val 1]; [val 1; val 1]]) =
  (Saturated,
   [Some None; Some None; Some None; Some None; Some None; Some None; None; None; None]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Two rounds stop before the naive round that would confirm saturation. *)
Example closure_iteration_limit :
  fst (PlanRun.run closure_program (PlanRun.plan closure_program) (Limits 2 100)
    closure_seed) = IterLimit.
Proof.
  vm_compute. reflexivity.
Qed.

(** Loops [2] are reflexive edges, threes [3] lead into [3], sums [4] add up to four, smalls
    [5] lie below five, and the empty query fires once into the nullary relation [6]. *)
Definition filter_program : program positive :=
  Program positive
    [Decl 1 [SVal; SVal] ORel; Decl 2 [SVal] ORel; Decl 3 [SVal] ORel;
     Decl 4 [SVal; SVal] ORel; Decl 5 [SVal] ORel; Decl 6 [] ORel]
    [Rule positive [Fun positive 1 [Var 7; Var 7] None] [Put 2 [Var 7] None];
     Rule positive [Fun positive 1 [Var 1; Lit 3%positive] None] [Put 3 [Var 1] None];
     Rule positive
       [Fun positive 1 [Var 1; Var 2] None; Prim positive 1 [Var 2; Var 1] (Lit 4%positive)]
       [Put 4 [Var 1; Var 2] None];
     Rule positive [Fun positive 1 [Var 1; Var 2] None; Prim positive 2 [Var 2] (Var 2)]
       [Put 5 [Var 2] None];
     Rule positive [] [Put 6 [] None]].

(** The checker accepts the filters. *)
Example filter_plan_checked :
  PlanRun.check_plan filter_program (PlanRun.plan filter_program) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A repeated variable reads a copy, named [8] after the largest variable, at the front of the
    plan's variables, and a literal reads a constant source. *)
Example filter_plan_layout :
  firstn 2 (naive positive (PlanRun.plan filter_program)) =
    [CPlan positive 0 (JPlan 2 [[0; 1]]) [All positive 0] [8; 7]%positive [0];
     CPlan positive 1 (JPlan 2 [[0; 1]; [1]]) [All positive 1; Const positive (val 3)]
       [1; 2]%positive []].
Proof.
  vm_compute. reflexivity.
Qed.

Definition filter_seed : PlanDatabase.t :=
  let db := PlanRun.load filter_program (PlanRun.plan filter_program) in
  let db := PlanDatabase.put 1 [val 1; val 3] None db in
  let db := PlanDatabase.put 1 [val 4; val 4] None db in
  PlanDatabase.put 1 [val 2; val 7] None db.

(** Each filter keeps exactly its matching edges. *)
Example filter_run :
  let result := PlanRun.run filter_program (PlanRun.plan filter_program) (Limits 10 100)
    filter_seed in
  let ends := [[val 1]; [val 3]; [val 4]; [val 7]] in
  (fst result, lookups 2 (snd result) ends, lookups 3 (snd result) ends,
   lookups 4 (snd result) [[val 1; val 3]; [val 4; val 4]; [val 2; val 7]],
   lookups 5 (snd result) ends, lookups 6 (snd result) [[]]) =
  (Saturated, [None; None; Some None; None], [Some None; None; None; None],
   [Some None; None; None], [None; Some None; Some None; None], [Some None]).
Proof.
  vm_compute. reflexivity.
Qed.

(** Unifying the cells of related constants allocates one class per argument and per pointer. *)
Definition class_program : program positive := Program positive
  [Decl 1 [SVal; SVal] ORel; Decl 2 [SVal; SVal] ORel; Decl 6 [SVal] OId; Decl 7 [SId] OId]
  [Rule positive [Fun positive 1 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Union (Var 5) (Var 4)];
   Rule positive [Fun positive 2 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Make 6 7 [Var 4];
      Union (Var 5) (Var 6)]].

(** The identifier functions get their full slots first. *)
Example class_plan :
  let cp := PlanRun.plan class_program in
  (Syntax.slots positive cp, PlanRun.check_plan class_program cp) =
    ([(6%positive, [0; 1]); (7%positive, [0; 1]); (1%positive, [0; 1]);
      (2%positive, [0; 1])], true).
Proof.
  vm_compute. reflexivity.
Qed.

Definition class_seed : PlanDatabase.t :=
  let db := PlanRun.load class_program (PlanRun.plan class_program) in
  let db := PlanDatabase.put 1 [val 1; val 2] None db in
  PlanDatabase.put 2 [val 3; val 1] None db.

(** The run allocates the classes of [1], [2] and [3] and of two pointers. *)
Example class_run :
  let result := PlanRun.run class_program (PlanRun.plan class_program) (Limits 10 100)
    class_seed in
  (fst result, PlanDatabase.ids (snd result)) = (Saturated, 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** A nullary relation atom is well sorted, but no join column can read it, so the checker
    rejects its plan. *)
Example nullary_atom_rejected :
  let p := Program positive [Decl 1 [] ORel; Decl 2 [] ORel]
    [Rule positive [Fun positive 1 [] None] [Put 2 [] None]] in
  (check_program p, PlanRun.check_plan p (PlanRun.plan p)) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.
