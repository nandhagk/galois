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

From Stdlib Require Import List PArith NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model Sorts
  RunSig Index Join Database Run.

Import Lia.
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

(** A nullary relation atom reads no column, so the sort checker rejects the program and the
    plan checker rejects its plan. *)
Example nullary_atom_rejected :
  let p := Program positive [Decl 1 [] ORel; Decl 2 [] ORel]
    [Rule positive [Fun positive 1 [] None] [Put 2 [] None]] in
  (check_program p, PlanRun.check_plan p (PlanRun.plan p)) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

(** * Rejecting aliases of hidden join variables *)

Definition copy_alias_program : program positive :=
  Program positive [Decl 1 [SVal; SVal] ORel; Decl 2 [SVal] ORel; Decl 3 [] ORel]
    [Rule positive [Fun positive 1 [Var 2; Var 2] None;
       Fun positive 2 [Var 1] None] [Put 3 [] None]].

Definition copy_alias_plan : cplan positive :=
  CPlan positive 0 (JPlan 2 [[0; 1]; [0]])
    [All positive 0; All positive 1] [1; 2]%positive [0].

Definition copy_alias_compiled : compiled positive :=
  Compiled positive [(1%positive, [1; 0]); (2%positive, [0])]
    [copy_alias_plan] [copy_alias_plan; copy_alias_plan].

Definition copy_alias_seed (cp : compiled positive) : PlanDatabase.t :=
  let db := PlanRun.load copy_alias_program cp in
  let db := PlanDatabase.put 1 [val 1; val 1] None db in
  PlanDatabase.put 2 [val 2] None db.

(** A copy of variable [2] must not reuse the join variable of [1]. *)
Example copy_alias_rejected :
  (PlanRun.check_plan copy_alias_program copy_alias_compiled,
   PlanRun.check_plan copy_alias_program (PlanRun.plan copy_alias_program)) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** The aliased join loses the match witnessed by the two stored rows. *)
Example copy_alias_loses_match :
  (lookups 1 (copy_alias_seed copy_alias_compiled) [[val 1; val 1]],
   lookups 2 (copy_alias_seed copy_alias_compiled) [[val 2]],
   length (PlanRun.jobs copy_alias_program copy_alias_compiled true
     (copy_alias_seed copy_alias_compiled)),
   length (PlanRun.jobs copy_alias_program (PlanRun.plan copy_alias_program) true
     (copy_alias_seed (PlanRun.plan copy_alias_program)))) =
  ([Some None], [Some None], 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

Definition literal_alias_program : program positive :=
  Program positive [Decl 1 [SVal] ORel; Decl 2 [SVal] ORel; Decl 3 [] ORel]
    [Rule positive [Fun positive 1 [Lit 1%positive] None;
       Fun positive 2 [Var 1] None] [Put 3 [] None]].

Definition literal_alias_plan : cplan positive :=
  CPlan positive 0 (JPlan 1 [[0]; [0]; [0]])
    [All positive 0; Const positive (val 1); All positive 1] [1]%positive [].

Definition literal_alias_compiled : compiled positive :=
  Compiled positive [(1%positive, [0]); (2%positive, [0])]
    [literal_alias_plan] [literal_alias_plan; literal_alias_plan].

Definition literal_alias_seed (cp : compiled positive) : PlanDatabase.t :=
  let db := PlanRun.load literal_alias_program cp in
  let db := PlanDatabase.put 1 [val 1] None db in
  PlanDatabase.put 2 [val 2] None db.

(** A literal must not reuse the join variable of a real query variable. *)
Example literal_alias_rejected :
  (PlanRun.check_plan literal_alias_program literal_alias_compiled,
   PlanRun.check_plan literal_alias_program (PlanRun.plan literal_alias_program)) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** The aliased constant excludes a real-variable match with a different value. *)
Example literal_alias_loses_match :
  (lookups 1 (literal_alias_seed literal_alias_compiled) [[val 1]],
   lookups 2 (literal_alias_seed literal_alias_compiled) [[val 2]],
   length (PlanRun.jobs literal_alias_program literal_alias_compiled true
     (literal_alias_seed literal_alias_compiled)),
   length (PlanRun.jobs literal_alias_program (PlanRun.plan literal_alias_program) true
     (literal_alias_seed (PlanRun.plan literal_alias_program)))) =
  ([Some None], [Some None], 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

Definition literals_alias_program : program positive :=
  Program positive [Decl 1 [SVal] ORel; Decl 2 [SVal] ORel; Decl 3 [] ORel]
    [Rule positive [Fun positive 1 [Lit 1%positive] None;
       Fun positive 2 [Lit 2%positive] None] [Put 3 [] None]].

Definition literals_alias_plan : cplan positive :=
  CPlan positive 0 (JPlan 1 [[0]; [0]; [0]; [0]])
    [All positive 0; Const positive (val 1); All positive 1; Const positive (val 2)]
    [2]%positive [].

Definition literals_alias_compiled : compiled positive :=
  Compiled positive [(1%positive, [0]); (2%positive, [0])]
    [literals_alias_plan] [literals_alias_plan; literals_alias_plan].

Definition literals_alias_seed (cp : compiled positive) : PlanDatabase.t :=
  let db := PlanRun.load literals_alias_program cp in
  let db := PlanDatabase.put 1 [val 1] None db in
  PlanDatabase.put 2 [val 2] None db.

(** Even a fresh name cannot serve two different literal occurrences. *)
Example literals_alias_rejected :
  (PlanRun.check_plan literals_alias_program literals_alias_compiled,
   PlanRun.check_plan literals_alias_program (PlanRun.plan literals_alias_program)) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Joining different literals through one variable discards their independent match. *)
Example literals_alias_loses_match :
  (lookups 1 (literals_alias_seed literals_alias_compiled) [[val 1]],
   lookups 2 (literals_alias_seed literals_alias_compiled) [[val 2]],
   length (PlanRun.jobs literals_alias_program literals_alias_compiled true
     (literals_alias_seed literals_alias_compiled)),
   length (PlanRun.jobs literals_alias_program (PlanRun.plan literals_alias_program) true
     (literals_alias_seed (PlanRun.plan literals_alias_program)))) =
  ([Some None], [Some None], 0, 1).
Proof.
  vm_compute. reflexivity.
Qed.

(** * A missing premise in the derivation plan law *)

(** The relational-fragment flag does not reject a result-bearing put. The database below
    makes that put a valid lattice insertion, while the program's relational derivation
    rules cannot derive any row from it. No unfinished Run law is used in this example. *)
Module DerivationPlanCounterexample (V : VALUE) (I : IndexSig.INDEX V)
    (J : JoinSig.JOIN V I) (D : DatabaseSig.DATABASE V I).
  Module R := Run V I J D.

  Definition counter_rule (v : V.t) : rule V.t :=
    Rule V.t [] [Put 1%positive [] (Some (Lit v))].
  Definition counter_program (v : V.t) : program V.t :=
    Program V.t [Decl 1%positive [] ORel] [counter_rule v].
  Definition counter_db : D.t := D.init [Decl 1%positive [] (OLat 1%positive)] [].
  Definition counter_derived (v : V.t) (current : D.t) : Prop :=
    forall f k o, row (D.view current) f k o ->
      derives V.prim (counter_program v) (D.view counter_db) f k.

  Lemma counter_empty : forall f k o, ~ row (D.view counter_db) f k o.
  Proof.
    intros f k o Hrow. unfold counter_db in Hrow.
    exact (proj1 (proj1 (D.init_view [Decl 1%positive [] (OLat 1%positive)] []
      f k o 1%positive 1%positive)) Hrow).
  Qed.

  Lemma counter_no_ids : R.no_ids counter_db.
  Proof.
    destruct (D.init_view [Decl 1%positive [] (OLat 1%positive)] []
      1%positive [] None 1%positive 1%positive) as [_ [_ [_ [_ [Hids _]]]]].
    split; [exact Hids|]. intros f k o Hrow. exfalso. eapply counter_empty. exact Hrow.
  Qed.

  Lemma counter_put_allowed : forall v, D.kind_ok counter_db 1%positive [] (Some (Val v)).
  Proof.
    intro v.
    destruct (D.init_view [Decl 1%positive [] (OLat 1%positive)] []
      1%positive [] None 1%positive 1%positive) as [_ [_ [Hkind [Hslots _]]]].
    split.
    - intros i Hin. destruct Hin as [Hbad|[]]. discriminate Hbad.
    - split.
      + intros perm Hin. unfold counter_db in Hin. rewrite Hslots in Hin. contradiction.
      + change (kind (D.view counter_db) 1%positive = Some (OLat 1%positive)) in Hkind.
        now rewrite Hkind.
  Qed.

  Lemma counter_old_empty : D.old counter_db 1%positive [] = None.
  Proof.
    destruct (D.old counter_db 1%positive []) as [o|] eqn:Hold; [|reflexivity].
    exfalso. apply (counter_empty 1%positive [] o).
    apply (proj1 (D.old_row counter_db 1%positive [] o
      (D.wf_init [Decl 1%positive [] (OLat 1%positive)] []))). exact Hold.
  Qed.

  Lemma counter_inserted : forall v,
    row (D.view (R.apply (actions V.t (counter_rule v)) (fun _ => None) counter_db))
      1%positive [] (Some (Val v)).
  Proof.
    intro v. change (row (D.view (D.put 1%positive [] (Some (Val v)) counter_db))
      1%positive [] (Some (Val v))).
    apply (proj2 (D.put_rows 1%positive [] (Some (Val v)) counter_db
      (D.wf_init [Decl 1%positive [] (OLat 1%positive)] []) (counter_put_allowed v)
      1%positive [] (Some (Val v)))).
    right. split; [reflexivity|]. split; [reflexivity|].
    change (D.combine counter_db 1%positive (D.old counter_db 1%positive [])
      (Some (Val v)) = Some (Val v)).
    rewrite counter_old_empty. reflexivity.
  Qed.

  Lemma counter_not_derivable : forall v f k,
    ~ derives V.prim (counter_program v) (D.view counter_db) f k.
  Proof.
    intros v f k Hderive. destruct Hderive as [f k Hrow|r s f k Hin Hbody Hactions].
    - eapply counter_empty. exact Hrow.
    - destruct Hin as [<-|[]]. cbn [counter_rule actions] in Hactions. inversion Hactions.
  Qed.

  (** All premises of F7 hold, but applying the rule produces an underivable row. *)
  Lemma F7_plan_counterexample : forall v,
    relational_fragment (counter_program v) = true /\ R.no_ids counter_db /\
    D.wf counter_db /\ counter_derived v counter_db /\
    In (counter_rule v) (rules V.t (counter_program v)) /\
    derivation_body V.prim (counter_program v) (D.view counter_db) (fun _ => None)
      (query V.t (counter_rule v)) /\
    ~ counter_derived v
      (R.apply (actions V.t (counter_rule v)) (fun _ => None) counter_db).
  Proof.
    intro v. split; [reflexivity|]. split; [exact counter_no_ids|].
    split; [apply D.wf_init|]. split.
    - intros f k o Hrow. exfalso. eapply counter_empty. exact Hrow.
    - split; [now left|]. split; [constructor|].
      intro Hderived. apply (counter_not_derivable v 1%positive []).
      eapply Hderived. apply counter_inserted.
  Qed.
End DerivationPlanCounterexample.

(** The same insertion is visible in the operations-only positive-value implementation. *)
Example derivation_plan_result_put :
  let p := Program positive [Decl 1 [] ORel]
    [Rule positive [] [Put 1 [] (Some (Lit 1%positive))]] in
  let db := PlanDatabase.init [Decl 1 [] (OLat 1)] [] in
  (relational_fragment p,
   fst (PlanDatabase.lookup 1 []
     (PlanRun.apply [Put 1 [] (Some (Lit 1%positive))] (fun _ => None) db))) =
  (true, Some (Some (val 1))).
Proof.
  vm_compute. reflexivity.
Qed.

(** * Repeated primitive filters

    An arbitrary post list may repeat one expensive primitive without charging its work
    again. The following certificate refutes the unrestricted filter bound for every
    fixed coefficient; checked plans retain their canonical post list. *)
Fixpoint duplicate_delay (n : nat) : option unit :=
  match n with
  | O => Some tt
  | S rest => duplicate_delay rest
  end.
TimeFun duplicate_delay.

Lemma duplicate_delay_result : forall n, duplicate_delay n = Some tt.
Proof.
  induction n as [|n IH]; cbn [duplicate_delay]; auto.
Qed.

Lemma duplicate_delay_clock : forall n, (N.of_nat n <= T_duplicate_delay n)%N.
Proof.
  induction n as [|n IH].
  - time_unfold T_duplicate_delay. lia.
  - time_unfold T_duplicate_delay. rewrite Nat2N.inj_succ. lia.
Qed.

Lemma duplicate_overhead : forall a b c : N, (a + b <= 1 + (c + (b + a)))%N.
Proof.
  intros a b c. lia.
Qed.

Module DuplicatePrimitiveValue <: VALUE_T.
  Definition t := unit.
  Definition encode (_ : t) := 1%positive.
  Definition eqb (_ _ : t) := true.
  Definition prim (p : positive) (_ : list t) : option t :=
    duplicate_delay (Pos.size_nat p * Pos.size_nat p).
  Definition merge (_ : positive) (_ _ : t) := tt.
  Definition bits (value : t) := Pos.size_nat (encode value).
  TimeFun encode.
  TimeFun eqb.
  TimeFun prim.
  TimeFun merge.
  Definition c_key := 1%N.
  Definition c_val := 1%N.
  Definition prim_work := T_prim.

  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [] []. reflexivity.
  Qed.

  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [] []. constructor. reflexivity.
  Qed.

  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof.
    reflexivity.
  Qed.

  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof.
    reflexivity.
  Qed.

  Lemma merge_idem : forall m a, merge m a a = a.
  Proof.
    intros m []. reflexivity.
  Qed.

  Lemma T_encode_le : forall value,
    (T_encode value <= c_key * N.of_nat (bits value + 1))%N.
  Proof.
    intros []. time_unfold T_encode. change (1 <= 2)%N. lia.
  Qed.

  Lemma T_eqb_le : forall a b,
    (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros [] []. time_unfold T_eqb. change (1 <= 2)%N. lia.
  Qed.

  Lemma T_prim_le : forall p xs, (T_prim p xs <= c_val * (prim_work p xs + 1))%N.
  Proof.
    intros p xs. unfold c_val, prim_work. lia.
  Qed.

  Lemma T_merge_le : forall m a b,
    (T_merge m a b <= c_val * N.of_nat (bits a + bits b + 1))%N.
  Proof.
    intros m [] []. time_unfold T_merge. change (1 <= 3)%N. lia.
  Qed.

  Lemma prim_result : forall p xs, prim p xs = Some tt.
  Proof.
    intros p xs. apply duplicate_delay_result.
  Qed.

  Lemma prim_clock : forall p xs,
    (N.of_nat (Pos.size_nat p) * N.of_nat (Pos.size_nat p) <= T_prim p xs)%N.
  Proof.
    intros p xs. pose proof (duplicate_delay_clock (Pos.size_nat p * Pos.size_nat p)) as Hdelay.
    time_unfold T_prim. rewrite Nat2N.inj_mul in Hdelay. lia.
  Qed.
End DuplicatePrimitiveValue.

Lemma duplicate_growth : forall coefficient width primitive actual : N,
  width = (16 * (coefficient + 1) + 1)%N ->
  (width * width <= primitive)%N ->
  ((2 * coefficient + 1) * primitive <= actual)%N ->
  ~ (actual <= coefficient * (2 * (2 * coefficient + 1) + 1) * (width + 1) +
    coefficient * primitive + coefficient * 2 + coefficient * 1)%N.
Proof.
  intros coefficient width primitive actual Hwidth Hprimitive Hactual Hbound.
  assert (Hscaled : ((coefficient + 1) * (width * width) <=
    (coefficient + 1) * primitive)%N).
  { apply N.mul_le_mono_l. exact Hprimitive. }
  subst width. nia.
Qed.

Module DuplicatePrimitiveCounterexample (I : INDEX_T DuplicatePrimitiveValue)
    (J : JOIN_T DuplicatePrimitiveValue I) (D : DATABASE_T DuplicatePrimitiveValue I).
  Module R := RunT DuplicatePrimitiveValue I J D.

  Definition duplicate_program (op : positive) : program unit :=
    Program unit [] [Rule unit [Prim unit op [] (Lit tt)] []].

  Definition duplicate_plan (count : nat) : cplan unit :=
    CPlan unit 0%N (JPlan 0 []) [] [] (repeat 0%nat count).

  Lemma duplicate_prim_holds : forall op t,
    prim_holds DuplicatePrimitiveValue.prim DuplicatePrimitiveValue.eqb t op [] (Lit tt) = true.
  Proof.
    intros op t. unfold prim_holds. cbn [trie_terms].
    rewrite DuplicatePrimitiveValue.prim_result. reflexivity.
  Qed.

  Lemma duplicate_prim_holds_clock : forall op t,
    (DuplicatePrimitiveValue.T_prim op [] <=
      T_prim_holds DuplicatePrimitiveValue.prim DuplicatePrimitiveValue.T_prim
        DuplicatePrimitiveValue.eqb DuplicatePrimitiveValue.T_eqb t op [] (Lit tt))%N.
  Proof.
    intros op t. time_unfold @T_prim_holds. time_simpl. time_cbn.
    rewrite DuplicatePrimitiveValue.prim_result. time_simpl. time_cbn. lia.
  Qed.

  Lemma duplicate_post_clock : forall count op t copies,
    (N.of_nat count * DuplicatePrimitiveValue.T_prim op [] <=
      T_keep_post DuplicatePrimitiveValue.prim DuplicatePrimitiveValue.T_prim
        DuplicatePrimitiveValue.eqb DuplicatePrimitiveValue.T_eqb
        [Prim unit op [] (Lit tt)] t (repeat 0%nat count) copies)%N.
  Proof.
    intro count. induction count as [|count IH]; intros op t copies.
    - time_unfold @T_keep_post. cbn [repeat]. lia.
    - pose proof (IH op t copies) as Htail.
      pose proof (duplicate_prim_holds_clock op t) as Hprim.
      time_unfold @T_keep_post. cbn [repeat nth_error].
      rewrite duplicate_prim_holds. rewrite Nat2N.inj_succ, N.mul_succ_l.
      eapply N.le_trans; [apply N.add_le_mono; [exact Htail | exact Hprim] | ].
      apply duplicate_overhead.
  Qed.

  Lemma duplicate_keep_clock : forall op count,
    (N.of_nat count * DuplicatePrimitiveValue.T_prim op [] <=
      R.T_keep (duplicate_program op) (duplicate_plan count)
        (R.bind_trie (duplicate_plan count) []))%N.
  Proof.
    intros op count. pose proof (duplicate_post_clock count op Empty []) as Hpost.
    unfold R.T_keep, duplicate_program, duplicate_plan, R.bind_trie.
    cbn [plan_rule_ix rules rule_at plan_post plan_vars bind_cells].
    time_unfold @T_rule_at. time_simpl. time_cbn.
    change (N.of_nat count * DuplicatePrimitiveValue.T_prim op [] <=
      1 + (1 + 1 + (1 + 0) + (1 + 1 +
        T_keep_post DuplicatePrimitiveValue.prim DuplicatePrimitiveValue.T_prim
        DuplicatePrimitiveValue.eqb DuplicatePrimitiveValue.T_eqb
        [Prim unit op [] (Lit tt)] Empty (repeat 0%nat count) [])))%N.
    lia.
  Qed.

  Lemma duplicate_post_work : forall op count,
    R.post_work (duplicate_program op) (duplicate_plan count) = (2 * count)%nat.
  Proof.
    intros op count. unfold R.post_work, duplicate_program, duplicate_plan, R.job_rule.
    cbn [rule_ix rules nth query post N.to_nat].
    induction count as [|count IH]; cbn [repeat fold_right nth_error atom_terms length app]; lia.
  Qed.

  Lemma duplicate_program_width : forall op,
    R.wbits (duplicate_program op) = Pos.size_nat op.
  Proof.
    intro op. unfold R.wbits, duplicate_program, program_words.
    cbn [decls rules flat_map app atom_words term_words fold_right DuplicatePrimitiveValue.encode].
    change (Nat.max (Pos.size_nat op) 1 = Pos.size_nat op).
    apply Nat.max_l. destruct op; cbn [Pos.size_nat]; lia.
  Qed.

  Lemma duplicate_rule_work : forall op count,
    R.rule_work (duplicate_program op) (duplicate_plan count) = 2%nat.
  Proof.
    reflexivity.
  Qed.

  Lemma duplicate_query_work : forall op count,
    query_prim_work DuplicatePrimitiveValue.prim_work
      (query unit (R.job_rule (duplicate_program op) (duplicate_plan count)))
      (R.env_of (duplicate_plan count) []) = DuplicatePrimitiveValue.T_prim op [].
  Proof.
    intros op count. cbn [query_prim_work R.job_rule duplicate_program duplicate_plan
      rule_ix rules nth query fold_right value_terms DuplicatePrimitiveValue.prim_work].
    apply N.add_0_r.
  Qed.

  (** Repeating one successful primitive refutes the bound for every coefficient. *)
  Lemma duplicate_filter_bound_refuted : forall coefficient : N, exists p c b,
    ~ (R.T_keep p c (R.bind_trie c b) <= coefficient * N.of_nat (R.post_work p c + 1) *
      N.of_nat (R.wbits p + fold_right
        (fun x n => Nat.max (cell_bits DuplicatePrimitiveValue.encode x) n) 0%nat b + 1) +
      coefficient * query_prim_work DuplicatePrimitiveValue.prim_work
        (query unit (R.job_rule p c)) (R.env_of c b) +
      coefficient * N.of_nat (R.rule_work p c) +
      coefficient * N.of_nat (fold_right
        (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat (var_of unit c) + 1))%N.
  Proof.
    intro coefficient.
    destruct (R.keep_width_key_exists (N.to_nat (16 * (coefficient + 1))%N)) as [op Hwidth].
    exists (duplicate_program op), (duplicate_plan (N.to_nat (2 * coefficient + 1)%N)), [].
    rewrite duplicate_post_work, duplicate_program_width, duplicate_rule_work, duplicate_query_work.
    cbn [duplicate_plan var_of fold_right].
    rewrite !Nat.add_0_r, !Nat2N.inj_add, !Nat2N.inj_mul, !N2Nat.id.
    pose proof (duplicate_keep_clock op (N.to_nat (2 * coefficient + 1)%N)) as Hkeep.
    rewrite N2Nat.id in Hkeep.
    pose proof (DuplicatePrimitiveValue.prim_clock op []) as Hprim.
    apply (f_equal N.of_nat) in Hwidth.
    rewrite Nat2N.inj_succ, N2Nat.id in Hwidth.
    eapply duplicate_growth; [lia | exact Hprim | exact Hkeep].
  Qed.
End DuplicatePrimitiveCounterexample.

Module DuplicatePrimitiveIndex := IndexT DuplicatePrimitiveValue.
Module DuplicatePrimitiveJoin := JoinT DuplicatePrimitiveValue DuplicatePrimitiveIndex.
Module DuplicatePrimitiveDatabase := DatabaseT DuplicatePrimitiveValue DuplicatePrimitiveIndex.
Module ClosedDuplicatePrimitive := DuplicatePrimitiveCounterexample DuplicatePrimitiveIndex
  DuplicatePrimitiveJoin DuplicatePrimitiveDatabase.
