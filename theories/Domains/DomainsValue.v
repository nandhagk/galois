(** * Open value dictionaries

    Values describe arbitrary concrete languages independently of their laws.
    For example, a client may interpret addition over integers or over words.
    Builds on: CostMonad, LatticeCore and LatticeConcrete. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
Import List.ListNotations Cost.Notations.

Module ValueAbs.

(** A value dictionary holds costed transfers and an abstract order. *)
Record t (A K G : Type) : Type := Make {
  lat : lattice A;
  top : A;
  op_c : K -> list A -> Cost.t A;
  back_c : K -> A -> list A -> Cost.t (list A);
  guard_c : G -> list A -> Cost.t (list A)
}.

Arguments lat {A K G}.
Arguments top {A K G}.
Arguments op_c {A K G}.
Arguments back_c {A K G}.
Arguments guard_c {A K G}.

(** Forward transfer observes the costed callback. *)
Definition op {A K G} (D : t A K G) k xs := Cost.value (op_c D k xs).

(** Backward transfer observes the costed callback. *)
Definition back {A K G} (D : t A K G) k a xs := Cost.value (back_c D k a xs).

(** Guard refinement observes the costed callback. *)
Definition guard {A K G} (D : t A K G) g xs := Cost.value (guard_c D g xs).

(** Pair operations retain both component callback charges. *)
Definition pair_lattice {A B} (LA : lattice A) (LB : lattice B) : lattice (A * B) :=
  {| leb_c := fun a b =>
       let* l := Cost.step ;; leb_c LA (fst a) (fst b) in
       let* r := Cost.step ;; leb_c LB (snd a) (snd b) in Cost.ret (l && r);
     bot := (bot LA, bot LB);
     join_c := fun a b =>
       let* l := Cost.step ;; join_c LA (fst a) (fst b) in
       Cost.map (pair l) (Cost.step ;; join_c LB (snd a) (snd b));
     widen_c := fun a b =>
       let* l := Cost.step ;; widen_c LA (fst a) (fst b) in
       Cost.map (pair l) (Cost.step ;; widen_c LB (snd a) (snd b));
     narrow_c := fun a b =>
       let* l := Cost.step ;; narrow_c LA (fst a) (fst b) in
       Cost.map (pair l) (Cost.step ;; narrow_c LB (snd a) (snd b)) |}.

(** Pairing results charges every reducer invocation and stops at the shorter list. *)
Fixpoint zip_reduce_c {A B} (red : A * B -> Cost.t (A * B)) (xs : list A) (ys : list B)
    : Cost.t (list (A * B)) :=
  match xs, ys with
  | x :: xs, y :: ys =>
    Cost.step ;;
    let* p := Cost.step ;; red (x, y) in
    Cost.map (cons p) (zip_reduce_c red xs ys)
  | _, _ => Cost.ret []
  end.

(** Products reduce forward, backward and guard results after component transfer. *)
Definition product {A B K G} (D : t A K G) (E : t B K G)
    (red : A * B -> Cost.t (A * B)) : t (A * B) K G :=
  {| lat := pair_lattice (lat D) (lat E);
     top := (top D, top E);
     op_c := fun k xs =>
       let* ls := map_c (fun p => Cost.ret (fst p)) xs in
       let* rs := map_c (fun p => Cost.ret (snd p)) xs in
       let* l := Cost.step ;; op_c D k ls in
       let* r := Cost.step ;; op_c E k rs in Cost.step ;; red (l, r);
     back_c := fun k a xs =>
       let* ls := map_c (fun p => Cost.ret (fst p)) xs in
       let* rs := map_c (fun p => Cost.ret (snd p)) xs in
       let* ls' := Cost.step ;; back_c D k (fst a) ls in
       let* rs' := Cost.step ;; back_c E k (snd a) rs in zip_reduce_c red ls' rs';
     guard_c := fun g xs =>
       let* ls := map_c (fun p => Cost.ret (fst p)) xs in
       let* rs := map_c (fun p => Cost.ret (snd p)) xs in
       let* ls' := Cost.step ;; guard_c D g ls in
       let* rs' := Cost.step ;; guard_c E g rs in zip_reduce_c red ls' rs' |}.

(** Renaming changes operator and guard vocabularies without changing the abstract carrier. *)
Definition rename {A K G K' G'} (fk : K' -> K) (fg : G' -> G) (D : t A K G)
    : t A K' G' :=
  {| lat := lat D;
     top := top D;
     op_c := fun k xs => Cost.step ;; op_c D (fk k) xs;
     back_c := fun k a xs => Cost.step ;; back_c D (fk k) a xs;
     guard_c := fun g xs => Cost.step ;; guard_c D (fg g) xs |}.

(** Choices enumerate the ordered Cartesian product and charge every copied list cell. *)
Fixpoint choices_c {A} (xss : list (list A)) : Cost.t (list (list A)) :=
  match xss with
  | [] => Cost.ret [[]]
  | xs :: xss =>
    Cost.step ;;
    let* tails := choices_c xss in
    fold_right_c (fun x rest =>
      let* rows := map_c (fun tail => Cost.ret (x :: tail)) tails in app_c rows rest) [] xs
  end.

(** Joining alternatives accounts for every lattice callback. *)
Definition join_all_c {A} (L : lattice A) (xs : list A) : Cost.t A :=
  fold_right_c (fun x a => Cost.step ;; join_c L x a) (bot L) xs.

(** Disjunction transfer takes its weak lattice and compaction policy as explicit parameters. *)
Definition disjunctive {A K G} (k : nat) (L : lattice (list A))
    (compact : nat -> list A -> Cost.t (list A)) (D : t A K G) : t (list A) K G :=
  {| lat := L;
     top := [top D];
     op_c := fun o xs =>
       let* rows := choices_c xs in
       let* results := map_c (fun row => Cost.step ;; op_c D o row) rows in
       Cost.step ;; compact k results;
     back_c := fun o a xs =>
       let* target := join_all_c (lat D) a in
       let* args := map_c (join_all_c (lat D)) xs in
       let* refined := Cost.step ;; back_c D o target args in
       map_c (fun a => Cost.ret [a]) refined;
     guard_c := fun g xs =>
       let* args := map_c (join_all_c (lat D)) xs in
       let* refined := Cost.step ;; guard_c D g args in
       map_c (fun a => Cost.ret [a]) refined |}.

End ValueAbs.

Module ValueSem.

(** Concrete operators may fail and guards describe complete operand lists. *)
Record t (C K G : Type) : Type := Make {
  eval : K -> list C -> option C;
  holds : G -> list C -> Prop
}.

Arguments eval {C K G}.
Arguments holds {C K G}.

End ValueSem.

(** Sound transfers retain every defined concrete result and every satisfying operand. *)
Record value_laws {A C K G} (D : ValueAbs.t A K G) (M : ValueSem.t C K G)
    (gam : concretisation A C) : Prop := {
  lat_ok : lattice_laws (ValueAbs.lat D);
  gamma_ok : concretisation_laws (ValueAbs.lat D) gam;
  bot_empty : forall c, ~ gamma gam (bot (ValueAbs.lat D)) c;
  top_full : forall c, gamma gam (ValueAbs.top D) c;
  op_sound : forall k fs cs c, Forall2 (gamma gam) fs cs ->
    ValueSem.eval M k cs = Some c -> gamma gam (ValueAbs.op D k fs) c;
  back_sound : forall k a fs cs c, Forall2 (gamma gam) fs cs ->
    ValueSem.eval M k cs = Some c -> gamma gam a c ->
    Forall2 (gamma gam) (ValueAbs.back D k a fs) cs;
  guard_sound : forall g fs cs, Forall2 (gamma gam) fs cs -> ValueSem.holds M g cs ->
    Forall2 (gamma gam) (ValueAbs.guard D g fs) cs;
  back_length : forall k a fs, length (ValueAbs.back D k a fs) = length fs;
  guard_length : forall g fs, length (ValueAbs.guard D g fs) = length fs
}.

Arguments lat_ok {A C K G D M gam}.
Arguments gamma_ok {A C K G D M gam}.
Arguments bot_empty {A C K G D M gam}.
Arguments top_full {A C K G D M gam}.
Arguments op_sound {A C K G D M gam}.
Arguments back_sound {A C K G D M gam}.
Arguments guard_sound {A C K G D M gam}.
Arguments back_length {A C K G D M gam}.
Arguments guard_length {A C K G D M gam}.

(** Refinement is structural and holds even for impossible operand lists. *)
Record value_refines {A K G} (D : ValueAbs.t A K G) : Prop := {
  back_refines : forall k a fs,
    Forall2 (fun x y => leb (ValueAbs.lat D) x y = true) (ValueAbs.back D k a fs) fs;
  guard_refines : forall g fs,
    Forall2 (fun x y => leb (ValueAbs.lat D) x y = true) (ValueAbs.guard D g fs) fs
}.

(** Related operand lists have identical lengths. *)
Theorem forall2_gamma_length {A C} (G : concretisation A C) xs ys :
  Forall2 (gamma G) xs ys -> length xs = length ys.
Proof.
  apply Forall2_length.
Qed.

(** A lawful value bottom denotes no concrete value. *)
Theorem value_laws_bot_gamma {A C K G} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) gam :
  value_laws D M gam -> forall c, ~ gamma gam (bot (ValueAbs.lat D)) c.
Proof.
  intros H c. exact (bot_empty H c).
Qed.

Create HintDb galois_gamma.
#[export] Hint Resolve op_sound back_sound guard_sound top_full : galois_gamma.
