(** * Rule plans, plan checking and saturation rounds

    The planner compiles each rule into join plans over shared index slots, the checker
    validates a plan against its program, a round joins, filters and applies the plans of a
    program, and a run drives rounds under its limits.
    For example, the rule [path(x, z) :- path(x, y), edge(y, z)] joins the slots
    [(path, [0; 1])] and [(edge, [0; 1])] on the join variable of [y].
    Builds on: RunSig, Sorts, the binary trie, the self-delimiting codes and the binary-fuel
    loop. *)

From Stdlib Require Import List PArith NArith Bool Relations.Relation_Operators.
From Stdlib Require Import PeanoNat.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Code Loop Trie.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model Sorts RunSig.

Import Lia.
Import List.ListNotations.

(** * Record readers *)

(** A reader takes one field of a plan record by one record elimination. *)
Definition plan_rule_ix {V : Type} (c : cplan V) : N :=
  match c with
  | CPlan _ ix _ _ _ _ => ix
  end.
TimeFun plan_rule_ix.

Definition plan_join {V : Type} (c : cplan V) : jplan :=
  match c with
  | CPlan _ _ j _ _ _ => j
  end.
TimeFun plan_join.

Definition plan_sources {V : Type} (c : cplan V) : list (source V) :=
  match c with
  | CPlan _ _ _ srcs _ _ => srcs
  end.
TimeFun plan_sources.

Definition plan_vars {V : Type} (c : cplan V) : list positive :=
  match c with
  | CPlan _ _ _ _ vars _ => vars
  end.
TimeFun plan_vars.

Definition plan_post {V : Type} (c : cplan V) : list nat :=
  match c with
  | CPlan _ _ _ _ _ post => post
  end.
TimeFun plan_post.

Definition compiled_slots {V : Type} (cp : compiled V) : list (positive * list nat) :=
  match cp with
  | Compiled _ sl _ _ => sl
  end.
TimeFun compiled_slots.

Definition compiled_naive {V : Type} (cp : compiled V) : list (cplan V) :=
  match cp with
  | Compiled _ _ nv _ => nv
  end.
TimeFun compiled_naive.

Definition compiled_semi {V : Type} (cp : compiled V) : list (cplan V) :=
  match cp with
  | Compiled _ _ _ sn => sn
  end.
TimeFun compiled_semi.

Definition limits_iter (lim : limits) : N :=
  match lim with
  | Limits it _ => it
  end.
TimeFun limits_iter.

Definition limits_ids (lim : limits) : N :=
  match lim with
  | Limits _ ids => ids
  end.
TimeFun limits_ids.

(** * Rule access and binding tries *)

(** The rule at a binary position walks the list with a binary countdown, and a position past
    the end gives the empty rule. *)
Fixpoint rule_at {V : Type} (n : N) (rs : list (rule V)) : rule V :=
  match rs with
  | [] => Rule V [] []
  | r :: rest =>
      match n with
      | N0 => r
      | Npos _ => rule_at (N.pred n) rest
      end
  end.
TimeFun rule_at.

(** The binary walk finds the rule that unary indexing names. *)
Lemma rule_at_nth : forall (V : Type) n (rs : list (rule V)),
  rule_at n rs = nth (N.to_nat n) rs (Rule V [] []).
Proof.
  intros V n rs. revert n.
  induction rs as [| r rest IH]; intro n.
  - destruct (N.to_nat n); reflexivity.
  - destruct n as [| p].
    + reflexivity.
    + cbn [rule_at]. rewrite IH, N2Nat.inj_pred.
      change (N.to_nat (Npos p)) with (Pos.to_nat p).
      destruct (Pos2Nat.is_succ p) as [m Hm]. rewrite Hm. reflexivity.
Qed.

(** The first binding of a name wins, as in [binding_env]. *)
Fixpoint bind_cells {V : Type} (vars : list positive) (cells : list (cell V))
    (t : ptrie (cell V)) : ptrie (cell V) :=
  match vars, cells with
  | x :: xs, c :: cs =>
      match trie_get x t with
      | Some _ => bind_cells xs cs t
      | None => bind_cells xs cs (PTrieCode.set x c t)
      end
  | _, _ => t
  end.
TimeFun bind_cells.

(** Binding onto a trie keeps its entries and adds the first binding of each new name. *)
Lemma bind_cells_get : forall (V : Type) vars (cells : list (cell V)) t x,
  trie_get x (bind_cells vars cells t) =
    match trie_get x t with
    | Some c => Some c
    | None => binding_env vars cells x
    end.
Proof.
  intros V vars. induction vars as [| v vs IH]; intros cells t x.
  - cbn [bind_cells binding_env]. destruct (trie_get x t); reflexivity.
  - destruct cells as [| c cs].
    + cbn [bind_cells binding_env]. destruct (trie_get x t); reflexivity.
    + cbn [bind_cells binding_env].
      destruct (Pos.eqb_spec x v) as [Hxv | Hxv].
      * subst v. destruct (trie_get x t) as [d |] eqn:Hget.
        -- rewrite IH, Hget. reflexivity.
        -- rewrite IH, PTrie.get_set_same. reflexivity.
      * destruct (trie_get v t) as [d |] eqn:Hget.
        -- apply IH.
        -- rewrite IH, PTrie.get_set_other by congruence. reflexivity.
Qed.

(** * Post filters *)

Definition cell_eqb {V : Type} (eqb : V -> V -> bool) (a b : cell V) : bool :=
  match a, b with
  | Id i, Id j => Pos.eqb i j
  | Val v, Val w => eqb v w
  | _, _ => false
  end.
TimeFun cell_eqb.

(** A term of a primitive atom names a value of the binding trie. *)
Definition trie_term {V : Type} (t : ptrie (cell V)) (x : term V) : option V :=
  match x with
  | Var y =>
      match trie_get y t with
      | Some (Val v) => Some v
      | _ => None
      end
  | Lit v => Some v
  end.
TimeFun trie_term.

Fixpoint trie_terms {V : Type} (t : ptrie (cell V)) (xs : list (term V)) : option (list V) :=
  match xs with
  | [] => Some []
  | x :: rest =>
      match trie_term t x with
      | Some v =>
          match trie_terms t rest with
          | Some vs => Some (v :: vs)
          | None => None
          end
      | None => None
      end
  end.
TimeFun trie_terms.

(** A primitive atom holds when its arguments are values and its result agrees with the
    primitive. The known result value is the first operand of the comparison. *)
Definition prim_holds {V : Type} (prim : positive -> list V -> option V)
    (eqb : V -> V -> bool) (t : ptrie (cell V)) (p : positive) (args : list (term V))
    (res : term V) : bool :=
  match trie_terms t args with
  | Some vs =>
      match prim p vs with
      | Some v =>
          match trie_term t res with
          | Some w => eqb w v
          | None => false
          end
      | None => false
      end
  | None => false
  end.
TimeFun prim_holds.

(** A later occurrence of a variable in one atom reads the next copy name of the plan, and the
    copy cell must equal the cell of the variable. The result is the unread copy names. *)
Fixpoint copies_ok {V : Type} (eqb : V -> V -> bool) (t : ptrie (cell V))
    (seen : ptrie unit) (xs : list (term V)) (copies : list positive)
    : option (list positive) :=
  match xs with
  | [] => Some copies
  | Lit _ :: rest => copies_ok eqb t seen rest copies
  | Var x :: rest =>
      match trie_get x seen with
      | Some _ =>
          match copies with
          | z :: more =>
              match trie_get z t, trie_get x t with
              | Some c, Some d =>
                  if cell_eqb eqb c d then copies_ok eqb t seen rest more else None
              | _, _ => None
              end
          | [] => None
          end
      | None => copies_ok eqb t (PTrieCode.set x tt seen) rest copies
      end
  end.
TimeFun copies_ok.

(** The post filter checks its listed atoms in order. It evaluates each primitive atom and
    compares the copies of each function atom. *)
Fixpoint keep_post {V : Type} (prim : positive -> list V -> option V) (eqb : V -> V -> bool)
    (q : list (atom V)) (t : ptrie (cell V)) (post : list nat) (copies : list positive)
    : bool :=
  match post with
  | [] => true
  | i :: rest =>
      match nth_error q i with
      | Some (Prim _ p args res) =>
          if prim_holds prim eqb t p args res then keep_post prim eqb q t rest copies
          else false
      | Some (Fun _ _ args res) =>
          match copies_ok eqb t Empty (args ++ option_list res) copies with
          | Some more => keep_post prim eqb q t rest more
          | None => false
          end
      | None => false
      end
  end.
TimeFun keep_post.

(** * Action terms *)

(** Variables bound by earlier actions shadow the binding environment. *)
Definition look {V : Type} (s : positive -> option (cell V)) (locals : ptrie (cell V))
    (x : positive) : option (cell V) :=
  match trie_get x locals with
  | Some c => Some c
  | None => s x
  end.
TimeFun look.

Definition term_cell {V : Type} (s : positive -> option (cell V)) (locals : ptrie (cell V))
    (t : term V) : option (cell V) :=
  match t with
  | Var x => look s locals x
  | Lit v => Some (Val v)
  end.
TimeFun term_cell.

Fixpoint term_cells {V : Type} (s : positive -> option (cell V)) (locals : ptrie (cell V))
    (ts : list (term V)) : option (list (cell V)) :=
  match ts with
  | [] => Some []
  | t :: rest =>
      match term_cell s locals t with
      | Some c =>
          match term_cells s locals rest with
          | Some cs => Some (c :: cs)
          | None => None
          end
      | None => None
      end
  end.
TimeFun term_cells.

Fixpoint term_values {V : Type} (s : positive -> option (cell V)) (locals : ptrie (cell V))
    (ts : list (term V)) : option (list V) :=
  match ts with
  | [] => Some []
  | t :: rest =>
      match term_cell s locals t with
      | Some (Val v) =>
          match term_values s locals rest with
          | Some vs => Some (v :: vs)
          | None => None
          end
      | _ => None
      end
  end.
TimeFun term_values.

Definition result_cell {V : Type} (s : positive -> option (cell V)) (locals : ptrie (cell V))
    (res : option (term V)) : option (option (cell V)) :=
  match res with
  | None => Some None
  | Some t =>
      match term_cell s locals t with
      | Some c => Some (Some c)
      | None => None
      end
  end.
TimeFun result_cell.

(** * Planning *)

(** Slots are identified by a self-delimiting code of the function and the permutation. *)
Fixpoint nat_code (n : nat) : positive :=
  match n with
  | O => xH
  | S m => xO (nat_code m)
  end.
TimeFun nat_code.

Definition slot_code (f : positive) (perm : list nat) : positive :=
  glue f (list_code nat_code perm).
TimeFun slot_code.

Fixpoint count_from (start len : nat) : list nat :=
  match len with
  | O => []
  | S len' => start :: count_from (S start) len'
  end.
TimeFun count_from.

(** The planner's slot state maps slot codes to slot numbers and keeps the slots reversed. *)
Inductive slot_state : Type :=
  | SlotState (table : ptrie N) (next : N) (rows : list (positive * list nat)).

(** A slot keeps the number of its first registration. *)
Definition add_slot (f : positive) (perm : list nat) (st : slot_state) : N * slot_state :=
  match st with
  | SlotState table next rows =>
      let key := slot_code f perm in
      match trie_get key table with
      | Some s => (s, st)
      | None => (next, SlotState (PTrieCode.set key next table) (N.succ next) ((f, perm) :: rows))
      end
  end.
TimeFun add_slot.

(** Each identifier function, at its first declaration, gets the slot of all its positions in
    declaration order. *)
Fixpoint full_slots (ds : list decl) (seen : ptrie unit) (st : slot_state) : slot_state :=
  match ds with
  | [] => st
  | Decl f ss o :: rest =>
      match trie_get f seen with
      | Some _ => full_slots rest seen st
      | None =>
          match o with
          | OId =>
              full_slots rest (PTrieCode.set f tt seen)
                (snd (add_slot f (count_from 0 (S (length ss))) st))
          | _ => full_slots rest (PTrieCode.set f tt seen) st
          end
      end
  end.
TimeFun full_slots.

Definition pos_max (a b : positive) : positive :=
  match Pos.compare a b with
  | Lt => b
  | _ => a
  end.
TimeFun pos_max.

Definition term_max {V : Type} (t : term V) (m : positive) : positive :=
  match t with
  | Var x => pos_max x m
  | Lit _ => m
  end.
TimeFun term_max.

Fixpoint terms_max {V : Type} (ts : list (term V)) (m : positive) : positive :=
  match ts with
  | [] => m
  | t :: rest => terms_max rest (term_max t m)
  end.
TimeFun terms_max.

(** The largest variable of a query bounds the names of its plan's real variables. *)
Fixpoint query_max {V : Type} (q : list (atom V)) (m : positive) : positive :=
  match q with
  | [] => m
  | Fun _ _ args res :: rest => query_max rest (terms_max (args ++ option_list res) m)
  | Prim _ _ args res :: rest => query_max rest (terms_max (res :: args) m)
  end.
TimeFun query_max.

(** Later occurrences of a variable in one function atom need copies. *)
Fixpoint term_copies {V : Type} (seen : ptrie unit) (ts : list (term V)) (n : nat) : nat :=
  match ts with
  | [] => n
  | Lit _ :: rest => term_copies seen rest n
  | Var x :: rest =>
      match trie_get x seen with
      | Some _ => term_copies seen rest (S n)
      | None => term_copies (PTrieCode.set x tt seen) rest n
      end
  end.
TimeFun term_copies.

Fixpoint query_copies {V : Type} (q : list (atom V)) (n : nat) : nat :=
  match q with
  | [] => n
  | Fun _ _ args res :: rest => query_copies rest (term_copies Empty (args ++ option_list res) n)
  | Prim _ _ _ _ :: rest => query_copies rest n
  end.
TimeFun query_copies.

(** The layout numbers the join variables of a rule. Copies come first, and real variables and
    literals follow in the order of their first positions. Its name lists are reversed. *)
Inductive var_layout : Type :=
  | VarLayout (names : ptrie nat) (copies mains : nat) (fresh : positive)
      (copy_names main_names : list positive).

(** Each atom position receives a join variable. A literal and the first query occurrence of a
    variable take the next main variable, a later occurrence in the same atom takes the next
    copy, and any other occurrence reuses its variable. *)
Fixpoint place_terms {V : Type} (base : nat) (ts : list (term V)) (pos : nat)
    (seen : ptrie unit) (lay : var_layout) (pairs : list (nat * nat))
    (lits : list (nat * V)) (copied : bool)
    : var_layout * list (nat * nat) * list (nat * V) * bool :=
  match ts with
  | [] => (lay, pairs, lits, copied)
  | t :: rest =>
      match lay with
      | VarLayout names nc nm fresh cn mn =>
          match t with
          | Lit v =>
              let j := base + nm in
              place_terms base rest (S pos) seen
                (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn))
                ((j, pos) :: pairs) ((j, v) :: lits) copied
          | Var x =>
              match trie_get x seen with
              | Some _ =>
                  place_terms base rest (S pos) seen
                    (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn)
                    ((nc, pos) :: pairs) lits true
              | None =>
                  match trie_get x names with
                  | Some j =>
                      place_terms base rest (S pos) (PTrieCode.set x tt seen) lay
                        ((j, pos) :: pairs) lits copied
                  | None =>
                      let j := base + nm in
                      place_terms base rest (S pos) (PTrieCode.set x tt seen)
                        (VarLayout (PTrieCode.set x j names) nc (S nm) fresh cn (x :: mn))
                        ((j, pos) :: pairs) lits copied
                  end
              end
          end
      end
  end.
TimeFun place_terms.

Fixpoint insert_pair (j pos : nat) (l : list (nat * nat)) : list (nat * nat) :=
  match l with
  | [] => [(j, pos)]
  | (k, q) :: rest =>
      if Nat.leb j k then (j, pos) :: l else (k, q) :: insert_pair j pos rest
  end.
TimeFun insert_pair.

(** Sorting the positions of an atom by join variable gives its column and its permutation. *)
Fixpoint sort_pairs (l : list (nat * nat)) : list (nat * nat) :=
  match l with
  | [] => []
  | (j, pos) :: rest => insert_pair j pos (sort_pairs rest)
  end.
TimeFun sort_pairs.

(** A planned function atom has a slot, a column and the literals of its positions. *)
Inductive atom_plan (V : Type) : Type :=
  | AtomPlan (slot : N) (col : list nat) (lits : list (nat * V)).

Arguments AtomPlan {V}.

(** Prim atoms and function atoms with copies enter the post filter in query order. *)
Fixpoint plan_atoms {V : Type} (base : nat) (q : list (atom V)) (ai : nat)
    (lay : var_layout) (st : slot_state) (outs : list (atom_plan V)) (post : list nat)
    : var_layout * slot_state * list (atom_plan V) * list nat :=
  match q with
  | [] => (lay, st, outs, post)
  | Prim _ _ _ _ :: rest => plan_atoms base rest (S ai) lay st outs (ai :: post)
  | Fun _ f args res :: rest =>
      let '(lay', pairs, lits, copied) :=
        place_terms base (args ++ option_list res) 0 Empty lay [] [] false in
      let sorted := sort_pairs pairs in
      let '(s, st') := add_slot f (map snd sorted) st in
      plan_atoms base rest (S ai) lay' st'
        (AtomPlan s (map fst sorted) (rev_append lits []) :: outs)
        (if copied then ai :: post else post)
  end.
TimeFun plan_atoms.

Fixpoint literal_cols {V : Type} (lits : list (nat * V)) (tail : list (list nat))
    : list (list nat) :=
  match lits with
  | [] => tail
  | (j, _) :: rest => [j] :: literal_cols rest tail
  end.
TimeFun literal_cols.

(** Each atom's column is followed by the columns of its literals in position order. *)
Fixpoint plan_cols {V : Type} (atoms : list (atom_plan V)) : list (list nat) :=
  match atoms with
  | [] => []
  | AtomPlan _ col lits :: rest => col :: literal_cols lits (plan_cols rest)
  end.
TimeFun plan_cols.

Fixpoint literal_sources {V : Type} (lits : list (nat * V)) (tail : list (source V))
    : list (source V) :=
  match lits with
  | [] => tail
  | (_, v) :: rest => Const V (Val v) :: literal_sources rest tail
  end.
TimeFun literal_sources.

Definition pivot_source {V : Type} (s : N) (pivot : option nat) : source V :=
  match pivot with
  | Some O => New V s
  | _ => All V s
  end.
TimeFun pivot_source.

Definition pivot_next (pivot : option nat) : option nat :=
  match pivot with
  | Some (S k) => Some k
  | _ => None
  end.
TimeFun pivot_next.

(** The atom at the pivot reads the new rows of its slot and every other atom reads all rows. *)
Fixpoint plan_srcs {V : Type} (atoms : list (atom_plan V)) (pivot : option nat)
    : list (source V) :=
  match atoms with
  | [] => []
  | AtomPlan s _ lits :: rest =>
      pivot_source s pivot :: literal_sources lits (plan_srcs rest (pivot_next pivot))
  end.
TimeFun plan_srcs.

(** A rule has one semi-naive plan for each function atom. *)
Fixpoint semi_plans {V : Type} (i : N) (j : jplan) (vars : list positive) (post : list nat)
    (atoms : list (atom_plan V)) (m : nat) (todo : list (atom_plan V)) : list (cplan V) :=
  match todo with
  | [] => []
  | _ :: rest =>
      CPlan V i j (plan_srcs atoms (Some m)) vars post ::
        semi_plans i j vars post atoms (S m) rest
  end.
TimeFun semi_plans.

(** A rule's naive plan and its semi-naive plans share one layout. *)
Definition plan_rule {V : Type} (i : N) (r : rule V) (st : slot_state)
    : slot_state * cplan V * list (cplan V) :=
  match r with
  | Rule _ q _ =>
      let base := query_copies q 0 in
      let '(lay, st', outs, post) :=
        plan_atoms base q 0 (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] [])
          st [] [] in
      match lay with
      | VarLayout _ _ nm _ cn mn =>
          let atoms := rev_append outs [] in
          let vars := rev_append cn (rev_append mn []) in
          let j := JPlan (base + nm) (plan_cols atoms) in
          let ps := rev_append post [] in
          (st', CPlan V i j (plan_srcs atoms None) vars ps, semi_plans i j vars ps atoms 0 atoms)
      end
  end.
TimeFun plan_rule.

Fixpoint plan_rules {V : Type} (rs : list (rule V)) (i : N) (st : slot_state)
    (naive semi : list (cplan V)) : slot_state * list (cplan V) * list (cplan V) :=
  match rs with
  | [] => (st, naive, semi)
  | r :: rest =>
      let '(st', c, cs) := plan_rule i r st in
      plan_rules rest (N.succ i) st' (c :: naive) (rev_append cs semi)
  end.
TimeFun plan_rules.

(** The full slots come first, and the rules follow in program order. *)
Definition plan_program {V : Type} (p : program V) : compiled V :=
  match p with
  | Program _ ds rs =>
      let '(st, naive, semi) :=
        plan_rules rs 0%N (full_slots ds Empty (SlotState Empty 0%N [])) [] [] in
      match st with
      | SlotState _ _ rows =>
          Compiled V (rev_append rows []) (rev_append naive []) (rev_append semi [])
      end
  end.
TimeFun plan_program.

(** * Checking *)

(** The first declaration of a name fixes its row width. *)
Fixpoint decl_widths (ds : list decl) (t : ptrie nat) : ptrie nat :=
  match ds with
  | [] => t
  | Decl f ss o :: rest =>
      match trie_get f t with
      | Some _ => decl_widths rest t
      | None =>
          let width := match o with
            | ORel => length ss
            | _ => S (length ss)
            end in
          decl_widths rest (PTrieCode.set f width t)
      end
  end.
TimeFun decl_widths.

(** A slot permutation lists distinct positions within the row width. *)
Fixpoint perm_ok (width : nat) (perm : list nat) (seen : ptrie unit) : bool :=
  match perm with
  | [] => true
  | i :: rest =>
      let key := nat_code i in
      match trie_get key seen with
      | Some _ => false
      | None =>
          if Nat.leb (S i) width then perm_ok width rest (PTrieCode.set key tt seen) else false
      end
  end.
TimeFun perm_ok.

(** The slot table maps the code of each valid slot to its first number and its contents. *)
Fixpoint slot_table (widths : ptrie nat) (sl : list (positive * list nat)) (next : N)
    (table : ptrie (N * (positive * list nat)))
    : option (ptrie (N * (positive * list nat))) :=
  match sl with
  | [] => Some table
  | (f, perm) :: rest =>
      match trie_get f widths with
      | Some width =>
          if perm_ok width perm Empty then
            let key := slot_code f perm in
            match trie_get key table with
            | Some _ => slot_table widths rest (N.succ next) table
            | None =>
                slot_table widths rest (N.succ next)
                  (PTrieCode.set key (next, (f, perm)) table)
            end
          else None
      | None => None
      end
  end.
TimeFun slot_table.

(** The names of a plan are distinct, and each names its join variable. *)
Fixpoint var_table (vars : list positive) (j : N) (t : ptrie N) : option (ptrie N) :=
  match vars with
  | [] => Some t
  | x :: rest =>
      match trie_get x t with
      | Some _ => None
      | None => var_table rest (N.succ j) (PTrieCode.set x j t)
      end
  end.
TimeFun var_table.

Fixpoint nat_n (n : nat) : N :=
  match n with
  | O => 0%N
  | S m => N.succ (nat_n m)
  end.
TimeFun nat_n.

Fixpoint nats_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => if Nat.eqb x y then nats_eqb xs ys else false
  | _, _ => false
  end.
TimeFun nats_eqb.

(** A column is nonempty, strictly increasing and below the variable count. *)
Fixpoint column_ok (n : nat) (lv : list nat) (prev : option nat) : bool :=
  match lv with
  | [] =>
      match prev with
      | Some _ => true
      | None => false
      end
  | l :: rest =>
      let above := match prev with
        | Some k => Nat.leb (S k) l
        | None => true
        end in
      if above then if Nat.leb (S l) n then column_ok n rest (Some l) else false else false
  end.
TimeFun column_ok.

(** Each position of an atom has a join variable. The first occurrence of a variable in the
    atom has the variable of its name, a later occurrence has the next copy, and a literal has
    the column of its constant source. The inverse table maps join variables to positions. *)
Fixpoint check_terms {V : Type} (eqb : V -> V -> bool) (names : ptrie N)
    (ts : list (term V)) (pos : nat) (seen : ptrie unit) (copy : N) (inv : ptrie nat)
    (srcs : list (source V)) (cols : list (list nat)) (copied : bool)
    : option (N * ptrie nat * list (source V) * list (list nat) * bool) :=
  match ts with
  | [] => Some (copy, inv, srcs, cols, copied)
  | Lit v :: rest =>
      match srcs, cols with
      | Const _ (Val w) :: srcs', [l] :: cols' =>
          if eqb w v then
            check_terms eqb names rest (S pos) seen copy
              (PTrieCode.set (N.succ_pos (nat_n l)) pos inv) srcs' cols' copied
          else None
      | _, _ => None
      end
  | Var x :: rest =>
      match trie_get x seen with
      | Some _ =>
          check_terms eqb names rest (S pos) seen (N.succ copy)
            (PTrieCode.set (N.succ_pos copy) pos inv) srcs cols true
      | None =>
          match trie_get x names with
          | Some j =>
              check_terms eqb names rest (S pos) (PTrieCode.set x tt seen) copy
                (PTrieCode.set (N.succ_pos j) pos inv) srcs cols copied
          | None => None
          end
      end
  end.
TimeFun check_terms.

(** The column of an atom reads its permutation from the inverse table and counts the distinct
    join variables that the plan uses. *)
Fixpoint column_perm (inv : ptrie nat) (lv : list nat) (used : ptrie unit) (count : N)
    : option (list nat * ptrie unit * N) :=
  match lv with
  | [] => Some ([], used, count)
  | l :: rest =>
      let key := N.succ_pos (nat_n l) in
      match trie_get key inv with
      | Some pos =>
          let count' := match trie_get key used with
            | Some _ => count
            | None => N.succ count
            end in
          match column_perm inv rest (PTrieCode.set key tt used) count' with
          | Some (perm, used', count'') => Some (pos :: perm, used', count'')
          | None => None
          end
      | None => None
      end
  end.
TimeFun column_perm.

Definition slot_matches (table : ptrie (N * (positive * list nat))) (f : positive)
    (perm : list nat) (s : N) : bool :=
  match trie_get (slot_code f perm) table with
  | Some (s', (f', perm')) =>
      if N.eqb s' s then if Pos.eqb f' f then nats_eqb perm' perm else false else false
  | None => false
  end.
TimeFun slot_matches.

Definition source_slot {V : Type} (newok : bool) (src : source V) : option N :=
  match src with
  | All _ s => Some s
  | New _ s => if newok then Some s else None
  | Const _ _ => None
  end.
TimeFun source_slot.

(** A function atom reads one slot source whose slot lays out its positions by join variable,
    and then the constant sources of its literals. *)
Definition check_atom {V : Type} (eqb : V -> V -> bool) (newok : bool) (names : ptrie N)
    (n : nat) (table : ptrie (N * (positive * list nat))) (f : positive) (ts : list (term V))
    (copy : N) (used : ptrie unit) (count : N) (srcs : list (source V))
    (cols : list (list nat))
    : option (N * ptrie unit * N * list (source V) * list (list nat) * bool) :=
  match srcs, cols with
  | src :: srcs', lv :: cols' =>
      match source_slot newok src with
      | Some s =>
          if column_ok n lv None then
            if Nat.eqb (length lv) (length ts) then
              match check_terms eqb names ts 0 Empty copy Empty srcs' cols' false with
              | Some (copy', inv, srcs'', cols'', copied) =>
                  match column_perm inv lv used count with
                  | Some (perm, used', count') =>
                      if slot_matches table f perm s then
                        Some (copy', used', count', srcs'', cols'', copied)
                      else None
                  | None => None
                  end
              | None => None
              end
            else None
          else None
      | None => None
      end
  | _, _ => None
  end.
TimeFun check_atom.

(** The query check returns the count of used join variables, the unread sources and columns,
    and the reversed post list that the query requires. *)
Fixpoint check_query {V : Type} (eqb : V -> V -> bool) (newok : bool) (names : ptrie N)
    (n : nat) (table : ptrie (N * (positive * list nat))) (q : list (atom V)) (ai : nat)
    (copy : N) (used : ptrie unit) (count : N) (srcs : list (source V))
    (cols : list (list nat)) (post : list nat)
    : option (N * list (source V) * list (list nat) * list nat) :=
  match q with
  | [] => Some (count, srcs, cols, post)
  | Prim _ _ _ _ :: rest =>
      check_query eqb newok names n table rest (S ai) copy used count srcs cols (ai :: post)
  | Fun _ f args res :: rest =>
      match check_atom eqb newok names n table f (args ++ option_list res) copy used count
          srcs cols with
      | Some (copy', used', count', srcs', cols', copied) =>
          check_query eqb newok names n table rest (S ai) copy' used' count' srcs' cols'
            (if copied then ai :: post else post)
      | None => None
      end
  end.
TimeFun check_query.

(** A plan names its rule, uses every join variable and lists the post filter of its query. *)
Definition check_cplan {V : Type} (eqb : V -> V -> bool) (newok : bool)
    (table : ptrie (N * (positive * list nat))) (i : N) (r : rule V) (c : cplan V) : bool :=
  match r, c with
  | Rule _ q _, CPlan _ ix (JPlan n cols) srcs vars post =>
      if N.eqb ix i then
        if Nat.eqb (length vars) n then
          match var_table vars 0 Empty with
          | Some names =>
              match check_query eqb newok names n table q 0 0 Empty 0 srcs cols [] with
              | Some (count, [], [], expected) =>
                  if N.eqb count (nat_n n) then nats_eqb (rev_append expected []) post
                  else false
              | _ => false
              end
          | None => false
          end
        else false
      else false
  end.
TimeFun check_cplan.

Fixpoint fun_count {V : Type} (q : list (atom V)) : nat :=
  match q with
  | [] => O
  | Fun _ _ _ _ :: rest => S (fun_count rest)
  | Prim _ _ _ _ :: rest => fun_count rest
  end.
TimeFun fun_count.

Fixpoint check_semis {V : Type} (eqb : V -> V -> bool)
    (table : ptrie (N * (positive * list nat))) (i : N) (r : rule V) (k : nat)
    (cs : list (cplan V)) : option (list (cplan V)) :=
  match k with
  | O => Some cs
  | S k' =>
      match cs with
      | [] => None
      | c :: rest =>
          if check_cplan eqb true table i r c then check_semis eqb table i r k' rest else None
      end
  end.
TimeFun check_semis.

(** Each rule has one naive plan and one semi-naive plan per function atom, in rule order. *)
Fixpoint check_rule_plans {V : Type} (eqb : V -> V -> bool)
    (table : ptrie (N * (positive * list nat))) (rs : list (rule V)) (i : N)
    (naive semi : list (cplan V)) : bool :=
  match rs, naive with
  | [], [] =>
      match semi with
      | [] => true
      | _ :: _ => false
      end
  | r :: rest, c :: naive' =>
      if check_cplan eqb false table i r c then
        match r with
        | Rule _ q _ =>
            match check_semis eqb table i r (fun_count q) semi with
            | Some semi' => check_rule_plans eqb table rest (N.succ i) naive' semi'
            | None => false
            end
        end
      else false
  | _, _ => false
  end.
TimeFun check_rule_plans.

(** The shape check validates the slots and then every plan against its rule. *)
Definition check_shape_with {V : Type} (eqb : V -> V -> bool) (p : program V)
    (cp : compiled V) : bool :=
  match p, cp with
  | Program _ ds rs, Compiled _ sl naive semi =>
      match slot_table (decl_widths ds Empty) sl 0 Empty with
      | Some table => check_rule_plans eqb table rs 0 naive semi
      | None => false
      end
  end.
TimeFun check_shape_with.

(** * Finite universes *)

(** Every tuple of a width over the listed values. *)
Fixpoint value_tuples {V : Type} (n : nat) (vs : list V) : list (list (cell V)) :=
  match n with
  | O => [[]]
  | S m => flat_map (fun v => map (fun k => Val v :: k) (value_tuples m vs)) vs
  end.

(** The first declaration of each relation name, with its arity. *)
Fixpoint relation_arities (ds : list decl) (seen : list positive) : list (positive * nat) :=
  match ds with
  | [] => []
  | Decl f ss o :: rest =>
      if existsb (Pos.eqb f) seen then relation_arities rest seen
      else
        match o with
        | ORel => (f, length ss) :: relation_arities rest (f :: seen)
        | _ => relation_arities rest (f :: seen)
        end
  end.

(** A value is kept unless an equal value was kept before it. *)
Definition distinct_values {V : Type} (eqb : V -> V -> bool) (vs : list V) : list V :=
  fold_left (fun acc v => if existsb (eqb v) acc then acc else v :: acc) vs [].

Definition program_literals {V : Type} (p : program V) : list V :=
  flat_map (fun t => match t with
    | Lit v => [v]
    | Var _ => []
    end) (program_terms p).

Module RunCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) <: RUN_OPS V I J D.
  Definition plan (p : program V.t) : compiled V.t := plan_program p.

  Definition check_shape (p : program V.t) (cp : compiled V.t) : bool :=
    check_shape_with V.eqb p cp.

  Definition check_plan (p : program V.t) (cp : compiled V.t) : bool :=
    check_program p && check_shape p cp.

  Definition load (p : program V.t) (cp : compiled V.t) : D.t :=
    D.init (decls V.t p) (compiled_slots cp).

  (** Actions run in order. A failed term lookup or primitive ends the application, and a union
      of two values changes nothing. *)
  Fixpoint apply_go (acts : list (action V.t)) (s : Model.env (V := V.t))
      (locals : ptrie (cell V.t)) (db : D.t) : D.t :=
    match acts with
    | [] => db
    | Make x f args :: rest =>
        match term_cells s locals args with
        | Some cells =>
            let '(i, db') := D.make f cells db in
            apply_go rest s (PTrieCode.set x (Id i) locals) db'
        | None => db
        end
    | Put f args res :: rest =>
        match term_cells s locals args, result_cell s locals res with
        | Some cells, Some out => apply_go rest s locals (D.put f cells out db)
        | _, _ => db
        end
    | Union a b :: rest =>
        match term_cell s locals a, term_cell s locals b with
        | Some (Id i), Some (Id j) => apply_go rest s locals (D.union i j db)
        | Some _, Some _ => apply_go rest s locals db
        | _, _ => db
        end
    | Let x p args :: rest =>
        match term_values s locals args with
        | Some vs =>
            match V.prim p vs with
            | Some v => apply_go rest s (PTrieCode.set x (Val v) locals) db
            | None => db
            end
        | None => db
        end
    end.

  Definition apply (acts : list (action V.t)) (s : Model.env (V := V.t)) (db : D.t) : D.t :=
    apply_go acts s Empty db.

  Definition bind_trie (c : cplan V.t) (b : list (cell V.t)) : ptrie (cell V.t) :=
    bind_cells (plan_vars c) b Empty.

  (** The post filter reads the copy names at the front of the plan's variables. *)
  Definition keep (p : program V.t) (c : cplan V.t) (t : ptrie (cell V.t)) : bool :=
    match rule_at (plan_rule_ix c) (rules V.t p) with
    | Rule _ q _ => keep_post V.prim V.eqb q t (plan_post c) (plan_vars c)
    end.

  Definition source_ix (db : D.t) (s : source V.t) : I.t :=
    match s with
    | All _ slot => D.index slot false db
    | New _ slot => D.index slot true db
    | Const _ c => I.insert [c] I.empty
    end.

  Definition plan_bindings (_ : compiled V.t) (c : cplan V.t) (db : D.t)
      : list (list (cell V.t)) :=
    J.run (plan_join c) (map (source_ix db) (plan_sources c)).

  Definition jobs (p : program V.t) (cp : compiled V.t) (nv : bool) (db : D.t)
      : list (cplan V.t * list (cell V.t)) :=
    flat_map (fun c => map (fun b => (c, b))
        (filter (fun b => keep p c (bind_trie c b)) (plan_bindings cp c db)))
      (if nv then compiled_naive cp else compiled_semi cp).

  (** Each job builds its binding trie once and applies the actions of its rule. *)
  Fixpoint apply_all (p : program V.t) (js : list (cplan V.t * list (cell V.t))) (db : D.t)
      : D.t :=
    match js with
    | [] => db
    | (c, b) :: rest =>
        let t := bind_trie c b in
        apply_all p rest
          (apply (actions V.t (rule_at (plan_rule_ix c) (rules V.t p)))
            (fun x => trie_get x t) db)
    end.

  Definition round (p : program V.t) (cp : compiled V.t) (nv : bool) (db : D.t) : D.t :=
    D.rebuild (apply_all p (jobs p cp nv db) db).

  (** A quiet semi-naive round is followed by a naive round, and a quiet naive round saturates. *)
  Definition driver (p : program V.t) (cp : compiled V.t) (lim : limits) (st : bool * D.t)
      : (bool * D.t) + (stop * D.t) :=
    let '(nv, db) := st in
    let next := round p cp nv db in
    if N.ltb (limits_ids lim) (D.ids next) then inr (IdLimit, next)
    else if andb nv (negb (D.changed next)) then inr (Saturated, next)
    else inl (negb (D.changed next), D.advance next).

  (** The final rebuild makes the result canonical even when the fuel is zero. *)
  Definition run (p : program V.t) (cp : compiled V.t) (lim : limits) (db : D.t)
      : stop * D.t :=
    match loopN (driver p cp lim) (limits_iter lim) (false, db) with
    | inl (_, final) => (IterLimit, D.rebuild final)
    | inr (st, final) => (st, D.rebuild final)
    end.
End RunCode.

Module Run (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) <: RUN V I J D.
  Include RunCode V I J D.
  Include RUN_SPEC V I J D.

  (** The cells on the edges below a node, down to the slot's tuple width. *)
  Fixpoint index_cells (fuel : nat) (ix : I.t) (n : positive) : list (cell V.t) :=
    match fuel with
    | O => []
    | S fuel' =>
        flat_map (fun c => c ::
            match I.child ix n c with
            | Some m => index_cells fuel' ix m
            | None => []
            end) (I.children ix n)
    end.

  (** The values stored in the full index of every slot from number [s] on. *)
  Fixpoint slot_values (db : D.t) (s : nat) (sl : list (positive * list nat)) : list V.t :=
    match sl with
    | [] => []
    | (_, perm) :: rest =>
        let ix := D.index (N.of_nat s) false db in
        flat_map (fun c => match c with
            | Val v => [v]
            | Id _ => []
            end) (index_cells (length perm) ix (I.root ix)) ++
          slot_values db (S s) rest
    end.

  (** The universe pairs each relation with every tuple of its arity over the distinct active
      values. *)
  Definition universe (p : program V.t) (db : D.t) : list (positive * list (cell V.t)) :=
    let vs := distinct_values V.eqb (program_literals p ++ slot_values db 0 (D.slots db)) in
    flat_map (fun fa => map (fun k => (fst fa, k)) (value_tuples (snd fa) vs))
      (relation_arities (decls V.t p) []).

  Definition active_value (p : program V.t) (db : D.t) (v : V.t) : Prop :=
    In (Lit v) (program_terms p) \/
    exists s u, N.to_nat s < length (D.slots db) /\ I.mem (D.index s false db) u /\
      In (Val v) u.

  Definition herbrand (p : program V.t) (db : D.t) : nat := length (universe p db).

  Lemma universe_spec : forall p db, D.wf db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    NoDup (universe p db) /\
    forall f k, In (f, k) (universe p db) <->
      program_kind p f = Some ORel /\
      (exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length k = length (arg_sorts d)) /\
      Forall (fun c => exists v, c = Val v /\ active_value p db v) k.
  Proof. Admitted. (* STUB *)

  Lemma herbrand_spec : forall p db, herbrand p db = length (universe p db).
  Proof.
    reflexivity.
  Qed.

  Lemma check_plan_scope : forall p cp r pre a rest x, plans_ok p cp ->
    In r (rules V.t p) -> actions V.t r = pre ++ a :: rest ->
    In x (flat_map term_vars (action_terms a)) ->
    In x (flat_map atom_vars (query V.t r) ++ flat_map action_binds pre).
  Proof. Admitted. (* STUB *)

  Lemma check_plan_arities : forall p cp r a, plans_ok p cp ->
    In r (rules V.t p) -> In a (actions V.t r) ->
    match a with
    | Make _ f args | Put f args _ =>
      exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length args = length (arg_sorts d)
    | _ => True
    end.
  Proof. Admitted. (* STUB *)

  Lemma check_plan_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) ->
    exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
      NoDup perm /\ Forall (fun i => i <
        length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end) perm.
  Proof. Admitted. (* STUB *)

  Lemma plans_ok_sorted : forall p cp, plans_ok p cp -> program_ok p.
  Proof. Admitted. (* STUB *)

  Lemma plan_checked : forall p, program_ok p -> plans_ok p (plan p).
  Proof. Admitted. (* STUB *)

  Lemma plan_full_slots : forall p f ss, program_kind p f = Some OId ->
    program_sorts p f = Some ss ->
    In (f, seq 0 (S (length ss))) (Syntax.slots V.t (plan p)).
  Proof. Admitted. (* STUB *)

  Lemma load_spec : forall p cp,
    load p cp = D.init (decls V.t p) (Syntax.slots V.t cp).
  Proof.
    reflexivity.
  Qed.

  Lemma run_wf : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)) /\
    loaded p cp (snd (run p cp lim db)).
  Proof. Admitted. (* STUB *)

  Lemma run_grows : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    grows db (snd (run p cp lim db)).
  Proof. Admitted. (* STUB *)

  Lemma run_sat : forall p cp lim db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> loaded p cp db -> valid_sorted V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run p cp lim db))).
  Proof. Admitted. (* STUB *)

  Lemma run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    run p cp lim db = (Saturated, db') -> closed V.prim V.merge p (D.view db').
  Proof. Admitted. (* STUB *)

  Lemma run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run p cp lim db))) f k o -> derives V.prim p (D.view db) f k.
  Proof. Admitted. (* STUB *)

  Lemma run_least : forall p cp lim db db', plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> run p cp lim db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      (forall f, kind w f = program_kind p f) -> view_sorted (program_sorts p) w ->
      includes (D.view db') w.
  Proof. Admitted. (* STUB *)

  Lemma run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> prim_free p = true -> no_ids db ->
    N.to_nat (max_iter lim) >= 2 * herbrand p db + 2 ->
    fst (run p cp lim db) = Saturated.
  Proof. Admitted. (* STUB *)

  Lemma run_limits : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    fst (run p cp lim db) = IdLimit -> (D.ids (snd (run p cp lim db)) > max_ids lim)%N.
  Proof. Admitted. (* STUB *)

End Run.

Module RunT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    <: RUN_ALL V I J D.
  Include Run V I J D.
  TimeFun plan.
  TimeFun check_shape.
  TimeFun check_plan.
  TimeFun load.
  TimeFun apply_go.
  TimeFun apply.
  TimeFun bind_trie.
  TimeFun keep.
  TimeFun source_ix.
  TimeFun plan_bindings.
  TimeFun jobs.
  TimeFun apply_all.
  TimeFun round.
  TimeFun driver.
  TimeFun run.
  Definition trace (p : program V.t) (cp : compiled V.t) (lim : limits) (db : D.t)
      : list (bool * D.t) :=
    driver_trace (driver p cp lim) (N.to_nat (max_iter lim)) (false, db).
  Definition job_rule (p : program V.t) (c : cplan V.t) : rule V.t :=
    nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []).
  (** Post work counts the position and the terms of each listed atom. *)
  Definition post_work (p : program V.t) (c : cplan V.t) : nat :=
    fold_right (fun i n => i + 1 +
      match nth_error (query V.t (job_rule p c)) i with
      | Some a => length (atom_terms a)
      | None => 0
      end + n) 0 (post V.t c).
  (** Finding the rule of a plan walks the rule list with a binary counter. *)
  Definition rule_work (p : program V.t) (c : cplan V.t) : nat :=
    (length (rules V.t p) + 1) * (N.size_nat (rule_ix V.t c) + 1).
  Definition round_work (p : program V.t) (cp : compiled V.t) (nv : bool) (db : D.t) : nat :=
    length (Syntax.slots V.t cp) +
      fold_right Nat.add 0 (map (fun c =>
        (J.work (join V.t c) (map (source_index db) (sources V.t c)) +
          length (sources V.t c) + 2) *
          (nvars (join V.t c) + 1) * (nvars (join V.t c) + 1) +
        length (bindings cp c db) *
          (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat (var_of V.t c) +
           post_work p c + rule_work p c + 1 +
           fold_right (fun a n => match a with
             | Make _ f args | Put f args _ => (length args + 2) * (length args + 2) *
                 (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1) + n
             | Union _ _ => 1 + n
             | Let _ _ args => length args + 1 + n
             end) 0 (actions V.t (nth (N.to_nat (rule_ix V.t c)) (rules V.t p)
               (Rule V.t [] [])))) +
        fold_right Nat.add 0 (map (fun binding =>
          let r := nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []) in
          N.to_nat (query_prim_work V.prim_work (query V.t r) (env_of c binding) +
            action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r)
              (env_of c binding))%N)
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)).
  Definition size_program (p : program V.t) : nat := program_bits p.
  Definition size_compiled (cp : compiled V.t) : nat :=
    fold_right (fun sl n => Pos.size_nat (fst sl) +
        fold_right (fun i m => i + 1 + m) 0 (snd sl) + 1 + n) 0 (Syntax.slots V.t cp) +
      fold_right (fun c n => N.size_nat (rule_ix V.t c) + nvars (join V.t c) +
        fold_right (fun col m => fold_right (fun i k => i + 1 + k) 0 col + 1 + m)
          0 (cols (join V.t c)) +
        fold_right (fun src m => match src with
          | All _ i | New _ i => N.size_nat i + 1 + m
          | Const _ value => cell_bits V.encode value + 1 + m
          end) 0 (sources V.t c) +
        fold_right (fun x m => Pos.size_nat x + 1 + m) 0 (var_of V.t c) +
        fold_right (fun i m => i + 1 + m) 0 (post V.t c) + 1 + n)
        0 (naive V.t cp ++ seminaive V.t cp).
  Definition wbits (p : program V.t) : nat :=
    fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Definition c_run : N :=
    (1024 * 4096 * (D.c_db + I.c_ix + J.c_join + V.c_val + V.c_key +
      PTrieT.c_trie + 1))%N.
  Lemma size_compiled_spec : forall cp,
    size_compiled cp =
      fold_right (fun sl n => Pos.size_nat (fst sl) +
        fold_right (fun i m => i + 1 + m) 0 (snd sl) + 1 + n) 0 (Syntax.slots V.t cp) +
      fold_right (fun c n => N.size_nat (rule_ix V.t c) + nvars (join V.t c) +
        fold_right (fun col m => fold_right (fun i k => i + 1 + k) 0 col + 1 + m)
          0 (cols (join V.t c)) +
        fold_right (fun src m => match src with
          | All _ i | New _ i => N.size_nat i + 1 + m
          | Const _ value => cell_bits V.encode value + 1 + m
          end) 0 (sources V.t c) +
        fold_right (fun x m => Pos.size_nat x + 1 + m) 0 (var_of V.t c) +
        fold_right (fun i m => i + 1 + m) 0 (post V.t c) + 1 + n)
        0 (naive V.t cp ++ seminaive V.t cp).
  Proof.
    reflexivity.
  Qed.

  Lemma wbits_spec : forall p,
    wbits p = fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Proof.
    reflexivity.
  Qed.

  (** Stored slots charge the bits of their name and the number of their positions. *)
  Definition run_slots_size (sl : list (positive * list nat)) : nat :=
    fold_right (fun s n => Pos.size_nat (fst s) + length (snd s) + 1 + n) 0 sl.

  Definition run_slot_state_size (st : slot_state) : nat :=
    match st with
    | SlotState _ _ rows => run_slots_size rows
    end.

  (** Accumulating a reversed list preserves the sum of its slot charges. *)
  Lemma run_slots_size_rev_append : forall xs ys,
    run_slots_size (rev_append xs ys) = run_slots_size xs + run_slots_size ys.
  Proof.
    induction xs as [| [f perm] xs IH]; intro ys.
    - reflexivity.
    - cbn [rev_append]. rewrite IH.
      change (run_slots_size xs +
        (Pos.size_nat f + length perm + 1 + run_slots_size ys) =
        Pos.size_nat f + length perm + 1 + run_slots_size xs + run_slots_size ys).
      lia.
  Qed.

  (** Registering a slot either reuses it or adds exactly its own charge. *)
  Lemma run_add_slot_size : forall f perm st,
    run_slot_state_size (snd (add_slot f perm st)) <=
      run_slot_state_size st + Pos.size_nat f + length perm + 1.
  Proof.
    intros f perm [table next rows]. unfold add_slot.
    destruct (trie_get (slot_code f perm) table).
    - change (run_slots_size rows <=
        run_slots_size rows + Pos.size_nat f + length perm + 1). lia.
    - change (Pos.size_nat f + length perm + 1 + run_slots_size rows <=
        run_slots_size rows + Pos.size_nat f + length perm + 1). lia.
  Qed.

  (** Counting consecutive positions allocates exactly the requested number of positions. *)
  Lemma run_count_from_length : forall len start,
    length (count_from start len) = len.
  Proof.
    induction len as [| len IH]; intro start; cbn [count_from length].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (** Insertion adds one position to a sorted list of pairs. *)
  Lemma run_insert_pair_length : forall pairs j pos,
    length (insert_pair j pos pairs) = S (length pairs).
  Proof.
    induction pairs as [| [k q] pairs IH]; intros j pos; cbn [insert_pair length].
    - reflexivity.
    - destruct (Nat.leb j k); cbn [length]; [reflexivity|].
      rewrite IH. reflexivity.
  Qed.

  (** Sorting positions preserves their number. *)
  Lemma run_sort_pairs_length : forall pairs,
    length (sort_pairs pairs) = length pairs.
  Proof.
    induction pairs as [| [j pos] pairs IH]; cbn [sort_pairs length].
    - reflexivity.
    - rewrite run_insert_pair_length, IH. reflexivity.
  Qed.

  (** Every term contributes one position pair to the layout. *)
  Lemma run_place_terms_length : forall base ts pos seen lay pairs lits copied,
    length (snd (fst (fst (@place_terms V.t base ts pos seen lay pairs lits copied)))) =
      length ts + length pairs.
  Proof.
    intros base ts. induction ts as [| [x | v] ts IH];
      intros pos seen [names nc nm fresh cn mn] pairs lits copied.
    - reflexivity.
    - cbn [place_terms]. destruct (trie_get x seen).
      + rewrite IH. cbn [length]. lia.
      + destruct (trie_get x names); rewrite IH; cbn [length]; lia.
    - cbn [place_terms]. rewrite IH. cbn [length]. lia.
  Qed.

  (** The number of term positions is bounded by their syntax charge. *)
  Lemma run_terms_length_bits : forall ts : list (term V.t),
    length ts <= terms_bits ts.
  Proof.
    induction ts as [| t ts IH].
    - change (0 <= 0). lia.
    - change (S (length ts) <= term_bits t + terms_bits ts).
      destruct t as [x | v]; unfold term_bits; lia.
  Qed.

  (** An optional result contributes at most its syntax charge. *)
  Lemma run_result_length_bits : forall res : option (term V.t),
    length (option_list res) <= result_bits res.
  Proof.
    intros [[x | v] |]; cbn [option_list length result_bits term_bits]; lia.
  Qed.

  (** Planning a query adds at most its syntax charge to the stored slots. *)
  Lemma run_plan_atoms_size : forall base q ai lay st outs post,
    run_slot_state_size
      (snd (fst (fst (@plan_atoms V.t base q ai lay st outs post)))) <=
      run_slot_state_size st + fold_right (fun a n => atom_bits a + n) 0 q.
  Proof.
    intros base q. induction q as [| [f args res | op args res] q IH];
      intros ai lay st outs post.
    - cbn [plan_atoms fst snd fold_right]. lia.
    - cbn [plan_atoms].
      destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
        as [[[lay' pairs] lits] copied] eqn:Hterms.
      destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'] eqn:Hslot.
      pose proof (run_place_terms_length base (args ++ option_list res) 0 Empty
        lay [] [] false) as Hlength.
      rewrite Hterms in Hlength. cbn [fst snd length] in Hlength.
      pose proof (run_add_slot_size f (map snd (sort_pairs pairs)) st) as Hsize.
      rewrite Hslot in Hsize. cbn [snd] in Hsize.
      rewrite length_map, run_sort_pairs_length, Hlength, length_app in Hsize.
      pose proof (IH (S ai) lay' st' (AtomPlan s (map fst (sort_pairs pairs))
        (rev_append lits []) :: outs) (if copied then ai :: post else post)) as Htail.
      pose proof (run_terms_length_bits args) as Hargs.
      pose proof (run_result_length_bits res) as Hres.
      cbn [fold_right atom_bits]. lia.
    - cbn [plan_atoms fold_right atom_bits].
      pose proof (IH (S ai) lay st outs (ai :: post)). lia.
  Qed.

  (** Planning one rule adds at most the charge of that rule. *)
  Lemma run_plan_rule_size : forall i r st,
    run_slot_state_size (fst (fst (@plan_rule V.t i r st))) <=
      run_slot_state_size st + rule_bits r.
  Proof.
    intros i [q acts] st. unfold plan_rule.
    pose proof (run_plan_atoms_size (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []) as Hsize.
    destruct (plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay st'] outs] post] eqn:Hplan.
    cbn [fst snd] in Hsize.
    destruct lay as [names nc nm fresh cn mn].
    change (run_slot_state_size st' <= run_slot_state_size st +
      (fold_right (fun a n => atom_bits a + n) 0 q +
       fold_right (fun a n => action_bits a + n) 0 acts + 1)).
    lia.
  Qed.

  (** The rule traversal sums the charge of its rules. *)
  Lemma run_plan_rules_size : forall rs i st naive semi,
    run_slot_state_size (fst (fst (@plan_rules V.t rs i st naive semi))) <=
      run_slot_state_size st + fold_right (fun r n => rule_bits r + n) 0 rs.
  Proof.
    induction rs as [| r rs IH]; intros i st naive semi.
    - cbn [plan_rules fst run_slot_state_size fold_right]. lia.
    - cbn [plan_rules].
      pose proof (run_plan_rule_size i r st) as Hsize.
      destruct (plan_rule i r st) as [[st' c] cs] eqn:Hrule.
      cbn [fst] in Hsize.
      pose proof (IH (N.succ i) st' (c :: naive) (rev_append cs semi)) as Htail.
      cbn [fold_right]. lia.
  Qed.

  (** Declared full slots cost at most twice the charge of their declarations. *)
  Lemma run_full_slots_size : forall ds seen st,
    run_slot_state_size (full_slots ds seen st) <=
      run_slot_state_size st + 2 * fold_right (fun d n => decl_bits d + n) 0 ds.
  Proof.
    induction ds as [| [f ss out] ds IH]; intros seen st.
    - cbn [full_slots fold_right]. lia.
    - cbn [full_slots]. destruct (trie_get f seen).
      + pose proof (IH seen st). cbn [fold_right decl_bits name arg_sorts]. lia.
      + destruct out.
        * pose proof (IH (PTrieCode.set f tt seen) st).
          cbn [fold_right decl_bits name arg_sorts]. lia.
        * pose proof (IH (PTrieCode.set f tt seen)
            (snd (add_slot f (count_from 0 (S (length ss))) st))) as Htail.
          pose proof (run_add_slot_size f (count_from 0 (S (length ss))) st) as Hsize.
          rewrite run_count_from_length in Hsize.
          cbn [fold_right decl_bits name arg_sorts].
          change (decl_bits (Decl f ss OId)) with (Pos.size_nat f + length ss + 1).
          lia.
        * pose proof (IH (PTrieCode.set f tt seen) st).
          cbn [fold_right decl_bits name arg_sorts]. lia.
  Qed.

  (** The planner's stored slot charge is linear in the program syntax. *)
  Lemma run_plan_slots_size : forall p,
    run_slots_size (Syntax.slots V.t (plan p)) <= 2 * (size_program p + 1).
  Proof.
    intros [ds rs]. unfold plan, plan_program.
    pose proof (run_full_slots_size ds Empty (SlotState Empty 0 [])) as Hfull.
    pose proof (run_plan_rules_size rs 0
      (full_slots ds Empty (SlotState Empty 0 [])) [] []) as Hrules.
    destruct (plan_rules rs 0 (full_slots ds Empty (SlotState Empty 0 [])) [] [])
      as [[[table next rows] nv] sn] eqn:Hplan.
    change (run_slots_size rows <=
      run_slot_state_size (full_slots ds Empty (SlotState Empty 0 [])) +
      fold_right (fun r n => rule_bits r + n) 0 rs) in Hrules.
    change (run_slot_state_size (full_slots ds Empty (SlotState Empty 0 [])) <=
      2 * fold_right (fun d n => decl_bits d + n) 0 ds) in Hfull.
    cbn [Syntax.slots]. rewrite run_slots_size_rev_append.
    change (run_slots_size rows + 0 <=
      2 * (fold_right (fun d n => decl_bits d + n) 0 ds +
        fold_right (fun r n => rule_bits r + n) 0 rs + 1 + 1)).
    lia.
  Qed.

  (** A position list charges the unary size of each stored position. *)
  Definition run_positions_size (positions : list nat) : nat :=
    fold_right (fun i n => i + 1 + n) 0 positions.

  (** A unary position code has one bit beyond its position. *)
  Lemma run_nat_code_bits : forall n, Pos.size_nat (nat_code n) = n + 1.
  Proof.
    induction n as [| n IH]; cbn [nat_code Pos.size_nat]; lia.
  Qed.

  (** Constructing a position code visits each unary constructor once. *)
  Lemma run_nat_code_time : forall n,
    (T_nat_code n <= N.of_nat (n + 1))%N.
  Proof.
    induction n as [| n IH]; time_unfold T_nat_code; lia.
  Qed.

  (** The self-delimiting position list has at most twice its unary input charge. *)
  Lemma run_nat_codes_bits : forall positions,
    Pos.size_nat (list_code nat_code positions) <= 2 * run_positions_size positions + 1.
  Proof.
    induction positions as [| i positions IH].
    - cbn [list_code Pos.size_nat run_positions_size fold_right]. lia.
    - cbn [list_code]. rewrite glue_bits, run_nat_code_bits.
      change (run_positions_size (i :: positions)) with (i + 1 + run_positions_size positions).
      lia.
  Qed.

  (** Encoding a list of positions is linear in their unary input charge. *)
  Lemma run_nat_codes_time : forall positions,
    (T_list_code nat_code T_nat_code positions <=
      4 * N.of_nat (run_positions_size positions) + 1)%N.
  Proof.
    induction positions as [| i positions IH].
    - time_unfold @T_list_code. cbn [run_positions_size fold_right]. lia.
    - pose proof (run_nat_code_time i) as Hcode.
      pose proof (T_glue_le (nat_code i) (list_code nat_code positions)) as Hglue.
      unfold c_glue in Hglue. rewrite run_nat_code_bits in Hglue.
      time_unfold @T_list_code.
      change (run_positions_size (i :: positions)) with (i + 1 + run_positions_size positions).
      lia.
  Qed.

  (** A slot code charges the name's bits and its unary position list. *)
  Lemma run_slot_code_bits : forall f positions,
    Pos.size_nat (slot_code f positions) <=
      2 * (Pos.size_nat f + run_positions_size positions + 1).
  Proof.
    intros f positions. unfold slot_code. rewrite glue_bits.
    pose proof (run_nat_codes_bits positions). lia.
  Qed.

  (** Constructing a slot code is linear in the same charge. *)
  Lemma run_slot_code_time : forall f positions,
    (T_slot_code f positions <=
      8 * N.of_nat (Pos.size_nat f + run_positions_size positions + 1))%N.
  Proof.
    intros f positions.
    pose proof (run_nat_codes_time positions) as Hpositions.
    pose proof (T_glue_le f (list_code nat_code positions)) as Hglue.
    unfold c_glue in Hglue. time_unfold T_slot_code.
    change (T_list_code nat_code (fun n => T_nat_code n) positions) with
      (T_list_code nat_code T_nat_code positions).
    lia.
  Qed.

  Lemma T_plan_le : forall p,
    (T_plan p <= c_run * N.of_nat (size_program p + 1) * N.of_nat (size_program p + 1) *
      N.of_nat (size_program p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma plan_slots_le : forall p,
    (N.of_nat (fold_right (fun s n =>
      (Pos.size_nat (fst s) + length (snd s) + 1 + n)%nat) 0%nat
      (Syntax.slots V.t (plan p))) <=
      c_run * N.of_nat (size_program p + 1) * N.of_nat (size_program p + 1) *
        N.of_nat (size_program p + 1))%N.
  Proof.
    intro p. pose proof (run_plan_slots_size p) as Hslots.
    assert (HslotsN : (N.of_nat (run_slots_size (Syntax.slots V.t (plan p))) <=
      N.of_nat (2 * (size_program p + 1)))%N) by lia.
    rewrite Nat2N.inj_mul in HslotsN.
    change (N.of_nat (run_slots_size (Syntax.slots V.t (plan p))) <=
      c_run * N.of_nat (size_program p + 1) * N.of_nat (size_program p + 1) *
        N.of_nat (size_program p + 1))%N.
    assert (Hconstant : (2 <= c_run)%N) by (unfold c_run; lia).
    assert (Hpositive : (1 <= N.of_nat (size_program p + 1))%N) by lia.
    nia.
  Qed.

  Lemma T_load_le : forall p cp,
    (T_load p cp <= D.T_init (decls V.t p) (Syntax.slots V.t cp) + c_run)%N.
  Proof.
    intros [ds rs] [sl nv sn].
    assert (Hconstant : (3 <= c_run)%N) by (unfold c_run; lia).
    time_unfold T_load.
    unfold T_decls, T_compiled_slots, decls, compiled_slots, Syntax.slots.
    time_cbn. lia.
  Qed.

  Lemma T_run_le : forall B U p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (snd (run p cp lim db)) <= B)%N -> D.unit (snd (run p cp lim db)) <= U ->
    (T_run p cp lim db <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        (fold_right N.add 0 (map (fun start =>
          N.of_nat (round_work p cp (fst start) (snd start) + 1)) (trace p cp lim db)) +
         N.of_nat (D.pending db + 1)) +
      c_run * N.of_nat (N.size_nat (max_iter lim) + 1) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_check_plan_le : forall p cp,
    (T_check_plan p cp <= c_run * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition query_vars (r : rule V.t) : list positive := flat_map atom_vars (query V.t r).
  Fixpoint apply_jobs (p : program V.t) (js : list (cplan V.t * list (cell V.t)))
      (db : D.t) : D.t :=
    match js with
    | [] => db
    | (c, b) :: rest =>
        apply_jobs p rest
          (apply (actions V.t (job_rule p c)) (fun x => trie_get x (bind_trie c b)) db)
    end.
  Fixpoint T_apply_jobs (p : program V.t) (js : list (cplan V.t * list (cell V.t)))
      (db : D.t) : N :=
    match js with
    | [] => 0%N
    | (c, b) :: rest =>
        (T_apply (actions V.t (job_rule p c)) (fun x => trie_get x (bind_trie c b))
            (fun x => 1 + T_trie_get x (bind_trie c b)) db +
          T_apply_jobs p rest
            (apply (actions V.t (job_rule p c)) (fun x => trie_get x (bind_trie c b)) db))%N
    end.

  Definition k_driver : N :=
    (64 * 1024 * (D.c_db + I.c_ix + J.c_join + V.c_val + V.c_key +
      PTrieT.c_trie + 1))%N.
  Definition env_allocated (db : D.t) (s : Model.env (V := V.t)) : Prop :=
    forall x i, s x = Some (Id i) -> D.allocated db i.
  Definition agrees (s t : Model.env (V := V.t)) (xs : list positive) : Prop :=
    forall x, In x xs -> s x = t x.
  Definition extends (db : D.t) (M : model (V := V.t))
      (nu nu' : positive -> carrier M) : Prop :=
    forall i, D.allocated db i -> nu' i = nu i.
  Definition derived (p : program V.t) (initial current : D.t) : Prop :=
    forall f k o, row (D.view current) f k o -> derives V.prim p (D.view initial) f k.
  Definition grows_upto (db db' : D.t) : Prop :=
    (forall i j, same (D.view db) i j -> same (D.view db') i j) /\
    (forall f k o, row (D.view db) f k o -> exists k' o',
      row (D.view db') f k' o' /\ Forall2 (cell_rel (same (D.view db'))) k k' /\
      D.out_le db' f (option_map (D.canon db') o) o').
  Definition k_check : N := (64 * 1024 * (V.c_key + PTrieT.c_trie + 1))%N.
  (** Two identifiers that occur in rows and are equal in the view are identical. *)
  Definition row_ids_unique (w : Model.view (V := V.t)) : Prop :=
    forall f k o f' k' o' i j, row w f k o -> row w f' k' o' ->
      In (Id i) (k ++ option_list o) -> In (Id j) (k' ++ option_list o') ->
      same w i j -> i = j.

  Lemma F1_plan_match_sound : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r ->
    In b (bindings cp c db) -> keep p c (bind_trie c b) = true ->
    matches V.prim (D.view db) (query V.t r) (env_of c b).
  Proof. Admitted. (* STUB *)

  Lemma F2_naive_plans_complete : forall p cp db r s, plans_ok p cp -> D.wf db ->
    loaded p cp db -> D.canonical db -> In r (rules V.t p) ->
    matches V.prim (D.view db) (query V.t r) s ->
    exists c b, In c (naive V.t cp) /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      In b (bindings cp c db) /\ keep p c (bind_trie c b) = true /\
      agrees (env_of c b) s (query_vars r).
  Proof. Admitted. (* STUB *)

  Lemma F3_apply_wf : forall p cp r s db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    In r (rules V.t p) -> rule_env (program_sorts p) (program_kind p) r s ->
    env_allocated db s ->
    D.wf (apply (actions V.t r) s db) /\ loaded p cp (apply (actions V.t r) s db) /\
    (D.ids db <= D.ids (apply (actions V.t r) s db))%N /\
    D.unit db <= D.unit (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F4a_match_model : forall (M : model (V := V.t)) nu p cp db q s,
    D.wf db -> loaded p cp db -> sat V.merge M nu (D.view db) ->
    matches V.prim (D.view db) q s ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x))) q.
  Proof. Admitted. (* STUB *)

  Lemma F4_apply_sat : forall (M : model (V := V.t)) nu p cp r s db,
    plans_ok p cp -> D.wf db -> loaded p cp db -> env_allocated db s ->
    rule_env (program_sorts p) (program_kind p) r s ->
    valid_sorted V.prim V.merge M p -> In r (rules V.t p) ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x)))
      (query V.t r) ->
    sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\
      sat V.merge M nu' (D.view (apply (actions V.t r) s db)).
  Proof. Admitted. (* STUB *)

  Lemma F5_apply_quiet_present : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    row_ids_unique (D.view db) ->
    D.changed db = false -> D.changed (apply (actions V.t r) s db) = false ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  Proof. Admitted. (* STUB *)

  Lemma F6_apply_grows : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    grows_upto db (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F6a_rebuild_grows : forall db0 db, D.wf db -> grows_upto db0 db ->
    grows db0 (D.rebuild db).
  Proof. Admitted. (* STUB *)

  Lemma F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply (actions V.t r) s db).
  Proof. Admitted. (* STUB *)

  Lemma F8_naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical db -> D.changed db = false -> D.changed (round p cp true db) = false ->
    closed V.prim V.merge p (D.view db).
  Proof. Admitted. (* STUB *)

  Lemma F9_round_progress : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db -> D.changed db = false ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
  Proof. Admitted. (* STUB *)

  Lemma F10_run_loop : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    match loopN (driver p cp lim) (max_iter lim) (false, db) with
    | inl (_, db') => run p cp lim db = (IterLimit, D.rebuild db')
    | inr (st, db') => run p cp lim db = (st, D.rebuild db')
    end.
  Proof.
    intros p cp lim db _ _ _. unfold run.
    change (limits_iter lim) with (max_iter lim).
    destruct (loopN (driver p cp lim) (max_iter lim) (false, db)) as [[nv db'] | [st db']];
      reflexivity.
  Qed.

  Lemma F11_derives_least : forall p db w f k, relational_fragment p = true ->
    no_ids db -> closed V.prim V.merge p w -> includes (D.view db) w ->
    (forall g, kind w g = program_kind p g) -> view_sorted (program_sorts p) w ->
    derives V.prim p (D.view db) f k -> row w f k None.
  Proof. Admitted. (* STUB *)

  Lemma F12_herbrand_bound : forall p cp db nv, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> prim_free p = true -> no_ids db ->
    herbrand p (round p cp nv db) <= herbrand p db.
  Proof. Admitted. (* STUB *)

  Lemma F13_herbrand_size : forall p db,
    relational_fragment p = true -> prim_free p = true ->
    herbrand p db = length (universe p db) /\ NoDup (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma F14_universe_rows : forall p cp lim db nv current f k o,
    plans_ok p cp -> D.wf db -> loaded p cp db -> relational_fragment p = true ->
    prim_free p = true -> no_ids db ->
    In (nv, current) (trace p cp lim db) -> row (D.view current) f k o ->
    ~ row (D.view db) f k o ->
    In (f, k) (universe p db).
  Proof. Admitted. (* STUB *)

  Lemma F15_unit_scale : forall (T C P P' : N) (u U : nat), 1 <= u -> u <= U ->
    (T + N.of_nat u * P' <= N.of_nat u * (C + P))%N ->
    (T + N.of_nat U * P' <= N.of_nat U * (C + P))%N.
  Proof.
    intros T C P P' u U Hu HuU Hbound.
    assert (HuN : (1 <= N.of_nat u)%N) by lia.
    assert (HuUN : (N.of_nat u <= N.of_nat U)%N) by lia.
    assert (Hpotential : (P' <= C + P)%N) by nia.
    pose proof (N.mul_le_mono_l P' (C + P) (N.of_nat U - N.of_nat u) Hpotential)
      as Hextra.
    nia.
  Qed.

  Lemma F16_unit_pos : forall db, 1 <= D.unit db.
  Proof.
    intro db. unfold D.unit. nia.
  Qed.

  Lemma F17_round_mono : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (round p cp nv db) /\ loaded p cp (round p cp nv db) /\
    (D.ids db <= D.ids (round p cp nv db))%N /\ D.unit db <= D.unit (round p cp nv db).
  Proof. Admitted. (* STUB *)

  Lemma F18_round_idle : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.canonical (round p cp nv db) /\ D.pending (round p cp nv db) = 0.
  Proof. Admitted. (* STUB *)

  Lemma trace_spec : forall p cp lim db,
    trace p cp lim db =
      driver_trace (driver p cp lim) (N.to_nat (max_iter lim)) (false, db).
  Proof. Admitted. (* STUB *)

  Lemma F19_trace_chain : forall p cp lim db,
    hd_error (trace p cp lim db) = Some (false, db) /\
    length (trace p cp lim db) <= N.to_nat (max_iter lim) + 1 /\
    forall n s s', nth_error (trace p cp lim db) n = Some s ->
      nth_error (trace p cp lim db) (S n) = Some s' -> driver p cp lim s = inl s'.
  Proof. Admitted. (* STUB *)

  Lemma F20_round_work : forall p cp nv db,
    round_work p cp nv db =
      length (Syntax.slots V.t cp) +
      fold_right Nat.add 0 (map (fun c =>
        (J.work (join V.t c) (map (source_index db) (sources V.t c)) +
          length (sources V.t c) + 2) *
          (nvars (join V.t c) + 1) * (nvars (join V.t c) + 1) +
        length (bindings cp c db) *
          (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat (var_of V.t c) +
           post_work p c + rule_work p c + 1 +
           fold_right (fun a n => match a with
             | Make _ f args | Put f args _ =>
                 (length args + 2) * (length args + 2) *
                   (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1)
                 + n
             | Union _ _ => 1 + n
             | Let _ _ args => length args + 1 + n
             end) 0 (actions V.t (nth (N.to_nat (rule_ix V.t c)) (rules V.t p)
               (Rule V.t [] [])))) +
        fold_right Nat.add 0 (map (fun binding =>
          let r := nth (N.to_nat (rule_ix V.t c)) (rules V.t p) (Rule V.t [] []) in
          N.to_nat (query_prim_work V.prim_work (query V.t r) (env_of c binding) +
            action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r)
              (env_of c binding))%N)
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)).
  Proof.
    reflexivity.
  Qed.

  Lemma F21_put_sorted : forall sorts f k o db, D.wf db -> D.kind_ok db f k o ->
    view_sorted sorts (D.view db) -> row_sorted sorts (kind (D.view db)) f k o ->
    view_sorted sorts (D.view (D.put f k o db)).
  Proof. Admitted. (* STUB *)

  Lemma F22_make_sorted : forall sorts f k db, D.wf db -> kind (D.view db) f = Some OId ->
    sorts f = Some (map cell_sort k) -> view_sorted sorts (D.view db) ->
    view_sorted sorts (D.view (snd (D.make f k db))).
  Proof. Admitted. (* STUB *)

  Lemma F23_union_sorted : forall sorts i j db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.union i j db)).
  Proof. Admitted. (* STUB *)

  Lemma F24_rebuild_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.rebuild db)).
  Proof. Admitted. (* STUB *)

  Lemma F25_advance_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.advance db)).
  Proof. Admitted. (* STUB *)

  Lemma F26_bindings_env : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r -> In b (bindings cp c db) ->
    rule_env (program_sorts p) (program_kind p) r (env_of c b) /\ env_allocated db (env_of c b).
  Proof. Admitted. (* STUB *)

  Lemma F27_check_plan_split : forall p cp,
    check_plan p cp = check_program p && check_shape p cp.
  Proof.
    reflexivity.
  Qed.

  Lemma F28_plan_shape : forall p, program_ok p -> check_shape p (plan p) = true.
  Proof. Admitted. (* STUB *)

  Lemma F29_shape_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) -> exists ss out,
      program_sorts p f = Some ss /\ program_kind p f = Some out /\
      NoDup perm /\ Forall (fun i => i < length ss +
        match out_sort out with
        | Some _ => 1
        | None => 0
        end) perm.
  Proof. Admitted. (* STUB *)

  Lemma T4_check_plan_split : forall p cp,
    (T_check_plan p cp <= T_check_program p + T_check_shape p cp + k_check)%N.
  Proof.
    intros p cp.
    assert (Hconstant : (2 <= k_check)%N) by (unfold k_check; lia).
    time_unfold T_check_plan.
    pose proof (Datatypes.T_andb_le (check_program p) (check_shape p cp)) as Hand.
    lia.
  Qed.

  Lemma T5_check_shape_le : forall p cp,
    (T_check_shape p cp <= k_check * N.of_nat (size_program p + size_compiled cp + 1) *
      N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F21_driver_step : forall p cp lim nv db,
    driver p cp lim (nv, db) =
      let next := round p cp nv db in
      if N.ltb (max_ids lim) (D.ids next) then inr (IdLimit, next)
      else if andb nv (negb (D.changed next)) then inr (Saturated, next)
      else inl (negb (D.changed next), D.advance next).
  Proof.
    reflexivity.
  Qed.

  (** The trie of a binding gives the plan's binding environment. *)
  Lemma F30_bind_trie : forall c b x, trie_get x (bind_trie c b) = env_of c b x.
  Proof.
    intros c b x. unfold bind_trie, env_of.
    rewrite bind_cells_get, PTrie.get_empty. reflexivity.
  Qed.

  (** A binding traversal pays for each variable's lookup and optional insertion once. *)
  Lemma bind_cells_clock_le : forall vars (cells : list (cell V.t)) t,
    (T_bind_cells vars cells t <= 16 *
      N.of_nat (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat vars + 1))%N.
  Proof.
    intro vars. induction vars as [|x xs IH]; intros cells t.
    - time_unfold @T_bind_cells. time_simpl. time_cbn. nia.
    - destruct cells as [|c cs].
      + time_unfold @T_bind_cells. time_simpl. time_cbn.
        rewrite !Nat2N.inj_add. nia.
      + pose proof (IH cs t) as Hkeep.
        pose proof (IH cs (PTrieCode.set x c t)) as Hnew.
        pose proof (PTrieT.replace_clock_bound (cell V.t) x (Some c) t) as Hset.
        time_unfold @T_bind_cells. time_simpl. time_cbn.
        unfold PTrieCode.T_set. rewrite PTrieT.trie_get_clock.
        destruct (trie_get x t); cbn [fold_right];
          rewrite !Nat2N.inj_add in *; nia.
  Qed.

  (** The wrapper adds only its own call and the variable-field reader. *)
  Lemma bind_trie_clock_le : forall c b,
    (T_bind_trie c b <= 32 *
      N.of_nat (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat
        (var_of V.t c) + 1))%N.
  Proof.
    intros c b. pose proof (bind_cells_clock_le (plan_vars c) b Empty) as Hcells.
    destruct c as [ix j srcs vars post].
    time_unfold T_bind_trie. time_simpl. time_cbn.
    cbn [plan_vars] in Hcells. nia.
  Qed.

  (** Building the trie of a binding pays for the bits of the plan's variables. *)
  Lemma T6_bind_trie_le : forall c b,
    (T_bind_trie c b <= k_driver *
      N.of_nat (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat
        (var_of V.t c) + 1))%N.
  Proof.
    intros c b.
    pose proof (bind_trie_clock_le c b) as Hbind.
    unfold k_driver. nia.
  Qed.

  Definition keep_width_program : program V.t :=
    Program V.t [] [Rule V.t [Fun V.t 1%positive [Var 1%positive; Var 1%positive] None] []].

  Definition keep_width_plan (z : positive) : cplan V.t :=
    CPlan V.t 0%N (JPlan 0 []) [] [z] [0].

  (** Even an empty binding pays the full width of the first copy-name lookup. *)
  Lemma keep_width_clock_lower : forall z,
    (2 * N.of_nat (Pos.size_nat z) <=
      T_keep keep_width_program (keep_width_plan z) (bind_trie (keep_width_plan z) []))%N.
  Proof.
    intro z.
    unfold T_keep, keep_width_program, keep_width_plan, bind_trie.
    cbn [plan_rule_ix rules rule_at plan_post plan_vars bind_cells].
    time_unfold @T_rule_at. time_unfold @T_keep_post.
    time_simpl. time_cbn.
    time_unfold @T_copies_ok. time_simpl. time_cbn.
    time_unfold @T_copies_ok. time_simpl. time_cbn.
    time_simpl. time_cbn.
    rewrite ?PTrie.get_empty. time_cbn.
    rewrite ?PTrieT.trie_get_clock. nia.
  Qed.

  (** Every charged measure stays fixed while the copy name grows. *)
  Lemma keep_width_work_fixed : forall z,
    post_work keep_width_program (keep_width_plan z) = 3%nat /\
    rule_work keep_width_program (keep_width_plan z) = 2%nat /\
    wbits keep_width_program = 1%nat /\
    query_prim_work V.prim_work (query V.t (job_rule keep_width_program
      (keep_width_plan z))) (env_of (keep_width_plan z) []) = 0%N.
  Proof.
    intro z. repeat split; reflexivity.
  Qed.

  (** Positive keys can have any nonzero width. *)
  Lemma keep_width_key_exists : forall n, exists z, Pos.size_nat z = S n.
  Proof.
    induction n as [|n [z Hz]].
    - exists 1%positive. reflexivity.
    - exists (xO z). cbn [Pos.size_nat]. now rewrite Hz.
  Qed.

  (** No fixed constant can bound the filter by the measures charged in [T7_keep_le]. *)
  Lemma keep_width_unbounded : forall k : N, exists z,
    (10 * k < T_keep keep_width_program (keep_width_plan z)
      (bind_trie (keep_width_plan z) []))%N.
  Proof.
    intro k.
    destruct (keep_width_key_exists (N.to_nat (5 * k)%N)) as [z Hz].
    exists z. pose proof (keep_width_clock_lower z) as Hclock.
    rewrite Hz, Nat2N.inj_succ, N2Nat.id in Hclock. nia.
  Qed.

  (** The proposed filter contract fails for every replacement of its constant. *)
  Lemma keep_bound_counterexample : forall k : N, exists p c b,
    ~ (T_keep p c (bind_trie c b) <= k * N.of_nat (post_work p c + 1) *
      N.of_nat (wbits p + fold_right (fun x n => Nat.max (cell_bits V.encode x) n) 0%nat b + 1) +
      k * query_prim_work V.prim_work (query V.t (job_rule p c)) (env_of c b) +
      k * N.of_nat (rule_work p c))%N.
  Proof.
    intro k. destruct (keep_width_unbounded k) as [z Hlarge].
    exists keep_width_program, (keep_width_plan z), [].
    destruct (keep_width_work_fixed z) as [Hpost [Hrule [Hwidth Hprim]]].
    rewrite Hpost, Hrule, Hwidth, Hprim. cbn [fold_right].
    intro Hbound. nia.
  Qed.
  (** The filter pays for its atoms at the widest program word or binding cell, and for the
      primitive work of the query. *)
  Lemma T7_keep_le : forall p c b,
    (T_keep p c (bind_trie c b) <= k_driver * N.of_nat (post_work p c + 1) *
      N.of_nat (wbits p + fold_right (fun x n => Nat.max (cell_bits V.encode x) n) 0%nat b + 1) +
      k_driver * query_prim_work V.prim_work (query V.t (job_rule p c)) (env_of c b) +
      k_driver * N.of_nat (rule_work p c))%N.
  Proof. Admitted. (* PLAN-DEFECT: copy-name widths are uncharged; keep_bound_counterexample. *)

  (** A round's jobs are the kept bindings of its plans, plan by plan. *)
  Lemma F31_jobs : forall p cp nv db,
    jobs p cp nv db = flat_map (fun c => map (fun b => (c, b))
      (filter (fun b => keep p c (bind_trie c b)) (bindings cp c db)))
      (if nv then naive V.t cp else seminaive V.t cp).
  Proof.
    reflexivity.
  Qed.

  (** A checked plan names a rule of its program. *)
  Lemma F33_plan_rule : forall p cp c, plans_ok p cp -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some (job_rule p c).
  Proof. Admitted. (* STUB *)

  (** Applying a rule queues at most one pending entry per action. *)
  Lemma F34_apply_pending : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    D.pending (apply (actions V.t r) s db) <= D.pending db + length (actions V.t r).
  Proof. Admitted. (* STUB *)

  (** The job loop of a round applies the jobs as the plan's job application does. *)
  Lemma apply_all_jobs : forall p js db, apply_all p js db = apply_jobs p js db.
  Proof.
    intros p js. induction js as [| [c b] rest IH]; intro db.
    - reflexivity.
    - cbn [apply_all apply_jobs]. rewrite IH.
      unfold job_rule. rewrite rule_at_nth. reflexivity.
  Qed.

  (** A round applies its jobs in order and rebuilds the resulting database once. *)
  Lemma F32_round_jobs : forall p cp nv db,
    round p cp nv db = D.rebuild (apply_jobs p (jobs p cp nv db) db).
  Proof.
    intros p cp nv db. unfold round. rewrite apply_all_jobs. reflexivity.
  Qed.

  (** A round's time is bounded by its joins, job applications, rebuild and driver overhead. *)
  Lemma T1a_round_split : forall p cp nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_round p cp nv db <=
      fold_right N.add 0 (map (fun c =>
        J.T_run (join V.t c) (map (source_index db) (sources V.t c)))
        (if nv then naive V.t cp else seminaive V.t cp)) +
      fold_right N.add 0 (map (fun c =>
        fold_right N.add 0 (map (fun b => T_bind_trie c b + T_keep p c (bind_trie c b))
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)) +
      T_apply_jobs p (jobs p cp nv db) db +
      D.T_rebuild (apply_jobs p (jobs p cp nv db) db) +
      k_driver * N.of_nat (round_work p cp nv db + 1) * N.of_nat (wbits p + 1))%N.
  Proof. Admitted. (* PLAN-DEFECT: repeated source lookups omit the slot-number width. *)

  Lemma T1_round_le : forall B U p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (round p cp nv db) <= B)%N -> D.unit (round p cp nv db) <= U ->
    (T_round p cp nv db + N.of_nat U * D.potential B (round p cp nv db) <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (round_work p cp nv db + D.pending db + 1) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** The driver constant covers the stored fields and binary comparison. *)
  Lemma driver_constant_fields : (32 * (D.c_db + 1) <= k_driver)%N.
  Proof.
    unfold k_driver. nia.
  Qed.

  Lemma T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (T_run p cp lim db <=
      T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) +
      match loopN (driver p cp lim) (max_iter lim) (false, db) with
      | inl (_, final) => D.T_rebuild final
      | inr (_, final) => D.T_rebuild final
      end + k_driver)%N.
  Proof.
    intros p cp lim db Hplans Hwf Hloaded.
    pose proof driver_constant_fields as Hconstant.
    time_unfold T_run. time_unfold T_limits_iter.
    change (limits_iter lim) with (max_iter lim).
    change (fun st : bool * D.t => T_driver p cp lim st) with (T_driver p cp lim).
    destruct (loopN (driver p cp lim) (max_iter lim) (false, db))
      as [[nv final] | [st final]]; lia.
  Qed.

  (** Positive comparison stops when either operand ends. *)
  Lemma compare_cont_right_clock : forall order p q,
    (Pos.T_compare_cont order p q <= N.of_nat (Pos.size_nat q))%N.
  Proof.
    intros order p q. revert order p.
    induction q as [q IH | q IH |]; intros order [p | p |];
      time_unfold Pos.T_compare_cont; cbn [Pos.size_nat];
      rewrite ?Nat2N.inj_succ;
      try pose proof (IH order p); try pose proof (IH Lt p);
      try pose proof (IH Gt p); lia.
  Qed.

  (** Natural comparison can be charged to the second operand. *)
  Lemma compare_right_clock : forall a b,
    (N.T_compare a b <= N.of_nat (N.size_nat b) + 2)%N.
  Proof.
    intros [|a] [|b]; time_unfold N.T_compare; cbn [N.size_nat]; try lia.
    pose proof (compare_cont_right_clock Eq a b) as Hcompare.
    time_unfold Pos.T_compare. lia.
  Qed.

  (** A driver call pays for its round, limit test, flag test and advance. *)
  Lemma T2a_driver_le : forall p cp lim nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_driver p cp lim (nv, db) <= T_round p cp nv db + k_driver *
      N.of_nat (length (Syntax.slots V.t cp) +
        N.size_nat (D.ids (round p cp nv db)) + 1))%N.
  Proof.
    intros p cp lim nv db Hplans Hwf Hloaded.
    destruct (F17_round_mono p cp nv db Hplans Hwf Hloaded)
      as [Hwf_next [Hloaded_next Hmono]].
    destruct Hloaded_next as [Hkinds [Hslots Hsorted]].
    pose proof (D.T_advance_le (round p cp nv db)) as Hadvance.
    unfold D.num_slots in Hadvance. rewrite Hslots in Hadvance.
    pose proof (D.T_ids_le (round p cp nv db)) as Hids.
    pose proof (D.T_changed_le (round p cp nv db)) as Hchanged.
    pose proof (compare_right_clock (max_ids lim) (D.ids (round p cp nv db))) as Hcompare.
    pose proof driver_constant_fields as Hconstant.
    clear Hplans Hwf Hloaded Hwf_next Hkinds Hslots Hsorted Hmono.
    time_unfold T_driver. time_unfold T_limits_ids. time_unfold N.T_ltb.
    change (limits_ids lim) with (max_ids lim).
    destruct (N.ltb (max_ids lim) (D.ids (round p cp nv db)));
      [| destruct (andb nv (negb (D.changed (round p cp nv db))))];
      rewrite ?Nat2N.inj_add in *; time_simpl; nia.
  Qed.

  (** A loop pays each visited callback and amortised binary decrement once. *)
  Lemma loop_trace_clock_acc : forall (St Out : Type) (step : St -> St + Out)
      (T_step : St -> N) fs (Hacc : Acc loopN_lt fs),
    (Loop.T_loop loopN_lt (loopN_step step) (fun fs => T_loopN_step step T_step fs) fs Hacc <=
      fold_right N.add 0 (map (fun st => T_step st + c_loopN)
        (firstn (N.to_nat (fst fs))
          (driver_trace step (N.to_nat (fst fs)) (snd fs)))) +
      loopN_zero_bits (fst fs) + 2)%N.
  Proof.
    intros St Out step T_step fs Hacc.
    induction Hacc as [[fuel state] Hnext IH] using Loop.Acc_ind_dep.
    cbn [fst snd]. destruct fuel as [|p].
    - time_unfold @Loop.T_loop. cbn [loopN_step Acc_inv].
      unfold T_loopN_step at 1.
      cbn [loopN_step loopN_zero_bits N.to_nat firstn map fold_right]. lia.
    - assert (Hfuel : N.to_nat (Npos p) = S (N.to_nat (N.pred (Npos p)))).
      { rewrite N2Nat.inj_pred.
        change (Pos.to_nat p = S (Nat.pred (Pos.to_nat p))).
        pose proof (Pos2Nat.is_pos p). lia. }
      time_unfold @Loop.T_loop.
      cbn [loopN_step Acc_inv].
      destruct (step state) as [next | result] eqn:Hstep.
      + match goal with
        | |- context [Loop.T_loop _ _ _ ?fs (Hnext _ ?Hlt)] =>
            pose proof (IH fs Hlt) as Htail
        end.
        cbn [fst snd] in Htail.
        pose proof (loopN_pred_credit (Npos p)) as Hcredit.
        unfold T_loopN_step at 1. cbn beta iota zeta. rewrite Hstep.
        rewrite Hfuel. cbn [driver_trace firstn map fold_right]. rewrite Hstep.
        unfold c_loopN in Htail |- *. lia.
      + unfold T_loopN_step at 1. cbn beta iota zeta. rewrite Hstep.
        rewrite Hfuel. cbn [driver_trace firstn map fold_right]. rewrite Hstep.
        rewrite ?firstn_nil. cbn [map fold_right]. unfold c_loopN. lia.
  Qed.

  (** The loop pays for every driver call in the trace prefix and its fuel. *)
  Lemma T2b_loop_trace : forall p cp lim db,
    (T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) <=
      fold_right N.add 0 (map (fun st => T_driver p cp lim st + c_loopN)
        (firstn (N.to_nat (max_iter lim)) (trace p cp lim db))) +
      c_loopN * N.of_nat (N.size_nat (max_iter lim) + 1))%N.
  Proof.
    intros p cp lim db. unfold trace.
    time_unfold @T_loopN.
    match goal with
    | |- context [Loop.T_loop _ _ _ _ ?Hacc] =>
        pose proof (loop_trace_clock_acc _ _ (driver p cp lim) (T_driver p cp lim)
          (max_iter lim, (false, db)) Hacc) as Hloop
    end.
    pose proof (loopN_zero_bits_le_size (max_iter lim)) as Hbits.
    cbn [fst snd] in Hloop. unfold c_loopN in Hloop |- *.
    rewrite Nat2N.inj_add. lia.
  Qed.
  (** Primitive arguments observe values but do not distinguish class identifiers. *)
  Definition run_value_view (s : Model.env (V := V.t)) (x : positive) : option V.t :=
    match s x with
    | Some (Val v) => Some v
    | _ => None
    end.

  Lemma run_value_terms_agree : forall ts s t,
    (forall x, run_value_view s x = run_value_view t x) ->
    value_terms s ts = value_terms t ts.
  Proof.
    intro ts. induction ts as [|a ts IH]; intros s t Hagree.
    - reflexivity.
    - cbn [value_terms]. rewrite (IH s t Hagree).
      destruct a as [x | v]; [|reflexivity].
      specialize (Hagree x). unfold run_value_view in Hagree.
      destruct (s x) as [[i | u] |]; destruct (t x) as [[j | v] |];
        cbn in Hagree; destruct (value_terms t ts); congruence.
  Qed.

  Lemma run_value_update_agree : forall s t x c d,
    (forall y, run_value_view s y = run_value_view t y) ->
    (match c with Val v => Some v | _ => None end) =
      (match d with Val v => Some v | _ => None end) ->
    forall y, run_value_view (update s x c) y = run_value_view (update t x d) y.
  Proof.
    intros s t x c d Hagree Hvalue y. unfold run_value_view, update.
    destruct (Pos.eqb x y); [exact Hvalue | exact (Hagree y)].
  Qed.

  (** The primitive-work specification depends only on the available values. *)
  Lemma run_action_prim_work_agree : forall kinds acts s t,
    (forall x, run_value_view s x = run_value_view t x) ->
    action_prim_work V.prim V.prim_work kinds acts s =
      action_prim_work V.prim V.prim_work kinds acts t.
  Proof.
    intros kinds acts. induction acts as [|a acts IH]; intros s t Hagree.
    - reflexivity.
    - destruct a as [x f args | f args res | a b | x op args];
        cbn [action_prim_work].
      + destruct (kinds f) as [kind |]; [destruct kind |];
          apply IH; try exact Hagree.
        apply run_value_update_agree; [exact Hagree | reflexivity].
      + apply IH. exact Hagree.
      + apply IH. exact Hagree.
      + rewrite (run_value_terms_agree args s t Hagree).
        destruct (value_terms t args) as [vs |]; [|reflexivity].
        destruct (V.prim op vs) as [v |]; [|reflexivity].
        f_equal. apply IH. apply run_value_update_agree; [exact Hagree | reflexivity].
  Qed.

  (** Empty local bindings leave the original environment visible. *)
  Lemma run_look_empty : forall s x, @look V.t s Empty x = s x.
  Proof.
    intros s x. unfold look. rewrite PTrie.get_empty. reflexivity.
  Qed.

  (** A new local binding has the same shadowing order as the specification update. *)
  Lemma run_look_set : forall s locals x c y,
    @look V.t s (PTrieCode.set x c locals) y = update (look s locals) x c y.
  Proof.
    intros s locals x c y. unfold look, update.
    destruct (Pos.eqb x y) eqn:Hxy.
    - apply Pos.eqb_eq in Hxy. subst y. rewrite PTrie.get_set_same. reflexivity.
    - apply Pos.eqb_neq in Hxy. rewrite PTrie.get_set_other by congruence. reflexivity.
  Qed.

  (** Local lookup charges one trie walk and at most one external environment call. *)
  Lemma run_look_clock : forall s Ts locals x,
    (@T_look V.t s Ts locals x <= 2 * N.of_nat (Pos.size_nat x) + Ts x + 1)%N.
  Proof.
    intros s Ts locals x. time_unfold @T_look.
    rewrite PTrieT.trie_get_clock. destruct (trie_get x locals); lia.
  Qed.

  (** Reading a term pays its variable width and its external callback once. *)
  Lemma run_term_clock : forall s Ts locals t W,
    (forall x, In x (term_vars t) -> Pos.size_nat x <= W) ->
    (@T_term_cell V.t s Ts locals t <= 2 * N.of_nat (W + 1) +
      fold_right N.add 0%N (map Ts (term_vars t)))%N.
  Proof.
    intros s Ts locals [x | v] W Hwidth.
    - pose proof (Hwidth x (or_introl eq_refl)) as Hx.
      pose proof (run_look_clock s Ts locals x) as Hlook.
      time_unfold @T_term_cell. cbn [term_vars map fold_right].
      rewrite Nat2N.inj_add. nia.
    - time_unfold @T_term_cell. cbn [term_vars map fold_right].
      rewrite Nat2N.inj_add. lia.
  Qed.

  Lemma run_sum_app : forall xs ys : list N,
    fold_right N.add 0%N (xs ++ ys) = (fold_right N.add 0%N xs + fold_right N.add 0%N ys)%N.
  Proof.
    induction xs as [|x xs IH]; intro ys; cbn [fold_right app]; [reflexivity|].
    rewrite IH. lia.
  Qed.

  (** A short-circuiting list read charges at most every listed variable once. *)
  Lemma run_terms_clock : forall ts s Ts locals W,
    Forall (fun t => forall x, In x (term_vars t) -> Pos.size_nat x <= W) ts ->
    (@T_term_cells V.t s Ts locals ts <= 4 * N.of_nat ((length ts + 1) * (W + 1)) +
      fold_right N.add 0%N (map Ts (flat_map term_vars ts)))%N.
  Proof.
    intro ts. induction ts as [|t ts IH]; intros s Ts locals W Hwidth.
    - time_unfold @T_term_cells. cbn [length flat_map map fold_right].
      rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia.
    - inversion Hwidth as [|t' ts' Hhead Htail]; subst t' ts'.
      pose proof (run_term_clock s Ts locals t W Hhead) as Hterm.
      pose proof (IH s Ts locals W Htail) as Hrest.
      time_unfold @T_term_cells.
      destruct (term_cell s locals t); [destruct (term_cells s locals ts)|];
        cbn [length flat_map]; rewrite map_app, run_sum_app;
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add, ?Nat2N.inj_succ in *; nia.
  Qed.

  (** Value arguments obey the same callback budget as cell arguments. *)
  Lemma run_values_clock : forall ts s Ts locals W,
    Forall (fun t => forall x, In x (term_vars t) -> Pos.size_nat x <= W) ts ->
    (@T_term_values V.t s Ts locals ts <= 4 * N.of_nat ((length ts + 1) * (W + 1)) +
      fold_right N.add 0%N (map Ts (flat_map term_vars ts)))%N.
  Proof.
    intro ts. induction ts as [|t ts IH]; intros s Ts locals W Hwidth.
    - time_unfold @T_term_values. cbn [length flat_map map fold_right].
      rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia.
    - inversion Hwidth as [|t' ts' Hhead Htail]; subst t' ts'.
      pose proof (run_term_clock s Ts locals t W Hhead) as Hterm.
      pose proof (IH s Ts locals W Htail) as Hrest.
      time_unfold @T_term_values.
      destruct (term_cell s locals t) as [[i | v] |];
        try destruct (term_values s locals ts);
        cbn [length flat_map]; rewrite map_app, run_sum_app;
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add, ?Nat2N.inj_succ in *; nia.
  Qed.
  (** Query typing determines its final context pointwise. *)
  Lemma run_query_context_agree : forall (p : program V.t) (q : list (atom V.t)) g h,
    query_ok (program_sorts p) (program_kind p) ctx_empty q g ->
    query_ok (program_sorts p) (program_kind p) ctx_empty q h -> forall x, g x = h x.
  Proof.
    intros p q g h Hg Hh x.
    assert (Hempty : forall y, trie_get y (@Empty sort) = ctx_empty y).
    { intro y. rewrite PTrie.get_empty. reflexivity. }
    destruct (bind_query_b_complete V.t (decls V.t p) Empty ctx_empty q g Hempty Hg)
      as [tg [Htg Hrg]].
    destruct (bind_query_b_complete V.t (decls V.t p) Empty ctx_empty q h Hempty Hh)
      as [th [Hth Hrh]].
    rewrite Htg in Hth. inversion Hth; subst th. rewrite <- Hrg, <- Hrh. reflexivity.
  Qed.

  (** The rule environment supplies the context used to type its actions. *)
  Lemma run_rule_actions_env : forall p cp r s, plans_ok p cp -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s ->
    exists g, actions_ok (program_sorts p) (program_kind p) g (actions V.t r) /\
      env_sorted g s.
  Proof.
    intros p cp r s Hplans Hr [h [Hqh Henv]].
    pose proof (plans_ok_sorted p cp Hplans) as Hok.
    unfold program_ok in Hok. rewrite Forall_forall in Hok.
    destruct (Hok r Hr) as [g [Hqg Hacts]]. exists g. split; [exact Hacts|].
    intros x ty Hx. apply Henv. rewrite <- (run_query_context_agree p _ g h Hqg Hqh x).
    exact Hx.
  Qed.

  (** A typed term resolves to a cell of its declared sort. *)
  Lemma run_term_sorted : forall g (s : Model.env (V := V.t)) locals t ty,
    env_sorted g (look s locals) -> has g t ty ->
    exists c, term_cell s locals t = Some c /\ cell_sort c = ty.
  Proof.
    intros g s locals [x | v] ty Henv Hhas.
    - exact (Henv x ty Hhas).
    - exists (Val v). cbn [term_cell cell_sort]. split; [reflexivity|symmetry; exact Hhas].
  Qed.

  (** A term cannot manufacture an unallocated class identifier. *)
  Lemma run_term_allocated : forall db s locals t i,
    env_allocated db (look s locals) -> term_cell s locals t = Some (Id i) ->
    D.allocated db i.
  Proof.
    intros db s locals [x | v] i Halloc Hterm.
    - exact (Halloc x i Hterm).
    - discriminate Hterm.
  Qed.

  (** Reading typed arguments preserves their list of sorts and their length. *)
  Lemma run_cells_sorted : forall (ts : list (term V.t)) ss g s locals,
    Forall2 (has g) ts ss -> env_sorted g (look s locals) ->
    exists cells, term_cells s locals ts = Some cells /\ map cell_sort cells = ss /\
      length cells = length ts.
  Proof.
    intros ts ss g s locals Htyped Henv. induction Htyped as [|t ty ts ss Ht Hts IH].
    - exists []. repeat split; reflexivity.
    - destruct (run_term_sorted g s locals t ty Henv Ht) as [c [Hc Hsort]].
      destruct IH as [cells [Hcells [Hsorts Hlen]]]. exists (c :: cells).
      cbn [term_cells map length]. rewrite Hc, Hcells, Hsort, Hsorts, Hlen.
      repeat split; reflexivity.
  Qed.

  (** Every identifier returned by an argument read came from its environment. *)
  Lemma run_cells_allocated : forall ts db s locals cells,
    env_allocated db (look s locals) -> term_cells s locals ts = Some cells ->
    forall i, In (Id i) cells -> D.allocated db i.
  Proof.
    intro ts. induction ts as [|t ts IH]; intros db s locals cells Halloc Hcells i Hi.
    - cbn [term_cells] in Hcells. inversion Hcells; subst cells. contradiction.
    - cbn [term_cells] in Hcells.
      destruct (term_cell s locals t) as [c |] eqn:Hc; [|discriminate].
      destruct (term_cells s locals ts) as [cs |] eqn:Hcs; [|discriminate].
      inversion Hcells; subst cells. destruct Hi as [Hi | Hi].
      + subst c. eapply run_term_allocated; eauto.
      + eapply IH; eauto.
  Qed.

  (** An optional output agrees with the function's output kind. *)
  Lemma run_result_sorted : forall g (s : Model.env (V := V.t)) locals out res,
    env_sorted g (look s locals) -> has_result g out res ->
    exists o, result_cell s locals res = Some o /\ option_map cell_sort o = out_sort out.
  Proof.
    intros g s locals out res Henv Htyped.
    destruct out as [| |m]; destruct res as [t |];
      cbn [has_result out_sort] in Htyped; try contradiction.
    - exists None. split; reflexivity.
    - destruct (run_term_sorted g s locals t SId Henv Htyped) as [c [Hc Hsort]].
      exists (Some c). cbn [result_cell]. rewrite Hc. split; [reflexivity|].
      cbn [option_map out_sort]. now rewrite Hsort.
    - destruct (run_term_sorted g s locals t SVal Henv Htyped) as [c [Hc Hsort]].
      exists (Some c). cbn [result_cell]. rewrite Hc. split; [reflexivity|].
      cbn [option_map out_sort]. now rewrite Hsort.
  Qed.

  Lemma run_result_allocated : forall db s locals res o,
    env_allocated db (look s locals) -> result_cell s locals res = Some o ->
    forall i, In (Id i) (option_list o) -> D.allocated db i.
  Proof.
    intros db s locals [t |] o Halloc Hres i Hi; cbn [result_cell] in Hres.
    - destruct (term_cell s locals t) as [c |] eqn:Hc; [|discriminate].
      inversion Hres; subst o. destruct Hi as [Hi | Hi]; [|contradiction].
      subst c. eapply run_term_allocated; eauto.
    - inversion Hres; subst o. contradiction.
  Qed.

  (** The executable value reader agrees with the work specification. *)
  Lemma run_values_spec : forall (ts : list (term V.t)) s locals,
    term_values s locals ts = value_terms (look s locals) ts.
  Proof.
    intro ts. induction ts as [|t ts IH]; intros s locals; cbn [term_values value_terms].
    - reflexivity.
    - rewrite IH. destruct t as [x |v]; cbn [term_cell]; [|reflexivity].
      destruct (look s locals x) as [[i | v] |]; reflexivity.
  Qed.

  (** A checked slot fits every tuple with its declared argument and output sorts. *)
  Lemma run_typed_slots : forall p cp db f (k : list (cell V.t)) o out,
    plans_ok p cp -> loaded p cp db -> program_sorts p f = Some (map cell_sort k) ->
    program_kind p f = Some out -> option_map cell_sort o = out_sort out ->
    D.slots_fit db f (length (k ++ option_list o)).
  Proof.
    intros p cp db f k o out Hplans [_ [Hslots _]] Hsort Hkind Hout perm Hin.
    rewrite Hslots in Hin.
    destruct (F29_shape_slots p cp f perm Hplans Hin)
      as [ss [out' [Hss [Hout' [Hnodup Hbound]]]]].
    rewrite Hsort in Hss. inversion Hss; subst ss.
    rewrite Hkind in Hout'. inversion Hout'; subst out'.
    split; [exact Hnodup|]. rewrite length_map in Hbound. rewrite length_app.
    destruct out as [| |m]; destruct o as [[i |v] |];
      cbn [option_map out_sort] in Hout; try discriminate;
      cbn [option_list length]; exact Hbound.
  Qed.

  Lemma run_make_slots : forall p cp db f (k : list (cell V.t)),
    plans_ok p cp -> loaded p cp db -> program_sorts p f = Some (map cell_sort k) ->
    program_kind p f = Some OId -> D.slots_fit db f (S (length k)).
  Proof.
    intros p cp db f k Hplans Hloaded Hsort Hkind.
    pose proof (run_typed_slots p cp db f k (Some (Id 1)) OId
      Hplans Hloaded Hsort Hkind eq_refl) as Hslots.
    rewrite length_app in Hslots. cbn [option_list length] in Hslots.
    replace (length k + 1) with (S (length k)) in Hslots by lia. exact Hslots.
  Qed.

  Lemma run_put_kind : forall p cp db f k o out,
    plans_ok p cp -> loaded p cp db ->
    (forall i, In (Id i) (k ++ option_list o) -> D.allocated db i) ->
    program_sorts p f = Some (map cell_sort k) -> program_kind p f = Some out ->
    option_map cell_sort o = out_sort out -> D.kind_ok db f k o.
  Proof.
    intros p cp db f k o out Hplans Hloaded Halloc Hsort Hkind Hout.
    split; [exact Halloc|]. split.
    - eapply run_typed_slots; eauto.
    - destruct Hloaded as [Hkinds _]. rewrite Hkinds, Hkind.
      destruct out as [| |m]; destruct o as [[i |v] |];
        cbn [option_map out_sort] in Hout; try discriminate; exact I.
  Qed.

  (** Allocation remains valid when the identifier counter grows. *)
  Lemma run_env_allocated_mono : forall db db' s,
    (D.ids db <= D.ids db')%N -> env_allocated db s -> env_allocated db' s.
  Proof.
    intros db db' s Hids Henv x i Hx.
    specialize (Henv x i Hx). unfold D.allocated in *. lia.
  Qed.

  (** Local updates preserve the typing and allocation conditions of an action environment. *)
  Lemma run_local_sorted : forall g s locals x (c : cell V.t),
    env_sorted g (look s locals) ->
    env_sorted (ctx_set g x (cell_sort c)) (look s (PTrieCode.set x c locals)).
  Proof.
    intros g s locals x c Henv y ty Hy. rewrite run_look_set. unfold ctx_set in Hy.
    unfold update. destruct (Pos.eqb x y) eqn:Hxy.
    - inversion Hy; subst ty. exists c. split; reflexivity.
    - exact (Henv y ty Hy).
  Qed.

  Lemma run_local_allocated : forall db s locals x c,
    env_allocated db (look s locals) ->
    (forall i, c = Id i -> D.allocated db i) ->
    env_allocated db (look s (PTrieCode.set x c locals)).
  Proof.
    intros db s locals x c Henv Hnew y i Hy. rewrite run_look_set in Hy.
    unfold update in Hy. destruct (Pos.eqb x y).
    - apply Hnew. now inversion Hy.
    - exact (Henv y i Hy).
  Qed.

  (** A constructor either reuses its input database or advances its identifier counter. *)
  Lemma run_make_ids : forall f k db, D.wf db -> kind (D.view db) f = Some OId ->
    (D.ids db <= D.ids (snd (D.make f k db)))%N.
  Proof.
    intros f k db Hwf Hkind. pose proof (D.make_spec f k db Hwf Hkind) as Hmake.
    destruct (D.make f k db) as [i db'] eqn:Hresult. cbn [snd] in *.
    destruct Hmake as [[j [_ [_ Hsame]]] | [Hfresh [_ Hextends]]].
    - subst db'. lia.
    - destruct Hextends as [Hids _]. unfold D.fresh_id in Hfresh.
      rewrite Hids, Hfresh, N.succ_pos_spec. lia.
  Qed.

  Lemma run_loaded_put : forall p cp db f k o, D.wf db -> loaded p cp db ->
    D.kind_ok db f k o -> row_sorted (program_sorts p) (kind (D.view db)) f k o ->
    loaded p cp (D.put f k o db).
  Proof.
    intros p cp db f k o Hwf [Hkinds [Hslots Hsorted]] Hkind Hrow.
    destruct (D.layout_put f k o db Hwf) as [Hkinds' [Hslots' _]].
    split.
    - intro x. rewrite Hkinds'. apply Hkinds.
    - split; [now rewrite Hslots'|]. eapply F21_put_sorted; eauto.
  Qed.

  Lemma run_loaded_make : forall p cp db f k, D.wf db -> loaded p cp db ->
    program_kind p f = Some OId -> program_sorts p f = Some (map cell_sort k) ->
    loaded p cp (snd (D.make f k db)).
  Proof.
    intros p cp db f k Hwf [Hkinds [Hslots Hsorted]] Hkind Hsort.
    destruct (D.layout_make f k db Hwf) as [Hkinds' [Hslots' _]].
    split.
    - intro x. rewrite Hkinds'. apply Hkinds.
    - split; [now rewrite Hslots'|]. eapply F22_make_sorted; eauto.
      rewrite Hkinds. exact Hkind.
  Qed.

  Lemma run_loaded_union : forall p cp db i j, D.wf db -> loaded p cp db ->
    loaded p cp (D.union i j db).
  Proof.
    intros p cp db i j Hwf [Hkinds [Hslots Hsorted]].
    destruct (D.layout_union i j db Hwf) as [Hkinds' [Hslots' _]].
    split.
    - intro x. rewrite Hkinds'. apply Hkinds.
    - split; [now rewrite Hslots'|]. eapply F23_union_sorted; eauto.
  Qed.

  (** Every suffix of an action application keeps its typing and monotone budgets. *)
  Lemma run_apply_go_state : forall acts p cp g s locals db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> env_allocated db (look s locals) ->
    D.wf (apply_go acts s locals db) /\ loaded p cp (apply_go acts s locals db) /\
    (D.ids db <= D.ids (apply_go acts s locals db))%N /\
    D.unit db <= D.unit (apply_go acts s locals db).
  Proof.
    intro acts. induction acts as [|a acts IH];
      intros p cp g s locals db Hplans Hwf Hloaded Hacts Henv Halloc.
    - cbn [apply_go]. split; [assumption|]. split; [assumption|]. split; lia.
    - destruct a as [x f args |f args res |a b |x op args]; cbn [apply_go].
      + destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
        destruct (run_cells_sorted args ss g s locals Hargs Henv)
          as [cells [Hcells [Hsorts Hlen]]]. rewrite Hcells.
        assert (Hsort_cells : program_sorts p f = Some (map cell_sort cells)).
        { now rewrite Hsorts. }
        pose proof (run_cells_allocated args db s locals cells Halloc Hcells) as Hcells_alloc.
        pose proof (run_make_slots p cp db f cells Hplans Hloaded Hsort_cells Hkind) as Hslots.
        assert (Hkind_db : kind (D.view db) f = Some OId).
        { rewrite (proj1 Hloaded). exact Hkind. }
        pose proof (D.wf_make f cells db Hwf Hcells_alloc Hslots) as Hwf_next.
        pose proof (run_loaded_make p cp db f cells Hwf Hloaded Hkind Hsort_cells)
          as Hloaded_next.
        pose proof (run_make_ids f cells db Hwf Hkind_db) as Hids.
        pose proof (D.unit_mono_make f cells db Hwf) as Hunit.
        pose proof (D.layout_make f cells db Hwf) as Hlayout.
        destruct (D.make f cells db) as [i next] eqn:Hmake in *.
        cbn [fst snd] in *. destruct Hlayout as [_ [_ [_ [Hi _]]]].
        assert (Henv_next : env_sorted (ctx_set g x SId)
          (look s (PTrieCode.set x (Id i) locals))).
        { exact (run_local_sorted g s locals x (Id i) Henv). }
        assert (Halloc_next : env_allocated next (look s (PTrieCode.set x (Id i) locals))).
        { apply run_local_allocated.
          - eapply run_env_allocated_mono; eauto.
          - intros j Heq. inversion Heq; subst j. exact Hi. }
        destruct (IH p cp (ctx_set g x SId) s (PTrieCode.set x (Id i) locals) next
          Hplans Hwf_next Hloaded_next Hrest Henv_next Halloc_next)
          as [Hwf_final [Hloaded_final [Hids_final Hunit_final]]].
        split; [assumption|]. split; [assumption|]. split; lia.
      + destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hres Hrest]]]]]].
        destruct (run_cells_sorted args ss g s locals Hargs Henv)
          as [cells [Hcells [Hsorts Hlen]]].
        destruct (run_result_sorted g s locals out res Henv Hres) as [o [Ho Hout]].
        rewrite Hcells, Ho.
        assert (Hsort_cells : program_sorts p f = Some (map cell_sort cells)).
        { now rewrite Hsorts. }
        assert (Htuple : forall i, In (Id i) (cells ++ option_list o) -> D.allocated db i).
        { intros i Hi. apply in_app_iff in Hi. destruct Hi as [Hi |Hi].
          - eapply run_cells_allocated; eauto.
          - eapply run_result_allocated; eauto. }
        pose proof (run_put_kind p cp db f cells o out Hplans Hloaded Htuple
          Hsort_cells Hkind Hout) as Hkind_ok.
        assert (Hrow : row_sorted (program_sorts p) (kind (D.view db)) f cells o).
        { exists out. split; [exact Hsort_cells|]. split; [|exact Hout].
          rewrite (proj1 Hloaded). exact Hkind. }
        pose proof (D.wf_put f cells o db Hwf Hkind_ok) as Hwf_next.
        pose proof (run_loaded_put p cp db f cells o Hwf Hloaded Hkind_ok Hrow)
          as Hloaded_next.
        destruct (D.layout_put f cells o db Hwf) as [_ [_ [Hids _]]].
        pose proof (D.unit_mono_put f cells o db Hwf) as Hunit.
        assert (Halloc_next : env_allocated (D.put f cells o db) (look s locals)).
        { apply (run_env_allocated_mono db _ (look s locals));
          [rewrite Hids; lia|exact Halloc]. }
        destruct (IH p cp g s locals (D.put f cells o db) Hplans Hwf_next Hloaded_next
          Hrest Henv Halloc_next) as [Hwf_final [Hloaded_final [Hids_final Hunit_final]]].
        split; [assumption|]. split; [assumption|]. split; lia.
      + destruct Hacts as [Ha [Hb Hrest]].
        destruct (run_term_sorted g s locals a SId Henv Ha) as [c [Hc Hcsort]].
        destruct c as [i |v]; [|discriminate Hcsort].
        destruct (run_term_sorted g s locals b SId Henv Hb) as [d [Hd Hdsort]].
        destruct d as [j |v]; [|discriminate Hdsort]. rewrite Hc, Hd.
        pose proof (run_term_allocated db s locals a i Halloc Hc) as Hi.
        pose proof (run_term_allocated db s locals b j Halloc Hd) as Hj.
        pose proof (D.wf_union i j db Hwf Hi Hj) as Hwf_next.
        pose proof (run_loaded_union p cp db i j Hwf Hloaded) as Hloaded_next.
        destruct (D.layout_union i j db Hwf) as [_ [_ [Hids _]]].
        pose proof (D.unit_mono_union i j db Hwf) as Hunit.
        assert (Halloc_next : env_allocated (D.union i j db) (look s locals)).
        { apply (run_env_allocated_mono db _ (look s locals));
          [rewrite Hids; lia|exact Halloc]. }
        destruct (IH p cp g s locals (D.union i j db) Hplans Hwf_next Hloaded_next
          Hrest Henv Halloc_next) as [Hwf_final [Hloaded_final [Hids_final Hunit_final]]].
        split; [assumption|]. split; [assumption|]. split; lia.
      + destruct Hacts as [Hargs Hrest].
        destruct (term_values s locals args) as [vs |] eqn:Hvs.
        * destruct (V.prim op vs) as [v |] eqn:Hprim.
          -- apply (IH p cp (ctx_set g x SVal)); try assumption.
             ++ exact (run_local_sorted g s locals x (Val v) Henv).
             ++ apply run_local_allocated; [exact Halloc|]. intros i Heq. discriminate Heq.
          -- split; [assumption|]. split; [assumption|]. split; lia.
        * split; [assumption|]. split; [assumption|]. split; lia.
  Qed.

  Definition run_term_width (W : nat) (t : term V.t) : Prop :=
    forall x, In x (term_vars t) -> Pos.size_nat x <= W.

  Definition run_action_width (W : nat) (a : action V.t) : Prop :=
    Forall (fun x => Pos.size_nat x <= W) (action_binds a) /\
    Forall (run_term_width W) (action_terms a).

  (** The maximum word width covers every member of the program's encoded words. *)
  Lemma run_word_width : forall p x, In x (program_words V.encode p) ->
    Pos.size_nat x <= wbits p.
  Proof.
    intros p x Hx. unfold wbits. revert Hx.
    generalize (program_words V.encode p) as xs. intro xs.
    induction xs as [|y xs IH]; intro Hx; [contradiction|].
    cbn [fold_right] in *. destruct Hx as [Hx |Hx].
    - subst y. apply Nat.le_max_l.
    - specialize (IH Hx). eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
  Qed.

  Lemma run_action_words_in : forall p r a x, In r (rules V.t p) -> In a (actions V.t r) ->
    In x (action_words V.encode a) -> In x (program_words V.encode p).
  Proof.
    intros p r a x Hr Ha Hx. unfold program_words.
    apply in_or_app. right. apply in_flat_map. exists r. split; [exact Hr|].
    destruct r as [q acts]. apply in_or_app. right. apply in_flat_map.
    exists a. split; assumption.
  Qed.

  Lemma run_term_words_in : forall t x, In x (term_vars t) -> In x (term_words V.encode t).
  Proof.
    intros [y |v] x Hx; exact Hx || contradiction.
  Qed.

  Lemma run_action_term_words : forall a t x, In t (action_terms a) ->
    In x (term_words V.encode t) -> In x (action_words V.encode a).
  Proof.
    intros [y f args |f args res |a b |y op args] t x Ht Hx;
      cbn [action_terms action_words] in *.
    - right. right. apply in_flat_map. exists t. split; assumption.
    - right. apply in_flat_map. exists t. split; assumption.
    - destruct Ht as [Ht |[Ht |Ht]]; try contradiction; subst t;
        apply in_or_app; [left|right]; exact Hx.
    - right. right. apply in_flat_map. exists t. split; assumption.
  Qed.

  Lemma run_action_bind_words : forall a x, In x (action_binds a) ->
    In x (action_words V.encode a).
  Proof.
    intros [y f args |f args res |a b |y op args] x Hx;
      cbn [action_binds action_words] in *.
    - destruct Hx as [<-|[]]. now left.
    - contradiction.
    - contradiction.
    - destruct Hx as [<-|[]]. now left.
  Qed.

  (** Every action name read by the engine has the program's maximum word width. *)
  Lemma run_rule_width : forall p r, In r (rules V.t p) ->
    Forall (run_action_width (wbits p)) (actions V.t r).
  Proof.
    intros p r Hr. rewrite Forall_forall. intros a Ha. split.
    - rewrite Forall_forall. intros x Hx. apply run_word_width.
      eapply run_action_words_in; eauto using run_action_bind_words.
    - rewrite Forall_forall. intros t Ht x Hx. apply run_word_width.
      eapply run_action_words_in; eauto.
      eapply run_action_term_words; [exact Ht|now apply run_term_words_in].
  Qed.

  Definition run_action_weight (cp : compiled V.t) (a : action V.t) : nat :=
    match a with
    | Make _ f args | Put f args _ => (length args + 2) * (length args + 2) *
        (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1)
    | Union _ _ => 1
    | Let _ _ args => length args + 1
    end.

  Definition run_actions_weight (cp : compiled V.t) (acts : list (action V.t)) : nat :=
    fold_right (fun a n => match a with
      | Make _ f args | Put f args _ => (length args + 2) * (length args + 2) *
          (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1) + n
      | Union _ _ => 1 + n
      | Let _ _ args => length args + 1 + n
      end) 0 acts.

  Definition run_term_calls (Ts : positive -> N) (ts : list (term V.t)) : N :=
    fold_right N.add 0%N (map Ts (flat_map term_vars ts)).

  Lemma run_term_calls_app : forall Ts xs ys,
    run_term_calls Ts (xs ++ ys) = (run_term_calls Ts xs + run_term_calls Ts ys)%N.
  Proof.
    intros Ts xs ys. unfold run_term_calls. rewrite flat_map_app, map_app, run_sum_app.
    reflexivity.
  Qed.

  Lemma run_action_weight_pos : forall cp a, 1 <= run_action_weight cp a.
  Proof.
    intros cp [x f args |f args res |a b |x op args]; unfold run_action_weight; nia.
  Qed.

  Lemma run_result_clock : forall res s Ts locals W,
    Forall (run_term_width W) (option_list res) ->
    (T_result_cell s Ts locals res <= 4 * N.of_nat (W + 1) +
      run_term_calls Ts (option_list res))%N.
  Proof.
    intros [t |] s Ts locals W Hwidth.
    - inversion Hwidth as [|t' ts Hhead Htail]; subst t' ts.
      pose proof (run_term_clock s Ts locals t W Hhead) as Hterm.
      time_unfold @T_result_cell. destruct (term_cell s locals t);
        cbn [option_list run_term_calls flat_map app map fold_right];
        rewrite ?app_nil_r; rewrite Nat2N.inj_add in *; lia.
    - time_unfold @T_result_cell. cbn [option_list run_term_calls flat_map map fold_right].
      rewrite Nat2N.inj_add. lia.
  Qed.

  (** Every nonzero final unit dominates the syntax and identifier factors separately. *)
  Lemma run_spending_factors : forall U L W,
    1 <= U -> 1 <= L ->
    (1 <= N.of_nat U * N.of_nat L * N.of_nat (W + 1))%N /\
    (N.of_nat (W + 1) <= N.of_nat U * N.of_nat L * N.of_nat (W + 1))%N /\
    (N.of_nat U * N.of_nat L <= N.of_nat U * N.of_nat L * N.of_nat (W + 1))%N.
  Proof.
    intros U L W HU HL.
    assert (Hu : (1 <= N.of_nat U)%N) by lia.
    assert (Hl : (1 <= N.of_nat L)%N) by lia.
    assert (Hw : (1 <= N.of_nat (W + 1))%N) by lia.
    assert (Hul : (1 <= N.of_nat U * N.of_nat L)%N) by nia.
    repeat split; nia.
  Qed.

  Definition run_apply_factor : N := (128 * (D.c_db + V.c_val + 1))%N.

  Lemma run_apply_factor_le : (2 * run_apply_factor + 8 <= k_driver)%N.
  Proof.
    unfold run_apply_factor, k_driver. nia.
  Qed.

  Definition run_action_budget (B : N) (U W : nat) : N :=
    (run_apply_factor * (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
      N.of_nat (W + 1)))%N.

  (** The action coefficient covers syntax, database operations and a primitive call. *)
  Lemma run_action_budget_covers : forall B U W, 1 <= U ->
    (32 * N.of_nat (W + 1) +
      D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) + V.c_val + 8 <=
      run_action_budget B U W)%N.
  Proof.
    intros B U W HU.
    destruct (run_spending_factors U (N.to_nat (N.log2 B) + 1) W HU ltac:(lia))
      as [Hpos [Hwidth Hdb]].
    set (E := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (W + 1))%N)
      in Hpos, Hwidth, Hdb.
    assert (Hsyntax : (32 * N.of_nat (W + 1) <= 32 * E)%N) by nia.
    assert (Hdatabase : (D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) <=
      D.c_db * E)%N) by nia.
    assert (Hvalue : (V.c_val + 8 <= (V.c_val + 8) * E)%N) by nia.
    change (32 * N.of_nat (W + 1) +
      D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) + V.c_val + 8 <=
      run_apply_factor * E)%N.
    unfold run_apply_factor. nia.
  Qed.

  Lemma run_set_clock : forall x (c : cell V.t) locals,
    (PTrieCode.T_set x c locals <= 8 * N.of_nat (Pos.size_nat x) + 1)%N.
  Proof.
    intros x c locals. pose proof (PTrieT.replace_clock_bound (cell V.t) x (Some c) locals).
    unfold PTrieCode.T_set. lia.
  Qed.

  (** Binding actions read their terms and insert a local result within one syntax charge. *)
  Lemma run_binding_charge : forall args s Ts locals x c W weight,
    Forall (run_term_width W) args -> Pos.size_nat x <= W -> length args + 1 <= weight ->
    (T_term_cells s Ts locals args + PTrieCode.T_set x c locals + 8 <=
      32 * N.of_nat (W + 1) * N.of_nat weight + run_term_calls Ts args)%N.
  Proof.
    intros args s Ts locals x c W weight Hterms Hx Hweight.
    pose proof (run_terms_clock args s Ts locals W Hterms) as Hread.
    pose proof (run_set_clock x c locals) as Hset.
    unfold run_term_calls. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    assert (Hwidth : (1 <= N.of_nat W + 1)%N) by lia.
    assert (Hcount : (N.of_nat (length args) + 1 <= N.of_nat weight)%N) by lia.
    assert (Hname : (N.of_nat (Pos.size_nat x) <= N.of_nat W)%N) by lia.
    clear -Hread Hset Hwidth Hcount Hname. nia.
  Qed.

  Lemma run_value_binding_charge : forall args s Ts locals x c W weight,
    Forall (run_term_width W) args -> Pos.size_nat x <= W -> length args + 1 <= weight ->
    (T_term_values s Ts locals args + PTrieCode.T_set x c locals + 8 <=
      32 * N.of_nat (W + 1) * N.of_nat weight + run_term_calls Ts args)%N.
  Proof.
    intros args s Ts locals x c W weight Hterms Hx Hweight.
    pose proof (run_values_clock args s Ts locals W Hterms) as Hread.
    pose proof (run_set_clock x c locals) as Hset.
    unfold run_term_calls. rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    assert (Hwidth : (1 <= N.of_nat W + 1)%N) by lia.
    assert (Hcount : (N.of_nat (length args) + 1 <= N.of_nat weight)%N) by lia.
    assert (Hname : (N.of_nat (Pos.size_nat x) <= N.of_nat W)%N) by lia.
    clear -Hread Hset Hwidth Hcount Hname. nia.
  Qed.

  (** Put reads its arguments and optional output within the same tuple charge. *)
  Lemma run_put_charge : forall args res s Ts locals W weight,
    Forall (run_term_width W) (args ++ option_list res) -> length args + 2 <= weight ->
    (T_term_cells s Ts locals args + T_result_cell s Ts locals res + 8 <=
      32 * N.of_nat (W + 1) * N.of_nat weight +
        run_term_calls Ts (args ++ option_list res))%N.
  Proof.
    intros args res s Ts locals W weight Hterms Hweight.
    apply Forall_app in Hterms. destruct Hterms as [Hargs Hres].
    pose proof (run_terms_clock args s Ts locals W Hargs) as Hread.
    pose proof (run_result_clock res s Ts locals W Hres) as Hout.
    rewrite run_term_calls_app. unfold run_term_calls in *.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *.
    assert (Hwidth : (1 <= N.of_nat W + 1)%N) by lia.
    assert (Hcount : (N.of_nat (length args) + 2 <= N.of_nat weight)%N) by lia.
    clear -Hread Hout Hwidth Hcount. nia.
  Qed.

  Lemma run_union_charge : forall a b s Ts locals W,
    Forall (run_term_width W) [a; b] ->
    (T_term_cell s Ts locals a + T_term_cell s Ts locals b + 8 <=
      32 * N.of_nat (W + 1) + run_term_calls Ts [a; b])%N.
  Proof.
    intros a b s Ts locals W Hterms.
    inversion Hterms as [|a' ts Ha Htail]; subst a' ts.
    inversion Htail as [|b' ts Hb Hnil]; subst b' ts.
    pose proof (run_term_clock s Ts locals a W Ha) as Hleft.
    pose proof (run_term_clock s Ts locals b W Hb) as Hright.
    unfold run_term_calls. cbn [flat_map]. rewrite app_nil_r, map_app, run_sum_app.
    assert (Hwidth : (1 <= N.of_nat (W + 1))%N) by lia.
    lia.
  Qed.

  (** A database operation can be charged at any later, larger spending unit. *)
  Lemma run_operation_scale : forall B U old next T C,
    D.unit next <= U ->
    (T + N.of_nat (D.unit next) * D.potential B next <=
      N.of_nat (D.unit next) * (C + D.potential B old))%N ->
    (T + N.of_nat U * D.potential B next <=
      N.of_nat U * C + N.of_nat U * D.potential B old)%N.
  Proof.
    intros B U old next T C Hunit Htime.
    pose proof (F15_unit_scale T C (D.potential B old) (D.potential B next)
      (D.unit next) U (F16_unit_pos next) Hunit Htime) as Hscaled.
    rewrite N.mul_add_distr_l in Hscaled. exact Hscaled.
  Qed.

  Lemma run_make_clock_split : forall x f args acts s Ts locals db cells i next,
    term_cells s locals args = Some cells -> D.make f cells db = (i, next) ->
    (T_apply_go (Make x f args :: acts) s Ts locals db <=
      T_term_cells s Ts locals args + D.T_make f cells db +
      PTrieCode.T_set x (Id i) locals +
      T_apply_go acts s Ts (PTrieCode.set x (Id i) locals) next + 8)%N.
  Proof.
    intros x f args acts s Ts locals db cells i next Hcells Hmake.
    time_unfold T_apply_go. rewrite Hcells, Hmake. lia.
  Qed.

  Lemma run_put_clock_split : forall f args res acts s Ts locals db cells o,
    term_cells s locals args = Some cells -> result_cell s locals res = Some o ->
    (T_apply_go (Put f args res :: acts) s Ts locals db <=
      T_term_cells s Ts locals args + T_result_cell s Ts locals res + D.T_put f cells o db +
      T_apply_go acts s Ts locals (D.put f cells o db) + 8)%N.
  Proof.
    intros f args res acts s Ts locals db cells o Hcells Ho.
    time_unfold T_apply_go. rewrite Hcells, Ho. lia.
  Qed.

  Lemma run_union_clock_split : forall a b acts s Ts locals db i j,
    term_cell s locals a = Some (Id i) -> term_cell s locals b = Some (Id j) ->
    (T_apply_go (Union a b :: acts) s Ts locals db <=
      T_term_cell s Ts locals a + T_term_cell s Ts locals b + D.T_union i j db +
      T_apply_go acts s Ts locals (D.union i j db) + 8)%N.
  Proof.
    intros a b acts s Ts locals db i j Ha Hb.
    time_unfold T_apply_go. rewrite Ha, Hb. lia.
  Qed.

  Lemma run_let_clock_split : forall x op args acts s Ts locals db vs v,
    term_values s locals args = Some vs -> V.prim op vs = Some v ->
    (T_apply_go (Let x op args :: acts) s Ts locals db <=
      T_term_values s Ts locals args + V.T_prim op vs +
      PTrieCode.T_set x (Val v) locals +
      T_apply_go acts s Ts (PTrieCode.set x (Val v) locals) db + 8)%N.
  Proof.
    intros x op args acts s Ts locals db vs v Hvs Hv.
    time_unfold T_apply_go. rewrite Hvs, Hv. lia.
  Qed.

  (** Typed actions telescope their database potential at the final spending unit. *)
  Lemma run_apply_go_amort : forall acts p cp g s Ts locals db W B U,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> env_allocated db (look s locals) ->
    Forall (run_action_width W) acts ->
    (D.ids (apply_go acts s locals db) <= B)%N -> D.unit (apply_go acts s locals db) <= U ->
    (T_apply_go acts s Ts locals db + N.of_nat U * D.potential B (apply_go acts s locals db) <=
      run_action_budget B U W * N.of_nat (run_actions_weight cp acts + 1) +
      run_term_calls Ts (flat_map action_terms acts) +
      run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p) acts
        (look s locals) + N.of_nat U * D.potential B db)%N.
  Proof.
    intro acts. induction acts as [|a acts IH];
      intros p cp g s Ts locals db W B U Hplans Hwf Hloaded Hacts Henv Halloc Hwidth HB HU.
    - assert (Hunit : 1 <= U) by (pose proof (F16_unit_pos db); cbn [apply_go] in HU; lia).
      pose proof (run_action_budget_covers B U W Hunit) as Hcover.
      time_unfold T_apply_go.
      cbn [apply_go run_actions_weight run_term_calls flat_map map fold_right action_prim_work].
      lia.
    - assert (Hunit : 1 <= U).
      { pose proof (F16_unit_pos (apply_go (a :: acts) s locals db)). lia. }
      pose proof (run_action_budget_covers B U W Hunit) as Hcover.
      inversion Hwidth as [|a' acts' Hhead Htail]; subst a' acts'.
      pose proof (run_action_weight_pos cp a) as Hweight_pos.
      pose proof (N.mul_le_mono_r
        (32 * N.of_nat (W + 1) +
          D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) + V.c_val + 8)%N
        (run_action_budget B U W) (N.of_nat (run_action_weight cp a)) Hcover) as Hcharge.
      destruct a as [x f args |f args res |a b |x op args].
      + destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
        destruct Hhead as [Hbind Hterms]. cbn [action_binds action_terms] in Hbind, Hterms.
        inversion Hbind as [|x' xs Hx Hnil]; subst x' xs.
        destruct (run_cells_sorted args ss g s locals Hargs Henv)
          as [cells [Hcells [Hsorts Hlen]]].
        assert (Hsort_cells : program_sorts p f = Some (map cell_sort cells)).
        { now rewrite Hsorts. }
        pose proof (run_cells_allocated args db s locals cells Halloc Hcells) as Hcells_alloc.
        pose proof (run_make_slots p cp db f cells Hplans Hloaded Hsort_cells Hkind) as Hslots.
        assert (Hkind_db : kind (D.view db) f = Some OId).
        { rewrite (proj1 Hloaded). exact Hkind. }
        pose proof (D.wf_make f cells db Hwf Hcells_alloc Hslots) as Hwf_next.
        pose proof (run_loaded_make p cp db f cells Hwf Hloaded Hkind Hsort_cells)
          as Hloaded_next.
        pose proof (run_make_ids f cells db Hwf Hkind_db) as Hids.
        pose proof (D.layout_make f cells db Hwf) as Hlayout.
        destruct (D.make f cells db) as [i next] eqn:Hmake in *.
        cbn [fst snd] in *. destruct Hlayout as [_ [_ [_ [Hi _]]]].
        assert (Henv_next : env_sorted (ctx_set g x SId)
          (look s (PTrieCode.set x (Id i) locals))).
        { exact (run_local_sorted g s locals x (Id i) Henv). }
        assert (Halloc_next : env_allocated next (look s (PTrieCode.set x (Id i) locals))).
        { apply run_local_allocated.
          - eapply run_env_allocated_mono; eauto.
          - intros j Heq. inversion Heq; subst j. exact Hi. }
        cbn [apply_go] in HB, HU |- *. rewrite Hcells, Hmake in HB, HU |- *.
        destruct (run_apply_go_state acts p cp (ctx_set g x SId) s
          (PTrieCode.set x (Id i) locals) next Hplans Hwf_next Hloaded_next Hrest
          Henv_next Halloc_next) as [_ [_ [Hids_final Hunit_final]]].
        assert (HBnext : (D.ids next <= B)%N) by lia.
        assert (HUnext : D.unit next <= U) by lia.
        pose proof (D.T_make_amort B f cells db Hwf Hslots) as Hdatabase.
        rewrite Hmake in Hdatabase. cbn [snd] in Hdatabase.
        specialize (Hdatabase HBnext).
        pose proof (run_operation_scale B U db next (D.T_make f cells db) _
          HUnext Hdatabase) as Hscaled.
        assert (Hdbcharge : (D.T_make f cells db + N.of_nat U * D.potential B next <=
          D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
            N.of_nat (run_action_weight cp (Make x f args)) +
          N.of_nat U * D.potential B db)%N).
        { unfold D.slots_of in Hscaled. rewrite (proj1 (proj2 Hloaded)), Hlen in Hscaled.
          unfold run_action_weight. rewrite !Nat2N.inj_mul in *. clear -Hscaled. nia. }
        pose proof (IH p cp (ctx_set g x SId) s Ts (PTrieCode.set x (Id i) locals) next
          W B U Hplans Hwf_next Hloaded_next Hrest Henv_next Halloc_next Htail HB HU)
          as Hremaining.
        assert (Hprim : action_prim_work V.prim V.prim_work (program_kind p) acts
          (look s (PTrieCode.set x (Id i) locals)) =
          action_prim_work V.prim V.prim_work (program_kind p) acts
            (update (look s locals) x (Id 1))).
        { apply run_action_prim_work_agree. intro y. unfold run_value_view.
          rewrite run_look_set. unfold update. destruct (Pos.eqb x y); reflexivity. }
        rewrite Hprim in Hremaining.
        pose proof (run_binding_charge args s Ts locals x (Id i) W
          (run_action_weight cp (Make x f args)) Hterms Hx ltac:(unfold run_action_weight; nia))
          as Hsyntax.
        pose proof (run_make_clock_split x f args acts s Ts locals db cells i next
          Hcells Hmake) as Hclock.
        change (T_apply_go (Make x f args :: acts) s Ts locals db +
          N.of_nat U * D.potential B (apply_go acts s (PTrieCode.set x (Id i) locals) next) <=
          run_action_budget B U W *
            N.of_nat (run_action_weight cp (Make x f args) + run_actions_weight cp acts + 1) +
          run_term_calls Ts (args ++ flat_map action_terms acts) +
          run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p)
            (Make x f args :: acts) (look s locals) + N.of_nat U * D.potential B db)%N.
        rewrite run_term_calls_app. cbn [action_prim_work]. rewrite Hkind.
        rewrite !Nat2N.inj_add in Hremaining |- *.
        clear -Hsyntax Hclock Hremaining Hdbcharge Hcharge. nia.
      + destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hres Hrest]]]]]].
        destruct Hhead as [_ Hterms]. cbn [action_terms] in Hterms.
        destruct (run_cells_sorted args ss g s locals Hargs Henv)
          as [cells [Hcells [Hsorts Hlen]]].
        destruct (run_result_sorted g s locals out res Henv Hres) as [o [Ho Hout]].
        assert (Hsort_cells : program_sorts p f = Some (map cell_sort cells)).
        { now rewrite Hsorts. }
        assert (Htuple : forall i, In (Id i) (cells ++ option_list o) -> D.allocated db i).
        { intros i Hi. apply in_app_iff in Hi. destruct Hi as [Hi |Hi].
          - eapply run_cells_allocated; eauto.
          - eapply run_result_allocated; eauto. }
        pose proof (run_put_kind p cp db f cells o out Hplans Hloaded Htuple
          Hsort_cells Hkind Hout) as Hkind_ok.
        assert (Hrow : row_sorted (program_sorts p) (kind (D.view db)) f cells o).
        { exists out. split; [exact Hsort_cells|]. split; [|exact Hout].
          rewrite (proj1 Hloaded). exact Hkind. }
        pose proof (D.wf_put f cells o db Hwf Hkind_ok) as Hwf_next.
        pose proof (run_loaded_put p cp db f cells o Hwf Hloaded Hkind_ok Hrow)
          as Hloaded_next.
        destruct (D.layout_put f cells o db Hwf) as [_ [_ [Hids _]]].
        assert (Halloc_next : env_allocated (D.put f cells o db) (look s locals)).
        { apply (run_env_allocated_mono db _ (look s locals));
          [rewrite Hids; lia|exact Halloc]. }
        cbn [apply_go] in HB, HU |- *. rewrite Hcells, Ho in HB, HU |- *.
        destruct (run_apply_go_state acts p cp g s locals (D.put f cells o db)
          Hplans Hwf_next Hloaded_next Hrest Henv Halloc_next)
          as [_ [_ [Hids_final Hunit_final]]].
        assert (HBnext : (D.ids (D.put f cells o db) <= B)%N) by lia.
        assert (HUnext : D.unit (D.put f cells o db) <= U) by lia.
        pose proof (D.T_put_amort B f cells o db Hwf (proj1 (proj2 Hkind_ok)) HBnext)
          as Hdatabase.
        pose proof (run_operation_scale B U db (D.put f cells o db) (D.T_put f cells o db) _
          HUnext Hdatabase) as Hscaled.
        assert (Hdbcharge : (D.T_put f cells o db +
          N.of_nat U * D.potential B (D.put f cells o db) <=
          D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
            N.of_nat (run_action_weight cp (Put f args res)) +
          N.of_nat U * D.potential B db)%N).
        { unfold D.slots_of in Hscaled. rewrite (proj1 (proj2 Hloaded)), Hlen in Hscaled.
          unfold run_action_weight. rewrite !Nat2N.inj_mul in *. clear -Hscaled. nia. }
        pose proof (IH p cp g s Ts locals (D.put f cells o db) W B U Hplans Hwf_next
          Hloaded_next Hrest Henv Halloc_next Htail HB HU) as Hremaining.
        pose proof (run_put_charge args res s Ts locals W
          (run_action_weight cp (Put f args res)) Hterms
          ltac:(unfold run_action_weight; nia)) as Hsyntax.
        pose proof (run_put_clock_split f args res acts s Ts locals db cells o Hcells Ho)
          as Hclock.
        change (T_apply_go (Put f args res :: acts) s Ts locals db +
          N.of_nat U * D.potential B (apply_go acts s locals (D.put f cells o db)) <=
          run_action_budget B U W *
            N.of_nat (run_action_weight cp (Put f args res) + run_actions_weight cp acts + 1) +
          run_term_calls Ts ((args ++ option_list res) ++ flat_map action_terms acts) +
          run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p) acts
            (look s locals) + N.of_nat U * D.potential B db)%N.
        rewrite run_term_calls_app. rewrite !Nat2N.inj_add in Hremaining |- *.
        clear -Hsyntax Hclock Hremaining Hdbcharge Hcharge. nia.
      + destruct Hacts as [Ha [Hb Hrest]].
        destruct Hhead as [_ Hterms]. cbn [action_terms] in Hterms.
        destruct (run_term_sorted g s locals a SId Henv Ha) as [c [Hc Hcsort]].
        destruct c as [i |v]; [|discriminate Hcsort].
        destruct (run_term_sorted g s locals b SId Henv Hb) as [d [Hd Hdsort]].
        destruct d as [j |v]; [|discriminate Hdsort].
        pose proof (run_term_allocated db s locals a i Halloc Hc) as Hi.
        pose proof (run_term_allocated db s locals b j Halloc Hd) as Hj.
        pose proof (D.wf_union i j db Hwf Hi Hj) as Hwf_next.
        pose proof (run_loaded_union p cp db i j Hwf Hloaded) as Hloaded_next.
        destruct (D.layout_union i j db Hwf) as [_ [_ [Hids _]]].
        assert (Halloc_next : env_allocated (D.union i j db) (look s locals)).
        { apply (run_env_allocated_mono db _ (look s locals));
          [rewrite Hids; lia|exact Halloc]. }
        cbn [apply_go] in HB, HU |- *. rewrite Hc, Hd in HB, HU |- *.
        destruct (run_apply_go_state acts p cp g s locals (D.union i j db)
          Hplans Hwf_next Hloaded_next Hrest Henv Halloc_next)
          as [_ [_ [Hids_final Hunit_final]]].
        assert (HBold : (D.ids db <= B)%N) by lia.
        assert (HUnext : D.unit (D.union i j db) <= U) by lia.
        pose proof (D.T_union_amort B i j db Hwf Hi Hj HBold) as Hdatabase.
        pose proof (run_operation_scale B U db (D.union i j db) (D.T_union i j db) D.c_db
          HUnext Hdatabase) as Hscaled.
        pose proof (IH p cp g s Ts locals (D.union i j db) W B U Hplans Hwf_next
          Hloaded_next Hrest Henv Halloc_next Htail HB HU) as Hremaining.
        pose proof (run_union_charge a b s Ts locals W Hterms) as Hsyntax.
        pose proof (run_union_clock_split a b acts s Ts locals db i j Hc Hd) as Hclock.
        change (T_apply_go (Union a b :: acts) s Ts locals db +
          N.of_nat U * D.potential B (apply_go acts s locals (D.union i j db)) <=
          run_action_budget B U W * N.of_nat (1 + run_actions_weight cp acts + 1) +
          run_term_calls Ts ([a; b] ++ flat_map action_terms acts) +
          run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p) acts
            (look s locals) + N.of_nat U * D.potential B db)%N.
        rewrite run_term_calls_app. rewrite !Nat2N.inj_add in Hremaining |- *.
        cbn [run_action_weight N.of_nat] in Hcharge.
        assert (Hlog : (1 <= N.of_nat (N.to_nat (N.log2 B) + 1))%N) by lia.
        assert (Hdb : (N.of_nat U * D.c_db <=
          D.c_db * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1))%N) by nia.
        clear -Hsyntax Hclock Hremaining Hscaled Hcharge Hdb. nia.
      + destruct Hacts as [Hargs Hrest].
        destruct Hhead as [Hbind Hterms]. cbn [action_binds action_terms] in Hbind, Hterms.
        inversion Hbind as [|x' xs Hx Hnil]; subst x' xs.
        pose proof (run_values_spec args s locals) as Hvalues.
        assert (Hfactor : (V.c_val <= run_apply_factor)%N) by (unfold run_apply_factor; lia).
        destruct (term_values s locals args) as [vs |] eqn:Hvs.
        * try rewrite Hvs in Hvalues. pose proof (V.T_prim_le op vs) as Hprimitive.
          destruct (V.prim op vs) as [v |] eqn:Hprim.
          -- assert (Henv_next : env_sorted (ctx_set g x SVal)
               (look s (PTrieCode.set x (Val v) locals))).
             { exact (run_local_sorted g s locals x (Val v) Henv). }
             assert (Halloc_next : env_allocated db (look s (PTrieCode.set x (Val v) locals))).
             { apply run_local_allocated; [exact Halloc|]. intros i Heq. discriminate Heq. }
             cbn [apply_go] in HB, HU |- *. rewrite Hvs, Hprim in HB, HU |- *.
             pose proof (IH p cp (ctx_set g x SVal) s Ts (PTrieCode.set x (Val v) locals) db
               W B U Hplans Hwf Hloaded Hrest Henv_next Halloc_next Htail HB HU)
               as Hremaining.
             assert (Hprim_rest : action_prim_work V.prim V.prim_work (program_kind p) acts
               (look s (PTrieCode.set x (Val v) locals)) =
               action_prim_work V.prim V.prim_work (program_kind p) acts
                 (update (look s locals) x (Val v))).
             { apply run_action_prim_work_agree. intro y. unfold run_value_view.
               rewrite run_look_set. reflexivity. }
             rewrite Hprim_rest in Hremaining.
             pose proof (run_value_binding_charge args s Ts locals x (Val v) W
               (run_action_weight cp (Let x op args)) Hterms Hx ltac:(cbn; lia)) as Hsyntax.
             pose proof (run_let_clock_split x op args acts s Ts locals db vs v Hvs Hprim)
               as Hclock.
             change (T_apply_go (Let x op args :: acts) s Ts locals db +
               N.of_nat U * D.potential B (apply_go acts s (PTrieCode.set x (Val v) locals) db) <=
               run_action_budget B U W *
                 N.of_nat (run_action_weight cp (Let x op args) + run_actions_weight cp acts + 1) +
               run_term_calls Ts (args ++ flat_map action_terms acts) +
               run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p)
                 (Let x op args :: acts) (look s locals) + N.of_nat U * D.potential B db)%N.
             rewrite run_term_calls_app. cbn [action_prim_work]. rewrite <- Hvalues, Hprim.
             rewrite !Nat2N.inj_add in Hremaining |- *.
             assert (Hpositive : (1 <= N.of_nat (run_action_weight cp (Let x op args)))%N)
               by lia.
             clear -Hsyntax Hclock Hremaining Hprimitive Hfactor Hcharge Hpositive. nia.
          -- pose proof (run_value_binding_charge args s Ts locals x (Id 1) W
               (run_action_weight cp (Let x op args)) Hterms Hx ltac:(cbn; lia)) as Hsyntax.
             assert (Hclock : (T_apply_go (Let x op args :: acts) s Ts locals db <=
               T_term_values s Ts locals args + V.T_prim op vs + 8)%N).
             { time_unfold T_apply_go. rewrite Hvs, Hprim. lia. }
             cbn [apply_go]. rewrite Hvs, Hprim.
             change (T_apply_go (Let x op args :: acts) s Ts locals db +
               N.of_nat U * D.potential B db <=
               run_action_budget B U W *
                 N.of_nat (run_action_weight cp (Let x op args) + run_actions_weight cp acts + 1) +
               run_term_calls Ts (args ++ flat_map action_terms acts) +
               run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p)
                 (Let x op args :: acts) (look s locals) + N.of_nat U * D.potential B db)%N.
             rewrite run_term_calls_app. cbn [action_prim_work]. rewrite <- Hvalues, Hprim.
             rewrite !Nat2N.inj_add.
             assert (Hpositive : (1 <= N.of_nat (run_action_weight cp (Let x op args)))%N)
               by lia.
             clear -Hsyntax Hclock Hprimitive Hfactor Hcharge Hpositive. nia.
        * try rewrite Hvs in Hvalues.
          pose proof (run_value_binding_charge args s Ts locals x (Id 1) W
            (run_action_weight cp (Let x op args)) Hterms Hx ltac:(cbn; lia)) as Hsyntax.
          assert (Hclock : (T_apply_go (Let x op args :: acts) s Ts locals db <=
            T_term_values s Ts locals args + 8)%N).
          { time_unfold T_apply_go. rewrite Hvs. lia. }
          cbn [apply_go]. rewrite Hvs.
          change (T_apply_go (Let x op args :: acts) s Ts locals db +
            N.of_nat U * D.potential B db <=
            run_action_budget B U W *
              N.of_nat (run_action_weight cp (Let x op args) + run_actions_weight cp acts + 1) +
            run_term_calls Ts (args ++ flat_map action_terms acts) +
            run_apply_factor * action_prim_work V.prim V.prim_work (program_kind p)
              (Let x op args :: acts) (look s locals) + N.of_nat U * D.potential B db)%N.
          rewrite run_term_calls_app. cbn [action_prim_work]. rewrite <- Hvalues.
          rewrite !Nat2N.inj_add. clear -Hsyntax Hclock Hcharge. nia.
  Qed.

  Lemma run_apply_wrapper_clock : forall acts s Ts db,
    (T_apply acts s Ts db <= T_apply_go acts s Ts Empty db + 2)%N.
  Proof.
    intros acts s Ts db. time_unfold T_apply. lia.
  Qed.

  (** Applying a rule pays for its actions, referenced bindings and transferred potential. *)
  Lemma T2c_apply_amort : forall B U p cp r s Ts db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    (D.ids (apply (actions V.t r) s db) <= B)%N ->
    D.unit (apply (actions V.t r) s db) <= U ->
    (T_apply (actions V.t r) s Ts db +
      N.of_nat U * D.potential B (apply (actions V.t r) s db) <=
      k_driver * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat ((fold_right (fun a n => match a with
          | Make _ f args | Put f args _ => ((length args + 2) * (length args + 2) *
              (length (filter (fun sl => Pos.eqb (fst sl) f) (Syntax.slots V.t cp)) + 1) + n)%nat
          | Union _ _ => (1 + n)%nat
          | Let _ _ args => (length args + 1 + n)%nat
          end) 0%nat (actions V.t r) + 1)%nat) +
      fold_right N.add 0 (map Ts (flat_map term_vars (flat_map action_terms (actions V.t r)))) +
      k_driver * action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r) s +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U p cp r s Ts db Hplans Hwf Hloaded Hr Hrule Halloc HB HU.
    destruct (run_rule_actions_env p cp r s Hplans Hr Hrule) as [g [Hacts Henv]].
    assert (Henv_empty : env_sorted g (look s Empty)).
    { intros x ty Hx. rewrite run_look_empty. exact (Henv x ty Hx). }
    assert (Halloc_empty : env_allocated db (look s Empty)).
    { intros x i Hx. rewrite run_look_empty in Hx. exact (Halloc x i Hx). }
    pose proof (run_apply_go_amort (actions V.t r) p cp g s Ts Empty db (wbits p) B U
      Hplans Hwf Hloaded Hacts Henv_empty Halloc_empty (run_rule_width p r Hr) HB HU)
      as Hcost.
    assert (Hprim : action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r)
      (look s Empty) = action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r) s).
    { apply run_action_prim_work_agree. intro x. unfold run_value_view.
      rewrite run_look_empty. reflexivity. }
    rewrite Hprim in Hcost.
    pose proof (run_apply_wrapper_clock (actions V.t r) s Ts db) as Hwrapper.
    pose proof run_apply_factor_le as Hfactor.
    assert (Hunit : 1 <= U) by (pose proof (F16_unit_pos (apply (actions V.t r) s db)); lia).
    destruct (run_spending_factors U (N.to_nat (N.log2 B) + 1) (wbits p) Hunit ltac:(lia))
      as [Hpositive _].
    assert (Hweight : (1 <= N.of_nat (run_actions_weight cp (actions V.t r) + 1))%N) by lia.
    change (T_apply (actions V.t r) s Ts db +
      N.of_nat U * D.potential B (apply_go (actions V.t r) s Empty db) <=
      k_driver * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (run_actions_weight cp (actions V.t r) + 1) +
      run_term_calls Ts (flat_map action_terms (actions V.t r)) +
      k_driver * action_prim_work V.prim V.prim_work (program_kind p) (actions V.t r) s +
      N.of_nat U * D.potential B db)%N.
    unfold run_action_budget in Hcost. rewrite Nat2N.inj_mul.
    clear -Hcost Hwrapper Hfactor Hpositive Hweight. nia.
  Qed.
End RunT.
