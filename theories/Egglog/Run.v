(** * Rule plans, plan checking and saturation rounds

    The planner compiles each rule into join plans over shared index slots, the checker
    validates a plan against its program, a round joins, filters and applies the plans of a
    program, and a run drives rounds under its limits.
    For example, the rule [path(x, z) :- path(x, y), edge(y, z)] joins the slots
    [(path, [0; 1])] and [(edge, [0; 1])] on the join variable of [y].
    Builds on: RunSig, Sorts, the binary trie, the self-delimiting codes and the binary-fuel
    loop. *)

From Stdlib Require Import List PArith NArith Arith Bool Lia Relations.Relation_Operators
  Sorting.Sorted Sorting.Permutation.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Code Loop Trie.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig Syntax Model Sorts RunSig.

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

(** Copy variables precede the real variables and have names above every query variable.
    Later fresh names are the only indices that a literal may use. *)
Fixpoint layout_fresh (bound : positive) (copies : nat) (vars : list positive)
    (j : N) (allowed : ptrie unit) : option (ptrie unit) :=
  match vars with
  | [] =>
      match copies with
      | O => Some allowed
      | S _ => None
      end
  | x :: rest =>
      match copies with
      | S copies' =>
          if Pos.ltb bound x then layout_fresh bound copies' rest (N.succ j) allowed
          else None
      | O =>
          let allowed' := if Pos.ltb bound x
            then PTrieCode.set (N.succ_pos j) tt allowed else allowed in
          layout_fresh bound 0 rest (N.succ j) allowed'
      end
  end.
TimeFun layout_fresh.

(** A literal consumes one fresh noncopy index, which no later literal may reuse. *)
Fixpoint layout_literals {V : Type} (srcs : list (source V)) (cols : list (list nat))
    (allowed : ptrie unit) : bool :=
  match srcs, cols with
  | [], [] => true
  | Const _ _ :: rest, [j] :: tail =>
      let key := N.succ_pos (nat_n j) in
      match trie_get key allowed with
      | Some _ => layout_literals rest tail (PTrieCode.remove key allowed)
      | None => false
      end
  | All _ _ :: rest, _ :: tail | New _ _ :: rest, _ :: tail =>
      layout_literals rest tail allowed
  | _, _ => false
  end.
TimeFun layout_literals.

(** Copies, query variables and literals occupy separate join variables. *)
Definition layout_ok {V : Type} (q : list (atom V)) (vars : list positive)
    (srcs : list (source V)) (cols : list (list nat)) : bool :=
  match layout_fresh (query_max q 1%positive) (query_copies q 0) vars 0 Empty with
  | Some allowed => layout_literals srcs cols allowed
  | None => false
  end.
TimeFun layout_ok.

(** A plan names its rule, uses every join variable and lists the post filter of its query. *)
Definition check_cplan {V : Type} (eqb : V -> V -> bool) (newok : bool)
    (table : ptrie (N * (positive * list nat))) (i : N) (r : rule V) (c : cplan V) : bool :=
  match r, c with
  | Rule _ q _, CPlan _ ix (JPlan n cols) srcs vars post =>
      if N.eqb ix i then
        if Nat.eqb (length vars) n then
          match var_table vars 0 Empty with
          | Some names =>
              if layout_ok q vars srcs cols then
                match check_query eqb newok names n table q 0 0 Empty 0 srcs cols [] with
                | Some (count, [], [], expected) =>
                    if N.eqb count (nat_n n) then nats_eqb (rev_append expected []) post
                    else false
                | _ => false
                end
              else false
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

  (** A binding can add only the variable that its term names. *)
  Lemma run_binds_scope : forall g (t : term V.t) s g',
    binds g t s g' -> forall x u, g' x = Some u -> g x = Some u \/ t = Var x.
  Proof.
    intros g t s g' Hbind. destruct Hbind as [y s Hsort|y s Hnone|v];
      intros x u H; try (left; exact H).
    unfold ctx_set in H. destruct (Pos.eqb y x) eqn:Hyx.
    - apply Pos.eqb_eq in Hyx. subst x. right. reflexivity.
    - left. exact H.
  Qed.

  (** Binding arguments adds only variables appearing among those arguments. *)
  Lemma run_binds_list_scope : forall g ts ss g',
    @binds_list V.t g ts ss g' -> forall x u,
    g' x = Some u -> g x = Some u \/ In (Var x) ts.
  Proof.
    intros g ts ss g' Hbind. induction Hbind as [g|g g1 g2 t ts s ss Hhead Htail IH];
      intros x u Hsort.
    - left. exact Hsort.
    - destruct (IH x u Hsort) as [Hbound|Hin].
      + destruct (run_binds_scope g t s g1 Hhead x u Hbound) as [Hold|Heq].
        * left. exact Hold.
        * right. left. exact Heq.
      + right. right. exact Hin.
  Qed.

  (** Binding a result adds only its result variable. *)
  Lemma run_binds_result_scope : forall g out res g',
    @binds_result V.t g out res g' -> forall x u,
    g' x = Some u -> g x = Some u \/ In (Var x) (option_list res).
  Proof.
    intros g out [t|] g' Hbind; destruct out;
      cbn [binds_result out_sort] in Hbind; try contradiction;
      intros x u Hsort.
    - destruct (run_binds_scope g t SId g' Hbind x u Hsort) as [Hold|Heq];
        [left; exact Hold|right; left; exact Heq].
    - destruct (run_binds_scope g t SVal g' Hbind x u Hsort) as [Hold|Heq];
        [left; exact Hold|right; left; exact Heq].
    - subst g'. left. exact Hsort.
  Qed.

  (** Every variable added by a query occurs in one of that query's atoms. *)
  Lemma run_query_scope : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' -> forall x s,
    g' x = Some s -> g x = Some s \/
      exists a, In a q /\ In (Var x) (atom_terms a).
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as
      [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hreads Hargs Hres Hrest IH|
       g g1 op args res rest Hargs Hres Hrest IH]; intros x s Hbound.
    - left. exact Hbound.
    - destruct (IH x s Hbound) as [Hnew|[a [Hin Hvar]]].
      + destruct (run_binds_result_scope g1 out res g2 Hres x s Hnew) as [Harg|Hvar].
        * destruct (run_binds_list_scope g args ss g1 Hargs x s Harg) as [Hold|Hvar].
          -- left. exact Hold.
          -- right. exists (Fun V.t f args res). split; [left; reflexivity|].
             cbn [atom_terms]. apply in_or_app. left. exact Hvar.
        * right. exists (Fun V.t f args res). split; [left; reflexivity|].
          cbn [atom_terms]. apply in_or_app. right. exact Hvar.
      + right. exists a. split; [right; exact Hin|exact Hvar].
    - destruct (IH x s Hbound) as [Hold|[a [Hin Hvar]]].
      + left. exact Hold.
      + right. exists a. split; [right; exact Hin|exact Hvar].
  Qed.

  (** The variable list of an atom is the concatenation of its term variable lists. *)
  Lemma run_atom_vars_terms : forall a : atom V.t,
    atom_vars a = flat_map term_vars (atom_terms a).
  Proof.
    intros [f args res|f args res]; cbn [atom_vars atom_terms]; rewrite flat_map_app.
    - reflexivity.
    - cbn. now rewrite app_nil_r.
  Qed.

  (** A typed term gives a context binding for each variable that it reads. *)
  Lemma run_has_scope : forall g (t : term V.t) s x,
    has g t s -> In x (term_vars t) -> exists u, g x = Some u.
  Proof.
    intros g [y|v] s x Hhas Hin; cbn [has term_vars] in *.
    - destruct Hin as [<-|Hin]; [exists s; exact Hhas|contradiction].
    - contradiction.
  Qed.

  (** A list of typed arguments reads only variables bound in its context. *)
  Lemma run_has_list_scope : forall g ts ss,
    Forall2 (@has V.t g) ts ss -> forall x,
    In x (flat_map term_vars ts) -> exists u, g x = Some u.
  Proof.
    intros g ts ss Htyped. induction Htyped as [|t s ts ss Hhead Htail IH]; intros x Hin.
    - contradiction.
    - cbn [flat_map] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + eapply run_has_scope; eassumption.
      + apply IH. exact Hin.
  Qed.

  (** A sorted action reads only variables already bound in its starting context. *)
  Lemma run_action_scope : forall sorts kinds g a rest,
    @actions_ok V.t sorts kinds g (a :: rest) -> forall x,
    In x (flat_map term_vars (action_terms a)) -> exists u, g x = Some u.
  Proof.
    intros sorts kinds g [y f args|f args res|t u|y op args] rest Hok x Hin;
      cbn [actions_ok action_terms] in Hok, Hin.
    - destruct Hok as [ss [Hsort [Hkind [Hargs Hrest]]]].
      eapply run_has_list_scope; eassumption.
    - destruct Hok as [ss [out [Hsort [Hkind [Hargs [Hres Hrest]]]]]].
      rewrite flat_map_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + eapply run_has_list_scope; eassumption.
      + destruct res as [t|]; [|contradiction].
        cbn [option_list flat_map] in Hin. rewrite app_nil_r in Hin.
        destruct out; cbn [has_result out_sort] in Hres; try contradiction;
          eapply run_has_scope; eassumption.
    - destruct Hok as [Ht [Hu Hrest]]. cbn [flat_map] in Hin.
      rewrite app_nil_r in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + eapply run_has_scope; [exact Ht|exact Hin].
      + eapply run_has_scope; [exact Hu|exact Hin].
    - destruct Hok as [Hargs Hrest]. apply in_flat_map in Hin.
      destruct Hin as [t [Hterm Hvar]]. rewrite Forall_forall in Hargs.
      eapply run_has_scope; [apply Hargs; exact Hterm|exact Hvar].
  Qed.

  (** An action prefix makes available only its explicit bindings. *)
  Lemma run_actions_prefix_scope : forall sorts kinds pre g a rest x,
    @actions_ok V.t sorts kinds g (pre ++ a :: rest) ->
    In x (flat_map term_vars (action_terms a)) ->
    (exists u, g x = Some u) \/ In x (flat_map action_binds pre).
  Proof.
    intros sorts kinds pre. induction pre as [|h pre IH]; intros g a rest x Hok Hin.
    - left. eapply run_action_scope; eassumption.
    - destruct h as [y f args|f args res|t u|y op args];
        cbn [app actions_ok flat_map action_binds] in Hok |- *.
      + destruct Hok as [ss [Hsort [Hkind [Hargs Hrest]]]].
        destruct (IH _ _ _ _ Hrest Hin) as [[s Hbound]|Hbound].
        * unfold ctx_set in Hbound. destruct (Pos.eqb y x) eqn:Heq.
          -- apply Pos.eqb_eq in Heq. right. left. exact Heq.
          -- left. exists s. exact Hbound.
        * right. right. exact Hbound.
      + destruct Hok as [ss [out [Hsort [Hkind [Hargs [Hres Hrest]]]]]].
        exact (IH _ _ _ _ Hrest Hin).
      + destruct Hok as [Ht [Hu Hrest]]. exact (IH _ _ _ _ Hrest Hin).
      + destruct Hok as [Hargs Hrest].
        destruct (IH _ _ _ _ Hrest Hin) as [[s Hbound]|Hbound].
        * unfold ctx_set in Hbound. destruct (Pos.eqb y x) eqn:Heq.
          -- apply Pos.eqb_eq in Heq. right. left. exact Heq.
          -- left. exists s. exact Hbound.
        * right. right. exact Hbound.
  Qed.

  (** Checked actions read only variables bound by the query or earlier actions. *)
  Lemma check_plan_scope : forall p cp r pre a rest x, plans_ok p cp ->
    In r (rules V.t p) -> actions V.t r = pre ++ a :: rest ->
    In x (flat_map term_vars (action_terms a)) ->
    In x (flat_map atom_vars (query V.t r) ++ flat_map action_binds pre).
  Proof.
    intros p cp r pre a rest x Hchecked Hrule Hacts Hvar.
    unfold plans_ok, check_plan in Hchecked. apply andb_true_iff in Hchecked.
    pose proof (proj1 (check_program_spec V.t p) (proj1 Hchecked)) as Hprogram.
    unfold program_ok in Hprogram. rewrite Forall_forall in Hprogram.
    destruct (Hprogram r Hrule) as [g [Hquery Hactions]].
    rewrite Hacts in Hactions.
    destruct (run_actions_prefix_scope _ _ pre g a rest x Hactions Hvar)
      as [[s Hbound]|Hbound]; apply in_or_app.
    - left. destruct (run_query_scope _ _ _ _ _ Hquery x s Hbound)
        as [Hempty|[b [Hatom Hterm]]]; [discriminate|].
      apply in_flat_map. exists b. split; [exact Hatom|].
      rewrite run_atom_vars_terms. apply in_flat_map. exists (Var x).
      split; [exact Hterm|left; reflexivity].
    - right. exact Hbound.
  Qed.

  (** A declaration found by name has the same sorts and kind as both program lookups. *)
  Lemma run_find_decl_fields : forall ds f d,
    find (fun d => Pos.eqb (name d) f) ds = Some d ->
    lookup_sorts ds f = Some (arg_sorts d) /\ lookup_kind ds f = Some (out d).
  Proof.
    intros ds. induction ds as [|h ds IH]; intros f d Hfind; [discriminate|].
    cbn [find lookup_sorts lookup_kind] in *.
    destruct (Pos.eqb (name h) f) eqn:Heq.
    - injection Hfind as <-. split; reflexivity.
    - apply IH. exact Hfind.
  Qed.

  (** A successful sort lookup names the first matching declaration. *)
  Lemma run_lookup_sorts_decl : forall ds f ss,
    lookup_sorts ds f = Some ss ->
    exists d, find (fun d => Pos.eqb (name d) f) ds = Some d /\ arg_sorts d = ss.
  Proof.
    intros ds. induction ds as [|h ds IH]; intros f ss Hsort; [discriminate|].
    cbn [lookup_sorts find] in *. destruct (Pos.eqb (name h) f) eqn:Heq.
    - exists h. split; [reflexivity|]. injection Hsort as Hsort. exact Hsort.
    - apply IH. exact Hsort.
  Qed.

  (** Every sorted action that writes a row has the declared number of arguments. *)
  Lemma run_actions_arities : forall sorts kinds acts g a,
    @actions_ok V.t sorts kinds g acts -> In a acts ->
    match a with
    | Make _ f args | Put f args _ => exists ss, sorts f = Some ss /\ length args = length ss
    | _ => True
    end.
  Proof.
    intros sorts kinds acts. induction acts as [|h acts IH]; intros g a Hok Hin;
      [contradiction|].
    destruct h as [x f args|f args res|t u|x op args]; cbn [actions_ok] in Hok.
    - destruct Hok as [ss [Hsort [Hkind [Hargs Hrest]]]].
      destruct Hin as [<-|Hin].
      + exists ss. split; [exact Hsort|]. eapply Forall2_length. exact Hargs.
      + eapply IH; eassumption.
    - destruct Hok as [ss [out [Hsort [Hkind [Hargs [Hres Hrest]]]]]].
      destruct Hin as [<-|Hin].
      + exists ss. split; [exact Hsort|]. eapply Forall2_length. exact Hargs.
      + eapply IH; eassumption.
    - destruct Hok as [Ht [Hu Hrest]]. destruct Hin as [<-|Hin]; [exact I|].
      eapply IH; eassumption.
    - destruct Hok as [Hargs Hrest]. destruct Hin as [<-|Hin]; [exact I|].
      eapply IH; eassumption.
  Qed.

  (** Checked row-writing actions have their declared argument count. *)
  Lemma check_plan_arities : forall p cp r a, plans_ok p cp ->
    In r (rules V.t p) -> In a (actions V.t r) ->
    match a with
    | Make _ f args | Put f args _ =>
      exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
        length args = length (arg_sorts d)
    | _ => True
    end.
  Proof.
    intros p cp r a Hchecked Hrule Haction.
    unfold plans_ok, check_plan in Hchecked. apply andb_true_iff in Hchecked.
    pose proof (proj1 (check_program_spec V.t p) (proj1 Hchecked)) as Hprogram.
    unfold program_ok in Hprogram. rewrite Forall_forall in Hprogram.
    destruct (Hprogram r Hrule) as [g [Hquery Hactions]].
    pose proof (run_actions_arities _ _ _ g a Hactions Haction) as Harity.
    destruct a as [x f args|f args res|t u|x op args]; try exact I.
    all: destruct Harity as [ss [Hsort Hlength]].
    all: destruct (run_lookup_sorts_decl _ _ _ Hsort) as [d [Hfind Hargs]].
    all: exists d; split; [exact Hfind|now rewrite Hargs].
  Qed.

  (** Declaration widths preserve existing entries and otherwise use the first declaration. *)
  Lemma decl_widths_get : forall ds t f,
    trie_get f (decl_widths ds t) =
      match trie_get f t with
      | Some width => Some width
      | None =>
          match find (fun d => Pos.eqb (name d) f) ds with
          | Some d => Some (length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end)
          | None => None
          end
      end.
  Proof.
    intros ds. induction ds as [|[h ss o] ds IH]; intros t f.
    - cbn [decl_widths find]. destruct (trie_get f t); reflexivity.
    - cbn [decl_widths find name arg_sorts out].
      destruct (Pos.eqb_spec h f) as [->|Hneq].
      + destruct (trie_get f t) as [width|] eqn:Hget; rewrite IH.
        * now rewrite Hget.
        * rewrite PTrie.get_set_same. destruct o; cbn [arg_sorts out];
            now rewrite ?Nat.add_0_r, ?Nat.add_1_r.
      + destruct (trie_get h t) as [width|] eqn:Hget; rewrite IH.
        * reflexivity.
        * rewrite PTrie.get_set_other by congruence. reflexivity.
  Qed.

  (** An absent entry after an insertion was absent before it and has a different key. *)
  Lemma run_get_set_none : forall (t : ptrie unit) k x,
    trie_get x (PTrieCode.set k tt t) = None -> trie_get x t = None /\ x <> k.
  Proof.
    intros t k x Hnone. destruct (Pos.eq_dec x k) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hnone. discriminate.
    - rewrite PTrie.get_set_other in Hnone by congruence. split; assumption.
  Qed.

  (** An accepted permutation has distinct in-range positions that were initially unseen. *)
  Lemma perm_ok_sound : forall perm width seen,
    perm_ok width perm seen = true ->
    NoDup perm /\ Forall (fun i => i < width) perm /\
      forall i, In i perm -> trie_get (nat_code i) seen = None.
  Proof.
    intros perm. induction perm as [|i perm IH]; intros width seen Hok.
    - split; [constructor|]. split; [constructor|]. intros j Hin. contradiction.
    - cbn [perm_ok] in Hok. destruct (trie_get (nat_code i) seen) eqn:Hget;
        [discriminate|].
      destruct (Nat.leb (S i) width) eqn:Hbound; [|discriminate].
      destruct (IH _ _ Hok) as [Hnodup [Hrange Hfresh]].
      split.
      + constructor; [|exact Hnodup]. intro Hin.
        pose proof (Hfresh i Hin) as Hnone. rewrite PTrie.get_set_same in Hnone.
        discriminate.
      + split.
        * constructor; [now apply Nat.leb_le in Hbound|exact Hrange].
        * intros j [<-|Hin]; [exact Hget|].
          destruct (run_get_set_none _ _ _ (Hfresh j Hin)) as [Hnone Hneq]. exact Hnone.
  Qed.

  (** Every slot traversed successfully has a declared width and an accepted permutation. *)
  Lemma slot_table_member : forall sl widths next table result f perm,
    slot_table widths sl next table = Some result -> In (f, perm) sl ->
    exists width, trie_get f widths = Some width /\ perm_ok width perm Empty = true.
  Proof.
    intros sl. induction sl as [|[g ps] sl IH];
      intros widths next table result f perm Htable Hin; [contradiction|].
    cbn [slot_table] in Htable. destruct (trie_get g widths) as [width|] eqn:Hwidth;
      [|discriminate].
    destruct (perm_ok width ps Empty) eqn:Hperm; [|discriminate].
    destruct Hin as [Heq|Hin].
    - injection Heq as <- <-. exists width. split; assumption.
    - destruct (trie_get (slot_code g ps) table); eapply IH; eassumption.
  Qed.

  (** Each accepted slot contains distinct positions within its declared row width. *)
  Lemma check_plan_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) ->
    exists d, find (fun d => Pos.eqb (name d) f) (decls V.t p) = Some d /\
      NoDup perm /\ Forall (fun i => i <
        length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end) perm.
  Proof.
    intros [ds rs] [sl naive semi] f perm Hchecked Hin.
    unfold plans_ok, check_plan, check_shape, check_shape_with in Hchecked.
    apply andb_true_iff in Hchecked. destruct Hchecked as [Hprogram Hshape].
    cbn [decls Syntax.slots] in *.
    destruct (slot_table (decl_widths ds Empty) sl 0 Empty) as [table|] eqn:Htable;
      [|discriminate].
    destruct (slot_table_member sl _ _ _ _ f perm Htable Hin) as [width [Hwidth Hperm]].
    rewrite decl_widths_get, PTrie.get_empty in Hwidth.
    destruct (find (fun d => Pos.eqb (name d) f) ds) as [d|] eqn:Hfind;
      [|discriminate].
    injection Hwidth as <-. exists d. split; [reflexivity|].
    destruct (perm_ok_sound perm _ _ Hperm) as [Hnodup [Hrange Hfresh]].
    split; assumption.
  Qed.

  (** Every accepted compiled plan belongs to a well-sorted program. *)
  Lemma plans_ok_sorted : forall p cp, plans_ok p cp -> program_ok p.
  Proof.
    intros p cp Hchecked. unfold plans_ok, check_plan in Hchecked.
    apply (proj1 (check_program_spec V.t p)).
    apply andb_true_iff in Hchecked. exact (proj1 Hchecked).
  Qed.

  (** The unary slot-position code preserves its natural argument. *)
  Lemma planner_nat_code_inj : forall n m, nat_code n = nat_code m -> n = m.
  Proof.
    induction n as [| n IH]; intros [| m] Hcode; cbn [nat_code] in Hcode;
      try discriminate Hcode.
    - reflexivity.
    - injection Hcode as Htail. f_equal. now apply IH.
  Qed.

  (** The code of a permutation preserves all its positions. *)
  Lemma planner_perm_code_inj : forall xs ys,
    list_code nat_code xs = list_code nat_code ys -> xs = ys.
  Proof.
    induction xs as [| x xs IH]; intros [| y ys] Hcode; cbn [list_code] in Hcode.
    - reflexivity.
    - destruct (nat_code y); cbn [glue] in Hcode; discriminate Hcode.
    - destruct (nat_code x); cbn [glue] in Hcode; discriminate Hcode.
    - destruct (glue_inj _ _ _ _ Hcode) as [Hhead Htail].
      f_equal.
      + now apply planner_nat_code_inj.
      + now apply IH.
  Qed.

  (** Equal slot keys identify the function and permutation. *)
  Lemma planner_slot_code_inj : forall f perm g other,
    slot_code f perm = slot_code g other -> f = g /\ perm = other.
  Proof.
    intros f perm g other Hcode.
    unfold slot_code in Hcode.
    destruct (glue_inj _ _ _ _ Hcode) as [Hname Hperm].
    split; [exact Hname | now apply planner_perm_code_inj].
  Qed.

  Definition planner_rows (st : slot_state) : list (positive * list nat) :=
    match st with
    | SlotState _ _ rows => rows
    end.

  (** Every registered slot key witnesses its exact row in the reversed slot list. *)
  Definition planner_slots_present (st : slot_state) : Prop :=
    match st with
    | SlotState table _ rows =>
        forall f perm s, trie_get (slot_code f perm) table = Some s -> In (f, perm) rows
    end.

  (** Registering a slot retains every previously registered row. *)
  Lemma add_slot_rows : forall f perm st,
    incl (planner_rows st) (planner_rows (snd (add_slot f perm st))).
  Proof.
    intros f perm [table next rows] x Hin.
    cbn [add_slot planner_rows].
    destruct (trie_get (slot_code f perm) table); cbn; auto.
  Qed.

  (** Registering a slot retains the table invariant and makes that slot present. *)
  Lemma add_slot_present : forall f perm st, planner_slots_present st ->
    planner_slots_present (snd (add_slot f perm st)) /\
    In (f, perm) (planner_rows (snd (add_slot f perm st))).
  Proof.
    intros f perm [table next rows] Hpresent.
    cbn [add_slot].
    destruct (trie_get (slot_code f perm) table) as [s |] eqn:Hget.
    - split; [exact Hpresent | now apply (Hpresent f perm s)].
    - split; [| now left].
      intros g other s Hlookup.
      destruct (Pos.eq_dec (slot_code g other) (slot_code f perm)) as [Hsame | Hother].
      + destruct (planner_slot_code_inj _ _ _ _ Hsame) as [-> ->]. now left.
      + rewrite PTrie.get_set_other in Hlookup by exact Hother.
        right. now apply (Hpresent g other s).
  Qed.

  (** Full-slot registration retains the slots it receives. *)
  Lemma full_slots_rows : forall ds seen st,
    incl (planner_rows st) (planner_rows (full_slots ds seen st)).
  Proof.
    induction ds as [| [f ss out] rest IH]; intros seen st x Hin.
    - exact Hin.
    - cbn [full_slots].
      destruct (trie_get f seen) as [u |].
      + now apply IH.
      + destruct out; apply IH; try exact Hin.
        now apply add_slot_rows.
  Qed.

  (** An unseen identifier declaration gets its full slot from its first occurrence. *)
  Lemma full_slots_complete : forall ds seen st f ss,
    planner_slots_present st -> trie_get f seen = None ->
    lookup_kind ds f = Some OId -> lookup_sorts ds f = Some ss ->
    In (f, count_from 0 (S (length ss))) (planner_rows (full_slots ds seen st)).
  Proof.
    induction ds as [| [g sorts o] rest IH]; intros seen st f ss
      Hpresent Hunseen Hkind Hsorts; cbn [lookup_kind lookup_sorts name arg_sorts Syntax.out]
      in Hkind, Hsorts.
    - discriminate Hkind.
    - destruct (Pos.eqb_spec g f) as [Hname | Hname].
      + subst g. injection Hkind as ->. injection Hsorts as ->.
        cbn [full_slots]. rewrite Hunseen.
        apply full_slots_rows.
        exact (proj2 (add_slot_present _ _ _ Hpresent)).
      + cbn [full_slots].
        destruct (trie_get g seen) as [u |] eqn:Hseen.
        * eapply IH; eassumption.
        * assert (Hunseen' : trie_get f (PTrieCode.set g tt seen) = None).
          { rewrite PTrie.get_set_other by congruence. exact Hunseen. }
          destruct o; eapply IH; try eassumption.
          exact (proj1 (add_slot_present _ _ _ Hpresent)).
  Qed.

  (** Planning query atoms only adds slots. *)
  Lemma plan_atoms_rows : forall (base : nat) (q : list (atom V.t)) ai lay st outs post
      lay' st' outs' post',
    plan_atoms base q ai lay st outs post = (lay', st', outs', post') ->
    incl (planner_rows st) (planner_rows st').
  Proof.
    intros base q. induction q as [| a rest IH]; intros ai lay st outs post
      lay' st' outs' post' Hplan x Hin.
    - cbn [plan_atoms] in Hplan. inversion Hplan; subst. exact Hin.
    - destruct a as [f args res | f args res]; cbn [plan_atoms] in Hplan.
      + destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[next pairs] lits] copied] eqn:Hplaced.
        destruct (add_slot f (map snd (sort_pairs pairs)) st)
          as [slot nextst] eqn:Hslot.
        eapply IH; [exact Hplan |].
        pose proof (add_slot_rows f (map snd (sort_pairs pairs)) st x Hin) as Hkeep.
        rewrite Hslot in Hkeep. exact Hkeep.
      + eapply IH; eassumption.
  Qed.

  (** Planning one rule retains the slots already registered. *)
  Lemma plan_rule_rows : forall i (r : rule V.t) st st' c cs,
    plan_rule i r st = (st', c, cs) -> incl (planner_rows st) (planner_rows st').
  Proof.
    intros i [q acts] st st' c cs Hplan.
    cbn [plan_rule] in Hplan.
    destruct (plan_atoms (query_copies q 0) q 0
        (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] outs] post] eqn:Hatoms.
    destruct lay as [names nc nm fresh cn mn].
    inversion Hplan; subst.
    eapply plan_atoms_rows. exact Hatoms.
  Qed.

  (** Planning later rules retains the full slots from the declarations. *)
  Lemma plan_rules_rows : forall (rs : list (rule V.t)) i st naive semi st' naive' semi',
    plan_rules rs i st naive semi = (st', naive', semi') ->
    incl (planner_rows st) (planner_rows st').
  Proof.
    induction rs as [| r rest IH]; intros i st naive semi st' naive' semi'
      Hplan x Hin.
    - cbn [plan_rules] in Hplan. inversion Hplan; subst. exact Hin.
    - cbn [plan_rules] in Hplan.
      destruct (plan_rule i r st) as [[nextst c] cs] eqn:Hrule.
      eapply IH; [exact Hplan |].
      eapply plan_rule_rows; eassumption.
  Qed.

  (** The executable position counter is the standard interval enumeration. *)
  Lemma count_from_seq : forall len start, count_from start len = seq start len.
  Proof.
    induction len as [| len IH]; intro start; cbn [count_from seq].
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma plan_full_slots : forall p f ss, program_kind p f = Some OId ->
    program_sorts p f = Some ss ->
    In (f, seq 0 (S (length ss))) (Syntax.slots V.t (plan p)).
  Proof.
    intros [ds rs] f ss Hkind Hsorts.
    unfold plan, plan_program.
    destruct (plan_rules rs 0%N (full_slots ds Empty (SlotState Empty 0%N [])) [] [])
      as [[[table next rows] naive] semi] eqn:Hrules.
    cbn [Syntax.slots]. rewrite rev_append_rev, app_nil_r.
    apply (proj1 (in_rev rows (f, seq 0 (S (length ss))))).
    pose proof (plan_rules_rows _ _ _ _ _ _ _ _ Hrules) as Hkeep.
    apply Hkeep.
    rewrite <- count_from_seq.
    eapply full_slots_complete.
    - intros g perm s Hget. rewrite PTrie.get_empty in Hget. discriminate Hget.
    - apply PTrie.get_empty.
    - exact Hkind.
    - exact Hsorts.
  Qed.


  (** Distinct in-range positions pass the permutation checker when initially unseen. *)
  Lemma perm_ok_complete : forall perm width seen,
    NoDup perm -> Forall (fun i => i < width) perm ->
    (forall i, In i perm -> trie_get (nat_code i) seen = None) ->
    perm_ok width perm seen = true.
  Proof.
    intros perm. induction perm as [|i perm IH]; intros width seen Hnodup Hrange Hfresh;
      [reflexivity|].
    inversion Hnodup as [|? ? Hnot Htail]; subst.
    inversion Hrange as [|? ? Hbound Hranges]; subst.
    cbn [perm_ok]. rewrite Hfresh by (left; reflexivity).
    assert (Hboundb : Nat.leb (S i) width = true) by (apply Nat.leb_le; exact Hbound).
    rewrite Hboundb. apply IH; [exact Htail|exact Hranges|].
    intros j Hin. rewrite PTrie.get_set_other.
    - apply Hfresh. right. exact Hin.
    - intro Heq. apply planner_nat_code_inj in Heq. subst j. contradiction.
  Qed.

  (** The full declaration-order permutation passes its width check. *)
  Lemma planner_full_perm_ok : forall width,
    perm_ok width (count_from 0 width) Empty = true.
  Proof.
    intro width. rewrite count_from_seq. apply perm_ok_complete.
    - apply seq_NoDup.
    - rewrite Forall_forall. intros i Hin. apply in_seq in Hin. lia.
    - intros i Hin. apply PTrie.get_empty.
  Qed.

  (** A nonempty increasing bounded column passes its checker. *)
  Lemma column_ok_complete : forall lv n prev,
    StronglySorted lt lv -> Forall (fun i => i < n) lv ->
    (match prev with None => lv <> [] | Some k => Forall (fun i => k < i) lv end) ->
    column_ok n lv prev = true.
  Proof.
    intros lv. induction lv as [|l lv IH]; intros n prev Hsorted Hrange Hprev.
    - destruct prev; [reflexivity|exfalso; apply Hprev; reflexivity].
    - inversion Hsorted as [|? ? Htail Hgreater]; subst.
      inversion Hrange as [|? ? Hbound Hranges]; subst.
      assert (Hboundb : Nat.leb (S l) n = true) by (apply Nat.leb_le; exact Hbound).
      destruct prev as [k|]; cbn [column_ok].
      + inversion Hprev as [|? ? Hlower Hlowers]; subst.
        assert (Hlowerb : Nat.leb (S k) l = true) by (apply Nat.leb_le; exact Hlower).
        rewrite Hlowerb, Hboundb. apply IH; assumption.
      + rewrite Hboundb. apply IH; assumption.
  Qed.

  (** Insertion rearranges its input without losing either coordinate. *)
  Lemma planner_insert_pair_perm : forall j pos l,
    Permutation ((j, pos) :: l) (insert_pair j pos l).
  Proof.
    intros j pos l. induction l as [|[k q] l IH]; cbn [insert_pair].
    - apply Permutation_refl.
    - destruct (Nat.leb j k).
      + apply Permutation_refl.
      + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact IH.
  Qed.

  (** Sorting pairs rearranges the input without changing its elements. *)
  Lemma planner_sort_pairs_perm : forall l, Permutation l (sort_pairs l).
  Proof.
    intros l. induction l as [|[j pos] l IH]; cbn [sort_pairs].
    - apply Permutation_refl.
    - eapply Permutation_trans; [apply perm_skip; exact IH|].
      apply planner_insert_pair_perm.
  Qed.

  (** Inserting a fresh first coordinate preserves the strict ordering of pairs. *)
  Lemma planner_insert_pair_sorted : forall l j pos,
    StronglySorted (fun a b : nat * nat => fst a < fst b) l ->
    ~ In j (map fst l) ->
    StronglySorted (fun a b : nat * nat => fst a < fst b) (insert_pair j pos l).
  Proof.
    intros l. induction l as [|[k q] l IH]; intros j pos Hsorted Hfresh.
    - cbn [insert_pair]. constructor; constructor.
    - inversion Hsorted as [|? ? Htail Hgreater]; subst.
      cbn [insert_pair]. destruct (Nat.leb j k) eqn:Hcompare.
      + constructor; [exact Hsorted|]. constructor.
        * cbn. apply Nat.leb_le in Hcompare. assert (j <> k).
          { intro Heq. apply Hfresh. cbn. left. symmetry. exact Heq. }
          lia.
        * rewrite Forall_forall in *. intros [m r] Hin. cbn.
          specialize (Hgreater (m, r) Hin). cbn in Hgreater.
          apply Nat.leb_le in Hcompare. lia.
      + constructor.
        * apply IH; [exact Htail|]. intro Hin. apply Hfresh. right. exact Hin.
        * eapply Permutation_Forall; [apply planner_insert_pair_perm|].
          constructor; [cbn; now apply Nat.leb_gt in Hcompare|exact Hgreater].
  Qed.

  (** Sorting distinct first coordinates produces a strictly increasing pair list. *)
  Lemma planner_sort_pairs_sorted : forall l,
    NoDup (map fst l) ->
    StronglySorted (fun a b : nat * nat => fst a < fst b) (sort_pairs l).
  Proof.
    intros l. induction l as [|[j pos] l IH]; intro Hnodup.
    - constructor.
    - cbn [map] in Hnodup. inversion Hnodup as [|? ? Hfresh Htail]; subst.
      cbn [sort_pairs]. apply planner_insert_pair_sorted; [apply IH; exact Htail|].
      intro Hin. apply Hfresh. eapply Permutation_in; [|exact Hin].
      apply Permutation_sym. apply Permutation_map. apply planner_sort_pairs_perm.
  Qed.

  (** Projecting ordered pairs preserves their first-coordinate ordering. *)
  Lemma planner_pair_column_sorted : forall l,
    StronglySorted (fun a b : nat * nat => fst a < fst b) l ->
    StronglySorted lt (map fst l).
  Proof.
    intros l Hsorted. induction Hsorted as [|[j pos] l Htail IH Hgreater].
    - constructor.
    - cbn [map]. constructor; [exact IH|].
      rewrite Forall_map. exact Hgreater.
  Qed.

  (** Sorting preserves every distinct projection of the pair list. *)
  Lemma planner_sort_pairs_nodup : forall (f : nat * nat -> nat) l,
    NoDup (map f l) -> NoDup (map f (sort_pairs l)).
  Proof.
    intros f l Hnodup. eapply Permutation_NoDup; [|exact Hnodup].
    apply Permutation_map. apply planner_sort_pairs_perm.
  Qed.

  (** Sorting preserves every elementwise property of its pairs. *)
  Lemma planner_sort_pairs_forall : forall (P : nat * nat -> Prop) l,
    Forall P l -> Forall P (sort_pairs l).
  Proof.
    intros P l Hall. eapply Permutation_Forall; [apply planner_sort_pairs_perm|exact Hall].
  Qed.

  (** Sorting leaves the pair count unchanged. *)
  Lemma planner_sort_pairs_length : forall l, length (sort_pairs l) = length l.
  Proof.
    intro l. symmetry. apply Permutation_length. apply planner_sort_pairs_perm.
  Qed.

  (** Sorting a nonempty bounded set of first coordinates produces an accepted column. *)
  Lemma planner_sorted_column_ok : forall pairs n,
    pairs <> [] -> NoDup (map fst pairs) -> Forall (fun p => fst p < n) pairs ->
    column_ok n (map fst (sort_pairs pairs)) None = true.
  Proof.
    intros pairs n Hnonempty Hnodup Hrange. apply column_ok_complete.
    - apply planner_pair_column_sorted. apply planner_sort_pairs_sorted. exact Hnodup.
    - rewrite Forall_map. apply planner_sort_pairs_forall. exact Hrange.
    - intro Hempty. apply (f_equal (@length nat)) in Hempty.
      rewrite length_map, planner_sort_pairs_length in Hempty.
      destruct pairs; [contradiction|discriminate].
  Qed.

  (** Sorting bounded distinct positions produces an accepted slot permutation. *)
  Lemma planner_sorted_perm_ok : forall pairs width,
    NoDup (map snd pairs) -> Forall (fun p => snd p < width) pairs ->
    perm_ok width (map snd (sort_pairs pairs)) Empty = true.
  Proof.
    intros pairs width Hnodup Hrange. apply perm_ok_complete.
    - apply planner_sort_pairs_nodup. exact Hnodup.
    - rewrite Forall_map. apply planner_sort_pairs_forall. exact Hrange.
    - intros i Hin. apply PTrie.get_empty.
  Qed.

  (** Appending one row keeps every old position and adds only the final position. *)
  Lemma planner_nth_error_snoc : forall (A : Type) (xs : list A) x i y,
    nth_error (xs ++ [x]) i = Some y <->
      nth_error xs i = Some y \/ i = length xs /\ y = x.
  Proof.
    intros A xs. induction xs as [| a xs IH]; intros x [| i] y; cbn.
    - split.
      + intro H. injection H as <-. now right.
      + intros [H | [_ ->]]; [discriminate H | reflexivity].
    - rewrite nth_error_nil. split; [discriminate |].
      intros [H | [H _]]; discriminate H.
    - split; [now left | intros [H | [H _]]; [exact H | discriminate H]].
    - rewrite IH. split.
      + intros [H | [H ->]]; [now left | right; split; [now f_equal | reflexivity]].
      + intros [H | [H ->]]; [now left | right; split; [now injection H | reflexivity]].
  Qed.

  (** The next slot number is the length of the forward rows, whose positions match the trie. *)
  Definition planner_state_exact (st : slot_state) : Prop :=
    match st with
    | SlotState table next rows =>
        next = N.of_nat (length rows) /\
        forall f perm s, trie_get (slot_code f perm) table = Some s <->
          nth_error (rev rows) (N.to_nat s) = Some (f, perm)
    end.

  (** The empty planner state numbers no slot. *)
  Lemma planner_state_empty : planner_state_exact (SlotState Empty 0%N []).
  Proof.
    split; [reflexivity |].
    intros f perm s. rewrite PTrie.get_empty.
    destruct (N.to_nat s); cbn; split; discriminate.
  Qed.

  (** Adding a slot preserves the exact forward numbering of all slots. *)
  Lemma add_slot_exact : forall f perm st, planner_state_exact st ->
    planner_state_exact (snd (add_slot f perm st)).
  Proof.
    intros f perm [table next rows] [Hnext Htable].
    cbn [add_slot].
    destruct (trie_get (slot_code f perm) table) as [found |] eqn:Hfind.
    - split; assumption.
    - split.
      + cbn [length]. rewrite Hnext, Nat2N.inj_succ. reflexivity.
      + intros g other s.
        cbn [rev]. rewrite planner_nth_error_snoc, length_rev.
        destruct (Pos.eq_dec (slot_code g other) (slot_code f perm)) as [Hsame | Hother].
        * destruct (planner_slot_code_inj _ _ _ _ Hsame) as [-> ->].
          rewrite PTrie.get_set_same. split.
          -- intro Heq. injection Heq as <-. right. split; [| reflexivity].
             rewrite Hnext, Nat2N.id. reflexivity.
          -- intros [Hold | [Hindex _]].
             ++ apply Htable in Hold. rewrite Hfind in Hold. discriminate Hold.
             ++ f_equal. apply N2Nat.inj. rewrite Hnext, Nat2N.id. symmetry. exact Hindex.
        * rewrite PTrie.get_set_other by exact Hother.
          rewrite Htable. split; [now left |].
          intros [Hold | [_ Hrow]]; [exact Hold |].
          injection Hrow as -> ->. exfalso. apply Hother. reflexivity.
  Qed.

  (** Registering identifier declarations preserves exact slot numbering. *)
  Lemma full_slots_exact : forall ds seen st, planner_state_exact st ->
    planner_state_exact (full_slots ds seen st).
  Proof.
    induction ds as [| [f ss o] rest IH]; intros seen st Hstate.
    - exact Hstate.
    - cbn [full_slots]. destruct (trie_get f seen) as [u |].
      + now apply IH.
      + destruct o; apply IH; try exact Hstate. now apply add_slot_exact.
  Qed.

  (** Planning query atoms preserves exact slot numbering. *)
  Lemma plan_atoms_exact : forall base (q : list (atom V.t)) ai lay st outs post
      lay' st' outs' post',
    planner_state_exact st ->
    plan_atoms base q ai lay st outs post = (lay', st', outs', post') ->
    planner_state_exact st'.
  Proof.
    intros base q. induction q as [| a rest IH]; intros ai lay st outs post
      lay' st' outs' post' Hstate Hplan.
    - cbn [plan_atoms] in Hplan. inversion Hplan; subst. exact Hstate.
    - destruct a as [f args res | f args res]; cbn [plan_atoms] in Hplan.
      + destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[next pairs] lits] copied] eqn:Hplaced.
        destruct (add_slot f (map snd (sort_pairs pairs)) st)
          as [slot nextst] eqn:Hslot.
        eapply IH; [| exact Hplan].
        pose proof (add_slot_exact f (map snd (sort_pairs pairs)) st Hstate) as Hkeep.
        rewrite Hslot in Hkeep. exact Hkeep.
      + eapply IH; eassumption.
  Qed.

  (** Planning a rule preserves exact slot numbering. *)
  Lemma plan_rule_exact : forall i (r : rule V.t) st st' c cs,
    planner_state_exact st -> plan_rule i r st = (st', c, cs) -> planner_state_exact st'.
  Proof.
    intros i [q acts] st st' c cs Hstate Hplan.
    cbn [plan_rule] in Hplan.
    destruct (plan_atoms (query_copies q 0) q 0
        (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] outs] post] eqn:Hatoms.
    destruct lay as [names nc nm fresh cn mn]. inversion Hplan; subst.
    eapply plan_atoms_exact; eassumption.
  Qed.

  (** Planning all rules preserves exact slot numbering. *)
  Lemma plan_rules_exact : forall (rs : list (rule V.t)) i st naive semi st' naive' semi',
    planner_state_exact st -> plan_rules rs i st naive semi = (st', naive', semi') ->
    planner_state_exact st'.
  Proof.
    induction rs as [| r rest IH]; intros i st naive semi st' naive' semi' Hstate Hplan.
    - cbn [plan_rules] in Hplan. inversion Hplan; subst. exact Hstate.
    - cbn [plan_rules] in Hplan.
      destruct (plan_rule i r st) as [[nextst c] cs] eqn:Hrule.
      eapply IH; [| exact Hplan]. eapply plan_rule_exact; eassumption.
  Qed.

  (** A trie assigning one number per slot makes all forward rows distinct. *)
  Lemma planner_rows_nodup : forall table next rows,
    planner_state_exact (SlotState table next rows) -> NoDup (rev rows).
  Proof.
    intros table next rows [_ Htable]. apply NoDup_nth_error.
    intros i j Hibound Hsame.
    destruct (nth_error (rev rows) i) as [[f perm] |] eqn:Hrow.
    - assert (Hi : trie_get (slot_code f perm) table = Some (N.of_nat i)).
      { apply Htable. now rewrite Nat2N.id. }
      assert (Hj : trie_get (slot_code f perm) table = Some (N.of_nat j)).
      { apply Htable. rewrite Nat2N.id. symmetry. exact Hsame. }
      assert (Hij : N.of_nat i = N.of_nat j) by congruence.
      now apply Nat2N.inj.
    - apply nth_error_None in Hrow. exfalso.
      exact (Nat.lt_irrefl i (Nat.lt_le_trans _ _ _ Hibound Hrow)).
  Qed.

  (** A completed slot scan retains every entry already in its table. *)
  Lemma slot_table_keeps : forall widths sl next table table',
    slot_table widths sl next table = Some table' ->
    forall key value, trie_get key table = Some value -> trie_get key table' = Some value.
  Proof.
    intros widths sl. induction sl as [| [f perm] rest IH]; intros next table table' Hscan
      key value Hget.
    - cbn [slot_table] in Hscan. inversion Hscan; subst. exact Hget.
    - cbn [slot_table] in Hscan.
      destruct (trie_get f widths) as [width |]; [| discriminate Hscan].
      destruct (perm_ok width perm Empty); [| discriminate Hscan].
      destruct (trie_get (slot_code f perm) table) as [entry |] eqn:Hentry.
      + eapply IH; eassumption.
      + eapply IH; [exact Hscan |].
        rewrite PTrie.get_set_other; [exact Hget |].
        intro Heq. subst key. rewrite Hentry in Hget. discriminate Hget.
  Qed.

  (** A list of valid slot declarations always produces a checked table. *)
  Lemma slot_table_complete : forall widths sl next table,
    Forall (fun fp => exists width, trie_get (fst fp) widths = Some width /\
      perm_ok width (snd fp) Empty = true) sl ->
    exists table', slot_table widths sl next table = Some table'.
  Proof.
    intros widths sl. induction sl as [| [f perm] rest IH]; intros next table Hvalid.
    - exists table. reflexivity.
    - inversion Hvalid as [| fp remaining Hhead Htail]; subst.
      destruct Hhead as [width [Hwidth Hperm]]. cbn in Hwidth, Hperm.
      cbn [slot_table]. rewrite Hwidth, Hperm.
      destruct (trie_get (slot_code f perm) table); now apply IH.
  Qed.

  (** A checked scan numbers distinct rows from its starting index. *)
  Lemma slot_table_numbers : forall widths sl next table table',
    NoDup sl ->
    (forall f perm, In (f, perm) sl -> trie_get (slot_code f perm) table = None) ->
    slot_table widths sl next table = Some table' ->
    forall i f perm, nth_error sl i = Some (f, perm) ->
      trie_get (slot_code f perm) table' = Some ((next + N.of_nat i)%N, (f, perm)).
  Proof.
    intros widths sl. induction sl as [| [g other] rest IH]; intros next table table'
      Hdistinct Hfresh Hscan i f perm Hrow.
    - destruct i; discriminate Hrow.
    - inversion Hdistinct as [| fp remaining Habsent Htail]; subst.
      cbn [slot_table] in Hscan.
      destruct (trie_get g widths) as [width |]; [| discriminate Hscan].
      destruct (perm_ok width other Empty); [| discriminate Hscan].
      rewrite (Hfresh g other (or_introl eq_refl)) in Hscan.
      destruct i as [| i].
      + cbn in Hrow. injection Hrow as -> ->.
        rewrite N.add_0_r.
        eapply slot_table_keeps; [exact Hscan | apply PTrie.get_set_same].
      + cbn in Hrow.
        assert (Hnew : forall h ps, In (h, ps) rest ->
            trie_get (slot_code h ps)
              (PTrieCode.set (slot_code g other) (next, (g, other)) table) = None).
        { intros h ps Hin. rewrite PTrie.get_set_other.
          - apply Hfresh. now right.
          - intro Heq. destruct (planner_slot_code_inj _ _ _ _ Heq) as [-> ->].
            exact (Habsent Hin). }
        specialize (IH (N.succ next) _ _ Htail Hnew Hscan i f perm Hrow).
        rewrite Nat2N.inj_succ, N.add_succ_r, <- N.add_succ_l. exact IH.
  Qed.

  (** The checking table reconstructs the numbers in a valid planner state. *)
  Lemma planner_slot_table : forall widths table next rows,
    planner_state_exact (SlotState table next rows) ->
    Forall (fun fp => exists width, trie_get (fst fp) widths = Some width /\
      perm_ok width (snd fp) Empty = true) (rev rows) ->
    exists checked, slot_table widths (rev rows) 0%N Empty = Some checked /\
      forall f perm s, trie_get (slot_code f perm) table = Some s ->
        trie_get (slot_code f perm) checked = Some (s, (f, perm)).
  Proof.
    intros widths table next rows Hstate Hvalid.
    destruct (slot_table_complete widths (rev rows) 0%N Empty Hvalid) as [checked Hscan].
    exists checked. split; [exact Hscan |].
    intros f perm s Hget.
    pose proof (planner_rows_nodup table next rows Hstate) as Hdistinct.
    destruct Hstate as [_ Hexact].
    assert (Hfresh : forall g ps, In (g, ps) (rev rows) ->
        trie_get (slot_code g ps) (@Empty (N * (positive * list nat))) = None).
    { intros. apply PTrie.get_empty. }
    pose proof (slot_table_numbers widths (rev rows) 0%N Empty checked Hdistinct
      Hfresh Hscan (N.to_nat s) f perm (proj1 (Hexact f perm s) Hget)) as Hnumber.
    rewrite N.add_0_l, N2Nat.id in Hnumber. exact Hnumber.
  Qed.

  (** The executable natural-to-binary counter agrees with the standard conversion. *)
  Lemma planner_nat_n_spec : forall n, nat_n n = N.of_nat n.
  Proof.
    induction n as [|n IH]; cbn [nat_n].
    - reflexivity.
    - now rewrite IH, Nat2N.inj_succ.
  Qed.

  (** Positive keys used by column tables distinguish natural column indexes. *)
  Lemma planner_column_key_inj : forall i j,
    N.succ_pos (nat_n i) = N.succ_pos (nat_n j) -> i = j.
  Proof.
    intros i j Heq.
    assert (Hnext : N.succ (nat_n i) = N.succ (nat_n j)).
    { rewrite <- !N.succ_pos_spec. now rewrite Heq. }
    apply N.succ_inj in Hnext. rewrite !planner_nat_n_spec in Hnext.
    now apply Nat2N.inj in Hnext.
  Qed.

  (** The columns of literals are listed in atom order and then literal order. *)
  Definition planner_literal_indices (atoms : list (atom_plan V.t)) : list nat :=
    flat_map (fun a => match a with AtomPlan _ _ lits => map fst lits end) atoms.

  (** Distinct concatenated lists have disjoint members. *)
  Lemma planner_nodup_disjoint : forall (xs ys : list nat),
    NoDup (xs ++ ys) -> forall x, In x xs -> ~ In x ys.
  Proof.
    induction xs as [|a xs IH]; intros ys Hnodup x Hin.
    - contradiction.
    - cbn [app] in Hnodup. inversion Hnodup as [|? ? Hnot Htail]; subst.
      destruct Hin as [<-|Hin].
      + intro Hiny. apply Hnot. apply in_or_app. right. exact Hiny.
      + eapply IH; eassumption.
  Qed.

  (** Consuming a literal block preserves every index outside that block. *)
  Lemma planner_layout_literal_prefix : forall (lits : list (nat * V.t)) srcs cols allowed,
    NoDup (map fst lits) ->
    (forall j, In j (map fst lits) ->
      trie_get (N.succ_pos (nat_n j)) allowed = Some tt) ->
    (forall next,
      (forall j, ~ In j (map fst lits) ->
        trie_get (N.succ_pos (nat_n j)) next = trie_get (N.succ_pos (nat_n j)) allowed) ->
      layout_literals srcs cols next = true) ->
    layout_literals (literal_sources lits srcs) (literal_cols lits cols) allowed = true.
  Proof.
    induction lits as [|[j v] lits IH]; intros srcs cols allowed Hnodup Hallowed Htail.
    - cbn [literal_sources literal_cols]. apply Htail. intros k _. reflexivity.
    - cbn [map] in Hnodup. inversion Hnodup as [|? ? Hnot Hrest]; subst.
      cbn [literal_sources literal_cols layout_literals].
      rewrite (Hallowed j (or_introl eq_refl)). apply IH.
      + exact Hrest.
      + intros k Hin. rewrite PTrie.get_remove_other.
        * apply Hallowed. right. exact Hin.
        * intro Heq. apply planner_column_key_inj in Heq. subst k. contradiction.
      + intros next Hkeeps. apply Htail. intros k Houtside.
        rewrite Hkeeps.
        * apply PTrie.get_remove_other. intro Heq.
          apply planner_column_key_inj in Heq. subst k. apply Houtside. left. reflexivity.
        * intro Hin. apply Houtside. right. exact Hin.
  Qed.

  (** Distinct eligible literal columns pass the layout guard in a planned source list. *)
  Lemma layout_literals_plans : forall (atoms : list (atom_plan V.t)) pivot allowed,
    NoDup (planner_literal_indices atoms) ->
    (forall j, In j (planner_literal_indices atoms) ->
      trie_get (N.succ_pos (nat_n j)) allowed = Some tt) ->
    layout_literals (plan_srcs atoms pivot) (plan_cols atoms) allowed = true.
  Proof.
    induction atoms as [|[slot col lits] atoms IH]; intros pivot allowed Hnodup Hallowed.
    - reflexivity.
    - change (NoDup (map fst lits ++ planner_literal_indices atoms)) in Hnodup.
      cbn [plan_srcs plan_cols].
      assert (Hbody : layout_literals
          (literal_sources lits (plan_srcs atoms (pivot_next pivot)))
          (literal_cols lits (plan_cols atoms)) allowed = true).
      {
        apply planner_layout_literal_prefix.
        - eapply NoDup_app_remove_r. exact Hnodup.
        - intros j Hin. apply Hallowed. apply in_or_app. left. exact Hin.
        - intros next Hkeeps. apply IH.
          + eapply NoDup_app_remove_l. exact Hnodup.
          + intros j Hin. rewrite Hkeeps.
            * apply Hallowed. apply in_or_app. right. exact Hin.
            * intro Hinlit. exact (planner_nodup_disjoint _ _ Hnodup j Hinlit Hin).
      }
      destruct pivot as [[|n]|]; exact Hbody.
  Qed.

  (** The variable maximum bounds both inputs. *)
  Lemma planner_pos_max_bounds : forall x y,
    (x <= pos_max x y /\ y <= pos_max x y)%positive.
  Proof.
    intros x y. unfold pos_max. destruct (Pos.compare x y) eqn:Hcompare.
    - apply Pos.compare_eq_iff in Hcompare. subst y. split; apply Pos.le_refl.
    - apply Pos.compare_lt_iff in Hcompare. split.
      + apply Pos.lt_le_incl. exact Hcompare.
      + apply Pos.le_refl.
    - apply Pos.compare_gt_iff in Hcompare. split.
      + apply Pos.le_refl.
      + apply Pos.lt_le_incl. exact Hcompare.
  Qed.

  (** Scanning one term never decreases the running maximum. *)
  Lemma planner_term_max_seed : forall (t : term V.t) m,
    (m <= term_max t m)%positive.
  Proof.
    intros [x|v] m; cbn [term_max].
    - exact (proj2 (planner_pos_max_bounds x m)).
    - apply Pos.le_refl.
  Qed.

  (** Scanning terms never decreases the running maximum. *)
  Lemma planner_terms_max_seed : forall (ts : list (term V.t)) m,
    (m <= terms_max ts m)%positive.
  Proof.
    induction ts as [|t rest IH]; intro m; cbn [terms_max].
    - apply Pos.le_refl.
    - eapply Pos.le_trans.
      + apply planner_term_max_seed.
      + apply IH.
  Qed.

  (** Every variable encountered by the term scan is bounded by its final maximum. *)
  Lemma planner_terms_max_member : forall (ts : list (term V.t)) m x,
    In (Var x) ts -> (x <= terms_max ts m)%positive.
  Proof.
    induction ts as [|t rest IH]; intros m x Hin; cbn [terms_max] in *.
    - contradiction.
    - destruct Hin as [Heq|Hin].
      + subst t. eapply Pos.le_trans.
        * exact (proj1 (planner_pos_max_bounds x m)).
        * apply planner_terms_max_seed.
      + exact (IH (term_max t m) x Hin).
  Qed.

  (** Scanning a query never decreases the running maximum. *)
  Lemma planner_query_max_seed : forall (q : list (atom V.t)) m,
    (m <= query_max q m)%positive.
  Proof.
    induction q as [|a rest IH]; intro m; cbn [query_max].
    - apply Pos.le_refl.
    - destruct a as [f args res|p args res]; eapply Pos.le_trans.
      + apply planner_terms_max_seed.
      + apply IH.
      + apply planner_terms_max_seed.
      + apply IH.
  Qed.

  (** The query maximum bounds every real query variable. *)
  Lemma planner_query_max_member : forall (q : list (atom V.t)) m x,
    In (Var x) (flat_map atom_terms q) -> (x <= query_max q m)%positive.
  Proof.
    induction q as [|a rest IH]; intros m x Hin; cbn [flat_map] in Hin.
    - contradiction.
    - apply in_app_iff in Hin. destruct a as [f args res|p args res];
        cbn [query_max]; destruct Hin as [Hin|Hin].
      + eapply Pos.le_trans.
        * apply planner_terms_max_member. exact Hin.
        * apply planner_query_max_seed.
      + apply IH. exact Hin.
      + eapply Pos.le_trans.
        * apply (planner_terms_max_member (res :: args) m x). cbn [atom_terms] in Hin.
          apply in_app_iff in Hin. destruct Hin as [Hin|[Heq|[]]].
          -- right. exact Hin.
          -- left. exact Heq.
        * apply planner_query_max_seed.
      + apply IH. exact Hin.
  Qed.

  (** The duplicate counter adds the same number at every initial offset. *)
  Lemma planner_term_copies_acc : forall (ts : list (term V.t)) seen n,
    term_copies seen ts n = n + term_copies seen ts 0.
  Proof.
    induction ts as [|t rest IH]; intros seen n; cbn [term_copies].
    - now rewrite Nat.add_0_r.
    - destruct t as [x|v]; cbn [term_copies].
      + destruct (trie_get x seen).
        * rewrite (IH seen (S n)), (IH seen 1). lia.
        * apply IH.
      + apply IH.
  Qed.

  (** The query duplicate counter adds the same number at every initial offset. *)
  Lemma planner_query_copies_acc : forall (q : list (atom V.t)) n,
    query_copies q n = n + query_copies q 0.
  Proof.
    induction q as [|a rest IH]; intro n; cbn [query_copies].
    - now rewrite Nat.add_0_r.
    - destruct a as [f args res|p args res]; cbn [query_copies].
      + rewrite (IH (term_copies Empty (args ++ option_list res) n)),
          (IH (term_copies Empty (args ++ option_list res) 0)),
          planner_term_copies_acc. lia.
      + apply IH.
  Qed.

  (** Placing terms allocates exactly the copies counted by the preliminary scan. *)
  Lemma planner_place_copies : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied,
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (VarLayout _ nc' _ _ _ _, _, _, _) => nc' = term_copies seen ts nc
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
        pairs lits copied; cbn [place_terms term_copies].
    - reflexivity.
    - destruct t as [x|v]; cbn [place_terms term_copies].
      + destruct (trie_get x seen).
        * apply IH.
        * destruct (trie_get x names); apply IH.
      + apply IH.
  Qed.

  (** Placing terms preserves the correspondence between layout counters and name lists. *)
  Lemma planner_place_lengths : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied,
    nc = length cn -> nm = length mn ->
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (VarLayout _ nc' nm' _ cn' mn', _, _, _) =>
        nc' = length cn' /\ nm' = length mn'
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
        pairs lits copied Hcn Hmn; cbn [place_terms].
    - split; assumption.
    - destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen).
        * apply IH; cbn; congruence.
        * destruct (trie_get x names); apply IH; cbn; congruence.
      + apply IH; cbn; congruence.
  Qed.

  (** Planning atoms allocates exactly the copies counted by the preliminary scan. *)
  Lemma planner_atoms_copies : forall (q : list (atom V.t)) base ai
      names nc nm fresh cn mn st outs post,
    match plan_atoms base q ai (VarLayout names nc nm fresh cn mn) st outs post with
    | (VarLayout _ nc' _ _ _ _, _, _, _) => nc' = query_copies q nc
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai names nc nm fresh cn mn st outs post;
      cbn [plan_atoms query_copies].
    - reflexivity.
    - destruct a as [f args res|p args res]; cbn [plan_atoms query_copies].
      + pose proof (planner_place_copies (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false) as Hcopies.
        destruct (place_terms base (args ++ option_list res) 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false)
          as [[[lay pairs] lits] copied].
        destruct lay as [names' nc' nm' fresh' cn' mn']; cbn in Hcopies.
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        rewrite <- Hcopies. apply IH.
      + apply IH.
  Qed.

  (** Planning atoms preserves the correspondence between counters and name lists. *)
  Lemma planner_atoms_lengths : forall (q : list (atom V.t)) base ai
      names nc nm fresh cn mn st outs post,
    nc = length cn -> nm = length mn ->
    match plan_atoms base q ai (VarLayout names nc nm fresh cn mn) st outs post with
    | (VarLayout _ nc' nm' _ cn' mn', _, _, _) =>
        nc' = length cn' /\ nm' = length mn'
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai names nc nm fresh cn mn st outs post
      Hcn Hmn; cbn [plan_atoms].
    - split; assumption.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + pose proof (planner_place_lengths (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false Hcn Hmn) as Hlengths.
        destruct (place_terms base (args ++ option_list res) 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false)
          as [[[lay pairs] lits] copied].
        destruct lay as [names' nc' nm' fresh' cn' mn']; cbn in Hlengths.
        destruct Hlengths as [Hcn' Hmn'].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        apply IH; assumption.
      + apply IH; assumption.
  Qed.

  (** Distinct unbound names can be numbered without changing existing bindings. *)
  Lemma planner_var_table_complete : forall vars j (t : ptrie N), NoDup vars ->
    (forall x, In x vars -> trie_get x t = None) ->
    exists result, var_table vars j t = Some result /\
      (forall x k, trie_get x t = Some k -> trie_get x result = Some k) /\
      (forall n x, nth_error vars n = Some x ->
        trie_get x result = Some (j + N.of_nat n)%N).
  Proof.
    induction vars as [|x rest IH]; intros j t Hnodup Hnone.
    - exists t. split; [reflexivity|]. split; [auto|].
      intros [|n] y Hnth; discriminate.
    - inversion Hnodup as [|x' rest' Hnot Hrest]; subst x' rest'.
      assert (Hnone' : forall y, In y rest ->
          trie_get y (PTrieCode.set x j t) = None).
      {
        intros y Hin. rewrite PTrie.get_set_other.
        - apply Hnone. now right.
        - intro Heq. subst y. contradiction.
      }
      destruct (IH (N.succ j) (PTrieCode.set x j t) Hrest Hnone')
        as [result [Htable [Hpreserve Hlookup]]].
      exists result. split.
      + cbn [var_table]. rewrite (Hnone x (or_introl eq_refl)). exact Htable.
      + split.
        * intros y k Hold. apply Hpreserve. rewrite PTrie.get_set_other.
          -- exact Hold.
          -- intro Heq. subst y. rewrite (Hnone x (or_introl eq_refl)) in Hold.
             discriminate.
        * intros [|n] y Hnth; cbn [nth_error] in Hnth.
          -- injection Hnth as <-. rewrite N.add_0_r. apply Hpreserve.
             apply PTrie.get_set_same.
          -- replace (j + N.of_nat (S n))%N with (N.succ j + N.of_nat n)%N
               by (rewrite Nat2N.inj_succ; lia).
             exact (Hlookup n y Hnth).
  Qed.

  (** Numbering distinct names from an empty table recovers their list positions. *)
  Lemma planner_var_table_empty : forall vars, NoDup vars ->
    exists names, var_table vars 0 Empty = Some names /\
      forall n x, nth_error vars n = Some x -> trie_get x names = Some (N.of_nat n).
  Proof.
    intros vars Hnodup.
    destruct (planner_var_table_complete vars 0 Empty Hnodup)
      as [names [Htable [_ Hlookup]]].
    - intros x _. apply PTrie.get_empty.
    - exists names. split; [exact Htable|]. intros n x Hnth.
      exact (Hlookup n x Hnth).
  Qed.

  (** Generated names are distinct; copies and unregistered main names are fresh. *)
  Definition planner_names_ok (bound : positive) (lay : var_layout) : Prop :=
    match lay with
    | VarLayout names _ _ fresh cn mn =>
        (bound < fresh)%positive /\ NoDup (cn ++ mn) /\
        Forall (fun x => (x < fresh)%positive) (cn ++ mn) /\
        Forall (fun x => (bound < x)%positive) cn /\
        (forall x, In x mn -> trie_get x names = None -> (bound < x)%positive)
    end.

  (** A newly generated copy name is distinct from all earlier names. *)
  Lemma planner_names_copy : forall bound names nc nm fresh cn mn,
    planner_names_ok bound (VarLayout names nc nm fresh cn mn) ->
    planner_names_ok bound
      (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn).
  Proof.
    intros bound names nc nm fresh cn mn [Hbound [Hnodup [Hbelow [Hcopies Hmain]]]].
    cbn [planner_names_ok]. split; [lia|]. split.
    - constructor; [|exact Hnodup]. intro Hin.
      apply Forall_forall with (x := fresh) in Hbelow; [lia|exact Hin].
    - split.
      + constructor; [lia|]. apply Forall_forall. intros x Hin.
        apply Forall_forall with (x := x) in Hbelow; [lia|exact Hin].
      + split; [constructor; assumption|exact Hmain].
  Qed.

  (** A newly generated literal name is distinct from all earlier names. *)
  Lemma planner_names_literal : forall bound names nc nm fresh cn mn,
    planner_names_ok bound (VarLayout names nc nm fresh cn mn) ->
    planner_names_ok bound
      (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)).
  Proof.
    intros bound names nc nm fresh cn mn [Hbound [Hnodup [Hbelow [Hcopies Hmain]]]].
    cbn [planner_names_ok]. split; [lia|]. split.
    - apply (proj2 (NoDup_Add (Add_app fresh cn mn))). split; [exact Hnodup|].
      intro Hin. apply Forall_forall with (x := fresh) in Hbelow; [lia|exact Hin].
    - split.
      + apply Forall_forall. intros x Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|[Heq|Hin]].
        * apply Forall_forall with (x := x) in Hbelow; [lia|apply in_app_iff; auto].
        * subst x. lia.
        * apply Forall_forall with (x := x) in Hbelow; [lia|apply in_app_iff; auto].
      + split; [exact Hcopies|]. intros x [Heq|Hin] Hnone.
        * subst x. exact Hbound.
        * exact (Hmain x Hin Hnone).
  Qed.

  (** A previously unregistered real name cannot be an existing fresh or real name. *)
  Lemma planner_names_real : forall bound names nc nm fresh cn mn x j,
    planner_names_ok bound (VarLayout names nc nm fresh cn mn) ->
    (x <= bound)%positive -> trie_get x names = None ->
    planner_names_ok bound
      (VarLayout (PTrieCode.set x j names) nc (S nm) fresh cn (x :: mn)).
  Proof.
    intros bound names nc nm fresh cn mn x j
      [Hbound [Hnodup [Hbelow [Hcopies Hmain]]]] Hx Hnone.
    cbn [planner_names_ok]. split; [exact Hbound|]. split.
    - apply (proj2 (NoDup_Add (Add_app x cn mn))). split; [exact Hnodup|].
      intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      + apply Forall_forall with (x := x) in Hcopies; [lia|exact Hin].
      + specialize (Hmain x Hin Hnone). lia.
    - split.
      + apply Forall_forall. intros y Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|[Heq|Hin]].
        * apply Forall_forall with (x := y) in Hbelow; [exact Hbelow|apply in_app_iff; auto].
        * subst y. lia.
        * apply Forall_forall with (x := y) in Hbelow; [exact Hbelow|apply in_app_iff; auto].
      + split; [exact Hcopies|]. intros y [Heq|Hin] Hmissing.
        * subst y. rewrite PTrie.get_set_same in Hmissing. discriminate.
        * destruct (Pos.eq_dec x y) as [Heq|Hneq].
          -- subst y. rewrite PTrie.get_set_same in Hmissing. discriminate.
          -- rewrite PTrie.get_set_other in Hmissing by congruence.
             exact (Hmain y Hin Hmissing).
  Qed.

  (** Placing bounded query variables preserves distinct and fresh layout names. *)
  Lemma planner_place_names : forall (ts : list (term V.t)) bound base pos seen lay
      pairs lits copied,
    planner_names_ok bound lay ->
    (forall x, In (Var x) ts -> (x <= bound)%positive) ->
    match place_terms base ts pos seen lay pairs lits copied with
    | (lay', _, _, _) => planner_names_ok bound lay'
    end.
  Proof.
    induction ts as [|t rest IH]; intros bound base pos seen lay pairs lits copied
      Hnames Hbound; cbn [place_terms].
    - exact Hnames.
    - destruct lay as [names nc nm fresh cn mn].
      destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen).
        * apply IH.
          -- apply planner_names_copy. exact Hnames.
          -- intros y Hin. apply Hbound. now right.
        * destruct (trie_get x names) eqn:Hname.
          -- apply IH; [exact Hnames|]. intros y Hin. apply Hbound. now right.
          -- apply IH.
             ++ apply planner_names_real; [exact Hnames|apply Hbound; now left|exact Hname].
             ++ intros y Hin. apply Hbound. now right.
      + apply IH.
        * apply planner_names_literal. exact Hnames.
        * intros y Hin. apply Hbound. now right.
  Qed.

  (** Planning atoms preserves distinct and fresh layout names. *)
  Lemma planner_atoms_names : forall (q : list (atom V.t)) bound base ai lay st outs post,
    planner_names_ok bound lay ->
    (forall x, In (Var x) (flat_map atom_terms q) -> (x <= bound)%positive) ->
    match plan_atoms base q ai lay st outs post with
    | (lay', _, _, _) => planner_names_ok bound lay'
    end.
  Proof.
    induction q as [|a rest IH]; intros bound base ai lay st outs post Hnames Hbound;
      cbn [plan_atoms].
    - exact Hnames.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + assert (Hterms : forall x, In (Var x) (args ++ option_list res) ->
            (x <= bound)%positive).
        { intros x Hin. apply Hbound. apply in_app_iff. now left. }
        pose proof (planner_place_names (args ++ option_list res) bound base 0 Empty
          lay [] [] false Hnames Hterms) as Hplaced.
        destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[lay' pairs] lits] copied].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        apply IH; [exact Hplaced|]. intros x Hin. apply Hbound.
        apply in_app_iff. now right.
      + apply IH; [exact Hnames|]. intros x Hin. apply Hbound.
        apply in_app_iff. now right.
  Qed.

  (** A fresh initial layout satisfies the name invariant. *)
  Lemma planner_names_initial : forall bound,
    planner_names_ok bound (VarLayout Empty 0 0 (Pos.succ bound) [] []).
  Proof.
    intro bound. cbn [planner_names_ok]. split; [lia|].
    split; [constructor|]. split; [constructor|]. split; [constructor|].
    intros x Hin. contradiction.
  Qed.

  (** A rule's variable list has the declared length and no duplicate name. *)
  Lemma planner_rule_variables : forall i r st st' c cs,
    plan_rule i r st = (st', c, cs) ->
    length (var_of V.t c) = nvars (join V.t c) /\ NoDup (var_of V.t c) /\
    Forall (fun x => (query_max (query V.t r) 1%positive < x)%positive)
      (firstn (query_copies (query V.t r) 0) (var_of V.t c)).
  Proof.
    intros i [q acts] st st' c cs Hplan. unfold plan_rule in Hplan.
    pose proof (planner_atoms_copies q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] []) as Hcopies.
    pose proof (planner_atoms_lengths q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] [] eq_refl eq_refl) as Hlengths.
    pose proof (planner_atoms_names q (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []
      (planner_names_initial (query_max q 1%positive))) as Hnames.
    specialize (Hnames (fun x Hin => planner_query_max_member q 1%positive x Hin)).
    destruct (plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay state] atoms] post].
    destruct lay as [names nc nm fresh cn mn].
    injection Hplan as <- <- <-. cbn [var_of join nvars query] in *.
    destruct Hlengths as [Hcn Hmn].
    destruct Hnames as [Hfresh [Hnodup [Hbelow [Hcopy _]]]].
    rewrite !rev_append_rev, app_nil_r. split.
    - rewrite length_app, !length_rev. lia.
    - split.
      + eapply Permutation_NoDup; [|exact Hnodup].
        apply Permutation_app; apply Permutation_rev.
      + replace (query_copies q 0) with (length (rev cn)) by (rewrite length_rev; lia).
        rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn].
        rewrite app_nil_r. apply Forall_rev. exact Hcopy.
  Qed.

  (** Every generated rule plan admits the variable-name lookup table. *)
  Lemma planner_rule_var_table : forall i r st st' c cs,
    plan_rule i r st = (st', c, cs) ->
    exists names, var_table (var_of V.t c) 0 Empty = Some names /\
      forall n x, nth_error (var_of V.t c) n = Some x ->
        trie_get x names = Some (N.of_nat n).
  Proof.
    intros i r st st' c cs Hplan.
    destruct (planner_rule_variables i r st st' c cs Hplan) as [_ [Hnodup _]].
    apply planner_var_table_empty. exact Hnodup.
  Qed.

  (** A sufficiently long fresh copy prefix passes the first layout guard. *)
  Lemma planner_layout_fresh_complete : forall vars bound copies j allowed,
    copies <= length vars ->
    Forall (fun x => (bound < x)%positive) (firstn copies vars) ->
    exists result, layout_fresh bound copies vars j allowed = Some result.
  Proof.
    induction vars as [|x rest IH]; intros bound copies j allowed Hlength Hfresh.
    - destruct copies; [exists allowed; reflexivity|cbn in Hlength; lia].
    - destruct copies as [|copies]; cbn [layout_fresh].
      + apply IH; [lia|constructor].
      + cbn [firstn] in Hfresh. inversion Hfresh as [|x' rest' Hx Hrest]; subst x' rest'.
        assert (Htest : Pos.ltb bound x = true) by (apply Pos.ltb_lt; exact Hx).
        rewrite Htest. apply IH; [cbn in Hlength; lia|exact Hrest].
  Qed.

  (** Every registered real variable names its position among the main variables. *)
  Definition planner_main_positions (base : nat) (lay : var_layout) : Prop :=
    match lay with
    | VarLayout names _ nm _ _ mn =>
        nm = length mn /\
        forall x j, trie_get x names = Some j ->
          exists k, j = base + k /\ nth_error (rev mn) k = Some x
    end.

  (** Adding a fresh unnamed main position preserves every registered position. *)
  Lemma planner_main_literal : forall base names nc nm fresh cn mn,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_main_positions base
      (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)).
  Proof.
    intros base names nc nm fresh cn mn [Hlength Hpositions].
    cbn [planner_main_positions]. split; [cbn; congruence|].
    intros x j Hget. destruct (Hpositions x j Hget) as [k [Hj Hnth]].
    exists k. split; [exact Hj|]. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
    apply nth_error_Some. rewrite Hnth. discriminate.
  Qed.

  (** Registering a new real variable places it after the existing main positions. *)
  Lemma planner_main_real : forall base names nc nm fresh cn mn x,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    trie_get x names = None ->
    planner_main_positions base
      (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn)).
  Proof.
    intros base names nc nm fresh cn mn x [Hlength Hpositions] Hnone.
    cbn [planner_main_positions]. split; [cbn; congruence|].
    intros y j Hget. destruct (Pos.eq_dec x y) as [Heq|Hneq].
    - subst y. rewrite PTrie.get_set_same in Hget. injection Hget as <-.
      exists nm. split; [reflexivity|]. cbn [rev].
      rewrite nth_error_app2; [|rewrite length_rev; lia].
      rewrite length_rev, <- Hlength, Nat.sub_diag. reflexivity.
    - rewrite PTrie.get_set_other in Hget by congruence.
      destruct (Hpositions y j Hget) as [k [Hj Hnth]].
      exists k. split; [exact Hj|]. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
      apply nth_error_Some. rewrite Hnth. discriminate.
  Qed.

  (** Placing terms preserves the positions assigned to real variables. *)
  Lemma planner_place_positions : forall (ts : list (term V.t)) base pos seen lay
      pairs lits copied,
    planner_main_positions base lay ->
    match place_terms base ts pos seen lay pairs lits copied with
    | (lay', _, _, _) => planner_main_positions base lay'
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen lay pairs lits copied Hpositions;
      cbn [place_terms].
    - exact Hpositions.
    - destruct lay as [names nc nm fresh cn mn]. destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen).
        * apply IH. exact Hpositions.
        * destruct (trie_get x names) eqn:Hget.
          -- apply IH. exact Hpositions.
          -- apply IH. apply planner_main_real; assumption.
      + apply IH. apply planner_main_literal. exact Hpositions.
  Qed.

  (** Planning atoms preserves the positions assigned to real variables. *)
  Lemma planner_atoms_positions : forall (q : list (atom V.t)) base ai lay st outs post,
    planner_main_positions base lay ->
    match plan_atoms base q ai lay st outs post with
    | (lay', _, _, _) => planner_main_positions base lay'
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai lay st outs post Hpositions;
      cbn [plan_atoms].
    - exact Hpositions.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + pose proof (planner_place_positions (args ++ option_list res) base 0 Empty
          lay [] [] false Hpositions) as Hplaced.
        destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[lay' pairs] lits] copied].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        apply IH. exact Hplaced.
      + apply IH. exact Hpositions.
  Qed.

  (** Placing more terms preserves every previously registered variable. *)
  Lemma planner_place_registered : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied x j,
    trie_get x names = Some j ->
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (VarLayout names' _ _ _ _ _, _, _, _) => trie_get x names' = Some j
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      pairs lits copied x j Hget; cbn [place_terms].
    - exact Hget.
    - destruct t as [y|v]; cbn [place_terms].
      + destruct (trie_get y seen).
        * apply IH. exact Hget.
        * destruct (trie_get y names) eqn:Hy.
          -- apply IH. exact Hget.
          -- apply IH. rewrite PTrie.get_set_other; [exact Hget|].
             intro Heq. subst y. congruence.
      + apply IH. exact Hget.
  Qed.

  (** Planning more atoms preserves every previously registered variable. *)
  Lemma planner_atoms_registered : forall (q : list (atom V.t)) base ai
      names nc nm fresh cn mn st outs post x j,
    trie_get x names = Some j ->
    match plan_atoms base q ai (VarLayout names nc nm fresh cn mn) st outs post with
    | (VarLayout names' _ _ _ _ _, _, _, _) => trie_get x names' = Some j
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai names nc nm fresh cn mn st outs post
      x j Hget; cbn [plan_atoms].
    - exact Hget.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + pose proof (planner_place_registered (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false x j Hget) as Hplaced.
        destruct (place_terms base (args ++ option_list res) 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false)
          as [[[lay pairs] lits] copied].
        destruct lay as [names' nc' nm' fresh' cn' mn']; cbn in Hplaced.
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        apply IH. exact Hplaced.
      + apply IH. exact Hget.
  Qed.

  (** Placement accumulators prepend precisely the new reversed positions and literals. *)
  Lemma planner_place_acc : forall (ts : list (term V.t)) base pos seen lay copied
      pairs lits,
    place_terms base ts pos seen lay pairs lits copied =
    let '(lay', newpairs, newlits, copied') :=
      place_terms base ts pos seen lay [] [] copied in
    (lay', newpairs ++ pairs, newlits ++ lits, copied').
  Proof.
    induction ts as [|t rest IH]; intros base pos seen lay copied pairs lits.
    - reflexivity.
    - destruct lay as [names nc nm fresh cn mn]. destruct t as [x|v];
        cbn [place_terms].
      + destruct (trie_get x seen).
        * rewrite (IH base (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) true
            ((nc, pos) :: pairs) lits).
          rewrite (IH base (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) true
            [(nc, pos)] []).
          destruct (place_terms base rest (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) [] [] true)
            as [[[lay' ps] ls] cp]. cbn. rewrite app_nil_r, <- app_assoc. reflexivity.
        * destruct (trie_get x names) as [j|].
          -- rewrite (IH base (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) copied ((j, pos) :: pairs) lits).
             rewrite (IH base (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) copied [(j, pos)] []).
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) [] [] copied)
               as [[[lay' ps] ls] cp]. cbn. rewrite app_nil_r, <- app_assoc. reflexivity.
          -- rewrite (IH base (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               copied ((base + nm, pos) :: pairs) lits).
             rewrite (IH base (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               copied [(base + nm, pos)] []).
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               [] [] copied) as [[[lay' ps] ls] cp].
             cbn. rewrite app_nil_r, <- app_assoc. reflexivity.
      + rewrite (IH base (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) copied
          ((base + nm, pos) :: pairs) ((base + nm, v) :: lits)).
        rewrite (IH base (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) copied
          [(base + nm, pos)] [(base + nm, v)]).
        destruct (place_terms base rest (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) [] [] copied)
          as [[[lay' ps] ls] cp]. cbn. rewrite <- !app_assoc. reflexivity.
  Qed.

  (** The checker builds the inverse of the reversed position list. *)
  Fixpoint planner_inverse (pairs : list (nat * nat)) (inv : ptrie nat) : ptrie nat :=
    match pairs with
    | [] => inv
    | (j, pos) :: rest => PTrieCode.set (N.succ_pos (nat_n j)) pos (planner_inverse rest inv)
    end.

  (** Appending positions first applies the right list to the inverse table. *)
  Lemma planner_inverse_app : forall xs ys inv,
    planner_inverse (xs ++ ys) inv = planner_inverse xs (planner_inverse ys inv).
  Proof.
    induction xs as [|[j pos] rest IH]; intros ys inv; cbn [app planner_inverse].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (** Value equality accepts identical literals. *)
  Lemma planner_value_refl : forall v, V.eqb v v = true.
  Proof.
    intro v. destruct (V.eqb_spec v v); [reflexivity|contradiction].
  Qed.

  (** Checking placed terms reconstructs their inverse position table and consumes literals. *)
  Lemma planner_place_check : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn copied checknames inv srcs cols,
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn) [] [] copied with
    | (VarLayout names' nc' _ _ _ _, pairs, lits, copied') =>
        (forall x j, trie_get x names' = Some j ->
          trie_get x checknames = Some (nat_n j)) ->
        check_terms V.eqb checknames ts pos seen (nat_n nc) inv
          (literal_sources (rev lits) srcs) (literal_cols (rev lits) cols) copied =
        Some (nat_n nc', planner_inverse pairs inv, srcs, cols, copied')
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      copied checknames inv srcs cols.
    - cbn [place_terms check_terms planner_inverse]. intros _. reflexivity.
    - destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen) eqn:Hseen.
        * rewrite (planner_place_acc rest base (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) true
            [(nc, pos)] []).
          destruct (place_terms base rest (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) [] [] true)
            as [[[lay pairs] lits] copied'] eqn:Hrest.
          destruct lay as [names' nc' nm' fresh' cn' mn']. intro Hmap.
          rewrite app_nil_r. cbn [check_terms]. rewrite Hseen, planner_inverse_app.
          cbn [planner_inverse].
          pose proof (IH base (S pos) seen names (S nc) nm (Pos.succ fresh)
            (fresh :: cn) mn true checknames (PTrieCode.set (N.succ_pos (nat_n nc)) pos inv)
            srcs cols) as Hcheck.
          rewrite Hrest in Hcheck. exact (Hcheck Hmap).
        * destruct (trie_get x names) as [j|] eqn:Hname.
          -- rewrite (planner_place_acc rest base (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) copied [(j, pos)] []).
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) [] [] copied)
               as [[[lay pairs] lits] copied'] eqn:Hrest.
             destruct lay as [names' nc' nm' fresh' cn' mn']. intro Hmap.
             pose proof (planner_place_registered rest base (S pos) (PTrieCode.set x tt seen)
               names nc nm fresh cn mn [] [] copied x j Hname) as Hregistered.
             rewrite Hrest in Hregistered.
             rewrite app_nil_r. cbn [check_terms]. rewrite Hseen, (Hmap x j Hregistered).
             rewrite planner_inverse_app. cbn [planner_inverse].
             pose proof (IH base (S pos) (PTrieCode.set x tt seen) names nc nm fresh cn mn
               copied checknames (PTrieCode.set (N.succ_pos (nat_n j)) pos inv) srcs cols)
               as Hcheck.
             rewrite Hrest in Hcheck. exact (Hcheck Hmap).
          -- rewrite (planner_place_acc rest base (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               copied [(base + nm, pos)] []).
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               [] [] copied) as [[[lay pairs] lits] copied'] eqn:Hrest.
             destruct lay as [names' nc' nm' fresh' cn' mn']. intro Hmap.
             assert (Hinitial : trie_get x (PTrieCode.set x (base + nm) names) =
                 Some (base + nm)) by apply PTrie.get_set_same.
             pose proof (planner_place_registered rest base (S pos) (PTrieCode.set x tt seen)
               (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn)
               [] [] copied x (base + nm) Hinitial) as Hregistered.
             rewrite Hrest in Hregistered.
             rewrite app_nil_r. cbn [check_terms].
             rewrite Hseen, (Hmap x (base + nm) Hregistered), planner_inverse_app.
             cbn [planner_inverse].
             pose proof (IH base (S pos) (PTrieCode.set x tt seen)
               (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn) copied
               checknames (PTrieCode.set (N.succ_pos (nat_n (base + nm))) pos inv) srcs cols)
               as Hcheck.
             rewrite Hrest in Hcheck. exact (Hcheck Hmap).
      + rewrite (planner_place_acc rest base (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) copied
          [(base + nm, pos)] [(base + nm, v)]).
        destruct (place_terms base rest (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) [] [] copied)
          as [[[lay pairs] lits] copied'] eqn:Hrest.
        destruct lay as [names' nc' nm' fresh' cn' mn']. intro Hmap.
        rewrite rev_app_distr. cbn [rev app literal_sources literal_cols check_terms].
        rewrite planner_value_refl, planner_inverse_app. cbn [planner_inverse].
        pose proof (IH base (S pos) seen names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)
          copied checknames (PTrieCode.set (N.succ_pos (nat_n (base + nm))) pos inv) srcs cols)
          as Hcheck.
        rewrite Hrest in Hcheck. exact (Hcheck Hmap).
  Qed.

  (** A registered main position lies in the main interval and names only one variable. *)
  Lemma planner_registered_range : forall base names nc nm fresh cn mn x j,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    trie_get x names = Some j -> base <= j /\ j < base + nm.
  Proof.
    intros base names nc nm fresh cn mn x j [Hlength Hpositions] Hget.
    destruct (Hpositions x j Hget) as [k [Hj Hnth]].
    assert (Hk : k < length (rev mn)) by (apply nth_error_Some; rewrite Hnth; discriminate).
    rewrite length_rev in Hk. lia.
  Qed.

  (** Distinct registered names have distinct main positions. *)
  Lemma planner_registered_injective : forall base names nc nm fresh cn mn x y j,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    trie_get x names = Some j -> trie_get y names = Some j -> x = y.
  Proof.
    intros base names nc nm fresh cn mn x y j [_ Hpositions] Hx Hy.
    destruct (Hpositions x j Hx) as [kx [Hxindex Hxnth]].
    destruct (Hpositions y j Hy) as [ky [Hyindex Hynth]].
    assert (Heq : kx = ky) by lia. subst ky. congruence.
  Qed.

  (** Already placed pairs use earlier copies or main positions. A real position can occur
      only after its variable has been seen in this atom. *)
  Definition planner_pairs_ok (base : nat) (seen : ptrie unit) (lay : var_layout)
      (pairs : list (nat * nat)) : Prop :=
    match lay with
    | VarLayout names nc nm _ _ _ =>
        NoDup (map fst pairs) /\
        Forall (fun jp => fst jp < base + nm /\ (fst jp < nc \/ base <= fst jp)) pairs /\
        (forall x j, trie_get x names = Some j -> In j (map fst pairs) ->
          exists u, trie_get x seen = Some u)
    end.

  (** Empty positions satisfy the atom-local pairing invariant. *)
  Lemma planner_pairs_empty : forall base seen lay, planner_pairs_ok base seen lay [].
  Proof.
    intros base seen [names nc nm fresh cn mn]. cbn [planner_pairs_ok].
    split; [constructor|]. split; [constructor|]. intros x j Hget Hin. contradiction.
  Qed.

  (** A new copy index is below the main interval and above every earlier copy. *)
  Lemma planner_pairs_copy : forall base seen names nc nm fresh cn mn pairs pos,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_pairs_ok base seen (VarLayout names nc nm fresh cn mn) pairs -> nc < base ->
    planner_pairs_ok base seen
      (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) ((nc, pos) :: pairs).
  Proof.
    intros base seen names nc nm fresh cn mn pairs pos Hmain
      [Hnodup [Hbounds Hseen]] Hcopy. cbn [planner_pairs_ok]. split.
    - constructor; [|exact Hnodup]. intro Hin.
      apply in_map_iff in Hin as [[j p] [Heq Hin]]. cbn in Heq. subst j.
      apply Forall_forall with (x := (nc, p)) in Hbounds; [cbn in Hbounds; lia|exact Hin].
    - split.
      + constructor; [cbn; lia|]. apply Forall_forall. intros [j p] Hin.
        apply Forall_forall with (x := (j, p)) in Hbounds; [cbn in *; lia|exact Hin].
      + intros x j Hget [Heq|Hin].
        * pose proof (planner_registered_range base names nc nm fresh cn mn x j Hmain Hget).
          cbn in Heq. lia.
        * exact (Hseen x j Hget Hin).
  Qed.

  (** A new literal index comes after every existing main position. *)
  Lemma planner_pairs_literal : forall base seen names nc nm fresh cn mn pairs pos,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_pairs_ok base seen (VarLayout names nc nm fresh cn mn) pairs ->
    planner_pairs_ok base seen
      (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn))
      ((base + nm, pos) :: pairs).
  Proof.
    intros base seen names nc nm fresh cn mn pairs pos Hmain [Hnodup [Hbounds Hseen]].
    cbn [planner_pairs_ok]. split.
    - constructor; [|exact Hnodup]. intro Hin.
      apply in_map_iff in Hin as [[j p] [Heq Hin]]. cbn in Heq. subst j.
      apply Forall_forall with (x := (base + nm, p)) in Hbounds;
        [cbn in Hbounds; lia|exact Hin].
    - split.
      + constructor; [cbn; lia|]. apply Forall_forall. intros [j p] Hin.
        apply Forall_forall with (x := (j, p)) in Hbounds; [cbn in *; lia|exact Hin].
      + intros x j Hget [Heq|Hin].
        * pose proof (planner_registered_range base names nc nm fresh cn mn x j Hmain Hget).
          cbn in Heq. lia.
        * exact (Hseen x j Hget Hin).
  Qed.

  (** A first atom-local occurrence may reuse its existing global main position. *)
  Lemma planner_pairs_reuse : forall base seen names nc nm fresh cn mn pairs pos x j,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_pairs_ok base seen (VarLayout names nc nm fresh cn mn) pairs ->
    trie_get x seen = None -> trie_get x names = Some j ->
    planner_pairs_ok base (PTrieCode.set x tt seen)
      (VarLayout names nc nm fresh cn mn) ((j, pos) :: pairs).
  Proof.
    intros base seen names nc nm fresh cn mn pairs pos x j Hmain
      [Hnodup [Hbounds Hseen]] Hmissing Hget. cbn [planner_pairs_ok]. split.
    - constructor; [|exact Hnodup]. intro Hin.
      destruct (Hseen x j Hget Hin) as [u Hu]. congruence.
    - split.
      + constructor; [|exact Hbounds]. cbn.
        pose proof (planner_registered_range base names nc nm fresh cn mn x j Hmain Hget).
        lia.
      + intros y k Hy [Heq|Hin].
        * cbn in Heq. subst k.
          pose proof (planner_registered_injective base names nc nm fresh cn mn x y j
            Hmain Hget Hy) as Hxy. subst y.
          exists tt. apply PTrie.get_set_same.
        * destruct (Pos.eq_dec x y) as [Heq|Hneq].
          -- subst y. exists tt. apply PTrie.get_set_same.
          -- destruct (Hseen y k Hy Hin) as [u Hu]. exists u.
             rewrite PTrie.get_set_other by congruence. exact Hu.
  Qed.

  (** A new real variable receives a new main index and becomes seen in its atom. *)
  Lemma planner_pairs_real : forall base seen names nc nm fresh cn mn pairs pos x,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_pairs_ok base seen (VarLayout names nc nm fresh cn mn) pairs ->
    trie_get x names = None ->
    planner_pairs_ok base (PTrieCode.set x tt seen)
      (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
      ((base + nm, pos) :: pairs).
  Proof.
    intros base seen names nc nm fresh cn mn pairs pos x Hmain
      [Hnodup [Hbounds Hseen]] Hmissing. cbn [planner_pairs_ok]. split.
    - constructor; [|exact Hnodup]. intro Hin.
      apply in_map_iff in Hin as [[j p] [Heq Hin]]. cbn in Heq. subst j.
      apply Forall_forall with (x := (base + nm, p)) in Hbounds;
        [cbn in Hbounds; lia|exact Hin].
    - split.
      + constructor; [cbn; lia|]. apply Forall_forall. intros [j p] Hin.
        apply Forall_forall with (x := (j, p)) in Hbounds; [cbn in *; lia|exact Hin].
      + intros y k Hy Hin. destruct (Pos.eq_dec x y) as [Heq|Hneq].
        * subst y. exists tt. apply PTrie.get_set_same.
        * rewrite PTrie.get_set_other in Hy by congruence.
          destruct Hin as [Heq|Hin].
          -- pose proof (planner_registered_range base names nc nm fresh cn mn y k Hmain Hy).
             cbn in Heq. lia.
          -- destruct (Hseen y k Hy Hin) as [u Hu]. exists u.
             rewrite PTrie.get_set_other by congruence. exact Hu.
  Qed.

  (** A bounded copy budget makes every atom position use a distinct join index. *)
  Lemma planner_place_pairs : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    planner_pairs_ok base seen (VarLayout names nc nm fresh cn mn) pairs ->
    term_copies seen ts nc <= base ->
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (lay', pairs', _, _) =>
        NoDup (map fst pairs') /\
        match lay' with
        | VarLayout _ _ nm' _ _ _ => Forall (fun jp => fst jp < base + nm') pairs'
        end
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      pairs lits copied Hmain Hpairs Hbudget; cbn [place_terms].
    - destruct Hpairs as [Hnodup [Hbounds _]]. split; [exact Hnodup|].
      apply Forall_forall. intros [j p] Hin.
      apply Forall_forall with (x := (j, p)) in Hbounds; [exact (proj1 Hbounds)|exact Hin].
    - destruct t as [x|v]; cbn [place_terms term_copies] in *.
      + destruct (trie_get x seen) eqn:Hseen.
        * apply IH.
          -- exact Hmain.
          -- apply planner_pairs_copy; [exact Hmain|exact Hpairs|].
             pose proof (planner_term_copies_acc rest seen (S nc)). lia.
          -- exact Hbudget.
        * destruct (trie_get x names) as [j|] eqn:Hget.
          -- apply IH; [exact Hmain| |exact Hbudget].
             apply planner_pairs_reuse; assumption.
          -- apply IH; [apply planner_main_real; assumption| |exact Hbudget].
             apply planner_pairs_real; assumption.
      + apply IH; [apply planner_main_literal; exact Hmain| |exact Hbudget].
        apply planner_pairs_literal; assumption.
  Qed.

  (** The indices allocated so far consist of a copy prefix and a main interval. *)
  Definition planner_used (base : nat) (lay : var_layout) (j : nat) : Prop :=
    match lay with
    | VarLayout _ nc nm _ _ _ => j < nc \/ (base <= j /\ j < base + nm)
    end.

  (** The new positions cover exactly the indices added by a term-placement pass. *)
  Lemma planner_place_coverage : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn copied,
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn) [] [] copied with
    | (lay', pairs, _, _) => forall j,
        planner_used base lay' j <->
        planner_used base (VarLayout names nc nm fresh cn mn) j \/ In j (map fst pairs)
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      copied Hmain.
    - cbn [place_terms map In]. intro j. tauto.
    - destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen) eqn:Hseen.
        * rewrite (planner_place_acc rest base (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) true
            [(nc, pos)] []).
          pose proof (IH base (S pos) seen names (S nc) nm (Pos.succ fresh)
            (fresh :: cn) mn true Hmain) as Hcoverage.
          destruct (place_terms base rest (S pos) seen
            (VarLayout names (S nc) nm (Pos.succ fresh) (fresh :: cn) mn) [] [] true)
            as [[[lay pairs] lits] copied'].
          intro j. rewrite Hcoverage, map_app, in_app_iff.
          cbn [planner_used map In fst]. intuition lia.
        * destruct (trie_get x names) as [k|] eqn:Hname.
          -- rewrite (planner_place_acc rest base (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) copied [(k, pos)] []).
             pose proof (IH base (S pos) (PTrieCode.set x tt seen) names nc nm fresh cn mn
               copied Hmain) as Hcoverage.
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout names nc nm fresh cn mn) [] [] copied)
               as [[[lay pairs] lits] copied'].
             intro j. rewrite Hcoverage, map_app, in_app_iff.
             pose proof (planner_registered_range base names nc nm fresh cn mn x k Hmain Hname).
             cbn [planner_used map In fst]. intuition lia.
          -- rewrite (planner_place_acc rest base (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               copied [(base + nm, pos)] []).
             pose proof (IH base (S pos) (PTrieCode.set x tt seen)
               (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn) copied
               (planner_main_real base names nc nm fresh cn mn x Hmain Hname)) as Hcoverage.
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               [] [] copied) as [[[lay pairs] lits] copied'].
             intro j. rewrite Hcoverage, map_app, in_app_iff.
             cbn [planner_used map In fst]. intuition lia.
      + rewrite (planner_place_acc rest base (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) copied
          [(base + nm, pos)] [(base + nm, v)]).
        pose proof (IH base (S pos) seen names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)
          copied (planner_main_literal base names nc nm fresh cn mn Hmain)) as Hcoverage.
        destruct (place_terms base rest (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) [] [] copied)
          as [[[lay pairs] lits] copied'].
        intro j. rewrite Hcoverage, map_app, in_app_iff.
        cbn [planner_used map In fst]. intuition lia.
  Qed.

  (** Later placement preserves every earlier main-name position. *)
  Lemma planner_place_main_entry : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied k x,
    nth_error (rev mn) k = Some x ->
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (VarLayout _ _ _ _ _ mn', _, _, _) => nth_error (rev mn') k = Some x
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      pairs lits copied k x Hnth; cbn [place_terms].
    - exact Hnth.
    - destruct t as [y|v]; cbn [place_terms].
      + destruct (trie_get y seen).
        * apply IH. exact Hnth.
        * destruct (trie_get y names).
          -- apply IH. exact Hnth.
          -- apply IH. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
             apply nth_error_Some. rewrite Hnth. discriminate.
      + apply IH. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
        apply nth_error_Some. rewrite Hnth. discriminate.
  Qed.

  (** Later placement never decreases the number of main indices. *)
  Lemma planner_place_mains : forall (ts : list (term V.t)) base pos seen
      names nc nm fresh cn mn pairs lits copied,
    match place_terms base ts pos seen (VarLayout names nc nm fresh cn mn)
        pairs lits copied with
    | (VarLayout _ _ nm' _ _ _, _, _, _) => nm <= nm'
    end.
  Proof.
    induction ts as [|t rest IH]; intros base pos seen names nc nm fresh cn mn
      pairs lits copied; cbn [place_terms].
    - lia.
    - destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen).
        * apply IH.
        * destruct (trie_get x names).
          -- apply IH.
          -- pose proof (IH base (S pos) (PTrieCode.set x tt seen)
               (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn)
               ((base + nm, pos) :: pairs) lits copied) as Hmains.
             destruct (place_terms base rest (S pos) (PTrieCode.set x tt seen)
               (VarLayout (PTrieCode.set x (base + nm) names) nc (S nm) fresh cn (x :: mn))
               ((base + nm, pos) :: pairs) lits copied)
               as [[[lay' ps] ls] cp]. destruct lay'. cbn in Hmains. lia.
      + pose proof (IH base (S pos) seen names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)
          ((base + nm, pos) :: pairs) ((base + nm, v) :: lits) copied) as Hmains.
        destruct (place_terms base rest (S pos) seen
          (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn))
          ((base + nm, pos) :: pairs) ((base + nm, v) :: lits) copied)
          as [[[lay' ps] ls] cp]. destruct lay'. cbn in Hmains. lia.
  Qed.

  (** Every positive trie key encodes a natural-number column. *)
  Lemma planner_column_key_surj : forall k,
    exists j, k = N.succ_pos (nat_n j).
  Proof.
    intro k. exists (N.to_nat (Pos.pred_N k)).
    rewrite planner_nat_n_spec, N2Nat.id.
    assert (Hkey : Npos k = Npos (N.succ_pos (Pos.pred_N k))).
    { rewrite N.succ_pos_spec, N.succ_pos_pred. reflexivity. }
    now injection Hkey.
  Qed.

  (** Distinct pair indices keep every position visible in their inverse trie. *)
  Lemma planner_inverse_member : forall pairs inv j pos,
    NoDup (map fst pairs) -> In (j, pos) pairs ->
    trie_get (N.succ_pos (nat_n j)) (planner_inverse pairs inv) = Some pos.
  Proof.
    intros pairs. induction pairs as [|[k q] pairs IH]; intros inv j pos Hnodup Hin;
      [contradiction|].
    cbn [map fst] in Hnodup. inversion Hnodup as [|? ? Hfresh Htail]; subst.
    cbn [planner_inverse]. destruct Hin as [Heq|Hin].
    - injection Heq as <- <-. apply PTrie.get_set_same.
    - rewrite PTrie.get_set_other.
      + apply IH; assumption.
      + intro Heq. apply planner_column_key_inj in Heq. subst j.
        apply Hfresh. apply in_map_iff. exists (k, pos). split; [reflexivity|exact Hin].
  Qed.

  (** The used-key list exposes the finite domain of the checker's unit trie. *)
  Definition planner_used_keys (used : ptrie unit) : list positive :=
    map fst (PTrie.elements used).

  (** A used key occurs exactly when its trie lookup returns the unique unit value. *)
  Lemma planner_used_keys_spec : forall used k,
    In k (planner_used_keys used) <-> trie_get k used = Some tt.
  Proof.
    intros used k. unfold planner_used_keys. split.
    - intro Hin. apply in_map_iff in Hin as [[p []] [Heq Hin]]. cbn in Heq. subst p.
      apply (proj1 (PTrie.elements_spec unit used k tt)). exact Hin.
    - intro Hget. apply in_map_iff. exists (k, tt). split; [reflexivity|].
      apply (proj2 (PTrie.elements_spec unit used k tt)). exact Hget.
  Qed.

  (** A trie lists every used key once. *)
  Lemma planner_used_keys_nodup : forall used, NoDup (planner_used_keys used).
  Proof.
    intro used. apply PTrie.elements_nodup.
  Qed.

  (** Inserting an already used key leaves the trie unchanged. *)
  Lemma planner_used_set_old : forall used k,
    trie_get k used = Some tt -> PTrieCode.set k tt used = used.
  Proof.
    intros used k Hget. apply PTrie.ext. intro q.
    destruct (Pos.eq_dec k q) as [->|Hneq].
    - rewrite PTrie.get_set_same. symmetry. exact Hget.
    - rewrite PTrie.get_set_other by congruence. reflexivity.
  Qed.

  (** Inserting a key adds exactly that key to the used-key predicate. *)
  Lemma planner_used_set_keys : forall used k q,
    In q (planner_used_keys (PTrieCode.set k tt used)) <->
      k = q \/ In q (planner_used_keys used).
  Proof.
    intros used k q. rewrite !planner_used_keys_spec.
    destruct (Pos.eq_dec k q) as [->|Hneq].
    - rewrite PTrie.get_set_same. tauto.
    - rewrite PTrie.get_set_other by congruence. tauto.
  Qed.

  (** The checker count is the cardinality of its used-key trie. *)
  Definition planner_used_count (used : ptrie unit) (count : N) : Prop :=
    count = N.of_nat (length (planner_used_keys used)).

  (** An empty used-key trie has zero cardinality. *)
  Lemma planner_used_count_empty : planner_used_count Empty 0%N.
  Proof.
    reflexivity.
  Qed.

  (** Insertion increases the count precisely when its key was previously absent. *)
  Lemma planner_used_count_set : forall used count k,
    planner_used_count used count ->
    planner_used_count (PTrieCode.set k tt used)
      (match trie_get k used with Some _ => count | None => N.succ count end).
  Proof.
    intros used count k Hcount. destruct (trie_get k used) as [[]|] eqn:Hget.
    - rewrite (planner_used_set_old used k Hget). exact Hcount.
    - assert (Hperm : Permutation (k :: planner_used_keys used)
        (planner_used_keys (PTrieCode.set k tt used))).
      { apply NoDup_Permutation.
        - constructor; [|apply planner_used_keys_nodup]. intro Hin.
          apply planner_used_keys_spec in Hin. congruence.
        - apply planner_used_keys_nodup.
        - intro q. cbn. symmetry. apply planner_used_set_keys. }
      pose proof (Permutation_length Hperm) as Hlength. cbn [length] in Hlength.
      unfold planner_used_count in *. rewrite <- Hlength, Nat2N.inj_succ, <- Hcount.
      reflexivity.
  Qed.

  (** Inserting a column key adds precisely that column to the lookup predicate. *)
  Lemma planner_used_set_column : forall used j k,
    trie_get (N.succ_pos (nat_n k))
      (PTrieCode.set (N.succ_pos (nat_n j)) tt used) = Some tt <->
      j = k \/ trie_get (N.succ_pos (nat_n k)) used = Some tt.
  Proof.
    intros used j k. rewrite <- !planner_used_keys_spec, planner_used_set_keys.
    split.
    - intros [Heq|Hin]; [left; apply planner_column_key_inj; exact Heq|right; exact Hin].
    - intros [->|Hin]; [left; reflexivity|right; exact Hin].
  Qed.

  (** Reading a pair list through its inverse emits the positions and records its columns. *)
  Lemma planner_column_perm_pairs : forall pairs inv used count,
    (forall j pos, In (j, pos) pairs -> trie_get (N.succ_pos (nat_n j)) inv = Some pos) ->
    planner_used_count used count ->
    exists used' count',
      column_perm inv (map fst pairs) used count = Some (map snd pairs, used', count') /\
      planner_used_count used' count' /\
      forall k, trie_get (N.succ_pos (nat_n k)) used' = Some tt <->
        trie_get (N.succ_pos (nat_n k)) used = Some tt \/ In k (map fst pairs).
  Proof.
    intros pairs. induction pairs as [|[j pos] pairs IH]; intros inv used count Hlookup Hcount.
    - exists used, count. split; [reflexivity|]. split; [exact Hcount|].
      intro k. cbn. tauto.
    - assert (Hhead : trie_get (N.succ_pos (nat_n j)) inv = Some pos).
      { apply Hlookup. left. reflexivity. }
      assert (Htail : forall k q, In (k, q) pairs ->
        trie_get (N.succ_pos (nat_n k)) inv = Some q).
      { intros k q Hin. apply Hlookup. right. exact Hin. }
      pose proof (planner_used_count_set used count (N.succ_pos (nat_n j)) Hcount) as Hnext.
      destruct (IH inv (PTrieCode.set (N.succ_pos (nat_n j)) tt used)
        (match trie_get (N.succ_pos (nat_n j)) used with
         | Some _ => count
         | None => N.succ count
         end) Htail Hnext) as [used' [count' [Hread [Hcount' Hused]]]].
      exists used', count'. split.
      + cbn [column_perm map fst snd]. rewrite Hhead, Hread. reflexivity.
      + split; [exact Hcount'|]. intro k. rewrite Hused, planner_used_set_column.
        cbn [map fst In]. tauto.
  Qed.

  (** Sorting preserves the column membership of a pair list. *)
  Lemma planner_sorted_column_member : forall pairs k,
    In k (map fst (sort_pairs pairs)) <-> In k (map fst pairs).
  Proof.
    intros pairs k. split; intro Hin.
    - eapply Permutation_in; [|exact Hin].
      apply Permutation_sym. apply Permutation_map. apply planner_sort_pairs_perm.
    - eapply Permutation_in; [|exact Hin].
      apply Permutation_map. apply planner_sort_pairs_perm.
  Qed.

  (** A generated inverse and sorted column recover the exact sorted slot permutation. *)
  Lemma planner_column_perm_sorted : forall pairs used count,
    NoDup (map fst pairs) -> planner_used_count used count ->
    exists used' count',
      column_perm (planner_inverse pairs Empty) (map fst (sort_pairs pairs)) used count =
        Some (map snd (sort_pairs pairs), used', count') /\
      planner_used_count used' count' /\
      forall k, trie_get (N.succ_pos (nat_n k)) used' = Some tt <->
        trie_get (N.succ_pos (nat_n k)) used = Some tt \/ In k (map fst pairs).
  Proof.
    intros pairs used count Hnodup Hcount.
    assert (Hlookup : forall j pos, In (j, pos) (sort_pairs pairs) ->
      trie_get (N.succ_pos (nat_n j)) (planner_inverse pairs Empty) = Some pos).
    { intros j pos Hin. apply planner_inverse_member; [exact Hnodup|].
      eapply Permutation_in; [|exact Hin].
      apply Permutation_sym. apply planner_sort_pairs_perm. }
    destruct (planner_column_perm_pairs (sort_pairs pairs) _ _ _ Hlookup Hcount)
      as [used' [count' [Hread [Hcount' Hused]]]].
    exists used', count'. split; [exact Hread|]. split; [exact Hcount'|].
    intro k. rewrite Hused, planner_sorted_column_member. reflexivity.
  Qed.

  (** Distinct column numbers remain distinct after encoding as trie keys. *)
  Lemma planner_column_keys_nodup : forall js,
    NoDup js -> NoDup (map (fun j => N.succ_pos (nat_n j)) js).
  Proof.
    intros js Hnodup. induction Hnodup as [|j js Hfresh Htail IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. intro Hin.
      apply in_map_iff in Hin as [k [Heq Hin]]. apply planner_column_key_inj in Heq.
      subst k. contradiction.
  Qed.

  (** A column occurs among encoded keys exactly when its number occurs in their source. *)
  Lemma planner_column_keys_member : forall js j,
    In (N.succ_pos (nat_n j)) (map (fun k => N.succ_pos (nat_n k)) js) <-> In j js.
  Proof.
    intros js j. split.
    - intro Hin. apply in_map_iff in Hin as [k [Heq Hin]].
      apply planner_column_key_inj in Heq. now subst k.
    - intro Hin. apply in_map_iff. exists j. split; [reflexivity|exact Hin].
  Qed.

  (** Disjoint copy and main intervals contain exactly their combined number of indices. *)
  Lemma planner_used_range_count : forall used count base nc nm,
    planner_used_count used count -> nc <= base ->
    (forall j, trie_get (N.succ_pos (nat_n j)) used = Some tt <->
      j < nc \/ (base <= j /\ j < base + nm)) ->
    count = N.of_nat (nc + nm).
  Proof.
    intros used count base nc nm Hcount Hdisjoint Hrange.
    assert (Hnodup : NoDup (seq 0 nc ++ seq base nm)).
    { apply NoDup_app; try apply seq_NoDup.
      intros j Hcopy Hmain. apply in_seq in Hcopy. apply in_seq in Hmain. lia. }
    assert (Hperm : Permutation (planner_used_keys used)
      (map (fun j => N.succ_pos (nat_n j)) (seq 0 nc ++ seq base nm))).
    { apply NoDup_Permutation.
      - apply planner_used_keys_nodup.
      - apply planner_column_keys_nodup. exact Hnodup.
      - intro key. destruct (planner_column_key_surj key) as [j ->].
        rewrite planner_used_keys_spec, Hrange, planner_column_keys_member,
          in_app_iff, !in_seq. lia. }
    pose proof (Permutation_length Hperm) as Hlength.
    rewrite length_map, length_app, !length_seq in Hlength.
    unfold planner_used_count in Hcount. now rewrite Hlength in Hcount.
  Qed.

  (** Placing terms appends their reversed positions to the existing reversed positions. *)
  Lemma planner_place_positions_result : forall base (ts : list (term V.t)) pos seen lay
      pairs lits copied lay' pairs' lits' copied',
    place_terms base ts pos seen lay pairs lits copied = (lay', pairs', lits', copied') ->
    map snd pairs' = rev (seq pos (length ts)) ++ map snd pairs.
  Proof.
    intros base ts. induction ts as [| t rest IH]; intros pos seen lay pairs lits copied
      lay' pairs' lits' copied' Hplaced.
    - cbn [place_terms] in Hplaced. inversion Hplaced; subst. reflexivity.
    - destruct lay as [names nc nm fresh cn mn]. destruct t as [x | v];
        cbn [place_terms] in Hplaced.
      + destruct (trie_get x seen) as [u |]; [| destruct (trie_get x names) as [j |]].
        all: etransitivity; [eapply IH; exact Hplaced |];
          cbn [seq rev map length]; rewrite <- app_assoc; reflexivity.
      + etransitivity; [eapply IH; exact Hplaced |].
        cbn [seq rev map length]. rewrite <- app_assoc. reflexivity.
  Qed.

  (** Every placed term contributes its original position to the reversed pair list. *)
  Lemma planner_place_positions_list : forall base (ts : list (term V.t)) pos seen lay
      pairs lits copied,
    let '(_, pairs', _, _) := place_terms base ts pos seen lay pairs lits copied in
    map snd pairs' = rev (seq pos (length ts)) ++ map snd pairs.
  Proof.
    intros base ts pos seen lay pairs lits copied.
    destruct (place_terms base ts pos seen lay pairs lits copied)
      as [[[lay' pairs'] lits'] copied'] eqn:Hplaced.
    eapply planner_place_positions_result. exact Hplaced.
  Qed.

  (** The sorted permutation of one placed atom uses each of its positions once. *)
  Lemma planner_place_perm_ok : forall base (ts : list (term V.t)) lay
      lay' pairs lits copied,
    place_terms base ts 0 Empty lay [] [] false = (lay', pairs, lits, copied) ->
    perm_ok (length ts) (map snd (sort_pairs pairs)) Empty = true.
  Proof.
    intros base ts lay lay' pairs lits copied Hplaced.
    pose proof (planner_place_positions_list base ts 0 Empty lay [] [] false) as Hpositions.
    rewrite Hplaced in Hpositions. cbn in Hpositions. rewrite app_nil_r in Hpositions.
    apply planner_sorted_perm_ok.
    - rewrite Hpositions. apply NoDup_rev. apply seq_NoDup.
    - apply (proj1 (@Forall_map (nat * nat) nat (@snd nat nat)
        (fun i => i < length ts) pairs)).
      rewrite Hpositions. apply Forall_rev.
      rewrite Forall_forall. intros i Hin. apply in_seq in Hin. lia.
  Qed.

  (** The first declaration determines the width used by the slot checker. *)
  Lemma planner_decl_width : forall ds f ss o,
    lookup_sorts ds f = Some ss -> lookup_kind ds f = Some o ->
    trie_get f (decl_widths ds Empty) =
      Some (length ss + match o with ORel => 0 | _ => 1 end).
  Proof.
    intros ds f ss o Hsort Hkind.
    destruct (run_lookup_sorts_decl ds f ss Hsort) as [d [Hfind Hargs]].
    destruct (run_find_decl_fields ds f d Hfind) as [_ Hout].
    assert (Hkindout : out d = o) by congruence.
    rewrite decl_widths_get, PTrie.get_empty, Hfind, Hargs, Hkindout. reflexivity.
  Qed.

  (** Binding arguments preserves their declared argument count. *)
  Lemma planner_binds_length : forall g ts ss g',
    @binds_list V.t g ts ss g' -> length ts = length ss.
  Proof.
    intros g ts ss g' Hbind. induction Hbind; cbn; congruence.
  Qed.

  (** A well-sorted result occupies exactly the output position of its declared kind. *)
  Lemma planner_result_length : forall g o res g', @binds_result V.t g o res g' ->
    length (option_list res) = match o with ORel => 0 | _ => 1 end.
  Proof.
    intros g o [t |] g' Hresult; destruct o; cbn [binds_result out_sort] in Hresult;
      try contradiction; reflexivity.
  Qed.

  Definition planner_slot_valid (widths : ptrie nat) (fp : positive * list nat) : Prop :=
    exists width, trie_get (fst fp) widths = Some width /\
      perm_ok width (snd fp) Empty = true.

  (** Adding a row with an elementwise property preserves that property of all rows. *)
  Lemma add_slot_property : forall (P : positive * list nat -> Prop) f perm st,
    Forall P (planner_rows st) -> P (f, perm) ->
    Forall P (planner_rows (snd (add_slot f perm st))).
  Proof.
    intros P f perm [table next rows] Hrows Hnew. cbn [add_slot].
    destruct (trie_get (slot_code f perm) table); cbn; [exact Hrows |].
    constructor; assumption.
  Qed.

  (** Full-slot registration needs the property only for unseen first declarations. *)
  Lemma full_slots_property : forall (P : positive * list nat -> Prop) ds seen st,
    Forall P (planner_rows st) ->
    (forall f ss, trie_get f seen = None -> lookup_kind ds f = Some OId ->
      lookup_sorts ds f = Some ss -> P (f, count_from 0 (S (length ss)))) ->
    Forall P (planner_rows (full_slots ds seen st)).
  Proof.
    intros P ds. induction ds as [| [g sorts o] rest IH]; intros seen st Hrows Hdecl.
    - exact Hrows.
    - cbn [full_slots]. destruct (trie_get g seen) as [u |] eqn:Hseen.
      + apply IH; [exact Hrows |].
        intros f ss Hunseen Hkind Hsorts.
        destruct (Pos.eqb g f) eqn:Hgf.
        * apply Pos.eqb_eq in Hgf. subst g. rewrite Hseen in Hunseen. discriminate Hunseen.
        * apply Hdecl; [exact Hunseen | |];
            cbn [lookup_kind lookup_sorts name arg_sorts out]; rewrite Hgf; assumption.
      + assert (Hnext : forall f ss, trie_get f (PTrieCode.set g tt seen) = None ->
            lookup_kind rest f = Some OId -> lookup_sorts rest f = Some ss ->
            P (f, count_from 0 (S (length ss)))).
        { intros f ss Hunseen Hkind Hsorts.
          destruct (run_get_set_none seen g f Hunseen) as [Hold Hneq].
          assert (Hgf : Pos.eqb g f = false) by (apply Pos.eqb_neq; congruence).
          apply Hdecl; [exact Hold | |];
            cbn [lookup_kind lookup_sorts name arg_sorts out]; rewrite Hgf; assumption. }
        destruct o; apply IH; try exact Hnext; try exact Hrows.
        apply add_slot_property; [exact Hrows |].
        apply Hdecl; [exact Hseen | |];
          cbn [lookup_kind lookup_sorts name arg_sorts out]; now rewrite Pos.eqb_refl.
  Qed.

  (** The initial full slots all use their declared widths. *)
  Lemma planner_full_slots_valid : forall ds,
    Forall (planner_slot_valid (decl_widths ds Empty))
      (planner_rows (full_slots ds Empty (SlotState Empty 0%N []))).
  Proof.
    intro ds. apply full_slots_property; [constructor |].
    intros f ss Hunseen Hkind Hsorts.
    exists (S (length ss)). split.
    - cbn [fst]. rewrite (planner_decl_width ds f ss OId Hsorts Hkind).
      cbn. now rewrite Nat.add_1_r.
    - apply planner_full_perm_ok.
  Qed.

  (** A typed function atom adds a valid permutation of its declared tuple. *)
  Lemma planner_fun_slot_valid : forall p g g1 g2 f args res ss o base lay
      lay' pairs lits copied,
    program_sorts p f = Some ss -> program_kind p f = Some o ->
    @binds_list V.t g args ss g1 -> binds_result g1 o res g2 ->
    place_terms base (args ++ option_list res) 0 Empty lay [] [] false =
      (lay', pairs, lits, copied) ->
    planner_slot_valid (decl_widths (decls V.t p) Empty) (f, map snd (sort_pairs pairs)).
  Proof.
    intros p g g1 g2 f args res ss o base lay lay' pairs lits copied
      Hsort Hkind Hargs Hres Hplaced.
    exists (length (args ++ option_list res)). split.
    - cbn [fst]. rewrite (planner_decl_width _ _ _ _ Hsort Hkind), length_app,
        (planner_binds_length _ _ _ _ Hargs), (planner_result_length _ _ _ _ Hres).
      reflexivity.
    - eapply planner_place_perm_ok. exact Hplaced.
  Qed.

  (** Planning a well-sorted query preserves validity of the accumulated slots. *)
  Lemma plan_atoms_slots_valid : forall p g q g',
    @query_ok V.t (program_sorts p) (program_kind p) g q g' ->
    forall base ai lay st outs post lay' st' outs' post',
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st) ->
    plan_atoms base q ai lay st outs post = (lay', st', outs', post') ->
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st').
  Proof.
    intros p g q g' Hquery.
    induction Hquery as
      [g | g g1 g2 g3 f args res ss o rest Hsort Hkind Hreads Hargs Hres Hrest IH |
       g g1 op args res rest Hargs Hres Hrest IH];
      intros base ai lay st outs post lay' st' outs' post' Hvalid Hplan.
    - cbn [plan_atoms] in Hplan. inversion Hplan; subst. exact Hvalid.
    - cbn [plan_atoms] in Hplan.
      destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
        as [[[next pairs] lits] copied] eqn:Hplaced.
      destruct (add_slot f (map snd (sort_pairs pairs)) st)
        as [slot nextst] eqn:Hslot.
      eapply IH; [| exact Hplan].
      pose proof (add_slot_property
        (planner_slot_valid (decl_widths (decls V.t p) Empty)) f
        (map snd (sort_pairs pairs)) st Hvalid) as Hkeep.
      rewrite Hslot in Hkeep. apply Hkeep.
      eapply planner_fun_slot_valid; eassumption.
    - cbn [plan_atoms] in Hplan. eapply IH; eassumption.
  Qed.

  (** Planning a well-sorted rule preserves validity of the accumulated slots. *)
  Lemma plan_rule_slots_valid : forall p i r st st' c cs,
    @rule_ok V.t (program_sorts p) (program_kind p) r ->
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st) ->
    plan_rule i r st = (st', c, cs) ->
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st').
  Proof.
    intros p i [q acts] st st' c cs [g [Hquery Hactions]] Hvalid Hplan.
    cbn [query] in Hquery. cbn [plan_rule] in Hplan.
    destruct (plan_atoms (query_copies q 0) q 0
        (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] outs] post] eqn:Hatoms.
    destruct lay as [names nc nm fresh cn mn]. inversion Hplan; subst.
    eapply plan_atoms_slots_valid; eassumption.
  Qed.

  (** Planning sorted rules keeps every accumulated slot within its declared width. *)
  Lemma plan_rules_slots_valid : forall p rs i st naive semi st' naive' semi',
    Forall (@rule_ok V.t (program_sorts p) (program_kind p)) rs ->
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st) ->
    plan_rules rs i st naive semi = (st', naive', semi') ->
    Forall (planner_slot_valid (decl_widths (decls V.t p) Empty)) (planner_rows st').
  Proof.
    intros p rs. induction rs as [| r rest IH]; intros i st naive semi st' naive' semi'
      Hsorted Hvalid Hplan.
    - cbn [plan_rules] in Hplan. inversion Hplan; subst. exact Hvalid.
    - inversion Hsorted as [| r' rest' Hrule Hrules]; subst.
      cbn [plan_rules] in Hplan.
      destruct (plan_rule i r st) as [[nextst c] cs] eqn:Hstep.
      eapply IH; [exact Hrules | | exact Hplan].
      eapply plan_rule_slots_valid; eassumption.
  Qed.

  (** All slots emitted by a sorted program pass the slot-table scan. *)
  Lemma planner_program_slot_table : forall p, program_ok p ->
    exists checked,
      slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t (plan p))
        0%N Empty = Some checked.
  Proof.
    intros [ds rs] Hsorted. unfold plan, plan_program.
    destruct (plan_rules rs 0%N (full_slots ds Empty (SlotState Empty 0%N [])) [] [])
      as [[[table next rows] naive] semi] eqn:Hrules.
    cbn [Syntax.slots decls]. rewrite rev_append_rev, app_nil_r.
    apply slot_table_complete. apply Forall_rev.
    exact (plan_rules_slots_valid (Program V.t ds rs) rs 0%N
      (full_slots ds Empty (SlotState Empty 0%N [])) [] [] (SlotState table next rows)
      naive semi Hsorted (planner_full_slots_valid ds) Hrules).
  Qed.

  (** Every sorted function atom reads an argument or an output column. *)
  Lemma planner_query_reads : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' ->
    Forall (fun a => match a with
      | Fun _ _ args res => args ++ option_list res <> []
      | Prim _ _ _ _ => True
      end) q.
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as
      [g | g g1 g2 g3 f args res ss o rest Hsort Hkind Hreads Hargs Hres Hrest IH |
       g g1 op args res rest Hargs Hres Hrest IH].
    - constructor.
    - constructor; [| exact IH]. intro Hempty. apply app_eq_nil in Hempty.
      destruct Hempty as [Hargsempty Hresempty].
      assert (Hsortsempty : ss = []).
      { apply length_zero_iff_nil.
        rewrite <- (planner_binds_length _ _ _ _ Hargs), Hargsempty. reflexivity. }
      destruct res as [t |]; [discriminate Hresempty |].
      destruct o; cbn [binds_result out_sort] in Hres; try contradiction.
      destruct Hreads as [Hnonempty | Hnotrel].
      + exact (Hnonempty Hsortsempty).
      + apply Hnotrel. reflexivity.
    - constructor; [exact I | exact IH].
  Qed.

  Definition planner_table (st : slot_state) : ptrie N :=
    match st with
    | SlotState table _ _ => table
    end.

  (** Adding a slot leaves every earlier slot number unchanged. *)
  Lemma add_slot_lookup : forall f perm st key s,
    trie_get key (planner_table st) = Some s ->
    trie_get key (planner_table (snd (add_slot f perm st))) = Some s.
  Proof.
    intros f perm [table next rows] key s Hget. cbn [add_slot planner_table] in *.
    destruct (trie_get (slot_code f perm) table) as [found |] eqn:Hfind.
    - exact Hget.
    - change (trie_get key (PTrieCode.set (slot_code f perm) next table) = Some s).
      rewrite PTrie.get_set_other; [exact Hget |].
      intro Heq. subst key. rewrite Hfind in Hget. discriminate Hget.
  Qed.

  (** The number returned when registering a slot is its stored number. *)
  Lemma add_slot_number : forall f perm st s st', add_slot f perm st = (s, st') ->
    trie_get (slot_code f perm) (planner_table st') = Some s.
  Proof.
    intros f perm [table next rows] s st' Hslot. cbn [add_slot] in Hslot.
    destruct (trie_get (slot_code f perm) table) as [found |] eqn:Hfind;
      inversion Hslot; subst; cbn [planner_table].
    - exact Hfind.
    - apply PTrie.get_set_same.
  Qed.

  (** Later full slots preserve the numbers of all earlier slots. *)
  Lemma full_slots_lookup : forall ds seen st key s,
    trie_get key (planner_table st) = Some s ->
    trie_get key (planner_table (full_slots ds seen st)) = Some s.
  Proof.
    induction ds as [| [f ss o] rest IH]; intros seen st key s Hget.
    - exact Hget.
    - cbn [full_slots]. destruct (trie_get f seen) as [u |].
      + now apply IH.
      + destruct o; apply IH; try exact Hget. now apply add_slot_lookup.
  Qed.

  (** Query planning preserves every slot number that was available before it. *)
  Lemma plan_atoms_lookup : forall base (q : list (atom V.t)) ai lay st outs post
      lay' st' outs' post',
    plan_atoms base q ai lay st outs post = (lay', st', outs', post') ->
    forall key s, trie_get key (planner_table st) = Some s ->
      trie_get key (planner_table st') = Some s.
  Proof.
    intros base q. induction q as [| a rest IH]; intros ai lay st outs post
      lay' st' outs' post' Hplan key s Hget.
    - cbn [plan_atoms] in Hplan. inversion Hplan; subst. exact Hget.
    - destruct a as [f args res | f args res]; cbn [plan_atoms] in Hplan.
      + destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[next pairs] lits] copied] eqn:Hplaced.
        destruct (add_slot f (map snd (sort_pairs pairs)) st)
          as [slot nextst] eqn:Hslot.
        eapply IH; [exact Hplan |].
        pose proof (add_slot_lookup f (map snd (sort_pairs pairs)) st key s Hget) as Hkeep.
        rewrite Hslot in Hkeep. exact Hkeep.
      + eapply IH; eassumption.
  Qed.

  (** Planning one later rule preserves all earlier slot numbers. *)
  Lemma plan_rule_lookup : forall i (r : rule V.t) st st' c cs,
    plan_rule i r st = (st', c, cs) ->
    forall key s, trie_get key (planner_table st) = Some s ->
      trie_get key (planner_table st') = Some s.
  Proof.
    intros i [q acts] st st' c cs Hplan key s Hget.
    cbn [plan_rule] in Hplan.
    destruct (plan_atoms (query_copies q 0) q 0
        (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] outs] post] eqn:Hatoms.
    destruct lay as [names nc nm fresh cn mn]. inversion Hplan; subst.
    eapply plan_atoms_lookup; eassumption.
  Qed.

  (** Planning all later rules preserves the slot identities of earlier plans. *)
  Lemma plan_rules_lookup : forall (rs : list (rule V.t)) i st naive semi st' naive' semi',
    plan_rules rs i st naive semi = (st', naive', semi') ->
    forall key s, trie_get key (planner_table st) = Some s ->
      trie_get key (planner_table st') = Some s.
  Proof.
    induction rs as [| r rest IH]; intros i st naive semi st' naive' semi' Hplan key s Hget.
    - cbn [plan_rules] in Hplan. inversion Hplan; subst. exact Hget.
    - cbn [plan_rules] in Hplan.
      destruct (plan_rule i r st) as [[nextst c] cs] eqn:Hrule.
      eapply IH; [exact Hplan |]. eapply plan_rule_lookup; eassumption.
  Qed.

  (** Comparing a permutation with itself succeeds. *)
  Lemma planner_nats_eqb_refl : forall ns, nats_eqb ns ns = true.
  Proof.
    induction ns as [| n ns IH]; [reflexivity |].
    cbn [nats_eqb]. rewrite Nat.eqb_refl. exact IH.
  Qed.

  (** An exact checked-table entry satisfies the slot matching test. *)
  Lemma slot_matches_complete : forall checked f perm s,
    trie_get (slot_code f perm) checked = Some (s, (f, perm)) ->
    slot_matches checked f perm s = true.
  Proof.
    intros checked f perm s Hget. unfold slot_matches.
    rewrite Hget, N.eqb_refl, Pos.eqb_refl. apply planner_nats_eqb_refl.
  Qed.

  (** Extending a checking table preserves every slot match already established. *)
  Lemma slot_matches_scan : forall widths sl next checked checked' f perm s,
    slot_table widths sl next checked = Some checked' ->
    slot_matches checked f perm s = true -> slot_matches checked' f perm s = true.
  Proof.
    intros widths sl next checked checked' f perm s Hscan Hmatch.
    unfold slot_matches in *.
    destruct (trie_get (slot_code f perm) checked) as [[number [g other]] |] eqn:Hget;
      [| discriminate Hmatch].
    rewrite (slot_table_keeps _ _ _ _ _ Hscan _ _ Hget). exact Hmatch.
  Qed.


  (** Each planned function atom contributes exactly one join source. *)
  Lemma planner_atoms_length : forall base (q : list (atom V.t)) ai lay st outs post,
    let '(_, _, outs', _) := plan_atoms base q ai lay st outs post in
    length outs' = fun_count q + length outs.
  Proof.
    intros base q. induction q as [|a rest IH]; intros ai lay st outs post.
    - reflexivity.
    - destruct a as [f args res|p args res]; cbn [plan_atoms fun_count].
      + destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[lay' pairs] lits] copied].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        specialize (IH (S ai) lay' st'
          (AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits []) :: outs)
          (if copied then ai :: post else post)).
        destruct (plan_atoms base rest (S ai) lay' st'
          (AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits []) :: outs)
          (if copied then ai :: post else post)) as [[[final state] result] posts].
        cbn [length] in *. lia.
      + apply IH.
  Qed.


  (** Semi-naive generation emits one plan for each requested pivot. *)
  Lemma planner_semis_length : forall i j vars post atoms m todo,
    length (@semi_plans V.t i j vars post atoms m todo) = length todo.
  Proof.
    intros i j vars post atoms m todo. revert m.
    induction todo as [|a rest IH]; intro m; cbn [semi_plans length]; [reflexivity|].
    now rewrite IH.
  Qed.

  (** A rule supplies precisely the number of semi-naive plans checked for it. *)
  Lemma planner_rule_semis_length : forall i r st st' c cs,
    @plan_rule V.t i r st = (st', c, cs) -> length cs = fun_count (query V.t r).
  Proof.
    intros i [q acts] st st' c cs Hplan. cbn [plan_rule] in Hplan.
    pose proof (planner_atoms_length (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []) as Hlength.
    destruct (plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] outs] post].
    destruct lay as [names nc nm fresh cn mn]. inversion Hplan; subst c cs st'.
    rewrite planner_semis_length, rev_append_rev, app_nil_r, length_rev.
    cbn [length query] in *. lia.
  Qed.

  (** Rule-list planning appends its reverse-order results to the supplied accumulators. *)
  Lemma planner_rules_accumulators : forall (rs : list (rule V.t)) i st naive semi,
    plan_rules rs i st naive semi =
      let '(st', nv, sn) := plan_rules rs i st [] [] in
      (st', nv ++ naive, sn ++ semi).
  Proof.
    induction rs as [|r rest IH]; intros i st naive semi; cbn [plan_rules].
    - reflexivity.
    - destruct (plan_rule i r st) as [[nextst c] cs].
      rewrite (IH (N.succ i) nextst (c :: naive) (rev_append cs semi)).
      rewrite (IH (N.succ i) nextst [c] (rev_append cs [])).
      destruct (plan_rules rest (N.succ i) nextst [] []) as [[final nv] sn].
      rewrite !rev_append_rev, app_nil_r, <- !app_assoc. reflexivity.
  Qed.

  (** The semi-naive checker consumes exactly a verified prefix. *)
  Lemma planner_check_semis_append : forall eqb table i r cs tail,
    Forall (fun c => @check_cplan V.t eqb true table i r c = true) cs ->
    check_semis eqb table i r (length cs) (cs ++ tail) = Some tail.
  Proof.
    intros eqb table i r cs tail Hchecked. induction Hchecked as [|c rest Hc Hrest IH].
    - reflexivity.
    - cbn [length app check_semis]. now rewrite Hc.
  Qed.

  (** Per-rule checker correctness composes through the reversed plan accumulators. *)
  Lemma planner_rules_checked : forall eqb table (rs : list (rule V.t)) i st st' nv sn,
    planner_state_exact st ->
    (forall r s j s' c cs, In r rs -> planner_state_exact s ->
      plan_rule j r s = (s', c, cs) ->
      (forall f perm slot, trie_get (slot_code f perm) (planner_table s') = Some slot ->
        slot_matches table f perm slot = true) ->
      check_cplan eqb false table j r c = true /\
      Forall (fun c' => check_cplan eqb true table j r c' = true) cs) ->
    plan_rules rs i st [] [] = (st', nv, sn) ->
    (forall f perm slot, trie_get (slot_code f perm) (planner_table st') = Some slot ->
      slot_matches table f perm slot = true) ->
    check_rule_plans eqb table rs i (rev nv) (rev sn) = true.
  Proof.
    intros eqb table rs. induction rs as [|[q acts] rest IH];
      intros i st st' nv sn Hstate Hrules Hplan Hslots.
    - cbn [plan_rules] in Hplan. inversion Hplan; subst. reflexivity.
    - cbn [plan_rules] in Hplan.
      destruct (plan_rule i (Rule V.t q acts) st) as [[nextst c] cs] eqn:Hrule.
      assert (Hnext : planner_state_exact nextst) by (eapply plan_rule_exact; eassumption).
      assert (Hheadslots : forall f perm slot,
          trie_get (slot_code f perm) (planner_table nextst) = Some slot ->
          slot_matches table f perm slot = true).
      { intros f perm slot Hget. apply Hslots.
        eapply plan_rules_lookup; [exact Hplan|exact Hget]. }
      destruct (Hrules (Rule V.t q acts) st i nextst c cs (or_introl eq_refl)
        Hstate Hrule Hheadslots) as [Hnaive Hsemis].
      rewrite planner_rules_accumulators in Hplan.
      destruct (plan_rules rest (N.succ i) nextst [] []) as [[final nr] sr] eqn:Hrest.
      inversion Hplan; subst st' nv sn.
      rewrite !rev_app_distr, rev_append_rev, app_nil_r, rev_involutive.
      cbn [rev app check_rule_plans]. rewrite Hnaive.
      pose proof (planner_rule_semis_length i (Rule V.t q acts) st nextst c cs Hrule)
        as Hlength. cbn [query] in Hlength. rewrite <- Hlength.
      rewrite planner_check_semis_append by exact Hsemis.
      eapply IH; [exact Hnext| |exact Hrest|exact Hslots].
      intros r s j s' c' cs' Hin Hs Hr Ht. eapply Hrules;
        [now right|exact Hs|exact Hr|exact Ht].
  Qed.

  (** A well-laid-out atom passes checking and adds its columns to the used-key trie. *)
  Lemma planner_check_atom_from_parts : forall newok checknames n table f ts copy used count
      src s pairs srcTail colsTail copy' remainingSrc remainingCols copied,
    pairs <> [] -> NoDup (map fst pairs) -> Forall (fun p => fst p < n) pairs ->
    length pairs = length ts -> source_slot newok src = Some s ->
    slot_matches table f (map snd (sort_pairs pairs)) s = true ->
    planner_used_count used count ->
    check_terms V.eqb checknames ts 0 Empty copy Empty srcTail colsTail false =
      Some (copy', planner_inverse pairs Empty, remainingSrc, remainingCols, copied) ->
    exists used' count',
      check_atom V.eqb newok checknames n table f ts copy used count
        (src :: srcTail) (map fst (sort_pairs pairs) :: colsTail) =
        Some (copy', used', count', remainingSrc, remainingCols, copied) /\
      planner_used_count used' count' /\
      forall k, trie_get (N.succ_pos (nat_n k)) used' = Some tt <->
        trie_get (N.succ_pos (nat_n k)) used = Some tt \/ In k (map fst pairs).
  Proof.
    intros newok checknames n table f ts copy used count src s pairs srcTail colsTail
      copy' remainingSrc remainingCols copied Hnonempty Hnodup Hrange Hlength
      Hsource Hslot Hcount Hterms.
    pose proof (planner_sorted_column_ok pairs n Hnonempty Hnodup Hrange) as Hcolumn.
    destruct (planner_column_perm_sorted pairs used count Hnodup Hcount)
      as [used' [count' [Hread [Hcount' Hused]]]].
    exists used', count'. split.
    - cbn [check_atom]. rewrite Hsource, Hcolumn, length_map,
        planner_sort_pairs_length, Hlength, Nat.eqb_refl, Hterms, Hread, Hslot.
      reflexivity.
    - split; [exact Hcount'|exact Hused].
  Qed.

  (** A completed name table agrees with every real variable registered by the planner. *)
  Lemma planner_final_names : forall base names nc nm fresh cn mn,
    base = length cn -> NoDup (cn ++ mn) ->
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    exists checknames,
      var_table (rev_append cn (rev_append mn [])) 0 Empty = Some checknames /\
      forall x j, trie_get x names = Some j -> trie_get x checknames = Some (nat_n j).
  Proof.
    intros base names nc nm fresh cn mn Hbase Hnodup [Hlength Hpositions].
    assert (Hvars : NoDup (rev_append cn (rev_append mn []))).
    { rewrite !rev_append_rev, app_nil_r.
      eapply Permutation_NoDup; [|exact Hnodup].
      apply Permutation_app; apply Permutation_rev. }
    destruct (planner_var_table_empty _ Hvars) as [checknames [Htable Hlookup]].
    exists checknames. split; [exact Htable|]. intros x j Hget.
    destruct (Hpositions x j Hget) as [k [Hindex Hnth]].
    rewrite planner_nat_n_spec. apply Hlookup.
    rewrite !rev_append_rev, app_nil_r.
    rewrite nth_error_app2 by (rewrite length_rev; lia).
    replace (j - length (rev cn)) with k by (rewrite length_rev; lia).
    exact Hnth.
  Qed.

  (** Literal indices are distinct fresh main positions allocated after the starting floor. *)
  Definition planner_literals_ok (bound : positive) (base floor : nat) (lay : var_layout)
      (lits : list (nat * V.t)) : Prop :=
    match lay with
    | VarLayout _ _ nm fresh _ mn =>
        (bound < fresh)%positive /\ floor <= nm /\ nm = length mn /\
        NoDup (map fst lits) /\ forall j v, In (j, v) lits ->
          exists k x, j = base + k /\ floor <= k /\ k < nm /\ (bound < x)%positive /\
            nth_error (rev mn) k = Some x
    end.

  (** Changing non-main fields preserves every earlier literal position. *)
  Lemma planner_literals_reframe : forall bound base floor names nc nm fresh cn mn lits
      names' nc' fresh' cn',
    planner_literals_ok bound base floor (VarLayout names nc nm fresh cn mn) lits ->
    (bound < fresh')%positive ->
    planner_literals_ok bound base floor (VarLayout names' nc' nm fresh' cn' mn) lits.
  Proof.
    intros bound base floor names nc nm fresh cn mn lits names' nc' fresh' cn'
      [_ Hrest] Hfresh. split; assumption.
  Qed.

  (** Adding a main position preserves every earlier literal position. *)
  Lemma planner_literals_main : forall bound base floor names nc nm fresh cn mn lits
      names' nc' fresh' cn' x,
    planner_literals_ok bound base floor (VarLayout names nc nm fresh cn mn) lits ->
    (bound < fresh')%positive ->
    planner_literals_ok bound base floor
      (VarLayout names' nc' (S nm) fresh' cn' (x :: mn)) lits.
  Proof.
    intros bound base floor names nc nm fresh cn mn lits names' nc' fresh' cn' x
      [Hfresh [Hfloor [Hlength [Hnodup Hpositions]]]] Hfresh'.
    cbn [planner_literals_ok]. split; [exact Hfresh'|]. split; [lia|].
    split; [cbn; congruence|]. split; [exact Hnodup|].
    intros j v Hin. destruct (Hpositions j v Hin) as [k [y [Hj [Hlower [Hupper [Hy Hnth]]]]]].
    exists k, y. split; [exact Hj|]. split; [exact Hlower|]. split; [lia|].
    split; [exact Hy|]. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
    rewrite length_rev. lia.
  Qed.

  (** Allocating a literal adds its fresh name at its new main index. *)
  Lemma planner_literals_add : forall bound base floor names nc nm fresh cn mn lits v,
    planner_literals_ok bound base floor (VarLayout names nc nm fresh cn mn) lits ->
    planner_literals_ok bound base floor
      (VarLayout names nc (S nm) (Pos.succ fresh) cn (fresh :: mn)) ((base + nm, v) :: lits).
  Proof.
    intros bound base floor names nc nm fresh cn mn lits v Hlits.
    destruct Hlits as [Hfresh [Hfloor [Hlength [Hnodup Hpositions]]]].
    cbn [planner_literals_ok]. split; [lia|]. split; [lia|]. split; [cbn; congruence|].
    split.
    - constructor; [|exact Hnodup]. intro Hin. apply in_map_iff in Hin as [[j w] [Heq Hin]].
      cbn in Heq. destruct (Hpositions j w Hin) as [k [x [Hj [_ [Hupper _]]]]]. lia.
    - intros j w [Heq|Hin].
      + injection Heq as <- <-. exists nm, fresh.
        split; [reflexivity|]. split; [exact Hfloor|]. split; [lia|].
        split; [exact Hfresh|]. cbn [rev]. rewrite nth_error_app2.
        * rewrite length_rev, <- Hlength, Nat.sub_diag. reflexivity.
        * rewrite length_rev. lia.
      + destruct (Hpositions j w Hin) as [k [x [Hj [Hlower [Hupper [Hx Hnth]]]]]].
        exists k, x. split; [exact Hj|]. split; [exact Hlower|]. split; [lia|].
        split; [exact Hx|]. cbn [rev]. rewrite nth_error_app1; [exact Hnth|].
        rewrite length_rev. lia.
  Qed.

  (** Term placement preserves the exact fresh positions of its literal sources. *)
  Lemma planner_place_literals : forall (ts : list (term V.t)) bound base floor pos seen
      lay pairs lits copied,
    planner_literals_ok bound base floor lay lits ->
    match place_terms base ts pos seen lay pairs lits copied with
    | (lay', _, lits', _) => planner_literals_ok bound base floor lay' lits'
    end.
  Proof.
    induction ts as [|t rest IH]; intros bound base floor pos seen lay pairs lits copied Hlits;
      cbn [place_terms].
    - exact Hlits.
    - destruct lay as [names nc nm fresh cn mn].
      assert (Hfresh : (bound < fresh)%positive) by exact (proj1 Hlits).
      destruct t as [x|v]; cbn [place_terms].
      + destruct (trie_get x seen).
        * apply IH. eapply planner_literals_reframe; [exact Hlits|lia].
        * destruct (trie_get x names).
          -- apply IH. exact Hlits.
          -- apply IH. eapply planner_literals_main; [exact Hlits|exact Hfresh].
      + apply IH. apply planner_literals_add. exact Hlits.
  Qed.

  (** Before an atom is placed, its empty literal list uses no main positions. *)
  Lemma planner_literals_initial : forall bound base names nc nm fresh cn mn,
    nm = length mn -> (bound < fresh)%positive ->
    planner_literals_ok bound base nm (VarLayout names nc nm fresh cn mn) [].
  Proof.
    intros bound base names nc nm fresh cn mn Hlength Hfresh.
    cbn [planner_literals_ok]. split; [exact Hfresh|]. split; [lia|].
    split; [exact Hlength|]. split; [constructor|]. intros j v Hin. contradiction.
  Qed.

  (** Reordering literal sources preserves their distinct fresh positions. *)
  Lemma planner_literals_permutation : forall bound base floor lay lits lits',
    Permutation lits lits' -> planner_literals_ok bound base floor lay lits ->
    planner_literals_ok bound base floor lay lits'.
  Proof.
    intros bound base floor [names nc nm fresh cn mn] lits lits' Hperm
      [Hfresh [Hfloor [Hlength [Hnodup Hpositions]]]].
    cbn [planner_literals_ok]. split; [exact Hfresh|]. split; [exact Hfloor|].
    split; [exact Hlength|]. split.
    - eapply Permutation_NoDup; [apply Permutation_map; exact Hperm|exact Hnodup].
    - intros j v Hin. apply (Hpositions j v).
      eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
      exact Hin.
  Qed.

  (** The literal positions of the planned atoms retain their associated values. *)
  Definition planner_atom_literals (atoms : list (atom_plan V.t)) : list (nat * V.t) :=
    flat_map (fun atom => match atom with AtomPlan _ _ lits => lits end) atoms.

  (** Forgetting literal values yields the guard's literal-index enumeration. *)
  Lemma planner_atom_literal_indices : forall atoms,
    map fst (planner_atom_literals atoms) = planner_literal_indices atoms.
  Proof.
    induction atoms as [|[s col lits] rest IH];
      cbn [planner_atom_literals planner_literal_indices flat_map].
    - reflexivity.
    - unfold planner_atom_literals, planner_literal_indices in IH. rewrite map_app, IH. reflexivity.
  Qed.

  (** Planning all atoms maintains distinct fresh positions for all literal sources. *)
  Lemma planner_atoms_literals : forall (q : list (atom V.t)) bound base ai lay st outs post,
    planner_literals_ok bound base 0 lay (planner_atom_literals outs) ->
    match plan_atoms base q ai lay st outs post with
    | (lay', _, outs', _) => planner_literals_ok bound base 0 lay' (planner_atom_literals outs')
    end.
  Proof.
    induction q as [|a rest IH]; intros bound base ai lay st outs post Hlits;
      cbn [plan_atoms].
    - exact Hlits.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + pose proof (planner_place_literals (args ++ option_list res) bound base 0 0 Empty
          lay [] (planner_atom_literals outs) false Hlits) as Hplaced.
        rewrite planner_place_acc in Hplaced.
        destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[lay' pairs] lits] copied].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        apply IH. cbn [planner_atom_literals flat_map].
        eapply planner_literals_permutation; [|exact Hplaced].
        rewrite rev_append_rev, app_nil_r.
        apply Permutation_app; [apply Permutation_rev|reflexivity].
      + apply IH. exact Hlits.
  Qed.

  (** Reversing the atom list only reorders its literal sources. *)
  Lemma planner_atom_literals_rev : forall atoms,
    Permutation (planner_atom_literals atoms) (planner_atom_literals (rev atoms)).
  Proof.
    intro atoms. unfold planner_atom_literals. apply Permutation_flat_map.
    apply Permutation_rev.
  Qed.

  (** Building the fresh-index table preserves its previous entries. *)
  Lemma planner_layout_fresh_preserves : forall vars bound copies j allowed result,
    layout_fresh bound copies vars j allowed = Some result ->
    forall key, trie_get key allowed = Some tt -> trie_get key result = Some tt.
  Proof.
    induction vars as [|x rest IH]; intros bound copies j allowed result Htable key Hget.
    - destruct copies; cbn [layout_fresh] in Htable;
        [injection Htable as <-; exact Hget|discriminate].
    - destruct copies as [|copies]; cbn [layout_fresh] in Htable.
      + destruct (Pos.ltb bound x).
        * eapply IH; [exact Htable|].
          destruct (Pos.eq_dec key (N.succ_pos j)) as [Heq|Hneq].
          -- subst key. apply PTrie.get_set_same.
          -- rewrite PTrie.get_set_other by exact Hneq. exact Hget.
        * eapply IH; eauto.
      + destruct (Pos.ltb bound x); [eapply IH; eauto|discriminate].
  Qed.

  (** A fresh noncopy name gives an available literal index. *)
  Lemma planner_layout_fresh_member : forall vars bound copies j allowed result n x,
    layout_fresh bound copies vars j allowed = Some result ->
    nth_error vars n = Some x -> copies <= n -> (bound < x)%positive ->
    trie_get (N.succ_pos (j + N.of_nat n)%N) result = Some tt.
  Proof.
    induction vars as [|y rest IH]; intros bound copies j allowed result n x
      Htable Hnth Hcopy Hfresh; [destruct n; discriminate|].
    destruct copies as [|copies]; cbn [layout_fresh] in Htable.
    - destruct n as [|n].
      + cbn [nth_error] in Hnth. injection Hnth as <-.
        assert (Htest : Pos.ltb bound y = true) by (apply Pos.ltb_lt; exact Hfresh).
        rewrite Htest in Htable. rewrite N.add_0_r.
        eapply planner_layout_fresh_preserves; [exact Htable|apply PTrie.get_set_same].
      + cbn [nth_error] in Hnth.
        replace (j + N.of_nat (S n))%N with (N.succ j + N.of_nat n)%N
          by (rewrite Nat2N.inj_succ; lia).
        eapply IH; [exact Htable|exact Hnth|lia|exact Hfresh].
    - destruct n as [|n]; [lia|]. cbn [nth_error] in Hnth.
      destruct (Pos.ltb bound y); [|discriminate].
      replace (j + N.of_nat (S n))%N with (N.succ j + N.of_nat n)%N
        by (rewrite Nat2N.inj_succ; lia).
      eapply IH; [exact Htable|exact Hnth|lia|exact Hfresh].
  Qed.

  (** Every generated query layout keeps copies, literals and real variables separate. *)
  Lemma planner_generated_layout : forall (q : list (atom V.t)) st names nc nm fresh cn mn
      st' outs post,
    plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [] =
      (VarLayout names nc nm fresh cn mn, st', outs, post) ->
    forall pivot, layout_ok q (rev_append cn (rev_append mn []))
      (plan_srcs (rev_append outs []) pivot) (plan_cols (rev_append outs [])) = true.
  Proof.
    intros q st names nc nm fresh cn mn st' outs post Hplan pivot.
    pose proof (planner_atoms_copies q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] []) as Hcopies.
    pose proof (planner_atoms_lengths q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] [] eq_refl eq_refl) as Hlengths.
    pose proof (planner_atoms_names q (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []
      (planner_names_initial (query_max q 1%positive))) as Hnames.
    specialize (Hnames (fun x Hin => planner_query_max_member q 1%positive x Hin)).
    assert (Hinitial : planner_literals_ok (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) []).
    { apply planner_literals_initial; [reflexivity|lia]. }
    pose proof (planner_atoms_literals q (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [] Hinitial)
      as Hlits.
    rewrite Hplan in Hcopies, Hlengths, Hnames, Hlits.
    cbn in Hcopies, Hlengths.
    destruct Hlengths as [Hcn Hmn].
    destruct Hnames as [Hfresh [Hnodup [Hbelow [Hcopy _]]]].
    pose proof (planner_literals_permutation (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout names nc nm fresh cn mn) (planner_atom_literals outs)
      (planner_atom_literals (rev outs)) (planner_atom_literals_rev outs) Hlits) as Hrevlits.
    destruct Hrevlits as [_ [_ [_ [Hliteral_nodup Hliteral_position]]]].
    rewrite !rev_append_rev, !app_nil_r. unfold layout_ok.
    destruct (planner_layout_fresh_complete (rev cn ++ rev mn) (query_max q 1%positive)
      (query_copies q 0) 0 Empty) as [allowed Hallowed].
    - rewrite length_app, !length_rev. lia.
    - replace (query_copies q 0) with (length (rev cn)) by (rewrite length_rev; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
      apply Forall_rev. exact Hcopy.
    - rewrite Hallowed. apply layout_literals_plans.
      + rewrite <- planner_atom_literal_indices. exact Hliteral_nodup.
      + intros j Hin. rewrite <- planner_atom_literal_indices in Hin.
        apply in_map_iff in Hin as [[j' v] [Heq Hin]]. cbn in Heq. subst j'.
        destruct (Hliteral_position j v Hin) as [k [x [Hj [_ [Hk [Hx Hnth]]]]]].
        assert (Hvar : nth_error (rev cn ++ rev mn) j = Some x).
        { rewrite nth_error_app2; [|rewrite length_rev; lia].
          replace (j - length (rev cn)) with k by (rewrite length_rev; lia). exact Hnth. }
        rewrite planner_nat_n_spec.
        exact (planner_layout_fresh_member (rev cn ++ rev mn) (query_max q 1%positive)
          (query_copies q 0) 0 Empty allowed j x Hallowed Hvar ltac:(lia) Hx).
  Qed.
  (** An initial atom accumulator only appends to the reversed generated atoms. *)
  Lemma planner_atoms_out_acc : forall (q : list (atom V.t)) base ai lay st outs post,
    plan_atoms base q ai lay st outs post =
    let '(lay', st', newouts, post') := plan_atoms base q ai lay st [] post in
    (lay', st', newouts ++ outs, post').
  Proof.
    induction q as [|a rest IH]; intros base ai lay st outs post.
    - reflexivity.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + destruct (place_terms base (args ++ option_list res) 0 Empty lay [] [] false)
          as [[[lay' pairs] lits] copied].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        rewrite (IH base (S ai) lay' st'
          (AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits []) :: outs)
          (if copied then ai :: post else post)).
        rewrite (IH base (S ai) lay' st'
          [AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits [])]
          (if copied then ai :: post else post)).
        destruct (plan_atoms base rest (S ai) lay' st' []
          (if copied then ai :: post else post)) as [[[lastlay lastst] atoms] lastpost].
        cbn. rewrite <- app_assoc. reflexivity.
      + apply IH.
  Qed.

  (** Later atoms never decrease the number of allocated main indices. *)
  Lemma planner_atoms_mains : forall (q : list (atom V.t)) base ai
      names nc nm fresh cn mn st outs post,
    match plan_atoms base q ai (VarLayout names nc nm fresh cn mn) st outs post with
    | (VarLayout _ _ nm' _ _ _, _, _, _) => nm <= nm'
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai names nc nm fresh cn mn st outs post;
      cbn [plan_atoms].
    - lia.
    - destruct a as [f args res|p args res]; cbn [plan_atoms].
      + pose proof (planner_place_mains (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false) as Hplaced.
        destruct (place_terms base (args ++ option_list res) 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false)
          as [[[lay pairs] lits] copied].
        destruct lay as [names' nc' nm' fresh' cn' mn']; cbn in Hplaced.
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s st'].
        pose proof (IH base (S ai) names' nc' nm' fresh' cn' mn' st'
          (AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits []) :: outs)
          (if copied then ai :: post else post)) as Hrest.
        destruct (plan_atoms base rest (S ai) (VarLayout names' nc' nm' fresh' cn' mn') st'
          (AtomPlan s (map fst (sort_pairs pairs)) (rev_append lits []) :: outs)
          (if copied then ai :: post else post)) as [[[lastlay lastst] atoms] lastpost].
        destruct lastlay. cbn in Hrest. lia.
      + apply IH.
  Qed.

  (** A naive plan has no pivot, and a semi-naive plan permits its chosen new source. *)
  Lemma planner_pivot_source : forall newok s pivot,
    (newok = false -> pivot = None) -> source_slot newok (@pivot_source V.t s pivot) = Some s.
  Proof.
    intros newok s [pivot|] Hpivot; [destruct pivot|];
      destruct newok; cbn [pivot_source source_slot]; try reflexivity.
    specialize (Hpivot eq_refl). discriminate.
  Qed.

  (** Moving past an atom preserves the absence of a pivot in a naive plan. *)
  Lemma planner_pivot_tail : forall newok pivot,
    (newok = false -> pivot = None) -> (newok = false -> pivot_next pivot = None).
  Proof.
    intros newok pivot Hpivot Hfalse. rewrite (Hpivot Hfalse). reflexivity.
  Qed.

  (** An empty name table has no registered main positions. *)
  Lemma planner_main_initial : forall base fresh,
    planner_main_positions base (VarLayout Empty 0 0 fresh [] []).
  Proof.
    intros base fresh. split; [reflexivity|]. intros x j Hget.
    rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** A generated query passes checking against its final names and slot identities. *)
  Lemma planner_query_checked : forall (q : list (atom V.t)) base ai names nc nm fresh cn mn
      st post newok pivot checknames n table used count,
    Forall (fun a => match a with
      | Fun _ _ args res => args ++ option_list res <> []
      | Prim _ _ _ _ => True
      end) q ->
    planner_main_positions base (VarLayout names nc nm fresh cn mn) ->
    query_copies q nc <= base -> planner_used_count used count ->
    (forall j, trie_get (N.succ_pos (nat_n j)) used = Some tt <->
      planner_used base (VarLayout names nc nm fresh cn mn) j) ->
    (newok = false -> pivot = None) ->
    match plan_atoms base q ai (VarLayout names nc nm fresh cn mn) st [] post with
    | (VarLayout names' nc' nm' _ _ _, st', atoms, post') =>
        base + nm' <= n ->
        (forall x j, trie_get x names' = Some j ->
          trie_get x checknames = Some (nat_n j)) ->
        (forall f perm s, trie_get (slot_code f perm) (planner_table st') = Some s ->
          slot_matches table f perm s = true) ->
        check_query V.eqb newok checknames n table q ai (nat_n nc) used count
          (plan_srcs (rev_append atoms []) pivot) (plan_cols (rev_append atoms [])) post =
        Some (nat_n (nc' + nm'), [], [], post')
    end.
  Proof.
    induction q as [|a rest IH]; intros base ai names nc nm fresh cn mn st post
      newok pivot checknames n table used count Hreads Hmain Hbudget Hcount Hused Hpivot.
    - cbn [plan_atoms query_copies] in *. intros Hn Hnames Hslots.
      assert (Htotal : count = N.of_nat (nc + nm)).
      { apply (planner_used_range_count used count base nc nm Hcount Hbudget). exact Hused. }
      cbn [rev_append plan_srcs plan_cols check_query]. rewrite Htotal, planner_nat_n_spec.
      reflexivity.
    - inversion Hreads as [|a' rest' Hhead Htail]; subst a' rest'.
      destruct a as [f args res|p args res]; cbn [plan_atoms query_copies] in *.
      + pose proof (planner_place_copies (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false) as Hcopies.
        pose proof (planner_place_positions (args ++ option_list res) base 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false Hmain) as Hpositions.
        pose proof (planner_place_coverage (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn false Hmain) as Hcoverage.
        assert (Hcopy_budget : term_copies Empty (args ++ option_list res) nc <= base).
        { pose proof (planner_query_copies_acc rest
            (term_copies Empty (args ++ option_list res) nc)).
          lia. }
        pose proof (planner_place_pairs (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn [] [] false Hmain (planner_pairs_empty base Empty _)
          Hcopy_budget) as Hpairs.
        destruct (place_terms base (args ++ option_list res) 0 Empty
          (VarLayout names nc nm fresh cn mn) [] [] false)
          as [[[lay pairs] lits] copied] eqn:Hplaced.
        destruct lay as [nextnames nextnc nextnm nextfresh nextcn nextmn].
        destruct (add_slot f (map snd (sort_pairs pairs)) st) as [s nextst] eqn:Hslot.
        rewrite planner_atoms_out_acc.
        destruct (plan_atoms base rest (S ai)
          (VarLayout nextnames nextnc nextnm nextfresh nextcn nextmn) nextst []
          (if copied then ai :: post else post))
          as [[[lastlay lastst] atoms] lastpost] eqn:Hrest.
        destruct lastlay as [lastnames lastnc lastnm lastfresh lastcn lastmn].
        intros Hn Hnames Hslots.
        assert (Hnext_names : forall x j, trie_get x nextnames = Some j ->
            trie_get x checknames = Some (nat_n j)).
        { intros x j Hget.
          pose proof (planner_atoms_registered rest base (S ai) nextnames nextnc nextnm
            nextfresh nextcn nextmn nextst [] (if copied then ai :: post else post)
            x j Hget) as Hregistered.
          rewrite Hrest in Hregistered. apply Hnames. exact Hregistered. }
        assert (Hnext_mains : nextnm <= lastnm).
        { pose proof (planner_atoms_mains rest base (S ai) nextnames nextnc nextnm nextfresh
            nextcn nextmn nextst [] (if copied then ai :: post else post)) as Hmains.
          rewrite Hrest in Hmains. exact Hmains. }
        assert (Hpair_length : length pairs = length (args ++ option_list res)).
        { pose proof (planner_place_positions_list base (args ++ option_list res) 0 Empty
            (VarLayout names nc nm fresh cn mn) [] [] false) as Hlist.
          rewrite Hplaced in Hlist. cbn in Hlist.
          apply (f_equal (@length nat)) in Hlist.
          rewrite length_map, length_app, length_rev, length_seq in Hlist. cbn in Hlist. lia. }
        destruct Hpairs as [Hpair_nodup Hpair_bound].
        assert (Hpair_nonempty : pairs <> []).
        { intro Heq. subst pairs. cbn in Hpair_length. apply Hhead.
          apply length_zero_iff_nil. lia. }
        assert (Hpair_n : Forall (fun pair => fst pair < n) pairs).
        { apply Forall_forall. intros pair Hin.
          apply Forall_forall with (x := pair) in Hpair_bound; [lia|exact Hin]. }
        assert (Hmatch : slot_matches table f (map snd (sort_pairs pairs)) s = true).
        { apply Hslots. eapply plan_atoms_lookup; [exact Hrest|].
          eapply add_slot_number. exact Hslot. }
        pose proof (planner_place_check (args ++ option_list res) base 0 Empty
          names nc nm fresh cn mn false checknames Empty
          (plan_srcs (rev_append atoms []) (pivot_next pivot))
          (plan_cols (rev_append atoms []))) as Hterms.
        rewrite Hplaced in Hterms. specialize (Hterms Hnext_names).
        destruct (planner_check_atom_from_parts newok checknames n table f
          (args ++ option_list res) (nat_n nc) used count (pivot_source s pivot) s pairs
          (literal_sources (rev lits) (plan_srcs (rev_append atoms []) (pivot_next pivot)))
          (literal_cols (rev lits) (plan_cols (rev_append atoms []))) (nat_n nextnc)
          (plan_srcs (rev_append atoms []) (pivot_next pivot))
          (plan_cols (rev_append atoms [])) copied Hpair_nonempty Hpair_nodup Hpair_n
          Hpair_length (planner_pivot_source newok s pivot Hpivot) Hmatch Hcount Hterms)
          as [used' [count' [Hatom [Hcount' Hused']]]].
        assert (Hnext_used : forall j, trie_get (N.succ_pos (nat_n j)) used' = Some tt <->
            planner_used base (VarLayout nextnames nextnc nextnm nextfresh nextcn nextmn) j).
        { intro j. rewrite Hused', Hused, Hcoverage. reflexivity. }
        pose proof (IH base (S ai) nextnames nextnc nextnm nextfresh nextcn nextmn nextst
          (if copied then ai :: post else post) newok (pivot_next pivot) checknames n table
          used' count' Htail Hpositions ltac:(rewrite Hcopies; exact Hbudget) Hcount'
          Hnext_used (planner_pivot_tail newok pivot Hpivot)) as Hchecked.
        rewrite Hrest in Hchecked. specialize (Hchecked Hn Hnames Hslots).
        rewrite !rev_append_rev, !app_nil_r, rev_app_distr.
        cbn [rev app plan_srcs plan_cols]. cbn [check_query].
        rewrite !rev_append_rev, !app_nil_r in Hatom, Hchecked.
        rewrite Hatom. exact Hchecked.
      + exact (IH base (S ai) names nc nm fresh cn mn st (ai :: post) newok pivot checknames
          n table used count Htail Hmain Hbudget Hcount Hused Hpivot).
  Qed.

  (** A finished rule layout has the counted copies and distinct position-correct names. *)
  Lemma planner_rule_layout : forall (q : list (atom V.t)) st names nc nm fresh cn mn
      st' atoms post,
    plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [] =
      (VarLayout names nc nm fresh cn mn, st', atoms, post) ->
    nc = query_copies q 0 /\ nm = length mn /\ query_copies q 0 = length cn /\
    NoDup (cn ++ mn) /\
    planner_main_positions (query_copies q 0) (VarLayout names nc nm fresh cn mn).
  Proof.
    intros q st names nc nm fresh cn mn st' atoms post Hplan.
    pose proof (planner_atoms_copies q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] []) as Hcopies.
    pose proof (planner_atoms_lengths q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] [] eq_refl eq_refl) as Hlengths.
    pose proof (planner_atoms_names q (query_max q 1%positive) (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []
      (planner_names_initial (query_max q 1%positive))
      (fun x Hin => planner_query_max_member q 1%positive x Hin)) as Hnames.
    pose proof (planner_atoms_positions q (query_copies q 0) 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] []
      (planner_main_initial (query_copies q 0) (Pos.succ (query_max q 1%positive))))
      as Hpositions.
    rewrite Hplan in Hcopies, Hlengths, Hnames, Hpositions.
    cbn in Hcopies, Hlengths.
    destruct Hlengths as [Hcn Hmn]. destruct Hnames as [_ [Hnodup _]].
    split; [exact Hcopies |]. split; [exact Hmn |]. split; [lia |].
    split; assumption.
  Qed.

  (** With no allocated indices, the empty used-key trie represents the layout exactly. *)
  Lemma planner_initial_used : forall base fresh j,
    trie_get (N.succ_pos (nat_n j)) (@Empty unit) = Some tt <->
    planner_used base (VarLayout Empty 0 0 fresh [] []) j.
  Proof.
    intros base fresh j. rewrite PTrie.get_empty. cbn [planner_used].
    split; [discriminate | lia].
  Qed.

  (** The checker accepts every allowed pivot of a generated rule layout. *)
  Lemma planner_cplan_checked : forall (q : list (atom V.t)) acts st names nc nm fresh cn mn
      st' atoms post table i newok pivot,
    Forall (fun a => match a with
      | Fun _ _ args res => args ++ option_list res <> []
      | Prim _ _ _ _ => True
      end) q ->
    plan_atoms (query_copies q 0) q 0
      (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [] =
      (VarLayout names nc nm fresh cn mn, st', atoms, post) ->
    (forall f perm slot, trie_get (slot_code f perm) (planner_table st') = Some slot ->
      slot_matches table f perm slot = true) ->
    (newok = false -> pivot = None) ->
    check_cplan V.eqb newok table i (Rule V.t q acts)
      (CPlan V.t i (JPlan (query_copies q 0 + nm) (plan_cols (rev_append atoms [])))
        (plan_srcs (rev_append atoms []) pivot) (rev_append cn (rev_append mn []))
        (rev_append post [])) = true.
  Proof.
    intros q acts st names nc nm fresh cn mn st' atoms post table i newok pivot
      Hreads Hplan Hslots Hpivot.
    destruct (planner_rule_layout q st names nc nm fresh cn mn st' atoms post Hplan)
      as [Hcopies [Hmn [Hbase [Hdistinct Hpositions]]]].
    destruct (planner_final_names (query_copies q 0) names nc nm fresh cn mn
      Hbase Hdistinct Hpositions) as [checknames [Htable Hnames]].
    assert (Hlength : length (rev_append cn (rev_append mn [])) = query_copies q 0 + nm).
    { rewrite !rev_append_rev, app_nil_r, length_app, !length_rev. lia. }
    pose proof (planner_query_checked q (query_copies q 0) 0 Empty 0 0
      (Pos.succ (query_max q 1%positive)) [] [] st [] newok pivot checknames
      (query_copies q 0 + nm) table Empty 0%N Hreads
      (planner_main_initial (query_copies q 0) (Pos.succ (query_max q 1%positive)))
      (Nat.le_refl _) planner_used_count_empty
      (planner_initial_used (query_copies q 0) (Pos.succ (query_max q 1%positive))) Hpivot)
      as Hquery.
    rewrite Hplan in Hquery. specialize (Hquery (Nat.le_refl _) Hnames Hslots).
    rewrite Hcopies in Hquery.
    cbn [check_cplan]. rewrite N.eqb_refl, Hlength, Nat.eqb_refl, Htable.
    rewrite (planner_generated_layout q st names nc nm fresh cn mn st' atoms post Hplan pivot).
    cbn [nat_n] in Hquery.
    rewrite Hquery, N.eqb_refl. apply planner_nats_eqb_refl.
  Qed.

  (** A checker-valid pivot family gives all of a rule's semi-naive plans. *)
  Lemma planner_semis_checked : forall table i (r : rule V.t) j vars post atoms todo m,
    (forall pivot, check_cplan V.eqb true table i r
      (CPlan V.t i j (plan_srcs atoms (Some pivot)) vars post) = true) ->
    Forall (fun c => check_cplan V.eqb true table i r c = true)
      (semi_plans i j vars post atoms m todo).
  Proof.
    intros table i r j vars post atoms todo. induction todo as [| a rest IH]; intros m Hchecked.
    - constructor.
    - cbn [semi_plans]. constructor; [apply Hchecked | now apply IH].
  Qed.

  (** A sorted rule produces checked naive and semi-naive plans in any containing slot table. *)
  Lemma planner_rule_checked : forall (p : program V.t) table i r st st' c cs,
    @rule_ok V.t (program_sorts p) (program_kind p) r -> planner_state_exact st ->
    plan_rule i r st = (st', c, cs) ->
    (forall f perm slot, trie_get (slot_code f perm) (planner_table st') = Some slot ->
      slot_matches table f perm slot = true) ->
    check_cplan V.eqb false table i r c = true /\
      Forall (fun c' => check_cplan V.eqb true table i r c' = true) cs.
  Proof.
    intros p table i [q acts] st st' c cs [g [Hquery Hactions]] Hstate Hrule Hslots.
    cbn [query] in Hquery.
    pose proof (planner_query_reads _ _ _ _ _ Hquery) as Hreads.
    cbn [plan_rule] in Hrule.
    destruct (plan_atoms (query_copies q 0) q 0
        (VarLayout Empty 0 0 (Pos.succ (query_max q 1%positive)) [] []) st [] [])
      as [[[lay nextst] atoms] post] eqn:Hatoms.
    destruct lay as [names nc nm fresh cn mn]. inversion Hrule; subst st' c cs.
    split.
    - eapply planner_cplan_checked; [exact Hreads | exact Hatoms | exact Hslots |].
      intros. reflexivity.
    - apply planner_semis_checked. intro pivot.
      eapply planner_cplan_checked; [exact Hreads | exact Hatoms | exact Hslots |].
      discriminate.
  Qed.

  Lemma F28_plan_shape : forall p, program_ok p -> check_shape p (plan p) = true.
  Proof.
    intros [ds rs] Hprogram.
    unfold check_shape, check_shape_with, plan, plan_program.
    destruct (plan_rules rs 0%N (full_slots ds Empty (SlotState Empty 0%N [])) [] [])
      as [[[stored next rows] nv] sn] eqn:Hrules.
    assert (Hinitial : planner_state_exact (full_slots ds Empty (SlotState Empty 0%N []))).
    { apply full_slots_exact. exact planner_state_empty. }
    assert (Hfinal : planner_state_exact (SlotState stored next rows)).
    { eapply plan_rules_exact; [exact Hinitial|exact Hrules]. }
    assert (Hvalid : Forall (planner_slot_valid (decl_widths ds Empty)) rows).
    { exact (plan_rules_slots_valid (Program V.t ds rs) rs 0%N
        (full_slots ds Empty (SlotState Empty 0%N [])) [] [] (SlotState stored next rows)
        nv sn Hprogram (planner_full_slots_valid ds) Hrules). }
    assert (Hvalidrev : Forall (planner_slot_valid (decl_widths ds Empty)) (rev rows)).
    { apply Forall_rev. exact Hvalid. }
    destruct (planner_slot_table (decl_widths ds Empty) stored next rows Hfinal
      Hvalidrev) as [checked [Hscan Hnumbers]].
    rewrite !rev_append_rev, !app_nil_r, Hscan.
    eapply planner_rules_checked; [exact Hinitial| |exact Hrules|].
    - intros r s j s' c cs Hin Hstate Hrule Hslots.
      eapply (planner_rule_checked (Program V.t ds rs));
        [|exact Hstate|exact Hrule|exact Hslots].
      exact ((proj1 (Forall_forall _ _)) Hprogram r Hin).
    - intros f perm slot Hget. apply slot_matches_complete. apply Hnumbers. exact Hget.
  Qed.

  Lemma plan_checked : forall p, program_ok p -> plans_ok p (plan p).
  Proof.
    intros p Hprogram. unfold plans_ok, check_plan.
    rewrite (proj2 (check_program_spec V.t p) Hprogram), (F28_plan_shape p Hprogram).
    reflexivity.
  Qed.

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
  Definition c_run : N := 1. (* STUB *)
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
  Proof. Admitted. (* STUB *)

  Lemma wbits_spec : forall p,
    wbits p = fold_right (fun x n => Nat.max (Pos.size_nat x) n)
      0 (program_words V.encode p).
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma T_load_le : forall p cp,
    (T_load p cp <= D.T_init (decls V.t p) (Syntax.slots V.t cp) + c_run)%N.
  Proof. Admitted. (* STUB *)

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

  Definition k_driver : N := 1. (* STUB *)
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
  Definition k_check : N := 1. (* STUB *)
  (** Two identifiers that occur in rows and are equal in the view are identical. *)
  Definition row_ids_unique (w : Model.view (V := V.t)) : Prop :=
    forall f k o f' k' o' i j, row w f k o -> row w f' k' o' ->
      In (Id i) (k ++ option_list o) -> In (Id j) (k' ++ option_list o') ->
      same w i j -> i = j.

  (** Every accepted plan carries the rule index used for checking it. *)
  Lemma run_check_cplan_index : forall newok table i r c,
    check_cplan V.eqb newok table i r c = true -> rule_ix V.t c = i.
  Proof.
    intros newok table i [q acts] [ix [n cols] srcs vars post] Hcheck.
    cbn [check_cplan rule_ix] in *.
    destruct (N.eqb ix i) eqn:Hindex; [now apply N.eqb_eq|discriminate].
  Qed.

  (** A successful semi-naive scan consumes exactly a prefix of accepted plans. *)
  Lemma run_check_semis_split : forall k table i r cs tail,
    check_semis V.eqb table i r k cs = Some tail ->
    exists prefix, cs = prefix ++ tail /\
      Forall (fun c => check_cplan V.eqb true table i r c = true) prefix.
  Proof.
    induction k as [|k IH]; intros table i r cs tail Hcheck.
    - cbn [check_semis] in Hcheck. inversion Hcheck; subst tail.
      exists []. split; [reflexivity|constructor].
    - destruct cs as [|c cs]; cbn [check_semis] in Hcheck; [discriminate|].
      destruct (check_cplan V.eqb true table i r c) eqn:Hplan; [|discriminate].
      destruct (IH table i r cs tail Hcheck) as [prefix [Hprefix Hall]].
      exists (c :: prefix). split; [cbn; now rewrite Hprefix|].
      constructor; assumption.
  Qed.

  (** Every plan accepted with a rule list is checked against its indexed rule. *)
  Lemma run_check_rule_plans_member : forall rs table i naive semi,
    check_rule_plans V.eqb table rs i naive semi = true ->
    forall c, In c (naive ++ semi) -> exists k r newok,
      nth_error rs k = Some r /\ N.to_nat (rule_ix V.t c) = N.to_nat i + k /\
      check_cplan V.eqb newok table (rule_ix V.t c) r c = true.
  Proof.
    induction rs as [|[q acts] rs IH]; intros table i naive semi Hcheck c Hin.
    - destruct naive as [|d naive]; cbn [check_rule_plans] in Hcheck; [|discriminate].
      destruct semi; [contradiction|discriminate].
    - destruct naive as [|d naive]; cbn [check_rule_plans] in Hcheck; [discriminate|].
      destruct (check_cplan V.eqb false table i (Rule V.t q acts) d)
        eqn:Hplan; [|discriminate].
      destruct (check_semis V.eqb table i (Rule V.t q acts) (fun_count q) semi)
        as [tail|] eqn:Hsemis; [|discriminate].
      destruct (run_check_semis_split (fun_count q) table i (Rule V.t q acts)
        semi tail Hsemis) as [prefix [Hprefix Hall]].
      assert (Hhere : forall newok,
          check_cplan V.eqb newok table i (Rule V.t q acts) c = true ->
          exists k r newok,
            nth_error (Rule V.t q acts :: rs) k = Some r /\
            N.to_nat (rule_ix V.t c) = N.to_nat i + k /\
            check_cplan V.eqb newok table (rule_ix V.t c) r c = true).
      { intros newok Hc. pose proof (run_check_cplan_index newok table i
          (Rule V.t q acts) c Hc) as Hindex.
        exists 0, (Rule V.t q acts), newok. split; [reflexivity|].
        rewrite Hindex. split; [lia|exact Hc]. }
      assert (Hlater : In c (naive ++ tail) -> exists k r newok,
          nth_error (Rule V.t q acts :: rs) k = Some r /\
          N.to_nat (rule_ix V.t c) = N.to_nat i + k /\
          check_cplan V.eqb newok table (rule_ix V.t c) r c = true).
      { intro Htail. destruct (IH table (N.succ i) naive tail Hcheck c Htail)
          as [k [r [newok [Hnth [Hindex Hc]]]]].
        exists (S k), r, newok. split; [exact Hnth|].
        split; [rewrite N2Nat.inj_succ in Hindex; lia|exact Hc]. }
      apply in_app_or in Hin. destruct Hin as [[Heq|Hin]|Hin].
      + subst c. now apply (Hhere false).
      + apply Hlater. apply in_or_app. now left.
      + rewrite Hprefix in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        * apply (Hhere true). now apply Forall_forall with (x := c) in Hall.
        * apply Hlater. apply in_or_app. now right.
  Qed.

  (** A checked compiled plan has a valid slot table and an accepted indexed rule. *)
  Lemma run_plan_member : forall p cp c, plans_ok p cp -> In c (all_plans cp) ->
    exists table newok r,
      slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty =
        Some table /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      check_cplan V.eqb newok table (rule_ix V.t c) r c = true.
  Proof.
    intros [ds rs] [sl naive semi] c Hplan Hin.
    unfold plans_ok, check_plan in Hplan. apply andb_true_iff in Hplan.
    destruct Hplan as [_ Hshape]. unfold check_shape, check_shape_with in Hshape.
    destruct (slot_table (decl_widths ds Empty) sl 0 Empty)
      as [table|] eqn:Htable; [|discriminate].
    destruct (run_check_rule_plans_member rs table 0 naive semi Hshape c Hin)
      as [k [r [newok [Hnth [Hindex Hc]]]]].
    cbn in Hindex. exists table, newok, r. split; [exact Htable|].
    split; [now rewrite Hindex|exact Hc].
  Qed.

  (** A checked plan names a rule of its program. *)
  Lemma F33_plan_rule : forall p cp c, plans_ok p cp -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some (job_rule p c).
  Proof.
    intros p cp c Hplan Hin.
    destruct (run_plan_member p cp c Hplan Hin) as [table [newok [r [_ [Hnth _]]]]].
    unfold job_rule. erewrite nth_error_nth; [exact Hnth|exact Hnth].
  Qed.

  (** Repeated variables consume copy positions in their order within one atom. *)
  Fixpoint run_term_duplicates (seen : ptrie unit) (ts : list (term V.t)) : list positive :=
    match ts with
    | [] => []
    | Lit _ :: rest => run_term_duplicates seen rest
    | Var x :: rest =>
        match trie_get x seen with
        | Some _ => x :: run_term_duplicates seen rest
        | None => run_term_duplicates (PTrieCode.set x tt seen) rest
        end
    end.

  (** Function atoms consume consecutive pieces of the shared copy prefix. *)
  Fixpoint run_query_duplicates (q : list (atom V.t)) : list positive :=
    match q with
    | [] => []
    | Prim _ _ _ _ :: rest => run_query_duplicates rest
    | Fun _ _ args res :: rest =>
        run_term_duplicates Empty (args ++ option_list res) ++ run_query_duplicates rest
    end.

  (** The exact post list contains primitives and function atoms with repeated variables. *)
  Fixpoint run_query_post (q : list (atom V.t)) (ai : nat) : list nat :=
    match q with
    | [] => []
    | Prim _ _ _ _ :: rest => ai :: run_query_post rest (S ai)
    | Fun _ _ args res :: rest =>
        match run_term_duplicates Empty (args ++ option_list res) with
        | [] => run_query_post rest (S ai)
        | _ :: _ => ai :: run_query_post rest (S ai)
        end
    end.

  (** Counting repeated variables is the length of their explicit enumeration. *)
  Lemma run_term_duplicates_count : forall ts seen n,
    term_copies seen ts n = length (run_term_duplicates seen ts) + n.
  Proof.
    induction ts as [|[x|v] rest IH]; intros seen n; cbn [term_copies run_term_duplicates].
    - reflexivity.
    - destruct (trie_get x seen); rewrite IH; cbn [length]; lia.
    - apply IH.
  Qed.

  (** The planner's copy budget is the total repeated-variable count. *)
  Lemma run_query_duplicates_count : forall q n,
    query_copies q n = length (run_query_duplicates q) + n.
  Proof.
    induction q as [|[f args res|p args res] rest IH]; intro n;
      cbn [query_copies run_query_duplicates].
    - reflexivity.
    - rewrite IH, run_term_duplicates_count, length_app. lia.
    - apply IH.
  Qed.

  (** Equal concrete cells pass the post filter's equality test. *)
  Lemma run_cell_eqb_refl : forall c : cell V.t, cell_eqb V.eqb c c = true.
  Proof.
    intros [i|v]; cbn [cell_eqb]; [apply Pos.eqb_refl|apply planner_value_refl].
  Qed.

  (** The concrete-cell equality test reflects actual equality. *)
  Lemma run_cell_eqb_spec : forall a b : cell V.t,
    reflect (a = b) (cell_eqb V.eqb a b).
  Proof.
    intros [i|v] [j|w]; cbn [cell_eqb].
    - destruct (Pos.eqb_spec i j); constructor; congruence.
    - constructor; discriminate.
    - constructor; discriminate.
    - destruct (V.eqb_spec v w); constructor; congruence.
  Qed.

  (** Correct copy cells consume precisely the names assigned to the repeated variables. *)
  Lemma run_copies_ok_complete : forall ts seen t names tail,
    Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
      names (run_term_duplicates seen ts) ->
    copies_ok V.eqb t seen ts (names ++ tail) = Some tail.
  Proof.
    induction ts as [|[x|v] rest IH]; intros seen t names tail Hcopies;
      cbn [run_term_duplicates] in Hcopies; cbn [copies_ok].
    - inversion Hcopies; subst. reflexivity.
    - destruct (trie_get x seen) as [u|] eqn:Hseen.
      + inversion Hcopies as [|z x' names' xs [c [Hz Hx]] Hrest]; subst.
        cbn [app]. rewrite Hz, Hx, run_cell_eqb_refl. now apply IH.
      + now apply IH.
    - now apply IH.
  Qed.

  (** A successful term check marks an atom exactly when it encounters a repeated variable. *)
  Lemma run_check_terms_copied : forall ts names pos seen copy inv srcs cols copied
      copy' inv' srcs' cols' copied',
    check_terms V.eqb names ts pos seen copy inv srcs cols copied =
      Some (copy', inv', srcs', cols', copied') ->
    copied' = match run_term_duplicates seen ts with [] => copied | _ :: _ => true end.
  Proof.
    induction ts as [|[x|v] rest IH]; intros names pos seen copy inv srcs cols copied
      copy' inv' srcs' cols' copied' Hcheck; cbn [check_terms] in Hcheck.
    - inversion Hcheck. reflexivity.
    - cbn [run_term_duplicates]. destruct (trie_get x seen) as [u|] eqn:Hseen.
      + specialize (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hcheck).
        destruct (run_term_duplicates seen rest); exact IH.
      + destruct (trie_get x names) as [j|]; [|discriminate Hcheck].
        eapply IH. exact Hcheck.
    - destruct srcs as [|[s|s|[i|w]] srcs]; try discriminate Hcheck.
      destruct cols as [|col cols]; [discriminate Hcheck|].
      destruct col as [|j col]; [discriminate Hcheck|].
      destruct col; [|discriminate Hcheck].
      destruct (V.eqb w v); [|discriminate Hcheck].
      eapply IH. exact Hcheck.
  Qed.

  (** An accepted atom reports whether its term list needs a copy comparison. *)
  Lemma run_check_atom_copied : forall newok names n table f ts copy used count srcs cols
      copy' used' count' srcs' cols' copied,
    check_atom V.eqb newok names n table f ts copy used count srcs cols =
      Some (copy', used', count', srcs', cols', copied) ->
    copied = match run_term_duplicates Empty ts with [] => false | _ :: _ => true end.
  Proof.
    intros newok names n table f ts copy used count srcs cols copy' used' count' srcs'
      cols' copied Hcheck. unfold check_atom in Hcheck.
    destruct srcs as [|src srcs]; [discriminate Hcheck|].
    destruct cols as [|col cols]; [discriminate Hcheck|].
    destruct (source_slot newok src) as [s|]; [|discriminate Hcheck].
    destruct (column_ok n col None); [|discriminate Hcheck].
    destruct (Nat.eqb (length col) (length ts)); [|discriminate Hcheck].
    destruct (check_terms V.eqb names ts 0 Empty copy Empty srcs cols false)
      as [[[[[next inv] remainingSrc] remainingCols] flag]|] eqn:Hterms;
      [|discriminate Hcheck].
    destruct (column_perm inv col used count) as [[[perm seen] total]|];
      [|discriminate Hcheck].
    destruct (slot_matches table f perm s); [|discriminate Hcheck].
    inversion Hcheck; subst. eapply run_check_terms_copied. exact Hterms.
  Qed.

  (** Successful query checking reconstructs the exact forward post list in reverse order. *)
  Lemma run_check_query_post : forall q newok names n table ai copy used count srcs cols post
      count' srcs' cols' post',
    check_query V.eqb newok names n table q ai copy used count srcs cols post =
      Some (count', srcs', cols', post') ->
    post' = rev (run_query_post q ai) ++ post.
  Proof.
    induction q as [|[f args res|p args res] rest IH];
      intros newok names n table ai copy used count srcs cols post count' srcs' cols' post'
      Hcheck; cbn [check_query] in Hcheck.
    - inversion Hcheck; reflexivity.
    - destruct (check_atom V.eqb newok names n table f (args ++ option_list res)
        copy used count srcs cols) as [[[[[[next seen] total] remainingSrc] remainingCols]
        copied]|] eqn:Hatom; [|discriminate Hcheck].
      pose proof (run_check_atom_copied _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hatom) as Hcopied.
      specialize (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcheck).
      cbn [run_query_post]. destruct (run_term_duplicates Empty (args ++ option_list res));
        subst copied; cbn in IH; rewrite IH; [reflexivity|].
      cbn [rev]. rewrite <- app_assoc. reflexivity.
    - specialize (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcheck).
      rewrite IH. cbn [run_query_post rev]. rewrite <- app_assoc. reflexivity.
  Qed.

  (** Trie value lookup is exactly the concrete meaning of a value term. *)
  Lemma run_trie_term_spec : forall (t : ptrie (cell V.t)) term v,
    trie_term t term = Some v <->
    term_value (fun x => trie_get x t) term (Val v).
  Proof.
    intros t [x|w] v; cbn [trie_term term_value].
    - destruct (trie_get x t) as [[i|w]|]; split; intros H; congruence.
    - split; intros H; congruence.
  Qed.

  (** A list of literal value cells has those exact primitive values. *)
  Lemma run_values_map : forall vs : list V.t, values (map Val vs) vs.
  Proof.
    induction vs; cbn [map]; constructor; auto.
  Qed.

  (** Successful trie evaluation supplies every argument term witness. *)
  Lemma run_trie_terms_sound : forall (ts : list (term V.t)) t vs, trie_terms t ts = Some vs ->
    terms_value (fun x => trie_get x t) ts (map Val vs).
  Proof.
    induction ts as [|term rest IH]; intros t vs Heval; cbn [trie_terms] in Heval.
    - inversion Heval. constructor.
    - destruct (trie_term t term) as [v|] eqn:Hterm; [|discriminate Heval].
      destruct (trie_terms t rest) as [tail|] eqn:Htail; [|discriminate Heval].
      inversion Heval; subst vs. cbn [map]. constructor.
      + apply run_trie_term_spec. exact Hterm.
      + now apply IH.
  Qed.

  (** Value term witnesses determine the executable primitive argument list. *)
  Lemma run_trie_terms_complete : forall (ts : list (term V.t)) cs t vs,
    terms_value (fun x => trie_get x t) ts cs -> values cs vs -> trie_terms t ts = Some vs.
  Proof.
    intros ts cs t vs Hterms. revert vs.
    induction Hterms as [|term c rest cells Hterm Hterms IH]; intros vs Hvalues.
    - inversion Hvalues; reflexivity.
    - inversion Hvalues as [|c' v cells' values' Hcell Htail]; subst c' cells' vs c.
      cbn [trie_terms]. rewrite (proj2 (run_trie_term_spec t term v) Hterm), (IH _ Htail).
      reflexivity.
  Qed.

  (** Primitive post checking decides the corresponding concrete query atom. *)
  Lemma run_prim_holds_spec : forall w t p args res,
    prim_holds V.prim V.eqb t p args res = true <->
    atom_holds V.prim w (fun x => trie_get x t) (Prim V.t p args res).
  Proof.
    intros w t p args res. split.
    - unfold prim_holds. destruct (trie_terms t args) as [vs|] eqn:Hargs;
        [|discriminate].
      destruct (V.prim p vs) as [v|] eqn:Hprim; [|discriminate].
      destruct (trie_term t res) as [value|] eqn:Hres; [|discriminate].
      intro Heq. destruct (V.eqb_spec value v) as [->|Hneq]; [|discriminate Heq].
      exists (map Val vs), vs, v. split; [now apply run_trie_terms_sound|].
      split; [apply run_values_map|]. split; [exact Hprim|].
      apply run_trie_term_spec. exact Hres.
    - intros [cells [vs [v [Hargs [Hvalues [Hprim Hres]]]]]].
      unfold prim_holds.
      rewrite (run_trie_terms_complete args cells t vs Hargs Hvalues), Hprim.
      rewrite (proj2 (run_trie_term_spec t res v) Hres). apply planner_value_refl.
  Qed.

  (** The exact query post list succeeds when primitives and assigned copy values agree. *)
  Lemma run_keep_query_complete : forall q whole ai t names extra,
    (forall j a, nth_error q j = Some a -> nth_error whole (ai + j) = Some a) ->
    Forall (fun a => match a with
      | Prim _ p args res => prim_holds V.prim V.eqb t p args res = true
      | Fun _ _ _ _ => True
      end) q ->
    Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
      names (run_query_duplicates q) ->
    keep_post V.prim V.eqb whole t (run_query_post q ai) (names ++ extra) = true.
  Proof.
    induction q as [|a rest IH]; intros whole ai t names extra Hindex Hprims Hcopies.
    - reflexivity.
    - inversion Hprims as [|a' rest' Hhead Htail]; subst a' rest'.
      assert (Hhere : nth_error whole ai = Some a).
      { replace ai with (ai + 0) at 1 by lia. apply Hindex. reflexivity. }
      assert (Hnext : forall j a', nth_error rest j = Some a' ->
          nth_error whole (S ai + j) = Some a').
      { intros j a' Hget. replace (S ai + j) with (ai + S j) by lia.
        apply Hindex. exact Hget. }
      destruct a as [f args res|p args res]; cbn [run_query_duplicates] in Hcopies.
      + apply Forall2_app_inv_r in Hcopies.
        destruct Hcopies as [local [later [Hlocal [Hlater ->]]]].
        cbn [run_query_post].
        destruct (run_term_duplicates Empty (args ++ option_list res)) as [|x xs] eqn:Hdups.
        * inversion Hlocal; subst local. cbn [app].
          eapply IH; eassumption.
        * cbn [keep_post]. rewrite Hhere, <- app_assoc.
          assert (Hconsume : copies_ok V.eqb t Empty (args ++ option_list res)
              (local ++ (later ++ extra)) = Some (later ++ extra)).
          { apply run_copies_ok_complete. now rewrite Hdups. }
          rewrite Hconsume. eapply IH; eassumption.
      + cbn [run_query_post keep_post]. rewrite Hhere, Hhead.
        eapply IH; eassumption.
  Qed.

  (** A correct copy prefix suffices for the complete post filter of a query. *)
  Lemma run_keep_post_complete : forall q t vars,
    Forall (fun a => match a with
      | Prim _ p args res => prim_holds V.prim V.eqb t p args res = true
      | Fun _ _ _ _ => True
      end) q ->
    Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
      (firstn (query_copies q 0) vars) (run_query_duplicates q) ->
    keep_post V.prim V.eqb q t (run_query_post q 0) vars = true.
  Proof.
    intros q t vars Hprim Hcopy.
    pose proof (run_keep_query_complete q q 0 t (firstn (query_copies q 0) vars)
      (skipn (query_copies q 0) vars) (fun j a Hget => Hget) Hprim Hcopy) as Hkeep.
    rewrite firstn_skipn in Hkeep. exact Hkeep.
  Qed.

  (** A successful copy scan consumes exactly a prefix with matching concrete values. *)
  Lemma run_copies_ok_sound : forall ts seen t vars tail,
    copies_ok V.eqb t seen ts vars = Some tail ->
    exists names, vars = names ++ tail /\
      Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
        names (run_term_duplicates seen ts).
  Proof.
    induction ts as [|[x|v] rest IH]; intros seen t vars tail Hcopy;
      cbn [copies_ok] in Hcopy; cbn [run_term_duplicates].
    - inversion Hcopy; subst vars. exists []. split; [reflexivity|constructor].
    - destruct (trie_get x seen) as [u|] eqn:Hseen.
      + destruct vars as [|z vars]; [discriminate Hcopy|].
        destruct (trie_get z t) as [c|] eqn:Hz; [|discriminate Hcopy].
        destruct (trie_get x t) as [d|] eqn:Hx; [|discriminate Hcopy].
        destruct (cell_eqb V.eqb c d) eqn:Heq; [|discriminate Hcopy].
        assert (Hsame : c = d).
        { destruct (run_cell_eqb_spec c d); [assumption|discriminate Heq]. }
        subst d. destruct (IH seen t vars tail Hcopy) as [names [Hvars Hnames]].
        exists (z :: names). split; [cbn [app]; now rewrite Hvars|].
        constructor; [exists c; auto|exact Hnames].
      + eapply IH. exact Hcopy.
    - eapply IH. exact Hcopy.
  Qed.

  (** Successful checking of the exact post list proves its primitive and copy conditions. *)
  Lemma run_keep_query_sound : forall q whole ai t vars,
    (forall j a, nth_error q j = Some a -> nth_error whole (ai + j) = Some a) ->
    keep_post V.prim V.eqb whole t (run_query_post q ai) vars = true ->
    Forall (fun a => match a with
      | Prim _ p args res => prim_holds V.prim V.eqb t p args res = true
      | Fun _ _ _ _ => True
      end) q /\
    exists names extra, vars = names ++ extra /\
      Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
        names (run_query_duplicates q).
  Proof.
    induction q as [|a rest IH]; intros whole ai t vars Hindex Hkeep.
    - split; [constructor|]. exists [], vars. split; [reflexivity|constructor].
    - assert (Hhere : nth_error whole ai = Some a).
      { replace ai with (ai + 0) at 1 by lia. apply Hindex. reflexivity. }
      assert (Hnext : forall j a', nth_error rest j = Some a' ->
          nth_error whole (S ai + j) = Some a').
      { intros j a' Hget. replace (S ai + j) with (ai + S j) by lia.
        apply Hindex. exact Hget. }
      destruct a as [f args res|p args res]; cbn [run_query_post] in Hkeep.
      + destruct (run_term_duplicates Empty (args ++ option_list res)) as [|x xs] eqn:Hdups.
        * destruct (IH whole (S ai) t vars Hnext Hkeep)
            as [Hprim [names [extra [Hvars Hnames]]]].
          split; [constructor; [exact I|exact Hprim]|].
          exists names, extra. split; [exact Hvars|].
          cbn [run_query_duplicates]. rewrite Hdups. exact Hnames.
        * cbn [keep_post] in Hkeep. rewrite Hhere in Hkeep.
          destruct (copies_ok V.eqb t Empty (args ++ option_list res) vars)
            as [later|] eqn:Hcopy; [|discriminate Hkeep].
          destruct (IH whole (S ai) t later Hnext Hkeep)
            as [Hprim [names [extra [Hlater Hnames]]]].
          destruct (run_copies_ok_sound _ _ _ _ _ Hcopy) as [local [Hvars Hlocal]].
          split; [constructor; [exact I|exact Hprim]|].
          exists (local ++ names), extra. split.
          -- rewrite Hvars, Hlater, app_assoc. reflexivity.
          -- cbn [run_query_duplicates]. now apply Forall2_app.
      + cbn [keep_post] in Hkeep. rewrite Hhere in Hkeep.
        destruct (prim_holds V.prim V.eqb t p args res) eqn:Hprim; [|discriminate Hkeep].
        destruct (IH whole (S ai) t vars Hnext Hkeep) as [Htail Hcopies].
        split; [constructor; assumption|exact Hcopies].
  Qed.

  (** The first counted copy names are exactly the successful query's compared copies. *)
  Lemma run_keep_post_sound : forall q t vars,
    keep_post V.prim V.eqb q t (run_query_post q 0) vars = true ->
    Forall (fun a => match a with
      | Prim _ p args res => prim_holds V.prim V.eqb t p args res = true
      | Fun _ _ _ _ => True
      end) q /\
    Forall2 (fun z x => exists c, trie_get z t = Some c /\ trie_get x t = Some c)
      (firstn (query_copies q 0) vars) (run_query_duplicates q).
  Proof.
    intros q t vars Hkeep.
    destruct (run_keep_query_sound q q 0 t vars (fun j a Hget => Hget) Hkeep)
      as [Hprim [names [extra [-> Hcopies]]]].
    split; [exact Hprim|].
    assert (Hlength : length names = length (run_query_duplicates q)).
    { eapply Forall2_length. exact Hcopies. }
    rewrite run_query_duplicates_count, Nat.add_0_r, <- Hlength.
    rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn].
    rewrite app_nil_r. exact Hcopies.
  Qed.

  (** The list equality test accepts only equal lists. *)
  Lemma run_nats_eqb_sound : forall xs ys, nats_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] Hcheck; cbn [nats_eqb] in Hcheck;
      try discriminate; [reflexivity|].
    destruct (Nat.eqb x y) eqn:Hhead; [|discriminate].
    apply Nat.eqb_eq in Hhead. subst y. f_equal. now apply IH.
  Qed.

  (** A successful variable scan starts with every scanned name unbound. *)
  Lemma run_var_table_fresh : forall vars j t names,
    var_table vars j t = Some names ->
    forall x, In x vars -> trie_get x t = None.
  Proof.
    induction vars as [|y vars IH]; intros j t names Hscan x Hin; [contradiction|].
    cbn [var_table] in Hscan.
    destruct (trie_get y t) eqn:Hfirst; [discriminate|].
    destruct Hin as [Heq|Hin]; [subst x; exact Hfirst|].
    pose proof (IH (N.succ j) (PTrieCode.set y j t) names Hscan x Hin) as Hnone.
    destruct (Pos.eq_dec y x) as [Heq|Hneq].
    - subst x. rewrite PTrie.get_set_same in Hnone. discriminate.
    - rewrite PTrie.get_set_other in Hnone by congruence. exact Hnone.
  Qed.

  (** A successful variable scan contains no repeated name. *)
  Lemma run_var_table_nodup : forall vars j t names,
    var_table vars j t = Some names -> NoDup vars.
  Proof.
    induction vars as [|x vars IH]; intros j t names Hscan; [constructor|].
    cbn [var_table] in Hscan. destruct (trie_get x t); [discriminate|].
    constructor.
    - intro Hin. pose proof (run_var_table_fresh vars (N.succ j)
        (PTrieCode.set x j t) names Hscan x Hin) as Hnone.
      rewrite PTrie.get_set_same in Hnone. discriminate.
    - exact (IH (N.succ j) (PTrieCode.set x j t) names Hscan).
  Qed.

  (** Every resulting variable-table entry was present or names its scanned position. *)
  Lemma run_var_table_origin : forall vars j t names,
    var_table vars j t = Some names -> forall x k,
    trie_get x names = Some k -> trie_get x t = Some k \/
      exists pos, nth_error vars pos = Some x /\ k = (j + N.of_nat pos)%N.
  Proof.
    induction vars as [|y vars IH]; intros j t names Hscan x k Hget.
    - cbn [var_table] in Hscan. inversion Hscan; subst names. now left.
    - cbn [var_table] in Hscan. destruct (trie_get y t); [discriminate|].
      destruct (IH (N.succ j) (PTrieCode.set y j t) names Hscan x k Hget)
        as [Hold|[pos [Hnth Hindex]]].
      + destruct (Pos.eq_dec y x) as [Heq|Hneq].
        * subst x. rewrite PTrie.get_set_same in Hold. injection Hold as <-.
          right. exists 0. split; [reflexivity|now rewrite N.add_0_r].
        * left. rewrite PTrie.get_set_other in Hold by congruence. exact Hold.
      + right. exists (S pos). split; [exact Hnth|].
        rewrite Hindex, Nat2N.inj_succ. lia.
  Qed.

  (** A checked variable table gives exactly the positions in its distinct name list. *)
  Lemma run_var_table_spec : forall vars names,
    var_table vars 0 Empty = Some names -> NoDup vars /\
      forall x j, trie_get x names = Some j <-> nth_error vars (N.to_nat j) = Some x.
  Proof.
    intros vars names Hscan.
    pose proof (run_var_table_nodup vars 0 Empty names Hscan) as Hnodup.
    split; [exact Hnodup|].
    destruct (planner_var_table_empty vars Hnodup) as [other [Hother Hlookup]].
    rewrite Hscan in Hother. injection Hother as <-.
    intros x j. split.
    - intro Hget. destruct (run_var_table_origin vars 0 Empty names Hscan x j Hget)
        as [Hempty|[pos [Hnth Hindex]]].
      + rewrite PTrie.get_empty in Hempty. discriminate.
      + rewrite Hindex, N.add_0_l, Nat2N.id. exact Hnth.
    - intro Hnth. specialize (Hlookup (N.to_nat j) x Hnth).
      now rewrite N2Nat.id in Hlookup.
  Qed.

  (** An accepted plan exposes its checked names, columns, count and exact post list. *)
  Lemma run_check_cplan_parts : forall newok table i r c,
    check_cplan V.eqb newok table i r c = true ->
    rule_ix V.t c = i /\ length (var_of V.t c) = nvars (join V.t c) /\
    exists names expected,
      var_table (var_of V.t c) 0 Empty = Some names /\
      layout_ok (query V.t r) (var_of V.t c) (sources V.t c) (cols (join V.t c)) = true /\
      check_query V.eqb newok names (nvars (join V.t c)) table (query V.t r)
        0 0 Empty 0 (sources V.t c) (cols (join V.t c)) [] =
        Some (nat_n (nvars (join V.t c)), [], [], expected) /\
      post V.t c = rev_append expected [].
  Proof.
    intros newok table i [q acts] [ix [n columns] srcs vars post] Hcheck.
    cbn [check_cplan] in Hcheck.
    destruct (N.eqb ix i) eqn:Hindex; [|discriminate].
    destruct (Nat.eqb (length vars) n) eqn:Hlength; [|discriminate].
    destruct (var_table vars 0 Empty) as [names|] eqn:Hnames; [|discriminate].
    destruct (layout_ok q vars srcs columns) eqn:Hlayout; [|discriminate].
    destruct (check_query V.eqb newok names n table q 0 0 Empty 0 srcs columns [])
      as [[[[count remaining_srcs] remaining_cols] expected]|] eqn:Hquery;
      [|discriminate].
    destruct remaining_srcs; [|discriminate]. destruct remaining_cols; [|discriminate].
    destruct (N.eqb count (nat_n n)) eqn:Hcount; [|discriminate].
    apply N.eqb_eq in Hindex. apply Nat.eqb_eq in Hlength.
    apply N.eqb_eq in Hcount. subst count.
    apply run_nats_eqb_sound in Hcheck.
    split; [exact Hindex|]. split; [exact Hlength|]. exists names, expected.
    split; [exact Hnames|]. split; [exact Hlayout|]. split; [exact Hquery|].
    symmetry. exact Hcheck.
  Qed.

  (** A matched slot test contains exactly the requested number and slot contents. *)
  Lemma run_slot_matches_sound : forall table f perm s,
    slot_matches table f perm s = true ->
    trie_get (slot_code f perm) table = Some (s, (f, perm)).
  Proof.
    intros table f perm s Hmatch. unfold slot_matches in Hmatch.
    destruct (trie_get (slot_code f perm) table) as [[s' [f' perm']]|] eqn:Hget;
      [|discriminate].
    destruct (N.eqb s' s) eqn:Hnumber; [|discriminate].
    destruct (Pos.eqb f' f) eqn:Hfunction; [|discriminate].
    apply N.eqb_eq in Hnumber. apply Pos.eqb_eq in Hfunction.
    apply run_nats_eqb_sound in Hmatch. now subst.
  Qed.

  (** Every checked slot-table entry was present or came from its numbered source row. *)
  Lemma run_slot_table_origin : forall sl widths next table checked,
    slot_table widths sl next table = Some checked -> forall key s fp,
    trie_get key checked = Some (s, fp) -> trie_get key table = Some (s, fp) \/
      exists pos, nth_error sl pos = Some fp /\ N.to_nat s = N.to_nat next + pos.
  Proof.
    induction sl as [|[f perm] sl IH]; intros widths next table checked Hscan key s fp Hget.
    - cbn [slot_table] in Hscan. inversion Hscan; subst checked. now left.
    - cbn [slot_table] in Hscan.
      destruct (trie_get f widths) as [width|]; [|discriminate].
      destruct (perm_ok width perm Empty); [|discriminate].
      destruct (trie_get (slot_code f perm) table).
      + destruct (IH widths (N.succ next) table checked Hscan key s fp Hget)
          as [Hold|[pos [Hnth Hindex]]]; [now left|].
        right. exists (S pos). split; [exact Hnth|].
        rewrite N2Nat.inj_succ in Hindex. lia.
      + destruct (IH widths (N.succ next)
          (PTrieCode.set (slot_code f perm) (next, (f, perm)) table)
          checked Hscan key s fp Hget) as [Hold|[pos [Hnth Hindex]]].
        * destruct (Pos.eq_dec (slot_code f perm) key) as [Heq|Hneq].
          -- subst key. rewrite PTrie.get_set_same in Hold.
             injection Hold as <- <-. right. exists 0. split; [reflexivity|lia].
          -- left. rewrite PTrie.get_set_other in Hold by congruence. exact Hold.
        * right. exists (S pos). split; [exact Hnth|].
          rewrite N2Nat.inj_succ in Hindex. lia.
  Qed.

  (** A slot accepted from an empty table names that slot in the original list. *)
  Lemma run_slot_matches_index : forall widths sl table f perm s,
    slot_table widths sl 0 Empty = Some table -> slot_matches table f perm s = true ->
    nth_error sl (N.to_nat s) = Some (f, perm).
  Proof.
    intros widths sl table f perm s Hscan Hmatch.
    pose proof (run_slot_matches_sound table f perm s Hmatch) as Hget.
    destruct (run_slot_table_origin sl widths 0 Empty table Hscan
      (slot_code f perm) s (f, perm) Hget) as [Hempty|[pos [Hnth Hindex]]].
    - rewrite PTrie.get_empty in Hempty. discriminate.
    - cbn in Hindex. now rewrite Hindex.
  Qed.

  (** An accepted column is ordered, bounded and nonempty at its initial check. *)
  Lemma run_column_ok_sound : forall lv n prev,
    column_ok n lv prev = true -> StronglySorted lt lv /\
      Forall (fun j => j < n) lv /\
      match prev with Some k => Forall (fun j => k < j) lv | None => lv <> [] end.
  Proof.
    induction lv as [|j lv IH]; intros n prev Hcheck.
    - destruct prev; cbn [column_ok] in Hcheck; [|discriminate].
      split; [constructor|]. split; constructor.
    - cbn [column_ok] in Hcheck.
      destruct (match prev with Some k => Nat.leb (S k) j | None => true end)
        eqn:Habove; [|discriminate].
      destruct (Nat.leb (S j) n) eqn:Hbound; [|discriminate].
      apply Nat.leb_le in Hbound.
      destruct (IH n (Some j) Hcheck) as [Hsorted [Hbounds Hafter]].
      split; [constructor; assumption|]. split; [constructor; [lia|exact Hbounds]|].
      destruct prev as [k|]; [|discriminate].
      apply Nat.leb_le in Habove. constructor; [lia|].
      apply Forall_forall. intros i Hin.
      apply Forall_forall with (x := i) in Hafter; [lia|exact Hin].
  Qed.

  (** Reading a column preserves its length, exact lookups and used-key cardinality. *)
  Lemma run_column_perm_sound : forall lv inv used count perm used' count',
    column_perm inv lv used count = Some (perm, used', count') ->
    length perm = length lv /\
    Forall2 (fun j pos => trie_get (N.succ_pos (nat_n j)) inv = Some pos) lv perm /\
    (planner_used_count used count -> planner_used_count used' count') /\
    forall j, trie_get (N.succ_pos (nat_n j)) used' = Some tt <->
      trie_get (N.succ_pos (nat_n j)) used = Some tt \/ In j lv.
  Proof.
    induction lv as [|l lv IH]; intros inv used count perm used' count' Hscan.
    - cbn [column_perm] in Hscan. inversion Hscan; subst.
      split; [reflexivity|]. split; [constructor|]. split; [auto|].
      intro j. cbn [In]. tauto.
    - cbn [column_perm] in Hscan.
      destruct (trie_get (N.succ_pos (nat_n l)) inv) as [pos|] eqn:Hpos;
        [|discriminate].
      destruct (column_perm inv lv (PTrieCode.set (N.succ_pos (nat_n l)) tt used)
        (match trie_get (N.succ_pos (nat_n l)) used with
         | Some _ => count | None => N.succ count end))
        as [[[tail used''] count'']|] eqn:Htail; [|discriminate].
      inversion Hscan; subst perm used'' count''.
      destruct (IH inv (PTrieCode.set (N.succ_pos (nat_n l)) tt used)
        (match trie_get (N.succ_pos (nat_n l)) used with
         | Some _ => count | None => N.succ count end) tail used' count' Htail)
        as [Hlength [Hlookups [Hcount Hused]]].
      split; [cbn; now rewrite Hlength|]. split; [constructor; assumption|].
      split.
      + intro Hbefore. apply Hcount. now apply planner_used_count_set.
      + intro j. rewrite Hused, planner_used_set_column. cbn [In]. tauto.
  Qed.

  (** A successful term scan leaves a suffix of its original column list. *)
  Lemma run_check_terms_tail_columns : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') -> incl columns' columns.
  Proof.
    induction ts as [|t ts IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan.
    - cbn [check_terms] in Hscan. inversion Hscan; subst. apply incl_refl.
    - destruct t as [x|v]; cbn [check_terms] in Hscan.
      + destruct (trie_get x seen).
        * eapply IH. exact Hscan.
        * destruct (trie_get x names); [eapply IH; exact Hscan|discriminate].
      + destruct srcs as [|src srcs]; [discriminate|].
        destruct src as [s|s|cell]; try discriminate.
        destruct cell as [i|w]; [discriminate|].
        destruct columns as [|lv columns]; [discriminate|].
        destruct lv as [|l lv]; [discriminate|]. destruct lv; [|discriminate].
        destruct (V.eqb w v); [|discriminate].
        intros col Hin. right. eapply IH; eassumption.
  Qed.

  (** A successful atom check exposes its checked source, terms and inverse permutation. *)
  Lemma run_check_atom_parts : forall newok names n table f ts copy used count srcs columns
      copy' used' count' srcs' columns' copied,
    check_atom V.eqb newok names n table f ts copy used count srcs columns =
      Some (copy', used', count', srcs', columns', copied) ->
    exists src src_tail lv col_tail s inv perm,
      srcs = src :: src_tail /\ columns = lv :: col_tail /\
      source_slot newok src = Some s /\ column_ok n lv None = true /\
      length lv = length ts /\
      check_terms V.eqb names ts 0 Empty copy Empty src_tail col_tail false =
        Some (copy', inv, srcs', columns', copied) /\
      column_perm inv lv used count = Some (perm, used', count') /\
      slot_matches table f perm s = true.
  Proof.
    intros newok names n table f ts copy used count [|src src_tail] [|lv col_tail]
      copy' used' count' srcs' columns' copied Hcheck; try discriminate.
    cbn [check_atom] in Hcheck.
    destruct (source_slot newok src) as [s|] eqn:Hsource; [|discriminate].
    destruct (column_ok n lv None) eqn:Hcolumn; [|discriminate].
    destruct (Nat.eqb (length lv) (length ts)) eqn:Hlength; [|discriminate].
    destruct (check_terms V.eqb names ts 0 Empty copy Empty src_tail col_tail false)
      as [[[[[nextcopy inv] nextsrcs] nextcols] nextcopied]|] eqn:Hterms;
      [|discriminate].
    destruct (column_perm inv lv used count) as [[[perm nextused] nextcount]|]
      eqn:Hperm; [|discriminate].
    destruct (slot_matches table f perm s) eqn:Hslot; [|discriminate].
    inversion Hcheck; subst nextcopy nextused nextcount nextsrcs nextcols nextcopied.
    apply Nat.eqb_eq in Hlength.
    exists src, src_tail, lv, col_tail, s, inv, perm.
    repeat split; assumption || reflexivity.
  Qed.

  (** Query checking records only bounded columns of its input, with an exact used count. *)
  Lemma run_check_query_used : forall q newok names n table ai copy used count srcs columns
      post finalcount srcs' columns' expected,
    check_query V.eqb newok names n table q ai copy used count srcs columns post =
      Some (finalcount, srcs', columns', expected) ->
    planner_used_count used count ->
    (forall j, trie_get (N.succ_pos (nat_n j)) used = Some tt -> j < n) ->
    exists finalused, planner_used_count finalused finalcount /\
      (forall j, trie_get (N.succ_pos (nat_n j)) finalused = Some tt -> j < n) /\
      forall j, trie_get (N.succ_pos (nat_n j)) finalused = Some tt ->
        trie_get (N.succ_pos (nat_n j)) used = Some tt \/
        exists lv, In lv columns /\ In j lv.
  Proof.
    induction q as [|a q IH]; intros newok names n table ai copy used count srcs columns
      post finalcount srcs' columns' expected Hcheck Hcount Hwithin.
    - cbn [check_query] in Hcheck. inversion Hcheck; subst.
      exists used. split; [exact Hcount|]. split; [exact Hwithin|]. intros j Hj. now left.
    - destruct a as [f args res|p args res]; cbn [check_query] in Hcheck.
      + destruct (check_atom V.eqb newok names n table f (args ++ option_list res)
          copy used count srcs columns)
          as [[[[[[nextcopy nextused] nextcount] nextsrcs] nextcols] copied]|]
          eqn:Hatom; [|discriminate].
        destruct (run_check_atom_parts newok names n table f (args ++ option_list res)
          copy used count srcs columns nextcopy nextused nextcount nextsrcs nextcols
          copied Hatom) as [src [src_tail [lv [col_tail [s [inv [perm
          [Hsrcs [Hcols [Hsource [Hcolumn [Hlength [Hterms [Hperm Hslot]]]]]]]]]]]]]].
        subst srcs columns.
        destruct (run_column_ok_sound lv n None Hcolumn) as [_ [Hbounds _]].
        destruct (run_column_perm_sound lv inv used count perm nextused nextcount Hperm)
          as [_ [_ [Hnextcount Hnextused]]].
        assert (Hnextwithin : forall j,
            trie_get (N.succ_pos (nat_n j)) nextused = Some tt -> j < n).
        { intros j Hj. apply Hnextused in Hj. destruct Hj as [Hj|Hin].
          - exact (Hwithin j Hj).
          - now apply Forall_forall with (x := j) in Hbounds. }
        destruct (IH newok names n table (S ai) nextcopy nextused nextcount
          nextsrcs nextcols (if copied then ai :: post else post)
          finalcount srcs' columns' expected Hcheck (Hnextcount Hcount) Hnextwithin)
          as [finalused [Hfinalcount [Hfinalwithin Hfinalcols]]].
        exists finalused. split; [exact Hfinalcount|]. split; [exact Hfinalwithin|].
        intros j Hj. destruct (Hfinalcols j Hj) as [Hj'|[col [Hcol Hin]]].
        * apply Hnextused in Hj'. destruct Hj' as [Hj'|Hin]; [now left|].
          right. exists lv. split; [now left|exact Hin].
        * right. exists col. split; [right|exact Hin].
          eapply run_check_terms_tail_columns; eassumption.
      + eapply IH; eassumption.
  Qed.

  (** An exact count equal to the bounded range's size forces every index to be present. *)
  Lemma run_used_count_full : forall used n,
    planner_used_count used (nat_n n) ->
    (forall j, trie_get (N.succ_pos (nat_n j)) used = Some tt -> j < n) ->
    forall j, j < n -> trie_get (N.succ_pos (nat_n j)) used = Some tt.
  Proof.
    intros used n Hcount Hwithin.
    assert (Hlength : n = length (planner_used_keys used)).
    { unfold planner_used_count in Hcount. rewrite planner_nat_n_spec in Hcount.
      now apply Nat2N.inj in Hcount. }
    assert (Hsubset : incl (planner_used_keys used)
        (map (fun j => N.succ_pos (nat_n j)) (seq 0 n))).
    { intros key Hin. destruct (planner_column_key_surj key) as [j ->].
      apply planner_used_keys_spec in Hin. apply in_map_iff. exists j.
      split; [reflexivity|]. apply in_seq. split; [lia|now apply Hwithin]. }
    assert (Hcover : incl (map (fun j => N.succ_pos (nat_n j)) (seq 0 n))
        (planner_used_keys used)).
    { apply NoDup_length_incl; [apply planner_used_keys_nodup| |exact Hsubset].
      rewrite length_map, length_seq. lia. }
    intros j Hbound. apply planner_used_keys_spec. apply Hcover.
    apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
  Qed.

  (** Constant sources remember the join index at which they supply their cell. *)
  Fixpoint run_literal_entries (srcs : list (source V.t)) (cols : list (list nat))
      : list (nat * cell V.t) :=
    match srcs, cols with
    | Const _ c :: rest, [j] :: tail => (j, c) :: run_literal_entries rest tail
    | _ :: rest, _ :: tail => run_literal_entries rest tail
    | _, _ => []
    end.

  (** Removing a key cannot create an entry and leaves the removed key absent. *)
  Lemma run_remove_some : forall A (t : ptrie A) key other value,
    trie_get other (PTrieCode.remove key t) = Some value ->
    other <> key /\ trie_get other t = Some value.
  Proof.
    intros A t key other value Hget.
    destruct (Pos.eq_dec other key) as [Heq|Hneq].
    - subst other. rewrite PTrie.get_remove_same in Hget. discriminate.
    - split; [exact Hneq|]. rewrite PTrie.get_remove_other in Hget by exact Hneq.
      exact Hget.
  Qed.

  (** The literal guard accepts only distinct indices present in its available-key table. *)
  Lemma run_layout_literals_sound : forall srcs cols allowed,
    layout_literals srcs cols allowed = true ->
    NoDup (map fst (run_literal_entries srcs cols)) /\
    forall j c, In (j, c) (run_literal_entries srcs cols) ->
      trie_get (N.succ_pos (nat_n j)) allowed = Some tt.
  Proof.
    induction srcs as [|src srcs IH]; intros cols allowed Hcheck.
    - destruct cols; cbn [layout_literals] in Hcheck; [|discriminate].
      split; [constructor|]. intros j c Hin. contradiction.
    - destruct cols as [|col cols]; [destruct src; discriminate|].
      destruct src as [s|s|c].
      + exact (IH cols allowed Hcheck).
      + exact (IH cols allowed Hcheck).
      + destruct col as [|j [|k col]]; cbn [layout_literals] in Hcheck;
          try discriminate.
        destruct (trie_get (N.succ_pos (nat_n j)) allowed) as [[]|] eqn:Hallowed;
          [|discriminate].
        destruct (IH cols (PTrieCode.remove (N.succ_pos (nat_n j)) allowed) Hcheck)
          as [Hdistinct Hmembers].
        cbn [run_literal_entries map]. split.
        * constructor; [|exact Hdistinct]. intro Hin.
          apply in_map_iff in Hin as [[k d] [Heq Hin]]. cbn in Heq. subst k.
          pose proof (Hmembers j d Hin) as Hget. rewrite PTrie.get_remove_same in Hget.
          discriminate.
        * intros k d [Heq|Hin].
          -- injection Heq as <- <-. exact Hallowed.
          -- exact (proj2 (run_remove_some unit allowed (N.succ_pos (nat_n j))
               (N.succ_pos (nat_n k)) tt (Hmembers k d Hin))).
  Qed.

  (** The fresh-layout scan certifies its copy prefix and records only fresh later names. *)
  Lemma run_layout_fresh_sound : forall vars bound copies j allowed result,
    layout_fresh bound copies vars j allowed = Some result ->
    copies <= length vars /\ Forall (fun x => (bound < x)%positive) (firstn copies vars) /\
    forall key, trie_get key result = Some tt -> trie_get key allowed = Some tt \/
      exists k x, copies <= k /\ nth_error vars k = Some x /\ (bound < x)%positive /\
        key = N.succ_pos (j + N.of_nat k)%N.
  Proof.
    induction vars as [|x rest IH]; intros bound copies j allowed result Htable.
    - destruct copies; cbn [layout_fresh] in Htable; [|discriminate].
      injection Htable as <-. split; [lia|]. split; [constructor|].
      intros key Hget. left. exact Hget.
    - destruct copies as [|copies]; cbn [layout_fresh] in Htable.
      + destruct (Pos.ltb bound x) eqn:Hfresh.
        * destruct (IH bound 0 (N.succ j) (PTrieCode.set (N.succ_pos j) tt allowed)
            result Htable) as [Hlength [Hprefix Hentries]].
          split; [lia|]. split; [constructor|]. intros key Hget.
          destruct (Hentries key Hget) as [Hold|[k [y [Hcopy [Hnth [Hy Hkey]]]]]].
          -- destruct (Pos.eq_dec key (N.succ_pos j)) as [Heq|Hneq].
             ++ right. exists 0, x. split; [lia|]. split; [reflexivity|].
                split; [now apply Pos.ltb_lt in Hfresh|]. now rewrite N.add_0_r.
             ++ left. rewrite PTrie.get_set_other in Hold by exact Hneq. exact Hold.
          -- right. exists (S k), y. split; [lia|]. split; [exact Hnth|].
             split; [exact Hy|]. rewrite Nat2N.inj_succ. replace (j + N.succ (N.of_nat k))%N
               with (N.succ j + N.of_nat k)%N by lia. exact Hkey.
        * destruct (IH bound 0 (N.succ j) allowed result Htable)
            as [Hlength [Hprefix Hentries]].
          split; [lia|]. split; [constructor|]. intros key Hget.
          destruct (Hentries key Hget) as [Hold|[k [y [Hcopy [Hnth [Hy Hkey]]]]]].
          -- left. exact Hold.
          -- right. exists (S k), y. split; [lia|]. split; [exact Hnth|].
             split; [exact Hy|]. rewrite Nat2N.inj_succ. replace (j + N.succ (N.of_nat k))%N
               with (N.succ j + N.of_nat k)%N by lia. exact Hkey.
      + destruct (Pos.ltb bound x) eqn:Hfresh; [|discriminate].
        destruct (IH bound copies (N.succ j) allowed result Htable)
          as [Hlength [Hprefix Hentries]].
        split; [cbn; lia|]. split.
        * cbn [firstn]. constructor; [now apply Pos.ltb_lt in Hfresh|exact Hprefix].
        * intros key Hget.
          destruct (Hentries key Hget) as [Hold|[k [y [Hcopy [Hnth [Hy Hkey]]]]]].
          -- left. exact Hold.
          -- right. exists (S k), y. split; [lia|]. split; [exact Hnth|].
             split; [exact Hy|]. rewrite Nat2N.inj_succ. replace (j + N.succ (N.of_nat k))%N
               with (N.succ j + N.of_nat k)%N by lia. exact Hkey.
  Qed.

  (** Accepted layouts give fresh copy names and distinct fresh noncopy literal positions. *)
  Lemma run_layout_ok_sound : forall q vars srcs cols,
    layout_ok q vars srcs cols = true ->
    query_copies q 0 <= length vars /\
    Forall (fun x => (query_max q 1%positive < x)%positive)
      (firstn (query_copies q 0) vars) /\
    NoDup (map fst (run_literal_entries srcs cols)) /\
    forall j c, In (j, c) (run_literal_entries srcs cols) -> exists x,
      query_copies q 0 <= j /\ nth_error vars j = Some x /\
      (query_max q 1%positive < x)%positive.
  Proof.
    intros q vars srcs cols Hcheck. unfold layout_ok in Hcheck.
    destruct (layout_fresh (query_max q 1%positive) (query_copies q 0) vars 0 Empty)
      as [allowed|] eqn:Hfresh; [|discriminate].
    destruct (run_layout_fresh_sound vars (query_max q 1%positive) (query_copies q 0)
      0 Empty allowed Hfresh) as [Hlength [Hprefix Hentries]].
    destruct (run_layout_literals_sound srcs cols allowed Hcheck) as [Hdistinct Hliterals].
    split; [exact Hlength|]. split; [exact Hprefix|]. split; [exact Hdistinct|].
    intros j c Hin. destruct (Hentries _ (Hliterals j c Hin)) as [Hempty|Hentry].
    - rewrite PTrie.get_empty in Hempty. discriminate.
    - destruct Hentry as [k [x [Hcopy [Hnth [Hx Hkey]]]]].
      change (N.succ_pos (nat_n j) = N.succ_pos (N.of_nat k)) in Hkey.
      rewrite <- planner_nat_n_spec in Hkey. apply planner_column_key_inj in Hkey.
      subst k. exists x. repeat split; assumption.
  Qed.

  (** Literal guards give one bounded column for each constant source. *)
  Lemma run_layout_literals_columns : forall (srcs : list (source V.t)) cols allowed n,
    layout_literals srcs cols allowed = true ->
    (forall j, trie_get (N.succ_pos (nat_n j)) allowed = Some tt -> j < n) ->
    Forall2 (fun src lv => match src with
      | Const _ _ => exists j, lv = [j] /\ j < n
      | _ => True
      end) srcs cols.
  Proof.
    induction srcs as [|src srcs IH]; intros cols allowed n Hcheck Hbound.
    - destruct cols; [constructor|discriminate].
    - destruct cols as [|col cols]; [destruct src; discriminate|].
      destruct src as [s|s|c].
      + constructor; [exact I|]. eapply IH; eassumption.
      + constructor; [exact I|]. eapply IH; eassumption.
      + destruct col as [|j [|k col]]; cbn [layout_literals] in Hcheck;
          try discriminate.
        destruct (trie_get (N.succ_pos (nat_n j)) allowed) as [[]|] eqn:Hallowed;
          [|discriminate].
        constructor.
        * exists j. split; [reflexivity|]. now apply Hbound.
        * eapply IH; [exact Hcheck|]. intros k Hget. apply Hbound.
          exact (proj2 (run_remove_some unit allowed (N.succ_pos (nat_n j))
            (N.succ_pos (nat_n k)) tt Hget)).
  Qed.

  (** The complete layout guard supplies well-formed constant-source columns. *)
  Lemma run_layout_columns : forall (q : list (atom V.t)) vars srcs cols,
    layout_ok q vars srcs cols = true ->
    Forall2 (fun src lv => match src with
      | Const _ _ => exists j, lv = [j] /\ j < length vars
      | _ => True
      end) srcs cols.
  Proof.
    intros q vars srcs cols Hcheck. unfold layout_ok in Hcheck.
    destruct (layout_fresh (query_max q 1%positive) (query_copies q 0) vars 0 Empty)
      as [allowed|] eqn:Hfresh; [|discriminate].
    apply (run_layout_literals_columns srcs cols allowed (length vars) Hcheck).
    intros j Hget.
    destruct (run_layout_fresh_sound vars (query_max q 1%positive) (query_copies q 0)
      0 Empty allowed Hfresh) as [_ [_ Hentries]].
    destruct (Hentries _ Hget) as [Hempty|[k [x [_ [Hnth [_ Hkey]]]]]].
    - rewrite PTrie.get_empty in Hempty. discriminate.
    - change (N.succ_pos (nat_n j) = N.succ_pos (N.of_nat k)) in Hkey.
      rewrite <- planner_nat_n_spec in Hkey. apply planner_column_key_inj in Hkey. subst k.
      apply nth_error_Some. rewrite Hnth. discriminate.
  Qed.

  (** A source column has valid join shape, a matching index arity and safe constants. *)
  Definition run_source_column (db : D.t) (n : nat) (src : source V.t)
      (lv : list nat) : Prop :=
    lv <> [] /\ StronglySorted lt lv /\ Forall (fun j => j < n) lv /\
    I.wf (length lv) (source_index db src) /\
    match src with Const _ c => exists v, c = Val v | _ => True end.

  (** A checked slot source has the arity of its registered permutation. *)
  Lemma run_source_index_wf : forall db widths sl table newok src s f perm,
    D.wf db -> D.slots db = sl -> slot_table widths sl 0 Empty = Some table ->
    source_slot newok src = Some s -> slot_matches table f perm s = true ->
    I.wf (length perm) (source_index db src).
  Proof.
    intros db widths sl table newok src s f perm Hwf Hslots Htable Hsource Hmatch.
    assert (Hslot : D.slot_of db s = Some (f, perm)).
    { unfold D.slot_of. rewrite Hslots. now apply (run_slot_matches_index widths sl table). }
    destruct src as [s'|s'|c]; cbn [source_slot source_index] in *; try discriminate.
    - injection Hsource as <-. now apply (D.index_wf db s' false f perm).
    - destruct newok; [|discriminate]. injection Hsource as <-.
      now apply (D.index_wf db s' true f perm).
  Qed.

  (** A term scan consumes well-formed singleton value sources and preserves its tail. *)
  Lemma run_check_terms_columns : forall ts db n names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    Forall2 (fun src lv => match src with
      | Const _ _ => exists j, lv = [j] /\ j < n | _ => True end) srcs columns ->
    Forall2 (fun src lv => match src with
      | Const _ _ => exists j, lv = [j] /\ j < n | _ => True end) srcs' columns' /\
    (Forall2 (run_source_column db n) srcs' columns' ->
      Forall2 (run_source_column db n) srcs columns).
  Proof.
    induction ts as [|t ts IH]; intros db n names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan Hlayout.
    - cbn [check_terms] in Hscan. inversion Hscan; subst. split; [exact Hlayout|auto].
    - destruct t as [x|v]; cbn [check_terms] in Hscan.
      + destruct (trie_get x seen).
        * eapply IH; eassumption.
        * destruct (trie_get x names); [eapply IH; eassumption|discriminate].
      + destruct srcs as [|src srcs]; [discriminate|].
        destruct src as [s|s|cell]; try discriminate.
        destruct cell as [i|w]; [discriminate|].
        destruct columns as [|lv columns]; [discriminate|].
        destruct lv as [|l lv]; [discriminate|]. destruct lv; [|discriminate].
        destruct (V.eqb w v); [|discriminate].
        inversion Hlayout as [|src lv src_tail col_tail Hhead Htail]; subst.
        destruct Hhead as [j [Heq Hbound]]. inversion Heq; subst j.
        destruct (IH db n names (S pos) seen copy
          (PTrieCode.set (N.succ_pos (nat_n l)) pos inv) srcs columns copied
          copy' inv' srcs' columns' copied' Hscan Htail) as [Hremaining Hextend].
        split; [exact Hremaining|]. intro Hcolumns. constructor; [|now apply Hextend].
        unfold run_source_column. split; [discriminate|].
        split; [constructor; constructor|].
        split; [constructor; [exact Hbound|constructor]|].
        split.
        * cbn [source_index]. apply I.wf_insert; [apply I.wf_empty|reflexivity].
        * exists w. reflexivity.
  Qed.

  (** Every source consumed by an accepted query has a valid join column. *)
  Lemma run_check_query_columns : forall q db widths sl table newok names n ai copy used
      count srcs columns post finalcount expected,
    D.wf db -> D.slots db = sl -> slot_table widths sl 0 Empty = Some table ->
    check_query V.eqb newok names n table q ai copy used count srcs columns post =
      Some (finalcount, [], [], expected) ->
    Forall2 (fun src lv => match src with
      | Const _ _ => exists j, lv = [j] /\ j < n | _ => True end) srcs columns ->
    Forall2 (run_source_column db n) srcs columns.
  Proof.
    induction q as [|a q IH]; intros db widths sl table newok names n ai copy used
      count srcs columns post finalcount expected Hwf Hslots Htable Hcheck Hlayout.
    - cbn [check_query] in Hcheck. inversion Hcheck; subst. constructor.
    - destruct a as [f args res|p args res]; cbn [check_query] in Hcheck.
      + destruct (check_atom V.eqb newok names n table f (args ++ option_list res)
          copy used count srcs columns)
          as [[[[[[nextcopy nextused] nextcount] nextsrcs] nextcols] copied]|]
          eqn:Hatom; [|discriminate].
        destruct (run_check_atom_parts newok names n table f (args ++ option_list res)
          copy used count srcs columns nextcopy nextused nextcount nextsrcs nextcols
          copied Hatom) as [src [src_tail [lv [col_tail [s [inv [perm
          [Hsrcs [Hcols [Hsource [Hcolumn [Hlength [Hterms [Hperm Hslot]]]]]]]]]]]]]].
        subst srcs columns.
        inversion Hlayout as [|src' lv' src_tail' col_tail' Hhead Htail];
          subst src' lv' src_tail' col_tail'.
        destruct (run_check_terms_columns (args ++ option_list res) db n names 0 Empty
          copy Empty src_tail col_tail false nextcopy inv nextsrcs nextcols copied
          Hterms Htail) as [Hremaining Hextend].
        constructor.
        * destruct (run_column_ok_sound lv n None Hcolumn)
            as [Hsorted [Hbounds Hnonempty]].
          destruct (run_column_perm_sound lv inv used count perm nextused nextcount Hperm)
            as [Hperm_length _].
          unfold run_source_column.
          split; [exact Hnonempty|]. split; [exact Hsorted|]. split; [exact Hbounds|].
          split.
          -- rewrite <- Hperm_length.
             exact (run_source_index_wf db widths sl table newok src s f perm
               Hwf Hslots Htable Hsource Hslot).
          -- destruct src; try exact I. discriminate Hsource.
        * apply Hextend. eapply IH; eassumption.
      + eapply IH; eassumption.
  Qed.

  (** A checked plan supplies valid source columns against a loaded database. *)
  Lemma run_check_cplan_columns : forall p cp db table newok r c,
    D.wf db -> loaded p cp db ->
    slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty =
      Some table ->
    check_cplan V.eqb newok table (rule_ix V.t c) r c = true ->
    Forall2 (run_source_column db (nvars (join V.t c))) (sources V.t c)
      (cols (join V.t c)).
  Proof.
    intros p cp db table newok r c Hwf Hloaded Htable Hcheck.
    destruct (run_check_cplan_parts newok table (rule_ix V.t c) r c Hcheck)
      as [_ [Hlength [names [expected [Hnames [Hlayout [Hquery Hpost]]]]]]].
    pose proof (run_layout_columns (query V.t r) (var_of V.t c) (sources V.t c)
      (cols (join V.t c)) Hlayout) as Hcolumns.
    rewrite Hlength in Hcolumns.
    destruct Hloaded as [_ [Hslots _]].
    eapply run_check_query_columns; eassumption.
  Qed.

  (** An accepted plan meets every well-formedness premise of the join interface. *)
  Lemma run_check_cplan_wf : forall p cp db table newok r c,
    D.wf db -> loaded p cp db ->
    slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty =
      Some table ->
    check_cplan V.eqb newok table (rule_ix V.t c) r c = true ->
    J.wf_plan (join V.t c) (map (source_index db) (sources V.t c)).
  Proof.
    intros p cp db table newok r c Hwf Hloaded Htable Hcheck.
    pose proof (run_check_cplan_columns p cp db table newok r c Hwf Hloaded Htable Hcheck)
      as Hcolumns.
    destruct (run_check_cplan_parts newok table (rule_ix V.t c) r c Hcheck)
      as [_ [Hlength [names [expected [Hnames [Hlayout [Hquery Hpost]]]]]]].
    unfold J.wf_plan. split.
    - rewrite length_map. symmetry. now apply Forall2_length in Hcolumns.
    - split.
      + clear -Hcolumns. induction Hcolumns as [|src lv srcs lvs Hhead Htail IH].
        * constructor.
        * cbn [map]. constructor; [|exact IH].
          destruct Hhead as [Hnonempty [Hsorted [Hbounds [Hindex _]]]].
          repeat split; assumption.
      + destruct (run_check_query_used (query V.t r) newok names (nvars (join V.t c))
          table 0 0 Empty 0 (sources V.t c) (cols (join V.t c)) []
          (nat_n (nvars (join V.t c))) [] [] expected Hquery planner_used_count_empty)
          as [used [Hcount [Hwithin Hcover]]].
        * intros j Hempty. rewrite PTrie.get_empty in Hempty. discriminate.
        * intros j Hbound.
          destruct (Hcover j (run_used_count_full used (nvars (join V.t c))
            Hcount Hwithin j Hbound)) as [Hempty|Hcolumn].
          -- rewrite PTrie.get_empty in Hempty. discriminate.
          -- exact Hcolumn.
  Qed.

  (** Every compiled plan accepted for a loaded database is a well-formed join. *)
  Lemma run_plan_join_wf : forall p cp db c, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    J.wf_plan (join V.t c) (map (source_index db) (sources V.t c)).
  Proof.
    intros p cp db c Hplan Hwf Hloaded Hin.
    destruct (run_plan_member p cp c Hplan Hin)
      as [table [newok [r [Htable [Hrule Hcheck]]]]].
    eapply run_check_cplan_wf; eassumption.
  Qed.

  (** A binding-environment result occurs in the binding's cell list. *)
  Lemma run_binding_env_member : forall vars (b : list (cell V.t)) x c,
    binding_env vars b x = Some c -> In c b.
  Proof.
    induction vars as [|v vars IH]; intros [|d b] x c Hget; try discriminate.
    cbn [binding_env] in Hget. destruct (Pos.eqb x v).
    - injection Hget as <-. now left.
    - right. eapply IH. exact Hget.
  Qed.

  (** A permutation only selects cells already present in its tuple. *)
  Lemma run_permute_member : forall perm u c, In c (D.permute perm u) -> In c u.
  Proof.
    intros perm u c Hin. unfold D.permute in Hin. apply in_flat_map in Hin.
    destruct Hin as [pos [_ Hin]].
    destruct (nth_error u pos) as [d|] eqn:Hnth; cbn [option_list In] in Hin;
      [|contradiction].
    destruct Hin as [Heq|Hin]; [subst d|contradiction]. now apply nth_error_In in Hnth.
  Qed.

  (** A successful projection contains every cell at a selected position. *)
  Lemma run_project_selected : forall lv b u,
    J.project lv b = Some u -> forall j c,
    In j lv -> nth_error b j = Some c -> In c u.
  Proof.
    induction lv as [|l lv IH]; intros b u Hproject j c Hin Hnth; [contradiction|].
    change (match nth_error b l, J.project lv b with
      | Some d, Some ds => Some (d :: ds) | _, _ => None end = Some u) in Hproject.
    destruct (nth_error b l) as [d|] eqn:Hhead; [|discriminate].
    destruct (J.project lv b) as [ds|] eqn:Htail; [|discriminate].
    injection Hproject as <-. destruct Hin as [Heq|Hin].
    - subst j. rewrite Hhead in Hnth. injection Hnth as <-. now left.
    - right. eapply IH; eassumption.
  Qed.

  (** Slot tuples and value constants contain only allocated identifiers. *)
  Lemma run_source_mem_allocated : forall db src u i, D.wf db ->
    (match src with Const _ c => exists v, c = Val v | _ => True end) ->
    I.mem (source_index db src) u -> In (Id i) u -> D.allocated db i.
  Proof.
    intros db [s|s|c] u i Hwf Hsafe Hmem Hin; cbn [source_index] in Hmem.
    - destruct (D.index_all db s false u Hwf Hmem)
        as [f [perm [k [o [Hslot [Hrow Heq]]]]]].
      subst u. eapply D.row_allocated; [exact Hwf|exact Hrow|].
      now apply run_permute_member in Hin.
    - destruct (D.index_all db s true u Hwf Hmem)
        as [f [perm [k [o [Hslot [Hrow Heq]]]]]].
      subst u. eapply D.row_allocated; [exact Hwf|exact Hrow|].
      now apply run_permute_member in Hin.
    - destruct Hsafe as [v ->].
      apply (proj1 (I.mem_insert 1 [Val v] I.empty u (I.wf_empty 1) eq_refl)) in Hmem.
      destruct Hmem as [->|Hempty].
      + cbn [In] in Hin. destruct Hin as [Heq|Hin]; [discriminate|contradiction].
      + exfalso. exact (I.mem_empty u Hempty).
  Qed.

  (** A joined source column allocates every identifier at one of its positions. *)
  Lemma run_source_columns_allocated : forall db n srcs columns b,
    D.wf db -> Forall2 (run_source_column db n) srcs columns ->
    Forall2 (fun lv ix => exists u, J.project lv b = Some u /\ I.mem ix u)
      columns (map (source_index db) srcs) ->
    forall lv j i, In lv columns -> In j lv -> nth_error b j = Some (Id i) ->
      D.allocated db i.
  Proof.
    intros db n srcs columns b Hwf Hcolumns.
    induction Hcolumns as [|src col srcs columns Hhead Htail IH];
      intros Hanswer lv j i Hcol Hj Hnth; [contradiction|].
    cbn [map] in Hanswer.
    inversion Hanswer as [|lv' ix columns' ixs Hsource Hrest]; subst.
    destruct Hcol as [Heq|Hcol].
    - subst lv. destruct Hsource as [u [Hproject Hmem]].
      destruct Hhead as [_ [_ [_ [_ Hsafe]]]].
      eapply run_source_mem_allocated; [exact Hwf|exact Hsafe|exact Hmem|].
      eapply run_project_selected; eassumption.
    - eapply IH; eassumption.
  Qed.

  (** Every identifier bound by an accepted plan is allocated in its loaded database. *)
  Lemma run_plan_bindings_allocated : forall p cp db c b,
    plans_ok p cp -> D.wf db -> loaded p cp db -> In c (all_plans cp) ->
    In b (bindings cp c db) -> env_allocated db (env_of c b).
  Proof.
    intros p cp db c b Hplan Hwf Hloaded Hin Hbinding.
    destruct (run_plan_member p cp c Hplan Hin)
      as [table [newok [r [Htable [Hrule Hcheck]]]]].
    pose proof (run_check_cplan_columns p cp db table newok r c Hwf Hloaded Htable Hcheck)
      as Hcolumns.
    pose proof (run_check_cplan_wf p cp db table newok r c Hwf Hloaded Htable Hcheck)
      as Hjoin.
    destruct (J.run_sound (join V.t c) (map (source_index db) (sources V.t c)) b
      Hjoin Hbinding) as [Hlength Hanswer].
    destruct Hjoin as [_ [_ Hcover]]. intros x i Henv.
    apply run_binding_env_member in Henv.
    apply In_nth_error in Henv. destruct Henv as [j Hnth].
    assert (Hbound : j < nvars (join V.t c)).
    { rewrite <- Hlength. apply nth_error_Some. rewrite Hnth. discriminate. }
    destruct (Hcover j Hbound) as [lv [Hcol Hj]].
    eapply run_source_columns_allocated; eassumption.
  Qed.

  (** The variables collected from a term list are exactly its variable terms. *)
  Lemma run_term_vars_member : forall (ts : list (term V.t)) x,
    In x (flat_map term_vars ts) <-> In (Var x) ts.
  Proof.
    intros ts x. split.
    - intro Hin. apply in_flat_map in Hin. destruct Hin as [t [Hterm Hvar]].
      destruct t as [y|v]; cbn [term_vars In] in Hvar; [|contradiction].
      destruct Hvar as [Heq|Hvar]; [now subst y|contradiction].
    - intro Hin. apply in_flat_map. exists (Var x). split; [exact Hin|now left].
  Qed.

  (** A function atom binds only variables already bound or present among its terms. *)
  Lemma run_binds_atom_scope : forall g g1 g2 args ss out res,
    @binds_list V.t g args ss g1 -> binds_result g1 out res g2 ->
    forall x u, g2 x = Some u -> g x = Some u \/ In (Var x) (args ++ option_list res).
  Proof.
    intros g g1 g2 args ss out res Hargs Hres x u Hbound.
    destruct (run_binds_result_scope g1 out res g2 Hres x u Hbound) as [Hargsbound|Hin].
    - destruct (run_binds_list_scope g args ss g1 Hargs x u Hargsbound) as [Hold|Hin].
      + now left.
      + right. apply in_or_app. now left.
    - right. apply in_or_app. now right.
  Qed.

  (** Every query variable is initially bound or appears in a function atom. *)
  Lemma run_query_vars_fun_context : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' -> forall x,
    In x (flat_map atom_vars q) -> (exists u, g x = Some u) \/
      exists f args res, In (Fun V.t f args res) q /\ In (Var x) (args ++ option_list res).
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hreads
      Hargs Hres Hrest IH|g g1 p args res rest Hargs Hres Hrest IH]; intros x Hin.
    - contradiction.
    - cbn [flat_map] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + cbn [atom_vars] in Hin. rewrite <- flat_map_app in Hin.
        apply run_term_vars_member in Hin. right. exists f, args, res.
        split; [now left|exact Hin].
      + destruct (IH x Hin) as [[u Hbound]|[f' [args' [res' [Hatom Hvar]]]]].
        * destruct (run_binds_atom_scope g g1 g2 args ss out res Hargs Hres x u Hbound)
            as [Hold|Hvar].
          -- left. now exists u.
          -- right. exists f, args, res. split; [now left|exact Hvar].
        * right. exists f', args', res'. split; [now right|exact Hvar].
    - cbn [flat_map] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + left. cbn [atom_vars] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        * apply in_flat_map in Hin. destruct Hin as [t [Hterm Hvar]].
          apply Forall_forall with (x := t) in Hargs; [|exact Hterm].
          exact (run_has_scope g t SVal x Hargs Hvar).
        * exact (run_has_scope g res SVal x Hres Hin).
      + destruct (IH x Hin) as [Hbound|[f [args' [res' [Hatom Hvar]]]]].
        * now left.
        * right. exists f, args', res'. split; [now right|exact Hvar].
  Qed.

  (** Every variable of a well-sorted closed query appears in a function atom. *)
  Lemma run_query_vars_fun : forall sorts kinds q g,
    @query_ok V.t sorts kinds ctx_empty q g -> forall x,
    In x (flat_map atom_vars q) -> exists f args res,
      In (Fun V.t f args res) q /\ In (Var x) (args ++ option_list res).
  Proof.
    intros sorts kinds q g Hquery x Hin.
    destruct (run_query_vars_fun_context sorts kinds ctx_empty q g Hquery x Hin)
      as [[u Hempty]|Hfunction]; [discriminate|exact Hfunction].
  Qed.

  (** Every checked variable term was already seen or has a registered name. *)
  Lemma run_check_terms_names : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') -> forall x,
    In (Var x) ts -> trie_get x seen = Some tt \/ exists j, trie_get x names = Some j.
  Proof.
    induction ts as [|t ts IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan x Hin; [contradiction|].
    destruct t as [y|v]; cbn [check_terms] in Hscan.
    - destruct (trie_get y seen) as [[]|] eqn:Hseen.
      + destruct Hin as [Heq|Hin].
        * injection Heq as <-. now left.
        * eapply IH; eassumption.
      + destruct (trie_get y names) as [j|] eqn:Hname; [|discriminate].
        destruct Hin as [Heq|Hin].
        * injection Heq as <-. right. now exists j.
        * destruct (IH names (S pos) (PTrieCode.set y tt seen) copy
            (PTrieCode.set (N.succ_pos j) pos inv) srcs columns copied
            copy' inv' srcs' columns' copied' Hscan x Hin) as [Hold|Hregistered].
          -- destruct (Pos.eq_dec y x) as [Heq|Hneq].
             ++ subst x. right. now exists j.
             ++ left. rewrite PTrie.get_set_other in Hold by congruence. exact Hold.
          -- now right.
    - destruct Hin as [Heq|Hin]; [discriminate|].
      destruct srcs as [|src srcs]; [discriminate|].
      destruct src as [s|s|cell]; try discriminate.
      destruct cell as [i|w]; [discriminate|].
      destruct columns as [|lv columns]; [discriminate|].
      destruct lv as [|l lv]; [discriminate|]. destruct lv; [|discriminate].
      destruct (V.eqb w v); [eapply IH; eassumption|discriminate].
  Qed.

  (** Every variable of a checked function atom has a registered plan name. *)
  Lemma run_check_query_names : forall q newok names n table ai copy used count srcs columns
      post finalcount srcs' columns' expected,
    check_query V.eqb newok names n table q ai copy used count srcs columns post =
      Some (finalcount, srcs', columns', expected) -> forall f args res x,
    In (Fun V.t f args res) q -> In (Var x) (args ++ option_list res) ->
    exists j, trie_get x names = Some j.
  Proof.
    induction q as [|a q IH]; intros newok names n table ai copy used count srcs columns
      post finalcount srcs' columns' expected Hcheck f args res x Hin Hvar;
      [contradiction|].
    destruct a as [g ts output|p ts result]; cbn [check_query] in Hcheck.
    - destruct (check_atom V.eqb newok names n table g (ts ++ option_list output)
        copy used count srcs columns)
        as [[[[[[nextcopy nextused] nextcount] nextsrcs] nextcols] copied]|]
        eqn:Hatom; [|discriminate].
      destruct Hin as [Heq|Hin].
      + injection Heq as <- <- <-.
        destruct (run_check_atom_parts newok names n table g (ts ++ option_list output)
          copy used count srcs columns nextcopy nextused nextcount nextsrcs nextcols
          copied Hatom) as [src [src_tail [lv [col_tail [s [inv [perm
          [Hsrcs [Hcols [Hsource [Hcolumn [Hlength [Hterms [Hperm Hslot]]]]]]]]]]]]]].
        destruct (run_check_terms_names (ts ++ option_list output) names 0 Empty copy Empty
          src_tail col_tail false nextcopy inv nextsrcs nextcols copied Hterms x Hvar)
          as [Hempty|Hname].
        * rewrite PTrie.get_empty in Hempty. discriminate.
        * exact Hname.
      + eapply IH; eassumption.
    - destruct Hin as [Heq|Hin]; [discriminate|]. eapply IH; eassumption.
  Qed.

  (** Every listed source rule has a corresponding accepted naive plan. *)
  Lemma run_check_rule_naive_member : forall rs table i nv sn r,
    check_rule_plans V.eqb table rs i nv sn = true -> In r rs ->
    exists c k, In c nv /\ nth_error rs k = Some r /\
      N.to_nat (rule_ix V.t c) = N.to_nat i + k /\
      check_cplan V.eqb false table (rule_ix V.t c) r c = true.
  Proof.
    induction rs as [|[q acts] rs IH]; intros table i nv sn r Hcheck Hin;
      [contradiction|].
    destruct nv as [|c nv]; cbn [check_rule_plans] in Hcheck; [discriminate|].
    destruct (check_cplan V.eqb false table i (Rule V.t q acts) c) eqn:Hplan;
      [|discriminate].
    destruct (check_semis V.eqb table i (Rule V.t q acts) (fun_count q) sn)
      as [tail|] eqn:Hsemi; [|discriminate].
    destruct Hin as [<-|Hin].
    - exists c, 0. split; [now left|]. split; [reflexivity|].
      rewrite (run_check_cplan_index false table i (Rule V.t q acts) c Hplan).
      split; [lia|exact Hplan].
    - destruct (IH table (N.succ i) nv tail r Hcheck Hin)
        as [d [k [Hmember [Hnth [Hindex Haccepted]]]]].
      exists d, (S k). split; [now right|]. split; [exact Hnth|].
      split; [rewrite N2Nat.inj_succ in Hindex; lia|exact Haccepted].
  Qed.

  (** A source rule of a checked program is represented by an accepted naive plan. *)
  Lemma run_rule_naive_member : forall p cp r, plans_ok p cp -> In r (rules V.t p) ->
    exists table c, In c (naive V.t cp) /\
      slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty =
        Some table /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      check_cplan V.eqb false table (rule_ix V.t c) r c = true.
  Proof.
    intros [ds rs] [sl nv sn] r Hcheck Hin.
    unfold plans_ok, check_plan in Hcheck. apply andb_true_iff in Hcheck.
    destruct Hcheck as [_ Hshape]. unfold check_shape, check_shape_with in Hshape.
    destruct (slot_table (decl_widths ds Empty) sl 0 Empty)
      as [table|] eqn:Htable; [|discriminate].
    destruct (run_check_rule_naive_member rs table 0 nv sn r Hshape Hin)
      as [c [k [Hmember [Hnth [Hindex Hplan]]]]].
    exists table, c. split; [exact Hmember|]. split; [exact Htable|].
    split; [rewrite Hindex; exact Hnth|exact Hplan].
  Qed.

  (** A total cell reader keeps every environment binding and fills unused names arbitrarily. *)
  Definition run_env_cell (s : Model.env (V := V.t)) (x : positive) : cell V.t :=
    match s x with Some c => c | None => Id 1%positive end.

  (** Distinct literal entries give a partial assignment at their join positions. *)
  Fixpoint run_literal_value (j : nat) (entries : list (nat * cell V.t)) : option (cell V.t) :=
    match entries with
    | [] => None
    | (k, c) :: rest => if Nat.eqb j k then Some c else run_literal_value j rest
    end.

  (** Every value found in the literal assignment comes from its indexed entry. *)
  Lemma run_literal_value_sound : forall entries j c,
    run_literal_value j entries = Some c -> In (j, c) entries.
  Proof.
    induction entries as [|[k d] rest IH]; intros j c Hvalue; cbn [run_literal_value] in Hvalue.
    - discriminate.
    - destruct (Nat.eqb_spec j k) as [Heq|Hneq].
      + subst k. injection Hvalue as <-. now left.
      + right. now apply IH.
  Qed.

  (** A literal entry is found when each index occurs once. *)
  Lemma run_literal_value_complete : forall entries j c,
    NoDup (map fst entries) -> In (j, c) entries -> run_literal_value j entries = Some c.
  Proof.
    induction entries as [|[k d] rest IH]; intros j c Hdistinct Hin; [contradiction|].
    cbn [map] in Hdistinct. inversion Hdistinct as [|? ? Hnot Htail]; subst.
    cbn [run_literal_value]. destruct Hin as [Heq|Hin].
    - injection Heq as <- <-. now rewrite Nat.eqb_refl.
    - destruct (Nat.eqb_spec j k) as [Heq|Hneq].
      + subst k. exfalso. apply Hnot. apply in_map_iff. exists (j, c). split; auto.
      + now apply IH.
  Qed.

  (** Copy indices, literal indices and named real indices receive their matching cells. *)
  Definition run_binding_cell (s : Model.env (V := V.t)) (vars copies : list positive)
      (literals : list (nat * cell V.t)) (j : nat) : cell V.t :=
    if Nat.ltb j (length copies) then run_env_cell s (nth j copies 1%positive)
    else match run_literal_value j literals with
      | Some c => c
      | None => run_env_cell s (nth j vars 1%positive)
      end.

  Definition run_make_binding (s : Model.env (V := V.t)) (vars copies : list positive)
      (literals : list (nat * cell V.t)) : list (cell V.t) :=
    map (run_binding_cell s vars copies literals) (seq 0 (length vars)).

  (** Tabulating the assignment gives its designated cell at every plan index. *)
  Lemma run_make_binding_nth : forall s vars copies literals j,
    j < length vars -> nth_error (run_make_binding s vars copies literals) j =
      Some (run_binding_cell s vars copies literals j).
  Proof.
    intros s vars copies literals j Hbound. unfold run_make_binding.
    rewrite nth_error_map, nth_error_seq.
    assert (Htest : Nat.ltb j (length vars) = true) by (apply Nat.ltb_lt; exact Hbound).
    now rewrite Htest.
  Qed.

  (** A fresh copy prefix cannot contain a real name bounded by the query maximum. *)
  Lemma run_real_after_copies : forall vars bound copies j x,
    Forall (fun y => (bound < y)%positive) (firstn copies vars) ->
    nth_error vars j = Some x -> (x <= bound)%positive -> copies <= j.
  Proof.
    intros vars bound copies j x Hprefix Hnth Hbound.
    destruct (Nat.lt_ge_cases j copies) as [Hbefore|Hafter]; [|exact Hafter].
    assert (Htest : Nat.ltb j copies = true) by (apply Nat.ltb_lt; exact Hbefore).
    assert (Hin : In x (firstn copies vars)).
    { apply nth_error_In with (n := j). now rewrite nth_error_firstn, Htest. }
    apply Forall_forall with (x := x) in Hprefix; [lia|exact Hin].
  Qed.

  (** Every separated layout admits an assignment respecting copies, real names and literals. *)
  Lemma run_make_binding_spec : forall s vars copies literals bound,
    length copies <= length vars ->
    Forall (fun x => (bound < x)%positive) (firstn (length copies) vars) ->
    NoDup (map fst literals) ->
    (forall j c, In (j, c) literals -> exists x,
      length copies <= j /\ nth_error vars j = Some x /\ (bound < x)%positive) ->
    let b := run_make_binding s vars copies literals in
    length b = length vars /\
    (forall j x, nth_error copies j = Some x -> nth_error b j = Some (run_env_cell s x)) /\
    (forall j x, nth_error vars j = Some x -> (x <= bound)%positive ->
      nth_error b j = Some (run_env_cell s x)) /\
    (forall j c, In (j, c) literals -> nth_error b j = Some c).
  Proof.
    intros s vars copies literals bound Hlength Hprefix Hdistinct Hliteral.
    cbn zeta. split.
    - unfold run_make_binding. now rewrite length_map, length_seq.
    - split.
      + intros j x Hnth. assert (Hj : j < length copies).
        { apply nth_error_Some. rewrite Hnth. discriminate. }
        rewrite run_make_binding_nth by lia. unfold run_binding_cell.
        assert (Htest : Nat.ltb j (length copies) = true) by (apply Nat.ltb_lt; exact Hj).
        rewrite Htest. now rewrite (@nth_error_nth positive copies j x 1%positive Hnth).
      + split.
        * intros j x Hnth Hbound. assert (Hj : j < length vars).
          { apply nth_error_Some. rewrite Hnth. discriminate. }
          assert (Hafter : length copies <= j).
          { eapply run_real_after_copies; eassumption. }
          rewrite run_make_binding_nth by exact Hj. unfold run_binding_cell.
          assert (Htest : Nat.ltb j (length copies) = false) by (apply Nat.ltb_ge; exact Hafter).
          rewrite Htest. destruct (run_literal_value j literals) as [c|] eqn:Hvalue.
          -- apply run_literal_value_sound in Hvalue.
             destruct (Hliteral j c Hvalue) as [y [_ [Hy Hfresh]]].
             rewrite Hnth in Hy. injection Hy as <-. lia.
          -- now rewrite (@nth_error_nth positive vars j x 1%positive Hnth).
        * intros j c Hin. destruct (Hliteral j c Hin) as [x [Hafter [Hnth Hfresh]]].
          assert (Hj : j < length vars).
          { apply nth_error_Some. rewrite Hnth. discriminate. }
          rewrite run_make_binding_nth by exact Hj. unfold run_binding_cell.
          assert (Htest : Nat.ltb j (length copies) = false) by (apply Nat.ltb_ge; exact Hafter).
          rewrite Htest, (run_literal_value_complete literals j c Hdistinct Hin). reflexivity.
  Qed.

  (** A source family is satisfied when every projected binding is indexed at that source. *)
  Definition run_sources_satisfied (db : D.t) (b : list (cell V.t))
      (srcs : list (source V.t)) (cols : list (list nat)) : Prop :=
    Forall2 (fun src lv => exists u, J.project lv b = Some u /\
      I.mem (source_index db src) u) srcs cols.

  (** An inverse-table entry points at the same cell in the binding and the atom tuple. *)
  Definition run_inverse_agrees (b tuple : list (cell V.t)) (inv : ptrie nat) : Prop :=
    forall j pos, trie_get (N.succ_pos j) inv = Some pos -> exists c,
      nth_error b (N.to_nat j) = Some c /\ nth_error tuple pos = Some c.

  (** Binary column keys preserve their numeric index. *)
  Lemma run_succ_pos_inj : forall j k, N.succ_pos j = N.succ_pos k -> j = k.
  Proof.
    intros j k Heq. apply N.succ_inj.
    rewrite <- !N.succ_pos_spec. now rewrite Heq.
  Qed.

  (** Adding a correct inverse entry preserves the cell agreement of every entry. *)
  Lemma run_inverse_agrees_set : forall b tuple inv j pos c,
    run_inverse_agrees b tuple inv -> nth_error b (N.to_nat j) = Some c ->
    nth_error tuple pos = Some c ->
    run_inverse_agrees b tuple (PTrieCode.set (N.succ_pos j) pos inv).
  Proof.
    intros b tuple inv j pos c Hinverse Hbinding Htuple k p Hget.
    destruct (Pos.eq_dec (N.succ_pos k) (N.succ_pos j)) as [Heq|Hneq].
    - apply run_succ_pos_inj in Heq. subst k.
      rewrite PTrie.get_set_same in Hget. injection Hget as <-.
      exists c. split; assumption.
    - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply Hinverse.
  Qed.

  (** Pointwise term interpretation records each term at its original tuple position. *)
  Definition run_terms_at (s : Model.env (V := V.t)) (ts : list (term V.t))
      (tuple : list (cell V.t)) (pos : nat) : Prop :=
    forall k t, nth_error ts k = Some t -> exists c,
      nth_error tuple (pos + k) = Some c /\ term_value s t c.

  (** Consuming a term leaves the interpretation of its suffix at the next tuple position. *)
  Lemma run_terms_at_cons : forall s t ts tuple pos,
    run_terms_at s (t :: ts) tuple pos -> exists c,
      nth_error tuple pos = Some c /\ term_value s t c /\
      run_terms_at s ts tuple (S pos).
  Proof.
    intros s t ts tuple pos Hterms.
    destruct (Hterms 0 t eq_refl) as [c [Hnth Hvalue]]. rewrite Nat.add_0_r in Hnth.
    exists c. split; [exact Hnth|]. split; [exact Hvalue|]. intros k u Hterm.
    destruct (Hterms (S k) u Hterm) as [d [Hd Hvalue']]. exists d.
    replace (S pos + k) with (pos + S k) by lia. split; assumption.
  Qed.

  (** A known environment cell is returned by its total reader. *)
  Lemma run_env_cell_some : forall s x c, s x = Some c -> run_env_cell s x = c.
  Proof.
    intros s x c Hvalue. unfold run_env_cell. now rewrite Hvalue.
  Qed.

  (** A binding at a constant column satisfies its singleton source index. *)
  Lemma run_constant_satisfied : forall db b j c,
    nth_error b j = Some c -> exists u, J.project [j] b = Some u /\
      I.mem (source_index db (Const V.t c)) u.
  Proof.
    intros db b j c Hnth. exists [c]. split.
    - cbn [J.project project_cells fold_right]. now rewrite Hnth.
    - unfold source_index. apply (proj2 (I.mem_insert 1 [c] I.empty [c]
        (I.wf_empty 1) eq_refl)). now left.
  Qed.

  (** Checked terms build a correct inverse and consume only satisfied literal sources. *)
  Lemma run_check_terms_answer : forall ts names pos seen copy inv srcs cols copied
      copy' inv' srcs' cols' copied' s b tuple db,
    check_terms V.eqb names ts pos seen copy inv srcs cols copied =
      Some (copy', inv', srcs', cols', copied') ->
    run_terms_at s ts tuple pos ->
    (forall x j, In (Var x) ts -> trie_get x names = Some j ->
      nth_error b (N.to_nat j) = Some (run_env_cell s x)) ->
    (forall k x, nth_error (run_term_duplicates seen ts) k = Some x ->
      nth_error b (N.to_nat copy + k) = Some (run_env_cell s x)) ->
    (forall j c, In (j, c) (run_literal_entries srcs cols) -> nth_error b j = Some c) ->
    run_inverse_agrees b tuple inv ->
    run_inverse_agrees b tuple inv' /\
    copy' = (copy + N.of_nat (length (run_term_duplicates seen ts)))%N /\
    (run_sources_satisfied db b srcs' cols' -> run_sources_satisfied db b srcs cols) /\
    incl (run_literal_entries srcs' cols') (run_literal_entries srcs cols).
  Proof.
    induction ts as [|t rest IH]; intros names pos seen copy inv srcs cols copied
      copy' inv' srcs' cols' copied' s b tuple db Hcheck Hterms Hnames Hcopies Hliterals
      Hinverse; cbn [check_terms] in Hcheck.
    - injection Hcheck as <- <- <- <- <-.
      split; [exact Hinverse|]. split; [now rewrite N.add_0_r|].
      split; [auto|apply incl_refl].
    - destruct (run_terms_at_cons s t rest tuple pos Hterms)
        as [c [Htuple [Hvalue Hrest]]].
      assert (Hnames_rest : forall x j, In (Var x) rest -> trie_get x names = Some j ->
          nth_error b (N.to_nat j) = Some (run_env_cell s x)).
      { intros x j Hin Hget. apply Hnames; [now right|exact Hget]. }
      destruct t as [x|v]; cbn [term_value] in Hvalue.
      + destruct (trie_get x seen) as [u|] eqn:Hseen.
        * cbn [run_term_duplicates] in Hcopies. rewrite Hseen in Hcopies.
          assert (Hcopy : nth_error b (N.to_nat copy) = Some c).
          { pose proof (Hcopies 0 x eq_refl) as Hcell. rewrite Nat.add_0_r in Hcell.
            now rewrite (run_env_cell_some s x c Hvalue) in Hcell. }
          assert (Hcopies_rest : forall k y,
              nth_error (run_term_duplicates seen rest) k = Some y ->
              nth_error b (N.to_nat (N.succ copy) + k) = Some (run_env_cell s y)).
          { intros k y Hnth. rewrite N2Nat.inj_succ.
            replace (S (N.to_nat copy) + k) with (N.to_nat copy + S k) by lia.
            exact (Hcopies (S k) y Hnth). }
          destruct (IH names (S pos) seen (N.succ copy)
            (PTrieCode.set (N.succ_pos copy) pos inv) srcs cols true
            copy' inv' srcs' cols' copied' s b tuple db Hcheck Hrest Hnames_rest
            Hcopies_rest Hliterals (run_inverse_agrees_set b tuple inv copy pos c
              Hinverse Hcopy Htuple)) as [Hinv [Hcount [Hsources Hremain]]].
          split; [exact Hinv|]. split.
          -- cbn [run_term_duplicates]. rewrite Hseen. cbn [length].
             rewrite Nat2N.inj_succ. lia.
          -- split; assumption.
        * destruct (trie_get x names) as [j|] eqn:Hname; [|discriminate].
          assert (Hreal : nth_error b (N.to_nat j) = Some c).
          { pose proof (Hnames x j (or_introl eq_refl) Hname) as Hcell.
            now rewrite (run_env_cell_some s x c Hvalue) in Hcell. }
          cbn [run_term_duplicates] in Hcopies. rewrite Hseen in Hcopies.
          destruct (IH names (S pos) (PTrieCode.set x tt seen) copy
            (PTrieCode.set (N.succ_pos j) pos inv) srcs cols copied
            copy' inv' srcs' cols' copied' s b tuple db Hcheck Hrest Hnames_rest Hcopies
            Hliterals (run_inverse_agrees_set b tuple inv j pos c Hinverse Hreal Htuple))
            as [Hinv [Hcount [Hsources Hremain]]].
          split; [exact Hinv|]. split.
          -- cbn [run_term_duplicates]. rewrite Hseen. exact Hcount.
          -- split; assumption.
      + subst c. destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
        destruct cols as [|col cols]; [discriminate|].
        destruct col as [|j col]; [discriminate|]. destruct col; [|discriminate].
        destruct (V.eqb_spec w v) as [Heq|Hneq]; [subst w|discriminate].
        assert (Hliteral : nth_error b j = Some (Val v)).
        { apply Hliterals. now left. }
        assert (Hliteral_rest : forall k d,
            In (k, d) (run_literal_entries srcs cols) -> nth_error b k = Some d).
        { intros k d Hin. apply Hliterals. now right. }
        assert (Hliteral_index : nth_error b (N.to_nat (nat_n j)) = Some (Val v)).
        { rewrite planner_nat_n_spec, Nat2N.id. exact Hliteral. }
        destruct (IH names (S pos) seen copy
          (PTrieCode.set (N.succ_pos (nat_n j)) pos inv) srcs cols copied
          copy' inv' srcs' cols' copied' s b tuple db Hcheck Hrest Hnames_rest Hcopies
          Hliteral_rest (run_inverse_agrees_set b tuple inv (nat_n j) pos (Val v)
            Hinverse Hliteral_index Htuple)) as [Hinv [Hcount [Hsources Hremain]]].
        split; [exact Hinv|]. split; [exact Hcount|]. split.
        * intro Htail. constructor; [now apply run_constant_satisfied|now apply Hsources].
        * intros entry Hin. right. now apply Hremain.
  Qed.

  (** Reading a checked inverse projects exactly the slot's tuple permutation. *)
  Lemma run_column_perm_answer : forall lv inv used count perm used' count' b tuple,
    column_perm inv lv used count = Some (perm, used', count') ->
    run_inverse_agrees b tuple inv -> J.project lv b = Some (D.permute perm tuple).
  Proof.
    induction lv as [|j lv IH]; intros inv used count perm used' count' b tuple Hcheck Hinv.
    - cbn [column_perm] in Hcheck. injection Hcheck as <- <- <-. reflexivity.
    - cbn [column_perm] in Hcheck.
      destruct (trie_get (N.succ_pos (nat_n j)) inv) as [pos|] eqn:Hposition;
        [|discriminate].
      destruct (column_perm inv lv (PTrieCode.set (N.succ_pos (nat_n j)) tt used)
        (match trie_get (N.succ_pos (nat_n j)) used with
         | Some _ => count | None => N.succ count end))
        as [[[rest used''] count'']|] eqn:Htail; [|discriminate].
      injection Hcheck as <- <- <-.
      destruct (Hinv (nat_n j) pos Hposition) as [c [Hbinding Htuple]].
      rewrite planner_nat_n_spec, Nat2N.id in Hbinding.
      pose proof (IH _ _ _ _ _ _ _ _ Htail Hinv) as Hproject.
      change (match nth_error b j, J.project lv b with
        | Some d, Some ds => Some (d :: ds) | _, _ => None end =
        Some (option_list (nth_error tuple pos) ++ D.permute rest tuple)).
      rewrite Hbinding, Hproject, Htuple. reflexivity.
  Qed.

  (** Relational term interpretation provides every tuple cell at its corresponding position. *)
  Lemma run_terms_value_at : forall s ts cells,
    terms_value s ts cells -> run_terms_at s ts cells 0.
  Proof.
    intros s ts cells Hvalues. unfold terms_value in Hvalues.
    induction Hvalues as [|t c ts cells Hvalue Hvalues IH]; intros k u Hnth.
    - destruct k; discriminate.
    - destruct k as [|k].
      + cbn [nth_error] in Hnth. injection Hnth as <-. exists c. split; [reflexivity|].
        exact Hvalue.
      + destruct (IH k u Hnth) as [d [Hd Hvalue']]. exists d. split; assumption.
  Qed.

  (** A matching function atom interprets all of its argument and output positions together. *)
  Lemma run_fun_match_tuple : forall db s f args res,
    atom_holds V.prim (D.view db) s (Fun V.t f args res) -> exists k o,
      row (D.view db) f k o /\
      terms_value s (args ++ option_list res) (k ++ option_list o).
  Proof.
    intros db s f args res [k [o [Hargs [Hres Hrow]]]]. exists k, o.
    split; [exact Hrow|]. apply Forall2_app; [exact Hargs|].
    destruct res as [t|], o as [c|]; cbn [option_list] in *; try contradiction.
    - constructor; [exact Hres|constructor].
    - constructor.
  Qed.

  (** An accepted naive atom is satisfied by correct real, copy and literal binding cells. *)
  Lemma run_check_atom_answer : forall db names n table f args res copy used count srcs cols
      copy' used' count' srcs' cols' copied s b,
    D.wf db ->
    check_atom V.eqb false names n table f (args ++ option_list res) copy used count srcs cols =
      Some (copy', used', count', srcs', cols', copied) ->
    atom_holds V.prim (D.view db) s (Fun V.t f args res) ->
    (forall x j, In (Var x) (args ++ option_list res) -> trie_get x names = Some j ->
      nth_error b (N.to_nat j) = Some (run_env_cell s x)) ->
    (forall k x, nth_error (run_term_duplicates Empty (args ++ option_list res)) k = Some x ->
      nth_error b (N.to_nat copy + k) = Some (run_env_cell s x)) ->
    (forall j c, In (j, c) (run_literal_entries srcs cols) -> nth_error b j = Some c) ->
    (forall g perm slot, slot_matches table g perm slot = true ->
      D.slot_of db slot = Some (g, perm)) ->
    copy' = (copy + N.of_nat
      (length (run_term_duplicates Empty (args ++ option_list res))))%N /\
    incl (run_literal_entries srcs' cols') (run_literal_entries srcs cols) /\
    (run_sources_satisfied db b srcs' cols' -> run_sources_satisfied db b srcs cols).
  Proof.
    intros db names n table f args res copy used count srcs cols copy' used' count'
      srcs' cols' copied s b Hwf Hcheck Hmatch Hnames Hcopies Hliterals Hslots.
    destruct (run_fun_match_tuple db s f args res Hmatch) as [k [o [Hrow Hvalues]]].
    unfold check_atom in Hcheck.
    destruct srcs as [|src srcs]; [discriminate|].
    destruct cols as [|col cols]; [discriminate|].
    destruct src as [slot|slot|cell]; cbn [source_slot] in Hcheck; try discriminate.
    destruct (column_ok n col None) eqn:Hcol; [|discriminate].
    destruct (Nat.eqb (length col) (length (args ++ option_list res))) eqn:Hlength;
      [|discriminate].
    destruct (check_terms V.eqb names (args ++ option_list res) 0 Empty copy Empty
      srcs cols false) as [[[[[next inv] remainingSrc] remainingCols] flag]|] eqn:Hterms;
      [|discriminate].
    destruct (column_perm inv col used count) as [[[perm seen] total]|] eqn:Hperm;
      [|discriminate].
    destruct (slot_matches table f perm slot) eqn:Hslot; [|discriminate].
    injection Hcheck as <- <- <- <- <- <-.
    assert (Hempty : run_inverse_agrees b (k ++ option_list o) Empty).
    { intros j pos Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    destruct (run_check_terms_answer (args ++ option_list res) names 0 Empty copy Empty
      srcs cols false next inv remainingSrc remainingCols flag s b (k ++ option_list o) db
      Hterms (run_terms_value_at s _ _ Hvalues) Hnames Hcopies Hliterals Hempty)
      as [Hinverse [Hcount [Hsources Hremain]]].
    split; [exact Hcount|]. split; [exact Hremain|]. intro Htail. constructor.
    - exists (D.permute perm (k ++ option_list o)). split.
      + eapply run_column_perm_answer; eassumption.
      + unfold source_index. eapply D.index_all_complete; [exact Hwf| |exact Hrow].
        now apply Hslots.
    - now apply Hsources.
  Qed.

  (** Checking a naive query preserves satisfaction when its binding agrees with each term. *)
  Lemma run_check_query_answer : forall q db names n table ai copy used count srcs cols post
      count' srcs' cols' post' s b,
    D.wf db ->
    check_query V.eqb false names n table q ai copy used count srcs cols post =
      Some (count', srcs', cols', post') ->
    matches V.prim (D.view db) q s ->
    (forall x j, In (Var x) (flat_map atom_terms q) -> trie_get x names = Some j ->
      nth_error b (N.to_nat j) = Some (run_env_cell s x)) ->
    (forall k x, nth_error (run_query_duplicates q) k = Some x ->
      nth_error b (N.to_nat copy + k) = Some (run_env_cell s x)) ->
    (forall j c, In (j, c) (run_literal_entries srcs cols) -> nth_error b j = Some c) ->
    (forall g perm slot, slot_matches table g perm slot = true ->
      D.slot_of db slot = Some (g, perm)) ->
    incl (run_literal_entries srcs' cols') (run_literal_entries srcs cols) /\
    (run_sources_satisfied db b srcs' cols' -> run_sources_satisfied db b srcs cols).
  Proof.
    induction q as [|a rest IH]; intros db names n table ai copy used count srcs cols post
      count' srcs' cols' post' s b Hwf Hcheck Hmatches Hnames Hcopies Hliterals Hslots.
    - cbn [check_query] in Hcheck. injection Hcheck as <- <- <- <-. split; [apply incl_refl|auto].
    - inversion Hmatches as [|a' rest' Hhead Htail]; subst a' rest'.
      assert (Hnames_rest : forall x j, In (Var x) (flat_map atom_terms rest) ->
          trie_get x names = Some j ->
          nth_error b (N.to_nat j) = Some (run_env_cell s x)).
      { intros x j Hin Hget. apply Hnames; [|exact Hget].
        cbn [flat_map]. apply in_or_app. now right. }
      destruct a as [f args res|p args res]; cbn [check_query] in Hcheck.
      + destruct (check_atom V.eqb false names n table f (args ++ option_list res)
          copy used count srcs cols) as [[[[[[next seen] total] remainingSrc]
          remainingCols] copied]|] eqn:Hatom; [|discriminate].
        assert (Hatom_names : forall x j, In (Var x) (args ++ option_list res) ->
            trie_get x names = Some j ->
            nth_error b (N.to_nat j) = Some (run_env_cell s x)).
        { intros x j Hin Hget. apply Hnames; [|exact Hget].
          cbn [flat_map atom_terms]. apply in_or_app. now left. }
        assert (Hatom_copies : forall k x,
            nth_error (run_term_duplicates Empty (args ++ option_list res)) k = Some x ->
            nth_error b (N.to_nat copy + k) = Some (run_env_cell s x)).
        { intros k x Hnth. apply Hcopies. cbn [run_query_duplicates].
          rewrite nth_error_app1; [exact Hnth|].
          apply nth_error_Some. rewrite Hnth. discriminate. }
        destruct (run_check_atom_answer db names n table f args res copy used count srcs cols
          next seen total remainingSrc remainingCols copied s b Hwf Hatom Hhead Hatom_names
          Hatom_copies Hliterals Hslots) as [Hnext [Hremain Hatom_answer]].
        assert (Hcopies_rest : forall k x, nth_error (run_query_duplicates rest) k = Some x ->
            nth_error b (N.to_nat next + k) = Some (run_env_cell s x)).
        { intros k x Hnth. rewrite Hnext, N2Nat.inj_add, Nat2N.id.
          replace (N.to_nat copy + length (run_term_duplicates Empty
              (args ++ option_list res)) + k) with
            (N.to_nat copy + (length (run_term_duplicates Empty
              (args ++ option_list res)) + k)) by lia.
          apply Hcopies. cbn [run_query_duplicates]. rewrite nth_error_app2 by lia.
          replace (length (run_term_duplicates Empty (args ++ option_list res)) + k -
            length (run_term_duplicates Empty (args ++ option_list res))) with k by lia.
          exact Hnth. }
        assert (Hliterals_rest : forall j c,
            In (j, c) (run_literal_entries remainingSrc remainingCols) ->
            nth_error b j = Some c).
        { intros j c Hin. apply Hliterals. now apply Hremain. }
        destruct (IH db names n table (S ai) next seen total remainingSrc remainingCols
          (if copied then ai :: post else post) count' srcs' cols' post' s b Hwf Hcheck
          Htail Hnames_rest Hcopies_rest Hliterals_rest Hslots) as [Hremaining Hanswer].
        split.
        * intros entry Hin. apply Hremain. now apply Hremaining.
        * intro Hfinal. apply Hatom_answer. now apply Hanswer.
      + exact (IH db names n table (S ai) copy used count srcs cols (ai :: post)
          count' srcs' cols' post' s b Hwf Hcheck Htail Hnames_rest Hcopies Hliterals Hslots).
  Qed.

  (** Satisfied source projections are exactly the join answer obligations in source order. *)
  Lemma run_sources_join_answer : forall db b j srcs,
    length b = nvars j -> run_sources_satisfied db b srcs (cols j) ->
    J.answer j (map (source_index db) srcs) b.
  Proof.
    intros db b j srcs Hlength Hsources. split; [exact Hlength|].
    induction Hsources; cbn [map]; [constructor|]. constructor; assumption.
  Qed.

  (** Binding a distinct variable list reads each name at its unique list position. *)
  Lemma run_binding_env_position : forall vars (cells : list (cell V.t)) j x,
    NoDup vars -> nth_error vars j = Some x ->
    binding_env vars cells x = nth_error cells j.
  Proof.
    induction vars as [|y vars IH]; intros cells j x Hdistinct Hnth;
      [destruct j; discriminate|].
    inversion Hdistinct as [|? ? Hnot Htail]; subst.
    destruct cells as [|c cells]; [destruct j; reflexivity|].
    destruct j as [|j].
    - cbn [nth_error] in Hnth. injection Hnth as <-. cbn [binding_env].
      now rewrite Pos.eqb_refl.
    - cbn [binding_env nth_error]. destruct (Pos.eqb_spec x y) as [Heq|Hneq].
      + subst x. exfalso. apply Hnot. now apply nth_error_In with (n := j).
      + now apply IH.
  Qed.

  (** The trie of a binding has exactly the list binding's environment. *)
  Lemma run_binding_trie_get : forall vars (b : list (cell V.t)) x,
    trie_get x (bind_cells vars b Empty) = binding_env vars b x.
  Proof.
    intros vars b x. rewrite bind_cells_get, PTrie.get_empty. reflexivity.
  Qed.

  (** Query variable membership is equivalent to a variable term occurrence. *)
  Lemma run_query_vars_member : forall (q : list (atom V.t)) x,
    In x (flat_map atom_vars q) <-> In (Var x) (flat_map atom_terms q).
  Proof.
    induction q as [|a q IH]; intro x; cbn [flat_map]; [tauto|].
    rewrite !in_app_iff, run_atom_vars_terms, run_term_vars_member, IH. reflexivity.
  Qed.

  (** Every variable occurrence in an interpreted term list has an environment value. *)
  Lemma run_terms_variable_bound : forall (s : Model.env (V := V.t)) ts cs,
    terms_value s ts cs -> forall x, In (Var x) ts -> exists c, s x = Some c.
  Proof.
    intros s ts cs Hterms. induction Hterms as [|t c ts cs Hvalue Hterms IH];
      intros x Hin; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst t. exists c. exact Hvalue.
    - now apply IH.
  Qed.

  (** Every variable of a true query atom has an environment value. *)
  Lemma run_atom_variable_bound : forall w s a,
    atom_holds V.prim w s a -> forall x, In (Var x) (atom_terms a) ->
    exists c, s x = Some c.
  Proof.
    intros w s [f args res|p args res] Hatom x Hin; cbn [atom_terms] in Hin;
      apply in_app_iff in Hin.
    - destruct Hatom as [k [o [Hargs [Hres Hrow]]]]. destruct Hin as [Hin|Hin].
      + eapply run_terms_variable_bound; eassumption.
      + destruct res as [t|]; [|contradiction]. cbn [option_list In] in Hin.
        destruct Hin as [Heq|[]]. subst t. destruct o as [c|]; [|contradiction].
        exists c. exact Hres.
    - destruct Hatom as [k [vs [v [Hargs [Hvalues [Hprim Hres]]]]]].
      destruct Hin as [Hin|Hin].
      + eapply run_terms_variable_bound; eassumption.
      + cbn [In] in Hin. destruct Hin as [Heq|[]]. subst res. exists (Val v). exact Hres.
  Qed.

  (** Every variable of a query match has an environment value. *)
  Lemma run_match_variable_bound : forall w s q,
    matches V.prim w q s -> forall x, In (Var x) (flat_map atom_terms q) ->
    exists c, s x = Some c.
  Proof.
    intros w s q Hmatch x Hin. apply in_flat_map in Hin as [a [Ha Hvar]].
    apply Forall_forall with (x := a) in Hmatch; [|exact Ha].
    eapply run_atom_variable_bound; eassumption.
  Qed.

  (** Duplicate variables are occurrences in the term list that produced them. *)
  Lemma run_term_duplicates_member : forall ts seen x,
    In x (run_term_duplicates seen ts) -> In (Var x) ts.
  Proof.
    induction ts as [|[y|v] ts IH]; intros seen x Hin; cbn [run_term_duplicates] in Hin;
      [contradiction| |].
    - destruct (trie_get y seen).
      + destruct Hin as [<-|Hin]; [now left|]. right. now apply IH with (seen := seen).
      + right. now apply IH with (seen := PTrieCode.set y tt seen).
    - right. now apply IH with (seen := seen).
  Qed.

  (** Every copy names a real variable occurring in its source query. *)
  Lemma run_query_duplicates_member : forall q x,
    In x (run_query_duplicates q) -> In (Var x) (flat_map atom_terms q).
  Proof.
    induction q as [|[f args res|p args res] q IH]; intros x Hin;
      cbn [run_query_duplicates] in Hin; [contradiction| |]; cbn [flat_map atom_terms].
    - apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin].
      + left. now apply run_term_duplicates_member with (seen := Empty).
      + right. now apply IH.
    - apply in_or_app. right. now apply IH.
  Qed.

  (** Correctness at the real-name positions recovers the original matching environment. *)
  Lemma run_binding_agrees : forall w q s vars names b,
    matches V.prim w q s -> var_table vars 0 Empty = Some names ->
    (forall x, In (Var x) (flat_map atom_terms q) -> exists j, trie_get x names = Some j) ->
    (forall j x, nth_error vars j = Some x -> (x <= query_max q 1%positive)%positive ->
      nth_error b j = Some (run_env_cell s x)) ->
    forall x, In (Var x) (flat_map atom_terms q) -> binding_env vars b x = s x.
  Proof.
    intros w q s vars names b Hmatches Htable Hregistered Hreal x Hin.
    destruct (run_var_table_spec vars names Htable) as [Hdistinct Hindices].
    destruct (Hregistered x Hin) as [j Hget]. apply Hindices in Hget.
    rewrite (run_binding_env_position vars b (N.to_nat j) x Hdistinct Hget).
    rewrite (Hreal (N.to_nat j) x Hget (planner_query_max_member q 1%positive x Hin)).
    destruct (run_match_variable_bound w s q Hmatches x Hin) as [c Hvalue].
    rewrite (run_env_cell_some s x c Hvalue), Hvalue. reflexivity.
  Qed.

  (** Corresponding positions determine a list relation when its lengths agree. *)
  Lemma run_Forall2_positions : forall A B (P : A -> B -> Prop) xs ys,
    length xs = length ys ->
    (forall j x y, nth_error xs j = Some x -> nth_error ys j = Some y -> P x y) ->
    Forall2 P xs ys.
  Proof.
    intros A B P xs. induction xs as [|x xs IH]; intros [|y ys] Hlength Hpositions;
      try discriminate; [constructor|].
    constructor.
    - exact (Hpositions 0 x y eq_refl eq_refl).
    - apply IH; [cbn in Hlength; lia|]. intros j a b Ha Hb.
      exact (Hpositions (S j) a b Ha Hb).
  Qed.

  (** Correct copy cells and real cells make every copy-prefix comparison succeed. *)
  Lemma run_binding_copy_cells : forall w q s vars b,
    matches V.prim w q s -> NoDup vars -> query_copies q 0 <= length vars ->
    (forall x, In (Var x) (flat_map atom_terms q) -> binding_env vars b x = s x) ->
    (forall j x, nth_error (run_query_duplicates q) j = Some x ->
      nth_error b j = Some (run_env_cell s x)) ->
    Forall2 (fun z x => exists c,
      trie_get z (bind_cells vars b Empty) = Some c /\
      trie_get x (bind_cells vars b Empty) = Some c)
      (firstn (query_copies q 0) vars) (run_query_duplicates q).
  Proof.
    intros w q s vars b Hmatches Hdistinct Hlength Hagree Hcopies.
    apply run_Forall2_positions.
    - rewrite firstn_length_le by exact Hlength. rewrite run_query_duplicates_count. lia.
    - intros j z x Hz Hx. assert (Hj : j < query_copies q 0).
      { assert (Hbound : j < length (firstn (query_copies q 0) vars)).
        { apply nth_error_Some. rewrite Hz. discriminate. }
        rewrite firstn_length_le in Hbound by exact Hlength. exact Hbound. }
      assert (Htest : Nat.ltb j (query_copies q 0) = true) by (apply Nat.ltb_lt; exact Hj).
      rewrite nth_error_firstn, Htest in Hz.
      assert (Hin : In (Var x) (flat_map atom_terms q)).
      { apply run_query_duplicates_member. now apply nth_error_In with (n := j). }
      destruct (run_match_variable_bound w s q Hmatches x Hin) as [c Hvalue].
      exists c. rewrite !run_binding_trie_get. split.
      + rewrite (run_binding_env_position vars b j z Hdistinct Hz), (Hcopies j x Hx).
        now rewrite (run_env_cell_some s x c Hvalue).
      + rewrite (Hagree x Hin). exact Hvalue.
  Qed.

  (** Changing an environment on absent variables preserves interpreted terms. *)
  Lemma run_terms_value_agree : forall (s : Model.env (V := V.t)) t ts cs,
    terms_value s ts cs ->
    (forall x, In (Var x) ts -> t x = s x) -> terms_value t ts cs.
  Proof.
    intros s t ts cs Hvalues. induction Hvalues as [|term c ts cs Hterm Hvalues IH];
      intro Hagree; [constructor|].
    constructor.
    - destruct term as [x|v]; cbn [term_value] in *; [|exact Hterm].
      rewrite (Hagree x (or_introl eq_refl)). exact Hterm.
    - apply IH. intros x Hin. apply Hagree. now right.
  Qed.

  (** A primitive atom remains true when the trie agrees on all of its variables. *)
  Lemma run_primitive_agree : forall w s t p args res,
    atom_holds V.prim w s (Prim V.t p args res) ->
    (forall x, In (Var x) (args ++ [res]) -> trie_get x t = s x) ->
    prim_holds V.prim V.eqb t p args res = true.
  Proof.
    intros w s t p args res [cs [vs [v [Hargs [Hvalues [Hprim Hres]]]]]] Hagree.
    apply (proj2 (run_prim_holds_spec w t p args res)).
    exists cs, vs, v. split.
    - eapply run_terms_value_agree; [exact Hargs|]. intros x Hin.
      apply Hagree. apply in_or_app. now left.
    - split; [exact Hvalues|]. split; [exact Hprim|].
      destruct res as [x|value]; cbn [term_value] in *; [|exact Hres].
      rewrite (Hagree x); [exact Hres|]. apply in_or_app. right. now left.
  Qed.

  (** A matching environment recovered by a binding passes all primitive post checks. *)
  Lemma run_binding_primitive_checks : forall w q s vars b,
    matches V.prim w q s ->
    (forall x, In (Var x) (flat_map atom_terms q) -> binding_env vars b x = s x) ->
    Forall (fun a => match a with
      | Prim _ p args res => prim_holds V.prim V.eqb (bind_cells vars b Empty) p args res = true
      | Fun _ _ _ _ => True
      end) q.
  Proof.
    intros w q s vars b Hmatches Hagree. apply Forall_forall. intros a Hin.
    apply Forall_forall with (x := a) in Hmatches; [|exact Hin].
    destruct a as [f args res|p args res]; [exact I|].
    eapply run_primitive_agree; [exact Hmatches|]. intros x Hvar.
    rewrite run_binding_trie_get. apply Hagree. apply in_flat_map.
    exists (Prim V.t p args res). split; assumption.
  Qed.

  (** Every accepted layout admits cells for its copies, real variables and literal sources. *)
  Lemma run_layout_assignment : forall q vars srcs columns s,
    layout_ok q vars srcs columns = true ->
    let b := run_make_binding s vars (run_query_duplicates q)
      (run_literal_entries srcs columns) in
    length b = length vars /\
    (forall j x, nth_error (run_query_duplicates q) j = Some x ->
      nth_error b j = Some (run_env_cell s x)) /\
    (forall j x, nth_error vars j = Some x -> (x <= query_max q 1%positive)%positive ->
      nth_error b j = Some (run_env_cell s x)) /\
    (forall j c, In (j, c) (run_literal_entries srcs columns) -> nth_error b j = Some c).
  Proof.
    intros q vars srcs columns s Hlayout.
    destruct (run_layout_ok_sound q vars srcs columns Hlayout)
      as [Hlength [Hprefix [Hdistinct Hliteral]]].
    assert (Hcopies : length (run_query_duplicates q) = query_copies q 0).
    { rewrite run_query_duplicates_count. lia. }
    apply (run_make_binding_spec s vars (run_query_duplicates q)
      (run_literal_entries srcs columns) (query_max q 1%positive)).
    - now rewrite Hcopies.
    - now rewrite Hcopies.
    - exact Hdistinct.
    - intros j c Hin. destruct (Hliteral j c Hin) as [x [Hafter [Hnth Hfresh]]].
      exists x. rewrite Hcopies. repeat split; assumption.
  Qed.

  (** A scan step adds only its current position to the possible inverse-table values. *)
  Lemma run_inverse_origin_step : forall inv result key pos len,
    (forall k value, trie_get k result = Some value ->
      trie_get k (PTrieCode.set key pos inv) = Some value \/
        S pos <= value < S pos + len) ->
    forall k value, trie_get k result = Some value ->
      trie_get k inv = Some value \/ pos <= value < pos + S len.
  Proof.
    intros inv result key pos len Hlater k value Hget.
    destruct (Hlater k value Hget) as [Hset|Hrange]; [|right; lia].
    destruct (Pos.eq_dec k key) as [Heq|Hneq].
    - subst k. rewrite PTrie.get_set_same in Hset. injection Hset as <-. right. lia.
    - left. rewrite PTrie.get_set_other in Hset by exact Hneq. exact Hset.
  Qed.

  (** Every inverse entry comes from the initial table or a position actually scanned. *)
  Lemma run_check_terms_origin : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') -> forall key value,
    trie_get key inv' = Some value ->
      trie_get key inv = Some value \/ pos <= value < pos + length ts.
  Proof.
    induction ts as [|t ts IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan.
    - cbn [check_terms] in Hscan. inversion Hscan; subst. intros key value Hget. now left.
    - destruct t as [x|v]; cbn [check_terms] in Hscan; cbn [length].
      + destruct (trie_get x seen).
        * eapply run_inverse_origin_step. intros key value Hget. eapply IH; eassumption.
        * destruct (trie_get x names); [|discriminate].
          eapply run_inverse_origin_step. intros key value Hget. eapply IH; eassumption.
      + destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
        destruct columns as [|[|j [|k column]] columns]; try discriminate.
        destruct (V.eqb w v); [|discriminate].
        eapply run_inverse_origin_step. intros key value Hget. eapply IH; eassumption.
  Qed.

  (** Scanning later positions cannot create a new entry at an earlier position. *)
  Lemma run_check_terms_before : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') -> forall key value,
    value < pos -> trie_get key inv' = Some value -> trie_get key inv = Some value.
  Proof.
    intros ts names pos seen copy inv srcs columns copied copy' inv' srcs' columns' copied'
      Hscan key value Hbefore Hget.
    destruct (run_check_terms_origin ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan key value Hget) as [Hold|Hrange];
      [exact Hold|lia].
  Qed.

  (** Inserting the current position preserves strict bounds for the next scan position. *)
  Lemma run_inverse_before_set : forall inv key pos,
    (forall k value, trie_get k inv = Some value -> value < pos) ->
    forall k value, trie_get k (PTrieCode.set key pos inv) = Some value -> value < S pos.
  Proof.
    intros inv key pos Hbefore k value Hget.
    destruct (Pos.eq_dec k key) as [Heq|Hneq].
    - subst k. rewrite PTrie.get_set_same in Hget. injection Hget as <-. lia.
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      specialize (Hbefore k value Hget). lia.
  Qed.

  (** Every tuple position is witnessed by an inverse entry reading that binding cell. *)
  Definition run_inverse_positions (b cells : list (cell V.t)) (inv : ptrie nat)
      (pos : nat) : Prop :=
    forall k c, nth_error cells k = Some c -> exists j,
      trie_get (N.succ_pos j) inv = Some (pos + k) /\
      nth_error b (N.to_nat j) = Some c.

  (** Removing a tuple head advances the position witnessed by its inverse. *)
  Lemma run_inverse_positions_tail : forall b c cells inv pos,
    run_inverse_positions b (c :: cells) inv pos ->
    run_inverse_positions b cells inv (S pos).
  Proof.
    intros b c cells inv pos Hpositions k d Hnth.
    destruct (Hpositions (S k) d Hnth) as [j [Hget Hbinding]].
    exists j. split; [|exact Hbinding].
    replace (S pos + k) with (pos + S k) by lia. exact Hget.
  Qed.

  (** A witnessed head position must read the key assigned at that scan step. *)
  Lemma run_check_terms_head_cell : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' idx b c cells,
    check_terms V.eqb names ts (S pos) seen copy
      (PTrieCode.set (N.succ_pos idx) pos inv) srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    (forall key value, trie_get key inv = Some value -> value < pos) ->
    run_inverse_positions b (c :: cells) inv' pos -> nth_error b (N.to_nat idx) = Some c.
  Proof.
    intros ts names pos seen copy inv srcs columns copied copy' inv' srcs' columns' copied'
      idx b c cells Hscan Hbefore Hpositions.
    destruct (Hpositions 0 c eq_refl) as [j [Hget Hbinding]]. rewrite Nat.add_0_r in Hget.
    pose proof (run_check_terms_before ts names (S pos) seen copy
      (PTrieCode.set (N.succ_pos idx) pos inv) srcs columns copied
      copy' inv' srcs' columns' copied' Hscan (N.succ_pos j) pos ltac:(lia) Hget) as Hset.
    assert (Hkey : N.succ_pos j = N.succ_pos idx).
    { destruct (Pos.eq_dec (N.succ_pos j) (N.succ_pos idx)) as [Heq|Hneq]; [exact Heq|].
      rewrite PTrie.get_set_other in Hset by exact Hneq.
      specialize (Hbefore (N.succ_pos j) pos Hset). lia. }
    apply run_succ_pos_inj in Hkey. now subst j.
  Qed.

  (** A successful term scan advances its copy counter by exactly its repeated variables. *)
  Lemma run_check_terms_count : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied',
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    copy' = (copy + N.of_nat (length (run_term_duplicates seen ts)))%N.
  Proof.
    induction ts as [|[x|v] ts IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' Hscan; cbn [check_terms] in Hscan.
    - inversion Hscan; subst. now rewrite N.add_0_r.
    - cbn [run_term_duplicates]. destruct (trie_get x seen) eqn:Hseen.
      + pose proof (IH names (S pos) seen (N.succ copy)
          (PTrieCode.set (N.succ_pos copy) pos inv) srcs columns true
          copy' inv' srcs' columns' copied' Hscan) as Hcount.
        cbn [length]. rewrite Nat2N.inj_succ. lia.
      + destruct (trie_get x names); [eapply IH; exact Hscan|discriminate].
    - destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
      destruct columns as [|[|j [|k column]] columns]; try discriminate.
      destruct (V.eqb w v); [eapply IH; exact Hscan|discriminate].
  Qed.

  (** A distinct bounded permutation of full length visits every position. *)
  Lemma run_perm_covers : forall perm width,
    NoDup perm -> Forall (fun p => p < width) perm -> length perm = width ->
    forall p, p < width -> In p perm.
  Proof.
    intros perm width Hnodup Hfits Hlength.
    assert (Hsubset : incl perm (seq 0 width)).
    { intros p Hin. apply in_seq. split; [lia|].
      now apply Forall_forall with (x := p) in Hfits. }
    assert (Hcover : incl (seq 0 width) perm).
    { apply NoDup_length_incl; [exact Hnodup| |exact Hsubset].
      rewrite length_seq, Hlength. lia. }
    intros p Hbound. apply Hcover. apply in_seq. lia.
  Qed.

  (** Equal full projections pair the selected binding and tuple cells. *)
  Lemma run_project_permute_cells : forall perm lv b cells,
    length lv = length perm -> Forall (fun pos => pos < length cells) perm ->
    J.project lv b = Some (D.permute perm cells) ->
    Forall2 (fun j pos => exists c,
      nth_error b j = Some c /\ nth_error cells pos = Some c) lv perm.
  Proof.
    induction perm as [|pos perm IH]; intros [|j lv] b cells Hlength Hfits Hproject;
      cbn [length] in Hlength; try discriminate; [constructor|].
    inversion Hfits as [|p ps Hbound Htail]; subst p ps.
    assert (Hexists : nth_error cells pos <> None) by (now apply nth_error_Some).
    destruct (nth_error cells pos) as [c|] eqn:Hcell; [|contradiction].
    change (match nth_error b j, J.project lv b with
      | Some d, Some ds => Some (d :: ds) | _, _ => None end =
      Some (option_list (nth_error cells pos) ++ D.permute perm cells)) in Hproject.
    rewrite Hcell in Hproject. cbn [option_list app] in Hproject.
    destruct (nth_error b j) as [d|] eqn:Hbinding; [|discriminate].
    destruct (J.project lv b) as [ds|] eqn:Hrest; [|discriminate].
    injection Hproject as Heq Hds. subst d ds. constructor.
    - exists c. split; assumption.
    - apply IH; [lia|exact Htail|exact Hrest].
  Qed.

  (** A listed permutation position has its recorded inverse key and tuple cell. *)
  Lemma run_column_position : forall lv perm inv (b : list (cell V.t)) cells,
    Forall2 (fun j pos => trie_get (N.succ_pos (nat_n j)) inv = Some pos) lv perm ->
    Forall2 (fun j pos => exists c,
      nth_error b j = Some c /\ nth_error cells pos = Some c) lv perm ->
    forall pos c, In pos perm -> nth_error cells pos = Some c -> exists j,
      trie_get (N.succ_pos (nat_n j)) inv = Some pos /\ nth_error b j = Some c.
  Proof.
    intros lv perm inv b cells Hlookups.
    induction Hlookups as [|j p lv perm Hlookup Htail IH];
      intros Hvalues pos c Hin Hcell; [contradiction|].
    inversion Hvalues as [|j' p' lv' perm' Hvalue Hrest]; subst j' p' lv' perm'.
    destruct Hin as [Heq|Hin].
    - subst pos. destruct Hvalue as [d [Hbinding Hd]]. rewrite Hcell in Hd.
      injection Hd as <-. exists j. split; assumption.
    - eapply IH; eassumption.
  Qed.

  (** A complete checked permutation witnesses every original tuple position in its inverse. *)
  Lemma run_column_inverse_positions : forall lv inv used count perm used' count' b cells,
    column_perm inv lv used count = Some (perm, used', count') -> NoDup perm ->
    length cells = length lv ->
    (forall j pos, trie_get (N.succ_pos j) inv = Some pos -> pos < length cells) ->
    J.project lv b = Some (D.permute perm cells) -> run_inverse_positions b cells inv 0.
  Proof.
    intros lv inv used count perm used' count' b cells Hscan Hnodup Hlength Hrange Hproject.
    destruct (run_column_perm_sound lv inv used count perm used' count' Hscan)
      as [Hperm_length [Hlookups _]].
    assert (Hfits : Forall (fun pos => pos < length cells) perm).
    { clear -Hlookups Hrange.
      induction Hlookups as [|j pos lv perm Hlookup Htail IH].
      - constructor.
      - constructor; [eapply Hrange; exact Hlookup|exact IH]. }
    pose proof (run_project_permute_cells perm lv b cells ltac:(lia) Hfits Hproject)
      as Hvalues.
    intros pos c Hcell.
    assert (Hbound : pos < length cells).
    { apply nth_error_Some. rewrite Hcell. discriminate. }
    assert (Hin : In pos perm).
    { apply (run_perm_covers perm (length cells) Hnodup Hfits); lia. }
    destruct (run_column_position lv perm inv b cells Hlookups Hvalues pos c Hin Hcell)
      as [j [Hget Hbinding]].
    exists (nat_n j). split; [exact Hget|].
    now rewrite planner_nat_n_spec, Nat2N.id.
  Qed.


  (** Binding two argument segments composes their successive contexts. *)
  Lemma run_binds_list_app : forall g (args : list (term V.t)) ss g1,
    binds_list g args ss g1 -> forall rest tt g2,
    binds_list g1 rest tt g2 -> binds_list g (args ++ rest) (ss ++ tt) g2.
  Proof.
    intros g args ss g1 Hargs. induction Hargs as [g|g h g1 t ts ty tys Ht Hts IH];
      intros rest tt g2 Hrest; cbn [app].
    - exact Hrest.
    - econstructor; [exact Ht|now apply IH].
  Qed.

  (** Binding a typed optional result is binding its optional output-cell list. *)
  Lemma run_binds_result_list : forall g out (res : option (term V.t)) g'
      (o : option (cell V.t)),
    binds_result g out res g' -> option_map cell_sort o = out_sort out ->
    binds_list g (option_list res) (map cell_sort (option_list o)) g'.
  Proof.
    intros g out res g' o Hresult Hsort.
    destruct out as [| |m]; destruct res as [t|]; destruct o as [c|];
      cbn [binds_result out_sort option_map] in Hresult, Hsort;
      try contradiction; try discriminate.
    - subst g'. constructor.
    - injection Hsort as Hsort. cbn [option_list map]. rewrite Hsort.
      econstructor; [exact Hresult|constructor].
    - injection Hsort as Hsort. cbn [option_list map]. rewrite Hsort.
      econstructor; [exact Hresult|constructor].
  Qed.

  (** Function arguments and result bind exactly the row's concatenated cell sorts. *)
  Lemma run_binds_atom_row : forall g (args : list (term V.t)) ss g1 out res g2
      (k : list (cell V.t)) o,
    binds_list g args ss g1 -> binds_result g1 out res g2 ->
    map cell_sort k = ss -> option_map cell_sort o = out_sort out ->
    binds_list g (args ++ option_list res) (map cell_sort (k ++ option_list o)) g2.
  Proof.
    intros g args ss g1 out res g2 k o Hargs Hresult Hsort Hout.
    rewrite map_app, Hsort. eapply run_binds_list_app; [exact Hargs|].
    eapply run_binds_result_list; eassumption.
  Qed.

  (** A bound argument list and a row with its declared sorts have equal lengths. *)
  Lemma run_binds_row_length : forall g (args : list (term V.t)) ss g' (k : list (cell V.t)),
    binds_list g args ss g' -> map cell_sort k = ss -> length args = length k.
  Proof.
    intros g args ss g' k Hargs Hsort.
    pose proof (planner_binds_length _ _ _ _ Hargs) as Hlength.
    rewrite <- Hsort, length_map in Hlength. exact Hlength.
  Qed.

  (** A successful constant-source projection fixes its one binding cell. *)
  Lemma run_constant_source_cell : forall db b v j srcs columns,
    run_sources_satisfied db b (Const V.t (Val v) :: srcs) ([j] :: columns) ->
    nth_error b j = Some (Val v) /\ run_sources_satisfied db b srcs columns.
  Proof.
    intros db b v j srcs columns Hsources.
    inversion Hsources as [|src col rest cols Hhead Htail]; subst src col rest cols.
    destruct Hhead as [u [Hproject Hmem]].
    apply (proj1 (I.mem_insert 1 [Val v] I.empty u (I.wf_empty 1) eq_refl)) in Hmem.
    destruct Hmem as [Heq|Hempty]; [subst u|exfalso; exact (I.mem_empty u Hempty)].
    cbn [J.project project_cells fold_right] in Hproject.
    destruct (nth_error b j) as [c|] eqn:Hcell; [|discriminate].
    injection Hproject as <-. split; [reflexivity|exact Htail].
  Qed.

  (** Checked names read existing binding cells through the binding environment. *)
  Lemma run_checked_names_cells : forall vars names (b : list (cell V.t)),
    var_table vars 0 Empty = Some names -> length b = length vars ->
    forall x j, trie_get x names = Some j -> exists c,
      nth_error b (N.to_nat j) = Some c /\ binding_env vars b x = Some c.
  Proof.
    intros vars names b Htable Hlength x j Hget.
    destruct (run_var_table_spec vars names Htable) as [Hnodup Hindices].
    apply Hindices in Hget.
    assert (Hbound : N.to_nat j < length b).
    { rewrite Hlength. apply nth_error_Some. rewrite Hget. discriminate. }
    assert (Hexists : nth_error b (N.to_nat j) <> None) by (now apply nth_error_Some).
    destruct (nth_error b (N.to_nat j)) as [c|] eqn:Hcell; [|contradiction].
    exists c. split; [reflexivity|].
    rewrite (run_binding_env_position vars b (N.to_nat j) x Hnodup Hget). exact Hcell.
  Qed.

  (** A relation on two lists supplies the paired element at any right-hand position. *)
  Lemma run_Forall2_nth_right : forall A B (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys -> forall j y, nth_error ys j = Some y ->
    exists x, nth_error xs j = Some x /\ R x y.
  Proof.
    intros A B R xs ys Hrelated.
    induction Hrelated as [|x y xs ys Hhead Htail IH]; intros [|j] z Hnth;
      try discriminate.
    - injection Hnth as <-. exists x. split; [reflexivity|exact Hhead].
    - apply IH. exact Hnth.
  Qed.

  (** Successful copy comparisons identify each copy-position cell with its variable. *)
  Lemma run_binding_copies_sound : forall vars (b : list (cell V.t)) copies,
    NoDup vars ->
    Forall2 (fun z x => exists c,
      trie_get z (bind_cells vars b Empty) = Some c /\
      trie_get x (bind_cells vars b Empty) = Some c)
      (firstn (length copies) vars) copies ->
    forall j x, nth_error copies j = Some x -> exists c,
      nth_error b j = Some c /\ binding_env vars b x = Some c.
  Proof.
    intros vars b copies Hnodup Hcopies j x Hnth.
    destruct (run_Forall2_nth_right _ _ _ _ _ Hcopies j x Hnth)
      as [z [Hz [c [Hzcell Hxcell]]]].
    assert (Hbound : j < length copies).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    assert (Htest : Nat.ltb j (length copies) = true) by (now apply Nat.ltb_lt).
    rewrite nth_error_firstn, Htest in Hz.
    rewrite !run_binding_trie_get in Hzcell, Hxcell.
    exists c. split; [|exact Hxcell].
    rewrite (run_binding_env_position vars b j z Hnodup Hz) in Hzcell. exact Hzcell.
  Qed.

  (** Complete inverse positions and checked copies interpret every scanned term. *)
  Lemma run_check_terms_values : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' s b cells db,
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    length ts = length cells ->
    (forall key value, trie_get key inv = Some value -> value < pos) ->
    run_inverse_positions b cells inv' pos ->
    (forall x j, trie_get x names = Some j -> exists c,
      nth_error b (N.to_nat j) = Some c /\ s x = Some c) ->
    (forall k x, nth_error (run_term_duplicates seen ts) k = Some x -> exists c,
      nth_error b (N.to_nat copy + k) = Some c /\ s x = Some c) ->
    run_sources_satisfied db b srcs columns ->
    terms_value s ts cells /\ run_sources_satisfied db b srcs' columns'.
  Proof.
    induction ts as [|t ts IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' s b cells db Hscan Hlength Hbefore Hpositions
      Hnames Hcopies Hsources.
    - destruct cells; [|discriminate]. cbn [check_terms] in Hscan.
      inversion Hscan; subst. split; [constructor|exact Hsources].
    - destruct cells as [|c cells]; [discriminate|].
      assert (Hrest_length : length ts = length cells) by (cbn in Hlength; lia).
      pose proof (run_inverse_positions_tail b c cells inv' pos Hpositions) as Hrest_positions.
      destruct t as [x|v]; cbn [check_terms] in Hscan.
      + destruct (trie_get x seen) eqn:Hseen.
        * pose proof (run_check_terms_head_cell ts names pos seen (N.succ copy) inv
            srcs columns true copy' inv' srcs' columns' copied' copy b c cells
            Hscan Hbefore Hpositions) as Hcell.
          cbn [run_term_duplicates] in Hcopies. rewrite Hseen in Hcopies.
          destruct (Hcopies 0 x eq_refl) as [d [Hd Hvalue]]. rewrite Nat.add_0_r in Hd.
          rewrite Hcell in Hd. injection Hd as <-.
          assert (Hrest_copies : forall k y,
              nth_error (run_term_duplicates seen ts) k = Some y -> exists d,
              nth_error b (N.to_nat (N.succ copy) + k) = Some d /\ s y = Some d).
          { intros k y Hnth. rewrite N2Nat.inj_succ.
            replace (S (N.to_nat copy) + k) with (N.to_nat copy + S k) by lia.
            exact (Hcopies (S k) y Hnth). }
          destruct (IH names (S pos) seen (N.succ copy)
            (PTrieCode.set (N.succ_pos copy) pos inv) srcs columns true
            copy' inv' srcs' columns' copied' s b cells db Hscan Hrest_length
            (run_inverse_before_set inv (N.succ_pos copy) pos Hbefore)
            Hrest_positions Hnames Hrest_copies Hsources) as [Hvalues Hremaining].
          split; [constructor; [exact Hvalue|exact Hvalues]|exact Hremaining].
        * destruct (trie_get x names) as [j|] eqn:Hname; [|discriminate].
          pose proof (run_check_terms_head_cell ts names pos (PTrieCode.set x tt seen)
            copy inv srcs columns copied copy' inv' srcs' columns' copied' j b c cells
            Hscan Hbefore Hpositions) as Hcell.
          destruct (Hnames x j Hname) as [d [Hd Hvalue]]. rewrite Hcell in Hd.
          injection Hd as <-. cbn [run_term_duplicates] in Hcopies. rewrite Hseen in Hcopies.
          destruct (IH names (S pos) (PTrieCode.set x tt seen) copy
            (PTrieCode.set (N.succ_pos j) pos inv) srcs columns copied
            copy' inv' srcs' columns' copied' s b cells db Hscan Hrest_length
            (run_inverse_before_set inv (N.succ_pos j) pos Hbefore)
            Hrest_positions Hnames Hcopies Hsources) as [Hvalues Hremaining].
          split; [constructor; [exact Hvalue|exact Hvalues]|exact Hremaining].
      + destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
        destruct columns as [|[|j [|k column]] columns]; try discriminate.
        destruct (V.eqb_spec w v) as [Heq|Hneq]; [subst w|discriminate].
        pose proof (run_check_terms_head_cell ts names pos seen copy inv srcs columns
          copied copy' inv' srcs' columns' copied' (nat_n j) b c cells
          Hscan Hbefore Hpositions) as Hcell.
        rewrite planner_nat_n_spec, Nat2N.id in Hcell.
        destruct (run_constant_source_cell db b v j srcs columns Hsources)
          as [Hliteral Htail].
        rewrite Hliteral in Hcell. injection Hcell as <-.
        destruct (IH names (S pos) seen copy
          (PTrieCode.set (N.succ_pos (nat_n j)) pos inv) srcs columns copied
          copy' inv' srcs' columns' copied' s b cells db Hscan Hrest_length
          (run_inverse_before_set inv (N.succ_pos (nat_n j)) pos Hbefore)
          Hrest_positions Hnames Hcopies Htail) as [Hvalues Hremaining].
        split; [constructor; [reflexivity|exact Hvalues]|exact Hremaining].
  Qed.


  (** Matching a slot from a successful table gives a distinct permutation. *)
  Lemma run_slot_matches_nodup : forall widths sl table f perm slot,
    slot_table widths sl 0 Empty = Some table -> slot_matches table f perm slot = true ->
    NoDup perm.
  Proof.
    intros widths sl table f perm slot Htable Hmatch.
    pose proof (run_slot_matches_index widths sl table f perm slot Htable Hmatch) as Hnth.
    apply nth_error_In in Hnth.
    destruct (slot_table_member sl widths 0 Empty table f perm Htable Hnth)
      as [width [_ Hperm]].
    exact (proj1 (perm_ok_sound perm width Empty Hperm)).
  Qed.

  (** An indexed tuple at a known slot comes from a row of exactly that slot's function. *)
  Lemma run_index_row : forall db slot new f perm tuple,
    D.wf db -> D.slot_of db slot = Some (f, perm) ->
    I.mem (D.index slot new db) tuple -> exists k o,
      row (D.view db) f k o /\ tuple = D.permute perm (k ++ option_list o).
  Proof.
    intros db slot new f perm tuple Hwf Hslot Hmem.
    destruct (D.index_all db slot new tuple Hwf Hmem)
      as [g [other [k [o [Hfound [Hrow Htuple]]]]]].
    rewrite Hslot in Hfound. injection Hfound as <- <-. exists k, o. split; assumption.
  Qed.

  (** An accepted slot source returns a row projected through its checked permutation. *)
  Lemma run_source_row : forall db widths sl table newok src slot f perm tuple,
    D.wf db -> D.slots db = sl -> slot_table widths sl 0 Empty = Some table ->
    source_slot newok src = Some slot -> slot_matches table f perm slot = true ->
    I.mem (source_index db src) tuple -> exists k o,
      row (D.view db) f k o /\ tuple = D.permute perm (k ++ option_list o).
  Proof.
    intros db widths sl table newok src slot f perm tuple Hwf Hslots Htable Hsource Hmatch
      Hmem.
    assert (Hslot : D.slot_of db slot = Some (f, perm)).
    { unfold D.slot_of. rewrite Hslots.
      exact (run_slot_matches_index widths sl table f perm slot Htable Hmatch). }
    destruct src as [s|s|c]; cbn [source_slot source_index] in *; try discriminate.
    - injection Hsource as <-. eapply run_index_row; eassumption.
    - destruct newok; [|discriminate]. injection Hsource as <-.
      eapply run_index_row; eassumption.
  Qed.

  (** A loaded row has precisely the argument and output sorts selected by its program. *)
  Lemma run_loaded_row_sorts : forall p cp db f ss kindout k o,
    loaded p cp db -> program_sorts p f = Some ss -> program_kind p f = Some kindout ->
    row (D.view db) f k o -> map cell_sort k = ss /\ option_map cell_sort o = out_sort kindout.
  Proof.
    intros p cp db f ss kindout k o [Hkinds [_ Hsorted]] Hsort Hkind Hrow.
    destruct (Hsorted f k o Hrow) as [out [Hargs [Hout Hresult]]].
    rewrite Hkinds, Hkind in Hout. injection Hout as <-.
    split; [congruence|exact Hresult].
  Qed.

  (** The typing of a function atom binds exactly the cells and sorts of any loaded row. *)
  Lemma run_atom_row_bindings : forall p cp db f (args : list (term V.t)) res
      g g1 g2 ss kindout k o,
    loaded p cp db -> program_sorts p f = Some ss -> program_kind p f = Some kindout ->
    binds_list g args ss g1 -> binds_result g1 kindout res g2 -> row (D.view db) f k o ->
    binds_list g (args ++ option_list res) (map cell_sort (k ++ option_list o)) g2 /\
    length args = length k /\ length (args ++ option_list res) = length (k ++ option_list o).
  Proof.
    intros p cp db f args res g g1 g2 ss kindout k o Hloaded Hsort Hkind Hargs Hres Hrow.
    destruct (run_loaded_row_sorts p cp db f ss kindout k o Hloaded Hsort Hkind Hrow)
      as [Harg_sorts Hout_sort].
    pose proof (run_binds_atom_row g args ss g1 kindout res g2 k o Hargs Hres
      Harg_sorts Hout_sort) as Hbinds.
    split; [exact Hbinds|]. split.
    - exact (run_binds_row_length g args ss g1 k Hargs Harg_sorts).
    - pose proof (planner_binds_length _ _ _ _ Hbinds) as Hlength.
      now rewrite length_map in Hlength.
  Qed.

  (** An accepted atom exposes its row and witnesses every term's original tuple position. *)
  Lemma run_check_atom_tuple : forall db widths sl table newok names n f ts copy used count
      srcs columns copy' used' count' srcs' columns' copied b,
    D.wf db -> D.slots db = sl -> slot_table widths sl 0 Empty = Some table ->
    check_atom V.eqb newok names n table f ts copy used count srcs columns =
      Some (copy', used', count', srcs', columns', copied) ->
    run_sources_satisfied db b srcs columns ->
    (forall k o, row (D.view db) f k o -> length (k ++ option_list o) = length ts) ->
    exists k o inv before_srcs before_cols,
      row (D.view db) f k o /\
      check_terms V.eqb names ts 0 Empty copy Empty before_srcs before_cols false =
        Some (copy', inv, srcs', columns', copied) /\
      run_inverse_positions b (k ++ option_list o) inv 0 /\
      length ts = length (k ++ option_list o) /\
      run_sources_satisfied db b before_srcs before_cols.
  Proof.
    intros db widths sl table newok names n f ts copy used count srcs columns copy' used'
      count' srcs' columns' copied b Hwf Hslots Htable Hcheck Hsources Hwidth.
    destruct (run_check_atom_parts newok names n table f ts copy used count srcs columns
      copy' used' count' srcs' columns' copied Hcheck)
      as [src [src_tail [lv [col_tail [slot [inv [perm
        [Hsrcs [Hcols [Hsource [Hcolumn [Hlength [Hterms [Hperm Hmatch]]]]]]]]]]]]]].
    subst srcs columns.
    inversion Hsources as [|src' lv' src_tail' col_tail' Hhead Htail];
      subst src' lv' src_tail' col_tail'.
    destruct Hhead as [tuple [Hproject Hmem]].
    destruct (run_source_row db widths sl table newok src slot f perm tuple Hwf Hslots
      Htable Hsource Hmatch Hmem) as [k [o [Hrow Htuple]]].
    subst tuple.
    pose proof (Hwidth k o Hrow) as Hrow_length.
    assert (Hrange : forall j pos,
        trie_get (N.succ_pos j) inv = Some pos -> pos < length (k ++ option_list o)).
    { intros j pos Hget.
      destruct (run_check_terms_origin ts names 0 Empty copy Empty src_tail col_tail false
        copy' inv srcs' columns' copied Hterms (N.succ_pos j) pos Hget)
        as [Hempty|Hbound].
      - rewrite PTrie.get_empty in Hempty. discriminate.
      - rewrite Hrow_length. lia. }
    exists k, o, inv, src_tail, col_tail. split; [exact Hrow|]. split; [exact Hterms|].
    split.
    - eapply run_column_inverse_positions; [exact Hperm| |lia|exact Hrange|exact Hproject].
      exact (run_slot_matches_nodup widths sl table f perm slot Htable Hmatch).
    - split; [symmetry; exact Hrow_length|exact Htail].
  Qed.


  (** Binding a term preserves every previously bound context entry. *)
  Lemma run_binds_preserves : forall g (term : term V.t) ty g',
    binds g term ty g' -> forall x other, g x = Some other -> g' x = Some other.
  Proof.
    intros g term ty g' Hbind. destruct Hbind as [y ty Hget|y ty Hnone|v];
      intros x other Hold; try exact Hold.
    unfold ctx_set. destruct (Pos.eqb_spec y x) as [Heq|Hneq]; [subst x; congruence|].
    exact Hold.
  Qed.

  (** A bound variable is present in the resulting context at the requested sort. *)
  Lemma run_binds_var_bound : forall g x ty g',
    @binds V.t g (Var x) ty g' -> g' x = Some ty.
  Proof.
    intros g x ty g' Hbind. inversion Hbind; subst.
    - assumption.
    - unfold ctx_set. now rewrite Pos.eqb_refl.
  Qed.

  (** A term binding keeps an already sorted environment when its new cell has that sort. *)
  Lemma run_binds_env_value : forall g (term : term V.t) ty g' s c,
    binds g term ty g' -> env_sorted g s -> term_value s term c -> cell_sort c = ty ->
    env_sorted g' s.
  Proof.
    intros g term ty g' s c Hbind Henv Hvalue Hsort.
    destruct Hbind as [x ty Hget|x ty Hnone|v]; try exact Henv.
    intros y other Hctx. unfold ctx_set in Hctx.
    destruct (Pos.eqb_spec x y) as [Heq|Hneq].
    - subst y. injection Hctx as <-. exists c. split; assumption.
    - now apply Henv.
  Qed.

  (** A repeated variable cannot allocate a new context entry. *)
  Lemma run_binds_env_existing : forall g x ty g' (s : Model.env (V := V.t)),
    @binds V.t g (Var x) ty g' -> (exists other, g x = Some other) -> env_sorted g s ->
    env_sorted g' s.
  Proof.
    intros g x ty g' s Hbind [other Hbound] Henv. inversion Hbind; subst.
    - exact Henv.
    - congruence.
  Qed.

  (** A complete checked inverse gives a sorted environment for all newly bound term names. *)
  Lemma run_check_terms_sorted : forall ts cells g g' names pos seen copy inv srcs columns
      copied copy' inv' srcs' columns' copied' b s,
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    binds_list g ts (map cell_sort cells) g' ->
    (forall key value, trie_get key inv = Some value -> value < pos) ->
    run_inverse_positions b cells inv' pos ->
    (forall x j, trie_get x names = Some j -> exists c,
      nth_error b (N.to_nat j) = Some c /\ s x = Some c) ->
    (forall x, trie_get x seen = Some tt -> exists ty, g x = Some ty) ->
    env_sorted g s -> env_sorted g' s.
  Proof.
    induction ts as [|term rest IH]; intros cells g g' names pos seen copy inv srcs columns
      copied copy' inv' srcs' columns' copied' b s Hcheck Hbinds Hbefore Hpositions Hnames
      Hseen Henv.
    - inversion Hbinds; subst. exact Henv.
    - destruct cells as [|c cells]; [inversion Hbinds|].
      inversion Hbinds as [|g0 middle g2 term' rest' ty types Hhead Htail];
        subst g0 g2 term' rest' ty types.
      assert (Hseen_keep : forall x, trie_get x seen = Some tt ->
          exists ty, middle x = Some ty).
      { intros x Hget. destruct (Hseen x Hget) as [ty Hbound]. exists ty.
        eapply run_binds_preserves; eassumption. }
      pose proof (run_inverse_positions_tail b c cells inv' pos Hpositions) as Hpositions_tail.
      destruct term as [x|v]; cbn [check_terms] in Hcheck.
      + destruct (trie_get x seen) as [[]|] eqn:Hget.
        * eapply (IH cells middle g' names (S pos) seen (N.succ copy)
            (PTrieCode.set (N.succ_pos copy) pos inv) srcs columns true
            copy' inv' srcs' columns' copied' b s Hcheck Htail).
          -- now apply run_inverse_before_set.
          -- exact Hpositions_tail.
          -- exact Hnames.
          -- exact Hseen_keep.
          -- eapply run_binds_env_existing; [exact Hhead|now apply Hseen|exact Henv].
        * destruct (trie_get x names) as [j|] eqn:Hname; [|discriminate].
          pose proof (run_check_terms_head_cell rest names pos (PTrieCode.set x tt seen)
            copy inv srcs columns copied copy' inv' srcs' columns' copied' j b c cells
            Hcheck Hbefore Hpositions) as Hcell.
          destruct (Hnames x j Hname) as [d [Hbinding Hvalue]].
          rewrite Hcell in Hbinding. injection Hbinding as <-.
          eapply (IH cells middle g' names (S pos) (PTrieCode.set x tt seen) copy
            (PTrieCode.set (N.succ_pos j) pos inv) srcs columns copied
            copy' inv' srcs' columns' copied' b s Hcheck Htail).
          -- now apply run_inverse_before_set.
          -- exact Hpositions_tail.
          -- exact Hnames.
          -- intros y Hlookup. destruct (Pos.eq_dec y x) as [Heq|Hneq].
             ++ subst y. exists (cell_sort c). now apply run_binds_var_bound with (g := g).
             ++ rewrite PTrie.get_set_other in Hlookup by exact Hneq. now apply Hseen_keep.
          -- eapply run_binds_env_value; [exact Hhead|exact Henv|exact Hvalue|reflexivity].
      + destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
        destruct columns as [|[|j [|k column]] columns]; try discriminate.
        destruct (V.eqb w v); [|discriminate].
        eapply (IH cells middle g' names (S pos) seen copy
          (PTrieCode.set (N.succ_pos (nat_n j)) pos inv) srcs columns copied
          copy' inv' srcs' columns' copied' b s Hcheck Htail).
        * now apply run_inverse_before_set.
        * exact Hpositions_tail.
        * exact Hnames.
        * exact Hseen_keep.
        * inversion Hhead; subst. exact Henv.
  Qed.

  (** Removing the literal prefix consumed by a term check preserves source satisfaction. *)
  Lemma run_check_terms_satisfied_tail : forall ts names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' db b,
    check_terms V.eqb names ts pos seen copy inv srcs columns copied =
      Some (copy', inv', srcs', columns', copied') ->
    run_sources_satisfied db b srcs columns -> run_sources_satisfied db b srcs' columns'.
  Proof.
    induction ts as [|[x|v] rest IH]; intros names pos seen copy inv srcs columns copied
      copy' inv' srcs' columns' copied' db b Hcheck Hsources;
      cbn [check_terms] in Hcheck.
    - injection Hcheck as <- <- <- <- <-. exact Hsources.
    - destruct (trie_get x seen).
      + eapply IH; eassumption.
      + destruct (trie_get x names); [eapply IH; eassumption|discriminate].
    - destruct srcs as [|[slot|slot|[i|w]] srcs]; try discriminate.
      destruct columns as [|[|j [|k column]] columns]; try discriminate.
      destruct (V.eqb w v); [|discriminate].
      inversion Hsources as [|src lv restSrc restCols Hhead Htail]; subst.
      eapply IH; eassumption.
  Qed.

  (** A join answer satisfies the original sources paired with their columns. *)
  Lemma run_join_answer_sources : forall db b j srcs,
    J.answer j (map (source_index db) srcs) b ->
    run_sources_satisfied db b srcs (cols j).
  Proof.
    intros db b [n columns] srcs [_ Hanswer]. cbn [cols] in *.
    revert columns Hanswer. induction srcs as [|src srcs IH]; intros [|lv columns] Hanswer;
      inversion Hanswer as [|lv' ix columns' indexes Hhead Htail]; subst; [constructor|].
    constructor; [exact Hhead|now apply IH].
  Qed.

  (** Raw checked query bindings type every context produced by the query's function atoms. *)
  Lemma run_check_query_sorted : forall p cp db table,
    D.wf db -> loaded p cp db ->
    slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty = Some table ->
    forall g q g', query_ok (program_sorts p) (program_kind p) g q g' ->
    forall newok names n ai copy used count srcs columns post
      finalcount srcs' columns' expected b s,
    check_query V.eqb newok names n table q ai copy used count srcs columns post =
      Some (finalcount, srcs', columns', expected) ->
    run_sources_satisfied db b srcs columns ->
    (forall x j, trie_get x names = Some j -> exists c,
      nth_error b (N.to_nat j) = Some c /\ s x = Some c) ->
    env_sorted g s -> env_sorted g' s.
  Proof.
    intros p cp db table Hwf Hloaded Htable g q g' Htyped.
    induction Htyped as [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hread Hargs Hres
      Htyped IH|g g1 primitive args res rest Hargs Hres Htyped IH];
      intros newok names n ai copy used count srcs columns post finalcount srcs' columns'
      expected b s Hcheck Hsources Hnames Henv.
    - exact Henv.
    - cbn [check_query] in Hcheck.
      destruct (check_atom V.eqb newok names n table f (args ++ option_list res)
        copy used count srcs columns) as [[[[[[nextcopy nextused] nextcount]
        nextsrcs] nextcols] copied]|] eqn:Hatom; [|discriminate].
      assert (Hwidth : forall k o, row (D.view db) f k o ->
          length (k ++ option_list o) = length (args ++ option_list res)).
      { intros k o Hrow.
        destruct (run_atom_row_bindings p cp db f args res g g1 g2 ss out k o
          Hloaded Hsort Hkind Hargs Hres Hrow) as [_ [_ Hlength]]. now symmetry. }
      destruct (run_check_atom_tuple db (decl_widths (decls V.t p) Empty)
        (Syntax.slots V.t cp) table newok names n f (args ++ option_list res)
        copy used count srcs columns nextcopy nextused nextcount nextsrcs nextcols copied b
        Hwf (proj1 (proj2 Hloaded)) Htable Hatom Hsources Hwidth)
        as [k [o [inv [before_srcs [before_cols [Hrow [Hterms [Hpositions
          [Hlength Hbefore]]]]]]]]].
      destruct (run_atom_row_bindings p cp db f args res g g1 g2 ss out k o
        Hloaded Hsort Hkind Hargs Hres Hrow) as [Hbinds _].
      assert (Hsorted : env_sorted g2 s).
      { eapply (run_check_terms_sorted (args ++ option_list res) (k ++ option_list o)
          g g2 names 0 Empty copy Empty before_srcs before_cols false nextcopy inv
          nextsrcs nextcols copied b s Hterms Hbinds).
        - intros key value Hget. rewrite PTrie.get_empty in Hget. discriminate.
        - exact Hpositions.
        - exact Hnames.
        - intros x Hget. rewrite PTrie.get_empty in Hget. discriminate.
        - exact Henv. }
      assert (Hremaining : run_sources_satisfied db b nextsrcs nextcols).
      { eapply run_check_terms_satisfied_tail; eassumption. }
      exact (IH newok names n (S ai) nextcopy nextused nextcount nextsrcs nextcols
        (if copied then ai :: post else post) finalcount srcs' columns' expected b s
        Hcheck Hremaining Hnames Hsorted).
    - exact (IH newok names n (S ai) copy used count srcs columns (ai :: post)
        finalcount srcs' columns' expected b s Hcheck Hsources Hnames Henv).
  Qed.

  (** Equal prefix lengths split pointwise interpretation at the same list boundary. *)
  Lemma run_terms_value_append_inv : forall (args : list (term V.t)) tail k output s,
    length args = length k -> terms_value s (args ++ tail) (k ++ output) ->
    terms_value s args k /\ terms_value s tail output.
  Proof.
    induction args as [|t args IH]; intros tail [|c k] output s Hlength Hvalues;
      cbn [length] in Hlength; try discriminate.
    - split; [constructor|exact Hvalues].
    - inversion Hvalues as [|t' c' ts cs Hhead Htail]; subst t' c' ts cs.
      destruct (IH tail k output s ltac:(lia) Htail) as [Hargs Houtput].
      split; [constructor; assumption|exact Houtput].
  Qed.

  (** A row whose concatenated positions interpret the terms satisfies its function atom. *)
  Lemma run_fun_from_values : forall w s f args res k o,
    length args = length k ->
    terms_value s (args ++ option_list res) (k ++ option_list o) ->
    row w f k o -> atom_holds V.prim w s (Fun V.t f args res).
  Proof.
    intros w s f args res k o Hlength Hvalues Hrow.
    destruct (run_terms_value_append_inv args (option_list res) k (option_list o) s
      Hlength Hvalues) as [Hargs Hresult].
    exists k, o. split; [exact Hargs|]. split; [|exact Hrow].
    destruct res as [t|], o as [c|]; cbn [option_list] in Hresult.
    - inversion Hresult as [|t' c' ts cs Hvalue Hnil]; subst. exact Hvalue.
    - inversion Hresult.
    - inversion Hresult.
    - exact I.
  Qed.

  (** A true primitive post check holds in any pointwise identical binding environment. *)
  Lemma run_primitive_check_sound : forall w t p args res s,
    prim_holds V.prim V.eqb t p args res = true ->
    (forall x, s x = trie_get x t) -> atom_holds V.prim w s (Prim V.t p args res).
  Proof.
    intros w t p args res s Hcheck Henv.
    destruct (proj1 (run_prim_holds_spec w t p args res) Hcheck)
      as [cells [values [v [Hargs [Hvalues [Hprim Hres]]]]]].
    exists cells, values, v. split.
    - eapply run_terms_value_agree; [exact Hargs|]. intros x _. apply Henv.
    - split; [exact Hvalues|]. split; [exact Hprim|].
      destruct res as [x|value]; cbn [term_value] in *; [|exact Hres].
      rewrite Henv. exact Hres.
  Qed.

  (** A well-sorted checked query interprets each matched row after its copy comparisons. *)
  Lemma run_check_query_values : forall p cp db q g g',
    query_ok (program_sorts p) (program_kind p) g q g' ->
    forall table newok names n ai copy used count srcs columns post finalcount srcs'
      columns' expected s b,
    D.wf db -> loaded p cp db ->
    slot_table (decl_widths (decls V.t p) Empty) (Syntax.slots V.t cp) 0 Empty = Some table ->
    check_query V.eqb newok names n table q ai copy used count srcs columns post =
      Some (finalcount, srcs', columns', expected) ->
    (forall x j, trie_get x names = Some j -> exists c,
      nth_error b (N.to_nat j) = Some c /\ s x = Some c) ->
    (forall k x, nth_error (run_query_duplicates q) k = Some x -> exists c,
      nth_error b (N.to_nat copy + k) = Some c /\ s x = Some c) ->
    run_sources_satisfied db b srcs columns ->
    Forall (fun a => match a with
      | Prim _ _ _ _ => atom_holds V.prim (D.view db) s a | Fun _ _ _ _ => True end) q ->
    matches V.prim (D.view db) q s /\ run_sources_satisfied db b srcs' columns'.
  Proof.
    intros p cp db q g g' Htyped.
    induction Htyped as [g|g g1 g2 g3 f args res ss kindout rest Hsort Hkind Hreads
      Hargs Hres Hrest IH|g g1 prim args res rest Hargs Hres Hrest IH];
      intros table newok names n ai copy used count srcs columns post finalcount srcs'
      columns' expected s b Hwf Hloaded Htable Hcheck Hnames Hcopies Hsources Hprimitives.
    - cbn [check_query] in Hcheck. inversion Hcheck; subst.
      split; [constructor|exact Hsources].
    - cbn [check_query] in Hcheck.
      destruct (check_atom V.eqb newok names n table f (args ++ option_list res)
        copy used count srcs columns)
        as [[[[[[nextcopy nextused] nextcount] nextsrcs] nextcols] copied]|]
        eqn:Hatom; [|discriminate].
      assert (Hwidth : forall k o, row (D.view db) f k o ->
          length (k ++ option_list o) = length (args ++ option_list res)).
      { intros k o Hrow. destruct (run_atom_row_bindings p cp db f args res g g1 g2 ss
          kindout k o Hloaded Hsort Hkind Hargs Hres Hrow) as [_ [_ Hlength]].
        symmetry. exact Hlength. }
      destruct (run_check_atom_tuple db (decl_widths (decls V.t p) Empty)
        (Syntax.slots V.t cp) table newok names n f (args ++ option_list res)
        copy used count srcs columns nextcopy nextused nextcount nextsrcs nextcols copied b
        Hwf (proj1 (proj2 Hloaded)) Htable Hatom Hsources Hwidth)
        as [k [o [inv [before_srcs [before_cols
          [Hrow [Hterms [Hpositions [Hlength Hbefore_sources]]]]]]]]].
      assert (Hatom_copies : forall j x,
          nth_error (run_term_duplicates Empty (args ++ option_list res)) j = Some x ->
          exists c, nth_error b (N.to_nat copy + j) = Some c /\ s x = Some c).
      { intros j x Hnth. apply Hcopies. cbn [run_query_duplicates].
        rewrite nth_error_app1; [exact Hnth|].
        apply nth_error_Some. rewrite Hnth. discriminate. }
      destruct (run_check_terms_values (args ++ option_list res) names 0 Empty copy Empty
        before_srcs before_cols false nextcopy inv nextsrcs nextcols copied s b
        (k ++ option_list o) db Hterms Hlength)
        as [Hvalues Hremaining].
      + intros key value Hempty. rewrite PTrie.get_empty in Hempty. discriminate.
      + exact Hpositions.
      + exact Hnames.
      + exact Hatom_copies.
      + exact Hbefore_sources.
      + pose proof (run_check_terms_count (args ++ option_list res) names 0 Empty copy Empty
          before_srcs before_cols false nextcopy inv nextsrcs nextcols copied Hterms)
          as Hnextcopy.
        assert (Hrest_copies : forall j x, nth_error (run_query_duplicates rest) j = Some x ->
            exists c, nth_error b (N.to_nat nextcopy + j) = Some c /\ s x = Some c).
        { intros j x Hnth. rewrite Hnextcopy, N2Nat.inj_add, Nat2N.id.
          replace (N.to_nat copy + length (run_term_duplicates Empty
              (args ++ option_list res)) + j) with
            (N.to_nat copy + (length (run_term_duplicates Empty
              (args ++ option_list res)) + j)) by lia.
          apply Hcopies. cbn [run_query_duplicates]. rewrite nth_error_app2 by lia.
          replace (length (run_term_duplicates Empty (args ++ option_list res)) + j -
            length (run_term_duplicates Empty (args ++ option_list res))) with j by lia.
          exact Hnth. }
        inversion Hprimitives as [|a rest' Hprimitive Hprimitive_tail]; subst a rest'.
        destruct (IH table newok names n (S ai) nextcopy nextused nextcount nextsrcs nextcols
          (if copied then ai :: post else post) finalcount srcs' columns' expected s b
          Hwf Hloaded Htable Hcheck Hnames Hrest_copies Hremaining Hprimitive_tail)
          as [Hmatches Hsources_final].
        split; [|exact Hsources_final]. constructor; [|exact Hmatches].
        destruct (run_atom_row_bindings p cp db f args res g g1 g2 ss kindout k o Hloaded
          Hsort Hkind Hargs Hres Hrow) as [_ [Hargs_length _]].
        exact (run_fun_from_values (D.view db) s f args res k o Hargs_length Hvalues Hrow).
    - cbn [check_query] in Hcheck.
      inversion Hprimitives as [|a rest' Hprimitive Hprimitive_tail]; subst a rest'.
      destruct (IH table newok names n (S ai) copy used count srcs columns (ai :: post)
        finalcount srcs' columns' expected s b Hwf Hloaded Htable Hcheck Hnames Hcopies
        Hsources Hprimitive_tail) as [Hmatches Hsources_final].
      split; [constructor; assumption|exact Hsources_final].
  Qed.

  Lemma F1_plan_match_sound : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r ->
    In b (bindings cp c db) -> keep p c (bind_trie c b) = true ->
    matches V.prim (D.view db) (query V.t r) (env_of c b).
  Proof.
    intros p cp db c b [q acts] Hplan Hwf Hloaded Hin Hrule Hbinding Hkeep.
    pose proof (plans_ok_sorted p cp Hplan) as Hprogram. unfold program_ok in Hprogram.
    apply Forall_forall with (x := Rule V.t q acts) in Hprogram;
      [|now apply nth_error_In in Hrule].
    destruct Hprogram as [g [Htyped Hactions]].
    destruct (run_plan_member p cp c Hplan Hin)
      as [table [newok [r [Htable [Hfound Hcheck]]]]].
    rewrite Hrule in Hfound. injection Hfound as <-.
    destruct (run_check_cplan_parts newok table (rule_ix V.t c) (Rule V.t q acts) c Hcheck)
      as [_ [Hvar_length [names [expected [Hnames [Hlayout [Hquery Hpost]]]]]]].
    pose proof (run_plan_join_wf p cp db c Hplan Hwf Hloaded Hin) as Hjoin.
    pose proof (J.run_sound (join V.t c) (map (source_index db) (sources V.t c)) b
      Hjoin Hbinding) as Hanswer.
    pose proof (proj1 Hanswer) as Hbinding_length.
    pose proof (run_join_answer_sources db b (join V.t c) (sources V.t c) Hanswer) as Hsources.
    destruct (run_var_table_spec (var_of V.t c) names Hnames) as [Hdistinct Hindices].
    assert (Hname_cells : forall x j, trie_get x names = Some j -> exists cell,
        nth_error b (N.to_nat j) = Some cell /\ env_of c b x = Some cell).
    { apply run_checked_names_cells; [exact Hnames|lia]. }
    assert (Hpost_correct : post V.t c = run_query_post q 0).
    { pose proof (run_check_query_post q newok names (nvars (join V.t c)) table 0 0 Empty 0
        (sources V.t c) (cols (join V.t c)) [] (nat_n (nvars (join V.t c))) [] [] expected
        Hquery) as Hexpected.
      rewrite Hpost, Hexpected, !rev_append_rev, !app_nil_r, rev_involutive. reflexivity. }
    unfold keep in Hkeep. rewrite rule_at_nth in Hkeep.
    change (plan_rule_ix c) with (rule_ix V.t c) in Hkeep.
    rewrite (@nth_error_nth (rule V.t) (rules V.t p) (N.to_nat (rule_ix V.t c))
      (Rule V.t q acts) (Rule V.t [] []) Hrule) in Hkeep.
    change (keep_post V.prim V.eqb q (bind_trie c b) (post V.t c) (var_of V.t c) = true)
      in Hkeep.
    rewrite Hpost_correct in Hkeep.
    destruct (run_keep_post_sound q (bind_trie c b) (var_of V.t c) Hkeep)
      as [Hprimitive_checks Hcopy_checks].
    rewrite run_query_duplicates_count, Nat.add_0_r in Hcopy_checks.
    assert (Hcopies : forall j x, nth_error (run_query_duplicates q) j = Some x -> exists cell,
        nth_error b j = Some cell /\ env_of c b x = Some cell).
    { apply run_binding_copies_sound; [exact Hdistinct|exact Hcopy_checks]. }
    assert (Hprimitives : Forall (fun a => match a with
        | Prim _ _ _ _ => atom_holds V.prim (D.view db) (env_of c b) a
        | Fun _ _ _ _ => True end) q).
    { apply Forall_forall. intros a Ha.
      apply Forall_forall with (x := a) in Hprimitive_checks; [|exact Ha].
      destruct a as [f args res|prim args res]; [exact I|].
      eapply run_primitive_check_sound; [exact Hprimitive_checks|].
      intro x. unfold bind_trie. rewrite run_binding_trie_get. reflexivity. }
    exact (proj1 (run_check_query_values p cp db q ctx_empty g Htyped table newok names
      (nvars (join V.t c)) 0 0 Empty 0 (sources V.t c) (cols (join V.t c)) []
      (nat_n (nvars (join V.t c))) [] [] expected (env_of c b) b Hwf Hloaded Htable Hquery
      Hname_cells Hcopies Hsources Hprimitives)).
  Qed.




  Lemma F2_naive_plans_complete : forall p cp db r s, plans_ok p cp -> D.wf db ->
    loaded p cp db -> D.canonical db -> In r (rules V.t p) ->
    matches V.prim (D.view db) (query V.t r) s ->
    exists c b, In c (naive V.t cp) /\
      nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r /\
      In b (bindings cp c db) /\ keep p c (bind_trie c b) = true /\
      agrees (env_of c b) s (query_vars r).
  Proof.
    intros p cp db [q acts] s Hplans Hwf Hloaded Hcanonical Hmember Hmatches.
    destruct (run_rule_naive_member p cp (Rule V.t q acts) Hplans Hmember)
      as [table [c [Hnaive [Hslots [Hrule Hchecked]]]]].
    destruct c as [ix [n columns] srcs vars postlist].
    destruct (run_check_cplan_parts false table ix (Rule V.t q acts)
      (CPlan V.t ix (JPlan n columns) srcs vars postlist) Hchecked)
      as [_ [Hlength [names [expected [Hnames [Hlayout [Hquery Hpost]]]]]]].
    cbn [var_of join sources query post nvars cols] in Hlength, Hnames, Hlayout, Hquery, Hpost.
    pose proof (plans_ok_sorted p cp Hplans) as Hprogram.
    apply Forall_forall with (x := Rule V.t q acts) in Hprogram; [|exact Hmember].
    destruct Hprogram as [g [Htyped Hactions]].
    assert (Hregistered : forall x, In (Var x) (flat_map atom_terms q) ->
        exists j, trie_get x names = Some j).
    { intros x Hin.
      destruct (run_query_vars_fun (program_sorts p) (program_kind p) q g Htyped x
        (proj2 (run_query_vars_member q x) Hin)) as [f [args [res [Hfun Hvar]]]].
      eapply run_check_query_names; [exact Hquery|exact Hfun|exact Hvar]. }
    set (b := run_make_binding s vars (run_query_duplicates q)
      (run_literal_entries srcs columns)).
    destruct (run_layout_assignment q vars srcs columns s Hlayout)
      as [Hbinding_length [Hcopies [Hreal Hliterals]]].
    change (length b = length vars) in Hbinding_length.
    change (forall j x, nth_error (run_query_duplicates q) j = Some x ->
      nth_error b j = Some (run_env_cell s x)) in Hcopies.
    change (forall j x, nth_error vars j = Some x ->
      (x <= query_max q 1%positive)%positive ->
      nth_error b j = Some (run_env_cell s x)) in Hreal.
    change (forall j c, In (j, c) (run_literal_entries srcs columns) ->
      nth_error b j = Some c) in Hliterals.
    destruct (run_var_table_spec vars names Hnames) as [Hdistinct Hpositions].
    assert (Hnamed_cells : forall x j, In (Var x) (flat_map atom_terms q) ->
        trie_get x names = Some j -> nth_error b (N.to_nat j) = Some (run_env_cell s x)).
    { intros x j Hin Hget. apply Hreal.
      - now apply Hpositions.
      - now apply planner_query_max_member with (m := 1%positive). }
    assert (Hslot_cells : forall f perm slot, slot_matches table f perm slot = true ->
        D.slot_of db slot = Some (f, perm)).
    { intros f perm slot Hmatch. unfold D.slot_of.
      rewrite (proj1 (proj2 Hloaded)).
      eapply run_slot_matches_index; [exact Hslots|exact Hmatch]. }
    destruct (run_check_query_answer q db names n table 0 0 Empty 0 srcs columns []
      (nat_n n) [] [] expected s b Hwf Hquery Hmatches Hnamed_cells Hcopies Hliterals
      Hslot_cells) as [_ Hanswer].
    assert (Hsatisfied : run_sources_satisfied db b srcs columns).
    { apply Hanswer. constructor. }
    assert (Hall : In (CPlan V.t ix (JPlan n columns) srcs vars postlist) (all_plans cp)).
    { unfold all_plans. apply in_or_app. now left. }
    assert (Hbinding : In b
        (bindings cp (CPlan V.t ix (JPlan n columns) srcs vars postlist) db)).
    { apply J.run_complete.
      - exact (run_plan_join_wf p cp db
          (CPlan V.t ix (JPlan n columns) srcs vars postlist) Hplans Hwf Hloaded Hall).
      - apply run_sources_join_answer; [cbn; lia|exact Hsatisfied]. }
    assert (Hagree : forall x, In (Var x) (flat_map atom_terms q) ->
        binding_env vars b x = s x).
    { eapply run_binding_agrees; eassumption. }
    assert (Hpost_exact : postlist = run_query_post q 0).
    { pose proof (run_check_query_post q false names n table 0 0 Empty 0 srcs columns []
        (nat_n n) [] [] expected Hquery) as Hexpected.
      rewrite Hpost, Hexpected, app_nil_r, rev_append_rev, app_nil_r, rev_involutive.
      reflexivity. }
    assert (Hkeep : keep p (CPlan V.t ix (JPlan n columns) srcs vars postlist)
        (bind_trie (CPlan V.t ix (JPlan n columns) srcs vars postlist) b) = true).
    { unfold keep, bind_trie. cbn [plan_rule_ix plan_vars plan_post].
      rewrite rule_at_nth.
      rewrite (@nth_error_nth (rule V.t) (rules V.t p) (N.to_nat ix)
        (Rule V.t q acts) (Rule V.t [] []) Hrule).
      rewrite Hpost_exact. apply run_keep_post_complete.
      - eapply run_binding_primitive_checks; eassumption.
      - eapply run_binding_copy_cells;
          [exact Hmatches|exact Hdistinct| |exact Hagree|exact Hcopies].
        exact (proj1 (run_layout_ok_sound q vars srcs columns Hlayout)). }
    exists (CPlan V.t ix (JPlan n columns) srcs vars postlist), b.
    split; [exact Hnaive|]. split; [exact Hrule|]. split; [exact Hbinding|].
    split; [exact Hkeep|]. intros x Hin. apply Hagree.
    now apply (proj1 (run_query_vars_member q x)).
  Qed.


  (** Canonicalization changes an identifier name without changing its sort. *)
  Lemma run_canon_sort : forall db (c : cell V.t), cell_sort (D.canon db c) = cell_sort c.
  Proof.
    intros db [i|v]; reflexivity.
  Qed.

  (** Canonicalizing a row keeps all argument sorts. *)
  Lemma run_canon_sorts : forall db (k : list (cell V.t)),
    map cell_sort (map (D.canon db) k) = map cell_sort k.
  Proof.
    intros db k. induction k as [|c rest IH]; cbn [map]; [reflexivity|].
    rewrite run_canon_sort, IH. reflexivity.
  Qed.

  (** Canonicalizing an optional output keeps its sort. *)
  Lemma run_canon_output_sort : forall db (o : option (cell V.t)),
    option_map cell_sort (option_map (D.canon db) o) = option_map cell_sort o.
  Proof.
    intros db [c|]; cbn [option_map]; [now rewrite run_canon_sort|reflexivity].
  Qed.

  (** Combining outputs of one declared kind preserves their output sort. *)
  Lemma run_combine_sorted : forall db f out previous o,
    kind (D.view db) f = Some out ->
    (match previous with
     | Some old => option_map cell_sort old = out_sort out
     | None => True
     end) ->
    option_map cell_sort o = out_sort out ->
    option_map cell_sort (D.combine db f previous o) = out_sort out.
  Proof.
    intros db f out previous o Hkind Hprevious Hout.
    unfold D.combine. rewrite Hkind.
    destruct previous as [[[i|v]|]|]; cbn in Hprevious |- *; try assumption.
    destruct out; destruct o as [[j|w]|]; cbn in *; congruence.
  Qed.

  (** Folding compatible outputs keeps their common sort. *)
  Lemma run_fold_outputs_sorted : forall db f out os acc,
    kind (D.view db) f = Some out ->
    Forall (fun o => option_map cell_sort o = out_sort out) os ->
    option_map cell_sort acc = out_sort out ->
    option_map cell_sort
      (fold_left (fun a o => D.combine db f (Some a) o) os acc) = out_sort out.
  Proof.
    intros db f out os. induction os as [|o rest IH]; intros acc Hkind Hsort Hacc.
    - exact Hacc.
    - inversion Hsort as [|o' rest' Ho Hrest]; subst o' rest'. cbn [fold_left].
      apply IH; [exact Hkind|exact Hrest|].
      apply run_combine_sorted; assumption.
  Qed.

  (** Merging a nonempty group of compatible outputs keeps their common sort. *)
  Lemma run_merged_sorted : forall db f out os,
    kind (D.view db) f = Some out -> os <> [] ->
    Forall (fun o => option_map cell_sort o = out_sort out) os ->
    option_map cell_sort (D.merged db f os) = out_sort out.
  Proof.
    intros db f out [|o rest] Hkind Hnonempty Hsort; [contradiction|].
    inversion Hsort as [|o' rest' Ho Hrest]; subst o' rest'.
    cbn [D.merged map]. apply run_fold_outputs_sorted; [exact Hkind| |].
    - apply Forall_forall. intros output Hin. apply in_map_iff in Hin as [old [<- Hin]].
      rewrite run_canon_output_sort. exact ((proj1 (Forall_forall _ _)) Hrest old Hin).
    - now rewrite run_canon_output_sort.
  Qed.

  Lemma F21_put_sorted : forall sorts f k o db, D.wf db -> D.kind_ok db f k o ->
    view_sorted sorts (D.view db) -> row_sorted sorts (kind (D.view db)) f k o ->
    view_sorted sorts (D.view (D.put f k o db)).
  Proof.
    intros sorts f k o db Hwf Hallowed Hsorted [out [Hsort [Hkind Hout]]].
    intros g key output Hrow. unfold row_sorted.
    rewrite (proj1 (D.layout_put f k o db Hwf)).
    apply (proj1 (D.put_rows f k o db Hwf Hallowed g key output)) in Hrow.
    destruct Hrow as [[Hrow _]|[-> [-> <-]]].
    - exact (Hsorted g key output Hrow).
    - exists out. split; [now rewrite run_canon_sorts|]. split; [exact Hkind|].
      apply run_combine_sorted; [exact Hkind| |now rewrite run_canon_output_sort].
      destruct (D.old db f (map (D.canon db) k)) as [old|] eqn:Hold; [|exact I].
      apply (proj1 (D.old_row db f (map (D.canon db) k) old Hwf)) in Hold.
      destruct (Hsorted f (map (D.canon db) k) old Hold)
        as [oldout [_ [Holdkind Holdsort]]].
      rewrite Hkind in Holdkind. injection Holdkind as <-. exact Holdsort.
  Qed.

  Lemma F22_make_sorted : forall sorts f k db, D.wf db -> kind (D.view db) f = Some OId ->
    sorts f = Some (map cell_sort k) -> view_sorted sorts (D.view db) ->
    view_sorted sorts (D.view (snd (D.make f k db))).
  Proof.
    intros sorts f k db Hwf Hkind Hsort Hsorted.
    pose proof (D.make_spec f k db Hwf Hkind) as Hmake.
    destruct (D.make f k db) as [i next]. cbn [snd].
    destruct Hmake as [[j [_ [_ ->]]]|[_ [_ [_ [Hkinds [_ Hrows]]]]]].
    - exact Hsorted.
    - intros g key output Hrow. unfold row_sorted. rewrite Hkinds.
      apply (proj1 (Hrows g key output)) in Hrow.
      destruct Hrow as [Hrow|[-> [-> ->]]].
      + exact (Hsorted g key output Hrow).
      + exists OId. split; [now rewrite run_canon_sorts|]. split; [exact Hkind|reflexivity].
  Qed.

  Lemma F23_union_sorted : forall sorts i j db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.union i j db)).
  Proof.
    intros sorts i j db Hwf Hsorted f k o Hrow.
    rewrite (D.union_rows i j db Hwf) in Hrow.
    unfold row_sorted. rewrite (proj1 (D.layout_union i j db Hwf)).
    exact (Hsorted f k o Hrow).
  Qed.

  Lemma F24_rebuild_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.rebuild db)).
  Proof.
    intros sorts db Hwf Hsorted f key output Hrow.
    destruct (D.rebuild_from db f key output Hwf Hrow)
      as [srcs [Hnonempty [Hsources Houtput]]].
    destruct srcs as [|[first old] rest]; [contradiction|].
    inversion Hsources as [|pair rest' [Hfirst Hkey] Hrest]; subst pair rest'.
    destruct (Hsorted f first old Hfirst) as [out [Hsort [Hkind Hout]]].
    assert (Hkind' : kind (D.view (D.rebuild db)) f = Some out).
    { rewrite (proj1 (D.layout_rebuild db Hwf)). exact Hkind. }
    exists out. split.
    - cbn [fst] in Hkey. rewrite <- Hkey, run_canon_sorts. exact Hsort.
    - split; [exact Hkind'|]. rewrite Houtput.
      apply run_merged_sorted; [exact Hkind'|discriminate|].
      apply Forall_forall. intros result Hin.
      apply in_map_iff in Hin as [[k o] [Heq Hin]]. cbn in Heq. subst result.
      destruct ((proj1 (Forall_forall _ _)) Hsources (k, o) Hin) as [Hsource _].
      destruct (Hsorted f k o Hsource) as [other [_ [Hother Hresult]]].
      rewrite Hkind in Hother. injection Hother as <-. exact Hresult.
  Qed.

  Lemma F25_advance_sorted : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> view_sorted sorts (D.view (D.advance db)).
  Proof.
    intros sorts db Hwf Hsorted. rewrite (proj1 (proj2 (D.wf_advance db Hwf))).
    exact Hsorted.
  Qed.

  (** An empty local table leaves the binding environment unchanged. *)
  Lemma run_look_empty : forall (s : Model.env (V := V.t)) x, look s Empty x = s x.
  Proof.
    intros s x. unfold look. now rewrite PTrie.get_empty.
  Qed.

  (** Updating a local binding implements the semantic environment update. *)
  Lemma run_look_set : forall (s : Model.env (V := V.t)) locals x c y,
    look s (PTrieCode.set x c locals) y = update (look s locals) x c y.
  Proof.
    intros s locals x c y. unfold look, update.
    destruct (Pos.eqb x y) eqn:Hsame.
    - apply Pos.eqb_eq in Hsame. subst y. now rewrite PTrie.get_set_same.
    - apply Pos.eqb_neq in Hsame. rewrite PTrie.get_set_other by congruence. reflexivity.
  Qed.

  (** A successful action-term lookup has exactly its semantic value. *)
  Lemma run_term_cell_spec : forall (s : Model.env (V := V.t)) locals t c,
    term_cell s locals t = Some c <-> term_value (look s locals) t c.
  Proof.
    intros s locals [x|v] c; cbn [term_cell term_value]; [reflexivity|].
    split; intro Heq; [now injection Heq as <-|now subst c].
  Qed.

  (** A successful argument lookup gives the semantic argument list. *)
  Lemma run_term_cells_spec : forall (s : Model.env (V := V.t)) locals ts cs,
    term_cells s locals ts = Some cs <-> terms_value (look s locals) ts cs.
  Proof.
    intros s locals ts. induction ts as [|t rest IH]; intro cs.
    - cbn [term_cells terms_value]. split; intro H.
      + injection H as <-. constructor.
      + inversion H. reflexivity.
    - split; intro H.
      + cbn [term_cells] in H.
        destruct (term_cell s locals t) as [c|] eqn:Hcell; [|discriminate].
        destruct (term_cells s locals rest) as [more|] eqn:Hmore; [|discriminate].
        injection H as <-. constructor.
        * apply run_term_cell_spec. exact Hcell.
        * apply IH. reflexivity.
      + inversion H as [|t' c rest' more Hhead Htail]; subst t' rest' cs.
        cbn [term_cells].
        rewrite (proj2 (run_term_cell_spec s locals t c) Hhead), (proj2 (IH more) Htail).
        reflexivity.
  Qed.

  (** An optional result lookup agrees with the semantic result pattern. *)
  Lemma run_result_cell_spec : forall (s : Model.env (V := V.t)) locals res o,
    result_cell s locals res = Some o <->
    match res, o with
    | None, None => True
    | Some t, Some c => term_value (look s locals) t c
    | _, _ => False
    end.
  Proof.
    intros s locals [t|] [c|]; cbn [result_cell].
    - rewrite <- run_term_cell_spec. destruct (term_cell s locals t); split; congruence.
    - destruct (term_cell s locals t); split; intro H; try discriminate; contradiction.
    - split; [discriminate|contradiction].
    - split; [intros; exact I|intros; reflexivity].
  Qed.

  (** Primitive argument lookup supplies exactly the value cells it reads. *)
  Lemma run_term_values_spec : forall (s : Model.env (V := V.t)) locals ts vs,
    term_values s locals ts = Some vs ->
    terms_value (look s locals) ts (map Val vs).
  Proof.
    intros s locals ts. induction ts as [|t rest IH]; intros vs Hlookup.
    - injection Hlookup as <-. constructor.
    - cbn [term_values] in Hlookup.
      destruct (term_cell s locals t) as [[i|v]|] eqn:Hcell; try discriminate.
      destruct (term_values s locals rest) as [more|] eqn:Hmore; [|discriminate].
      injection Hlookup as <-. constructor.
      + apply run_term_cell_spec. exact Hcell.
      + apply IH. reflexivity.
  Qed.

  (** Value cells represent their underlying primitive arguments. *)
  Lemma run_value_cells : forall vs : list V.t, values (map Val vs) vs.
  Proof.
    intro vs. induction vs; constructor; auto.
  Qed.

  (** A sorted term has a successful lookup of its declared sort. *)
  Lemma run_term_cell_typed : forall g (s : Model.env (V := V.t)) locals t ty,
    env_sorted g (look s locals) -> has g t ty ->
    exists c, term_cell s locals t = Some c /\ cell_sort c = ty.
  Proof.
    intros g s locals [x|v] ty Henv Hhas.
    - apply Henv. exact Hhas.
    - cbn [has] in Hhas. subst ty. exists (Val v). split; reflexivity.
  Qed.

  (** Sorted argument terms have successful lookups with the declared argument sorts. *)
  Lemma run_term_cells_typed : forall g (s : Model.env (V := V.t)) locals ts ss,
    env_sorted g (look s locals) -> Forall2 (has g) ts ss ->
    exists cs, term_cells s locals ts = Some cs /\ map cell_sort cs = ss.
  Proof.
    intros g s locals ts ss Henv Hhas. induction Hhas as [|t ty ts ss Hhead Htail IH].
    - exists []. split; reflexivity.
    - destruct (run_term_cell_typed g s locals t ty Henv Hhead) as [c [Hc Hty]].
      destruct IH as [cs [Hcs Hsort]]. exists (c :: cs).
      cbn [term_cells map]. rewrite Hc, Hcs, Hty, Hsort. split; reflexivity.
  Qed.

  (** A sorted optional result has a successful lookup of its declared output sort. *)
  Lemma run_result_cell_typed : forall g (s : Model.env (V := V.t)) locals out res,
    env_sorted g (look s locals) -> has_result g out res ->
    exists o, result_cell s locals res = Some o /\ option_map cell_sort o = out_sort out.
  Proof.
    intros g s locals out res Henv Hhas. destruct out; destruct res as [t|];
      cbn [has_result out_sort] in Hhas; try contradiction.
    - exists None. split; reflexivity.
    - destruct (run_term_cell_typed g s locals t SId Henv Hhas) as [c [Hc Hsort]].
      exists (Some c). cbn [result_cell option_map out_sort]. rewrite Hc, Hsort.
      split; reflexivity.
    - destruct (run_term_cell_typed g s locals t SVal Henv Hhas) as [c [Hc Hsort]].
      exists (Some c). cbn [result_cell option_map out_sort]. rewrite Hc, Hsort.
      split; reflexivity.
  Qed.

  (** Sorted primitive arguments always evaluate to a list of values. *)
  Lemma run_term_values_typed : forall g (s : Model.env (V := V.t)) locals ts,
    env_sorted g (look s locals) -> Forall (fun t => has g t SVal) ts ->
    exists vs, term_values s locals ts = Some vs.
  Proof.
    intros g s locals ts Henv Hhas. induction Hhas as [|t rest Hhead Htail IH].
    - exists []. reflexivity.
    - destruct (run_term_cell_typed g s locals t SVal Henv Hhead) as [[i|v] [Hc Hsort]];
        [discriminate|].
      destruct IH as [vs Hvs]. exists (v :: vs). cbn [term_values]. now rewrite Hc, Hvs.
  Qed.

  (** An identifier read by an action term was already allocated. *)
  Lemma run_term_cell_allocated : forall db (s : Model.env (V := V.t)) locals t i,
    env_allocated db (look s locals) -> term_cell s locals t = Some (Id i) ->
    D.allocated db i.
  Proof.
    intros db s locals [x|v] i Hallocated Hcell; [eapply Hallocated; exact Hcell|discriminate].
  Qed.

  (** Every identifier in a successfully read argument list was already allocated. *)
  Lemma run_term_cells_allocated : forall db (s : Model.env (V := V.t)) locals ts cs,
    env_allocated db (look s locals) -> term_cells s locals ts = Some cs ->
    forall i, In (Id i) cs -> D.allocated db i.
  Proof.
    intros db s locals ts. induction ts as [|t rest IH]; intros cs Hallocated Hcells i Hin.
    - injection Hcells as <-. contradiction.
    - cbn [term_cells] in Hcells.
      destruct (term_cell s locals t) as [c|] eqn:Hc; [|discriminate].
      destruct (term_cells s locals rest) as [more|] eqn:Hmore; [|discriminate].
      injection Hcells as <-. destruct Hin as [Heq|Hin].
      + subst c. eapply run_term_cell_allocated; eauto.
      + eapply IH; eauto.
  Qed.

  (** An identifier in a successfully read result was already allocated. *)
  Lemma run_result_cell_allocated : forall db (s : Model.env (V := V.t)) locals res o,
    env_allocated db (look s locals) -> result_cell s locals res = Some o ->
    forall i, In (Id i) (option_list o) -> D.allocated db i.
  Proof.
    intros db s locals [t|] o Hallocated Hresult i Hin; cbn [result_cell] in Hresult.
    - destruct (term_cell s locals t) as [c|] eqn:Hc; [|discriminate].
      injection Hresult as <-. destruct Hin as [Heq|[]]. subst c.
      eapply run_term_cell_allocated; eauto.
    - injection Hresult as <-. contradiction.
  Qed.

  (** A local assignment preserves the context's environment typing. *)
  Lemma run_env_sorted_set : forall g (s : Model.env (V := V.t)) locals x c ty,
    env_sorted g (look s locals) -> cell_sort c = ty ->
    env_sorted (ctx_set g x ty) (look s (PTrieCode.set x c locals)).
  Proof.
    intros g s locals x c ty Henv Hsort y other Hctx.
    rewrite run_look_set. unfold ctx_set in Hctx. unfold update.
    destruct (Pos.eqb x y).
    - injection Hctx as <-. exists c. split; [reflexivity|exact Hsort].
    - apply Henv. exact Hctx.
  Qed.

  (** Allocated environment identifiers remain allocated when the counter grows. *)
  Lemma run_env_allocated_mono : forall db next (s : Model.env (V := V.t)),
    (D.ids db <= D.ids next)%N -> env_allocated db s -> env_allocated next s.
  Proof.
    intros db next s Hids Henv x i Hcell. unfold D.allocated.
    specialize (Henv x i Hcell). unfold D.allocated in Henv. lia.
  Qed.

  (** A local assignment preserves allocation when its new cell is allocated. *)
  Lemma run_env_allocated_set : forall db (s : Model.env (V := V.t)) locals x c,
    env_allocated db (look s locals) ->
    (forall i, c = Id i -> D.allocated db i) ->
    env_allocated db (look s (PTrieCode.set x c locals)).
  Proof.
    intros db s locals x c Henv Hcell y i Hlookup.
    rewrite run_look_set in Hlookup. unfold update in Hlookup.
    destruct (Pos.eqb x y).
    - apply Hcell. now injection Hlookup.
    - eapply Henv. exact Hlookup.
  Qed.

  (** Typing a query from the empty context determines every output-context binding. *)
  Lemma run_query_context : forall (p : program V.t) (q : list (atom V.t)) g h,
    query_ok (program_sorts p) (program_kind p) ctx_empty q g ->
    query_ok (program_sorts p) (program_kind p) ctx_empty q h ->
    forall x, g x = h x.
  Proof.
    intros p q g h Hg Hh x.
    destruct (bind_query_b_complete V.t (decls V.t p) Empty ctx_empty q g
      trie_ctx_empty Hg) as [tg [Htg Hgrepr]].
    destruct (bind_query_b_complete V.t (decls V.t p) Empty ctx_empty q h
      trie_ctx_empty Hh) as [th [Hth Hhrepr]].
    rewrite Htg in Hth. injection Hth as <-. rewrite <- Hgrepr, <- Hhrepr. reflexivity.
  Qed.

  (** A checked rule and its environment share a context that types all its actions. *)
  Lemma run_rule_context : forall p cp r s, plans_ok p cp -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s ->
    exists g, query_ok (program_sorts p) (program_kind p) ctx_empty (query V.t r) g /\
      actions_ok (program_sorts p) (program_kind p) g (actions V.t r) /\ env_sorted g s.
  Proof.
    intros p cp r s Hchecked Hin [h [Hquery Henv]].
    pose proof (plans_ok_sorted p cp Hchecked) as Hprogram.
    destruct ((proj1 (Forall_forall _ _)) Hprogram r Hin) as [g [Hg Hacts]].
    exists g. split; [exact Hg|]. split; [exact Hacts|].
    intros x ty Hctx. apply Henv. rewrite <- (run_query_context p (query V.t r) g h Hg Hquery x).
    exact Hctx.
  Qed.

  (** Every checked slot fits a row having its declaration's width. *)
  Lemma run_slots_fit : forall p cp db f ss kindout n,
    plans_ok p cp -> loaded p cp db -> program_sorts p f = Some ss ->
    program_kind p f = Some kindout ->
    n = length ss + match kindout with ORel => 0 | _ => 1 end -> D.slots_fit db f n.
  Proof.
    intros p cp db f ss kindout n Hchecked [_ [Hslots _]] Hsort Hkind Hwidth perm Hin.
    rewrite Hslots in Hin.
    destruct (check_plan_slots p cp f perm Hchecked Hin) as [d [Hdecl [Hnodup Hbound]]].
    destruct (run_find_decl_fields (decls V.t p) f d Hdecl) as [Hds Hdk].
    change (program_sorts p f = Some (arg_sorts d)) in Hds.
    change (program_kind p f = Some (out d)) in Hdk.
    rewrite Hsort in Hds. injection Hds as Hss. rewrite Hkind in Hdk. injection Hdk as Hout.
    rewrite <- Hss, <- Hout in Hbound. split; [exact Hnodup|]. now rewrite Hwidth.
  Qed.

  (** The output sort determines how many cells the output contributes. *)
  Lemma run_output_length : forall (o : option (cell V.t)) kindout,
    option_map cell_sort o = out_sort kindout ->
    length (option_list o) = match kindout with ORel => 0 | _ => 1 end.
  Proof.
    intros [c|] kindout Hsort; destruct kindout; cbn in *; try discriminate; reflexivity.
  Qed.

  (** A sorted and allocated row meets the database's insertion preconditions. *)
  Lemma run_put_allowed : forall p cp db f k o,
    plans_ok p cp -> loaded p cp db ->
    row_sorted (program_sorts p) (program_kind p) f k o ->
    (forall i, In (Id i) (k ++ option_list o) -> D.allocated db i) -> D.kind_ok db f k o.
  Proof.
    intros p cp db f k o Hchecked Hloaded [out [Hsort [Hkind Hout]]] Hallocated.
    split; [exact Hallocated|]. split.
    - eapply run_slots_fit; [exact Hchecked|exact Hloaded|exact Hsort|exact Hkind|].
      rewrite length_app, length_map, (run_output_length o out Hout). reflexivity.
    - rewrite (proj1 Hloaded), Hkind. destruct out; destruct o as [[i|v]|];
        cbn in *; try discriminate; exact I.
  Qed.

  (** Constructor allocation never decreases the identifier counter. *)
  Lemma run_make_ids : forall f k db, D.wf db -> kind (D.view db) f = Some OId ->
    (D.ids db <= D.ids (snd (D.make f k db)))%N.
  Proof.
    intros f k db Hwf Hkind. pose proof (D.make_spec f k db Hwf Hkind) as Hmake.
    destruct (D.make f k db) as [i next]. cbn [snd].
    destruct Hmake as [[j [_ [_ ->]]]|[Hfresh [_ [Hids _]]]]; [lia|].
    unfold D.fresh_id in Hfresh. rewrite Hids, Hfresh.
    replace (Npos (N.succ_pos (D.ids db))) with (N.succ (D.ids db))
      by (destruct (D.ids db); reflexivity).
    lia.
  Qed.

  (** A typed constructor action preserves the loaded state and returns an allocated name. *)
  Lemma run_make_state : forall p cp f k db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    program_kind p f = Some OId -> program_sorts p f = Some (map cell_sort k) ->
    (forall i, In (Id i) k -> D.allocated db i) ->
    D.wf (snd (D.make f k db)) /\ loaded p cp (snd (D.make f k db)) /\
    (D.ids db <= D.ids (snd (D.make f k db)))%N /\
    D.unit db <= D.unit (snd (D.make f k db)) /\
    D.allocated (snd (D.make f k db)) (fst (D.make f k db)) /\
    D.pending (snd (D.make f k db)) = D.pending db.
  Proof.
    intros p cp f k db Hchecked Hwf Hloaded Hkind Hsort Hallocated.
    assert (Hkinddb : kind (D.view db) f = Some OId) by (rewrite (proj1 Hloaded); exact Hkind).
    assert (Hfit : D.slots_fit db f (S (length k))).
    { eapply run_slots_fit; [exact Hchecked|exact Hloaded|exact Hsort|exact Hkind|].
      rewrite length_map. cbn. lia. }
    destruct (D.layout_make f k db Hwf) as [Hkinds [Hslots [_ [Hnew Hpending]]]].
    split; [apply D.wf_make; assumption|]. split.
    - destruct Hloaded as [Hdecls [Hlayout Hsorted]].
      split; [intro g; rewrite Hkinds; apply Hdecls|].
      split; [now rewrite Hslots|]. apply F22_make_sorted; assumption.
    - split; [apply run_make_ids; assumption|].
      split; [apply D.unit_mono_make; exact Hwf|]. split; assumption.
  Qed.

  (** A typed insertion preserves the loaded state and queues at most one entry. *)
  Lemma run_put_state : forall p cp f k o db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    row_sorted (program_sorts p) (program_kind p) f k o ->
    (forall i, In (Id i) (k ++ option_list o) -> D.allocated db i) ->
    D.wf (D.put f k o db) /\ loaded p cp (D.put f k o db) /\
    D.ids (D.put f k o db) = D.ids db /\ D.unit db <= D.unit (D.put f k o db) /\
    D.pending (D.put f k o db) <= D.pending db + 1.
  Proof.
    intros p cp f k o db Hchecked Hwf Hloaded Hrow Hallocated.
    pose proof (run_put_allowed p cp db f k o Hchecked Hloaded Hrow Hallocated) as Hallowed.
    destruct (D.layout_put f k o db Hwf) as [Hkinds [Hslots [Hids Hpending]]].
    split; [apply D.wf_put; assumption|]. split.
    - destruct Hloaded as [Hdecls [Hlayout Hsorted]].
      split; [intro g; rewrite Hkinds; apply Hdecls|]. split; [now rewrite Hslots|].
      apply F21_put_sorted; try assumption.
      destruct Hrow as [out [Hsort [Hkind Hout]]]. exists out.
      split; [exact Hsort|]. split; [rewrite Hdecls; exact Hkind|exact Hout].
    - split; [exact Hids|]. split; [apply D.unit_mono_put; exact Hwf|exact Hpending].
  Qed.

  (** An allocated union preserves the loaded state and queues at most one entry. *)
  Lemma run_union_state : forall p cp i j db,
    D.wf db -> loaded p cp db -> D.allocated db i -> D.allocated db j ->
    D.wf (D.union i j db) /\ loaded p cp (D.union i j db) /\
    D.ids (D.union i j db) = D.ids db /\ D.unit db <= D.unit (D.union i j db) /\
    D.pending (D.union i j db) <= D.pending db + 1.
  Proof.
    intros p cp i j db Hwf Hloaded Hi Hj.
    destruct (D.layout_union i j db Hwf) as [Hkinds [Hslots [Hids Hpending]]].
    split; [apply D.wf_union; assumption|]. split.
    - destruct Hloaded as [Hdecls [Hlayout Hsorted]].
      split; [intro g; rewrite Hkinds; apply Hdecls|]. split; [now rewrite Hslots|].
      apply F23_union_sorted; assumption.
    - split; [exact Hids|]. split; [apply D.unit_mono_union; exact Hwf|exact Hpending].
  Qed.

  (** Typed actions preserve loaded well-formed states and bound their pending work. *)
  Lemma run_apply_go_typed : forall p cp acts g s locals db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> env_allocated db (look s locals) ->
    D.wf (apply_go acts s locals db) /\ loaded p cp (apply_go acts s locals db) /\
    (D.ids db <= D.ids (apply_go acts s locals db))%N /\
    D.unit db <= D.unit (apply_go acts s locals db) /\
    D.pending (apply_go acts s locals db) <= D.pending db + length acts.
  Proof.
    intros p cp acts. induction acts as [|a rest IH]; intros g s locals db
      Hchecked Hwf Hloaded Hacts Henv Hallocated.
    - cbn [apply_go length]. split; [exact Hwf|]. split; [exact Hloaded|]. repeat split; lia.
    - destruct a as [x f args|f args res|t u|x op args]; cbn [actions_ok] in Hacts.
      + destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
        destruct (run_term_cells_typed g s locals args ss Henv Hargs)
          as [cells [Hcells Hsorts]].
        rewrite <- Hsorts in Hsort.
        pose proof (run_term_cells_allocated db s locals args cells Hallocated Hcells) as Hids.
        pose proof (run_make_state p cp f cells db Hchecked Hwf Hloaded Hkind Hsort Hids)
          as Hstate.
        destruct (D.make f cells db) as [i next] eqn:Hmake. cbn [fst snd] in Hstate.
        destruct Hstate as [Hwf' [Hloaded' [Hids' [Hunit' [Hnew Hpending]]]]].
        assert (Henv' : env_sorted (ctx_set g x SId)
            (look s (PTrieCode.set x (Id i) locals))).
        { apply run_env_sorted_set; [exact Henv|reflexivity]. }
        assert (Hallocated' : env_allocated next (look s (PTrieCode.set x (Id i) locals))).
        { apply run_env_allocated_set.
          - eapply run_env_allocated_mono; [exact Hids'|exact Hallocated].
          - intros j Heq. injection Heq as <-. exact Hnew. }
        destruct (IH _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv' Hallocated')
          as [Hfinal [Hloadfinal [Hidfinal [Hunitfinal Hpendfinal]]]].
        cbn [apply_go]. rewrite Hcells, Hmake.
        split; [exact Hfinal|]. split; [exact Hloadfinal|]. cbn [length]. repeat split; lia.
      + destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hresult Hrest]]]]]].
        destruct (run_term_cells_typed g s locals args ss Henv Hargs)
          as [cells [Hcells Hsorts]].
        destruct (run_result_cell_typed g s locals out res Henv Hresult)
          as [output [Houtput Houtsort]].
        assert (Hrow : row_sorted (program_sorts p) (program_kind p) f cells output).
        { exists out. rewrite Hsorts. repeat split; assumption. }
        assert (Hids : forall i, In (Id i) (cells ++ option_list output) -> D.allocated db i).
        { intros i Hin. apply in_app_iff in Hin as [Hin|Hin].
          - eapply run_term_cells_allocated; eauto.
          - eapply run_result_cell_allocated; eauto. }
        destruct (run_put_state p cp f cells output db Hchecked Hwf Hloaded Hrow Hids)
          as [Hwf' [Hloaded' [Hids' [Hunit' Hpending]]]].
        assert (Hallocated' : env_allocated (D.put f cells output db) (look s locals)).
        { eapply run_env_allocated_mono with (db := db);
            [rewrite Hids'; reflexivity|exact Hallocated]. }
        destruct (IH _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated')
          as [Hfinal [Hloadfinal [Hidfinal [Hunitfinal Hpendfinal]]]].
        cbn [apply_go]. rewrite Hcells, Houtput.
        split; [exact Hfinal|]. split; [exact Hloadfinal|]. cbn [length]. repeat split; lia.
      + destruct Hacts as [Ht [Hu Hrest]].
        destruct (run_term_cell_typed g s locals t SId Henv Ht)
          as [[i|v] [Hi Hitype]]; [|discriminate].
        destruct (run_term_cell_typed g s locals u SId Henv Hu)
          as [[j|v] [Hj Hjtype]]; [|discriminate].
        pose proof (run_term_cell_allocated db s locals t i Hallocated Hi) as Hiall.
        pose proof (run_term_cell_allocated db s locals u j Hallocated Hj) as Hjall.
        destruct (run_union_state p cp i j db Hwf Hloaded Hiall Hjall)
          as [Hwf' [Hloaded' [Hids' [Hunit' Hpending]]]].
        assert (Hallocated' : env_allocated (D.union i j db) (look s locals)).
        { eapply run_env_allocated_mono with (db := db);
            [rewrite Hids'; reflexivity|exact Hallocated]. }
        destruct (IH _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated')
          as [Hfinal [Hloadfinal [Hidfinal [Hunitfinal Hpendfinal]]]].
        cbn [apply_go]. rewrite Hi, Hj.
        split; [exact Hfinal|]. split; [exact Hloadfinal|]. cbn [length]. repeat split; lia.
      + destruct Hacts as [Hargs Hrest].
        destruct (run_term_values_typed g s locals args Henv Hargs) as [vs Hvalues].
        cbn [apply_go]. rewrite Hvalues. destruct (V.prim op vs) as [v|] eqn:Hprim.
        * assert (Henv' : env_sorted (ctx_set g x SVal)
              (look s (PTrieCode.set x (Val v) locals))).
          { apply run_env_sorted_set; [exact Henv|reflexivity]. }
          assert (Hallocated' : env_allocated db (look s (PTrieCode.set x (Val v) locals))).
          { apply run_env_allocated_set; [exact Hallocated|]. intros i Heq. discriminate. }
          destruct (IH _ _ _ _ Hchecked Hwf Hloaded Hrest Henv' Hallocated')
            as [Hfinal [Hloadfinal [Hidfinal [Hunitfinal Hpendfinal]]]].
          split; [exact Hfinal|]. split; [exact Hloadfinal|]. cbn [length]. repeat split; lia.
        * split; [exact Hwf|]. split; [exact Hloaded|]. cbn [length]. repeat split; lia.
  Qed.

  (** The public action entry starts the typed action invariant with no locals. *)
  Lemma run_apply_typed : forall p cp acts g s db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts -> env_sorted g s ->
    env_allocated db s ->
    D.wf (apply acts s db) /\ loaded p cp (apply acts s db) /\
    (D.ids db <= D.ids (apply acts s db))%N /\ D.unit db <= D.unit (apply acts s db) /\
    D.pending (apply acts s db) <= D.pending db + length acts.
  Proof.
    intros p cp acts g s db Hchecked Hwf Hloaded Hacts Henv Hallocated.
    unfold apply. eapply run_apply_go_typed; try eassumption.
    - intros x ty Hctx. destruct (Henv x ty Hctx) as [c [Hc Hty]].
      exists c. rewrite run_look_empty. split; assumption.
    - intros x i Hcell. rewrite run_look_empty in Hcell. eapply Hallocated. exact Hcell.
  Qed.

  Lemma F3_apply_wf : forall p cp r s db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    In r (rules V.t p) -> rule_env (program_sorts p) (program_kind p) r s ->
    env_allocated db s ->
    D.wf (apply (actions V.t r) s db) /\ loaded p cp (apply (actions V.t r) s db) /\
    (D.ids db <= D.ids (apply (actions V.t r) s db))%N /\
    D.unit db <= D.unit (apply (actions V.t r) s db).
  Proof.
    intros p cp r s db Hchecked Hwf Hloaded Hin Henv Hallocated.
    destruct (run_rule_context p cp r s Hchecked Hin Henv) as [g [_ [Hacts Hsorted]]].
    destruct (run_apply_typed p cp (actions V.t r) g s db Hchecked Hwf Hloaded Hacts
      Hsorted Hallocated) as [Hwf' [Hloaded' [Hids [Hunit _]]]].
    split; [exact Hwf'|]. split; [exact Hloaded'|]. split; assumption.
  Qed.

  (** Applying a rule queues at most one pending entry per action. *)
  Lemma F34_apply_pending : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    D.pending (apply (actions V.t r) s db) <= D.pending db + length (actions V.t r).
  Proof.
    intros p cp r s db Hchecked Hwf Hloaded Hin Henv Hallocated.
    destruct (run_rule_context p cp r s Hchecked Hin Henv) as [g [_ [Hacts Hsorted]]].
    exact (proj2 (proj2 (proj2 (proj2 (run_apply_typed p cp (actions V.t r) g s db
      Hchecked Hwf Hloaded Hacts Hsorted Hallocated))))).
  Qed.

  (** Interpreting a concrete term preserves its environment lookup. *)
  Lemma run_model_term : forall (M : model (V := V.t)) nu s t c,
    term_value s t c ->
    model_term M (fun x => option_map (den nu) (s x)) t (den nu c).
  Proof.
    intros M nu s [x|v] c Hterm; cbn [term_value model_term] in *.
    - now rewrite Hterm.
    - subst c. reflexivity.
  Qed.

  (** Interpreting an argument list preserves each term witness. *)
  Lemma run_model_terms : forall (M : model (V := V.t)) nu s ts cs,
    terms_value s ts cs ->
    Forall2 (model_term M (fun x => option_map (den nu) (s x))) ts (map (den nu) cs).
  Proof.
    intros M nu s ts cs Hterms. induction Hterms; cbn [map]; constructor; auto.
    now apply run_model_term.
  Qed.

  (** Value-only argument lists have the same primitive inputs after interpretation. *)
  Lemma run_model_values : forall (M : model (V := V.t)) nu cs vs,
    values cs vs -> model_values M (map (den nu) cs) vs.
  Proof.
    intros M nu cs vs Hvalues. induction Hvalues; cbn [map]; constructor; auto.
    subst x. reflexivity.
  Qed.

  (** Every satisfied concrete query atom is true in a model of its view. *)
  Lemma run_model_atom : forall (M : model (V := V.t)) nu w kinds s a,
    (forall f, kind w f = kinds f) -> sat V.merge M nu w ->
    atom_holds V.prim w s a ->
    model_atom V.prim M kinds (fun x => option_map (den nu) (s x)) a.
  Proof.
    intros M nu w kinds s [f args res|p args res] Hkind [Hrows Hsat] Hatom;
      cbn [atom_holds model_atom] in *.
    - destruct Hatom as [k [o [Hterms [Hresult Hrow]]]].
      exists (map (den nu) k). split; [now apply run_model_terms|].
      specialize (Hrows f k o Hrow). unfold holds in Hrows. rewrite Hkind in Hrows.
      destruct (kinds f) as [out|]; [|contradiction].
      destruct out; destruct o as [[i|v]|]; cbn in Hrows; try contradiction.
      + destruct res as [t|]; [contradiction|exact Hrows].
      + destruct res as [t|]; [|contradiction]. rewrite Hrows.
        exact (run_model_term M nu s t (Id i) Hresult).
      + destruct res as [t|]; [|contradiction]. exists v. split.
        * exact (run_model_term M nu s t (Val v) Hresult).
        * exact Hrows.
    - destruct Hatom as [k [vs [v [Hterms [Hvalues [Hprim Hresult]]]]]].
      exists (map (den nu) k), vs, v. split; [now apply run_model_terms|].
      split; [now apply run_model_values|]. split; [exact Hprim|].
      exact (run_model_term M nu s res (Val v) Hresult).
  Qed.

  Lemma F4a_match_model : forall (M : model (V := V.t)) nu p cp db q s,
    D.wf db -> loaded p cp db -> sat V.merge M nu (D.view db) ->
    matches V.prim (D.view db) q s ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x))) q.
  Proof.
    intros M nu p cp db q s Hwf [Hkind Hloaded] Hsat Hmatch.
    eapply Forall_impl; [|exact Hmatch]. intros a Hatom.
    eapply run_model_atom; eassumption.
  Qed.


  (** A concrete term determines its value in the interpreted environment. *)
  Lemma run_model_term_unique : forall (M : model (V := V.t)) nu s t c value,
    term_value s t c -> model_term M (fun x => option_map (den nu) (s x)) t value ->
    value = den nu c.
  Proof.
    intros M nu s [x|v] c value Hcell Hvalue; cbn [term_value model_term] in *.
    - rewrite Hcell in Hvalue. now injection Hvalue.
    - subst c value. reflexivity.
  Qed.

  (** Concrete argument witnesses determine the model's argument list. *)
  Lemma run_model_terms_unique : forall (M : model (V := V.t)) nu s ts cs values,
    terms_value s ts cs ->
    Forall2 (model_term M (fun x => option_map (den nu) (s x))) ts values ->
    values = map (den nu) cs.
  Proof.
    intros M nu s ts cs values Hterms. revert values.
    induction Hterms as [|t c rest cells Hterm Hterms IH]; intros vals Hvals.
    - inversion Hvals. reflexivity.
    - inversion Hvals as [|t' v rest' vals' Hvalue Htail]; subst t' rest' vals.
      cbn [map]. f_equal; [eapply run_model_term_unique; eassumption|now apply IH].
  Qed.

  (** Concrete value arguments determine the primitive inputs in the model. *)
  Lemma run_model_values_unique : forall (M : model (V := V.t)) nu cs vs ws,
    values cs vs -> model_values M (map (den nu) cs) ws -> ws = vs.
  Proof.
    intros M nu cs vs ws Hvalues. revert ws.
    induction Hvalues as [|c v cells vals Hcell Hvalues IH]; intros ws Hmodel.
    - inversion Hmodel. reflexivity.
    - subst c. inversion Hmodel as [|c' w cells' ws' Hhead Htail]; subst c' cells' ws.
      cbn [den] in Hhead. injection Hhead as <-. f_equal. now apply IH.
  Qed.

  (** Interpreting a sorted environment preserves its sorts. *)
  Lemma run_model_env_sorted : forall (M : model (V := V.t)) nu g s,
    env_sorted g s -> model_env_sorted M g (fun x => option_map (den nu) (s x)).
  Proof.
    intros M nu g s Henv x ty Htype.
    destruct (Henv x ty Htype) as [c [Hlookup Hsort]].
    exists (den nu c). rewrite Hlookup. split; [reflexivity|].
    destruct c; exact Hsort.
  Qed.

  (** Pointwise agreement preserves a model term. *)
  Lemma run_model_term_agree : forall (M : model (V := V.t)) s t term value,
    (forall x, s x = t x) -> model_term M s term value -> model_term M t term value.
  Proof.
    intros M s t [x|v] value Henv Hterm.
    - cbn [model_term] in *. now rewrite <- Henv.
    - exact Hterm.
  Qed.

  (** Pointwise agreement preserves a list of model terms. *)
  Lemma run_model_terms_agree : forall (M : model (V := V.t)) s t terms values,
    (forall x, s x = t x) -> Forall2 (model_term M s) terms values ->
    Forall2 (model_term M t) terms values.
  Proof.
    intros M s t terms values Henv Hterms. induction Hterms; constructor; auto.
    eapply run_model_term_agree; eassumption.
  Qed.

  (** A common assignment preserves pointwise model-environment agreement. *)
  Lemma run_model_update_agree : forall (M : model (V := V.t)) s t x c,
    (forall y, s y = t y) ->
    forall y, model_update M s x c y = model_update M t x c y.
  Proof.
    intros M s t x c Henv y. unfold model_update. destruct (Pos.eqb x y); auto.
  Qed.

  (** Model action semantics depends only on pointwise environment observations. *)
  Lemma run_model_actions_agree : forall (M : model (V := V.t)) kinds acts s t,
    (forall x, s x = t x) -> model_actions V.prim M kinds s acts ->
    model_actions V.prim M kinds t acts.
  Proof.
    intros M kinds acts. induction acts as [|a rest IH]; intros s t Henv Hacts;
      [exact I|].
    destruct a as [x f args|f args res|a b|x p args]; cbn [model_actions] in *.
    - destruct Hacts as [k [Hargs [Hkind Hrest]]]. exists k. split.
      + eapply run_model_terms_agree; eassumption.
      + split; [exact Hkind|]. eapply IH; [apply run_model_update_agree; exact Henv|exact Hrest].
    - destruct Hacts as [k [Hargs [Hput Hrest]]]. exists k. split.
      + eapply run_model_terms_agree; eassumption.
      + split; [|eapply IH; eassumption].
        destruct (kinds f) as [out|]; [|contradiction].
        destruct out; destruct res as [term|]; try contradiction; try exact Hput.
        * eapply run_model_term_agree; eassumption.
        * destruct Hput as [v [Hterm Hlat]]. exists v. split;
            [eapply run_model_term_agree; eassumption|exact Hlat].
    - destruct Hacts as [c [d [Ha [Hb [Hsame Hrest]]]]]. exists c, d. split.
      + eapply run_model_term_agree; eassumption.
      + split; [eapply run_model_term_agree; eassumption|].
        split; [exact Hsame|eapply IH; eassumption].
    - destruct Hacts as [k [vs [Hargs [Hvalues Hrest]]]]. exists k, vs. split.
      + eapply run_model_terms_agree; eassumption.
      + split; [exact Hvalues|]. destruct (V.prim p vs); [|exact I].
        eapply IH; [apply run_model_update_agree; exact Henv|exact Hrest].
  Qed.

  (** A true model function atom justifies the corresponding concrete insertion. *)
  Lemma run_model_fun_holds : forall (M : model (V := V.t)) nu s w kinds f args res k o,
    (forall g, kind w g = kinds g) -> terms_value s args k ->
    (match res, o with
     | None, None => True
     | Some t, Some c => term_value s t c
     | _, _ => False
     end) ->
    model_atom V.prim M kinds (fun x => option_map (den nu) (s x))
      (Fun V.t f args res) -> holds M nu w f k o.
  Proof.
    intros M nu s w kinds f args res k o Hkind Hargs Hres [vals [Hvals Hhead]].
    pose proof (run_model_terms_unique M nu s args k vals Hargs Hvals) as Hlist.
    subst vals. unfold holds. rewrite Hkind.
    destruct (kinds f) as [out|]; [|contradiction].
    destruct out; destruct res as [term|]; try contradiction.
    - destruct o; [contradiction|exact Hhead].
    - destruct o as [[i|v]|]; [| |contradiction].
      + pose proof (run_model_term_unique M nu s term (Id i) _ Hres Hhead) as Hvalue.
        now injection Hvalue.
      + pose proof (run_model_term_unique M nu s term (Val v) _ Hres Hhead) as Hvalue.
        discriminate Hvalue.
    - destruct Hhead as [v [Hterm Hlat]]. destruct o as [[i|w']|]; [| |contradiction].
      + pose proof (run_model_term_unique M nu s term (Id i) _ Hres Hterm) as Hvalue.
        discriminate Hvalue.
      + pose proof (run_model_term_unique M nu s term (Val w') _ Hres Hterm) as Hvalue.
        injection Hvalue as ->. exact Hlat.
  Qed.

  (** Canonical representatives have their identifiers' original model meaning. *)
  Lemma run_canon_den : forall (M : model (V := V.t)) nu db c,
    D.wf db -> sat V.merge M nu (D.view db) -> den nu (D.canon db c) = den nu c.
  Proof.
    intros M nu db [i|v] Hwf [_ [Hsame Hlat]]; [|reflexivity].
    cbn [D.canon den]. f_equal. apply Hsame.
    apply (proj2 (D.same_repr db (D.repr db i) i Hwf)). now rewrite D.repr_idem.
  Qed.

  (** Canonicalizing arguments preserves their full interpreted key. *)
  Lemma run_canon_key_den : forall (M : model (V := V.t)) nu db k,
    D.wf db -> sat V.merge M nu (D.view db) ->
    map (den nu) (map (D.canon db) k) = map (den nu) k.
  Proof.
    intros M nu db k Hwf Hsat. rewrite map_map. apply map_ext.
    intro c. now apply run_canon_den.
  Qed.

  (** Constructor allocation extends the interpretation of every old allocated identifier. *)
  Lemma run_make_model : forall (M : model (V := V.t)) nu db f k i next,
    D.wf db -> kind (D.view db) f = Some OId ->
    (forall j, In (Id j) k -> D.allocated db j) -> sat V.merge M nu (D.view db) ->
    D.make f k db = (i, next) ->
    exists nu', extends db M nu nu' /\
      nu' i = con M f (map (den nu) k) /\ sat V.merge M nu' (D.view next).
  Proof.
    intros M nu db f k i next Hwf Hkind Hallocated Hsat Hmake.
    pose proof (D.make_spec f k db Hwf Hkind) as Hspec.
    pose proof (D.make_sat M nu db f k Hwf Hkind Hallocated Hsat) as Hmodel.
    rewrite Hmake in Hspec, Hmodel.
    destruct Hmodel as [nu' [Hother [Hmeaning Hsat']]].
    exists nu'. split; [|split; assumption].
    intros j Hj. destruct (Pos.eq_dec j i) as [->|Hdifferent]; [|now apply Hother].
    destruct Hspec as [[old [Hrow [Hrepr Hnext]]]|[Hfresh Hnew]].
    - pose proof (proj1 Hsat f (map (D.canon db) k) (Some (Id old)) Hrow) as Hholds.
      unfold holds in Hholds. rewrite Hkind in Hholds.
      rewrite (run_canon_key_den M nu db k Hwf Hsat) in Hholds.
      rewrite Hmeaning, Hholds, Hrepr.
      destruct Hsat as [_ [Hequal _]]. symmetry. apply Hequal.
      apply (proj2 (D.same_repr db (D.repr db old) old Hwf)). now rewrite D.repr_idem.
    - unfold D.fresh_id in Hfresh. unfold D.allocated in Hj. rewrite Hfresh in Hj.
      rewrite N.succ_pos_spec in Hj. lia.
  Qed.

  (** An interpretation extension preserves every allocated environment observation. *)
  Lemma run_env_den_ext : forall (M : model (V := V.t)) nu nu' db s,
    extends db M nu nu' -> env_allocated db s ->
    forall x, option_map (den nu') (s x) = option_map (den nu) (s x).
  Proof.
    intros M nu nu' db s Hext Hallocated x. destruct (s x) as [[i|v]|] eqn:Hlookup;
      [|reflexivity|reflexivity].
    cbn [option_map den]. rewrite Hext; [reflexivity|eapply Hallocated; exact Hlookup].
  Qed.

  (** Extensions through growing identifier counters compose on the original allocation. *)
  Lemma run_extends_trans : forall (M : model (V := V.t)) before middle nu nu' nu'',
    (D.ids before <= D.ids middle)%N -> extends before M nu nu' ->
    extends middle M nu' nu'' -> extends before M nu nu''.
  Proof.
    intros M before middle nu nu' nu'' Hids Hfirst Hsecond i Hallocated.
    rewrite Hsecond; [now apply Hfirst|]. unfold D.allocated in *. lia.
  Qed.

  (** Executing true typed actions preserves a model while extending allocated meanings. *)
  Lemma run_apply_go_sat : forall p cp (M : model (V := V.t)) acts g s locals db nu,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> env_allocated db (look s locals) ->
    model_actions V.prim M (program_kind p)
      (fun x => option_map (den nu) (look s locals x)) acts ->
    sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\ sat V.merge M nu' (D.view (apply_go acts s locals db)).
  Proof.
    intros p cp M acts. induction acts as [|a rest IH]; intros g s locals db nu
      Hchecked Hwf Hloaded Hacts Henv Hallocated Hmodel Hsat.
    - exists nu. split; [intros i Hi; reflexivity|exact Hsat].
    - destruct a as [x f args|f args res|t u|x op args];
        cbn [actions_ok] in Hacts; cbn [model_actions] in Hmodel.
      + destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
        destruct (run_term_cells_typed g s locals args ss Henv Hargs)
          as [cells [Hcells Hsorts]].
        rewrite <- Hsorts in Hsort.
        pose proof (run_term_cells_allocated db s locals args cells Hallocated Hcells) as Hids.
        destruct Hmodel as [vals [Hvals [Hmodelkind Hmodelrest]]].
        pose proof (run_model_terms_unique M nu (look s locals) args cells vals
          (proj1 (run_term_cells_spec s locals args cells) Hcells) Hvals) as Hargsmodel.
        subst vals.
        pose proof (run_make_state p cp f cells db Hchecked Hwf Hloaded Hkind Hsort Hids)
          as Hstate.
        destruct (D.make f cells db) as [i next] eqn:Hmake. cbn [fst snd] in Hstate.
        destruct Hstate as [Hwf' [Hloaded' [Hids' [Hunit' [Hnew Hpending]]]]].
        assert (Hkinddb : kind (D.view db) f = Some OId).
        { rewrite (proj1 Hloaded). exact Hkind. }
        destruct (run_make_model M nu db f cells i next Hwf Hkinddb Hids Hsat Hmake)
          as [middle [Hextension [Hmeaning Hsat']]].
        assert (Henv' : env_sorted (ctx_set g x SId)
            (look s (PTrieCode.set x (Id i) locals))).
        { apply run_env_sorted_set; [exact Henv|reflexivity]. }
        assert (Hallocated' : env_allocated next (look s (PTrieCode.set x (Id i) locals))).
        { apply run_env_allocated_set.
          - eapply run_env_allocated_mono; [exact Hids'|exact Hallocated].
          - intros j Heq. injection Heq as <-. exact Hnew. }
        assert (Hmodel' : model_actions V.prim M (program_kind p)
            (fun y => option_map (den middle) (look s (PTrieCode.set x (Id i) locals) y)) rest).
        { eapply run_model_actions_agree; [|exact Hmodelrest].
          intro y. rewrite run_look_set. unfold model_update, update.
          destruct (Pos.eqb x y).
          - cbn [option_map den]. now rewrite Hmeaning.
          - symmetry. eapply run_env_den_ext; eassumption. }
        destruct (IH _ _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv' Hallocated' Hmodel' Hsat')
          as [final [Hfinal Hsatfinal]].
        cbn [apply_go]. rewrite Hcells, Hmake. exists final. split.
        * eapply run_extends_trans; eassumption.
        * exact Hsatfinal.
      + destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hresult Hrest]]]]]].
        destruct (run_term_cells_typed g s locals args ss Henv Hargs)
          as [cells [Hcells Hsorts]].
        destruct (run_result_cell_typed g s locals out res Henv Hresult)
          as [output [Houtput Houtsort]].
        assert (Hrow : row_sorted (program_sorts p) (program_kind p) f cells output).
        { exists out. rewrite Hsorts. repeat split; assumption. }
        assert (Hids : forall i, In (Id i) (cells ++ option_list output) -> D.allocated db i).
        { intros i Hin. apply in_app_iff in Hin as [Hin|Hin].
          - eapply run_term_cells_allocated; eauto.
          - eapply run_result_cell_allocated; eauto. }
        pose proof (run_put_allowed p cp db f cells output Hchecked Hloaded Hrow Hids)
          as Hallowed.
        destruct (run_put_state p cp f cells output db Hchecked Hwf Hloaded Hrow Hids)
          as [Hwf' [Hloaded' [Hids' [Hunit' Hpending]]]].
        destruct Hmodel as [vals [Hvals [Hput Hmodelrest]]].
        assert (Hholds : holds M nu (D.view db) f cells output).
        { eapply run_model_fun_holds.
          - exact (proj1 Hloaded).
          - apply run_term_cells_spec. exact Hcells.
          - apply run_result_cell_spec. exact Houtput.
          - exists vals. split; assumption. }
        pose proof (D.put_sat M nu db f cells output Hwf Hallowed Hsat Hholds) as Hsat'.
        assert (Hallocated' : env_allocated (D.put f cells output db) (look s locals)).
        { eapply run_env_allocated_mono with (db := db);
            [rewrite Hids'; reflexivity|exact Hallocated]. }
        destruct (IH _ _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated' Hmodelrest Hsat')
          as [final [Hfinal Hsatfinal]].
        cbn [apply_go]. rewrite Hcells, Houtput. exists final. split.
        * intros i Hi. apply Hfinal. unfold D.allocated in *. now rewrite Hids'.
        * exact Hsatfinal.
      + destruct Hacts as [Ht [Hu Hrest]].
        destruct (run_term_cell_typed g s locals t SId Henv Ht)
          as [[i|v] [Hi Hitype]]; [|discriminate].
        destruct (run_term_cell_typed g s locals u SId Henv Hu)
          as [[j|v] [Hj Hjtype]]; [|discriminate].
        pose proof (run_term_cell_allocated db s locals t i Hallocated Hi) as Hiall.
        pose proof (run_term_cell_allocated db s locals u j Hallocated Hj) as Hjall.
        destruct (run_union_state p cp i j db Hwf Hloaded Hiall Hjall)
          as [Hwf' [Hloaded' [Hids' [Hunit' Hpending]]]].
        destruct Hmodel as [a [b [Hma [Hmb [Hequal Hmodelrest]]]]].
        pose proof (run_model_term_unique M nu (look s locals) t (Id i) a
          (proj1 (run_term_cell_spec s locals t (Id i)) Hi) Hma) as Ha.
        pose proof (run_model_term_unique M nu (look s locals) u (Id j) b
          (proj1 (run_term_cell_spec s locals u (Id j)) Hj) Hmb) as Hb.
        rewrite Ha, Hb in Hequal. change (nu i = nu j) in Hequal.
        pose proof (D.union_sat M nu db i j Hwf Hsat Hequal) as Hsat'.
        assert (Hallocated' : env_allocated (D.union i j db) (look s locals)).
        { eapply run_env_allocated_mono with (db := db);
            [rewrite Hids'; reflexivity|exact Hallocated]. }
        destruct (IH _ _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated' Hmodelrest Hsat')
          as [final [Hfinal Hsatfinal]].
        cbn [apply_go]. rewrite Hi, Hj. exists final. split.
        * intros k Hk. apply Hfinal. unfold D.allocated in *. now rewrite Hids'.
        * exact Hsatfinal.
      + destruct Hacts as [Hargs Hrest].
        destruct (run_term_values_typed g s locals args Henv Hargs) as [vs Hvalues].
        destruct Hmodel as [vals [inputs [Hvals [Hinputs Hmodelrest]]]].
        pose proof (run_term_values_spec s locals args vs Hvalues) as Hcells.
        pose proof (run_model_terms_unique M nu (look s locals) args (map Val vs) vals
          Hcells Hvals) as Hlist. subst vals.
        pose proof (run_model_values_unique M nu (map Val vs) vs inputs
          (run_value_cells vs) Hinputs) as Hinputs_eq. subst inputs.
        cbn [apply_go]. rewrite Hvalues. destruct (V.prim op vs) as [v|] eqn:Hprim.
        * assert (Henv' : env_sorted (ctx_set g x SVal)
              (look s (PTrieCode.set x (Val v) locals))).
          { apply run_env_sorted_set; [exact Henv|reflexivity]. }
          assert (Hallocated' : env_allocated db (look s (PTrieCode.set x (Val v) locals))).
          { apply run_env_allocated_set; [exact Hallocated|]. intros i Heq. discriminate. }
          assert (Hmodel' : model_actions V.prim M (program_kind p)
              (fun y => option_map (den nu) (look s (PTrieCode.set x (Val v) locals) y)) rest).
          { eapply run_model_actions_agree; [|exact Hmodelrest].
            intro y. rewrite run_look_set. unfold model_update, update.
            destruct (Pos.eqb x y); reflexivity. }
          destruct (IH _ _ _ _ _ Hchecked Hwf Hloaded Hrest Henv' Hallocated' Hmodel' Hsat)
            as [final [Hfinal Hsatfinal]].
          exists final. split; assumption.
        * exists nu. split; [intros i Hi; reflexivity|exact Hsat].
  Qed.

  Lemma F4_apply_sat : forall (M : model (V := V.t)) nu p cp r s db,
    plans_ok p cp -> D.wf db -> loaded p cp db -> env_allocated db s ->
    rule_env (program_sorts p) (program_kind p) r s ->
    valid_sorted V.prim V.merge M p -> In r (rules V.t p) ->
    Forall (model_atom V.prim M (program_kind p) (fun x => option_map (den nu) (s x)))
      (query V.t r) ->
    sat V.merge M nu (D.view db) ->
    exists nu', extends db M nu nu' /\
      sat V.merge M nu' (D.view (apply (actions V.t r) s db)).
  Proof.
    intros M nu p cp r s db Hchecked Hwf Hloaded Hallocated Henv [Hvalid Hlat] Hin
      Hmatch Hsat.
    destruct (run_rule_context p cp r s Hchecked Hin Henv) as [g [Hquery [Hacts Hsorted]]].
    pose proof ((proj1 (Forall_forall _ _)) Hvalid r Hin) as Hrule.
    specialize (Hrule g (fun x => option_map (den nu) (s x)) Hquery
      (run_model_env_sorted M nu g s Hsorted) Hmatch).
    unfold apply. eapply run_apply_go_sat;
      [exact Hchecked|exact Hwf|exact Hloaded|exact Hacts| | | |exact Hsat].
    - intros x ty Hctx. destruct (Hsorted x ty Hctx) as [c [Hc Hty]].
      exists c. rewrite run_look_empty. split; assumption.
    - intros x i Hcell. rewrite run_look_empty in Hcell. eapply Hallocated. exact Hcell.
    - eapply run_model_actions_agree; [|exact Hrule].
      intro x. now rewrite run_look_empty.
  Qed.


  (** Database equality is reflexive on every identifier. *)
  Lemma run_same_refl : forall db i, D.wf db -> same (D.view db) i i.
  Proof.
    intros db i Hwf. apply (proj2 (D.same_repr db i i Hwf)). reflexivity.
  Qed.

  (** Database equality composes through representatives. *)
  Lemma run_same_trans : forall db i j k, D.wf db ->
    same (D.view db) i j -> same (D.view db) j k -> same (D.view db) i k.
  Proof.
    intros db i j k Hwf Hij Hjk. apply (proj2 (D.same_repr db i k Hwf)).
    apply (proj1 (D.same_repr db i j Hwf)) in Hij.
    apply (proj1 (D.same_repr db j k Hwf)) in Hjk. congruence.
  Qed.

  (** Canonicalizing the source output leaves output containment unchanged. *)
  Lemma run_out_canon_left : forall db f a b, D.wf db ->
    (D.out_le db f (option_map (D.canon db) a) b <-> D.out_le db f a b).
  Proof.
    intros db f [[i|a]|] [[j|b]|] Hwf;
      cbn [D.out_le option_map D.canon cell_le]; try reflexivity.
    rewrite (D.same_repr db (D.repr db i) j Hwf), (D.same_repr db i j Hwf).
    now rewrite D.repr_idem.
  Qed.

  (** Enlarging equality while keeping kinds preserves output containment. *)
  Lemma run_out_le_mono : forall db next f a b,
    (forall g, kind (D.view next) g = kind (D.view db) g) ->
    (forall i j, same (D.view db) i j -> same (D.view next) i j) ->
    D.out_le db f a b -> D.out_le next f a b.
  Proof.
    intros db next f [[i|a]|] [[j|b]|] Hkind Hsame Hle;
      cbn [D.out_le cell_le] in *; try contradiction; try exact I.
    - now apply Hsame.
    - destruct Hle as [m [Hdecl Hmerge]]. exists m.
      split; [now rewrite Hkind|exact Hmerge].
  Qed.

  (** Output containment composes using equality and the semilattice merge laws. *)
  Lemma run_out_le_trans : forall db f a b c, D.wf db ->
    D.out_le db f a b -> D.out_le db f b c -> D.out_le db f a c.
  Proof.
    intros db f [a|] [b|] [c|] Hwf Hab Hbc;
      cbn [D.out_le] in *; try contradiction; try exact I.
    destruct a as [i|a], b as [j|b], c as [k|c]; cbn [cell_le] in *; try contradiction.
    - eapply run_same_trans; eassumption.
    - destruct Hab as [m [Hkind Hab]], Hbc as [n [Hkind' Hbc]].
      assert (Hequal : m = n) by congruence. subst n. exists m. split; [exact Hkind|].
      rewrite <- Hbc at 1. rewrite V.merge_assoc, Hab. exact Hbc.
  Qed.

  (** Enlarging identifier equality preserves a related pair of cells. *)
  Lemma run_cell_rel_mono : forall db next (a b : cell V.t),
    (forall i j, same (D.view db) i j -> same (D.view next) i j) ->
    cell_rel (same (D.view db)) a b -> cell_rel (same (D.view next)) a b.
  Proof.
    intros db next a b Hsame Hrel. destruct Hrel; constructor; auto.
  Qed.

  (** Enlarging identifier equality preserves related keys. *)
  Lemma run_key_rel_mono : forall db next (a b : list (cell V.t)),
    (forall i j, same (D.view db) i j -> same (D.view next) i j) ->
    Forall2 (cell_rel (same (D.view db))) a b ->
    Forall2 (cell_rel (same (D.view next))) a b.
  Proof.
    intros db next a b Hsame Hrel. induction Hrel; constructor; auto.
    eapply run_cell_rel_mono; eassumption.
  Qed.

  (** Every key is related to itself in a well-formed database. *)
  Lemma run_key_rel_refl : forall db (k : list (cell V.t)), D.wf db ->
    Forall2 (cell_rel (same (D.view db))) k k.
  Proof.
    intros db k Hwf. induction k as [|c rest IH]; [constructor|].
    constructor; [|exact IH]. destruct c as [i|v].
    - constructor. now apply run_same_refl.
    - constructor.
  Qed.

  (** Cell relatedness composes in a well-formed database. *)
  Lemma run_cell_rel_trans : forall db (a b c : cell V.t), D.wf db ->
    cell_rel (same (D.view db)) a b -> cell_rel (same (D.view db)) b c ->
    cell_rel (same (D.view db)) a c.
  Proof.
    intros db a b c Hwf Hab Hbc. destruct Hab.
    - inversion Hbc; subst. constructor. eapply run_same_trans; eassumption.
    - inversion Hbc; subst. constructor.
  Qed.

  (** Key relatedness composes in a well-formed database. *)
  Lemma run_key_rel_trans : forall db (a b c : list (cell V.t)), D.wf db ->
    Forall2 (cell_rel (same (D.view db))) a b ->
    Forall2 (cell_rel (same (D.view db))) b c ->
    Forall2 (cell_rel (same (D.view db))) a c.
  Proof.
    intros db a b c Hwf Hab. revert c.
    induction Hab as [|a b rest more Hab Hrest IH]; intros c Hbc.
    - inversion Hbc. constructor.
    - inversion Hbc as [|b' c' more' tail Hhead Htail]; subst b' more' c.
      constructor; [eapply run_cell_rel_trans; eassumption|now apply IH].
  Qed.

  (** A well-sorted row contains its own output. *)
  Lemma run_row_out_refl : forall sorts db f k o, D.wf db ->
    row_sorted sorts (kind (D.view db)) f k o ->
    D.out_le db f (option_map (D.canon db) o) o.
  Proof.
    intros sorts db f k o Hwf [out [_ [Hkind Hout]]].
    apply (proj2 (run_out_canon_left db f o o Hwf)).
    destruct o as [[i|v]|]; cbn [D.out_le cell_le]; [now apply run_same_refl| |exact I].
    destruct out as [| |m]; cbn [out_sort option_map cell_sort] in Hout; try discriminate.
    exists m. split; [exact Hkind|apply V.merge_idem].
  Qed.

  (** A sorted database grows to itself. *)
  Lemma run_grows_upto_refl : forall sorts db, D.wf db ->
    view_sorted sorts (D.view db) -> grows_upto db db.
  Proof.
    intros sorts db Hwf Hsorted. split; [auto|]. intros f k o Hrow.
    exists k, o. split; [exact Hrow|]. split; [now apply run_key_rel_refl|].
    eapply run_row_out_refl; [exact Hwf|eapply Hsorted; exact Hrow].
  Qed.

  (** Growth composes when later states keep kinds and remain well formed. *)
  Lemma run_grows_upto_trans : forall before middle after,
    D.wf middle -> D.wf after ->
    (forall f, kind (D.view after) f = kind (D.view middle) f) ->
    grows_upto before middle -> grows_upto middle after -> grows_upto before after.
  Proof.
    intros before middle after Hwfmid Hwfafter Hkinds [Hsame1 Hrows1] [Hsame2 Hrows2].
    split; [intros i j Hsame; apply Hsame2; now apply Hsame1|].
    intros f k o Hrow. destruct (Hrows1 f k o Hrow) as [k1 [o1 [Hrow1 [Hkey1 Hout1]]]].
    destruct (Hrows2 f k1 o1 Hrow1) as [k2 [o2 [Hrow2 [Hkey2 Hout2]]]].
    exists k2, o2. split; [exact Hrow2|]. split.
    - eapply run_key_rel_trans; [exact Hwfafter| |exact Hkey2].
      eapply run_key_rel_mono; eassumption.
    - apply (proj2 (run_out_canon_left after f o o2 Hwfafter)).
      eapply run_out_le_trans; [exact Hwfafter| |].
      + eapply run_out_le_mono; [exact Hkinds|exact Hsame2|].
        exact (proj1 (run_out_canon_left middle f o o1 Hwfmid) Hout1).
      + exact (proj1 (run_out_canon_left after f o1 o2 Hwfafter) Hout2).
  Qed.

  (** The value equality test also decides equality of complete cells. *)
  Lemma run_cell_eq_dec : forall a b : cell V.t, {a = b} + {a <> b}.
  Proof.
    intros a b. destruct (run_cell_eqb_spec a b); [left|right]; assumption.
  Qed.

  (** Combining a row's existing output with another output retains the old information. *)
  Lemma run_combine_old : forall sorts db next f k old o,
    D.wf next -> (forall g, kind (D.view next) g = kind (D.view db) g) ->
    row_sorted sorts (kind (D.view db)) f k old ->
    D.out_le next f old (D.combine db f (Some old) o).
  Proof.
    intros sorts db next f k old o Hwf Hkinds [out [_ [Hkind Hout]]].
    destruct old as [[i|v]|]; [| |exact I].
    - destruct out as [| |m]; cbn [out_sort option_map cell_sort] in Hout;
        try discriminate.
      cbn [D.combine D.out_le cell_le]. now apply run_same_refl.
    - destruct out as [| |m]; cbn [out_sort option_map cell_sort] in Hout;
        try discriminate.
      unfold D.combine. rewrite Hkind. destruct o as [[j|w]|]; cbn [D.out_le cell_le].
      + exists m. split; [rewrite Hkinds; exact Hkind|apply V.merge_idem].
      + exists m. split; [rewrite Hkinds; exact Hkind|].
        rewrite V.merge_assoc, V.merge_idem. reflexivity.
      + exists m. split; [rewrite Hkinds; exact Hkind|apply V.merge_idem].
  Qed.

  (** A well-typed insertion preserves every old row and equality up to output growth. *)
  Lemma run_put_grows : forall sorts f k o db, D.wf db -> D.kind_ok db f k o ->
    view_sorted sorts (D.view db) -> grows_upto db (D.put f k o db).
  Proof.
    intros sorts f k o db Hwf Hallowed Hsorted.
    pose proof (D.wf_put f k o db Hwf Hallowed) as Hnext.
    pose proof (proj1 (D.layout_put f k o db Hwf)) as Hkinds.
    split.
    - intros i j Hsame. apply (proj2 (D.put_same f k o db i j Hwf Hallowed)).
      apply rst_step. now left.
    - intros g key old Hrow.
      assert (Hchoice : (g, key) = (f, map (D.canon db) k) \/
          (g, key) <> (f, map (D.canon db) k)).
      { destruct (Pos.eq_dec g f) as [Hg|Hg]; [|right; congruence].
        destruct (list_eq_dec run_cell_eq_dec key (map (D.canon db) k)) as [Hk|Hk].
        - left. now subst.
        - right. congruence. }
      destruct Hchoice as [Hequal|Hother].
      + injection Hequal as Hgf Hkey. subst g key.
        assert (Hprevious : D.old db f (map (D.canon db) k) = Some old).
        { apply (proj2 (D.old_row db f (map (D.canon db) k) old Hwf)). exact Hrow. }
        exists (map (D.canon db) k),
          (D.combine db f (Some old) (option_map (D.canon db) o)).
        split.
        * apply (proj2 (D.put_rows f k o db Hwf Hallowed _ _ _)). right.
          split; [reflexivity|]. split; [reflexivity|]. now rewrite Hprevious.
        * split; [now apply run_key_rel_refl|].
          apply (proj2 (run_out_canon_left (D.put f k o db) f old _ Hnext)).
          eapply run_combine_old; [exact Hnext|intro h; now rewrite Hkinds|].
          apply Hsorted. exact Hrow.
      + exists key, old. split.
        * apply (proj2 (D.put_rows f k o db Hwf Hallowed _ _ _)). now left.
        * split; [now apply run_key_rel_refl|].
          eapply run_row_out_refl; [exact Hnext|].
          unfold row_sorted. rewrite Hkinds. apply Hsorted. exact Hrow.
  Qed.

  (** Constructor allocation preserves every old row and equality. *)
  Lemma run_make_grows : forall sorts f k db, D.wf db ->
    D.wf (snd (D.make f k db)) -> kind (D.view db) f = Some OId ->
    view_sorted sorts (D.view db) -> grows_upto db (snd (D.make f k db)).
  Proof.
    intros sorts f k db Hwf Hnext Hkind Hsorted.
    pose proof (D.make_spec f k db Hwf Hkind) as Hmake.
    destruct (D.make f k db) as [i next]. cbn [snd] in Hnext |- *.
    destruct Hmake as [[j [_ [_ ->]]]|[_ [_ [_ [Hkinds [Hsame Hrows]]]]]].
    - now apply (run_grows_upto_refl sorts).
    - split.
      + intros a b Hab. apply (proj2 (Hsame a b)). now left.
      + intros g key old Hrow. exists key, old. split.
        * apply (proj2 (Hrows g key old)). now left.
        * split; [now apply run_key_rel_refl|].
          eapply run_row_out_refl; [exact Hnext|].
          unfold row_sorted. rewrite Hkinds. apply Hsorted. exact Hrow.
  Qed.

  (** Identifier union preserves every old row and equality. *)
  Lemma run_union_grows : forall sorts i j db, D.wf db -> D.wf (D.union i j db) ->
    view_sorted sorts (D.view db) -> grows_upto db (D.union i j db).
  Proof.
    intros sorts i j db Hwf Hnext Hsorted. split.
    - intros a b Hab. apply (proj2 (D.union_same i j db a b Hwf)).
      apply rst_step. now left.
    - intros f k o Hrow. exists k, o. split.
      + rewrite (D.union_rows i j db Hwf). exact Hrow.
      + split; [now apply run_key_rel_refl|]. eapply run_row_out_refl; [exact Hnext|].
        unfold row_sorted. rewrite (proj1 (D.layout_union i j db Hwf)).
        apply Hsorted. exact Hrow.
  Qed.

  (** Growth composes between states loaded for the same program and compiled plan. *)
  Lemma run_loaded_growth_trans : forall p cp before db next,
    D.wf db -> D.wf next -> loaded p cp db -> loaded p cp next ->
    grows_upto before db -> grows_upto db next -> grows_upto before next.
  Proof.
    intros p cp before db next Hwf Hnext Hloaded Hloadnext Hbefore Hstep.
    eapply run_grows_upto_trans; [exact Hwf|exact Hnext| |exact Hbefore|exact Hstep].
    intro f. rewrite (proj1 Hloadnext), (proj1 Hloaded). reflexivity.
  Qed.

  (** Typed actions preserve growth from any earlier database. *)
  Lemma run_apply_go_grows : forall p cp acts g s locals db before,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> env_allocated db (look s locals) ->
    grows_upto before db -> grows_upto before (apply_go acts s locals db).
  Proof.
    intros p cp acts. induction acts as [|a rest IH]; intros g s locals db before
      Hchecked Hwf Hloaded Hacts Henv Hallocated Hbefore; [exact Hbefore|].
    destruct a as [x f args|f args res|t u|x op args]; cbn [actions_ok] in Hacts.
    - destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
      destruct (run_term_cells_typed g s locals args ss Henv Hargs)
        as [cells [Hcells Hsorts]]. rewrite <- Hsorts in Hsort.
      pose proof (run_term_cells_allocated db s locals args cells Hallocated Hcells) as Hids.
      pose proof (run_make_state p cp f cells db Hchecked Hwf Hloaded Hkind Hsort Hids)
        as Hstate.
      pose proof (run_make_grows (program_sorts p) f cells db Hwf (proj1 Hstate)
        ltac:(rewrite (proj1 Hloaded); exact Hkind) (proj2 (proj2 Hloaded))) as Hstep.
      destruct (D.make f cells db) as [i next] eqn:Hmake. cbn [fst snd] in Hstate, Hstep.
      destruct Hstate as [Hwf' [Hloaded' [Hids' [_ [Hnew _]]]]].
      cbn [apply_go]. rewrite Hcells, Hmake.
      eapply IH; [exact Hchecked|exact Hwf'|exact Hloaded'|exact Hrest| | |].
      + apply run_env_sorted_set; [exact Henv|reflexivity].
      + apply run_env_allocated_set.
        * eapply run_env_allocated_mono; [exact Hids'|exact Hallocated].
        * intros j Heq. injection Heq as <-. exact Hnew.
      + exact (run_loaded_growth_trans p cp before db next Hwf Hwf' Hloaded Hloaded'
          Hbefore Hstep).
    - destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hresult Hrest]]]]]].
      destruct (run_term_cells_typed g s locals args ss Henv Hargs)
        as [cells [Hcells Hsorts]].
      destruct (run_result_cell_typed g s locals out res Henv Hresult)
        as [output [Houtput Houtsort]].
      assert (Hrow : row_sorted (program_sorts p) (program_kind p) f cells output).
      { exists out. rewrite Hsorts. repeat split; assumption. }
      assert (Hids : forall i, In (Id i) (cells ++ option_list output) -> D.allocated db i).
      { intros i Hin. apply in_app_iff in Hin as [Hin|Hin].
        - eapply run_term_cells_allocated; eauto.
        - eapply run_result_cell_allocated; eauto. }
      destruct (run_put_state p cp f cells output db Hchecked Hwf Hloaded Hrow Hids)
        as [Hwf' [Hloaded' [Hids' _]]].
      pose proof (run_put_allowed p cp db f cells output Hchecked Hloaded Hrow Hids)
        as Hallowed.
      pose proof (run_put_grows (program_sorts p) f cells output db Hwf Hallowed
        (proj2 (proj2 Hloaded))) as Hstep.
      cbn [apply_go]. rewrite Hcells, Houtput.
      eapply IH; [exact Hchecked|exact Hwf'|exact Hloaded'|exact Hrest|exact Henv| |].
      + eapply run_env_allocated_mono with (db := db);
          [rewrite Hids'; reflexivity|exact Hallocated].
      + exact (run_loaded_growth_trans p cp before db (D.put f cells output db)
          Hwf Hwf' Hloaded Hloaded' Hbefore Hstep).
    - destruct Hacts as [Ht [Hu Hrest]].
      destruct (run_term_cell_typed g s locals t SId Henv Ht)
        as [[i|v] [Hi Hitype]]; [|discriminate].
      destruct (run_term_cell_typed g s locals u SId Henv Hu)
        as [[j|v] [Hj Hjtype]]; [|discriminate].
      pose proof (run_term_cell_allocated db s locals t i Hallocated Hi) as Hiall.
      pose proof (run_term_cell_allocated db s locals u j Hallocated Hj) as Hjall.
      destruct (run_union_state p cp i j db Hwf Hloaded Hiall Hjall)
        as [Hwf' [Hloaded' [Hids' _]]].
      pose proof (run_union_grows (program_sorts p) i j db Hwf Hwf'
        (proj2 (proj2 Hloaded))) as Hstep.
      cbn [apply_go]. rewrite Hi, Hj.
      eapply IH; [exact Hchecked|exact Hwf'|exact Hloaded'|exact Hrest|exact Henv| |].
      + eapply run_env_allocated_mono with (db := db);
          [rewrite Hids'; reflexivity|exact Hallocated].
      + exact (run_loaded_growth_trans p cp before db (D.union i j db)
          Hwf Hwf' Hloaded Hloaded' Hbefore Hstep).
    - destruct Hacts as [Hargs Hrest].
      destruct (run_term_values_typed g s locals args Henv Hargs) as [vs Hvalues].
      cbn [apply_go]. rewrite Hvalues. destruct (V.prim op vs) as [v|]; [|exact Hbefore].
      eapply IH; [exact Hchecked|exact Hwf|exact Hloaded|exact Hrest| | |exact Hbefore].
      + apply run_env_sorted_set; [exact Henv|reflexivity].
      + apply run_env_allocated_set; [exact Hallocated|]. intros i Heq. discriminate.
  Qed.

  Lemma F6_apply_grows : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) ->
    rule_env (program_sorts p) (program_kind p) r s -> env_allocated db s ->
    grows_upto db (apply (actions V.t r) s db).
  Proof.
    intros p cp r s db Hchecked Hwf Hloaded Hin Henv Hallocated.
    destruct (run_rule_context p cp r s Hchecked Hin Henv) as [g [_ [Hacts Hsorted]]].
    unfold apply. eapply run_apply_go_grows; try eassumption.
    - intros x ty Hctx. destruct (Hsorted x ty Hctx) as [c [Hc Hty]].
      exists c. rewrite run_look_empty. split; assumption.
    - intros x i Hcell. rewrite run_look_empty in Hcell. eapply Hallocated. exact Hcell.
    - apply (run_grows_upto_refl (program_sorts p)); [exact Hwf|exact (proj2 (proj2 Hloaded))].
  Qed.

  (** Rebuilding retains every equality already present in the database. *)
  Lemma run_rebuild_same_incl : forall db i j, D.wf db ->
    same (D.view db) i j -> same (D.view (D.rebuild db)) i j.
  Proof.
    intros db i j Hwf Hsame. apply (proj2 (D.rebuild_same db i j Hwf)).
    apply cong_same. exact Hsame.
  Qed.

  (** Related old keys have identical canonical keys after rebuilding. *)
  Lemma run_rebuild_key_equal : forall db k k', D.wf db ->
    Forall2 (cell_rel (same (D.view db))) k k' ->
    map (D.canon (D.rebuild db)) k = map (D.canon (D.rebuild db)) k'.
  Proof.
    intros db k k' Hwf Hkeys. induction Hkeys as [|a b rest more Hab Htail IH].
    - reflexivity.
    - cbn [map]. rewrite IH. f_equal. destruct Hab as [i j Hij|v].
      + cbn [D.canon]. f_equal.
        apply (proj1 (D.same_repr (D.rebuild db) i j (D.wf_rebuild db Hwf))).
        apply run_rebuild_same_incl; assumption.
      + reflexivity.
  Qed.

  Lemma F6a_rebuild_grows : forall db0 db, D.wf db -> grows_upto db0 db ->
    grows db0 (D.rebuild db).
  Proof.
    intros db0 db Hwf [Hsame Hrows].
    pose proof (D.wf_rebuild db Hwf) as Hwf'.
    destruct (D.layout_rebuild db Hwf) as [Hkind Hlayout].
    assert (Hkeep : forall i j, same (D.view db) i j -> same (D.view (D.rebuild db)) i j).
    { intros i j Hij. now apply run_rebuild_same_incl. }
    split; [intros i j Hij; apply Hkeep; now apply Hsame|].
    intros f k o Hrow. destruct (Hrows f k o Hrow) as [k' [o' [Hrow' [Hkeys Hout]]]].
    destruct (D.rebuild_keeps db f k' o' Hwf Hrow') as [out [Hreb Hle]].
    exists out. split.
    - rewrite <- (run_rebuild_key_equal db k k' Hwf Hkeys) in Hreb. exact Hreb.
    - apply (proj2 (run_out_canon_left (D.rebuild db) f o out Hwf')).
      eapply run_out_le_trans; [exact Hwf'| |].
      + eapply run_out_le_mono; [intro g; now rewrite Hkind|exact Hkeep|].
        exact (proj1 (run_out_canon_left db f o o' Hwf) Hout).
      + exact (proj1 (run_out_canon_left (D.rebuild db) f o' out Hwf') Hle).
  Qed.

  (** A semantic identifier is supported when it occurs in a stored row. *)
  Definition run_supported (db : D.t) (c : cell V.t) : Prop :=
    match c with
    | Id i => exists f k o, row (D.view db) f k o /\ In (Id i) (k ++ option_list o)
    | Val _ => True
    end.

  (** Only context-bound variables need allocated action identifiers. *)
  Definition run_allocated_on (db : D.t) (g : ctx) (s : Model.env (V := V.t)) : Prop :=
    forall x ty i, g x = Some ty -> s x = Some (Id i) -> D.allocated db i.

  (** Semantic bindings use supported cells related to the evaluator's bindings. *)
  Definition run_env_related (db : D.t) (g : ctx)
      (actual semantic : Model.env (V := V.t)) : Prop :=
    forall x ty c, g x = Some ty -> actual x = Some c ->
    exists d, semantic x = Some d /\ run_supported db d /\
      cell_rel (same (D.view db)) c d.

  (** A cell occurring in a row is supported. *)
  Lemma run_row_supported : forall db f k o c, row (D.view db) f k o ->
    In c (k ++ option_list o) -> run_supported db c.
  Proof.
    intros db f k o [i|v] Hrow Hin; [exists f, k, o; now split|exact I].
  Qed.

  (** Supported identifiers are allocated in well-formed databases. *)
  Lemma run_supported_allocated : forall db i, D.wf db -> run_supported db (Id i) ->
    D.allocated db i.
  Proof.
    intros db i Hwf [f [k [o [Hrow Hin]]]]. eapply D.row_allocated; eassumption.
  Qed.

  (** Every cell is related to itself by database equality. *)
  Lemma run_cell_rel_refl : forall db (c : cell V.t), D.wf db ->
    cell_rel (same (D.view db)) c c.
  Proof.
    intros db [i|v] Hwf; constructor. now apply run_same_refl.
  Qed.

  (** Relating cells preserves their sorts. *)
  Lemma run_cell_rel_sort : forall db (c d : cell V.t), cell_rel (same (D.view db)) c d ->
    cell_sort c = cell_sort d.
  Proof.
    intros db c d Hrel. destruct Hrel; reflexivity.
  Qed.

  (** A variable's semantic cell occurs in every argument list that reads that variable. *)
  Lemma run_terms_var_cell : forall (s : Model.env (V := V.t)) ts cs x c,
    terms_value s ts cs -> In (Var x) ts -> s x = Some c -> In c cs.
  Proof.
    intros s ts cs x c Hterms. induction Hterms as [|t d rest more Hhead Htail IH];
      intros Hin Hlookup; [contradiction|].
    destruct Hin as [Heq|Hin].
    - subst t. cbn [term_value] in Hhead. rewrite Hlookup in Hhead.
      injection Hhead as <-. now left.
    - right. now apply IH.
  Qed.

  (** A matched function atom reads its arguments and result from one stored row. *)
  Lemma run_matched_fun_terms : forall db (s : Model.env (V := V.t)) f args res,
    atom_holds V.prim (D.view db) s (Fun V.t f args res) ->
    exists k o, row (D.view db) f k o /\
      terms_value s (args ++ option_list res) (k ++ option_list o).
  Proof.
    intros db s f args res [k [o [Hargs [Hresult Hrow]]]]. exists k, o.
    split; [exact Hrow|]. apply Forall2_app; [exact Hargs|].
    destruct res as [t|], o as [c|]; cbn [option_list] in *; try contradiction.
    - constructor; [exact Hresult|constructor].
    - constructor.
  Qed.

  (** Every variable bound by a closed query occurs in a function atom. *)
  Lemma run_query_bound_fun : forall sorts kinds q g,
    @query_ok V.t sorts kinds ctx_empty q g -> forall x ty, g x = Some ty ->
    exists f args res, In (Fun V.t f args res) q /\ In (Var x) (args ++ option_list res).
  Proof.
    intros sorts kinds q g Hquery x ty Hbound.
    destruct (run_query_scope sorts kinds ctx_empty q g Hquery x ty Hbound)
      as [Hempty|[a [Hin Hvar]]]; [discriminate|].
    apply (run_query_vars_fun sorts kinds q g Hquery x).
    apply in_flat_map. exists a. split; [exact Hin|]. rewrite run_atom_vars_terms.
    apply in_flat_map. exists (Var x). split; [exact Hvar|now left].
  Qed.

  (** Matched query bindings use supported cells, independently of unrelated environment entries. *)
  Lemma run_query_supported : forall sorts kinds q g db s,
    @query_ok V.t sorts kinds ctx_empty q g -> matches V.prim (D.view db) q s ->
    forall x ty c, g x = Some ty -> s x = Some c -> run_supported db c.
  Proof.
    intros sorts kinds q g db s Hquery Hmatches x ty c Hbound Hlookup.
    destruct (run_query_bound_fun sorts kinds q g Hquery x ty Hbound)
      as [f [args [res [Hfun Hvar]]]].
    destruct (run_matched_fun_terms db s f args res
      ((proj1 (Forall_forall _ _)) Hmatches _ Hfun)) as [k [o [Hrow Hterms]]].
    eapply run_row_supported; [exact Hrow|]. eapply run_terms_var_cell; eassumption.
  Qed.

  (** A well-typed identifier read uses only a context-bound allocation. *)
  Lemma run_term_allocated_on : forall db g s locals t ty i,
    run_allocated_on db g (look s locals) -> has g t ty ->
    term_cell s locals t = Some (Id i) -> D.allocated db i.
  Proof.
    intros db g s locals [x|v] ty i Hallocated Hhas Hcell; [|discriminate].
    eapply Hallocated; eassumption.
  Qed.

  (** Well-typed argument lookups require allocation only on their context. *)
  Lemma run_terms_allocated_on : forall db g s locals ts ss cs,
    run_allocated_on db g (look s locals) -> Forall2 (has g) ts ss ->
    term_cells s locals ts = Some cs -> forall i, In (Id i) cs -> D.allocated db i.
  Proof.
    intros db g s locals ts ss cs Hallocated Htyped. revert cs.
    induction Htyped as [|t ty rest types Hhead Htail IH]; intros cs Hcells i Hin.
    - injection Hcells as <-. contradiction.
    - cbn [term_cells] in Hcells.
      destruct (term_cell s locals t) as [c|] eqn:Hcell; [|discriminate].
      destruct (term_cells s locals rest) as [more|] eqn:Hmore; [|discriminate].
      injection Hcells as <-. destruct Hin as [Heq|Hin].
      + subst c. eapply run_term_allocated_on; eassumption.
      + eapply IH; eauto.
  Qed.

  (** Well-typed result lookups require allocation only on their context. *)
  Lemma run_result_allocated_on : forall db g s locals out res o,
    run_allocated_on db g (look s locals) -> has_result g out res ->
    result_cell s locals res = Some o ->
    forall i, In (Id i) (option_list o) -> D.allocated db i.
  Proof.
    intros db g s locals out res o Hallocated Htyped Hresult i Hin.
    destruct res as [t|]; cbn [result_cell] in Hresult.
    - destruct (term_cell s locals t) as [c|] eqn:Hcell; [|discriminate].
      injection Hresult as <-. destruct Hin as [Heq|[]]. subst c.
      destruct out; cbn [has_result out_sort] in Htyped; [contradiction| |];
        eapply run_term_allocated_on; eassumption.
    - injection Hresult as <-. contradiction.
  Qed.

  (** Related environments give related supported cells to every typed action term. *)
  Lemma run_term_related : forall db g s locals semantic t ty c,
    run_env_related db g (look s locals) semantic -> has g t ty ->
    term_cell s locals t = Some c ->
    exists d, term_value semantic t d /\ run_supported db d /\
      cell_rel (same (D.view db)) c d.
  Proof.
    intros db g s locals semantic [x|v] ty c Hrelated Hhas Hcell.
    - exact (Hrelated x ty c Hhas Hcell).
    - injection Hcell as <-. exists (Val v). split; [reflexivity|].
      split; [exact I|constructor].
  Qed.

  (** Related environments give related supported cells to a typed argument list. *)
  Lemma run_terms_related : forall db g s locals semantic ts ss cs,
    run_env_related db g (look s locals) semantic -> Forall2 (has g) ts ss ->
    term_cells s locals ts = Some cs ->
    exists ds, terms_value semantic ts ds /\ Forall (run_supported db) ds /\
      Forall2 (cell_rel (same (D.view db))) cs ds.
  Proof.
    intros db g s locals semantic ts ss cs Hrelated Htyped. revert cs.
    induction Htyped as [|t ty rest types Hhead Htail IH]; intros cs Hcells.
    - injection Hcells as <-. exists []. repeat split; constructor.
    - cbn [term_cells] in Hcells.
      destruct (term_cell s locals t) as [c|] eqn:Hcell; [|discriminate].
      destruct (term_cells s locals rest) as [more|] eqn:Hmore; [|discriminate].
      injection Hcells as <-.
      destruct (run_term_related db g s locals semantic t ty c Hrelated Hhead Hcell)
        as [d [Hvalue [Hsupport Hrel]]].
      destruct (IH more eq_refl) as [ds [Hvalues [Hsupports Hrels]]].
      exists (d :: ds). split; [now constructor|]. split; now constructor.
  Qed.

  (** Related environments agree on the value arguments supplied to a primitive. *)
  Lemma run_values_related : forall db g s locals semantic ts vs,
    run_env_related db g (look s locals) semantic -> Forall (fun t => has g t SVal) ts ->
    term_values s locals ts = Some vs -> terms_value semantic ts (map Val vs).
  Proof.
    intros db g s locals semantic ts vs Hrelated Htyped. revert vs.
    induction Htyped as [|t rest Hhead Htail IH]; intros vs Hvalues.
    - injection Hvalues as <-. constructor.
    - cbn [term_values] in Hvalues.
      destruct (term_cell s locals t) as [[i|v]|] eqn:Hcell; try discriminate.
      destruct (term_values s locals rest) as [more|] eqn:Hmore; [|discriminate].
      injection Hvalues as <-.
      destruct (run_term_related db g s locals semantic t SVal (Val v)
        Hrelated Hhead Hcell) as [d [Hvalue [_ Hrel]]].
      inversion Hrel; subst d. constructor; [exact Hvalue|now apply IH].
  Qed.

  (** A supported semantic cell equals a related canonical cell occurring in a row. *)
  Lemma run_canon_related_supported : forall db f k o c d,
    D.wf db -> row_ids_unique (D.view db) -> row (D.view db) f k o ->
    In (D.canon db c) (k ++ option_list o) -> run_supported db d ->
    cell_rel (same (D.view db)) c d -> D.canon db c = d.
  Proof.
    intros db f k o c d Hwf Hunique Hrow Hin Hsupport Hrel.
    destruct Hrel as [i j Hij|v]; [|reflexivity].
    destruct Hsupport as [g [key [output [Hother Hj]]]]. cbn [D.canon] in Hin |- *.
    f_equal. eapply Hunique; [exact Hrow|exact Hother|exact Hin|exact Hj|].
    apply (proj2 (D.same_repr db (D.repr db i) j Hwf)).
    rewrite D.repr_idem by exact Hwf. apply (proj1 (D.same_repr db i j Hwf)). exact Hij.
  Qed.

  (** A canonical row key equals its related supported semantic argument list. *)
  Lemma run_canon_key_related : forall db f key output actual semantic,
    D.wf db -> row_ids_unique (D.view db) -> row (D.view db) f key output ->
    (forall c, In c actual -> In (D.canon db c) (key ++ option_list output)) ->
    Forall2 (cell_rel (same (D.view db))) actual semantic ->
    Forall (run_supported db) semantic -> map (D.canon db) actual = semantic.
  Proof.
    intros db f key output actual semantic Hwf Hunique Hrow Hin Hrelated.
    revert Hin. induction Hrelated as [|a b rest more Hab Hrest IH]; intros Hin Hsupport.
    - reflexivity.
    - inversion Hsupport as [|b' more' Hb Hmore]; subst b' more'. cbn [map].
      f_equal.
      + eapply run_canon_related_supported; [exact Hwf|exact Hunique|exact Hrow| |exact Hb|].
        * apply Hin. now left.
        * exact Hab.
      + apply IH; [intros c Hc; apply Hin; now right|exact Hmore].
  Qed.

  (** A row read by actual arguments has exactly their supported semantic key. *)
  Lemma run_related_row_arguments : forall db f actual semantic output,
    D.wf db -> row_ids_unique (D.view db) ->
    row (D.view db) f (map (D.canon db) actual) output ->
    Forall2 (cell_rel (same (D.view db))) actual semantic ->
    Forall (run_supported db) semantic -> map (D.canon db) actual = semantic.
  Proof.
    intros db f actual semantic output Hwf Hunique Hrow Hrel Hsupport.
    eapply run_canon_key_related; [exact Hwf|exact Hunique|exact Hrow| |exact Hrel|exact Hsupport].
    intros c Hin. apply in_app_iff. left. now apply in_map.
  Qed.

  (** A typed result term has a related supported semantic result. *)
  Lemma run_result_related_term : forall db g s locals semantic out t c,
    run_env_related db g (look s locals) semantic -> has_result g out (Some t) ->
    term_cell s locals t = Some c ->
    exists d, term_value semantic t d /\ run_supported db d /\
      cell_rel (same (D.view db)) c d.
  Proof.
    intros db g s locals semantic out t c Hrelated Hhas Hcell.
    destruct out; cbn [has_result out_sort] in Hhas; [contradiction| |];
      eapply run_term_related; eassumption.
  Qed.

  (** Action execution cannot clear a raised change flag. *)
  Lemma run_apply_go_changed : forall acts s locals db, D.changed db = true ->
    D.changed (apply_go acts s locals db) = true.
  Proof.
    intro acts. induction acts as [|a rest IH]; intros s locals db Hchanged;
      [exact Hchanged|].
    destruct a as [x f args|f args res|t u|x op args]; cbn [apply_go].
    - destruct (term_cells s locals args) as [cells|]; [|exact Hchanged].
      pose proof (D.changed_make f cells db Hchanged) as Hnext.
      destruct (D.make f cells db) as [i next]. apply IH. exact Hnext.
    - destruct (term_cells s locals args) as [cells|]; [|exact Hchanged].
      destruct (result_cell s locals res) as [output|]; [|exact Hchanged].
      apply IH. now apply D.changed_put.
    - destruct (term_cell s locals t) as [[i|v]|]; [| |exact Hchanged];
        destruct (term_cell s locals u) as [[j|w]|]; try exact Hchanged;
        apply IH; try exact Hchanged.
      now apply D.changed_union.
    - destruct (term_values s locals args) as [vs|]; [|exact Hchanged].
      destruct (V.prim op vs); [apply IH|]; exact Hchanged.
  Qed.

  (** A quiet completed suffix started with a quiet database. *)
  Lemma run_apply_go_quiet_start : forall acts s locals db,
    D.changed (apply_go acts s locals db) = false -> D.changed db = false.
  Proof.
    intros acts s locals db Hquiet. destruct (D.changed db) eqn:Hchanged; [|reflexivity].
    pose proof (run_apply_go_changed acts s locals db Hchanged) as Hraised. congruence.
  Qed.

  (** Context-restricted allocation survives a growing identifier counter. *)
  Lemma run_allocated_on_mono : forall db next g s,
    (D.ids db <= D.ids next)%N -> run_allocated_on db g s -> run_allocated_on next g s.
  Proof.
    intros db next g s Hids Hallocated x ty i Hbound Hcell.
    specialize (Hallocated x ty i Hbound Hcell). unfold D.allocated in *. lia.
  Qed.

  (** A typed local assignment preserves context-restricted allocation. *)
  Lemma run_allocated_on_set : forall db g s locals x c ty,
    run_allocated_on db g (look s locals) ->
    (forall i, c = Id i -> D.allocated db i) ->
    run_allocated_on db (ctx_set g x ty) (look s (PTrieCode.set x c locals)).
  Proof.
    intros db g s locals x c ty Hallocated Hnew y other i Hbound Hcell.
    rewrite run_look_set in Hcell. unfold ctx_set in Hbound. unfold update in Hcell.
    destruct (Pos.eqb x y).
    - apply Hnew. now injection Hcell.
    - eapply Hallocated; eassumption.
  Qed.

  (** A pair of related local assignments preserves the environment relation. *)
  Lemma run_env_related_set : forall db g s locals semantic x c d ty,
    run_env_related db g (look s locals) semantic -> run_supported db d ->
    cell_rel (same (D.view db)) c d ->
    run_env_related db (ctx_set g x ty) (look s (PTrieCode.set x c locals))
      (update semantic x d).
  Proof.
    intros db g s locals semantic x c d ty Hrelated Hsupport Hrel y other a Hbound Hcell.
    rewrite run_look_set in Hcell. unfold ctx_set in Hbound. unfold update in Hcell |- *.
    destruct (Pos.eqb x y).
    - injection Hcell as <-. exists d. split; [reflexivity|]. split; assumption.
    - eapply Hrelated; eassumption.
  Qed.

  (** Retaining rows retains supported semantic identifiers. *)
  Lemma run_supported_mono : forall db next c,
    (forall f k o, row (D.view db) f k o -> row (D.view next) f k o) ->
    run_supported db c -> run_supported next c.
  Proof.
    intros db next [i|v] Hrows Hsupport; [|exact I].
    destruct Hsupport as [f [k [o [Hrow Hin]]]]. exists f, k, o. split; [now apply Hrows|exact Hin].
  Qed.

  (** Retaining rows and equalities preserves related semantic bindings. *)
  Lemma run_env_related_mono : forall db next g actual semantic,
    (forall f k o, row (D.view db) f k o -> row (D.view next) f k o) ->
    (forall i j, same (D.view db) i j -> same (D.view next) i j) ->
    run_env_related db g actual semantic -> run_env_related next g actual semantic.
  Proof.
    intros db next g actual semantic Hrows Hsame Hrelated x ty c Hbound Hcell.
    destruct (Hrelated x ty c Hbound Hcell) as [d [Hd [Hsupport Hrel]]].
    exists d. split; [exact Hd|]. split.
    - eapply run_supported_mono; eassumption.
    - eapply run_cell_rel_mono; eassumption.
  Qed.

  (** Database equality is symmetric. *)
  Lemma run_same_sym : forall db i j, D.wf db ->
    same (D.view db) i j -> same (D.view db) j i.
  Proof.
    intros db i j Hwf Hij. apply (proj2 (D.same_repr db j i Hwf)).
    symmetry. apply (proj1 (D.same_repr db i j Hwf)). exact Hij.
  Qed.

  (** Related source cells have the same output-containment consequences. *)
  Lemma run_cell_le_related : forall db f a b c, D.wf db ->
    cell_rel (same (D.view db)) a b -> cell_le V.merge (D.view db) f a c ->
    cell_le V.merge (D.view db) f b c.
  Proof.
    intros db f a b c Hwf Hrel Hle. destruct Hrel as [i j Hij|v]; [|exact Hle].
    destruct c as [k|w]; [|contradiction].
    eapply run_same_trans; [exact Hwf| |exact Hle]. now apply run_same_sym.
  Qed.

  (** A quiet union adds no new identifier equality. *)
  Lemma run_quiet_union_same : forall i j db, D.wf db -> D.changed db = false ->
    D.changed (D.union i j db) = false ->
    forall a b, same (D.view (D.union i j db)) a b -> same (D.view db) a b.
  Proof.
    intros i j db Hwf Hquiet Hnext a b Hsame.
    pose proof (D.union_quiet i j db Hwf Hquiet Hnext) as Hij.
    apply (proj1 (D.union_same i j db a b Hwf)) in Hsame.
    induction Hsame as [a b Hstep|a|a b Hstep IH|a b c Hab IH1 Hbc IH2].
    - destruct Hstep as [Hstep|Hpair]; [exact Hstep|].
      injection Hpair as Hai Hbj. subst a b. exact Hij.
    - now apply run_same_refl.
    - now apply run_same_sym.
    - eapply run_same_trans; eassumption.
  Qed.

  (** A quiet union preserves uniqueness of identifiers that occur in rows. *)
  Lemma run_quiet_union_unique : forall i j db, D.wf db -> D.changed db = false ->
    D.changed (D.union i j db) = false -> row_ids_unique (D.view db) ->
    row_ids_unique (D.view (D.union i j db)).
  Proof.
    intros i j db Hwf Hquiet Hnext Hunique f k o g key output a b Hrow Hother Ha Hb Hab.
    rewrite (D.union_rows i j db Hwf) in Hrow, Hother.
    eapply Hunique; [exact Hrow|exact Hother|exact Ha|exact Hb|].
    eapply run_quiet_union_same; eassumption.
  Qed.

  (** Row, equality and kind inclusion transports cell output containment. *)
  Lemma run_cell_le_transport : forall (before after : view (V := V.t)) f a b,
    (forall i j, same after i j -> same before i j) ->
    (forall g, kind before g = kind after g) ->
    cell_le V.merge after f a b -> cell_le V.merge before f a b.
  Proof.
    intros before after f [i|v] [j|w] Hsame Hkinds Hle; cbn [cell_le] in *;
      try contradiction.
    - now apply Hsame.
    - destruct Hle as [m [Hkind Hmerge]]. exists m. split; [now rewrite Hkinds|exact Hmerge].
  Qed.

  (** Keeping semantic rows, equalities and kinds transports action presence. *)
  Lemma run_present_transport : forall (before after : view (V := V.t)) acts semantic,
    (forall f k o, row after f k o -> row before f k o) ->
    (forall i j, same after i j -> same before i j) ->
    (forall f, kind before f = kind after f) ->
    present V.prim V.merge after semantic acts -> present V.prim V.merge before semantic acts.
  Proof.
    intros before after acts. induction acts as [|a rest IH]; intros semantic Hrows Hsame
      Hkinds Hpresent; [exact I|].
    destruct a as [x f args|f args res|t u|x op args]; cbn [present] in Hpresent |- *.
    - destruct Hpresent as [k [i [Hterms [Hrow Htail]]]]. exists k, i.
      split; [exact Hterms|]. split; [now apply Hrows|]. eapply IH; eassumption.
    - destruct Hpresent as [k [o [Hterms [Hrow [Hresult Htail]]]]]. exists k, o.
      split; [exact Hterms|]. split; [now apply Hrows|]. split.
      + destruct res as [t|]; [|exact I].
        destruct Hresult as [c [d [Ht [Ho Hle]]]]. exists c, d.
        split; [exact Ht|]. split; [exact Ho|]. eapply run_cell_le_transport; eassumption.
      + eapply IH; eassumption.
    - destruct Hpresent as [c [d [Ht [Hu [Hrel Htail]]]]]. exists c, d.
      split; [exact Ht|]. split; [exact Hu|]. split.
      + destruct c as [i|v], d as [j|w]; try exact I. now apply Hsame.
      + eapply IH; eassumption.
    - destruct Hpresent as [k [vs [Hterms [Hvalues Htail]]]]. exists k, vs.
      split; [exact Hterms|]. split; [exact Hvalues|].
      destruct (V.prim op vs) as [v|]; [eapply IH; eassumption|exact I].
  Qed.

  (** A quiet constructor call reuses an old row and leaves the database itself unchanged. *)
  Lemma run_quiet_make_reuse : forall db f k, D.wf db ->
    kind (D.view db) f = Some OId ->
    (forall j, In (Id j) k -> D.allocated db j) -> D.slots_fit db f (S (length k)) ->
    D.changed db = false -> D.changed (snd (D.make f k db)) = false ->
    exists i next j, D.make f k db = (i, next) /\ next = db /\
      row (D.view db) f (map (D.canon db) k) (Some (Id j)) /\ i = D.repr db j.
  Proof.
    intros db f k Hwf Hkind Hallocated Hfit Hquiet Hafter.
    destruct (D.make_quiet f k db Hwf Hquiet Hafter) as [old Hrowold].
    pose proof (D.make_spec f k db Hwf Hkind) as Hspec.
    pose proof (D.wf_make f k db Hwf Hallocated Hfit) as Hwfnext.
    destruct (D.make f k db) as [i next] eqn:Hmake. cbn [snd] in Hwfnext.
    destruct Hspec as [[j [Hrow [Hrepr Hnext]]]|[Hfresh [Hrow Hextension]]].
    - exists i, next, j. split; [reflexivity|]. split; [exact Hnext|]. split; assumption.
    - destruct Hextension as [Hids [Hkinds [Hsame Hrows]]].
      assert (Hold : row (D.view next) f (map (D.canon db) k) (Some (Id old))).
      { apply (proj2 (Hrows f (map (D.canon db) k) (Some (Id old)))). now left. }
      pose proof (D.row_functional next f (map (D.canon db) k) (Some (Id i))
        (Some (Id old)) Hwfnext Hrow Hold) as Heq. injection Heq as Heqold. subst old.
      assert (Hi : D.allocated db i).
      { eapply D.row_allocated; [exact Hwf|exact Hrowold|].
        apply in_app_iff. right. now left. }
      unfold D.fresh_id in Hfresh. unfold D.allocated in Hi.
      rewrite Hfresh, N.succ_pos_spec in Hi. lia.
  Qed.

  (** Quiet typed execution already has each action present in its semantic environment. *)
  Lemma run_apply_go_present : forall p cp acts g s locals semantic db,
    plans_ok p cp -> D.wf db -> loaded p cp db ->
    actions_ok (program_sorts p) (program_kind p) g acts ->
    env_sorted g (look s locals) -> run_allocated_on db g (look s locals) ->
    run_env_related db g (look s locals) semantic -> row_ids_unique (D.view db) ->
    D.changed db = false -> D.changed (apply_go acts s locals db) = false ->
    present V.prim V.merge (D.view db) semantic acts.
  Proof.
    intros p cp acts. induction acts as [|a rest IH]; intros g s locals semantic db
      Hchecked Hwf Hloaded Hacts Henv Hallocated Hrelated Hunique Hquiet Hfinal;
      [exact I|].
    destruct a as [x f args|f args res|t u|x op args]; cbn [actions_ok] in Hacts.
    - destruct Hacts as [ss [Hsort [Hkind [Hargs Hrest]]]].
      destruct (run_term_cells_typed g s locals args ss Henv Hargs)
        as [cells [Hcells Hsorts]].
      destruct (run_terms_related db g s locals semantic args ss cells Hrelated Hargs Hcells)
        as [semcells [Hsemterms [Hsupports Hrels]]].
      assert (Hargs_allocated : forall i, In (Id i) cells -> D.allocated db i).
      { eapply run_terms_allocated_on; eassumption. }
      assert (Hkinddb : kind (D.view db) f = Some OId).
      { rewrite (proj1 Hloaded). exact Hkind. }
      assert (Hfit : D.slots_fit db f (S (length cells))).
      { eapply run_slots_fit; [exact Hchecked|exact Hloaded|exact Hsort|exact Hkind|].
        rewrite <- Hsorts, length_map. cbn. lia. }
      cbn [apply_go] in Hfinal. rewrite Hcells in Hfinal.
      destruct (D.make f cells db) as [i next] eqn:Hmake.
      pose proof (run_apply_go_quiet_start rest s (PTrieCode.set x (Id i) locals) next Hfinal)
        as Hnextquiet.
      assert (Hafter : D.changed (snd (D.make f cells db)) = false).
      { rewrite Hmake. exact Hnextquiet. }
      destruct (run_quiet_make_reuse db f cells Hwf Hkinddb Hargs_allocated Hfit Hquiet Hafter)
        as [ri [rn [j [Hcall [Hsame [Hrow Hrepr]]]]]].
      rewrite Hmake in Hcall. injection Hcall as Heqi Heqn. subst ri rn next.
      assert (Hnew : D.allocated db i).
      { pose proof (D.layout_make f cells db Hwf) as Hlayout. rewrite Hmake in Hlayout.
        destruct Hlayout as [_ [_ [_ [Hnew _]]]]. exact Hnew. }
      pose proof (run_related_row_arguments db f cells semcells (Some (Id j))
        Hwf Hunique Hrow Hrels Hsupports) as Hkey.
      rewrite Hkey in Hrow. cbn [present]. exists semcells, j.
      split; [exact Hsemterms|]. split; [exact Hrow|].
      assert (Henv' : env_sorted (ctx_set g x SId)
          (look s (PTrieCode.set x (Id i) locals))).
      { apply run_env_sorted_set; [exact Henv|reflexivity]. }
      assert (Hallocated' : run_allocated_on db (ctx_set g x SId)
          (look s (PTrieCode.set x (Id i) locals))).
      { apply run_allocated_on_set; [exact Hallocated|].
        intros k Heq. injection Heq as <-. exact Hnew. }
      assert (Hrelated' : run_env_related db (ctx_set g x SId)
          (look s (PTrieCode.set x (Id i) locals)) (update semantic x (Id j))).
      { apply run_env_related_set; [exact Hrelated| |].
        - eapply run_row_supported; [exact Hrow|]. apply in_app_iff. right. now left.
        - constructor. apply (proj2 (D.same_repr db i j Hwf)).
          rewrite Hrepr, D.repr_idem by exact Hwf. reflexivity. }
      exact (IH _ _ _ _ _ Hchecked Hwf Hloaded Hrest Henv' Hallocated' Hrelated'
        Hunique Hquiet Hfinal).
    - destruct Hacts as [ss [out [Hsort [Hkind [Hargs [Hresult Hrest]]]]]].
      destruct (run_term_cells_typed g s locals args ss Henv Hargs)
        as [cells [Hcells Hsorts]].
      destruct (run_result_cell_typed g s locals out res Henv Hresult)
        as [output [Houtput Houtsort]].
      destruct (run_terms_related db g s locals semantic args ss cells Hrelated Hargs Hcells)
        as [semcells [Hsemterms [Hsupports Hrels]]].
      assert (Hrowtyped : row_sorted (program_sorts p) (program_kind p) f cells output).
      { exists out. rewrite Hsorts. repeat split; assumption. }
      assert (Hargs_allocated : forall i, In (Id i) (cells ++ option_list output) ->
          D.allocated db i).
      { intros i Hin. apply in_app_iff in Hin as [Hin|Hin].
        - eapply run_terms_allocated_on; eassumption.
        - eapply run_result_allocated_on; eassumption. }
      pose proof (run_put_allowed p cp db f cells output Hchecked Hloaded Hrowtyped
        Hargs_allocated) as Hallowed.
      destruct (run_put_state p cp f cells output db Hchecked Hwf Hloaded Hrowtyped
        Hargs_allocated) as [Hwf' [Hloaded' [Hids _]]].
      cbn [apply_go] in Hfinal. rewrite Hcells, Houtput in Hfinal.
      pose proof (run_apply_go_quiet_start rest s locals (D.put f cells output db) Hfinal)
        as Hnextquiet.
      destruct (D.put_quiet f cells output db Hwf Hallowed Hquiet Hnextquiet)
        as [Hview [stored [Hrow Hcontained]]].
      pose proof (run_related_row_arguments db f cells semcells stored Hwf Hunique Hrow
        Hrels Hsupports) as Hkey. rewrite Hkey in Hrow.
      assert (Hallocated' : run_allocated_on (D.put f cells output db) g (look s locals)).
      { eapply run_allocated_on_mono with (db := db);
          [rewrite Hids; reflexivity|exact Hallocated]. }
      assert (Hrelated' : run_env_related (D.put f cells output db) g (look s locals) semantic).
      { eapply run_env_related_mono; [| |exact Hrelated]; intros; now rewrite Hview. }
      assert (Hunique' : row_ids_unique (D.view (D.put f cells output db))).
      { now rewrite Hview. }
      pose proof (IH _ _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated' Hrelated'
        Hunique' Hnextquiet Hfinal) as Htail.
      rewrite Hview in Htail. cbn [present]. exists semcells, stored.
      split; [exact Hsemterms|]. split; [exact Hrow|]. split; [|exact Htail].
      destruct res as [t|]; [|exact I]. cbn [result_cell] in Houtput.
      destruct (term_cell s locals t) as [c|] eqn:Hcell; [|discriminate].
      injection Houtput as Heqoutput. subst output.
      destruct (run_result_related_term db g s locals semantic out t c
        Hrelated Hresult Hcell) as [d [Hterm [_ Hrel]]].
      destruct stored as [target|]; [|contradiction]. exists d, target.
      split; [exact Hterm|]. split; [reflexivity|].
      eapply run_cell_le_related; eassumption.
    - destruct Hacts as [Ht [Hu Hrest]].
      destruct (run_term_cell_typed g s locals t SId Henv Ht)
        as [[i|v] [Hi Hitype]]; [|discriminate].
      destruct (run_term_cell_typed g s locals u SId Henv Hu)
        as [[j|v] [Hj Hjtype]]; [|discriminate].
      pose proof (run_term_allocated_on db g s locals t SId i Hallocated Ht Hi) as Hiall.
      pose proof (run_term_allocated_on db g s locals u SId j Hallocated Hu Hj) as Hjall.
      destruct (run_union_state p cp i j db Hwf Hloaded Hiall Hjall)
        as [Hwf' [Hloaded' [Hids _]]].
      cbn [apply_go] in Hfinal. rewrite Hi, Hj in Hfinal.
      pose proof (run_apply_go_quiet_start rest s locals (D.union i j db) Hfinal) as Hnextquiet.
      pose proof (D.union_quiet i j db Hwf Hquiet Hnextquiet) as Hij.
      destruct (run_term_related db g s locals semantic t SId (Id i) Hrelated Ht Hi)
        as [c [Hsemantic_t [_ Hic]]].
      destruct (run_term_related db g s locals semantic u SId (Id j) Hrelated Hu Hj)
        as [d [Hsemantic_u [_ Hjd]]].
      inversion Hic as [i0 a Hia|]; subst.
      inversion Hjd as [j0 b Hjb|]; subst.
      assert (Hab : same (D.view db) a b).
      { eapply run_same_trans with (j := i); [exact Hwf|now apply run_same_sym|].
        eapply run_same_trans; [exact Hwf|exact Hij|exact Hjb]. }
      assert (Hallocated' : run_allocated_on (D.union i j db) g (look s locals)).
      { eapply run_allocated_on_mono with (db := db);
          [rewrite Hids; reflexivity|exact Hallocated]. }
      assert (Hrelated' : run_env_related (D.union i j db) g (look s locals) semantic).
      { eapply run_env_related_mono; [| |exact Hrelated].
        - intros f k o Hrow. now rewrite (D.union_rows i j db Hwf).
        - intros k l Hkl. apply (proj2 (D.union_same i j db k l Hwf)).
          apply rst_step. now left. }
      assert (Hunique' : row_ids_unique (D.view (D.union i j db))).
      { eapply run_quiet_union_unique; eassumption. }
      pose proof (IH _ _ _ _ _ Hchecked Hwf' Hloaded' Hrest Henv Hallocated' Hrelated'
        Hunique' Hnextquiet Hfinal) as Htail.
      cbn [present]. exists (Id a), (Id b).
      split; [exact Hsemantic_t|]. split; [exact Hsemantic_u|]. split; [exact Hab|].
      eapply run_present_transport; [| | |exact Htail].
      + intros f k o Hrow. rewrite (D.union_rows i j db Hwf) in Hrow. exact Hrow.
      + eapply run_quiet_union_same; eassumption.
      + intro f. rewrite (proj1 (D.layout_union i j db Hwf)). reflexivity.
    - destruct Hacts as [Hargs Hrest].
      destruct (run_term_values_typed g s locals args Henv Hargs) as [vs Hvalues].
      pose proof (run_values_related db g s locals semantic args vs Hrelated Hargs Hvalues)
        as Hsemterms.
      cbn [apply_go] in Hfinal. rewrite Hvalues in Hfinal.
      cbn [present]. exists (map Val vs), vs.
      split; [exact Hsemterms|]. split; [apply run_value_cells|].
      destruct (V.prim op vs) as [v|]; [|exact I].
      assert (Henv' : env_sorted (ctx_set g x SVal)
          (look s (PTrieCode.set x (Val v) locals))).
      { apply run_env_sorted_set; [exact Henv|reflexivity]. }
      assert (Hallocated' : run_allocated_on db (ctx_set g x SVal)
          (look s (PTrieCode.set x (Val v) locals))).
      { apply run_allocated_on_set; [exact Hallocated|]. intros i Heq. discriminate. }
      assert (Hrelated' : run_env_related db (ctx_set g x SVal)
          (look s (PTrieCode.set x (Val v) locals)) (update semantic x (Val v))).
      { apply run_env_related_set; [exact Hrelated|exact I|constructor]. }
      exact (IH _ _ _ _ _ Hchecked Hwf Hloaded Hrest Henv' Hallocated' Hrelated'
        Hunique Hquiet Hfinal).
  Qed.

  Lemma F5_apply_quiet_present : forall p cp r s db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In r (rules V.t p) -> matches V.prim (D.view db) (query V.t r) s ->
    row_ids_unique (D.view db) ->
    D.changed db = false -> D.changed (apply (actions V.t r) s db) = false ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  Proof.
    intros p cp r s db Hchecked Hwf Hloaded Hin Hmatches Hunique Hquiet Hfinal.
    pose proof (plans_ok_sorted p cp Hchecked) as Hprogram.
    destruct ((proj1 (Forall_forall _ _)) Hprogram r Hin) as [g [Hquery Hacts]].
    pose proof (matches_rule_env V.t V.prim (D.view db) (program_sorts p) (program_kind p)
      r g s (proj2 (proj2 Hloaded)) (proj1 Hloaded) Hquery Hmatches) as Henv.
    assert (Hsupport : forall x ty c, g x = Some ty -> s x = Some c -> run_supported db c).
    { eapply run_query_supported; eassumption. }
    unfold apply in Hfinal. eapply run_apply_go_present; try eassumption.
    - intros x ty Hbound. destruct (Henv x ty Hbound) as [c [Hc Hsort]].
      exists c. rewrite run_look_empty. split; assumption.
    - intros x ty i Hbound Hcell. rewrite run_look_empty in Hcell.
      apply run_supported_allocated; [exact Hwf|]. eapply Hsupport; eassumption.
    - intros x ty c Hbound Hcell. rewrite run_look_empty in Hcell.
      exists c. split; [exact Hcell|]. split.
      + eapply Hsupport; eassumption.
      + now apply run_cell_rel_refl.
  Qed.

  Lemma F7_apply_derives : forall p initial db r s, relational_fragment p = true ->
    no_ids initial -> D.wf db -> derived p initial db -> In r (rules V.t p) ->
    derivation_body V.prim p (D.view initial) s (query V.t r) ->
    derived p initial (apply (actions V.t r) s db).
  Proof. Admitted. (* PLAN-DEFECT: result-bearing relational Put; see RunTest. *)

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
  Proof. Admitted. (* STUB *)

  Lemma F16_unit_pos : forall db, 1 <= D.unit db.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma F26_bindings_env : forall p cp db c b r, plans_ok p cp -> D.wf db ->
    loaded p cp db -> In c (all_plans cp) ->
    nth_error (rules V.t p) (N.to_nat (rule_ix V.t c)) = Some r -> In b (bindings cp c db) ->
    rule_env (program_sorts p) (program_kind p) r (env_of c b) /\ env_allocated db (env_of c b).
  Proof.
    intros p cp db c b r Hplans Hwf Hloaded Hin Hrule Hbinding. split.
    - pose proof (plans_ok_sorted p cp Hplans) as Hprogram.
      unfold program_ok in Hprogram.
      assert (Hmember : In r (rules V.t p)) by (eapply nth_error_In; exact Hrule).
      apply Forall_forall with (x := r) in Hprogram; [|exact Hmember].
      destruct Hprogram as [g [Htyped Hactions]]. exists g. split; [exact Htyped|].
      destruct (run_plan_member p cp c Hplans Hin)
        as [table [newok [checked_r [Htable [Hchecked_rule Hcheck]]]]].
      rewrite Hrule in Hchecked_rule. injection Hchecked_rule as <-.
      destruct (run_check_cplan_parts newok table (rule_ix V.t c) r c Hcheck)
        as [_ [Hlength [names [expected [Hnames [Hlayout [Hquery Hpost]]]]]]].
      pose proof (run_plan_join_wf p cp db c Hplans Hwf Hloaded Hin) as Hjoin.
      pose proof (J.run_sound (join V.t c) (map (source_index db) (sources V.t c)) b
        Hjoin Hbinding) as Hanswer.
      destruct Hanswer as [Hbinding_length Hprojections].
      assert (Hsources : run_sources_satisfied db b (sources V.t c) (cols (join V.t c))).
      { apply (run_join_answer_sources db b (join V.t c) (sources V.t c)).
        split; assumption. }
      assert (Hname_cells : forall x j, trie_get x names = Some j -> exists cell,
          nth_error b (N.to_nat j) = Some cell /\ env_of c b x = Some cell).
      { intros x j Hget. unfold env_of.
        eapply run_checked_names_cells; [exact Hnames|lia|exact Hget]. }
      eapply (run_check_query_sorted p cp db table Hwf Hloaded Htable ctx_empty
        (query V.t r) g Htyped newok names (nvars (join V.t c)) 0 0 Empty 0
        (sources V.t c) (cols (join V.t c)) [] (nat_n (nvars (join V.t c))) [] [] expected
        b (env_of c b) Hquery Hsources Hname_cells).
      intros x ty Hempty. discriminate.
    - eapply run_plan_bindings_allocated; eassumption.
  Qed.


  Lemma F27_check_plan_split : forall p cp,
    check_plan p cp = check_program p && check_shape p cp.
  Proof.
    reflexivity.
  Qed.

  Lemma F29_shape_slots : forall p cp f perm, plans_ok p cp ->
    In (f, perm) (Syntax.slots V.t cp) -> exists ss out,
      program_sorts p f = Some ss /\ program_kind p f = Some out /\
      NoDup perm /\ Forall (fun i => i < length ss +
        match out_sort out with
        | Some _ => 1
        | None => 0
        end) perm.
  Proof.
    intros p cp f perm Hplan Hslot.
    destruct (check_plan_slots p cp f perm Hplan Hslot)
      as [d [Hdecl [Hnodup Hbound]]].
    destruct (run_find_decl_fields (decls V.t p) f d Hdecl) as [Hsort Hkind].
    exists (arg_sorts d), (out d).
    split; [exact Hsort|]. split; [exact Hkind|].
    split; [exact Hnodup|]. destruct (out d); exact Hbound.
  Qed.


  Lemma T4_check_plan_split : forall p cp,
    (T_check_plan p cp <= T_check_program p + T_check_shape p cp + k_check)%N.
  Proof. Admitted. (* STUB *)

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

  (** Building the trie of a binding pays for the bits of the plan's variables. *)
  Lemma T6_bind_trie_le : forall c b,
    (T_bind_trie c b <= k_driver *
      N.of_nat (fold_right (fun x n => (Pos.size_nat x + 1 + n)%nat) 0%nat
        (var_of V.t c) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The filter pays for its atoms at the widest program word or binding cell, and for the
      primitive work of the query. *)
  Lemma T7_keep_le : forall p c b,
    (T_keep p c (bind_trie c b) <= k_driver * N.of_nat (post_work p c + 1) *
      N.of_nat (wbits p + fold_right (fun x n => Nat.max (cell_bits V.encode x) n) 0%nat b + 1) +
      k_driver * query_prim_work V.prim_work (query V.t (job_rule p c)) (env_of c b) +
      k_driver * N.of_nat (rule_work p c))%N.
  Proof. Admitted. (* STUB *)

  (** A round's jobs are the kept bindings of its plans, plan by plan. *)
  Lemma F31_jobs : forall p cp nv db,
    jobs p cp nv db = flat_map (fun c => map (fun b => (c, b))
      (filter (fun b => keep p c (bind_trie c b)) (bindings cp c db)))
      (if nv then naive V.t cp else seminaive V.t cp).
  Proof.
    reflexivity.
  Qed.

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
  Proof. Admitted. (* STUB *)

  Lemma T1_round_le : forall B U p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (D.ids (round p cp nv db) <= B)%N -> D.unit (round p cp nv db) <= U ->
    (T_round p cp nv db + N.of_nat U * D.potential B (round p cp nv db) <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (round_work p cp nv db + D.pending db + 1) +
      N.of_nat U * D.potential B db)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_driver_wrapper : forall p cp lim db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    (T_run p cp lim db <=
      T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) +
      match loopN (driver p cp lim) (max_iter lim) (false, db) with
      | inl (_, final) => D.T_rebuild final
      | inr (_, final) => D.T_rebuild final
      end + k_driver)%N.
  Proof. Admitted. (* STUB *)

  (** A driver call pays for its round, limit test, flag test and advance. *)
  Lemma T2a_driver_le : forall p cp lim nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_driver p cp lim (nv, db) <= T_round p cp nv db + k_driver *
      N.of_nat (length (Syntax.slots V.t cp) +
        N.size_nat (D.ids (round p cp nv db)) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The loop pays for every driver call in the trace prefix and its fuel. *)
  Lemma T2b_loop_trace : forall p cp lim db,
    (T_loopN (driver p cp lim) (T_driver p cp lim) (max_iter lim) (false, db) <=
      fold_right N.add 0 (map (fun st => T_driver p cp lim st + c_loopN)
        (firstn (N.to_nat (max_iter lim)) (trace p cp lim db))) +
      c_loopN * N.of_nat (N.size_nat (max_iter lim) + 1))%N.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
End RunT.
