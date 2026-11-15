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
