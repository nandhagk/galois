(** * Flat rewrite compilation

    Compilation names constructor nodes, queries the left side and builds the right side.
    For example, the rewrite [f(x) = x] queries [f] and joins its result with [x].
    Builds on: CompileSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig DatabaseSig Syntax Model Sorts.
From Galois.Egraph Require Import Syntax CompileSig.

Import List.ListNotations.

Definition name_max (x y : positive) : positive :=
  match Pos.compare x y with
  | Lt => y
  | _ => x
  end.
TimeFun name_max.

(** The largest hole name in a pattern bounds the names that compilation must preserve. *)
Fixpoint pattern_max {A} (ns : list (pnode A)) : positive :=
  match ns with
  | [] => 1%positive
  | PHole h :: rest => name_max h (pattern_max rest)
  | _ :: rest => pattern_max rest
  end.
TimeFun pattern_max.

Definition term_name {A} (t : term A) : positive :=
  match t with
  | Var x => x
  | Lit _ => 1%positive
  end.
TimeFun term_name.

Definition atom_name_max {A} (a : atom A) : positive :=
  match a with
  | Fun _ _ args res =>
    fold_right (fun t m => name_max (term_name t) m)
      (match res with Some t => term_name t | None => 1%positive end) args
  | Prim _ _ args res =>
    fold_right (fun t m => name_max (term_name t) m) (term_name res) args
  end.
TimeFun atom_name_max.

(** The root countdown distinguishes the root without rescanning its prefix. *)
Definition next_root (r : option nat) : option nat :=
  match r with
  | Some (S n) => Some n
  | _ => None
  end.
TimeFun next_root.

(** A table keeps hole and literal terms and gives every constructor a fresh variable. *)
Fixpoint pattern_terms {A} (ns : list (pnode A)) (r : option nat)
    (root_name fresh : positive) : list (term A) * positive :=
  match ns with
  | [] => ([], fresh)
  | n :: rest =>
    let '(t, fresh') :=
      match n with
      | PHole h => (Var h, fresh)
      | PLit v => (Lit v, fresh)
      | PApp _ _ =>
        match r with
        | Some 0 => (Var root_name, fresh)
        | _ => (Var fresh, Pos.succ fresh)
        end
      end in
    let '(ts, last) := pattern_terms rest (next_root r) root_name fresh' in
    (t :: ts, last)
  end.
TimeFun pattern_terms.

Definition pattern_table {A} (p : fpat A) (root_name : positive)
    : list (term A) * positive :=
  match p with
  | FPat _ ns r => pattern_terms ns (Some r) root_name (Pos.succ root_name)
  end.
TimeFun pattern_table.

Definition pattern_get {A} (default : term A) (j : nat) (ts : list (term A)) : term A :=
  match nth_error ts j with
  | Some t => t
  | None => default
  end.
TimeFun pattern_get.

(** Each constructor contributes one query atom whose children read the term table. *)
Fixpoint pattern_atoms {A} (ns : list (pnode A)) (ts all : list (term A))
    : list (atom A) :=
  match ns, ts with
  | n :: rest, t :: tail =>
    match n with
    | PApp f children =>
      Fun A f (map (fun j => pattern_get (Var 1%positive) j all) children) (Some t) ::
        pattern_atoms rest tail all
    | _ => pattern_atoms rest tail all
    end
  | _, _ => []
  end.
TimeFun pattern_atoms.

(** Right-side constructors become ordered allocations with the same table references. *)
Fixpoint pattern_actions {A} (ns : list (pnode A)) (ts all : list (term A))
    : list (action A) :=
  match ns, ts with
  | n :: rest, t :: tail =>
    match n, t with
    | PApp f children, Var x =>
      Make x f (map (fun j => pattern_get (Var 1%positive) j all) children) ::
        pattern_actions rest tail all
    | _, _ => pattern_actions rest tail all
    end
  | _, _ => []
  end.
TimeFun pattern_actions.

Module CompileCode (V : VALUE_OPS) <: COMPILE_OPS V.
  Definition root_var (rw : rewrite V.t) : positive :=
    match rw with
    | Rewrite _ (FPat _ lnodes _) (FPat _ rnodes _) conditions =>
      Pos.succ (name_max (pattern_max lnodes)
        (name_max (pattern_max rnodes)
          (fold_right (fun a m => name_max (atom_name_max a) m) 1%positive conditions)))
    end.

  Definition flatten_pat (p : fpat V.t) (x : positive) : list (atom V.t) :=
    match p with
    | FPat _ ns _ => let ts := fst (pattern_table p x) in pattern_atoms ns ts ts
    end.

  Definition flatten_lhs (rw : rewrite V.t) : list (atom V.t) :=
    match rw with
    | Rewrite _ lp _ conditions => flatten_pat lp (root_var rw) ++ conditions
    end.

  Definition compile_rule (rw : rewrite V.t) : rule V.t :=
    match rw with
    | Rewrite _ lp (FPat _ ns r as rp) _ =>
      let x := root_var rw in
      let next := snd (pattern_table lp x) in
      let ts := fst (pattern_table rp next) in
      Rule V.t (flatten_lhs rw)
        (pattern_actions ns ts ts ++ [Union (Var x) (pattern_get (Var next) r ts)])
    end.

  Definition compile (ds : list decl) (rws : list (rewrite V.t)) (ans : list (rule V.t))
      : program V.t := Program V.t ds (map compile_rule rws ++ ans).
End CompileCode.

Module Compile (V : VALUE) <: COMPILE V.
  Include CompileCode V.
  Include COMPILE_SPEC V.
  Lemma compile_program : forall ds rws ans,
    decls V.t (compile ds rws ans) = ds /\
    rules V.t (compile ds rws ans) = map compile_rule rws ++ ans.
  Proof.
    intros ds rws ans. split; reflexivity.
  Qed.

  Lemma compile_query : forall rw, query V.t (compile_rule rw) = flatten_lhs rw.
  Proof.
    intros [lp [ns r] conditions]. reflexivity.
  Qed.

  Lemma compile_sorted : forall ds rws ans, rules_ok ds rws ans ->
    program_ok (compile ds rws ans).
  Proof. Admitted. (* STUB *)

  Lemma compile_valid : forall (M : model (V := V.t)) ds rws ans, rules_ok ds rws ans ->
    Forall (valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds)) rws ->
    Forall (rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds)) ans ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    valid_sorted V.prim V.merge M (compile ds rws ans).
  Proof. Admitted. (* STUB *)

  Lemma flatten_complete : forall ds w rw g tau c e,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g -> canonical_view w ->
    instantiates tau (lhs V.t rw) e -> represents w (Id c) e ->
    cond_in_view w tau (cond V.t rw) ->
    exists s j, matches V.prim w (flatten_lhs rw) s /\ represents_on g w tau s /\
      s (root_var rw) = Some (Id j) /\ same w c j /\
      exists f k, row w f k (Some (Id j)).
  Proof. Admitted. (* STUB *)

  Lemma present_represents : forall ds w rw g s tau c r,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    canonical_view w -> matches V.prim w (flatten_lhs rw) s ->
    s (root_var rw) = Some (Id c) -> represents_on g w tau s ->
    instantiates tau (rhs V.t rw) r ->
    present V.prim V.merge w s (actions V.t (compile_rule rw)) ->
    represents w (Id c) r.
  Proof. Admitted. (* STUB *)

End Compile.

Module CompileT (V : VALUE_T) <: COMPILE_ALL V.
  Include Compile V.
  TimeFun root_var.
  TimeFun flatten_pat.
  TimeFun flatten_lhs.
  TimeFun compile_rule.
  TimeFun compile.
  Definition c_compile : N := 1. (* STUB *)
  Definition k_compile : N := 1. (* STUB *)
  Lemma T_compile_le : forall ds rws ans,
    (T_compile ds rws ans <= c_compile *
      N.of_nat (fold_right (fun rw n => (rewrite_size rw + n)%nat) 0 rws +
        length ans + 1)%nat)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_compile_rule_valid : forall (M : model (V := V.t)) ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds) rw ->
    rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof. Admitted. (* STUB *)

  Lemma F2_compile_rule_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    rule_ok (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof. Admitted. (* STUB *)

  Lemma F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  Proof.
    intros [lp rp conditions]. reflexivity.
  Qed.

  Lemma T1_compile_split : forall ds rws ans,
    (T_compile ds rws ans <= fold_right (fun rw n => T_compile_rule rw + n) 0 rws +
      k_compile * N.of_nat (length rws + length ans + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_compile_rule_le : forall rw,
    (T_compile_rule rw <= k_compile * N.of_nat (rewrite_size rw + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The compiled rule's bit size is bounded by the square of its rewrite size. *)
  Lemma compile_rule_bits : forall rw,
    (N.of_nat (rule_bits (compile_rule rw)) <=
      c_compile * N.of_nat (rewrite_size rw + 1) * N.of_nat (rewrite_size rw + 1))%N.
  Proof. Admitted. (* STUB *)
End CompileT.
