(** * Block language for imperative and SSA programs

    Functions contain blocks whose exits pass values to successor parameters.
    For example, a return exit returns the values of its listed variables.
    Builds on: Stdlib lists and positive identifiers. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Std.

Inductive exit (X G : Type) : Type :=
  | Jump (b : positive) (args : list X)
  | Branch (g : G) (xs : list X) (b1 : positive) (a1 : list X)
      (b2 : positive) (a2 : list X)
  | Return (xs : list X).

Arguments Jump {X G}.
Arguments Branch {X G}.
Arguments Return {X G}.

Record block (X K G : Type) : Type := Block {
  params : list X;
  code : list (X * K * list X);
  term : exit X G
}.

Record func (X K G : Type) : Type := Func {
  entry : positive;
  inputs : list X;
  blocks : list (positive * block X K G)
}.

Inductive result (C : Type) : Type :=
  | Returned (cs : list C)
  | Wrong
  | Timeout.

Arguments Returned {C}.
Arguments Wrong {C}.
Arguments Timeout {C}.

(** Imperative exits pass no block arguments. *)
Definition imp_exit {X G} (e : exit X G) : Prop :=
  match e with
  | Jump _ args => args = nil
  | Branch _ _ _ a1 _ a2 => a1 = nil /\ a2 = nil
  | Return _ => True
  end.

(** An imperative function has no block parameters or edge arguments. *)
Definition imp_form {K G} (p : func positive K G) : Prop :=
  Forall (fun item => params _ _ _ (snd item) = nil /\ imp_exit (term _ _ _ (snd item)))
    (blocks _ _ _ p).

Module Type OPS.
  Parameter K G C : Type.
  Parameter eval : K -> list C -> option C.
  Parameter test : G -> list C -> option bool.
  Parameter mov : K.
End OPS.

Module Type LAWS (O : OPS).
  (** The move operator returns its sole operand. *)
  Parameter eval_mov : forall c, O.eval O.mov (c :: nil) = Some c.
End LAWS.

(** Environments are association lists, with the newest binding first. *)
Definition env (C : Type) := list (positive * C).

Fixpoint lookup {C} (x : positive) (s : env C) : option C :=
  match s with
  | nil => None
  | (y, c) :: rest => if Pos.eqb x y then Some c else lookup x rest
  end.

TimeFun lookup.

Fixpoint read_vars {C} (s : env C) (xs : list positive) : option (list C) :=
  match xs with
  | nil => Some nil
  | x :: rest =>
      match lookup x s, read_vars s rest with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end
  end.

TimeFun read_vars.

Fixpoint bind_vars {C} (xs : list positive) (cs : list C) (s : env C) : option (env C) :=
  match xs, cs with
  | nil, nil => Some s
  | x :: rest, c :: values => bind_vars rest values ((x, c) :: s)
  | _, _ => None
  end.

TimeFun bind_vars.

Fixpoint find_block {K G} (b : positive) (bs : list (positive * block positive K G)) :
    option (block positive K G) :=
  match bs with
  | nil => None
  | (id, body) :: rest => if Pos.eqb b id then Some body else find_block b rest
  end.

TimeFun find_block.

Fixpoint exec_code {K C} (eval : K -> list C -> option C)
    (instructions : list (positive * K * list positive)) (s : env C) : option (env C) :=
  match instructions with
  | nil => Some s
  | (x, op, args) :: rest =>
      match read_vars s args with
      | None => None
      | Some cs =>
          match eval op cs with
          | None => None
          | Some c => exec_code eval rest ((x, c) :: s)
          end
      end
  end.

TimeFun exec_code.

Fixpoint steps {K G C} (eval : K -> list C -> option C)
    (test : G -> list C -> option bool) (fuel : nat) (p : func positive K G) (b : positive)
    (args : list C) (s : env C) : result C :=
    match fuel with
    | O => Timeout
    | S remaining =>
        match find_block b (blocks _ _ _ p) with
        | None => Wrong
        | Some body =>
            match bind_vars (params _ _ _ body) args s with
            | None => Wrong
            | Some entered =>
                match exec_code eval (code _ _ _ body) entered with
                | None => Wrong
                | Some finished =>
                    match term _ _ _ body with
                    | Jump next actuals =>
                        match read_vars finished actuals with
                        | Some values => steps eval test remaining p next values finished
                        | None => Wrong
                        end
                    | Branch guard operands yes yes_args no no_args =>
                        match read_vars finished operands with
                        | None => Wrong
                        | Some values =>
                            match test guard values with
                            | None => Wrong
                            | Some choice =>
                                let next := if choice then yes else no in
                                let actuals := if choice then yes_args else no_args in
                                match read_vars finished actuals with
                                | Some passed => steps eval test remaining p next passed finished
                                | None => Wrong
                                end
                            end
                        end
                    | Return values =>
                        match read_vars finished values with
                        | Some returned => Returned returned
                        | None => Wrong
                        end
                    end
                end
            end
        end
    end.

TimeFun blocks.
TimeFun params.
TimeFun code.
TimeFun term.
TimeFun steps.

Definition run_with {K G C} (eval : K -> list C -> option C)
    (test : G -> list C -> option bool) (fuel : nat)
    (p : func positive K G) (args : list C) : result C :=
  match bind_vars (inputs _ _ _ p) args nil with
  | Some s => steps eval test fuel p (entry _ _ _ p) nil s
  | None => Wrong
  end.

TimeFun inputs.
TimeFun entry.
TimeFun run_with.

Module Interp (O : OPS).
  Definition run := run_with O.eval O.test.
End Interp.

(** An edge names a successor of a block exit. *)
Definition successor {X G} (e : exit X G) (b : positive) : Prop :=
  match e with
  | Jump target _ => b = target
  | Branch _ _ yes _ no _ => b = yes \/ b = no
  | Return _ => False
  end.

(** A path follows block exits from its first identifier to its last. *)
Inductive path {K G} (p : func positive K G) : positive -> list positive -> positive -> Prop :=
  | path_here b : path p b (b :: nil) b
  | path_next b body next rest target :
      In (b, body) (blocks _ _ _ p) -> successor (term _ _ _ body) next ->
      path p next rest target -> path p b (b :: rest) target.

Definition dominates {K G} (p : func positive K G) (d b : positive) : Prop :=
  forall route, path p (entry _ _ _ p) route b -> In d route.

Definition exit_uses {G} (e : exit positive G) : list positive :=
  match e with
  | Jump _ args => args
  | Branch _ xs _ yes _ no => xs ++ yes ++ no
  | Return xs => xs
  end.

TimeFun exit_uses.

Definition block_defs {K G} (b : block positive K G) : list positive :=
  params _ _ _ b ++ map (fun instruction => fst (fst instruction)) (code _ _ _ b).

TimeFun block_defs.

Definition use_at {K G} (b : block positive K G) (x : positive) (i : nat) : Prop :=
  (exists op args dst, nth_error (code _ _ _ b) i = Some (dst, op, args) /\ In x args) \/
  (i = length (code _ _ _ b) /\ In x (exit_uses (term _ _ _ b))).

Definition def_before {K G} (b : block positive K G) (x : positive) (i : nat) : Prop :=
  In x (params _ _ _ b) \/
  exists j op args, j < i /\ nth_error (code _ _ _ b) j = Some (x, op, args).

(** SSA definitions are unique and dominate each use, including uses on outgoing edges. *)
Definition ssa_wf {K G} (p : func positive K G) : Prop :=
  NoDup (map fst (blocks _ _ _ p)) /\
  NoDup (inputs _ _ _ p ++ concat (map (fun item => block_defs (snd item)) (blocks _ _ _ p))) /\
  (forall id body x i, In (id, body) (blocks _ _ _ p) -> use_at body x i ->
    In x (inputs _ _ _ p) \/ def_before body x i \/
    exists def_id def_body, In (def_id, def_body) (blocks _ _ _ p) /\
      def_id <> id /\ In x (block_defs def_body) /\ dominates p def_id id).
