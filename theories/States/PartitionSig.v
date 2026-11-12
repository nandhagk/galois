(** * Token-partitioned states

    Token maps describe unions of states while retaining a separate state for each token.
    For example, inject stores one branch state under its branch token.
    Builds on: MapSig, LatticeSig and StateSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.

(** A partition is either unrestricted or a token map of stored states. *)
Inductive parts (A : Type) :=
  | PAll
  | PSome (m : A).

Arguments PAll {A}.
Arguments PSome {A} m.

(** The unrestricted partition is above every partition. *)
Definition parts_leb {A} (leb : A -> A -> bool) (a b : parts A) : bool :=
  match a, b with
  | _, PAll => true
  | PAll, PSome _ => false
  | PSome x, PSome y => leb x y
  end.
TimeFun parts_leb.

(** The unrestricted partition is never bottom. *)
Definition parts_is_bot {A} (is_bot : A -> bool) (a : parts A) : bool :=
  match a with
  | PAll => false
  | PSome x => is_bot x
  end.
TimeFun parts_is_bot.

(** Joining with the unrestricted partition is unrestricted. *)
Definition parts_join {A} (join : A -> A -> A) (a b : parts A) : parts A :=
  match a, b with
  | PAll, _ | _, PAll => PAll
  | PSome x, PSome y => PSome (join x y)
  end.
TimeFun parts_join.

Module Type PARTITION_LINK (Tk : KEY) (M : MAP Tk) (X : KEY) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t).
  (** The shared order compares stored parts, with absent codes at bottom. *)
  Parameter leb_parts : forall a b p s, P.leb a b = true -> M.find p a = Some s ->
    S.leb s (match M.find p b with Some s' => s' | None => S.bot end) = true.
  (** The shared bottom stores no part. *)
  Parameter bot_parts : forall p, M.find p P.bot = None.
End PARTITION_LINK.

(** A code is fresh when the candidate stores a nonbottom part the previous map lacks. *)
Definition fresh_part {A} (is_bot : A -> bool) (x y : option A) : option bool :=
  match x, y with
  | _, None => None
  | Some s, Some t => if is_bot t then None else if is_bot s then Some true else None
  | None, Some t => if is_bot t then None else Some true
  end.
TimeFun fresh_part.

(** Widening keeps previous parts and widens the nonbottom common ones. *)
Definition widen_part {A} (is_bot : A -> bool) (widen : A -> A -> A) (x y : option A)
    : option A :=
  match x, y with
  | Some s, Some t => if is_bot s then Some s else Some (widen s t)
  | Some s, None => Some s
  | None, _ => None
  end.
TimeFun widen_part.

Module Type PARTITION_OPS (X Tk : KEY_OPS) (M : MAP_OPS Tk) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (S : STATE_DOMAIN_OPS X L V)
    (P : LATTICE_OPS with Definition t := M.t S.t).
  Include STATE_DOMAIN_OPS X L V with Definition t := parts (M.t S.t)
    with Definition leb := parts_leb P.leb with Definition bot := PSome P.bot
    with Definition is_bot := parts_is_bot P.is_bot
    with Definition join := parts_join P.join
    with Definition top := @PAll (M.t S.t)
    with Definition wparam := S.wparam.
  Parameter inject : Tk.t -> S.t -> t.
  Parameter merge retag : Tk.t -> t -> t.
End PARTITION_OPS.

Module Type PARTITION_BASE (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P) :=
  PARTITION_OPS X Tk M L V S P <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type PARTITION_LAWS (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P)
    (Import D : PARTITION_BASE X Tk M L V S P PL).
  (** The unrestricted partition denotes every store. *)
  Parameter gamma_all : forall st, gamma PAll st.
  (** A token map denotes the union of its stored states. *)
  Parameter gamma_parts : forall p st,
    gamma (PSome p) st <-> exists k s, M.get k p = Some s /\ S.gamma s st.
  (** Injection stores exactly one token binding. *)
  Parameter inject_eq : forall k s, inject k s = PSome (M.set k s M.empty).
  (** Merging joins all stored states under the selected token. *)
  Parameter merge_eq : forall k p, merge k p =
    match p with
    | PAll => PAll
    | PSome m => inject k (M.fold (fun acc _ s => S.join s acc) m S.bot)
    end.
  (** Retagging collapses the old partition into the selected token. *)
  Parameter retag_eq : forall k p, retag k p = merge k p.
  (** Injection retains the injected state's concrete environments. *)
  Parameter gamma_inject : forall k s st, S.gamma s st -> gamma (inject k s) st.
  (** Merging retains every environment described by a partition. *)
  Parameter merge_sound : forall k p st, gamma p st -> gamma (merge k p) st.
End PARTITION_LAWS.

Module Type PARTITION (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P) :=
  PARTITION_BASE X Tk M L V S P PL <+ PARTITION_LAWS X Tk M L V S P PL.

Module Type PARTITION_TIME (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P)
    (Import D : PARTITION X Tk M L V S P PL).
  Include STATE_DOMAIN_TIME X L V D.
  Parameter T_inject : Tk.t -> S.t -> N.
  Parameter T_merge T_retag : Tk.t -> t -> N.
  Parameter c_partition : N.
  (** Injection charges the token encoding and the retained state. *)
  Parameter T_inject_le : forall k s, (T_inject k s <=
    c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  (** Assignment charges each part's own transfer and its token. *)
  Parameter T_assign_parts : forall x e p, (T_assign x e (PSome p) <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_assign x e (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** Havoc charges each part's own transfer and its token. *)
  Parameter T_havoc_parts : forall x p, (T_havoc x (PSome p) <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_havoc x (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** Assumption charges each part's own transfer and its token. *)
  Parameter T_assume_parts : forall g es p, (T_assume g es (PSome p) <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_assume g es (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** The shared constant pays for the shared order and join. *)
  Parameter c_lat_parts : (P.c_lat <= c_lat)%N.
  (** A token map is measured by the shared lattice, and top by one unit. *)
  Parameter size_parts : forall p, size p =
    match p with PAll => 1 | PSome m => P.size m + 1 end.
  (** Evaluation work follows the actual fold, including each join on its accumulator. *)
  Parameter eval_work_parts : forall e p, eval_work e p =
    match p with
    | PAll => 1
    | PSome m => fst (M.fold (fun acc k s =>
        (fst acc + S.eval_work e s + Tk.bits k + V.size (S.eval e s) + V.size (snd acc) + 1,
         V.join (S.eval e s) (snd acc))) m (1, V.bot))
    end.
End PARTITION_TIME.

Module Type PARTITION_T (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P) :=
  PARTITION X Tk M L V S P PL <+ PARTITION_TIME X Tk M L V S P PL.

Module Type PARTITION_PLAN (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P)
    (Import D : PARTITION_T X Tk M L V S P PL).
  Parameter k_partition : N.
  (** Evaluation joins the evaluated parts, and the unrestricted partition evaluates to top. *)
  Parameter F_eval : forall e p, eval e p =
    match p with
    | PAll => V.top
    | PSome m => M.fold (fun acc _ s => V.join (S.eval e s) acc) m V.bot
    end.

  (** Assignment changes each stored state at its original token. *)
  Parameter F1_assign : forall x e p k,
    match assign x e (PSome p) with
    | PAll => False
    | PSome m => M.get k m = option_map (S.assign x e) (M.get k p)
    end.
  (** Havoc changes each stored state at its original token. *)
  Parameter F2_havoc : forall x p k,
    match havoc x (PSome p) with
    | PAll => False
    | PSome m => M.get k m = option_map (S.havoc x) (M.get k p)
    end.
  (** Assumption changes each stored state at its original token. *)
  Parameter F3_assume : forall g es p k,
    match assume g es (PSome p) with
    | PAll => False
    | PSome m => M.get k m = option_map (S.assume g es) (M.get k p)
    end.
  (** Assignment keeps unrestricted partitions unrestricted. *)
  Parameter F1_assign_all : forall x e, assign x e PAll = PAll.
  (** Havoc keeps unrestricted partitions unrestricted. *)
  Parameter F2_havoc_all : forall x, havoc x PAll = PAll.
  (** Assumption keeps unrestricted partitions unrestricted. *)
  Parameter F3_assume_all : forall g es, assume g es PAll = PAll.
  (** Fresh nonbottom parts give up the partition, and other parts widen pointwise. *)
  Parameter F_widen : forall q a b, widen q a b =
    if leb b a then a else
    match a, b with
    | PSome m, PSome n =>
      if M.existsb (fun x => x) (M.merge (fresh_part S.is_bot) m n) then PAll
      else PSome (M.merge (widen_part S.is_bot (S.widen q)) m n)
    | _, _ => PAll
    end.
  (** The rank counts one for a token map plus the ranks of its nonbottom parts. *)
  Parameter F4_rank : forall q p, wrank q p =
    match p with
    | PAll => 0
    | PSome m => 1 + fold_right Nat.add 0 (map (fun c =>
        match M.find c m with
        | Some s => if S.is_bot s then 0 else S.wrank q s
        | None => 0
        end) (M.codes m))
    end.
  (** Collapse charging follows the actual changing join accumulator. *)
  Parameter T1_merge_fold : forall k p, (T_merge k (PSome p) <= k_partition *
    (M.T_fold (fun acc _ s => S.join s acc)
      (fun acc _ s => S.T_join s acc) p S.bot +
      T_inject k (M.fold (fun acc _ s => S.join s acc) p S.bot) + 1))%N.
  (** Retagging charges the merge it performs. *)
  Parameter T2_retag : forall k p, (T_retag k p <= k_partition * (T_merge k p + 1))%N.
End PARTITION_PLAN.

Module Type PARTITION_ALL (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (PL : PARTITION_LINK Tk M X L V S P) :=
  PARTITION_T X Tk M L V S P PL <+ PARTITION_PLAN X Tk M L V S P PL.
