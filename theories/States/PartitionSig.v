(** * Token-partitioned states

    Token maps describe unions of states while retaining a separate state for each token.
    For example, inject stores one branch state under its branch token.
    Builds on: MapSig, LatticeSig and StateSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import BigO.
From Galois.Base Require Import KeySig MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.

Module Type PARTITION_OPS (X Tk : KEY_OPS) (M : MAP_OPS Tk) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) (S : STATE_DOMAIN_OPS X L V)
    (P : LATTICE_OPS with Definition t := M.t S.t).
  Include STATE_DOMAIN_OPS X L V with Definition t := M.t S.t
    with Definition leb := P.leb with Definition bot := P.bot
    with Definition is_bot := P.is_bot with Definition join := P.join
    with Definition wparam := S.wparam.
  Parameter inject : Tk.t -> S.t -> t.
  Parameter merge retag : Tk.t -> t -> t.
End PARTITION_OPS.

Module Type PARTITION_BASE (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t) :=
  PARTITION_OPS X Tk M L V S P <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.

Module Type PARTITION_LAWS (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t)
    (Import D : PARTITION_BASE X Tk M L V S P).
  (** Partition concretization is the union of its stored states. *)
  Parameter gamma_parts : forall p st,
    gamma p st <-> exists k s, M.get k p = Some s /\ S.gamma s st.
  (** Injection stores exactly one token binding. *)
  Parameter inject_eq : forall k s, inject k s = M.set k s M.empty.
  (** Merging joins all stored states under the selected token. *)
  Parameter merge_eq : forall k p,
    merge k p = inject k (M.fold (fun acc _ s => S.join s acc) p S.bot).
  (** Retagging collapses the old partition into the selected token. *)
  Parameter retag_eq : forall k p, retag k p = merge k p.
  (** Injection retains the injected state's concrete environments. *)
  Parameter gamma_inject : forall k s st, S.gamma s st -> gamma (inject k s) st.
  (** Merging retains every environment described by a partition. *)
  Parameter merge_sound : forall k p st, gamma p st -> gamma (merge k p) st.
  (* SIG-QUESTION: Empty Tk.t makes gamma_parts incompatible with gamma_top.
     The design supplies no inhabited token or separate top constructor. *)
  (* SIG-QUESTION: P shares the map carrier but has no operation correspondence to
     MapLatticeCode Tk M S. An unrelated map lattice can select a nonempty P.bot or
     reversed P.leb, invalidating gamma_bot or gamma_mono under gamma_parts.
     A shared-instance operation pin or a semantic correspondence bundle is missing. *)
End PARTITION_LAWS.

Module Type PARTITION (X Tk : KEY) (M : MAP Tk) (L : LANG)
    (V : VALUE_DOMAIN L) (S : STATE_DOMAIN X L V)
    (P : LATTICE with Definition t := M.t S.t) :=
  PARTITION_BASE X Tk M L V S P <+ PARTITION_LAWS X Tk M L V S P.

Module Type PARTITION_TIME (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (Import D : PARTITION X Tk M L V S P).
  Include STATE_DOMAIN_TIME X L V D.
  Parameter T_inject : Tk.t -> S.t -> N.
  Parameter T_merge T_retag : Tk.t -> t -> N.
  Parameter c_partition : N.
  (** Injection charges the token encoding and the retained state. *)
  Parameter T_inject_le : forall k s, (T_inject k s <=
    c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  (** Assignment charges each part's own transfer and its token. *)
  Parameter T_assign_parts : forall x e p, (T_assign x e p <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_assign x e (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** Havoc charges each part's own transfer and its token. *)
  Parameter T_havoc_parts : forall x p, (T_havoc x p <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_havoc x (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** Assumption charges each part's own transfer and its token. *)
  Parameter T_assume_parts : forall g es p, (T_assume g es p <= c_partition *
    (fold_right N.add 0%N (map (fun ks => S.T_assume g es (snd ks) +
      N.of_nat (Tk.bits (fst ks) + 1)) (M.elements p)) + 1))%N.
  (** Evaluation work follows the actual fold, including each join on its accumulator. *)
  Parameter eval_work_parts : forall e p, eval_work e p =
    fst (M.fold (fun acc k s =>
      (fst acc + S.eval_work e s + Tk.bits k + V.size (S.eval e s) + V.size (snd acc) + 1,
       V.join (S.eval e s) (snd acc))) p (1, V.bot)).
End PARTITION_TIME.

Module Type PARTITION_T (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t) :=
  PARTITION X Tk M L V S P <+ PARTITION_TIME X Tk M L V S P.

Module Type PARTITION_PLAN (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t)
    (Import D : PARTITION_T X Tk M L V S P).
  Parameter k_partition : N.
  (** Evaluation joins the evaluated parts into a value accumulator. *)
  Parameter F_eval : forall e p,
    eval e p = M.fold (fun acc _ s => V.join (S.eval e s) acc) p V.bot.
  (** Assignment changes each stored state at its original token. *)
  Parameter F1_assign : forall x e p k,
    M.get k (assign x e p) = option_map (S.assign x e) (M.get k p).
  (** Havoc changes each stored state at its original token. *)
  Parameter F2_havoc : forall x p k,
    M.get k (havoc x p) = option_map (S.havoc x) (M.get k p).
  (** Assumption changes each stored state at its original token. *)
  Parameter F3_assume : forall g es p k,
    M.get k (assume g es p) = option_map (S.assume g es) (M.get k p).
  (** The proposed partition rank adds the ranks of stored parts. *)
  Parameter F4_rank : forall q p, M.wf p ->
    wrank q p = fold_right Nat.add 0 (map (fun ks => S.wrank q (snd ks)) (M.elements p)).
  (* SIG-QUESTION: Pointwise widening can introduce a fresh token with positive rank.
     Its sum then increases, contradicting wrank_widen_le. No support credit is specified. *)
  (** Collapse charging follows the actual changing join accumulator. *)
  Parameter T1_merge_fold : forall k p, (T_merge k p <= k_partition *
    (M.T_fold (fun acc _ s => S.join s acc)
      (fun acc _ s => S.T_join s acc) p S.bot +
      T_inject k (M.fold (fun acc _ s => S.join s acc) p S.bot) + 1))%N.
  (** Retagging charges the merge it performs. *)
  Parameter T2_retag : forall k p, (T_retag k p <= k_partition * (T_merge k p + 1))%N.
End PARTITION_PLAN.

Module Type PARTITION_ALL (X Tk : KEY_T) (M : MAP_T Tk) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (S : STATE_DOMAIN_T X L V)
    (P : LATTICE_T with Definition t := M.t S.t) :=
  PARTITION_T X Tk M L V S P <+ PARTITION_PLAN X Tk M L V S P.
