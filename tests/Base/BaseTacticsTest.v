(** * Shared tactic contracts

    Symbolic goals exercise interface rewriting and option inversion without exposing containers.
    For example, set difference membership implies the right set does not contain the key.
    Builds on: BaseTactics. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseTactics.

Section MapGoals.
Context {K V : Type} (E : encoding K) (HE : encoding_laws E).
Variables (k : K) (v : V) (m : Map.t K V).
Hypothesis Hm : Map.wf E m.

Example simpl_map_set :
  Map.get E k (Map.set E k v m) = Some v.
Proof.
  simpl_map.
Qed.

Example simpl_map_remove :
  Map.get E k (Map.remove E k m) = None.
Proof.
  simpl_map.
Qed.

Example simpl_map_update :
  Map.get E k (Map.update E k (fun _ => Some v) m) = Some v.
Proof.
  simpl_map.
Qed.
End MapGoals.

Section SetGoals.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).
Variables (k : K) (s u : FinSet.t K).
Hypotheses (Hs : FinSet.wf E s) (Hu : FinSet.wf E u).

Example simpl_set_add : FinSet.mem E k (FinSet.add E k s) = true.
Proof.
  simpl_set.
Qed.

Example simpl_set_remove : FinSet.mem E k (FinSet.remove E k s) = false.
Proof.
  simpl_set.
Qed.

Example simpl_set_inter_empty :
  FinSet.mem E k (FinSet.inter s FinSet.empty) = false.
Proof.
  simpl_set. apply andb_false_r.
Qed.

Example set_solver_union :
  FinSet.mem E k (FinSet.union s u) = true ->
  FinSet.mem E k (FinSet.union u s) = true.
Proof.
  set_solver.
Qed.

Example set_solver_inter :
  FinSet.mem E k (FinSet.inter s u) = true -> FinSet.mem E k s = true.
Proof.
  set_solver.
Qed.

Example set_solver_diff :
  FinSet.mem E k (FinSet.diff s u) = true -> FinSet.mem E k u <> true.
Proof.
  set_solver.
Qed.
End SetGoals.

Example set_solver_residue (xs : list nat) : rev (rev xs) = xs.
Proof.
  set_solver. apply rev_involutive.
Qed.

Example inv_option_match (o : option nat) n :
  (match o with
  | Some k => Some (S k)
  | None => None
  end) = Some n ->
  exists k, o = Some k /\ n = S k.
Proof.
  intro H. inv_option. eauto.
Qed.

Example inv_option_pair (a b x y : nat) :
  Some (a, b) = Some (x, y) -> a = x /\ b = y.
Proof.
  intro H. inv_option. auto.
Qed.

Example inv_option_none (o : option nat) :
  o = None ->
  (match o with
  | Some _ => true
  | None => false
  end) = false.
Proof.
  intro H. inv_option. reflexivity.
Qed.

Example inv_option_clash (o : option nat) :
  (match o with
  | Some k => Some k
  | None => None
  end) = Some 0 ->
  o <> None.
Proof.
  intros H Hnone. inv_option.
Qed.
