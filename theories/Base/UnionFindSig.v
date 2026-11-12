(** * Union-find signatures

    Union by size and path compression preserve representatives.
    For example, union reports the winning root and the root that it links.
    Builds on: Stdlib arithmetic and lists, and Argent time and asymptotic bounds. *)

From Stdlib Require Import List PArith NArith Arith.
From Argent Require Import Time BigO.

Module Type UNION_FIND_OPS.
  Parameter t : Type.
  Parameter empty : t.
  Parameter add   : positive -> t -> t.
  Parameter find  : positive -> t -> positive * t.
  Parameter union : positive -> positive -> t -> option (positive * positive) * t.
End UNION_FIND_OPS.

Module Type UNION_FIND_LAWS (Import U : UNION_FIND_OPS).
  (* spec: wf mem repr size_of card width *)
  Parameter wf      : t -> Prop.
  Parameter mem     : t -> positive -> Prop.
  Parameter repr    : t -> positive -> positive.
  Parameter size_of : t -> positive -> nat.
  Parameter card    : t -> nat.
  Parameter width   : t -> nat.
  (** The empty structure has a well-formed parent forest. *)
  Parameter wf_empty : wf empty.
  (** Adding a singleton retains a well-formed forest. *)
  Parameter wf_add   : forall x u, wf u -> wf (add x u).
  (** Path compression retains a well-formed forest. *)
  Parameter wf_find  : forall x u, wf u -> wf (snd (find x u)).
  (** Union retains a well-formed forest. *)
  Parameter wf_union : forall x y u, wf u -> wf (snd (union x y u)).
  (** Adding a key extends membership by that key. *)
  Parameter mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x).
  (** Finding leaves membership unchanged. *)
  Parameter mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y).
  (** Union adds its queried keys to membership. *)
  Parameter mem_union : forall x y u z, wf u ->
    (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  (** Absent keys represent themselves in the empty structure. *)
  Parameter repr_empty : forall x, repr empty x = x.
  (** Every representative represents itself. *)
  Parameter repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x.
  (** Adding a singleton leaves representatives unchanged. *)
  Parameter repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y.
  (** Finding returns the queried key representative. *)
  Parameter find_repr  : forall x u, wf u -> fst (find x u) = repr u x.
  (** Path compression leaves every representative unchanged. *)
  Parameter find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y.
  (** A redundant union leaves representatives unchanged. *)
  Parameter union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z.
  (** A successful union redirects the losing class to the winning root. *)
  Parameter union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z.
  (** Union links the smaller class under the larger class. *)
  Parameter union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w.
  (** The winning class size includes both merged classes. *)
  Parameter size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l.
  (** A member class fits within the total membership count. *)
  Parameter size_of_le_card : forall u x, wf u -> mem u x -> size_of u x <= card u.
  (** The empty structure has no member. *)
  Parameter card_empty : card empty = 0.
  (** Adding a key increases cardinality by at most one. *)
  Parameter card_add   : forall x u, wf u -> card (add x u) <= card u + 1.
  (** Finding leaves cardinality unchanged. *)
  Parameter card_find  : forall x u, wf u -> card (snd (find x u)) = card u.
  (** Union adds at most its two queried keys. *)
  Parameter card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2.
  (** The stored width covers each member key. *)
  Parameter width_mem  : forall u x, wf u -> mem u x -> Pos.size_nat x <= width u.
  Parameter size_of_fresh : forall u x, wf u -> ~ mem u x -> size_of u x = 1.
  Parameter size_of_repr : forall u x, wf u -> size_of u x = size_of u (repr u x).
  Parameter size_of_add : forall x u y, wf u -> size_of (add x u) y = size_of u y.
  Parameter size_of_find : forall x u y, wf u -> size_of (snd (find x u)) y = size_of u y.
  Parameter size_of_union_other : forall x y u o u1 z, wf u -> union x y u = (o, u1) ->
  (forall w l, o = Some (w, l) -> repr u z <> w /\ repr u z <> l) ->
  size_of u1 z = size_of u z.

  Parameter width_empty : width empty = 0.
  Parameter width_add : forall x u, wf u ->
  width (add x u) <= Nat.max (width u) (Pos.size_nat x).
  Parameter width_find : forall x u, wf u -> width (snd (find x u)) <= width u.
  Parameter width_union : forall x y u, wf u ->
  width (snd (union x y u)) <= Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)).
End UNION_FIND_LAWS.

Module Type UNION_FIND := UNION_FIND_OPS <+ UNION_FIND_LAWS.

Module Type UNION_FIND_TIME (Import U : UNION_FIND).
  Parameter T_add   : positive -> t -> N.
  Parameter T_find  : positive -> t -> N.
  Parameter T_union : positive -> positive -> t -> N.
  Parameter c_uf : N.
  (** Adding charges the queried key and the membership counter width. *)
  Parameter T_add_le : forall x u, (wf u ->
    T_add x u <= c_uf * N.of_nat (Pos.size_nat x + Nat.log2 (card u) + 2))%N.
  (** Finding charges a logarithmic path at the maximum encountered key width. *)
  Parameter T_find_le : forall x u, (wf u ->
    T_find x u <= c_uf * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  (** Union charges two finds and a root link at the resulting membership width. *)
  Parameter T_union_le : forall x y u, (wf u ->
    T_union x y u <= c_uf * N.of_nat (Nat.log2 (card u + 2) + 1) *
      N.of_nat (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1))%N.
  (* Published asymptotic bound. *)
  (** Finding has logarithmic path length and per-bit lookup cost. *)
  Parameter find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => N.of_nat ((Nat.log2 (card (snd xu)) + 1) *
      (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1)))
    (fun xu => T_find (fst xu) (snd xu)).
End UNION_FIND_TIME.

Module Type UNION_FIND_T := UNION_FIND <+ UNION_FIND_TIME.

Module Type UNION_FIND_PLAN (Import U : UNION_FIND_T).
  (* internals the chain talks about *)
  Parameter parent_of : positive -> t -> positive.
  Parameter walk_step : t -> positive * list positive ->
    positive * list positive + positive * list positive.
  Parameter walk      : positive -> t -> positive * list positive.
  Parameter compress  : positive -> list positive -> t -> t.
  Parameter link      : positive -> positive -> t -> t.
  Parameter T_parent_of : positive -> t -> N.
  Parameter T_walk_step : t -> positive * list positive -> N.
  Parameter T_walk      : positive -> t -> N.
  Parameter T_compress  : positive -> list positive -> t -> N.
  Parameter T_link      : positive -> positive -> t -> N.
  Parameter k_get k_step k_walk k_comp k_link : N.
  (** A root has no parent edge to a different key. *)
  Definition is_root (u : t) (x : positive) : Prop := parent_of x u = x.
  (** Ghost ranks increase along parent edges and fit within root class sizes. *)
  Definition ranked (u : t) (rk : positive -> nat) : Prop :=   (* ghost ranks: nothing is stored *)
    (forall x, mem u x -> ~ is_root u x -> rk x < rk (parent_of x u)) /\
    (forall r, mem u r -> is_root u r -> 2 ^ rk r <= size_of u r).
  (* F: functional chain *)
  (** Every well-formed forest admits increasing ghost ranks. *)
  Parameter F1_ranked    : forall u, wf u -> exists rk, ranked u rk.
  (** Every member rank is bounded by the logarithm of cardinality. *)
  Parameter F2_rank_log : forall u rk x, wf u -> ranked u rk -> mem u x ->
    rk x <= Nat.log2 (card u).
  (** Walking reaches the queried key representative. *)
  Parameter F3_walk_root : forall x u, wf u -> fst (walk x u) = repr u x.
  (** The recorded path has logarithmic length and stays within the queried class. *)
  Parameter F4_walk_path : forall x u, wf u -> mem u x ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  (** Compressing nonroot class members retains the ghost rank invariant. *)
  Parameter F5_compress  : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) -> ranked (compress r path u) rk.
  (** Linking by class size admits an updated ghost rank at the winning root. *)
  Parameter F6_link : forall u rk w l, wf u -> ranked u rk ->
    is_root u w -> is_root u l -> w <> l ->
    size_of u l <= size_of u w ->
    ranked (link w l u) (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  (* T: time chain; T_find_le follows from T3, T4 and F4, T_union_le from T_find_le twice and T5 *)
  (** Reading a parent charges the queried positive key bits. *)
  Parameter T1_parent_of : forall x u, (T_parent_of x u <= k_get * N.of_nat (Pos.size_nat x + 1))%N.
  (** A member walk step charges the stored width budget. *)
  Parameter T2_walk_step : forall u s, (wf u -> mem u (fst s) ->
    T_walk_step u s <= k_step * N.of_nat (width u + 1))%N.
  (** A logarithmic rank potential pays the bounded walk loop. *)
  Parameter T3_walk      : forall x u, (wf u ->
    T_walk x u <= k_walk * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  (** Compression charges each path update at the stored width budget. *)
  Parameter T4_compress  : forall r path u, (wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * N.of_nat (length path + 1) * N.of_nat (width u + 1))%N.
  (** Linking charges root keys and the class size counter width. *)
  Parameter T5_link      : forall w l u, (wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * N.of_nat (width u + Nat.log2 (card u) + 2))%N.
End UNION_FIND_PLAN.

Module Type UNION_FIND_ALL := UNION_FIND_T <+ UNION_FIND_PLAN.
