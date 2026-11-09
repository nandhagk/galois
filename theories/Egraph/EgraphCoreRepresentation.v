(** * E-graph grammar and semantic predicates

    A single inductive grammar gives meaning to finite witnesses through possibly cyclic classes.
    For example, a leaf and its own unary application can belong to one productive class.
    Builds on: EgraphGraph, EgraphRules and EgraphEquality. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphRules EgraphEquality EgraphGraph.

Module EggRepresentation.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** The algebra's three key dictionaries distinguish different client values. *)
Record encoding_laws : Prop := Encoding_laws {
  op_encoding : BaseEncoding.encoding_laws (EggAlg.op_enc K Sort V a);
  sort_encoding : BaseEncoding.encoding_laws (EggAlg.sort_enc K Sort V a);
  var_encoding : BaseEncoding.encoding_laws (EggAlg.var_enc K Sort V a)
}.

Definition nodes_get (g : Egraph.t K Sort V) c :=
  Map.get Egraph.id_encoding c (Egraph.nodes g).

(** Representation unfolds a finite tree through nodes in the queried class. *)
Inductive represents (g : Egraph.t K Sort V) : Egraph.id -> EggTerm.t K Sort V -> Prop :=
  | rep_var : forall c i s v,
      Egraph.find a g i = Egraph.find a g c ->
      nodes_get g i = Some (Egraph.NVar s v) ->
      represents g c (EggTerm.Var s v)
  | rep_app : forall c i s op cs args,
      Egraph.find a g i = Egraph.find a g c ->
      nodes_get g i = Some (Egraph.NApp s op cs) ->
      Forall2 (represents g) cs args ->
      represents g c (EggTerm.App s op args).

(** Class equality compares the representatives returned by the implementation. *)
Definition same_class (g : Egraph.t K Sort V) c d : Prop :=
  Egraph.find a g c = Egraph.find a g d.

(** A local node has declared variables or allocated children of an accepted shape. *)
Definition node_typed (g : Egraph.t K Sort V) (n : Egraph.enode K Sort V) : Prop :=
  match n with
  | Egraph.NVar s v => EggAlg.var_sort a v = Some s
  | Egraph.NApp s op cs =>
    exists ss, Forall2 (fun c s => Egraph.sort_of a g c = Some s) cs ss /\
      EggAlg.op_shape a op ss s = true
  end.

(** Dirty memo keys retain historical syntax whose children still denote the same classes. *)
Definition memo_sound (g : Egraph.t K Sort V) : Prop :=
  forall key c, Map.get Egraph.id_encoding key (Egraph.memo g) = Some c ->
    exists i n historical,
      nodes_get g i = Some n /\
      same_class g i c /\
      Egraph.node_code a historical = key /\
      Egraph.canonical a g historical = Egraph.canonical a g n.

(** Structural validity retains the original forest, typing, productivity and memo domain. *)
Record structural_wf (g : Egraph.t K Sort V) : Prop := Structural_wf {
  forest_wf : UnionFind.wf Egraph.id_encoding (Egraph.uf g);
  nodes_wf : Map.wf Egraph.id_encoding (Egraph.nodes g);
  memo_wf : Map.wf Egraph.id_encoding (Egraph.memo g);
  allocation : forall c, (exists n, nodes_get g c = Some n) <-> (c < Egraph.next g)%positive;
  forest_domain : forall c, In c (UnionFind.keys Egraph.id_encoding (Egraph.uf g)) ->
    (c < Egraph.next g)%positive;
  class_sorts : forall c d sc sd, same_class g c d ->
    Egraph.sort_of a g c = Some sc -> Egraph.sort_of a g d = Some sd -> sc = sd;
  nodes_typed : forall c n, nodes_get g c = Some n -> node_typed g n;
  finite_witness : forall c n, nodes_get g c = Some n -> exists e, represents g c e;
  memo_correct : memo_sound g
}.

(** Maintained WF adds concrete parent, memo and pending-work coverage to structural validity. *)
Record wf (g : Egraph.t K Sort V) : Prop := Wf {
  wf_structural : structural_wf g;
  wf_kernel : Egraph.kernel_inv a g
}.

Coercion wf_structural : wf >-> structural_wf.

(** Clean graphs retain WF, canonical congruence closure and current complete memo indexing. *)
Record clean (g : Egraph.t K Sort V) : Prop := Clean {
  clean_wf : wf g;
  congruence_closed : forall i j n m, nodes_get g i = Some n -> nodes_get g j = Some m ->
    Egraph.canonical a g n = Egraph.canonical a g m -> same_class g i j;
  memo_current : forall key c, Map.get Egraph.id_encoding key (Egraph.memo g) = Some c ->
    exists i n, nodes_get g i = Some n /\ same_class g i c /\
      Egraph.node_code a (Egraph.canonical a g n) = key;
  memo_complete : forall i n, nodes_get g i = Some n ->
    exists c, Map.get Egraph.id_encoding
      (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g) = Some c /\
      same_class g i c
}.

(** Soundness relates all finite terms of each class by the client's generated equality. *)
Definition sound {H F C} (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) (g : Egraph.t K Sort V) : Prop :=
  forall c t u, represents g c t -> represents g c u -> EggEqual.rel a adm facts rules t u.

(** Class partitions agree on all identifiers, including unknown singleton keys. *)
Definition same_class_equal (g h : Egraph.t K Sort V) : Prop :=
  forall c d, same_class g c d <-> same_class h c d.

(** A node represents a term when its child identifiers represent that term's arguments. *)
Inductive node_represents (g : Egraph.t K Sort V) :
    Egraph.enode K Sort V -> EggTerm.t K Sort V -> Prop :=
  | node_rep_var : forall s v, node_represents g (Egraph.NVar s v) (EggTerm.Var s v)
  | node_rep_app : forall s op cs args, Forall2 (represents g) cs args ->
      node_represents g (Egraph.NApp s op cs) (EggTerm.App s op args).

(** An extension preserves every finite representation and every old class equality. *)
Definition extends (g h : Egraph.t K Sort V) : Prop :=
  (forall c e, represents g c e -> represents h c e) /\
  (forall c d, same_class g c d -> same_class h c d).

End Graph.

End EggRepresentation.
