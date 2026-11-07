(** * Public insertion-soundness clients

    The clients combine soundness with finite represented terms at allocated identifiers.
    For example, insertion of f(a) into a graph already containing a yields a sound new class.
    Builds on: EgraphInsertSpec and the arithmetic fixtures in EgraphGraphTest. *)

From Stdlib Require Import List PArith.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphSpec EgraphInsertSpec.
From Galois.Tests.Egraph Require Import EgraphGraphTest.
Import List.ListNotations.

Section PublicClients.
Context {K Sort V H F C : Type} (a : EggAlg.t K Sort V)
  (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
  (rules : list (EggRule.t K Sort V H F)).

(** A client uses the node insertion law to relate arbitrary terms of every output class. *)
Theorem symbolic_node_sound_client g n c h :
  EggSpec.encoding_laws a -> EggSpec.wf a g -> EggSpec.sound a adm facts rules g ->
  Egraph.add_node a g n = Some (c, h) ->
  forall d t u, EggSpec.represents a h d t -> EggSpec.represents a h d u ->
    EggEqual.rel a adm facts rules t u.
Proof.
  intros Hl Hwf Hsound Hadded.
  exact (EggInsertSpec.add_node_sound a adm facts rules g n c h Hl Hwf Hsound Hadded).
Qed.

(** A client composes term insertion soundness and WF using only the public operation laws. *)
Theorem symbolic_term_sound_client g e c h :
  EggSpec.encoding_laws a -> EggSpec.wf a g -> EggSpec.sound a adm facts rules g ->
  Egraph.add_term a g e = Some (c, h) ->
  EggSpec.wf a h /\ EggSpec.sound a adm facts rules h.
Proof.
  intros Hl Hwf Hsound Hadded.
  destruct (proj1 (EggSpec.add_term_represents a g e Hl Hwf) c h Hadded)
    as [Hrep [Hnew Hext]].
  split; [exact Hnew|].
  exact (EggInsertSpec.add_term_sound a adm facts rules Hl e g c h Hwf Hsound Hadded).
Qed.

End PublicClients.

Definition seed :=
  match Egraph.add_term arith Egraph.empty leaf_a with
  | Some (_, g) => g
  | None => Egraph.empty
  end.

Example seed_success :
  Egraph.add_term arith Egraph.empty leaf_a = Some (1%positive, seed).
Proof.
  vm_compute. reflexivity.
Qed.

(** The seed's WF evidence comes from the public typed-term insertion interface. *)
Theorem seed_wf : EggSpec.wf arith seed.
Proof.
  destruct (proj1 (EggSpec.add_term_represents arith Egraph.empty leaf_a
    arith_encoding_laws (EggSpec.empty_wf arith)) 1%positive seed seed_success)
    as [Hrep [Hwf Hext]].
  exact Hwf.
Qed.

(** The input graph is productive at an allocated identifier before the tested insertion. *)
Theorem seed_represents : EggSpec.represents arith seed 1%positive leaf_a.
Proof.
  exact (proj1 (proj1 (EggSpec.add_term_represents arith Egraph.empty leaf_a
    arith_encoding_laws (EggSpec.empty_wf arith)) 1%positive seed seed_success)).
Qed.

Definition inserted_node_graph :=
  match Egraph.add_node arith seed (Egraph.NApp true 4 [1%positive]) with
  | Some (_, g) => g
  | None => Egraph.empty
  end.

Example inserted_node_success :
  Egraph.add_node arith seed (Egraph.NApp true 4 [1%positive]) =
    Some (2%positive, inserted_node_graph).
Proof.
  vm_compute. reflexivity.
Qed.

(** The new class has a finite application witness built from the seed's old represented leaf. *)
Theorem inserted_node_productive :
  EggSpec.represents arith inserted_node_graph 2%positive (unary leaf_a).
Proof.
  apply (EggSpec.add_node_represents arith seed (Egraph.NApp true 4 [1%positive])
    2%positive inserted_node_graph (unary leaf_a) arith_encoding_laws seed_wf
    inserted_node_success).
  constructor; constructor; [exact seed_represents|constructor].
Qed.

Definition inserted_term_graph :=
  match Egraph.add_term arith seed arithmetic_term with
  | Some (_, g) => g
  | None => Egraph.empty
  end.

Example inserted_term_success :
  Egraph.add_term arith seed arithmetic_term = Some (6%positive, inserted_term_graph).
Proof.
  vm_compute. reflexivity.
Qed.

Example malformed_insertion_from_nonempty_seed_rejected :
  Egraph.add_node arith seed (Egraph.NApp true 0 []) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Section ProductiveClients.
Context {H F C : Type} (adm : EggSem.t nat nat C -> Prop)
  (facts : EggFact.t F nat bool nat C) (rules : list (EggRule.t nat bool nat H F)).

(** Inserting the seed leaf constructs a sound nonempty input for subsequent soundness clients. *)
Theorem seed_sound : EggSpec.sound arith adm facts rules seed.
Proof.
  exact (EggInsertSpec.add_term_sound arith adm facts rules arith_encoding_laws
    leaf_a Egraph.empty 1%positive seed (EggSpec.empty_wf arith)
    (EggInsertSpec.empty_sound arith adm facts rules) seed_success).
Qed.

(** Node soundness applies to a nonempty seed and an output class with a finite application. *)
Theorem productive_node_sound_client :
  EggSpec.represents arith inserted_node_graph 2%positive (unary leaf_a) /\
  EggSpec.sound arith adm facts rules inserted_node_graph.
Proof.
  split; [exact inserted_node_productive|].
  exact (EggInsertSpec.add_node_sound arith adm facts rules seed
    (Egraph.NApp true 4 [1%positive]) 2%positive inserted_node_graph
    arith_encoding_laws seed_wf seed_sound inserted_node_success).
Qed.

(** Term soundness applies after a prior allocation and supplies a represented two-sort term. *)
Theorem productive_term_sound_client :
  EggSpec.represents arith inserted_term_graph 6%positive arithmetic_term /\
  EggSpec.sound arith adm facts rules inserted_term_graph.
Proof.
  split.
  - exact (proj1 (proj1 (EggSpec.add_term_represents arith seed arithmetic_term
      arith_encoding_laws seed_wf) 6%positive inserted_term_graph inserted_term_success)).
  - exact (EggInsertSpec.add_term_sound arith adm facts rules arith_encoding_laws
      arithmetic_term seed 6%positive inserted_term_graph seed_wf seed_sound inserted_term_success).
Qed.

End ProductiveClients.
