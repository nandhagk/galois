(** * IFDS and IDE problem dictionaries

    Facts have a finite support list and values have no enumeration field.
    For example, None is the distinguished zero fact at every program point.
    Builds on: ProgramIcfg and FrameworkMicro. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro.
Import Cost.Notations.

Module IfdsData.

(** The fact inventory supports finite rows without enumerating a value carrier. *)
Record t (N E P D : Type) := Make {
  icfg : Icfg.t N E P;
  fact_enc : encoding D;
  facts : list D;
  flow_c : E -> option D -> Cost.t (list (option D))
}.
Arguments Make {N E P D}.
Arguments icfg {N E P D}.
Arguments fact_enc {N E P D}.
Arguments facts {N E P D}.
Arguments flow_c {N E P D}.

Definition flow {N E P D} (I : t N E P D) e d := Cost.value (flow_c I e d).

(** Pure exploded-flow readers are primitive client callbacks. *)
Definition of_pure {N E P D} cfg enc facts flow : t N E P D :=
  Make cfg enc facts (fun e d => Cost.step ;; Cost.ret (flow e d)).

End IfdsData.

Module Ide.

(** Weights are symbolic functions and both application and composition are charged. *)
Record t (N E P D A F : Type) := Make {
  ifds : IfdsData.t N E P D;
  values : lattice A;
  micro : Micro.t A F;
  weight_c : E -> option D -> option D -> Cost.t F
}.
Arguments Make {N E P D A F}.
Arguments ifds {N E P D A F}.
Arguments values {N E P D A F}.
Arguments micro {N E P D A F}.
Arguments weight_c {N E P D A F}.

Definition weight {N E P D A F} (I : t N E P D A F) e d d' :=
  Cost.value (weight_c I e d d').

End Ide.

Module Ifds.

(** The public IFDS namespace owns construction and the IDE conversion together. *)
Definition t := IfdsData.t.
Definition Make := @IfdsData.Make.
Definition icfg := @IfdsData.icfg.
Definition fact_enc := @IfdsData.fact_enc.
Definition facts := @IfdsData.facts.
Definition flow_c := @IfdsData.flow_c.
Definition flow := @IfdsData.flow.
Definition of_pure := @IfdsData.of_pure.
Arguments Make {N E P D}.
Arguments icfg {N E P D}.
Arguments fact_enc {N E P D}.
Arguments facts {N E P D}.
Arguments flow_c {N E P D}.
Arguments flow {N E P D}.
Arguments of_pure {N E P D}.

(** IFDS is IDE with Boolean jump weights and unit values. *)
Definition as_ide {N E P D} (I : t N E P D) : Ide.t N E P D unit bool :=
  Ide.Make I unit_lattice Micro.boolean (fun _ _ _ => Cost.ret true).

(** None is supported independently of the finite inventory of ordinary facts. *)
Definition fact_supported {N E P D} (I : t N E P D) (d : option D) : Prop :=
  match d with
  | None => True
  | Some d => In d (facts I)
  end.

(** Flow closure covers listed edges and supported inputs without requiring graph closure. *)
Definition flow_closed {N E P D} (I : t N E P D) : Prop :=
  forall e d d', In e (Cfg.edges (Icfg.cfg (icfg I))) -> fact_supported I d ->
    In d' (flow I e d) -> fact_supported I d'.

(** Value-start support concerns its fact independently of node and encoding laws. *)
Definition seed_supported {N E P D} (I : t N E P D) (start : N * option D) : Prop :=
  fact_supported I (snd start).

End Ifds.
