(** * Word payload semantic clients

    A constant word payload exports meaning and refinement laws.
    For example, a wrapped constant is described by its singleton payload.
    Builds on: Const and BitsLang. *)

(* Groups:
   - Fixtures: the constant word domain over the word language.
   - Laws: the constant, meet, monotonicity and singleton laws that the domain exports. *)

From Stdlib Require Import ZArith.
From Galois.Domains Require Import BitsLang Const.

(** * Fixtures *)

(** The constant word domain over the word language. *)
Module Point := ConstWord WordLanguage.

(** * Laws *)

(** The constant law of the domain is sound. *)
Definition point_constant_law := Point.pconst_sound.
(** The meet law of the domain is exported. *)
Definition point_meet_law := Point.pgamma_meet.
(** The monotonicity law of the domain is exported. *)
Definition point_monotonicity_law := Point.pgamma_mono.
(** The singleton law of the domain is sound. *)
Definition point_singleton_law := Point.ppoint_sound.
