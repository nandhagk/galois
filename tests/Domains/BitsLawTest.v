(** * Word payload semantic clients

    A constant word payload exports meaning and refinement laws.
    For example, a wrapped constant is described by its singleton payload.
    Builds on: Const and BitsLang. *)

From Stdlib Require Import ZArith.
From Galois.Domains Require Import BitsLang Const.

Module Point := ConstWord WordLanguage.
Definition point_constant_law := Point.pconst_sound.
Definition point_meet_law := Point.pgamma_meet.
Definition point_monotonicity_law := Point.pgamma_mono.
Definition point_singleton_law := Point.ppoint_sound.
