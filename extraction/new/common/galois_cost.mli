(** The extraction ABI erases computational counts and proof-only refinements. *)
type 'a t = 'a

val make : 'a -> 'a t
val ret : 'a -> 'a t
val bind : 'a t -> ('a -> 'b t) -> 'b t
val value : 'a t -> 'a
val map : ('a -> 'b) -> 'a t -> 'b t
val lift : ('a -> 'weight) -> ('a -> 'b) -> 'a -> 'b t
val tick : 'count -> unit t
val step : unit t
val tick_bits : 'key -> unit t
val refine : 'a t -> 'a t

(** Raises [Failure "GALOIS_COST_TICKS"] if a computation violates cost erasure. *)
val ticks : 'a t -> 'count
