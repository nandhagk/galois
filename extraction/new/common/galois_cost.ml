(* This module implements the extraction ABI. Counts and weights are erased. *)
type 'a t = 'a

let make value = value
let ret value = value
let bind value f = f value
let value value = value
let map f value = f value
let lift _weight f value = f value
let tick _count = ()
let step = ()
let tick_bits _key = ()
let refine value = value

(* The ABI deliberately raises if an extracted computation observes a count. *)
let ticks _value = failwith "GALOIS_COST_TICKS"
