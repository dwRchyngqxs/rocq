type ('a, 'b) reduction =
(*| RHRule (* Rewrite rules *)*)
| RHCast (* Head cast removal *)
| RHBeta (* Head beta: applied lambda to substitution *)
| RHZeta (* Head zeta: letin to substitution *)
| RHZetaMatch of 'a (* Head zetamatch: match-letin to substitution *)
| RHDelta of 'b option (* Head delta: name resolution *)
| RHEta (* Head eta expansion: expand lambda *)
| RHEtaPrime
(* Head eta reduction:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| RHEvar (* Head evar: evar resolution + context substitution *)
| RHFix (* Head fix: push fixpoint inward when allowed to *)
| RHFixPrime (* Head fixprime: push fixpoint inward *)
| RHCofix (* Head cofix: match or project a cofix *)
| RHCofixPrime (* Head cofixprime: push cofix inward *)
| RHMatch (* Head match: match or project on a constructor *)
(* TODO: match UIP? *)
| RHInferUnique (* Head unique value inference: reduce match on a UIP type *)
| RHead (* Any head reduction *)
| RCbv (* Next reduction step of a call-by-value strategy *)
| RCbn (* Next reduction step of a call-by-name strategy *)
| RLazy (* Next reduction step of a call-by-need / lazy strategy *)

val map_reduction : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) reduction -> ('c, 'd) reduction
val step : (Names.inductive * int * int, Evaluable.t) reduction -> Reductionops.e_reduction_function