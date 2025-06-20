type ('a, 'b, 'c) reduction =
(*| RHRule (* Rewrite rules *)*)
| RHCast of 'c Locus.occurrences_gen (* Head cast removal *)
| RHBeta of 'c Locus.occurrences_gen
(* Head beta: applied lambda to substitution *)
| RHZeta of 'c Locus.occurrences_gen (* Head zeta: letin to substitution *)
| RHZetaMatch of 'a * 'c Locus.occurrences_gen
(* Head zetamatch: match-letin to substitution *)
| RHDelta of 'b option * 'c Locus.occurrences_gen
(* Head delta: name resolution *)
| RHEta (* Head eta expansion: expand lambda *)
| RHEtaPrime of 'c Locus.occurrences_gen
(* Head eta reduction:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| RHEvar of 'c Locus.occurrences_gen
(* Head evar: evar resolution + context substitution *)
| RHFix of 'c Locus.occurrences_gen
(* Head fix: push fixpoint inward when allowed to *)
| RHFixPrime of 'c Locus.occurrences_gen
(* Head fixprime: push fixpoint inward *)
| RHCofix of 'c Locus.occurrences_gen (* Head cofix: match or project a cofix *)
| RHCofixPrime of 'c Locus.occurrences_gen
(* Head cofixprime: push cofix inward *)
| RHMatch of 'c Locus.occurrences_gen
(* Head match: match or project on a constructor *)
(* TODO: match UIP? *)
| RHInferUnique of 'c Locus.occurrences_gen
(* Head unique value inference: reduce match on a UIP type *)
| RHead (* Any head reduction *)
| RCbv (* Next reduction step of a call-by-value strategy *)
| RCbn (* Next reduction step of a call-by-name strategy *)
| RLazy (* Next reduction step of a call-by-need / lazy strategy *)

val map_reduction : ('a -> 'd) -> ('b -> 'e) -> ('c Locus.occurrences_gen -> 'f Locus.occurrences_gen) -> ('a, 'b, 'c) reduction -> ('d, 'e, 'f) reduction
val step : (Names.inductive * int * int, Evaluable.t, int) reduction -> Reductionops.e_reduction_function
