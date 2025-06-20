open Names
open Locus

type 'c end_condition =
| ECNat of int
| ECLocal of 'c
| ECGlobal of 'c

type 'e eta_kind =
| EBoth
| ELambda of Id.t option
| EPrim of 'e option

type ('occ, 'endc, 'tycons, 'zeta, 'delta) reduction =
(*| SRRule (* Rewrite rules *)*)
| Cast of 'occ occurrences_gen (* Cast removal *)
| Beta of Id.t option * 'occ occurrences_gen
(* Beta: applied lambda to substitution *)
| Zeta of Id.t option * 'occ occurrences_gen
(* Zeta: letin to substitution *)
| ZetaMatch of 'zeta * 'occ occurrences_gen
(* Zeta-match: match-letin to substitution *)
| Delta of 'delta option * 'occ occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| Eta of 'tycons eta_kind * 'occ occurrences_gen
(* Eta:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| Evar
(* Evar: evar resolution + context substitution, not sure about this one *)
| IotaFix of Id.t option * 'occ occurrences_gen
(* Iota-fix: push fixpoint inward when allowed to *)
| IotaFixPrime of Id.t option * 'occ occurrences_gen
(* Iota-fix-prime: push fixpoint inward, maybe unfold and refold too? *)
| IotaCofix of Id.t option * 'occ occurrences_gen
(* Iota-cofix: match or project a cofix *)
| IotaCofixPrime of Id.t option * 'occ occurrences_gen
(* Iota-cofix-prime: push cofix inward, maybe unfold and refold too? *)
| IotaMatch of 'tycons option * 'occ occurrences_gen
(* Iota-match: match or project on a constructor + inversion in SProp *)
| Root (* Any reduction applicable at the root of the whole term *)
| Head of 'endc end_condition (* Any reduction at head *)
| Cbv of 'endc end_condition (* Next reduction step of a call-by-value strategy *)
| Cbn of 'endc end_condition (* Next reduction step of a call-by-name strategy *)
| Lazy of 'endc end_condition (* Next reduction step of a call-by-need / lazy strategy *)

val map_end_condition : ('a -> 'b) -> 'a end_condition -> 'b end_condition
val map_eta_kind : ('a -> 'b) -> 'a eta_kind -> 'b eta_kind
val map_reduction :
  ('occa occurrences_gen -> 'occb occurrences_gen) ->
  ('enda -> 'endb) -> ('tyca -> 'tycb) -> ('zeta -> 'zetb) -> ('delta -> 'deltb) ->
  ('occa, 'enda, 'tyca, 'zeta, 'delta) reduction -> ('occb, 'endb, 'tycb, 'zetb, 'deltb) reduction
val pr_tycons : Environ.env -> inductive * int option -> Pp.t
val pr_zeta_raw : Libnames.qualid Constrexpr.or_by_notation * int or_var option -> Pp.t
val pr_zeta_glob : Environ.env -> GlobRef.t * int or_var option -> Pp.t
val pr_zeta : Environ.env -> inductive * int * int -> Pp.t
val pr_end_condition : ('endc -> Pp.t) -> 'endc end_condition -> Pp.t
val pr_eta_kind : ('tycons -> Pp.t) -> 'tycons eta_kind -> Pp.t
val pr_reduction :
  ('occ occurrences_gen -> Pp.t) -> ('endc -> Pp.t) -> ('tyc -> Pp.t) -> ('zeta -> Pp.t) -> ('delta -> Pp.t) ->
  ('occ, 'endc, 'tyc, 'zeta, 'delta) reduction -> Pp.t
val interp_tycons : Environ.env -> GlobRef.t -> inductive * int option
val interp_zeta :
  Environ.env -> GlobRef.t * int or_var option -> inductive * int * int
val step :
  (int, unit, inductive * int option, inductive * int * int, Evaluable.t) reduction -> Reductionops.e_reduction_function
