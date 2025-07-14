(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Univ
open UVars
open Declarations
open Environ
open CClosure

(** {6 Extracting an inductive type from a construction } *)

(** [find_m*type env sigma c] coerce [c] to an recursive type (I args).
   [find_rectype], [find_inductive] and [find_coinductive]
   respectively accepts any recursive type, only an inductive type and
   only a coinductive type.
   They raise [Not_found] if not convertible to a recursive type. *)

val find_rectype     : ?evars:evar_handler -> env -> types -> pinductive * constr list
val find_inductive   : ?evars:evar_handler -> env -> types -> pinductive * constr list
val find_coinductive : ?evars:evar_handler -> env -> types -> pinductive * constr list

(** {6 ... } *)
(** Fetching information in the environment about an inductive type.
    Raises an anomaly if the inductive type is not found. *)
val lookup_mind_specif : env -> inductive -> mind_specif

(** {6 Functions to build standard types related to inductive } *)

(** Returns the parameters of an inductive type with universes instantiated *)
val inductive_paramdecls : mutual_inductive_body puniverses -> Constr.rel_context

(** Returns the parameters of an inductive type with universes
    instantiated, splitting it into the contexts of recursively
    uniform and recursively non-uniform parameters *)
val inductive_nonrec_rec_paramdecls : mutual_inductive_body puniverses -> Constr.rel_context * Constr.rel_context

val instantiate_inductive_constraints :
  mutual_inductive_body -> Instance.t -> Constraints.t

type template_univ =
  | TemplateProp
  | TemplateUniv of Universe.t

type param_univs = (expected:Univ.Level.t -> template_univ) list

val constrained_type_of_inductive : mind_specif puniverses -> types constrained
val constrained_type_of_inductive_knowing_parameters :
  mind_specif puniverses -> param_univs -> types constrained

val relevance_of_ind_body : one_inductive_body -> UVars.Instance.t -> Sorts.relevance

val relevance_of_inductive : env -> pinductive -> Sorts.relevance

val type_of_inductive : mind_specif puniverses -> types

val type_of_inductive_knowing_parameters :
  ?polyprop:bool -> mind_specif puniverses -> param_univs -> types

val quality_leq : Sorts.Quality.t -> Sorts.Quality.t -> bool
(** For squashing. *)

type squash = SquashToSet | SquashToQuality of Sorts.Quality.t

val is_squashed : mind_specif puniverses -> squash option

val is_allowed_elimination : mind_specif puniverses -> Sorts.t -> bool

val is_private : mind_specif -> bool
val is_primitive_record : mind_specif -> bool

(** Return type as quoted by the user *)

val constrained_type_of_constructor : pconstructor -> mind_specif -> types constrained
val type_of_constructor : pconstructor -> mind_specif -> types

(** Return constructor types in normal form *)
val arities_of_constructors : pinductive -> mind_specif -> types array

(** Return constructor types in user form *)
val type_of_constructors : pinductive -> mind_specif -> types array

(** Turns a constructor type recursively referring to inductive types
    into the same constructor type referring instead to a context made
    from the abstract declaration of the inductive types (e.g. turns
    [nat->nat] into [mkArrowR (Rel 1) (Rel 2)]); takes as arguments the number
    of inductive types in the block and the name of the block *)
val abstract_constructor_type_relatively_to_inductive_types_context :
  int -> MutInd.t -> types -> types

val inductive_params : mind_specif -> int

type ('constr,'types,'r) pexpanded_case =
  (case_info * ('constr * 'r) * 'constr pcase_invert * 'constr * 'constr array)

type expanded_case = (constr,types,Sorts.relevance) pexpanded_case

(** Given a pattern-matching represented compactly, expands it so as to produce
    lambda and let abstractions in front of the return clause and the pattern
    branches. *)
val expand_case : env -> case -> expanded_case

val expand_case_specif : mind_specif -> case -> expanded_case

val expand_branches : mind_specif -> case -> constr array

val expand_branch : mind_specif -> case -> int -> constr

val expand_arity : mind_specif -> case -> types

(** Dual operation of the above. Fails if the return clause or branch has not
    the expected form. *)
val contract_case : env -> expanded_case -> case

val build_branches_type :
  pinductive -> mutual_inductive_body * one_inductive_body ->
    constr list -> constr -> types array

(** Check a [case_info] actually correspond to a Case expression on the
   given inductive type. *)
val check_case_info : env -> pinductive -> case_info -> unit

val contract_fix : fixpoint -> constr
val contract_cofix : cofixpoint -> constr

(** {6 Guard conditions for fix and cofix-points. } *)

(** [is_primitive_positive_container env c] tells if the constant [c] is
    registered as a primitive type that can be seen as a container where the
    occurrences of its parameters are positive, in which case the positivity and
    guard conditions are extended to allow inductive types to nest their subterms
    in these containers. *)
val is_primitive_positive_container : env -> Constant.t -> bool

(** When [chk] is false, the guard condition is not actually
    checked. *)
val check_fix : ?evars:evar_handler -> env -> fixpoint -> unit
val check_cofix : ?evars:evar_handler -> env -> cofixpoint -> unit

(** {6 Support for sort-polymorphic inductive types } *)

(** The "polyprop" optional argument below controls
    the "Prop-polymorphism". By default, it is allowed.
    But when "polyprop=false", the following exception is raised
    when a polymorphic singleton inductive type becomes Prop due to
    parameter instantiation. This is used by the Ocaml extraction,
    which cannot handle (yet?) Prop-polymorphism. *)

exception SingletonInductiveBecomesProp of Id.t

val abstract_mind_lc : int -> int -> MutInd.t -> (rel_context * constr) array -> constr array
