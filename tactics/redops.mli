(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genredexpr

val make_red_flag : 'a red_atom list -> 'a glob_red_flag

val all_flags : 'a glob_red_flag

(** Mapping [red_expr_gen] *)

val map_red_expr_gen : ('a1 -> 'a2) -> ('b1 -> 'b2) -> ('c1 -> 'c2) -> ('d1 -> 'd2) ->
  ('a1, 'b1, 'c1, unit,'e, 'f, 'occvar, 'd1) red_expr_gen -> ('a2, 'b2, 'c2, unit, 'e, 'f, 'occvar, 'd2) red_expr_gen
