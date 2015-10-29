(* ========================================================================= *)
(* Initialize theorem proving example code.                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#load "nums.cma";;                                     (* For Ocaml 3.06     *)

if let v = String.sub Sys.ocaml_version 0 4 in v >= "3.10"
then (Topdirs.dir_directory "+camlp5";
      Topdirs.dir_load Format.std_formatter "camlp5o.cma")
else (Topdirs.dir_load Format.std_formatter "camlp4o.cma");;

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;
#use "initialization.ml";;
#use "Quotexpander.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic background.                                                         *)
(* ------------------------------------------------------------------------- *)

#use "lib.ml";;              (* Utility functions                            *)
#use "intro.ml";;            (* Trivial example from the introduction        *)

(* ------------------------------------------------------------------------- *)
(* General type of formulas, parser and printer (used for prop and FOL).     *)
(* ------------------------------------------------------------------------- *)

#use "formulas.ml";;
(* ------------------------------------------------------------------------- *)
(* Propositional logic.                                                      *)
(* ------------------------------------------------------------------------- *)

#use "prop.ml";;             (* Basic propositional logic stuff              *)
#use "propexamples.ml";;     (* Generate tautologies                         *)
#use "defcnf.ml";;           (* Definitional CNF                             *)
#use "dp.ml";;               (* Davis-Putnam procedure                       *)

(* ------------------------------------------------------------------------- *)
(* First order logic.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "fol.ml";;              (* Basic first order logic stuff                *)
#use "skolem.ml";;           (* Prenex and Skolem normal forms               *)
#use "herbrand.ml";;         (* Herbrand theorem and mechanization           *)
#use "unif.ml";;             (* Unification algorithm                        *)
#use "tableaux.ml";;         (* Tableaux                                     *)
#use "resolution.ml";;       (* Resolution                                   *)
#use "prolog.ml";;           (* Horn clauses and Prolog                      *)
#use "meson.ml";;            (* MESON-type model elimination                 *)
#use "skolems.ml";;          (* Skolemizing a set of formulas (theoretical)  *)

(* ------------------------------------------------------------------------- *)
(* Equality handling.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "equal.ml";;            (* Naive equality axiomatization                *)
