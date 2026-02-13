(* -----------------------------------------------------------------------
                      Named AST and conversion
   ----------------------------------------------------------------------- *)

open Common

type term =
  | Var of name
  | App of term * term
  | Lam of name * term
  | Let of name * term * term

(* 
  | TyPi of ty * (name * ty)
  | Ann of term * ty
  | TyBool
  | Bool of bool
  | If of term * term * term
  | Let of term * (name * term) *)
