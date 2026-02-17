open Common

type t_ty = term

and term =
  | Var of index
  | Lam of name * term
  | App of term * term
  | Universe
  | Pi of name * t_ty * term
  | Let of name * t_ty * term * term
[@@deriving show]
