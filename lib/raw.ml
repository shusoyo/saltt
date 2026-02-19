open Common

type ty = term

and term =
  | Var of name
  | App of term * term
  | Lam of name * term
  | Let of name * ty * term * term
  | Universe
  | Pi of name * term * term
  | Hole
[@@deriving show]
