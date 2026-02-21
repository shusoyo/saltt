open Common

type ('a, 'b) either = ('a, 'b) Either.t = Left of 'a | Right of 'b [@@deriving show]

type ty = term

and term =
  | Var of name
  | App of term * term * (name, implicit) either
  | Lam of name * (name, implicit) either * term
  | Let of name * ty * term * term
  | Universe
  | Pi of name * implicit * term * term
  | Hole
[@@deriving show]
