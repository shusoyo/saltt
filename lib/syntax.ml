open Common

(** one to one correspond to [env] *)

type sty = term

and term =
  | Var of index
  | Lam of name * implicit * term
  | App of term * term * implicit
  | Universe
  | Pi of name * implicit * sty * term
  | Let of name * sty * term * term
  | Meta of meta_var
  | InsertedMeta of meta_var * bd list
[@@deriving show]
