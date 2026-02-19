open Common

(** one to one correspond to [env] *)
type bd = Bound | Defined

and meta_var = MetaVar of int
and t_ty = term

and term =
  | Var of index
  | Lam of name * term
  | App of term * term
  | Universe
  | Pi of name * t_ty * term
  | Let of name * t_ty * term * term
  | Meta of meta_var
  | InsertedMeta of meta_var * bd list
[@@deriving show]
