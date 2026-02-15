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

let rec to_string : term -> string = function
  | Var (Ix i) -> string_of_int i
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Lam (name, t) -> Printf.sprintf "λ %s. %s" name (to_string t)
  | Let (name, ty, t, u) ->
      Printf.sprintf "let %s : %s = %s in\n%s" name (to_string ty) (to_string t)
        (to_string u)
  | Universe -> "Type"
  | Pi (name, ty, body) ->
      Printf.sprintf "Π %s : %s. %s" name (to_string ty) (to_string body)
