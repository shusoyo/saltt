open Common

type ty = term

and term =
  | Var of name
  | App of term * term
  | Lam of name * term
  | Let of name * ty * term * term
  | Universe
  | Pi of name * term * term
[@@deriving show]

let rec to_string : term -> string = function
  | Var x -> x
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Lam (x, t) -> Printf.sprintf "(λ%s.%s)" x (to_string t)
  | Let (x, t, a, u) ->
      Printf.sprintf "let %s : %s = %s in\n%s" x (to_string t) (to_string a)
        (to_string u)
  | Universe -> "Type"
  | Pi (x, a, t) ->
      Printf.sprintf "((%s : %s) → %s)" x (to_string a) (to_string t)
