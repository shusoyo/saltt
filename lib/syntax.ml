open Common

type term =
  | Var of index
  | Lam of term
  | App of term * term
  | Let of term * term

let rec to_string = function
  | Var (Ix i) -> string_of_int i
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Lam t -> Printf.sprintf "λ %s" (to_string t)
  | Let (t, u) -> Printf.sprintf "let %s in\n%s" (to_string t) (to_string u)
