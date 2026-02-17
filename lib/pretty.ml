open Common
open Syntax

let rec fresh_name (names : name list) (base : name) : name =
  if List.mem base names then fresh_name names (base ^ "'") else base

let rec pretty_term names fmt = function
  | Var (Ix i) ->
      let name = try List.nth names i with _ -> "fvar_" ^ string_of_int i in
      Format.fprintf fmt "%s" name
  | App (t, u) ->
      Format.fprintf fmt "(%a %a)" (pretty_term names) t (pretty_term names) u
  | Lam (name, t) ->
      let name = fresh_name names name in
      Format.fprintf fmt "λ%s. %a" name (pretty_term (name :: names)) t
  | Let (name, ty, t, u) ->
      let name = fresh_name names name in
      Format.fprintf fmt "let %s : %a = %a in\n%a" name (pretty_term names) ty
        (pretty_term names) t
        (pretty_term (name :: names))
        u
  | Universe -> Format.fprintf fmt "Type"
  | Pi (name, ty, body) ->
      let name = fresh_name names name in
      Format.fprintf fmt "Π %s : %a.\n        %a" name (pretty_term names) ty
        (pretty_term (name :: names))
        body

let syntax_to_string t = Format.asprintf "%a" (pretty_term []) t

let rec raw_to_string : Raw.term -> string = function
  | Var x -> x
  | App (t, u) -> "(" ^ raw_to_string t ^ " " ^ raw_to_string u ^ ")"
  | Lam (x, t) -> Format.asprintf "(λ%s.%s)" x (raw_to_string t)
  | Let (x, t, a, u) ->
      Format.asprintf "let %s : %s = %s in\n%s" x (raw_to_string t)
        (raw_to_string a) (raw_to_string u)
  | Universe -> "Type"
  | Pi (x, a, t) ->
      Format.asprintf "((%s : %s) → %s)" x (raw_to_string a) (raw_to_string t)
