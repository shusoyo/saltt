open Common
open Syntax

let rec fresh_name (names : name list) (base : name) : name =
  if List.mem base names then fresh_name names (base ^ "'") else base

let rec pretty_term names fmt = function
  | Var (Ix i) ->
      let name = try List.nth names i with _ -> "fvar_" ^ string_of_int i in
      Format.fprintf fmt "%s" name
  | App (t, u, icit) ->
      Format.fprintf fmt "(%a %a)" (pretty_term names) t (pretty_term names) u
  | Lam (name, icit, t) ->
      let name = fresh_name names name in
      Format.fprintf fmt "λ%s. %a" name (pretty_term (name :: names)) t
  | Let (name, ty, t, u) ->
      let name = fresh_name names name in
      Format.fprintf fmt "let %s : %a = %a in\n%a" name (pretty_term names) ty
        (pretty_term names) t
        (pretty_term (name :: names))
        u
  | Universe -> Format.fprintf fmt "Type"
  | Pi (name, icit, ty, body) ->
      if name = "_" then
        Format.fprintf fmt "%a -> %a" (pretty_term names) ty
          (pretty_term ("_" :: names))
          body
      else
        let name = fresh_name names name in
        Format.fprintf fmt "(%s : %a) -> %a" name (pretty_term names) ty
          (pretty_term (name :: names))
          body
  | Meta (MetaVar m) -> Format.fprintf fmt "? %d" m
  | InsertedMeta (MetaVar m, bds) -> Format.fprintf fmt "? %d" m

let syntax_to_string t = Format.asprintf "%a" (pretty_term []) t

let rec raw_to_string : Raw.term -> string = function
  | Var name -> name
  | App (t, u, _) -> Printf.sprintf "(%s %s)" (raw_to_string t) (raw_to_string u)
  | Lam (name, _, t) -> Printf.sprintf "λ%s. %s" name (raw_to_string t)
  | Let (name, ty, t, u) ->
      Printf.sprintf "let %s : %s = %s in\n%s" name (raw_to_string ty) (raw_to_string t)
        (raw_to_string u)
  | Universe -> "Type"
  | Pi ("_", _, ty, body) ->
      Printf.sprintf "%s -> %s" (raw_to_string ty) (raw_to_string body)
  | Pi (name, _, ty, body) ->
      Printf.sprintf "(%s : %s) -> %s" name (raw_to_string ty) (raw_to_string body)
  | Hole -> "?"
