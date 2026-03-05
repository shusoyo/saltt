open Common
open Syntax

let rec fresh_name (names : name list) (base : name) : name =
  if List.mem base names then fresh_name names (base ^ "'") else base

let rec pretty_term names = function
  | Global name -> name
  | Var (Ix i) ->
      let name = try List.nth names i with _ -> "fvar_" ^ string_of_int i in
      Printf.sprintf "%s" name
  | App (t, u, icit) ->
      Printf.sprintf "(%s %s)" (pretty_term names t) (pretty_term names u)
  | Lam (name, icit, t) ->
      let name = fresh_name names name in
      Printf.sprintf "λ%s. %s" name (pretty_term (name :: names) t)
  | Let (name, ty, t, u) ->
      let name = fresh_name names name in
      Printf.sprintf "let %s : %s = %s in\n%s" name (pretty_term names ty)
        (pretty_term names t)
        (pretty_term (name :: names) u)
  | Universe -> "Type"
  | Pi (name, icit, ty, body) ->
      if name = "_" then
        Printf.sprintf "%s -> %s" (pretty_term names ty) (pretty_term ("_" :: names) body)
      else
        let name = fresh_name names name in
        Printf.sprintf "(%s : %s) -> %s" name (pretty_term names ty)
          (pretty_term (name :: names) body)
  | Meta (MetaVar m) -> Printf.sprintf "? %d" m
  | InsertedMeta (MetaVar m, bds) -> Printf.sprintf "? %d" m

let syntax_to_string t = pretty_term [] t

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
