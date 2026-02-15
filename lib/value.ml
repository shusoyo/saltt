open Common
open Syntax

(*
    It's have two kind of laziness:
      1. `closure`
      2. ocaml primitive `lazy_t` (deprecated)
*)

type env = value list

(** closure is [env * term], only converted by a binder [Pi, Lam], env is
    environment when meet the binder *)
and closure = Closure of env * term

(* value *)
and ty = value

and value =
  | VVar of level
  | VApp of value * value
  | VLam of name * closure
  | VPi of name * ty * closure
  | VUniverse
[@@deriving show]

let length (env : env) : level = Lvl (List.length env)
let lookup (Ix l : index) (env : env) : value = List.nth env l
let extend_env (v : value) (env : env) : env = v :: env
let to_string : value -> string = show_value
