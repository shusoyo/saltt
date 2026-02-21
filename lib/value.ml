open Common
open Syntax

(*
    It's have two kind of laziness:
      1. `closure`
      2. ocaml primitive `lazy_t` (deprecated)
*)

type env = value list

(** closure is [env * term], only converted by a binder [Pi, Lam], env is environment when
    meet the binder *)
and closure = Closure of env * term

and spine = (value * implicit) list

(* value *)
and ty = value
and neutral = NVar of level | NMeta of meta_var

and value =
  | VNe of neutral * spine
  | VLam of name * implicit * closure
  | VPi of name * implicit * ty * closure
  | VUniverse
[@@deriving show]

let vvar x = VNe (NVar x, [])
let vmeta x = VNe (NMeta x, [])
let lookup (Ix l : index) (env : env) : value = List.nth env l
let extend_env (v : value) (env : env) : env = v :: env
let extend_spine (v : value * implicit) (s : spine) : spine = v :: s
