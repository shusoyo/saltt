open Common
open Syntax

type env = value list

(* closure *)
and closure = env * term

(* value *)
and value = Var of level | App of value * value | Lam of closure
