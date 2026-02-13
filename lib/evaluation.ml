open Common
open Value
open Syntax
open Env

let rec eval (env : env) (tm : term) : value =
  match tm with
  | Var index -> lookup env index
  | Lam body_tm -> Lam (env, body_tm)
  | App (f, a) -> begin
      match (eval env f, eval env a) with
      | Lam (env', body_tm), a_val -> eval (extend_env env' a_val) body_tm
      | f_val, a_val -> App (f_val, a_val)
    end
  | Let (a_tm, body_tm) ->
      let a_val = eval env a_tm in
      eval (extend_env env a_val) body_tm

let rec quote (lvl : level) (value : value) : term =
  match value with
  | Var x -> Var (index_of_level lvl x)
  | App (f_val, a_val) -> App (quote lvl f_val, quote lvl a_val)
  | Lam (env, body_tm) ->
      let t = eval (Var lvl :: env) body_tm in
      Lam (quote (next_level lvl) t)

let normalize (env : env) (tm : term) : term = quote (length env) (eval env tm)
