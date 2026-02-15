open Common
open Value
open Syntax

(** [closure (env, body_tm) $$ v] will update the [env] and [eval] `compute` the
    [body_tm] *)
let rec ( $$ ) (Closure (env, body_tm) : closure) (v : value) : value =
  eval (extend_env v env) body_tm

and eval (env : env) (tm : term) : value =
  match tm with
  | Var index -> lookup index env
  (* lazy: explicit closure *)
  | Lam (name, body_tm) -> VLam (name, Closure (env, body_tm))
  (* lazy: body is explicit closure, a_type_tm is lazy_t  *)
  | Pi (name, a_type_tm, body_tm) ->
      let a_type_val = eval env a_type_tm in
      VPi (name, a_type_val, Closure (env, body_tm))
  (* lazy: argument thunks, [a] must be lazy evaluated *)
  | App (f, a) -> begin
      match (eval env f, eval env a) with
      | VLam (_, f_clos), a_val -> f_clos $$ a_val
      | f_val, a_val -> VApp (f_val, a_val)
    end
  | Let (_, _, a_tm, body_tm) ->
      let a_val = eval env a_tm in
      eval (extend_env a_val env) body_tm
  | Universe -> VUniverse

let rec quote (lvl : level) (value : value) : term =
  match value with
  | VVar x -> Var (index_of_level lvl x)
  | VApp (f_val, a) -> App (quote lvl f_val, quote lvl a)
  | VLam (name, f_clos) ->
      let var = VVar lvl in
      Lam (name, quote (next_level lvl) (f_clos $$ var))
  | VPi (name, a_type, f_clos) ->
      let a_type_val = a_type in
      let var = VVar lvl in
      Pi (name, quote lvl a_type_val, quote (next_level lvl) (f_clos $$ var))
  | VUniverse -> Universe

let normalize (env : env) (tm : term) : term = quote (length env) (eval env tm)

(* beta-eta conversion checking.
   precondition : both [value] have same type;  *)
let rec conv (lvl : level) (a_val : value) (b_val : value) : bool =
  match (a_val, b_val) with
  | VUniverse, VUniverse -> true
  | VPi (_, a_type, f_clos), VPi (_, b_type, g_clos) ->
      let a_type_val = a_type in
      let b_type_val = b_type in
      let var = VVar lvl in
      conv lvl a_type_val b_type_val
      && conv (next_level lvl) (f_clos $$ var) (g_clos $$ var)
  | VLam (_, f_clos), VLam (_, g_clos) ->
      let var = VVar lvl in
      conv (next_level lvl) (f_clos $$ var) (g_clos $$ var)
  (* eta conversion checking : 
        (\x. g x) ≡ g `or` g ≡ (\x. g x) *)
  | VLam (_, f_clos), _ ->
      let var = VVar lvl in
      conv (next_level lvl) (f_clos $$ var) (VApp (b_val, var))
  | _, VLam (_, g_clos) ->
      let var = VVar lvl in
      conv (next_level lvl) (VApp (a_val, var)) (g_clos $$ var)
  (* neutral value *)
  | VVar x, VVar y -> x = y
  | VApp (f_val, a), VApp (g_val, b) -> conv lvl f_val g_val && conv lvl a b
  (* rigid mismatch *)
  | _ -> false
