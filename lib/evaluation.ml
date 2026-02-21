open Common
open Value
open Syntax
open Meta

(** [closure (env, body_tm) $$ v] will update the [env] and [eval] `compute` the [body_tm]
*)
let rec ( $$ ) (Closure (env, body_tm) : closure) (v : value) : value =
  eval (extend_env v env) body_tm

and eval_app (f : value) (a : value) (icit : implicit) : value =
  match (f, a) with
  | VLam (_, _, f_clos), a_val -> f_clos $$ a_val
  | VNe (head, spine), x -> VNe (head, extend_spine (x, icit) spine)
  | _ -> failwith "Impossible"

and eval_meta (m : meta_var) : value =
  match lookup_meta m with
  | Solved v -> v (* refine meta variable to value *)
  | Unsolved -> vmeta m

and eval_app_bound_vars (env : env) (m : meta_var) (bds : bd list) : value =
  assert (List.length env = List.length bds);
  List.fold_right2
    (fun x y acc -> match y with Defined -> acc | Bound -> eval_app acc x Explicit)
    env bds (eval_meta m)

and eval (env : env) (tm : term) : value =
  match tm with
  | Var index -> lookup index env
  (* lazy: explicit closure *)
  | Lam (name, icit, body_tm) -> VLam (name, icit, Closure (env, body_tm))
  (* lazy: body is explicit closure, a_type_tm is lazy_t  *)
  | Pi (name, icit, a_type_tm, body_tm) ->
      let a_type_val = eval env a_type_tm in
      VPi (name, icit, a_type_val, Closure (env, body_tm))
  (* lazy: argument thunks, [a] must be lazy evaluated *)
  | App (f, a, icit) -> eval_app (eval env f) (eval env a) icit
  | Let (_, _, a_tm, body_tm) ->
      let a_val = eval env a_tm in
      eval (extend_env a_val env) body_tm
  | Universe -> VUniverse
  | Meta m -> eval_meta m
  | InsertedMeta (m, bds) -> eval_app_bound_vars env m bds

let rec force (v : value) : value =
  match v with
  | VNe (NMeta m, sp) -> begin
      match lookup_meta m with
      | Solved t -> force (List.fold_right (fun (x, i) acc -> eval_app acc x i) sp t)
      | _ -> v
    end
  | _ -> v

let rec quote (lvl : level) (value : value) : term =
  match force value with
  | VNe (head, spine) ->
      let f h = List.fold_right (fun (v, i) acc -> App (acc, quote lvl v, i)) spine h in
      begin match head with
      | NVar x -> f (Var (index_of_level lvl x))
      | NMeta m -> f (Meta m)
      end
  | VLam (name, icit, f_clos) ->
      Lam (name, icit, quote (next_level lvl) (f_clos $$ vvar lvl))
  | VPi (name, icit, a_ty_val, f_clos) ->
      Pi (name, icit, quote lvl a_ty_val, quote (next_level lvl) (f_clos $$ vvar lvl))
  | VUniverse -> Universe

let normalize (env : env) (tm : term) : term = quote (Lvl (List.length env)) (eval env tm)
