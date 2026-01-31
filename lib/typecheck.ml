open Env
open Syntax

(* -----------------------------------------------------------------------
                      Bidirectional type checking
   ----------------------------------------------------------------------- *)

(* Type inference function: given a term and a context, infer its type *)
let rec infer_type (t : term) (env : env) : ty option =
  match t with
  | Var x -> lookup env x
  | TyType -> Some TyType
  | App (f, a) -> (
      match infer_type f env with
      | Some (TyPi (param_ty, ret_ty)) when check_type a param_ty env ->
          Some (subst 0 a ret_ty)
      | _ -> None)
  | TyPi (param_ty, ret_ty) ->
      if tc_Type param_ty env then
        let env' = extend env (make_decl_entry "" param_ty) in
        if tc_Type ret_ty env' then
          Some TyType
        else
          None
      else
        None
  | Ann (t, ty) ->
      if tc_Type ty env then
        if check_type t ty env then
          Some ty
        else
          None
      else
        None
  | _ -> None

and check_type (t : term) (ty : ty) (ctx : env) : bool =
  match (t, ty) with
  | Lam body, TyPi (param_ty, ret_ty) ->
      let env' = extend ctx (make_decl_entry "" param_ty) in
      check_type body ret_ty env'
  | _, _ -> (
      match infer_type t ctx with
      | Some inferred_ty -> inferred_ty = ty
      | None -> false)

and tc_Type (t : term) (ctx : env) : bool = check_type t TyType ctx
