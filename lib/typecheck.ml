open Env
open Syntax
open Syntax.LNR

(* -----------------------------------------------------------------------
                      Bidirectional type checking
   ----------------------------------------------------------------------- *)

let ( let* ) = Result.bind

(* Type inference function: given a term and a context, infer its type *)
let rec infer_type (env : env) (tm : term) : (ty, error) result =
  match tm with
  (* using opening style, never reached `Var (Bound i)` *)
  (* I-Var *)
  | Var (Free x) -> lookup_type env x
  (* I-Type *)
  | TyType -> Ok TyType
  (* I-App *)
  | App (f, a) ->
      let* f_ty = infer_type env f in
      begin match strip f_ty with
      | TyPi (f_param_ty, f_ret_ty) ->
          let* () = check_type env a f_param_ty in
          Ok (instantiate f_ret_ty a)
      | _ -> Error (TypeInferError ("Not a TyPi type", f_ty))
      end
  (* I-TyPi *)
  | TyPi (param_ty, ret_ty) ->
      let x, ret_ty' = unbind ret_ty in
      let* () = tc_Type env param_ty in
      let env' = extend_ctx env (make_decl_entry x param_ty) in
      let* () = tc_Type env' ret_ty' in
      Ok TyType
  (* I-Ann *)
  | Ann (a, a_ty) ->
      let* () = tc_Type env a_ty in
      let* () = check_type env a a_ty in
      Ok a_ty
  (* I-TyBool *)
  | TyBool -> Ok TyType
  (* I-Bool *)
  | Bool _ -> Ok TyBool
  (* I-If *)
  | If (cond, then_branch, else_branch) ->
      let* () = check_type env cond TyBool in
      let* then_ty = infer_type env then_branch in
      let* () = check_type env else_branch then_ty in
      Ok then_ty
  (* I-TySigma *)
  | TySigma (fst_ty, snd_ty) ->
      let x, snd_ty' = unbind snd_ty in
      let* () = tc_Type env fst_ty in
      let env' = extend_ctx env (make_decl_entry x fst_ty) in
      let* () = tc_Type env' snd_ty' in
      Ok TyType
  (* I-Pair *)
  (* cannot synthesize the type of the term *)
  | _ -> Error (TypeInferError ("Must have a type annotation for", tm))

and check_type (env : env) (tm : term) (ty : ty) : (unit, error) result =
  let ty' = strip ty in
  match tm with
  | Lam body -> begin
      match ty' with
      | TyPi (param_ty, ret_ty) ->
          let x, body', ret_ty' = unbind2 (body, ret_ty) in
          let env' = extend_ctx env (make_decl_entry x param_ty) in
          check_type env' body' ret_ty'
      | _ ->
          Error
            (TypeCheckError ("when checking [Lam body], ty is not Typi", [ ty ]))
    end
  | If (cond, then_branch, else_branch) ->
      let* () = check_type env cond TyBool in
      let* () = check_type env then_branch ty' in
      let* () = check_type env else_branch ty' in
      Ok ()
  | Pair (fst, snd) -> begin
      match ty with
      | TySigma (fst_ty, snd_ty) ->
          let* () = check_type env fst fst_ty in
          let x, snd_ty' = unbind snd_ty in
          let env' = extend_ctx env (make_decl_entry x fst_ty) in
          check_type env' snd (instantiate snd_ty' (free_var x))
      | _ ->
          Error
            (TypeCheckError
               ("when checking [Pair fst snd], ty is not TySigma", [ ty ]))
    end
  | LetPair (pair_term, body) -> begin
      let* pair_ty = infer_type env pair_term in
      match pair_ty with
      | TySigma (fst_ty, snd_ty) ->
          let x, y, body' = unbind_pair body in
          let snd_ty' = instantiate snd_ty (free_var x) in
          let env' = extend_ctx env (make_decl_entry x fst_ty) in
          let env'' = extend_ctx env' (make_decl_entry y snd_ty') in
          check_type env'' body' ty'
      | _ ->
          Error
            (TypeCheckError ("Expected TySigma type in LetPair", [ pair_ty ]))
    end
  | _ ->
      let* inferred_ty = infer_type env tm in
      if equal inferred_ty ty' then
        Ok ()
      else
        Error
          (TypeCheckError
             ("Types [ty] and [inferred_ty] don't match", [ ty; inferred_ty ]))

and tc_Type (env : env) (t : term) : (unit, error) result =
  check_type env t TyType
