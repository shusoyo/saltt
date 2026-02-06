open Env
open Pp
open Syntax

(* -----------------------------------------------------------------------
                      Bidirectional type checking
   ----------------------------------------------------------------------- *)
let ( let* ) = Result.bind

(* Type inference function: given a term and a context, infer its type *)
let rec infer_type (env : env) (tm : term) : (ty, error) result =
  match tm with
  (* using opening style, never reached `Var (Bound i)` *)
  (* I-Var *)
  | Var (Free x) ->
      let* decl = lookup_type env x in
      Ok decl.decl_type
  (* I-Type *)
  | TyType -> Ok TyType
  (* I-App *)
  | App (f, a) -> begin
      let* f_ty = infer_type env f in
      match strip f_ty with
      | TyPi (f_param_ty, f_ret_ty) ->
          let* () = check_type env a f_param_ty in
          Ok (instantiate f_ret_ty a)
      | _ -> Error [ DS "Not a TyPi type"; DT f_ty ]
    end
  (* I-TyPi *)
  | TyPi (param_ty, ret_ty) ->
      let x, ret_ty' = unbind ret_ty in
      let* () = tc_Type env param_ty in
      let env' = extend_ctx env (decl_entry x param_ty) in
      let* () = tc_Type env' ret_ty' in
      Ok TyType
  (* I-Ann *)
  | Ann (a, a_ty) ->
      let* () = tc_Type env a_ty in
      let* () = check_type env a a_ty in
      Ok a_ty
  (* I-Unit *)
  | TyUnit -> Ok TyType
  | Unit -> Ok TyUnit
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
      let env' = extend_ctx env (decl_entry x fst_ty) in
      let* () = tc_Type env' snd_ty' in
      Ok TyType
  (* I-Pair *)
  (* cannot synthesize the type of the term *)
  | _ -> Error [ DS "Must have a type annotation for"; DT tm ]

and check_type (env : env) (tm : term) (ty : ty) : (unit, error) result =
  let ty' = strip ty in
  match tm with
  | Lam body -> begin
      match ty' with
      | TyPi (param_ty, ret_ty) ->
          let x, body', ret_ty' = unbind2 (body, ret_ty) in
          let env' = extend_ctx env (decl_entry x param_ty) in
          check_type env' body' ret_ty'
      | _ -> Error [ DS "when checking [Lam body], ty is not Typi"; DT ty ]
    end
  | Sorry -> Ok ()
  | PrintMe ->
      (* TODO *)
      Ok ()
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
          let env' = extend_ctx env (decl_entry x fst_ty) in
          check_type env' snd (instantiate snd_ty' (free_var x))
      | _ ->
          Error [ DS "when checking [Pair fst snd], ty is not TySigma"; DT ty ]
    end
  | LetPair (pair_term, body) -> begin
      let* pair_ty = infer_type env pair_term in
      match pair_ty with
      | TySigma (fst_ty, snd_ty) ->
          let x, y, body' = unbind_pair body in
          let snd_ty' = instantiate snd_ty (free_var x) in
          let env' = extend_ctx env (decl_entry x fst_ty) in
          let env'' = extend_ctx env' (decl_entry y snd_ty') in
          check_type env'' body' ty'
      | _ -> Error [ DS "Expected TySigma type in LetPair"; DT pair_ty ]
    end
  (* C-Let *)
  | Let (a, body) ->
      let* a_type = infer_type env a in
      let x, body' = unbind body in
      let env' = extend_ctx env (decl_entry x a_type) in
      check_type env' body' ty'
  | _ ->
      let* inferred_ty = infer_type env tm in
      if alpha_eq inferred_ty ty' then
        Ok ()
      else
        Error
          [
            DS "Types [ty] and [inferred_ty] don't match"; DT ty; DT inferred_ty;
          ]

(** [tc_Type env t] is abbreviation for [check_type env t TyType] *)
and tc_Type (env : env) (t : term) : (unit, error) result =
  check_type env t TyType

type hint_or_ctx = AddHints of type_decl | AddCtx of entry list

let type_check_entry (env : env) (entry : entry) : (hint_or_ctx, error) result =
  match entry with
  | Decl decl ->
      (* TODO: check if exist duplicate binding *)
      let* () = tc_Type env decl.decl_type in
      Ok (AddHints decl)
  | Def (name, def_term) -> begin
      match lookup_def env name with
      | Error err -> begin
          match lookup_hint env name with
          | Error _ ->
              let* ty = infer_type env def_term in
              Ok (AddCtx [ decl_entry name ty; entry ])
          | Ok decl ->
              let env' = extend_ctx env (Decl decl) in
              begin match check_type env' def_term decl.decl_type with
              | Ok () -> Ok (AddCtx [ Decl decl; entry ])
              | Error msg ->
                  Error
                    (msg
                    @ [
                        DS "when checking the term";
                        DT def_term;
                        DS "against the type";
                        DD decl;
                      ])
              end
        end
      | Ok older_term ->
          Error
            [
              DS "duplicate definitions of";
              DN name;
              DS "previous is";
              DT older_term;
            ]
    end

let type_check_package (env : env) (pkgs : package list) (pkg : package) :
    (package, error) result =
  let is_imported x = List.mem (PackageImport x.name) pkg.imports in
  let imported_pkgs = List.filter is_imported pkgs in
  let env' = extend_ctx_packages env imported_pkgs in
  let* _, checked_entries =
    List.fold_left
      (fun acc entry ->
        let* current_env, checked = acc in
        let* res = type_check_entry current_env entry in
        match res with
        | AddCtx decls ->
            let next_env = extend_ctxs_globally current_env decls in
            Ok (next_env, decls @ checked)
        | AddHints hints ->
            let next_env = extend_hint current_env hints in
            Ok (next_env, checked))
      (Ok (env', []))
      pkg.entries
  in
  Ok { pkg with entries = checked_entries }

let type_check_packages (env : env) (pkgs : package list) :
    (package list, error) result =
  List.fold_left
    (fun acc_res pkg ->
      let* defs = acc_res in
      let* pkg' = type_check_package env defs pkg in
      Ok (defs @ [ pkg' ]))
    (Ok []) pkgs
