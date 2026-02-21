open Syntax
open Context
open Evaluation
open Value
open Meta
open Common
open Unification
module R = Raw

let ( let* ) = Result.bind
let ( <$> ) = Result.map

let rec insert' ctx ((t, t_ty) : term * ty) =
  match force t_ty with
  | VPi (x, Implicit, param_ty, body_ty_clos) ->
      let m = fresh_meta ctx in
      let m_val = eval ctx.env m in
      insert' ctx (App (t, m, Implicit), body_ty_clos $$ m_val)
  | _ -> (t, t_ty)

let rec insert ctx (t, t_ty) =
  match (t, t_ty) with Lam (_, Implicit, _), _ -> (t, t_ty) | _ -> insert' ctx (t, t_ty)

let rec insert_until_name ctx name ((t, t_ty) : term * ty) : (term * ty, string) result =
  match force t_ty with
  | VPi (x, Implicit, param_ty, body_ty_clos) ->
      if x = name then Ok (t, t_ty)
      else
        let m = fresh_meta ctx in
        let m_val = eval ctx.env m in
        insert_until_name ctx name (App (t, m, Implicit), body_ty_clos $$ m_val)
  | _ -> Error "Can't meet a Explicit Pi with this function"

(*
  bidirectional algorithm:

    use check when the type is already known
    use infer if the type is unknown
*)

(** [check_type ctx raw_term expected_type] checks if [raw_term] has type [expected_type]
    under context [ctx]. Returns the elaborated term if successful, or an error message.
    This function implements the bidirectional checking judgment [check: Γ ⊢ t ⇐ A]. *)
let rec check_type ctx (raw_term : R.term) (expected_type : ty) : (term, string) result =
  match (raw_term, force expected_type) with
  (*    
    check lambda is Pi, rule:
      Γ, x : A ⊢ a ⇐ B
      ------------------------
      (\x. a) ⇐ ((x : A) → B) 
  *)
  | R.Lam (x, icit, body_raw), VPi (x', icit', param_type, body_ty_clos)
    when Either.fold
           ~left:(fun name -> name = x' && icit' = Implicit) (* check \{x = y}. a *)
           ~right:(( = ) icit') icit ->
      let ctx' = bind x param_type ctx in
      let* body_term = check_type ctx' body_raw (body_ty_clos $$ vvar ctx.level) in
      Ok (Lam (x, icit', body_term))
  | raw_term, VPi (x, Implicit, param_type, body_ty_clos) ->
      let ctx' = new_binder x param_type ctx in
      let* body_term = check_type ctx' raw_term (body_ty_clos $$ vvar ctx.level) in
      Ok (Lam (x, Implicit, body_term))
  (*
    check Let-statement: 'let x : A = t in u' is 'B'
      Γ ⊢ A ⇐ Universe
      Γ ⊢ t ⇐ A
      Γ x : A, x = t ⊢ u ⇐ B
      ----------------------
      let x : A = t in u ⇐ B
  *)
  | R.Let (x, type_raw, val_raw, body_raw), expected_body_type ->
      let* type_term = check_type ctx type_raw VUniverse in
      let type_val = eval ctx.env type_term in
      let* val_term = check_type ctx val_raw type_val in
      let val_eval = eval ctx.env val_term in
      let ctx' = define x val_eval type_val ctx in
      let* body_term = check_type ctx' body_raw expected_body_type in
      Ok (Let (x, type_term, val_term, body_term))
  (* Hole *)
  | R.Hole, _ -> Ok (fresh_meta ctx)
  (* 
    if term is not checkable, switch to infer mode (CHANGE THE DIRECTION)
      Γ ⊢ a ⇒ B
      B ≡ A
      ---------
      Γ ⊢ a ⇐ A 

      why `insert` in this branch? 
        consider without let-generalization, for example:

          let id = \x. x : {A : Universe} -> A -> A in
          let f : _ = id in
          f

        expectedly, `f` should have type `f = (id ?α) : ?α -> ?α` rather than `{A : Universe} -> A -> A`.
        此处 f 单态化了，insert 了隐式参数 (这是大多数依赖类型实现的选择)
  *)
  | raw_term, expected_type ->
      let* inferred_term, inferred_type = insert ctx <$> infer_type ctx raw_term in
      begin match unify ctx.level inferred_type expected_type with
      | Ok () -> Ok inferred_term
      | Error s ->
          let inferred_type_tm = quote ctx.level inferred_type in
          let expected_type_tm = quote ctx.level expected_type in
          report ctx raw_term
            (Format.asprintf
               "@[<v>type mismatch(can't unify):@,\
               \  @[<v 2>expected type:@ %a@]@,\
               \  @[<v 2>inferred type:@ %a@]@]"
               pp_term expected_type_tm pp_term inferred_type_tm)
      end

(** [infer_type ctx raw_term] infers the type of [raw_term] under context [ctx]. Returns a
    pair of the elaborated term and its inferred type if successful, or an error message.
    This function implements the bidirectional inference judgment [infer: Γ ⊢ t ⇒ A]. *)
and infer_type (ctx : ctx) (raw_term : R.term) : (term * ty, string) result =
  match raw_term with
  (*
    I-Var : x
      x : A ∈ Γ
      ---------
      Γ ⊢ x ⇒ A
  *)
  | R.Var name ->
      ctx.types
      |> List.find_mapi (fun index (var_name, name_origin, var_type) ->
        match name_origin with
        | Source when var_name = name -> Some (Var (Ix index), var_type)
        | _ -> None)
      |> Option.to_result ~none:(report' ctx raw_term ("var not found: " ^ name))
  (*
    I-universe :

      -----------------------
      Γ ⊢ Universe ⇒ Universe
  *)
  | R.Universe -> Ok (Universe, VUniverse)
  | R.Lam (x, Right i, body_raw) ->
      let param_type = eval ctx.env (fresh_meta ctx) in
      let* body_term, body_type = infer_type (bind x param_type ctx) body_raw in
      let body_clos = Closure (ctx.env, quote (next_level ctx.level) body_type) in
      Ok (Lam (x, i, body_term), VPi (x, i, param_type, body_clos))
  | R.Lam (x, Left _, body_raw) ->
      Error "Can't infer type of lambda with implicit named parameter"
  (* 
    I-App
      Γ ⊢ f ⇒ (x : A) → B
      Γ ⊢ a ⇐ A
      -------------------
      Γ ⊢ f a ⇒ B[a/x]
  *)
  | R.App (func_raw, arg_raw, icit) ->
      let* func_term, func_type = infer_type ctx func_raw in
      let* i, func_term, func_type =
        match icit with
        | Left name ->
            let* f_term, f_type = insert_until_name ctx name (func_term, func_type) in
            Ok (Implicit, f_term, f_type)
        | Right Implicit -> Ok (Implicit, func_term, func_type)
        | Right Explicit ->
            (* Why insert'''' ? *)
            let func_term, func_type = insert' ctx (func_term, func_type) in
            Ok (Explicit, func_term, func_type)
      in
      begin match force func_type with
      | VPi (_, i', param_type, body_clos) ->
          if i <> i' then
            report ctx raw_term "TypeInference: (R.App branch) implicit/explicit mismatch"
          else
            let* arg_term = check_type ctx arg_raw param_type in
            Ok (App (func_term, arg_term, i), body_clos $$ eval ctx.env arg_term)
      | _ ->
          let param_type = eval ctx.env (fresh_meta ctx) in
          let body_clos = Closure (ctx.env, fresh_meta (bind "x" param_type ctx)) in
          begin match unify ctx.level (VPi ("x", i, param_type, body_clos)) func_type with
          | Ok () ->
              let* arg_term = check_type ctx arg_raw param_type in
              Ok (App (func_term, arg_term, i), body_clos $$ eval ctx.env arg_term)
          | Error s ->
              report ctx raw_term
                (Format.asprintf
                   "@[<v>TypeInference: (R.App branch) type mismatch(can't unify):@,\
                   \  @[<v 2>expected type:@ ((x : ?A) -> B) @]@,\
                   \  @[<v 2>inferred type:@ %a@]@]"
                   pp_term (quote ctx.level func_type))
          end
      end
  (*
    I-Pi
      Γ ⊢ A ⇐ Universe
      Γ, x : A ⊢ B ⇐ Universe
      --------------------------
      Γ ⊢ (x : A) → B ⇒ Universe
  *)
  | R.Pi (x, i, param_type_raw, body_raw) ->
      let* param_type_term = check_type ctx param_type_raw VUniverse in
      let ctx' = bind x (eval ctx.env param_type_term) ctx in
      let* body_term = check_type ctx' body_raw VUniverse in
      Ok (Pi (x, i, param_type_term, body_term), VUniverse)
  (*
    I-Let
      Γ ⊢ A ⇐ Universe
      Γ ⊢ t ⇐ A
      Γ, x : A, x = t ⊢ u ⇒ B
      --------------------------
      Γ ⊢ let x : A = t in u ⇒ B
  *)
  | R.Let (x, type_raw, val_raw, body_raw) ->
      let* type_term = check_type ctx type_raw VUniverse in
      let type_val = eval ctx.env type_term in
      let* val_term = check_type ctx val_raw type_val in
      let val_eval = eval ctx.env val_term in
      let ctx' = define x val_eval type_val ctx in
      let* body_term, body_type = infer_type ctx' body_raw in
      Ok (Let (x, type_term, val_term, body_term), body_type)
  | Hole ->
      let meta_type_term = fresh_meta ctx in
      let meta_type = eval ctx.env meta_type_term in
      let meta_term = fresh_meta ctx in
      Ok (meta_term, meta_type)
