open Syntax
open Context
open Value
open Evaluation
module R = Raw

let ( let* ) = Result.bind

(*
  bidirectional algorithm:
    use check when the type is already known
    use infer if the type is unknown
*)

let rec check_type ctx (raw : R.term) (ty : ty) : (term, string) result =
  match (raw, ty) with
  (*    
    check lambda is Pi, rule:
      Γ, x : A ⊢ a ⇐ B
      ------------------------
      (\x. a) ⇐ ((x : A) → B) 
  *)
  | R.Lam (x, body), VPi (x', x_type, clos) ->
      let var = VVar ctx.level in
      let ctx' = bind x x_type ctx in
      let* res = check_type ctx' body (clos $$ var) in
      Ok (Lam (x, res))
  (*
    check Let-statement: 'let x : A = t in u' is 'B'
      Γ ⊢ A ⇐ Universe
      Γ ⊢ t ⇐ A
      Γ x : A, x = t ⊢ u ⇐ B
      ----------------------
      let x : A = t in u ⇐ B
  *)
  | R.Let (x, a, t, u), b_ty ->
      let* a_tm = check_type ctx a VUniverse in
      let a_val = eval ctx.env a_tm in
      let* t_tm = check_type ctx t a_val in
      let t_val = eval ctx.env t_tm in
      let ctx' = define x t_val a_val ctx in
      let* u_tm = check_type ctx' u b_ty in
      Ok (Let (x, a_tm, t_tm, u_tm))
  (* 
    if term is not checkable, switch to infer mode
      Γ ⊢ a ⇒ B
      B ≣ A
      ---------
      Γ ⊢ a ⇐ A 
  *)
  | _ ->
      let* tm, t_ty = infer_type ctx raw in
      if conv ctx.level t_ty ty then Ok tm
      else
        report ctx raw
          (Format.asprintf
             "@[<v>type mismatch:@,\
             \  @[<v 2>expected type:@ %a@]@,\
             \  @[<v 2>inferred type:@ %a@]@]"
             pp_value ty pp_value t_ty)

and infer_type ctx (raw : R.term) : (term * ty, string) result =
  match raw with
  (*
    I-Var : x
      x : A ∈ Γ
      ---------
      Γ ⊢ x ⇒ A
  *)
  | R.Var name ->
      let f i (k, v) = if k = name then Some (i, v) else None in
      let res = List.find_mapi f ctx.types in
      begin match res with
      | Some (i, ty) -> Ok (Var (Ix i), ty)
      | None -> report ctx raw ("var not found: " ^ name)
      end
  (*
    I-universe :

      -----------------------
      Γ ⊢ Universe ⇒ Universe
  *)
  | R.Universe -> Ok (Universe, VUniverse)
  (* 
    I-App
      Γ ⊢ f ⇒ (x : A) → B
      Γ ⊢ a ⇐ A
      -------------------
      Γ ⊢ f a ⇒ B[a/x]
  *)
  | R.App (f, a) ->
      let* f_tm, f_ty = infer_type ctx f in
      begin match f_ty with
      | VPi (_, x_type, body_clos) ->
          let* a_tm = check_type ctx a x_type in
          Ok (App (f_tm, a_tm), body_clos $$ eval ctx.env a_tm)
      | _ ->
          report ctx raw
            (Format.asprintf "Expected a function type, but inferred: \n %a\n"
               Value.pp_value f_ty)
      end
  | R.Lam _ -> report ctx raw "Can't infer type for lambda expression"
  (*
    I-Pi
      Γ ⊢ A ⇐ Universe
      Γ, x : A ⊢ B ⇐ Universe
      --------------------------
      Γ ⊢ (x : A) → B ⇒ Universe
  *)
  | R.Pi (x, a, body) ->
      let* a_tm = check_type ctx a VUniverse in
      let ctx' = bind x (eval ctx.env a_tm) ctx in
      let* body_tm = check_type ctx' body VUniverse in
      Ok (Pi (x, a_tm, body_tm), VUniverse)
  (*
    I-Let
      Γ ⊢ A ⇐ Universe
      Γ ⊢ t ⇐ A
      Γ, x : A, x = t ⊢ u ⇒ B
      --------------------------
      Γ ⊢ let x : A = t in u ⇒ B
  *)
  | R.Let (x, x_ty, t, u) ->
      let* x_ty_tm = check_type ctx x_ty VUniverse in
      let x_ty_val = eval ctx.env x_ty_tm in
      let* t_tm = check_type ctx t x_ty_val in
      let t_val = eval ctx.env t_tm in
      let ctx' = define x t_val x_ty_val ctx in
      let* u_tm, u_ty = infer_type ctx' u in
      Ok (Let (x, x_ty_tm, t_tm, u_tm), u_ty)
