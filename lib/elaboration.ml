open Syntax
open Context
open Evaluation
open Value
open Meta
open Common
open Unification
module R = Raw

let ( let* ) = Result.bind

(*
  bidirectional algorithm:

    use check when the type is already known
    use infer if the type is unknown
*)

let rec check_type ctx (raw : R.term) (ty : ty) : (term, string) result =
  match (raw, force ty) with
  (*    
    check lambda is Pi, rule:
      Γ, x : A ⊢ a ⇐ B
      ------------------------
      (\x. a) ⇐ ((x : A) → B) 
  *)
  | R.Lam (x, body), VPi (_, x_type, body_ty_clos) ->
      let ctx' = bind x x_type ctx in
      let* res = check_type ctx' body (body_ty_clos $$ vvar ctx.level) in
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
  (* Hole *)
  | R.Hole, _ -> fresh_meta ctx
  (* 
    if term is not checkable, switch to infer mode
      Γ ⊢ a ⇒ B
      B ≡ A
      ---------
      Γ ⊢ a ⇐ A 
  *)
  | raw, expected -> (
      let* tm, inferred = infer_type ctx raw in
      match unify ctx.level inferred expected with
      | Ok () -> Ok tm
      | Error s ->
          let inferred_tm = quote ctx.level inferred in
          let expected_tm = quote ctx.level expected in
          report ctx raw
            (Format.asprintf
               "@[<v>type mismatch(can't unify):@,\
               \  @[<v 2>expected type:@ %a@]@,\
               \  @[<v 2>inferred type:@ %a@]@]"
               pp_term expected_tm pp_term inferred_tm))

and infer_type (ctx : ctx) (raw : R.term) : (term * ty, string) result =
  match raw with
  (*
    I-Var : x
      x : A ∈ Γ
      ---------
      Γ ⊢ x ⇒ A
  *)
  | R.Var name -> (
      let check_name i (k, v) = if k = name then Some (i, v) else None in
      let res = List.find_mapi check_name ctx.types in
      match res with
      | Some (i, ty) -> Ok (Var (Ix i), ty)
      | None -> report ctx raw ("var not found: " ^ name))
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
      begin match force f_ty with
      | VPi (_, x_type, body_clos) ->
          let* a_tm = check_type ctx a x_type in
          Ok (App (f_tm, a_tm), body_clos $$ eval ctx.env a_tm)
      | f_ty ->
          let* x_ty_tm = fresh_meta ctx in
          let x_ty = eval ctx.env x_ty_tm in
          let* body_tm = fresh_meta (bind "x" x_ty ctx) in
          let body_clos = Closure (ctx.env, body_tm) in
          begin match unify ctx.level (VPi ("x", x_ty, body_clos)) f_ty with
          | Ok () ->
              let* a_tm = check_type ctx a x_ty in
              Ok (App (f_tm, a_tm), body_clos $$ eval ctx.env a_tm)
          | Error s ->
              report ctx raw
                (Format.asprintf
                   "@[<v>TypeInference: (R.App branch) type mismatch(can't unify):@,\
                   \  @[<v 2>expected type:@ ((x : ?A) -> B) @]@,\
                   \  @[<v 2>inferred type:@ %a@]@]"
                   pp_term (quote ctx.level f_ty))
          end
      end
  | R.Lam (x, body) ->
      let* x_ty_meta = fresh_meta ctx in
      let x_ty = eval ctx.env x_ty_meta in
      let* body_tm, body_ty = infer_type (bind x x_ty ctx) body in
      let body_ty_syntax = quote (next_level ctx.level) body_ty in
      Ok (Lam (x, body_tm), VPi (x, x_ty, Closure (ctx.env, body_ty_syntax)))
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
  | Hole ->
      let* m_ty_meta = fresh_meta ctx in
      let m_ty = eval ctx.env m_ty_meta in
      let* m_tm = fresh_meta ctx in
      Ok (m_tm, m_ty)
