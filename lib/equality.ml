open Syntax
open Env

let ( let* ) = Result.bind

let rec equate (env : env) (t1 : term) (t2 : term) : (unit, error) result =
  if alpha_eq t1 t2 then Ok ()
  else
    let nf1 = whnf env t1 in
    let nf2 = whnf env t2 in
    match (nf1, nf2) with
    (* EQ-Abs *)
    | Lam a_body_bnd, Lam b_body_bnd ->
        let _, a_body, b_body = unbind_both a_body_bnd b_body_bnd in
        equate env a_body b_body
    (* EQ-Pi *)
    | TyPi (a_param_ty, a_ret_bnd), TyPi (b_param_ty, b_ret_bnd) ->
        let _, a_ret_ty, b_ret_ty = unbind_both a_ret_bnd b_ret_bnd in
        let* () = equate env a_param_ty b_param_ty in
        equate env a_ret_ty b_ret_ty
    (* EQ-App *)
    | App (f_ne, a), App (g_ne, b) ->
        let* () = equate env f_ne g_ne in
        equate env a b
    (* EQ-extend *)
    | If (a_cond, a_brh1, a_brh2), If (b_cond, b_brh1, b_brh2) ->
        let* () = equate env a_cond b_cond in
        let* () = equate env a_brh1 b_brh1 in
        equate env a_brh2 b_brh2
    | Let (a, a_body_bnd), Let (b, b_body_bnd) ->
        let x, a_body, b_body = unbind_both a_body_bnd b_body_bnd in
        let* () = equate env a b in
        equate env a_body b_body
    | TySigma (a_fst, a_snd_bnd), TySigma (b_fst, b_snd_bnd) ->
        let x, a_snd, b_snd = unbind_both a_snd_bnd b_snd_bnd in
        let* () = equate env a_fst b_fst in
        equate env a_snd b_snd
    | Pair (a_fst, a_snd), Pair (b_fst, b_snd) ->
        let* () = equate env a_fst b_fst in
        equate env a_snd b_snd
    | LetPair (a, a_body_bnd), LetPair (b, b_body_bnd) ->
        let* () = equate env a b in
        let (x, y), (a_body, b_body) = unbind_pair_both a_body_bnd b_body_bnd in
        equate env a_body b_body
    (* EQ-refl *)
    | _ ->
        if nf1 = nf2 then Ok ()
        else
          Error [ DS "expect"; DT nf1; DS "but found"; DT nf2; DS "in context" ]

(* 
    value   = ꟛx. b | (x: A) -> B | Type | Bool | True | False |
              (a, b) | {x : A | B} | Unit | () | Sorry | PrintMe 
    neutral = x | ne a 
    whnf    = value | neutral
*)
and whnf (env : env) (tm : term) : term =
  match tm with
  | Var (Free x) ->
      let def_unwrap = lookup_def env x in
      begin match def_unwrap with
      | Ok def -> whnf env def
      | Error _ -> tm (* don't raise error *)
      end
  (* WHNF-App: 1, beta-reduction; 2, neutral value *)
  | App (f, a) ->
      let nf_f = whnf env f in
      begin match nf_f with
      | Lam body_bnd -> whnf env (instantiate body_bnd a)
      | _ -> App (nf_f, a)
      end
  | If (cond, then_branch, else_branch) ->
      let nf_cond = whnf env cond in
      begin match nf_cond with
      | Bool bool -> if bool then then_branch else else_branch
      | _ -> If (nf_cond, then_branch, else_branch)
      end
  | Let (a, body_bnd) -> whnf env (instantiate body_bnd a)
  | LetPair (a, body_bnd) ->
      let nf_a = whnf env a in
      begin match nf_a with
      | Pair (fst_tm, snd_tm) ->
          whnf env (instantiates body_bnd [ fst_tm; snd_tm ])
      | _ -> LetPair (nf_a, body_bnd)
      end
  (* WHNF-Annnot *)
  | Ann (a, _) -> whnf env a
  (* value *)
  | _ -> tm
