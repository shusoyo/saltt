(* -----------------------------------------------------------------------
                      Named AST and conversion
   ----------------------------------------------------------------------- *)
open Syntax
open Syntax.LocallyNameless

type n_name = string

type n_ty = n_term

and n_term =
  | TyType
  | Var of n_name
  | App of n_term * n_term
  | Lam of (n_name * n_term)
  | TyPi of n_ty * (n_name * n_ty)
  | Ann of n_term * n_ty
  | TyBool
  | Bool of bool
  | If of n_term * n_term * n_term
  | TySigma of n_ty * (n_name * n_ty)
  | Pair of n_term * n_term
  | LetPair of n_term * (n_name * n_name * n_term)
  | Let of n_term * (n_name * n_term)
  | TyUnit
  | Unit
  | Sorry
  | PrintMe

module StringMap = Map.Make (String)

type context = name StringMap.t

let rec to_term_aux (ctx : context) (n_term : n_term) : term =
  match n_term with
  | TyType -> TyType
  | Var x -> begin
      match StringMap.find_opt x ctx with
      | Some name -> free_var name
      | None -> free_var (Atom.fresh x)
    end
  | App (t1, t2) -> App (to_term_aux ctx t1, to_term_aux ctx t2)
  | Lam (x, body) ->
      let ax = Atom.fresh x in
      let b' = to_term_aux (StringMap.add x ax ctx) body in
      Lam (bind ax b')
  | TyPi (a, (x, b)) ->
      let ax = Atom.fresh x in
      let a' = to_term_aux ctx a in
      let b' = to_term_aux (StringMap.add x ax ctx) b in
      TyPi (a', bind ax b')
  | Ann (t, ty) -> Ann (to_term_aux ctx t, to_term_aux ctx ty)
  | TyBool -> TyBool
  | Bool b -> Bool b
  | If (tm1, tm2, tm3) ->
      If (to_term_aux ctx tm1, to_term_aux ctx tm2, to_term_aux ctx tm3)
  | TySigma (a, (x, b)) ->
      let ax = Atom.fresh x in
      let a' = to_term_aux ctx a in
      let b' = to_term_aux (StringMap.add x ax ctx) b in
      TySigma (a', bind ax b')
  | Pair (t1, t2) -> Pair (to_term_aux ctx t1, to_term_aux ctx t2)
  | LetPair (t1, (x, y, t2)) ->
      let ax, ay = Atom.(fresh x, fresh y) in
      let t1' = to_term_aux ctx t1 in
      let t2' = to_term_aux StringMap.(ctx |> add x ax |> add y ay) t2 in
      LetPair (t1', bind_pair (ax, ay) t2')
  | Let (t1, (x, t2)) ->
      let ax = Atom.fresh x in
      let t1' = to_term_aux ctx t1 in
      let t2' = to_term_aux (StringMap.add x ax ctx) t2 in
      Let (t1', bind ax t2')
  | TyUnit -> TyUnit
  | Unit -> Unit
  | Sorry -> Sorry
  | PrintMe -> PrintMe

let to_term : n_term -> term = to_term_aux StringMap.empty
