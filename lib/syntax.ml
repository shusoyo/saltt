(* -----------------------------------------------------------------------
   Core dependently typed lambda calculus language syntax
   ----------------------------------------------------------------------- 

    a, A, b, B ::=  x             - Variable
                  | A B           - Application
                  | λx:A. b       - Lambda abstraction
                  | (x: A) -> B   - Dependent function type (Πx:A. B)
                  | Type          - Universe type
                  | (t : A)       - Type annotation
*)

type index = int
type name = string

(* type and term use the same ast  *)
type ty = term

and term =
  (* Universe type `Type` *)
  | TyType
  (* Variable `x` *)
  | Var of index
  (* Application `f a` *)
  | App of term * term
  (* Lambda abstraction `λx.b` *)
  | Lam of term
  (* Dependent function type (Πx:A. B) `(x: A) -> B` *)
  | TyPi of ty * ty
  (* Type annotation `(t : A)` *)
  | Ann of term * ty

type decl_type = { decl_name : name; decl_type : ty }

type entry =
  (* type declaration *)
  | Decl of decl_type
  (* definition *)
  | Def of name * term

let make_decl_entry name decl_type : entry =
  Decl { decl_name = name; decl_type }

module NamedAst = struct
  type n_ty = n_term

  and n_term =
    | TyType
    | Var of name
    | App of n_term * n_term
    | Lam of name * n_term
    | TyPi of name * n_ty * n_ty
    | Ann of n_term * n_ty

  exception VariableNotFound of name

  type context = name list

  let rec index_of (x : name) (ctx : context) : int =
    match List.find_index (fun y -> y = x) ctx with
    | None -> raise (VariableNotFound x)
    | Some i -> i

  let rec remove_names (nt : n_term) (ctx : context) : term =
    match nt with
    | TyType -> TyType
    | Var x -> Var (index_of x ctx)
    | App (t1, t2) -> App (remove_names t1 ctx, remove_names t2 ctx)
    | Lam (x, b) -> Lam (remove_names b (x :: ctx))
    | TyPi (x, param_ty, ret_ty) ->
        TyPi (remove_names param_ty ctx, remove_names ret_ty (x :: ctx))
    | Ann (t, ty) -> Ann (remove_names t ctx, remove_names ty ctx)
end

(* -----------------------------------------------------------------------
                      De Bruijn indices 
   ----------------------------------------------------------------------- *)

let rec shift (d : int) (c : index) (t : term) : term =
  match t with
  | TyType -> TyType
  | Var x -> if x >= c then Var (x + d) else Var x
  | App (t1, t2) -> App (shift d c t1, shift d c t2)
  | Lam b -> Lam (shift d (c + 1) b)
  | TyPi (param_ty, ret_ty) -> TyPi (shift d c param_ty, shift d (c + 1) ret_ty)
  | Ann (t, ty) -> Ann (shift d c t, shift d c ty)

(* [j -> s]t *)
let rec subst (j : index) (s : term) (t : term) : term =
  match t with
  | TyType -> TyType
  | Var x -> if x = j then s else Var x
  | App (t1, t2) -> App (subst j s t1, subst j s t2)
  | Lam b -> Lam (subst (j + 1) (shift 1 0 s) b)
  | TyPi (param_ty, ret_ty) ->
      TyPi (subst j s param_ty, subst (j + 1) (shift 1 0 s) ret_ty)
  | Ann (t, ty) -> Ann (subst j s t, subst j s ty)

let subst_top (s : term) (t : term) : term =
  shift (-1) 0 (subst 0 (shift 1 0 s) t)

(* maybe different in different context *)
let alpha_eq (t1 : term) (t2 : term) : bool = t1 = t2
