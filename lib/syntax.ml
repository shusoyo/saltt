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

module Atom : sig
  type t = { name : string; id : int }

  val fresh : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
end = struct
  type t = { name : string; id : int }

  let counter = ref 0

  let fresh s =
    incr counter;
    { name = s; id = !counter }

  let equal a b = a.id = b.id
  let compare a b = compare a.id b.id
  let to_string a = a.name ^ "_" ^ string_of_int a.id
end

type index = int
type name = Atom.t

(* type and term use the same ast  *)

type var = Bound of index | Free of name

type ty = term

and term =
  (* Universe type `Type` *)
  | TyType
  (* Variable `x` *)
  | Var of var
  (* Application `f a` *)
  | App of term * term
  (* Lambda abstraction `λx.b` *)
  | Lam of term
  (* Dependent function type (Πx:A. B) `(x: A) -> B` *)
  | TyPi of ty * ty
  (* Type annotation `(t : A)` *)
  | Ann of term * ty

(* Auxiliary functions on syntax *)
let bound_var (i : index) : term = Var (Bound i)
let free_var (x : name) : term = Var (Free x)

(** [strip tm] 返回消除顶层类型注解的项；strip 的时机: 解构 (Elimination)：当要 match ... with TyPi
    ... 或 match ... with TyType 时。也可能要限制类型标注出现的地方？ *)
let rec strip (tm : term) : term =
  match tm with Ann (t_inner, _) -> strip t_inner | _ -> tm

(* -----------------------------------------------------------------------
                      Locally nameless substitution
   ----------------------------------------------------------------------- *)

module LNR : sig
  val subst : name -> term -> term -> term
  val bind : name -> term -> term
  val unbind : term -> name * term
  val unbind2 : term * term -> name * term * term
  val instantiate : term -> term -> term
  val is_lc : term -> bool
  val equal : term -> term -> bool
  val fv : term -> name list
  val to_string : term -> string
end = struct
  let rec open_term_aux (t : term) (r : term) (depth : int) : term =
    match t with
    | Var (Bound k) when depth = k -> r
    | TyType | Var _ -> t
    | Lam body -> Lam (open_term_aux body r (depth + 1))
    | TyPi (t1, t2) ->
        TyPi (open_term_aux t1 r depth, open_term_aux t2 r (depth + 1))
    | App (t1, t2) -> App (open_term_aux t1 r depth, open_term_aux t2 r depth)
    | Ann (t_inner, ty) ->
        Ann (open_term_aux t_inner r depth, open_term_aux ty r depth)

  let rec close_term_aux (t : term) (x : name) (n : int) : term =
    match t with
    | Var (Free y) when y = x -> Var (Bound n)
    | TyType | Var _ -> t
    | Lam body -> Lam (close_term_aux body x (n + 1))
    | TyPi (t1, t2) -> TyPi (close_term_aux t1 x n, close_term_aux t2 x (n + 1))
    | App (t1, t2) -> App (close_term_aux t1 x n, close_term_aux t2 x n)
    | Ann (t_inner, ty) ->
        Ann (close_term_aux t_inner x n, close_term_aux ty x n)

  let rec subst (x : name) (u : term) (t : term) : term =
    match t with
    | Var (Free y) when y = x -> u
    | Var _ | TyType -> t
    | Lam body -> Lam (subst x u body)
    | App (t1, t2) -> App (subst x u t1, subst x u t2)
    | TyPi (a, b) -> TyPi (subst x u a, subst x u b)
    | Ann (t, ty) -> Ann (subst x u t, subst x u ty)

  let bind (x : name) (t : term) : term = close_term_aux t x 0

  let unbind (t : term) : name * term =
    let x = Atom.fresh "x" in
    (x, open_term_aux t (free_var x) 0)

  let unbind2 ((lhs, rhs) : term * term) : name * term * term =
    let x = Atom.fresh "x" in
    let f tm = open_term_aux tm (free_var x) 0 in
    (x, f lhs, f rhs)

  let instantiate (body : term) (arg : term) : term = open_term_aux body arg 0

  (** Check if a term is locally closed (well-formed at level k) *)
  let rec is_lc_at (k : int) (t : term) : bool =
    match t with
    | Var (Bound i) -> i < k
    | Var (Free _) | TyType -> true
    | Lam body -> is_lc_at (k + 1) body
    | TyPi (a, b) -> is_lc_at k a && is_lc_at (k + 1) b
    | App (t1, t2) | Ann (t1, t2) -> is_lc_at k t1 && is_lc_at k t2

  let is_lc t = is_lc_at 0 t

  (** Recursive structural equality that ignores all type annotations *)
  let rec equal (t1 : term) (t2 : term) : bool =
    match (strip t1, strip t2) with
    | TyType, TyType -> true
    | Var v1, Var v2 -> v1 = v2
    | App (f1, a1), App (f2, a2) -> equal f1 f2 && equal a1 a2
    | Lam b1, Lam b2 -> equal b1 b2
    | TyPi (a1, r1), TyPi (a2, r2) -> equal a1 a2 && equal r1 r2
    | _ -> false

  (** Free variables collection *)
  let rec fv (t : term) : name list =
    match t with
    | Var (Free x) -> [ x ]
    | Var (Bound _) | TyType -> []
    | App (t1, t2) -> fv t1 @ fv t2
    | Lam body -> fv body
    | TyPi (a, b) -> fv a @ fv b
    | Ann (t, ty) -> fv t @ fv ty

  (** Internal string representation for debugging (shows indices) *)
  let rec to_string (t : term) : string =
    match t with
    | TyType -> "Type"
    | Var (Bound i) -> "#" ^ string_of_int i
    | Var (Free x) -> x.name ^ "_" ^ string_of_int x.id
    | Lam body -> "λ. " ^ to_string body
    | App (t1, t2) -> "(" ^ to_string t1 ^ " " ^ to_string t2 ^ ")"
    | TyPi (a, b) -> "(Π " ^ to_string a ^ ". " ^ to_string b ^ ")"
    | Ann (t, ty) -> "(" ^ to_string t ^ " : " ^ to_string ty ^ ")"
end

(* -----------------------------------------------------------------------
                      Named AST and conversion
   ----------------------------------------------------------------------- *)
module NamedAst = struct
  open LNR

  type n_ty = n_term

  and n_term =
    | TyType
    | Var of name
    | App of n_term * n_term
    | Lam of name * n_term
    | TyPi of name * n_ty * n_ty
    | Ann of n_term * n_ty

  exception VariableNotFound of name

  (** Convert Named AST to Locally Nameless Term *)
  let rec to_term (nt : n_term) : term =
    match nt with
    | TyType -> TyType
    | Var x -> free_var x
    | App (t1, t2) -> App (to_term t1, to_term t2)
    | Lam (x, b) ->
        let b' = to_term b in
        Lam (bind x b')
    | TyPi (x, a, b) ->
        let a', b' = (to_term a, to_term b) in
        TyPi (a', bind x b')
    | Ann (t, ty) -> Ann (to_term t, to_term ty)

  (** Convert Locally Nameless Term back to Named AST *)
  let rec of_term (t : term) : n_term =
    match t with
    | TyType -> TyType
    | Var (Free x) -> Var x
    | Var (Bound i) ->
        failwith
          ("Unexpected bound variable #" ^ string_of_int i
         ^ " during conversion to Named AST")
    | App (t1, t2) -> App (of_term t1, of_term t2)
    | Lam body ->
        let x, opened = unbind body in
        Lam (x, of_term opened)
    | TyPi (a, b) ->
        let a' = of_term a in
        let x, opened = unbind b in
        TyPi (x, a', of_term opened)
    | Ann (t, ty) -> Ann (of_term t, of_term ty)

  (** Pretty print Named AST *)
  let rec to_string (nt : n_term) : string =
    match nt with
    | TyType -> "Type"
    | Var x -> Atom.to_string x
    | App (t1, t2) -> "(" ^ to_string t1 ^ " " ^ to_string t2 ^ ")"
    | Lam (x, b) -> "λ" ^ Atom.to_string x ^ ". " ^ to_string b
    | TyPi (x, a, b) ->
        "(" ^ Atom.to_string x ^ " : " ^ to_string a ^ ") -> " ^ to_string b
    | Ann (t, ty) -> "(" ^ to_string t ^ " : " ^ to_string ty ^ ")"
end

(* -----------------------------------------------------------------------------
                              Modules and declarations
   ----------------------------------------------------------------------------- *)

type decl_type = { decl_name : name; decl_type : ty }

type entry =
  (* type declaration *)
  | Decl of decl_type
  (* definition *)
  | Def of name * term

let make_decl_entry name decl_type : entry =
  Decl { decl_name = name; decl_type }

type module_name = string
type module_import = module_name

type modules = {
  name : module_name;
  imports : module_import list;
  entries : entry list;
}
