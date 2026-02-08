module Atom = struct
  type t = { name : string; id : int }

  let counter = ref 0

  let fresh s =
    incr counter;
    { name = s; id = !counter }

  let equal a b = a.id = b.id
  let compare a b = compare a.id b.id
  let to_string a = a.name ^ "_" ^ string_of_int a.id
end

(* -----------------------------------------------------------------------
        Core dependently typed lambda calculus language syntax
   -----------------------------------------------------------------------  *)

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
  (* Bool type `Bool` *)
  | TyBool
  (* bool value : `True` or `False` *)
  | Bool of bool
  (* If statement `if <cond> then <then_branch> else <else_branch>` *)
  | If of term * term * term
  (* dependently pair type `{x : A | B}` *)
  | TySigma of ty * ty
  (* Pair constructor `(a, b)` *)
  | Pair of term * term
  (* Pair deconstruction `let (x, y) = a in b` *)
  | LetPair of term * term
  (* An axiom 'sorry', inhabits all types *)
  | Sorry
  (* print context *)
  | PrintMe
  (* Let statement `let x = a in b` *)
  | Let of term * term
  (* Unit type `Unit` *)
  | TyUnit
  (* Unit value `()` *)
  | Unit

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

module LocallyNameless = struct
  let rec open_term_aux (t : term) (rs : term list) (depth : int) : term =
    match t with
    | Var (Bound k) when k >= depth && k < depth + List.length rs ->
        List.nth rs (k - depth)
    | TyType | Var _ | Bool _ | TyBool | Sorry | PrintMe | TyUnit | Unit -> t
    | Lam body -> Lam (open_term_aux body rs (depth + 1))
    | TyPi (t1, t2) ->
        TyPi (open_term_aux t1 rs depth, open_term_aux t2 rs (depth + 1))
    | App (t1, t2) -> App (open_term_aux t1 rs depth, open_term_aux t2 rs depth)
    | Ann (t_inner, ty) ->
        Ann (open_term_aux t_inner rs depth, open_term_aux ty rs depth)
    | If (tm1, tm2, tm3) ->
        If
          ( open_term_aux tm1 rs depth,
            open_term_aux tm2 rs depth,
            open_term_aux tm3 rs depth )
    | Pair (t1, t2) ->
        Pair (open_term_aux t1 rs depth, open_term_aux t2 rs depth)
    | LetPair (t1, t2) ->
        (* let-pair bind 2 var *)
        LetPair (open_term_aux t1 rs depth, open_term_aux t2 rs (depth + 2))
    | TySigma (t1, t2) ->
        TySigma (open_term_aux t1 rs depth, open_term_aux t2 rs (depth + 1))
    | Let (t1, t2) ->
        Let (open_term_aux t1 rs depth, open_term_aux t2 rs (depth + 1))

  let rec close_term_aux (t : term) (xs : name list) (n : int) : term =
    match t with
    | Var (Free y) -> begin
        match List.find_index (Atom.equal y) xs with
        | Some i -> bound_var (n + i)
        | None -> t
      end
    | TyType | Var _ | Bool _ | TyBool | Sorry | PrintMe | TyUnit | Unit -> t
    | Lam body -> Lam (close_term_aux body xs (n + 1))
    | TyPi (t1, t2) ->
        TyPi (close_term_aux t1 xs n, close_term_aux t2 xs (n + 1))
    | App (t1, t2) -> App (close_term_aux t1 xs n, close_term_aux t2 xs n)
    | Ann (t_inner, ty) ->
        Ann (close_term_aux t_inner xs n, close_term_aux ty xs n)
    | If (tm1, tm2, tm3) ->
        If
          ( close_term_aux tm1 xs n,
            close_term_aux tm2 xs n,
            close_term_aux tm3 xs n )
    | Pair (t1, t2) -> Pair (close_term_aux t1 xs n, close_term_aux t2 xs n)
    | LetPair (t1, t2) ->
        LetPair (close_term_aux t1 xs n, close_term_aux t2 xs (n + 2))
    | TySigma (t1, t2) ->
        TySigma (close_term_aux t1 xs n, close_term_aux t2 xs (n + 1))
    | Let (t1, t2) -> Let (close_term_aux t1 xs n, close_term_aux t2 xs (n + 1))

  let rec subst (x : name) (u : term) (t : term) : term =
    match t with
    | Var (Free y) when y = x -> u
    | Var _ | TyType | Bool _ | TyBool | Sorry | PrintMe | TyUnit | Unit -> t
    | Lam body -> Lam (subst x u body)
    | App (t1, t2) -> App (subst x u t1, subst x u t2)
    | TyPi (a, b) -> TyPi (subst x u a, subst x u b)
    | Ann (t, ty) -> Ann (subst x u t, subst x u ty)
    | If (tm1, tm2, tm3) -> If (subst x u tm1, subst x u tm2, subst x u tm3)
    | Pair (t1, t2) -> Pair (subst x u t1, subst x u t2)
    | LetPair (t1, t2) -> LetPair (subst x u t1, subst x u t2)
    | TySigma (t1, t2) -> TySigma (subst x u t1, subst x u t2)
    | Let (t1, t2) -> Let (subst x u t1, subst x u t2)

  (** Check if a term is locally closed (well-formed at level k) *)
  let rec is_lc_at (k : int) (t : term) : bool =
    match t with
    | Var (Bound i) -> i < k
    | Var (Free _) | TyType | Bool _ | TyBool | TyUnit | Unit -> true
    | Sorry | PrintMe -> true
    | Lam body -> is_lc_at (k + 1) body
    | TyPi (a, b) -> is_lc_at k a && is_lc_at (k + 1) b
    | App (t1, t2) | Ann (t1, t2) -> is_lc_at k t1 && is_lc_at k t2
    | If (tm1, tm2, tm3) -> is_lc_at k tm1 && is_lc_at k tm2 && is_lc_at k tm3
    | Pair (t1, t2) -> is_lc_at k t1 && is_lc_at k t2
    | LetPair (t1, t2) -> is_lc_at k t1 && is_lc_at (k + 2) t2
    | TySigma (t1, t2) -> is_lc_at k t1 && is_lc_at (k + 1) t2
    | Let (t1, t2) -> is_lc_at k t1 && is_lc_at (k + 1) t2

  let is_lc t = is_lc_at 0 t

  (** Recursive structural equality that ignores all type annotations *)
  let rec alpha_eq (t1 : term) (t2 : term) : bool =
    match (strip t1, strip t2) with
    | TyType, TyType -> true
    | TyBool, TyBool -> true
    | TyUnit, TyUnit -> true
    | Unit, Unit -> true
    | Sorry, Sorry -> true
    | PrintMe, PrintMe -> true
    | Bool b1, Bool b2 -> b1 = b2
    | Var v1, Var v2 -> v1 = v2
    (* nested *)
    | App (f1, a1), App (f2, a2) -> alpha_eq f1 f2 && alpha_eq a1 a2
    | Lam b1, Lam b2 -> alpha_eq b1 b2
    | TyPi (a1, r1), TyPi (a2, r2) -> alpha_eq a1 a2 && alpha_eq r1 r2
    | If (c1, t1, e1), If (c2, t2, e2) ->
        alpha_eq c1 c2 && alpha_eq t1 t2 && alpha_eq e1 e2
    | TySigma (a1, r1), TySigma (a2, r2) -> alpha_eq a1 a2 && alpha_eq r1 r2
    | Pair (p1a, p1b), Pair (p2a, p2b) -> alpha_eq p1a p2a && alpha_eq p1b p2b
    | LetPair (l1a, l1b), LetPair (l2a, l2b) ->
        alpha_eq l1a l2a && alpha_eq l1b l2b
    | Let (l1a, l1b), Let (l2a, l2b) -> alpha_eq l1a l2a && alpha_eq l1b l2b
    | _ -> false

  (** Free variables collection *)
  let rec fv (t : term) : name list =
    match t with
    | Var (Free x) -> [ x ]
    | Var (Bound _) | TyType | TyBool | Bool _ | Sorry | PrintMe | TyUnit | Unit
      ->
        []
    | App (t1, t2) -> fv t1 @ fv t2
    | Lam body -> fv body
    | TyPi (a, b) -> fv a @ fv b
    | Ann (t, ty) -> fv t @ fv ty
    | If (tm1, tm2, tm3) -> fv tm1 @ fv tm2 @ fv tm3
    | Pair (t1, t2) -> fv t1 @ fv t2
    | LetPair (t1, t2) -> fv t1 @ fv t2
    | TySigma (t1, t2) -> fv t1 @ fv t2
    | Let (t1, t2) -> fv t1 @ fv t2
end

open LocallyNameless

let bind (x : name) (t : term) : term = close_term_aux t [ x ] 0
let binds (xs : name list) (t : term) : term = close_term_aux t (List.rev xs) 0

let unbind (t : term) : name * term =
  let x = Atom.fresh "x" in
  (x, open_term_aux t [ free_var x ] 0)

let unbinds (t : term) (n : int) : name list * term =
  let xs = List.init n (fun _ -> Atom.fresh "x") in
  (xs, open_term_aux t List.(rev (map free_var xs)) 0)

(** [instantiate body arg] *)
let instantiate (body : term) (arg : term) : term = open_term_aux body [ arg ] 0

let instantiates (body : term) (arg : term list) : term =
  open_term_aux body (List.rev arg) 0

let bind_pair ((x, y) : name * name) (t : term) : term = binds [ x; y ] t

let unbind_pair (t : term) : name * name * term =
  let x = Atom.fresh "x" in
  let y = Atom.fresh "y" in
  (x, y, open_term_aux t [ free_var y; free_var x ] 0)

let unbind_both (lhs : term) (rhs : term) : name * term * term =
  let x = Atom.fresh "x" in
  let fvx = free_var x in
  (x, instantiate lhs fvx, instantiate rhs fvx)

let unbind_pair_both (lhs : term) (rhs : term) =
  let x = Atom.fresh "x" in
  let y = Atom.fresh "y" in
  ( (x, y),
    ( open_term_aux lhs [ free_var y; free_var x ] 0,
      open_term_aux rhs [ free_var y; free_var x ] 0 ) )

let alpha_eq = alpha_eq

(* -----------------------------------------------------------------------
                      Named AST and conversion
   ----------------------------------------------------------------------- *)
module NamedAst = struct
  open LocallyNameless

  type n_ty = n_term

  and n_term =
    | TyType
    | Var of name
    | App of n_term * n_term
    | Lam of (name * n_term)
    | TyPi of n_ty * (name * n_ty)
    | Ann of n_term * n_ty
    | TyBool
    | Bool of bool
    | If of n_term * n_term * n_term
    | TySigma of n_ty * (name * n_ty)
    | Pair of n_term * n_term
    | LetPair of n_term * (name * name * n_term)
    | Let of n_term * (name * n_term)
    | TyUnit
    | Unit
    | Sorry
    | PrintMe

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
    | TyPi (a, (x, b)) ->
        let a', b' = (to_term a, to_term b) in
        TyPi (a', bind x b')
    | Ann (t, ty) -> Ann (to_term t, to_term ty)
    | TyBool -> TyBool
    | Bool b -> Bool b
    | If (tm1, tm2, tm3) -> If (to_term tm1, to_term tm2, to_term tm3)
    | TySigma (a, (x, b)) ->
        let a', b' = (to_term a, to_term b) in
        TySigma (a', bind x b')
    | Pair (t1, t2) -> Pair (to_term t1, to_term t2)
    | LetPair (t1, (x, y, t2)) ->
        let t1' = to_term t1 in
        let t2' = to_term t2 in
        LetPair (t1', bind_pair (x, y) t2')
    | Let (t1, (x, t2)) ->
        let t1' = to_term t1 in
        let t2' = to_term t2 in
        Let (t1', bind x t2')
    | TyUnit -> TyUnit
    | Unit -> Unit
    | Sorry -> Sorry
    | PrintMe -> PrintMe
end

(* -----------------------------------------------------------------------------
                              Modules and declarations
   ----------------------------------------------------------------------------- *)

type type_decl = { decl_name : name; decl_type : ty }

type entry =
  | Decl of type_decl  (** type declaration *)
  | Def of name * term  (** definition [name * term] *)

(** [decl_entry name decl_type] make a declaration entry
    [Decl { decl_name = name; decl_type }] *)
let decl_entry name decl_type : entry = Decl { decl_name = name; decl_type }

type package_name = string
type package_import = PackageImport of package_name

type package = {
  name : package_name;
  imports : package_import list;
  entries : entry list;
}

type packages = package list
