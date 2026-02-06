open Syntax

(** error message quoting *)
type err_quot =
  | DS of string  (** string *)
  | DT of term  (** term *)
  | DN of name  (** name *)
  | DD of type_decl

type error = err_quot list

(** Internal string representation for debugging (shows indices) *)
let rec string_of_term (t : term) : string =
  match t with
  | TyType -> "Type"
  | Var (Bound i) -> "#" ^ string_of_int i
  | Var (Free x) -> x.name ^ "_" ^ string_of_int x.id
  | Lam body -> "λ. " ^ string_of_term body
  | App (t1, t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"
  | TyPi (a, b) -> "(Π " ^ string_of_term a ^ ". " ^ string_of_term b ^ ")"
  | Ann (t, ty) -> "(" ^ string_of_term t ^ " : " ^ string_of_term ty ^ ")"
  | TyBool -> "Bool"
  | Bool b -> string_of_bool b
  | If (tm1, tm2, tm3) ->
      "if " ^ string_of_term tm1 ^ " then " ^ string_of_term tm2 ^ " else "
      ^ string_of_term tm3
  | Pair (t1, t2) -> "(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ ")"
  | LetPair (t1, t2) ->
      "let (x, y) = " ^ string_of_term t1 ^ " in " ^ string_of_term t2
  | TySigma (t1, t2) ->
      "{x : " ^ string_of_term t1 ^ " | " ^ string_of_term t2 ^ "}"
  | Let (t1, t2) -> "let x = " ^ string_of_term t1 ^ " in " ^ string_of_term t2
  | TyUnit -> "Unit"
  | Unit -> "()"
  | Sorry -> "Sorry"
  | PrintMe -> "PrintMe"

let string_of_name : name -> string = Atom.to_string
