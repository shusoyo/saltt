open Syntax

(* environment *)
type env = { ctx : entry list; globals : int }

(* empty environment *)
let empty_env = { ctx = []; globals = 0 }

(* extend environment: new entries added to the front of the list (corresponding to de Bruijn index increase) *)
let extend env entry = { env with ctx = entry :: env.ctx }

(* lookup the type *)
let lookup env (n : index) : ty option =
  if n >= 0 && n < List.length env.ctx then
    match List.nth env.ctx n with
    | Decl decl -> Some decl.decl_type
    | Def _ -> None (* 如果是定义则查找失败 *)
  else
    None
