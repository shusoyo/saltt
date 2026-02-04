open Syntax

type error =
  | EnvError of string * term
  | TypeInferError of string * term
  | TypeCheckError of string * term list

(* environment *)
type env = {
  (* elaborated term and datatype declarations *)
  ctx : entry list;
  (* how long the tail of "global" variables in the context is *)
  globals : int;
  hints : decl_type list;
}

(* empty environment *)
let empty_env : env = { ctx = []; globals = 0; hints = [] }

(* extend environment: new entries added to the front of the list *)
let extend_ctx env entry : env = { env with ctx = entry :: env.ctx }

(* Find a name's user supplied type signature. *)
let lookup_hint env (n : name) : decl_type option =
  List.find_opt (fun decl -> decl.decl_name = n) env.hints

(* lookup the type *)
let lookup_type env (n : name) : (ty, error) result =
  List.find_map
    (fun entry ->
      match entry with
      | Decl decl when decl.decl_name = n -> Some decl.decl_type
      | _ -> None)
    env.ctx
  |> Option.to_result ~none:(EnvError ("name not found", Var (Free n)))

let looktup_def env (n : name) : term option =
  List.find_map
    (fun entry ->
      match entry with
      | Def (def_name, def_term) when n = def_name -> Some def_term
      | _ -> None)
    env.ctx
