open Syntax
open Pp

(** error message quoting *)
type err_quot =
  | DS of string  (** string *)
  | DT of term  (** term *)
  | DN of name  (** name *)
  | DD of type_decl

type error = err_quot list

(* -----------------------------------------------------------------------------
                              Environment
   ----------------------------------------------------------------------------- *)

(* environment *)
type env = {
  ctx : entry list;  (** elaborated term and datatype declarations *)
  globals : int;
      (** how long the tail of "global" variables in the context is *)
  hints : type_decl list;
      (** Type declarations: it's not safe to put these in the context until a
          corresponding term has been checked. *)
}

(* Find a name's user supplied type signature. *)
let lookup_hint env (n : name) : (type_decl, error) result =
  List.find_opt (fun decl -> decl.decl_name = n) env.hints
  |> Option.to_result
       ~none:[ DS "[lookup_hint]: name not found"; DT (free_var n) ]

(** lookup the type *)
let lookup_type env (n : name) : (type_decl, error) result =
  List.find_map
    (fun entry ->
      match entry with
      | Decl decl when decl.decl_name = n -> Some decl
      | _ -> None)
    env.ctx
  |> Option.to_result
       ~none:[ DS "[lookup_type]: name not found"; DT (free_var n) ]

(** [lookup_def env n] return a definition term associated with the name [n] if
    it exists. *)
let lookup_def env (n : name) : (term, error) result =
  List.find_map
    (fun entry ->
      match entry with
      | Def (def_name, def_term) when n = def_name -> Some def_term
      | _ -> None)
    env.ctx
  |> Option.to_result
       ~none:[ DS "[lookup_def]: name not found"; DT (free_var n) ]

(** a empty environment *)
let empty_env : env = { ctx = []; globals = 0; hints = [] }

(** extend environment: new entries added to the front of the list *)
let extend_ctx env entry : env = { env with ctx = entry :: env.ctx }

let extend_ctxs env (entries : entry list) : env =
  { env with ctx = entries @ env.ctx }

let extend_ctxs_globally env (entries : entry list) : env =
  {
    ctx = entries @ env.ctx;
    globals = env.globals + List.length entries;
    hints = env.hints;
  }

let extend_ctx_package env (package : package) : env =
  extend_ctxs env (List.rev package.entries)

let extend_ctx_packages env (packages : package list) : env =
  List.fold_left (fun env pkg -> extend_ctx_package env pkg) env packages

let get_local_ctx env : entry list =
  List.(take (length env.ctx - env.globals) env.ctx)

let extend_hint env decl_type : env =
  { env with hints = decl_type :: env.hints }
