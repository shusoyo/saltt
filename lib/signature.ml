open Common
open Value

type definition_status = Defined of value | Postulate | Opaque of value
type global_entry = { ty : ty; status : definition_status }
type signature = (name, global_entry) Hashtbl.t

let global_state : signature = Hashtbl.create 100

(* TODO: Need better error handler  *)

let lookup_global (name : name) : global_entry =
  try Hashtbl.find global_state name
  with Not_found -> failwith ("Undefined global: " ^ name)

let define (name : name) (tm : value) (ty : ty) : unit =
  if Hashtbl.mem global_state name then failwith ("Global already defined: " ^ name)
  else Hashtbl.add global_state name { ty; status = Defined tm }

let postulate (name : name) (ty : ty) : unit =
  if Hashtbl.mem global_state name then failwith ("Global already defined: " ^ name)
  else Hashtbl.add global_state name { ty; status = Postulate }

let opaque (name : name) (tm : value) (ty : ty) : unit =
  if Hashtbl.mem global_state name then failwith ("Global already defined: " ^ name)
  else Hashtbl.add global_state name { ty; status = Opaque tm }
