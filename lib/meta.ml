open Value
open Syntax
open Context

type meta_entry = Solved of value | Unsolved

let is_solved (me : meta_entry) : bool = match me with Solved _ -> true | _ -> false
let mcxt : (meta_var, meta_entry) Hashtbl.t = Hashtbl.create 100
let next_meta : int ref = ref 0

let lookup_meta (m : meta_var) : meta_entry =
  try Hashtbl.find mcxt m
  with Not_found -> failwith "impossible: meta variable not found in context"

let reset () : unit =
  next_meta := 0;
  Hashtbl.clear mcxt

let fresh_meta (ctx : ctx) =
  let m = MetaVar !next_meta in
  incr next_meta;
  Hashtbl.add mcxt m Unsolved;
  Ok (InsertedMeta (m, ctx.bds))
