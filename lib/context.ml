open Common
open Value
open Syntax

type name_origin = Inserted | Source [@@deriving show]
type types = (name * name_origin * ty) list [@@deriving show]

(* Elaboration context *)
type ctx = {
  env : env; (* evaluation *)
  types : types; (* raw name lookup, preety printing *)
  level : level; (* unification *)
  bds : bd list; (* fresh meta creation *)
}
[@@deriving show]
(** Elaboration context *)

let empty_ctx : ctx = { env = []; types = []; level = Lvl 0; bds = [] }

let bind (x : name) (a : ty) (ctx : ctx) : ctx =
  {
    env = vvar ctx.level :: ctx.env;
    types = (x, Source, a) :: ctx.types;
    level = next_level ctx.level;
    bds = Bound :: ctx.bds;
  }

let new_binder (x : name) (a : ty) (ctx : ctx) : ctx =
  {
    env = vvar ctx.level :: ctx.env;
    types = (x, Inserted, a) :: ctx.types;
    level = next_level ctx.level;
    bds = Bound :: ctx.bds;
  }

(** [define (x : name) (t : value) (a : ty) (ctx : ctx)] *)
let define (x : name) (t : value) (a : ty) (ctx : ctx) : ctx =
  {
    env = t :: ctx.env;
    types = (x, Source, a) :: ctx.types;
    level = next_level ctx.level;
    bds = Defined :: ctx.bds;
  }

let report ctx raw msg =
  Error
    (Format.asprintf
       {|@[<v>@{<red>Error:@}@,  %s@,@,@[<v 2>Raw term:@,%a@]@,@,@[<v 2>Ctx:@,%a@]@]|} msg
       Raw.pp_term raw pp_ctx ctx)

let report' ctx raw msg =
  Format.asprintf
    {|@[<v>@{<red>Error:@}@,  %s@,@,@[<v 2>Raw term:@,%a@]@,@,@[<v 2>Ctx:@,%a@]@]|} msg
    Raw.pp_term raw pp_ctx ctx
