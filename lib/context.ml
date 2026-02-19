open Common
open Value
open Syntax

type types = (name * ty) list [@@deriving show]

type ctx = { env : env; types : types; level : level; bds : bd list } [@@deriving show]
(** Elaboration context *)

let empty_ctx : ctx = { env = []; types = []; level = Lvl 0; bds = [] }

let bind (x : name) (a : ty) (ctx : ctx) : ctx =
  {
    env = vvar ctx.level :: ctx.env;
    types = (x, a) :: ctx.types;
    level = next_level ctx.level;
    bds = Bound :: ctx.bds;
  }

(** [define (x : name) (t : value) (a : ty) (ctx : ctx)] *)
let define (x : name) (t : value) (a : ty) (ctx : ctx) : ctx =
  {
    env = t :: ctx.env;
    types = (x, a) :: ctx.types;
    level = next_level ctx.level;
    bds = Defined :: ctx.bds;
  }

let report ctx raw msg =
  Error
    (Format.asprintf
       {|@[<v>@{<red>Error:@}@,  %s@,@,@[<v 2>Raw term:@,%a@]@,@,@[<v 2>Ctx:@,%a@]@]|} msg
       Raw.pp_term raw pp_ctx ctx)
