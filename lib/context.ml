open Common
open Value

type types = (name * ty) list [@@deriving show]

type ctx = { env : env; types : types; level : level } [@@deriving show]
(** Elaboration context *)

let empty_ctx : ctx = { env = []; types = []; level = Lvl 0 }

let bind (x : name) (a : ty) (ctx : ctx) : ctx =
  {
    env = VVar ctx.level :: ctx.env;
    types = (x, a) :: ctx.types;
    level = next_level ctx.level;
  }

let define (x : name) (t : value) (a : ty) (ctx : ctx) : ctx =
  {
    env = t :: ctx.env;
    types = (x, a) :: ctx.types;
    level = next_level ctx.level;
  }

let report ctx raw msg =
  Error
    (Format.asprintf
       {|@[<v>@{<red>Error:@}@,  %s@,@,@[<v 2>Raw term:@,%a@]@,@,@[<v 2>Ctx:@,%a@]@]|}
       msg Raw.pp_term raw pp_ctx ctx)
