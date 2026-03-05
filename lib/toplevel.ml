open Common
open Evaluation
open Elaboration
open Context

type command =
  | Definition of name * Raw.ty * Raw.term
  | Axiom of name * Raw.term
  | Theorem of name * Raw.ty * Raw.term
(* | Check of Raw.term
  | Eval of Raw.term *)

let process_command (cmd : command) : unit =
  match cmd with
  | Definition (name, ty, tm) ->
      let ctx = empty_ctx in
      let ty_val = eval ctx.env (check_type ctx ty VUniverse) in
      let tm_val = eval ctx.env (check_type ctx tm ty_val) in
      Signature.define name tm_val ty_val
  | Axiom (name, ty) ->
      let ctx = empty_ctx in
      let ty_val = eval ctx.env (check_type ctx ty VUniverse) in
      Signature.postulate name ty_val
  | Theorem (name, ty, tm) ->
      let ctx = empty_ctx in
      let ty_val = eval ctx.env (check_type ctx ty VUniverse) in
      let tm_val = eval ctx.env (check_type ctx tm ty_val) in
      Signature.opaque name tm_val ty_val
