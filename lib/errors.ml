type display =
  | DS of string
  | DR of Raw.term
  | DC of Context.ctx
  | DT of Syntax.term
  | DV of Value.value

type error = display list

exception TypeError of error
exception UnifyError of error
exception EvalError of error

let display_to_string ?(value_to_string = fun _ -> "<value>") = function
  | DS s -> s
  | DR r -> Display.raw_to_string r
  | DT t -> Display.syntax_to_string t
  | DV v -> value_to_string v
  | DC _ -> "<ctx>"

let error_to_string ?value_to_string (err : error) =
  err |> List.map (display_to_string ?value_to_string) |> String.concat "\n  "

let is_domain_error = function
  | TypeError _ | UnifyError _ | EvalError _ | Failure _ -> true
  | _ -> false

let exn_to_string ?value_to_string = function
  | TypeError err -> error_to_string ?value_to_string err
  | UnifyError err -> error_to_string ?value_to_string err
  | EvalError err -> error_to_string ?value_to_string err
  | Failure msg -> msg
  | exn -> Printexc.to_string exn
