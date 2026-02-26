open Saltt
open Common
open Context
open Elaboration
open Parser
open Display
open Evaluation

let prog_name = Filename.basename Sys.argv.(0)

(* ── help messages ─────────────────────────────────────── *)

let usage = Printf.sprintf "usage: %s <command> [<file>]\n" prog_name

let general_help =
  String.concat "\n"
    [
      usage;
      "commands:";
      "  elab <file>   elaborate the file and print the core term";
      "  nf   <file>   elaborate, normalise, and print the normal form with its type";
      "  type <file>   elaborate and print the type";
      "  help          show this message";
      "";
      "options:";
      "  -h, --help    show this message";
    ]

let command_help cmd =
  match cmd with
  | "elab" ->
      String.concat "\n"
        [
          Printf.sprintf "usage: %s elab <file>" prog_name;
          "";
          "Read & elaborate expression from <file>, print the elaborated core term.";
        ]
  | "nf" ->
      String.concat "\n"
        [
          Printf.sprintf "usage: %s nf <file>" prog_name;
          "";
          "Read & elaborate expression from <file>, normalise it,";
          "then print the normal form together with its type.";
        ]
  | "type" ->
      String.concat "\n"
        [
          Printf.sprintf "usage: %s type <file>" prog_name;
          "";
          "Read & elaborate expression from <file>, print its type.";
        ]
  | _ -> general_help

(* ── utilities ─────────────────────────────────────────── *)

let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let get_raw src = src |> Oscar.make_input |> parser.run |> Result.get_ok |> snd

let run_elab filename =
  prerr_endline (read_file filename);
  let raw = get_raw (read_file filename) in
  infer_type empty_ctx raw

let type_error ds = raise (TypeError ds)

(* ── error helpers ─────────────────────────────────────── *)

let die fmt =
  Printf.ksprintf
    (fun msg ->
      Printf.eprintf "%s: %s\n" prog_name msg;
      exit 1)
    fmt

let die_usage fmt =
  Printf.ksprintf
    (fun msg ->
      Printf.eprintf "%s: %s\n%s" prog_name msg usage;
      exit 1)
    fmt

(* ── argument parsing ──────────────────────────────────── *)

type cmd =
  | Elab of string
  | Nf of string
  | Type of string
  | Help of string option (* optional subcommand *)

let is_help_flag s = s = "-h" || s = "--help"

let parse_args argv =
  (* drop the program name *)
  let args = Array.to_list argv |> List.tl in
  (* strip leading help flags *)
  match args with
  | [] -> Help None
  | [ flag ] when is_help_flag flag -> Help None
  | [ "help" ] -> Help None
  | [ "help"; sub ] -> Help (Some sub)
  | cmd :: rest -> (
      (* if the subcommand itself is followed by --help, show command help *)
      match (cmd, rest) with
      | _, [ flag ] when is_help_flag flag -> Help (Some cmd)
      | ("elab" | "nf" | "type"), [] -> die_usage "%s: missing <file> argument" cmd
      | ("elab" | "nf" | "type"), [ _; _ ] -> die_usage "%s: too many arguments" cmd
      | "elab", [ file ] -> Elab file
      | "nf", [ file ] -> Nf file
      | "type", [ file ] -> Type file
      | unknown, _ -> die_usage "unknown command '%s'" unknown)

(* ── dispatch ──────────────────────────────────────────── *)

let run cmd =
  match cmd with
  | Help sub -> print_endline (command_help (Option.value sub ~default:""))
  | Elab filename ->
      let tm, _ty = run_elab filename in
      Printf.printf "%s\n" (syntax_to_string tm)
  | Nf filename ->
      let tm, ty = run_elab filename in
      let norm = normalize [] tm in
      Printf.printf "%s\n" (syntax_to_string norm);
      Printf.printf "  :\n%s\n" (syntax_to_string (quote empty_ctx.level ty))
  | Type filename ->
      let _tm, ty = run_elab filename in
      Printf.printf "%s\n" (syntax_to_string (quote empty_ctx.level ty))

(* ── entry point ───────────────────────────────────────── *)

let () =
  let cmd = parse_args Sys.argv in
  try run cmd
  with TypeError err ->
    Printf.eprintf "%s: %s\n" prog_name (error_to_string err);
    exit 1
